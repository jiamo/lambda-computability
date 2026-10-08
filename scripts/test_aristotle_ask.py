from __future__ import annotations

import argparse
import asyncio
from contextlib import redirect_stdout
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from scripts import aristotle_ask as ask


class SourceBundleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.files = {
            "source/README.md": b"Read me first.\n",
            "source/A/Main.lean": "theorem exampleA : True := by trivial\n".encode(),
            "source/B/Main.lean": "-- Different same-named file: λ\r\n".encode(),
            "source/papers/main.pdf": b"%PDF-1.7\n\x00\xff\x80\n",
            "source/LICENSE": b"Apache-2.0\n",
        }

    def archive(self, *, zip_format=False):
        archive = self.root / ("input.zip" if zip_format else "input.tar.gz")
        if zip_format:
            with zipfile.ZipFile(archive, "w") as source:
                for path, content in self.files.items():
                    source.writestr(path, content)
        else:
            with tarfile.open(archive, "w:gz") as source:
                for path, content in self.files.items():
                    info = tarfile.TarInfo(path)
                    info.size = len(content)
                    source.addfile(info, io.BytesIO(content))
        return archive

    def test_tar_and_zip_roundtrip_preserve_paths_and_every_byte(self):
        for zip_format in (False, True):
            with self.subTest(zip_format=zip_format):
                bundle = self.root / "source.json"
                ask.build_bundle(self.archive(zip_format=zip_format), bundle)
                destination = self.root / str(zip_format)
                self.assertEqual(ask.restore_bundle(bundle, destination), len(self.files))
                self.assertEqual(ask.restore_bundle(bundle, destination), len(self.files))
                for name, content in self.files.items():
                    self.assertEqual((destination / name).read_bytes(), content)

    def test_tampered_bundle_is_rejected_before_writing_files(self):
        bundle_path = self.root / "source.json"
        bundle = ask.build_bundle(self.archive(), bundle_path)
        next(file for file in bundle["files"] if file["encoding"] == "utf8")["content"] += " changed"
        bundle_path.write_text(json.dumps(bundle))
        destination = self.root / "restored"
        with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
            ask.restore_bundle(bundle_path, destination)
        self.assertFalse(destination.exists())

    def test_archive_rejects_traversal_links_and_duplicate_paths(self):
        for bad_name, bad_type in (("../escape", tarfile.REGTYPE),
                                   ("source/link", tarfile.SYMTYPE),
                                   ("source/link", tarfile.LNKTYPE)):
            with self.subTest(name=bad_name, kind=bad_type):
                archive = self.root / "bad.tar"
                with tarfile.open(archive, "w") as source:
                    member = tarfile.TarInfo(bad_name)
                    member.type = bad_type
                    member.linkname = "/tmp/other"
                    source.addfile(member)
                with self.assertRaises(ValueError):
                    ask.build_bundle(archive, self.root / "source.json")
        archive = self.root / "duplicate.tar"
        with tarfile.open(archive, "w") as source:
            for _ in range(2):
                source.addfile(tarfile.TarInfo("source/A.lean"))
        with self.assertRaisesRegex(ValueError, "Duplicate source path"):
            ask.build_bundle(archive, self.root / "source.json")

    def test_zip_symlink_is_rejected(self):
        archive = self.root / "bad.zip"
        with zipfile.ZipFile(archive, "w") as source:
            member = zipfile.ZipInfo("source/link")
            member.create_system = 3
            member.external_attr = (stat.S_IFLNK | 0o777) << 16
            source.writestr(member, "/tmp/other")
        with self.assertRaisesRegex(ValueError, "Non-regular ZIP"):
            ask.build_bundle(archive, self.root / "source.json")

    def test_restore_rejects_existing_symlink_and_conflicting_content(self):
        bundle_path = self.root / "source.json"
        ask.build_bundle(self.archive(), bundle_path)
        destination = self.root / "restored"
        outside = self.root / "outside"
        outside.mkdir()
        (destination / "source").mkdir(parents=True)
        (destination / "source/A").symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "escapes destination"):
            ask.restore_bundle(bundle_path, destination)
        self.assertEqual(list(outside.iterdir()), [])
        (destination / "source/A").unlink()
        (destination / "source/README.md").write_bytes(b"Keep existing input.")
        with self.assertRaisesRegex(ValueError, "Refusing to overwrite"):
            ask.restore_bundle(bundle_path, destination)
        self.assertEqual((destination / "source/README.md").read_bytes(), b"Keep existing input.")

    def test_project_link_uses_project_id_instead_of_task_id(self):
        url = (f"https://aristotle.harmonic.fun/projects/{ask.DEFAULT_PROJECT}"
               "?task=ffb9579d-5d45-4b21-b15c-fa46cda39086&files=input")
        self.assertEqual(ask.project_id(url), ask.DEFAULT_PROJECT)
        with self.assertRaises(ValueError):
            ask.project_id(url.replace("aristotle.harmonic.fun", "example.com"))

    def test_prepare_preserves_instruction_and_uploads_two_unique_names_only(self):
        instruction = "Exact instruction.\nKeep the pin and attribution.\n"
        prompt_file = self.root / "prompt.md"
        prompt_file.write_text(instruction)
        output = self.root / "output"
        output.mkdir()
        (output / "api-key").write_text("private-key-never-uploaded")
        prompt, files, summary = ask.prepare(self.archive(), prompt_file, output)
        self.assertTrue(prompt.endswith(instruction))
        self.assertIn("/tmp/aristotle-math-source/source/README.md", prompt)
        self.assertEqual([p.name for p in files], ["oai-math-relevant.bundle.json", "restore_source_bundle.py"])
        self.assertEqual(summary["lean_files"], 2)
        self.assertEqual(summary["source_files"], 5)
        self.assertNotIn("private-key-never-uploaded", prompt)
        for file in files:
            self.assertNotIn(b"private-key-never-uploaded", file.read_bytes())


@unittest.skipUnless(importlib.util.find_spec("aristotlelib"), "Install aristotlelib==2.1.0 for SDK wire tests")
class SDKSubmissionTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        import httpx
        self.httpx = httpx
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.requests = []
        self.statuses = [2, 2]
        self.post_status = 200
        self.args = argparse.Namespace(
            project=ask.DEFAULT_PROJECT, wait_idle=0, wait=False,
            output_dir=self.root, resubmit=False, key_file=self.root / "api-key",
        )
        self.attachments = [self.root / "oai-math-relevant.bundle.json", self.root / "restore_source_bundle.py"]
        for file in self.attachments:
            file.write_text("offline attachment")
        self.environment = patch.dict(os.environ, {"ARISTOTLE_API_KEY": "offline-test-key"})
        self.environment.start()
        self.addCleanup(self.environment.stop)
        original_client = httpx.AsyncClient
        transport = httpx.MockTransport(self.handle_request)

        def client(*args, **kwargs):
            return original_client(*args, transport=transport, **kwargs)

        self.client_patch = patch("httpx.AsyncClient", side_effect=client)
        self.client_patch.start()
        self.addCleanup(self.client_patch.stop)

    def handle_request(self, request):
        self.requests.append(request)
        if request.method == "GET":
            return self.httpx.Response(200, json={
                "project_id": ask.DEFAULT_PROJECT, "status": self.statuses.pop(0),
                "created_at": "2026-10-08T00:00:00Z", "last_updated": "2026-10-08T00:00:00Z",
                "description": "Existing project", "has_input": True, "has_files": True,
            })
        if self.post_status != 200:
            return self.httpx.Response(self.post_status, json={"detail": "offline simulated failure"})
        return self.httpx.Response(200, json={
            "project_id": ask.DEFAULT_PROJECT, "agent_task_id": "offline-task", "status": "QUEUED",
            "created_at": "2026-10-08T00:00:00Z", "last_updated_at": "2026-10-08T00:00:00Z",
            "percent_complete": None, "file_name": None, "description": None, "output_summary": None,
        })

    async def test_sdk_sends_one_instruct_to_existing_project_and_blocks_duplicate(self):
        with redirect_stdout(io.StringIO()):
            await ask.submit(self.args, "Exact prompt", self.attachments, {})
        posts = [request for request in self.requests if request.method == "POST"]
        self.assertEqual(len(posts), 1)
        request = posts[0]
        self.assertEqual(request.url.path, f"/api/v3/project/{ask.DEFAULT_PROJECT}/ask")
        body = request.content
        self.assertEqual(body.count(b'filename="'), 2)
        self.assertIn(b'filename="oai-math-relevant.bundle.json"', body)
        self.assertIn(b'filename="restore_source_bundle.py"', body)
        self.assertIn(b'name="mode"\r\n\r\n2\r\n', body)
        self.assertIn(b"Exact prompt", body)
        receipt = (self.root / "last-submission.json").read_text()
        self.assertNotIn("offline-test-key", receipt)
        self.assertEqual(json.loads(receipt)["task_id"], "offline-task")
        before = len(self.requests)
        with self.assertRaisesRegex(ValueError, "already submitted"):
            await ask.submit(self.args, "Exact prompt", self.attachments, {})
        self.assertEqual(len(self.requests), before)

    async def test_busy_project_and_race_do_not_upload_or_start_task(self):
        for statuses in ([1], [2, 1]):
            with self.subTest(statuses=statuses):
                self.requests.clear()
                self.statuses = statuses.copy()
                with redirect_stdout(io.StringIO()), self.assertRaises((ValueError, RuntimeError)):
                    await ask.submit(self.args, "Exact prompt", self.attachments, {})
                self.assertFalse(any(request.method == "POST" for request in self.requests))
                self.assertFalse((self.root / "last-submission.json").exists())

    async def test_failed_upload_is_not_retried(self):
        self.post_status = 500
        with redirect_stdout(io.StringIO()), self.assertRaisesRegex(RuntimeError, "did not retry"):
            await ask.submit(self.args, "Exact prompt", self.attachments, {})
        self.assertEqual(sum(request.method == "POST" for request in self.requests), 1)
        self.assertFalse((self.root / "last-submission.json").exists())

    async def test_key_file_is_used_but_never_attached(self):
        os.environ.pop("ARISTOTLE_API_KEY", None)
        self.args.key_file.write_text("offline-file-key\n")
        with redirect_stdout(io.StringIO()):
            await ask.submit(self.args, "Exact prompt", self.attachments, {})
        request = next(request for request in self.requests if request.method == "POST")
        self.assertEqual(request.headers["X-API-Key"], "offline-file-key")
        self.assertNotIn(b"offline-file-key", request.content)
        self.assertNotIn("offline-file-key", (self.root / "last-submission.json").read_text())


if __name__ == "__main__":
    unittest.main()
