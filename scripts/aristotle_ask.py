#!/usr/bin/env python3
"""Attach the source snapshot and delivery prompt to an existing Aristotle project.

Uses aristotlelib 2.1.0. Its ask() sends basenames only, so a JSON bundle preserves
the input hierarchy without hundreds of colliding filenames or open file handles.
Dry-run and bundle restoration use only the Python standard library.
"""

from __future__ import annotations

import argparse
import asyncio
import base64
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shlex
import shutil
import stat
import sys
import tarfile
import time
from urllib.parse import urlparse
from uuid import UUID
import zipfile


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROJECT = "04009a97-5b4f-4a0f-872c-515ae1fa69cc"
BUNDLE_FORMAT = "aristotle-source-bundle-v1"
MAX_SOURCE_BYTES = 512 * 1024 * 1024


def source_path(name: str) -> PurePosixPath:
    path = PurePosixPath(name)
    if (
        not name or "\\" in name or path.is_absolute()
        or ".." in path.parts or not path.parts or ":" in path.parts[0]
    ):
        raise ValueError(f"Unsafe source path: {name!r}")
    return path


def project_id(value: str) -> str:
    if "://" in value:
        url = urlparse(value)
        parts = url.path.strip("/").split("/")
        if (
            url.scheme != "https" or url.netloc != "aristotle.harmonic.fun"
            or len(parts) != 2 or parts[0] != "projects"
        ):
            raise ValueError("Use an Aristotle project URL or project UUID.")
        value = parts[1]
    return str(UUID(value))


def archive_files(archive: Path):
    """Read regular files only; never extract arbitrary archive entries locally."""
    if zipfile.is_zipfile(archive):
        with zipfile.ZipFile(archive) as source:
            for member in source.infolist():
                if member.is_dir():
                    continue
                path = source_path(member.filename)
                kind = stat.S_IFMT(member.external_attr >> 16)
                if kind not in (0, stat.S_IFREG):
                    raise ValueError(f"Non-regular ZIP entry: {path}")
                if member.file_size > MAX_SOURCE_BYTES:
                    raise ValueError(f"Source file too large: {path}")
                yield path, source.read(member)
    else:
        with tarfile.open(archive, "r:*") as source:
            for member in source:
                if member.isdir():
                    continue
                path = source_path(member.name)
                if not member.isfile():
                    raise ValueError(f"Non-regular TAR entry: {path}")
                if member.size > MAX_SOURCE_BYTES:
                    raise ValueError(f"Source file too large: {path}")
                with source.extractfile(member) as stream:
                    yield path, stream.read()


def build_bundle(archive: Path, destination: Path) -> dict:
    files = []
    seen = set()
    total = 0
    for path, content in archive_files(archive):
        name = path.as_posix()
        if name in seen:
            raise ValueError(f"Duplicate source path: {name}")
        seen.add(name)
        total += len(content)
        if total > MAX_SOURCE_BYTES:
            raise ValueError("Source archive expands beyond 512 MiB.")
        try:
            text = content.decode("utf-8")
            encoding = "utf8"
        except UnicodeDecodeError:
            text = base64.b64encode(content).decode("ascii")
            encoding = "base64"
        files.append({
            "path": name, "encoding": encoding, "content": text,
            "sha256": hashlib.sha256(content).hexdigest(),
        })
    if not files:
        raise ValueError("Source archive contains no files.")
    bundle = {
        "format": BUNDLE_FORMAT, "source_archive": archive.name,
        "files": sorted(files, key=lambda file: file["path"]),
    }
    destination.write_text(json.dumps(bundle, ensure_ascii=False) + "\n", encoding="utf-8")
    return bundle


def restore_bundle(bundle_path: Path, destination: Path) -> int:
    bundle = json.loads(bundle_path.read_text(encoding="utf-8"))
    if bundle.get("format") != BUNDLE_FORMAT or not isinstance(bundle.get("files"), list):
        raise ValueError("Unrecognized source bundle format.")
    root = destination.resolve()
    decoded = []
    seen = set()
    total = 0
    for file in bundle["files"]:
        path = source_path(file["path"])
        if path in seen:
            raise ValueError(f"Duplicate source path: {path}")
        seen.add(path)
        if file["encoding"] == "utf8":
            content = file["content"].encode("utf-8")
        elif file["encoding"] == "base64":
            content = base64.b64decode(file["content"], validate=True)
        else:
            raise ValueError(f"Unknown encoding for {path}")
        total += len(content)
        if total > MAX_SOURCE_BYTES:
            raise ValueError("Source bundle expands beyond 512 MiB.")
        if hashlib.sha256(content).hexdigest() != file["sha256"]:
            raise ValueError(f"SHA-256 mismatch: {path}")
        target = root.joinpath(*path.parts)
        if target.is_symlink() or not target.resolve().is_relative_to(root):
            raise ValueError(f"Source path escapes destination: {path}")
        if target.exists() and (not target.is_file() or target.read_bytes() != content):
            raise ValueError(f"Refusing to overwrite different existing content: {target}")
        decoded.append((target, content))
    for target, content in decoded:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    return len(decoded)


def prepare(archive: Path, prompt_file: Path, output_dir: Path) -> tuple[str, list[Path], dict]:
    instruction = prompt_file.read_text(encoding="utf-8")
    if not instruction.strip():
        raise ValueError("The delivery prompt is empty.")
    output_dir.mkdir(parents=True, exist_ok=True)
    bundle_path = output_dir / "oai-math-relevant.bundle.json"
    bundle = build_bundle(archive, bundle_path)
    restorer = output_dir / "restore_source_bundle.py"
    shutil.copyfile(Path(__file__), restorer)
    names = [file["path"] for file in bundle["files"]]
    readmes = [name for name in names if PurePosixPath(name).name == "README.md"]
    if not readmes:
        raise ValueError("Source archive has no README.md; check the archive you selected.")
    readme = min(readmes, key=lambda name: (len(PurePosixPath(name).parts), name))
    lean_count = sum(name.endswith(".lean") for name in names)
    prompt = (
        "ATTACHMENT TRANSPORT -- restore the reference inputs before doing any work.\n\n"
        "The source snapshot mentioned below is attached as oai-math-relevant.bundle.json,\n"
        "not as a compressed archive. It preserves every original path and file byte;\n"
        "text is UTF-8 and binary files (including PDFs) use base64. Run:\n\n"
        "python3 restore_source_bundle.py --restore-bundle oai-math-relevant.bundle.json "
        "--destination /tmp/aristotle-math-source\n\n"
        "If attachments are in another directory, locate these two filenames and use\n"
        "their actual paths. The restore command needs no SDK, network, or API key.\n"
        f"It checks every file's SHA-256 and restores {len(names)} files, including "
        f"{lean_count} Lean files.\n"
        f"Read {shlex.quote('/tmp/aristotle-math-source/' + readme)} first.\n"
        "The restored tree is reference input outside the target repository. Continue\n"
        "in this existing project's repository; do not vendor the reference tree or\n"
        "replace our build configuration with its upstream configuration.\n"
        "M26 may already contain a completed local submission-tool row; preserve it\n"
        "and add the requested directory rows without duplicating the milestone.\n\n"
        "DELIVERY INSTRUCTION\n\n" + instruction
    )
    (output_dir / "prompt.txt").write_text(prompt, encoding="utf-8")
    summary = {
        "source_files": len(names), "lean_files": lean_count,
        "bundle_bytes": bundle_path.stat().st_size,
    }
    return prompt, [bundle_path, restorer], summary


async def idle_project(sdk, identifier: str, wait_seconds: int):
    project = await sdk.Project.from_id(identifier)
    deadline = time.monotonic() + wait_seconds
    while project.status != sdk.ProjectStatus.IDLE:
        remaining = deadline - time.monotonic()
        if project.status != sdk.ProjectStatus.RUNNING or remaining <= 0:
            raise ValueError(
                f"Project is {project.status.name}, not IDLE. No prompt was sent. "
                "Try later, or use --wait-idle 3600 to wait up to an hour."
            )
        print("Project is RUNNING; waiting for IDLE...", flush=True)
        await asyncio.sleep(min(15, remaining))
        await project.refresh()
    return project


async def submit(args, prompt: str, attachments: list[Path], summary: dict) -> None:
    key = os.environ.get("ARISTOTLE_API_KEY", "").strip()
    if not key and args.key_file.expanduser().is_file():
        key = args.key_file.expanduser().read_text(encoding="utf-8").strip()
    if not key:
        raise ValueError(
            f"Set ARISTOTLE_API_KEY, or put the key alone in {args.key_file}."
        )
    # Keep error redaction consistent for keys loaded from a file as well.
    os.environ["ARISTOTLE_API_KEY"] = key
    try:
        import aristotlelib as sdk
    except ImportError as error:
        raise ValueError("Install the SDK: python -m pip install aristotlelib==2.1.0") from error
    sdk.set_api_key(key)
    digest = hashlib.sha256((args.project + prompt).encode("utf-8"))
    for file in attachments:
        digest.update(file.read_bytes())
    fingerprint = digest.hexdigest()
    receipt_path = args.output_dir / "last-submission.json"
    if receipt_path.exists() and not args.resubmit:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        if receipt.get("fingerprint") == fingerprint:
            raise ValueError(
                f"This request was already submitted as task {receipt['task_id']}. "
                "Use --resubmit only if you intend to start it again."
            )
    project = await idle_project(sdk, args.project, args.wait_idle)
    questions = (
        sdk.AgentQuestionsSetting.TIMEOUT_15_MIN if args.wait
        else sdk.AgentQuestionsSetting.DISABLED
    )
    print("Submitting one follow-up with two attachments...", flush=True)
    try:
        task = await project.ask(
            prompt, mode=sdk.FollowUpMode.INSTRUCT, files=attachments,
            agent_questions_setting=questions,
        )
    except Exception as error:
        raise RuntimeError(
            f"project.ask failed: {error}. The script did not retry. "
            "Check the project page for a new task before running it again."
        ) from error
    url = f"https://aristotle.harmonic.fun/projects/{args.project}?task={task.agent_task_id}"
    receipt = {
        "project_id": args.project, "task_id": task.agent_task_id,
        "url": url, "fingerprint": fingerprint, **summary,
    }
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(f"Submitted: {url}\nReceipt: {receipt_path}", flush=True)
    if args.wait:
        await task.wait_for_completion()
        print(f"Task status: {task.status.name}", flush=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", default=DEFAULT_PROJECT, help="Project UUID or project URL")
    parser.add_argument("--archive", type=Path, default=Path.home() / "Downloads/oai-math-relevant.tar.gz",
                        help="Source snapshot (.tar.gz or .zip)")
    parser.add_argument("--prompt-file", type=Path, default=ROOT / "docs/aristotle-absorption-prompt.md")
    parser.add_argument("--output-dir", type=Path, default=ROOT / ".aristotle")
    parser.add_argument("--key-file", type=Path, default=ROOT / ".aristotle/api-key",
                        help="Read the key here if ARISTOTLE_API_KEY is unset; never uploaded")
    parser.add_argument("--dry-run", action="store_true", help="Prepare and inspect; no key, SDK, or network needed")
    parser.add_argument("--wait-idle", type=int, default=0, metavar="SECONDS")
    parser.add_argument("--wait", action="store_true", help="Stream task events and answer agent questions in this terminal")
    parser.add_argument("--resubmit", action="store_true", help="Allow repeating a request recorded in last-submission.json")
    parser.add_argument("--restore-bundle", type=Path, help="Restore reference files locally; no API call")
    parser.add_argument("--destination", type=Path, default=Path("/tmp/aristotle-math-source"))
    args = parser.parse_args(argv)
    try:
        if args.restore_bundle:
            count = restore_bundle(args.restore_bundle, args.destination)
            print(f"Restored {count} verified files to {args.destination.resolve()}")
            return 0
        if args.wait_idle < 0:
            raise ValueError("--wait-idle must be non-negative.")
        args.project = project_id(args.project)
        args.archive = args.archive.expanduser().resolve(strict=True)
        args.prompt_file = args.prompt_file.expanduser().resolve(strict=True)
        args.output_dir = args.output_dir.expanduser().resolve()
        prompt, attachments, summary = prepare(args.archive, args.prompt_file, args.output_dir)
        print(f"Project: {args.project}\nSource: {args.archive}")
        print(f"Source files: {summary['source_files']} ({summary['lean_files']} Lean files)")
        print(f"Bundle: {summary['bundle_bytes'] / 1024 / 1024:.2f} MiB")
        print(f"Prompt preview: {args.output_dir / 'prompt.txt'}")
        if args.dry_run:
            print("Dry run complete. Nothing was sent to Aristotle.")
        else:
            asyncio.run(submit(args, prompt, attachments, summary))
        return 0
    except KeyboardInterrupt:
        print("Interrupted. Check the project page before resubmitting.", file=sys.stderr)
        return 130
    except Exception as error:
        message = str(error)
        key = os.environ.get("ARISTOTLE_API_KEY", "").strip()
        if key:
            message = message.replace(key, "<redacted>")
        print(f"Error: {message}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
