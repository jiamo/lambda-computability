# Continue the existing Aristotle project

The default project is
[04009a97-5b4f-4a0f-872c-515ae1fa69cc](https://aristotle.harmonic.fun/projects/04009a97-5b4f-4a0f-872c-515ae1fa69cc).
The script calls `Project.from_id(...)`, then `project.ask(...)` in `INSTRUCT`
mode with attachments. It continues that project's existing work. The task ID
in the supplied URL is the old task, not the project ID to pass to the SDK.

## Run

From the repository root, with Python 3.10 or later and `uv` installed:

```bash
python3 scripts/aristotle_ask.py --dry-run
uv run --with aristotlelib==2.1.0 python scripts/aristotle_ask.py --wait-idle 3600
```

Before the second command, either set `ARISTOTLE_API_KEY` in that terminal, or
put the key alone in `.aristotle/api-key`. The environment variable takes
precedence. The key file is ignored by Git and is never attached to Aristotle.
An alternative file location is supported with `--key-file /path/to/key`.
Do not paste the key into the prompt document.

If you prefer pip, install `aristotlelib==2.1.0` in a virtual environment and
run the same script with that environment's Python. The SDK's
[published package](https://pypi.org/project/aristotlelib/2.1.0/) documents
installation and `ARISTOTLE_API_KEY` authentication. The SDK source in that
release is the API contract used here.

The default input is `~/Downloads/oai-math-relevant.tar.gz`. Override it with
`--archive /path/to/snapshot.tar.gz`; ZIP snapshots are accepted too. A
different project UUID or full project URL can be supplied with `--project`.

The script waits up to 3600 seconds for the existing project to become `IDLE`
when invoked as above. It submits one follow-up with two attachments and
prints the new task URL. Add `--wait` to stream events and answer any agent
questions in the terminal. Without `--wait`, submission returns immediately
and agent questions are disabled, following the SDK's default.

## What is sent

The delivery instruction is stored in `docs/aristotle-absorption-prompt.md`.
The generated prompt adds transport instructions before that text; the
delivery instruction remains intact. It tells Aristotle to restore the
source snapshot outside the target repository, read its README first, then
continue the existing project under the specified pin and attribution rules.

SDK 2.1.0's `Project.ask` uses `file_path.name` for multipart filenames and
opens all attachments at once. Directly attaching 1441 extracted files would
lose their hierarchy, collide on filenames such as `README.md`, and could
exceed the local open-file limit. Instead the script attaches:

- `oai-math-relevant.bundle.json`: every regular archive file, its original
  relative path, exact content, and SHA-256. Text stays readable; binary
  content including PDFs uses base64.
- `restore_source_bundle.py`: a copy of the script whose restore mode uses
  only the Python standard library.

Aristotle is instructed to run:

```bash
python3 restore_source_bundle.py --restore-bundle oai-math-relevant.bundle.json --destination /tmp/aristotle-math-source
```

This recreates the complete input hierarchy, including Lean files, papers,
licenses, and upstream build metadata. The upstream configuration is reference
material and must not replace this library's configuration.

Generated attachments and `prompt.txt` are in `.aristotle/`, ignored by Git.
`--dry-run` prepares them without an API key, SDK, network request, or remote
task. `.aristotle/last-submission.json` records the returned task ID and URL.
The script rejects repeating the same recorded request unless `--resubmit`
is given. It does not retry a failed `ask`: after a timeout, check the project
page before submitting again because the server may already have started it.

The source bundle is an attachment transport, not a library delivery archive.
No library packaging command or Lean pin is changed by this tool.

## Verification

```bash
uv run --with aristotlelib==2.1.0 python -m unittest scripts.test_aristotle_ask -v
python3 scripts/goal_state.py validate
```

Tests use an in-memory HTTP transport with the real SDK; they never contact
Aristotle. They check exact source restoration, duplicate basenames, binary
content, integrity failures, existing-project multipart requests, busy-project
and race rejection, failed-request behavior, and key exclusion. Without the
SDK, only the standard-library tests run and the wire tests are skipped.

Local verification does not establish server acceptance of the attachments.
A real submission needs authentication and an idle project; success is the
new task ID returned by `ask`, recorded in the receipt.
