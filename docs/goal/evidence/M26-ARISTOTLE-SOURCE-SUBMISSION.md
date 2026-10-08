# M26-ARISTOTLE-SOURCE-SUBMISSION

On 2026-10-08, after the user replaced the rejected key, the live submission
command succeeded:

```bash
/tmp/church-turing-aristotle-test/bin/python scripts/aristotle_ask.py --wait-idle 3600
```

The tested environment uses `aristotlelib==2.1.0`. The command called the
existing project's `ask` in `INSTRUCT` mode, with the full preserved delivery
instruction, the source bundle, and the standalone restoration script. It
returned:

```text
Submitted: https://aristotle.harmonic.fun/projects/04009a97-5b4f-4a0f-872c-515ae1fa69cc?task=79ddcf9b-59ab-4dbe-ad7b-c84b3cc9dc17
Receipt: /Users/jiamo/projects/church-turing/.aristotle/last-submission.json
```

The bundle carries 1441 original files, including 1275 Lean files, all papers,
and licenses. Byte-for-byte restoration was proved before submission as
recorded in `M26-ARISTOTLE-ASK-TOOL.md`.

An independent authenticated SDK readback used the following code, with the
key loaded locally and never printed:

```python
receipt = json.loads((root / ".aristotle/last-submission.json").read_text())
sdk.set_api_key((root / ".aristotle/api-key").read_text().strip())
task = await sdk.AgentTask.from_id(receipt["task_id"])
assert task.project_id == receipt["project_id"]
```

The readback returned:

```json
{"project_id": "04009a97-5b4f-4a0f-872c-515ae1fa69cc", "task_id": "79ddcf9b-59ab-4dbe-ad7b-c84b3cc9dc17", "status": "IN_PROGRESS", "percent_complete": 1, "source_files": 1441, "lean_files": 1275}
```

This closes submission only. The source absorption and theorem proofs are
the work of the remote task; no completed absorption is claimed here.
