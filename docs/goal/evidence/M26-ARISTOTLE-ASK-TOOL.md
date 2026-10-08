# M26-ARISTOTLE-ASK-TOOL

The local submission tool is `scripts/aristotle_ask.py`, documented in
`docs/aristotle-ask.md`. It continues the existing Aristotle project with the
source snapshot and the supplied delivery instruction.

This row proves preparation and SDK request construction only. It does not
claim that any upstream theorem has been absorbed or that a remote task has
been started. The directory-level M26 rows are requested in the preserved
Aristotle delivery prompt; their proofs and statuses belong to that work.

Verification on 2026-10-08:

- `python3 scripts/aristotle_ask.py --dry-run` prepared 1441 source files,
  including 1275 Lean files, from the local snapshot. The bundle is 19.65 MiB.
- Restoring the generated bundle with the uploaded copy of the script and
  comparing every regular file with the original TAR yielded 1441 exact byte
  matches. This includes all licenses and binary PDFs.
- The test suite with `aristotlelib==2.1.0` exercises the actual SDK against
  an in-memory HTTP transport; all 11 tests pass. Its existing-project request is exactly one
  `POST /api/v3/project/04009a97-5b4f-4a0f-872c-515ae1fa69cc/ask`, in
  `INSTRUCT` mode, with two unique multipart filenames.
- The suite rejects busy projects and a project becoming busy before the
  SDK's attachment check; it sends no POST in either case. Failed POSTs are
  not retried, successful repeat requests are guarded by the receipt, and
  the key is excluded from attachments and receipts.

No Lean source, toolchain, dependency pin, or library delivery archive was
changed. After the user supplied a local key, an actual submission attempt
stopped at `Project.from_id`: the service returned `401 Invalid API key`.
No attachment upload or task-creating POST was reached in that attempt.
After the user replaced the key, the actual service accepted the submission;
see `M26-ARISTOTLE-SOURCE-SUBMISSION.md` for the returned task ID and readback.
