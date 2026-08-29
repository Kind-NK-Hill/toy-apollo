# Security policy

ToyApollo is a local-first research prototype. It does not currently publish a
stable release line or provide a hosted service.

## Reporting a vulnerability

Do not open a public issue for a suspected vulnerability, exposed credential,
private source disclosure, or path that could reveal personal information.

Use GitHub's private vulnerability reporting or a private security advisory for
this repository when available. If that channel is unavailable, contact the
repository owner privately through the GitHub account before sharing technical
details.

Include:

- the affected revision and file or command;
- reproduction steps with secrets removed;
- expected and observed behavior;
- impact and any known workaround.

## Sensitive material

The public source plane must not contain:

- API keys, access tokens, cookies, or `.env` files;
- private textbook/source corpora or unreviewed excerpts;
- machine-local absolute paths in published examples;
- operational SQLite databases, ledger snapshots, prompt packs, logs, or batch
  receipts;
- personal data from local workspaces or review transcripts.

The full private evidence plane may contain local paths and source-derived
material. Treat it as sensitive even when individual files do not contain
credentials.

## Current limitations

- `.gitignore` reduces accidental additions but is not a secret scanner.
- The repository does not yet have an automated PII or credential-redaction
  gate.
- Python dependencies are not yet locked.
- A complete cross-platform security/test matrix is not yet present.
- Model-generated review output is untrusted input until schema, freshness,
  hashes, and apply rules validate it.

These limitations are documented so that users do not infer protections that
the project has not implemented.
