# Security And Secrets

## Hard Rules

- Never commit API keys, tokens, or credentials.
- Never hardcode secrets in Python, PowerShell, Markdown, or test fixtures.
- Do not add `.env` files to the project root.

## Current Required Secrets

- No current secret is required for Phase 0/1/2 prompt-pack workflows.
- `ARISTOTLE_API_KEY` is required only for Phase 3 Aristotle offload.

Common optional variables:

- `DEEPSEEK_API_KEY` for legacy/direct-generation-only paths; it is not a current required secret.
- `DEEPSEEK_BASE_URL`
- `DEEPSEEK_MODEL`

## Preferred Handling

- Use process or user-level environment variables.
- If local secret tooling is introduced later, document it here and keep secrets outside the repo tree.
- Do not perform stabilization by cleaning, deleting, moving, or rewriting `.env*` or secret-adjacent local files.

## Current Enforcement Reality

- `.gitignore` blocks `.env` from being committed, but that is not a sufficient security boundary.
- The repository does not yet have pre-tool hooks for dangerous shell commands.
- The repository does not yet have a redaction layer for PII or secret masking.

Document these gaps honestly. Do not pretend the protections already exist.
