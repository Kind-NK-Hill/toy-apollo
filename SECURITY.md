# Security policy

ProbabilityTheoryFormalization is a local research system. The v0.2 release
packages the public runtime and corpus; it is not a hosted service or a guarantee
of production security support.

## Report privately

For vulnerabilities, exposed credentials or private-source disclosure, use this
repository's GitHub private vulnerability reporting when available. Otherwise
contact the maintainer at [kdsdengshuo2823@gmail.com](mailto:kdsdengshuo2823@gmail.com)
before sending sensitive details. Do not include secrets in a public issue.

Include the affected revision, file/command, a sanitized reproducer, expected
and observed behavior, and impact.

## Data and execution boundaries

Public releases exclude credentials, private textbook inputs, full plans/catalog
policies, upstream snapshots, operational databases, live prompt packs and private
review transcripts. The publication checker verifies the selected file inventory,
normalized content fingerprints and source-prose boundary. It is not a general
secret or personal-information scanner.

Model output is untrusted until schema, binding, freshness and apply checks pass.
Those checks establish protocol consistency; they do not establish mathematical
truth or prove that a reviewer operated independently.

The workflow demonstration's external reviewer is a user-supplied command.
Configure its permissions and isolation before running it. Before/after file
hash checks detect persisted changes; they are not an operating-system sandbox.
Default replay calls no external model and uses a separately generated workspace.

## Current limits

- `.gitignore` is an accidental-addition guard, not a secret scanner.
- Python dependencies are not fully locked.
- The tested platform/version set is limited.
- SHA-256 bindings are consistency checks, not signatures or protection against
  an adversary who can rewrite both data and its claimed digest.

Complete local evidence can include source-derived text and machine paths even
when it contains no credentials. Preserve it under the workspace's access policy.
