# Step 6 Challenger Postmortem For Step Redesign

Audience: future step designers and Phase2 mechanism maintainers.

Role: challenger / opposition reviewer. This report is intentionally critical.
Its purpose is to stop the next iteration from repeating the same failure mode:
the project appears to prove a source obligation, but the proof burden has only
been moved into a new assumption, wrapper theorem, support constructor, adapter,
or metadata label.

## Executive Judgment

The original Step 1-6 sequence was useful, but it did not fully protect
Textbook Complete claims.

Step 1-4 succeeded at producing a more trustworthy Good Corpus:

- public `Support` / `Spine` / `Bridge` proof-package parameters were exposed
  and mostly cleaned;
- private axioms and source-route gaps became visible instead of being hidden in
  the ledger;
- Mathlib-backed adapters were separated from strict textbook proof completion;
- the classification artifact now says that build success and clean audit are
  not proof-fidelity evidence.

But Step 6 showed that Good Corpus is not Textbook Complete Corpus. Removing a
private axiom can be real progress while still not proving the textbook step. In
`thm_11_7` and `thm_13_14`, the private axiom was removed, but the core missing
mathematics became explicit statement-boundary premises. That is cleaner than a
hidden axiom, but it is not a completed textbook proof.

The current Phase2 obligation mechanism still has a structural weakness:
`proved` can be applied from reviewer coverage without a hard contract that the
landing theorem's statement proves the expected source step and that the theorem
body does not re-assume the same step. This is the exact gap that let wrappers,
support constructors, public extra premises, and adapters look like proof
landings.

Therefore Step 5 must not be followed directly by Lean proof work. A new
mechanism step is required:

**Step 5.5: Obligation Contract Hardening.**

Only after Step 5.5 and source-route extraction should a later step allow
aggressive Lean proof implementation.

## Concrete Evidence From This Run

### `thm_11_7`: private axiom removed, proof still open

Evidence:

- `ToyApollo/Output/thm_11_7.lean:257` defines
  `thm_11_7_from_tailSummability`.
- `ToyApollo/Output/thm_11_7.lean:282` defines public `thm_11_7`.
- `ToyApollo/Output/thm_11_7.lean:293` routes the public theorem through
  `thm_11_7_from_tailSummability`.
- `docs/phase2_completion_classification.md:55` explicitly records
  `thm_11_7` as `open_math_debt`, with `public_interface_leak` and
  `source_route_open`.

The important point is not whether the file builds. It does build. The problem
is that the missing fourth-moment-to-tail-summability proof has not been
formalized. It is now an explicit premise:

- `thm_11_7_tailSummabilitySupport P X μ`

This is better than a private axiom, but it is not a proof of the source step.
If the metadata marked this as `textbook_proof_completed`, it would be false.

### `thm_13_14`: private axiom removed, Fubini / pi-lambda still open

Evidence:

- `ToyApollo/Output/thm_13_14.lean:287` defines
  `thm_13_14_intervalFubiniSupport`.
- `ToyApollo/Output/thm_13_14.lean:296` defines
  `thm_13_14_piLambdaExtensionSupport`.
- `ToyApollo/Output/thm_13_14.lean:327` defines
  `thm_13_14_from_intervalFubini_piLambda`.
- `ToyApollo/Output/thm_13_14.lean:347` defines public `thm_13_14`.
- `docs/phase2_completion_classification.md:59` records `thm_13_14` as
  `open_math_debt`, with `public_interface_leak` and `source_route_open`.

Again, the private axiom removal is real cleanup. It is not the same as proving
the interval Fubini and pi-lambda / generator-extension route from the current
source assumptions. The burden moved to explicit premises.

### Current obligation application is too weak

Evidence:

- `src/toy_apollo/phase2_proof_obligations.py:118` initializes obligations with
  `lean_landing`, `status`, and `review_status`, but no required
  `expected_theorem_signature`.
- `src/toy_apollo/phase2_proof_obligations.py:137` normalizes proof
  obligations, but the schema does not force a theorem-signature contract.
- `src/toy_apollo/phase2_proof_obligations.py:501` applies reviewer output to
  the obligation file.
- `src/toy_apollo/phase2_proof_obligations.py:528` sets
  `target["status"] = "proved"` when review status is `covered`.

This means the mechanism trusts reviewer classification more than it should.
Reviewer prompts warn against moving source obligations into assumptions, but
warnings are not enough:

- `src/toy_apollo/phase2_pack_shared/review_basis_parts.py:25` says statement
  preservation and downstream usability are not enough.
- `src/toy_apollo/phase2_pack_shared/review_basis_parts.py:32` warns that moving
  a source-side obligation into a new theorem-level assumption is a failure.
- `src/toy_apollo/phase2_semantic_review.py:278` says opaque shortcuts should not
  pass.

Those are useful prompts. They are not hard validators. The next mechanism must
turn these review principles into enforceable obligation contracts.

## What The Original Steps Got Right

### Step 1-4: Good Corpus cleanup was necessary

Step 1-4 were effective for the layer they targeted:

- they forced hidden public proof-package parameters into view;
- they separated interface bridge, adapter, open debt, and textbook proof labels;
- they made build and audit status less misleading;
- they prevented `Support` / `Spine` parameters from being treated as normal
  public theorem interfaces;
- they made `thm_14_8_ProofBeyondBook` the only accepted beyond-book root
  exception.

This is genuine progress. Without Step 1-4, Step 6 would have been operating on
a corpus that could still hide source obligations in public parameters or stale
metadata.

### Step 5: target freeze was valuable

Step 5 also did something important: it stopped the project from demanding
Textbook Complete for every file at once. It distinguished:

- selected Textbook Complete targets;
- accepted adapters;
- bridge files;
- open debt backlog;
- tasks requiring route decisions.

That prevented scope explosion. It also stopped `thm_14_5`-style adapter work
from being silently counted as strict textbook proof.

But Step 5 is only a decision freeze. It does not prove anything, and it does
not make the obligation mechanism safe.

## Where The Original Steps Misled Us

The misleading part was treating "private axiom removed" as almost equivalent
to "source obligation proved". Step 6 showed that this inference is invalid.

A private axiom can be removed in at least four different ways:

1. It is replaced by a real theorem proving the source step.
2. It is replaced by a wrapper theorem whose parameters are the same missing
   step.
3. It is replaced by a public premise on the final theorem.
4. It is replaced by a Mathlib-backed adapter that proves a related stronger or
   different statement.

Only the first is strict textbook proof completion. The other three may be
useful cleanup, but they are not `textbook_proof_completed`.

The old steps did not force the mechanism to distinguish these cases before
Step 6 implementation.

## Problems Exposed Only After Step 6

These were not just abstract risks. Step 6 made them concrete:

1. **Statement-boundary premise problem.** `thm_11_7` and `thm_13_14` no longer
   hide their core gap in a private axiom, but they still require a premise
   representing the missing source proof.
2. **Wrapper theorem problem.** A theorem can be theorem-level and still not
   prove the source step if it takes the source step as an input.
3. **Support constructor problem.** A constructor returning `Support` is not
   automatically evidence that every source obligation has been proved. The
   constructor must itself be backed by theorem-level field proofs.
4. **Adapter problem.** A Mathlib-backed theorem may be mathematically valid but
   still not follow the textbook route.
5. **Metadata promotion problem.** The current schema can mark obligations
   `proved` using `lean_landing` plus reviewer `covered`, without requiring
   `expected_theorem_signature` or body-level anti-reassumption checks.
6. **Build/audit insufficiency.** Lean build and public-surface audit can pass
   while the source route remains open.

## Why Step 6A And Step 6B Must Stay Separate

Step 6A is investigation. It extracts the source proof route and determines
whether the current Lean statement has enough assumptions and bridges to support
that route.

Step 6B is implementation. It edits Lean.

Collapsing them causes predictable damage:

- the implementer discovers missing measurability / integrability / bridge
  assumptions mid-proof;
- instead of returning to statement design, it adds a premise or wrapper;
- the file builds;
- metadata labels the wrapper as proof;
- the project again reports false completion.

Therefore a Step 6A blocker is a legitimate outcome. If the route needs a
statement decision, bridge theorem, or foundation lemma, Step 6B must not start.

## Why Step 5.5 Is Required

Step 5.5 must harden the obligation contract before aggressive proof work. It
must prevent "proof by relocation".

Minimum contract:

1. Every obligation must include `expected_theorem_signature`.
2. `proved` can only land on a Lean declaration that is a theorem or lemma, not
   a structure field, support predicate, setup structure, private axiom, or
   adapter label.
3. The landing theorem's statement must imply the expected source step.
4. The landing theorem body must not re-assume the same source step as a premise.
5. A public extra premise on the final theorem does not prove the obligation.
6. A private theorem wrapper does not prove the obligation if its parameters
   include the obligation itself.
7. A support constructor proves an obligation only if the relevant field proof
   is theorem-level and the constructor does not assume the field.
8. A Mathlib-backed adapter can close a task only under
   `mathlib_backed_adapter_completed`, not `textbook_proof_completed`.
9. Reviewer `covered` is insufficient unless the contract validator confirms the
   landing declaration and signature relationship.

This is the mechanism the project assumed Phase2 already had. It did not have
it strongly enough.

## Old Steps Problem To New Steps Correction

| old step / assumption | problem exposed | new correction |
| --- | --- | --- |
| Step 4 public interface cleanup | Clean interface can still expose missing proof as an explicit premise. | Keep Step 4 as Good Corpus only; never promote from Step 4 to Textbook Complete without later proof-fidelity gates. |
| Step 5 target freeze | Selecting a target does not prove route feasibility. | Keep Step 5, but add Step 5.5 before proof implementation. |
| Step 6 route extraction and proof work too close together | Implementer can patch missing route by adding premises or wrappers. | Split Step 6A route extraction from later Lean implementation. A blocker is an allowed Step 6A result. |
| `lean_landing` field | Landing name alone does not say what theorem proves. | Require `expected_theorem_signature` and validator comparison. |
| Reviewer `covered` | Reviewer can miss that theorem body re-assumes the source step. | Add body / premise review and contract validation before applying `proved`. |
| Private axiom removal | Missing proof can move to statement-boundary premise. | Completion requires proving the new premise internally, not merely exposing it. |
| Support constructor accepted as landing | Constructor may package assumptions instead of proving fields. | Require theorem-level field landings and no source-step premise in constructor. |
| Adapter accepted as completion | Adapter may prove a valid Mathlib specialization but not the textbook route. | Adapter remains `mathlib_backed_adapter_completed` unless source route is rebuilt. |
| Build/audit pass | Build/audit cannot judge proof fidelity. | Use build/audit only as hygiene checks, not completion classifiers. |

## Redesigned Step 5-10

### Step 5: Textbook-Complete Target Selection

Purpose: freeze which tasks are strict Textbook Complete targets and which are
accepted adapters, bridges, or open debt.

Output:

- target list;
- current class;
- target class;
- blocker declaration;
- allowed route;
- decision required;
- acceptance criterion.

Hard rule: Step 5 cannot edit Lean and cannot mark anything complete.

### Step 5.5: Obligation Contract Hardening

Purpose: make Phase2 unable to certify fake proof landings.

Required implementation:

- extend `proof_obligations.json` schema with `expected_theorem_signature`;
- add a validator that rejects proved obligations landing on:
  - structure fields;
  - support predicates;
  - setup structures;
  - private axioms;
  - theorem wrappers that assume the obligation;
  - public extra premises;
  - adapter declarations when target class is textbook proof;
- update review prompts so reviewer must compare expected signature to landing
  signature;
- update apply-review logic so `covered` does not automatically become
  `proved` unless the validator passes;
- add tests with adversarial examples.

Exit criterion:

- an obligation cannot be marked `proved` unless its landing theorem is a real
  theorem/lemma whose statement proves the expected source step without
  re-assuming it.

### Step 6A: Source Proof Route Extraction

Purpose: extract textbook proof route without Lean edits.

Output per target:

- source theorem statement;
- source proof steps;
- expected Lean theorem signatures for each step;
- existing earlier results or bridge candidates;
- missing foundation lemmas;
- decision: `ready_for_lean`, `needs_bridge`, `needs_statement_decision`, or
  `open_math_debt`.

Hard rule: if a target needs stronger hypotheses or bridge/foundation work, do
not start Lean proof implementation.

### Step 6B: Feasibility And Signature Freeze

Purpose: freeze the exact lemma queue before proof work.

Output:

- ordered theorem signatures;
- allowed imports;
- allowed Mathlib use;
- no-new-public-premise rule;
- validation command list;
- write scope.

This step prevents "proof work" from rewriting the target into a different
theorem.

### Step 7: Bridge / Foundation Completion

Purpose: prove missing interface and foundation lemmas before final theorem
assembly.

Examples:

- DCT / convergence bridges;
- finite or countable distribution bridges;
- moment / integrability bridges;
- Fubini / generator-extension lemmas;
- independence-to-centered-variable transfer lemmas.

Hard rule: bridge completion is not final theorem completion unless the task is
classified as `interface_bridge_completed`.

### Step 8: Scoped Lean Proof Implementation

This is the first step where "hard proof work" is allowed.

Entry conditions:

- Step 5 target is frozen;
- Step 5.5 obligation contract is active;
- Step 6A route extraction exists;
- Step 6B theorem signatures are frozen;
- required Step 7 bridge/foundation lemmas are either proved or explicitly
  accepted as out of scope;
- write scope is bounded;
- no new public theorem premise is allowed without returning to Step 5.

Allowed behavior:

- aggressively prove the frozen lemmas;
- split implementation into theorem-level sublemmas;
- use Mathlib for local standard facts;
- use subagents only with disjoint write scopes.

Forbidden behavior:

- replacing a frozen source step by a new hypothesis;
- landing an obligation on a constructor or wrapper that assumes the same step;
- marking an adapter as textbook proof;
- changing final theorem statement to make proof easier without returning to
  Step 5.

### Step 9: Textbook Fidelity Review

Purpose: verify proof route, not just build.

Review checklist:

- statement remains faithful to source;
- no extra public proof premise was added;
- every source step has a theorem/lemma landing;
- theorem body does not assume the expected source step;
- Mathlib calls are local tools, not replacement of the whole textbook proof;
- earlier ToyApollo results are reused where claimed;
- classification matches proof route.

### Step 10: Final Classification Update

Purpose: update classification only after proof-fidelity review.

Allowed promotions:

- `textbook_proof_completed`: only after Step 8 and Step 9 pass;
- `mathlib_backed_adapter_completed`: valid Lean adapter, no strict source route
  claim;
- `interface_bridge_completed`: bridge/equivalence theorem only;
- `open_math_debt`: source step still not proved;
- `beyond_book_exception`: only the allowed root exception.

Hard rule: build success and audit success are not sufficient evidence for
`textbook_proof_completed`.

## What Must Not Be Marked `textbook_proof_completed`

Do not mark any of the following as `textbook_proof_completed`:

1. A theorem whose proof depends on a private axiom for the source step.
2. A theorem whose public statement includes a new premise equal to the missing
   source step.
3. A private theorem wrapper whose parameters include the source obligation.
4. A support constructor that packages source-step assumptions without proving
   them.
5. A structure field projection or support predicate.
6. A theorem landed only because it has the right name but not the expected
   statement.
7. A Mathlib-backed adapter that bypasses the textbook proof route.
8. A theorem whose body proves the conclusion by invoking a hypothesis that is
   substantially the same as the obligation.
9. A task whose proof route is clean only in metadata but not in Lean.
10. A task that passes build/audit but lacks source-route theorem landings.

## Mechanism Files That Need Changes

### Required code changes

- `src/toy_apollo/phase2_proof_obligations.py`
  - add `expected_theorem_signature` to normalized obligations;
  - reject `proved` if signature contract is missing;
  - stop mapping reviewer `covered` directly to `proved` unless contract
    validation passes;
  - record `proof_contract_status` separately from reviewer status.

- `src/toy_apollo/phase2_semantic_review.py`
  - require reviewer output to compare expected signature with landing
    signature;
  - require explicit body-level anti-reassumption review;
  - distinguish adapter coverage from textbook proof coverage.

- `src/toy_apollo/phase2_pack_shared/review_basis_parts.py`
  - promote current warnings into mandatory review fields:
    `signature_match`, `body_reassumption_check`, `adapter_or_source_route`,
    `public_premise_check`.

- `tools/validate_phase2_completion_classification.py`
  - reject `textbook_proof_completed` when evidence points only to adapter,
    support constructor, setup structure, public extra premise, or private
    axiom;
  - require proof-contract status for promoted textbook tasks.

- New validator recommended:
  - `tools/validate_phase2_obligation_contracts.py`
  - checks every `phase2_prompt_packs/*/proof_obligations.json`;
  - verifies `expected_theorem_signature` exists for blocking obligations;
  - rejects forbidden landing classes;
  - flags missing or stale proof-contract reviews.

- `tools/audit_phase2_clean_debt_surface.py`
  - keep as public-surface hygiene only;
  - do not let this tool become a proof-fidelity oracle;
  - optionally emit hints for public extra premises that look like source-step
    obligations.

### Required tests

- `tests/test_phase2_proof_obligation_contracts.py`
  - proved landing on structure field must fail;
  - proved landing on support predicate must fail;
  - proved landing on private axiom must fail;
  - wrapper theorem assuming same obligation must fail;
  - adapter landing must not satisfy textbook target;
  - real theorem/lemma with matching expected signature must pass.

- Extend `tests/test_phase2_completion_classification.py`
  - `textbook_proof_completed` requires proof-contract evidence, not only build
    and audit evidence.

- Extend semantic review tests
  - pass verdict without signature comparison should be inconclusive or fail;
  - pass verdict with public-premise replacement should fail.

## Final Challenger Conclusion

The Step 1-4 work was not wasted. It made the corpus honest enough to reveal the
real problem. The mistake would be to treat that honesty as completion.

Step 6 proved that "remove private axiom" is an ambiguous operation. It can mean
real proof completion, or it can mean the missing proof moved to the theorem
boundary. `prob_10_6` is the good case: strict proof landed. `thm_11_7` and
`thm_13_14` are the warning cases: axiom removal happened, but the source route
is still open.

The next design must enforce this distinction mechanically. Add Step 5.5 before
any future hard proof push. After that, the first step that should allow
aggressive Lean proof implementation is Step 8, not Step 6A and not Step 5.

The rule for future designers is simple:

**No expected theorem signature, no proved obligation. No body anti-reassumption
check, no textbook proof completion. No source-route theorem landings, no
Textbook Complete label.**
