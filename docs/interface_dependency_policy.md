# Interface Dependency Policy

## Purpose

This note records how ToyApollo should handle common textbook notation that
appears again and again in later chapters.

Examples:

- `E[X]`
- Lebesgue integrals
- distributions
- Lebesgue-Stieltjes or Riemann-Stieltjes integrals

The problem is not that later chapters depend on earlier chapters. That is
normal.

The problem is that the same mathematical idea can often be written in Lean in
two different ways:

1. using a project definition introduced from the textbook
2. using the standard Mathlib definition or notation

If an earlier theorem uses one way and a later theorem uses the other way,
importing the earlier theorem may not be enough to use it directly. A separate
translation lemma may be needed.

## Tao-Style Rule

Use this order for a new important concept:

1. When the concept is first introduced, define it in the textbook style.
2. Prove the first few basic properties in that textbook style.
3. If Mathlib already has the same idea, or a more general version of it, prove
   a theorem connecting the textbook version to the Mathlib version.
4. After that connection is available, later files should usually use the
   Mathlib version.

This is the pattern Kenneth pointed out from Terence Tao's Analysis I
formalization:

- early chapters introduce textbook objects
- technical epilogues connect them to Mathlib objects
- later chapters switch to Mathlib objects

So the policy is not "always use Mathlib from the start".

It is also not "always keep using the textbook definition forever".

The policy is:

> first textbook, then interface translation, then Mathlib.

This policy is for shared mathematical interfaces and recurring textbook
notation. It is not a requirement that every local lemma go through a full
textbook-definition, bridge, and Mathlib cycle.

## Term Boundaries

An interface bridge is a theorem-level translation between a textbook-facing
project object and a Mathlib-facing object or API. Its purpose is to let later
files use Mathlib without skipping the source-side interface.

Foundational support is different. It is maintenance planning for two project
hygiene problems: splitting super-long official output files and absorbing
former `obl_*` obligation output into stable support or parent files. It does
not by itself prove textbook fidelity, update the ledger, or replace Phase2
review.

Legacy files with names ending in `_bridge` are not automatically examples of
the Tao-style interface bridge pattern. Some are historical proof-debt support
or holding files. Treat each such file by its actual role and review evidence,
not by the word `bridge` in its name.

## What We Found Locally

The current Chapter 1-8 output is mostly close to this practice:

- many theorem statements and proofs use standard Mathlib forms
- project definitions are introduced when useful
- interface translation lemmas are used when the two ways must meet

Examples of standard Mathlib forms already used in built output:

- `MeasureTheory.Integrable`
- integrals and `lintegral`
- `Measure.map`
- `StieltjesFunction.measure`

Examples of project definitions already present:

- `expectation`
- `textbookIntegral`
- `textbookIntegrable`
- `StieltjesMeasureFunction`
- `rsIntegral`
- `improperRSIntegral`
- `totalVariationDistance`

Examples of existing legacy support, historical proof-debt support, or
foundation-like core files that are not automatically Tao-style interface
bridge examples:

- `rs_stieltjes_bridge`
- `cantor_distribution_bridge`
- `dirichlet_simplex_bridge`
- `gamma_beta_bridge`
- `tv_distance_core`

## Policy For Existing Files

Do not rewrite existing runnable Lean files only to make every file use one
style.

Keep the current Chapter 1-8 output unless a specific reuse problem appears.

When a later task needs to use an earlier theorem but the two statements use
different ways of writing the same idea, add a translation lemma.

If there are duplicate local definitions, do not do a large cleanup only for
neatness. Record the issue, and fix it when it blocks reuse.

## Policy For New Files

For a concept that is new to the project:

- define it first in the textbook style
- prove a small set of direct textbook properties
- if Mathlib has a matching concept, prove the translation theorem early
- after that, use the Mathlib version by default in later theorem statements

Use the project textbook definition directly in a later file only when one of
these is true:

- the task explicitly asks for that textbook definition
- an earlier theorem that must be reused is already stated with that project
  definition
- the project definition is the main object being studied
- no Mathlib version is available or convenient

When a proof or theorem must move between the textbook way and the Mathlib way,
add or import a translation lemma.

## Rule For Common Notation

Common notation such as `E[X]`, integrals, distributions, and Stieltjes
integrals should be recorded as mathematical context.

It should not automatically become a Lean import.

For example, a task that mentions `E[X]` should not automatically import
`def_6_7` only because expectation appears in the textbook text. The Lean file
should import `def_6_7` only if it actually uses the project `expectation`
definition or a theorem stated with that definition.

When a common notation does become a Lean dependency, record the reason in the
dependency decision trail.  The record should say whether the import was needed
because of an explicit text reference, a theorem stated with the project
definition, or an interface translation between the textbook interface and
Mathlib.

## Chapter 9 Guidance

For Chapter 9 onward:

- if an object is new in Chapter 9, introduce it first in textbook style
- prove its first basic properties in that style
- connect it to Mathlib as soon as there is a useful matching Mathlib form
- after the connection exists, prefer the Mathlib form in later theorem
  statements and proofs
- do not automatically import chapter 6 expectation definitions for every
  appearance of `E[X]`
- import or create a translation lemma when a theorem needs to connect textbook
  expectation with a Mathlib integral
- import or create a Stieltjes translation lemma when a theorem needs to connect
  distribution-function notation with a Stieltjes-measure integral

Short version:

First use the textbook definition. Then prove how it connects to Mathlib. After
that, use Mathlib for later work unless the textbook definition is the point of
the task.
