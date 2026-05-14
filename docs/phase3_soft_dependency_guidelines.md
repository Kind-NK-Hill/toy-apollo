# Phase3 Soft Dependency Guidelines

## Purpose

This document defines how to select `soft imports` for `Problem` tasks.

## Core Principle

`soft imports` are soft only in how they are generated. They are not soft in execution semantics.

Once selected, they become part of:

- `hard dependencies ∪ soft imports`

That union is the final mandatory import set used later by:

- `phase 2` problem prompt packs
- `phase 3` Aristotle packaging

## Selection Scope

Only select from:

- `allowed_material_ids.json`

In the current workflow this means:

- chapter-local `def_*`
- chapter-local `thm_*`

Do not introduce ids outside that list.

## Selection Heuristics

Prefer materials that:

1. define the central objects appearing in the problem
2. provide reusable chapter-local closure or measurability theorems
3. are likely to reduce re-derivation inside the final candidate
4. make Aristotle or the downstream operator workflow likely to succeed without having to reconstruct obvious chapter facts

Avoid:

1. selecting the whole chapter by default
2. selecting materials only because they are nearby in the text
3. selecting remarks, intros, or unrelated examples
4. optimizing for the absolute smallest list when the problem clearly wants a direct supporting theorem

## Sufficient, Not Merely Minimal

The objective is a **minimal but sufficient** import set.

This means:

- use a small set of chapter-local supports
- but include direct closure/characterization theorems when the problem is clearly about proving a reusable property

Examples:

- if a problem asks whether operations on measurable functions remain measurable, prefer the direct arithmetic/measurability theorem, not only bare definitions
- if a problem asks about complex random variables under algebraic operations, prefer both the complex-RV definition and the relevant operations material
- if a problem is a direct limsup/liminf sequence exercise, the core limsup/liminf definition may be sufficient by itself

## Ordering

Within each problem's list, order selected ids by expected usefulness:

1. foundational definitions
2. direct supporting theorems
3. secondary helper theorems

## Output Format

The selection result must be JSON only.

It must:

- use problem ids as keys
- use ordered `list[str]` values
- avoid explanations in the JSON body

## Relationship to Hard Dependencies

`hard dependencies` come from the Phase1 plan and are not changed by this workflow.

This workflow only supplies:

- `candidate_snapshot.soft_imports`

Later pack/build steps must consume both sources together.
