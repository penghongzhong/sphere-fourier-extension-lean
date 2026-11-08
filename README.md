# Sphere Fourier extension — Lean

[![Lean verification](https://github.com/penghongzhong/sphere-fourier-extension-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/penghongzhong/sphere-fourier-extension-lean/actions/workflows/verify.yml)

Lean sources accompanying **The sharp Fourier extension estimate for the sphere**.
The repository restores the complete source dependency closure from the archived
version 24 proof package, together with the current manuscript and its statement
correspondence. There are **2,310 proof modules**, plus `lakefile.lean`.

## Reproduce the verification

Use Lean **4.34.1**. The Mathlib revision is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612` in both Lake configuration files.

```sh
lake exe cache get
python3 scripts/verify.py --jobs 2
```

The default verification rebuilds every project proof module from source. Only
Mathlib and its external dependencies use their normal compiled cache. The run
then prints and audits the two manuscript statements, checks 78 declarations in
the manuscript correspondence and 82 declarations in the final proof audit, and
replays the two final statement modules with Lean's `leanchecker`.
The only permitted transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`. Source scanning also rejects proof placeholders, new axioms,
`native_decide` and the listed environment-modification commands.

Results are written to `build/Verification.json`; individual compile, statement,
axiom and replay logs are in `build/logs/`. GitHub Actions uploads the same
evidence for each run. A green workflow means that these checks completed for
the commit shown by that run. Files under `verification/archive/` are historical
evidence, not evidence for a new GitHub run.

For an interrupted local build, `python3 scripts/verify.py --jobs 2 --resume`
reuses objects only when their source/dependency fingerprints and object hashes
match the local checkpoint. CI deliberately performs the full rebuild.

## Main files

- [`ManuscriptStatement.lean`](ManuscriptStatement.lean): the two main statements
  with the actual sphere surface measure and Fourier kernel.
- [`ManuscriptCorrespondence.lean`](ManuscriptCorrespondence.lean): declarations
  corresponding to the manuscript's mathematical environments and proof steps.
- [`verification/LeanCorrespondence.md`](verification/LeanCorrespondence.md):
  the archived theorem/equation correspondence and editorial history.
- [`paper/Sphere_Fourier_Extension_ArXiv.tex`](paper/Sphere_Fourier_Extension_ArXiv.tex):
  the unchanged manuscript at migration.
- [`scripts/verify.py`](scripts/verify.py): reproducible compilation and audits.

The proof source hashes and manuscript hash are recorded in
[`provenance/MigrationBaseline.json`](provenance/MigrationBaseline.json).
The fresh verification report states whether they remain unchanged.

## Source provenance

The `OAI/` dependencies are taken from
[`openai/math`](https://github.com/openai/math) at commit
`4eaee87548250b2682affda7d05d947c05554bae`. The two principal external analytic
inputs used in the manuscript are the critical local estimate and the strict
mixed estimate. Their imported Lean proofs are included in this source build;
they are not introduced as additional analytic axioms.

The `LeanOscillatory/` dependency comes from
[`roos-j/lean-oscillatory`](https://github.com/roos-j/lean-oscillatory).
The `provenance/` manifests retain upstream file hashes, import-only pruning
records and port notes. Upstream copyright notices are preserved, and
[`UPSTREAM_LICENSE`](UPSTREAM_LICENSE) contains the upstream Apache 2.0 license.

迁移与调试优先保持原证明和论文不变。若后续发现需要更改数学陈述或证明，
应同时更新 Lean、论文及对应说明。编译通过与自然语言稿件的逐项对应分别记录。
