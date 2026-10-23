# The evidence calculus of mlir-trait-dialect

What the evidence operations of mlir-trait-dialect mean, and why each one is correct and needed, as a specification
and as machine-checked theorems. The operations are `trait.allege`, `trait.derive`, `trait.project`, `trait.witness`,
`trait.coerce` and `trait.proof`; the object is the operations as their descriptions and verifiers define them, not
the C++ that implements them.

- `SPEC.md`: one card per operation (its typing rule, its soundness case, its independence lemma, each naming the
  Lean theorem that proves it), the trait logic, the calculus, the theorems, and the findings about the dialect.
- The Lean 4 project (standard library only; Lean 4.35, Lake 5, both installed by `elan` from `lean-toolchain`):

      lake build

  `Defs.lean` (types, signature, evidence terms), `Logic.lean` (the trait logic and the denotation), `Calculus.lean`
  (the typing rules and the reading of a term to its root), then one file per theorem family: `Soundness.lean`,
  `Completeness.lean` (the cut: `trait.allege`), `Coherence.lean`, `Minimality.lean` (the independence lemmas, `witness
  compose` carried by `coerce`, `trait.proof` as the `let`), `Erasure.lean`, `Findings.lean` (machine-checked
  counterexamples to the statements that had to be weakened), `ReqAdmissible.lean` (a lemma of the specification
  refuted, with the hypothesis it lacks named).
- `PHASE_B_REPORT.md`: what is proved as stated, what is proved weakened and why, `#print axioms` for every theorem
  (only `propext`, `Classical.choice`, `Quot.sound`), and the findings.

The project has no `sorry`. It is kept apart from the dialect's repository because nothing builds against it; it
changes when the operations' meaning changes.
