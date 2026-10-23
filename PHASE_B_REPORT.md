(This report was written on 2026-10-23 when the project lived under mlir-trait-dialect's working tree as `proofs/`; the files are now the ones beside it in this repository, and its SPEC.md is `SPEC.md` here.)

# PHASE_B_REPORT.md: the Lean 4 proofs of the evidence calculus

Written 2026-10-23, about 05:50 Central, from the files at
`/home/jhoberock/dev/git/.wt/evidence-calculus/mlir-trait-dialect/proofs` (branch `evidence-calculus`; the
directory is untracked and nothing else in that repository is touched). The brief is BRIEF_PHASE_B.md beside
this file; the specification is SPEC.md (sections 3 to 7 for the statements, 8 for the findings' shape).
Standard library only; Lean 4.35.0, Lake 5. The nine files total 6967 lines: Defs.lean 403, Logic.lean 988,
Calculus.lean 1941, Soundness.lean 170, Completeness.lean 547, Coherence.lean 553, Minimality.lean 1284,
Erasure.lean 561, Findings.lean 520. SPEC.md section 1 now names, on each card, the Lean theorems below.

## 0. What is proved, and what is not

Proved, with no `sorry` (after B20's integration) and no axiom beyond Lean's own three (`propext`, `Classical.choice`, `Quot.sound`):

- Theorem 3, soundness, as SPEC.md 6.1 states it (`Trait.soundness`, through `Trait.hasType_valid` for any
  restriction on impl citations), with the closure lemma (`Trait.entails_valid`, `Trait.predEntails_valid`).
  Two of its stated hypotheses, DeclWF and G-WF, are not used by the proof.
- Theorem 4a and 4b as stated (`Trait.completeness`, `Trait.cut_admissible`), and the stage's form of the cut,
  a `trait.proof` written to the table and cited by a witness (`Trait.cut_proof`). DeclWF is not used.
- Theorem 6: the five independence lemmas as stated (`Trait.independence_derive`, `_project`, `_projRes`,
  `_refl`, `_coerce`); `compose` carried by `coerce`, one direction, as stated (`Trait.compose_derivable`);
  the let theorem as SPEC.md 6.4 states it, closed (`Trait.witness_is_let`, its root half
  `Trait.witness_is_let_root` for every term with no hypothesis); the inversion theorem for the where-entry
  arm of `trait.project` (D2) under H2 (`Trait.project_where_is_inversion`).
- The instantiation lemmas of SPEC.md 6.5 (`Trait.subst_types`, `Trait.subst_evidence`), restated so that they
  apply to the return a projection of a plain requirement reads, and H3 instantiated from them at a
  well-formed base (`Trait.returnsInstWF_of_returnsWF`).
- Theorem 7, erasure, weakened: at the limit of the fuel, for a primitive derivation whose (BIND) nodes stand
  at applications the denotation resolves, under an oracle that is sound and complete and a constructor law
  that forgets no argument (`Trait.erasure`, `Trait.erasure_core`, `Trait.coerce_value_erases`,
  `Trait.claim_denotes`). Three machine-checked refutations (`Trait.fixed_fuel_erasure_fails`,
  `Trait.erasure_needs_sel_complete`, `Trait.erasure_needs_primitive`) show section 7's statement false
  without the first three of those changes.
- Theorem 5, coherence, weakened: theorem 7's oracle hypotheses, the stage's two facts about the term
  (`Reads`: every projection's reading reaches a base, and every `proj_resolve` stands at an application the
  denotation resolves to a ground one), H2's groundness clauses (`Module.ProofsGround`) and H4 at the
  instance (`Module.ReturnsCitesOk`) (`Trait.coherence`, `Trait.root_serves`, `Trait.coherence_two_terms`,
  through the induction `Trait.reads_spec`). ReqDuty and the denotation of the claim are not used. Binder
  calls are outside the statement.
- The converse of the closure lemma for derivations by the equality rules alone
  (`Trait.entails_of_equational`); the skeleton's form of it is refuted (`Trait.entails_of_equational_as_stated_fails`).

Not proved:

- (REQ-ADMISSIBLE), `Trait.req_admissible` (Logic.lean:234-235): REFUTED after this report was first written
  (about 08:00 Central; finding B20 below, `Trait.req_admissible_fails` in ReqAdmissible.lean). No theorem
  depended on it: theorem 7 is stated on primitive derivations, where (REQ) has no instance at `G = []`, and
  theorem 5 reads a projected requirement through the impl's return instead. The `sorry` is gone from the
  project with the refutation in its place.
- Theorem 5 for a term whose reading passes through a binder call (`trait.method.call @requirement_i`):
  `Reads` has no `reqCall` case (finding B14).
- The formal refutation of theorem 5 without `Reads`' second fact (B11's program) and the three instances
  that force `Resolvable` and `KeepsArgs` in theorem 7 (B9) are stated in words and in the files' headers, not
  as Lean examples.

Mathlib was not needed. `lake build` from the project directory: "Build completed successfully (11 jobs)";
one warning `Logic.lean:234:8: declaration uses sorry`, two warnings that `hS` is not referenced
(Completeness.lean:502:75, :520:74).

## 1. The theorems, one by one

"Skeleton" is the statement of SPEC.md section 7; "Lean" is the statement in the file; "Difference" says what
changed and why. The scaffold step changed the vocabulary uniformly before any prover worked, and those
changes are not repeated per theorem: `ProofsWF` takes the restriction `Ok` and requires the proved
application ground; `root` is the relation `root M e i σ := ∃ ds, Root M e (i, σ, ds)` over the reading
`Root` (Calculus.lean:309), so a reading with no base has no root; (REQ-A) is `Deriv.reqA` and (REQ-CALL)
is `HasType.reqCall` and `Ev.reqCall`, by the pattern of `derive`; the skeleton's `full : Bool` and `Env`
became the predicates `Deriv.InEnv` and `Deriv.Primitive` on one inductive (Logic.lean:117, :124); the
constructor law is the normalizing function `ConLaw.rebuild` with stability under substitution as its one
axiom; an impl carries its returned evidence (`returns`, `binderReturns`).

### 1.1 Theorem 3, soundness (Soundness.lean, Calculus.lean, Logic.lean)

`Trait.soundness` (Soundness.lean:41): proved as stated.
Skeleton: `(hS : M.sig.DeclWF) (hP : ProofsWF L M) (hΓ : GammaWF M Γ) (he : e.allegeFree) (ht : HasType L M Ok Γ e c) : Valid L M.sig (Γ.map Claim.pred) c.pred`.
Lean: the same, with `hP : ProofsWF L M Ok`. It is the instance at `AnyImpl` of `Trait.hasType_valid`
(Calculus.lean:697), which concludes `Nonempty (Deriv L M.sig Ok (Γ.map Claim.pred) c.pred)` for any `Ok`:
the derivation cites the same impls the term does, which theorem 5 needs at `DenL`. The induction is
`Trait.hasType_deriv` (Calculus.lean:568): an outer strong induction on a bound above every proof the term
cites, which H2's clause "p cites q only for q < p" makes descend at every witness of a proof, and an inner
induction on the typing, because WIT-APP of a proof is not a sub-derivation of the term's typing.
Difference: none in the statement. `hS` and `hΓ` are not used (finding B3).

Closure lemma, `Trait.entails_valid` and `Trait.predEntails_valid` (Logic.lean:207, :222): proved as stated,
induction on `Entails`, `Classical.choice` to assemble the per-position derivations.

Its converse, `Trait.entails_of_equational` (Soundness.lean:70): weakened.
Skeleton: `(d : Deriv L S AnyImpl (E.map fun lr => Pred.eq lr.1 lr.2) (.eq a b)) (hEq : ∀ {P} (d' : Deriv L S AnyImpl (E.map ..) P), d'.Primitive) : Entails L E a b`.
Lean: `(d : Deriv L S AnyImpl (E.map fun lr => Pred.eq lr.1 lr.2) (.eq a b)) (hd : d.Equational) : Entails L E a b`,
where `Deriv.Equational` (Soundness.lean:51) is true of (HYP) on a seed, (REFL), (SYM), (TRANS), (CONG),
(CONG-P), (NORM), and false at (IMPL), (REQ), (REQ-A), (BIND), (CONV).
Difference: "every derivation under the seeds is primitive" became "this derivation uses the equality rules
alone", the docstring's own words ("derivable from the seeds by the equality rules alone"). The skeleton's
form is false: `Trait.entails_of_equational_as_stated_fails` (Soundness.lean:157), finding B1.

(REQ-ADMISSIBLE), `Trait.req_admissible` (Logic.lean:234): open, `by sorry`. Statement unchanged:
`(hS : S.DeclWF) (hD : S.ReqDuty L) : Valid L S Γ P -> ValidP L S Γ P`. See section 0.

### 1.2 Theorem 4, completeness and the cut (Completeness.lean)

`Trait.completeness` (:502): proved as stated.
Skeleton: `(hS : M.sig.DeclWF) (hP : ProofsWF L M) (d : Deriv L M.sig true AnyImpl Γ P) : ∃ M', M'.sig = M.sig ∧ ProofsWF L M' ∧ (elab L M d).allegeFree ∧ HasType L M' AnyImpl (Γ.map (⟨·, none⟩)) (elab L M d) ⟨P, none⟩`.
Lean: the same with `elabDeriv` for `elab` (a reserved word) and `ProofsWF L M' AnyImpl`. `M' = M`:
`elabL` (Calculus.lean:391) writes no proof, no `trait.allege` and no witness of a proof. The equality rules
(SYM)(TRANS)(CONG)(CONG-P)(NORM) and (CONV) become one `trait.coerce` over the equality leaves of the
subderivation, and the coerce's closure premise is proved from those leaves inside `Entails` itself
(`elabL_spec`, `seeds`, Completeness.lean:250, :214).
`Trait.cut_admissible` (:510): proved as stated.
`Trait.cut_proof` (:520): added, theorem 4b in the stage's form.
`(hS) (hP : ProofsWF L M AnyImpl) (hg : groundList as = true) (h : Valid L M.sig [] (.app t as)) (Γ) : ∃ M' p, M'.sig = M.sig ∧ ProofsWF L M' AnyImpl ∧ HasType L M' AnyImpl Γ (.witness (.proof p) (.app t as)) ⟨.app t as, some (.proof p)⟩`.
The derivation's term is written as a new `trait.proof` at the end of the table; every existing typing survives
the write (`hasType_append`, :478); the new proof cites nothing, so the table stays well founded.
Difference: none in the statements. `hS` is not used by any of the three (finding B4).

### 1.3 Theorem 5, coherence (Coherence.lean, Calculus.lean, Logic.lean)

`Trait.coherence` (Coherence.lean:524): weakened.
Skeleton: `(sel L M fuel) (hS : M.sig.DeclWF) (hD : M.sig.ReqDuty L) (hP : ProofsWF L M) (hSel : SelSound sel L M.sig fuel) (hC : M.sig.Coherent sel L fuel) (he : e.allegeFree) (ht : HasType L M (Den sel L M.sig fuel) [] e ⟨.app t as, π⟩) (hden : (denotePred sel L M.sig fuel (.app t as)).isSome) : ∃ i σ, root M e = some (i, σ) ∧ ServedBy sel L M.sig fuel (.app t as) i σ`.
Lean: `(sel L M) (hS : M.sig.DeclWF) (hD : M.sig.ReqDuty L) (hG : M.ProofsGround) (hR : M.ReturnsWF L AnyImpl) (hH4 : M.ReturnsCitesOk L (DenL sel L M.sig)) (hP : ProofsWF L M (DenL sel L M.sig)) (hL : L.KeepsArgs sel M.sig) (hSel : SelSoundL sel L M.sig) (hSelC : SelCompleteL sel L M.sig) (hC : M.sig.CoherentL sel L) (hRd : Reads sel L M e) (he : e.allegeFree) (ht : HasType L M (DenL sel L M.sig) [] e ⟨.app t as, π⟩) (hden : ∃ Q, DnP sel L M.sig (.app t as) Q) : ∃ i σ, root M e i σ ∧ ServedByL sel L M.sig (.app t as) i σ`.
Difference:
1. No fuel: `Den`, `ServedBy`, `SelSound`, `Coherent` are stated at the limit of the fuel (`DenL`,
   `ServedByL`, `SelSoundL`, `Sig.CoherentL`, Logic.lean:800-825), as theorem 7 is (B6). `CoherentL`'s
   argument clause is `All2 (DnEquiv sel L S) σ σ'` in place of `σ.map denote = σ'.map denote`.
2. Added `hSelC` (the oracle answers every served ground application) and `hL` (the constructor law forgets
   no argument): what theorem 7 needs, used by the COERCE case (B7, B9).
3. Added `hRd : Reads sel L M e` (Coherence.lean:164): the reading of every projection in the term reaches a
   base, and every `proj_resolve` stands at an application whose header arguments and GAT arguments denote
   to ground lists (theorem 7's `Deriv.Resolvable`, on the term). Without the second fact the statement is
   false (B11). The first is what the skeleton's `root(e) = (I, s)` presupposed; it is not a consequence of
   H2 and H3 as formalized, since two impls whose returns project one another through each other's derives
   satisfy `ReturnsWF` while their reading has no base (X/x3, X/x10).
4. Added `hR : M.ReturnsWF L AnyImpl` (the term form of H3, Calculus.lean:285: each impl's return is typed
   under its where entries at the requirement it discharges, allege-free), `hG : M.ProofsGround`
   (Calculus.lean:1204: a proof proves an application at its trait's arity, and its derive stands at ground
   arguments) and `hH4 : M.ReturnsCitesOk L (DenL ..)` (Calculus.lean:1806: every impl a return cites, at a
   well-formed base's arguments, has a header that denotes). From these the PROJECT-REQ case gets the
   instantiated return typed closed at the instantiated requirement (`Module.ReturnsInstWF`, derived by
   `Trait.returnsInstWF_of_returnsWF`, Calculus.lean:1828) (B13).
5. `hD` and `hden` are kept as the specification wrote them and are not used: a reading that reaches a base
   denotes its own claim, so `hden` is derived, and ReqDuty plays no role once the reading is given (B15).
6. Binder calls: `Reads` has no `reqCall` case, so a term whose reading passes through
   `trait.method.call @requirement_i` is outside the theorem (B14).

The proof is `Trait.reads_spec` (Coherence.lean:339), an induction on `Reads` rather than on the typing,
because the instantiated return a projection reads is not a sub-derivation of the term's typing. It
concludes, for an application claim, a base that serves it and is well formed, and for an equality claim
that the endpoints denote alike. Theorem 7's role in theorem 5 is that second conclusion: `erasure_core`
takes a primitive, resolvable derivation, which the typing of an equality term does not give (B12).

`Trait.root_serves` (:507): the same hypotheses, concluding `ServedByL sel L M.sig (.app t as) i σ` from
`Root M e (i, σ, ds)`.
`Trait.coherence_two_terms` (:538): the corollary SPEC.md 6.3 states, `∃ i σ₁ σ₂, root M e₁ i σ₁ ∧ root M e₂ i σ₂ ∧ All2 (DnEquiv sel L M.sig) σ₁ σ₂`,
with `Reads` for each term and `as` ground.

### 1.4 Theorem 6, minimality (Minimality.lean)

`Trait.independence_derive`, `_project`, `_projRes`, `_refl`, `_coerce` (:133, :198, :255, :307, :347): proved
as stated, each at the witness SPEC.md's card names, by induction on the typing: without the operation, every
claim a term can state in the witness module has a shape the goal lacks.
`Trait.compose_derivable` (:367): proved as stated; the converse's failure is Findings.lean's F3 example (:162).

`Trait.witness_is_let` (:1237): proved as SPEC.md 6.4 states it.
Skeleton: `(hP : ProofsWF L M) (ht : HasType L M Ok Γ e c) : HasType L M Ok Γ (e.inlineProofs M) c.strip ∧ root M (e.inlineProofs M) = root M e`.
Lean: `(hS : M.sig.DeclWF) (hP : ProofsWF L M Ok) (he : e.allegeFree) (ht : HasType L M Ok [] e c) : HasType L M Ok [] (e.inlineProofs M) c.strip ∧ ∀ i σ, root M (e.inlineProofs M) i σ ↔ root M e i σ`.
Difference: closed (`Γ = []`), as 6.4 says ("a closed allege-free term"); the skeleton's any-`Γ` form fails
at a proven hypothesis `^0 : <P by @p>`, which is its own inlining and keeps its citation (Findings.lean:508,
B19). `hS` and `he` were added by the scaffold and are not used (an allegation is its own inlining and keeps
its claim). The root half, `Trait.witness_is_let_root` (:1217), is proved for every term under no hypothesis,
through a relation `Sim` (:574) between a term and its inlining at any fuel and two lemmas (a reading of the
term is a reading of its inlining to a related base, and back). The two conditions the Minimality prover
first needed, `hnest`/`hnP` (no projection whose operand is a projection, in the term or in a proof body) and
`hOk` (the restriction admits every unconditional impl at no arguments), dropped out when the integration
step applied definition requests D1 and D3 (section 4; findings B17, B18).

`Trait.project_where_is_inversion` (:1252): stated and proved; the skeleton had a comment in its place.
Lean: `(hP : ProofsWF L M Ok) (ht : HasType L M Ok Γ e ⟨.app t as, some (.proof p)⟩) (htr : t < M.sig.traits.length) (hder : M.proofDerive p = some (i, σ, ds)) (hj : j < ds.length) (hc : HasType L M Ok [] (ds.getD j default) c) : HasType L M Ok Γ (ds.getD j default) c ∧ (Root M e (i, σ, ds) -> ∀ r, Root M (.project e (M.sig.traits[t].reqs.length + j)) r ↔ Root M (ds.getD j default) r)`.
`hP` (H2) was not in the prover's first statement and is needed: the projection index is read by `Root`
against the requirement list of the trait the cited proof's derive implements, which is the written trait
`t` only when the proof's body is typed at the application it proves (Findings.lean:448 refutes the statement
without it; B5). `hj` is not read by the proof.

### 1.5 The instantiation lemmas of SPEC.md 6.5 (Calculus.lean)

`Trait.subst_types` (:1419): proved, restated.
Skeleton: `(hS : M.sig.DeclWF) (ht : HasType L M Ok Γ e c) : HasType L M Ok (Γ.map (Claim.subst σ)) (e.substTy σ) (c.subst σ)`.
Lean: `(σ) (hS) (hP : ProofsWF L M Ok) (hG : M.ProofsGround) (hOk : ∀ i τ, Ok i (Subst.ofList τ) -> Ok i (Subst.ofList (substList σ τ))) : HasType L M Ok Γ e c -> ClaimsWF M.sig Γ -> HasType L M Ok (Γ.map (Claim.subst σ)) (e.substTy σ) (c.subst σ)`.
Difference: `hP` and `hG`, because the proof table is not cloned, so a where-entry projection off a proof
keeps its claim and that claim must be ground; `ClaimsWF M.sig Γ` (:1178; every hypothesis is a claim the
claim type verifier admits: no citation on an equality, an application at its trait's arity) for the same
reason at the hypotheses; `hOk`, because a restriction need not be stable under substitution. `hOk` is
trivial at `AnyImpl` and false at `DenL` (a header `V[T[a0]::N]` denotes at the variable, as a standing
projection, and not at an unserved ground instance), so the `DenL` restriction on the instantiated term is
re-established afterwards by `Trait.hasType_strengthen` (:1723) from H4 read off the term (`Ev.CitesOk`,
:1666) and H2 under `DenL`.

`Trait.subst_evidence` (:1554): proved, restated.
Skeleton: `(ht : HasType L M Ok Γ e c) (hd : ∀ k (hk : k < Γ.length), HasType L M Ok Δ (fs k) Γ[k]) : HasType L M Ok Δ (e.substHyp fs) c`.
Lean: `(fs) : HasType L M Ok Γ e c -> (∀ k (hk : k < Γ.length), ∃ c', HasType L M Ok Δ (fs k) c' ∧ c'.Replaces Γ[k]) -> ∃ c', HasType L M Ok Δ (e.substHyp fs) c' ∧ c'.Replaces c`,
where `c'.Replaces c` (:1539) says the predicates agree and either the citation is `c`'s or `c` has none and
`c'` is well formed.
Difference: a derive's operands are typed with any citation (`πs j`) where the return's hypotheses are typed
with none, so the skeleton's exact-claim form does not apply to the return `Root.projReq` reads
(`T/coerce_claim_respell.mlir`'s shape); "under any citation" alone is not provable either, since
PROJECT-WHERE reads its operand's citation and the operands of compose and coerce must be uncited.

`Trait.returnsInstWF_of_returnsWF` (:1828): added.
`(hS) (hP : ProofsWF L M Ok) (hG : M.ProofsGround) (hR : M.ReturnsWF L AnyImpl) (hH4 : M.ReturnsCitesOk L Ok) : M.ReturnsInstWF L Ok`:
at a well-formed base `(I, σ, ds)` (`RootWF`, :1794), the return for the `k`-th plain requirement with `σ`
for the impl's labels and `ds` for its hypotheses is a closed allege-free term for `rho_k[h][σ]` cited within
`Ok` (`Module.ReturnsInstWF`, :1815). This is what theorem 5's PROJECT-REQ case reads; `hH4` is the new
hypothesis (B13).

### 1.6 Theorem 7, erasure (Erasure.lean, Logic.lean)

`Trait.erasure` (Erasure.lean:86): weakened.
Skeleton: `(sel L S fuel) (hS : S.DeclWF) (hD : S.ReqDuty L) (hSel : SelSound sel L S fuel) (hC : S.Coherent sel L fuel) (h : ValidD sel L S fuel [] (.eq a b)) (d : Ty) (ha : denote sel L S fuel a = some d) : denote sel L S fuel b = some d`.
Lean: `(sel L S) (hL : L.KeepsArgs sel S) (hSel : SelSoundL sel L S) (hSelC : SelCompleteL sel L S) (hC : S.CoherentL sel L) (h : ValidGround sel L S (.eq a b)) (d : Ty) (ha : Dn sel L S a d) : Dn sel L S b d`,
the instance of `Trait.erasure_core` (Logic.lean:980), which concludes two-sidedly, `DnEquiv sel L S a b`,
that is `∀ d, Dn sel L S a d ↔ Dn sel L S b d` (`Trait.erasure_equiv`, Logic.lean:937, is the induction).
Difference:
1. The denotation is at the limit of the fuel: `Dn t d := ∃ f, denote sel L S f t = some d` (Logic.lean:474),
   monotone in the fuel (`Trait.denote_mono`, :396). At one fixed fuel the statement is false
   (`Trait.fixed_fuel_erasure_fails`, Erasure.lean:391; B6). `denote` with its fuel stays the computable
   function (Logic.lean:256).
2. `SelCompleteL` added (Logic.lean:816): an oracle that declines a served ground application satisfies
   `SelSound` and refutes the statement (`Trait.erasure_needs_sel_complete`, Erasure.lean:242; B7).
3. `ValidGround` (Logic.lean:925) in place of `ValidD`: a derivation at `DenL` that is primitive
   (`Deriv.Primitive`) and whose every (BIND) stands at an application and GAT arguments that denote to
   ground types (`Deriv.Resolvable`, :913). Primitive, because with (REQ) admitted the statement is false:
   H3 discharges a requirement in the full signature, through impls whose headers need not denote
   (`Trait.erasure_needs_primitive`, Erasure.lean:553; B8). Resolvable, with `ConLaw.KeepsArgs`
   (Logic.lean:746), because `[[.]]` is partial where the equality rules are total (B9).
4. `hS : S.DeclWF` and `hD : S.ReqDuty L` dropped: not needed once the derivation is primitive; H3's only
   role in SPEC.md 6.6 was (REQ-ADMISSIBLE) (B10).
`Trait.coerce_value_erases` (Erasure.lean:111): the value arm of `trait.coerce`.
`(hL hSel hSelC hC) (E) (hE : ∀ l r, (l, r) ∈ E -> ValidGround sel L S (.eq l r)) (h : Entails L E a b) (d) (ha : Dn sel L S a d) : Dn sel L S b d`,
by induction on `Entails` (`entails_dnEquiv`, :94), not through Logic.lean's `entails_valid`, whose
`Nonempty` output hides the derivation (B16).
`Trait.claim_denotes` (:122): `∀ Q, DnP sel L S (.app t bs) Q ↔ DnP sel L S (.app t as) Q` for arguments
pairwise `ValidGround`-equal; the skeleton's one-sided `isSome` premise is not needed.

## 2. `#print axioms`

Command, from the project directory after `lake build`:
`export PATH=$HOME/.elan/bin:$PATH && lake env lean /tmp/claude-1000/-home-jhoberock-dev-git-screech-fable/43f1b9ea-b545-476e-8bcc-8689b5f6108f/scratchpad/Axioms2.lean`,
the scratch file importing Soundness, Completeness, Coherence, Minimality, Erasure and Findings and printing
the axioms of every theorem and of the shared lemmas they rest on (exit 0). Output, verbatim, run 2026-10-23
05:47 Central; the integration step's run of 05:42 over the twenty-nine of these names it listed printed the
same lines:

```
'Trait.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.hasType_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.hasType_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.entails_valid' depends on axioms: [propext, Classical.choice]
'Trait.predEntails_valid' depends on axioms: [propext, Classical.choice]
'Trait.entails_of_equational' depends on axioms: [propext]
'Trait.req_admissible' depends on axioms: [propext, sorryAx]
'Trait.completeness' depends on axioms: [propext, Quot.sound]
'Trait.cut_admissible' depends on axioms: [propext, Quot.sound]
'Trait.cut_proof' depends on axioms: [propext, Quot.sound]
'Trait.coherence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.coherence_two_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.root_serves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.reads_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.independence_derive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.independence_project' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.independence_projRes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.independence_refl' depends on axioms: [propext, Quot.sound]
'Trait.independence_coerce' depends on axioms: [propext, Quot.sound]
'Trait.compose_derivable' depends on axioms: [propext]
'Trait.witness_is_let' depends on axioms: [propext, Quot.sound]
'Trait.witness_is_let_root' depends on axioms: [propext, Quot.sound]
'Trait.project_where_is_inversion' depends on axioms: [propext, Quot.sound]
'Trait.subst_types' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.subst_evidence' depends on axioms: [propext, Classical.choice]
'Trait.returnsInstWF_of_returnsWF' depends on axioms: [propext, Classical.choice, Quot.sound]
'Trait.hasType_strengthen' depends on axioms: [propext, Quot.sound]
'Trait.hasType_weaken' depends on axioms: [propext]
'Trait.hasType_unique' depends on axioms: [propext, Quot.sound]
'Trait.root_unique' depends on axioms: [propext]
'Trait.erasure' depends on axioms: [propext, Quot.sound]
'Trait.coerce_value_erases' depends on axioms: [propext, Quot.sound]
'Trait.claim_denotes' depends on axioms: [propext, Quot.sound]
'Trait.erasure_core' depends on axioms: [propext, Quot.sound]
'Trait.erasure_equiv' depends on axioms: [propext, Quot.sound]
'Trait.DnEquiv_bind' depends on axioms: [propext, Quot.sound]
'Trait.denote_mono' depends on axioms: [propext, Quot.sound]
'Trait.erasure_needs_sel_complete' depends on axioms: [propext, Quot.sound]
'Trait.fixed_fuel_erasure_fails' depends on axioms: [propext, Quot.sound]
'Trait.erasure_needs_primitive' depends on axioms: [propext, Quot.sound]
'Trait.entails_of_equational_as_stated_fails' depends on axioms: [propext, Quot.sound]
```

Reading: every theorem of section 1 rests on Lean's own three axioms at most. The one declaration carrying
`sorryAx` is `Trait.req_admissible`; no other declaration lists it, so nothing proved depends on it.
`Classical.choice` enters where a derivation is assembled from per-position derivations hidden in `Nonempty`
(the closure lemma, `hasType_deriv`) and where citations given one by one are turned into a function of the
position (`exists_cites`, used by `subst_types` and `subst_evidence`); the theorems that use neither are free
of it (completeness, the let theorem, erasure). The refutations in Findings.lean are anonymous `example`s,
so `#print axioms` has no name to take for them; the build checks them.

Sorry census (the word `sorry` outside `--` and `/- -/` comments and strings): Logic.lean 1 (line 235, the
body of `req_admissible`); Calculus.lean, Coherence.lean, Completeness.lean, Defs.lean, Erasure.lean,
Findings.lean, Minimality.lean, Soundness.lean 0 each (Defs.lean line 8 mentions the word inside its header
comment). Total 1.

## 3. Findings

Shape as SPEC.md section 8: severity; the defect in one sentence; evidence; what the calculus does with it.
"Applied" means the integration step changed the definition (section 4), so the finding is about the skeleton
as phase A wrote it and is closed in the files. The provers' labels are in parentheses.

**B1 (medium; theorem statement).** The converse of the closure lemma is false under the skeleton's
hypothesis: `Deriv.bind` with no premises is primitive and derives `hdr_I[σ]::N<gs> = bind_I(N)[..]` from no
seeds, while `GC` reads no binding (SPEC.md 5.2, "no binding read"). Evidence: `entails_of_equational_as_stated_fails`
(Soundness.lean:157) over `refuteSig` (:111: one trait with an associated type and no requirements, one
unconditional impl binding it to another constructor): every closed derivation under it is primitive
(`refuteSig_all_primitive`, :115), (BIND) derives `T[K0]::N = K1` from `E = []`, and `Entails freeAlgebra []`
relates a type to itself only (`entails_nil_free`, :133). What the calculus does: the converse is restated for
derivations by the equality rules alone (`Deriv.Equational`), which is what SPEC.md 6.1 ("the closure decides
this fragment") and the exactness claim for WIT-COMPOSE and COERCE mean; a (BIND) fact reaches a compose or
coerce only as a seed, through a `trait.witness proj_resolve` operand. No operation changes.
Program: card 4's WIT-PROJ independence case. `trait.trait @A { type Item }`, `trait.impl @A for i64 { Item = i32 }`,
`G = []`: `trait.witness proj_resolve @A[i64]::Item resolves i32 by @A_i64 : (A[i64]::Item = i32)` verifies,
while `trait.witness compose(...)` and `trait.coerce ... via (...)` with no equality premise cannot reach
`A[i64]::Item = i32` (Q/p26, Q/p30, Q/p34 refused).

**B2 (low; skeleton/definition; applied).** Theorem 3 at a general restriction `Ok` was unprovable because
`HasType.witImpl` carried no `Ok i (Subst.ofList [])` while `Deriv.impl` requires one; every other
impl-citing typing rule (`derive`, `projRes`) carries it. Under `Ok = DenL` (H4) this is the question whether
an unconditional impl's header denotes, which the witness rule did not ask. What the calculus does:
definition request D1, applied (Calculus.lean:237); `hasType_valid` is then proved for every `Ok`.
Program: `trait.witness @I for hdr_I` with `I` unconditional (T/derive_of_an_unconditional_impl_is_the_impl_itself.mlir,
P/s6), where `hdr_I` writes a projection no impl serves (the shape of V/v3, J/j1): the witness verifies, and a
derivation restricted to denoting citations has no (IMPL) step for it.

**B3 (low; the spec's hypothesis list).** Theorem 3 needs neither G-WF nor DeclWF. SPEC.md 6.1 states it
under "H1, H2, G-WF"; the proof uses H2 only (`hS` and `hΓ` are unused hypotheses of `soundness` and
`hasType_valid`, kept because the statement is the spec's; the unused-variable linter is silenced for those
two declarations). Soundness speaks of a claim's predicate, never its citation: (HYP) reads the predicate of
a hypothesis whatever its citation names, and PROJECT-WHERE concludes the operand's own closed type, valid
from `S` alone. G-WF is where the root of a term is read (theorem 5), which is F1's territory. What the
calculus does: section 6.1's hypothesis list can drop G-WF; nothing about the operations changes.
Program: W/f1, P/s5: a parameter `<@T[i32] by @T_i64>` verifies; the predicate `T[i32]` is valid from the
hypothesis regardless of the wrong citation, and only dispatch (F1) is wrong, which is theorem 5's concern.

**B4 (observation).** Theorem 4 needs no declaration well-formedness: `hS : M.sig.DeclWF` is not used by
`completeness`, `cut_admissible` or `cut_proof` (the two linter warnings at Completeness.lean:502, :520;
`cut_admissible` passes it through). The only module hypothesis the three proofs read is H2
(`ProofsWF L M AnyImpl`), and only to carry it to `M'`. SPEC.md 6.2 states theorem 4 with no hypothesis beyond
the derivation; the Lean statements strengthen it harmlessly with `hS` and `hP`, and `hS` could be dropped
from section 7's statements of 4a and 4b. No program: nothing is refuted.

**B5 (observation; theorem statement).** The inversion theorem (D2) reads through H2, which the first
statement omitted: `project_where_is_inversion` identifies the index `|R_T| + j`, written against the trait
`t` of the operand's claim, with the position `Root.projWhere` reads, which is against the requirement list
of the trait the cited proof's derive implements. The two agree when the proof's body is typed at the
application it proves (H2's typing clause). The dialect enforces this clause (a `trait.proof` body's returned
claim is checked against the proved application, D/TraitOps.td:1572-1702), so no IR program reaches the gap.
What the calculus does: `hP : ProofsWF L M Ok` added; the needed lemma is `trait_of_proofDeriveAux`, with
`proofCite_rooted` carrying the trait through coerces (F7 moves the arguments, not the trait).
Program (outside H2; Findings.lean:448): traits `T0` (no requirements) and `T1` (two requirements); impl
`I = impl T1 for () where W` returning two terms; the table `[p0 : T0[] with body derive I [] [refl i32]]`,
ill typed since the body derives `T1[]`. For `e := witness @p0 for T0[]`, `j = 0`, the operand `refl i32`:
`Root (project e 0) r` reads `I`'s return at `0 < |R_T1| = 2` by `Root.projReq`, while `Root (refl i32) r`
never is; conversely `Root.projWhere` needs `|R_T1| ≤ 0`. Both directions fail.

**B6 (high; theorem 7 as stated in section 7 is false at a fixed fuel) (F-E1).** The fixed-fuel denotation
`denote sel L S fuel` is not a congruence: `Sig.Coherent` at fuel `f` equates the oracle's impl arguments
and the citation's at fuel `f`, but a (BIND)'s binding reads those arguments one or more constructors deep,
with less fuel; a sound oracle and a coherent signature admit a valid closed (BIND) equality with the left
side defined at fuel 4 and the right side undefined. The stage is safe (the barrier refuses a coerce whose
endpoint does not resolve, T/invalid_coerce_undischarged_at_barrier.mlir; the exit walk refuses standing
ground projections), so this is a defect of the Lean statement, not of the dialect; F16 says the 128 bound
is a stage fact. What the calculus does: theorem 7 and theorem 5 are stated at the limit of the fuel (`Dn`),
where `denote` is monotone (`denote_mono`); definition request D6, applied.
Program: Erasure.lean `fixed_fuel_erasure_fails` (:391), machine-checked, over `fuelSig` (:254): trait `T { type Out }`
with `impl<X> T for X { type Out = K<K<X>> }`; trait `U { type Item }` with `impl U for i64 { Item = i32 }`
and `impl U for i32 { Item = i32 }`; oracle `fuelSel` answering `T[i32] ↦ (T_gen, [i32])`, `U[i64] ↦ U_i64`,
`U[i32] ↦ U_i32`; `x = U[U[i64]::Item]::Item` (denotes to `i32` at fuel 3, not below). At fuel 4,
`[[T[x]::Out]] = K<K<i32>>` and `[[K<K<x>>]] = none`, while `T[x]::Out = K<K<x>>` is `ValidD` by (BIND) at `[x]`.
DeclWF, ReqDuty, SelSound and Coherent at fuel 4 are proved for the instance (:274-:320).

**B7 (medium; H4 lacks the oracle's completeness) (F-E2).** `SelSound` constrains positive answers only; an
oracle that declines a served ground application satisfies it, and then `[[T[i32]::Out]]` is undefined while
(SYM) of (BIND) proves `i32 = T[i32]::Out`, refuting theorem 7 as stated with one trait and one impl.
`resolveImplFor` answers whenever exactly one satisfiable candidate exists (D/ImplResolution.cpp:148-170,
374-400) or refuses the program; that completeness is part of what theorems 5 and 7 rest on and sections 6
and 7 did not state it. What the calculus does: `SelCompleteL` (the oracle answers every served ground
application) is a hypothesis of `erasure_core`, `erasure`, `coherence`; definition request D7, applied.
Program: Erasure.lean `erasure_needs_sel_complete` (:242), machine-checked: `oneImplSig` (:181) = trait
`T { type Out }`, `impl T for i32 { Out = i32 }`; `sel := fun _ => none`; fuel 2; `a = i32`,
`b = T[i32]::Out`; derivation `symm (bind T_i32 [])`; `[[a]] = i32`, `[[b]] = none`.

**B8 (high; (REQ-ADMISSIBLE) does not transfer into the denotable fragment; theorem 7 with (REQ) admitted is
false) (F-E3).** SPEC.md 6.6 says "(REQ) absent under H3 (4.3)", relying on (REQ-ADMISSIBLE). H3
(`Sig.ReqDuty`) discharges each impl's requirement with a primitive derivation at `AnyImpl`, in the full
signature, which may cite an impl whose header does not denote; instantiating that derivation at the (IMPL)
node's arguments leaves the denotable fragment, and the equality a (REQ) node concludes can be false under
`[[.]]` although `Coherent`, `SelSound`, `DeclWF` and `ReqDuty` are all satisfied. A `ReqDuty` restricted to
`Den` would not repair it: `Den` is not stable under substitution (a header `T[U[a_0]::Item]` denotes at the
variable and not at `a_0 := i64` when no impl serves `U[i64]`), so the instantiation lemma of 6.5 cannot
carry it. In the dialect this is the F13 shape: the verifier admits the requirement evidence (X/x9, X/x3,
X/x10) and only the stage refuses ("resolves its sides to i32 and i64"; "has no base"). What the calculus
does: theorem 7 takes a primitive derivation (`Deriv.Primitive`), where (REQ) and (REQ-A) have no instance at
`G = []` (`Deriv.not_inEnv_nil`); `Sig.ReqDuty` and `Sig.DeclWF` are then unused by theorem 7; definition
request D8, applied.
Program: Erasure.lean `erasure_needs_primitive` (:553), machine-checked, over `reqSig` (:406): trait
`Has { type Out; Has[Self]::Out = i64 }`, trait `U { type Item }`; `impl Has for i32 { Out = i32 }` (Has_i32),
`impl Has for U[i64]::Item { Out = i64 }` (Has_bad), `impl U for i64 { Item = i32 }` (U_bad2); oracle `reqSel`
answers `Has[i32] ↦ Has_i32` and declines `U[i64]`. ReqDuty is satisfied: Has_i32's requirement
`Has[i32]::Out = i64` is derived primitively by (TRANS) of (CONG-P) over (SYM)(BIND U_bad2) and (BIND Has_bad)
(`reqD5`); Has_bad's by (BIND Has_bad). Coherent at fuel 3 is satisfied (Has_bad's header never denotes). The
`ValidD` derivation `req (impl Has_i32 [])` gives `Has[i32]::Out = i64`; `[[Has[i32]::Out]] = i32 ≠ i64 = [[i64]]`.
Dialect twin: the X/x9 program of SPEC.md F13 with the alleged requirement replaced by this two-impl discharge;
the stage refuses it at exit, the verifier accepts it.

**B9 (medium; `[[.]]` is partial where the equality rules are total) (F-E4).** `denote` resolves ground
projections only and is undefined where a projection no impl serves stands inside the type, while (BIND) and
(NORM) prove equalities through such positions. Three valid closed equalities in the denotable fragment with
one side denoting and the other not, or differently: (a) `T[a_3]::Out = a_3` by (BIND) through a generic impl
binding `Out = Self` at the variable `a_3` (`Den` is satisfied: `T[a_3]` denotes to itself);
`[[T[a_3]::Out]]` is the standing projection, `[[a_3]] = a_3`; (b) `T[i32]::Out<u> = i64` by (BIND) through
a binding `Out<X> = i64` at a GAT argument `u` no impl serves; `[[i64]]` defined, the left side undefined;
(c) `K(u) = i32` by (NORM) under a constructor law `K(x) = i32` for every `x`, `u` as before. The stage never
reaches erasure with such a type standing (the exit walk, D/Passes.cpp:1962-1990; the barrier checks both
endpoints). What the calculus does: `Deriv.Resolvable` (every (BIND) at an application and GAT arguments that
denote to ground types) and `ConLaw.KeepsArgs` (a law's answer denoting makes its arguments denote; true of
the free algebra, `freeAlgebra_keepsArgs`, and of coop's Uniform collapse, whose answer keeps its argument)
are hypotheses of theorems 7 and 5. Whether every ground closed equality the stage accepts has a Resolvable
derivation is not proved.
Program: instances (a), (b), (c) above, each a one-trait one-impl signature; (c) with a two-constructor
ConLaw. Not written as Lean examples (the file's three refutations cover the statement's falsity); the owner
may want them in Findings.lean.

**B10 (observation; what theorem 7 does not need) (F-E5).** Once the derivation is primitive, theorem 7 uses
neither `Sig.DeclWF` nor `Sig.ReqDuty`: the (BIND) case needs only the lengths `|σ| = arity` (from the
derivation and `ServedBy`) and `|gs| = |labels|`, and substitution respects the denotation without
well-formedness of the binding. H3's only role in 6.6 was (REQ-ADMISSIBLE), which B8 shows does not apply
inside the denotable fragment. Program: Erasure.lean `erasure`, `coerce_value_erases`, `claim_denotes` take
no `hS`, `hD`.

**B11 (medium; theorem 5 as stated) (F-C1).** A closed term at a non-ground claim may be coerced through a
(BIND) at an unresolved application; its root serves nothing of the claim. SPEC.md 6.3 and the skeleton state
theorem 5 for `M; [] |- e : T[a]` with `[[T[a]]]` defined and no groundness on the term. In the model `G = []`
does not make the term's types ground: `trait.derive` and `trait.witness proj_resolve` are typeable at `σ`
containing `!trait.poly<i>` (`DenL` only asks the header to denote, and a variable denotes to itself), and a
`proj_resolve` at such `σ` states `T[a0]::N = B[a0]` whose left side `[[.]]` leaves standing. Through COERCE
the root then serves a different denotation than the claim. The exit walk refuses standing ground
projections (F17) and monomorphization leaves no variable, so the dialect never dispatches on such a term.
What the calculus does: the theorem is stated on terms satisfying `Reads` (every `proj_resolve` at an
application and GAT arguments that denote to ground lists), which is `Deriv.Resolvable` of theorem 7 moved
onto the term. A formal refutation of the un-weakened statement (the program below, with its oracle and
`CoherentL`) was not written and belongs in Findings.lean.
Program:
```
trait.trait @T { assoc N }                                   // arity 1
trait.trait @V                                               // arity 2
trait.impl<a> @T for a { N = i32 }                           // @T_all
trait.impl<b> @V for (b, !trait.proj<@T[b],"N">)             // @V_all; coherent: the servers of a ground
                                                             //   V[x, y] are @V_all at σ0 with [[σ0]] = x
%d = trait.derive @V[!trait.poly<0>, !trait.proj<@T[!trait.poly<0>],"N">] from @V_all[!trait.poly<0>] given()
%e = trait.witness proj_resolve @T[!trait.poly<0>]::N = i32 by @T_all[!trait.poly<0>] given()
%c = trait.coerce %d : .. to <@V[!trait.poly<0>, i32]> via (%e)
```
In the model `%c` is closed, allege-free, typed at `V[a0, i32]` under `DenL` (both headers denote),
`V[a0, i32]` denotes to itself, `root(%c) = (V_all, [a0])`, and `V_all` at `[a0]` does not serve `V[a0, i32]`:
`[[V[a0, T[a0]::N]]] = V[a0, T[a0]::N] ≠ V[a0, i32]`. `Reads` fails at `%e`: `[a0]` denotes to `[a0]`, not ground.

**B12 (observation; proof architecture) (F-C2).** Theorem 7 on derivations does not give theorem 7 on the
equality operands of a coerce; the term statement needs its own induction. SPEC.md 6.3's COERCE case says the
two applications denote alike "by theorem 7 on the cited equalities". `erasure_core` takes `ValidGround`, a
primitive derivation whose (BIND)s resolve. The derivation `hasType_valid` builds for a closed equality term
is neither in general: a `trait.project` at an equality requirement of a derived application is (REQ) on
(IMPL), non-primitive at `G = []` (`Deriv.not_inEnv_nil`), and `req_admissible` (sorry) would return
`ValidP` at `AnyImpl` without `Resolvable`. Coherence.lean therefore proves the term statement directly,
every closed allege-free equality term the reading reaches has endpoints that denote alike (`reads_spec`'s
second conclusion), by the same induction on `Reads` as the application statement, since a projected equality
requirement reads the impl's return exactly as a projected application does. The cards are unchanged;
theorem 7's role in theorem 5 is through `reads_spec`, not `erasure_core`.
Program:
```
trait.trait @Has { assoc Out; requirement Has[Self]::Out = i64 }
trait.impl @Has for i32 { Out = i64 }   // returning trait.witness proj_resolve @Has[i32]::Out = i64 by @Has_i32
%h = trait.derive @Has[i32] from @Has_i32 given()
%q = trait.project %h[0] : <@Has[i32]::Out = i64>          // (REQ) on (IMPL): not primitive at G = []
%c = trait.coerce %v : <@U[!trait.proj<@Has[i32],"Out">]> to <@U[i64]> via (%q)
```
`erasure_core` does not apply to `%q`'s derivation; `reads_spec` reads `%q` to Has_i32's return and concludes
`[[Has[i32]::Out]] = [[i64]]`.

**B13 (medium; H3 instantiated) (F-C3; applied, with one residual hypothesis).** The instantiation lemmas of
SPEC.md 6.5, as the scaffold first stated them, did not type the return a PROJECT-REQ reads.
`Root.projReq` reads `((I.returns[k]).substTy (ofList σ)).substHyp (hypsOf ds)`; typing it from `ReturnsWF`
needs (subst-types) at `σ` and (subst-evidence) at `ds`, and both were mis-stated for this use:
`subst_evidence` required each `ds j` typed at exactly `⟨W_j[σ], none⟩` while `HasType.derive` types the
operands at `⟨W_j[σ], πs j⟩` with any citation (`T/coerce_claim_respell.mlir`'s shape); `subst_types`'s `hOk`
is false at `DenL` (an impl header writing a projection, J/j1, denotes at a variable and need not at its
instance). The dialect's (beta-req) inlines exactly this instantiated return (D/TraitOps.cpp:1600-1648;
D/Specialization.cpp:359-378). What the calculus does: definition request D10, applied: `subst_evidence` takes
and returns claims up to `Claim.Replaces`; `subst_types` keeps `hOk` and the `DenL` restriction is
re-established by `hasType_strengthen`; `returnsInstWF_of_returnsWF` derives `ReturnsInstWF` from
`ReturnsWF L AnyImpl`, H2 (`ProofsWF` at `DenL`, `ProofsGround`) and one new hypothesis, `ReturnsCitesOk`
(H4 at the instance: the impls a return cites denote at a well-formed base's arguments). That hypothesis is
not a consequence of H3 and the base: a return `derive Baz[T[a0]::N] from @Baz_all[T[a0]::N]` types
generically, and at the base `[i32]` of a served `Foo[i32]` its citation `Baz_all[T[i32]::N]` denotes only
where an impl of `T` serves `i32`, which nothing about `Foo`'s impl says; the stage refuses the standing
projection at exit (F17). Theorem 5 therefore takes `hR : ReturnsWF L AnyImpl` (the spec's H3 on terms,
now doing its work) together with `hG : ProofsGround` and `hH4 : ReturnsCitesOk`.
Program:
```
trait.trait @W
trait.trait @T { requirement @R[Self] }
trait.impl @W for i32                                        // @W_i32
trait.proof @pW : @W[i32] { derive from @W_i32 }
trait.impl<a> @T for a where @W[a]                           // @T_cond, returning trait.project ^0[..] through the where argument
%w = trait.witness @pW for @W[i32]                           // proven operand: <@W[i32] by @pW>
%d = trait.derive @T[i32] from @T_cond[i32] given(%w)        // DERIVE accepts the citation on the operand
%r = trait.project %d[0] : <@R[i32]>                         // reads T_cond's return at [i32] with %w for ^0
```
The return's hypothesis `^0` is typed `<@W[a]>` (unproven); `subst_evidence` as first stated needed `%w`
typed `<@W[i32]>` with no citation.

**B14 (medium; binder calls, F4) (F-C4).** `Root.reqCall` substitutes the call's premises at the receiver's
written arguments for method hypotheses at the header's; the instantiated body is ill typed whenever the two
written forms differ, so theorem 5 excludes binder calls. `HasType.reqCall` types the premises `fs j` at
`P_j[a ++ u]`, `a` the receiver's written arguments; `ImplDecl.binderHyps` types the method body's hypotheses
at `P_j[h[σ] ++ X]` (SPEC.md 3: a method's signature is the trait's at the header). `Root.reqCall` reads the
body with `substHyp (hypsOf (ds ++ fs))`, so each `fs j` stands where a hypothesis of a different written
predicate stood; every typing rule compares predicates by identity, so the body is well typed only when
`a = h[σ]` as written. The integration step's answer to the probe (Calculus.lean's header, read off
D/TraitOps.cpp:1314-1356): the dialect's `inlineMethodAt` maps a binder call's operands onto the method body's
parameters with no bridge and bridges only the result with a coerce citing nothing, so `Root.reqCall` reads
what the stage reads and is left unchanged (definition request D11, not applied by decision). A premise that
the receiver is written as the header at `σ` belongs to the theorem that needs it: a `Reads.reqCall` case
mirroring `Reads.projReq`, with a binder clause of `ReturnsInstWF`, would prove theorem 5 for binder calls by
the same induction. Until then `Reads` has no `reqCall` case and theorem 5 is silent on terms whose reading
passes through one.
Program:
```
trait.trait @U { assoc Item }
trait.impl @U for i64 { Item = i32 }
trait.trait @T { method @requirement_0(%p : <@P[Self]>) -> <@Q[Self]> }
trait.impl @T for i32 { method @requirement_0(%p : <@P[i32]>) -> <@Q[i32]> { .. } }
%rcv : <@T[!trait.proj<@U[i64],"Item">] by @pT>             // the receiver written at the projection
%f   : <@P[!trait.proj<@U[i64],"Item">]>                     // the premise at the receiver's form
%q = trait.method.call %rcv @T[!trait.proj<@U[i64],"Item">]::@requirement_0(%f) : (<@P[..]>) -> <@Q[..]>
```
Under `monomorphize-trait`, after (beta-A) the inlined body receives `%f : <@P[U[i64]::Item]>` for the block
argument `%p : <@P[i32]>` with no bridge; the restriction `a = h[σ]` as written is the rule the theorem would
state.

**B15 (observation) (F-C5).** `hD` (H3 in the logic) and `hden` are not needed by theorem 5's proof, as `hS`
and `hΓ` are not by theorem 3's: given `Reads`, `ReturnsWF`, `ProofsGround` and `ReturnsCitesOk`, a reading
that reaches a base denotes its own claim (the DERIVE and WIT-APP cases produce `∃ Q, DnP P Q` from `DenL`,
every other case transports it), so `hden` is derived; and `Sig.ReqDuty` plays no role once the reading is
given, as it plays none in theorem 7. Both are kept in the statements as the specification wrote them and
marked unused. Falsifier: a model satisfying every hypothesis of `root_serves` but `hden`, with a reading that
reaches a base and a claim that does not denote; none exists, by `reads_spec`.

**B16 (observation; closure lemma not reused) (F-E6).** Logic.lean's `entails_valid` returns
`Nonempty (Deriv ..)`, which hides the derivation, so its output cannot be known primitive or resolvable;
theorem 7's value arm (`coerce_value_erases`) is proved by a direct induction on `Entails` (`entails_dnEquiv`)
rather than through the closure lemma. A `Type`-valued closure lemma (a function from `Entails` and seed
derivations to a `Deriv` with `Primitive` and `Resolvable` preserved) would let theorems 3 and 7 share it.
Program: Logic.lean:207-232 (`entails_valid`, `predEntails_valid`, both `Nonempty`-valued).

**B17 (medium for the Lean model, none for the dialect; applied).** `inlineAux` as the scaffold wrote it did
not inline a projection whose operand is a projection, so the let theorem's type clause was false as the
skeleton stated it: it decided whether a `project e k` is a D2 projection by reading the operand's text
(`Ev.citedProof`, `Ev.writtenPred`), while (PROJECT-WHERE) reads the citation off the operand's claim; a
projection past the plain requirements carries the claim of the cited derive's operand, citation included,
but writes nothing, so for `project (project w[k1])[k2]` with both past the plain requirements the inner
projection was inlined to an uncited derive and the outer one kept over it, and the result had no type.
The dialect reads the operand's claim type for this decision (D/TraitOps.cpp:3159-3161), so the stage lowers
the nested shape; the gap was in the Lean definition. What the calculus does: definition request D3, applied
(Calculus.lean:338-351): `inlineAux` reads the projection off the derive its inlined operand returns, as
`Root.projWhere` does; `Ev.citedProof` and `Ev.writtenPred` are deleted; `witness_is_let` is proved with no
shape condition.
Program (the skeleton's definition): trait `T0` (arity 0, no requirements, no binders, no associated types);
impl `I0 = impl T0 for () where T0[]`; impl `I1 = impl T0 for ()` (unconditional); proofs
`p0 : T0[] := derive I0 [] [witness @I1 for T0[]]`, `p1 : T0[] := derive I0 [] [witness @p0 for T0[]]`
(DeclWF and ProofsWF satisfied). Term `e := project (project (witness @p1 for T0[]) 0) 0`: the inner project
by PROJECT-WHERE : `<T0[] by @p0>`, the outer likewise : `<T0[] by @I1>`; the old inlining gave
`project (derive I0 [] [derive I1 [] []]) 0`, which no rule types, while `c.strip = <T0[]>`. In IR:
`%w = trait.witness @p1 for @T0[]; %a = trait.project %w[0] : <@T0[] by @p1> -> <@T0[] by @p0>; %b = trait.project %a[0] : <@T0[] by @p0> -> <@T0[] by @I1>`.

**B18 (observation; F8; applied).** `witness @I` and `derive hdr_I from @I given()` differed under H4's
restriction: WIT-APP of an unconditional impl had no `Ok` premise while DERIVE requires `Ok i (Subst.ofList σ)`,
and `inlineAux` rewrites the witness to `derive i [] []` (F8's identification), so under a restriction that
refuses the impl the inlined term had no type although the witness had one. The dialect does not see this
(both forms lower to one instance, T/derive_of_an_unconditional_impl_is_the_impl_itself.mlir); the gap was
where the calculus put H4. What the calculus does: closed by D1 (B2); `witness_is_let` needs no `hOk`.
Program (the skeleton's rule): `Ok := fun _ _ => False`; trait `T` (arity 0); `impl T for ()` (I); no proofs.
`e := witness @I for T[]` was typed at `<T[] by @I>` with no `Ok` premise; `e.inlineProofs M = derive I [] []`
demands `Ok I (Subst.ofList []) = False`. In IR: `trait.witness @I for @T[]` against
`trait.derive @T[] from @I given()`.

**B19 (observation; theorem statement).** `witness_is_let` as the section 7 skeleton stated it, for any `Γ`,
fails at a proven hypothesis: `^0 : <P by @p>` is its own inlining and keeps its citation, so its claim is not
`c.strip`. Evidence: Findings.lean:508, over a module with one unconditional impl of `Tr[i32]` and the proof
`@p` whose body is its derive, `Γ = [<Tr[i32] by @p>]` (H2 and G-WF satisfied). What the calculus does: the
theorem is stated closed, as SPEC.md 6.4 states it.

**B20 (medium; SPEC.md 4.3's lemma is false as stated; H3 lacks the condition the stage checks).** (REQ-ADMISSIBLE),
"every valid judgment has a primitive derivation under DeclWF and ReqDuty", is refuted by `Trait.req_admissible_fails`
(ReqAdmissible.lean, axioms: `propext` only) over `loopSig`: traits `A` (requirement `C[Self]`), `B` (requirement
`A[Self]`), `C` (none), all of arity 1, no projections, no binders; impls `I_A = impl A for a_0 where B[a_0]`, returning
`project (project ^0 0) 0` (its duty `C[a_0]` read as the requirement of the requirement of its where entry), and
`I_B0 = impl B for i32`, returning `derive I_A[i32] given (derive I_B0[])`. `DeclWF` and `ReqDuty` hold
(`loopSig_declWF`, `loopSig_reqDuty`); `C[i32]` is valid by (REQ) on (IMPL) at `I_A` (`loopDeriv`); no primitive
derivation concludes an application of `C` (`loopSig_no_C`: under `G = []` nothing is an `Env` member, no impl is of
`C`, (CONV) needs an application of `C` to start from). The intended proof (SPEC.md 4.3: "(REQ) on an (IMPL)-derived
application is the impl's duty under `s` and the premise derivations") has no induction measure: replacing `I_A`'s
where entry by the premise puts the duty's inner (REQ) on the (IMPL) node at `I_B0`, whose duty is the (IMPL) node at
`I_A` again, and the replacement never terminates. `DeclWF` forbids a requirement applying its own trait directly,
not a cycle of length two; `ReqDuty` does not require that the duties' mutual reading reach a base. The stage requires
exactly that ("has no base: it is read through the returns of ...", D/Passes.cpp:1870; `readEvidence`; rows
`T/invalid_impl_return_reads_a_requirement_that_leads_back_to_itself.mlir`,
`T/invalid_impl_return_reads_its_own_requirement_through_its_witness.mlir`) and the verifier does not (F13). What the
calculus does with it: H3 as formalized (`Sig.ReqDuty`) is weaker than the stage's H3; the two repairs are (a) a duty
whose derivations carry no (REQ)/(REQ-A) node at all (`Deriv.NoReq`, stronger than `Primitive`), under which the
lemma's proof closes by structural induction with `Deriv.substTy_exists` (proved in ReqAdmissible.lean) and one cut
lemma, at the cost that a return may no longer be `trait.project ^j[k]` on a where entry (card 3 allows it, the verifier
admits it); or (b) the stage's own condition, every reading of every return at every instance reaching a base, which is
the lemma's content stated as a hypothesis. Which one is the owner's call; SPEC.md 4.3 and section 3's H3 are to be
rewritten with the refutation either way (with the card 5/5.1/F1/F7 rewrite after the owner's rulings). The lemma was
used by no theorem: theorem 7 is on primitive derivations and theorem 5 reads returns, so nothing else changes.

Hypotheses the proofs needed that section 6 did not state: the oracle's completeness `SelCompleteL` (B7);
`Deriv.Resolvable`/`ValidGround` and `ConLaw.KeepsArgs` (B9); primitive derivations in place of H3 in theorem
7 (B8); `Reads` on the term (B11); `Module.ProofsGround` and `Module.ReturnsCitesOk` (B13); `ClaimsWF` and
`hOk` in `subst_types` (section 1.5). Hypotheses stated and not needed: DeclWF and G-WF in theorem 3 (B3);
DeclWF in theorem 4 (B4); ReqDuty and the denotation of the claim in theorem 5 (B15); DeclWF and ReqDuty in
theorem 7 (B10); `hS` and `he` in the let theorem; `hj` in the inversion theorem.

## 4. Definition changes requested, and whether the integration step took them

D1 (Soundness prover; Calculus.lean). `HasType.witImpl` carries `Ok i (Subst.ofList [])`, by the pattern of
`derive` and `projRes`. Applied (Calculus.lean:237). Consequence: `hasType_valid` proved for every `Ok`.

D2 (Soundness prover; Logic.lean). Replace the `sorry` of `entails_valid` and `predEntails_valid` by the
proofs Soundness.lean carried under other names. Applied (Logic.lean:207-232); Soundness.lean has no copy.

D3 (Minimality prover; Calculus.lean). `inlineAux`'s projection case reads the derive the inlined operand
returns, as `Root.projWhere` does; `Ev.citedProof` and `Ev.writtenPred` deleted. Applied (Calculus.lean:338-351;
no occurrence of either name remains). Consequence: `hnest`/`hnP` dropped from `witness_is_let`.

D4 (Minimality prover; Calculus.lean). The `sorry` of `root_unique` and `hasType_weaken` replaced by the
bodies of Minimality.lean's private copies, and the copies deleted. Applied (Calculus.lean:1897, :1878); no
private copy and no XXX TODO remains in Minimality.lean.

D5 (Minimality prover; Findings.lean). Three refutations as examples: (a) the nested-projection term of B17,
(b) the `Ok := False` module of B18, (c) the inversion iff without `ProofsWF`. (c) is written
(Findings.lean:448). (a) and (b) are not, and are no longer refutations: with D1 and D3 applied, the
statements they refuted are the theorems `witness_is_let` now proves; their modules stand in B17 and B18 as
records of the skeleton's defect.

D6 (Erasure prover; Logic.lean). The oracle notions at the limit of the fuel (`Dn`, `DnP`, `DnEquiv`, `DenL`,
`ServedByL`, `SelSoundL`, `SelCompleteL`, `Sig.CoherentL`, with `denote_mono`, `denote_idem`, `Dn_con_iff`,
`Dn_proj_iff`) moved into Logic.lean; `denote` kept as the computable function. Applied (Logic.lean:396-:825).
The fixed-fuel `Den`, `ValidD`, `ServedBy`, `SelSound`, `Sig.Coherent` survive only in Erasure.lean
(:144-:172), to write the refuted proposition `ErasureAsStated` (:174) as section 7 wrote it.

D7 (Erasure prover; Logic.lean). `SelComplete` beside `SelSound`, a hypothesis of `erasure_core` and
`coherence`. Applied as `SelCompleteL` (Logic.lean:816).

D8 (Erasure prover; Logic.lean). `erasure_core` takes `ValidGround` (primitive, resolvable, at `DenL`) and
`L.KeepsArgs`, drops `hS`/`hD`, concludes `DnEquiv`; `Deriv.Resolvable` and `ConLaw.KeepsArgs` move to
Logic.lean. Applied (Logic.lean:746, :913, :925, :980); Erasure.lean's `erasure` is its instance.

D9 (Erasure prover; a consequence for theorem 5, no edit asked). Either `hasType_valid` is strengthened to
produce a primitive, resolvable derivation, or theorem 5 states the stage's exit-walk condition on the term.
Resolved the second way: `Reads` states the condition on the term and `reads_spec` proves the equality
statement directly (B11, B12).

D10 (Coherence prover; Calculus.lean). Restate the 6.5 lemmas so they apply to `Root.projReq`'s instantiated
return, and derive `ReturnsInstWF` from `ReturnsWF`. Applied (Calculus.lean:1419, :1554, :1723, :1828), with
`ReturnsCitesOk` as the one hypothesis the derivation needs beyond H2 and H3 (B13). The Coherence theorems
now take `hR : ReturnsWF L AnyImpl`, `hG : ProofsGround`, `hH4 : ReturnsCitesOk` in place of the prover's
interim `hRI : ReturnsInstWF`.

D11 (Coherence prover; Calculus.lean). `Root.reqCall`: either carry the premise that the receiver is written
as the header at `σ`, or model the bridge (beta-A) performs. Not applied, by decision: the integration step
read `inlineMethodAt` (D/TraitOps.cpp:1314-1356) as mapping the operands with no bridge, so `Root.reqCall`
reads what the stage reads, and the premise belongs to a `Reads.reqCall` case that does not yet exist (B14).

Also decided by the integration step without a request: `Module.ProofsGround` stated beside `ProofsWF` rather
than in it, because theorem 4b's written proof (`cut_proof`) is ground only when the derivation it elaborates
is; `ClaimsWF` as a premise of `subst_types`.

## 5. Commands

```
export PATH=$HOME/.elan/bin:$PATH
cd /home/jhoberock/dev/git/.wt/evidence-calculus/mlir-trait-dialect/proofs
lake build
#   Build completed successfully (11 jobs)
#   warning: Logic.lean:234:8: declaration uses `sorry`
#   warning: Completeness.lean:502:75: Variable name `hS` is not explicitly referenced.
#   warning: Completeness.lean:520:74: Variable name `hS` is not explicitly referenced.
lake env lean <file>.lean          # one file against the built dependencies (what each prover ran)
lake env lean /tmp/claude-1000/-home-jhoberock-dev-git-screech-fable/43f1b9ea-b545-476e-8bcc-8689b5f6108f/scratchpad/Axioms2.lean
#   the `#print axioms` output of section 2
grep -n sorry *.lean               # Defs.lean:8 (header comment), Logic.lean:235
```
Nothing else was run: no cargo, no estate build, no suite.

## 6. What this report changed in SPEC.md

Section 1 only: one line after each card's "WHY IT IS CORRECT" paragraph and one after its "WHY IT EXISTS"
paragraph, each naming the Lean theorems that are that paragraph's proof. Card 1: `cut_admissible`,
`cut_proof` / `completeness`. Card 2: `hasType_valid` (the `derive` case of `hasType_deriv`), `soundness` /
`independence_derive`. Card 3: the `projReq` and `projWhere` cases of `hasType_deriv`, `reads_spec` /
`independence_project`, `project_where_is_inversion`. Card 4: the `witProof`, `witImpl`, `projRes`, `refl`,
`compose` cases of `hasType_deriv` with `entails_valid`, `entails_of_equational` /
`independence_projRes`, `independence_refl`, `witness_is_let`, `compose_derivable`. Card 5: the `coerce` case
with `predEntails_valid`, `coerce_value_erases`, `reads_spec` / `independence_coerce`. Card 6: the
`witProof` case under `ProofsWF`, `cut_proof` / `witness_is_let`, `witness_is_let_root`. Nothing else in
SPEC.md changed.
