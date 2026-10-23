# SPEC.md: the evidence calculus of mlir-trait-dialect

Phase A deliverable of `/home/jhoberock/.claude/projects/-home-jhoberock-dev-git-screech-fable/briefs/EVIDENCE_CALCULUS/BRIEF.md`,
judged 2026-10-22 from two blind specifications (rules-first, ops-first) and their verifications, against mlir-trait-dialect
`bfb4342bc9ed6b1b3e1ecee3cf66a32907fc5ded` and screech-fable `d32613c3` (only `docs/plans/ROADMAP.md` differs from the revisions the
drafts read; no anchor moved). Read-only everywhere; the only thing run was `mlir-opt` with
`--load-dialect-plugin=/home/jhoberock/dev/git/mlir-trait-dialect/cpp/build/libtrait_dialect.so`, alone (verify) and with
`-pass-pipeline='builtin.module(monomorphize-trait)'` (the stage), on probes. Probe directories under
`/tmp/claude-1000/-home-jhoberock-dev-git-screech-fable/43f1b9ea-b545-476e-8bcc-8689b5f6108f/scratchpad/evidence_calculus/`:
R = `read_ops/probes/`, Q = `read_equality/probes/`, P = `spec_rules-first/probes/`, W = `spec_ops-first/probes/`,
V = `verify_rules-first/probes/`, X = `verify_ops-first/probes/`, J = `judge/probes/` (mine: j1, j2, j3); each probe's `.verify.*` and
`.mono.*` stand beside it. `D/` = `/home/jhoberock/dev/git/mlir-trait-dialect/cpp/`, `T/` = `D/tests/`, `S/` = `/home/jhoberock/dev/git/screech-fable/`.

Vocabulary. The dialect's names are used as names. "Written form" is a type's text as the IR prints it. "Valid" means derivable in
the trait logic (section 4). "Citation" is the `by @p` a proven claim carries. `==` is interned identity after one substitution
pass; `|C|` is a claim with its citation removed (`stripClaimProofs`, `D/EqualityVerification.cpp:278-290`); `C ==p D` is `|C| == |D|`.
`M = (S, Pi)` is a module (signature, proof table); `G` the claim-typed block arguments in scope; `R_T` a trait's plain
requirements (its result list); `W_I,j` an impl's where entries; `hdr_I` its header; `bind_I(N)` its binding of `N`.

## 0. What is proved

The object is the six evidence operations as defined (operands, results, description, verifier), read as the constructors of a
proof calculus (section 5). The trait logic (section 4) is the frontend's obligations as the analyzer generates them. Theorem 3: a
well-typed term's claim is valid. Theorem 4: every valid judgment has an allege-free term, built by the frontend's `emit` and the
stage's proof writer, so `trait.allege` is a cut. Theorem 5: under a coherent signature two closed terms for one application reach
one impl. Theorem 6: five constructors are independent, two are let/inversion, one redundant, one a cut; every rule without a
constructor and constructor without a rule is a finding. Theorem 7: a closed valid equality relates two written forms of one type,
so `trait.coerce` forwards its value and evidence erases. The C++ is the source for what the rules say, never the thing proved.
Section 1 holds the cards; 2 the deletions; 3 to 7 make the cards true; 8 the findings, each with its program; 11 the scores.

## 1. The six cards

ITS MEANING is the typing rule `M; G |- e : C`, the operation's whole semantics; WHY IT IS CORRECT the soundness case; WHY IT EXISTS
the independence lemma or the finding replacing it. H1 to H5 are the hypotheses of section 6.

### Card 1: `trait.allege`

ITS MEANING (`D/TraitOps.td:861-917`; no verifier; the custom text builds an unproven claim, `D/TraitOps.cpp:52-60`; a Write on
`ObligationResource` keeps it alive, `:105-110`)
```
(ALLEGE)  ----------------------------------      C any claim, application or equality, unproven
          M; G |- trait.allege C : C
```
WHY IT IS CORRECT. Not by itself: it is the cut. The stage replaces a monomorphic allegation by the closed term selection builds or
reuses (`D/Passes.cpp:565-594`, `:711-744`; `D/ImplResolution.cpp:771-873`, `:879-1005`), defers a polymorphic one to each instance that
grounds it (`:565-567`; `T/impl_selection_skips_polymorphic_allege.mlir`), and refuses one nothing proves where it stands
(`T/invalid_allegation_unsatisfied.mlir`, `T/invalid_allegation_ambiguous.mlir`, `T/invalid_allege_of_an_equality_its_binding_refutes.mlir`,
`T/invalid_allegation_nothing_reads_is_decided.mlir`; the exit walk, `D/Passes.cpp:1939-1941`). Theorem 4b: a closed valid allegation
has a closed allege-free replacement, so a module leaving the stage has none and theorem 3 covers what remains.
Lean (why it is correct): `Trait.cut_admissible`, `Trait.cut_proof` (Completeness.lean): every closed valid predicate has a closed allege-free term, written as a `trait.proof` under which the table stays well founded.

WHY IT EXISTS. No judgment needs it (theorem 4). It carries the frontend's compiler-rule facts, (RULE) and (RULE-B) of 4.1, whose
derivation the dialect cannot state: fourteen rules (`S/src/types/auto_impl_rule.rs:14-29`), alleged by codegen
(`S/src/codegen/mlir/generator.rs:1938-1944`, `:2006-2010`), re-proved by selection through the impls the dialects' generators write
(`D/ImplResolution.cpp:336-364`; `allegeRequirements`, `D/TraitOps.cpp:1091-1105`); and the owner ruled an allegation a trusted assertion
naming no impl (2026-09-28, `S/docs/plans/EVIDENCE_TERMS_AUDIT.md:66`). Falsifier of "no rule": `P/s2b_allege_instead_of_project.mlir`
alleges where only a hypothesis's requirement reaches the claim; the stage refuses it: the cut is admissible from `S` alone, never
from a hypothesis. Findings F1, F5.
Lean (why it exists): `Trait.completeness` (Completeness.lean): `elabDeriv` writes an allege-free term for every derivation, so no judgment needs the cut; `HasType` has no rule for `allege`.

### Card 2: `trait.derive`

ITS MEANING (`D/TraitOps.td:919-990`; `verifyCitationOf` `D/TraitOps.cpp:2413-2431`, `verifyPremisesSuppliedByPosition` `:2391-2407`,
`DeriveOp::verifySymbolUses` `:2524-2536`)
```
          I in S    |s| = n_I    hdr_I[s] == T[a]    M; G |- e_j : C_j,  C_j ==p W_I,j[s]   (j = 1..k_I)
(DERIVE)  -------------------------------------------------------------------------------------------
          M; G |- trait.derive T[a] from @I[s] given(e_1 .. e_k) : T[a]        (unproven)
```
Refusals, in order: argument count (`:2417-2421`), header identity (`:2422-2427`), premise count (`:2394-2397`), premise identity modulo
citation (`:2398-2405`) (`T/invalid_derive_states_its_impl_arguments.mlir:43,14,30,59`; `T/invalid_derive_equality_assumption.mlir`); an
application result (`D/TraitOps.td:961`; `T/invalid_derive_of_an_equality.mlir`). A premise may be unproven or polymorphic (`T/derive.mlir`,
`P/s3`); no body is read, nothing normalized. The generic form admits a citation on the result (`R/p1`; F1).

WHY IT IS CORRECT. Rule (IMPL): the operands give `S; |G| |- W_I,j[s]` by induction (a citation is no part of a predicate), and the
header at `s` is `T[a]` by identity. GHC's `evDFunApp`, rustc's `ImplSource::UserDefined`, chalk's `Implemented-From-Impl`.
Lean (why it is correct): the `derive` case of `Trait.hasType_deriv`, concluding by `Deriv.impl`, through `Trait.hasType_valid` and `Trait.soundness` (Calculus.lean, Soundness.lean).

WHY IT EXISTS (independence, theorem 6). `S` = trait `Tr`; `impl<U> Tr for tuple<U> where Tr[U]`; `G = [Tr[a0]]`; goal `Tr[tuple<a0>]`.
A hypothesis gives `Tr[a0]` only; `Tr` has no requirement to project; the application arm of `trait.witness` is ground only (a proof
is ground, `D/TraitOps.cpp:2012-2017`; an unconditional impl has no parameters, `:1107-1113`; `T/invalid_polymorphic_witness.mlir`);
`trait.coerce` from `Tr[a0]` needs `a0 = tuple<a0>`, which no equality constructor yields and the closure never instantiates (`Q/p16`).
The description's own case (`D/TraitOps.td:926-930`); `P/s3_derive_independence.mlir` verifies.
Lean (why it exists): `Trait.independence_derive` (Minimality.lean).

### Card 3: `trait.project`

ITS MEANING (`D/TraitOps.td:992-1079`; `ProjectOp::verifySymbolUses` `D/TraitOps.cpp:3141-3167`; `getClaimRequirementAt` `D/TraitTypes.cpp:429-465`;
a Write on `ObligationResource`, `D/TraitOps.cpp:112-117`)
```
                M; G |- e : T[a] (by c)?     k < |R_T|     D ==p rho_k[a]
(PROJECT-REQ)   -----------------------------------------------------------      sound only with D unproven (F1)
                M; G |- trait.project e[k] : .. -> D   : D

                M; G |- e : T[a] by p    Pi(p)'s derive is `from @I[s] given(d_1 .. d_m)`    k = |R_T| + j,  j < m
                D == type(d_j) when type(d_j) is proven;  D ==p type(d_j) otherwise
(PROJECT-WHERE) ------------------------------------------------------------------------------------   deletion D2
                M; G |- trait.project e[k] : .. -> D   : D
```
Refusals: index at or past the count (`D/TraitTypes.cpp:437-441`; `T/invalid_project_index_out_of_range.mlir`, `P/s1`); result not the
selected requirement (`D/TraitOps.cpp:3156-3166`; `T/invalid_project_equality_hop_mismatch.mlir`, `R/q7`). Both predicate arms are
reachable by position (`T/project_selects_a_requirement_by_position.mlir`); a derive may be the source (`W/d1`, `J/j2`). The trait
requirement is read at the source's arguments as written, through no binding (`D/TraitTypes.cpp:448-455`; the header comment
`D/TraitTypes.hpp:920-934` says otherwise, F11). Any citation on a trait-requirement result is admitted (`R/q9`, `R/p2`); a where-entry
result is held to the operand's citation only when the operand is proven (`X/x5`, `V/v4`) (F1).

WHY IT IS CORRECT. PROJECT-REQ is rule (REQ): a trait's plain requirement at the application's arguments is valid whenever the
application is. On a hypothesis it is the primitive rule; on an (IMPL)-derived application it is admissible under H3 (the impl's
requirement evidence is derivable from its where entries in the primitive fragment, 4.3), which the stage's (beta-req) performs by
inlining the impl's return (`D/TraitOps.cpp:1600-1648`). PROJECT-WHERE is inversion on the cited proof's derive, whose operand is a
closed term for `W_I,j[s]` (H2). Chalk's `Implied-Bound-From-Trait`, GHC's superclass selector.
Lean (why it is correct): the `projReq` case (by `Deriv.req`) and the `projWhere` case (inversion on `proofDerive_spec`) of `Trait.hasType_deriv` (Calculus.lean); the root of a projected requirement serves its claim by `Trait.reads_spec` (Coherence.lean).

WHY IT EXISTS (independence). `S` = traits `Eq`, `Ord` with `R_Ord = [Eq[a0]]`, no impls; `G = [Ord[i32]]`; goal `Eq[i32]`. No impl to
derive from or witness, no proof, no equality to coerce along (the one claim in scope has another constructor key); only
`trait.project` reaches it (`P/s2_project_independence.mlir` verifies; the cut in its place is refused, `P/s2b`). PROJECT-WHERE has no
rule and no writer: no `ProjectOp::create` in `D/*.cpp`; the frontend indexes plain requirements only (`S/src/codegen/mlir/generator.rs:1897-1900`).
Deletion D2.
Lean (why it exists): `Trait.independence_project` (Minimality.lean); the where-entry arm is inversion, `Trait.project_where_is_inversion` (D2).

### Card 4: `trait.witness`

ITS MEANING (`D/TraitOps.td:1081-1219`; `WitnessOp::verify` `D/TraitOps.cpp:2300-2385`, `verifyResolution` `:2433-2460`, `verifySymbolUses`
`:2462-2507`; `verifyCitation` `D/TraitTypes.cpp:362-382`). The arm is read off the result claim; impl arguments are stated exactly where
an impl is cited (`:2308-2310`).
```
          c = a trait.proof p with Pi(p) proving T[a], or an unconditional trait.impl I with hdr_I == T[a]
          in a trait.proof body c is a root, not a cast;  no premises, no refl, no impl_args
(WIT-APP) ---------------------------------------------------------------------------------------------
          M; G |- trait.witness @c for T[a] : T[a] by c

          I in S   |s| = n_I   hdr_I[s] == T[a]   M; G |- e_j : C_j, C_j ==p W_I,j[s]   bind_I(N)[s + (X_N -> g)] == rho
(WIT-PROJ) --------------------------------------------------------------------------------------------
          M; G |- trait.witness proj_resolve T[a]::N<g> resolves rho by @I[s] given(e) : (T[a]::N<g> = rho)
          (X_N: the labels the impl's binding declares, V/v6; one substitution pass)

(WIT-REFL) ------------------------------------------      no premises; endpoints identical; t may be polymorphic (R/p12)
           M; G |- trait.witness refl : (t = t)

          k >= 1    M; G |- e_j : (l_j = r_j)  (j = 1..k)    GC({l_j = r_j}) |= t1 ~ t2    SSA-dominance region
(WIT-COMPOSE) -----------------------------------------------------------------------------------------   deletion D1
          M; G |- trait.witness compose(e) : (t1 = t2)
```
Refusals: WIT-APP `T/invalid_witness_cites_a_proof_of_another_application.mlir`, `T/invalid_proof_casting_a_cast.mlir` (the root rule, `D/TraitOps.cpp:2498-2504`), `W/e1`; WIT-PROJ `T/invalid_witness_impl_arguments.mlir`, `T/witness_gat_argument.mlir` (an unproven premise is accepted, `R/p7`; a polymorphic witness is re-verified per clone, `T/witness_clone_specialization.mlir`); WIT-REFL `T/invalid_bound_evidence.mlir:100`; WIT-COMPOSE `R/p6a` (no premise), `T/invalid_witness_compose_application_premise.mlir`, `T/invalid_witness_compose_unentailed.mlir`, `R/p6e` (no injectivity), while it supplies symmetry (`R/p6c`), transitivity (`T/witness_equality_compose.mlir`), congruence (`R/p6d`) and `t = t` for every `t` given any premise (`R/p6b`). No fourth arm exists in parse or verify (`D/TraitOps.cpp:2201-2256`, `2300-2385`).

WHY IT IS CORRECT. WIT-APP: for a proof, H2 (the proof table is well typed under `G = []`, allege-free, its citation relation well
founded) and weakening give the body's closed derivation of exactly the cited application (`verifyCitation`); for an unconditional
impl, (IMPL) with no premises. WIT-PROJ: rule (BIND), with DERIVE's premises. WIT-REFL: (REFL). WIT-COMPOSE: the closure lemma (6.1):
`GC` decides ground equational consequence of its seeds under (SYM)(TRANS)(CONG)(CONG-P)(NORM). The one acceptance the inductive
logic does not justify: a proof citing itself through a where entry (`R/p14_self_citing_proof.mlir` verifies and lowers to
`Foo_all::m`; selection refuses the application, `R/p15`; F2), which H2 excludes.
Lean (why it is correct): the `witProof` (H2 and `Deriv.weakenNil`), `witImpl` (`Deriv.impl` with no premises), `projRes` (`Deriv.bind`), `refl` and `compose` (`Trait.entails_valid`) cases of `Trait.hasType_deriv`; the closure's exactness is `Trait.entails_of_equational` (Soundness.lean).

WHY IT EXISTS. WIT-PROJ, independent: `S` = trait `A` with `Item`, `impl A for i64 { Item = i32 }`; `G = []`; goal `A[i64]::Item = i32`.
refl needs identical endpoints; compose and coerce need an equality premise and derive nothing past their seeds (`Q/p26`, `Q/p30`,
`Q/p34` refused); only proj_resolve reads a binding. Chalk's `Normalize-From-Impl`. WIT-REFL, independent: `G = []`, goal `i32 = i32`.
compose needs a premise (`R/p6a`); coerce from a value or an application claim to an equality claim is refused (`W/g1`, `W/g2`);
proj_resolve needs a binding (`P/s7` verifies). Scoped: given any `h : a = b` in scope, `compose(h) : t = t` is accepted for every `t`
(`R/p6b`), and after D1 `coerce h : (a = b) to (a = a) via (h)` still yields `a = a`; refl is independent for a `t` no equality in scope
relates, which includes every closed program's first one. WIT-APP, not independent: the `let` reference to a `trait.proof` (card 6),
and for an unconditional impl (IMPL) with `k_I = 0` under a name (`trait.derive hdr_I from @I given()` types the same claim up to the
citation and lowers to one instance: `T/derive_of_an_unconditional_impl_is_the_impl_itself.mlir`, `P/s6`; F8); kept because consumers
dispatch on the name (5.3). WIT-COMPOSE, not independent: every accepted `compose(e) : t1 = t2` has the accepted
`trait.coerce (trait.witness refl : t1 = t1) to (t1 = t2) via (e)` (`R/r1`, `R/r2`, `Q/p07`, `R/q5`, `W/c1`, `J/j3`; F3, D1). The converse
fails (`X/x1a` accepted, `X/x1b` refused) and is not needed.
Lean (why it exists): `Trait.independence_projRes`, `Trait.independence_refl` (Minimality.lean); WIT-APP is the let, `Trait.witness_is_let`; WIT-COMPOSE is carried by coerce, `Trait.compose_derivable` (the converse fails: Findings.lean's F3 example).

### Card 5: `trait.coerce`

ITS MEANING (`D/TraitOps.td:1221-1274`; `CoerceOp::verify` `D/TraitOps.cpp:2607-2662`; `fold` `:2664-2670`)
```
          M; G |- v : tin      M; G |- e_j : (l_j = r_j)  (j = 1..k, k >= 0)      SSA-dominance region
          tin and tout each a claim at its root or claim-free
          tout = T'[b] by c  =>  tin = T[a] by c          (no citation minted or exchanged; dropping one is allowed)
          GC({l_j = r_j}) |= |tin| ~ |tout|
(COERCE)  --------------------------------------------------------------------------------------------
          M; G |- trait.coerce v : tin to tout via (e) : tout
(FOLD)    tin == tout  =>  the op folds to v                                   (T/coerce_reflexive_fold.mlir)
```
Refusals, in order: graph region (`:2616-2619`), a claim nested in a container (`:2625-2629`; `T/invalid_coerce_masked_swap.mlir:57`), a citation not the input's (`:2635-2640`; `:28`, `R/p4`), a non-equality operand (`:2646-2651`; `Q/p32`), endpoints not entailed (`:2656-2659`; `T/invalid_coerce_shape_drift.mlir`, `P/s4`). Accepted: `T/coerce_congruence.mlir`, `T/coerce_claim_respell.mlir` (citation kept), `R/p5` (dropped), `Q/p20` (kept across a change of application; F7), `Q/p07` (an equality claim's endpoints moved by congruence; `R/q4`: not by symmetry alone), `P/s8` (a value's type changed through a polymorphic hypothesis), `Q/p09` (direction-blind).

WHY IT IS CORRECT. Three readings of one rule, each by the closure lemma on the cited leaves, valid by induction. (i) `tin` a value
type: the value is unchanged, its type rewritten along a valid equality; theorem 7 says the two written forms denote one type, so the
barrier's forward is the identity (`D/Passes.cpp:2108-2160`). (ii) `tin` an application claim: rule (CONV), the arguments rewritten
under valid equalities, the citation carried unchanged so dispatch is unchanged (`evidenceOf` reads through it, `D/TraitOps.cpp:1530-1540`;
theorem 5's COERCE case). (iii) `tin` an equality claim: (SYM)(TRANS)(CONG) on the two children, the case duplicating compose. The
no-exchange clause keeps (CONV) from trading one derivation for another (`T/invalid_coerce_masked_swap.mlir`, `R/p4`). Under H1 (no claim
type inside an equality endpoint) two claim nodes meet only by congruence over their children, which is what (ii) and (iii) read; the
verifier enforces H1 (F10), so no hypothesis converts evidence between unrelated applications (`V/v2`) or into a value (`X/x6`).
FC's cast, GHC's `evCast`.
Lean (why it is correct): the `coerce` case of `Trait.hasType_deriv` through `Trait.predEntails_valid` ((CONV) on an application, (SYM)(TRANS) on an equality); the value arm is `Trait.coerce_value_erases` and `Trait.erasure` (Erasure.lean); dispatch unchanged is the `coerce` case of `Trait.reads_spec` (Coherence.lean).

WHY IT EXISTS (independent twice). Value arm: `G = [A[a0]::Item = i32]`, `v : A[a0]::Item`, goal a value of type `i32`: no other
operation changes a value's type (`D/TraitOps.td:1225-1226`; `P/s8`). Claim arm: `S` = trait `Tr` with no impl for `i32`;
`G = [Tr[a0], a0 = i32]`; goal `Tr[i32]`: derive and witness have no impl or proof, project no requirement, compose yields no application
claim; only (CONV) reaches it. The frontend's `Cast` and value coercions (`S/src/codegen/mlir/generator.rs:1970-1981`, `2093-2132`).
Lean (why it exists): `Trait.independence_coerce` (Minimality.lean) for the claim arm; the value arm has no term in `Ev` and no Lean independence statement, its correctness being `Trait.coerce_value_erases`.

### Card 6: `trait.proof`

ITS MEANING (`D/TraitOps.td:1572-1702`; `ProofOp::verify` `D/TraitOps.cpp:1994-2019`; `respelledFrom` `:1982-1992`; `ReturnOp::verify` `:2593-2598`;
child list `D/TraitOps.td:1573-1574`; privacy `D/TraitOps.cpp:132-139`)
```
          body in {trait.coerce, trait.derive, trait.witness, trait.return}, one block, no block arguments, SSA dominance
          each body op typed by its own rule under G = []
          ret = c?(d)  with d = trait.derive T[a] from @I[s] given(e)                  (a root)
            or ret = c?(w)  with w = trait.witness @r for T'[b], r a root, not a cast   (a cast of r)
          c? = at most one trait.coerce;  type(ret) an application claim, ground;  the proof is private
(PROOF)   ---------------------------------------------------------------------------------------------
          trait.proof private @p { ..; trait.return ret }   proves   type(ret) by @p
```
The impl, arguments and premises are read off the derive, a cast's off its root's (`:2021-2062`). Refusals: `T/invalid_polymorphic_witness.mlir`,
`T/invalid_proof_of_an_impl_whose_premise_reads_an_unresolved_projection.mlir:27` (no projection, no allegation), `T/invalid_public_template.mlir`,
`T/invalid_proof_casting_a_cast.mlir`. A derive result naming another citation inside a proof is accepted and ignored; the derive's impl
dispatches (`W/b1`; F1).

WHY IT IS CORRECT. The body is closed; by theorem 3 under `G = []` its returned application is valid from `S` alone, and a citation of
it (WIT-APP) is sound for exactly that application. The hypothesis is H2: citation is well founded. The verifier enforces closure, the
child list, the return shape, groundness and the root rule; the stage bounds citation depth at 128, counting a proof cited again at an
application on its own chain as zero (`D/Passes.cpp:293-373`). Neither refuses a proof citing itself through its own where entry (`R/p14`;
F2), the shape H2 excludes and selection refuses (`R/p15`).
Lean (why it is correct): the `witProof` case of `Trait.hasType_deriv` under `ProofsWF` (H2, Calculus.lean); the stage's written proof keeps the table well typed and well founded, `Trait.cut_proof` (Completeness.lean).

WHY IT EXISTS. No judgment requires it: a closed term with a witness of `@p` is a closed term with `p`'s body in its place
(`witness_is_let`, 6.4). It is the `let` of the calculus (GHC's `EvBind`, rustc's memoized `ImplSource`), kept for three pipeline reasons:
the name is what `trait.method.call` dispatches on and what identifies an instance (`getProvenImpl`, `D/TraitOps.cpp:2889-2907`;
`InstanceKey`, `D/Specialization.hpp:59-122`; `T/two_proofs_of_one_application_with_different_premises_stay_apart.mlir`, 1 + 10); one
proof per (impl, resolved application, roots of the premises) is written and shared (`D/ImplResolution.cpp:508-576`); the proof is the
unit the depth check walks. Only the stage writes one (`D/ImplResolution.cpp:466-498`; the frontend emits none,
`S/src/codegen/mlir/generator.rs:1916-1931`; `S/docs/plans/EVIDENCE_FUNCTION_DESIGN.md:324-326`).
Lean (why it exists): `Trait.witness_is_let`, `Trait.witness_is_let_root` (Minimality.lean): the let; no judgment requires it.

## 2. The deletion list

A constructor the calculus does not need is one whose every use other constructors reproduce with no loss of provability. Two are
found; four admitted states go with them. Nothing here adds an operation.

**D1. `trait.witness compose(...)`.** WIT-COMPOSE asks `GC(premises) |= t1 ~ t2`; `trait.coerce` asks the same closure (`D/TraitOps.cpp:2370`
and `:2656-2659` both call `entailedByGroundCongruence`, `D/EqualityVerification.cpp:266-276`), and an equality claim is a constructor with
key `trait.claim.eq` over `[lhs, rhs]` (`:30-36`), so `trait.coerce (trait.witness refl : t1 = t1) to (t1 = t2) via (premises)` asks
`t1 ~ t1 and t1 ~ t2`, compose's question (`R/r1`: transitivity, symmetry, congruence over `tuple`; `R/r2`: `T/witness_equality_compose.mlir`
with compose replaced, lowering to the same identity function; `Q/p07`, `R/q5`, `W/c1`, `J/j3`). Only this direction is claimed; the
converse fails on a claim-typed endpoint (`X/x1a` accepted, `X/x1b` refused), which H1 excludes and the verifier now refuses (F10).
What goes: the verify arm `D/TraitOps.cpp:2337-2373`; the parser and printer arms `:2237-2243`, `:2278-2284`; the builder `D/TraitOps.td:1177-1186`
and description `:1119-1129`; the Rust builder `/home/jhoberock/dev/git/mlir-trait-dialect/src/lib.rs:542-546`; the two writers,
`supplied_equality` (`S/src/codegen/mlir/generator.rs:2038-2073`) and `buildEqualityEvidence` (`D/ImplResolution.cpp:994-1005`), each writing
the coerce of a refl over the same leaves; the twelve lit tests naming `compose(` are rewritten.
What must change with it: the erase barrier judges a claim-to-claim coerce by its written endpoints after stripping citations and
refuses one whose endpoints differ unless its input is application evidence (`D/Passes.cpp:2108-2160`), while a witness is erased
unconditionally (`:2091-2098`). An equality-claim coerce whose result reaches the barrier live is therefore refused where the compose
passes: `V/v1a` (the lit test's composed equality passed to a non-template `trait.func.call`) lowers; `V/v1b`, the same with the coerce
of a refl, fails "failed to legalize operation 'trait.coerce'". That shape is the frontend's own: `supplied_equality` writes compose for
an equality "a call supplies whole". Landed (trait `evidence-calculus` 9f57b80, a8d6948, 9ad9853, 9134810 and 532f8b2): `EraseCoerceOp` erases a coerce whose result
is an equality claim as `EraseWitnessOp` erases a witness, and the judgment that makes both erasures sound, every monomorphic equality
claim standing outside a template settled (its sides resolving to one type that names no projection) or refused, runs at the ENTRY of erase-polymorphs
over everything it is about to erase (`judgeStandingTheory`, `D/Passes.cpp`), not at the exit of instantiate-monomorphs: that exit
walk had skipped a coerce read only by trait ops (`readThrough`), and the lowering driver runs instantiate-monomorphs only while an
operation is pending, which no equality claim is, so a module whose only trait work was an equality was never judged at all (the compose
round's one HIGH, Astra and Sol; the design DESIGN_EQUALITY_JUDGMENT_BEFORE_ERASURE.md). The pending predicate counts a standing
monomorphic `trait.allege` too, so an allegation alone is served, and a polymorphic one reaches erasure's entry, which names it. The
entry judgment reads block arguments as well as results, so a hypothesis is judged where it is assumed; it refuses a claim carrying a
type variable outside a template and an undischarged application claim or projection, so the barrier keeps one rule per result kind
and no verdict (a claim erases; a value forwards, the entry having left its endpoints one type); what instantiation still owes (the
pending predicate and instantiation's exit walk) and what erasure judges are verdicts on one enumeration of standing sites
(`walkStandingSites`), which reads the types an op's attributes carry and a bodied function's declared result types (a function that
never returns hands back no value of them, so selection proves them, as it proves an external function's) as well as its results and
block arguments, and whose one exemption is the application claim
of a coerce read through; erasure's entry refuses first, at the op owing it, any work instantiation still owes, then reads every proven
claim's application as selection reads one before it proves it (`readApplication`), refusing an argument that resolves to no type a
predicate states; and erasure's readiness is one rule, reading the predicate erasure's own conversion target reads, with
no opinion on any pending operation, so instantiation runs alone before it. Where a value coerce consumes
the equality the replacement already lowers (`J/j3`, `R/r2`). Gate: output equivalence on the corpus suites in both runners, the dialect lit suite and device runs; never byte identity.

**D2. The where-entry arm of `trait.project` (index at or past the trait's requirement count).** PROJECT-WHERE is inversion on a proof's
derive (6.4): a where entry is a premise of the impl's derivation, read by opening it, admissible wherever proof bodies are available
(H2). No rule of the logic corresponds to it and nothing writes it: no `ProjectOp::create` in `D/*.cpp`; the frontend indexes plain
requirements only (`S/src/codegen/mlir/generator.rs:1897-1900`); the stage reads a where entry off the derive's operands (`inlineEvidence`'s
where branch, `D/TraitOps.cpp:1616-1621`, serves only such a projection; `readEvidence` stops at one as a base, `:1735-1739`). The arm
carries F1's gap: a where-entry result is held to the operand's citation only when the operand is proven (`X/x5`, `V/v4`; refused only at
inlining by the bridging coerce's no-exchange clause).
What goes: `D/TraitTypes.cpp:418-427` (the count's proof arm) and `:457-464`; `D/TraitOps.cpp:1616-1621`; the where-entry base of
`readEvidence` (`:1735-1739`); the description items `D/TraitOps.td:1005-1007`, `:1028-1033`; the lit tests `T/proven_source_projects_to_impl_assumption.mlir`
and `T/proven_source_projects_to_impl_equality.mlir`, the only files reaching the arm. The ops-first draft kept the arm "for the stage's
reading"; the stage reads premises off the derive, so the reason fails.

**Admitted states deleted with them** (programs in section 8). (a) A citation on a result nothing checks: the result constraints of
`trait.allege` (`D/TraitOps.td:897`) and `trait.derive` (`:961`) become unproven claims, and `ProjectOp` refuses a cited result at a trait
requirement (`D/TraitOps.cpp:3156-3166`) (F1). (b) A proof citing itself, or a ring of proofs, through a where entry: `verifyProofDerivationsEnd`
refuses a repeat on its chain instead of counting it zero (`D/Passes.cpp:293-373`) (F2). (c) A claim type inside an equality endpoint:
every evidence op refuses evidence of such an equality among what it reads and produces (`EqualitiesRelateTypes`), and
`ClaimType::verifySymbolUses` wherever an equality naming a symbol stands, as `TraitApplicationAttr::verifySymbolUses` refuses a claim
argument (`D/TraitTypes.cpp`); erasure's entry refuses one still standing anywhere else (F10). (d) A derive or projection feeding itself in a graph region: `DeriveOp` and
`ProjectOp` take the SSA-dominance check `WitnessOp` and `CoerceOp` have (`D/TraitOps.cpp:2353-2360`, `:2616-2619`) (F12).

**Kept, with the overlap named.** `trait.witness @I for hdr_I` with `I` unconditional is `trait.derive hdr_I from @I given()` plus a
citation (F8); it stays because the citation is what the consumer dispatches on and `findProof` rests on "an unconditional impl is its
own proof" (`D/ImplResolution.cpp:530-533`). `trait.witness refl` stays: the only constructor of `t = t` for a `t` no equality in scope
relates, and the base D1's replacement is built on. `trait.proof` and the application arm of `trait.witness` stay as the `let` (card 6).
`trait.allege` stays as the cut (card 1). The binder constructor `trait.method @requirement_k` with its claim-returning
`trait.method.call` stays and is outside the brief's six (F4).

## 3. The signature

Types `t ::= a_i | K(t_1 .. t_n) | T[t]::N<u>`: a variable `!trait.poly<i>`, `i` the position of the parameter in the declaration
binding it (`D/TraitTypes.td:13-57`; a negative label is refused at parse, `D/TraitTypes.cpp:189-193`); any other constructor, `K` the type
rebuilt over position placeholders with its immediate sub-types as children (`D/EqualityVerification.cpp:69-95`); a projection
`!trait.proj<@T[t], "N", [u]>` (`D/TraitTypes.td:196-231`). A type is ground when it has no variable (`D/TraitTypes.cpp:351-359`). A
kind-constraining wrapper around a variable is a variable occurrence, atomic (`D/EqualityVerification.cpp:59-67`); a constructor declining
placeholders is atomic too (`:77-95`; F9). `t[s]`: `a_i` becomes `s_i` when `i < |s|` and stays otherwise, one pass, a substituted term
never revisited (`D/TraitTypes.hpp:824-831`; `#trait.impl_args`, `D/TraitAttributes.td:132-174`). H1: no claim type inside an equality
endpoint, which every evidence op enforces on the evidence it reads and produces, `ClaimType::verifySymbolUses` where an equality
naming a symbol stands, and selection and erasure's entry where its sides resolve (`D/TraitOps.cpp`, `D/TraitTypes.cpp`,
`D/ImplResolution.cpp`; F10).
Predicates `P ::= T[t] | t1 = t2`: an application names an existing trait at its arity with no claim among its arguments
(`D/TraitAttributes.cpp:126-156`; `T/invalid_claim_as_a_type_argument.mlir`, `X/x7`); an equality is ordered as written and read
direction-blind (`D/TraitAttributes.td:91-92`; `Q/p09`). Claims `C ::= P | T[t] by c`, `c` a `trait.proof` or an unconditional `trait.impl`
(`D/TraitTypes.cpp:241-272`; `D/TraitOps.cpp:2118-2131`); an equality never carries a citation (`D/TraitTypes.cpp:224-235`; `T/invalid_equality_claim_proof.mlir`).
A trait `T`: parameters `a_0 .. a_{m-1}`, `Self` first, labelled by position (`D/TraitOps.cpp:401-420`); associated types `N` with declared
parameters `X_N` distinct from the trait's (`:433-451`); plain requirements `R_T`, the result list, each an unproven claim mentioning a
parameter and applying `T` itself only under a projection (`D/TraitOps.td:161-164`; `D/TraitOps.cpp:471-485`; `T/cyclic_traits.mlir`); binders
`B_T`, each a bodiless `trait.method @requirement_i` whose claim parameters are the binder's premises and whose result is its
conclusion (`D/TraitOps.td:186-190`, `:1020-1021`). The frontend's one requirement list is in source order, header predicates then each
associated type's bounds, a bound on a generic associated type a binder (`S/src/evidence/contract.rs:76-103`, `126-180`); codegen splits
it into `R_T` (arity 0, positions among them) and `B_T` (named by the combined index) (`S/src/codegen/mlir/generator.rs:674-679`, `733-757`,
`1897-1914`). A binder `Pi X.(P => Q)` instantiates as `Q[a ++ u]` with premises `P[a ++ u]` (`contract.rs:197-215`; `D/TraitOps.cpp:576-585`).
An impl `I`: parameters `a_0 .. a_{n-1}`, labels dense across header and where clause (`D/TraitOps.cpp:890-894`); header `hdr_I = T[h]`,
which may spell a projection (`J/j1`: verifies, and selection serves `T[i32]` through `impl T for U[i64]::Item`); where entries
`W_I,1 .. W_I,k`, block arguments after the first, each an unproven claim (`:877-889`); a binding `bind_I(N)` per associated type over
the impl's parameters and labels the binding declares for `N`'s (`:826-869`; `V/v6`: not positional). Unconditional iff `n = 0` and
`k = 0` (`:1107-1113`).
Well-formedness enforced: every impl parameter stands in the header outside every projection or on the determined side of a
where-equality whose input is constrained, to a fixed point, a projection of the impl's own application never an input (rustc E0207;
`D/TraitOps.cpp:1004-1089`; `T/invalid_impl_parameter_determined_only_through_its_own_trait.mlir`; the frontend's twin
`S/src/analysis/semantic_analyzer.rs:5710`); every associated type bound in scope at the trait's arity (`:826-869`, `:950-985`); each
method's signature the trait's at the header through own bindings and where equalities (`:705-765`); the return supplies one claim per
plain requirement agreeing with `rho_k[h]` under own bindings and where equalities modulo citation (`agreeInOwnContext`, `:654-690`),
resting on no argument 0 (`restsOn`, `:292-306`), projecting no application of `I` itself (`projectsOwnApplication`, `:308-349`)
(`verifyRequirementEvidence`, `:774-810`; `T/invalid_impl_return_evidence.mlir`, `T/invalid_impl_return_reads_its_own_requirement_through_its_witness.mlir`;
GHC's rule for instance superclasses); a binder's method typed under the binder's premises (`S/src/codegen/mlir/generator.rs:928-962`;
`T/evidence_method_states_a_quantified_requirement_and_lowers_with_its_consumer.mlir`); an op in an impl body outside its methods has
the where arguments as its only hypotheses (`D/TraitOps.td:115-117`).
Not enforced, added by H3 (F13): a return may be an allegation (`T/impl_satisfies_trait_equality_requirement.mlir`; `allegeRequirements`
writes exactly that for a generated impl, `:1091-1105`; `X/x8` is proved by selection; `X/x9` is an allegation the impl's own binding
refutes, refused by the stage), and two impls' returns may project one another with no base (`X/x3`, `X/x10`; refused by `readEvidence`,
"has no base", `D/TraitOps.cpp:1696-1767`, `D/Passes.cpp:1946-1960`). The frontend's two declaration rules with no dialect counterpart: a
where entry mentioning no type parameter is an obligation proved where written (`semantic_analyzer.rs:3889`); impls of compiler-owned
roles are refused (`:5773`).

## 4. The trait logic

`S; G |- P`, `G` a list of predicates, the hypotheses of a frame (a function's contract entries; a trait body's own application; an
impl body's where entries; `S/src/evidence/contract.rs:449-475`). The brief's two judgments are the two arms of `P` at `G = []`.

### 4.1 Rules
```
(HYP)    P in G                                                         =>  S; G |- P
(IMPL)   I in S,  |s| = n_I,  S; G |- W_I,j[s] for every j              =>  S; G |- hdr_I[s]
(REQ)    S; G |- T[a],  rho_k in R_T                                    =>  S; G |- rho_k[a]
(REQ-A)  S; G |- T[a],  Pi X.(P => Q) in B_T,  S; G |- P_i[a ++ u] for every i  =>  S; G |- Q[a ++ u]
(BIND)   I in S,  |s| = n_I,  S; G |- W_I,j[s] for every j,  bind_I(N) defined
                                                                        =>  S; G |- hdr_I[s]::N<u> = bind_I(N)[s + (X_N -> u)]
(REFL)                                                                  =>  S; G |- t = t
(SYM)    S; G |- a = b                                                  =>  S; G |- b = a
(TRANS)  S; G |- a = b,  S; G |- b = c                                  =>  S; G |- a = c
(CONG)   S; G |- a_i = b_i for every i                                  =>  S; G |- K(a) = K(b)
(CONG-P) S; G |- a_i = b_i,  S; G |- u_j = v_j for every i, j           =>  S; G |- T[a]::N<u> = T[b]::N<v>
(NORM)   K(a) rebuilt through its constructor is K'(b) != K(a)          =>  S; G |- K(a) = K'(b)
         an axiom schema per loaded dialect (D/EqualityVerification.cpp:176-248; H5, F14)
(CONV)   S; G |- T[a],  S; G |- a_i = b_i for every i                   =>  S; G |- T[b]
```
Chalk's `Implemented-From-Env/-From-Impl`, `Implied-Bound-From-Trait`, `Normalize-From-Impl`; GHC's `evId`, `evDFunApp`, superclass
selection, FC axioms and casts. No rule decomposes an equality (projections are not injective; `Q/p04`, `R/p6e` refused) or
instantiates a polymorphic one (`Q/p16`): a variable is a constant of the logic; instantiation is the metatheorem of 6.5.
Frontend-only facts the dialect states no rule for:
```
(RULE)    rule r decides T[a] from facts F with S; G |- F, discharging T's plain requirements at a  =>  S; G |- T[a]
          (S/src/evidence/term.rs:326-342)
(RULE-B)  r serves T and binds T[a]::N<u> to t                           =>  S; G |- T[a]::N<u> = t     (term.rs:453-457)
(UNIF)                                                                   =>  S; G |- t = collapse_uniforms(t)
          (term.rs:396-401; S/src/types/kinds/uniform.rs:38-63; same-group nesting is (NORM) through coop's UniformType::get,
          /home/jhoberock/dev/git/mlir-coop-dialect/cpp/CoopTypes.cpp:43-59; the cross-group fold has no rule here, F6)
```

### 4.2 Where each rule comes from in the frontend
A call to a declaration with contract `G_D` at `th` obligates `G_D(k)[th]` for every entry, one hole per entry in contract order
(`S/src/analysis/constraints/constraint_environment.rs:504-580`); a method call obligates the receiver's `Self: T[..]` (`:687-784`); a
written projection obligates its head (`:385-405`); an impl obligates each `rho_k[h]` under its where entries (`semantic_analyzer.rs:3956`);
a value coercion obligates `tfrom = tto` (`S/src/analysis/elaboration/elaborate_coercions.rs:139-152`). The solver's answers are terms of
these rules (`S/src/evidence/term.rs:39-120`; each constructor refuses a term whose predicate does not follow from its parts, `:239-493`;
the predicate of a term is derived, `:754-818`): `Assumed` (HYP), `Project` (REQ)/(REQ-A), `Apply` (IMPL), `Own` (IMPL at the identity
substitution over the impl's own where entries), `Assoc` (BIND), `Equal` (a composition of (REFL)(SYM)(TRANS)(CONG)(UNIF) storing
endpoints and leaves), `Cast` (CONV), `Rule`/`RuleBinding` (RULE)/(RULE-B). The solver's search (hypotheses first for a non-concrete
goal, impls otherwise, exactly one viable impl, an inductive reading of a revisited goal; `S/src/analysis/impls/environment.rs:207-224`,
`725-820`, `1402-1443`) is a strategy for finding a derivation; the logic is what it finds.

### 4.3 The primitive fragment and the admissible rules
`Env(G)` is the closure of `G` under (REQ) and (REQ-A): hypotheses and their requirements (chalk's `FromEnv`). The primitive fragment
`|-p` permits (REQ) and (REQ-A) on `Env(G)` members only; the full logic `|-` permits them on any derived application. H3 (ReqDuty):
for every impl `I` and `rho_k in R_T`, `S; W_I |-p rho_k[h]`; for every binder, `S; W_I ++ P[h ++ X] |-p Q[h ++ X]`.
(REQ-ADMISSIBLE) Under H3, `S; G |- P` implies `S; G |-p P`: (REQ) on an (IMPL)-derived application is the impl's duty under `s` and the
premise derivations (6.5); on a (CONV)-derived one it commutes through (CONG)/(CONV); on a (REQ)-derived one it is a requirement of a
requirement, by induction. This is why chalk projects requirements out of the environment alone, and why the stage inlines a
projection of a proven source (beta-req) instead of selecting for it. The verifier accepts a return projecting a derived application
through another impl (`J/j2`: verifies and lowers), which H3 permits; it forbids a return with no base (`X/x3`, `X/x10`) or an allegation
the signature refutes (`X/x9`). (CUT): `trait.allege`, theorem 4b. (SUBST): 6.5.

### 4.4 Where the dialect's equality is more and less than the frontend's
The dialect reads hypotheses as classes, direction-blind, admitting inconsistent ones (`Q/p35`, `Q/p36`); the frontend keeps directed
rows keyed by projection head, refuses two disagreeing source rows (`S/src/analysis/assumption_environment.rs:895-961`), and keeps a
projection rigid where a hypothesis entails its head (`S/src/analysis/impls/environment/entailment.rs:128-151`). Both are sound for the
logic: it is relative to `G`, and a frame with a false hypothesis proves what it implies (theorem 7 is about closed equalities).
Rigidity is a search strategy, not a rule: (BIND) stays valid under any `G`. Under cyclic or contradictory where clauses the two accept
different programs (F15).

## 5. The evidence calculus

### 5.1 Terms and the typing judgment
A term is an SSA value of claim type (or, for the value arm of `trait.coerce`, of any type); each constructor is one operation; a block
argument is the hypothesis `^k` with `M; G |- ^k : G(k)`. The constructors are the six operations' forms on the cards, plus the binder
call outside the six (F4):
```
          M; G |- e : T[a] (by c)?    Pi X.(P => Q) is binder i of T    M; G |- f_j : C_j, C_j ==p P_j[a ++ u]
(REQ-CALL) -----------------------------------------------------------------------------------------------
          M; G |- trait.method.call e @T[a]::@requirement_i(f) : (P[a ++ u]) -> Q[a ++ u]   : Q[a ++ u]
```
(`D/TraitOps.cpp:2774-2795`, `2857-2887`; the `u` are read off the call's written signature; inlined by the stage, `:1477-1506`). Terms are
finite trees: a value feeding itself is not a term. The verifier admits one for `trait.derive` and `trait.project` in a graph region,
which carry no dominance check (`X/x2`: `%d = trait.derive .. given(%d)` in a module body verifies; the exit walk names it) (F12). Every
premise of every rule reads only operand types, cited declarations and attributes (`D/TraitOps.td:32-36`, "Verification is always
local"): nothing normalizes a projection, reads a binding except WIT-PROJ, or instantiates a variable (`Q/p26`, `Q/p30`, `Q/p16` refused).
The citation is read by identity at exactly five places: WIT-APP (`verifyCitation`), the cast rule in a proof body
(`D/TraitOps.cpp:2498-2504`), COERCE's no-exchange clause (`:2635-2640`), PROJECT-WHERE with a proven operand (`:3159-3161`), a method's
`trait.return` (`:2573-2585`). Everywhere else a citation is text the verifier does not read (F1).

### 5.2 The ground congruence closure, used twice
`GC(E) |= a ~ b` (`entailedByGroundCongruence`, `D/EqualityVerification.cpp:98-276`): `a` and `b` fall in one class of the least relation on
the subterms of `a`, `b` and the endpoints of `E` closed under (SEED) `(l = r) in E => l ~ r` (`:271-272`); (EQUIV) (`:172-174`); (CONG) same
key, children pairwise `~` (`:149-166`); (NORM) a child replaced by a class member and rebuilt through the constructor's own `get()`
gives `r != s`, not a free re-application, then `s ~ r` (`:176-248`); and nothing else: no decomposition (`:100-105`), no instantiation,
no binding read. Keys: an equality claim `trait.claim.eq` over `[lhs, rhs]` (`:30-36`); an application claim `[trait.claim.app, @T]`
over the arguments, citation ignored (`:37-43`); a projection `[trait.proj, @T, N, |g|]` over `a ++ g` (`:45-57`); a variable atomic
(`:59-67`); any other type its shell over placeholders, or atomic when the constructor declines them (`:69-95`). Nelson-Oppen /
Downey-Sethi-Tarjan closure, sound and complete for ground equational consequence under (REFL)(SYM)(TRANS)(CONG)(CONG-P), extended by
(NORM) under the stated, unenforced invariant that a constructor normalizes "purely as a context-free, deterministic function of its
arguments" (`:183-189`; F14), its completeness forgone across placeholder-declining constructors (F9).

### 5.3 The consumers, and what "correct" delivers
`trait.method.call rcv @T[a]::@m(x) : (A) -> R (by c)?` verifies when `rcv : T[a] (by c)?`, the trait's parameters take `a`, the method's
own labels are read off the written signature and `|F_m[s]| == |(A) -> R|` (`D/TraitOps.cpp:2774-2795`, `2845-2887`;
`T/invalid_method_call_equality_receiver.mlir`); `trait.func.call @f(o)` the same against a callee with dense labels (`:3038-3082`); both
modulo citation (`verifyEqualAfterInstantiation`, `D/TraitTypes.cpp:720-745`). In the stage a call is rewritable once every claim its
operands carry names its citation through its coercions (`isRewritableGenericCall`, `D/Passes.cpp:2483-2530`; `evidenceOf`,
`D/TraitOps.cpp:1530-1540`); a method call dispatches to the impl the receiver's citation roots at (`getProvenImpl`, `:2889-2907`;
`getRootOf`, `:2133-2143`); an instance is keyed by (template, type arguments, the citation at each claim position by interned identity)
(`D/Specialization.hpp:59-122`; `D/Specialization.cpp:260-308`); a non-template callee requires the operand's root to be its parameter's
(`D/Passes.cpp:980-1015`; `T/invalid_call_of_a_function_supplies_another_proof_than_it_takes.mlir`). One evidence term reaches one impl;
two terms with different roots for one application reach two instances (`T/one_callee_called_with_two_impls_of_one_claim_runs_each.mlir`,
7 + 9). Theorem 5 must deliver that two closed terms for one application have one root.

### 5.4 The root of a term
```
root(^k) = open     root(derive .. from @I[s] ..) = (I, s)     root(witness @I for ..) = (I, [])  (I unconditional)
root(witness @p for ..) = root(body of p), a cast's its source's     root(coerce e ..) = root(e)
root(project e[k]), k < |R_T| = root(return_k of root(e)'s impl)[s][derive operands for W_I]
root(project e[k]), k >= |R_T| = root(f_{k-|R_T|}), the derive operand (D2)     root(allege ..) = none until the stage replaces it
```
(`evidenceOf`, `throughCoercions`, `D/TraitOps.cpp:1522-1540`; `getRootOf`, `:2133-2143`; `readEvidence`, `:1696-1767`). Total on closed
allege-free terms under H2 and H3; `readEvidence` names readings with no base (`T/invalid_impl_return_reads_a_requirement_that_leads_back_to_itself.mlir`)
and past the depth limit (`T/evidence_read_through_128_returns_reaches_its_base.mlir`).

### 5.5 Reductions: what instantiate-monomorphs performs
```
(cut)      allege P                   -> the closed term selection builds (D/Passes.cpp:565-594, 711-744)
(let)      derive .. (closed)         -> witness @p .., p the proof whose body it is, written once (D/Passes.cpp:596-709)
(beta-req) project (e : T[a] by p)[k] -> return_k of p's impl, cloned at p's arguments with p's derive operands for the where
                                         hypotheses, bridged to the result's written form by a coerce citing nothing
                                         (D/TraitOps.cpp:1600-1648; D/Specialization.cpp:359-378)
(beta-A)   method.call rcv @T::@requirement_i(..) -> the impl's method body inlined (D/TraitOps.cpp:1477-1506)
(id)       coerce v : t to t          -> v (D/TraitOps.cpp:2664-2670; D/Passes.cpp:1121-1125)
(cast)     coerce (evidence) to T'[b], read by an op outside the dialect -> witness @<root>_as (D/Passes.cpp:1098-1141; D/ImplResolution.cpp:578-619)
(inst)     a call at ground arguments with proven operands -> a call of the instance cut under s with the caller's evidence for the
                                         hypotheses (D/Passes.cpp:1026-1087, 885-946)
(erase)    every claim value          -> nothing; a coerce forwards its value (D/Passes.cpp:2091-2160)
```
A normal form is closed, allege-free, has no projection of a proven source, and every coerce in it is the identity after projection
resolution. The exit walk of instantiate-monomorphs checks it was reached for obligations (unproven monomorphic claims, standing
allegations, standing ground projections); the entry of erase-polymorphs judges every claim and projection standing outside a
template, at op results and block arguments alike (`judgeStandingTheory`), so that what it erases is true (theorem 7). The depth
limits of 128 (obligations, `D/ImplResolution.cpp:252-260`; proof frames, `D/Passes.cpp:293-373`; projection steps, `D/TraitTypes.hpp:486`; instances per
template, `D/Passes.cpp:889-946`) are stage facts, not rules (F16).

## 6. The theorems

Standing hypotheses, each with the program showing the verifier does not enforce it:
- H1 (grammar): no claim type inside an equality endpoint, in `S`, `G` or a cited equality (`V/v2`, `X/x6`; F10). The tree enforces
  it for every equality it states and every predicate it proves: every evidence op refuses evidence of such an equality among
  what it reads and produces, as written or as a clone's substitution wrote it (`EqualitiesRelateTypes`;
  `T/invalid_equality_over_evidence_naming_no_symbol.mlir`, `T/invalid_equality_a_substitution_states_over_evidence_is_refused.mlir`),
  the claim's symbol-use verifier one naming a symbol wherever it stands (`T/invalid_claim_inside_an_equality_endpoint.mlir`),
  erasure's entry one still standing anywhere, and selection a predicate whose normal form reaches one
  (`T/invalid_equality_side_resolving_to_evidence_is_refused.mlir`, `T/invalid_application_whose_argument_resolves_to_evidence_is_refused.mlir`).
  It does not hold of bindings or substitutions: the model covers the fragment in which no associated type is bound to a claim-carrying
  type and no type parameter is instantiated at one (F10).
- H2 (proof table): every `trait.proof` body is typed under `G = []` at the application it proves, ground, allege-free, and "p cites q"
  is well founded (`R/p14`; F2).
- H3 (ReqDuty, 4.3): every impl's plain and binder requirements are derivable in the primitive fragment from its where entries
  (`X/x3`, `X/x8`, `X/x9`, `X/x10`; F13).
- H4 (denotation): every impl citation and header in a derivation denotes under `S` (`V/v3`, `J/j1`; F17).
- H5 (constructor laws): a constructor normalizes as a context-free deterministic function of its arguments, stable under
  substitution (`D/EqualityVerification.cpp:183-189`; F14).
- Terms are finite trees (`X/x2`; F12). G-WF: a proven hypothesis names a proof of its own predicate (`D/Passes.cpp:278-291` checks
  module-level `func.func` signatures only; `P/s5`, `W/f1`; F1). `pred(G)` is `G` with citations removed.

### 6.1 Theorem 3, SOUNDNESS
In words: an allege-free evidence term's claim is valid in the trait logic under the predicates of its hypotheses.
```
H1, H2, G-WF.   e allege-free,   M; G |- e : C     =>     S; pred(G) |- |C|
```
Induction on the typing derivation. HYP by (HYP). DERIVE by (IMPL), each operand's predicate by induction. PROJECT-REQ by (REQ); the
conclusion is read as `|D|`, where F1 is absorbed. PROJECT-WHERE by inversion on the cited proof's derive (H2). REQ-CALL by (REQ-A).
WIT-APP by H2 and weakening, or (IMPL) with no premises. WIT-PROJ by (BIND). WIT-REFL by (REFL). WIT-COMPOSE and the equality arm of
COERCE by the closure lemma. COERCE on an application claim by (CONV) with the closure lemma at each argument (H1 makes two claim nodes
meet only by congruence). COERCE on a value states no predicate (theorem 7). ALLEGE has no case.
Closure lemma: if every `(l_j = r_j)` is valid under `G` and `GC({l_j = r_j}) |= a ~ b` then `S; G |- a = b`; (SEED) is the premises,
(EQUIV) is (REFL)(SYM)(TRANS), (CONG) is (CONG)/(CONG-P) and congruence over a claim's children, (NORM) is H5. The closure decides this
fragment, so for ground terms the converse holds: WIT-COMPOSE and COERCE accept exactly the ground equational consequences of their
premises. OutsideIn(X)'s (S1). Falsifiers tried: `R/p14` (accepted, underivable; excluded by H2); `V/v2` (accepted; `S; {claim<T[i32]> =
claim<T[i64]>} |- T[i64]` underivable; excluded by H1); `R/q9` (accepted; the predicate is derivable, the citation wrong; F1); `Q/p35`
(accepted; derivable, `pred(G)` carrying the inconsistent hypotheses).

### 6.2 Theorem 4, COMPLETENESS, and the cut
4a, in words: every valid judgment has an allege-free term, and the construction is the frontend's `emit` and the stage's proof writer
read as one function of the derivation.
```
S; pred(G) |- P    =>    exists M' >= M (the proofs written), exists e allege-free.  M'; G |- e : P
```
`elab`: (HYP) -> `^k`; (IMPL) -> `trait.derive`, or `trait.witness @I` for an unconditional `I`; (REQ) -> `trait.project` (on a proven
ground base the stage inlines, the same term after (beta-req)); (REQ-A) -> `trait.method.call @requirement_i`; (BIND) -> `trait.witness
proj_resolve`; (REFL) -> `trait.witness refl`; (SYM)(TRANS)(CONG)(CONG-P)(NORM) -> one `trait.coerce` of a refl over the leaves of the
equational subderivation (today one `compose`; D1), by the closure lemma's converse; (CONV) -> `trait.coerce` over the leaves of the
argument equalities. This is `emit` (`S/src/codegen/mlir/generator.rs:1864-2032`) and the writer (`D/ImplResolution.cpp:466-498`, `994-1005`).
The written proofs are closed, so `M'` satisfies H2 whenever the citation order is well founded, which selection's cycle guard
guarantees (`D/ImplResolution.cpp:239-250`). Exceptions, each a finding: (CONG) across a placeholder-declining constructor has no coerce
(F9); the cross-group (UNIF) has no term (F6). Guess-free completeness in OutsideIn(X)'s sense is about the frontend's search and the
stage's selection, not the calculus; not claimed; the frontend's termination cuts (`S/src/analysis/impls/environment.rs:207-224`) are
where it fails.
4b, the cut, in words: every monomorphic allegation the logic validates from `S` alone is replaced by a closed term; every one it does
not validate is refused where it stands.
```
P monomorphic,  S; [] |- P,  Coherent(S)   =>   exists p. Pi + {p} well founded,  M'; G |- coerce (witness @p for P*) to P : P
```
`P*` the application with its ground projections resolved (`D/ImplResolution.cpp:193-197`). Existence is 4a at `G = []` plus PROOF.
Selection is one algorithm computing such a `p` (`resolveImplFor`, `D/ImplResolution.cpp:172-401`; `proofAtResolution`, `:816-873`); its
correctness is a statement about the C++, outside the proof's scope by the owner's words, and enters theorems 5 and 7 as the oracle
`sel` (section 7). (RULE)/(RULE-B) are derivable only in `S` extended by the generators' impls (F5).

### 6.3 Theorem 5, COHERENCE
`[[t]]` (denotation) resolves each ground projection through the impl selection serves its application with, to a fixed point,
applying the constructor laws; partial where no impl serves or the step bound is reached (`D/TraitTypes.cpp:117-129`; 128).
`ServedBy(S, P, I, s)` iff `|s| = n_I`, `[[hdr_I[s]]] = [[P]]` both defined, and `S; [] |- W_I,j[s]` for every `j` in the denotable
fragment (H4). `Coherent(S)` iff for every ground `P` with `[[P]]` defined, any two servers `(I, s)`, `(I', s')` have `I = I'` and
`[[s]] = [[s']]`. Comparing `s` up to denotation is forced: `(T_all, [i32])` and `(T_all, [U[i64]::Item])` both serve `T[i32]` and the
stage lowers both to one instance (`V/v5`, `X/x4`), identifying a proof by the resolved application (`D/Passes.cpp:618-660`). The header
is denoted, not read as written (`J/j1`). Selection refuses two satisfiable candidates per demand ("incoherent impls (multiple
satisfiable)", `D/ImplResolution.cpp:148-170`, `374-400`; `T/invalid_allegation_ambiguous.mlir`); the frontend refuses two viable impls per
demand and rechecks concrete self applications after publication (`S/src/analysis/impls/environment.rs:1427-1431`, `1461-1507`). Two impls
of one ground application are legal declarations in both (`T/invalid_coerce_masked_swap.mlir:14-15`,
`T/one_callee_called_with_two_impls_of_one_claim_runs_each.mlir`), so `Coherent(S)` is a hypothesis (F18); generic overlap at no demanded
instance is judged by neither (`S/tests/src/14_129_illegal_blanket_impls_overlap_on_one_instance.expected_failure`; rustc's E0119
refuses it) (F19).
In words: under a coherent signature every closed term for an application has, up to denotation of the arguments, the unique server
as its root; so `trait.method.call` through any two such terms resolves to one method.
```
Coherent(S), H1-H5.   e allege-free,  M; [] |- e : T[a] (by c)?,  [[T[a]]] defined
    =>   root(e) = (I, s) with ServedBy(S, T[a], I, s);   hence [[root(e1)]] = [[root(e2)]] for any two such terms
```
Induction on the typing derivation. DERIVE: `root = (I, s)`, the premises valid by theorem 3, so `(I, s)` serves `hdr_I[s] = T[a]`;
unique by hypothesis. WIT-APP: a proof's body is closed, induction through H2; an unconditional impl serves its header. COERCE: `root`
is preserved and `[[T[a]]] = [[T[b]]]` by theorem 7 on the cited equalities. PROJECT-REQ: the root is that of the impl's return at `k`
under `s` and the derive's operands; by H3 that return is a closed term for `rho_k[h[s]]`, whose denotation is `[[D]]`, and induction
gives the unique server. PROJECT-WHERE: inversion. Equality arms carry no root. Stuckey-Sulzmann: coherence as confluence with no
critical pairs.
Without the hypothesis: `T/one_callee_called_with_two_impls_of_one_claim_runs_each.mlir` has two closed terms for `Tr[i32]` with roots
`@One` and `@Two`, and the answer (16) depends on which each call carries. Inside a coherent `S` the one way to break the conclusion is
F1: a PROJECT-REQ result annotated with a proof of another application makes `evidenceOf` return a root serving a different
denotation than the term's claim (`R/q9` lowers `T[i32]` to `T_i64`'s method, 8 for 7); the rule as stated (root from the term, not the
annotation) does not have this failure. Without H4: an impl whose header spells an unserved projection and a blanket impl both bind
one associated type at that header, deriving `i32 = i64` closed and letting two closed terms for `V[i32]` root at `V_i32` and `V_i64`;
the stage refuses the standing projection at exit (F17).

### 6.4 Theorem 6, MINIMALITY
Independence: for each of `trait.derive`, `trait.project` (`k < |R_T|`), `trait.witness proj_resolve`, `trait.witness refl`,
`trait.coerce`, a signature, a context and a valid judgment every allege-free term for which uses the operation (cards 2, 3, 4, 4, 5),
each by case analysis on a term's last constructor. Correspondence:
```
(HYP) <-> block argument          (IMPL) <-> derive (k_I = 0 also witness @I: F8)      (REQ) <-> project, k < |R_T|
(REQ-A) <-> method @requirement_i / method.call (outside the six: F4)              (BIND) <-> witness proj_resolve
(REFL) <-> witness refl           (SYM)(TRANS)(CONG)(CONG-P)(NORM) <-> coerce on an equality claim (and compose: D1, F3)
(CONV) <-> coerce on an application claim        (RULE)(RULE-B) <-> allege, a cut into the generator-extended signature (F5)
(UNIF) cross-group <-> none (F6)
allege <-> none: the cut (theorem 4)             witness @p / proof <-> none: let (witness_is_let)
project, k >= |R_T| <-> none: inversion (D2)     compose <-> the equality rules, carried by coerce (D1)
```
The bijection is exact on {(IMPL), (REQ), (BIND), (REFL), (CONV)} <-> {derive, project, proj_resolve, refl, coerce-on-claims}. The
value arm of coerce is FC's cast with no counterpart in the predicate logic; its correctness is theorem 7. Redundancy: `M; G |-
compose(e) : (t1 = t2)` implies `M; G |- coerce (refl : t1 = t1) to (t1 = t2) via (e) : (t1 = t2)`, one direction. Let: a closed
allege-free term with a witness of `@p` has an equivalent term with `p`'s body in its place, same type up to the citation, same root
(H2 makes the substitution well founded). Inversion: the derive's operand in place of a projection past `|R_T|`. No "project-free"
clause: PROJECT-REQ is a rule, and card 3's witness has no project-free term.

### 6.5 Instantiation lemmas (what instantiate-monomorphs performs)
```
(subst-types)     WF(S), H5.   M; G |- e : C   =>   M; G[s] |- e[s] : C[s]      the clone rule: every claim predicate and every
                                                                                #trait.impl_args receives the variable bindings alone
                                                                                (D/Specialization.cpp:106-128; D/TraitTypes.hpp:44-78)
(subst-evidence)  M; G |- e : C,  for all k. M; D |- f_k : G(k)   =>   M; D |- e[f/G] : C    an instance's evidence parameters take the
                                                                                caller's proofs (D/Passes.cpp:1026-1087; D/Specialization.cpp:329-357)
```
Every premise is an identity after substitution or a closure fact, both stable under substitution of ground types for variables when
every header variable is below its arity and the constructor law commutes with substitution (H5; the dialect does not assume it and
re-verifies a cloned witness, `T/witness_clone_specialization.mlir`). A polymorphic `trait.allege` is reduced by (cut) at the instance.

### 6.6 Theorem 7, ERASURE
In words: a closed valid equality relates two written forms of one type, so a `trait.coerce` on a value changes nothing the value
carries, and every claim value carries nothing.
```
Coherent(S), H1, H3, H4, H5.   S; [] |- a = b in the denotable fragment,  [[a]] defined    =>    [[b]] defined and [[a]] = [[b]]
```
Induction on the derivation: (REFL)(SYM)(TRANS) are equality's; (CONG)(CONG-P) because `[[.]]` is a congruence; (BIND) is the definition's
projection clause with uniqueness of the server (H4 gives the server exists; `V/v3` is the (BIND) H4 excludes, at an argument no impl
serves, relating a defined type to an undefined one); (NORM) because the laws are context-free (H5); (HYP) vacuous; (REQ) absent under
H3 (4.3). Two counterexamples to weaker statements: without the fragment restriction, two impls binding one associated type at an
undenotable header derive `i32 = i64` with both sides defined (6.3); without H1, which the verifier now enforces, `claim<T[i32]> = i64` would be a legal hypothesis (`X/x6`).
For the operations: (erase) forwards a coerce's input, both types denoting one type, which after projection resolution means they
coincide (`EraseCoerceOp`; `T/erase_coerce_barrier.mlir`, `T/invalid_coerce_of_undischarged_evidence_is_refused_at_erasure.mlir`); a witness, derive, project
or proof carries no value and is erased (`:2091-2106`). Consistency (OutsideIn(X) Def. 3.1) is the corollary under the free algebra;
(NORM) is the one place the algebra is not free. Closed-only: under hypotheses `i32 = i64` is a legal premise and `coerce i32 to i64`
verifies (`Q/p35`), which is why erasure's entry judges every hypothesis and every cited equality rather than trusting the verifier.

## 7. Lean 4 skeleton

Standard library only; every `sorry` is phase B's. Decisions against the verifications: derivations are `Type`-valued (`Deriv`) so `elab`
recurses on them, `Valid` is their inhabitation; `HasType` takes `G` as an index (`projWhere` recurses at `[]`); the requirement list is the
dialect's plain list, binders apart; GAT labels are declared, not positional; the constructor law carries its axioms; selection is an
oracle `sel` whose soundness is a hypothesis, so `denote`, `ServedBy` and `Coherent` do not define one another; `Ok` restricts derivations
to denotable citations where theorems 5 and 7 need it; `Ty` has no claim constructor (H1). The model's grammar covers the types
predicates mention, and its substitutions are `Var -> Option Ty` (`Defs.lean`), so it covers the fragment in which no associated type is
bound to a claim-carrying type and no type parameter is instantiated at one. The tree admits both, the binding for the tuple dialect's
`Claims` and the instantiation where a generic function's parameter takes evidence
(`T/equality_a_substitution_states_over_evidence_unused_is_collected.mlir`), and selection refuses every predicate whose normal form reaches a claim (`isNoPredicateType`,
read by `readApplication`, `readEqualitySides` and a projection's associated-type arguments), so every predicate the tree proves lies in
the model's fragment (F10). The binder constructor (REQ-CALL) and the (REQ-A) rule are elided here and added in phase B by the pattern
of `derive`.

```lean
namespace Trait
abbrev TraitId := Nat   -- index into Sig.traits
abbrev ImplId  := Nat   -- index into Sig.impls
abbrev ProofId := Nat   -- index into Module.proofs
abbrev AssocId := Nat
abbrev Var     := Nat   -- the label of !trait.poly<i>
abbrev ConId   := Nat   -- any non-trait type constructor

inductive Ty where      -- TraitTypes.td; no claim constructor (H1, F10)
  | var  : Var -> Ty
  | con  : ConId -> List Ty -> Ty
  | proj : TraitId -> List Ty -> AssocId -> List Ty -> Ty
  deriving Repr
instance : Inhabited Ty := ⟨.con 0 []⟩

/-- Substitution by label; one pass (TraitTypes.hpp:824-831). A citation's positional arguments are `ofList`; a binding's declared
GAT labels extend them (TraitOps.cpp:1908-1938). -/
abbrev Subst := Var -> Option Ty
def Subst.ofList (σ : List Ty) : Subst := fun i => σ.get? i
def Subst.extend (σ : Subst) (labels : List Var) (gs : List Ty) : Subst :=
  fun i => match (labels.zip gs).find? (·.1 = i) with | some (_, g) => some g | none => σ i
mutual
  def Ty.subst (σ : Subst) : Ty -> Ty
    | .var i          => (σ i).getD (.var i)
    | .con c as       => .con c (substList σ as)
    | .proj t as a gs => .proj t (substList σ as) a (substList σ gs)
  def substList (σ : Subst) : List Ty -> List Ty
    | []      => []
    | a :: as => a.subst σ :: substList σ as
end
def Ty.ground : Ty -> Bool := sorry

inductive Pred where
  | app : TraitId -> List Ty -> Pred
  | eq  : Ty -> Ty -> Pred       -- ordered as written, read direction-blind
  deriving Repr
instance : Inhabited Pred := ⟨.app 0 []⟩
def Pred.subst (σ : Subst) : Pred -> Pred
  | .app t as => .app t (substList σ as)
  | .eq a b   => .eq (a.subst σ) (b.subst σ)

inductive Cite where | proof : ProofId -> Cite | impl : ImplId -> Cite     -- TraitOps.cpp:2118-2131
  deriving DecidableEq, Repr
structure Claim where
  pred : Pred
  cite : Option Cite := none
  deriving Repr
def Claim.WF : Claim -> Prop | ⟨.eq _ _, some _⟩ => False | _ => True    -- TraitTypes.cpp:224-235
def Claim.strip (c : Claim) : Claim := { c with cite := none }

structure Binder where (labels : List Var) (premises : List Pred) (concl : Pred)   -- a `trait.method @requirement_i`
structure TraitDecl where
  arity   : Nat                 -- parameters 0..arity-1, Self first (TraitOps.cpp:404-420)
  reqs    : List Pred           -- R_T, the result list (TraitOps.td:161-164)
  binders : List Binder         -- B_T
  assocs  : List (List Var)     -- per associated type, its declared parameter labels
structure ImplDecl where
  arity    : Nat                             -- dense labels (TraitOps.cpp:890-894)
  trait    : TraitId
  head     : List Ty
  wheres   : List Pred                       -- block arguments 1..k (TraitOps.cpp:877-889)
  bindings : List (Option (List Var × Ty))   -- per associated type: declared GAT labels and the bound type (V/v6)
structure Sig where (traits : List TraitDecl) (impls : List ImplDecl)
def ImplDecl.header (I : ImplDecl) (σ : Subst) : Pred := .app I.trait (substList σ I.head)
def ImplDecl.unconditional (I : ImplDecl) : Prop := I.arity = 0 ∧ I.wheres = []
def Sig.DeclWF (S : Sig) : Prop := sorry   -- TraitOp::verify (397-501), ImplOp::verify/verifySymbolUses (871-898, 1004-1089, 826-869)

/-- H5: the constructor laws (NORM) (EqualityVerification.cpp:176-248). -/
structure ConLaw where
  law     : Ty -> Ty -> Prop
  onCon   : ∀ a b, law a b -> ∃ c as, a = Ty.con c as                  -- only type constructors normalize (:197-205)
  substOk : ∀ (σ : Subst) a b, law a b -> law (a.subst σ) (b.subst σ)   -- needed by subst_types
def freeAlgebra : ConLaw := ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ _ h => h.elim⟩

/-- Ground equational consequence, `entailedByGroundCongruence` (EqualityVerification.cpp:98-276); no decomposition. -/
inductive Entails (L : ConLaw) (E : List (Ty × Ty)) : Ty -> Ty -> Prop where
  | ax    : (a, b) ∈ E -> Entails L E a b
  | refl  : Entails L E a a
  | symm  : Entails L E a b -> Entails L E b a
  | trans : Entails L E a b -> Entails L E b c -> Entails L E a c
  | con   : as.length = bs.length -> (∀ i, i < as.length -> Entails L E (as.getD i default) (bs.getD i default)) ->
            Entails L E (.con c as) (.con c bs)
  | proj  : as.length = bs.length -> gs.length = hs.length ->
            (∀ i, i < as.length -> Entails L E (as.getD i default) (bs.getD i default)) ->
            (∀ i, i < gs.length -> Entails L E (gs.getD i default) (hs.getD i default)) ->
            Entails L E (.proj t as a gs) (.proj t bs a hs)
  | law   : L.law a b -> Entails L E a b
inductive PredEntails (L : ConLaw) (E : List (Ty × Ty)) : Pred -> Pred -> Prop where   -- modulo citation (:30-43)
  | app : as.length = bs.length -> (∀ i, i < as.length -> Entails L E (as.getD i default) (bs.getD i default)) ->
          PredEntails L E (.app t as) (.app t bs)
  | eq  : Entails L E a c -> Entails L E b d -> PredEntails L E (.eq a b) (.eq c d)

/-- `Env(G)`: hypotheses and their plain requirements (chalk's FromEnv). -/
inductive Env (S : Sig) (Γ : List Pred) : Pred -> Prop where
  | hyp : P ∈ Γ -> Env S Γ P
  | req : Env S Γ (.app t as) -> (ht : t < S.traits.length) -> (hk : k < S.traits[t].reqs.length) ->
          Env S Γ ((S.traits[t].reqs[k]).subst (Subst.ofList as))

/-- Derivations `S; G |- P` (4.1), Type-valued. `full = false` is the primitive fragment; `Ok i σ` restricts impl citations (H4). -/
inductive Deriv (L : ConLaw) (S : Sig) (full : Bool) (Ok : ImplId -> Subst -> Prop) (Γ : List Pred) : Pred -> Type where
  | env   : Env S Γ P -> Deriv L S full Ok Γ P
  | impl  : (hi : i < S.impls.length) -> (σ : List Ty) -> σ.length = S.impls[i].arity -> Ok i (Subst.ofList σ) ->
            (∀ W ∈ S.impls[i].wheres, Deriv L S full Ok Γ (W.subst (Subst.ofList σ))) ->
            Deriv L S full Ok Γ (S.impls[i].header (Subst.ofList σ))
  | req   : full = true -> Deriv L S full Ok Γ (.app t as) -> (ht : t < S.traits.length) -> (hk : k < S.traits[t].reqs.length) ->
            Deriv L S full Ok Γ ((S.traits[t].reqs[k]).subst (Subst.ofList as))
  | bind  : (hi : i < S.impls.length) -> (σ : List Ty) -> σ.length = S.impls[i].arity -> Ok i (Subst.ofList σ) ->
            (∀ W ∈ S.impls[i].wheres, Deriv L S full Ok Γ (W.subst (Subst.ofList σ))) ->
            S.impls[i].bindings[a]? = some (some (labels, B)) ->
            Deriv L S full Ok Γ (.eq (.proj S.impls[i].trait (substList (Subst.ofList σ) S.impls[i].head) a gs)
                                   (B.subst ((Subst.ofList σ).extend labels gs)))
  | refl  : Deriv L S full Ok Γ (.eq a a)
  | symm  : Deriv L S full Ok Γ (.eq a b) -> Deriv L S full Ok Γ (.eq b a)
  | trans : Deriv L S full Ok Γ (.eq a b) -> Deriv L S full Ok Γ (.eq b c) -> Deriv L S full Ok Γ (.eq a c)
  | cong  : as.length = bs.length -> (∀ i, i < as.length -> Deriv L S full Ok Γ (.eq (as.getD i default) (bs.getD i default))) ->
            Deriv L S full Ok Γ (.eq (.con c as) (.con c bs))
  | congP : as.length = bs.length -> gs.length = hs.length ->
            (∀ i, i < as.length -> Deriv L S full Ok Γ (.eq (as.getD i default) (bs.getD i default))) ->
            (∀ i, i < gs.length -> Deriv L S full Ok Γ (.eq (gs.getD i default) (hs.getD i default))) ->
            Deriv L S full Ok Γ (.eq (.proj t as a gs) (.proj t bs a hs))
  | norm  : L.law a b -> Deriv L S full Ok Γ (.eq a b)
  | conv  : Deriv L S full Ok Γ (.app t as) -> as.length = bs.length ->
            (∀ i, i < as.length -> Deriv L S full Ok Γ (.eq (as.getD i default) (bs.getD i default))) ->
            Deriv L S full Ok Γ (.app t bs)
abbrev AnyImpl : ImplId -> Subst -> Prop := fun _ _ => True
abbrev Valid  (L : ConLaw) (S : Sig) (Γ : List Pred) (P : Pred) : Prop := Nonempty (Deriv L S true AnyImpl Γ P)
abbrev ValidP (L : ConLaw) (S : Sig) (Γ : List Pred) (P : Pred) : Prop := Nonempty (Deriv L S false AnyImpl Γ P)
/-- H3 (ReqDuty), plain requirements; the binder clause is added with (REQ-A) in phase B. -/
def Sig.ReqDuty (L : ConLaw) (S : Sig) : Prop :=
  ∀ i (hi : i < S.impls.length) (ht : S.impls[i].trait < S.traits.length) k (hk : k < (S.traits[S.impls[i].trait]).reqs.length),
    ValidP L S S.impls[i].wheres (((S.traits[S.impls[i].trait]).reqs[k]).subst (Subst.ofList S.impls[i].head))

/-- Evidence terms: one constructor per operation and the hypothesis. -/
inductive Ev where
  | hyp     : Nat -> Ev
  | allege  : Claim -> Ev
  | derive  : ImplId -> List Ty -> List Ev -> Ev
  | project : Ev -> Nat -> Ev
  | witness : Cite -> Pred -> Ev
  | projRes : ImplId -> List Ty -> List Ev -> AssocId -> List Ty -> Ev
  | refl    : Ty -> Ev
  | compose : List Ev -> Ty -> Ty -> Ev            -- D1
  | coerce  : Ev -> List Ev -> Claim -> Ev         -- claim arm
  deriving Inhabited
def Ev.allegeFree : Ev -> Prop := sorry
def Ev.cites : Ev -> List ProofId := sorry
def Ev.uses (e : Ev) (f : Ev -> Bool) : Prop := sorry
structure Module where (sig : Sig) (proofs : List (Pred × Ev))   -- a proof: its application and its returned term
def Module.proofDerive (M : Module) (p : ProofId) : Option (ImplId × List Ty × List Ev) := sorry   -- ProofOp::getDerive

/-- Typing `M; G |- e : C`, one rule per card; `G` an index; results of derive, projReq, allege unproven (F1). -/
inductive HasType (L : ConLaw) (M : Module) (Ok : ImplId -> Subst -> Prop) : List Claim -> Ev -> Claim -> Prop where
  | hyp     : (hk : k < Γ.length) -> HasType L M Ok Γ (.hyp k) Γ[k]
  | derive  : (hi : i < M.sig.impls.length) -> σ.length = M.sig.impls[i].arity -> Ok i (Subst.ofList σ) ->
              es.length = M.sig.impls[i].wheres.length ->
              (∀ j, j < es.length -> ∃ π, HasType L M Ok Γ (es.getD j default)
                  ⟨(M.sig.impls[i].wheres.getD j default).subst (Subst.ofList σ), π⟩) ->
              HasType L M Ok Γ (.derive i σ es) ⟨M.sig.impls[i].header (Subst.ofList σ), none⟩       -- TraitOps.cpp:2413-2431
  | projReq : HasType L M Ok Γ e ⟨.app t as, π⟩ -> (ht : t < M.sig.traits.length) -> (hk : k < M.sig.traits[t].reqs.length) ->
              HasType L M Ok Γ (.project e k) ⟨(M.sig.traits[t].reqs[k]).subst (Subst.ofList as), none⟩   -- TraitTypes.cpp:448-455
  | projWhere : HasType L M Ok Γ e ⟨.app t as, some (.proof p)⟩ -> (ht : t < M.sig.traits.length) ->
              M.proofDerive p = some (i, σ, ds) -> (hj : j < ds.length) -> HasType L M Ok [] (ds.getD j default) c ->
              HasType L M Ok Γ (.project e (M.sig.traits[t].reqs.length + j)) c                        -- TraitTypes.cpp:457-464 (D2)
  | witProof : (hp : p < M.proofs.length) -> M.proofs[p].1 = P ->
              HasType L M Ok Γ (.witness (.proof p) P) ⟨P, some (.proof p)⟩                            -- TraitTypes.cpp:362-382
  | witImpl : (hi : i < M.sig.impls.length) -> M.sig.impls[i].unconditional ->
              HasType L M Ok Γ (.witness (.impl i) (M.sig.impls[i].header (Subst.ofList [])))
                ⟨M.sig.impls[i].header (Subst.ofList []), some (.impl i)⟩                              -- TraitOps.cpp:1107-1113
  | projRes : (hi : i < M.sig.impls.length) -> σ.length = M.sig.impls[i].arity -> Ok i (Subst.ofList σ) ->
              es.length = M.sig.impls[i].wheres.length ->
              (∀ j, j < es.length -> ∃ π, HasType L M Ok Γ (es.getD j default)
                  ⟨(M.sig.impls[i].wheres.getD j default).subst (Subst.ofList σ), π⟩) ->
              M.sig.impls[i].bindings[a]? = some (some (labels, B)) -> gs.length = labels.length ->
              HasType L M Ok Γ (.projRes i σ es a gs)
                ⟨.eq (.proj M.sig.impls[i].trait (substList (Subst.ofList σ) M.sig.impls[i].head) a gs)
                     (B.subst ((Subst.ofList σ).extend labels gs)), none⟩                              -- TraitOps.cpp:2433-2460
  | refl    : HasType L M Ok Γ (.refl a) ⟨.eq a a, none⟩                                                -- TraitOps.cpp:2319-2326
  | compose : es ≠ [] -> E.length = es.length ->
              (∀ j, j < es.length -> HasType L M Ok Γ (es.getD j default) ⟨.eq (E.getD j default).1 (E.getD j default).2, none⟩) ->
              Entails L E l r -> HasType L M Ok Γ (.compose es l r) ⟨.eq l r, none⟩                     -- TraitOps.cpp:2337-2373
  | coerce  : HasType L M Ok Γ e ⟨P, π⟩ -> E.length = es.length ->
              (∀ j, j < es.length -> HasType L M Ok Γ (es.getD j default) ⟨.eq (E.getD j default).1 (E.getD j default).2, none⟩) ->
              (π' = none ∨ π' = π) -> Claim.WF ⟨P', π'⟩ -> PredEntails L E P P' ->
              HasType L M Ok Γ (.coerce e es ⟨P', π'⟩) ⟨P', π'⟩                                          -- TraitOps.cpp:2607-2662
  -- no rule for `allege`: the cut (theorem 4b). The value arm of coerce is `Entails L E a b` alone (theorem 7).

def ProofsWF (L : ConLaw) (M : Module) : Prop :=        -- H2; the citation clause no verifier enforces (F2)
  ∀ p (hp : p < M.proofs.length),
    (∃ π, HasType L M AnyImpl [] M.proofs[p].2 ⟨M.proofs[p].1, π⟩) ∧ M.proofs[p].2.allegeFree ∧ (∀ q ∈ M.proofs[p].2.cites, q < p)
def GammaWF (M : Module) (Γ : List Claim) : Prop :=     -- Passes.cpp:278-291 (F1)
  ∀ c ∈ Γ, ∀ p, c.cite = some (.proof p) -> ∃ hp : p < M.proofs.length, M.proofs[p].1 = c.pred

theorem soundness (L : ConLaw) (M : Module) (hS : M.sig.DeclWF) (hP : ProofsWF L M) (hΓ : GammaWF M Γ)
    (he : e.allegeFree) (ht : HasType L M Ok Γ e c) : Valid L M.sig (Γ.map Claim.pred) c.pred := by sorry
theorem req_admissible (L : ConLaw) (S : Sig) (hS : S.DeclWF) (hD : S.ReqDuty L) : Valid L S Γ P -> ValidP L S Γ P := by sorry
def elab (L : ConLaw) (M : Module) : Deriv L M.sig true AnyImpl Γ P -> Ev := sorry   -- emit + the stage's writer
theorem completeness (L : ConLaw) (M : Module) (hS : M.sig.DeclWF) (hP : ProofsWF L M) (d : Deriv L M.sig true AnyImpl Γ P) :
    ∃ M', M'.sig = M.sig ∧ ProofsWF L M' ∧ (elab L M d).allegeFree ∧
      HasType L M' AnyImpl (Γ.map (⟨·, none⟩)) (elab L M d) ⟨P, none⟩ := by sorry
theorem cut_admissible (L : ConLaw) (M : Module) (hS : M.sig.DeclWF) (hP : ProofsWF L M) (h : Valid L M.sig [] P) :
    ∃ M' e, M'.sig = M.sig ∧ e.allegeFree ∧ HasType L M' AnyImpl [] e ⟨P, none⟩ := by sorry
def Ev.substTy (σ : Subst) : Ev -> Ev := sorry
def Ev.substHyp (fs : Nat -> Ev) : Ev -> Ev := sorry
def Claim.subst (σ : Subst) (c : Claim) : Claim := { c with pred := c.pred.subst σ }
theorem subst_types (L : ConLaw) (M : Module) (hS : M.sig.DeclWF) (ht : HasType L M Ok Γ e c) :
    HasType L M Ok (Γ.map (Claim.subst σ)) (e.substTy σ) (c.subst σ) := by sorry
theorem subst_evidence (L : ConLaw) (M : Module) (ht : HasType L M Ok Γ e c)
    (hd : ∀ k (hk : k < Γ.length), HasType L M Ok Δ (fs k) Γ[k]) : HasType L M Ok Δ (e.substHyp fs) c := by sorry

/-! Denotation through an oracle `sel` (the stage's `resolveImplFor`, ImplResolution.cpp:172-401); its soundness is a hypothesis. -/
abbrev Sel := Pred -> Option (ImplId × List Ty)
def denote (sel : Sel) (L : ConLaw) (S : Sig) : Nat -> Ty -> Option Ty := sorry          -- fuel; the stage's bound is 128
def denotePred (sel : Sel) (L : ConLaw) (S : Sig) (fuel : Nat) : Pred -> Option Pred := sorry
def Den (sel : Sel) (L : ConLaw) (S : Sig) (fuel : Nat) : ImplId -> Subst -> Prop :=
  fun i σ => ∃ hi : i < S.impls.length, (denotePred sel L S fuel (S.impls[i].header σ)).isSome
abbrev ValidD (sel : Sel) (L : ConLaw) (S : Sig) (fuel : Nat) (Γ : List Pred) (P : Pred) : Prop :=
  Nonempty (Deriv L S true (Den sel L S fuel) Γ P)
def ServedBy (sel : Sel) (L : ConLaw) (S : Sig) (fuel : Nat) (P : Pred) (i : ImplId) (σ : List Ty) : Prop :=
  ∃ hi : i < S.impls.length, σ.length = S.impls[i].arity ∧ (denotePred sel L S fuel P).isSome ∧
    denotePred sel L S fuel (S.impls[i].header (Subst.ofList σ)) = denotePred sel L S fuel P ∧
    (∀ W ∈ S.impls[i].wheres, ValidD sel L S fuel [] (W.subst (Subst.ofList σ)))
def SelSound (sel : Sel) (L : ConLaw) (S : Sig) (fuel : Nat) : Prop := ∀ P i σ, sel P = some (i, σ) -> ServedBy sel L S fuel P i σ
def Sig.Coherent (sel : Sel) (L : ConLaw) (S : Sig) (fuel : Nat) : Prop :=     -- up to denotation of σ (V/v5, X/x4)
  ∀ t as, as.all Ty.ground -> (denotePred sel L S fuel (.app t as)).isSome ->
    ∀ i σ j σ', ServedBy sel L S fuel (.app t as) i σ -> ServedBy sel L S fuel (.app t as) j σ' ->
      i = j ∧ σ.map (denote sel L S fuel) = σ'.map (denote sel L S fuel)
def root (M : Module) : Ev -> Option (ImplId × List Ty) := sorry   -- evidenceOf, getRootOf, readEvidence (5.4)
theorem coherence (sel : Sel) (L : ConLaw) (M : Module) (fuel : Nat) (hS : M.sig.DeclWF) (hD : M.sig.ReqDuty L)
    (hP : ProofsWF L M) (hSel : SelSound sel L M.sig fuel) (hC : M.sig.Coherent sel L fuel)
    (he : e.allegeFree) (ht : HasType L M (Den sel L M.sig fuel) [] e ⟨.app t as, π⟩)
    (hden : (denotePred sel L M.sig fuel (.app t as)).isSome) :
    ∃ i σ, root M e = some (i, σ) ∧ ServedBy sel L M.sig fuel (.app t as) i σ := by sorry
  -- corollary: two such terms' roots agree after `denote` is mapped over their arguments
theorem erasure (sel : Sel) (L : ConLaw) (S : Sig) (fuel : Nat) (hS : S.DeclWF) (hD : S.ReqDuty L)
    (hSel : SelSound sel L S fuel) (hC : S.Coherent sel L fuel) (h : ValidD sel L S fuel [] (.eq a b))
    (d : Ty) (ha : denote sel L S fuel a = some d) : denote sel L S fuel b = some d := by sorry

def Ev.isDerive  : Ev -> Bool | .derive .. => true | _ => false
def Ev.isProject : Ev -> Bool | .project .. => true | _ => false
def Ev.isProjRes : Ev -> Bool | .projRes .. => true | _ => false
def Ev.isRefl    : Ev -> Bool | .refl .. => true | _ => false
def Ev.isCoerce  : Ev -> Bool | .coerce .. => true | _ => false
theorem independence_derive : ∃ (M : Module) Γ P, Valid freeAlgebra M.sig (Γ.map Claim.pred) P ∧
    ∀ e, e.allegeFree -> HasType freeAlgebra M AnyImpl Γ e ⟨P, none⟩ -> e.uses Ev.isDerive := by sorry    -- card 2
theorem independence_project : ∃ (M : Module) Γ P, Valid freeAlgebra M.sig (Γ.map Claim.pred) P ∧
    ∀ e, e.allegeFree -> HasType freeAlgebra M AnyImpl Γ e ⟨P, none⟩ -> e.uses Ev.isProject := by sorry   -- card 3
theorem independence_projRes : ∃ (M : Module) P, Valid freeAlgebra M.sig [] P ∧
    ∀ e, e.allegeFree -> HasType freeAlgebra M AnyImpl [] e ⟨P, none⟩ -> e.uses Ev.isProjRes := by sorry   -- card 4
theorem independence_refl : ∃ (M : Module) P, Valid freeAlgebra M.sig [] P ∧
    ∀ e, e.allegeFree -> HasType freeAlgebra M AnyImpl [] e ⟨P, none⟩ -> e.uses Ev.isRefl := by sorry      -- card 4
theorem independence_coerce : ∃ (M : Module) Γ P, Valid freeAlgebra M.sig (Γ.map Claim.pred) P ∧
    ∀ e, e.allegeFree -> HasType freeAlgebra M AnyImpl Γ e ⟨P, none⟩ -> e.uses Ev.isCoerce := by sorry    -- card 5
theorem compose_derivable (L : ConLaw) (M : Module) :      -- D1, one direction (X/x1a, x1b refute the converse)
    HasType L M Ok Γ (.compose es l r) ⟨.eq l r, none⟩ ->
    HasType L M Ok Γ (.coerce (.refl l) es ⟨.eq l r, none⟩) ⟨.eq l r, none⟩ := by sorry
def Ev.inlineProofs (M : Module) : Ev -> Ev := sorry
theorem witness_is_let (L : ConLaw) (M : Module) (hP : ProofsWF L M) (ht : HasType L M Ok Γ e c) :
    HasType L M Ok Γ (e.inlineProofs M) c.strip ∧ root M (e.inlineProofs M) = root M e := by sorry
-- D2: a projection past |R_T| is the derive's operand in its place; phase B states the inlined term.
end Trait
```
Standard library only; a ground congruence-closure decision procedure for `Entails` would let phase B check the probes by `decide`; it is an implementation, not a theorem.

## 8. Findings

Most severe first: severity; the defect in one sentence; evidence (anchors, the program or lit test); what the calculus does with it.
"Verifies" means `mlir-opt` with the plugin and no pass accepts the file; "lowers" means `monomorphize-trait` succeeds.

**F1 (high; dispatch, well-formedness).** A proven claim's citation is checked against its application only at `trait.witness` and, by
the stage, on module-level `func.func` signatures; the result of `trait.project` at a trait requirement, the generic forms of
`trait.derive` and `trait.allege`, a where-entry projection off an unproven derive operand, and any other block argument may name a
proof of another application, and `trait.method.call` dispatches on it. Evidence: `ClaimType::verifySymbolUses` checks only that the
symbol resolves (`D/TraitTypes.cpp:266-269`); `verifyCitation` (`:362-382`) is called from `D/TraitOps.cpp:2489` and `D/Passes.cpp:286` alone;
`ProjectOp` compares a trait requirement `asUnproven` (`D/TraitOps.cpp:3159-3163`); `evidenceOf` returns the first cited claim it meets
(`:1530-1540`). Programs: `R/q9` (`trait.project %h[0] : <@Has[i32] by @Has_i32> -> <@T[i32] by @T_i64>` verifies and lowers to `call @T_i64_..._m`, 8, under a receiver written `@T[i32]` whose impl answers 7); `R/p1`, `R/p2`, `R/p3b`; `W/b1` (inside a proof the written citation is ignored); `W/f1`, `P/s5` (a parameter `<@T[i32] by @T_i64>` verifies; only the stage refuses it); `X/x5`, `V/v4` (a where-entry result naming another proof when the derive's operand is unproven). Reachable from the frontend: no
(`S/src/codegen/mlir/generator.rs:1897-1900`, `1916-1931`, `1938-1944` emit unproven results). The calculus: PROJECT-REQ, DERIVE and ALLEGE
conclude unproven; `root` is computed from the term; G-WF is a hypothesis. Fix: the result constraints `D/TraitOps.td:897`, `:961` become
unproven-claim constraints; `ProjectOp` refuses a citation on a trait-requirement result; `verifyCitation` runs on every claim-typed
block argument, methods included (`D/Passes.cpp:284-285` says "not yet covered"). Not on every claim type: a coerce result legitimately
carries its input's citation to another written form (`T/coerce_claim_respell.mlir`; `D/ImplResolution.cpp:578-619`) (F7).

**F2 (high; soundness against the inductive logic).** The verifier accepts a `trait.proof` that cites itself through a where entry and
the stage lowers it, while selection refuses the same application as a cycle and the frontend's solver is inductive; theorem 3 is
false without H2's well-founded-citation clause, which nothing enforces. Evidence: `R/p14_self_citing_proof.mlir` (`impl<T: Foo> Foo for T`; a proof deriving `@Foo[i32]` from a witness of itself) verifies and lowers `main` to `call @Foo_all_..._m`; `R/p15` alleges `@Foo[i32]`, refused "no impl with satisfiable assumptions" (`D/ImplResolution.cpp:239-250`); `verifyProofDerivationsEnd` counts a proof cited again at an application on its chain as zero (`D/Passes.cpp:293-373`); the frontend's `ChainPolicy::cut` (`S/src/analysis/impls/environment.rs:207-224`). The case the zero-count was written for (`T/coinductive_proof.mlir`: an impl returns a coerce of its own witness for a requirement over its own projection) passes through no where entry and no proof's citation of itself; the inductive logic handles it by (IMPL) with no premises plus (CONV). Decision for the owner: refuse the repeat in `verifyProofDerivationsEnd` (or in `ProofOp`, a derive whose application premise roots at the enclosing proof), keeping the logic inductive as rustc's non-auto traits and the frontend are; or state the logic coinductively and make selection coinductive to match. This document takes the inductive reading.

**F3 (medium; minimality).** `trait.witness compose` is derivable from `trait.coerce` on a `refl` witness (card 4, D1); two constructors
for one conclusion. The deletion needs D1's barrier amendment (`V/v1a` lowers, `V/v1b` fails); the rules-first draft's claim that the
barrier difference "fires only where an equality has no evidence after resolution" is refuted by `V/v1b`.

**F4 (medium; a rule with no constructor among the six).** A requirement quantified over its own variables is introduced by a
`trait.method @requirement_i` and eliminated by a claim-returning `trait.method.call`, neither in the brief's list. Evidence:
`D/TraitOps.td:1020-1021` ("called rather than projected"), `:1438-1455`; `D/TraitOps.cpp:1477-1506`; `S/src/codegen/mlir/generator.rs:928-962`,
`1902-1914`; `S/src/evidence/contract.rs:154-177`; `T/evidence_method_states_a_quantified_requirement_and_lowers_with_its_consumer.mlir`;
`S/tests/src/15_12_illegal_gat_use_misses_a_bound_premise.src`. The calculus adds the pair as its seventh constructor (REQ-CALL); its
soundness is the method's body typed under the binder's premises (H3's binder clause).

**F5 (medium; trust).** The frontend's (RULE) and (RULE-B) have no constructor; `trait.allege` carries no justification and the stage
proves it by whichever impl selection finds, including impls the dialects' generators write, so soundness of compiler-rule evidence
rests on the generators and completeness is relative to the generated signature. Evidence: `S/src/codegen/mlir/generator.rs:1938-1944`,
`2006-2010`; `S/src/types/auto_impl_rule.rs:14-29`; `D/ImplResolution.cpp:336-364`; `allegeRequirements`, `D/TraitOps.cpp:1091-1105`; the ruling,
`S/docs/plans/EVIDENCE_TERMS_AUDIT.md:66`. A rule's consulted premises are not transcribed, so the dialect cannot check them.
Owner, 2026-10-22: "I understand that allege is trusted." F5 records where the trust sits, by the ruling; it asks for no change.

**F6 (medium; a rule with no constructor).** The frontend's cross-group uniform collapse `(T/G1)/G2 = T/max(G1, G2)` rests on nothing and
has no dialect claim; codegen returns the inner value with no `trait.coerce` where the collapsed forms agree. Evidence:
`S/src/types/kinds/uniform.rs:38-63`; `S/src/evidence/term.rs:396-401`; `S/src/codegen/mlir/generator.rs:2101-2110` (XXX TODO naming row
`45_03_ground_canonicalization_preserves_pair_spelling`); same-group collapse is a constructor law (`UniformType::get`,
`/home/jhoberock/dev/git/mlir-coop-dialect/cpp/CoopTypes.cpp:43-59`) covered by (NORM); the cross-group fold is a type sweep after
monomorphization (`CoopTypes.cpp:198-225`). Either a constructor law or an equality leaf is missing.

**F7 (low; proven claims under COERCE).** A coerce may carry a citation to a different application (`Q/p20`: `<@T[i32] by @T_i32>` to
`<@T[i64] by @T_i32>` via `i32 = i64` accepted); the result names a declaration proving `@T[i32]`. The stage treats it as transient and
writes a cast proof when a foreign op reads it (`D/Passes.cpp:1098-1141`; `D/ImplResolution.cpp:578-619`). The calculus reads the citation on
a coerce result as the root annotation, checked by `verifyCitation` at WIT-APP and HYP only; "a claim names the proof of exactly its
own" written form (`D/TraitTypes.cpp:370-372`) is a statement about witnesses and hypotheses, not every claim type.

**F8 (low; overlap).** `trait.witness @I for hdr_I` with `I` unconditional and `trait.derive hdr_I from @I given()` type one claim up to
the citation and lower to one instance (`T/derive_of_an_unconditional_impl_is_the_impl_itself.mlir`, `P/s6`). Kept; one role per
constructor would make `derive` the only introduction from an impl and `witness` the only reference to a named closed term, with the
stage naming an unconditional impl's derive by the impl's own symbol as `findProof` does today (`D/ImplResolution.cpp:530-533`).

**F9 (low; completeness of the closure).** Congruence is forgone across a type constructor that declines placeholder arguments: such a
type is atomic to `GC` and a coerce needing it is refused (`D/EqualityVerification.cpp:77-95`: "deliberately forgone"). Theorem 4a excludes it.

**F10 (medium; semantics; representation fix; landed).** An equality endpoint could be an unproven claim type, so a hypothesis
`claim<P> = claim<P'>` would let `trait.coerce` convert evidence of `P` into evidence of `P'` with no equality between their arguments,
and `claim<P> = i64` would turn evidence into a value (`V/v2`, `X/x6`, `Q/p11`, `Q/p03c`). Erasure's entry had already refused both
shapes by judgment ("does not settle before erasure"). Landed: the rule `verifyEndpointsRelateTypes` refuses a claim inside an
endpoint, as an application refuses a claim argument, and every evidence op (allege, derive, project, witness, coerce) asks it of the evidence it reads and produces
(`EqualitiesRelateTypes`, an op verifier, which every verification runs), so no coerce cites such an equality
(`T/invalid_equality_over_evidence_naming_no_symbol.mlir`); the claim's symbol-use verifier asks it wherever an equality naming a symbol
stands (`T/invalid_claim_inside_an_equality_endpoint.mlir`), and erasure's entry judges one standing anywhere else, an inert signature
over builtin types, which the symbol-use walk does not reach. The rule was first an invariant of the attribute (`TypeEqualityAttr::verify`,
362cf96), which a clone's substitution and selection's normal forms rebuild and cannot fail: an instance substituting evidence into a
template's equality, and a respelling equality over an argument a binding resolves to evidence, aborted the compiler there. It then
lived in the symbol-use verifier alone (3a1498d), which never sees a type naming no symbol, so a hypothesis over builtin evidence let two
coerces turn an i32 into an i64 at verification. Now the attribute is built whatever its endpoints, and a substituted one an op reads or
produces is refused by the verifier after the step that wrote it
(`T/invalid_equality_a_substitution_states_over_evidence_is_refused.mlir`). An impl may still bind an associated type to a type
carrying claims -- the tuple dialect's mappers bind their `Claims` so, and Screech programs reach them -- and selection refuses every
predicate whose normal form reaches one, by one rule (`isNoPredicateType`): an application's arguments (`readApplication`, which
`resolveImplFor` reads before it selects and erasure's entry reads for a proof cited by hand), a projection's associated-type
arguments, and an equality's sides (`readEqualitySides`, which judges an impl's equality premise at selection too, as the proof citing the impl
reads it: every projection's associated-type arguments are judged before a binding is substituted for it, and a premise projecting
through the application being selected meets that selection again and refuses the impl, rustc's E0275), so no proof is written over
such a predicate, no impl is a candidate through such a premise
(`T/invalid_hypothesis_resting_on_an_impl_premise_through_its_own_application.mlir`,
`T/impl_premise_through_its_own_application_leaves_the_other_candidate.mlir`), and no resolution step
states an equality relating a claim (`T/invalid_equality_side_resolving_to_evidence_is_refused.mlir`,
`T/invalid_application_whose_argument_resolves_to_evidence_is_refused.mlir`). So H1 holds of every equality the tree states and every
predicate it proves, and not of bindings or substitutions: the Lean model covers the fragment in which no associated type is bound to a
claim-carrying type and no type parameter is instantiated at one, the tree admits both, and an equality over claims is refused by every
evidence op reading or producing it, wherever it names a symbol, wherever a side resolves to one, and at erasure's entry wherever it stands.
Three end states are consistent, and the choice among them is a decision after the Lean phase. In GHC's and Rust's, a
type carrying evidence (`Dict c`, `dyn Trait`) is an ordinary type everywhere, predicates may mention it, and the one soundness law is
the judgment at erasure's entry; the as-written and as-resolved refusals go and the model's `Ty` gains a claim constructor. In the
model's, no claim stands inside any type a predicate or a binding states, at the cost of re-representing the tuple dialect's `Claims`
(refusing such a binding failed 59 codegen rows and 7 rows each of the tuple and coord dialects). The third, the candidate, is the
shape GHC gives an associated type family whose results are constraints: an associated type declares its kind (`Constraint` against
`Type`). `trait.assoc_type` gains a kind, type or evidence, which the three symbol-use verifiers read off the declaration they already
look up, so an application argument, a GAT argument and an equality endpoint of evidence kind are refused as written; a binding whose
kind disagrees with its declaration is refused at the impl, and a type variable, of type kind, instantiated at evidence is refused at
the call. The tuple dialect's `Claims` is declared evidence-kinded and kept, and the evidence half of `isNoPredicateType`, the three
containment checks (an application's arguments, a projection's, an equality's endpoints) and the evidence ops' trait judging
equalities are deleted. The Lean `Ty` stays as it is while `TraitDecl.assocs` gains a kind and `ImplDecl.bindings` splits by it, which is why it
follows phase B. The capability the two deleted rows `T/generic_function_parameter_spelled_as_a_projection_takes_its_callers_proof.mlir`
and `T/method_parameter_spelled_as_a_projection_takes_its_callers_proof.mlir` exercised -- a formal spelled as a projection that
resolves to a claim, coerced into evidence through a requirement `@Wrap[T]::Item = claim<@Mark[T]>` -- is one no Screech construct
reaches: no Screech type lowers to a claim, and the frontend writes no equality over one.
`T/equality_over_a_type_carrying_a_claim_settles_at_erasure.mlir` went with them, and `T/equality_endpoint_claim_is_not_stamped.mlir`
keeps its projection case as `T/witness_equality_keeps_the_projection_it_was_minted_with.mlir`.

**F11 (low; documentation).** `D/TraitTypes.hpp:920-934` says a trait requirement of a proven claim is "read through the cited impl's own
bindings"; `getClaimRequirementAt` instantiates it at the unproven claim's arguments and reads no binding (`D/TraitTypes.cpp:448-455`).

**F12 (medium; SSA values as terms).** `DeriveOp` and `ProjectOp` carry no SSA-dominance check, so in a graph region a derive may be
given its own result (`X/x2`: `%d = trait.derive @Foo[i32] from @Foo_all[i32] given(%d)` in a module body verifies; the exit walk names it
"unproven monomorphic claim"; `X/x2b` with a consumer, the same), while compose and coerce have the check (`D/TraitOps.cpp:2353-2360`,
`:2616-2619`). Its predicate has no derivation; it is outside the calculus only because it is not a term. Fix: the same region check on
`DeriveOp::verify` and `ProjectOp::verify`.

**F13 (medium; H3 is not what the verifier enforces).** `verifyRequirementEvidence` (`D/TraitOps.cpp:774-810`) admits a return that is an
allegation and a pair of returns projecting one another with no base, so the impl well-formedness the verifier checks does not imply
the duty theorems 5 and 7 need. Evidence: `X/x9` (trait `Has` requires `Has[Self]::Out = i64`; `Has_i32` binds `Out = i32` and returns
`trait.allege Has[i32]::Out = i64`; verifies, both sides reading through the binding to `i32 = i64`; the stage refuses "resolves its sides
to 'i32' and 'i64'"); `X/x10`, `X/x3` (allege-free returns projecting each other, neither its own application; verify; refused "has no
base: it is read through the returns of @A_i32, @C_i32, @A_i32"); `X/x8` (an alleged application requirement, proved by selection); `J/j2`
(a return projecting a derived application through another impl: verifies, lowers; permitted by H3). In the logic the unsound
derivations are (IMPL), (REQ), (BIND) giving `i32 = i64` closed. H3 states the duty in the primitive fragment; the stage enforces it
(`readEvidence`, `D/TraitOps.cpp:1696-1767`; `proveAllegedEquality`, `D/Passes.cpp:711-744`); the verifier cannot without selection.

**F14 (observation).** The closure unites a composite with the normal form its constructor yields when a class member is substituted for
a child (`D/EqualityVerification.cpp:176-248`), under the stated, unenforced invariant of `:183-189`. The calculus carries it as `ConLaw`
(H5) with substitution stability; soundness of WIT-COMPOSE, COERCE and the instantiation lemma is relative to it.

**F15 (observation; inconsistency in kind).** The frontend decides equality by directed rows with a rigidity rule and a conflict policy;
the dialect by a class-based closure accepting contradictory hypotheses (`Q/p35`, `Q/p36`) and resolving every ground projection whatever
hypotheses stand. Under cyclic or contradictory where clauses the two accept different programs. Not a soundness defect; theorem 7 is
closed-only for this reason.

**F16 (observation).** The depth limits of 128 (5.5) are stage facts; theorem 4b is stated within them
(`T/invalid_obligation_recursion_hits_the_limit.mlir`, `T/evidence_read_through_128_returns_reaches_its_base.mlir`).

**F17 (observation; H4).** The verifier admits a citation at arguments no impl serves (`V/v3`: a `proj_resolve` by `@T_all[!trait.proj<@U[i64],
"Item">]` with no impl of `@U` verifies) and an impl header spelling a projection (`J/j1`); denotation is a selection fact the verifier
cannot compute ("Verification is always local"); the exit walk refuses the standing projection (`D/Passes.cpp:1962-1990`). Theorems 5 and
7 are stated on the denotable fragment the stage accepts, by design rather than defect.

**F18 (observation).** Coherence is not a verifier invariant: two impls of one ground application and two witnesses through them verify
and run both impls (`T/one_callee_called_with_two_impls_of_one_claim_runs_each.mlir`, 16; `T/invalid_coerce_masked_swap.mlir:14-15`). The
dialect guarantees that selection refuses two satisfiable candidates per demand and dispatch follows the term's root; theorem 5 is
conditional on `Coherent(S)`, per denotable ground application, servers compared up to denotation (`V/v5`, `X/x4`).

**F19 (observation).** Generic overlap at no demanded instance is unjudged at both ends
(`S/tests/src/14_129_illegal_blanket_impls_overlap_on_one_instance.expected_failure`; rustc's E0119 refuses it).

**F20 (low; anchors in the drafts, corrected here).** Lit-test lines in the rules-first draft were off by two in three tests
(`invalid_derive_states_its_impl_arguments.mlir` 14/30/43/59; `invalid_bound_evidence.mlir` 80/100; `invalid_coerce_masked_swap.mlir`
14-15/28/57); `EVIDENCE_TERMS_AUDIT.md`'s ruling is at line 66. The ops-first draft's "by identity at four places only" omitted a method's
`trait.return` (`D/TraitOps.cpp:2573-2585`).

No further finding at any severity in the verifiers of `trait.witness refl`, `trait.witness proj_resolve`, the value arm of
`trait.coerce`, the two consumers, the three types and the three attributes: every refusal probe was refused with the diagnostic its
verifier states, and every acceptance is an instance of a rule in section 1 or 5.

## 9. Prior art, and what was copied

Wadler and Blott 1989 (dictionary-passing translation driven by typing derivations; here the target is the IR: a claim block argument is the dictionary variable, `trait.derive`/`trait.proof` the instance dictionary, `trait.method.call` field selection). Jones, qualified types (1992, 1994, 1993): `P ||- e : Q`; (subst) is 6.5, (cut) theorem 4b, coherence as conversion to a canonical derivation is theorem 5's method with `Coherent(S)` for unambiguity. OutsideIn(X) (JFP 2011): (S1), (P1) are theorems 3, 4a; Def. 3.1 consistency is theorem 7's corollary; Def. 7.1 non-overlap is `Coherent(S)`'s shape; guess-free completeness is left open there and not claimed here. System FC and GHC's `GHC.Tc.Types.Evidence`: `evId`/`evDFunApp`/`evSelector`/`evCast` are hypothesis/derive/project/coerce, `EvBind` is `trait.proof`, the instance-superclass rule is H3, roles are why no representational equality leaf exists (`D/TraitOps.td:1131-1136`); GHC's recursive dictionaries are the coinductive alternative F2 declines. chalk: `Implemented-From-Impl/-From-Env`, `Implied-Bound-From-Trait` (from the environment alone, 4.3), `WellFormed-TraitRef` (H3), `Normalize-From-Impl`, `AliasEq-Placeholder`; rustc's `ImplSource` variants, provisional cache, E0207, E0119; a-mir-formality as an executable model with no theorems. Lean 4 and Coq/Rocq resolution: first-solution semantics, which the dialect refuses as incoherence (`D/ImplResolution.cpp:166-168`), the refusal that makes theorem 5 provable. Nelson-Oppen and Downey-Sethi-Tarjan: the closure of 5.2. Mechanizations: Weirich et al. (ICFP 2017; Coq, coercions with erasure) is the nearest relative of the equality arm; Aman Pohjola and Gengelbach (LPAR 2020; HOL4) of `Coherent(S)`; Bottu et al. (ICFP 2019) prove coherence of resolution on paper and name mechanization as future work; Stuckey and Sulzmann (TOPLAS 2005) read coherence as confluence. No mechanized soundness, completeness or coherence of a dictionary-passing type-class or trait calculus was found.

## 10. Falsifying experiments

Every claim about an operation names its falsifier where it is made (sections 1, 2, 4.3, 6, 8); each cited file was checked to exist at the revision read. The judge's probes: `J/j1` (an impl header spelling a projection verifies and serves the denoted application), `J/j2` (an impl return projecting a derived application through another impl verifies and lowers), `J/j3` (D1's replacement lowers when a value coerce consumes the equality). Claims made without an experiment of their own, and what would falsify them: the closure lemma's converse (a `compose` refused for an equality derivable by the equality rules from its premises); (beta-req) preserving typing (an inlined return whose bridging coerce the verifier refuses); (REQ-ADMISSIBLE) (a stage-accepted program whose requirement reading reaches a base yet whose requirement is not derivable in the primitive fragment). Frontend rows: `S/tests/src/45_03_ground_canonicalization_preserves_pair_spelling.src` (F6), `15_12_illegal_gat_use_misses_a_bound_premise.src` (F4), `14_129_illegal_blanket_impls_overlap_on_one_instance.expected_failure` (F19), `38_06_illegal_impl_violates_trait_equality.src` (the frontend refuses the `X/x9` shape at the impl). No closure claim is made: every theorem is a statement for phase B.

## 11. The two specifications, scored

Fidelity to the operations / fidelity to the frontend's needs / provability, each out of 10.
- rules-first: 8 / 9 / 5. Contributed the frame (the logic first, each operation its proof term), the deletion list with D2's
  evidence, the independence case analyses, the environment-only reading of (REQ) that became 4.3, `root`, the reduction rules and the
  instantiation lemmas; its grammar had no claim types (right, taken as H1 once the probes showed the operations admit them). Its
  theorems 5 and 7 were vacuous or false as stated (circular denotation, syntactic `s`, no fragment restriction), its D1 was not
  behaviour-preserving at the barrier, and its Lean eliminated a `Prop` into `Type` and interleaved binders in the requirement list.
- ops-first: 9 / 7 / 6. Contributed the verifier-exact rules (arm by arm, the identity-comparison sites, effects, dominance regions),
  the `Cite` type and `G`-as-index shape, the frontend-rule comparison table, the observation that the dialect's requirement list is the
  plain sublist, the overload (F8) and two-kinds-of-equality (F15) readings. It kept the where-entry arm for a reason the code refutes,
  claimed compose's redundancy in both directions, stated `let_admissible` with a clause contradicting its own independence lemma, and
  its Lean had the parameter/index error, an unparameterized law and a coherence statement counting two undefined denotations as equal.
- Both verifications: every finding they raised stands and is folded above. The judge added `J/j1`, `J/j2`, `J/j3` and the statement of
  H3 in the primitive fragment (on the duty, not on the term, since `J/j2` is accepted and sound).
