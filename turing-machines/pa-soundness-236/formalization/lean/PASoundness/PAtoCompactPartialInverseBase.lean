import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroTransitive
import PASoundness.PAtoCompactTransitiveWitness

/-! Exact named partial inverse-graph invariant and its empty-prefix base in
literal K. This does not construct a successor extension or an inverse graph
for an arbitrary domain. Code 1 remains literal compact bottom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactZeroExistence PASoundness.PAtoCompactZeroTransitive
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not
private def iff' (a b : Formula) : Formula := conj (a.imp b) (b.imp a)

/-- Names 0,1 are full input/output domains, 6 is the original graph,
7 the partial inverse graph, 8 a prefix; 2,3 and graph-internal 19–22 are
bound. On pairs from the two full domains, the inverse graph is exact:
`Graph(7,u,t) ↔ (t∈8 ∧ Graph(6,t,u))`. Correctness outside those domains is
not asserted. -/
def partialInverse : Formula := .all 2 (.all 3
  (.imp (conj (.member 0 2) (.member 1 3))
    (iff' (graphFormula 7 3 2)
      (conj (.member 8 2) (graphFormula 6 2 3)))))

theorem partialInverse_free : partialInverse.free = {0,1,6,7,8} := by decide

/-- A zero graph has no encoded graph edge, for any coordinate names. The
edge graph's pair binders need not be decoded in this projection. -/
def zero_has_no_edge (h z a b : Nat) (hzh : z ≠ h) (hz19 : z ≠ 19)
    (h19h : 19 ≠ h) : KDerivation
    (imp (zeroCode h z) (neg (graphFormula h a b).encode)) := by
  let Z := zeroCode h z
  let M := member h 19
  let B := both M (pairFormula 19 a b).encode
  let E := existsCode 19 B
  have hbody : Context [Z] (imp B 1) := by
    apply Context.deduction
    let Γ := [B,Z]
    have hb : Context Γ B := Context.head _ _
    have hz : Context Γ Z := .hypothesis (by simp [Γ])
    have hm : Context Γ M := Context.conjunctionLeft hb
    have hn : Context Γ (neg M) := .mp hz (.closed (zero_excludes h z 19 hz19 hzh))
    exact .mp hm hn
  have hv : ∀ q, q ∈ [Z] → KDerivation (imp q (allCode 19 q)) := by
    intro q hq
    have he : q = Z := by simpa using hq
    subst q
    exact zero_graph_vacuity h z 19 h19h (Ne.symm hz19)
  have hall : Context [Z] (allCode 19 (imp B 1)) := Context.generalize 19 hv hbody
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,Z]
  have he : Context Γ E := Context.head _ _
  have hh : Context Γ (allCode 19 (imp B 1)) := Context.under hall E
  exact Context.existsElim (explosion (allCode 19 1)) hh he

/-- An empty prefix and an empty inverse graph establish the exact invariant.
No restriction on the original graph is needed. -/
def empty_prefix_empty_graph : KDerivation
    (imp (zeroCode 8 9) (imp (zeroCode 7 10) partialInverse.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let ZP := zeroCode 8 9
  let ZH := zeroCode 7 10
  let G := (graphFormula 7 3 2).encode
  let O := (graphFormula 6 2 3).encode
  let T := both (member 8 2) O
  let Y := both (member 0 2) (member 1 3)
  let Γ := [ZH,ZP]
  have hp : Context Γ ZP := .hypothesis (by simp [Γ])
  have hh : Context Γ ZH := Context.head _ _
  have hnp : Context Γ (neg (member 8 2)) :=
    .mp hp (.closed (zero_excludes 8 9 2 (by decide) (by decide)))
  have hng : Context Γ (neg G) :=
    .mp hh (.closed (zero_has_no_edge 7 10 3 2 (by decide) (by decide) (by decide)))
  have hforward : Context Γ (imp G T) := by
    apply Context.deduction
    exact Context.explode T (.mp (Context.head _ G) (Context.under hng G))
  have hback : Context Γ (imp T G) := by
    apply Context.deduction
    let Δ := [T,ZH,ZP]
    have ht : Context Δ T := Context.head _ _
    have hm : Context Δ (member 8 2) := Context.conjunctionLeft ht
    exact Context.explode G (.mp hm (Context.under hnp T))
  have hpoint : Context Γ (imp Y (both (imp G T) (imp T G))) :=
    Context.lift (Context.conjunctionIntro hforward hback) Y
  have hv3 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 3 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = ZH
    · subst q
      exact zero_graph_vacuity 7 10 3 (by decide) (by decide)
    · have he' : q = ZP := hq.resolve_left he
      subst q
      exact zero_graph_vacuity 8 9 3 (by decide) (by decide)
  have hv2 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 2 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = ZH
    · subst q
      exact zero_graph_vacuity 7 10 2 (by decide) (by decide)
    · have he' : q = ZP := hq.resolve_left he
      subst q
      exact zero_graph_vacuity 8 9 2 (by decide) (by decide)
  exact Context.generalize 2 hv2 (Context.generalize 3 hv3 hpoint)

/-- Selector 8 supplies a zero graph at name 7 (after alpha conversion). -/
def empty_graph_exists : KDerivation (existsCode 7 (zeroCode 7 10)) := by
  let f : Formula := .all 10 (.imp (.member 1 10) .bottom)
  have ha := (existentialAlpha 1 7 f (by decide) (by decide) (by decide)).1
  have he : KDerivation (imp (existsCode 1 (zeroCode 1 10))
      (existsCode 7 (zeroCode 7 10))) := by
    simpa [f, zeroCode, neg, Formula.encode, replace, rename] using ha
  exact .mp (zero_graph_exists 10 (by decide)) he

/-- Under an explicit empty-prefix hypothesis, K constructs some represented
partial inverse graph satisfying the full displayed invariant. -/
def empty_prefix_partial_inverse_exists : KDerivation
    (imp (zeroCode 8 9) (existsCode 7 partialInverse.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Z := zeroCode 8 9
  let Γ := [Z]
  have hz : Context Γ Z := Context.head [] _
  have hi : Context Γ (imp (zeroCode 7 10) partialInverse.encode) :=
    .mp hz (.closed empty_prefix_empty_graph)
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 7 q)) := by
    intro q hq
    have he : q = Z := by simpa [Γ] using hq
    subst q
    exact zero_graph_vacuity 8 9 7 (by decide) (by decide)
  have hall := Context.generalize 7 hv hi
  exact exists_map_context hall (.closed empty_graph_exists)

theorem empty_prefix_partial_inverse_certificate :
    theoremCode (certificate empty_prefix_partial_inverse_exists) =
      imp (zeroCode 8 9) (existsCode 7 partialInverse.encode) :=
  certificate_correct empty_prefix_partial_inverse_exists

end PASoundness.PAtoCompactPartialInverseBase

#print axioms PASoundness.PAtoCompactPartialInverseBase.zero_has_no_edge
#print axioms PASoundness.PAtoCompactPartialInverseBase.empty_prefix_partial_inverse_exists
#print axioms PASoundness.PAtoCompactPartialInverseBase.empty_prefix_partial_inverse_certificate
