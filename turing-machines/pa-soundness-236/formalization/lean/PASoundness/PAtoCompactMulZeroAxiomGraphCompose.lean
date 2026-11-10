import PASoundness.PAtoCompactTermZeroGuarded

/-! Witness composition retaining an output zero proof alongside the binary graph. -/
namespace PASoundness.PAtoCompactMulZeroAxiomGraphCompose
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTermZeroGuarded
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def binary_total_with_zero_from_children {α : Type} (v : α → Nat) (add : Bool)
    (t u : Peano.language.Term α) (b out : Nat) (g : Formula) (hout : out < b)
    (child1 : KDerivation (imp g.encode
      (existsCode b (termGraph v t b (b+64)).encode)))
    (child2 : KDerivation (imp g.encode
      (existsCode (b+1) (termGraph v u (b+1) (b+64+termCost t)).encode)))
    (operation : KDerivation (imp (termGraph v t b (b+64)).encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (existsCode out (andF (domainAt b out) (andF (zeroAt b out) (binaryRel add b b (b+1) out))).encode))))
    (vgb : KDerivation (imp g.encode (allCode b g.encode)))
    (vgb1 : KDerivation (imp g.encode (allCode (b+1) g.encode)))
    (vgo : KDerivation (imp g.encode (allCode out g.encode)))
    (vtb1 : KDerivation (imp (termGraph v t b (b+64)).encode
      (allCode (b+1) (termGraph v t b (b+64)).encode)))
    (vto : KDerivation (imp (termGraph v t b (b+64)).encode
      (allCode out (termGraph v t b (b+64)).encode)))
    (vuo : KDerivation (imp (termGraph v u (b+1) (b+64+termCost t)).encode
      (allCode out (termGraph v u (b+1) (b+64+termCost t)).encode)))
    (vg1 : KDerivation (imp (existsCode out (andF (termGraph v (binaryTerm add t u) out b) (zeroAt b out)).encode)
      (allCode b (existsCode out (andF (termGraph v (binaryTerm add t u) out b) (zeroAt b out)).encode))))
    (vg2 : KDerivation (imp (existsCode out (andF (termGraph v (binaryTerm add t u) out b) (zeroAt b out)).encode)
      (allCode (b+1) (existsCode out (andF (termGraph v (binaryTerm add t u) out b) (zeroAt b out)).encode))))
    (vgo' : KDerivation (imp (existsCode out (andF (termGraph v (binaryTerm add t u) out b) (zeroAt b out)).encode)
      (allCode out (existsCode out (andF (termGraph v (binaryTerm add t u) out b) (zeroAt b out)).encode)))) :
    KDerivation (imp g.encode (existsCode out (andF (termGraph v (binaryTerm add t u) out b) (zeroAt b out)).encode)) := by
  let T := (termGraph v t b (b+64)).encode
  let U := (termGraph v u (b+1) (b+64+termCost t)).encode
  let N := (andF (domainAt b out) (andF (zeroAt b out) (binaryRel add b b (b+1) out))).encode
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [g.encode]
  have h1 : Context Γ (existsCode b T) := .mp (Context.head [] _) (.closed child1)
  apply Context.existsElim vg1 _ h1
  apply generalizeOne b vgb
  apply Context.deduction
  let Δ := [T, g.encode]
  have hg : Context Δ g.encode := .hypothesis (by simp [Δ])
  have h2 : Context Δ (existsCode (b+1) U) := .mp hg (.closed child2)
  apply Context.existsElim vg2 _ h2
  apply Context.generalize (b+1)
  · intro q hq
    change q ∈ [T, g.encode] at hq
    by_cases he : q = T
    · subst q; exact vtb1
    · have he' : q = g.encode := by simpa [he] using hq
      subst q; exact vgb1
  apply Context.deduction
  let Θ := [U, T, g.encode]
  have hu : Context Θ U := .hypothesis (by simp [Θ])
  have ht : Context Θ T := .hypothesis (by simp [Θ])
  have hn : Context Θ (existsCode out N) := .mp hu (.mp ht (.closed operation))
  apply Context.existsElim vgo' _ hn
  apply Context.generalize out
  · intro q hq
    change q ∈ [U, T, g.encode] at hq
    by_cases he : q = U
    · subst q; exact vuo
    · by_cases he' : q = T
      · subst q; exact vto
      · have he'' : q = g.encode := by simpa [he, he'] using hq
        subst q; exact vgo
  apply Context.deduction
  let Ξ := [N, U, T, g.encode]
  have hn' : Context Ξ (both (domainAt b out).encode (both (zeroAt b out).encode (binaryRel add b b (b+1) out).encode)) := by
    have h : Context Ξ N := .hypothesis (by simp [Ξ])
    simpa [N, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
  have hu' : Context Ξ U := .hypothesis (by simp [Ξ])
  have ht' : Context Ξ T := .hypothesis (by simp [Ξ])
  have hgraph : Context Ξ (termGraph v (binaryTerm add t u) out b).encode :=
    .mp (Context.conjunctionRight (Context.conjunctionRight hn')) (.mp hu' (.mp ht'
      (.mp (Context.conjunctionLeft hn') (.closed (binary_from_witness v add t u b out)))))
  let Q := andF (termGraph v (binaryTerm add t u) out b) (zeroAt b out)
  have hq : Context Ξ Q.encode := by
    have hz := Context.conjunctionLeft (Context.conjunctionRight hn')
    simpa [Q, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using
      Context.conjunctionIntro hgraph hz
  have hb : out ∉ Q.binders := by
    simp only [Q, andF_binders, Finset.mem_union, not_or]
    constructor
    · exact termGraph_below_not_binder v _ out b out hout
    · intro h
      have hh := PAtoCompactTermGraphBinderRange.zeroAt_private b out out h
      omega
  have hi := existsIntroduce out Q hb
  exact .mp hq (.closed hi)


end PASoundness.PAtoCompactMulZeroAxiomGraphCompose

#print axioms PASoundness.PAtoCompactMulZeroAxiomGraphCompose.binary_total_with_zero_from_children
