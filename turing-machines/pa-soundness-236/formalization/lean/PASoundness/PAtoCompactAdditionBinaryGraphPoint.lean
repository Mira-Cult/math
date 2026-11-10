import PASoundness.PAtoCompactAdditionGraphOperationPoint
import PASoundness.PAtoCompactBinaryGraphFunctionalConditional

/-! The guarded point step for addition-node graph functionality, using the
actual parent and child graphs to obtain every candidate premise. -/
namespace PASoundness.PAtoCompactAdditionBinaryGraphPoint

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactAllElimTermEquality

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Child functionality plus the two actual parent/child graph matrices
provides the result comparison; all allocator bounds remain explicit. -/
def addition_binary_point {α : Type} (v : α → Nat) (t u : Peano.language.Term α)
    (b c p q e f : Nat) (g : Formula)
    (hbe : b+1 < e+2) (hce : c+1 < e+2)
    (hpe : p < e+2) (hqe : q < e+2) (hpb : p < b+2) (hqc : q < c+2)
    (hpf : p < f+2) (hqf : q < f+2)
    (left : KDerivation (imp g.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (right : KDerivation (imp g.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (imp (termGraph v u (c+1) (c+64+termCost t)).encode
          (equivAt e (b+1) (c+1)).encode)))) :
    let A := termGraph v (binaryTerm true t u) p b
    let B := termGraph v (binaryTerm true t u) q c
    let H := andF g (andF A B)
    let M := matrix v true t u b p
    let N := matrix v true t u c q
    KDerivation (imp (andF H M).encode (imp N.encode (equivAt f p q).encode)) := by
  dsimp only
  let A := termGraph v (binaryTerm true t u) p b
  let B := termGraph v (binaryTerm true t u) q c
  let H := andF g (andF A B)
  let M := matrix v true t u b p
  let N := matrix v true t u c q
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [N.encode, (andF H M).encode]
  have hN : Context Γ N.encode := .head _ _
  have hHM : Context Γ (andF H M).encode := .hypothesis (by simp [Γ])
  have hHM' : Context Γ (both H.encode M.encode) := by
    simpa [andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hHM
  have hH := Context.conjunctionLeft hHM'
  have hM := Context.conjunctionRight hHM'
  have hH' : Context Γ (both g.encode (andF A B).encode) := by
    simpa [H, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hH
  have hg := Context.conjunctionLeft hH'
  have hAB : Context Γ (both A.encode B.encode) := by
    simpa [andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using Context.conjunctionRight hH'
  have hA : Context Γ A.encode := Context.conjunctionLeft hAB
  have hB : Context Γ B.encode := Context.conjunctionRight hAB
  have hM' : Context Γ (both (termGraph v t b (b+64)).encode
      (both (termGraph v u (b+1) (b+64+termCost t)).encode (addAt b b (b+1) p).encode)) := by
    simpa [M, matrix, binaryRel, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hM
  have hN' : Context Γ (both (termGraph v t c (c+64)).encode
      (both (termGraph v u (c+1) (c+64+termCost t)).encode (addAt c c (c+1) q).encode)) := by
    simpa [N, matrix, binaryRel, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hN
  have hl1 := Context.conjunctionLeft hM'
  have hr1 := Context.conjunctionLeft (Context.conjunctionRight hM')
  have ha1 := Context.conjunctionRight (Context.conjunctionRight hM')
  have hl2 := Context.conjunctionLeft hN'
  have hr2 := Context.conjunctionLeft (Context.conjunctionRight hN')
  have ha2 := Context.conjunctionRight (Context.conjunctionRight hN')
  have he1 : Context Γ (equivAt e b c).encode := .mp hl2 (.mp hl1 (.mp hg (.closed left)))
  have he2 : Context Γ (equivAt e (b+1) (c+1)).encode := .mp hr2 (.mp hr1 (.mp hg (.closed right)))
  have hguard : Context Γ (PASoundness.PAtoCompactAdditionGraphOperationPoint.guard v t u b c p q e).encode :=
    Context.conjunctionIntro hl1 (Context.conjunctionIntro hr1 (Context.conjunctionIntro hl2
      (Context.conjunctionIntro hr2 (Context.conjunctionIntro hA (Context.conjunctionIntro hB
        (Context.conjunctionIntro he1 (Context.conjunctionIntro he2 (Context.conjunctionIntro ha1 ha2))))))))
  exact .mp hguard (.closed (PASoundness.PAtoCompactAdditionGraphOperationPoint.graph_operation_point
    v t u b c p q e f hbe hce hpe hqe hpb hqc hpf hqf))

end PASoundness.PAtoCompactAdditionBinaryGraphPoint

#print axioms PASoundness.PAtoCompactAdditionBinaryGraphPoint.addition_binary_point
