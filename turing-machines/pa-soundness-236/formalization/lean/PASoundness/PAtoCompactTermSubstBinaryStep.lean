import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactDerivations
import PASoundness.PAtoCompactGuardedExistsCongruence

/-! The binary-node step for graph substitution.  Two child alignments are
explicit K proof inputs; their graph allocation bases may differ because the
left child can have changed cost. The same two values and operation relation
are reused. No arithmetic graph existence or functionality is asserted. -/
namespace PASoundness.PAtoCompactTermSubstBinaryStep

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactGuardedExistsCongruence

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def binaryTerm {α : Type} (add : Bool) (t u : Peano.language.Term α) : Peano.language.Term α :=
  if add then .func .add ![t, u] else .func .mul ![t, u]

def binaryRel (add : Bool) (b out : Nat) : Formula :=
  if add then addAt b b (b+1) out else mulAt b b (b+1) out

def matrix {α : Type} (v : α → Nat) (add : Bool)
    (t u : Peano.language.Term α) (b out : Nat) : Formula :=
  andF (termGraph v t b (b+64))
    (andF (termGraph v u (b+1) (b+64+termCost t)) (binaryRel add b out))

/-- Pointwise transport of a binary matrix using the same child values. -/
def matrix_forward {α β : Type} (v : α → Nat) (w : β → Nat)
    (add : Bool) (t u : Peano.language.Term α) (t' u' : Peano.language.Term β)
    (b out : Nat) (H : Formula)
    (left : KDerivation (imp H.encode (imp (termGraph v t b (b+64)).encode
      (termGraph w t' b (b+64)).encode)))
    (right : KDerivation (imp H.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (termGraph w u' (b+1) (b+64+termCost t')).encode))) :
    KDerivation (imp H.encode (imp (matrix v add t u b out).encode
      (matrix w add t' u' b out).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(matrix v add t u b out).encode, H.encode]
  have hH : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hM : Context Γ (both (termGraph v t b (b+64)).encode
      (both (termGraph v u (b+1) (b+64+termCost t)).encode (binaryRel add b out).encode)) := by
    have h := Context.head [H.encode] (matrix v add t u b out).encode
    simpa [Γ, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
  have hT := Context.mp (Context.conjunctionLeft hM) (Context.mp hH (.closed left))
  have hU := Context.mp (Context.conjunctionLeft (Context.conjunctionRight hM))
    (Context.mp hH (.closed right))
  have hR := Context.conjunctionRight (Context.conjunctionRight hM)
  have hc := Context.conjunctionIntro hT (Context.conjunctionIntro hU hR)
  simpa [Γ, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hc

/-- The allocated witness names are not internal target-matrix binders. -/
theorem matrix_witness_not_binder {α : Type} (v : α → Nat) (add : Bool)
    (t u : Peano.language.Term α) (b out : Nat) (k : Nat) (hk : k < b+2) :
    k ∉ (matrix v add t u b out).binders := by
  have hr : k ∉ (binaryRel add b out).binders := by
    intro h
    cases add <;> simp only [binaryRel, Bool.false_eq_true, ↓reduceIte] at h
    · have hh := mulAt_private b b (b+1) out k h; omega
    · have hh := addAt_private b b (b+1) out k h; omega
  simp only [matrix, andF_binders, Finset.mem_union, not_or]
  exact ⟨termGraph_below_not_binder v t b (b+64) k (by omega),
    termGraph_below_not_binder v u (b+1) (b+64+termCost t) k (by omega), hr⟩

/-- A binary graph aligns from pointwise child alignments under the same
guard. Explicit vacuity lets the child witnesses be generalized. -/
def binary_forward {α β : Type} (v : α → Nat) (w : β → Nat)
    (add : Bool) (t u : Peano.language.Term α) (t' u' : Peano.language.Term β)
    (b out : Nat) (H : Formula)
    (vacuity₀ : KDerivation (imp H.encode (allCode b H.encode)))
    (vacuity₁ : KDerivation (imp H.encode (allCode (b+1) H.encode)))
    (left : KDerivation (imp H.encode (imp (termGraph v t b (b+64)).encode
      (termGraph w t' b (b+64)).encode)))
    (right : KDerivation (imp H.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (termGraph w u' (b+1) (b+64+termCost t')).encode))) :
    KDerivation (imp H.encode (imp (termGraph v (binaryTerm add t u) out b).encode
      (termGraph w (binaryTerm add t' u') out b).encode)) := by
  let M := matrix v add t u b out
  let M' := matrix w add t' u' b out
  have hb1 : b+1 ∉ M'.binders := matrix_witness_not_binder w add t' u' b out (b+1) (by omega)
  have hb : b ∉ (Formula.ex (b+1) M').binders := by
    simp only [Formula.binders, Finset.mem_insert, not_or]
    exact ⟨by omega, matrix_witness_not_binder w add t' u' b out b (by omega)⟩
  have h1 := exists_congr_of_vacuity (b+1) H.encode M M' vacuity₁ hb1
    (matrix_forward v w add t u t' u' b out H left right)
  have h2 := exists_congr_of_vacuity b H.encode (.ex (b+1) M) (.ex (b+1) M') vacuity₀ hb h1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(termGraph v (binaryTerm add t u) out b).encode, H.encode]
  have hH : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hG : Context Γ (both (domainAt b out).encode
      (existsCode b (existsCode (b+1) M.encode))) := by
    have h := Context.head [H.encode] (termGraph v (binaryTerm add t u) out b).encode
    cases add <;> simpa [Γ, binaryTerm, binaryRel, termGraph, M, matrix, andF,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using h
  have hE := Context.mp (Context.conjunctionRight hG) (Context.mp hH (.closed h2))
  have hc := Context.conjunctionIntro (Context.conjunctionLeft hG) hE
  cases add <;> simpa [Γ, binaryTerm, binaryRel, termGraph, M', matrix, andF,
    CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using hc

/-- Both K directions, with the same retained guard and the correct child
allocation base in each direction. -/
def binary_both {α β : Type} (v : α → Nat) (w : β → Nat)
    (add : Bool) (t u : Peano.language.Term α) (t' u' : Peano.language.Term β)
    (b out : Nat) (H : Formula)
    (vacuity₀ : KDerivation (imp H.encode (allCode b H.encode)))
    (vacuity₁ : KDerivation (imp H.encode (allCode (b+1) H.encode)))
    (left₁ : KDerivation (imp H.encode (imp (termGraph v t b (b+64)).encode
      (termGraph w t' b (b+64)).encode)))
    (left₂ : KDerivation (imp H.encode (imp (termGraph w t' b (b+64)).encode
      (termGraph v t b (b+64)).encode)))
    (right₁ : KDerivation (imp H.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (termGraph w u' (b+1) (b+64+termCost t')).encode)))
    (right₂ : KDerivation (imp H.encode
      (imp (termGraph w u' (b+1) (b+64+termCost t')).encode
        (termGraph v u (b+1) (b+64+termCost t)).encode))) :
    KDerivation (imp H.encode (imp (termGraph v (binaryTerm add t u) out b).encode
      (termGraph w (binaryTerm add t' u') out b).encode)) ×
    KDerivation (imp H.encode (imp (termGraph w (binaryTerm add t' u') out b).encode
      (termGraph v (binaryTerm add t u) out b).encode)) :=
  ⟨binary_forward v w add t u t' u' b out H vacuity₀ vacuity₁ left₁ right₁,
    binary_forward w v add t' u' t u b out H vacuity₀ vacuity₁ left₂ right₂⟩

theorem binary_forward_certificate {α β : Type} (v : α → Nat) (w : β → Nat)
    (add : Bool) (t u : Peano.language.Term α) (t' u' : Peano.language.Term β)
    (b out : Nat) (H : Formula)
    (vacuity₀ : KDerivation (imp H.encode (allCode b H.encode)))
    (vacuity₁ : KDerivation (imp H.encode (allCode (b+1) H.encode)))
    (left : KDerivation (imp H.encode (imp (termGraph v t b (b+64)).encode
      (termGraph w t' b (b+64)).encode)))
    (right : KDerivation (imp H.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (termGraph w u' (b+1) (b+64+termCost t')).encode))) :
    theoremCode (certificate (binary_forward v w add t u t' u' b out H vacuity₀ vacuity₁ left right)) =
      imp H.encode (imp (termGraph v (binaryTerm add t u) out b).encode
        (termGraph w (binaryTerm add t' u') out b).encode) := certificate_correct _

end PASoundness.PAtoCompactTermSubstBinaryStep

#print axioms PASoundness.PAtoCompactTermSubstBinaryStep.matrix_forward
#print axioms PASoundness.PAtoCompactTermSubstBinaryStep.matrix_witness_not_binder
#print axioms PASoundness.PAtoCompactTermSubstBinaryStep.binary_forward
#print axioms PASoundness.PAtoCompactTermSubstBinaryStep.binary_both
#print axioms PASoundness.PAtoCompactTermSubstBinaryStep.binary_forward_certificate
