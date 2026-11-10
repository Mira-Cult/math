import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactGuardedExistsCongruence
import PASoundness.CompactDerivations

/-! Successor-node alignment for term-graph substitution. This proof keeps
the same child witness and successor relation; it is conditional on a finite
K child alignment and vacuity of the retained guard. -/
namespace PASoundness.PAtoCompactTermSubstSuccStep

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactGuardedExistsCongruence

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def succTerm {α : Type} (t : Peano.language.Term α) : Peano.language.Term α :=
  .func .succ ![t]

def matrix {α : Type} (v : α → Nat) (t : Peano.language.Term α)
    (b out : Nat) : Formula :=
  andF (termGraph v t b (b+64)) (succAt b b out)

/-- Align child graphs while retaining the same successor relation. -/
def matrix_forward {α β : Type} (v : α → Nat) (w : β → Nat)
    (t : Peano.language.Term α) (t' : Peano.language.Term β)
    (b out : Nat) (H : Formula)
    (child : KDerivation (imp H.encode (imp (termGraph v t b (b+64)).encode
      (termGraph w t' b (b+64)).encode))) :
    KDerivation (imp H.encode (imp (matrix v t b out).encode
      (matrix w t' b out).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(matrix v t b out).encode, H.encode]
  have hH : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hM : Context Γ (both (termGraph v t b (b+64)).encode (succAt b b out).encode) := by
    have h := Context.head [H.encode] (matrix v t b out).encode
    simpa [Γ, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
  have hT := Context.mp (Context.conjunctionLeft hM) (Context.mp hH (.closed child))
  have hR := Context.conjunctionRight hM
  have hc := Context.conjunctionIntro hT hR
  simpa [Γ, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hc

/-- The allocated child witness is not an internal matrix binder. -/
theorem matrix_witness_not_binder {α : Type} (v : α → Nat)
    (t : Peano.language.Term α) (b out : Nat) : b ∉ (matrix v t b out).binders := by
  simp only [matrix, andF_binders, Finset.mem_union, not_or]
  constructor
  · exact termGraph_below_not_binder v t b (b+64) b (by omega)
  · intro h
    have hh := succAt_private b b out b h
    omega

/-- Lift a guarded child implication to successor graphs. The guard is
required to have an explicit K vacuity proof at the existential witness. -/
def succ_forward {α β : Type} (v : α → Nat) (w : β → Nat)
    (t : Peano.language.Term α) (t' : Peano.language.Term β)
    (b out : Nat) (H : Formula)
    (vacuity : KDerivation (imp H.encode (allCode b H.encode)))
    (child : KDerivation (imp H.encode (imp (termGraph v t b (b+64)).encode
      (termGraph w t' b (b+64)).encode))) :
    KDerivation (imp H.encode (imp (termGraph v (succTerm t) out b).encode
      (termGraph w (succTerm t') out b).encode)) := by
  let M := matrix v t b out
  let M' := matrix w t' b out
  have h1 := exists_congr_of_vacuity b H.encode M M' vacuity
    (matrix_witness_not_binder w t' b out) (matrix_forward v w t t' b out H child)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(termGraph v (succTerm t) out b).encode, H.encode]
  have hH : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hG : Context Γ (both (domainAt b out).encode (existsCode b M.encode)) := by
    have h := Context.head [H.encode] (termGraph v (succTerm t) out b).encode
    simpa [Γ, succTerm, termGraph, M, matrix, andF,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using h
  have hE := Context.mp (Context.conjunctionRight hG) (Context.mp hH (.closed h1))
  have hc := Context.conjunctionIntro (Context.conjunctionLeft hG) hE
  simpa [Γ, succTerm, termGraph, M', matrix, andF,
    CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using hc

/-- Both implications share the guard and the same allocated child witness. -/
def succ_both {α β : Type} (v : α → Nat) (w : β → Nat)
    (t : Peano.language.Term α) (t' : Peano.language.Term β)
    (b out : Nat) (H : Formula)
    (vacuity : KDerivation (imp H.encode (allCode b H.encode)))
    (forward : KDerivation (imp H.encode (imp (termGraph v t b (b+64)).encode
      (termGraph w t' b (b+64)).encode)))
    (backward : KDerivation (imp H.encode (imp (termGraph w t' b (b+64)).encode
      (termGraph v t b (b+64)).encode))) :
    KDerivation (imp H.encode (imp (termGraph v (succTerm t) out b).encode
      (termGraph w (succTerm t') out b).encode)) ×
    KDerivation (imp H.encode (imp (termGraph w (succTerm t') out b).encode
      (termGraph v (succTerm t) out b).encode)) :=
  ⟨succ_forward v w t t' b out H vacuity forward,
    succ_forward w v t' t b out H vacuity backward⟩

theorem succ_forward_certificate {α β : Type} (v : α → Nat) (w : β → Nat)
    (t : Peano.language.Term α) (t' : Peano.language.Term β)
    (b out : Nat) (H : Formula)
    (vacuity : KDerivation (imp H.encode (allCode b H.encode)))
    (child : KDerivation (imp H.encode (imp (termGraph v t b (b+64)).encode
      (termGraph w t' b (b+64)).encode))) :
    theoremCode (certificate (succ_forward v w t t' b out H vacuity child)) =
      imp H.encode (imp (termGraph v (succTerm t) out b).encode
        (termGraph w (succTerm t') out b).encode) := certificate_correct _

end PASoundness.PAtoCompactTermSubstSuccStep

#print axioms PASoundness.PAtoCompactTermSubstSuccStep.matrix_forward
#print axioms PASoundness.PAtoCompactTermSubstSuccStep.matrix_witness_not_binder
#print axioms PASoundness.PAtoCompactTermSubstSuccStep.succ_forward
#print axioms PASoundness.PAtoCompactTermSubstSuccStep.succ_both
#print axioms PASoundness.PAtoCompactTermSubstSuccStep.succ_forward_certificate
