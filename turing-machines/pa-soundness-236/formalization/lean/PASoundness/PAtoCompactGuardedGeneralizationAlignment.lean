import PASoundness.PAtoCompactGuardedBridge

/-! A syntactic allocation control for guarded generalization. The generated
body and the original open translation are not literally equal in general,
even when the generalized name is absent. No alpha-equivalence is asserted. -/
namespace PASoundness.PAtoCompactGuardedGeneralizationAlignment

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation

def zeroEq : Peano.Formula := Peano.zero.equal Peano.zero

def allAtBody (x : Nat) (φ : Peano.Formula) : Peano.language.BoundedFormula Nat 1 :=
  BoundedFormula.relabel (fun y => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y) φ

def topName (x : Nat) (φ : Peano.Formula) : Nat :=
  scopeBase (FOL.allAt x φ) Fin.elim0

def topBody (x : Nat) (φ : Peano.Formula) : CompactNamed.Formula :=
  scopedFormula 1 (allAtBody x φ) (Fin.snoc Fin.elim0 (topName x φ))

/-- Literal top-level shape of the translated named PA universal. -/
theorem code_allAt (x : Nat) (φ : Peano.Formula) :
    code (FOL.allAt x φ) =
      allCode (topName x φ)
        (imp (domainAt (topName x φ + 1) (topName x φ)).encode (topBody x φ).encode) := by
  rfl

def outerExistsName : CompactNamed.Formula → Option Nat
  | .ex x _ => some x
  | _ => none

theorem zeroEq_free (x : Nat) : x ∉ zeroEq.freeVarFinset := by
  simp [zeroEq, Peano.zero, Term.equal, Term.bdEqual,
    BoundedFormula.freeVarFinset, Term.varFinsetLeft]

theorem zeroEq_original_name : outerExistsName (formula zeroEq) = some 1 := by
  rfl

theorem zeroEq_top_body_name (x : Nat) : outerExistsName (topBody x zeroEq) = some 2 := by
  rfl

theorem zeroEq_body_ne (x : Nat) : formula zeroEq ≠ topBody x zeroEq := by
  intro h
  have hn := congrArg outerExistsName h
  rw [zeroEq_original_name, zeroEq_top_body_name] at hn
  contradiction

end PASoundness.PAtoCompactGuardedGeneralizationAlignment

#print axioms PASoundness.PAtoCompactGuardedGeneralizationAlignment.zeroEq_free
#print axioms PASoundness.PAtoCompactGuardedGeneralizationAlignment.code_allAt
#print axioms PASoundness.PAtoCompactGuardedGeneralizationAlignment.zeroEq_original_name
#print axioms PASoundness.PAtoCompactGuardedGeneralizationAlignment.zeroEq_top_body_name
#print axioms PASoundness.PAtoCompactGuardedGeneralizationAlignment.zeroEq_body_ne
