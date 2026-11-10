import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactTermTranslation

/-! A finite K proof constructor for composing two existential witnesses.
The source and conclusion freshness conditions are syntactic name conditions;
represented objects may coincide. -/
namespace PASoundness.PAtoCompactTotalityExistsBind

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactTermTranslation

/-- If each `A` has a `B` witness, combine an existing `A` witness with
that witness under both existential quantifiers. -/
def exists_bind (x y : Nat) (A B : Formula)
    (hxy : y ≠ x) (hxA : x ∉ A.binders) (hxB : x ∉ B.binders)
    (hyA : y ∉ A.free) (hyAb : y ∉ A.binders) (hyBb : y ∉ B.binders)
    (step : KDerivation (imp A.encode (existsCode y B.encode))) :
    KDerivation (imp (existsCode x A.encode)
      (existsCode y (existsCode x (andF A B).encode))) := by
  let C : Formula := .ex y (.ex x (andF A B))
  have hC : C.encode = existsCode y (existsCode x (andF A B).encode) := rfl
  have hxC : x ∉ C.free := by simp [C, Formula.free, andF, Formula.not]
  have hyC : y ∉ C.free := by simp [C, Formula.free]
  have hvx := free_vacuity x C hxC
  have hvy := free_vacuity y C hyC
  have hvA := free_vacuity y A hyA
  have hxyIntro : KDerivation (imp (andF A B).encode
      (existsCode x (andF A B).encode)) :=
    existsIntroduce x (andF A B) (by simp [andF, Formula.not, Formula.binders, hxA, hxB])
  have hyIntro : KDerivation (imp (existsCode x (andF A B).encode) C.encode) := by
    simpa [C, Formula.encode] using existsIntroduce y (.ex x (andF A B))
      (by simp [andF, Formula.not, Formula.binders, hxy, hyAb, hyBb])
  have hAB : KDerivation (imp A.encode (imp B.encode C.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [B.encode, A.encode]
    have ha : Context Γ A.encode := .hypothesis (by simp [Γ])
    have hb : Context Γ B.encode := .hypothesis (by simp [Γ])
    have hab : Context Γ (andF A B).encode := by
      simpa [andF, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro ha hb
    exact .mp (.mp hab (.closed hxyIntro)) (.closed hyIntro)
  have hAC : KDerivation (imp A.encode C.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.existsElim hvy
    · apply generalizeOne y hvA
      exact .mp (Context.head [] A.encode) (.closed hAB)
    · exact .mp (Context.head [] A.encode) (.closed step)
  have hout : KDerivation (imp (existsCode x A.encode) C.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.existsElim hvx
    · exact .closed (.generalize x hAC)
    · exact Context.head [] (existsCode x A.encode)
  simpa only [hC] using hout

/-- A guarded first-witness proof composes with the witness step. -/
def guarded_exists_bind (p x y : Nat) (A B : Formula)
    (hxy : y ≠ x) (hxA : x ∉ A.binders) (hxB : x ∉ B.binders)
    (hyA : y ∉ A.free) (hyAb : y ∉ A.binders) (hyBb : y ∉ B.binders)
    (first : KDerivation (imp p (existsCode x A.encode)))
    (step : KDerivation (imp A.encode (existsCode y B.encode))) :
    KDerivation (imp p (existsCode y (existsCode x (andF A B).encode))) :=
  compose first (exists_bind x y A B hxy hxA hxB hyA hyAb hyBb step)

theorem guarded_exists_bind_certificate (p x y : Nat) (A B : Formula)
    (hxy : y ≠ x) (hxA : x ∉ A.binders) (hxB : x ∉ B.binders)
    (hyA : y ∉ A.free) (hyAb : y ∉ A.binders) (hyBb : y ∉ B.binders)
    (first : KDerivation (imp p (existsCode x A.encode)))
    (step : KDerivation (imp A.encode (existsCode y B.encode))) :
    theoremCode (certificate (guarded_exists_bind p x y A B hxy hxA hxB hyA hyAb hyBb first step)) =
      imp p (existsCode y (existsCode x (andF A B).encode)) := certificate_correct _

/-- As well as the paired witnesses, retain an output property implied by
the second witness. The property must be vacuous in the eliminated first
name; no relationship between the represented witness values is assumed. -/
def guarded_exists_bind_with_output (p x y : Nat) (A B D : Formula)
    (hxy : y ≠ x) (hxA : x ∉ A.binders) (hxB : x ∉ B.binders)
    (hxD : x ∉ D.free) (hyA : y ∉ A.free)
    (hyAb : y ∉ A.binders) (hyBb : y ∉ B.binders) (hyDb : y ∉ D.binders)
    (first : KDerivation (imp p (existsCode x A.encode)))
    (step : KDerivation (imp A.encode (existsCode y B.encode)))
    (output : KDerivation (imp B.encode D.encode)) :
    KDerivation (imp p (existsCode y (andF D (.ex x (andF A B))).encode)) := by
  let C : Formula := .ex y (andF D (.ex x (andF A B)))
  have hC : C.encode = existsCode y (andF D (.ex x (andF A B))).encode := rfl
  have hxC : x ∉ C.free := by simp [C, Formula.free, andF, Formula.not, hxD]
  have hyC : y ∉ C.free := by simp [C, Formula.free]
  have hvx := free_vacuity x C hxC
  have hvy := free_vacuity y C hyC
  have hvA := free_vacuity y A hyA
  have hxIntro : KDerivation (imp (andF A B).encode
      (existsCode x (andF A B).encode)) :=
    existsIntroduce x (andF A B) (by simp [andF, Formula.not, Formula.binders, hxA, hxB])
  have hyIntro := existsIntroduce y (andF D (.ex x (andF A B)))
    (by simp [andF, Formula.not, Formula.binders, hxy, hyAb, hyBb, hyDb])
  have hAB : KDerivation (imp A.encode (imp B.encode C.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [B.encode, A.encode]
    have ha : Context Γ A.encode := .hypothesis (by simp [Γ])
    have hb : Context Γ B.encode := .hypothesis (by simp [Γ])
    have hab : Context Γ (andF A B).encode := by
      simpa [andF, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro ha hb
    have hd : Context Γ D.encode := .mp hb (.closed output)
    have he : Context Γ (existsCode x (andF A B).encode) := .mp hab (.closed hxIntro)
    have hp : Context Γ (andF D (.ex x (andF A B))).encode := by
      simpa [andF, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hd he
    exact .mp hp (.closed hyIntro)
  have hAC : KDerivation (imp A.encode C.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.existsElim hvy
    · apply generalizeOne y hvA
      exact .mp (Context.head [] A.encode) (.closed hAB)
    · exact .mp (Context.head [] A.encode) (.closed step)
  have hout : KDerivation (imp (existsCode x A.encode) C.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.existsElim hvx
    · exact .closed (.generalize x hAC)
    · exact Context.head [] (existsCode x A.encode)
  exact compose first (by simpa only [hC] using hout)

theorem guarded_exists_bind_with_output_certificate (p x y : Nat) (A B D : Formula)
    (hxy : y ≠ x) (hxA : x ∉ A.binders) (hxB : x ∉ B.binders)
    (hxD : x ∉ D.free) (hyA : y ∉ A.free)
    (hyAb : y ∉ A.binders) (hyBb : y ∉ B.binders) (hyDb : y ∉ D.binders)
    (first : KDerivation (imp p (existsCode x A.encode)))
    (step : KDerivation (imp A.encode (existsCode y B.encode)))
    (output : KDerivation (imp B.encode D.encode)) :
    theoremCode (certificate (guarded_exists_bind_with_output p x y A B D hxy hxA hxB
      hxD hyA hyAb hyBb hyDb first step output)) =
      imp p (existsCode y (andF D (.ex x (andF A B))).encode) := certificate_correct _

end PASoundness.PAtoCompactTotalityExistsBind

#print axioms PASoundness.PAtoCompactTotalityExistsBind.exists_bind
#print axioms PASoundness.PAtoCompactTotalityExistsBind.guarded_exists_bind
#print axioms PASoundness.PAtoCompactTotalityExistsBind.guarded_exists_bind_certificate
#print axioms PASoundness.PAtoCompactTotalityExistsBind.guarded_exists_bind_with_output
#print axioms PASoundness.PAtoCompactTotalityExistsBind.guarded_exists_bind_with_output_certificate
