import PASoundness.SyntaxDecidable
import PASoundness.Peano

/-!
# Total syntactic proof checking

Codes are finite algebraic trees. A nonlogical axiom leaf carries a finite
witness to a supplied total decoder. For a c.e. axiom enumeration, this witness
can be a stage and list position, as `enumeratedDecode` demonstrates. PA uses
the explicit `PACode` constructors, with both origin and coverage proved.

No semantic truth test occurs in either decoder or the proof checker. Numeric
serialization of these constructor trees and translation to the compact HF
producer are separate interfaces.
-/

namespace PASoundness.Certificates

open FirstOrder FirstOrder.Language

variable {L : Language}

inductive LogicalCode (L : Language) : Type
  | k (φ ψ : FOL.Formula L)
  | s (φ ψ χ : FOL.Formula L)
  | classical (φ : FOL.Formula L)
  | allElim (φ : FOL.Formula L) (x : Nat) (t : FOL.Term L)
  | allImp (φ ψ : FOL.Formula L) (x : Nat)
  | vacuous (φ : FOL.Formula L) (x : Nat)
  | eqRefl (t : FOL.Term L)
  | eqSubst (φ : FOL.Formula L) (x : Nat) (t u : FOL.Term L)

def logicalDecode : LogicalCode L → Option (FOL.Formula L)
  | .k φ ψ => some (φ.imp (ψ.imp φ))
  | .s φ ψ χ => some ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | .classical φ => some (φ.not.not.imp φ)
  | .allElim φ x t => some ((FOL.allAt x φ).imp (FOL.substAt φ x t))
  | .allImp φ ψ x =>
      some ((FOL.allAt x (φ.imp ψ)).imp ((FOL.allAt x φ).imp (FOL.allAt x ψ)))
  | .vacuous φ x => if x ∉ φ.freeVarFinset then some (φ.imp (FOL.allAt x φ)) else none
  | .eqRefl t => some (t.equal t)
  | .eqSubst φ x t u =>
      some ((t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u)))

theorem logical_origin (c : LogicalCode L) (φ : FOL.Formula L)
    (h : logicalDecode c = some φ) : FOL.LogicalAxiom φ := by
  cases c with
  | k ψ χ => cases h; exact .k ψ χ
  | s ψ χ θ => cases h; exact .s ψ χ θ
  | classical ψ => cases h; exact .classical ψ
  | allElim ψ x t => cases h; exact .allElim ψ x t
  | allImp ψ χ x => cases h; exact .allImp ψ χ x
  | vacuous ψ x =>
      by_cases hx : x ∉ ψ.freeVarFinset
      · simp only [logicalDecode, if_pos hx, Option.some.injEq] at h
        subst φ
        exact .vacuous ψ x hx
      · simp [logicalDecode, hx] at h
  | eqRefl t => cases h; exact .eqRefl t
  | eqSubst ψ x t u => cases h; exact .eqSubst ψ x t u

theorem logical_coverage {φ : FOL.Formula L} (h : FOL.LogicalAxiom φ) :
    ∃ c, logicalDecode c = some φ := by
  cases h with
  | k φ ψ => exact ⟨.k φ ψ, rfl⟩
  | s φ ψ χ => exact ⟨.s φ ψ χ, rfl⟩
  | classical φ => exact ⟨.classical φ, rfl⟩
  | allElim φ x t => exact ⟨.allElim φ x t, rfl⟩
  | allImp φ ψ x => exact ⟨.allImp φ ψ x, rfl⟩
  | vacuous φ x hx => exact ⟨.vacuous φ x, by simp [logicalDecode, hx]⟩
  | eqRefl t => exact ⟨.eqRefl t, rfl⟩
  | eqSubst φ x t u => exact ⟨.eqSubst φ x t u, rfl⟩

inductive ProofCode (L : Language) (Witness : Type) : Type
  | logical (c : LogicalCode L)
  | nonlogical (w : Witness)
  | mp (implication argument : ProofCode L Witness)
  | generalize (x : Nat) (premise : ProofCode L Witness)

section Checker

variable {Witness : Type}
variable [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)]

/-- Total proof inference: every malformed inference returns `none`. -/
def check (decode : Witness → Option (FOL.Formula L)) :
    ProofCode L Witness → Option (FOL.Formula L)
  | .logical c => logicalDecode c
  | .nonlogical w => decode w
  | .mp p q => match check decode p, check decode q with
      | some (.imp φ ψ), some χ => if φ = χ then some ψ else none
      | _, _ => none
  | .generalize x p => (check decode p).map (FOL.allAt x)

theorem check_sound {A : FOL.Formula L → Prop}
    (decode : Witness → Option (FOL.Formula L))
    (origin : ∀ w φ, decode w = some φ → A φ)
    (c : ProofCode L Witness) (φ : FOL.Formula L) (h : check decode c = some φ) :
    FOL.Derivation A φ := by
  induction c generalizing φ with
  | logical c => exact .logical (logical_origin c φ h)
  | nonlogical w => exact .axiom (origin w φ h)
  | generalize x c ih =>
      cases hc : check decode c with
      | none => simp [check, hc] at h
      | some ψ =>
          simp only [check, hc, Option.map_some, Option.some.injEq] at h
          subst φ
          exact .generalize x (ih ψ hc)
  | mp p q ihp ihq =>
      cases hp : check decode p with
      | none => simp [check, hp] at h
      | some ψ =>
          cases ψ with
          | falsum => simp [check, hp] at h
          | equal _ _ => simp [check, hp] at h
          | rel _ _ => simp [check, hp] at h
          | all _ => simp [check, hp] at h
          | imp a b =>
              cases hq : check decode q with
              | none => simp [check, hp, hq] at h
              | some χ =>
                  by_cases he : a = χ
                  · subst χ
                    simp [check, hp, hq] at h
                    subst φ
                    exact .mp (ihp _ hp) (ihq _ hq)
                  · simp [check, hp, hq, he] at h

theorem check_coverage {A : FOL.Formula L → Prop}
    (decode : Witness → Option (FOL.Formula L))
    (coverage : ∀ φ, A φ → ∃ w, decode w = some φ)
    {φ : FOL.Formula L} (h : FOL.Derivation A φ) :
    ∃ c, check decode c = some φ := by
  induction h with
  | «axiom» h =>
      obtain ⟨w, hw⟩ := coverage _ h
      exact ⟨.nonlogical w, hw⟩
  | logical h =>
      obtain ⟨c, hc⟩ := logical_coverage h
      exact ⟨.logical c, hc⟩
  | mp _ _ ihp ihq =>
      obtain ⟨p, hp⟩ := ihp
      obtain ⟨q, hq⟩ := ihq
      exact ⟨.mp p q, by simp [check, hp, hq]⟩
  | generalize x _ ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨.generalize x c, by simp [check, hc]⟩

end Checker

/-- A finite enumeration witness consists of a stage and a list position.
Repeated occurrences of an axiom cause no ambiguity. -/
def enumeratedDecode (enumerate : Nat → List (FOL.Formula L))
    (w : Nat × Nat) : Option (FOL.Formula L) := (enumerate w.1)[w.2]?

def EnumeratedAxiom (enumerate : Nat → List (FOL.Formula L)) (φ : FOL.Formula L) : Prop :=
  ∃ s, φ ∈ enumerate s

theorem enumeration_origin (enumerate : Nat → List (FOL.Formula L))
    (w : Nat × Nat) (φ : FOL.Formula L) (h : enumeratedDecode enumerate w = some φ) :
    EnumeratedAxiom enumerate φ :=
  ⟨w.1, List.mem_of_getElem? h⟩

theorem enumeration_coverage (enumerate : Nat → List (FOL.Formula L))
    (φ : FOL.Formula L) (h : EnumeratedAxiom enumerate φ) :
    ∃ w, enumeratedDecode enumerate w = some φ := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hs
  exact ⟨(s, i), hi⟩

inductive PACode : Type
  | succNeZero (t : Peano.Term)
  | succInjective (t u : Peano.Term)
  | addZero (t : Peano.Term)
  | addSucc (t u : Peano.Term)
  | mulZero (t : Peano.Term)
  | mulSucc (t u : Peano.Term)
  | induction (φ : Peano.Formula) (x : Nat)

def paDecode : PACode → Option Peano.Formula
  | .succNeZero t => some ((Peano.succ t).equal Peano.zero).not
  | .succInjective t u => some (((Peano.succ t).equal (Peano.succ u)).imp (t.equal u))
  | .addZero t => some ((Peano.add t Peano.zero).equal t)
  | .addSucc t u => some ((Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u)))
  | .mulZero t => some ((Peano.mul t Peano.zero).equal Peano.zero)
  | .mulSucc t u => some ((Peano.mul t (Peano.succ u)).equal (Peano.add (Peano.mul t u) t))
  | .induction φ x => some (Peano.inductionAxiom φ x)

theorem pa_origin (c : PACode) (φ : Peano.Formula) (h : paDecode c = some φ) :
    Peano.Axiom φ := by
  cases c with
  | succNeZero t => cases h; exact .succ_ne_zero t
  | succInjective t u => cases h; exact .succ_injective t u
  | addZero t => cases h; exact .add_zero t
  | addSucc t u => cases h; exact .add_succ t u
  | mulZero t => cases h; exact .mul_zero t
  | mulSucc t u => cases h; exact .mul_succ t u
  | induction ψ x => cases h; exact .induction ψ x

theorem pa_coverage (φ : Peano.Formula) (h : Peano.Axiom φ) :
    ∃ c, paDecode c = some φ := by
  cases h with
  | succ_ne_zero t => exact ⟨.succNeZero t, rfl⟩
  | succ_injective t u => exact ⟨.succInjective t u, rfl⟩
  | add_zero t => exact ⟨.addZero t, rfl⟩
  | add_succ t u => exact ⟨.addSucc t u, rfl⟩
  | mul_zero t => exact ⟨.mulZero t, rfl⟩
  | mul_succ t u => exact ⟨.mulSucc t u, rfl⟩
  | induction φ x => exact ⟨.induction φ x, rfl⟩

instance (n : Nat) : DecidableEq (Peano.language.Functions n) :=
  inferInstanceAs (DecidableEq (Peano.FunctionSymbol n))
instance (n : Nat) : DecidableEq (Peano.language.Relations n) :=
  inferInstanceAs (DecidableEq Empty)

abbrev PAProofCode := ProofCode Peano.language PACode
def paCheck : PAProofCode → Option Peano.Formula := check paDecode

theorem paCheck_sound (c : PAProofCode) (φ : Peano.Formula) (h : paCheck c = some φ) :
    Peano.FormulaProves φ := check_sound paDecode pa_origin c φ h

theorem paCheck_complete {φ : Peano.Formula} (h : Peano.FormulaProves φ) :
    ∃ c, paCheck c = some φ := check_coverage paDecode pa_coverage h

theorem paCheck_exact (φ : Peano.Formula) :
    (∃ c, paCheck c = some φ) ↔ Peano.FormulaProves φ :=
  ⟨fun ⟨c, hc⟩ => paCheck_sound c φ hc, paCheck_complete⟩

/-- Certificate correctness is derived from syntax before standard PA soundness
is applied; PA soundness is not used to establish any decoder/checker result. -/
theorem paCheck_nat (c : PAProofCode) (φ : Peano.Formula) (h : paCheck c = some φ)
    (v : Nat → Nat) : φ.Realize v := Peano.formula_soundness (paCheck_sound c φ h) v

end PASoundness.Certificates
