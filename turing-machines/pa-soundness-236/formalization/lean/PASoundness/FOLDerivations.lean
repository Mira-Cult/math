import PASoundness.FOL

/-!
# Finite derived rules for the genuine first-order calculus

Every result in this module constructs a derivation from the explicit Hilbert
schemas in `FOL.LogicalAxiom`. The temporary-context calculus has only finite
hypotheses, closed derivations, and modus ponens. Its deduction theorem expands
through K and S. No semantic completeness theorem is used.
-/

namespace PASoundness.FOL

open FirstOrder FirstOrder.Language

variable {L : Language} {A : Formula L → Prop}

/-- Finite temporary hypotheses, kept separate from universally interpreted
nonlogical axioms. Generalization is introduced only by a derived rule with
an explicit freshness condition below. -/
inductive Context (A : Formula L → Prop) (Γ : List (Formula L)) : Formula L → Prop
  | hypothesis {φ} : φ ∈ Γ → Context A Γ φ
  | closed {φ} : Derivation A φ → Context A Γ φ
  | mp {φ ψ} : Context A Γ (φ.imp ψ) → Context A Γ φ → Context A Γ ψ

namespace Derivation

theorem identity (φ : Formula L) : Derivation A (φ.imp φ) := by
  have h₁ := Derivation.logical (Axiom := A) (LogicalAxiom.k φ (φ.imp φ))
  have h₂ := Derivation.logical (Axiom := A) (LogicalAxiom.k φ φ)
  have h₃ := Derivation.logical (Axiom := A) (LogicalAxiom.s φ (φ.imp φ) φ)
  exact .mp (.mp h₃ h₁) h₂

theorem top : Derivation A (⊤ : Formula L) := identity ⊥

theorem weakening {φ : Formula L} (h : Derivation A φ) (ψ : Formula L) :
    Derivation A (ψ.imp φ) := .mp (.logical (.k φ ψ)) h

end Derivation

namespace Context

theorem weaken {Γ Δ : List (Formula L)} {φ : Formula L} (d : Context A Γ φ)
    (h : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ) : Context A Δ φ := by
  induction d with
  | hypothesis hφ => exact .hypothesis (h _ hφ)
  | closed d => exact .closed d
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

theorem close {Γ : List (Formula L)} {φ : Formula L} (d : Context A Γ φ)
    (h : ∀ ψ, ψ ∈ Γ → Derivation A ψ) : Derivation A φ := by
  induction d with
  | hypothesis hφ => exact h _ hφ
  | closed d => exact d
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

theorem closeEmpty {φ : Formula L} (d : Context A [] φ) : Derivation A φ :=
  close d (fun _ h => False.elim (List.not_mem_nil h))

theorem lift {Γ : List (Formula L)} {φ : Formula L} (d : Context A Γ φ)
    (ψ : Formula L) : Context A Γ (ψ.imp φ) :=
  .mp (.closed (.logical (.k φ ψ))) d

theorem under {Γ : List (Formula L)} {φ : Formula L} (d : Context A Γ φ)
    (ψ : Formula L) : Context A (ψ :: Γ) φ :=
  weaken d (fun _ h => List.mem_cons_of_mem ψ h)

theorem head (Γ : List (Formula L)) (φ : Formula L) : Context A (φ :: Γ) φ :=
  .hypothesis (List.mem_cons_self ..)

/-- Actual Hilbert deduction, using K for old hypotheses and S for MP. -/
theorem deduction {Γ : List (Formula L)} {φ ψ : Formula L}
    (d : Context A (φ :: Γ) ψ) : Context A Γ (φ.imp ψ) := by
  induction d with
  | @hypothesis ψ hψ =>
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact .closed (.identity _)
    · exact lift (.hypothesis hψ) φ
  | closed d => exact lift (.closed d) φ
  | @mp ψ χ _ _ ih₁ ih₂ =>
    exact .mp (.mp (.closed (.logical (.s φ ψ χ))) ih₁) ih₂

theorem apply {Γ : List (Formula L)} {φ ψ : Formula L}
    (d : Context A (φ :: Γ) ψ) (hφ : Context A Γ φ) : Context A Γ ψ :=
  .mp (deduction d) hφ

/-- Explosion is derived from K and double-negation elimination. -/
theorem explode {Γ : List (Formula L)} (φ : Formula L)
    (h : Context A Γ ⊥) : Context A Γ φ :=
  .mp (.closed (.logical (.classical φ))) (lift h φ.not)

theorem dne {Γ : List (Formula L)} {φ : Formula L}
    (h : Context A Γ φ.not.not) : Context A Γ φ :=
  .mp (.closed (.logical (.classical φ))) h

theorem doubleNegIntro {Γ : List (Formula L)} {φ : Formula L}
    (h : Context A Γ φ) : Context A Γ φ.not.not :=
  deduction (.mp (head Γ φ.not) (under h φ.not))

theorem conjunctionIntro {Γ : List (Formula L)} {φ ψ : Formula L}
    (hφ : Context A Γ φ) (hψ : Context A Γ ψ) : Context A Γ (φ ⊓ ψ) :=
  deduction (.mp (.mp (head Γ (φ.imp ψ.not)) (under hφ (φ.imp ψ.not)))
    (under hψ (φ.imp ψ.not)))

theorem conjunctionLeft {Γ : List (Formula L)} {φ ψ : Formula L}
    (h : Context A Γ (φ ⊓ ψ)) : Context A Γ φ := by
  apply dne
  apply deduction
  apply Context.mp (φ := φ.imp ψ.not)
  · exact under h φ.not
  · apply deduction
    exact explode ψ.not (.mp (under (head Γ φ.not) φ) (head (φ.not :: Γ) φ))

theorem conjunctionRight {Γ : List (Formula L)} {φ ψ : Formula L}
    (h : Context A Γ (φ ⊓ ψ)) : Context A Γ ψ :=
  dne (deduction (.mp (under h ψ.not) (lift (head Γ ψ.not) φ)))

theorem contrapose {Γ : List (Formula L)} {φ ψ : Formula L}
    (h : Context A Γ (φ.imp ψ)) : Context A Γ (ψ.not.imp φ.not) :=
  deduction (deduction (.mp (under (head Γ ψ.not) φ)
    (.mp (under (under h ψ.not) φ) (head (ψ.not :: Γ) φ))))

theorem implicationCongr {Γ : List (Formula L)} {φ φ' ψ ψ' : Formula L}
    (hφ : Context A Γ (φ'.imp φ)) (hψ : Context A Γ (ψ.imp ψ')) :
    Context A Γ ((φ.imp ψ).imp (φ'.imp ψ')) := by
  apply deduction
  apply deduction
  exact .mp (under (under hψ (φ.imp ψ)) φ')
    (.mp (under (head Γ (φ.imp ψ)) φ')
      (.mp (under (under hφ (φ.imp ψ)) φ') (head ((φ.imp ψ) :: Γ) φ')))

/-- Context generalization uses the actual finite free-variable side condition. -/
theorem generalize {Γ : List (Formula L)} {φ : Formula L} (x : Nat)
    (hx : ∀ ψ, ψ ∈ Γ → x ∉ ψ.freeVarFinset)
    (h : Context A Γ φ) : Context A Γ (allAt x φ) := by
  induction h with
  | @hypothesis ψ hψ =>
    exact .mp (.closed (.logical (.vacuous ψ x (hx ψ hψ)))) (.hypothesis hψ)
  | closed h => exact .closed (.generalize x h)
  | @mp ψ χ _ _ ih₁ ih₂ =>
    exact .mp (.mp (.closed (.logical (.allImp ψ χ x))) ih₁) ih₂

end Context

namespace Derivation

theorem explosion (φ : Formula L) : Derivation A ((⊥ : Formula L).imp φ) :=
  Context.closeEmpty (Context.deduction (Context.explode φ (Context.head [] ⊥)))

theorem doubleNegIntro (φ : Formula L) : Derivation A (φ.imp φ.not.not) :=
  Context.closeEmpty (Context.deduction (Context.doubleNegIntro (Context.head [] φ)))

theorem contrapose {φ ψ : Formula L} (h : Derivation A (φ.imp ψ)) :
    Derivation A (ψ.not.imp φ.not) :=
  Context.closeEmpty (Context.contrapose (.closed h))

theorem compose {φ ψ χ : Formula L} (hφψ : Derivation A (φ.imp ψ))
    (hψχ : Derivation A (ψ.imp χ)) : Derivation A (φ.imp χ) :=
  Context.closeEmpty (Context.deduction
    (.mp (.closed hψχ) (.mp (.closed hφψ) (Context.head [] φ))))

theorem implicationCongr {φ φ' ψ ψ' : Formula L}
    (hφ : Derivation A (φ'.imp φ)) (hψ : Derivation A (ψ.imp ψ')) :
    Derivation A ((φ.imp ψ).imp (φ'.imp ψ')) :=
  Context.closeEmpty (Context.implicationCongr (.closed hφ) (.closed hψ))

theorem allCongr (x : Nat) {φ ψ : Formula L} (h : Derivation A (φ.imp ψ)) :
    Derivation A ((allAt x φ).imp (allAt x ψ)) :=
  .mp (.logical (.allImp φ ψ x)) (.generalize x h)

/-- The compact single propositional axiom is an actual finite Hilbert theorem. -/
theorem compactPropositional (φ ψ χ υ : Formula L) :
    Derivation A (((χ.imp υ).imp φ).imp ((φ.imp χ).imp (ψ.imp χ))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.dne
  apply Context.deduction
  have hneg : Context A [χ.not, ψ, φ.imp χ, (χ.imp υ).imp φ] χ.not :=
    Context.head _ _
  have hφχ : Context A [χ.not, ψ, φ.imp χ, (χ.imp υ).imp φ] (φ.imp χ) :=
    .hypothesis (by simp)
  have hi : Context A [χ.not, ψ, φ.imp χ, (χ.imp υ).imp φ] ((χ.imp υ).imp φ) :=
    .hypothesis (by simp)
  have hχυ : Context A [χ.not, ψ, φ.imp χ, (χ.imp υ).imp φ] (χ.imp υ) :=
    Context.deduction (Context.explode υ (.mp (Context.under hneg χ)
      (Context.head _ χ)))
  exact .mp hneg (.mp hφχ (.mp hi hχυ))

/-- Two finite derivations, one in each direction. This is syntactic
interderivability, without a semantic equivalence premise. -/
def Equivalent (A : Formula L → Prop) (φ ψ : Formula L) : Prop :=
  Derivation A (φ.imp ψ) ∧ Derivation A (ψ.imp φ)

namespace Equivalent

theorem refl (φ : Formula L) : Equivalent A φ φ := ⟨identity φ, identity φ⟩

theorem symm {φ ψ : Formula L} (h : Equivalent A φ ψ) : Equivalent A ψ φ :=
  ⟨h.2,h.1⟩

theorem trans {φ ψ χ : Formula L} (hφψ : Equivalent A φ ψ)
    (hψχ : Equivalent A ψ χ) : Equivalent A φ χ :=
  ⟨compose hφψ.1 hψχ.1, compose hψχ.2 hφψ.2⟩

theorem of_provable {φ ψ : Formula L} (hφ : Derivation A φ)
    (hψ : Derivation A ψ) : Equivalent A φ ψ :=
  ⟨weakening hψ φ, weakening hφ ψ⟩

theorem imp {φ φ' ψ ψ' : Formula L} (hφ : Equivalent A φ φ')
    (hψ : Equivalent A ψ ψ') : Equivalent A (φ.imp ψ) (φ'.imp ψ') :=
  ⟨implicationCongr hφ.2 hψ.1, implicationCongr hφ.1 hψ.2⟩

theorem all (x : Nat) {φ ψ : Formula L} (h : Equivalent A φ ψ) :
    Equivalent A (allAt x φ) (allAt x ψ) :=
  ⟨allCongr x h.1, allCongr x h.2⟩

theorem forward {φ ψ : Formula L} (h : Equivalent A φ ψ)
    (d : Derivation A φ) : Derivation A ψ := .mp h.1 d

theorem backward {φ ψ : Formula L} (h : Equivalent A φ ψ)
    (d : Derivation A ψ) : Derivation A φ := .mp h.2 d

end Equivalent

end Derivation

end PASoundness.FOL
