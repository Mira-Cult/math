import PASoundness.PAtoCompactAllElimTermEquality
import PASoundness.PAtoCompactVacuousQuantifierFree

/-! A conditional reduction of guarded PA equality substitution to its
equality-frame matrix. The pointwise matrix implication is an explicit finite
K proof input; this file does not construct term-graph functionality or output
transport, and does not use semantic soundness. -/

namespace PASoundness.PAtoCompactEqSubstFrameElimination

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactAllElimTermEquality

/-- Eliminate the two value witnesses of an equality frame. The pointwise
matrix proof and freshness of the guard/source/target free names are explicit. -/
def frame_of_matrix (g : Formula) (φ : Peano.Formula) (x : Nat) (t u : Peano.Term)
    (b : Nat) (hg : ∀ a ∈ g.free, a < b)
    (hs : ∀ a ∈ (formula (FOL.substAt φ x t)).free, a < b)
    (ht : ∀ a ∈ (formula (FOL.substAt φ x u)).free, a < b)
    (pointwise : KDerivation (imp g.encode
      (imp (matrix id t u b (b+1) (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost u)).encode
        (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x u)))))) :
    KDerivation (imp g.encode (imp (equalityFrame id t u b).encode
      (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x u))))) := by
  let M := matrix id t u b (b+1) (b+2) (b+2+termCost t)
    (b+2+termCost t+termCost u)
  let X := Formula.imp (formula (FOL.substAt φ x t)) (formula (FOL.substAt φ x u))
  have hg0 : b ∉ g.free := by intro h; have := hg b h; omega
  have hg1 : b+1 ∉ g.free := by intro h; have := hg (b+1) h; omega
  have hx0 : b ∉ X.free := by
    intro h
    have h' : b ∈ (formula (FOL.substAt φ x t)).free ∨
        b ∈ (formula (FOL.substAt φ x u)).free := by simpa [X, Formula.free] using h
    rcases h' with h | h
    · have := hs b h; omega
    · have := ht b h; omega
  have hx1 : b+1 ∉ X.free := by
    intro h
    have h' : b+1 ∈ (formula (FOL.substAt φ x t)).free ∨
        b+1 ∈ (formula (FOL.substAt φ x u)).free := by simpa [X, Formula.free] using h
    rcases h' with h | h
    · have := hs (b+1) h; omega
    · have := ht (b+1) h; omega
  have hp : KDerivation (imp g.encode (imp M.encode X.encode)) := by
    simpa only [M, X, Formula.encode, code] using pointwise
  change KDerivation (imp g.encode
    (imp (existsCode b (existsCode (b+1) M.encode)) X.encode))
  exact two_exists_left_guarded b (b+1) g.encode M.encode X.encode
    (free_vacuity b g hg0) (free_vacuity (b+1) g hg1)
    (free_vacuity b X hx0) (free_vacuity (b+1) X hx1) hp

/-- Construct a guarded equality-substitution axiom from its pointwise matrix
proof. The equality frame is first transported to a common high base; no
assumption that its original witness names are fresh for the other formulas
is made. -/
noncomputable def guarded_of_matrix (φ : Peano.Formula) (x : Nat) (t u : Peano.Term)
    (b : Nat) (ht : ∀ a ∈ t.varFinset, a < b) (hu : ∀ a ∈ u.varFinset, a < b)
    (hg : ∀ a ∈ (guardFormula ((t.equal u).imp
      ((FOL.substAt φ x t).imp (FOL.substAt φ x u)))).free, a < b)
    (hs : ∀ a ∈ (formula (FOL.substAt φ x t)).free, a < b)
    (hd : ∀ a ∈ (formula (FOL.substAt φ x u)).free, a < b)
    (pointwise : KDerivation (imp (guardFormula ((t.equal u).imp
      ((FOL.substAt φ x t).imp (FOL.substAt φ x u)))).encode
      (imp (matrix id t u b (b+1) (b+2) (b+2+termCost t)
        (b+2+termCost t+termCost u)).encode
        (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x u)))))) :
    KDerivation (guardedCode ((t.equal u).imp
      ((FOL.substAt φ x t).imp (FOL.substAt φ x u)))) := by
  let A := (t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))
  let G := (guardFormula A).encode
  let E := code (t.equal u)
  let C := code (FOL.substAt φ x t)
  let D := code (FOL.substAt φ x u)
  let F := (equalityFrame id t u b).encode
  have ht0 : ∀ a ∈ t.varFinset, a < scopeBase (t.equal u) Fin.elim0 := by
    intro a ha
    exact names_lt_original_base t u a (Finset.mem_union_left _ ha)
  have hu0 : ∀ a ∈ u.varFinset, a < scopeBase (t.equal u) Fin.elim0 := by
    intro a ha
    exact names_lt_original_base t u a (Finset.mem_union_right _ ha)
  have hm := (equalityFrame_base_transport id t u (scopeBase (t.equal u) Fin.elim0)
    b ht0 hu0 ht hu).1
  have he : KDerivation (imp E F) := by
    simpa only [E, F, code, original_shape] using hm
  have hf : KDerivation (imp G (imp F (imp C D))) :=
    frame_of_matrix (guardFormula A) φ x t u b hg hs hd pointwise
  change KDerivation (guardedCode A)
  simp only [guardedCode, A, code_imp]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [C, E, G]
  have hc : Context Γ C := Context.head _ _
  have heq : Context Γ E := .hypothesis (by simp [Γ])
  have hguard : Context Γ G := .hypothesis (by simp [Γ])
  exact .mp hc (.mp (.mp heq (.closed he)) (.mp hguard (.closed hf)))

end PASoundness.PAtoCompactEqSubstFrameElimination

#print axioms PASoundness.PAtoCompactEqSubstFrameElimination.frame_of_matrix
#print axioms PASoundness.PAtoCompactEqSubstFrameElimination.guarded_of_matrix
