import Shared.Codes.VerifierPrograms

/-! Class-theoretic consequences for the pinned Google complexity classes.
The polynomial closure, completeness, candidate-model, and finite-machine
certificate hypotheses are not discharged here. The two endpoint theorems are
conditional, use separate comparisons, and assume no complexity negation. -/
namespace Shared.ComplexityBridge.CanonicalClasses
open ComplexityTheory

/-- A uniform polynomial-time many-one reduction on all raw bitstrings. -/
def PolyRed (A B : DecisionProblem) : Prop :=
  ∃ f : List Bool → List Bool, IsPolyTime f ∧ ∀ x, A x = B (f x)

/-- Membership and uniform polynomial many-one hardness for canonical NP. -/
structure CompleteLanguage (S : DecisionProblem) where
  reference : DecisionProblem
  reference_correct : ∀ x, reference x = S x
  reference_computable : Computable reference
  member : S ∈ NP
  hard : ∀ L : DecisionProblem, L ∈ NP → PolyRed L S

/-- Closure under the reduction actually used; this is an explicit obligation. -/
def PullbackClosed (C : DecisionComplexityClass) : Prop :=
  ∀ A B : DecisionProblem, B ∈ C → PolyRed A B → A ∈ C

theorem polyRed_complement {A B : DecisionProblem} (h : PolyRed A B) :
    PolyRed Aᶜ Bᶜ := by
  obtain ⟨f, hf, h⟩ := h
  refine ⟨f, hf, ?_⟩
  intro x
  exact congrArg (fun b : Bool => !b) (h x)

theorem coNP_subset_NP_iff : coNP ⊆ NP ↔ NP = coNP := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro L hL
      change Lᶜ ∈ NP
      apply h
      change (Lᶜ)ᶜ ∈ NP
      simpa using hL
    · exact h
  · intro h L hL
    rw [h]
    exact hL

theorem p_eq_np_iff_complete_in_p {S : DecisionProblem} (complete : CompleteLanguage S)
    (p_subset_np : P ⊆ NP) (p_pullback : PullbackClosed P) :
    P = NP ↔ S ∈ P := by
  constructor
  · intro h
    rw [h]
    exact complete.member
  · intro h
    apply Set.Subset.antisymm p_subset_np
    intro L hL
    exact p_pullback L S h (complete.hard L hL)

theorem np_eq_conp_iff_complement_complete_in_np {S : DecisionProblem}
    (complete : CompleteLanguage S) (np_pullback : PullbackClosed NP) :
    NP = coNP ↔ Sᶜ ∈ NP := by
  constructor
  · intro h
    have hs : Sᶜ ∈ coNP := by
      change (Sᶜ)ᶜ ∈ NP
      simpa using complete.member
    rw [h]
    exact hs
  · intro h
    apply coNP_subset_NP_iff.mp
    intro L hL
    have hc : Lᶜ ∈ NP := hL
    have hr : PolyRed L Sᶜ := by
      have hred := polyRed_complement (complete.hard Lᶜ hc)
      simpa using hred
    exact np_pullback L Sᶜ h hr


/-- The SAT candidate-to-P equivalence remains a model-simulation obligation. -/
def SatCandidateBridge : Prop :=
  (∃ c : Shared.Codes.FinitePrograms.Candidate,
    Shared.Codes.FinitePrograms.valid c.2 = true ∧
      ∀ input, Shared.Codes.FinitePrograms.evaluate c (BitstringEncoding.bitEncode input) = some (Shared.ComplexityBridge.CNF.sat input)) ↔
    Shared.ComplexityBridge.CNF.sat ∈ P

/-- The UNSAT verifier-to-NP equivalence remains a separate model obligation. -/
def UnsatCandidateBridge : Prop :=
  (∃ v : Shared.Codes.VerifierPrograms.Verifier,
    Shared.Codes.FinitePrograms.valid v.2.2 = true ∧
      ∀ input, Shared.Codes.VerifierPrograms.test v input = true) ↔
    (Shared.ComplexityBridge.CNF.sat)ᶜ ∈ NP

theorem pnp_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.Codes.FinitePrograms.compareSAT 0 M)
    (complete : CompleteLanguage Shared.ComplexityBridge.CNF.sat)
    (p_subset_np : P ⊆ NP) (p_pullback : PullbackClosed P)
    (candidate : SatCandidateBridge) :
    M.system.EventuallySilent ↔ P = NP := by
  exact (Shared.Codes.FinitePrograms.certified_machine_silent_iff cert).trans
    (candidate.trans
      (p_eq_np_iff_complete_in_p complete p_subset_np p_pullback).symm)

theorem npconp_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.Codes.VerifierPrograms.compare 0 M)
    (complete : CompleteLanguage Shared.ComplexityBridge.CNF.sat)
    (np_pullback : PullbackClosed NP) (candidate : UnsatCandidateBridge) :
    M.system.EventuallySilent ↔ NP = coNP := by
  exact (Shared.Codes.VerifierPrograms.certified_machine_silent_iff cert).trans
    (candidate.trans
      (np_eq_conp_iff_complement_complete_in_np complete np_pullback).symm)


/-- The already executable CNF reference discharges the reference fields;
NP membership and uniform hardness remain explicit inputs. -/
def cnfComplete
    (membership : Shared.ComplexityBridge.CNF.sat ∈ NP)
    (hardness : ∀ L : DecisionProblem, L ∈ NP → PolyRed L Shared.ComplexityBridge.CNF.sat) :
    CompleteLanguage Shared.ComplexityBridge.CNF.sat where
  reference := Shared.ComplexityBridge.CNF.sat
  reference_correct := fun _ => rfl
  reference_computable := Shared.ComplexityBridge.ParserComputability.sat_computable
  member := membership
  hard := hardness

theorem totalComplement_eq :
    Shared.ComplexityBridge.CNF.complementSat = (Shared.ComplexityBridge.CNF.sat)ᶜ := rfl

end Shared.ComplexityBridge.CanonicalClasses
