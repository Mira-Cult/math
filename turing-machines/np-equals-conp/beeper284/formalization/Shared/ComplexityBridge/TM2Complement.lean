import Shared.ComplexityBridge.TM2WholePair

namespace Shared.ComplexityBridge.TM2Complement
open Shared.Codes.TM2Candidate Shared.Codes.TM2CheckedCandidate
open Shared.ComplexityBridge.TM2BooleanOutput Shared.ComplexityBridge.TM2RawInput
open Shared.Codes.TM2Micro

/-- Exchange the output codes while keeping the program, input data, clock,
and output-stack index unchanged. -/
def swap (c : Candidate) : Candidate :=
  (c.1,(c.2.2.1,c.2.1,c.2.2.2))

@[simp] theorem swap_involutive (c : Candidate) : swap (swap c) = c := by
  rcases c with ⟨a,z,o,k⟩
  rfl

@[simp] theorem swap_valid (c : Candidate) : candidateValid (swap c) = candidateValid c := by
  rfl

/-- Swapping codes flips only valid Booleans and retains rejection of every
malformed output, including coincident codes. -/
theorem decodeStack_swap (z o : Nat) (xs : List Nat) :
    decodeStack (o,z,xs) = (decodeStack (z,o,xs)).map (!·) := by
  by_cases h : z = o
  · subst o
    simp [decodeStack]
  · have h' : o ≠ z := Ne.symm h
    by_cases hz : xs = [z]
    · subst xs
      simp [decodeStack,h,h']
    · by_cases ho : xs = [o]
      · subst xs
        simp [decodeStack,h,h']
      · simp [decodeStack,h,h',hz,ho]

theorem extractMemory_swap (z o out : Nat) (label : Option Nat) (s : Shared.Codes.TM2StatementExecution.Stacks) :
    extractMemory (o,z,out,label,s) = (extractMemory (z,o,out,label,s)).map (!·) := by
  cases label with
  | none =>
    change decodeStack (o,z,Shared.Codes.TM2StatementExecution.stackFn s out) =
      (decodeStack (z,o,Shared.Codes.TM2StatementExecution.stackFn s out)).map (!·)
    exact decodeStack_swap z o _
  | some l => rfl

/-- Swapping a checked candidate's codes preserves every timeout or invalid
result and complements each successfully decoded Boolean. -/
theorem evaluate_swap (c : Candidate) (x : List Bool) :
    Shared.Codes.TM2CheckedCandidate.evaluate (swap c) x =
      (Shared.Codes.TM2CheckedCandidate.evaluate c x).map (!·) := by
  unfold Shared.Codes.TM2CheckedCandidate.evaluate
  rw [swap_valid]
  cases hv : candidateValid c with
  | false => simp
  | true =>
    simp only [↓reduceIte]
    unfold Shared.Codes.TM2Candidate.evaluate
    cases hs : buildDecisionInput (c.1.2.2,x) with
    | none => simp [swap, hs]
    | some start =>
      cases hr : runEncoded ((c.1.1,(x.length+2)^c.1.2.1),start) with
      | none => simp [swap, hs, hr]
      | some r =>
        rcases r with ⟨halted,raw⟩
        cases halted with
        | false => simp [swap,hs,hr]
        | true => simpa [swap,hs,hr] using extractMemory_swap c.2.1 c.2.2.1 c.2.2.2 raw.1 raw.2.2

/-- Canonical P is closed under Boolean complement. -/
theorem p_complement (f : ComplexityTheory.DecisionProblem) (hf : f ∈ ComplexityTheory.P) :
    (fun x => !f x) ∈ ComplexityTheory.P := by
  obtain ⟨c,hc⟩ := (Shared.ComplexityBridge.TM2Whole.candidate_iff_P f).2 hf
  apply (Shared.ComplexityBridge.TM2Whole.candidate_iff_P (fun x => !f x)).1
  refine ⟨swap c,?_⟩
  intro x
  rw [evaluate_swap,hc x]
  rfl

/-- Class-level complement closure for the public P class. -/
theorem p_closed_under_complement (f : ComplexityTheory.DecisionProblem) :
    f ∈ ComplexityTheory.P ↔ fᶜ ∈ ComplexityTheory.P := by
  constructor
  · intro h
    exact p_complement f h
  · intro h
    have h' := p_complement fᶜ h
    simpa using h'

/-- The same code swap works for the independently clocked pair evaluator. -/
theorem pair_evaluate_swap (c : Candidate) (x w : List Bool) :
    Shared.Codes.TM2PairCandidate.evaluate (swap c) x w =
      (Shared.Codes.TM2PairCandidate.evaluate c x w).map (!·) := by
  unfold Shared.Codes.TM2PairCandidate.evaluate
  rw [swap_valid]
  cases hv : candidateValid c with
  | false => simp
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
    cases hs : Shared.ComplexityBridge.TM2RawInput.buildPairInput (c.1.2.2,(x,w)) with
    | none => simp [swap,hs]
    | some start =>
      cases hr : runEncoded ((c.1.1,(x.length+w.length+2)^c.1.2.1),start) with
      | none => simp [swap,hs,hr]
      | some r =>
        rcases r with ⟨halted,raw⟩
        cases halted with
        | false => simp [swap,hs,hr]
        | true => simpa [swap,hs,hr] using extractMemory_swap c.2.1 c.2.2.1 c.2.2.2 raw.1 raw.2.2

/-- Canonical polynomial-time Boolean relations are closed under negation. -/
theorem pair_complement (R : (List Bool × List Bool) → Bool) (hR : ComplexityTheory.IsPolyTime R) :
    ComplexityTheory.IsPolyTime (fun x => !R x) := by
  obtain ⟨c,hc⟩ := (Shared.ComplexityBridge.TM2WholePair.pair_candidate_iff_poly R).2 hR
  apply (Shared.ComplexityBridge.TM2WholePair.pair_candidate_iff_poly (fun x => !R x)).1
  refine ⟨swap c,?_⟩
  intro x w
  rw [pair_evaluate_swap,hc x w]
  rfl

/-- The complement class formed from P is exactly P, proved independently of
the placeholder declarations in the conjecture file. -/
theorem complement_class_eq_P :
    {f : ComplexityTheory.DecisionProblem | fᶜ ∈ ComplexityTheory.P} = ComplexityTheory.P := by
  ext f
  exact (p_closed_under_complement f).symm

/-- For this complement-closed P, inclusion in NP and inclusion in coNP
are equivalent; neither inclusion is assumed or asserted unconditionally. -/
theorem P_subset_coNP_iff_P_subset_NP :
    ComplexityTheory.P ⊆ ComplexityTheory.coNP ↔ ComplexityTheory.P ⊆ ComplexityTheory.NP := by
  constructor
  · intro h L hL
    have hc : Lᶜ ∈ ComplexityTheory.P := (p_closed_under_complement L).1 hL
    have hn := h hc
    change (Lᶜ)ᶜ ∈ ComplexityTheory.NP at hn
    simpa using hn
  · intro h L hL
    change Lᶜ ∈ ComplexityTheory.NP
    exact h ((p_closed_under_complement L).1 hL)

/-- The known one-way implication between the two complexity equalities.
No converse is asserted. -/
theorem P_eq_NP_implies_NP_eq_coNP (h : ComplexityTheory.P = ComplexityTheory.NP) :
    ComplexityTheory.NP = ComplexityTheory.coNP := by
  apply Set.ext
  intro L
  change L ∈ ComplexityTheory.NP ↔ Lᶜ ∈ ComplexityTheory.NP
  rw [← h]
  exact p_closed_under_complement L

example : decodeStack (1,0,[1]) = some false ∧ decodeStack (0,1,[1]) = some true := by decide
example : decodeStack (1,0,[2]) = none ∧ decodeStack (0,1,[2]) = none := by decide
example : decodeStack (0,0,[0]) = none := by decide

end Shared.ComplexityBridge.TM2Complement
