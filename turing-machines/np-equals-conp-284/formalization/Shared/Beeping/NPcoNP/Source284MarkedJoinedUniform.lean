import Shared.Beeping.NPcoNP.Source284MarkedJoinedInput

/-! Uniform polynomial workspace and transition bounds for the actual
counter-transfer and joined-input source path. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedJoinedUniform

open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace
open Shared.Beeping.NPcoNP.Source284MarkedJoinedInput (enlargedLimit)

/-- The same fixed source program covers the witness cutoff and gives both
sides any fixed polynomial blank demand in the actual generated guard. -/
theorem uniform_workspace (witnessDemand inputDemand witnessScratchDemand : Polynomial Nat) :
    ∃ k r : Nat, ∀ n inputSuffix witnessSuffix : Nat,
      witnessDemand.eval n ≤ Source284DynamicGuardSource.bound k n ∧
      2^(inputDemand.eval (Source284DynamicGuardSource.bound k n)) ∣ blankTail k r n inputSuffix/2 ∧
      2^(witnessScratchDemand.eval (Source284DynamicGuardSource.bound k n)) ∣
        Source284DynamicJoinedInput.witnessTail (enlargedLimit k r n) witnessSuffix := by
  obtain ⟨k,hk⟩ := Source284DynamicGuardSource.bound_dominates witnessDemand
  obtain ⟨r,hr⟩ := Source284CheckpointGuardVerifier.workspace_dominates_bound k (inputDemand+witnessScratchDemand)
  refine ⟨k,r,?_⟩
  intro n inputSuffix witnessSuffix
  have h := hr n
  simp only [Polynomial.eval_add] at h
  have hm := Source284CheckpointMarkedBounds.mark_count_large k r n
  exact ⟨hk n,Source284MarkedJoinedInput.input_tail_zero k r n inputSuffix _ (by omega),
    Source284MarkedJoinedInput.witness_tail_zero k r n witnessSuffix _ (by omega)⟩

noncomputable def gapBoundPolynomial (k r : Nat) : Polynomial Nat :=
  Source284RestoredPolynomialRunway.countPolynomial k+1+Source284MarkedInputTransferCost.countPolynomial k r

theorem gap_bound (k r n : Nat) : enlargedLimit k r n ≤ (gapBoundPolynomial k r).eval n := by
  have hc : Source284DynamicGuardSource.bound k n ≤ Source284PolynomialMarkedCleanup.count k n+1 := by
    exact Nat.div_le_self _ _
  have he : Source284InputCounterGeometry.extraPairs k r n ≤ markCount k r n := Nat.div_le_self _ _
  simp only [gapBoundPolynomial,Polynomial.eval_add,Polynomial.eval_one,
    Source284RestoredPolynomialRunway.countPolynomial_eval,Source284MarkedInputTransferCost.countPolynomial_eval]
  unfold enlargedLimit
  omega

noncomputable def joinPolynomial (k r : Nat) : Polynomial Nat :=
  let b := gapBoundPolynomial k r
  18*b*b+100*b+2*Polynomial.X+200

/-- Seeking and compacting the enlarged gap remains polynomial, including
all iterations driven by the transferred tape counter. -/
theorem join_polynomial (k r : Nat) (input witness : List Bool) (certificate : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    Source284DynamicJoinedInput.cost (enlargedLimit k r input.length) input witness ≤
      (joinPolynomial k r).eval input.length := by
  let limit := enlargedLimit k r input.length
  let b := (gapBoundPolynomial k r).eval input.length
  have hw := Source284TaggedWitnessCodec.decode_length (Source284DynamicGuardSource.bound k input.length)
    certificate witness hdec
  have hb : limit ≤ b := gap_bound k r input.length
  have hl : Source284DynamicGuardSource.bound k input.length ≤ limit := by dsimp [limit,enlargedLimit]; omega
  have hwb : witness.length ≤ b := by omega
  have hsquare := Nat.mul_self_le_mul_self hwb
  have hmul : (2*((limit+1)+1))*(8*witness.length+11) ≤ (2*(b+2))*(8*b+11) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hif : (if witness=[] then 4 else 2) ≤ 4 := by split <;> omega
  simp only [joinPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  change Source284DynamicJoinedInput.cost limit input witness ≤ 18*b*b+100*b+2*input.length+200
  unfold Source284DynamicJoinedInput.cost Source284WitnessCompact.extraCost
  rw [Source284ScratchPack.totalCost_formula]
  nlinarith

noncomputable def totalPolynomial (k r : Nat) : Polynomial Nat :=
  Source284MarkedInputTransferCost.totalPolynomial k r+joinPolynomial k r

theorem total_polynomial (k r : Nat) (input witness : List Bool) (certificate : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    Source284MarkedJoinedInput.totalCost k r input witness ≤ (totalPolynomial k r).eval input.length := by
  have hfirst := Source284MarkedInputTransferCost.total_polynomial k r input witness certificate hdec
  have hsecond := join_polynomial k r input witness certificate hdec
  simp only [totalPolynomial,Polynomial.eval_add,Source284MarkedJoinedInput.totalCost]
  omega

end Shared.Beeping.NPcoNP.Source284MarkedJoinedUniform
