import Shared.Beeping.NPcoNP.Source284CheckpointMarkedVerifier
import Shared.Beeping.NPcoNP.Source284DynamicGuardReveal

/-! Reveal the successfully guarded witness and the counter-bearing input
stream. This is the executable handoff needed by the existing frame and
join tables; extra witness-side workspace is not yet manufactured here. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointMarkedReveal

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift)
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedGuard (stream otherHalf)

def description (k r n : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284CheckpointMarkedVerifier.description k r (Source284DynamicGuardReveal.states n)
    (Source284DynamicGuardReveal.table continuation)

def totalCost (k r : Nat) (input witness : List Bool) : Nat :=
  Source284CheckpointMarkedGuard.totalCost k r input+
    Source284DynamicGuardReveal.revealCost (Source284DynamicGuardSource.bound k input.length) witness

/-- The actual guard and reveal table hands off both the saved witness and
counter-bearing input stream, for every continuation clock. -/
theorem decoded_reveal (k r n : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (certificate inputSuffix : Nat) (hn : 0 < n) (hv : Closed n continuation)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate=4*encodeFrame witness witnessSuffix ∧ ∀ fuel,
      let limit := Source284DynamicGuardSource.bound k input.length
      let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
      let saved := 4*(4^(limit+1)*(2*wf))+1
      Source284Relative.run (description k r n continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (totalCost k r input witness+fuel) =
      lift (1371+317*k+317*r+318+1) (Source284Relative.run (encode n continuation 1)
        ⟨2*saved+1,stream k r input inputSuffix,active 0⟩ fuel) := by
  let limit := Source284DynamicGuardSource.bound k input.length
  let inputData := otherHalf k r input inputSuffix
  have hm := Source284DynamicGuardReveal.marker_closed n continuation hn hv
  obtain ⟨witnessSuffix,hcert,hreveal⟩ := Source284OffsetRevealInput.decoded_reveal_then
    (1+n) (Source284DynamicGuardReveal.markerTable continuation) limit certificate inputData witness (by omega) hm hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
  let saved := 4*(4^(limit+1)*(2*wf))+1
  have hinput : inputData = 2*stream k r input inputSuffix+1 :=
    Source284CheckpointMarkedGuard.otherHalf_shape k r input inputSuffix
  have ht := hreveal (1+fuel)
  change Source284Relative.run
    (Source284OffsetTagged.description (Source284DynamicGuardReveal.states n)
      (Source284DynamicGuardReveal.table continuation))
    (Source284Relative.initial certificate _) _ =
      lift 318 (Source284Relative.run (encode (1+n) (Source284DynamicGuardReveal.markerTable continuation) 1)
        ⟨saved,inputData,active 0⟩ (1+fuel)) at ht
  rw [hinput,Source284DynamicGuardReveal.encoded_marker_then n continuation saved (stream k r input inputSuffix)
    fuel hn hv,Source284SourceRelocation.lift_add] at ht
  have hs := Source284CheckpointMarkedVerifier.source_after k r (Source284DynamicGuardReveal.states n)
    (Source284DynamicGuardReveal.table continuation) input certificate inputSuffix
    (Source284DynamicGuardReveal.revealCost limit witness+fuel)
    (by simp [Source284DynamicGuardReveal.states]) (Source284DynamicGuardReveal.table_closed n continuation hn hv)
  change Source284Relative.run (description k r n continuation)
    (Source284Relative.initial (encodeFrame input inputSuffix) certificate) _ =
      lift (1371+317*k+317*r) (Source284Relative.run
        (Source284OffsetTagged.description (Source284DynamicGuardReveal.states n)
          (Source284DynamicGuardReveal.table continuation))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) inputData))
        (Source284DynamicGuardReveal.revealCost limit witness+fuel)) at hs
  have htime : Source284DynamicGuardReveal.revealCost limit witness+fuel =
      4+(Source284PayloadSentinelPipeline.totalCost witness.length+
        (Source284OffsetMatch.compareCost witness.length+(1+
          ((1+((4*(limit+1)+6)+(4*witness.length+12)))+
            (10*witness.length+21+((3+(2*(limit+1)+3))+(1+fuel))))))) := by
    simp [Source284DynamicGuardReveal.revealCost]; omega
  rw [hinput,htime,ht,Source284SourceRelocation.lift_add] at hs
  rw [← htime] at hs
  simpa [totalCost,limit,wf,saved,Nat.add_assoc] using hs

theorem rejected_raw_never_accepts (k r n : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < n) (hv : Closed n continuation)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k r n continuation) input certificate clock = false := by
  exact Source284CheckpointMarkedVerifier.rejected_raw_certificate_never_accepts k r _ _ input certificate
    (by simp [Source284DynamicGuardReveal.states]) (Source284DynamicGuardReveal.table_closed n continuation hn hv) hbad

noncomputable def costPolynomial (k r : Nat) : Polynomial Nat :=
  let b := Source284RestoredPolynomialRunway.countPolynomial k+1
  Source284CheckpointMarkedGuard.costPolynomial k r+6*b*b+70*b+114

theorem cost_polynomial (k r : Nat) (input witness : List Bool) (certificate : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    totalCost k r input witness ≤ (costPolynomial k r).eval input.length := by
  have hw := Source284TaggedWitnessCodec.decode_length
    (Source284DynamicGuardSource.bound k input.length) certificate witness hdec
  have hb : Source284DynamicGuardSource.bound k input.length ≤
      Source284GapUnarySource.gap k input.length := Nat.div_le_self _ _
  have hsquare := Nat.mul_self_le_mul_self (le_trans hw hb)
  have hinit := Source284CheckpointMarkedGuard.cost_polynomial k r input
  unfold totalCost
  rw [Source284DynamicGuardReveal.revealCost_formula]
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_one,Source284RestoredPolynomialRunway.countPolynomial_eval]
  simp only [Source284GapUnarySource.gap] at hb hsquare
  nlinarith

end Shared.Beeping.NPcoNP.Source284CheckpointMarkedReveal
