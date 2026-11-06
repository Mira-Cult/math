import Shared.Beeping.NPcoNP.Source284DynamicGuardSource
import Shared.Beeping.NPcoNP.Source284OffsetRevealInput

/-! After the dynamic guard accepts a tagged witness, reveal both the
protected witness frame and the original flipped input stream. One paid
transition removes the known odd-gap marker. Packing these two components
for the canonical verifier remains a separate implementation obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284DynamicGuardReveal

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)

def markerTable (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨b,false,some 1⟩ else shiftRow 1 (continuation (q-1) b)

theorem marker_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (1+states) (markerTable continuation) := by
  intro q hq b q' hnext
  by_cases h : q=0
  · subst q; simp [markerTable] at hnext; omega
  · have he : (shiftRow 1 (continuation (q-1) b)).next = some q' := by
      simpa [markerTable,h] using hnext
    cases ht : (continuation (q-1) b).next with
    | none => simp [shiftRow,ht] at he
    | some r =>
      have hr := hv (q-1) (by omega) b r ht
      simp [shiftRow,ht] at he
      subst q'
      omega

theorem marker_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    markerTable continuation (1+q) b = shiftRow 1 (continuation q b) := by simp [markerTable]

theorem marker_relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (markerTable continuation) (shiftConfig 1 c) = shiftConfig 1 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,marker_row,shiftRow]
      split <;> rfl

theorem marker_relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (markerTable continuation) (shiftConfig 1 c) fuel = shiftConfig 1 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,marker_relocated_step]

theorem marker_then (continuation : Nat → Bool → Row) (left stream fuel : Nat) :
    run (markerTable continuation) ⟨left,2*stream+1,some 0⟩ (1+fuel) =
      shiftConfig 1 (run continuation ⟨2*left+1,stream,some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add]
  change run (markerTable continuation)
    (step (markerTable continuation) ⟨left,2*stream+1,some 0⟩) fuel = _
  have hs : step (markerTable continuation) ⟨left,2*stream+1,some 0⟩ =
      ⟨2*left+1,stream,some 1⟩ := by
    simp [step,markerTable,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  rw [hs]
  change run (markerTable continuation) (shiftConfig 1 ⟨2*left+1,stream,some 0⟩) fuel = _
  exact marker_relocated_run continuation _ fuel

theorem encoded_marker_then (states : Nat) (continuation : Nat → Bool → Row)
    (left stream fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (1+states) (markerTable continuation) 1)
      ⟨left,2*stream+1,active 0⟩ (1+fuel) =
    lift 1 (Source284Relative.run (encode states continuation 1)
      ⟨2*left+1,stream,active 0⟩ fuel) := by
  let c : Config := ⟨left,2*stream+1,some 0⟩
  let d : Config := ⟨2*left+1,stream,some 0⟩
  have hc : Valid (1+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hd : Valid states d := by intro q hq; simp [d] at hq; subst q; exact hn
  have hr := run_toSource (1+states) (markerTable continuation) 1 c (marker_closed states continuation hn hv) hc (1+fuel)
  have hd' := run_toSource states continuation 1 d hv hd fuel
  change Source284Relative.run (encode (1+states) (markerTable continuation) 1)
    ⟨left,2*stream+1,active 0⟩ (1+fuel) = _ at hr
  change Source284Relative.run (encode states continuation 1)
    ⟨2*left+1,stream,active 0⟩ fuel = _ at hd'
  rw [hr,marker_then,← lift_toSource,← hd']

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284OffsetFrameAdapter.table (Source284OffsetRevealInput.table (markerTable continuation))

def states (n : Nat) : Nat := 19+(80+(7+(1+n)))

def description (k n : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DynamicGuardSource.description k (states n) (table continuation)

theorem table_closed (n : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < n) (hv : Closed n continuation) : Closed (states n) (table continuation) := by
  have hm := marker_closed n continuation hn hv
  have hr := Source284OffsetRevealInput.closed (1+n) (markerTable continuation) (by omega) hm
  exact Source284OffsetFrameAdapter.closed (7+(1+n))
    (Source284OffsetRevealInput.table (markerTable continuation)) (by omega) hr

def revealCost (limit : Nat) (witness : List Bool) : Nat :=
  4+(Source284PayloadSentinelPipeline.totalCost witness.length+
    (Source284OffsetMatch.compareCost witness.length+(1+
      ((1+((4*(limit+1)+6)+(4*witness.length+12)))+
        (10*witness.length+21+((3+(2*(limit+1)+3))+1))))))

theorem revealCost_formula (limit : Nat) (witness : List Bool) :
    revealCost limit witness =
      6*witness.length*witness.length+64*witness.length+6*limit+114 := by
  simp [revealCost,Source284PayloadSentinelPipeline.totalCost_formula,Source284OffsetMatch.compareCost]
  ring

noncomputable def revealPolynomial (k : Nat) : Polynomial Nat :=
  let b := Source284RestoredPolynomialRunway.countPolynomial k+1
  Source284GapUnarySource.costPolynomial k+6*b*b+70*b+114

/-- Initialization, witness guard and both-frame reveal are all bounded by
one fixed polynomial in the parsed input length. -/
theorem reveal_polynomial (k : Nat) (input witness : List Bool) (certificate : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    Source284GapUnarySource.totalCost k input+
      revealCost (Source284DynamicGuardSource.bound k input.length) witness ≤
        (revealPolynomial k).eval input.length := by
  have hw := Source284TaggedWitnessCodec.decode_length
    (Source284DynamicGuardSource.bound k input.length) certificate witness hdec
  have hb : Source284DynamicGuardSource.bound k input.length ≤
      Source284GapUnarySource.gap k input.length := Nat.div_le_self _ _
  have hsquare := Nat.mul_self_le_mul_self (le_trans hw hb)
  have hinit := Source284GapUnarySource.cost_polynomial k input
  rw [revealCost_formula]
  simp only [revealPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_one,Source284RestoredPolynomialRunway.countPolynomial_eval]
  simp only [Source284GapUnarySource.gap] at hb hsquare
  nlinarith

/-- The saved tape half exposes a frame for the decoded witness after the
known displacement is undone. Its displayed suffix reflects the guard's
earlier handling of the original certificate suffix. -/
theorem saved_witness_recover (limit : Nat) (witness : List Bool) (witnessSuffix : Nat) :
    let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
    let saved := 4*(4^(limit+1)*(2*wf))+1
    ((2*saved+1)/2)/4^(limit+2)/2 = wf := by
  dsimp only
  let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
  let saved := 4*(4^(limit+1)*(2*wf))+1
  have hhalf : (2*saved+1)/2=saved := by omega
  have hrec : saved/4^(limit+2)=2*wf := by
    have h := Source284OffsetRevealInput.reveal_frame_recover (limit+1) wf
    simpa [saved,show limit+1+1=limit+2 by omega] using h
  change ((2*saved+1)/2)/4^(limit+2)/2 = wf
  rw [hhalf,hrec]
  omega

/-- The successful dynamic guard reaches the supplied continuation with
a decoded witness frame recoverably saved and the parsed input's flipped
stream exposed with its retained suffix. Every source transition, including
marker removal, is paid. -/
theorem decoded_reveal (k n : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (certificate inputSuffix : Nat) (hn : 0 < n) (hv : Closed n continuation)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate=4*encodeFrame witness witnessSuffix ∧ ∀ fuel,
      let limit := Source284DynamicGuardSource.bound k input.length
      let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
      let saved := 4*(4^(limit+1)*(2*wf))+1
      Source284Relative.run (description k n continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (Source284GapUnarySource.totalCost k input+(revealCost limit witness+fuel)) =
      lift (707+317*k+318+1) (Source284Relative.run (encode n continuation 1)
        ⟨2*saved+1,Source284GapUnarySource.stream k input inputSuffix,active 0⟩ fuel) := by
  let limit := Source284DynamicGuardSource.bound k input.length
  let inputData := Source284DynamicGuardSource.otherHalf k input inputSuffix
  have hm := marker_closed n continuation hn hv
  obtain ⟨witnessSuffix,hcert,hreveal⟩ := Source284OffsetRevealInput.decoded_reveal_then
    (1+n) (markerTable continuation) limit certificate inputData witness (by omega) hm hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
  let saved := 4*(4^(limit+1)*(2*wf))+1
  have hinput : inputData = 2*Source284GapUnarySource.stream k input inputSuffix+1 :=
    Source284DynamicGuardSource.otherHalf_shape k input inputSuffix
  have ht := hreveal (1+fuel)
  change Source284Relative.run (Source284OffsetTagged.description (states n) (table continuation))
    (Source284Relative.initial certificate _) _ =
      lift 318 (Source284Relative.run (encode (1+n) (markerTable continuation) 1)
        ⟨saved,inputData,active 0⟩ (1+fuel)) at ht
  rw [hinput,encoded_marker_then n continuation saved (Source284GapUnarySource.stream k input inputSuffix)
    fuel hn hv,Source284SourceRelocation.lift_add] at ht
  have hs := Source284DynamicGuardSource.source_after k (states n) (table continuation)
    input certificate inputSuffix (revealCost limit witness+fuel) (by simp [states])
    (table_closed n continuation hn hv)
  change Source284Relative.run (description k n continuation)
    (Source284Relative.initial (encodeFrame input inputSuffix) certificate) _ =
      lift (707+317*k) (Source284Relative.run (Source284OffsetTagged.description (states n) (table continuation))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) inputData))
        (revealCost limit witness+fuel)) at hs
  have htime : revealCost limit witness+fuel =
      4+(Source284PayloadSentinelPipeline.totalCost witness.length+
        (Source284OffsetMatch.compareCost witness.length+(1+
          ((1+((4*(limit+1)+6)+(4*witness.length+12)))+
            (10*witness.length+21+((3+(2*(limit+1)+3))+(1+fuel))))))) := by
    simp [revealCost]; omega
  rw [hinput,htime,ht,Source284SourceRelocation.lift_add] at hs
  rw [← htime] at hs
  simpa [limit,wf,saved,Nat.add_assoc] using hs

end Shared.Beeping.NPcoNP.Source284DynamicGuardReveal
