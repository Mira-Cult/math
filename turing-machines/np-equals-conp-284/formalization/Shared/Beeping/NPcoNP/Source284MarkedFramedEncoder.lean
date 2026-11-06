import Shared.Beeping.NPcoNP.Source284MarkedInputRunway
import Shared.Beeping.NPcoNP.Source284DynamicFramedEncoder

/-! Connect the counter-transfer source path to the existing finite
serializer and encoded verifier windows. Both runway sizes are explicit. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedFramedEncoder

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable
open Shared.Beeping.NPcoNP.Source284FramedSerialize (rest body_reverse remaining out seedCost)
open Shared.Beeping.NPcoNP.Source284FramedEncoder (serialClock serialTime target)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift)
open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.FinitePrograms (Program Tape valid run initial)
open Shared.ComplexityBridge.TM2BinaryPostCosts (inputBits)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace (workspace)
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace (markCount blankTail)
open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)

def sourceDescription {width : Nat} (enc : Codec width) (next : Program) (k r : Nat) :=
  Source284MarkedInputRunway.description k r (states enc next) (table enc next)

def sourceTime {width : Nat} (enc : Codec width) (k r : Nat) (x w : List Bool) (fuel : Nat) :=
  Source284MarkedInputRunway.cost k r x w+serialTime enc x w fuel

def inputTail (k r : Nat) (input : List Bool) (suffix : Nat) := blankTail k r input.length suffix/2

def inputList (k r : Nat) (input : List Bool) (suffix : Nat) := (4*inputTail k r input suffix).bits

theorem input_left (k r : Nat) (input : List Bool) (suffix : Nat) :
    stack [false] (value (inputList k r input suffix)) = 8*inputTail k r input suffix := by
  change 2*value ((4*inputTail k r input suffix).bits) = _
  rw [Shared.Codes.BinaryAdditionCanonical.value_bits]
  ring

theorem input_suffix_zero (k r : Nat) (input : List Bool) (suffix depth : Nat)
    (hfit : depth ≤ workspace k r input.length) :
    2^depth ∣ value (inputList k r input suffix).tail := by
  unfold inputList
  rw [← Nat.div2_bits_eq_tail,Shared.Codes.BinaryAdditionCanonical.value_bits]
  have h := Source284MarkedJoinedInput.input_tail_zero k r input.length suffix depth hfit
  simp only [Nat.div2_val]
  have he : 4*inputTail k r input suffix/2 = 2*inputTail k r input suffix := by omega
  rw [he]
  exact dvd_mul_of_dvd_right h 2

theorem serializer_seed_agree (k r n suffix skip depth : Nat)
    (hfit : skip+depth ≤ markCount k r n-1) :
    Agree depth (2*((2*(Source284DynamicJoinedInput.witnessTail
      (Source284MarkedJoinedInput.enlargedLimit k r n) suffix))/2^(skip+1))) 0 := by
  let tail := Source284DynamicJoinedInput.witnessTail (Source284MarkedJoinedInput.enlargedLimit k r n) suffix
  have hall : 2^(skip+depth) ∣ tail := Source284MarkedJoinedInput.witness_tail_zero k r n suffix _ hfit
  have hpref : 2^skip ∣ tail := dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hall
  have hd : 2^depth ∣ tail/2^skip := by
    apply (Nat.dvd_div_iff_mul_dvd hpref).2
    simpa [pow_add,Nat.mul_comm] using hall
  have he (t : Nat) : 2*t/2^(skip+1)=t/2^skip := by
    rw [pow_succ,Nat.mul_comm (2^skip) 2,Nat.mul_div_mul_left _ _ (by decide)]
  change Agree depth (2*((2*tail)/2^(skip+1))) 0
  rw [he]
  have hm : 2^depth ∣ 2*(tail/2^skip) := dvd_mul_of_dvd_right hd 2
  simp [Agree,Nat.mod_eq_zero_of_dvd hm]

/-- Exact source-to-serializer window after the runtime counter transfer. -/
theorem source_continue_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k r : Nat) (x w : List Bool) (certificate inputSuffix radius fuel : Nat)
    (last : Shared.Codes.FinitePrograms.Config)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate = some w)
    (hnext : run next (0,Source284UntagOutputWindow.outputTape (out enc x w)
      (inputList k r x inputSuffix).tail (processed (remaining x w) false).length) fuel = some (.inr last))
    (hfit : (word enc).length+(radius+serialClock enc x w fuel) ≤ markCount k r x.length-1) :
    ∃ witnessSuffix rev, certificate=4*encodeFrame w witnessSuffix ∧
      Window radius
        (Source284Relative.run (sourceDescription enc next k r)
          (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel))
        (lift (1371+317*k+317*r+318+1+178+254+6) (target enc next last rev)) := by
  let L := inputList k r x inputSuffix
  let limit := Source284MarkedJoinedInput.enlargedLimit k r x.length
  let t := serialTime enc x w fuel
  obtain ⟨witnessSuffix,hcert,hjoined⟩ := Source284MarkedInputRunway.decoded_then
    k r (states enc next) (table enc next) x w certificate inputSuffix (states_pos enc next)
    (closed enc next hn) hdec
  let tail := Source284DynamicJoinedInput.witnessTail limit witnessSuffix
  have hb := body_reverse x w
  have hblank := serializer_seed_agree k r x.length witnessSuffix
    (word enc).length (radius+serialClock enc x w fuel) hfit
  obtain ⟨rev,hw⟩ := Source284SerializerContinuePipeline.scan_seed_serializer_continue enc x w (rest x w)
    L false tail radius hb next hn fuel last hnext hblank
  let c : Config := ⟨8*inputTail k r x inputSuffix,
    stack (Source284JoinedFrames.joinedBits x w) tail,some 0⟩
  have hc : Valid (states enc next) c := by intro q hq; simp [c] at hq; subst q; exact states_pos enc next
  have hrun := run_toSource (states enc next) (table enc next) 1 c (closed enc next hn) hc t
  have hleft : stack [false] (value L) = 8*inputTail k r x inputSuffix := input_left k r x inputSuffix
  rw [hleft] at hw
  change Window radius (Source284Relative.run (encode (states enc next) (table enc next) 1) (toSource c) t)
    (target enc next last rev) at hw
  have hl := Source284SerializerStripWindow.lift_window radius (1371+317*k+317*r+318+1+178+254+6) _ _ hw
  have hs := hjoined t
  change Source284Relative.run (sourceDescription enc next k r)
      (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel) =
    lift (1371+317*k+317*r+318+1+178+254+6)
      (Source284Relative.run (encode (states enc next) (table enc next) 1) (toSource c) t) at hs
  rw [← hs] at hl
  exact ⟨witnessSuffix,rev,hcert,hl⟩

/-- The canonical encoder run is reflected through the guarded finite
source table with explicit, independently produced workspace fits. -/
theorem source_encoder_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k r : Nat) (x w : List Bool) (certificate inputSuffix radiusSource radiusEncoder fuel q : Nat)
    (reference : Tape)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate = some w)
    (hrun : run next (initial (inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w))) fuel = some (.inr (q,reference)))
    (hinputFit : radiusEncoder+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w)).length+3) ≤ workspace k r x.length)
    (hwitnessFit : (word enc).length+(radiusSource+serialClock enc x w fuel) ≤ markCount k r x.length-1) :
    ∃ witnessSuffix actualTape rev revSource, certificate=4*encodeFrame w witnessSuffix ∧
      Window radiusEncoder (represented actualTape rev (codeState q rev))
        (represented reference rev (codeState q rev)) ∧
      Window radiusSource
        (Source284Relative.run (sourceDescription enc next k r)
          (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel))
        (lift (1371+317*k+317*r+318+1+178+254+6) (target enc next (q,actualTape) revSource)) := by
  let L := inputList k r x inputSuffix
  have hpad := input_suffix_zero k r x inputSuffix _ hinputFit
  obtain ⟨actualTape,rev,hnext,henc⟩ := Source284SerializerEncoderSuffix.joined_output_live
    enc x w (rest x w) false L.tail (body_reverse x w) next hn fuel radiusEncoder q reference hrun hpad
  obtain ⟨witnessSuffix,revSource,hcert,hsource⟩ := source_continue_window enc next hn k r x w
    certificate inputSuffix radiusSource fuel (q,actualTape) hdec hnext hwitnessFit
  exact ⟨witnessSuffix,actualTape,rev,revSource,hcert,henc,hsource⟩

theorem rejected_raw_never_accepts {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k r input certificate : Nat)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (sourceDescription enc next k r) input certificate clock = false :=
  Source284MarkedInputRunway.rejected_raw_never_accepts k r (states enc next) (table enc next)
    input certificate (states_pos enc next) (closed enc next hn) hbad

/-- After the guard stage count is chosen, one additional fixed stage count
simultaneously covers any two fixed polynomial serializer demands. -/
theorem uniform_workspace_for_k (k : Nat) (inputDemand witnessDemand : Polynomial Nat) :
    ∃ r : Nat, ∀ n : Nat,
      inputDemand.eval n ≤ workspace k r n ∧ witnessDemand.eval n ≤ markCount k r n-1 := by
  obtain ⟨r,hr⟩ := Source284CheckpointGrowth.workspace_dominates_guard (inputDemand+witnessDemand)
  refine ⟨r,?_⟩
  intro n
  have hseed := Source284ProductGrowth.inner_lower k 1
    (Source284CheckpointWorkspace.base n) (Source284CheckpointWorkspace.base n)
    (by omega) (by simp [Source284CheckpointWorkspace.base]) (by simp [Source284CheckpointWorkspace.base])
  simp only [one_pow,Nat.mul_one] at hseed
  change n+2 ≤ Source284CheckpointWorkspace.guard k n at hseed
  have hm := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono (inputDemand+witnessDemand)
    (show n ≤ Source284CheckpointWorkspace.guard k n by omega)
  have hs := hr k n
  simp only [Polynomial.eval_add] at hm hs
  have hc := Source284CheckpointMarkedBounds.mark_count_large k r n
  omega

noncomputable def clockPolynomial {width : Nat} (k r : Nat) (enc : Codec width)
    (witnessBound fuelBound : Polynomial Nat) : Polynomial Nat :=
  Source284MarkedInputRunway.costPolynomial k r+
    (2*(Polynomial.X+witnessBound)+6)+Polynomial.C (seedCost enc)+
    (Source284VerifierPolynomialBudget.serializerPolynomial width).comp (Polynomial.X+witnessBound)+fuelBound+3

theorem sourceTime_polynomial {width : Nat} (enc : Codec width) (k r : Nat)
    (witnessBound fuelBound : Polynomial Nat) (x w : List Bool) (certificate fuel : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate = some w)
    (hw : w.length ≤ witnessBound.eval x.length) (hf : fuel ≤ fuelBound.eval x.length) :
    sourceTime enc k r x w fuel+1 ≤ (clockPolynomial k r enc witnessBound fuelBound).eval x.length := by
  have hj := Source284MarkedInputRunway.cost_polynomial k r x w certificate hdec
  have hs := Source284VerifierPolynomialBudget.serializer_bound enc x w fuel
  have hsize : x.length+w.length ≤ x.length+witnessBound.eval x.length := by omega
  have hm := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono
    (Source284VerifierPolynomialBudget.serializerPolynomial width) hsize
  have hl : (Source284JoinedFrames.joinedBits x w).length ≤ 2*(x.length+witnessBound.eval x.length)+6 := by
    rw [Source284JoinedFrames.joined_length]; omega
  simp only [clockPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]
  simp only [sourceTime,Source284FramedEncoder.serialTime]
  omega

end Shared.Beeping.NPcoNP.Source284MarkedFramedEncoder
