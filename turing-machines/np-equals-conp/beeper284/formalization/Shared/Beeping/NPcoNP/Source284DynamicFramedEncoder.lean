import Shared.Beeping.NPcoNP.Source284DynamicInputRunway
import Shared.Beeping.NPcoNP.Source284PolynomialFramedEncoder
import Shared.Beeping.NPcoNP.Source284VerifierPolynomialBudget

/-! Feed the actual dynamic-cutoff source program into the existing finite
serializer and verifier encoder. Both input and witness workspace fits are
explicit hypotheses. This does not yet prove those fits uniformly, enforce
the original smaller witness cutoff, or refine the physical 284-state table. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284DynamicFramedEncoder

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
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
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block)
open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)

def sourceDescription {width : Nat} (enc : Codec width) (next : Program) (k : Nat) :=
  Source284DynamicInputRunway.description k (states enc next) (table enc next)

def sourceTime {width : Nat} (enc : Codec width) (k : Nat) (x w : List Bool) (fuel : Nat) :=
  Source284DynamicInputRunway.cost k x w+serialTime enc x w fuel

def inputList (k : Nat) (input : List Bool) (suffix : Nat) :=
  Source284PolynomialFramedEncoder.inputList k input suffix

theorem input_tail_eq (k : Nat) (input : List Bool) (suffix : Nat) :
    Source284DynamicInputFrame.tail k input suffix =
      Source284PolynomialJoinedInput.inputTail k input.length suffix := by rfl

theorem input_left (k : Nat) (input : List Bool) (suffix : Nat) :
    stack [false] (value (inputList k input suffix)) =
      8*Source284DynamicInputFrame.tail k input suffix := by
  rw [input_tail_eq]
  exact Source284PolynomialFramedEncoder.input_left k input suffix

theorem input_suffix_zero (k : Nat) (input : List Bool) (suffix depth : Nat)
    (hfit : depth ≤ block k input.length) :
    2^depth ∣ value (inputList k input suffix).tail :=
  Source284PolynomialFramedEncoder.input_suffix_zero k input suffix depth hfit

/-- A single stage count can simultaneously dominate the original witness
cutoff and any two fixed polynomial workspace demands. The demands must be
bounded independently of the chosen stage count. -/
theorem uniform_workspace (cutoff inputDemand witnessDemand : Polynomial Nat) :
    ∃ k : Nat, ∀ n : Nat,
      cutoff.eval n ≤ Source284DynamicGuardSource.bound k n ∧
      inputDemand.eval n ≤ block k n ∧
      witnessDemand.eval n ≤ 2*((Source284DynamicGuardSource.bound k n+1)+1) := by
  obtain ⟨k,hk⟩ := Source284PositivePolynomialRunway.block_dominates
    (inputDemand+witnessDemand+2*cutoff+4)
  refine ⟨k,?_⟩
  intro n
  have hg := Source284GapUnarySource.gap_odd k n
  have hc : block k n ≤ Source284PolynomialMarkedCleanup.count k n+3 := by
    simp only [Source284PolynomialMarkedCleanup.count,Source284PolynomialRunwayCleanup.zeros]; omega
  have hd := hk n
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat] at hd
  dsimp [Source284DynamicGuardSource.bound,Source284GapUnarySource.gap] at hg ⊢
  omega

theorem witness_tail_zero (limit suffix depth : Nat)
    (hfit : depth ≤ 2*((limit+1)+1)) :
    2^depth ∣ Source284DynamicJoinedInput.witnessTail limit suffix := by
  unfold Source284DynamicJoinedInput.witnessTail
  exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hfit) _

/-- The retained witness tail has the finite blank window needed by the
serializer whenever its explicit demand fits the dynamic guard bound. -/
theorem serializer_seed_agree (limit suffix skip depth : Nat)
    (hfit : skip+depth ≤ 2*((limit+1)+1)) :
    Agree depth (2*((2*Source284DynamicJoinedInput.witnessTail limit suffix)/2^(skip+1))) 0 := by
  have hall := witness_tail_zero limit suffix (skip+depth) hfit
  have hpref : 2^skip ∣ Source284DynamicJoinedInput.witnessTail limit suffix :=
    dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hall
  have hd : 2^depth ∣ Source284DynamicJoinedInput.witnessTail limit suffix/2^skip := by
    apply (Nat.dvd_div_iff_mul_dvd hpref).2
    simpa [pow_add,Nat.mul_comm] using hall
  have he (t : Nat) : 2*t/2^(skip+1)=t/2^skip := by
    rw [pow_succ,Nat.mul_comm (2^skip) 2,Nat.mul_div_mul_left _ _ (by decide)]
  rw [he]
  have hm : 2^depth ∣ 2*(Source284DynamicJoinedInput.witnessTail limit suffix/2^skip) :=
    dvd_mul_of_dvd_right hd 2
  simp [Agree,Nat.mod_eq_zero_of_dvd hm]

/-- The same concrete source table first checks the dynamic witness cutoff,
then executes the existing finite serializer up to an arbitrary continuing
verifier window. Both exact suffixes and the source clock are retained. -/
theorem source_continue_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k : Nat) (x w : List Bool) (certificate inputSuffix radius fuel : Nat)
    (last : Shared.Codes.FinitePrograms.Config)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate = some w)
    (hnext : run next (0,Source284UntagOutputWindow.outputTape (out enc x w)
      (inputList k x inputSuffix).tail (processed (remaining x w) false).length) fuel = some (.inr last))
    (hfit : (word enc).length+(radius+serialClock enc x w fuel) ≤
      2*((Source284DynamicGuardSource.bound k x.length+1)+1)) :
    ∃ witnessSuffix rev, certificate=4*encodeFrame w witnessSuffix ∧
      Window radius
        (Source284Relative.run (sourceDescription enc next k)
          (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k x w fuel))
        (lift (707+317*k+318+1+139+254+6) (target enc next last rev)) := by
  let L := inputList k x inputSuffix
  let limit := Source284DynamicGuardSource.bound k x.length
  let t := serialTime enc x w fuel
  obtain ⟨witnessSuffix,hcert,hjoined⟩ := Source284DynamicInputRunway.decoded_then
    k (states enc next) (table enc next) x w certificate inputSuffix (states_pos enc next)
    (closed enc next hn) hdec
  let tail := Source284DynamicJoinedInput.witnessTail limit witnessSuffix
  have hb := body_reverse x w
  have hblank := serializer_seed_agree limit witnessSuffix (word enc).length (radius+serialClock enc x w fuel) hfit
  obtain ⟨rev,hw⟩ := Source284SerializerContinuePipeline.scan_seed_serializer_continue enc x w (rest x w)
    L false tail radius hb next hn fuel last hnext hblank
  let c : Config := ⟨8*Source284DynamicInputFrame.tail k x inputSuffix,
    stack (Source284JoinedFrames.joinedBits x w) tail,some 0⟩
  have hc : Valid (states enc next) c := by intro q hq; simp [c] at hq; subst q; exact states_pos enc next
  have hrun := run_toSource (states enc next) (table enc next) 1 c (closed enc next hn) hc t
  have hleft : stack [false] (value L) = 8*Source284DynamicInputFrame.tail k x inputSuffix :=
    input_left k x inputSuffix
  rw [hleft] at hw
  change Window radius (Source284Relative.run (encode (states enc next) (table enc next) 1) (toSource c) t)
    (target enc next last rev) at hw
  have hl := Source284SerializerStripWindow.lift_window radius (707+317*k+318+1+139+254+6) _ _ hw
  have hs := hjoined t
  change Source284Relative.run (sourceDescription enc next k)
      (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k x w fuel) =
    lift (707+317*k+318+1+139+254+6)
      (Source284Relative.run (encode (states enc next) (table enc next) 1) (toSource c) t) at hs
  rw [← hs] at hl
  exact ⟨witnessSuffix,rev,hcert,hl⟩

/-- An independently supplied canonical encoder run is reflected through
the dynamically guarded source program when both workspace demands fit. -/
theorem source_encoder_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k : Nat) (x w : List Bool) (certificate inputSuffix radiusSource radiusEncoder fuel q : Nat)
    (reference : Tape)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate = some w)
    (hrun : run next (initial (inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w))) fuel = some (.inr (q,reference)))
    (hinputFit : radiusEncoder+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w)).length+3) ≤ block k x.length)
    (hwitnessFit : (word enc).length+(radiusSource+serialClock enc x w fuel) ≤
      2*((Source284DynamicGuardSource.bound k x.length+1)+1)) :
    ∃ witnessSuffix actualTape rev revSource, certificate=4*encodeFrame w witnessSuffix ∧
      Window radiusEncoder (represented actualTape rev (codeState q rev))
        (represented reference rev (codeState q rev)) ∧
      Window radiusSource
        (Source284Relative.run (sourceDescription enc next k)
          (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k x w fuel))
        (lift (707+317*k+318+1+139+254+6) (target enc next (q,actualTape) revSource)) := by
  let L := inputList k x inputSuffix
  have hpad := input_suffix_zero k x inputSuffix _ hinputFit
  obtain ⟨actualTape,rev,hnext,henc⟩ := Source284SerializerEncoderSuffix.joined_output_live
    enc x w (rest x w) false L.tail (body_reverse x w) next hn fuel radiusEncoder q reference hrun hpad
  obtain ⟨witnessSuffix,revSource,hcert,hsource⟩ := source_continue_window enc next hn k x w
    certificate inputSuffix radiusSource fuel (q,actualTape) hdec hnext hwitnessFit
  exact ⟨witnessSuffix,actualTape,rev,revSource,hcert,henc,hsource⟩

/-- The same encoded program rejects every certificate outside the dynamic
guard, independent of any serializer workspace hypotheses. -/
theorem rejected_raw_never_accepts {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k input certificate : Nat)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (sourceDescription enc next k) input certificate clock = false :=
  Source284DynamicInputRunway.rejected_raw_never_accepts k (states enc next) (table enc next)
    input certificate (states_pos enc next) (closed enc next hn) hbad

noncomputable def clockPolynomial {width : Nat} (k : Nat) (enc : Codec width)
    (witnessBound fuelBound : Polynomial Nat) : Polynomial Nat :=
  Source284DynamicInputRunway.costPolynomial k+
    (2*(Polynomial.X+witnessBound)+6)+Polynomial.C (seedCost enc)+
    (Source284VerifierPolynomialBudget.serializerPolynomial width).comp (Polynomial.X+witnessBound)+fuelBound+3

/-- An explicit polynomial charges the guarded preparation, joined-prefix
serialization, finite verifier fuel, and one terminal transition. -/
theorem sourceTime_polynomial {width : Nat} (enc : Codec width) (k : Nat)
    (witnessBound fuelBound : Polynomial Nat) (x w : List Bool) (certificate fuel : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate = some w)
    (hw : w.length ≤ witnessBound.eval x.length) (hf : fuel ≤ fuelBound.eval x.length) :
    sourceTime enc k x w fuel+1 ≤ (clockPolynomial k enc witnessBound fuelBound).eval x.length := by
  have hj := Source284DynamicInputRunway.cost_polynomial k x w certificate hdec
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

end Shared.Beeping.NPcoNP.Source284DynamicFramedEncoder
