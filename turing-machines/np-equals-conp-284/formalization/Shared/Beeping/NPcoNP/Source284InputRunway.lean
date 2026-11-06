import Shared.Beeping.NPcoNP.Source284InputRunwayClear
import Shared.Beeping.NPcoNP.Source284FramedEncoderTable
import Shared.Beeping.NPcoNP.Source284UntagSuffixWindow

/-! A source-bound input-side zero runway for the serialized encoder. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284InputRunway

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificateJoin (witnessTail)
open Shared.Beeping.NPcoNP.Source284JoinedReframe (inputTail)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Codes.BitNumeralCompare (value)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284FramedJoin.table (Source284InputRunwayClear.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (452+states) (table continuation) := by
  have h := Source284FramedJoin.closed (6+states) (Source284InputRunwayClear.table continuation)
    (by omega) (Source284InputRunwayClear.closed states continuation hn hv)
  change Closed (446+(6+states)) (table continuation) at h
  convert h using 1 <;> omega

def description (k states : Nat) (continuation : Nat → Bool → Row) :=
  Source284FramedJoin.description k (6+states) (Source284InputRunwayClear.table continuation)

def preparationTime (k : Nat) (input witness : List Bool) :=
  Source284FramedJoin.totalCost k input witness+6

/-- Every raw framed input and tagged witness reaches the existing joined
prefix with the input-side marker cleared in six extra source steps. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (witnessSuffix inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame input inputSuffix) (4*encodeFrame witness witnessSuffix))
      (preparationTime k input witness+fuel) =
    toSource (shiftConfig (1292+220*k) (run continuation
      ⟨8*inputTail k input inputSuffix,
        stack (Source284JoinedFrames.joinedBits input witness)
          (witnessTail (firstZeros k input.length) input.length witnessSuffix/2),some 0⟩ fuel)) := by
  have hp := Source284FramedJoin.source_joined_then k (6+states) (Source284InputRunwayClear.table continuation)
    input witness witnessSuffix inputSuffix (6+fuel) (by omega) (Source284InputRunwayClear.closed states continuation hn hv)
  have ht : preparationTime k input witness+fuel = Source284FramedJoin.totalCost k input witness+(6+fuel) := by
    simp [preparationTime]; omega
  rw [ht]
  change Source284Relative.run (Source284FramedJoin.description k (6+states)
    (Source284InputRunwayClear.table continuation)) _ _ = _
  rw [hp,Source284InputRunwayClear.clear_then,Source284SourceRelocation.shiftConfig_add]
  have he : 1286+220*k+6=1292+220*k := by omega
  rw [he]

def inputList (k : Nat) (input : List Bool) (suffix : Nat) := (4*inputTail k input suffix).bits

theorem input_left (k : Nat) (input : List Bool) (suffix : Nat) :
    stack [false] (value (inputList k input suffix)) = 8*inputTail k input suffix := by
  change 2*value ((4*inputTail k input suffix).bits) = _
  rw [Shared.Codes.BinaryAdditionCanonical.value_bits]
  ring

theorem input_suffix_value (k : Nat) (input : List Bool) (suffix : Nat) :
    value (inputList k input suffix).tail = 2*inputTail k input suffix := by
  unfold inputList
  rw [← Nat.div2_bits_eq_tail,Shared.Codes.BinaryAdditionCanonical.value_bits]
  simp [Nat.div2_val] <;> omega

/-- The bit-value of the actual retained input suffix has a paid quadratic
zero prefix, independently of all bits of the original input suffix. -/
theorem input_suffix_zero (k : Nat) (input : List Bool) (suffix depth : Nat)
    (hfit : depth ≤ k*(input.length*input.length)+2) :
    2^depth ∣ value (inputList k input suffix).tail := by
  rw [input_suffix_value]
  have hpow : 2^depth ∣ 2^(k*(input.length*input.length)+2) := Nat.pow_dvd_pow 2 hfit
  have he : 2*inputTail k input suffix =
      2^(k*(input.length*input.length)+2)*Source284TwoSidedScaledQuadratic.finalTail k input.length suffix := by
    unfold inputTail
    rw [show k*(input.length*input.length)+2 = (k*(input.length*input.length)+1)+1 by omega,pow_succ]
    ring
  rw [he]
  exact dvd_mul_of_dvd_left hpow _

end Shared.Beeping.NPcoNP.Source284InputRunway
