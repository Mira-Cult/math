import Shared.Beeping.NPcoNP.Source284HardwireOverwrite
import Shared.Beeping.NPcoNP.Source284EncoderSourceWindow

/-! A paid finite source-table prefix writes the fixed first codeword of the
joined encoder's serialized input. It preserves the raw joined body on the
opposite tape half while overwriting only a bounded number of old suffix
cells. The remaining input-dependent codewords and the required zero window
are not yet constructed. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed

open Turing Shared.ComplexityBridge Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2BinaryPostCosts (Alphabet)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig offset)
open Shared.Beeping.NPcoNP.Source284HardwireCorrect (run_add)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284JoinedFrames (joinedBits)
open Shared.Beeping.NPcoNP.Source284JoinedRawEncodeTM2 (machine)

/-- One initial turn, followed by the existing hardwired-word table. -/
def table (word : List Bool) (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else shiftRow 1 (Source284HardwireTable.table word continuation (q-1) b)

theorem closed (word : List Bool) (continuation : Nat → Bool → Row) (states : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (1+(offset word+states)) (table word continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · have hc := Source284HardwireTable.closed word continuation states hn hv
    have hq0 : q-1 < offset word+states := by omega
    have ht : (shiftRow 1 (Source284HardwireTable.table word continuation (q-1) b)).next = some q' := by
      simpa [table,h0] using hnext
    cases he : (Source284HardwireTable.table word continuation (q-1) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hc (q-1) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem turn (word : List Bool) (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table word continuation) ⟨left,right,some 0⟩ = ⟨right,left,some 1⟩ := by
  simp [step,table,Source284HardwireTable.bit_decide_mod]
  omega

theorem relocated_step (word : List Bool) (continuation : Nat → Bool → Row) (c : Config) :
    step (table word continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284HardwireTable.table word continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,table,show 1+q ≠ 0 by omega,
        ↓reduceIte,show 1+q-1=q by omega,shiftRow]
      split <;> rfl

theorem relocated_run (word : List Bool) (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table word continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284HardwireTable.table word continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem shift_add (a b : Nat) (c : Config) :
    shiftConfig a (shiftConfig b c) = shiftConfig (a+b) c := by
  cases c with
  | mk left right state => cases state <;> simp [shiftConfig,Nat.add_assoc]

/-- The actual finite table seeds the fixed word over arbitrary target cells,
then runs every subsequent continuation step. -/
theorem seed_then (word : List Bool) (continuation : Nat → Bool → Row)
    (left right fuel : Nat) :
    run (table word continuation) ⟨left,right,some 0⟩ (1+offset word+fuel) =
      shiftConfig (1+offset word) (run continuation
        ⟨right,stack word (2*(left/2^(word.length+1))),some 0⟩ fuel) := by
  rw [show 1+offset word+fuel = (offset word+fuel)+1 by omega,
    Source284HardwireTable.run_front,turn]
  change run (table word continuation) (shiftConfig 1 ⟨right,left,some 0⟩) _ = _
  rw [relocated_run,Source284HardwireOverwrite.overwrite_then,shift_add]

/-- Run the joined-prefix scanner and then write the known first serialized
codeword. The body remains available in its exact reverse order. -/
theorem scan_and_seed (word : List Bool) (continuation : Nat → Bool → Row)
    (x w : List Bool) (left tail fuel : Nat) :
    run (Source284JoinedPrefixScan.table (table word continuation))
      ⟨left,stack (joinedBits x w) tail,some 0⟩
      ((joinedBits x w).length+(1+offset word+fuel)) =
    shiftConfig (7+(1+offset word)) (run continuation
      ⟨stack (Source284JoinedPrefixScan.joinedBody x w).reverse left,
        stack word (2*((2*tail)/2^(word.length+1))),some 0⟩ fuel) := by
  rw [Source284JoinedPrefixScan.scan_then]
  rw [Source284LoaderAlgebra.pushed_eq_stack,seed_then,shift_add]

/-- The real decoded source path reaches the seeded-word boundary and then
follows the continuation for every later clock. Every suffix value is kept
explicit in the resulting configuration. -/
theorem decoded_scan_and_seed (word : List Bool) (states : Nat)
    (continuation : Nat → Bool → Row) (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*Source284Parser.encodeFrame w witnessSuffix ∧
      input = Source284Parser.encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description
          (19+(80+(7+(210+(10+(160+(68+(16+(7+(1+(offset word+states)))))))))))
          (Source284BothFrames.table (Source284WitnessSeek.table
            (Source284WitnessCompact.table (Source284ScratchNormalize.table
              (Source284JoinedFrames.table (Source284JoinedPrefixScan.table (table word continuation))))))))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+
          ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
            (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
              ((2*(Source284RawParse.payload input.bits).length+6)+
                ((joinedBits (Source284RawParse.payload input.bits) w).length+
                  (1+offset word+fuel))))))) =
      Source284SourceRelocation.lift (789+(1+offset word))
        (Source284Relative.run (encode states continuation 1)
          ⟨stack (Source284JoinedPrefixScan.joinedBody (Source284RawParse.payload input.bits) w).reverse
              (2*(inputSuffix/4)+1),
            stack word (2*((2*(2^(2*((limit+1)+1))*((8*((witnessSuffix/4)/4)+1)/4))) /
              2^(word.length+1))),active 0⟩ fuel) := by
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284JoinedPrefixScan.decoded_scan_then
    (1+(offset word+states)) (table word continuation) limit certificate input w (by omega)
      (closed word continuation states hn hv) hdec
  refine ⟨ws,is,hcert,hinput,?_⟩
  intro fuel
  let x := Source284RawParse.payload input.bits
  let left := 2*(is/4)+1
  let tail := 2^(2*((limit+1)+1))*((8*((ws/4)/4)+1)/4)
  let t := 1+offset word
  have hr' := hr (t+fuel)
  let c : Config := ⟨2*tail,Source284Parser.payloadFold left (Source284JoinedPrefixScan.joinedBody x w),some 0⟩
  have hc : Valid (1+(offset word+states)) c := by
    intro q hq; simp [c] at hq; subst q; omega
  have hv0 := run_toSource (1+(offset word+states)) (table word continuation) 1 c
    (closed word continuation states hn hv) hc (t+fuel)
  change Source284Relative.run (encode (1+(offset word+states)) (table word continuation) 1)
    ⟨2*tail,Source284Parser.payloadFold left (Source284JoinedPrefixScan.joinedBody x w),active 0⟩
      (t+fuel) = _ at hv0
  have hp := seed_then word continuation (2*tail)
    (Source284Parser.payloadFold left (Source284JoinedPrefixScan.joinedBody x w)) fuel
  change run (table word continuation) c (t+fuel) = _ at hp
  rw [hv0,hp,Source284LoaderAlgebra.pushed_eq_stack] at hr'
  let c' : Config := ⟨stack (Source284JoinedPrefixScan.joinedBody x w).reverse left,
    stack word (2*((2*tail)/2^(word.length+1))),some 0⟩
  have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hv1 := run_toSource states continuation 1 c' hv hc' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨stack (Source284JoinedPrefixScan.joinedBody x w).reverse left,
      stack word (2*((2*tail)/2^(word.length+1))),active 0⟩ fuel = _ at hv1
  rw [← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

/-- The first serialized codeword is fixed once the finite alphabet codec is
chosen; it is independent of both payloads and all tape suffixes. -/
def marker {width : Nat} (enc : Alphabet machine → List.Vector Bool width) : List Bool :=
  (enc (true, Function.update (fun _ => none) machine.k₀ (some true))).toList

theorem marker_length {width : Nat} (enc : Alphabet machine → List.Vector Bool width) :
    (marker enc).length = width := by simp [marker]

/-- The marker is exactly the leading codeword of the TM2 serialization. -/
theorem marker_is_serialized_prefix {width : Nat}
    (enc : Alphabet machine → List.Vector Bool width) (x w : List Bool) :
    Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits machine enc (joinedBits x w) =
      marker enc ++ (Source284JoinedPrefixScan.joinedBody x w).reverse.flatMap
        (fun b => (enc (false,Function.update (fun _ => none) machine.k₀ (some b))).toList) := by
  simpa [marker] using Source284EncoderSourceWindow.serialized_input_shape enc x w

/-- The additional seed consists of one turn and the exact fixed-word
outward/return pass, so its cost is fixed once the codec is fixed. -/
theorem marker_seed_cost {width : Nat} (enc : Alphabet machine → List.Vector Bool width) :
    1+offset (marker enc) = 2*width+3 := by
  simp [offset,marker_length]
  omega

theorem decoded_seed_bound (word : List Bool) (limit certificate input : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    Source284BothFrames.time limit w input+
      ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
        (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
          ((2*(Source284RawParse.payload input.bits).length+6)+
            ((joinedBits (Source284RawParse.payload input.bits) w).length+(1+offset word)))))) ≤
      24*limit*limit+156*limit+
        2*Source284Parser.length input*Source284Parser.length input+
        32*Source284Parser.length input+252+(1+offset word) := by
  have h := Source284JoinedPrefixScan.decoded_scan_bound limit certificate input w hdec
  omega

namespace Fixtures
example :
    run (table [true,false,true] (fun _ b => ⟨b,false,some 0⟩)) ⟨255,19,some 0⟩ 9 =
      ⟨19,245,some 9⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed
