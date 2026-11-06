import Shared.Beeping.NPcoNP.Source284SelectOverwrite

/-! After the fixed marker seed, a finite table consumes the known delimiter
and writes the first input-dependent codeword. The selected input bit remains
at the raw-body head; the later repeated serializer is not yet supplied. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284EncoderFirstSelection

open Turing Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig offset)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284JoinedRawEncodeTM2 (machine)
open Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed (marker shift_add)

def code {width : Nat} (enc : Alphabet machine → List.Vector Bool width) (b : Bool) : List Bool :=
  (enc (false,Function.update (fun _ => none) machine.k₀ (some b))).toList

def word {width : Nat} (enc : Alphabet machine → List.Vector Bool width) (b : Bool) : List Bool :=
  marker enc ++ code enc false ++ code enc b

theorem word_length {width : Nat} (enc : Alphabet machine → List.Vector Bool width) (b : Bool) :
    (word enc b).length = 3*width := by
  simp [word,code,Source284EncoderMarkerSeed.marker_length]
  omega

/-- Two paid setup states turn to the raw body and consume its first zero;
all following states are the finite bit-selector table. -/
def table (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else shiftRow 2 (Source284SelectOverwrite.table zero one states continuation (q-2) b)

theorem closed (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (2+Source284SelectOverwrite.total zero one states) (table zero one states continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext
    have ht : 0 < Source284SelectOverwrite.total zero one states := by
      simp [Source284SelectOverwrite.total,Source284SelectOverwrite.trueStart,
        Source284SelectOverwrite.falseSize,offset]
    omega
  · by_cases h1 : q = 1
    · subst q; simp [table] at hnext
      have ht : 0 < Source284SelectOverwrite.total zero one states := by
        simp [Source284SelectOverwrite.total,Source284SelectOverwrite.trueStart,
          Source284SelectOverwrite.falseSize,offset]
      omega
    · have hc := Source284SelectOverwrite.closed zero one states continuation hn hv
      have hq0 : q-2 < Source284SelectOverwrite.total zero one states := by omega
      have ht : (shiftRow 2 (Source284SelectOverwrite.table zero one states continuation (q-2) b)).next = some q' := by
        simpa [table,h0,h1] using hnext
      cases he : (Source284SelectOverwrite.table zero one states continuation (q-2) b).next with
      | none => simp [shiftRow,he] at ht
      | some r =>
        have h := hc (q-2) hq0 b r he
        simp [shiftRow,he] at ht
        subst q'; omega

theorem setup (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (encoded raw : Nat) :
    run (table zero one states continuation) ⟨2*raw,encoded,some 0⟩ 2 =
      ⟨2*encoded,raw,some 2⟩ := by
  simp [run,step,table,Nat.testBit_zero,bit] <;> split_ifs <;> omega

theorem relocated_step (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (c : Config) :
    step (table zero one states continuation) (shiftConfig 2 c) =
      shiftConfig 2 (step (Source284SelectOverwrite.table zero one states continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,table,show 2+q ≠ 0 by omega,
        show 2+q ≠ 1 by omega,↓reduceIte,show 2+q-2=q by omega,shiftRow]
      split <;> rfl

theorem relocated_run (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (c : Config) (fuel : Nat) :
    run (table zero one states continuation) (shiftConfig 2 c) fuel =
      shiftConfig 2 (run (Source284SelectOverwrite.table zero one states continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- The new table writes a word selected by the next body bit. It includes
both setup transitions, selector transition, and every fixed-word write and
return transition. The selected bit remains in the body. -/
theorem first_then (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation)
    (encoded tail fuel : Nat) (b : Bool) :
    let selected := if b then one else zero
    let start := if b then Source284SelectOverwrite.trueStart zero states else 1
    run (table zero one states continuation) ⟨2*(2*tail+bit b),encoded,some 0⟩
      (2+(1+offset selected+fuel)) =
    shiftConfig (2+(start+offset selected)) (run continuation
      ⟨2*tail+bit b,stack selected (2*((2*encoded)/2^(selected.length+1))),some 0⟩ fuel) := by
  dsimp only
  rw [Source284HardwireCorrect.run_add,setup]
  change run (table zero one states continuation)
    (shiftConfig 2 ⟨2*encoded,2*tail+bit b,some 0⟩) _ = _
  rw [relocated_run,Source284SelectOverwrite.select_then _ _ _ _ hn hv,shift_add]

/-- The first input-dependent write composes with the actual marker seed on
the same finite table. The prefix is rewritten as three fixed-width words;
the next raw bit is still available on the opposite half. -/
theorem seed_and_first {width : Nat} (enc : Alphabet machine → List.Vector Bool width)
    (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) (left tail fuel : Nat) (b : Bool) (rest : List Bool) :
    let seeded := stack (marker enc) (2*(left/2^((marker enc).length+1)))
    let start := if b then Source284SelectOverwrite.trueStart (word enc false) states else 1
    run (Source284EncoderMarkerSeed.table (marker enc)
        (table (word enc false) (word enc true) states continuation))
      ⟨left,stack (false::b::rest) tail,some 0⟩
      ((1+offset (marker enc))+(2+(1+offset (word enc b)+fuel))) =
    shiftConfig ((1+offset (marker enc))+(2+(start+offset (word enc b))))
      (run continuation ⟨stack (b::rest) tail,
        stack (word enc b) (2*((2*seeded)/2^((word enc b).length+1))),some 0⟩ fuel) := by
  dsimp only
  rw [Source284EncoderMarkerSeed.seed_then]
  have hs : stack (false::b::rest) tail = 2*(2*(stack rest tail)+bit b) := by
    simp [stack,bit]
  rw [hs]
  have hh := first_then (word enc false) (word enc true) states continuation hn hv
    (stack (marker enc) (2*(left/2^((marker enc).length+1)))) (stack rest tail) fuel b
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at hh ⊢ <;>
    rw [hh,shift_add] <;> simp [stack,bit]

/-- The fixed marker seed plus the first dynamic word selection has a
uniform codec-dependent cost, independent of the chosen bit. -/
theorem initialization_extra_cost {width : Nat}
    (enc : Alphabet machine → List.Vector Bool width) (b : Bool) :
    (1+offset (marker enc))+(2+(1+offset (word enc b))) = 8*width+8 := by
  simp [offset,Source284EncoderMarkerSeed.marker_length,word_length]
  omega

/-- The scanned joined body always starts with the witness delimiter zero. -/
theorem body_reverse_starts_zero (x w : List Bool) :
    ∃ rest, (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest := by
  have hf : ∃ rest, (Source284Parser.frameBits w []).reverse = false::rest := by
    induction w with
    | nil => exact ⟨[],rfl⟩
    | cons b bs ih =>
      obtain ⟨rest,hr⟩ := ih
      refine ⟨rest++[b,true],?_⟩
      simp [Source284Parser.frameBits,List.reverse_cons,hr,List.append_assoc]
  obtain ⟨rest,hr⟩ := hf
  refine ⟨rest ++ [false,false,false] ++ Source284Parser.frameBits x [],?_⟩
  simp [Source284JoinedPrefixScan.joinedBody,List.reverse_append,hr,List.append_assoc]

/-- The reversed body contains at least two symbols, so the bit selected
after its initial delimiter is an actual input bit, not virtual zero. -/
theorem body_reverse_two (x w : List Bool) :
    ∃ b rest, (Source284JoinedPrefixScan.joinedBody x w).reverse = false::b::rest := by
  obtain ⟨rest,hr⟩ := body_reverse_starts_zero x w
  have hlen : (Source284JoinedPrefixScan.joinedBody x w).length =
      2*x.length+2*w.length+5 := by
    have h := congrArg List.length (Source284JoinedPrefixScan.joined_eq_body x w)
    simp only [List.length_append,List.length_singleton,Source284JoinedFrames.joined_length] at h
    omega
  cases rest with
  | nil =>
    have hh := congrArg List.length hr
    simp [hlen] at hh
  | cons b rest => exact ⟨b,rest,hr⟩

/-- The joined scan, paid marker seed and first dynamic selection form a
single finite table run, for arbitrary higher tape suffixes. -/
theorem scan_seed_and_first {width : Nat} (enc : Alphabet machine → List.Vector Bool width)
    (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) (x w : List Bool) (left tail fuel : Nat)
    (b : Bool) (rest : List Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::b::rest) :
    let seeded := stack (marker enc) (2*((2*tail)/2^((marker enc).length+1)))
    let start := if b then Source284SelectOverwrite.trueStart (word enc false) states else 1
    run (Source284JoinedPrefixScan.table (Source284EncoderMarkerSeed.table (marker enc)
          (table (word enc false) (word enc true) states continuation)))
      ⟨left,stack (Source284JoinedFrames.joinedBits x w) tail,some 0⟩
      ((Source284JoinedFrames.joinedBits x w).length+
        ((1+offset (marker enc))+(2+(1+offset (word enc b)+fuel)))) =
    shiftConfig (7+((1+offset (marker enc))+(2+(start+offset (word enc b)))))
      (run continuation ⟨stack (b::rest) left,
        stack (word enc b) (2*((2*seeded)/2^((word enc b).length+1))),some 0⟩ fuel) := by
  dsimp only
  rw [Source284JoinedPrefixScan.scan_then,Source284LoaderAlgebra.pushed_eq_stack,hbody]
  rw [seed_and_first enc states continuation hn hv,shift_add]

/-- The first three serialized words are the fixed marker, the known zero,
then the next raw bit. -/
theorem serialized_after_first {width : Nat} (enc : Alphabet machine → List.Vector Bool width)
    (x w : List Bool) (b : Bool) (rest : List Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::b::rest) :
    Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits machine enc
      (Source284JoinedFrames.joinedBits x w) =
      word enc b ++ rest.flatMap (code enc) := by
  rw [Source284EncoderMarkerSeed.marker_is_serialized_prefix,hbody]
  simp only [List.flatMap_cons]
  simp [word,code,List.append_assoc]
  rfl

/-- Every successfully decoded source input reaches the first dynamic
serialization boundary in finite time and follows the continuation. The
actual next body bit determines the chosen finite-state branch. -/
theorem decoded_first_selection {width : Nat} (enc : Alphabet machine → List.Vector Bool width)
    (states : Nat) (continuation : Nat → Bool → Row) (limit certificate input : Nat)
    (w : List Bool) (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix b rest,
      certificate = 4*Source284Parser.encodeFrame w witnessSuffix ∧
      input = Source284Parser.encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      (Source284JoinedPrefixScan.joinedBody (Source284RawParse.payload input.bits) w).reverse = false::b::rest ∧
      ∀ fuel,
      let start := if b then Source284SelectOverwrite.trueStart (word enc false) states else 1
      let seeded := stack (marker enc)
        (2*((2*(2^(2*((limit+1)+1))*((8*((witnessSuffix/4)/4)+1)/4))) /
          2^((marker enc).length+1)))
      Source284Relative.run
        (Source284OffsetTagged.description
          (19+(80+(7+(210+(10+(160+(68+(16+(7+(1+(offset (marker enc)+
            (2+Source284SelectOverwrite.total (word enc false) (word enc true) states))))))))))))
          (Source284BothFrames.table (Source284WitnessSeek.table
            (Source284WitnessCompact.table (Source284ScratchNormalize.table
              (Source284JoinedFrames.table (Source284JoinedPrefixScan.table
                (Source284EncoderMarkerSeed.table (marker enc)
                  (table (word enc false) (word enc true) states continuation)))))))))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+
          ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
            (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
              ((2*(Source284RawParse.payload input.bits).length+6)+
                ((Source284JoinedFrames.joinedBits (Source284RawParse.payload input.bits) w).length+
                  ((1+offset (marker enc))+(2+(1+offset (word enc b)+fuel))))))))) =
      Source284SourceRelocation.lift (789+(1+offset (marker enc))+(2+(start+offset (word enc b))))
        (Source284Relative.run (encode states continuation 1)
          ⟨stack (b::rest) (2*(inputSuffix/4)+1),
            stack (word enc b) (2*((2*seeded)/2^((word enc b).length+1))),active 0⟩ fuel) := by
  obtain ⟨b,rest,hbody⟩ := body_reverse_two (Source284RawParse.payload input.bits) w
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284EncoderMarkerSeed.decoded_scan_and_seed
    (marker enc) (2+Source284SelectOverwrite.total (word enc false) (word enc true) states)
    (table (word enc false) (word enc true) states continuation) limit certificate input w
    (by omega) (closed _ _ states continuation hn hv) hdec
  refine ⟨ws,is,b,rest,hcert,hinput,hbody,?_⟩
  intro fuel
  dsimp only
  let left := 2*(is/4)+1
  let tail := 2^(2*((limit+1)+1))*((8*((ws/4)/4)+1)/4)
  let seeded := stack (marker enc) (2*((2*tail)/2^((marker enc).length+1)))
  let t := 2+(1+offset (word enc b))
  have hr' := hr (t+fuel)
  rw [hbody] at hr'
  let c : Config := ⟨stack (false::b::rest) left,seeded,some 0⟩
  have hc : Valid (2+Source284SelectOverwrite.total (word enc false) (word enc true) states) c := by
    intro q hq; simp [c] at hq; subst q; omega
  have hv0 := run_toSource _ (table (word enc false) (word enc true) states continuation) 1 c
    (closed _ _ states continuation hn hv) hc (t+fuel)
  change Source284Relative.run (encode _ (table (word enc false) (word enc true) states continuation) 1)
    ⟨stack (false::b::rest) left,seeded,active 0⟩ (t+fuel) = _ at hv0
  have hp := first_then (word enc false) (word enc true) states continuation hn hv
    seeded (stack rest left) fuel b
  have he : stack (false::b::rest) left = 2*(2*(stack rest left)+bit b) := by simp [stack,bit]
  rw [he] at hv0 hr'
  change Source284Relative.run (encode _ (table (word enc false) (word enc true) states continuation) 1)
    ⟨2*(2*(stack rest left)+bit b),seeded,active 0⟩ (t+fuel) = _ at hv0
  dsimp only at hp
  have hw : (if b then word enc true else word enc false) = word enc b := by cases b <;> rfl
  rw [hw] at hp
  change run (table (word enc false) (word enc true) states continuation) c
    (2+(1+offset (word enc b)+fuel)) = _ at hp
  have ht : t+fuel = 2+(1+offset (word enc b)+fuel) := by dsimp [t]; omega
  rw [ht] at hr' hv0
  cases b with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte] at hp hr' hv0 ⊢
    rw [hv0,hp,← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add] at hr'
    let c' : Config := ⟨stack (false::rest) left,
      stack (word enc false) (2*((2*seeded)/2^((word enc false).length+1))),some 0⟩
    have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
    have hv1 := run_toSource states continuation 1 c' hv hc' fuel
    change Source284Relative.run (encode states continuation 1) ⟨stack (false::rest) left,
      stack (word enc false) (2*((2*seeded)/2^((word enc false).length+1))),active 0⟩ fuel = _ at hv1
    dsimp only [c'] at hv1
    simp only [stack,bit] at hr' hv1 ⊢
    rw [← hv1] at hr'
    exact hr'
  | true =>
    simp only [↓reduceIte] at hp hr' hv0 ⊢
    rw [hv0,hp,← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add] at hr'
    let c' : Config := ⟨stack (true::rest) left,
      stack (word enc true) (2*((2*seeded)/2^((word enc true).length+1))),some 0⟩
    have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
    have hv1 := run_toSource states continuation 1 c' hv hc' fuel
    change Source284Relative.run (encode states continuation 1) ⟨stack (true::rest) left,
      stack (word enc true) (2*((2*seeded)/2^((word enc true).length+1))),active 0⟩ fuel = _ at hv1
    dsimp only [c'] at hv1
    simp only [stack,bit] at hr' hv1 ⊢
    rw [← hv1] at hr'
    exact hr'

namespace Fixtures

def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (Source284SelectOverwrite.table [false] [true] 1 loop)
    ⟨15,0,some 0⟩ 5 = ⟨0,12,some 5⟩ := by decide +kernel
example : run (Source284SelectOverwrite.table [false] [true] 1 loop)
    ⟨15,1,some 0⟩ 5 = ⟨1,13,some 10⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284EncoderFirstSelection
