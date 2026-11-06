import Shared.Beeping.NPcoNP.Source284SerializerStripWindow
import Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed

/-! Paid fixed tagged-marker initialization after the joined-body scan.
This overwrites a fixed prefix of arbitrary old scratch cells, preserves the
body and high suffix, and enters an arbitrary finite continuation. A longer
zero runway is not supplied by this construction. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284TaggedMarkerSeed

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig offset)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed (shift_add)

/-- One turn selects any specified state of the relocated continuation. -/
def turnTable (start : Nat) (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some (1+start)⟩
  else shiftRow 1 (continuation (q-1) b)

theorem turn_closed (states start : Nat) (continuation : Nat → Bool → Row)
    (hs : start < states) (hc : Closed states continuation) :
    Closed (1+states) (turnTable start continuation) := by
  intro q hq b q' hn
  by_cases h0 : q=0
  · subst q; simp [turnTable] at hn; omega
  · have hv := hc (q-1) (by omega) b
    have he : (shiftRow 1 (continuation (q-1) b)).next = some q' := by
      simpa [turnTable,h0] using hn
    cases hh : (continuation (q-1) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hv r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem turn_step (start : Nat) (continuation : Nat → Bool → Row) (left right : Nat) :
    step (turnTable start continuation) ⟨left,right,some 0⟩ =
      ⟨right,left,some (1+start)⟩ := by
  simp [step,turnTable,Source284HardwireTable.bit_decide_mod]
  omega

theorem turn_relocated_step (start : Nat) (continuation : Nat → Bool → Row) (c : Config) :
    step (turnTable start continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,turnTable,show 1+q ≠ 0 by omega,
        ↓reduceIte,show 1+q-1=q by omega,shiftRow]
      split <;> rfl

theorem turn_relocated_run (start : Nat) (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (turnTable start continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,turn_relocated_step]

theorem turn_then (start : Nat) (continuation : Nat → Bool → Row) (left right fuel : Nat) :
    run (turnTable start continuation) ⟨left,right,some 0⟩ (1+fuel) =
      shiftConfig 1 (run continuation ⟨right,left,some start⟩ fuel) := by
  rw [show 1+fuel = fuel+1 by omega,Source284HardwireTable.run_front,turn_step]
  change run (turnTable start continuation) (shiftConfig 1 ⟨right,left,some start⟩) fuel = _
  rw [turn_relocated_run]

/-- A fixed seed, then a turn, with its continuation start specified. -/
def table (word : List Bool) (start : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284EncoderMarkerSeed.table word (turnTable start continuation)

theorem closed (word : List Bool) (states start : Nat) (continuation : Nat → Bool → Row)
    (hs : start < states) (hc : Closed states continuation) :
    Closed (1+(offset word+(1+states))) (table word start continuation) := by
  exact Source284EncoderMarkerSeed.closed word _ _ (by omega) (turn_closed states start continuation hs hc)

/-- The body half is unchanged; the scratch half has the specified word and
one zero sentinel, with all higher old cells retained. Each step is paid. -/
theorem seed_then (word : List Bool) (start : Nat) (continuation : Nat → Bool → Row)
    (left body fuel : Nat) :
    run (table word start continuation) ⟨left,body,some 0⟩
      (1+offset word+1+fuel) =
      shiftConfig (1+offset word+1) (run continuation
        ⟨stack word (2*(left/2^(word.length+1))),body,some start⟩ fuel) := by
  change run (Source284EncoderMarkerSeed.table word (turnTable start continuation)) _ _ = _
  rw [show 1+offset word+1+fuel = 1+offset word+(1+fuel) by omega,
    Source284EncoderMarkerSeed.seed_then,turn_then,shift_add]

/-- The initialized tagged word begins with the blank separator. Its length
is fixed by the alphabet codec and does not depend on the tested input. -/
def word {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width) : List Bool :=
  false::tagged (Source284EncoderMarkerSeed.marker enc)

theorem word_length {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width) :
    (word enc).length = 1+3*width := by
  simp [word,tagged,Source284EncoderMarkerSeed.marker_length]
  omega

theorem seed_cost {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width) :
    1+offset (word enc)+1 = 6*width+6 := by
  simp [offset,word_length]
  omega

/-- The actual finite prefix scan and fixed tagged seed share one table. -/
theorem scan_then (x w : List Bool) (word : List Bool) (start : Nat)
    (continuation : Nat → Bool → Row) (left tail fuel : Nat) :
    run (Source284JoinedPrefixScan.table (table word start continuation))
      ⟨left,stack (Source284JoinedFrames.joinedBits x w) tail,some 0⟩
      ((Source284JoinedFrames.joinedBits x w).length+(1+offset word+1+fuel)) =
      shiftConfig (7+(1+offset word+1)) (run continuation
        ⟨stack word (2*((2*tail)/2^(word.length+1))),
          stack (Source284JoinedPrefixScan.joinedBody x w).reverse left,some start⟩ fuel) := by
  rw [Source284JoinedPrefixScan.scan_then]
  rw [Source284LoaderAlgebra.pushed_eq_stack,seed_then,shift_add]

/-- The numeric unary-record source performs the same scan and seed, then
executes every step of the supplied continuation. -/
theorem source_scan_then (x w : List Bool) (word : List Bool) (states start : Nat)
    (continuation : Nat → Bool → Row) (left tail fuel : Nat)
    (hs : start < states) (hc : Closed states continuation) :
    Source284Relative.run
      (encode (7+(1+(offset word+(1+states))))
        (Source284JoinedPrefixScan.table (table word start continuation)) 1)
      ⟨left,stack (Source284JoinedFrames.joinedBits x w) tail,active 0⟩
      ((Source284JoinedFrames.joinedBits x w).length+(1+offset word+1+fuel)) =
      Source284SourceRelocation.lift (7+(1+offset word+1))
        (Source284Relative.run (encode states continuation 1)
          ⟨stack word (2*((2*tail)/2^(word.length+1))),
            stack (Source284JoinedPrefixScan.joinedBody x w).reverse left,active start⟩ fuel) := by
  let original := Source284JoinedPrefixScan.table (table word start continuation)
  let initial : Config := ⟨left,stack (Source284JoinedFrames.joinedBits x w) tail,some 0⟩
  let n := 7+(1+(offset word+(1+states)))
  let clock := (Source284JoinedFrames.joinedBits x w).length+(1+offset word+1+fuel)
  have hclosed : Closed n original := Source284JoinedPrefixScan.closed _ _ (by omega)
    (closed word states start continuation hs hc)
  have hvalid : Valid n initial := by intro q hq; simp [initial] at hq; subst q; dsimp [n]; omega
  have hr := run_toSource n original 1 initial hclosed hvalid clock
  have he := scan_then x w word start continuation left tail fuel
  change run original initial clock = _ at he
  rw [he,← Source284SourceRelocation.lift_toSource] at hr
  let final : Config := ⟨stack word (2*((2*tail)/2^(word.length+1))),
    stack (Source284JoinedPrefixScan.joinedBody x w).reverse left,some start⟩
  have hfinal : Valid states final := by intro q hq; simp [final] at hq; subst q; exact hs
  have hf := run_toSource states continuation 1 final hc hfinal fuel
  rw [← hf] at hr
  exact hr

namespace Fixtures
example : run (table [false,true,false,true] 1 (fun _ b => ⟨b,false,some 0⟩))
    ⟨255,18,some 0⟩ 12 = ⟨234,18,some 13⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284TaggedMarkerSeed
