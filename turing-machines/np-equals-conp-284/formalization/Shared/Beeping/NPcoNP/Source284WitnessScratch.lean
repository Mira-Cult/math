import Shared.Beeping.NPcoNP.Source284WitnessSeek
import Shared.Beeping.NPcoNP.Source284ScratchPack

/-! Pack the entire decoded witness frame into the existing self-delimited
scratch representation after the paid witness seek. This finite source table
preserves the input-side half. It is not yet the canonical verifier-window
loader or a refinement of the physical 284-state beeper. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284WitnessScratch

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchTerminator (mark)

/-- Merge the seek's empty/nonempty modes via two paid turns. -/
def entry (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q < 2 then ⟨b,true,some (q+2)⟩
  else if q < 4 then ⟨b,true,some 4⟩
  else shiftRow 4 (Source284ScratchPack.table continuation (q-4) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (137+states) (entry continuation) := by
  have hc := Source284ScratchPack.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases hs : q < 4
  · interval_cases q <;> cases b <;> simp [entry] at hnext <;> omega
  · have ht : (shiftRow 4 (Source284ScratchPack.table continuation (q-4) b)).next = some q' := by
      simpa [entry,show ¬ q < 2 by omega,hs] using hnext
    cases he : (Source284ScratchPack.table continuation (q-4) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hc (q-4) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    entry continuation (4+q) b = shiftRow 4 (Source284ScratchPack.table continuation q b) := by
  simp [entry,show ¬ 4+q < 2 by omega,show ¬ 4+q < 4 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (entry continuation) (shiftConfig 4 c) =
      shiftConfig 4 (step (Source284ScratchPack.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (entry continuation) (shiftConfig 4 c) fuel =
      shiftConfig 4 (run (Source284ScratchPack.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem enter (continuation : Nat → Bool → Row) (mode left right : Nat) (hm : mode < 2) :
    run (entry continuation) ⟨left,right,some mode⟩ 2 = ⟨left,right,some 4⟩ := by
  have h0 : step (entry continuation) ⟨left,right,some mode⟩ = ⟨right,left,some (mode+2)⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [entry,hm]
  have h1 : step (entry continuation) ⟨right,left,some (mode+2)⟩ = ⟨left,right,some 4⟩ := by
    apply Source284WindowRewind.generic_turn; intro b
    simp [entry,show ¬ mode+2 < 2 by omega,show mode+2 < 4 by omega]
  simp only [run,h0,h1]

theorem toSource_injective : Function.Injective toSource := by
  intro a b h
  cases a with
  | mk al ar ast =>
    cases b with
    | mk bl br bst =>
      cases ast <;> cases bst <;>
        simp [toSource,nextState,active,Source284Relative.Config.mk.injEq] at h ⊢ <;> omega

/-- The scratch packer's existing source-run theorem yields an exact logical
configuration, not merely an acceptance test. -/
theorem pack (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (left suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    run (Source284ScratchPack.table continuation) ⟨left,encodeFrame w suffix,some 0⟩
      (Source284ScratchPack.totalCost w.length) =
      ⟨left,encodeFrame [] (scratch w (mark suffix)),some 133⟩ := by
  apply toSource_injective
  have hc : Valid (133+states) ⟨left,encodeFrame w suffix,some 0⟩ := by
    intro q hq; simp at hq; subst q; omega
  have hr := run_toSource (133+states) (Source284ScratchPack.table continuation) 1
    ⟨left,encodeFrame w suffix,some 0⟩ (Source284ScratchPack.closed states continuation hn hv) hc
    (Source284ScratchPack.totalCost w.length)
  have hp := Source284ScratchPack.source_pack_frame states continuation w left suffix hn hv
  change Source284Relative.run (Source284ScratchPack.description states continuation)
    (toSource ⟨left,encodeFrame w suffix,some 0⟩) _ = _ at hp
  rw [Source284ScratchPack.description] at hp
  rw [hr] at hp
  exact hp

theorem pack_after (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (Source284ScratchPack.table continuation) (shiftConfig 133 c) fuel =
      shiftConfig 133 (run continuation c fuel) := by
  have he : shiftConfig 133 c = shiftConfig 8 (shiftConfig 8 (shiftConfig 16
      (shiftConfig 32 (shiftConfig 69 c)))) := by
    repeat rw [Source284SourceRelocation.shiftConfig_add]
  rw [he]
  unfold Source284ScratchPack.table
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

/-- Both seek modes enter the same packer. Every witness bit is represented
in its output, and the entire input-side tape is unchanged. -/
theorem pack_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (left suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    run (entry continuation) ⟨left,encodeFrame w suffix,some (if w = [] then 1 else 0)⟩
      (2+Source284ScratchPack.totalCost w.length+fuel) =
    shiftConfig 137 (run continuation
      ⟨left,encodeFrame [] (scratch w (mark suffix)),some 0⟩ fuel) := by
  have hm : (if w = [] then 1 else 0) < 2 := by split <;> omega
  rw [Nat.add_assoc,run_add,enter _ _ _ _ hm]
  change run (entry continuation) (shiftConfig 4 ⟨left,encodeFrame w suffix,some 0⟩) _ = _
  rw [relocated_run,run_add,pack states continuation w left suffix hn hv]
  change shiftConfig 4 (run (Source284ScratchPack.table continuation)
    (shiftConfig 133 ⟨left,encodeFrame [] (scratch w (mark suffix)),some 0⟩) fuel) = _
  rw [pack_after,Source284SourceRelocation.shiftConfig_add]

/-- For a valid tagged certificate, the actual source program prepares both
frames, seeks the witness, packs every witness bit, then follows the supplied
continuation for every subsequent clock. The scratch terminator overwrites
exactly the two low cells of the witness frame's ignored suffix. -/
theorem decoded_pack_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*encodeFrame w witnessSuffix ∧
      input = encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description (19+(80+(7+(210+(10+(137+states))))))
          (Source284BothFrames.table (Source284WitnessSeek.table (entry continuation))))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+
          ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
            ((2+Source284ScratchPack.totalCost w.length)+fuel))) =
      Source284SourceRelocation.lift 675 (Source284Relative.run (encode states continuation 1)
        ⟨4^((limit+1)+1)*(4*encodeFrame (Source284RawParse.payload input.bits)
            (2*(inputSuffix/4)+1)+1),
          encodeFrame [] (scratch w (mark (8*((witnessSuffix/4)/4)+1))),active 0⟩ fuel) := by
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284WitnessSeek.decoded_seek_then
    (137+states) (entry continuation) limit certificate input w (by omega)
      (closed states continuation hn hv) hdec
  refine ⟨ws,is,hcert,hinput,?_⟩
  intro fuel
  let x := Source284RawParse.payload input.bits
  let left := 4^((limit+1)+1)*(4*encodeFrame x (2*(is/4)+1)+1)
  let suffix := 8*((ws/4)/4)+1
  let t := 2+Source284ScratchPack.totalCost w.length
  have hr' := hr (t+fuel)
  change Source284Relative.run _ _ _ = Source284SourceRelocation.lift 538
    (Source284Relative.run (encode (137+states) (entry continuation) 1)
      ⟨left,encodeFrame w suffix,active (if w = [] then 1 else 0)⟩ (t+fuel)) at hr'
  let c : Config := ⟨left,encodeFrame w suffix,some (if w = [] then 1 else 0)⟩
  have hc : Valid (137+states) c := by
    intro q hq; simp [c] at hq; subst q; split <;> omega
  have hv0 := run_toSource (137+states) (entry continuation) 1 c (closed states continuation hn hv) hc (t+fuel)
  change Source284Relative.run (encode (137+states) (entry continuation) 1)
    ⟨left,encodeFrame w suffix,active (if w = [] then 1 else 0)⟩ (t+fuel) = _ at hv0
  have hp := pack_then states continuation w left suffix fuel hn hv
  change run (entry continuation) c (t+fuel) = _ at hp
  rw [hv0,hp] at hr'
  let c' : Config := ⟨left,encodeFrame [] (scratch w (mark suffix)),some 0⟩
  have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hv1 := run_toSource states continuation 1 c' hv hc' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨left,encodeFrame [] (scratch w (mark suffix)),active 0⟩ fuel = _ at hv1
  rw [← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

/-- The scratch stream has a mathematical decoder that recovers every
witness bit in order. This does not assert that decoder is the verifier. -/
theorem packed_decodes (w : List Bool) (suffix : Nat) :
    Source284ScratchDecode.decode (scratch w (mark suffix)) = some w ∧
      Source284ScratchDecode.inspections (scratch w (mark suffix)) = w.length+1 :=
  Source284ScratchPack.output_decodes w suffix

/-- The preparation, seek, and whole-witness packing have a uniform quadratic
bound in the original cutoff and parsed input length. -/
theorem decoded_pack_bound (limit certificate input : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    Source284BothFrames.time limit w input+
      ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
        (2+Source284ScratchPack.totalCost w.length)) ≤
      8*limit*limit+90*limit+
        2*Source284Parser.length input*Source284Parser.length input+
        28*Source284Parser.length input+177 := by
  have h0 := Source284BothFramesContinue.decoded_time_bound limit certificate input w hdec
  have h1 := Source284WitnessSeek.seek_time_bound limit w
  have h2 := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  have h3 : w.length*w.length ≤ limit*limit := Nat.mul_self_le_mul_self h2
  rw [Source284ScratchPack.totalCost_formula]
  nlinarith

namespace Fixtures

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    run (entry continuation) ⟨7,38,some 1⟩ 18 = ⟨7,36,some 137⟩ := by
  have h := pack_then states continuation [] 7 19 0 hn hv
  simpa [encodeFrame,Source284ScratchPack.totalCost,Source284PayloadLoop.cost,
    scratch,mark,shiftConfig,run] using h

example : Source284ScratchDecode.decode (scratch [true,false,true] (mark 19)) =
    some [true,false,true] := (packed_decodes _ _).1

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    run (entry continuation) ⟨7,295,some 0⟩ 62 = ⟨7,322,some 137⟩ := by
  have h := pack_then states continuation [true,false] 7 9 0 hn hv
  simpa [encodeFrame,Source284ScratchPack.totalCost,Source284PayloadLoop.cost,
    scratch,mark,bit,shiftConfig,run] using h

end Fixtures
end Shared.Beeping.NPcoNP.Source284WitnessScratch
