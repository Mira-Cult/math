import Shared.Beeping.NPcoNP.Source284OffsetFrameAdapter

/-! Reveal the original input after the decoded-witness frame is prepared.
The witness and all high data remain on the opposite tape; this does not yet
copy or pack the two components into the verifier's canonical window. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284OffsetRevealInput

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource shiftConfig_add)

/-- Three paid orientation/boundary moves precede the existing unary-pair
scanner; four scanner states precede the supplied continuation. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,true,some 3⟩
  else shiftRow 3 (Source284UnaryPairScanner.table continuation (q-3) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (7+states) (table continuation) := by
  have hs := Source284UnaryPairScanner.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases hq0 : q < 3
  · interval_cases q <;> simp [table] at hnext <;> omega
  · have h0 : q ≠ 0 := by omega
    have h1 : q ≠ 1 := by omega
    have h2 : q ≠ 2 := by omega
    have ht : (shiftRow 3 (Source284UnaryPairScanner.table continuation (q-3) b)).next = some q' := by
      simpa [table,h0,h1,h2] using hnext
    cases he : (Source284UnaryPairScanner.table continuation (q-3) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hs (q-3) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (3+q) b = shiftRow 3 (Source284UnaryPairScanner.table continuation q b) := by
  simp [table,show 3+q ≠ 1 by omega,show 3+q ≠ 2 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 3 c) =
      shiftConfig 3 (step (Source284UnaryPairScanner.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 3 c) fuel =
      shiftConfig 3 (run (Source284UnaryPairScanner.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem setup (continuation : Nat → Bool → Row) (tokens : List Bool) (input frame : Nat) :
    run (table continuation) ⟨2*pairTape tokens input,frame,some 0⟩ 3 =
      ⟨pairTape tokens input,2*frame,some 3⟩ := by
  have h0 : step (table continuation) ⟨2*pairTape tokens input,frame,some 0⟩ =
      ⟨frame,2*pairTape tokens input,some 1⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  have h1 : step (table continuation) ⟨frame,2*pairTape tokens input,some 1⟩ =
      ⟨2*frame,pairTape tokens input,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
  have h2 : step (table continuation) ⟨2*frame,pairTape tokens input,some 2⟩ =
      ⟨pairTape tokens input,2*frame,some 3⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  simp only [run,h0,h1,h2]

/-- The original input is exposed without erasing the witness or high data;
the precise tape displacement and source time include the extra tag pair. -/
theorem reveal (continuation : Nat → Bool → Row) (n input frame : Nat) :
    run (table continuation) ⟨2*pairTape (List.replicate n false) input,frame,some 0⟩
      (3+(2*n+3)) =
    ⟨4*(4^n*(2*frame))+1,input,some 7⟩ := by
  rw [run_add,setup]
  change run (table continuation) (shiftConfig 3
    ⟨pairTape (List.replicate n false) input,2*frame,some 0⟩) _ = _
  rw [relocated_run]
  have hs := Source284UnaryPairScanner.scan continuation (List.replicate n false) input (2*frame)
  simp only [List.length_replicate,Source284UnaryPairScanner.push_zeros] at hs
  rw [hs]
  simp [shiftConfig]

/-- The displacement does not lose any witness-frame or suffix bits: the
complete original frame is recovered from the opposite half arithmetically. -/
theorem reveal_frame_recover (n frame : Nat) :
    (4*(4^n*(2*frame))+1) / 4^(n+1) = 2*frame := by
  have hp : 1 < 4^(n+1) := one_lt_pow₀ (by decide : (1 : Nat) < 4) (by omega)
  have he : 4*(4^n*(2*frame))+1 = 1+4^(n+1)*(2*frame) := by
    rw [pow_succ]
    ring
  rw [he,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt hp,Nat.zero_add]

/-- All subsequent continuation steps preserve the seven-state relocation. -/
theorem reveal_then (continuation : Nat → Bool → Row) (n input frame fuel : Nat) :
    run (table continuation) ⟨2*pairTape (List.replicate n false) input,frame,some 0⟩
      ((3+(2*n+3))+fuel) =
    shiftConfig 7 (run continuation ⟨4*(4^n*(2*frame))+1,input,some 0⟩ fuel) := by
  rw [run_add,reveal]
  let c : Config := ⟨4*(4^n*(2*frame))+1,input,some 0⟩
  change run (table continuation) (shiftConfig 3 (shiftConfig 1 (shiftConfig 3 c))) fuel = _
  rw [relocated_run,Source284UnaryPairScanner.relocated_run,Source284ScratchScanner.relocated_run,
    shiftConfig_add,shiftConfig_add]

/-- The decoded witness frame is prepared, the original input is revealed,
and the supplied finite continuation runs from the resulting exact tape. -/
theorem decoded_reveal_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ suffix, certificate = 4*encodeFrame w suffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description (19+(80+(7+states)))
          (Source284OffsetFrameAdapter.table (table continuation)))
        (Source284Relative.initial certificate (pairTape (List.replicate limit false) input))
        (4+(Source284PayloadSentinelPipeline.totalCost w.length+
          (Source284OffsetMatch.compareCost w.length+(1+
            ((1+((4*(limit+1)+6)+(4*w.length+12)))+
              (10*w.length+21+((3+(2*(limit+1)+3))+fuel))))))) =
      lift 318 (Source284Relative.run (encode states continuation 1)
        ⟨4*(4^(limit+1)*(2*encodeFrame w (8*((suffix/4)/4)+1)))+1,input,active 0⟩ fuel) := by
  obtain ⟨suffix,hcert,_,hr⟩ := Source284OffsetFrameAdapter.decoded_frame_then
    (7+states) (table continuation) limit certificate input w (by omega) (closed states continuation hn hv) hdec
  refine ⟨suffix,hcert,?_⟩
  intro fuel
  let frame := encodeFrame w (8*((suffix/4)/4)+1)
  let t := 3+(2*(limit+1)+3)
  have hr' := hr (t+fuel)
  change Source284Relative.run _ _ _ = lift 311
    (Source284Relative.run (encode (7+states) (table continuation) 1)
      ⟨2*pairTape (List.replicate (limit+1) false) input,frame,active 0⟩ (t+fuel)) at hr'
  let c : Config := ⟨2*pairTape (List.replicate (limit+1) false) input,frame,some 0⟩
  have hvalid : Valid (7+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hv0 := run_toSource (7+states) (table continuation) 1 c (closed states continuation hn hv) hvalid (t+fuel)
  change Source284Relative.run (encode (7+states) (table continuation) 1)
    ⟨2*pairTape (List.replicate (limit+1) false) input,frame,active 0⟩ (t+fuel) = _ at hv0
  rw [hv0,reveal_then] at hr'
  let c' : Config := ⟨4*(4^(limit+1)*(2*frame))+1,input,some 0⟩
  have hvalid' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hv1 := run_toSource states continuation 1 c' hv hvalid' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨4*(4^(limit+1)*(2*frame))+1,input,active 0⟩ fuel = _ at hv1
  rw [← lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

namespace Fixtures

/-- A zero-token tape still pays the sentinel scan and keeps both values. -/
example (continuation : Nat → Bool → Row) :
    run (table continuation) ⟨2*pairTape [] 7,13,some 0⟩ 6 = ⟨105,7,some 7⟩ := by
  simpa using reveal continuation 0 7 13

example : (4*(4^3*(2*12345))+1)/4^4 = 2*12345 := by
  exact reveal_frame_recover 3 12345

end Fixtures

end Shared.Beeping.NPcoNP.Source284OffsetRevealInput
