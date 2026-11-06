import Shared.Beeping.NPcoNP.Source284BothFramesContinue

/-! Finite seek from the two-frame layout to the witness boundary. The even
unary gap distinguishes a nonempty witness marker from the empty witness's
sentinel. Both tape halves are preserved; this is not a pair-window loader. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284WitnessSeek

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

/-- States three and four scan zeros in alternating parity. On the first
one they dispatch to continuation mode zero (nonempty) or one (empty). -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,false,some 3⟩
  else if q = 3 then ⟨b,b,some (if b then 5 else 4)⟩
  else if q = 4 then ⟨b,b,some (if b then 6 else 3)⟩
  else if q = 5 then ⟨b,true,some 10⟩
  else if q = 6 then ⟨b,false,some 9⟩
  else if q = 9 then ⟨b,true,some 11⟩
  else if q < 10 then ⟨b,false,some q⟩
  else shiftRow 10 (continuation (q-10) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (10+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hs : q < 10
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have h0 : q ≠ 0 := by omega
    have h1 : q ≠ 1 := by omega
    have h2 : q ≠ 2 := by omega
    have h3 : q ≠ 3 := by omega
    have h4 : q ≠ 4 := by omega
    have h5 : q ≠ 5 := by omega
    have h6 : q ≠ 6 := by omega
    have h9 : q ≠ 9 := by omega
    have ht : (shiftRow 10 (continuation (q-10) b)).next = some q' := by
      simpa [table,h0,h1,h2,h3,h4,h5,h6,h9,hs] using hnext
    cases he : (continuation (q-10) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-10) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (10+q) b = shiftRow 10 (continuation q b) := by
  simp [table,show 10+q ≠ 1 by omega,show 10+q ≠ 2 by omega,
    show 10+q ≠ 3 by omega,show 10+q ≠ 4 by omega,show 10+q ≠ 5 by omega,
    show 10+q ≠ 6 by omega,show 10+q ≠ 9 by omega,show ¬ 10+q < 10 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 10 c) = shiftConfig 10 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 10 c) fuel = shiftConfig 10 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- Cross the protected boundary and enter the even-parity zero scan. -/
theorem setup (continuation : Nat → Bool → Row) (n inputFrame witnessFrame : Nat) :
    run (table continuation)
      ⟨2*(4*(4^n*(2*witnessFrame))+1),inputFrame,some 0⟩ 3 =
      ⟨4*inputFrame+1,4^(n+1)*witnessFrame,some 3⟩ := by
  have h0 : step (table continuation)
      ⟨2*(4*(4^n*(2*witnessFrame))+1),inputFrame,some 0⟩ =
      ⟨inputFrame,2*(4*(4^n*(2*witnessFrame))+1),some 1⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  have h1 : step (table continuation)
      ⟨inputFrame,2*(4*(4^n*(2*witnessFrame))+1),some 1⟩ =
      ⟨2*inputFrame,4*(4^n*(2*witnessFrame))+1,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
  have h2 : step (table continuation)
      ⟨2*inputFrame,4*(4^n*(2*witnessFrame))+1,some 2⟩ =
      ⟨4*inputFrame+1,4^(n+1)*witnessFrame,some 3⟩ := by
    have hdiv : (4*(4^n*(2*witnessFrame))+1)/2 = 4^n*4*witnessFrame := by
      have he : 4*(4^n*(2*witnessFrame))+1 = 2*(4^n*4*witnessFrame)+1 := by ring
      rw [he]; omega
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod,pow_succ,hdiv] <;> ring
  simp only [run,h0,h1,h2]

theorem zero_pair (continuation : Nat → Bool → Row) (left right : Nat) :
    run (table continuation) ⟨left,4*right,some 3⟩ 2 = ⟨4*left,right,some 3⟩ := by
  have h0 : step (table continuation) ⟨left,4*right,some 3⟩ = ⟨2*left,2*right,some 4⟩ := by
    have hm : (4*right).testBit 0 = false := by simp [Nat.testBit_zero,Nat.mul_mod]
    have hd : (4*right)/2 = 2*right := by omega
    simp [step,table,bit,hm,hd]
  have h1 : step (table continuation) ⟨2*left,2*right,some 4⟩ = ⟨4*left,right,some 3⟩ := by
    have hm : (2*right).testBit 0 = false := by simp [Nat.testBit_zero]
    simp [step,table,bit,hm] <;> omega
  simp only [run,h0,h1]

/-- The finite scan is controlled by actual bits; `n` is only a proof index. -/
theorem zero_pairs (continuation : Nat → Bool → Row) (n left right : Nat) :
    run (table continuation) ⟨left,4^n*right,some 3⟩ (2*n) =
      ⟨4^n*left,right,some 3⟩ := by
  induction n generalizing left with
  | zero => simp [run]
  | succ n ih =>
    have ht : 2*(n+1) = 2+2*n := by omega
    rw [ht,run_add,pow_succ]
    have hmul : (4^n*4)*right = 4*(4^n*right) := by ring
    rw [hmul,zero_pair,ih]
    congr 1 <;> ring

/-- A nonempty frame is restored exactly at its marker and enters mode zero. -/
theorem nonempty (continuation : Nat → Bool → Row) (b : Bool) (bs : List Bool)
    (left tail : Nat) :
    run (table continuation) ⟨left,encodeFrame (b::bs) tail,some 3⟩ 2 =
      ⟨left,encodeFrame (b::bs) tail,some 10⟩ := by
  have hodd : encodeFrame (b::bs) tail % 2 = 1 := by
    cases b <;> simp [encodeFrame] <;> omega
  have ht : (encodeFrame (b::bs) tail).testBit 0 = true := by
    simp [Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod,hodd]
  have hs : step (table continuation) ⟨left,encodeFrame (b::bs) tail,some 3⟩ =
      ⟨encodeFrame (b::bs) tail,left,some 5⟩ := by
    simp [step,table,ht,bit]
    omega
  have hr : step (table continuation) ⟨encodeFrame (b::bs) tail,left,some 5⟩ =
      ⟨left,encodeFrame (b::bs) tail,some 10⟩ := by
    apply Source284WindowRewind.generic_turn; intro a; simp [table]
  simp only [run,hs,hr]

/-- The empty frame's zero delimiter is crossed and restored, then the
continuation enters mode one. The high suffix is untouched. -/
theorem empty (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,encodeFrame [] (8*tail+1),some 3⟩ 4 =
      ⟨left,encodeFrame [] (8*tail+1),some 11⟩ := by
  have h0 : step (table continuation) ⟨left,2*(8*tail+1),some 3⟩ =
      ⟨2*left,8*tail+1,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> omega
  have h1 : step (table continuation) ⟨2*left,8*tail+1,some 4⟩ =
      ⟨8*tail+1,2*left,some 6⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨8*tail+1,2*left,some 6⟩ =
      ⟨2*(8*tail+1),left,some 9⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> omega
  have h3 : step (table continuation) ⟨2*(8*tail+1),left,some 9⟩ =
      ⟨left,2*(8*tail+1),some 11⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  simp only [encodeFrame,run,h0,h1,h2,h3]

/-- From the actual two-frame shape, the finite machine reaches the exact
witness boundary. `n` is the already-present unary gap, not preloaded state. -/
theorem seek (continuation : Nat → Bool → Row) (n inputFrame : Nat)
    (w : List Bool) (tail : Nat) :
    let frame := encodeFrame w (8*tail+1)
    run (table continuation)
      ⟨2*(4*(4^n*(2*frame))+1),inputFrame,some 0⟩
      (3+2*(n+1)+(if w = [] then 4 else 2)) =
      ⟨4^(n+1)*(4*inputFrame+1),frame,some (if w = [] then 11 else 10)⟩ := by
  dsimp only
  rw [Nat.add_assoc,run_add,setup,run_add,zero_pairs]
  cases w with
  | nil => simp [empty]
  | cons b bs => simp [nonempty]

/-- After the finite seek, both continuation modes preserve every later
transition and both full tape halves. -/
theorem seek_then (continuation : Nat → Bool → Row) (n inputFrame : Nat)
    (w : List Bool) (tail fuel : Nat) :
    let frame := encodeFrame w (8*tail+1)
    run (table continuation)
      ⟨2*(4*(4^n*(2*frame))+1),inputFrame,some 0⟩
      ((3+2*(n+1)+(if w = [] then 4 else 2))+fuel) =
    shiftConfig 10 (run continuation
      ⟨4^(n+1)*(4*inputFrame+1),frame,some (if w = [] then 1 else 0)⟩ fuel) := by
  dsimp only
  rw [run_add,seek]
  have he : (if w = [] then 11 else 10) = 10+(if w = [] then 1 else 0) := by
    split <;> omega
  rw [he]
  change run (table continuation) (shiftConfig 10
    ⟨4^(n+1)*(4*inputFrame+1),encodeFrame w (8*tail+1),some (if w = [] then 1 else 0)⟩) fuel = _
  rw [relocated_run]

/-- From a valid tagged certificate, the same finite source table prepares
both frames, seeks the witness, and follows the selected continuation mode.
The bound and input are runtime tape data; suffixes remain represented. -/
theorem decoded_seek_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 2 ≤ states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*encodeFrame w witnessSuffix ∧
      input = encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description (19+(80+(7+(210+(10+states)))))
          (Source284BothFrames.table (table continuation)))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+
          ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+fuel)) =
      Source284SourceRelocation.lift 538 (Source284Relative.run (encode states continuation 1)
        ⟨4^((limit+1)+1)*(4*encodeFrame (Source284RawParse.payload input.bits)
            (2*(inputSuffix/4)+1)+1),
          encodeFrame w (8*((witnessSuffix/4)/4)+1),
          active (if w = [] then 1 else 0)⟩ fuel) := by
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284BothFramesContinue.both_frames_after
    (10+states) (table continuation) limit certificate input w (by omega) (closed states continuation hn hv) hdec
  refine ⟨ws,is,hcert,hinput,?_⟩
  intro fuel
  let frame := encodeFrame w (8*((ws/4)/4)+1)
  let inputFrame := encodeFrame (Source284RawParse.payload input.bits) (2*(is/4)+1)
  let seekTime := 3+2*((limit+1)+1)+(if w = [] then 4 else 2)
  have hr' := hr (seekTime+fuel)
  change Source284Relative.run _ _ _ = Source284SourceRelocation.lift 528
    (Source284Relative.run (encode (10+states) (table continuation) 1)
      ⟨2*(4*(4^(limit+1)*(2*frame))+1),inputFrame,active 0⟩ (seekTime+fuel)) at hr'
  let c : Config := ⟨2*(4*(4^(limit+1)*(2*frame))+1),inputFrame,some 0⟩
  have hc : Valid (10+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hv0 := run_toSource (10+states) (table continuation) 1 c (closed states continuation hn hv) hc (seekTime+fuel)
  change Source284Relative.run (encode (10+states) (table continuation) 1)
    ⟨2*(4*(4^(limit+1)*(2*frame))+1),inputFrame,active 0⟩ (seekTime+fuel) = _ at hv0
  rw [hv0,seek_then] at hr'
  let mode := if w = [] then 1 else 0
  let c' : Config := ⟨4^((limit+1)+1)*(4*inputFrame+1),frame,some mode⟩
  have hmode : mode < states := by dsimp [mode]; split <;> omega
  have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hmode
  have hv1 := run_toSource states continuation 1 c' hv hc' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨4^((limit+1)+1)*(4*inputFrame+1),frame,active mode⟩ fuel = _ at hv1
  rw [← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

/-- The branch-specific seek time is linear in the original cutoff and is
independent of the input, witness payload and high suffixes. -/
theorem seek_time_bound (limit : Nat) (w : List Bool) :
    3+2*((limit+1)+1)+(if w = [] then 4 else 2) ≤ 2*limit+11 := by
  split <;> omega

namespace Fixtures

/-- The original zero cutoff still has one tag pair. Empty and nonempty
frames reach different continuation modes without losing their delimiters. -/
example (continuation : Nat → Bool → Row) :
    run (table continuation) ⟨130,3,some 0⟩ 11 = ⟨208,2,some 11⟩ := by
  simpa [encodeFrame] using seek continuation 1 3 [] 0

example (continuation : Nat → Bool → Row) :
    run (table continuation) ⟨578,3,some 0⟩ 9 = ⟨208,9,some 10⟩ := by
  simpa [encodeFrame] using seek continuation 1 3 [false] 0

end Fixtures

end Shared.Beeping.NPcoNP.Source284WitnessSeek
