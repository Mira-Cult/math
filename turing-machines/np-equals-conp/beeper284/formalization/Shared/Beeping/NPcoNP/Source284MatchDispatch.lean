import Shared.Beeping.NPcoNP.Source284PayloadMarkLoop

/-! Two-entry finite dispatch to two copies of the payload scanner. The
separate entries retain the unary scanner's success/exhaustion result; the
four exit states additionally record the payload result. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace Shared.Beeping.NPcoNP.Source284MatchDispatch

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284PayloadMarkLoop (base)

/-- Entry 0 denotes an available unary token; entry 1 denotes exhaustion.
Each dispatch transition performs the payload scanner's actual first step.
The two copies return to distinct pairs of continuation entries. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨true,false,some 3⟩
  else if q = 1 then ⟨true,false,some 20⟩
  else if q < 19 then
    if q = 16 then ⟨b,true,some 36⟩
    else if q = 17 then ⟨b,true,some 37⟩
    else shiftRow 2 (base (q-2) b)
  else if q < 36 then
    if q = 33 then ⟨b,true,some 38⟩
    else if q = 34 then ⟨b,true,some 39⟩
    else shiftRow 19 (base (q-19) b)
  else shiftRow 36 (continuation (q-36) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 4 ≤ states) (hv : Closed states continuation) : Closed (36+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hsmall : q < 36
  · interval_cases q <;> cases b <;>
      simp [table,base,Source284PayloadMarkOne.table,Source284PayloadMarkLoop.sink,shiftRow] at hnext <;> omega
  · have h0 : q ≠ 0 := by omega
    have h1 : q ≠ 1 := by omega
    have h19 : ¬q < 19 := by omega
    have h36 : ¬q < 36 := by omega
    have ht : (shiftRow 36 (continuation (q-36) b)).next = some q' := by
      simpa [table,h0,h1,h19,h36] using hnext
    have hq0 : q-36 < states := by omega
    cases he : (continuation (q-36) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-36) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (36+q) b = shiftRow 36 (continuation q b) := by
  have h0 : 36+q ≠ 0 := by omega
  have h1 : 36+q ≠ 1 := by omega
  have h19 : ¬36+q < 19 := by omega
  have h36 : ¬36+q < 36 := by omega
  simp [table,h0,h1,h19,h36]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 36 c) = shiftConfig 36 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 36 c) fuel = shiftConfig 36 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

def offset (mode : Nat) : Nat := if mode = 0 then 2 else 19

theorem copied_row (continuation : Nat → Bool → Row) (mode q : Nat) (hm : mode < 2)
    (hq : q < 17) (h14 : q ≠ 14) (h15 : q ≠ 15) (b : Bool) :
    table continuation (offset mode+q) b = shiftRow (offset mode) (base q b) := by
  interval_cases mode <;> interval_cases q <;> simp_all [table,offset]

theorem entry (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (certificate stream : Nat) :
    step (table continuation) ⟨certificate,2*stream,some mode⟩ =
      shiftConfig (offset mode) (step base ⟨certificate,2*stream,some 0⟩) := by
  interval_cases mode <;>
    simp [table,offset,step,base,Source284PayloadMarkOne.table,shiftConfig,shiftRow,bit,Nat.testBit_zero]

theorem copied_step (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (c : Config) (hrows : ∀ q, c.state = some q → q < 17 ∧ q ≠ 14 ∧ q ≠ 15) :
    step (table continuation) (shiftConfig (offset mode) c) =
      shiftConfig (offset mode) (step base c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq := hrows q rfl
      simp only [shiftConfig,Option.map_some,step,copied_row continuation mode q hm hq.1 hq.2.1 hq.2.2,shiftRow]
      split <;> rfl

theorem copied_run (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 17 ∧ q ≠ 14 ∧ q ≠ 15) :
    run (table continuation) (shiftConfig (offset mode) c) fuel =
      shiftConfig (offset mode) (run base c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, (run base c t).state = some q → q < 17 ∧ q ≠ 14 ∧ q ≠ 15 := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    apply copied_step continuation mode hm
    intro q hq
    exact hrows fuel (by omega) q hq

/-- At either final row, the copied scanner returns to the appropriate one
of four continuations without changing its write or movement. -/
theorem final_success (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (stream certificate : Nat) :
    step (table continuation) (shiftConfig (offset mode) ⟨2*stream,certificate,some 14⟩) =
      ⟨certificate,2*stream,some (36+2*mode)⟩ := by
  interval_cases mode <;> simp [table,offset,shiftConfig,step,bit,Nat.testBit_zero] <;>
    split_ifs <;> omega

theorem final_exhausted (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (stream certificate : Nat) :
    step (table continuation) (shiftConfig (offset mode) ⟨2*stream,certificate,some 15⟩) =
      ⟨certificate,2*stream,some (37+2*mode)⟩ := by
  interval_cases mode <;> simp [table,offset,shiftConfig,step,bit,Nat.testBit_zero] <;>
    split_ifs <;> omega

/-- Dispatch and the reference scanner agree up to either final row. -/
theorem to_pre (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (certificate stream limit final : Nat) (hpos : 0 < limit) (hfinal : final = 14 ∨ final = 15)
    (hfinish : (run base ⟨certificate,2*stream,some 0⟩ limit).state = some final) :
    run (table continuation) ⟨certificate,2*stream,some mode⟩ limit =
      shiftConfig (offset mode) (run base ⟨certificate,2*stream,some 0⟩ limit) := by
  let c : Config := ⟨certificate,2*stream,some 0⟩
  have hc : Valid 19 c := by intro q hq; simp [c] at hq; subst q; omega
  have hc1 : Valid 19 (step base c) := valid_step 19 base c Source284PayloadMarkLoop.base_closed hc
  have ht : limit = 1+(limit-1) := by omega
  have hp : run base c limit = run base (step base c) (limit-1) := by
    conv_lhs => rw [ht,run_add]
    rfl
  have hf : (run base (step base c) (limit-1)).state = some final := by
    rw [← hp]
    exact hfinish
  have hr := Source284PayloadMarkLoop.avoid_before_final (step base c) (limit-1) final hc1 hfinal hf
  conv_lhs => rw [ht,run_add]
  change run (table continuation)
    (step (table continuation) ⟨certificate,2*stream,some mode⟩) (limit-1) = _
  rw [entry continuation mode hm,copied_run continuation mode hm _ _ hr]
  exact congrArg (shiftConfig (offset mode)) hp.symm

/-- Both unary-result entries mark the next payload pair and select their
own success continuation. -/
theorem mark (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (xs ys : List Bool) (b c : Bool) (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*zeros xs (flipped (b::c::ys) tail),some mode⟩
      (4*xs.length+10) =
      ⟨certificate,2*zeros (xs++[b]) (flipped (c::ys) tail),some (36+2*mode)⟩ := by
  let limit := 4*xs.length+9
  have hp := Source284PayloadMarkLoop.mark_pre xs ys b c certificate tail
  have hf : (run base ⟨certificate,2*zeros xs (flipped (b::c::ys) tail),some 0⟩ limit).state = some 14 := by
    rw [hp]
  have ha := to_pre continuation mode hm certificate (zeros xs (flipped (b::c::ys) tail))
    limit 14 (by dsimp [limit]; omega) (Or.inl rfl) hf
  have ht : 4*xs.length+10 = limit+1 := by dsimp [limit]
  rw [ht,run,ha,hp,final_success continuation mode hm]

/-- Both unary-result entries detect the payload sentinel and select their
own exhaustion continuation without changing the tape. -/
theorem exhausted (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (xs : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*zeros xs (flipped [false] tail),some mode⟩
      (4*xs.length+10) =
      ⟨certificate,2*zeros xs (flipped [false] tail),some (37+2*mode)⟩ := by
  let limit := 4*xs.length+9
  have hp := Source284PayloadMarkLoop.exhausted_pre xs certificate tail
  have hf : (run base ⟨certificate,2*zeros xs (flipped [false] tail),some 0⟩ limit).state = some 15 := by
    rw [hp]
  have ha := to_pre continuation mode hm certificate (zeros xs (flipped [false] tail))
    limit 15 (by dsimp [limit]; omega) (Or.inr rfl) hf
  have ht : 4*xs.length+10 = limit+1 := by dsimp [limit]
  rw [ht,run,ha,hp,final_exhausted continuation mode hm]

end Shared.Beeping.NPcoNP.Source284MatchDispatch
