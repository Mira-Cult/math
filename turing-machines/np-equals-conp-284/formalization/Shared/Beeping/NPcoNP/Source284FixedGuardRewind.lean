import Shared.Beeping.NPcoNP.Source284FixedWitnessGuard
import Shared.Beeping.NPcoNP.Source284WindowRewind
import Shared.Beeping.NPcoNP.Source284HardwireTable

/-! A fixed-limit tagged-witness scan with a paid, tape-preserving rewind.
The limit is hardwired in the finite source table. This is not an
input-dependent cutoff, witness verifier, bit-cost bound, or physical beeper
refinement. State counts here are logical source states. -/
set_option maxRecDepth 4096

namespace Shared.Beeping.NPcoNP.Source284FixedGuardRewind

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284FixedWitnessGuard (scanner cutoff)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (transfer)

/-- Time and scanner mode in the forward segment. -/
def code (time mode : Nat) : Nat := 7*time+mode

def rewindTurn (m : Nat) : Nat := 7*cutoff m
def sink (m : Nat) : Nat := rewindTurn m+1
def rewindStart (m : Nat) : Nat := rewindTurn m+2
def width (m : Nat) : Nat := cutoff m-1
def handoff (m : Nat) : Nat := rewindStart m+width m
def states (m : Nat) : Nat := handoff m+1

def table (m q : Nat) (b : Bool) : Row :=
  if q < rewindTurn m then
    let r := scanner (q%7) b
    let target := r.next.getD 6
    ⟨r.write, r.turn, some (if q/7+1 < cutoff m then code (q/7+1) target
      else if target=3 then rewindTurn m else sink m)⟩
  else if q = rewindTurn m then ⟨b,true,some (rewindStart m)⟩
  else if rewindStart m ≤ q ∧ q < handoff m then ⟨b,false,some (q+1)⟩
  else ⟨b,false,some (sink m)⟩

theorem cutoff_pos (m : Nat) : 0 < cutoff m := by simp [cutoff]

theorem code_lt (m k q : Nat) (hk : k < cutoff m) (hq : q < 7) :
    code k q < rewindTurn m := by simp [code, rewindTurn]; omega

theorem code_div (k q : Nat) (hq : q < 7) : code k q / 7 = k := by
  simp [code]; omega

theorem code_mod (k q : Nat) (hq : q < 7) : code k q % 7 = q := by
  simp [code, Nat.add_mod, Nat.mod_eq_of_lt hq]

theorem scanner_next (q : Nat) (b : Bool) :
    (scanner q b).next = some ((scanner q b).next.getD 6) := by
  cases q with
  | zero => cases b <;> rfl
  | succ q =>
    cases q with
    | zero => cases b <;> rfl
    | succ q =>
      cases q with
      | zero => cases b <;> rfl
      | succ q =>
        cases q with
        | zero => cases b <;> rfl
        | succ q =>
          cases q with
          | zero => cases b <;> rfl
          | succ q =>
            cases q with
            | zero => cases b <;> rfl
            | succ q => cases b <;> rfl

theorem scanner_target_lt (q : Nat) (b : Bool) :
    (scanner q b).next.getD 6 < 7 := by
  cases q with
  | zero => cases b <;> decide
  | succ q =>
    cases q with
    | zero => cases b <;> decide
    | succ q =>
      cases q with
      | zero => cases b <;> decide
      | succ q =>
        cases q with
        | zero => cases b <;> decide
        | succ q =>
          cases q with
          | zero => cases b <;> decide
          | succ q =>
            cases q with
            | zero => cases b <;> decide
            | succ q => cases b <;> simp [scanner, Source284TaggedScanner.table]

theorem forward_row (m k q : Nat) (b : Bool) (hk : k < cutoff m) (hq : q < 7) :
    table m (code k q) b =
      let r := scanner q b
      ⟨r.write, r.turn, some (if k+1 < cutoff m then code (k+1) (r.next.getD 6)
        else if r.next.getD 6=3 then rewindTurn m else sink m)⟩ := by
  simp [table, code_lt m k q hk hq, code_div k q hq, code_mod k q hq]

theorem table_closed (m : Nat) : Closed (states m) (table m) := by
  intro q hq b q' hn
  by_cases hf : q < rewindTurn m
  · have htime : q/7 < cutoff m := by simp [rewindTurn] at hf; omega
    have htarget := scanner_target_lt (q%7) b
    unfold table at hn
    simp only [hf, ↓reduceIte, Option.some.injEq] at hn
    subst q'
    split_ifs <;> simp [states, handoff, rewindStart, rewindTurn, sink, code] at * <;> omega
  · by_cases ht : q = rewindTurn m
    · simp [table, ht] at hn
      subst q'
      simp [states,handoff,rewindStart]
    · by_cases hr : rewindStart m ≤ q ∧ q < handoff m
      · simp [table,hf,ht,hr] at hn
        subst q'
        simp [states]
        omega
      · simp [table,hf,ht,hr] at hn
        subst q'
        simp [states,handoff,rewindStart,rewindTurn,sink]; omega

def mapped (k : Nat) (c : Config) : Config :=
  ⟨c.left,c.right,c.state.map (code k)⟩

theorem mapped_step (m k : Nat) (c : Config)
    (hvalid : Valid 7 c) (hlive : c.state ≠ none) (hk : k+1 < cutoff m) :
    step (table m) (mapped k c) = mapped (k+1) (step scanner c) := by
  cases c with
  | mk l r s =>
    cases s with
    | none => simp at hlive
    | some q =>
      have hq := hvalid q rfl
      have hk' : k < cutoff m := by omega
      cases hn : (scanner q (r.testBit 0)).next with
      | none =>
        have h := scanner_next q (r.testBit 0)
        rw [hn] at h
        contradiction
      | some q' =>
        cases ht : (scanner q (r.testBit 0)).turn <;>
          simp only [Nat.testBit_zero] at hn ht <;>
          simp [mapped,step,forward_row m k q _ hk' hq,hk,hn,ht]

theorem scanner_live (c : Config) (h : c.state ≠ none) (k : Nat) :
    (run scanner c k).state ≠ none := by
  induction k with
  | zero => exact h
  | succ k ih =>
    cases hc : run scanner c k with
    | mk l r s =>
      cases s with
      | none => simp [hc] at ih
      | some q =>
        cases hn : (scanner q (r.testBit 0)).next with
        | none =>
          have h := scanner_next q (r.testBit 0)
          rw [hn] at h
          contradiction
        | some q' =>
          cases ht : (scanner q (r.testBit 0)).turn <;>
            simp only [Nat.testBit_zero] at hn ht <;>
            simp [run,hc,step,ht,hn]

theorem run_mapped (m : Nat) (c : Config) (hvalid : Valid 7 c)
    (hlive : c.state ≠ none) (k : Nat) (hk : k < cutoff m) :
    run (table m) (mapped 0 c) k = mapped k (run scanner c k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run, ih (by omega), mapped_step m k _
      (valid_run 7 scanner c Source284TaggedScanner.table_closed hvalid k)
      (scanner_live c hlive k) hk]
    rfl

theorem mapped_final (m k : Nat) (c : Config)
    (hvalid : Valid 7 c) (hlive : c.state ≠ none) (hk : k+1 = cutoff m) :
    step (table m) (mapped k c) =
      let x := step scanner c
      ⟨x.left,x.right,some (if x.state = some 3 then rewindTurn m else sink m)⟩ := by
  cases c with
  | mk l r s =>
    cases s with
    | none => simp at hlive
    | some q =>
      have hq := hvalid q rfl
      have hk' : k < cutoff m := by omega
      have hlast : ¬ k+1 < cutoff m := by omega
      cases hn : (scanner q (r.testBit 0)).next with
      | none =>
        have h := scanner_next q (r.testBit 0)
        rw [hn] at h
        contradiction
      | some q' =>
        cases ht : (scanner q (r.testBit 0)).turn <;>
          simp only [Nat.testBit_zero] at hn ht <;>
          simp [mapped,step,forward_row m k q _ hk' hq,hlast,hn,ht]

theorem width_succ (m : Nat) : width m+1 = cutoff m := by
  dsimp [width]
  have h := cutoff_pos m
  omega

/-- At the fixed cutoff, the wrapper has made exactly the scanner's tape
changes and routes its completed-frame mode to the rewind turn. -/
theorem run_cutoff (m c i : Nat) :
    let x := run scanner ⟨c,i,some 0⟩ (cutoff m)
    run (table m) ⟨c,i,some 0⟩ (cutoff m) =
      ⟨x.left,x.right,some (if x.state = some 3 then rewindTurn m else sink m)⟩ := by
  dsimp only
  let start : Config := ⟨c,i,some 0⟩
  have hv : Valid 7 start := by
    intro q hq; simp only [start,Option.some.injEq] at hq; omega
  have hl : start.state ≠ none := by simp [start]
  have hlt : width m < cutoff m := by have h := width_succ m; omega
  have hm := run_mapped m start hv hl (width m) hlt
  have hs : mapped 0 start = start := by simp [mapped,start,code]
  rw [hs] at hm
  have hf := mapped_final m (width m) (run scanner start (width m))
    (valid_run 7 scanner start Source284TaggedScanner.table_closed hv (width m))
    (scanner_live start hl (width m)) (width_succ m)
  have hr : step scanner (run scanner start (width m)) = run scanner start (cutoff m) := by
    rw [← width_succ m]
    rfl
  calc
    run (table m) start (cutoff m) = step (table m) (run (table m) start (width m)) := by
      rw [← width_succ m]
      rfl
    _ = step (table m) (mapped (width m) (run scanner start (width m))) := by rw [hm]
    _ = _ := by simpa [hr] using hf

/-- The scanner reaches completed-frame mode exactly for accepted tagged
window codes, with arbitrary high bits still present. -/
theorem scanner_completed_iff (m c i : Nat) :
    (run scanner ⟨c,i,some 0⟩ (cutoff m)).state = some 3 ↔
      Source284TaggedWitnessCodec.decode m c ≠ none := by
  have hs := Source284FixedWitnessGuard.scanner_final_states m c i
  have hr := Source284FixedWitnessGuard.scanner_reject m c i
  dsimp only at hs
  rcases hs with hs | hs | hs
  · have hn := hr.mp (Or.inl hs)
    simp [hs,hn]
  · have hn : Source284TaggedWitnessCodec.decode m c ≠ none := by
      intro h
      rcases hr.mpr h with he | he <;> rw [hs] at he <;> contradiction
    simp [hs,hn]
  · have hn := hr.mp (Or.inr hs)
    simp [hs,hn]

theorem scanner_target_pos (q : Nat) (b : Bool) (hq : 1 ≤ q) :
    1 ≤ (scanner q b).next.getD 6 := by
  cases q with
  | zero => omega
  | succ q =>
    cases q with
    | zero => cases b <;> decide
    | succ q =>
      cases q with
      | zero => cases b <;> decide
      | succ q =>
        cases q with
        | zero => cases b <;> decide
        | succ q =>
          cases q with
          | zero => cases b <;> decide
          | succ q =>
            cases q with
            | zero => cases b <;> decide
            | succ q => cases b <;> simp [scanner,Source284TaggedScanner.table]

/-- Once on the certificate half, every scanner step copies exactly one bit
and remains in a positive mode, including its invalid-tag sink. -/
theorem scanner_transfer (k q left right : Nat) (hq : 1 ≤ q) :
    ∃ q', 1 ≤ q' ∧
      run scanner ⟨left,right,some q⟩ k =
        ⟨(transfer k left right).1,(transfer k left right).2,some q'⟩ := by
  induction k generalizing q left right with
  | zero => exact ⟨q,hq,rfl⟩
  | succ k ih =>
    let q' := (scanner q (right.testBit 0)).next.getD 6
    have hn : (scanner q (right.testBit 0)).next = some q' := scanner_next q _
    have hq' : 1 ≤ q' := scanner_target_pos q _ hq
    have hstep := Source284TaggedScanner.tag_step q left right hq
    change step scanner ⟨left,right,some q⟩ =
      ⟨2*left+right%2,right/2,(scanner q (right.testBit 0)).next⟩ at hstep
    rw [hn] at hstep
    rw [Shared.Beeping.NPcoNP.Source284HardwireTable.run_front, hstep]
    obtain ⟨target,htarget,hr⟩ := ih q' (2*left+right%2) (right/2) hq'
    exact ⟨target,htarget,by simpa [transfer] using hr⟩

/-- The forward scan's halves are the exact fixed-width transfer of the full
certificate, preserving arbitrary high bits and the opposite input half. -/
theorem scanner_cutoff_tapes (m c i : Nat) :
    let x := run scanner ⟨c,i,some 0⟩ (cutoff m)
    x.left = (transfer (width m) i c).1 ∧
    x.right = (transfer (width m) i c).2 := by
  dsimp only
  have htime : cutoff m = 1+width m := by have h := width_succ m; omega
  simp only [htime, Source284TaggedScanner.run_add]
  change (run scanner (step scanner ⟨c,i,some 0⟩) (width m)).left = _ ∧
    (run scanner (step scanner ⟨c,i,some 0⟩) (width m)).right = _
  rw [Source284TaggedScanner.initial_turn]
  obtain ⟨q,hq,hr⟩ := scanner_transfer (width m) 4 i c (by omega)
  rw [hr]
  exact ⟨rfl,rfl⟩

theorem turn_row (m : Nat) (b : Bool) :
    table m (rewindTurn m) b = ⟨b,true,some (rewindStart m)⟩ := by
  simp [table]

theorem rewind_row (m j : Nat) (hj : j < width m) (b : Bool) :
    table m (rewindStart m+j) b = ⟨b,false,some (rewindStart m+j+1)⟩ := by
  have hf : ¬ rewindStart m+j < rewindTurn m := by simp [rewindStart]; omega
  have ht : rewindStart m+j ≠ rewindTurn m := by simp [rewindStart]; omega
  have hh : rewindStart m+j < handoff m := by simp [handoff]; omega
  simp [table,hf,ht,hh]

theorem sink_row (m : Nat) (b : Bool) :
    table m (sink m) b = ⟨b,false,some (sink m)⟩ := by
  have hf : ¬ sink m < rewindTurn m := by simp [sink]
  have ht : sink m ≠ rewindTurn m := by simp [sink]
  have hr : ¬ rewindStart m ≤ sink m := by simp [rewindStart,sink]
  simp [table,hf,ht,hr]

theorem sink_run (m : Nat) (c : Config) (h : c.state = some (sink m)) (k : Nat) :
    (run (table m) c k).state = some (sink m) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    cases hc : run (table m) c k with
    | mk left right state =>
      have hs : state = some (sink m) := by simpa [hc] using ih
      subst state
      simp [run,hc,step,sink_row]

def duration (m : Nat) : Nat := cutoff m+1+width m

/-- On a valid tagged window, the actual finite table returns to the original
input/certificate boundary, with both complete numeric halves unchanged. -/
theorem run_rewind (m c i : Nat)
    (hgood : Source284TaggedWitnessCodec.decode m c ≠ none) :
    run (table m) ⟨c,i,some 0⟩ (duration m) = ⟨c,i,some (handoff m)⟩ := by
  let p := transfer (width m) i c
  let x := run scanner ⟨c,i,some 0⟩ (cutoff m)
  have hx := scanner_cutoff_tapes m c i
  change x.left = p.1 ∧ x.right = p.2 at hx
  have hs : x.state = some 3 := (scanner_completed_iff m c i).mpr hgood
  have hcut : run (table m) ⟨c,i,some 0⟩ (cutoff m) =
      ⟨p.1,p.2,some (rewindTurn m)⟩ := by
    have h := run_cutoff m c i
    change run (table m) ⟨c,i,some 0⟩ (cutoff m) =
      ⟨x.left,x.right,some (if x.state = some 3 then rewindTurn m else sink m)⟩ at h
    simpa [hx.1,hx.2,hs] using h
  have hturn : run (table m) ⟨p.1,p.2,some (rewindTurn m)⟩ 1 =
      ⟨p.2,p.1,some (rewindStart m)⟩ := by
    simpa [run] using Source284WindowRewind.generic_turn (table m) _ _ _ _ (turn_row m)
  have hrows : ∀ j < width m, ∀ b,
      table m (rewindStart m+j) b = ⟨b,false,some (rewindStart m+j+1)⟩ := by
    intro j hj b
    exact rewind_row m j hj b
  have hscan := Source284WindowRewind.generic_scan (table m) (rewindStart m)
    (width m) p.2 p.1 hrows
  have hp : transfer (width m) p.2 p.1 = (c,i) := by
    simpa [p] using Source284TransferInvolution.transfer_involution (width m) i c
  rw [hp] at hscan
  rw [show duration m = cutoff m+1+width m by rfl,
    Source284WindowRewind.run_add_generic,Source284WindowRewind.run_add_generic,
    hcut, hturn]
  simpa [handoff] using hscan

/-- Rejected windows reach the sink at the fixed cutoff and remain there. -/
theorem run_reject (m c i extra : Nat)
    (hbad : Source284TaggedWitnessCodec.decode m c = none) :
    (run (table m) ⟨c,i,some 0⟩ (cutoff m+extra)).state = some (sink m) := by
  have hs : (run scanner ⟨c,i,some 0⟩ (cutoff m)).state ≠ some 3 := by
    intro h
    exact ((scanner_completed_iff m c i).mp h) hbad
  rw [Source284WindowRewind.run_add_generic,run_cutoff]
  apply sink_run
  simp [hs]

/-- Encoded source execution reaches the continuing handoff with the entire
input and certificate restored; arbitrary unused description tails are allowed. -/
theorem source_rewind (m c i tail : Nat)
    (hgood : Source284TaggedWitnessCodec.decode m c ≠ none) :
    Source284Relative.run (encode (states m) (table m) tail)
      (Source284Relative.initial i c) (duration m) = ⟨c,i,active (handoff m)⟩ := by
  have hv : Valid (states m) ⟨c,i,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    simp [states,handoff,rewindStart,rewindTurn]
  have h := run_toSource (states m) (table m) tail ⟨c,i,some 0⟩
    (table_closed m) hv (duration m)
  change Source284Relative.run (encode (states m) (table m) tail)
    (Source284Relative.initial i c) _ = _ at h
  rw [h,run_rewind m c i hgood]
  rfl

theorem source_reject (m c i tail extra : Nat)
    (hbad : Source284TaggedWitnessCodec.decode m c = none) :
    (Source284Relative.run (encode (states m) (table m) tail)
      (Source284Relative.initial i c) (cutoff m+extra)).state = active (sink m) := by
  have hv : Valid (states m) ⟨c,i,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    simp [states,handoff,rewindStart,rewindTurn]
  have h := run_toSource (states m) (table m) tail ⟨c,i,some 0⟩
    (table_closed m) hv (cutoff m+extra)
  change Source284Relative.run (encode (states m) (table m) tail)
    (Source284Relative.initial i c) _ = _ at h
  rw [h]
  simp [toSource,nextState,run_reject m c i extra hbad]

theorem state_count (m : Nat) : states m = 16*m+34 := by
  have hw : width m = 2*m+3 := by simp [width,cutoff]
  simp [states,handoff,rewindStart,rewindTurn,cutoff,hw]
  omega

theorem duration_exact (m : Nat) : duration m = 4*m+8 := by
  have hw : width m = 2*m+3 := by simp [width,cutoff]
  simp [duration,cutoff,hw]
  omega

/-- Exactly the successfully decoded certificates reach the handoff at the
published boundary; malformed and overlong windows remain in the sink. -/
theorem source_handoff_iff (m c i tail : Nat) :
    (Source284Relative.run (encode (states m) (table m) tail)
      (Source284Relative.initial i c) (duration m)).state = active (handoff m) ↔
      Source284TaggedWitnessCodec.decode m c ≠ none := by
  by_cases h : Source284TaggedWitnessCodec.decode m c = none
  · have hs := source_reject m c i tail (1+width m) h
    have ht : cutoff m+(1+width m) = duration m := by simp [duration]; omega
    rw [ht] at hs
    have hne : active (sink m) ≠ active (handoff m) := by
      simp [active,sink,handoff,rewindStart,rewindTurn,width,cutoff]
      omega
    simp [h,hs,hne]
  · have hs := source_rewind m c i tail h
    simp [h,hs]

theorem record_count (m : Nat) :
    (records (states m) (table m)).length = 2*(16*m+34) := by
  have h : (records (states m) (table m)).length = 2*states m := by simp [records]
  rw [h,state_count]

-- Small kernel-checked fixtures cover empty and one-bit witnesses, high-bit
-- aliases, invalid tags, overlong witnesses, and a nonzero input half.
example : run (table 0) ⟨0,7,some 0⟩ (duration 0) = ⟨0,7,some (handoff 0)⟩ := by
  apply run_rewind
  decide +kernel
example : run (table 1) ⟨68,9,some 0⟩ (duration 1) = ⟨68,9,some (handoff 1)⟩ := by
  apply run_rewind
  decide +kernel
example : (run (table 0) ⟨1,7,some 0⟩ (cutoff 0+5)).state = some (sink 0) := by
  apply run_reject
  decide +kernel
example : (run (table 0) ⟨4,7,some 0⟩ (cutoff 0+5)).state = some (sink 0) := by
  apply run_reject
  decide +kernel

end Shared.Beeping.NPcoNP.Source284FixedGuardRewind
