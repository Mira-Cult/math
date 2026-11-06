import Shared.Beeping.NPcoNP.Source284ScratchShiftLoop

/-! A finite source table with a tape-controlled unary stopping condition.
The counter is explicitly supplied in the high scratch suffix: one bits
continue and the first zero exits after that cycle. Preparing this counter
from an original input is a separate loader obligation. -/
namespace Shared.Beeping.NPcoNP.Source284CountedShift

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284ScratchShift (written)
open Shared.Beeping.NPcoNP.Source284ScratchShiftLoop (base)

/-- Read the consumed high-suffix bit at the shifter's flush. One chooses the
ordinary return-to-start path; zero chooses a separate return-to-continuation
path. Both paths make the same write and turn. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 5 then ⟨false,true,some (if b then 7 else 14)⟩
  else if q < 7 then base q b
  else if q < 14 then
    if q = 13 then let r := base q b; ⟨r.write,r.turn,some 0⟩ else base q b
  else shiftRow 14 (Source284ScratchShiftReturn.table continuation (q-14) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (21+states) (table continuation) := by
  have hc := Source284ScratchShiftReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h5 : q = 5
  · subst q; cases b <;> simp [table] at hnext <;> omega
  · by_cases h7 : q < 7
    · have hb := Source284ScratchShiftLoop.base_closed q (by omega) b q'
      have he : (base q b).next = some q' := by simpa [table,h5,h7] using hnext
      have h := hb he
      omega
    · by_cases h14 : q < 14
      · by_cases h13 : q = 13
        · subst q; simp [table] at hnext; omega
        · have hb := Source284ScratchShiftLoop.base_closed q (by omega) b q'
          have he : (base q b).next = some q' := by simpa [table,h5,h7,h14,h13] using hnext
          have h := hb he
          omega
      · have ht : (shiftRow 14 (Source284ScratchShiftReturn.table continuation (q-14) b)).next = some q' := by
          simpa [table,h5,h7,h14] using hnext
        have hq0 : q-14 < 7+states := by omega
        cases he : (Source284ScratchShiftReturn.table continuation (q-14) b).next with
        | none => simp [shiftRow,he] at ht
        | some r =>
          have h := hc (q-14) hq0 b r he
          simp [shiftRow,he] at ht
          subst q'
          omega

/-- Once the reference cycle reaches the return region, its finite rows stay
there until they reach the absorbing reference sink. -/
theorem zone_rows : ∀ q : Fin 15, 7 ≤ q.val → ∀ b : Bool,
    7 ≤ (base q.val b).next.getD 0 := by decide +kernel

theorem flush_next : ∀ b : Bool, (base 5 b).next = some 7 := by decide +kernel

theorem zone_step (c : Config) (hvalid : Valid 15 c)
    (hzone : ∃ q, c.state = some q ∧ 7 ≤ q) :
    ∃ q, (step base c).state = some q ∧ 7 ≤ q := by
  rcases c with ⟨left,right,state⟩
  obtain ⟨q,hq,hge⟩ := hzone
  simp only at hq
  subst state
  have hbound := hvalid q rfl
  have hz := zone_rows ⟨q,hbound⟩ hge (right.testBit 0)
  simp only [Nat.testBit_zero] at hz
  cases he : (base q (decide (right%2 = 1))).next with
  | none => simp [he] at hz
  | some r =>
    have hr : 7 ≤ r := by simpa [he] using hz
    refine ⟨r,?_,hr⟩
    simp [step,Nat.testBit_zero,he]
    split <;> simp [he]

theorem zone_run (c : Config) (hvalid : Valid 15 c)
    (hzone : ∃ q, c.state = some q ∧ 7 ≤ q) (fuel : Nat) :
    ∃ q, (run base c fuel).state = some q ∧ 7 ≤ q := by
  induction fuel with
  | zero => exact hzone
  | succ fuel ih =>
    exact zone_step _ (valid_run 15 base c Source284ScratchShiftLoop.base_closed hvalid fuel) ih

theorem flush_step (c : Config) (h : c.state = some 5) :
    (step base c).state = some 7 := by
  cases c with
  | mk left right state =>
    simp only at h
    subst state
    have hr := flush_next (right.testBit 0)
    simp only [Nat.testBit_zero] at hr
    simp [step,hr]
    split <;> simp [hr]

/-- The existing cycle is exactly at its flush row after this finite prefix. -/
theorem preflush (w : List Bool) (certificate tail : Nat) :
    run base ⟨certificate,2*flipped w tail,some 0⟩ (2*w.length+3) =
      ⟨payloadFold (2*certificate) (written false w),tail,some 5⟩ := by
  have ht : 2*w.length+3 = (2*w.length+2)+1 := by omega
  rw [ht,Source284HardwireTable.run_front]
  change run (Source284ScratchShiftPipeline.entry
    (Source284ScratchShiftReturn.table Source284ScratchShiftLoop.sink))
    (step (Source284ScratchShiftPipeline.entry
      (Source284ScratchShiftReturn.table Source284ScratchShiftLoop.sink)) _ ) _ = _
  rw [Source284ScratchShiftPipeline.entry_step]
  change run (Source284ScratchShiftPipeline.entry
    (Source284ScratchShiftReturn.table Source284ScratchShiftLoop.sink))
    (shiftConfig 1 ⟨2*certificate,flipped w tail,some 0⟩) _ = _
  rw [Source284ScratchShiftPipeline.relocated_run]
  have hs := Source284ScratchShift.scan (Source284ScratchShiftReturn.table Source284ScratchShiftLoop.sink)
    false w (2*certificate) tail
  change run (Source284ScratchShift.table (Source284ScratchShiftReturn.table Source284ScratchShiftLoop.sink))
    ⟨2*certificate,flipped w tail,some 0⟩ (2*w.length+2) =
    ⟨payloadFold (2*certificate) (written false w),tail,some 4⟩ at hs
  rw [hs]
  rfl

/-- Before the first flush, the reference cycle is in neither the flush row
nor the return region. -/
theorem avoid_before_flush (c : Config) (hvalid : Valid 15 c) (limit : Nat)
    (hfinal : (run base c limit).state = some 5) :
    ∀ t < limit, ∀ q, (run base c t).state = some q → q < 7 ∧ q ≠ 5 := by
  intro t ht q hq
  have hvt := valid_run 15 base c Source284ScratchShiftLoop.base_closed hvalid t
  have hlt : q < 7 := by
    by_contra h
    have hz := zone_run (run base c t) hvt ⟨q,hq,by omega⟩ (limit-t)
    rw [← Source284PayloadPop.run_add] at hz
    have he : t+(limit-t) = limit := by omega
    rw [he,hfinal] at hz
    obtain ⟨r,hr,hge⟩ := hz
    have : r = 5 := (Option.some.inj hr).symm
    omega
  refine ⟨hlt,?_⟩
  intro heq
  subst q
  have hs : (run base c (t+1)).state = some 7 := by
    simp only [run]
    exact flush_step _ hq
  have hvnext := valid_run 15 base c Source284ScratchShiftLoop.base_closed hvalid (t+1)
  have hz := zone_run (run base c (t+1)) hvnext ⟨7,hs,by omega⟩ (limit-(t+1))
  rw [← Source284PayloadPop.run_add] at hz
  have he : t+1+(limit-(t+1)) = limit := by omega
  rw [he,hfinal] at hz
  obtain ⟨r,hr,hge⟩ := hz
  have : r = 5 := (Option.some.inj hr).symm
  omega

/-- Tables agree on all rows actually visited by the reference run. -/
theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, (run base c t).state = some q →
      table continuation q ((run base c t).right.testBit 0) =
        base q ((run base c t).right.testBit 0)) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, (run base c t).state = some q →
        table continuation q ((run base c t).right.testBit 0) =
          base q ((run base c t).right.testBit 0) := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hs := hrows fuel (by omega) q (by simp [hc])
        simp only [hc] at hs
        simp only [Nat.testBit_zero] at hs
        simp [step,hs]

/-- The actual counter-sensitive table reaches its branch point in the same
positive finite time as the reference shift. -/
theorem reaches_flush (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*flipped w tail,some 0⟩ (2*w.length+3) =
      ⟨payloadFold (2*certificate) (written false w),tail,some 5⟩ := by
  let c : Config := ⟨certificate,2*flipped w tail,some 0⟩
  let limit := 2*w.length+3
  have hv : Valid 15 c := by intro q hq; simp [c] at hq; subst q; decide
  have hp : run base c limit = ⟨payloadFold (2*certificate) (written false w),tail,some 5⟩ :=
    preflush w certificate tail
  have hf : (run base c limit).state = some 5 := by rw [hp]
  have ha := avoid_before_flush c hv limit hf
  have hrows : ∀ t < limit, ∀ q, (run base c t).state = some q →
      table continuation q ((run base c t).right.testBit 0) =
        base q ((run base c t).right.testBit 0) := by
    intro t ht q hq
    obtain ⟨hlt,hne⟩ := ha t ht q hq
    simp [table,hne,hlt]
  change run (table continuation) c limit = _
  rw [run_agree continuation c limit hrows,hp]

theorem stop_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (14+q) b =
      shiftRow 14 (Source284ScratchShiftReturn.table continuation q b) := by
  have h5 : 14+q ≠ 5 := by omega
  have h7 : ¬ 14+q < 7 := by omega
  have h14 : ¬ 14+q < 14 := by omega
  simp [table,h5,h7,h14]

theorem stop_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 14 c) =
      shiftConfig 14 (step (Source284ScratchShiftReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,stop_row,shiftRow]
      split <;> rfl

theorem stop_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 14 c) fuel =
      shiftConfig 14 (run (Source284ScratchShiftReturn.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,stop_step]

theorem flush_zero (continuation : Nat → Bool → Row) (left higher : Nat) :
    step (table continuation) ⟨left,2*higher,some 5⟩ = ⟨2*higher,left,some 14⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem flush_one (continuation : Nat → Bool → Row) (left higher : Nat) :
    step (table continuation) ⟨left,2*higher+1,some 5⟩ = ⟨2*higher,left,some 7⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

/-- A zero counter bit takes the paid return path into the supplied finite
continuation, preserving all higher suffix bits. -/
theorem iteration_stop (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate higher : Nat) :
    run (table continuation) ⟨certificate,2*flipped w (2*higher),some 0⟩ (4*w.length+7) =
      ⟨2*certificate,2*flipped w higher,some 21⟩ := by
  have ht : 4*w.length+7 = (2*w.length+3)+(1+(2*w.length+3)) := by omega
  rw [ht,Source284PayloadPop.run_add _ _ (2*w.length+3) (1+(2*w.length+3)),reaches_flush]
  rw [Source284PayloadPop.run_add _ _ 1 (2*w.length+3)]
  change run (table continuation)
    (step (table continuation) ⟨payloadFold (2*certificate) (written false w),2*higher,some 5⟩) _ = _
  rw [flush_zero]
  change run (table continuation)
    (shiftConfig 14 ⟨2*higher,payloadFold (2*certificate) (written false w),some 0⟩) _ = _
  rw [stop_run]
  have hret := Source284ScratchShiftReturn.return_frame continuation w certificate (2*higher)
  have hd : (2*higher)/2 = higher := by omega
  rw [hd] at hret
  rw [hret]
  rfl

/-- The reference return reaches its final row in a finite number of steps. -/
theorem return_zone_pre (w : List Bool) (certificate tail : Nat) :
    run base ⟨2*(tail/2),payloadFold (2*certificate) (written false w),some 7⟩ (2*w.length+2) =
      ⟨2*flipped w (tail/2),2*certificate,some 13⟩ := by
  change run (Source284ScratchShiftPipeline.entry
    (Source284ScratchShiftReturn.table Source284ScratchShiftLoop.sink))
    (shiftConfig 1 (shiftConfig 6 ⟨2*(tail/2),payloadFold (2*certificate)
      (written false w),some 0⟩)) _ = _
  rw [Source284ScratchShiftPipeline.relocated_run,Source284ScratchShift.relocated_run,
    Source284ScratchShiftLoop.return_pre]
  rfl

theorem return_prefix (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨2*(tail/2),payloadFold (2*certificate) (written false w),some 7⟩
      (2*w.length+2) = ⟨2*flipped w (tail/2),2*certificate,some 13⟩ := by
  let c : Config := ⟨2*(tail/2),payloadFold (2*certificate) (written false w),some 7⟩
  let limit := 2*w.length+2
  have hv : Valid 15 c := by intro q hq; simp [c] at hq; subst q; decide
  have hp : run base c limit = ⟨2*flipped w (tail/2),2*certificate,some 13⟩ :=
    return_zone_pre w certificate tail
  have hf : (run base c limit).state = some 13 := by rw [hp]
  have havoid := Source284ScratchShiftLoop.avoid_before_final c limit hf
  have hrows : ∀ t < limit, ∀ q, (run base c t).state = some q →
      table continuation q ((run base c t).right.testBit 0) =
        base q ((run base c t).right.testBit 0) := by
    intro t ht q hq
    have hbound := (valid_run 15 base c Source284ScratchShiftLoop.base_closed hv t) q hq
    have hz := zone_run c hv ⟨7,by rfl,by decide⟩ t
    obtain ⟨r,hr,hge⟩ := hz
    rw [hq] at hr
    have he : r = q := (Option.some.inj hr).symm
    subst r
    have hne13 : q ≠ 13 := by intro he; subst q; exact havoid t ht hq
    have hne14 : q ≠ 14 := by
      intro he
      subst q
      have hs := Source284ScratchShiftLoop.sink_run (run base c t) hq (limit-t)
      rw [← Source284PayloadPop.run_add] at hs
      have he : t+(limit-t) = limit := by omega
      rw [he,hf] at hs
      contradiction
    have h5 : q ≠ 5 := by omega
    have h7 : ¬ q < 7 := by omega
    have h14 : q < 14 := by omega
    simp [table,h5,h7,h14,hne13]
  change run (table continuation) c limit = _
  rw [run_agree continuation c limit hrows,hp]

theorem redirected_final (continuation : Nat → Bool → Row) (left certificate : Nat) :
    step (table continuation) ⟨2*left,2*certificate,some 13⟩ =
      ⟨2*certificate,2*left,some 0⟩ := by
  simp [step,table,base,Source284ScratchShiftCycle.table,Source284ScratchShiftPipeline.entry,
    Source284ScratchShift.table,Source284ScratchShiftReturn.table,Source284ScratchFlipReturn.table,
    shiftRow,bit,Nat.testBit_zero]

/-- A one counter bit returns to the loop start with the next counter bit
now in the low suffix cell. -/
theorem iteration_continue (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate higher : Nat) :
    run (table continuation) ⟨certificate,2*flipped w (2*higher+1),some 0⟩ (4*w.length+7) =
      ⟨2*certificate,2*flipped w higher,some 0⟩ := by
  have ht : 4*w.length+7 = (2*w.length+3)+(1+((2*w.length+2)+1)) := by omega
  rw [ht,Source284PayloadPop.run_add _ _ (2*w.length+3) (1+((2*w.length+2)+1)),reaches_flush]
  rw [Source284PayloadPop.run_add _ _ 1 ((2*w.length+2)+1)]
  change run (table continuation)
    (step (table continuation) ⟨payloadFold (2*certificate) (written false w),2*higher+1,some 5⟩) _ = _
  rw [flush_one]
  have hd : (2*higher+1)/2 = higher := by omega
  have hp := return_prefix continuation w certificate (2*higher+1)
  rw [hd] at hp
  rw [Source284PayloadPop.run_add,hp]
  exact redirected_final continuation _ _

/-- Low-endian `count` one bits, followed by a zero and the untouched high
suffix. This is tape data, not a parameter compiled into the transition table. -/
def counter : Nat → Nat → Nat
  | 0, higher => 2*higher
  | count+1, higher => 2*counter count higher+1

/-- The single finite table consumes every unary counter and reaches the
continuation. The terminating zero itself causes one final shift, so a
counter with `count` ones performs exactly `count+1` cycles. -/
theorem countdown (continuation : Nat → Bool → Row) (count : Nat) (w : List Bool)
    (certificate higher : Nat) :
    run (table continuation) ⟨certificate,2*flipped w (counter count higher),some 0⟩
      ((count+1)*(4*w.length+7)) =
      ⟨2^(count+1)*certificate,2*flipped w higher,some 21⟩ := by
  induction count generalizing certificate with
  | zero => simpa [counter] using iteration_stop continuation w certificate higher
  | succ count ih =>
    have ht : (count+1+1)*(4*w.length+7) = (4*w.length+7)+(count+1)*(4*w.length+7) := by ring
    rw [ht,Source284PayloadPop.run_add]
    change run (table continuation)
      (run (table continuation) ⟨certificate,2*flipped w (2*counter count higher+1),some 0⟩ _) _ = _
    rw [iteration_continue,ih]
    have he : 2^(count+1)*(2*certificate) = 2^(count+1+1)*certificate := by
      rw [pow_succ]
      ring
    rw [he]

/-- All one bits have been consumed after `count` cycles, but the zero
terminator has not yet been processed. -/
theorem counter_prefix (continuation : Nat → Bool → Row) (count : Nat) (w : List Bool)
    (certificate higher : Nat) :
    run (table continuation) ⟨certificate,2*flipped w (counter count higher),some 0⟩
      (count*(4*w.length+7)) =
      ⟨2^count*certificate,2*flipped w (2*higher),some 0⟩ := by
  induction count generalizing certificate with
  | zero => simp [counter,run]
  | succ count ih =>
    have ht : (count+1)*(4*w.length+7) = (4*w.length+7)+count*(4*w.length+7) := by ring
    rw [ht,Source284PayloadPop.run_add]
    change run (table continuation)
      (run (table continuation) ⟨certificate,2*flipped w (2*counter count higher+1),some 0⟩ _) _ = _
    rw [iteration_continue,ih]
    have he : 2^count*(2*certificate) = 2^(count+1)*certificate := by rw [pow_succ]; ring
    rw [he]

/-- With an absorbing continuation, entering the continuation cannot be
followed by a return to a prefix state. -/
theorem sink_row (b : Bool) : table Source284ScratchShiftLoop.sink 21 b = ⟨b,false,some 21⟩ := by
  cases b <;> rfl

theorem sink_run (c : Config) (h : c.state = some 21) (fuel : Nat) :
    (run (table Source284ScratchShiftLoop.sink) c fuel).state = some 21 := by
  induction fuel with
  | zero => exact h
  | succ fuel ih =>
    cases hc : run (table Source284ScratchShiftLoop.sink) c fuel with
    | mk left right state =>
      simp only [hc] at ih
      subst state
      simp [run,hc,step,sink_row]

/-- A unary counter of `count` ones cannot enter the absorbing continuation
before those `count` complete cycles. Thus the counter cannot silently be
replaced by a bound depending only on the parsed payload length. -/
theorem no_early_exit (count : Nat) (w : List Bool) (certificate higher t : Nat)
    (ht : t ≤ count*(4*w.length+7)) :
    (run (table Source284ScratchShiftLoop.sink)
      ⟨certificate,2*flipped w (counter count higher),some 0⟩ t).state ≠ some 21 := by
  intro h
  let c : Config := ⟨certificate,2*flipped w (counter count higher),some 0⟩
  have hs := sink_run (run (table Source284ScratchShiftLoop.sink) c t) h
    (count*(4*w.length+7)-t)
  rw [← Source284PayloadPop.run_add] at hs
  have he : t+(count*(4*w.length+7)-t) = count*(4*w.length+7) := by omega
  rw [he] at hs
  dsimp only [c] at hs
  rw [counter_prefix] at hs
  simp at hs

/-- For a fixed payload, arbitrary supplied suffix counters defeat every
fixed deadline for this implementation. -/
theorem no_fixed_payload_deadline (w : List Bool) (certificate bound : Nat) :
    ∃ count, ∀ t ≤ bound,
      (run (table Source284ScratchShiftLoop.sink)
        ⟨certificate,2*flipped w (counter count 0),some 0⟩ t).state ≠ some 21 := by
  refine ⟨bound+1,?_⟩
  intro t ht
  apply no_early_exit (bound+1) w certificate 0 t
  have h : bound ≤ (bound+1)*(4*w.length+7) := by nlinarith
  omega

/-- The shifted continuation is available after the paid stopping cycle. -/
theorem countdown_after (continuation : Nat → Bool → Row) (count : Nat) (w : List Bool)
    (certificate higher fuel : Nat) :
    let c : Config := ⟨2^(count+1)*certificate,2*flipped w higher,some 0⟩
    run (table continuation) ⟨certificate,2*flipped w (counter count higher),some 0⟩
      ((count+1)*(4*w.length+7)+fuel) =
      shiftConfig 14 (shiftConfig 1 (shiftConfig 6 (run continuation c fuel))) := by
  let c : Config := ⟨2^(count+1)*certificate,2*flipped w higher,some 0⟩
  rw [Source284PayloadPop.run_add,countdown]
  change run (table continuation) (shiftConfig 14 (shiftConfig 1 (shiftConfig 6 c))) fuel = _
  rw [stop_run,Source284ScratchShiftReturn.relocated_run,Source284ScratchFlipReturn.relocated_run]

end Shared.Beeping.NPcoNP.Source284CountedShift
