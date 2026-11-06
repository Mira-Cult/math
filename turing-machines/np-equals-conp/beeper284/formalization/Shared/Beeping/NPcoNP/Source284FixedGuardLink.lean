import Shared.Beeping.NPcoNP.Source284FixedGuardRewind
import Shared.Beeping.NPcoNP.Source284HardwireTable

/-! Link the fixed-window guard to a supplied finite source verifier. The
verifier receives the complete original tape halves; no canonical input
initializer or input-dependent witness limit is asserted. -/
namespace Shared.Beeping.NPcoNP.Source284FixedGuardLink

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284FixedGuardRewind
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)

/-- The verifier's first row replaces the guard's handoff row; remaining
verifier states are relocated above the guard's logical state range. -/
def table (m : Nat) (verifier : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = handoff m then shiftRow (states m) (verifier 0 b)
  else if states m ≤ q then shiftRow (states m) (verifier (q-states m) b)
  else Source284FixedGuardRewind.table m q b

theorem handoff_lt (m : Nat) : handoff m < states m := by simp [states]
theorem sink_lt (m : Nat) : sink m < states m := by
  simp [states,handoff,rewindStart,sink]
  omega

theorem handoff_ne_sink (m : Nat) : handoff m ≠ sink m := by
  simp [handoff,rewindStart,sink,width,Source284FixedWitnessGuard.cutoff]
  omega

theorem guard_row (m : Nat) (verifier : Nat → Bool → Row) (q : Nat) (b : Bool)
    (hq : q < states m) (hn : q ≠ handoff m) :
    table m verifier q b = Source284FixedGuardRewind.table m q b := by
  simp [table,hn,Nat.not_le_of_gt hq]

theorem guard_step (m : Nat) (verifier : Nat → Bool → Row) (c : Config)
    (hv : Valid (states m) c) (hn : c.state ≠ some (handoff m)) :
    step (table m verifier) c = step (Source284FixedGuardRewind.table m) c := by
  cases c with
  | mk l r s =>
    cases s with
    | none => rfl
    | some q =>
      have hq := hv q rfl
      have hneq : q ≠ handoff m := by simpa using hn
      simp only [step,guard_row m verifier q _ hq hneq]

theorem run_before (m : Nat) (verifier : Nat → Bool → Row) (c : Config)
    (hv : Valid (states m) c) (fuel : Nat)
    (ha : ∀ t < fuel, (run (Source284FixedGuardRewind.table m) c t).state ≠ some (handoff m)) :
    run (table m verifier) c fuel = run (Source284FixedGuardRewind.table m) c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hprefix : ∀ t < fuel,
        (run (Source284FixedGuardRewind.table m) c t).state ≠ some (handoff m) := by
      intro t ht; exact ha t (by omega)
    have hs := guard_step m verifier (run (Source284FixedGuardRewind.table m) c fuel)
      (valid_run _ _ _ (table_closed m) hv fuel) (ha fuel (by omega))
    simp only [run, ih hprefix, hs]

theorem handoff_row (m : Nat) (b : Bool) :
    Source284FixedGuardRewind.table m (handoff m) b = ⟨b,false,some (sink m)⟩ := by
  have hf : ¬ handoff m < rewindTurn m := by simp [handoff,rewindStart]; omega
  have ht : handoff m ≠ rewindTurn m := by simp [handoff,rewindStart]; omega
  simp [Source284FixedGuardRewind.table,hf,ht]

/-- A guard run that ends at the handoff cannot have visited it earlier:
its next row would enter the permanent sink. -/
theorem no_early_handoff (m : Nat) (c : Config) (fuel : Nat)
    (hend : (run (Source284FixedGuardRewind.table m) c fuel).state = some (handoff m)) :
    ∀ t < fuel, (run (Source284FixedGuardRewind.table m) c t).state ≠ some (handoff m) := by
  intro t ht he
  have hs : (run (Source284FixedGuardRewind.table m) c (t+1)).state = some (sink m) := by
    cases hc : run (Source284FixedGuardRewind.table m) c t with
    | mk left right state =>
      have hh : state = some (handoff m) := by simpa [hc] using he
      subst state
      simp [run,hc,step,handoff_row]
  have hsink := sink_run m (run (Source284FixedGuardRewind.table m) c (t+1))
    hs (fuel-(t+1))
  rw [← Source284WindowRewind.run_add_generic] at hsink
  have htime : t+1+(fuel-(t+1)) = fuel := by omega
  rw [htime,hend] at hsink
  exact handoff_ne_sink m (Option.some.inj hsink)

theorem relocated_row (m : Nat) (verifier : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table m verifier (states m+q) b = shiftRow (states m) (verifier q b) := by
  have hn : states m+q ≠ handoff m := by have h := handoff_lt m; omega
  simp [table,hn]

theorem relocated_step (m : Nat) (verifier : Nat → Bool → Row) (c : Config) :
    step (table m verifier) (shiftConfig (states m) c) =
      shiftConfig (states m) (step verifier c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (m : Nat) (verifier : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table m verifier) (shiftConfig (states m) c) fuel =
      shiftConfig (states m) (run verifier c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem handoff_step (m : Nat) (verifier : Nat → Bool → Row) (left right : Nat) :
    step (table m verifier) ⟨left,right,some (handoff m)⟩ =
      shiftConfig (states m) (step verifier ⟨left,right,some 0⟩) := by
  have hrow (b : Bool) : table m verifier (handoff m) b =
      shiftRow (states m) (verifier 0 b) := by simp [table]
  cases ht : (verifier 0 (decide (right % 2 = 1))).turn <;>
    simp [step,hrow,shiftConfig,shiftRow,ht]

theorem handoff_run (m : Nat) (verifier : Nat → Bool → Row) (left right fuel : Nat) :
    run (table m verifier) ⟨left,right,some (handoff m)⟩ (fuel+1) =
      shiftConfig (states m) (run verifier ⟨left,right,some 0⟩ (fuel+1)) := by
  rw [run_front,handoff_step,relocated_run,← run_front]

/-- Good certificates run the guard, return the untouched complete tape,
then execute the verifier with its first transition charged. -/
theorem good_then_verifier (m c i : Nat) (verifier : Nat → Bool → Row) (fuel : Nat)
    (hgood : Source284TaggedWitnessCodec.decode m c ≠ none) :
    run (table m verifier) ⟨c,i,some 0⟩ (duration m+(fuel+1)) =
      shiftConfig (states m) (run verifier ⟨c,i,some 0⟩ (fuel+1)) := by
  let start : Config := ⟨c,i,some 0⟩
  have hv : Valid (states m) start := by
    intro q hq
    simp only [start,Option.some.injEq] at hq
    subst q
    simp [states,handoff,rewindStart,rewindTurn]
  have hend : (run (Source284FixedGuardRewind.table m) start (duration m)).state =
      some (handoff m) := by
    dsimp [start]
    rw [run_rewind m c i hgood]
  have ha := no_early_handoff m start (duration m) hend
  have hr := run_before m verifier start hv (duration m) ha
  dsimp only [start] at hr
  rw [Source284WindowRewind.run_add_generic,hr,run_rewind m c i hgood,handoff_run]

/-- Prior to the fixed cutoff, the guard's time-coded modes are strictly
below the handoff, even on malformed certificates. -/
theorem before_cutoff (m c i t : Nat) (ht : t < Source284FixedWitnessGuard.cutoff m) :
    (run (Source284FixedGuardRewind.table m) ⟨c,i,some 0⟩ t).state ≠ some (handoff m) := by
  let start : Config := ⟨c,i,some 0⟩
  have hv : Valid 7 start := by
    intro q hq; simp only [start,Option.some.injEq] at hq; omega
  have hl : start.state ≠ none := by simp [start]
  have hr := run_mapped m start hv hl t ht
  have hm : mapped 0 start = start := by simp [mapped,start,code]
  rw [hm] at hr
  change (run (Source284FixedGuardRewind.table m) start t).state ≠ _
  rw [hr]
  cases hq : (run Source284FixedWitnessGuard.scanner start t).state with
  | none => simp [mapped,hq]
  | some q =>
    have hvq := (valid_run 7 Source284FixedWitnessGuard.scanner start
      Source284TaggedScanner.table_closed hv t) q hq
    have hcode := code_lt m t q ht hvq
    have hhandoff : rewindTurn m < handoff m := by simp [handoff,rewindStart]; omega
    have hn : code t q ≠ handoff m := by omega
    simp [mapped,hq,hn]

theorem linked_sink_row (m : Nat) (verifier : Nat → Bool → Row) (b : Bool) :
    table m verifier (sink m) b = ⟨b,false,some (sink m)⟩ := by
  rw [guard_row m verifier (sink m) b (sink_lt m) (Ne.symm (handoff_ne_sink m))]
  exact sink_row m b

theorem linked_sink_run (m : Nat) (verifier : Nat → Bool → Row) (c : Config)
    (hs : c.state = some (sink m)) (fuel : Nat) :
    (run (table m verifier) c fuel).state = some (sink m) := by
  induction fuel with
  | zero => exact hs
  | succ fuel ih =>
    cases hc : run (table m verifier) c fuel with
    | mk l r state =>
      have hstate : state = some (sink m) := by simpa [hc] using ih
      subst state
      simp [run,hc,step,linked_sink_row]

/-- A bad certificate enters the guard's sink by the cutoff even after
linking, and the verifier can never accept it at a later clock. -/
theorem bad_reaches_sink (m c i : Nat) (verifier : Nat → Bool → Row) (extra : Nat)
    (hbad : Source284TaggedWitnessCodec.decode m c = none) :
    (run (table m verifier) ⟨c,i,some 0⟩
      (Source284FixedWitnessGuard.cutoff m+extra)).state = some (sink m) := by
  have hv : Valid (states m) ⟨c,i,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    simp [states,handoff,rewindStart,rewindTurn]
  have ha : ∀ t < Source284FixedWitnessGuard.cutoff m,
      (run (Source284FixedGuardRewind.table m) ⟨c,i,some 0⟩ t).state ≠ some (handoff m) := by
    intro t ht
    exact before_cutoff m c i t ht
  have hr := run_before m verifier ⟨c,i,some 0⟩ hv _ ha
  have hs := run_reject m c i 0 hbad
  simp only [Nat.add_zero] at hs
  rw [Source284WindowRewind.run_add_generic,hr]
  exact linked_sink_run m verifier _ hs extra

theorem shifted_bound (m n : Nat) (verifier : Nat → Bool → Row)
    (hclosed : Closed n verifier) (q : Nat) (hq : q < n) (b : Bool) (target : Nat)
    (hnext : (shiftRow (states m) (verifier q b)).next = some target) :
    target < states m+n := by
  cases hn : (verifier q b).next with
  | none => simp [shiftRow,hn] at hnext
  | some r =>
    have hr := hclosed q hq b r hn
    simp only [shiftRow,hn,Option.map_some,Option.some.injEq] at hnext
    omega

theorem closed (m n : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n verifier) :
    Closed (states m+n) (table m verifier) := by
  intro q hq b target hnext
  by_cases hh : q = handoff m
  · subst q
    have hrow : table m verifier (handoff m) b = shiftRow (states m) (verifier 0 b) := by simp [table]
    rw [hrow] at hnext
    exact shifted_bound m n verifier hclosed 0 hn b target hnext
  · by_cases hs : states m ≤ q
    · have hrow : table m verifier q b =
          shiftRow (states m) (verifier (q-states m) b) := by simp [table,hh,hs]
      rw [hrow] at hnext
      exact shifted_bound m n verifier hclosed (q-states m) (by omega) b target hnext
    · have hrow := guard_row m verifier q b (by omega) hh
      rw [hrow] at hnext
      have htarget := table_closed m q (by omega) b target hnext
      omega

/-- Actual encoded source execution agrees with the linked verifier's
bounded acceptance for every successfully decoded fixed-window certificate. -/
theorem source_good_accepts (m n c i tail fuel : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n verifier)
    (hgood : Source284TaggedWitnessCodec.decode m c ≠ none) :
    Source284Relative.accepts (encode (states m+n) (table m verifier) tail) i c
      (duration m+(fuel+1)) = (run verifier ⟨c,i,some 0⟩ (fuel+1)).state.isNone := by
  rw [bounded_acceptance (states m+n) (table m verifier) tail (by omega)
    (closed m n verifier hn hclosed),good_then_verifier m c i verifier fuel hgood]
  cases hs : (run verifier ⟨c,i,some 0⟩ (fuel+1)).state <;>
    simp [shiftConfig,hs]

/-- Bad certificates are rejected for every outer time at or above the
fixed guard cutoff, independent of the verifier table. -/
theorem source_bad_rejects (m n c i tail extra : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n verifier)
    (hbad : Source284TaggedWitnessCodec.decode m c = none) :
    Source284Relative.accepts (encode (states m+n) (table m verifier) tail) i c
      (Source284FixedWitnessGuard.cutoff m+extra) = false := by
  rw [bounded_acceptance (states m+n) (table m verifier) tail (by omega)
    (closed m n verifier hn hclosed)]
  rw [bad_reaches_sink m c i verifier extra hbad]
  rfl

/-- No malformed or overlong certificate can accept at any finite clock,
including clocks shorter than the guard's cutoff. -/
theorem bad_never_accepts (m c i : Nat) (verifier : Nat → Bool → Row) (clock : Nat)
    (hbad : Source284TaggedWitnessCodec.decode m c = none) :
    (run (table m verifier) ⟨c,i,some 0⟩ clock).state ≠ none := by
  by_cases ht : clock < Source284FixedWitnessGuard.cutoff m
  · let start : Config := ⟨c,i,some 0⟩
    have hv : Valid (states m) start := by
      intro q hq
      simp only [start,Option.some.injEq] at hq
      subst q
      simp [states,handoff,rewindStart,rewindTurn]
    have hv7 : Valid 7 start := by
      intro q hq; simp only [start,Option.some.injEq] at hq; omega
    have hl : start.state ≠ none := by simp [start]
    have ha : ∀ t < clock,
        (run (Source284FixedGuardRewind.table m) start t).state ≠ some (handoff m) := by
      intro t htime
      exact before_cutoff m c i t (by omega)
    have hr := run_before m verifier start hv clock ha
    have hm := run_mapped m start hv7 hl clock ht
    have hstart : mapped 0 start = start := by simp [mapped,start,code]
    rw [hstart] at hm
    change (run (table m verifier) start clock).state ≠ none
    rw [hr,hm]
    have hlive := scanner_live start hl clock
    cases hs : (run Source284FixedWitnessGuard.scanner start clock).state with
    | none => contradiction
    | some q => simp [mapped,hs]
  · have hc : Source284FixedWitnessGuard.cutoff m ≤ clock := by omega
    have hs := bad_reaches_sink m c i verifier (clock-Source284FixedWitnessGuard.cutoff m) hbad
    have he : Source284FixedWitnessGuard.cutoff m+
        (clock-Source284FixedWitnessGuard.cutoff m) = clock := by omega
    rw [he] at hs
    rw [hs]
    simp

theorem source_bad_never_accepts (m n c i tail clock : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n verifier)
    (hbad : Source284TaggedWitnessCodec.decode m c = none) :
    Source284Relative.accepts (encode (states m+n) (table m verifier) tail) i c clock = false := by
  rw [bounded_acceptance (states m+n) (table m verifier) tail (by omega)
    (closed m n verifier hn hclosed)]
  have h := bad_never_accepts m c i verifier clock hbad
  cases hs : (run (table m verifier) ⟨c,i,some 0⟩ clock).state <;> simp_all

/-- Fixed-window existential search preserves the original witness cutoff.
The supplied verifier must be correct for every decoded certificate, including
high-bit aliases, at its stated positive finite fuel. This theorem does not
construct that verifier, a dynamic limit, or any polynomial-time bound. -/
theorem source_search_iff (m n i tail fuel bits : Nat) (verifier : Nat → Bool → Row)
    (predicate : List Bool → Bool) (hn : 0 < n) (hclosed : Closed n verifier)
    (hbits : Source284WitnessWindow.width m+2 ≤ bits)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode m c = some w →
      (run verifier ⟨c,i,some 0⟩ (fuel+1)).state.isNone = predicate w) :
    Source284Relative.acceptBound (encode (states m+n) (table m verifier) tail) i
        (duration m+(fuel+1)) (2^bits) = true ↔
      ∃ w, w.length ≤ m ∧ predicate w = true := by
  have hpoint (c : Nat) :
      Source284Relative.accepts (encode (states m+n) (table m verifier) tail) i c
          (duration m+(fuel+1)) = Source284TaggedWitnessCodec.check m predicate c := by
    cases hd : Source284TaggedWitnessCodec.decode m c with
    | none =>
      rw [source_bad_never_accepts m n c i tail (duration m+(fuel+1)) verifier hn hclosed hd]
      simp [Source284TaggedWitnessCodec.check,hd]
    | some w =>
      have hg : Source284TaggedWitnessCodec.decode m c ≠ none := by rw [hd]; simp
      rw [source_good_accepts m n c i tail fuel verifier hn hclosed hg,hmatch c w hd]
      simp [Source284TaggedWitnessCodec.check,hd]
  have hraw :
      Source284Relative.acceptBound (encode (states m+n) (table m verifier) tail) i
          (duration m+(fuel+1)) (2^bits) = true ↔
        ∃ c, c < 2^bits ∧ Source284TaggedWitnessCodec.check m predicate c = true := by
    rw [Source284Relative.acceptBound_iff]
    simp_rw [hpoint]
  exact hraw.trans (Source284TaggedWitnessCodec.clock_search_iff m bits predicate hbits)

/-- The actual source convention uses the same clock for verifier steps and
the exponent of the numeric certificate search. The guard's own paid work is
already enough to cover its tagged window, for every fixed limit. -/
theorem source_coupled_search_iff (m n i tail fuel : Nat) (verifier : Nat → Bool → Row)
    (predicate : List Bool → Bool) (hn : 0 < n) (hclosed : Closed n verifier)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode m c = some w →
      (run verifier ⟨c,i,some 0⟩ (fuel+1)).state.isNone = predicate w) :
    let clock := duration m+(fuel+1)
    Source284Relative.acceptBound (encode (states m+n) (table m verifier) tail) i
        clock (2^clock) = true ↔ ∃ w, w.length ≤ m ∧ predicate w = true := by
  dsimp only
  apply source_search_iff m n i tail fuel (duration m+(fuel+1)) verifier predicate hn hclosed
  · have hd := duration_exact m
    simp [Source284WitnessWindow.width]
    omega
  · exact hmatch

private def acceptsAll (_ : Nat) (b : Bool) : Row := ⟨b,false,none⟩
private theorem acceptsAll_closed : Closed 1 acceptsAll := by
  intro q hq b q' h
  simp [acceptsAll] at h

-- Even an accepting verifier cannot rescue a malformed tag or an overlong
-- witness; a valid high-bit alias reaches it with a nonzero input intact.
example (clock : Nat) :
    Source284Relative.accepts (encode (states 0+1) (table 0 acceptsAll) 0) 7 1 clock = false := by
  apply source_bad_never_accepts 0 1 1 7 0 clock acceptsAll (by decide) acceptsAll_closed
  decide +kernel
example :
    Source284Relative.accepts (encode (states 1+1) (table 1 acceptsAll) 0) 9 68
      (duration 1+1) = true := by
  rw [source_good_accepts 1 1 68 9 0 0 acceptsAll (by decide) acceptsAll_closed (by decide +kernel)]
  rfl

example :
    Source284Relative.acceptBound (encode (states 0+1) (table 0 acceptsAll) 0) 7
      (duration 0+1) (2^(duration 0+1)) = true := by
  have hm : ∀ c w, Source284TaggedWitnessCodec.decode 0 c = some w →
      (run acceptsAll ⟨c,7,some 0⟩ 1).state.isNone = (fun _ : List Bool => true) w := by
    intro c w _
    rfl
  have h := source_coupled_search_iff 0 1 7 0 0 acceptsAll (fun _ => true)
    (by decide) acceptsAll_closed hm
  dsimp only at h
  apply h.mpr
  exact ⟨[],by simp,rfl⟩

end Shared.Beeping.NPcoNP.Source284FixedGuardLink
