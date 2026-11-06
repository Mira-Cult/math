import Shared.Beeping.NPcoNP.Source284FixedGuardLink
import Shared.Beeping.NPcoNP.Source284TableCountdown
import Shared.Beeping.NPcoNP.Source284ClockStability

/-! A fixed-limit tagged guard linked to a fixed-clock finite verifier.
The countdown is actual finite control, not an assumption that the original
verifier terminates. Both limit and verifier cutoff are hardwired. This is
not an input-dependent compiler, a bit-cost bound, or a physical refinement. -/
namespace Shared.Beeping.NPcoNP.Source284FixedGuardTimed

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284FixedGuardRewind (duration states)

/-- The verifier gets a positive fixed number of steps. Timeout is routed to
an explicitly allocated nonaccepting sink by the finite countdown table. -/
def timed (n fuel : Nat) (verifier : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284TableCountdown.table n (fuel+1) verifier

def timedStates (n fuel : Nat) : Nat := Source284TableCountdown.allocated n (fuel+1)

def table (m n fuel : Nat) (verifier : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284FixedGuardLink.table m (timed n fuel verifier)

def statesTotal (m n fuel : Nat) : Nat := states m+timedStates n fuel

def time (m fuel : Nat) : Nat := duration m+(fuel+1)

def description (m n fuel tail : Nat) (verifier : Nat → Bool → Row) : Nat :=
  encode (statesTotal m n fuel) (table m n fuel verifier) tail

theorem timed_positive (n fuel : Nat) : 0 < timedStates n fuel := by
  simp [timedStates,Source284TableCountdown.allocated]

theorem closed (m n fuel : Nat) (verifier : Nat → Bool → Row) :
    Closed (statesTotal m n fuel) (table m n fuel verifier) := by
  apply Source284FixedGuardLink.closed m (timedStates n fuel) (timed n fuel verifier)
    (timed_positive n fuel)
  exact Source284TableCountdown.closed n (fuel+1) verifier

def guardSink (m : Nat) : Nat := Source284FixedGuardRewind.sink m

def timedSink (m n fuel : Nat) : Nat :=
  states m + Source284TableCountdown.sink n (fuel+1)

theorem guard_sink_row (m n fuel : Nat) (verifier : Nat → Bool → Row) (b : Bool) :
    (table m n fuel verifier (guardSink m) b).next = some (guardSink m) := by
  unfold table guardSink
  rw [Source284FixedGuardLink.linked_sink_row]

theorem timed_sink_row (m n fuel : Nat) (verifier : Nat → Bool → Row) (b : Bool) :
    (table m n fuel verifier (timedSink m n fuel) b).next = some (timedSink m n fuel) := by
  unfold table timedSink
  rw [Source284FixedGuardLink.relocated_row]
  simp [timed,Source284TableCountdown.table,Source284TableCountdown.sinkRow,
    Source284HardwireTable.shiftRow]

/-- A self-looping allocated logical control becomes an invariant nonzero
control of the actual unary-record source program, for arbitrary tape halves. -/
theorem source_sink_of_rows (m n fuel tail q : Nat) (verifier : Nat → Bool → Row)
    (hq : q < statesTotal m n fuel)
    (hnext : ∀ b, (table m n fuel verifier q b).next = some q) :
    ∀ c : Source284Relative.Config, c.state = active q →
      (Source284Relative.step (description m n fuel tail verifier) c).state = active q := by
  intro c hc
  cases c with
  | mk left right state =>
    simp only at hc
    subst state
    have h := step_lookup (statesTotal m n fuel) (table m n fuel verifier) tail q left right hq
    change Source284Relative.step (description m n fuel tail verifier) ⟨left,right,active q⟩ = _ at h
    split_ifs at h <;>
      have hs := congrArg Source284Relative.Config.state h <;>
      simpa [hnext,nextState] using hs

theorem source_guard_sink_invariant (m n fuel tail : Nat) (verifier : Nat → Bool → Row) :
    ∀ c : Source284Relative.Config, c.state = active (guardSink m) →
      (Source284Relative.step (description m n fuel tail verifier) c).state = active (guardSink m) := by
  apply source_sink_of_rows m n fuel tail (guardSink m) verifier
  · have h := Source284FixedGuardLink.sink_lt m
    simp only [statesTotal,guardSink]
    omega
  · exact guard_sink_row m n fuel verifier

theorem source_timed_sink_invariant (m n fuel tail : Nat) (verifier : Nat → Bool → Row) :
    ∀ c : Source284Relative.Config, c.state = active (timedSink m n fuel) →
      (Source284Relative.step (description m n fuel tail verifier) c).state = active (timedSink m n fuel) := by
  apply source_sink_of_rows m n fuel tail (timedSink m n fuel) verifier
  · simp [statesTotal,timedStates,timedSink,Source284TableCountdown.allocated]
  · exact timed_sink_row m n fuel verifier

/-- By the fixed source time every certificate has accepted, reached the
invalid-window sink, or reached the verifier-timeout sink. Both sinks are
actual self-looping logical states for either tape symbol. -/
theorem finished (m n fuel c i : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n verifier) :
    let s := (run (table m n fuel verifier) ⟨c,i,some 0⟩ (time m fuel)).state
    s = none ∨ s = some (guardSink m) ∨ s = some (timedSink m n fuel) := by
  dsimp only
  by_cases hbad : Source284TaggedWitnessCodec.decode m c = none
  · have ht : Source284FixedWitnessGuard.cutoff m ≤ time m fuel := by
      have hd := Source284FixedGuardRewind.duration_exact m
      simp [Source284FixedWitnessGuard.cutoff,time]
      omega
    have h := Source284FixedGuardLink.bad_reaches_sink m c i (timed n fuel verifier)
      (time m fuel-Source284FixedWitnessGuard.cutoff m) hbad
    have he : Source284FixedWitnessGuard.cutoff m+
        (time m fuel-Source284FixedWitnessGuard.cutoff m) = time m fuel := by omega
    rw [he] at h
    exact Or.inr (Or.inl h)
  · have h := Source284FixedGuardLink.good_then_verifier m c i (timed n fuel verifier) fuel hbad
    have hv : Valid n ⟨c,i,some 0⟩ := by
      intro q hq; simp only [Option.some.injEq] at hq; omega
    have hc := Source284TableCountdown.run_mapped n (fuel+1) verifier ⟨c,i,some 0⟩
      hv hclosed (fuel+1) (by omega)
    rw [Source284TableCountdown.mapped_start] at hc
    change run (timed n fuel verifier) ⟨c,i,some 0⟩ (fuel+1) = _ at hc
    rw [hc] at h
    change run (table m n fuel verifier) ⟨c,i,some 0⟩ (time m fuel) = _ at h
    rw [h]
    cases hs : (run verifier ⟨c,i,some 0⟩ (fuel+1)).state with
    | none => simp [Source284HardwireTable.shiftConfig,Source284TableCountdown.mapped,hs]
    | some q => simp [Source284HardwireTable.shiftConfig,Source284TableCountdown.mapped,hs,timedSink]

/-- The same three-way completion statement for the actual encoded source
numeral, with an arbitrary unused table-description tail. -/
theorem source_finished (m n fuel c i tail : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n verifier) :
    let s := (Source284Relative.run (description m n fuel tail verifier)
      (Source284Relative.initial i c) (time m fuel)).state
    s = 0 ∨ s = active (guardSink m) ∨ s = active (timedSink m n fuel) := by
  dsimp only
  have hv : Valid (statesTotal m n fuel) ⟨c,i,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    unfold statesTotal
    have := timed_positive n fuel
    omega
  have hr := run_toSource (statesTotal m n fuel) (table m n fuel verifier) tail
    ⟨c,i,some 0⟩ (closed m n fuel verifier) hv (time m fuel)
  change Source284Relative.run (description m n fuel tail verifier)
    (Source284Relative.initial i c) (time m fuel) = _ at hr
  rw [hr]
  rcases finished m n fuel c i verifier hn hclosed with h | h | h
  · left; simp [toSource,nextState,h]
  · exact Or.inr (Or.inl (by simp [toSource,nextState,h]))
  · exact Or.inr (Or.inr (by simp [toSource,nextState,h]))

/-- For a successfully decoded certificate, the full source program has
exactly the original verifier's acceptance at its own fixed cutoff, no
matter how much more time the outer source search supplies. -/
theorem source_good_stable (m n fuel c i tail extra : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n verifier)
    (hgood : Source284TaggedWitnessCodec.decode m c ≠ none) :
    Source284Relative.accepts (description m n fuel tail verifier) i c (time m fuel+extra) =
      (run verifier ⟨c,i,some 0⟩ (fuel+1)).state.isNone := by
  have htime : time m fuel+extra = duration m+((fuel+extra)+1) := by simp [time]; omega
  rw [htime]
  unfold description statesTotal table
  rw [Source284FixedGuardLink.source_good_accepts m (timedStates n fuel) c i tail
    (fuel+extra) (timed n fuel verifier) (timed_positive n fuel)
    (Source284TableCountdown.closed n (fuel+1) verifier) hgood]
  have h := Source284TableCountdown.initial_acceptance_stable n (fuel+1) verifier hn hclosed c i extra
  change (run (timed n fuel verifier) ⟨c,i,some 0⟩ ((fuel+1)+extra)).state.isNone = _ at h
  have hlen : (fuel+1)+extra = fuel+extra+1 := by omega
  simpa only [hlen] using h

/-- Invalid tagged certificates cannot accept, regardless of either clock. -/
theorem source_bad (m n fuel c i tail clock : Nat) (verifier : Nat → Bool → Row)
    (hbad : Source284TaggedWitnessCodec.decode m c = none) :
    Source284Relative.accepts (description m n fuel tail verifier) i c clock = false := by
  exact Source284FixedGuardLink.source_bad_never_accepts m (timedStates n fuel) c i tail clock
    (timed n fuel verifier) (timed_positive n fuel)
    (Source284TableCountdown.closed n (fuel+1) verifier) hbad

/-- A real finite timeout removes the silent-divergence loophole: acceptance
of every certificate is stable at the stated fixed source clock. -/
theorem source_stable (m n fuel c i tail extra : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n verifier) :
    Source284Relative.accepts (description m n fuel tail verifier) i c (time m fuel+extra) =
      Source284Relative.accepts (description m n fuel tail verifier) i c (time m fuel) := by
  by_cases hbad : Source284TaggedWitnessCodec.decode m c = none
  · rw [source_bad m n fuel c i tail _ verifier hbad,
      source_bad m n fuel c i tail _ verifier hbad]
  · rw [source_good_stable m n fuel c i tail extra verifier hn hclosed hbad]
    have hzero := source_good_stable m n fuel c i tail 0 verifier hn hclosed hbad
    simpa using hzero.symm

/-- Once the fixed source clock has been reached, enlarging both time and the
numerical certificate range cannot change existential acceptance. -/
theorem source_bound_stable (m n fuel i tail extra bound : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n verifier) (hb : 2^(time m fuel) ≤ bound) :
    Source284Relative.acceptBound (description m n fuel tail verifier) i (time m fuel+extra) bound =
      Source284Relative.acceptBound (description m n fuel tail verifier) i (time m fuel) (2^(time m fuel)) := by
  apply Bool.eq_iff_iff.mpr
  rw [Source284Relative.acceptBound_iff,Source284Relative.acceptBound_iff]
  constructor
  · rintro ⟨c,_,hc⟩
    refine ⟨c % 2^(time m fuel), Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    rw [← Source284Relative.accepts_truncate (description m n fuel tail verifier) i c (time m fuel)]
    rw [← source_stable m n fuel c i tail extra verifier hn hclosed]
    exact hc
  · rintro ⟨c,hc,ha⟩
    refine ⟨c,lt_of_lt_of_le hc hb,?_⟩
    rw [source_stable m n fuel c i tail extra verifier hn hclosed]
    exact ha

/-- At every later coupled clock, the completed timed guard searches exactly
the original bounded witness set, assuming the supplied verifier computes
the intended predicate at its fixed cutoff for all decoded aliases. -/
theorem source_coupled_stable_search (m n fuel i tail extra : Nat)
    (verifier : Nat → Bool → Row) (predicate : List Bool → Bool)
    (hn : 0 < n) (hclosed : Closed n verifier)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode m c = some w →
      (run verifier ⟨c,i,some 0⟩ (fuel+1)).state.isNone = predicate w) :
    Source284Relative.acceptBound (description m n fuel tail verifier) i (time m fuel+extra)
        (2^(time m fuel+extra)) = true ↔ ∃ w, w.length ≤ m ∧ predicate w = true := by
  have hb : 2^(time m fuel) ≤ 2^(time m fuel+extra) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [source_bound_stable m n fuel i tail extra _ verifier hn hclosed hb]
  have hm : ∀ c w, Source284TaggedWitnessCodec.decode m c = some w →
      (run (timed n fuel verifier) ⟨c,i,some 0⟩ (fuel+1)).state.isNone = predicate w := by
    intro c w hw
    have h := Source284TableCountdown.initial_acceptance_stable n (fuel+1) verifier hn hclosed c i 0
    simp only [Nat.add_zero] at h
    change (run (timed n fuel verifier) ⟨c,i,some 0⟩ (fuel+1)).state.isNone = _ at h
    rw [h]
    exact hmatch c w hw
  have hh := Source284FixedGuardLink.source_coupled_search_iff m (timedStates n fuel) i tail fuel
    (timed n fuel verifier) predicate (timed_positive n fuel)
    (Source284TableCountdown.closed n (fuel+1) verifier) hm
  simpa only [description,statesTotal,table,time] using hh

-- This verifier accepts on its second transition. An outer clock increase
-- must not turn a one-transition timeout into acceptance.
private def acceptsSecond (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩ else ⟨b,false,none⟩

private theorem acceptsSecond_closed : Closed 2 acceptsSecond := by
  intro q hq b q' h
  interval_cases q <;> cases b <;> simp_all [acceptsSecond]

example (extra : Nat) :
    Source284Relative.accepts (description 0 2 0 0 acceptsSecond) 7 0 (time 0 0+extra) = false := by
  have h := source_good_stable 0 2 0 0 7 0 extra acceptsSecond (by decide)
    acceptsSecond_closed (by decide +kernel)
  simpa [run,step,acceptsSecond] using h

example (extra : Nat) :
    Source284Relative.accepts (description 0 2 1 0 acceptsSecond) 7 0 (time 0 1+extra) = true := by
  have h := source_good_stable 0 2 1 0 7 0 extra acceptsSecond (by decide)
    acceptsSecond_closed (by decide +kernel)
  simpa [run,step,acceptsSecond] using h

example (clock : Nat) :
    Source284Relative.accepts (description 0 2 1 0 acceptsSecond) 7 1 clock = false := by
  apply source_bad
  decide +kernel

end Shared.Beeping.NPcoNP.Source284FixedGuardTimed
