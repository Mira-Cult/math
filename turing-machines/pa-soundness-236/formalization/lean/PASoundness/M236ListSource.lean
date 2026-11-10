import PASoundness.M236ListScheduleObserver
import PASoundness.M236Observer
/-! Abstract complete-frame source in an alternative non-repeating list-stage order.
No claim is made here about the M236 register program's implementation. -/
namespace PASoundness.M236ListSource
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236.ListSchedule

def recordAt (value : Address → Bool) (n : Nat) : Record :=
  (scheduledAddress n, value (scheduledAddress n))

def recordsBefore (value : Address → Bool) (n : Nat) : List Record :=
  (List.range n).map (recordAt value)

def source (value : Address → Bool) : WordEventSystem Nat Bool where
  initial := 0
  step := fun n => (n+1, encodeFrame (scheduledAddress n) (value (scheduledAddress n)))

theorem source_run (value : Address → Bool) (n : Nat) : (source value).run n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [WordEventSystem.run_succ, ih]; rfl

theorem source_prefix (value : Address → Bool) (n : Nat) :
    (source value).prefixWord n = encodeRecords (recordsBefore value n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [WordEventSystem.prefix_succ, ih, source_run]
    simp only [recordsBefore, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, Source.encodeRecords_append, encodeRecords, List.append_nil]
    rfl

theorem recordsBefore_valued (value : Address → Bool) (n : Nat) :
    Source.Valued value (recordsBefore value n) := by
  intro r hr
  obtain ⟨stage, _, h⟩ := List.mem_map.mp hr
  rw [← h]
  rfl

theorem recordsBefore_valid (value : Address → Bool) (n : Nat) :
    RecordsValid (recordsBefore value n) := by
  intro r hr
  obtain ⟨stage, _, h⟩ := List.mem_map.mp hr
  rw [← h]
  have ha := scheduled_admissible stage
  exact ⟨ha.2 rfl, ha.1⟩

theorem recordsBefore_coherent (value : Address → Bool) (n : Nat) :
    CoherentAfter [] (recordsBefore value n) :=
  Source.coherentAfter_valued value [] (recordsBefore value n)
    (by intro r hr; cases hr) (recordsBefore_valued value n) (recordsBefore_valid value n)

theorem decode_source_prefix (value : Address → Bool) (n : Nat) :
    feedBits {} ((source value).prefixWord n) =
      ⟨active .rank (recordsBefore value n), 0⟩ := by
  rw [source_prefix]
  simpa only [List.nil_append, active] using
    decode_encodeRecords [] (recordsBefore value n) (recordsBefore_coherent value n)

def events (value : Address → Bool) : EventStructure := wordDecodedEvents (source value)

theorem out_iff_mem (value : Address → Bool) (b : Bool) (t : Nat) (a : Address) :
    (events value).out b t a ↔ (a, b) ∈ recordsBefore value t := by
  change (a, b) ∈ (feedBits {} ((source value).prefixWord t)).numbers.records ↔ _
  rw [decode_source_prefix]
  rfl

/-- Each admissible record is present at its explicit finite stage. -/
theorem emitted_at_stage (value : Address → Bool) (a : Address) (ha : Admissible .legacy a) :
    (events value).out (value a) (stageForAddress a + 1) a := by
  apply (out_iff_mem value (value a) _ a).mpr
  apply List.mem_map.mpr
  refine ⟨stageForAddress a, List.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
  simp [recordAt, scheduled_stageForAddress a ha]

theorem emitted_exact (value : Address → Bool) (b : Bool) (a : Address) :
    Emitted (events value) b a ↔ Admissible .legacy a ∧ value a = b := by
  constructor
  · rintro ⟨t, hout⟩
    have hr := (out_iff_mem value b t a).mp hout
    obtain ⟨stage, _, h⟩ := List.mem_map.mp hr
    have ha : scheduledAddress stage = a := congrArg Prod.fst h
    have hb : value (scheduledAddress stage) = b := congrArg Prod.snd h
    exact ⟨by rw [← ha]; exact scheduled_admissible stage, by rw [← ha]; exact hb⟩
  · rintro ⟨ha, hb⟩
    refine ⟨stageForAddress a + 1, ?_⟩
    simpa [hb] using emitted_at_stage value a ha

theorem no_error (value : Address → Bool) (t : Nat) : ¬ (events value).error t := by
  change ¬ (feedBits {} ((source value).prefixWord t)).numbers.failed = true
  rw [decode_source_prefix]
  simp [active]

theorem frame_progress (value : Address → Bool) : M236Observer.FrameProgress (source value) := by
  intro t
  refine ⟨t, Nat.le_refl t, ?_, ?_⟩
  · rw [decode_source_prefix]; rfl
  · rw [decode_source_prefix]

theorem same_receipts (value : Address → Bool) : SameReceipts (events value) (Source.events value) := by
  refine ⟨rfl, ?_, ?_⟩
  · constructor
    · rintro ⟨t, h⟩; exact False.elim (no_error value t h)
    · rintro ⟨t, h⟩; exact False.elim (Source.no_error value t h)
  · intro b a
    rw [emitted_exact, Source.emitted_exact]

/-- The fixed observer has the same acceptance for the alternative list order
and the repeated-address abstract order, for any total record-value function. -/
theorem trace_accept_reindex (value : Address → Bool) :
    M236Observer.TraceAccept (source value) ↔ M236Observer.TraceAccept (Source.source value) := by
  change (M236Observer.Accept (events value) ∧ M236Observer.FrameProgress (source value)) ↔
    (M236Observer.Accept (Source.events value) ∧ M236Observer.FrameProgress (Source.source value))
  rw [and_iff_left (frame_progress value), and_iff_left (M236Observer.source_frame_progress value)]
  exact M236Observer.accept_preserved (same_receipts value)

end PASoundness.M236ListSource
