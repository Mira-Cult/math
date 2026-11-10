import PASoundness.Schedule
import PASoundness.ObserverBridge
import PASoundness.DecoderRefinement

/-!
The exact fair addressed-unary source interface.  Each abstract transition
computes one total address-value function and emits one complete frame.  A
concrete implementation still owes the local positive-block simulation of
that finite computation.  No theory soundness is used for address coverage,
framing correctness, decoder progress, or output correctness.
-/

namespace PASoundness.Source

open Observer UnaryCodec

def recordAt (value : Address → Bool) (stage : Nat) : Record :=
  (Schedule.scheduledAddress stage, value (Schedule.scheduledAddress stage))

def recordsBefore (value : Address → Bool) (stage : Nat) : List Record :=
  (List.range stage).map (recordAt value)

def source (value : Address → Bool) : WordEventSystem Nat Bool where
  initial := 0
  step := fun stage =>
    (stage+1, encodeFrame (Schedule.scheduledAddress stage)
      (value (Schedule.scheduledAddress stage)))

theorem source_run (value : Address → Bool) (n : Nat) : (source value).run n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [WordEventSystem.run_succ, ih]
    rfl

theorem encodeRecords_append (left right : List Record) :
    encodeRecords (left ++ right) = encodeRecords left ++ encodeRecords right := by
  induction left with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append, encodeRecords, ih, List.append_assoc]

/-- Every bit, including unary zeros and repeated records, occurs in its fixed order. -/
theorem source_prefix (value : Address → Bool) (n : Nat) :
    (source value).prefixWord n = encodeRecords (recordsBefore value n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [WordEventSystem.prefix_succ, ih, source_run]
    simp only [recordsBefore, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, encodeRecords_append, encodeRecords, List.append_nil]
    rfl

def Valued (value : Address → Bool) (records : List Record) : Prop :=
  ∀ r ∈ records, r.2 = value r.1

theorem coherentAfter_valued (value : Address → Bool) (before records : List Record)
    (hbefore : Valued value before) (hrecords : Valued value records)
    (hvalid : RecordsValid records) : CoherentAfter before records := by
  induction records generalizing before with
  | nil => trivial
  | cons r rs ih =>
    have hr : r.2 = value r.1 := hrecords r (by simp)
    refine ⟨hvalid r (by simp), ?_, ?_⟩
    · intro old hold heq
      rw [hbefore old hold, hr, heq]
    · apply ih (before ++ [r])
      · intro old hold
        simp only [List.mem_append, List.mem_singleton] at hold
        rcases hold with hold | rfl
        · exact hbefore old hold
        · exact hr
      · intro old hold
        exact hrecords old (List.mem_cons_of_mem r hold)
      · intro old hold
        exact hvalid old (List.mem_cons_of_mem r hold)

theorem recordsBefore_valued (value : Address → Bool) (n : Nat) :
    Valued value (recordsBefore value n) := by
  intro r hr
  obtain ⟨stage, _, h⟩ := List.mem_map.mp hr
  rw [← h]
  rfl

theorem recordsBefore_valid (value : Address → Bool) (n : Nat) :
    RecordsValid (recordsBefore value n) := by
  intro r hr
  obtain ⟨stage, _, h⟩ := List.mem_map.mp hr
  rw [← h]
  have ha := Schedule.scheduled_admissible stage
  exact ⟨ha.2 rfl, ha.1⟩

theorem recordsBefore_coherent (value : Address → Bool) (n : Nat) :
    CoherentAfter [] (recordsBefore value n) :=
  coherentAfter_valued value [] (recordsBefore value n)
    (by intro r hr; cases hr) (recordsBefore_valued value n) (recordsBefore_valid value n)

/-- Source-to-online-decoder correctness at every completed source stage. -/
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

/-- Exact source relation, with correct addressing and no absent records filled in. -/
theorem emitted_exact (value : Address → Bool) (b : Bool) (a : Address) :
    Emitted (events value) b a ↔ Admissible .legacy a ∧ value a = b := by
  constructor
  · rintro ⟨t, hout⟩
    have hr := (out_iff_mem value b t a).mp hout
    obtain ⟨stage, _, h⟩ := List.mem_map.mp hr
    have ha : Schedule.scheduledAddress stage = a := congrArg Prod.fst h
    have hb : value (Schedule.scheduledAddress stage) = b := congrArg Prod.snd h
    exact ⟨by rw [← ha]; exact Schedule.scheduled_admissible stage, by rw [← ha]; exact hb⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨stage, _, hs⟩ := Schedule.schedule_fair a ha 0
    refine ⟨stage+1, (out_iff_mem value b (stage+1) a).mpr ?_⟩
    apply List.mem_map.mpr
    refine ⟨stage, List.mem_range.mpr (Nat.lt_succ_self stage), ?_⟩
    simp only [recordAt, hs, hb]

theorem no_error (value : Address → Bool) (t : Nat) : ¬ (events value).error t := by
  change ¬ (feedBits {} ((source value).prefixWord t)).numbers.failed = true
  rw [decode_source_prefix]
  simp [active]

/-- A closed completeness theorem for every total address-value function.
Its proof uses exact parsing, deterministic repeated values, and schedule fairness. -/
theorem complete (value : Address → Bool) : Complete (events value) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨t, ht⟩
    exact no_error value t ht
  · intro a ha
    cases hb : value a with
    | false => exact Or.inl ((emitted_exact value false a).mpr ⟨ha, hb⟩)
    | true => exact Or.inr ((emitted_exact value true a).mpr ⟨ha, hb⟩)
  · rintro a ⟨hf, ht⟩
    have hfalse := ((emitted_exact value false a).mp hf).2
    have htrue := ((emitted_exact value true a).mp ht).2
    rw [hfalse] at htrue
    cases htrue
  · intro b t a hout
    exact ((emitted_exact value b a).mp ⟨t, hout⟩).1

def recordValues (value : Address → Bool) : RecordValues :=
  fun n p xs => value ⟨n, p, xs⟩

theorem recordsAgree (value : Address → Bool) : RecordsAgree (events value) (recordValues value) := by
  intro n p xs hn hlen
  rw [emitted_exact]
  exact and_iff_right ⟨hlen, fun _ => hn⟩

/-- The producer's syntactic/calculus obligations remain visible, while
completeness, parsing and source addressing are now derived automatically. -/
theorem acceptance_iff_sound {T : TheoryPresentation}
    (N : NormalizationCertificate T) (B : BottomCertificates T)
    (value : Address → Bool) (records : EmittedRelation N (recordValues value))
    (view : ZeroView) (zeroRecords : ZeroEmittedRelation B view (events value)) :
    SoundnessAcceptance view (events value) ↔ T.Sound :=
  observer_soundness_reduction N B (recordValues value) records view (events value)
    (recordsAgree value) zeroRecords (complete value)

theorem formulaAcceptance_iff_sound {T : TheoryPresentation}
    (N : NormalizationCertificate T) (B : BottomCertificates T)
    (value : Address → Bool) (records : EmittedRelation N (recordValues value))
    (view : ZeroView) (zeroRecords : ZeroEmittedRelation B view (events value)) :
    FormulaAcceptance view (events value) ↔ T.Sound :=
  formula_soundness_reduction N B (recordValues value) records view (events value)
    (recordsAgree value) zeroRecords (complete value)

end PASoundness.Source
