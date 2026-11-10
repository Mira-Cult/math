import PASoundness.M236FrameSegmentation
import PASoundness.M236FirstRecord

/-!
A proposed formal binding of the four historical `WellFormedTotal` clauses
for physical singleton-bit streams. Source: omega-semantics.md §§1–2 at
60c6f2c22ddd50d3ba40e2ca94a4a63a87e74a0c. The syntax of frames and the
finite decoder are the explicitly fixed `UnaryCodec` definitions. This module
proves no machine implementation or PA-soundness result.
-/
namespace PASoundness.M236HistoricalGuard

open PASoundness PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open PASoundness.M236FrameSegmentation
open Shared.Beeping.Machines

/-- An actual completed legal frame in the output word, independently of the
decoder ledger. The prefix before it is a sequence of legal frames; the tail
may contain any bits and is not presumed to be a completed frame. -/
def FrameSeen {C : Type} (M : WordEventSystem C Bool) (a : Address) (b : Bool) : Prop :=
  ∃ t before suffix, RecordsValid (before ++ [(a,b)]) ∧
    M.prefixWord t = encodeRecords before ++ encodeFrame a b ++ suffix

/-- Clause 1: the fixed physical alphabet is guaranteed by the `Bool` word
and `PhysicalBits` hypothesis; this is its no-parser-error component. -/
def NoError {C : Type} (M : WordEventSystem C Bool) : Prop :=
  ∀ t, (feedBits {} (M.prefixWord t)).numbers.failed = false

/-- Clause 3: independently located completed frames agree at each address. -/
def NoConflict {C : Type} (M : WordEventSystem C Bool) : Prop :=
  ∀ a b c, FrameSeen M a b → FrameSeen M a c → b = c

/-- Clause 4: every legal positive-rank address has a completed frame. -/
def FullCoverage {C : Type} (M : WordEventSystem C Bool) : Prop :=
  ∀ a, ValidAddress a → ∃ b, FrameSeen M a b

/-- Manuscript guard for a physical execution. The physical alphabet
condition is an explicit outer hypothesis of the comparison theorem. -/
def WellFormedTotal {C : Type} (M : WordEventSystem C Bool) : Prop :=
  NoError M ∧ EveryBitInCompletedFrame M ∧ NoConflict M ∧ FullCoverage M

theorem noError_iff {C : Type} (M : WordEventSystem C Bool) :
    NoError M ↔ ¬ ∃ t, (wordDecodedEvents M).error t := by
  unfold NoError wordDecodedEvents
  simp only [not_exists]
  constructor
  · intro h t
    rw [h t]
    decide
  · intro h t
    cases ht : (feedBits {} (M.prefixWord t)).numbers.failed with
    | false => rfl
    | true => exact False.elim (h t ht)

theorem word_wellAddressed {C : Type} (M : WordEventSystem C Bool) :
    WellAddressed (wordDecodedEvents M) := by
  intro b t a h
  have hv : RecordsValid (feedBits {} (M.prefixWord t)).numbers.records := by
    apply feedBits_records_valid
    intro r hr
    cases hr
  have ha := hv (a,b) h
  exact ⟨ha.2, fun _ => ha.1⟩

/-- Under no error, a ledger receipt corresponds to an actual complete legal
frame in the raw output, with any later bits retained as a suffix. -/
theorem frameSeen_of_emitted {C : Type} (M : WordEventSystem C Bool)
    (hgood : NoError M) {a : Address} {b : Bool}
    (hem : Emitted (wordDecodedEvents M) b a) : FrameSeen M a b := by
  obtain ⟨t, ht⟩ := hem
  change (a,b) ∈ (feedBits {} (M.prefixWord t)).numbers.records at ht
  obtain ⟨before, after, hrecords⟩ := List.mem_iff_append.mp ht
  have hform := parseForm_feedBits ({} : Decoder) (M.prefixWord t) rfl (hgood t)
  have hv : RecordsValid (feedBits {} (M.prefixWord t)).numbers.records := by
    apply feedBits_records_valid
    intro r hr
    cases hr
  refine ⟨t, before, encodeRecords after ++
    (encodeFields (pendingFields (feedBits {} (M.prefixWord t))) ++
      List.replicate (feedBits {} (M.prefixWord t)).ones true), ?_, ?_⟩
  · intro r hr
    apply hv r
    rw [hrecords]
    simp only [List.mem_append, List.mem_singleton] at hr ⊢
    rcases hr with hr | rfl
    · exact Or.inl hr
    · exact Or.inr (by simp)
  · simpa [parseForm, pendingFields, encodeRecords, encodeRecords_append, hrecords, encodeFields,
      List.append_assoc] using hform

/-- An error-free decode of legal frame encodings records each frame in order.
Proof contributed by Codex subagent `/root/frame_binding/inverse`. -/
theorem encodeRecords_no_error (before records : List Record)
    (hv : RecordsValid records)
    (hg : (feedBits ⟨active .rank before, 0⟩ (encodeRecords records)).numbers.failed = false) :
    feedBits ⟨active .rank before, 0⟩ (encodeRecords records) =
      ⟨active .rank (before ++ records), 0⟩ := by
  induction records generalizing before with
  | nil => simp [encodeRecords, feedBits]
  | cons r rs ih =>
    have hr : ValidAddress r.1 := hv r (by simp)
    have hrest : RecordsValid rs := by
      intro q hq
      exact hv q (by simp [hq])
    rw [encodeRecords, feedBits_append, decode_encodeFrame r.1 r.2 before hr] at hg ⊢
    by_cases hc : Compatible before r
    · simp only [Prod.mk.eta, if_pos hc] at hg ⊢
      simpa [List.append_assoc] using ih (before ++ [r]) hrest hg
    · simp only [Prod.mk.eta, if_neg hc] at hg
      rw [feedBits_failed _ _ (by rfl)] at hg
      contradiction

/-- On an error-free physical trace, every independently located legal frame
is present in the decoder ledger at its physical completion boundary. -/
theorem emitted_of_frameSeen {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) (hgood : NoError M) {a : Address} {b : Bool}
    (hseen : FrameSeen M a b) : Emitted (wordDecodedEvents M) b a := by
  obtain ⟨t, before, suffix, hvalid, hword⟩ := hseen
  have hword' : M.prefixWord t = encodeRecords (before ++ [(a,b)]) ++ suffix := by
    simpa [encodeRecords_append, encodeRecords, List.append_assoc] using hword
  obtain ⟨u, _, _, hu⟩ := physical_reaches_output_prefix M hphys
    (t := 0) (u := t) (w := encodeRecords (before ++ [(a,b)])) (suffix := suffix)
    (by omega) (by simp) hword'
  have hg := hgood u
  rw [hu] at hg
  have he := encodeRecords_no_error [] (before ++ [(a,b)]) hvalid (by simpa [active] using hg)
  refine ⟨u, ?_⟩
  change (a,b) ∈ (feedBits {} (M.prefixWord u)).numbers.records
  rw [hu]
  change (a,b) ∈ (feedBits ⟨active .rank [], 0⟩ (encodeRecords (before ++ [(a,b)]))).numbers.records
  rw [he]
  simp [active]

theorem frameSeen_iff_emitted {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) (hgood : NoError M) (a : Address) (b : Bool) :
    FrameSeen M a b ↔ Emitted (wordDecodedEvents M) b a :=
  ⟨emitted_of_frameSeen M hphys hgood, frameSeen_of_emitted M hgood⟩

theorem noConflict_iff {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) (hgood : NoError M) :
    NoConflict M ↔ ∀ a, ¬ (Emitted (wordDecodedEvents M) false a ∧
      Emitted (wordDecodedEvents M) true a) := by
  constructor
  · intro hn a ⟨hf, ht⟩
    have h := hn a false true ((frameSeen_iff_emitted M hphys hgood a false).mpr hf)
      ((frameSeen_iff_emitted M hphys hgood a true).mpr ht)
    cases h
  · intro hn a b c hb hc
    have hb' := (frameSeen_iff_emitted M hphys hgood a b).mp hb
    have hc' := (frameSeen_iff_emitted M hphys hgood a c).mp hc
    cases b <;> cases c <;> simp_all

theorem coverage_iff {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) (hgood : NoError M) :
    FullCoverage M ↔ ∀ a, Admissible (wordDecodedEvents M).profile a →
      Emitted (wordDecodedEvents M) false a ∨ Emitted (wordDecodedEvents M) true a := by
  constructor
  · intro hc a ha
    have hv : ValidAddress a := ⟨ha.2 rfl, ha.1⟩
    obtain ⟨b, hb⟩ := hc a hv
    have he := (frameSeen_iff_emitted M hphys hgood a b).mp hb
    cases b <;> simp_all
  · intro hc a ha
    have hadm : Admissible (wordDecodedEvents M).profile a := ⟨ha.2, fun _ => ha.1⟩
    rcases hc a hadm with hf | ht
    · exact ⟨false, (frameSeen_iff_emitted M hphys hgood a false).mpr hf⟩
    · exact ⟨true, (frameSeen_iff_emitted M hphys hgood a true).mpr ht⟩

/-- The four explicit historical guard clauses coincide with the existing
complete receipt guard and frame progress on error-free physical bit streams.
The physical hypothesis supplies the fixed event alphabet; `FrameSeen` refers
to actual legal frame encodings in the output, not ledger membership. -/
theorem wellFormedTotal_iff_observer_guard {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) : WellFormedTotal M ↔
      Complete (wordDecodedEvents M) ∧ FrameProgress M := by
  constructor
  · rintro ⟨he, hb, hn, hc⟩
    refine ⟨⟨⟨(noError_iff M).mp he, (coverage_iff M hphys he).mp hc,
      (noConflict_iff M hphys he).mp hn⟩, word_wellAddressed M⟩, ?_⟩
    exact (physical_frameProgress_iff_everyBitInCompletedFrame M hphys he).mpr hb
  · rintro ⟨hc, hp⟩
    have he : NoError M := (noError_iff M).mpr hc.1.1
    exact ⟨he, (physical_frameProgress_iff_everyBitInCompletedFrame M hphys he).mp hp,
      (noConflict_iff M hphys he).mpr hc.1.2.2,
      (coverage_iff M hphys he).mpr hc.1.2.1⟩

/-- The manuscript's value function, using the first eligible online
completion before permanent error and defaulting to false if absent. This is
the transition-event interface rather than cumulative prefix membership. -/
noncomputable def historicalValues {C : Type} (M : WordEventSystem C Bool) : RecordValues :=
  PASoundness.M236FirstRecord.values (decodedEvents (eventTrace M))

/-- Historical guarded acceptance: the four explicit guard clauses followed
by the dual finite alternating rank tests on first-record values. -/
def HistoricalAccept {C : Type} (M : WordEventSystem C Bool) : Prop :=
  WellFormedTotal M ∧ ∀ n, 0 < n → ¬ RankFailure (historicalValues M) n

/-- On physical streams the manuscript-style first-record observer and the
existing Lean trace observer are equivalent, without producer correctness or
PA soundness assumptions. The theorem binds these explicit Lean definitions to
each other; assessment of the transcription against the pinned manuscript is
a separate review obligation. -/
theorem historicalAccept_iff_traceAccept {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) : HistoricalAccept M ↔ TraceAccept M := by
  have hsame := online_sameReceipts_word M hphys
  have hacc : Accept (wordDecodedEvents M) ↔
      Complete (wordDecodedEvents M) ∧ ∀ n, 0 < n → ¬ RankFailure (historicalValues M) n := by
    calc
      Accept (wordDecodedEvents M) ↔ Accept (decodedEvents (eventTrace M)) :=
        (accept_preserved hsame).symm
      _ ↔ Complete (decodedEvents (eventTrace M)) ∧
          ∀ n, 0 < n → ¬ RankFailure (historicalValues M) n :=
        PASoundness.M236FirstRecord.accept_iff_firstValues _ rfl
      _ ↔ Complete (wordDecodedEvents M) ∧
          ∀ n, 0 < n → ¬ RankFailure (historicalValues M) n := by
        rw [complete_preserved hsame]
  unfold HistoricalAccept TraceAccept
  rw [wellFormedTotal_iff_observer_guard M hphys, hacc]
  tauto

/-- Literal blank-start M236 specialization. This compares predicates; it does
not assert that either predicate is satisfied. -/
theorem selected_historicalAccept_iff_traceAccept :
    HistoricalAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      TraceAccept (machineWordSystem M236.machine M236.machineLabels) :=
  historicalAccept_iff_traceAccept _ (machineWordSystem_physicalBits _ _)

end PASoundness.M236HistoricalGuard
