import PASoundness.M236ObserverFrontDoor

/-!
A bounded binding between the observer's cofinal clean-boundary condition
and an event-indexed condition closer to the historical progress clause.
The equivalence itself does not assert that a clean boundary is legal after
parser failure. The no-error guard is needed for that reading. The separate
finite-word theorem identifying each bit's containing legal frame is not
established here.
-/
namespace PASoundness.M236FrameProgressBinding

open PASoundness PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open PASoundness.M236ObserverFrontDoor
open Shared.Beeping.Machines

/-- A boundary of the decoder at physical time `t`. This has no error
requirement; see `malformed_frame_progress` below. -/
def CleanBoundary {C : Type} (M : WordEventSystem C Bool) (t : Nat) : Prop :=
  (feedBits {} (M.prefixWord t)).numbers.cursor = .rank ∧
  (feedBits {} (M.prefixWord t)).ones = 0

/-- Every emitting transition is followed by some clean boundary. With
singleton-bit physical output this is the time-indexed completion condition
for each emitted bit, subject to separately establishing that clean boundaries
correspond to completed *legal* frames on an error-free run. -/
def EmissionBoundaryProgress {C : Type} (M : WordEventSystem C Bool) : Prop :=
  ∀ t, (M.step (M.run t)).2 ≠ [] → ∃ u, t < u ∧ CleanBoundary M u

/-- This is valid even for word-valued steps: every nonempty transition word
is covered by a later clean boundary. Silence needs no such witness. -/
theorem frameProgress_iff_emissionBoundaryProgress {C : Type}
    (M : WordEventSystem C Bool) : FrameProgress M ↔ EmissionBoundaryProgress M := by
  constructor
  · intro h t _
    obtain ⟨u, hle, hc, ho⟩ := h (t + 1)
    exact ⟨u, by omega, hc, ho⟩
  · intro h t
    induction t with
    | zero =>
      refine ⟨0, Nat.le_refl 0, ?_⟩
      simp [feedBits]
    | succ t ih =>
      by_cases he : (M.step (M.run t)).2 = []
      · obtain ⟨u, htu, hu⟩ := ih
        by_cases htu' : t + 1 ≤ u
        · exact ⟨u, htu', hu⟩
        · have h : u = t := by omega
          subst u
          refine ⟨t + 1, Nat.le_refl _, ?_⟩
          simpa [CleanBoundary, WordEventSystem.prefix_succ, he] using hu
      · obtain ⟨u, hu, hb⟩ := h t he
        exact ⟨u, by omega, hb⟩

/-- On an error-free run every boundary obtained from the equivalent progress
conditions is additionally parser-good. This theorem makes no new claim about
record coverage or identification with the manuscript's independently defined
legal-frame membership predicate. -/
theorem error_free_emission_boundaries {C : Type} (M : WordEventSystem C Bool)
    (hgood : ∀ t, (feedBits {} (M.prefixWord t)).numbers.failed = false)
    (hp : FrameProgress M) :
    ∀ t, (M.step (M.run t)).2 ≠ [] → ∃ u, t < u ∧ CleanBoundary M u ∧
      (feedBits {} (M.prefixWord u)).numbers.failed = false := by
  intro t he
  obtain ⟨u, htu, hb⟩ := (frameProgress_iff_emissionBoundaryProgress M).mp hp t he
  exact ⟨u, htu, hb, hgood u⟩

theorem malformed_run_succ (n : Nat) : malformedWire.run (n+1) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [WordEventSystem.run_succ, ih]; rfl

theorem malformed_prefix_succ (n : Nat) : malformedWire.prefixWord (n+1) = [false] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [WordEventSystem.prefix_succ, ih, malformed_run_succ]; rfl

/-- A malformed rank-zero trace can satisfy `FrameProgress`: the failed
decoder happens to have the rank cursor and zero pending ones. Thus no-error
cannot be dropped when relating clean boundaries to legal completed frames. -/
theorem malformed_frame_progress : FrameProgress malformedWire := by
  intro t
  refine ⟨t + 1, by omega, ?_, ?_⟩ <;>
    rw [malformed_prefix_succ] <;> decide

theorem malformed_progress_but_rejected :
    FrameProgress malformedWire ∧ ¬ TraceAccept malformedWire :=
  ⟨malformed_frame_progress, malformed_rank_rejected⟩

/-- Whenever the numeric parser appends a record, its cursor is back at the
start of the next frame. -/
theorem onNumber_cursor_of_record_change (d : NumberDecoder) (v : Nat)
    (h : (onNumber d v).records ≠ d.records) : (onNumber d v).cursor = .rank := by
  cases hf : d.failed with
  | true => simp [onNumber, hf] at h
  | false =>
    cases hc : d.cursor with
    | rank =>
      by_cases hz : v = 0 <;> simp [onNumber, hf, hc, hz, active] at h
    | body remaining fields =>
      cases remaining with
      | zero => simp [onNumber, hf, hc] at h
      | succ r =>
        cases r with
        | zero =>
          simp only [onNumber, hf, Bool.false_eq_true, ↓reduceIte, hc]
          unfold finish
          split <;> simp_all; split <;> rfl
        | succ r => simp [onNumber, hf, hc, active] at h

theorem feedBit_boundary_of_record_change (d : Decoder) (b : Bool)
    (h : (feedBit d b).numbers.records ≠ d.numbers.records) :
    (feedBit d b).numbers.cursor = .rank ∧ (feedBit d b).ones = 0 := by
  cases hf : d.numbers.failed <;> cases b <;> simp [feedBit, hf] at h ⊢
  exact onNumber_cursor_of_record_change d.numbers d.ones h

theorem physical_record_change_boundary {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) (t : Nat)
    (hchange : (feedBits {} (M.prefixWord (t+1))).numbers.records ≠
      (feedBits {} (M.prefixWord t)).numbers.records) : CleanBoundary M (t+1) := by
  have hlen := hphys t
  cases hw : (M.step (M.run t)).2 with
  | nil =>
    simp [WordEventSystem.prefix_succ, hw] at hchange
  | cons b bs =>
    cases bs with
    | nil =>
      unfold CleanBoundary
      rw [WordEventSystem.prefix_succ, hw, feedBits_append] at hchange ⊢
      simpa [feedBits] using
        feedBit_boundary_of_record_change (feedBits {} (M.prefixWord t)) b (by
          simpa [feedBits] using hchange)
    | cons b' bs => simp [hw] at hlen

theorem exists_nat_beyond_list (xs : List Nat) : ∃ b, ∀ x ∈ xs, x < b := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨max a b + 1, ?_⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := hb x hx
      omega

/-- If every rank-one address `(1,p,[0])` is eventually recorded by a
physical-bit system, clean frame boundaries occur cofinally. Only this fixed
infinite family of coverage is needed, not error-freedom or soundness. -/
theorem frameProgress_of_rank_one_coverage {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits)
    (hcover : ∀ p, ∃ b u,
      (⟨1, p, [0]⟩, b) ∈ (feedBits {} (M.prefixWord u)).numbers.records) :
    FrameProgress M := by
  intro t
  classical
  by_contra hno
  have hbad : ∀ u, t ≤ u → ¬ CleanBoundary M u := by
    intro u htu hb
    apply hno
    exact ⟨u, htu, hb⟩
  let records := (feedBits {} (M.prefixWord t)).numbers.records
  obtain ⟨p, hp⟩ := exists_nat_beyond_list (records.map (fun r => r.1.certificate))
  have hfresh (b : Bool) : ((⟨1,p,[0]⟩ : PASoundness.Observer.Address), b) ∉ records := by
    intro hin
    have hlt := hp p (List.mem_map.mpr ⟨(⟨1,p,[0]⟩, b), hin, rfl⟩)
    omega
  obtain ⟨b, u, hu⟩ := hcover p
  have heq : ∀ k, (feedBits {} (M.prefixWord (t+k))).numbers.records = records := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hs : (feedBits {} (M.prefixWord ((t+k)+1))).numbers.records =
          (feedBits {} (M.prefixWord (t+k))).numbers.records := by
        by_contra hn
        exact hbad ((t+k)+1) (by omega) (physical_record_change_boundary M hphys (t+k) hn)
      simpa [Nat.add_assoc] using hs.trans ih
  obtain ⟨tail, htail⟩ := M.prefix_extends (Nat.le_max_right t u)
  have hlater : ((⟨1,p,[0]⟩ : PASoundness.Observer.Address), b) ∈
      (feedBits {} (M.prefixWord (max t u))).numbers.records := by
    rw [htail, feedBits_append]
    exact feedBits_records_mono _ _ _ hu
  have htime : max t u = t + (max t u - t) := by omega
  rw [htime, heq] at hlater
  exact hfresh b hlater

/-- The existing complete-trace guard includes the necessary rank-one
coverage, so it entails frame progress for every physical-bit system. This
does not assert that the actual selected machine has a complete trace. -/
theorem frameProgress_of_complete_physical {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) (hc : Complete (wordDecodedEvents M)) : FrameProgress M := by
  apply frameProgress_of_rank_one_coverage M hphys
  intro p
  have ha : Admissible (wordDecodedEvents M).profile ⟨1, p, [0]⟩ := by
    simp [Admissible, wordDecodedEvents]
  rcases hc.1.2.1 ⟨1, p, [0]⟩ ha with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact ⟨false, u, hu⟩
  · exact ⟨true, u, hu⟩

/-- For singleton-bit traces the explicit progress guard is redundant under
the complete-trace guard; it remains stated separately in `TraceAccept`. -/
theorem physical_traceAccept_iff_accept {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) : TraceAccept M ↔ Accept (wordDecodedEvents M) := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, frameProgress_of_complete_physical M hphys h.1⟩

/-- Specialization to the actual selected literal blank-start machine; this
is an equivalence of predicates, not an assertion that either side holds. -/
theorem selected_traceAccept_iff_accept :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      Accept (wordDecodedEvents (machineWordSystem M236.machine M236.machineLabels)) :=
  physical_traceAccept_iff_accept _ (machineWordSystem_physicalBits _ _)

end PASoundness.M236FrameProgressBinding
