import PASoundness.M236Observer

/-!
An explicit front door for the fixed M236 omega observer and small rejection
controls. The equivalence unfolds the existing observer; it does not identify
the literal machine with the source or prove any PA interpretation.
-/
namespace PASoundness.M236ObserverFrontDoor

open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Guarded trace acceptance is completeness and frame progress together with
a separate winning strategy for each positive-rank game. Strategies may
depend on both rank and game identifier and need not be computable. -/
theorem trace_accept_iff_complete_and_strategies {C : Type} (M : WordEventSystem C Bool) :
    TraceAccept M ↔
      (Complete (wordDecodedEvents M) ∧ FrameProgress M) ∧
        ∀ n, 0 < n → ∀ p, ∃ s : Strategy .ex n,
          Winning s (fun xs => Emitted (wordDecodedEvents M) false ⟨n, p, xs⟩) := by
  rw [TraceAccept, accept_iff_strategies (wordDecodedEvents M) rfl]
  tauto

/-- The same front door for the literal selected blank-start M236 table. -/
theorem selected_trace_iff_complete_and_strategies :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (Complete (wordDecodedEvents (machineWordSystem M236.machine M236.machineLabels)) ∧
        FrameProgress (machineWordSystem M236.machine M236.machineLabels)) ∧
      ∀ n, 0 < n → ∀ p, ∃ s : Strategy .ex n,
        Winning s (fun xs => Emitted (wordDecodedEvents (machineWordSystem M236.machine M236.machineLabels))
          false ⟨n, p, xs⟩) :=
  trace_accept_iff_complete_and_strategies (machineWordSystem M236.machine M236.machineLabels)

/-- The same statement with the complete-trace guard displayed: no error,
coverage of each legal address, no conflict, valid emitted addresses, and
eventual completion of every emitted bit. -/
theorem trace_accept_iff_explicit_guards {C : Type} (M : WordEventSystem C Bool) :
    TraceAccept M ↔
      (¬ ∃ t, (wordDecodedEvents M).error t) ∧
      (∀ a, Admissible .legacy a →
        Emitted (wordDecodedEvents M) false a ∨ Emitted (wordDecodedEvents M) true a) ∧
      (∀ a, ¬ (Emitted (wordDecodedEvents M) false a ∧ Emitted (wordDecodedEvents M) true a)) ∧
      WellAddressed (wordDecodedEvents M) ∧ FrameProgress M ∧
      (∀ n, 0 < n → ∀ p, ∃ s : Strategy .ex n,
        Winning s (fun xs => Emitted (wordDecodedEvents M) false ⟨n, p, xs⟩)) := by
  rw [trace_accept_iff_complete_and_strategies]
  simp only [Complete, BasicComplete, wordDecodedEvents]
  tauto

/-- Omitting even one legal address rejects the trace; absence is not a zero
record. This applies to arbitrary ordered-word systems, not a finite sample. -/
theorem missing_address_rejected {C : Type} (M : WordEventSystem C Bool) (a : Address)
    (ha : Admissible .legacy a)
    (hzero : ¬ Emitted (wordDecodedEvents M) false a)
    (hone : ¬ Emitted (wordDecodedEvents M) true a) : ¬ TraceAccept M := by
  intro h
  have hcover := (trace_accept_iff_explicit_guards M).mp h |>.2.1 a ha
  exact hcover.elim hzero hone

/-- On an accepted trace, each legal address has exactly one recorded Boolean
value. No default is needed on this guarded domain. -/
theorem accepted_unique_record {C : Type} (M : WordEventSystem C Bool)
    (h : TraceAccept M) (a : Address) (ha : Admissible .legacy a) :
    ∃! b, Emitted (wordDecodedEvents M) b a := by
  have hg := (trace_accept_iff_explicit_guards M).mp h
  rcases hg.2.1 a ha with hz | ho
  · refine ⟨false, hz, ?_⟩
    intro b hb
    cases b with
    | false => rfl
    | true => exact False.elim (hg.2.2.1 a ⟨hz, hb⟩)
  · refine ⟨true, ho, ?_⟩
    intro b hb
    cases b with
    | false => exact False.elim (hg.2.2.1 a ⟨hb, ho⟩)
    | true => rfl

/-- A finite bit list is emitted one bit per transition, then the system is
silent. These systems are controls, not the selected M236 machine. -/
def finiteWire (bits : List Bool) : WordEventSystem (List Bool) Bool where
  initial := bits
  step := fun remaining => match remaining with
    | [] => ([], [])
    | b :: rest => (rest, [b])

theorem finite_wire_physical (bits : List Bool) : (finiteWire bits).PhysicalBits := by
  intro n
  cases h : (finiteWire bits).run n with
  | nil => simp [finiteWire, h]
  | cons b rest => simp [finiteWire, h]

def silentWire : WordEventSystem Unit Bool where
  initial := ()
  step := fun _ => ((), [])

theorem silent_wire_physical : silentWire.PhysicalBits := by
  intro n
  simp [silentWire]

theorem silent_prefix (n : Nat) : silentWire.prefixWord n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [WordEventSystem.prefix_succ, ih]; rfl

theorem silent_no_error (t : Nat) : ¬ (wordDecodedEvents silentWire).error t := by
  simp [wordDecodedEvents, silent_prefix, feedBits]

/-- A completely silent trace misses the legal address `(1,0,[0])` and is
rejected by coverage, even though it never reports a malformed record. -/
theorem silent_missing_record_rejected : ¬ TraceAccept silentWire := by
  apply missing_address_rejected silentWire ⟨1, 0, [0]⟩ (by simp [Admissible])
  · rintro ⟨t, ht⟩
    simp [wordDecodedEvents, silent_prefix, feedBits] at ht
  · rintro ⟨t, ht⟩
    simp [wordDecodedEvents, silent_prefix, feedBits] at ht

def exampleAddress : Address := ⟨1, 0, [0]⟩

def conflictingWire : WordEventSystem (List Bool) Bool :=
  finiteWire (encodeFrame exampleAddress false ++ encodeFrame exampleAddress true)

/-- Repeating the same completed record is not a parser conflict. -/
theorem identical_duplicate_not_error :
    (feedBits {} (encodeFrame exampleAddress false ++ encodeFrame exampleAddress false)).numbers.failed = false := by decide

/-- Opposite completed records at the same address trigger a permanent
decoder error; identical records are separately allowed by the decoder. -/
theorem conflicting_wire_error : (wordDecodedEvents conflictingWire).error 11 := by
  change (feedBits {} (conflictingWire.prefixWord 11)).numbers.failed = true
  decide

theorem conflicting_records_rejected : ¬ TraceAccept conflictingWire := by
  intro h
  have hnoerror := ((trace_accept_iff_explicit_guards conflictingWire).mp h).1
  exact hnoerror ⟨11, conflicting_wire_error⟩

def malformedWire : WordEventSystem (List Bool) Bool := finiteWire [false]

/-- A zero rank is malformed, independently of later output. -/
theorem malformed_rank_rejected : ¬ TraceAccept malformedWire := by
  intro h
  have hnoerror := ((trace_accept_iff_explicit_guards malformedWire).mp h).1
  apply hnoerror
  refine ⟨1, ?_⟩
  change (feedBits {} (malformedWire.prefixWord 1)).numbers.failed = true
  decide

def unfinishedWire : WordEventSystem (List Bool) Bool := finiteWire [true]

theorem unfinished_run_succ (n : Nat) : unfinishedWire.run (n+1) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [WordEventSystem.run_succ, ih]; rfl

theorem unfinished_prefix_succ (n : Nat) : unfinishedWire.prefixWord (n+1) = [true] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [WordEventSystem.prefix_succ, ih, unfinished_run_succ]; rfl

/-- A single `1` followed by silence leaves an unfinished unary field forever,
so the explicit frame-progress guard rejects it. -/
theorem unfinished_frame_rejected : ¬ TraceAccept unfinishedWire := by
  intro h
  obtain ⟨u, hu, _, hones⟩ := h.2 1
  have hne : u ≠ 0 := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
  rw [unfinished_prefix_succ] at hones
  have hone : (feedBits {} [true]).ones = 1 := by decide
  omega

/-- Different game identifiers may need different first moves; the quantified
strategy family does not require a single move that wins them all. -/
theorem separate_game_witnesses :
    (∀ p, ∃ s : Strategy .ex 1, Winning s (fun xs => xs = [p])) ∧
      ¬ (∃ x : Nat, ∀ p : Nat, [x] = [p]) := by
  constructor
  · intro p
    exact ⟨.choose p (.done .all), rfl⟩
  · rintro ⟨x, hx⟩
    have h0 := hx 0
    have h1 := hx 1
    simp only [List.cons.injEq, and_true] at h0 h1
    omega

end PASoundness.M236ObserverFrontDoor
