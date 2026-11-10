import PASoundness.Source
import PASoundness.M236Quotient

/-!
The positive-rank addressed observer used by the M236 construction. This
module contains no arithmetic theory or evaluation procedure. It keeps the
legacy unary wire decoder, but does not add the separate compact-suffix zero
channel used by the old PA926 producer.

A strategy is a finite-height, potentially infinitely branching tree. It need
not be computable or uniform across addresses or ranks. Each existential node
chooses a natural move; each universal node has a continuation for every
natural move.
-/
namespace PASoundness.M236Observer

open PASoundness.Observer PASoundness.UnaryCodec

inductive Strategy : Polarity → Nat → Type where
  | done (q : Polarity) : Strategy q 0
  | choose {n : Nat} : Nat → Strategy .all n → Strategy .ex (n + 1)
  | respond {n : Nat} : (Nat → Strategy .ex n) → Strategy .all (n + 1)

/-- The strategy wins if the matrix holds for every universal response. -/
def Winning : {q : Polarity} → {n : Nat} → Strategy q n → (List Nat → Prop) → Prop
  | _, 0, .done _, P => P []
  | _, _ + 1, .choose x s, P => Winning s (fun xs => P (x :: xs))
  | _, _ + 1, .respond f, P => ∀ x, Winning (f x) (fun xs => P (x :: xs))

/-- Finite alternating truth is exactly the existence of a strategy tree.
Classical choice is used in the universal branch, with no computability
requirement imposed on the strategy. -/
theorem strategy_iff (q : Polarity) (n : Nat) (P : List Nat → Prop) :
    (∃ s : Strategy q n, Winning s P) ↔ altPrefix q n P := by
  classical
  induction n generalizing q P with
  | zero =>
      constructor
      · rintro ⟨s, hs⟩
        cases s
        exact hs
      · intro h
        exact ⟨.done q, h⟩
  | succ n ih =>
      cases q with
      | ex =>
          constructor
          · rintro ⟨s, hs⟩
            cases s with
            | choose x child =>
              exact ⟨x, (ih .all _).mp ⟨child, hs⟩⟩
          · rintro ⟨x, hx⟩
            obtain ⟨child, hc⟩ := (ih .all _).mpr hx
            exact ⟨.choose x child, hc⟩
      | all =>
          constructor
          · rintro ⟨s, hs⟩
            cases s with
            | respond child =>
              intro x
              exact (ih .ex _).mp ⟨child x, hs x⟩
          · intro h
            have he : ∀ x, ∃ s : Strategy .ex n,
                Winning s (fun xs => P (x :: xs)) := by
              intro x
              exact (ih .ex _).mpr (h x)
            choose f hf using he
            exact ⟨.respond f, hf⟩

/-- Guarded all-positive-rank acceptance, without a separate rank-zero test. -/
def Accept (E : EventStructure) : Prop :=
  Complete E ∧ ∀ n, 0 < n → ¬ RawFailure E n

/-- On an admissible address of a complete trace, lack of rejection is a
recorded zero, not a default for missing data. -/
theorem no_reject_iff_zero {E : EventStructure} (hc : Complete E)
    (a : Address) (ha : Admissible E.profile a) :
    (¬ Emitted E true a) ↔ Emitted E false a := by
  constructor
  · intro hn
    rcases hc.1.2.1 a ha with hz | ho
    · exact hz
    · exact False.elim (hn ho)
  · intro hz ho
    exact hc.1.2.2 a ⟨hz, ho⟩

/-- On complete legacy traces the observer asks for a winning strategy
separately for every positive rank and game index. -/
theorem accept_iff_strategies (E : EventStructure) (hp : E.profile = .legacy) :
    Accept E ↔ Complete E ∧ ∀ n, 0 < n → ∀ p,
      ∃ s : Strategy .ex n,
        Winning s (fun xs => Emitted E false ⟨n, p, xs⟩) := by
  classical
  unfold Accept
  apply and_congr_right
  intro hc
  apply forall_congr'
  intro n
  apply imp_congr_right
  intro hn
  simp only [RawFailure, not_exists]
  apply forall_congr'
  intro p
  rw [strategy_iff]
  have hm : altPrefix .all n (fun xs => Emitted E true ⟨n, p, xs⟩) ↔
      altPrefix .all n (fun xs => ¬ Emitted E false ⟨n, p, xs⟩) := by
    apply altPrefix_congr_length
    intro xs hlen
    have ha : Admissible E.profile ⟨n, p, xs⟩ := by
      simp [Admissible, hp, hlen, hn]
    constructor
    · intro ht hz
      exact (no_reject_iff_zero hc _ ha).mpr hz ht
    · intro h
      by_contra ht
      exact h ((no_reject_iff_zero hc _ ha).mp ht)
  rw [hm, altPrefix_duality]
  simp [Polarity.flip]

/-- Each already-emitted bit is eventually inside a completed frame. A
boundary after the first `t` transitions has no unfinished unary field or
unfinished record. This explicitly retains the wire-progress clause of the
published observer; it is not assumed to follow from `Complete` here. -/
def FrameProgress {C : Type} (M : WordEventSystem C Bool) : Prop :=
  ∀ t, ∃ u, t ≤ u ∧
    (feedBits {} (M.prefixWord u)).numbers.cursor = .rank ∧
    (feedBits {} (M.prefixWord u)).ones = 0

/-- Fixed theory-independent positive-rank acceptance for an ordered wire.
Completeness supplies the error, missing-record and conflict guards, while
`FrameProgress` makes the unfinished-frame guard explicit. -/
def TraceAccept {C : Type} (M : WordEventSystem C Bool) : Prop :=
  Accept (wordDecodedEvents M) ∧ FrameProgress M

/-- The observer depends only on completed receipts and permanent errors. -/
theorem accept_preserved {E F : EventStructure} (h : SameReceipts E F) :
    Accept E ↔ Accept F := by
  unfold Accept
  apply and_congr (complete_preserved h)
  apply forall_congr'
  intro n
  exact imp_congr_right (fun _ => not_congr (rawFailure_preserved h n))

/-- The previously proved physical quotient preserves the actual positive-rank
observer, without assuming any producer semantics or PA soundness. -/
theorem quotient_acceptance :
    Accept (wordDecodedEvents (machineWordSystem M236.raw M236.rawLabels)) ↔
      Accept (wordDecodedEvents (machineWordSystem M236.machine M236.machineLabels)) :=
  accept_preserved (sameOutput_sameReceipts M236.same_output)

/-- The fair, frame-at-a-time source already has all records and no conflicts.
This theorem is parametrized by its total value function; it does not claim
that M236 implements that function. -/
theorem source_accept_iff_strategies (value : Address → Bool) :
    Accept (Source.events value) ↔ ∀ n, 0 < n → ∀ p,
      ∃ s : Strategy .ex n,
        Winning s (fun xs => value ⟨n, p, xs⟩ = false) := by
  rw [accept_iff_strategies (Source.events value) rfl]
  simp only [Source.complete, true_and]
  apply forall_congr'
  intro n
  apply imp_congr_right
  intro hn
  apply forall_congr'
  intro p
  rw [strategy_iff, strategy_iff]
  apply altPrefix_congr_length
  intro xs hlen
  rw [Source.emitted_exact]
  simp [Admissible, hlen, hn]

/-- Each abstract source step ends at a completed frame, even though the
individual fields and finite numbers have no global bound. -/
theorem source_frame_progress (value : Address → Bool) :
    FrameProgress (Source.source value) := by
  intro t
  refine ⟨t, Nat.le_refl t, ?_, ?_⟩
  · rw [Source.decode_source_prefix]; rfl
  · rw [Source.decode_source_prefix]

/-- Exact accepted source condition in terms of separate finite game
strategies. This still has an arbitrary total record-value function. -/
theorem source_trace_accept_iff_strategies (value : Address → Bool) :
    TraceAccept (Source.source value) ↔ ∀ n, 0 < n → ∀ p,
      ∃ s : Strategy .ex n,
        Winning s (fun xs => value ⟨n, p, xs⟩ = false) := by
  change (Accept (Source.events value) ∧ FrameProgress (Source.source value)) ↔ _
  rw [and_iff_left (source_frame_progress value), source_accept_iff_strategies]

/-- Exact per-time word equality transports the frame-progress guard across
the final quotient, including a potential partially completed frame. -/
theorem quotient_frame_progress :
    FrameProgress (machineWordSystem M236.raw M236.rawLabels) ↔
      FrameProgress (machineWordSystem M236.machine M236.machineLabels) := by
  unfold FrameProgress
  simp only [← M236.prefix_eq]

/-- The full guarded positive-rank wire observer is invariant under the
actual raw-to-selected quotient. This does not establish acceptance. -/
theorem quotient_trace_acceptance :
    TraceAccept (machineWordSystem M236.raw M236.rawLabels) ↔
      TraceAccept (machineWordSystem M236.machine M236.machineLabels) :=
  and_congr quotient_acceptance quotient_frame_progress

/-- The machine's online singleton-bit decoder and word-prefix decoder have
the same positive-rank acceptance. -/
theorem selected_online_acceptance :
    Accept (decodedEvents (eventTrace (machineWordSystem M236.machine M236.machineLabels))) ↔
      Accept (wordDecodedEvents (machineWordSystem M236.machine M236.machineLabels)) :=
  accept_preserved (online_sameReceipts_word _ (machineWordSystem_physicalBits _ _))

/-- One rejected tuple does not defeat an existential strategy. -/
theorem rejecting_tuple_not_strategy_failure :
    (∃ s : Strategy .ex 1, Winning s (fun xs => xs ≠ [0])) ∧ ¬ ([0] ≠ [0]) := by
  constructor
  · exact ⟨.choose 1 (.done .all), by simp [Winning]⟩
  · simp

/-- The final choice may depend on an arbitrary preceding universal move. -/
theorem strategy_responds_to_unbounded_move :
    ∃ s : Strategy .ex 3,
      Winning s (fun xs => xs[2]? = xs[1]?) := by
  refine ⟨.choose 0 (.respond (fun y => .choose y (.done .all))), ?_⟩
  intro y
  rfl

end PASoundness.M236Observer
