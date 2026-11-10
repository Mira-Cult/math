import PASoundness.UnaryCodec
import PASoundness.Machine

/-!
Composition of the verified online wire decoder with ordered-word simulation.
The observer is invariant because finite completed receipts and fatal errors
are preserved. This is derived from local positive simulation blocks, not
assumed as an opaque decoded-trace correspondence field.
-/
namespace PASoundness.UnaryCodec

open PASoundness.Observer Shared.Beeping.Machines

/-- Auxiliary prefix view. Time `t` records which receipts have been completed
after the first `t` source transitions. Source transitions may emit whole finite
words. The next theorem relates this view to actual online completion events
for physical singleton-bit traces. -/
def wordDecodedEvents {C : Type} (M : WordEventSystem C Bool) : EventStructure where
  profile := .legacy
  out := fun b t a => (a, b) ∈ (feedBits {} (M.prefixWord t)).numbers.records
  error := fun t => (feedBits {} (M.prefixWord t)).numbers.failed = true

theorem sameOutput_receipt_transfer {S T : Type} {source : WordEventSystem S Bool}
    {target : WordEventSystem T Bool} (h : SameOutput source target)
    (b : Bool) (a : Address) :
    Emitted (wordDecodedEvents source) b a → Emitted (wordDecodedEvents target) b a := by
  rintro ⟨n, hr⟩
  have hp : source.OutputPrefix (source.prefixWord n) := ⟨n, [], by simp⟩
  obtain ⟨m, suffix, hm⟩ := (h _).mp hp
  refine ⟨m, ?_⟩
  change (a, b) ∈ (feedBits {} (target.prefixWord m)).numbers.records
  rw [hm, feedBits_append]
  exact feedBits_records_mono _ suffix (a, b) hr

theorem sameOutput_error_transfer {S T : Type} {source : WordEventSystem S Bool}
    {target : WordEventSystem T Bool} (h : SameOutput source target) :
    (∃ t, (wordDecodedEvents source).error t) → ∃ t, (wordDecodedEvents target).error t := by
  rintro ⟨n, hr⟩
  have hp : source.OutputPrefix (source.prefixWord n) := ⟨n, [], by simp⟩
  obtain ⟨m, suffix, hm⟩ := (h _).mp hp
  refine ⟨m, ?_⟩
  change (feedBits {} (target.prefixWord m)).numbers.failed = true
  rw [hm, feedBits_append, feedBits_failed _ _ hr]
  exact hr

theorem sameOutput_sameReceipts {S T : Type} {source : WordEventSystem S Bool}
    {target : WordEventSystem T Bool} (h : SameOutput source target) :
    SameReceipts (wordDecodedEvents source) (wordDecodedEvents target) where
  profile := rfl
  errors := ⟨sameOutput_error_transfer h, sameOutput_error_transfer (fun w => (h w).symm)⟩
  emitted := fun b a => ⟨sameOutput_receipt_transfer h b a,
    sameOutput_receipt_transfer (fun w => (h w).symm) b a⟩

theorem sameOutput_observer_preserved {S T : Type} {source : WordEventSystem S Bool}
    {target : WordEventSystem T Bool} (h : SameOutput source target) (view : ZeroView) :
    SoundnessAcceptance view (wordDecodedEvents source) ↔
      SoundnessAcceptance view (wordDecodedEvents target) :=
  acceptance_preserved view (sameOutput_sameReceipts h)

def eventTrace {C : Type} (M : WordEventSystem C Bool) (t : Nat) : Option Bool :=
  ((M.step (M.run t)).2).head?

theorem word_eq_eventTrace {C : Type} (M : WordEventSystem C Bool)
    (hphysical : M.PhysicalBits) (t : Nat) :
    (M.step (M.run t)).2 = (eventTrace M t).toList := by
  cases hw : (M.step (M.run t)).2 with
  | nil => simp [eventTrace, hw]
  | cons b bs =>
    cases bs with
    | nil => simp [eventTrace, hw]
    | cons c cs =>
      have hlen := hphysical t
      rw [hw] at hlen
      simp at hlen

theorem feedEvent_eq_feedBits (d : Decoder) (event : Option Bool) :
    feedEvent d event = feedBits d event.toList := by
  cases event <;> rfl

/-- Exact online execution agrees with decoding the flattened word prefix.
Singleton legality is used here; arbitrary grouped signals are not silently
treated as one physical transition. -/
theorem decoderRun_eventTrace {C : Type} (M : WordEventSystem C Bool)
    (hphysical : M.PhysicalBits) (t : Nat) :
    decoderRun (eventTrace M) t = feedBits {} (M.prefixWord t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change feedEvent (decoderRun (eventTrace M) t) (eventTrace M t) = _
    rw [ih, WordEventSystem.prefix_succ, feedBits_append, word_eq_eventTrace M hphysical t,
      feedEvent_eq_feedBits]

/-- Cumulative prefix receipt membership and the actual online completion
events have precisely the same emitted records and fatal-error witnesses. -/
theorem online_sameReceipts_word {C : Type} (M : WordEventSystem C Bool)
    (hphysical : M.PhysicalBits) :
    SameReceipts (decodedEvents (eventTrace M)) (wordDecodedEvents M) where
  profile := rfl
  errors := by
    apply exists_congr
    intro t
    change (decoderRun (eventTrace M) t).numbers.failed = true ↔ _
    rw [decoderRun_eventTrace M hphysical t]
    rfl
  emitted := by
    intro b a
    rw [decodedEvents_emitted_iff_record]
    apply exists_congr
    intro t
    rw [decoderRun_eventTrace M hphysical t]
    rfl

theorem physical_observer_preserved {S T : Type} {source : WordEventSystem S Bool}
    {target : WordEventSystem T Bool} (r : SegmentSimulation source target)
    (htarget : target.PhysicalBits) (view : ZeroView) :
    SoundnessAcceptance view (wordDecodedEvents source) ↔
      SoundnessAcceptance view (decodedEvents (eventTrace target)) :=
  (sameOutput_observer_preserved r.sameOutput view).trans
    (acceptance_preserved view (online_sameReceipts_word target htarget)).symm

/-- The ordinary-machine interface theorem. Its only implementation premise is
the explicit local simulation certificate. No PA soundness premise or entire
decoded-correspondence hypothesis is hidden in the statement. -/
theorem implementation_observer_preserved {S : Type} {source : WordEventSystem S Bool}
    {n : Nat} {M : Machine n} (cert : ImplementationCertificate source M) (view : ZeroView) :
    SoundnessAcceptance view (wordDecodedEvents source) ↔
      SoundnessAcceptance view
        (decodedEvents (eventTrace (machineWordSystem M cert.labels))) :=
  physical_observer_preserved cert.simulation cert.physicalBits view

theorem implementation_complete_preserved {S : Type} {source : WordEventSystem S Bool}
    {n : Nat} {M : Machine n} (cert : ImplementationCertificate source M) :
    Complete (wordDecodedEvents source) ↔
      Complete (decodedEvents (eventTrace (machineWordSystem M cert.labels))) :=
  (complete_preserved (sameOutput_sameReceipts cert.sameOutput)).trans
    (complete_preserved
      (online_sameReceipts_word (machineWordSystem M cert.labels) cert.physicalBits)).symm

end PASoundness.UnaryCodec
