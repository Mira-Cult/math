import Shared.Beeping.NPcoNP.Source284CheckpointMarkedGuard

/-! Run the existing tagged witness comparator with the paid marked
workspace initializer. The independently generated counter remains in the
retained input stream; moving it across the input is a later operation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointMarkedVerifier

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedGuard (otherHalf)

def description (k r n : Nat) (verifier : Nat → Bool → Row) : Nat :=
  Source284CheckpointMarkedGuard.description k r (Source284DynamicGuardSource.states n)
    (Source284OffsetTagged.table n verifier)

/-- The exact existing comparator is reached with the same guard cutoff,
original certificate, and marked workspace behind the input stream. -/
theorem source_after (k r n : Nat) (verifier : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < n) (hv : Closed n verifier) :
    Source284Relative.run (description k r n verifier)
      (Source284Relative.initial (encodeFrame w suffix) certificate)
      (Source284CheckpointMarkedGuard.totalCost k r w+fuel) =
    lift (1371+317*k+317*r) (Source284Relative.run (Source284OffsetTagged.description n verifier)
      (Source284Relative.initial certificate
        (pairTape (List.replicate (Source284DynamicGuardSource.bound k w.length) false)
          (otherHalf k r w suffix))) fuel) := by
  have hc : Closed (Source284DynamicGuardSource.states n) (Source284OffsetTagged.table n verifier) :=
    Source284OffsetTagged.table_closed n verifier hn hv
  let c : Config := ⟨pairTape (List.replicate (Source284DynamicGuardSource.bound k w.length) false)
    (otherHalf k r w suffix),certificate,some 0⟩
  have hvalid : Valid (Source284DynamicGuardSource.states n) c := by
    intro q hq
    simp [c] at hq
    subst q
    simp [Source284DynamicGuardSource.states,Source284OffsetTagged.goodStates,
      Source284OffsetTagged.rawStates,Source284PositiveTaggedCutoff.rawStates]
  have hr := run_toSource (Source284DynamicGuardSource.states n) (Source284OffsetTagged.table n verifier)
    1 c hc hvalid fuel
  change Source284Relative.run (Source284OffsetTagged.description n verifier)
    (Source284Relative.initial certificate
      (pairTape (List.replicate (Source284DynamicGuardSource.bound k w.length) false)
        (otherHalf k r w suffix))) fuel = _ at hr
  calc
    _ = toSource (shiftConfig (1371+317*k+317*r) (run (Source284OffsetTagged.table n verifier) c fuel)) := by
      simpa [description,c] using Source284CheckpointMarkedGuard.source_then k r
        (Source284DynamicGuardSource.states n) (Source284OffsetTagged.table n verifier)
        w certificate suffix fuel (by simp [Source284DynamicGuardSource.states]) hc
    _ = lift (1371+317*k+317*r) (toSource (run (Source284OffsetTagged.table n verifier) c fuel)) :=
      (lift_toSource _ _).symm
    _ = _ := by rw [hr]

theorem rejected_certificate_never_accepts (k r n : Nat) (verifier : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < n) (hv : Closed n verifier)
    (hbad : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k w.length) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k r n verifier)
      (encodeFrame w suffix) certificate clock = false := by
  apply Source284PositiveTaggedCutoff.never_of_after _ _ _ (Source284CheckpointMarkedGuard.totalCost k r w)
  intro extra
  have h := Source284OffsetTagged.decoded_none_never_accepts n verifier
    (Source284DynamicGuardSource.bound k w.length) certificate (otherHalf k r w suffix) hn hv hbad extra
  unfold Source284Relative.accepts at h ⊢
  rw [source_after k r n verifier w certificate suffix extra hn hv]
  simp only [beq_eq_false_iff_ne] at h ⊢
  simp [Source284SourceRelocation.lift,h]

theorem rejected_raw_certificate_never_accepts (k r n : Nat) (verifier : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < n) (hv : Closed n verifier)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k r n verifier) input certificate clock = false := by
  obtain ⟨w,suffix,hframe⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hframe]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  have hbad' : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k w.length)
      certificate = none := by simpa [hlen] using hbad
  have h := rejected_certificate_never_accepts k r n verifier w certificate suffix hn hv hbad'
  simpa [hframe] using h

/-- Successful certificates reach the existing verifier continuation without
losing the separated workspace counter in the retained input data. -/
theorem decoded_verifier_exact (k r n : Nat) (verifier : Nat → Bool → Row)
    (input witness : List Bool) (certificate suffix : Nat) (hn : 0 < n) (hv : Closed n verifier)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate = 4*encodeFrame witness witnessSuffix ∧
      ∀ fuel, Source284Relative.run (description k r n verifier)
        (Source284Relative.initial (encodeFrame input suffix) certificate)
        (Source284CheckpointMarkedGuard.totalCost k r input+
          (4+(Source284PayloadSentinelPipeline.totalCost witness.length+
            (Source284OffsetMatch.compareCost witness.length+(1+fuel))))) =
      lift (1371+317*k+317*r+212) (Source284Relative.run (encode n verifier 1)
        ⟨2*Source284PayloadMarkOne.zeros witness
            (Source284ScratchFlip.flipped [false] ((witnessSuffix/4)/4)),
          pairTape (Source284OffsetExactHandoff.boundTokens (Source284DynamicGuardSource.bound k input.length) witness)
            (otherHalf k r input suffix),active 0⟩ fuel) := by
  obtain ⟨witnessSuffix,hcert,hafter⟩ := Source284OffsetDecodedHandoff.decoded_verifier_exact
    n verifier (Source284DynamicGuardSource.bound k input.length) certificate (otherHalf k r input suffix)
    witness hn hv hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  rw [source_after k r n verifier input certificate suffix _ hn hv,hafter fuel,
    Source284SourceRelocation.lift_add]

/-- Both stage counts are fixed before execution: the guard covers the
original witness demand and the separate on-tape counter covers any chosen
polynomial demand in that generated guard. -/
theorem uniform_bound_and_counter (witnessDemand workspaceDemand : Polynomial Nat) :
    ∃ k r : Nat, ∀ n suffix : Nat,
      witnessDemand.eval n ≤ Source284DynamicGuardSource.bound k n ∧
      workspaceDemand.eval (Source284DynamicGuardSource.bound k n) ≤
        Source284CheckpointMarkedWorkspace.markCount k r n-1 ∧
      Source284CheckpointMarkedWorkspace.higher k r n suffix =
        Source284CountedShift.counter (Source284CheckpointMarkedWorkspace.markCount k r n-1)
          (Source284CheckpointMarkedWorkspace.blankTail k r n suffix/2) := by
  obtain ⟨k,hk⟩ := Source284DynamicGuardSource.bound_dominates witnessDemand
  obtain ⟨r,hr⟩ := Source284CheckpointMarkedGuard.counter_uniform k workspaceDemand
  exact ⟨k,r,fun n suffix => ⟨hk n,(hr n suffix).1,(hr n suffix).2⟩⟩

end Shared.Beeping.NPcoNP.Source284CheckpointMarkedVerifier
