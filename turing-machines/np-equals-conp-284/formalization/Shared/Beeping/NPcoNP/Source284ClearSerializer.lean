import Shared.Beeping.NPcoNP.Source284ClearedUntagSource
import Shared.Beeping.NPcoNP.Source284OrientedSerializer

/-! Connect the exact marked serializer trace to the two-step boundary
clearing exit. The initialized tagged tape remains an explicit hypothesis. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ClearSerializer

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun (Valid Closed toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (allocated lifted)
open Shared.Beeping.NPcoNP.Source284DetectorExit (stopping stopConfig entry)
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284JoinedEndDetectorTable (index)

/-- First complete-body detection followed by two boundary-clearing steps. -/
theorem run_body_exit (states : Nat) (marks : List Bool)
    (original continuation : Nat → Bool → Source284TableEncode.Row)
    (c : Source284TableRun.Config) (hc : Valid states c) (ho : Closed states original)
    (x w : List Bool) (n fuel q : Nat)
    (hprefix : ∀ i < n,
      (∃ q, (Source284TableRun.run original c i).state = some q ∧ (marks[q]?).getD false = true) →
      ∃ j, j < (Source284JoinedPrefixScan.joinedBody x w).length ∧
        Source284DetectorProduct.observed marks original c i =
          (Source284JoinedPrefixScan.joinedBody x w).reverse.take j)
    (hfull : Source284DetectorProduct.observed marks original c n =
      (Source284JoinedPrefixScan.joinedBody x w).reverse)
    (hq : (Source284TableRun.run original c n).state = some q)
    (hmarked : (marks[q]?).getD false = true) :
    Source284TableRun.run (Source284ClearExit.table states marks original continuation)
      (lifted .lead c) (n+2+fuel) =
      shiftConfig (entry states) (Source284TableRun.run continuation
        (Source284ClearExit.cleared (Nat.pair (index .done) q)
          (lifted .done (Source284TableRun.run original c n))) fuel) := by
  have hbefore : ∀ i < n, ¬ stopConfig marks
      (Source284TableRun.run (Source284DetectorProduct.table states marks original) (lifted .lead c) i) := by
    intro i hi hs
    rw [Source284DetectorProduct.run_lifted states marks original .lead c hc ho] at hs
    obtain ⟨hd,hm⟩ := (Source284DetectorExit.stop_lifted_iff marks _ _).1 hs
    obtain ⟨j,hj,htrace⟩ := hprefix i hi hm
    exact (Source284DetectorProduct.monitor_no_early marks original c i x w j hj htrace) hd
  have hdone := Source284DetectorProduct.monitor_done_of_body marks original c n x w hfull
  have hq' : (Source284TableRun.run (Source284DetectorProduct.table states marks original) (lifted .lead c) n).state =
      some (Nat.pair (index .done) q) := by
    rw [Source284DetectorProduct.run_lifted states marks original .lead c hc ho,hdone]
    simp [lifted,hq]
  have hs : stopping marks (Nat.pair (index .done) q) = true := by
    simp [Source284DetectorExit.stop_lifted,hmarked]
  have h := Source284ClearExit.run_first_stop states marks original continuation
    (lifted .lead c) (Source284DetectorProduct.lifted_valid states .lead c hc) ho
    n fuel _ hbefore hq' hs
  rw [Source284DetectorProduct.run_lifted states marks original .lead c hc ho,hdone] at h
  exact h

/-- On a prepared tagged tape the marked-body detector reaches the clearing
exit, clears the boundary in two steps, and follows all continuation steps
from the normalized orientation. -/
theorem prepared_exit (zero one : List Bool) (continuation : Nat → Bool → Source284TableEncode.Row)
    (x w rest : List Bool) (dummy : Bool) (xs L : List Bool) (c : Config) (rev : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical ((rest++[dummy])++L) false xs).2)
    (fuel : Nat) :
    let remaining := rest++[dummy]
    let N := totalCost zero one remaining false xs
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let csrc := logical c.2 rev 0
    Source284TableRun.run (Source284ClearExit.table states marks original continuation)
      (lifted .lead csrc) (N+2+fuel) =
      shiftConfig (entry states) (Source284TableRun.run continuation
        (logical (Source284ClearTape.clearBoundary
          (canonical L (result zero one remaining false xs).1
            (result zero one remaining false xs).2).2) false 0) fuel) := by
  dsimp only
  let remaining := rest++[dummy]
  let N := totalCost zero one remaining false xs
  let states := (Source284DetectorProduct.serializerRows zero one).length
  let marks := Source284DetectorProduct.serializerMarks zero one
  let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
  let csrc := logical c.2 rev 0
  have hfull : Source284DetectorProduct.observed marks original csrc N =
      (Source284JoinedPrefixScan.joinedBody x w).reverse := by
    have h := Source284SerializerTrace.source_cycles_observed zero one remaining false xs L c rev hq ht
    change Source284DetectorProduct.observed marks original csrc N = processed remaining false at h
    rw [h,Source284SerializerTrace.processed_append,hbody]
  have hprefix : ∀ i < N,
      (∃ q, (Source284TableRun.run original csrc i).state = some q ∧ (marks[q]?).getD false = true) →
      ∃ j, j < (Source284JoinedPrefixScan.joinedBody x w).length ∧
        Source284DetectorProduct.observed marks original csrc i =
          (Source284JoinedPrefixScan.joinedBody x w).reverse.take j := by
    intro i hi hm
    obtain ⟨j,hj,he⟩ := Source284SerializerTrace.marked_proper_prefix marks original csrc i N hi
      (Source284JoinedPrefixScan.joinedBody x w).reverse hfull hm
    exact ⟨j,by simpa using hj,he⟩
  obtain ⟨rev',hfinal⟩ := Source284SerializerTrace.source_cycles_final zero one remaining false xs L c rev hq ht
  change Source284TableRun.run original csrc N = logical (canonical L (result zero one remaining false xs).1
      (result zero one remaining false xs).2).2 rev' 0 at hfinal
  let t := (canonical L (result zero one remaining false xs).1 (result zero one remaining false xs).2).2
  let q := Source284FiniteRelativeRows.index 0 rev'
  have hlast : (Source284TableRun.run original csrc N).state = some q := by rw [hfinal]; rfl
  have hpos : 0 < (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  have hmark : (marks[q]?).getD false = true := by
    have hm := Source284SerializerTrace.logical_mark zero one t rev' 0 hpos
    simpa [marks,q] using hm
  have hvalid : Valid states csrc := Source284SerializerTrace.logical_valid _ _ _ _ hpos
  have ho : Closed states original := Source284FiniteRelativeRows.closed _
    (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  have h := run_body_exit states marks original continuation csrc hvalid ho x w N fuel q
    hprefix hfull hlast hmark
  rw [hfinal,Source284ClearTape.cleared_logical] at h
  exact h

/-- Numeric source version of the complete prepared serializer and clearing
handoff. The continuation can be the frame-removal table; both boundary
clearing transitions and all later continuation steps are charged. -/
theorem source_prepared_exit (zero one : List Bool) (continuationStates : Nat)
    (continuation : Nat → Bool → Source284TableEncode.Row) (hn : 0 < continuationStates)
    (hcont : Closed continuationStates continuation)
    (x w rest : List Bool) (dummy : Bool) (xs L : List Bool) (c : Config) (rev : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical ((rest++[dummy])++L) false xs).2)
    (fuel : Nat) :
    let remaining := rest++[dummy]
    let N := totalCost zero one remaining false xs
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let csrc := logical c.2 rev 0
    let target := Source284ClearTape.clearBoundary
      (canonical L (result zero one remaining false xs).1 (result zero one remaining false xs).2).2
    Source284Relative.run (encode (entry states+continuationStates)
      (Source284ClearExit.table states marks original continuation) 1)
      (toSource (lifted .lead csrc)) (N+2+fuel) =
    Source284SourceRelocation.lift (entry states)
      (Source284Relative.run (encode continuationStates continuation 1)
        (Source284FiniteTapeStep.represented target false (Source284CompileRecords.codeState 0 false)) fuel) := by
  dsimp only
  let remaining := rest++[dummy]
  let N := totalCost zero one remaining false xs
  let states := (Source284DetectorProduct.serializerRows zero one).length
  let marks := Source284DetectorProduct.serializerMarks zero one
  let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
  let csrc := logical c.2 rev 0
  let target := Source284ClearTape.clearBoundary
    (canonical L (result zero one remaining false xs).1 (result zero one remaining false xs).2).2
  have hpos : 0 < (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  have hc : Valid states csrc := Source284SerializerTrace.logical_valid _ _ _ _ hpos
  have ho : Closed states original := Source284FiniteRelativeRows.closed _
    (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  have hsmall := Source284DetectorProduct.lifted_valid states .lead csrc hc
  have hstart : Valid (entry states+continuationStates) (lifted .lead csrc) := by
    intro q hq'
    have h := hsmall q hq'
    dsimp [entry]
    omega
  have hr := Source284TableRun.run_toSource (entry states+continuationStates)
    (Source284ClearExit.table states marks original continuation) 1 (lifted .lead csrc)
    (Source284ClearExit.closed states continuationStates marks original continuation hn ho hcont)
    hstart (N+2+fuel)
  have he := prepared_exit zero one continuation x w rest dummy xs L c rev hbody hq ht fuel
  change Source284TableRun.run (Source284ClearExit.table states marks original continuation)
    (lifted .lead csrc) (N+2+fuel) = _ at he
  rw [he,← Source284SourceRelocation.lift_toSource] at hr
  have htarget : Valid continuationStates (logical target false 0) := by
    intro q hq'
    simp [logical,Source284FiniteRelativeRows.index,Source284CompileRecords.bit] at hq'
    subst q
    exact hn
  have hf := Source284TableRun.run_toSource continuationStates continuation 1
    (logical target false 0) hcont htarget fuel
  rw [Source284SerializerTrace.logical_toSource] at hf
  rw [← hf] at hr
  exact hr

end Shared.Beeping.NPcoNP.Source284ClearSerializer
