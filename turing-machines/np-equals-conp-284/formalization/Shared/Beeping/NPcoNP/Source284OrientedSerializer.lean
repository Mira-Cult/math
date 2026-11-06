import Shared.Beeping.NPcoNP.Source284OrientedExit

/-! Connect the marked serializer trace to the orientation-preserving paid
exit. The initial tagged buffer remains an explicit hypothesis. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284OrientedSerializer

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (allocated lifted)
open Shared.Beeping.NPcoNP.Source284DetectorExit (stopping stopConfig)
open Shared.Beeping.NPcoNP.Source284OrientedExit (side entry table)
open Shared.Beeping.NPcoNP.Source284JoinedEndDetectorTable (index)

/-- Detector run to the first marked visit after a complete body, retaining
its source-state parity for the continuation. -/
theorem run_body_exit (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (hc : Valid states c) (ho : Closed states original)
    (x w : List Bool) (n fuel q : Nat)
    (hprefix : ∀ i < n,
      (∃ q, (run original c i).state = some q ∧ (marks[q]?).getD false = true) →
      ∃ j, j < (Source284JoinedPrefixScan.joinedBody x w).length ∧
        Source284DetectorProduct.observed marks original c i =
          (Source284JoinedPrefixScan.joinedBody x w).reverse.take j)
    (hfull : Source284DetectorProduct.observed marks original c n =
      (Source284JoinedPrefixScan.joinedBody x w).reverse)
    (hq : (run original c n).state = some q) (hmarked : (marks[q]?).getD false = true) :
    run (table states marks original continuation) (lifted .lead c) (n+2+fuel) =
      shiftConfig (entry states)
        (run continuation ⟨(run original c n).left,(run original c n).right,some (q%2)⟩ fuel) := by
  have hbefore : ∀ i < n, ¬ stopConfig marks
      (run (Source284DetectorProduct.table states marks original) (lifted .lead c) i) := by
    intro i hi hs
    rw [Source284DetectorProduct.run_lifted states marks original .lead c hc ho] at hs
    obtain ⟨hd,hm⟩ := (Source284DetectorExit.stop_lifted_iff marks _ _).1 hs
    obtain ⟨j,hj,htrace⟩ := hprefix i hi hm
    exact (Source284DetectorProduct.monitor_no_early marks original c i x w j hj htrace) hd
  have hdone := Source284DetectorProduct.monitor_done_of_body marks original c n x w hfull
  have hq' : (run (Source284DetectorProduct.table states marks original) (lifted .lead c) n).state =
      some (Nat.pair (index .done) q) := by
    rw [Source284DetectorProduct.run_lifted states marks original .lead c hc ho,hdone]
    simp [lifted,hq]
  have hs : stopping marks (Nat.pair (index .done) q) = true := by
    simp [Source284DetectorExit.stop_lifted,hmarked]
  have h := Source284OrientedExit.run_first_stop states marks original continuation
    (lifted .lead c) (Source284DetectorProduct.lifted_valid states .lead c hc) ho
    n fuel hbefore _ hq' hs
  rw [Source284DetectorProduct.run_lifted states marks original .lead c hc ho] at h
  simpa [lifted] using h

/-- Source-record version; the caller supplies a closed continuation with two
orientation entries. Both exit transitions are included in the runtime. -/
theorem source_body_exit (states continuationStates : Nat) (marks : List Bool)
    (original continuation : Nat → Bool → Row) (hn : 2 ≤ continuationStates)
    (ho : Closed states original) (hcont : Closed continuationStates continuation)
    (c : Config) (hc : Valid states c) (x w : List Bool) (n fuel q : Nat)
    (hprefix : ∀ i < n,
      (∃ q, (run original c i).state = some q ∧ (marks[q]?).getD false = true) →
      ∃ j, j < (Source284JoinedPrefixScan.joinedBody x w).length ∧
        Source284DetectorProduct.observed marks original c i =
          (Source284JoinedPrefixScan.joinedBody x w).reverse.take j)
    (hfull : Source284DetectorProduct.observed marks original c n =
      (Source284JoinedPrefixScan.joinedBody x w).reverse)
    (hq : (run original c n).state = some q) (hmarked : (marks[q]?).getD false = true) :
    let last := run original c n
    Source284Relative.run (encode (entry states+continuationStates)
      (table states marks original continuation) 1) (toSource (lifted .lead c)) (n+2+fuel) =
    Source284SourceRelocation.lift (entry states)
      (Source284Relative.run (encode continuationStates continuation 1)
        ⟨last.left,last.right,active (q%2)⟩ fuel) := by
  dsimp only
  have hsmall := Source284DetectorProduct.lifted_valid states .lead c hc
  have hstart : Valid (entry states+continuationStates) (lifted .lead c) := by
    intro r hr
    have h := hsmall r hr
    dsimp [entry,Source284OrientedExit.entry]
    omega
  have hr := run_toSource (entry states+continuationStates)
    (table states marks original continuation) 1 (lifted .lead c)
      (Source284OrientedExit.closed states continuationStates marks original continuation hn ho hcont)
      hstart (n+2+fuel)
  have he := run_body_exit states marks original continuation c hc ho x w n fuel q
    hprefix hfull hq hmarked
  rw [he] at hr
  let last := run original c n
  let target : Config := ⟨last.left,last.right,some (q%2)⟩
  have htarget : Valid continuationStates target := by
    intro r hr; simp [target] at hr; subst r
    have hh := Nat.mod_lt q (by decide : 0 < 2)
    omega
  have ht := run_toSource continuationStates continuation 1 target hcont htarget fuel
  rw [← Source284SourceRelocation.lift_toSource,← ht] at hr
  exact hr

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284FiniteRelativeRows (rows)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)

/-- For a prepared tagged serializer tape, the detector exits at the end
of the complete body and hands the exact final tape and its actual orientation
to the continuation. The construction of that initial tape is not assumed to
be free and remains a separate obligation. -/
theorem serializer_exit_prepared (zero one : List Bool) (continuationStates : Nat)
    (continuation : Nat → Bool → Source284TableEncode.Row) (hn : 2 ≤ continuationStates)
    (hcont : Closed continuationStates continuation)
    (x w rest : List Bool) (dummy : Bool) (xs L : List Bool)
    (c : Shared.Codes.FinitePrograms.Config) (rev : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical ((rest++[dummy])++L) false xs).2)
    (fuel : Nat) :
    let remaining := rest++[dummy]
    let N := totalCost zero one remaining false xs
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let csrc := logical c.2 rev 0
    ∃ rev', Source284Relative.run (encode (entry states+continuationStates)
      (table states marks original continuation) 1) (toSource (lifted .lead csrc)) (N+2+fuel) =
      Source284SourceRelocation.lift (entry states)
        (Source284Relative.run (encode continuationStates continuation 1)
          (represented (canonical L (result zero one remaining false xs).1
            (result zero one remaining false xs).2).2 rev' (codeState 0 rev')) fuel) := by
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
      (∃ q, (run original csrc i).state = some q ∧ (marks[q]?).getD false = true) →
      ∃ j, j < (Source284JoinedPrefixScan.joinedBody x w).length ∧
        Source284DetectorProduct.observed marks original csrc i =
          (Source284JoinedPrefixScan.joinedBody x w).reverse.take j := by
    intro i hi hm
    obtain ⟨j,hj,he⟩ := Source284SerializerTrace.marked_proper_prefix marks original csrc i N hi
      (Source284JoinedPrefixScan.joinedBody x w).reverse hfull hm
    exact ⟨j,by simpa using hj,he⟩
  obtain ⟨rev',hfinal⟩ := Source284SerializerTrace.source_cycles_final zero one remaining false xs L c rev hq ht
  change run original csrc N = logical (canonical L (result zero one remaining false xs).1
      (result zero one remaining false xs).2).2 rev' 0 at hfinal
  let t := (canonical L (result zero one remaining false xs).1 (result zero one remaining false xs).2).2
  let q := Source284FiniteRelativeRows.index 0 rev'
  have hlast : (run original csrc N).state = some q := by rw [hfinal]; rfl
  have hpos : 0 < (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  have hmark : (marks[q]?).getD false = true := by
    have hm := Source284SerializerTrace.logical_mark zero one t rev' 0 hpos
    simpa [marks,q] using hm
  have hvalid : Valid states csrc := Source284SerializerTrace.logical_valid _ _ _ _ hpos
  have ho : Closed states original := Source284FiniteRelativeRows.closed _
    (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  have h := source_body_exit states continuationStates marks original continuation hn ho hcont
    csrc hvalid x w N fuel q hprefix hfull hlast hmark
  rw [hfinal] at h
  have hidx : q % 2 = q := by
    cases rev' <;> simp [q,Source284FiniteRelativeRows.index,Source284CompileRecords.bit]
  rw [hidx] at h
  refine ⟨rev',?_⟩
  have hsrc := Source284SerializerTrace.logical_toSource t rev' 0
  change toSource (logical t rev' 0) = represented t rev' (codeState 0 rev') at hsrc
  rw [← hsrc]
  simpa [Source284SerializerTrace.logical,toSource,nextState,q,csrc,N,states,marks,original,remaining,t] using h

end Shared.Beeping.NPcoNP.Source284OrientedSerializer
