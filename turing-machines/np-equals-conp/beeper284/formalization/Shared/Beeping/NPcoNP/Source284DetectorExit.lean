import Shared.Beeping.NPcoNP.Source284DetectorProduct

/-! A paid finite-table exit for the monitored product. At a marked row with
monitor state `done`, two turns restore both tape halves and enter a supplied
continuation. Before that first condition, all product steps agree exactly.
A serializer-specific theorem identifying the marked trace is still needed. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284DetectorExit

open Shared.Beeping.NPcoNP.Source284JoinedEndDetector (State)
open Shared.Beeping.NPcoNP.Source284JoinedEndDetectorTable (index)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (allocated lifted)

def stopping (marks : List Bool) (s : Nat) : Bool :=
  ((Nat.unpair s).1 == index .done) && (marks[(Nat.unpair s).2]?).getD false

def stopConfig (marks : List Bool) (c : Config) : Prop :=
  ∃ q, c.state = some q ∧ stopping marks q = true

def entry (states : Nat) : Nat := allocated states + 1

/-- Product states are followed by one turning bridge and a relocated
continuation. Both exit transitions are explicitly charged. -/
def table (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (q : Nat) (b : Bool) : Row :=
  if q < allocated states then
    if stopping marks q then ⟨b,true,some (allocated states)⟩
    else Source284DetectorProduct.table states marks original q b
  else if q = allocated states then ⟨b,true,some (entry states)⟩
  else shiftRow (entry states) (continuation (q-entry states) b)

theorem stop_lifted (marks : List Bool) (phase : State) (q : Nat) :
    stopping marks (Nat.pair (index phase) q) =
      (decide (phase = .done) && (marks[q]?).getD false) := by
  cases phase <;> simp [stopping,index,Nat.unpair_pair]

theorem closed (states continuationStates : Nat) (marks : List Bool)
    (original continuation : Nat → Bool → Row) (hn : 0 < continuationStates)
    (ho : Closed states original) (hc : Closed continuationStates continuation) :
    Closed (entry states+continuationStates) (table states marks original continuation) := by
  intro q hq b q' hnext
  by_cases hq0 : q < allocated states
  · by_cases hs : stopping marks q = true
    · simp [table,hq0,hs] at hnext
      subst q'; simp [entry]; omega
    · have hb : stopping marks q = false := Bool.eq_false_iff.mpr hs
      have ht : (Source284DetectorProduct.table states marks original q b).next = some q' := by
        simpa [table,hq0,hb] using hnext
      have hv := Source284DetectorProduct.closed states marks original ho q hq0 b q' ht
      simp [entry] at *; omega
  · by_cases he : q = allocated states
    · subst q; simp [table,entry] at hnext
      subst q'; simp [entry]; omega
    · have hge : entry states ≤ q := by simp [entry]; omega
      have ht : (shiftRow (entry states) (continuation (q-entry states) b)).next = some q' := by
        simpa [table,hq0,he] using hnext
      cases hh : (continuation (q-entry states) b).next with
      | none => simp [shiftRow,hh] at ht
      | some r =>
        have hv := hc (q-entry states) (by omega) b r hh
        simp [shiftRow,hh] at ht
        subst q'; omega

/-- On a non-stopping allocated configuration the extended table takes
exactly the original product step. -/
theorem step_before (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (hc : Valid (allocated states) c) (hs : ¬ stopConfig marks c) :
    step (table states marks original continuation) c =
      step (Source284DetectorProduct.table states marks original) c := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq := hc q rfl
      have hfalse : stopping marks q = false := by
        cases he : stopping marks q with
        | false => rfl
        | true => exact False.elim (hs ⟨q,rfl,he⟩)
      simp [step,table,hq,hfalse]

/-- A first stop takes two real turns, restoring the original tape exactly. -/
theorem exit_two (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (left right q : Nat) (hq : q < allocated states) (hs : stopping marks q = true) :
    run (table states marks original continuation) ⟨left,right,some q⟩ 2 =
      ⟨left,right,some (entry states)⟩ := by
  simp [run,step,table,hq,hs,entry,Source284HardwireTable.bit_decide_mod] <;> omega

theorem relocated_row (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (q : Nat) (b : Bool) :
    table states marks original continuation (entry states+q) b =
      shiftRow (entry states) (continuation q b) := by
  have h0 : ¬ entry states+q < allocated states := by simp [entry]; omega
  have h1 : entry states+q ≠ allocated states := by simp [entry]; omega
  simp [table,h0,h1]

theorem relocated_step (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) :
    step (table states marks original continuation) (shiftConfig (entry states) c) =
      shiftConfig (entry states) (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (fuel : Nat) :
    run (table states marks original continuation) (shiftConfig (entry states) c) fuel =
      shiftConfig (entry states) (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- If no stop is reached in the first `n` product steps, the extended
machine follows those steps exactly. -/
theorem run_before (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (hc : Valid (allocated states) c) (ho : Closed states original) (n : Nat)
    (hs : ∀ i < n, ¬ stopConfig marks (run (Source284DetectorProduct.table states marks original) c i)) :
    run (table states marks original continuation) c n =
      run (Source284DetectorProduct.table states marks original) c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [ih (by intro i hi; exact hs i (by omega))]
    apply step_before states marks original continuation
    · exact valid_run _ _ c (Source284DetectorProduct.closed states marks original ho) hc n
    · exact hs n (by omega)

/-- At the first marked `done` configuration, the table pays two turns and
then follows every step of the supplied finite continuation. -/
theorem run_first_stop (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (hc : Valid (allocated states) c) (ho : Closed states original) (n fuel : Nat)
    (hbefore : ∀ i < n, ¬ stopConfig marks (run (Source284DetectorProduct.table states marks original) c i))
    (hstop : stopConfig marks (run (Source284DetectorProduct.table states marks original) c n)) :
    let last := run (Source284DetectorProduct.table states marks original) c n
    run (table states marks original continuation) c (n+2+fuel) =
      shiftConfig (entry states) (run continuation ⟨last.left,last.right,some 0⟩ fuel) := by
  dsimp only
  obtain ⟨q,hq,hs⟩ := hstop
  have hvalid := valid_run _ _ c (Source284DetectorProduct.closed states marks original ho) hc n
  have hq' := hvalid q hq
  have he := exit_two states marks original continuation
    (run (Source284DetectorProduct.table states marks original) c n).left
    (run (Source284DetectorProduct.table states marks original) c n).right q hq' hs
  have hconfig : (run (Source284DetectorProduct.table states marks original) c n) =
      ⟨(run (Source284DetectorProduct.table states marks original) c n).left,
        (run (Source284DetectorProduct.table states marks original) c n).right,some q⟩ := by
    cases h : run (Source284DetectorProduct.table states marks original) c n with
    | mk left right state => simp_all
  rw [← hconfig] at he
  rw [Source284HardwireCorrect.run_add,Source284HardwireCorrect.run_add,
    run_before states marks original continuation c hc ho n hbefore,he]
  change run (table states marks original continuation) (shiftConfig (entry states)
    ⟨(run (Source284DetectorProduct.table states marks original) c n).left,
      (run (Source284DetectorProduct.table states marks original) c n).right,some 0⟩) fuel = _
  rw [relocated_run]

/-- A lifted live state stops exactly when the monitor is done and the
original row is marked. -/
theorem stop_lifted_iff (marks : List Bool) (phase : State) (c : Config) :
    stopConfig marks (lifted phase c) ↔
      phase = .done ∧ ∃ q, c.state = some q ∧ (marks[q]?).getD false = true := by
  cases c with
  | mk left right state =>
    cases state with
    | none => simp [stopConfig,lifted]
    | some q =>
      cases phase <;> simp [stopConfig,lifted,stop_lifted]

/-- If marked visits before `n` have only proper-body-prefix traces, and the
marked visit at `n` follows the whole body, the product takes its first exit
at exactly `n`. These trace hypotheses must be proved for the chosen
serializer; they do not assert termination or a complexity equality. -/
theorem run_body_exit (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (hc : Valid states c) (ho : Closed states original)
    (x w : List Bool) (n fuel : Nat)
    (hprefix : ∀ i < n,
      (∃ q, (run original c i).state = some q ∧ (marks[q]?).getD false = true) →
      ∃ j, j < (Source284JoinedPrefixScan.joinedBody x w).length ∧
        Source284DetectorProduct.observed marks original c i =
          (Source284JoinedPrefixScan.joinedBody x w).reverse.take j)
    (hfull : Source284DetectorProduct.observed marks original c n =
      (Source284JoinedPrefixScan.joinedBody x w).reverse)
    (hmarked : ∃ q, (run original c n).state = some q ∧ (marks[q]?).getD false = true) :
    run (table states marks original continuation) (lifted .lead c) (n+2+fuel) =
      shiftConfig (entry states)
        (run continuation ⟨(run original c n).left,(run original c n).right,some 0⟩ fuel) := by
  have hbefore : ∀ i < n, ¬ stopConfig marks
      (run (Source284DetectorProduct.table states marks original) (lifted .lead c) i) := by
    intro i hi hs
    rw [Source284DetectorProduct.run_lifted states marks original .lead c hc ho] at hs
    obtain ⟨hd,hm⟩ := (stop_lifted_iff marks _ _).1 hs
    obtain ⟨j,hj,htrace⟩ := hprefix i hi hm
    exact (Source284DetectorProduct.monitor_no_early marks original c i x w j hj htrace) hd
  have hdone := Source284DetectorProduct.monitor_done_of_body marks original c n x w hfull
  have hstop : stopConfig marks
      (run (Source284DetectorProduct.table states marks original) (lifted .lead c) n) := by
    rw [Source284DetectorProduct.run_lifted states marks original .lead c hc ho]
    exact (stop_lifted_iff marks _ _).2 ⟨hdone,hmarked⟩
  have h := run_first_stop states marks original continuation (lifted .lead c)
    (Source284DetectorProduct.lifted_valid states .lead c hc) ho n fuel hbefore hstop
  rw [Source284DetectorProduct.run_lifted states marks original .lead c hc ho] at h
  simpa [lifted] using h

/-- Instantiation for the actual compiled tagged serializer, including the
unary-record source and every later continuation step. The marked-trace
hypotheses are the exact outstanding serializer-specific obligations. -/
theorem serializer_body_exit (zero one : List Bool) (continuationStates : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < continuationStates)
    (hcont : Closed continuationStates continuation) (c : Config)
    (hc : Valid (Source284DetectorProduct.serializerRows zero one).length c)
    (x w : List Bool) (n fuel : Nat)
    (hprefix : ∀ i < n,
      (∃ q, (run (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)) c i).state = some q ∧
        ((Source284DetectorProduct.serializerMarks zero one)[q]?).getD false = true) →
      ∃ j, j < (Source284JoinedPrefixScan.joinedBody x w).length ∧
        Source284DetectorProduct.observed (Source284DetectorProduct.serializerMarks zero one)
          (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)) c i =
          (Source284JoinedPrefixScan.joinedBody x w).reverse.take j)
    (hfull : Source284DetectorProduct.observed (Source284DetectorProduct.serializerMarks zero one)
      (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)) c n =
        (Source284JoinedPrefixScan.joinedBody x w).reverse)
    (hmarked : ∃ q,
      (run (Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)) c n).state = some q ∧
        ((Source284DetectorProduct.serializerMarks zero one)[q]?).getD false = true) :
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let last := run original c n
    Source284Relative.run (encode (entry states+continuationStates)
      (table states marks original continuation) 1) (toSource (lifted .lead c)) (n+2+fuel) =
    Source284SourceRelocation.lift (entry states)
      (Source284Relative.run (encode continuationStates continuation 1)
        ⟨last.left,last.right,active 0⟩ fuel) := by
  dsimp only
  let states := (Source284DetectorProduct.serializerRows zero one).length
  let marks := Source284DetectorProduct.serializerMarks zero one
  let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
  have ho : Closed states original := Source284FiniteRelativeRows.closed _
    (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  have hsmall := Source284DetectorProduct.lifted_valid states .lead c hc
  have hstart : Valid (entry states+continuationStates) (lifted .lead c) := by
    intro q hq
    have h := hsmall q hq
    dsimp [entry]
    omega
  have hr := run_toSource (entry states+continuationStates)
    (table states marks original continuation) 1 (lifted .lead c)
      (closed states continuationStates marks original continuation hn ho hcont) hstart (n+2+fuel)
  have he := run_body_exit states marks original continuation c hc ho x w n fuel hprefix hfull hmarked
  rw [he] at hr
  let last := run original c n
  let target : Config := ⟨last.left,last.right,some 0⟩
  have htarget : Valid continuationStates target := by
    intro q hq; simp [target] at hq; subst q; exact hn
  have ht := run_toSource continuationStates continuation 1 target hcont htarget fuel
  rw [← Source284SourceRelocation.lift_toSource,← ht] at hr
  exact hr

namespace Fixtures
example : stopping [true] (Nat.pair (index .done) 0) = true := by decide +kernel
example : stopping [false] (Nat.pair (index .done) 0) = false := by decide +kernel
example : stopping [true] (Nat.pair (index .lead) 0) = false := by decide +kernel

def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
/-- The empty joined body is detected in five steps and the continuation
is reached only after the two paid turns. -/
example : run (table 9 (List.replicate 9 true)
    (Source284JoinedEndDetectorTable.table loop) loop)
    (lifted .lead ⟨0,0,some 0⟩) 7 = ⟨0,0,some (entry 9)⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284DetectorExit
