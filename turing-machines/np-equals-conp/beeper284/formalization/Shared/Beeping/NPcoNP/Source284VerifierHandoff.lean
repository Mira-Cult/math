import Shared.Beeping.NPcoNP.Source284CertificateDispatch

/-! A paid verifier continuation for the finite certificate validator.
This proves the matching-certificate validator and verifier run in one table.
The invalid-certificate path, initial turn, finite serialization and
polynomial table construction remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.Source284VerifierHandoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284CertificateDispatch

/-- Reuse the validator's handoff row as the verifier's first paid step;
the rest of the verifier is relocated above all validator states. -/
def table (expected : List Bool) (clock : Nat) (verifier : Nat → Bool → Row)
    (q : Nat) (read : Bool) : Row :=
  if q = handoff expected clock then
    shiftRow (allocated expected clock) (verifier 0 read)
  else if allocated expected clock ≤ q then
    shiftRow (allocated expected clock) (verifier (q-allocated expected clock) read)
  else Source284CertificateDispatch.table expected clock q read

theorem validator_row (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (q : Nat) (read : Bool)
    (hbound : q < allocated expected clock) (hneq : q ≠ handoff expected clock) :
    table expected clock verifier q read =
      Source284CertificateDispatch.table expected clock q read := by
  simp [table,hneq, Nat.not_le_of_gt hbound]

theorem validator_step (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (c : Config)
    (hvalid : Valid (allocated expected clock) c)
    (hneq : c.state ≠ some (handoff expected clock)) :
    step (table expected clock verifier) c =
      step (Source284CertificateDispatch.table expected clock) c := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq : q < allocated expected clock := hvalid q rfl
      have hn : q ≠ handoff expected clock := by simpa using hneq
      simp only [step, validator_row expected clock verifier q _ hq hn]

/-- If the original validator does not reach the handoff before a given
time, the combined table follows exactly the same run through that time. -/
theorem run_before_handoff (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (c : Config) (fuel : Nat)
    (hvalid : Valid (allocated expected clock) c)
    (havoid : ∀ i < fuel,
      (run (Source284CertificateDispatch.table expected clock) c i).state ≠
        some (handoff expected clock)) :
    run (table expected clock verifier) c fuel =
      run (Source284CertificateDispatch.table expected clock) c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      have ha : ∀ i < fuel,
          (run (Source284CertificateDispatch.table expected clock) c i).state ≠
            some (handoff expected clock) := by
        intro i hi
        exact havoid i (by omega)
      have hs := validator_step expected clock verifier
        (run (Source284CertificateDispatch.table expected clock) c fuel)
        (valid_run _ _ _ (Source284CertificateDispatch.closed expected clock) hvalid fuel)
        (havoid fuel (by omega))
      simp only [run, ih ha, hs]

/-- In the unmodified validator, running beyond its handoff enters the
permanent reject sink. Thus a run ending at the handoff cannot have visited
it at an earlier time. -/
theorem validator_handoff_row (expected : List Bool) (clock : Nat) (b : Bool) :
    Source284CertificateDispatch.table expected clock (handoff expected clock) b =
      ⟨b,false,some (sink expected clock)⟩ := by
  have hp : ¬ handoff expected clock < expected.length := by
    simp [handoff,rewindStart,width]; omega
  have hg : ¬ handoff expected clock < expected.length+5*clock := by
    simp [handoff,rewindStart,width]; omega
  have hb0 : handoff expected clock ≠ Source284CertificateValidator.boundary expected clock 0 := by
    simp [handoff,rewindStart,width,Source284CertificateValidator.boundary,
      Source284CertificateGrammarClock.state]; omega
  have hb3 : handoff expected clock ≠ Source284CertificateValidator.boundary expected clock 3 := by
    simp [handoff,rewindStart,width,Source284CertificateValidator.boundary,
      Source284CertificateGrammarClock.state]; omega
  have hr : ¬ handoff expected clock < rewindStart expected clock+width expected clock := by
    simp [handoff]
  have hf : handoff expected clock ≠ rewindStart expected clock+width expected clock := by
    simp [handoff]
  simp [Source284CertificateDispatch.table,hp,hg,hb0,hb3,hr,hf]

theorem no_early_handoff (expected : List Bool) (clock : Nat) (c : Config) (fuel : Nat)
    (hend : (run (Source284CertificateDispatch.table expected clock) c fuel).state =
      some (handoff expected clock)) :
    ∀ i < fuel, (run (Source284CertificateDispatch.table expected clock) c i).state ≠
      some (handoff expected clock) := by
  intro i hi he
  have hs : (run (Source284CertificateDispatch.table expected clock) c (i+1)).state =
      some (sink expected clock) := by
    cases hc : run (Source284CertificateDispatch.table expected clock) c i with
    | mk left right state =>
        have hh : state = some (handoff expected clock) := by simpa [hc] using he
        subst state
        simp [run,hc,step,validator_handoff_row]
  have hsink := Source284CertificateDispatch.sink_forever expected clock
    (run (Source284CertificateDispatch.table expected clock) c (i+1)) (fuel-(i+1)) hs
  rw [← Source284CertificateValidator.run_add] at hsink
  have ht : i+1+(fuel-(i+1)) = fuel := by omega
  rw [ht,hend] at hsink
  simp [sink] at hsink

theorem relocated_row (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (q : Nat) (read : Bool) :
    table expected clock verifier (allocated expected clock + q) read =
      shiftRow (allocated expected clock) (verifier q read) := by
  have hne : allocated expected clock + q ≠ handoff expected clock := by
    simp [allocated,sink]
    omega
  simp [table,hne]

theorem shifted_next_bound (expected : List Bool) (clock n : Nat)
    (verifier : Nat → Bool → Row) (hclosed : Closed n verifier)
    (q : Nat) (hq : q < n) (read : Bool) (q' : Nat)
    (hnext : (shiftRow (allocated expected clock) (verifier q read)).next = some q') :
    q' < allocated expected clock+n := by
  cases hn : (verifier q read).next with
  | none => simp [shiftRow,hn] at hnext
  | some r =>
      have hr := hclosed q hq read r hn
      simp only [shiftRow,hn,Option.map_some,Option.some.injEq] at hnext
      omega

/-- The linked table has exactly the validator allocation plus the
verifier's state budget, provided the verifier is nonempty and closed. -/
theorem closed (expected : List Bool) (clock n : Nat)
    (verifier : Nat → Bool → Row) (hn : 0 < n) (hclosed : Closed n verifier) :
    Closed (allocated expected clock+n) (table expected clock verifier) := by
  intro q hq read q' hnext
  by_cases hh : q = handoff expected clock
  · subst q
    have hrow : table expected clock verifier (handoff expected clock) read =
        shiftRow (allocated expected clock) (verifier 0 read) := by simp [table]
    rw [hrow] at hnext
    exact shifted_next_bound expected clock n verifier hclosed 0 hn read q' hnext
  · by_cases ha : allocated expected clock ≤ q
    · have hrow : table expected clock verifier q read =
          shiftRow (allocated expected clock) (verifier (q-allocated expected clock) read) := by
        simp [table,hh,ha]
      rw [hrow] at hnext
      apply shifted_next_bound expected clock n verifier hclosed (q-allocated expected clock)
        (by omega) read q' hnext
    · have hrow : table expected clock verifier q read =
          Source284CertificateDispatch.table expected clock q read := by simp [table,hh,ha]
      rw [hrow] at hnext
      have hq' := Source284CertificateDispatch.closed expected clock q (by omega) read q' hnext
      omega

theorem relocated_step (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (c : Config) :
    step (table expected clock verifier) (shiftConfig (allocated expected clock) c) =
      shiftConfig (allocated expected clock) (step verifier c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig, Option.map_some, step, relocated_row, shiftRow]
      split <;> rfl

theorem relocated_run (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table expected clock verifier) (shiftConfig (allocated expected clock) c) fuel =
      shiftConfig (allocated expected clock) (run verifier c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run, ih, relocated_step]

theorem handoff_step (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (left right : Nat) :
    step (table expected clock verifier) ⟨left,right,some (handoff expected clock)⟩ =
      shiftConfig (allocated expected clock) (step verifier ⟨left,right,some 0⟩) := by
  have hrow (b : Bool) : table expected clock verifier (handoff expected clock) b =
      shiftRow (allocated expected clock) (verifier 0 b) := by simp [table]
  cases ht : (verifier 0 (decide (right % 2 = 1))).turn <;>
    simp [step,hrow,shiftConfig,shiftRow,ht]

/-- From the supplied handoff, exactly `fuel+1` combined steps simulate the
same positive number of verifier steps, preserving its accepting outcome. -/
theorem handoff_run (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (left right fuel : Nat) :
    run (table expected clock verifier) ⟨left,right,some (handoff expected clock)⟩
        (fuel+1) =
      shiftConfig (allocated expected clock) (run verifier ⟨left,right,some 0⟩ (fuel+1)) := by
  rw [run_front, handoff_step, relocated_run, ← run_front]

/-- A matching, complete certificate reaches the same handoff in the
combined table, because that handoff cannot occur earlier in the original
validator run. -/
theorem validator_rewinds (expected bits : List Bool) (tail : Nat)
    (verifier : Nat → Bool → Row)
    (hm : Source284CertificateGrammar.scanState 0 bits = 0 ∨
      Source284CertificateGrammar.scanState 0 bits = 3) :
    let c : Config := ⟨0,Source284LoaderAlgebra.stack (expected++bits) tail,some 0⟩
    run (table expected bits.length verifier) c (2*(expected.length+bits.length)+2) =
      ⟨0,Source284LoaderAlgebra.stack (expected++bits) tail,
        some (handoff expected bits.length)⟩ := by
  let c : Config := ⟨0,Source284LoaderAlgebra.stack (expected++bits) tail,some 0⟩
  let fuel := 2*(expected.length+bits.length)+2
  have hv : Valid (allocated expected bits.length) c := by
    intro q hq
    simp only [c, Option.some.injEq] at hq
    subst q
    simp [allocated,sink,handoff,rewindStart,width]
  have hr := Source284CertificateDispatch.matching_rewind expected bits tail hm
  have he : (run (Source284CertificateDispatch.table expected bits.length) c fuel).state =
      some (handoff expected bits.length) := by
    change (run (Source284CertificateDispatch.table expected bits.length)
      ⟨0,Source284LoaderAlgebra.stack (expected++bits) tail,some 0⟩
      (2*(expected.length+bits.length)+2)).state = _
    rw [hr]
  have ha := no_early_handoff expected bits.length c fuel he
  have hrun := run_before_handoff expected bits.length verifier c fuel hv ha
  change run (table expected bits.length verifier) c fuel =
    ⟨0,Source284LoaderAlgebra.stack (expected++bits) tail,
      some (handoff expected bits.length)⟩
  rw [hrun]
  exact hr

/-- The matching validator and verifier now execute in one finite table;
the verifier's first transition is charged at the handoff. -/
theorem validator_then_verifier (expected bits : List Bool) (tail : Nat)
    (verifier : Nat → Bool → Row) (fuel : Nat)
    (hm : Source284CertificateGrammar.scanState 0 bits = 0 ∨
      Source284CertificateGrammar.scanState 0 bits = 3) :
    let certificate := Source284LoaderAlgebra.stack (expected++bits) tail
    run (table expected bits.length verifier) ⟨0,certificate,some 0⟩
      ((2*(expected.length+bits.length)+2)+(fuel+1)) =
      shiftConfig (allocated expected bits.length)
        (run verifier ⟨0,certificate,some 0⟩ (fuel+1)) := by
  dsimp only
  rw [Source284CertificateValidator.run_add, validator_rewinds expected bits tail verifier hm,
    handoff_run]

end Shared.Beeping.NPcoNP.Source284VerifierHandoff
