import Shared.Beeping.NPcoNP.Source284SerializerTrace

/-! A finite, paid detector exit that retains the parity of the stopped
serializer state. The compiler uses that parity for tape orientation; the
continuation must allocate both initial orientation states. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284OrientedExit

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (allocated lifted)
open Shared.Beeping.NPcoNP.Source284DetectorExit (stopping stopConfig)

/-- Preserve the low bit of the source state, which is the relative
orientation for the finite-program compiler. -/
def side (q : Nat) : Nat := (Nat.unpair q).2 % 2

def entry (states : Nat) : Nat := allocated states + 2

/-- Two separate turning rows remember the orientation across two actual
transitions. Continuation states 0 and 1 are the two orientations. -/
def table (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (q : Nat) (b : Bool) : Row :=
  if q < allocated states then
    if stopping marks q then ⟨b,true,some (allocated states + side q)⟩
    else Source284DetectorProduct.table states marks original q b
  else if q < entry states then ⟨b,true,some (entry states + (q - allocated states))⟩
  else shiftRow (entry states) (continuation (q-entry states) b)

@[simp] theorem side_lt_two (q : Nat) : side q < 2 := Nat.mod_lt _ (by decide)

@[simp] theorem side_lifted (phase q : Nat) : side (Nat.pair phase q) = q % 2 := by
  simp [side]

theorem closed (states continuationStates : Nat) (marks : List Bool)
    (original continuation : Nat → Bool → Row) (hn : 2 ≤ continuationStates)
    (ho : Closed states original) (hc : Closed continuationStates continuation) :
    Closed (entry states+continuationStates) (table states marks original continuation) := by
  intro q hq b q' hnext
  by_cases hq0 : q < allocated states
  · by_cases hs : stopping marks q = true
    · simp [table,hq0,hs] at hnext
      subst q'; have h := side_lt_two q
      simp [entry]; omega
    · have hb : stopping marks q = false := Bool.eq_false_iff.mpr hs
      have ht : (Source284DetectorProduct.table states marks original q b).next = some q' := by
        simpa [table,hq0,hb] using hnext
      have hv := Source284DetectorProduct.closed states marks original ho q hq0 b q' ht
      simp [entry] at *; omega
  · by_cases he : q < entry states
    · simp [table,hq0,he] at hnext
      subst q'; simp [entry] at *; omega
    · have hge : entry states ≤ q := by omega
      have ht : (shiftRow (entry states) (continuation (q-entry states) b)).next = some q' := by
        simpa [table,hq0,he] using hnext
      cases hh : (continuation (q-entry states) b).next with
      | none => simp [shiftRow,hh] at ht
      | some r =>
        have hv := hc (q-entry states) (by omega) b r hh
        simp [shiftRow,hh] at ht
        subst q'; omega

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

/-- Both intermediate rows turn, so two paid steps restore the exact tape
and enter the orientation-selected continuation. -/
theorem exit_two (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (left right q : Nat) (hq : q < allocated states) (hs : stopping marks q = true) :
    run (table states marks original continuation) ⟨left,right,some q⟩ 2 =
      ⟨left,right,some (entry states + side q)⟩ := by
  have hside := side_lt_two q
  have hq₁ : ¬ allocated states + side q < allocated states := by omega
  have hq₂ : allocated states + side q < entry states := by simp [entry]; omega
  simp [run,step,table,hq,hs,hq₁,hq₂,Source284HardwireTable.bit_decide_mod] <;> omega

theorem relocated_row (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (q : Nat) (b : Bool) :
    table states marks original continuation (entry states+q) b =
      shiftRow (entry states) (continuation q b) := by
  have h0 : ¬ entry states+q < allocated states := by simp [entry]; omega
  have h1 : ¬ entry states+q < entry states := by omega
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

/-- The first marked stop enters the continuation at its selected orientation
and then follows all of its steps. -/
theorem run_first_stop (states : Nat) (marks : List Bool) (original continuation : Nat → Bool → Row)
    (c : Config) (hc : Valid (allocated states) c) (ho : Closed states original) (n fuel : Nat)
    (hbefore : ∀ i < n, ¬ stopConfig marks (run (Source284DetectorProduct.table states marks original) c i))
    (q : Nat) (hq : (run (Source284DetectorProduct.table states marks original) c n).state = some q)
    (hs : stopping marks q = true) :
    let last := run (Source284DetectorProduct.table states marks original) c n
    run (table states marks original continuation) c (n+2+fuel) =
      shiftConfig (entry states) (run continuation ⟨last.left,last.right,some (side q)⟩ fuel) := by
  dsimp only
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
      (run (Source284DetectorProduct.table states marks original) c n).right,some (side q)⟩) fuel = _
  rw [relocated_run]

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩

example : run (table 2 [true,true] loop loop)
    ⟨5,6,some (Nat.pair 8 0)⟩ 2 = ⟨5,6,some (entry 2)⟩ := by decide +kernel
example : run (table 2 [true,true] loop loop)
    ⟨5,6,some (Nat.pair 8 1)⟩ 2 = ⟨5,6,some (entry 2+1)⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284OrientedExit
