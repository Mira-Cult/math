import Shared.Beeping.NPcoNP.Source284DynamicInputFrame

/-! Restore a known zero sentinel on the opposite tape half by two paid
transitions, preserving the entire current half. -/
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284SetLeftOne

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨b,true,some 1⟩
  else if q=1 then ⟨true,true,some 2⟩
  else shiftRow 2 (continuation (q-2) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (2+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hs : q<2
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 2 (continuation (q-2) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega] using hnext
    cases ht : (continuation (q-2) b).next with
    | none => simp [shiftRow,ht] at he
    | some s =>
      have hr := hv (q-2) (by omega) b s ht
      simp [shiftRow,ht] at he
      subst q'
      omega

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 2 c) fuel = shiftConfig 2 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,ih]
    cases hc : run continuation c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        simp only [shiftConfig,Option.map_some,step,table,show 2+q ≠ 0 by omega,
          show 2+q ≠ 1 by omega,↓reduceIte,show 2+q-2=q by omega,shiftRow]
        split <;> rfl

theorem set_then (continuation : Nat → Bool → Row) (left right fuel : Nat) :
    run (table continuation) ⟨2*left,right,some 0⟩ (2+fuel) =
      shiftConfig 2 (run continuation ⟨2*left+1,right,some 0⟩ fuel) := by
  have h0 : step (table continuation) ⟨2*left,right,some 0⟩ = ⟨right,2*left,some 1⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  have h1 : step (table continuation) ⟨right,2*left,some 1⟩ = ⟨2*left+1,right,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
  rw [Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    (step (table continuation) ⟨2*left,right,some 0⟩)) fuel = _
  rw [h0,h1]
  change run (table continuation) (shiftConfig 2 ⟨2*left+1,right,some 0⟩) fuel = _
  exact relocated_run continuation _ fuel

end Shared.Beeping.NPcoNP.Source284SetLeftOne
