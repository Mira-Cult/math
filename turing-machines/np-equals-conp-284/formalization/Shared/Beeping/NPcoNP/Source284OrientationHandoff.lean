import Shared.Beeping.NPcoNP.Source284TaggedMarkerSeed
import Shared.Beeping.NPcoNP.Source284FiniteTapeEncoding

/-! A paid, finite-control orientation normalizer before an arbitrary
continuation. This is a local adapter: it does not attach itself to the
serializer's table or assert any blank-tape window. -/
namespace Shared.Beeping.NPcoNP.Source284OrientationHandoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Codes.FinitePrograms (Tape)

def table (start : Nat) (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 2⟩
  else if q = 1 then ⟨b,true,some 2⟩
  else if q = 2 then ⟨b,true,some (3+start)⟩
  else shiftRow 3 (continuation (q-3) b)

def initialState (rev : Bool) : Nat := if rev then 0 else 1

def normalized (rev : Bool) (left right : Nat) : Nat × Nat :=
  if rev then (right/2,2*left+right%2) else (left,right)

theorem closed (states start : Nat) (continuation : Nat → Bool → Row)
    (hs : start < states) (hc : Closed states continuation) :
    Closed (3+states) (table start continuation) := by
  intro q hq b q' hn
  by_cases h0 : q=0
  · subst q; simp [table] at hn; omega
  · by_cases h1 : q=1
    · subst q; simp [table] at hn; omega
    · by_cases h2 : q=2
      · subst q; simp [table] at hn; omega
      · have hv := hc (q-3) (by omega) b
        have he : (shiftRow 3 (continuation (q-3) b)).next = some q' := by
          simpa [table,h0,h1,h2] using hn
        cases hh : (continuation (q-3) b).next with
        | none => simp [shiftRow,hh] at he
        | some r =>
          have hr := hv r hh
          simp [shiftRow,hh] at he
          subst q'; omega

theorem two_steps (start : Nat) (continuation : Nat → Bool → Row)
    (rev : Bool) (left right : Nat) :
    run (table start continuation) ⟨left,right,some (initialState rev)⟩ 2 =
      ⟨(normalized rev left right).1,(normalized rev left right).2,some (3+start)⟩ := by
  cases rev <;>
    simp [run,step,table,initialState,normalized,Source284HardwireTable.bit_decide_mod,
      Nat.testBit_zero] <;> omega

theorem relocated_step (start : Nat) (continuation : Nat → Bool → Row) (c : Config) :
    step (table start continuation) (shiftConfig 3 c) =
      shiftConfig 3 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,table,show 3+q ≠ 0 by omega,
        show 3+q ≠ 1 by omega,show 3+q ≠ 2 by omega,↓reduceIte,
        show 3+q-3=q by omega,shiftRow]
      split <;> rfl

theorem relocated_run (start : Nat) (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table start continuation) (shiftConfig 3 c) fuel =
      shiftConfig 3 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem then_run (start : Nat) (continuation : Nat → Bool → Row)
    (rev : Bool) (left right fuel : Nat) :
    run (table start continuation) ⟨left,right,some (initialState rev)⟩ (2+fuel) =
      shiftConfig 3 (run continuation
        ⟨(normalized rev left right).1,(normalized rev left right).2,some start⟩ fuel) := by
  rw [Source284HardwireCorrect.run_add,two_steps]
  change run (table start continuation)
    (shiftConfig 3 ⟨(normalized rev left right).1,(normalized rev left right).2,some start⟩) fuel = _
  exact relocated_run start continuation _ fuel

/-- Two paid source moves restore the same physical head and tape, facing
right, from either relative orientation. -/
theorem normalized_represented (t : Tape) (rev : Bool) (state : Nat) :
    normalized rev (represented t rev state).left (represented t rev state).right =
      ((represented t false state).left,(represented t false state).right) := by
  cases rev with
  | false => rfl
  | true =>
    rcases t with ⟨left,head,right⟩
    cases head <;>
      simp [normalized,represented,Shared.Beeping.NPcoNP.Source284FiniteTapeStep.digit] <;> omega


/-- The encoded numeric source executes the two-move orientation adapter
and then every requested step of the supplied closed continuation. -/
theorem source_then (states start : Nat) (continuation : Nat → Bool → Row)
    (rev : Bool) (left right fuel : Nat)
    (hs : start < states) (hc : Closed states continuation) :
    Source284Relative.run (encode (3+states) (table start continuation) 1)
      ⟨left,right,active (initialState rev)⟩ (2+fuel) =
      Source284SourceRelocation.lift 3
        (Source284Relative.run (encode states continuation 1)
          ⟨(normalized rev left right).1,(normalized rev left right).2,active start⟩ fuel) := by
  let initial : Config := ⟨left,right,some (initialState rev)⟩
  have hi : Valid (3+states) initial := by
    intro q hq
    simp only [initial,Option.some.injEq] at hq
    subst q
    cases rev <;> simp [initialState] <;> omega
  have hr := run_toSource (3+states) (table start continuation) 1 initial
    (closed states start continuation hs hc) hi (2+fuel)
  rw [then_run,← Source284SourceRelocation.lift_toSource] at hr
  let final : Config := ⟨(normalized rev left right).1,(normalized rev left right).2,some start⟩
  have hf : Valid states final := by
    intro q hq
    simp only [final,Option.some.injEq] at hq
    subst q
    exact hs
  have he := run_toSource states continuation 1 final hc hf fuel
  rw [← he] at hr
  exact hr

namespace Fixtures
example : run (table 0 (fun _ b => ⟨b,false,some 0⟩)) ⟨5,13,some 0⟩ 2 =
    ⟨6,11,some 3⟩ := by decide +kernel
example : run (table 0 (fun _ b => ⟨b,false,some 0⟩)) ⟨5,13,some 1⟩ 2 =
    ⟨5,13,some 3⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284OrientationHandoff
