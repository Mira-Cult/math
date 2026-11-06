import Shared.Beeping.NPcoNP.NativeFirstNextPath

/-! A generic literal-table checker for silent, unchanged rightward dispatch. -/
namespace Shared.Beeping.NPcoNP.NativeRightDispatchGeneric
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeFirstNextPath
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- Follow a supplied word only while every literal-table transition writes
its input unchanged, moves right, and emits no beep. -/
def followRight : Fin 284 → List Bool → Option (Fin 284)
  | q, [] => some q
  | q, b::rest =>
    let row := machine.table.row q b
    if row.write=b ∧ row.move=.right ∧ row.beep=false then
      followRight row.next rest
    else none

/-- A checked rightward path executes in exactly the word length, silently,
without changing any tape cell. -/
theorem dispatch (q r : Fin 284) (h : Int) (t : Int → Bool) (word : List Bool)
    (checked : followRight q word=some r) (layout : Holds t h word) :
    silentSegment machine (cfg q h t) (cfg r (h+(word.length : Int)) t) word.length := by
  induction word generalizing q h with
  | nil =>
    simp only [followRight,Option.some.injEq] at checked
    subst r
    simp [silentSegment,WordEventSystem.advance,WordEventSystem.wordFrom]
  | cons b rest ih =>
    simp only [followRight] at checked
    by_cases hp : (machine.table.row q b).write=b ∧
        (machine.table.row q b).move=.right ∧ (machine.table.row q b).beep=false
    · rw [if_pos hp] at checked
      have hr : machine.table.row q b = ⟨b,.right,(machine.table.row q b).next,false⟩ := by
        cases he : machine.table.row q b with
        | mk w mv nxt beep =>
          simp only [he] at hp ⊢
          rcases hp with ⟨hw,hm,hb⟩
          subst w
          subst mv
          subst beep
          rfl
      have hl : t h=b ∧ Holds t (h+1) rest := layout
      have first := oneSeg machine _ _ (unchanged_right q (machine.table.row q b).next b h t hr hl.1)
      have later := ih (machine.table.row q b).next (h+1) checked hl.2
      have both := segAdd machine _ _ _ 1 rest.length first later
      simpa [List.length_cons,Nat.cast_add,Int.add_assoc,Nat.add_comm,Int.add_comm,Int.add_left_comm] using both
    · simp [hp] at checked

#print axioms dispatch
end Shared.Beeping.NPcoNP.NativeRightDispatchGeneric
