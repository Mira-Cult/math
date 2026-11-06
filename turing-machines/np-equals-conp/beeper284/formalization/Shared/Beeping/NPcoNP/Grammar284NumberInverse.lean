import Shared.Beeping.NPcoNP.Grammar284JumpProgress
namespace Shared.Beeping.NPcoNP.Grammar284Operational
open Shared.Beeping.NPcoNP.Grammar284
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

def inverseCheck (i : Nat) : Bool :=
  match producerNumbering.map[i]? with
  | some (some j) => producerNumbering.kept[j]? == some i
  | _ => true

set_option maxHeartbeats 0 in
theorem allInverses : (List.range producerNumbering.map.size).all inverseCheck = true := by decide

theorem inverse_sound (i j : Nat) (h : producerNumbering.map[i]? = some (some j)) :
    producerNumbering.kept[j]? = some i := by
  have ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp h
  have hc := List.all_eq_true.mp allInverses i (List.mem_range.mpr hi)
  simpa [inverseCheck,h,beq_iff_eq] using hc

#print axioms allInverses
#print axioms inverse_sound
end Shared.Beeping.NPcoNP.Grammar284Operational
