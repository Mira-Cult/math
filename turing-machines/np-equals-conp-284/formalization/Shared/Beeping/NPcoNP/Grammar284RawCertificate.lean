import Shared.Beeping.NPcoNP.Grammar284JumpProgress
import Shared.Beeping.NPcoNP.GraphExtendedTrace
import Shared.Beeping.NPcoNP.GraphCandidate284Coverage

namespace Shared.Beeping.NPcoNP.Grammar284Operational
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284JumpProgress
open Shared.Beeping.NPcoNP.GraphExtended284
open Shared.Beeping.NPcoNP.MaskInvariant
open Shared.Beeping.NPcoNP.Parent290Coalesced
open PASoundness.RegisterMachine
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

/-- Decode the original retained row's action independently of its uncontracted targets. -/
def decodeRaw (k : Nat) : Option (Action 12 × Nat × Nat) := do
  let row ← producerFullRows[k]?
  let ins ← decode ⟨row.op, row.targets.map (fun _ => 0)⟩
  let (yes,no) ← match row.targets with
    | [a] => some (a,a)
    | [a,b] => some (a,b)
    | _ => none
  pure (ins.action,yes,no)

def rawInstruction (i : Fin 185) : Option (Action 12 × Nat × Nat) := do
  let k ← producerNumbering.kept[i.val]?
  decodeRaw k

def rawCheck (i : Fin 185) : Bool :=
  match rawInstruction i with
  | none => false
  | some (action,yes,no) =>
      decide (action = target.code[i].action) &&
      (Grammar284.target producerFullRows producerNumbering.map 3 yes == some target.code[i].yes.val) &&
      (Grammar284.target producerFullRows producerNumbering.map 3 no == some target.code[i].no.val)

set_option maxHeartbeats 0 in
 theorem rawChecks : (List.finRange 185).all rawCheck = true := by decide

theorem rawCheck_sound (i : Fin 185) :
    ∃ k action yes no, producerNumbering.kept[i.val]? = some k ∧
      decodeRaw k = some (action,yes,no) ∧
      action = target.code[i].action ∧
      Grammar284.target producerFullRows producerNumbering.map 3 yes = some target.code[i].yes.val ∧
      Grammar284.target producerFullRows producerNumbering.map 3 no = some target.code[i].no.val := by
  have hc := List.all_eq_true.mp rawChecks i (List.mem_finRange i)
  unfold rawCheck at hc
  cases hi : rawInstruction i with
  | none => simp [hi] at hc
  | some value =>
    rcases value with ⟨action,yes,no⟩
    simp only [hi, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    unfold rawInstruction at hi
    cases hk : producerNumbering.kept[i.val]? with
    | none => simp [hk] at hi
    | some k =>
      have hd : decodeRaw k = some (action,yes,no) := by simpa [hk] using hi
      exact ⟨k,action,yes,no,rfl,hd,hc.1.1,hc.1.2,hc.2⟩

#print axioms rawChecks
#print axioms rawCheck_sound
end Shared.Beeping.NPcoNP.Grammar284Operational
