import Shared.Beeping.NPcoNP.Grammar284InfiniteIncrement
import Shared.Beeping.NPcoNP.Grammar284OrdinaryWindow
import Shared.Beeping.NPcoNP.NativeIncBank

/-! An infinite blank-tail parser window supplies any requested finite reserve.
The converse and reachable initialization are not asserted. -/
namespace Shared.Beeping.NPcoNP.Grammar284InfiniteWindowBridge
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Grammar284InfiniteIncrement
open Shared.Beeping.NPcoNP.Grammar284OrdinaryWindow
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

theorem blank_replicate (t : Int → Bool) (start : Int) (n : Nat)
    (blank : ∀ q, start≤q → t q=false) : Holds t start (List.replicate n false) := by
  induction n generalizing start with
  | zero => simp [Holds]
  | succ n ih =>
    simp only [List.replicate_succ,Holds]
    exact ⟨blank start (by omega),ih (start+1) (by intro q hq; exact blank q (by omega))⟩

/-- The same supplied tape satisfies every finite-reserve window. -/
theorem finite_of_infinite (state : Fin 185) (bank : Bank 12) (origin separator : Int)
    (t : Int → Bool) (window : InfiniteWindow state bank origin separator t) (reserve : Nat) :
    Window state bank origin separator t reserve := by
  obtain ⟨path,name,more,hleaf,hroom,hword,hleft,hgap,hright,hsep,hbank,htail⟩ := window
  refine ⟨path,name,more,hleaf,hroom,hword,hleft,hgap,hright,hsep,?_⟩
  exact holds_append_intro t (separator+1) _ _ hbank (blank_replicate t _ (reserve+2) htail)

#print axioms finite_of_infinite
end Shared.Beeping.NPcoNP.Grammar284InfiniteWindowBridge
