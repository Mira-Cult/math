import Shared.Beeping.NPcoNP.NativeState98Progress

/-! Exact state-98 passage through a zero corridor to its first one. -/
namespace Shared.Beeping.NPcoNP.NativeState98Exact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeState98Progress
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem scan98_corridor (d : Nat) (h p : Int) (t : Int → Bool)
    (he : h-(d : Int)=p) (hm : t p=true)
    (hc : ∀ q, p<q → q≤h → t q=false) :
    silentSegment machine (cfg 98 h t) (cfg 97 (p-1) (put t p false)) (d+1) := by
  induction d generalizing h with
  | zero =>
    have hh : h=p := by simpa using he
    subst h
    simpa using oneSeg machine _ _ (step98_one p t hm)
  | succ d ih =>
    have hp : p<h := by push_cast at he; omega
    have hzero : t h=false := hc h hp (le_refl _)
    have he' : (h-1)-(d : Int)=p := by push_cast at he; omega
    have hc' : ∀ q, p<q → q≤h-1 → t q=false := by
      intro q hq hq'
      exact hc q hq (by omega)
    have hrest := ih (h-1) he' hc'
    have hall := segAdd machine _ _ _ 1 (d+1) (oneSeg machine _ _ (step98_zero h t hzero)) hrest
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

#print axioms scan98_corridor
end Shared.Beeping.NPcoNP.NativeState98Exact
