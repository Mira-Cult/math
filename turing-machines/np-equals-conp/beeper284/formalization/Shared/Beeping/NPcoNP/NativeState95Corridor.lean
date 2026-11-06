import Shared.Beeping.NPcoNP.NativeHalfState95Stop

/-! State 95 clears a supplied run of ones and stops at its first zero. -/
namespace Shared.Beeping.NPcoNP.NativeState95Corridor
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact

open Shared.Beeping.NPcoNP.NativeHalfState95Stop
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem scan95_corridor (h p : Int) (t : Int → Bool) (hp : p≤h)
    (zero : t p=false) (ones : ∀ q, p<q → q≤h → t q=true) :
    ∃ n : Nat, 0<n ∧ silentSegment machine (cfg 95 h t)
      (cfg 1 (p-1) (clearRange t (p+1) (h+1))) n := by
  let k := (h-p).toNat
  have hk : h-(k : Int)=p := by
    have he : (k : Int)=h-p := Int.toNat_of_nonneg (by omega)
    omega
  obtain ⟨n,hn,hbound,hstop,hones,hseg⟩ := scan95_exact_with_stop k h t (by simpa only [hk] using zero)
  have hstopEq : h-(n : Int)+1=p := by
    have hge : p≤h-(n : Int)+1 := by
      have he : (k : Int)=h-p := Int.toNat_of_nonneg (by omega)
      omega
    by_contra hne
    have hv := ones (h-(n : Int)+1) (by omega) (by omega)
    rw [hstop] at hv
    contradiction
  refine ⟨n,hn,?_⟩
  have hh : h-(n : Int)=p-1 := by omega
  have hc : h-(n : Int)+2=p+1 := by omega
  rw [hc,hh] at hseg
  exact hseg

#print axioms scan95_corridor
end Shared.Beeping.NPcoNP.NativeState95Corridor
