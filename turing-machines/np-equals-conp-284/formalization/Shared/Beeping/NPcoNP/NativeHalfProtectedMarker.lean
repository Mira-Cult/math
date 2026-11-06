import Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

/-! A left marker survives the literal state-28 erasure scan and guarantees
finite progress through state 97. Preconditions concern a supplied tape; no
blank-start reachability is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeHalfProtectedMarker
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The rightward erasure never touches a protected one strictly to the left
of its starting head; it leaves state 6 over a zero. -/
theorem scan_to_zero_preserving_marker (k : Nat) (h p : Int) (t : Int → Bool)
    (hp : p ≤ h-2) (hmark : t p = true) (hleft : t (h-1) = false)
    (hz : t (h+(k : Int)) = false) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ n ≤ k+1 ∧ e.state = 6 ∧
      h-1 ≤ e.head ∧ e.tape e.head = false ∧ e.tape p = true ∧
      (∀ q, q < h → e.tape q = t q) ∧ silentSegment machine (cfg 28 h t) e n := by
  induction k generalizing h t with
  | zero =>
    refine ⟨1,cfg 6 (h-1) t,by omega,by omega,rfl,by simp [cfg],hleft,hmark,by intro q hq; rfl,?_⟩
    exact oneSeg machine _ _ (step28_zero h t (by simpa using hz))
  | succ k ih =>
    cases hv : t h with
    | false =>
      refine ⟨1,cfg 6 (h-1) t,by omega,by omega,rfl,by simp [cfg],hleft,hmark,by intro q hq; rfl,?_⟩
      exact oneSeg machine _ _ (step28_zero h t hv)
    | true =>
      have hneq : h+1+(k : Int) ≠ h := by omega
      have he : h+1+(k : Int) = h+((Nat.succ k : Nat) : Int) := by push_cast; omega
      have hz' : put t h false ((h+1)+(k : Int)) = false := by
        rw [put_other _ _ _ _ hneq,he]
        exact hz
      have hm' : put t h false p = true := by
        rw [put_other _ _ _ _ (by omega)]
        exact hmark
      have hl' : put t h false ((h+1)-1) = false := by simp [put]
      obtain ⟨n,e,hn,hnBound,hstate,hhead,hread,hprotected,hprefix,hseg⟩ :=
        ih (h+1) (put t h false) (by omega) hm' hl' hz'
      have hpref : ∀ q, q < h → e.tape q = t q := by
        intro q hq
        rw [hprefix q (by omega),put_other _ _ _ _ (by omega)]
      refine ⟨1+n,e,by omega,by omega,hstate,by omega,hread,hprotected,hpref,?_⟩
      exact segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step28_one h t hv)) hseg

/-- A leftward one, a zero immediately left of state 28, and a rightward zero
suffice for the literal machine to reach state 83 in positive finite silent
time. The marker is preserved in the output tape. -/
theorem state28_to_83 (h p : Int) (t : Int → Bool)
    (hp : p ≤ h-2) (hmark : t p = true) (hleft : t (h-1) = false)
    (k : Nat) (hz : t (h+(k : Int)) = false) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state = 83 ∧ e.tape p = true ∧ e.tape (e.head+1) = true ∧
      (∀ q, q < h-1 → e.tape q = t q) ∧ silentSegment machine (cfg 28 h t) e n := by
  obtain ⟨n,c,hn,_,hc,hhead,hread,hprotected,hprefix,hseg⟩ :=
    scan_to_zero_preserving_marker k h p t hp hmark hleft hz
  let t' := put c.tape c.head true
  have hp' : p ≤ c.head-1 := by omega
  have hm' : t' p = true := by
    dsimp [t']
    rw [put_other _ _ _ _ (by omega)]
    exact hprotected
  have hcfg : c = cfg 6 c.head c.tape := by
    have he : c = cfg c.state c.head c.tape := by cases c; rfl
    simpa only [hc] using he
  have hstep : machine.step c = (cfg 97 (c.head-1) t',false) := by
    conv_lhs => rw [hcfg]
    exact step6_zero c.head c.tape hread
  let d := ((c.head-1)-p).toNat
  have hd : (c.head-1)-(d : Int)=p := by
    have hn : 0 ≤ (c.head-1)-p := by omega
    have he : (d : Int) = (c.head-1)-p := Int.toNat_of_nonneg hn
    omega
  have hm'' : t' ((c.head-1)-(d : Int)) = true := by rw [hd]; exact hm'
  obtain ⟨m,hm,_,hfound,hscan⟩ := scan97_marked d (c.head-1) t' hm''
  have hprefix' : ∀ q, q < h-1 → t' q = t q := by
    intro q hq
    dsimp [t']
    rw [put_other _ _ _ _ (by omega)]
    exact hprefix q (by omega)
  refine ⟨n+1+m,cfg 83 ((c.head-1)-(m : Int)) t',by omega,rfl,hm',hfound,hprefix',?_⟩
  exact segAdd machine _ _ _ (n+1) m
    (segAdd machine _ _ _ n 1 hseg (oneSeg machine _ _ hstep)) hscan

end Shared.Beeping.NPcoNP.NativeHalfProtectedMarker
