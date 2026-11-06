import Shared.Beeping.NPcoNP.NativeState97MarkerRegion
import Shared.Beeping.NPcoNP.NativeHalfSweep

/-! Literal state 98 always has a marker at or left of its head on the
blank-start run and hence cannot scan zeros forever. Whether a *second*
marker survives its erasing exit remains an independent obligation. -/
namespace Shared.Beeping.NPcoNP.NativeState98Progress
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeState97EntryInvariant
open Shared.Beeping.NPcoNP.NativeState97MarkerRegion
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 50000000

/-- Every non-loop incoming 98 row originates in the marker region. -/
theorem incoming98 (q : Fin 284) (b : Bool)
    (hn : (machine.table.row q b).next=98) :
    (q=98 ∧ b=false) ∨ (marked q=true ∧ b=true) := by
  have hall : ∀ (q : Fin 284) (b : Bool), (machine.table.row q b).next=98 →
      (q=98 ∧ b=false) ∨ (marked q=true ∧ b=true) := by decide
  exact hall q b hn

theorem incoming98_left (q : Fin 284) (b : Bool)
    (hn : (machine.table.row q b).next=98) :
    (machine.table.row q b).move=.left := by
  have hall : ∀ (q : Fin 284) (b : Bool), (machine.table.row q b).next=98 →
      (machine.table.row q b).move=.left := by decide
  exact hall q b hn

/-- Every actual state-98 visit has at least one one at or left of its head. -/
theorem reachable_98_marker (time : Nat)
    (hs : (machine.system.run time).state=98) :
    ∃ p : Int, p≤(machine.system.run time).head ∧ (machine.system.run time).tape p=true := by
  induction time with
  | zero =>
    have h0 : (machine.system.run 0).state.val=0 := machine_starts_zero.1
    have hh := congrArg Fin.val hs
    rw [h0] at hh
    contradiction
  | succ time ih =>
    let c := machine.system.run time
    let row := machine.table.row c.state (c.tape c.head)
    have hn : row.next=98 := hs
    have hm : row.move=.left := incoming98_left c.state (c.tape c.head) hn
    have hp : ∃ p : Int, p<c.head ∧ c.tape p=true := by
      rcases incoming98 c.state (c.tape c.head) hn with hloop | hregion
      · obtain ⟨p,hp,ht⟩ := ih hloop.1
        change p≤c.head at hp
        change c.tape p=true at ht
        have hne : p≠c.head := by
          intro he
          rw [he,hloop.2] at ht
          contradiction
        exact ⟨p,by omega,ht⟩
      · exact run_region time hregion.1
    exact left_marker_after_step c hm hp

theorem row98_zero : machine.table.row 98 false=⟨false,.left,98,false⟩ := by decide
theorem row98_one : machine.table.row 98 true=⟨false,.left,97,false⟩ := by decide

theorem step98_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 98 h t)=(cfg 98 (h-1) t,false) := by
  have hw : (⟨98,h,t⟩ : Config 284).write false=t := by
    rw [← ht]
    exact write_current _
  simp [cfg,Machine.step,ht,row98_zero,Move.apply,hw]

theorem step98_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 98 h t)=(cfg 97 (h-1) (put t h false),false) := by
  change machine.step ⟨98,h,t⟩=(⟨97,h-1,put t h false⟩,false)
  have hw : (⟨98,h,t⟩ : Config 284).write false=put t h false := rfl
  simp [Machine.step,ht,row98_one,Move.apply,hw]

/-- A marker `k` cells left forces state 98 to reach state 97 in at most
`k+1` silent steps, clearing exactly the encountered marker. -/
theorem scan98 (k : Nat) (h : Int) (t : Int → Bool)
    (hone : t (h-(k : Int))=true) :
    ∃ n : Nat, 0<n ∧ n≤k+1 ∧
      silentSegment machine (cfg 98 h t)
        (cfg 97 (h-(n : Int)) (put t (h-(n : Int)+1) false)) n := by
  induction k generalizing h with
  | zero =>
    refine ⟨1,by omega,by omega,?_⟩
    simpa using oneSeg machine _ _ (step98_one h t (by simpa using hone))
  | succ k ih =>
    cases hv : t h with
    | true =>
      refine ⟨1,by omega,by omega,?_⟩
      simpa using oneSeg machine _ _ (step98_one h t hv)
    | false =>
      have he : (h-1)-(k : Int)=h-((Nat.succ k : Nat) : Int) := by push_cast; omega
      have hh : t ((h-1)-(k : Int))=true := by rw [he]; exact hone
      obtain ⟨n,hn,hb,hs⟩ := ih (h-1) hh
      refine ⟨1+n,by omega,by omega,?_⟩
      have seg := segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step98_zero h t hv)) hs
      have hp : (h-1)-(n : Int)=h-((1+n : Nat) : Int) := by push_cast; omega
      simpa [hp] using seg

/-- State 98 always reaches 97 in at most `2*time+1` positive silent
steps on the blank-start run. This does not prove 97 has a surviving marker. -/
theorem reachable_98_to_97 (time : Nat)
    (hs : (machine.system.run time).state=98) :
    ∃ n : Nat, 0<n ∧ n≤2*time+1 ∧ ∃ e : Config 284, e.state=97 ∧
      silentSegment machine (machine.system.run time) e n := by
  let c := machine.system.run time
  obtain ⟨p,hp,hm⟩ := reachable_98_marker time hs
  change p≤c.head at hp
  change c.tape p=true at hm
  let k := (c.head-p).toNat
  have he : c.head-(k : Int)=p := by
    have hn : 0≤c.head-p := by omega
    have hk : (k : Int)=c.head-p := Int.toNat_of_nonneg hn
    omega
  have light := machine.run_lightCone time
  have hpmin : machine.startHead-(time : Int)≤p := by
    by_contra hnot
    have hb := light.2.2.1 p (by omega)
    have hb' : c.tape p=false := by simpa [c,machine_starts_zero.2.1] using hb
    rw [hm] at hb'
    contradiction
  have hkbound : k≤2*time := by
    have hh : c.head≤machine.startHead+(time : Int) := light.2.1
    have hk : (k : Int)=c.head-p := Int.toNat_of_nonneg (by omega)
    omega
  have ht : c.tape (c.head-(k : Int))=true := by rw [he]; exact hm
  obtain ⟨n,hn,hbound,hseg⟩ := scan98 k c.head c.tape ht
  have hc : c=cfg 98 c.head c.tape := by
    have he' : c=cfg c.state c.head c.tape := by cases c; rfl
    have hh : c.state=98 := hs
    simpa only [hh] using he'
  refine ⟨n,hn,by omega,cfg 97 (c.head-(n : Int)) (put c.tape (c.head-(n : Int)+1) false),rfl,?_⟩
  change silentSegment machine c _ n
  rw [hc]
  exact hseg

#print axioms incoming98
#print axioms reachable_98_marker
#print axioms scan98
#print axioms reachable_98_to_97
end Shared.Beeping.NPcoNP.NativeState98Progress
