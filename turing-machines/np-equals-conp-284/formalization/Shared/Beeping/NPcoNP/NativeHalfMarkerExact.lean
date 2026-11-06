import Shared.Beeping.NPcoNP.NativeHalfProtectedMarker
import Shared.Beeping.NPcoNP.NativeHalfState28Exact

/-! Exact marker location after the literal state-28 clearing scan and
state-97 leftward search, under an explicit zero corridor. -/
namespace Shared.Beeping.NPcoNP.NativeHalfMarkerExact

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- State 28 clears every cell between the left marker and its output head. -/
theorem scan28_corridor (k : Nat) (h p : Int) (t : Int → Bool)
    (hp : p≤h-2) (hm : t p=true)
    (hc : ∀ q, p<q → q<h → t q=false)
    (hz : t (h+(k : Int))=false) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=6 ∧ h-1≤e.head ∧
      e.tape e.head=false ∧ e.tape p=true ∧
      (∀ q, p<q → q≤e.head → e.tape q=false) ∧
      (∀ q, q<h → e.tape q=t q) ∧
      e.tape=clearRange t h (e.head+1) ∧
      t (e.head+1)=false ∧
      (∀ q, h≤q → q≤e.head → t q=true) ∧
      silentSegment machine (cfg 28 h t) e n := by
  induction k generalizing h t with
  | zero =>
    refine ⟨1,cfg 6 (h-1) t,by omega,rfl,by simp [cfg],?_,hm,?_,by intro q hq; rfl,?_,?_,?_,?_⟩
    · exact hc (h-1) (by omega) (by omega)
    · intro q hq hq'
      exact hc q hq (by simp [cfg] at hq'; omega)
    · simpa only [cfg,show h-1+1=h by omega,clear_empty]
    · simpa [cfg] using hz
    · intro q hq hq'; simp [cfg] at hq'; omega
    · exact oneSeg machine _ _ (step28_zero h t (by simpa using hz))
  | succ k ih =>
    cases hv : t h with
    | false =>
      refine ⟨1,cfg 6 (h-1) t,by omega,rfl,by simp [cfg],?_,hm,?_,by intro q hq; rfl,?_,?_,?_,?_⟩
      · exact hc (h-1) (by omega) (by omega)
      · intro q hq hq'
        exact hc q hq (by simp [cfg] at hq'; omega)
      · simpa only [cfg,show h-1+1=h by omega,clear_empty]
      · simpa [cfg] using hv
      · intro q hq hq'; simp [cfg] at hq'; omega
      · exact oneSeg machine _ _ (step28_zero h t hv)
    | true =>
      let t' := put t h false
      have hneq : h+1+(k : Int)≠h := by omega
      have he : h+1+(k : Int)=h+((Nat.succ k : Nat) : Int) := by push_cast; omega
      have hz' : t' ((h+1)+(k : Int))=false := by
        change put t h false ((h+1)+(k : Int))=false
        rw [put_other _ _ _ _ hneq,he]
        exact hz
      have hm' : t' p=true := by
        change put t h false p=true
        rw [put_other _ _ _ _ (by omega)]
        exact hm
      have hc' : ∀ q, p<q → q<h+1 → t' q=false := by
        intro q hq hq'
        by_cases heq : q=h
        · subst q; simp [t',put]
        · change put t h false q=false
          rw [put_other _ _ _ _ heq]
          exact hc q hq (by omega)
      obtain ⟨n,e,hn,hstate,hhead,hread,hmark,hcorr,hprefix,hexact,hstop,hones,hseg⟩ :=
        ih (h+1) t' (by omega) hm' hc' hz'
      have hpref : ∀ q, q<h → e.tape q=t q := by
        intro q hq
        rw [hprefix q (by omega)]
        change put t h false q=t q
        exact put_other _ _ _ _ (by omega)
      have hextape : e.tape=clearRange t h (e.head+1) := by
        rw [hexact]
        change clearRange (put t h false) (h+1) (e.head+1) = _
        exact clear_tail t h (e.head+1) (by omega)
      have hstop' : t (e.head+1)=false := by
        have hne : e.head+1≠h := by omega
        change put t h false (e.head+1)=false at hstop
        rw [put_other _ _ _ _ hne] at hstop
        exact hstop
      have hones' : ∀ q, h≤q → q≤e.head → t q=true := by
        intro q hq hq'
        by_cases he : q=h
        · subst q; exact hv
        · have hh := hones q (by omega) hq'
          change put t h false q=true at hh
          rw [put_other _ _ _ _ he] at hh
          exact hh
      refine ⟨1+n,e,by omega,hstate,by omega,hread,hmark,hcorr,hpref,hextape,hstop',hones',?_⟩
      exact segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step28_one h t hv)) hseg

/-- State 97 scans exactly the specified zero corridor and stops just left
of the marked one. -/
theorem scan97_corridor (d : Nat) (h p : Int) (t : Int → Bool)
    (he : h-(d : Int)=p) (hm : t p=true)
    (hc : ∀ q, p<q → q≤h → t q=false) :
    silentSegment machine (cfg 97 h t) (cfg 83 (p-1) t) (d+1) := by
  induction d generalizing h with
  | zero =>
    have hh : h=p := by simpa using he
    subst h
    simpa using oneSeg machine _ _ (step97_one p t hm)
  | succ d ih =>
    have hp : p<h := by push_cast at he; omega
    have hzero : t h=false := hc h hp (le_refl _)
    have he' : (h-1)-(d : Int)=p := by push_cast at he; omega
    have hc' : ∀ q, p<q → q≤h-1 → t q=false := by
      intro q hq hq'
      exact hc q hq (by omega)
    have hrest := ih (h-1) he' hc'
    have hall := segAdd machine _ _ _ 1 (d+1) (oneSeg machine _ _ (step97_zero h t hzero)) hrest
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

/-- A state-28 input with a marked one and a zero corridor returns to state
83 with its head exactly one cell left of the marker. -/
theorem state28_to83_exact (h p : Int) (t : Int → Bool)
    (hp : p≤h-2) (hm : t p=true)
    (hc : ∀ q, p<q → q<h → t q=false)
    (k : Nat) (hz : t (h+(k : Int))=false) :
    ∃ (n : Nat) (stop : Int) (out : Int → Bool), 0<n ∧ h-1≤stop ∧ out p=true ∧
      t (stop+1)=false ∧ (∀ q, h≤q → q≤stop → t q=true) ∧
      out=put (clearRange t h (stop+1)) stop true ∧
      (∀ q, q<h-1 → out q=t q) ∧
      silentSegment machine (cfg 28 h t) (cfg 83 (p-1) out) n := by
  obtain ⟨n,c,hn,hstate,hhead,hread,hmark,hcorr,hprefix,hexact,hstop,hones,hseg⟩ :=
    scan28_corridor k h p t hp hm hc hz
  let out := put c.tape c.head true
  have hcfg : c=cfg 6 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    simpa only [hstate] using he
  have hstep : machine.step c=(cfg 97 (c.head-1) out,false) := by
    conv_lhs => rw [hcfg]
    exact step6_zero c.head c.tape hread
  have houtmark : out p=true := by
    change put c.tape c.head true p=true
    rw [put_other _ _ _ _ (by omega)]
    exact hmark
  have hzero : ∀ q, p<q → q≤c.head-1 → out q=false := by
    intro q hq hq'
    change put c.tape c.head true q=false
    rw [put_other _ _ _ _ (by omega)]
    exact hcorr q hq (by omega)
  let d := (c.head-1-p).toNat
  have hd : (c.head-1)-(d : Int)=p := by
    have hn' : 0≤c.head-1-p := by omega
    have he : (d : Int)=c.head-1-p := Int.toNat_of_nonneg hn'
    omega
  have hscan := scan97_corridor d (c.head-1) p out hd houtmark hzero
  have houtprefix : ∀ q, q<h-1 → out q=t q := by
    intro q hq
    change put c.tape c.head true q=t q
    rw [put_other _ _ _ _ (by omega),hprefix q (by omega)]
  have houtExact : out=put (clearRange t h (c.head+1)) c.head true := by dsimp [out]; rw [hexact]
  exact ⟨n+1+(d+1),c.head,out,by omega,hhead,houtmark,hstop,hones,houtExact,houtprefix,
    segAdd machine _ _ _ (n+1) (d+1)
      (segAdd machine _ _ _ n 1 hseg (oneSeg machine _ _ hstep)) hscan⟩

end Shared.Beeping.NPcoNP.NativeHalfMarkerExact

#print axioms Shared.Beeping.NPcoNP.NativeHalfMarkerExact.state28_to83_exact
