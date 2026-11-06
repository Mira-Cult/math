import Shared.Beeping.NPcoNP.NativeHalfState14Progress
import Shared.Beeping.NPcoNP.NativeHalfState97Progress

/-! The literal state-10 scan fills zeros until a supplied one. Starting on
a zero ensures the ensuing state-97 scan immediately reads a one and exits.
The marker premise is explicit; finite tape support alone cannot supply it. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState10Progress

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState97Progress

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem row10_zero : machine.table.row 10 false = ⟨true,.right,10,false⟩ := by decide
theorem row10_one : machine.table.row 10 true = ⟨true,.left,97,false⟩ := by decide
theorem row42_zero : machine.table.row 42 false = ⟨false,.right,10,false⟩ := by decide
theorem row261_zero : machine.table.row 261 false = ⟨true,.right,42,false⟩ := by decide

theorem step10_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 10 h t) = (cfg 10 (h+1) (setAt h t),false) := by
  have hw : (⟨10,h,t⟩ : Config 284).write true = setAt h t := rfl
  simp [cfg,Machine.step,ht,row10_zero,Move.apply,hw]

theorem step10_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 10 h t) = (cfg 97 (h-1) t,false) := by
  have hw : (⟨10,h,t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row10_one,Move.apply,hw]

theorem step42_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 42 h t) = (cfg 10 (h+1) t,false) := by
  have hw : (⟨42,h,t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row42_zero,Move.apply,hw]

theorem step261_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 261 h t) = (cfg 42 (h+1) (setAt h t),false) := by
  have hw : (⟨261,h,t⟩ : Config 284).write true = setAt h t := rfl
  simp [cfg,Machine.step,ht,row261_zero,Move.apply,hw]

/-- Filling a starting zero and then scanning to a supplied rightward one
reaches state 97 on a freshly written one in at most `k+1` transitions. -/
theorem scan10_marker (k : Nat) (h : Int) (t : Int → Bool)
    (h0 : t h=false) (hm : t (h+(k : Int))=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ n≤k+1 ∧ e.state=97 ∧
      e.tape e.head=true ∧ silentSegment machine (cfg 10 h t) e n := by
  induction k generalizing h t with
  | zero =>
    simp only [Nat.cast_zero,add_zero] at hm
    rw [h0] at hm
    contradiction
  | succ k ih =>
    let t' := setAt h t
    have hneq : (h+1)+(k : Int) ≠ h := by omega
    have hmark : t' ((h+1)+(k : Int))=true := by
      have he : (h+1)+(k : Int)=h+((Nat.succ k : Nat) : Int) := by push_cast; omega
      change (if (h+1)+(k : Int)=h then true else t ((h+1)+(k : Int)))=true
      rw [if_neg hneq,he]
      exact hm
    have hstep := oneSeg machine _ _ (step10_zero h t h0)
    cases hnext : t' (h+1) with
    | true =>
      have hfinish := oneSeg machine _ _ (step10_one (h+1) t' hnext)
      refine ⟨2,cfg 97 h t',by omega,by omega,rfl,?_,?_⟩
      · simp [cfg,t',setAt]
      · have hall := segAdd machine _ _ _ 1 1 hstep hfinish
        simpa [Int.add_assoc] using hall
    | false =>
      obtain ⟨n,e,hn,hbound,he,hmarker,hseg⟩ := ih (h+1) t' hnext hmark
      exact ⟨1+n,e,by omega,by omega,he,hmarker,
        segAdd machine _ _ _ 1 n hstep hseg⟩

/-- State 42 reading zero, followed by a zero and a supplied later one,
reaches state 83 in positive finite silent time. -/
theorem dispatch42_to83 (k : Nat) (h : Int) (t : Int → Bool)
    (h0 : t h=false) (hnext : t (h+1)=false) (hm : t ((h+1)+(k : Int))=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧
      silentSegment machine (cfg 42 h t) e n := by
  obtain ⟨n,e,hn,_,he,hmarker,hseg⟩ := scan10_marker k (h+1) t hnext hm
  have hcfg : e = cfg 97 e.head e.tape := by
    have hh : e = cfg e.state e.head e.tape := by cases e; rfl
    simpa only [he] using hh
  have hstep : machine.step e = (cfg 83 (e.head-1) e.tape,false) := by
    conv_lhs => rw [hcfg]
    exact step97_one e.head e.tape hmarker
  refine ⟨1+n+1,cfg 83 (e.head-1) e.tape,by omega,rfl,?_⟩
  exact segAdd machine _ _ _ (1+n) 1
    (segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step42_zero h t h0)) hseg)
    (oneSeg machine _ _ hstep)

/-- The state-261 zero branch reaches state 83 under the two supplied
zeros and a later marker; the initial state-261 write is accounted for. -/
theorem dispatch261_zero_to83 (k : Nat) (h : Int) (t : Int → Bool)
    (h0 : t h=false) (h1 : t (h+1)=false) (h2 : t (h+1+1)=false)
    (hm : t ((h+1+1)+(k : Int))=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧
      silentSegment machine (cfg 261 h t) e n := by
  have hp1 : h+1 ≠ h := by omega
  have hp2 : h+1+1 ≠ h := by omega
  have hp3 : (h+1+1)+(k : Int) ≠ h := by omega
  have h1' : setAt h t (h+1)=false := by simp [setAt,hp1,h1]
  have h2' : setAt h t ((h+1)+1)=false := by simp [setAt,hp2,h2]
  have hm' : setAt h t (((h+1)+1)+(k : Int))=true := by
    change (if (h+1+1)+(k : Int)=h then true else t ((h+1+1)+(k : Int)))=true
    rw [if_neg hp3]
    exact hm
  obtain ⟨n,e,hn,he,hseg⟩ := dispatch42_to83 k (h+1) (setAt h t) h1' h2' hm'
  exact ⟨1+n,e,by omega,he,
    segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step261_zero h t h0)) hseg⟩

end Shared.Beeping.NPcoNP.NativeHalfState10Progress

#print axioms Shared.Beeping.NPcoNP.NativeHalfState10Progress.scan10_marker
#print axioms Shared.Beeping.NPcoNP.NativeHalfState10Progress.dispatch42_to83
#print axioms Shared.Beeping.NPcoNP.NativeHalfState10Progress.dispatch261_zero_to83
