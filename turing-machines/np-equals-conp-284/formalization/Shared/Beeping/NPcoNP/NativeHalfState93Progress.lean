import Shared.Beeping.NPcoNP.NativeHalfState28Exit
import Shared.Beeping.NPcoNP.NativeHalfPreparedTo93

/-! Progress after the literal state-93 selector return. A finite right-zero
 tail rules out an infinite state-6/7 scan. This does not prove which dispatch
 exit is taken or establish the full register-to-tape refinement. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState93Progress

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfPreparedTo93

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem row93_zero : machine.table.row 93 false = ⟨false,.right,6,false⟩ := by decide
theorem row93_one : machine.table.row 93 true = ⟨true,.right,94,false⟩ := by decide
theorem row94_zero : machine.table.row 94 false = ⟨false,.right,259,false⟩ := by decide
theorem row94_one : machine.table.row 94 true = ⟨false,.right,259,false⟩ := by decide
theorem row6_one : machine.table.row 6 true = ⟨true,.right,7,false⟩ := by decide
theorem row7_zero : machine.table.row 7 false = ⟨false,.right,6,false⟩ := by decide
theorem row7_one : machine.table.row 7 true = ⟨true,.right,8,false⟩ := by decide
theorem row8_zero : machine.table.row 8 false = ⟨false,.right,261,false⟩ := by decide
theorem row8_one : machine.table.row 8 true = ⟨true,.right,260,false⟩ := by decide

theorem step93_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 93 h t) = (cfg 6 (h+1) t,false) := by
  have hw : (⟨93,h,t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row93_zero,Move.apply,hw]

theorem step93_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 93 h t) = (cfg 94 (h+1) t,false) := by
  have hw : (⟨93,h,t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row93_one,Move.apply,hw]

theorem step94 (h : Int) (t : Int → Bool) :
    machine.step (cfg 94 h t) = (cfg 259 (h+1) (put t h false),false) := by
  change machine.step ⟨94,h,t⟩ = (⟨259,h+1,put t h false⟩,false)
  have hw : (⟨94,h,t⟩ : Config 284).write false = put t h false := rfl
  cases ht : t h <;> simp [Machine.step,ht,row94_zero,row94_one,Move.apply,hw]

theorem step6_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 6 h t) = (cfg 7 (h+1) t,false) := by
  have hw : (⟨6,h,t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row6_one,Move.apply,hw]

theorem step7_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 7 h t) = (cfg 6 (h+1) t,false) := by
  have hw : (⟨7,h,t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row7_zero,Move.apply,hw]

theorem step7_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 7 h t) = (cfg 8 (h+1) t,false) := by
  have hw : (⟨7,h,t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row7_one,Move.apply,hw]

theorem step8_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 8 h t) = (cfg 261 (h+1) t,false) := by
  have hw : (⟨8,h,t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row8_zero,Move.apply,hw]

theorem step8_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 8 h t) = (cfg 260 (h+1) t,false) := by
  have hw : (⟨8,h,t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row8_one,Move.apply,hw]

def Dispatch (q : Fin 284) : Prop := q=97 ∨ q=259 ∨ q=260 ∨ q=261

/-- A right-zero tail forces the 6/7 scan to one of its actual dispatch
states in at most `2*k+3` transitions, without emitting a beep. -/
theorem scan6_dispatch (k : Nat) (h : Int) (t : Int → Bool)
    (hz : ∀ p ≥ h+(k : Int), t p=false) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ n≤2*k+3 ∧ Dispatch e.state ∧
      silentSegment machine (cfg 6 h t) e n := by
  induction k generalizing h with
  | zero =>
    have ht : t h=false := hz h (by simp)
    refine ⟨1,cfg 97 (h-1) (put t h true),by omega,by omega,?_,?_⟩
    · simp [Dispatch,cfg]
    · exact oneSeg machine _ _ (step6_zero h t ht)
  | succ k ih =>
    cases h0 : t h with
    | false =>
      refine ⟨1,cfg 97 (h-1) (put t h true),by omega,by omega,?_,?_⟩
      · simp [Dispatch,cfg]
      · exact oneSeg machine _ _ (step6_zero h t h0)
    | true =>
      cases h1 : t (h+1) with
      | true =>
        have ha := oneSeg machine _ _ (step6_one h t h0)
        have hb := oneSeg machine _ _ (step7_one (h+1) t h1)
        cases h2 : t (h+1+1) with
        | false =>
          refine ⟨3,cfg 261 (h+1+1+1) t,by omega,by omega,?_,?_⟩
          · simp [Dispatch,cfg]
          · have hc := oneSeg machine _ _ (step8_zero (h+1+1) t h2)
            simpa using segAdd machine _ _ _ 2 1 (segAdd machine _ _ _ 1 1 ha hb) hc
        | true =>
          refine ⟨3,cfg 260 (h+1+1+1) t,by omega,by omega,?_,?_⟩
          · simp [Dispatch,cfg]
          · have hc := oneSeg machine _ _ (step8_one (h+1+1) t h2)
            simpa using segAdd machine _ _ _ 2 1 (segAdd machine _ _ _ 1 1 ha hb) hc
      | false =>
        have hz' : ∀ p ≥ (h+2)+(k : Int), t p=false := by
          intro p hp
          apply hz p
          push_cast at *
          omega
        obtain ⟨n,e,hn,hbound,he,hseg⟩ := ih (h+2) hz'
        refine ⟨2+n,e,by omega,by omega,he,?_⟩
        have ha := oneSeg machine _ _ (step6_one h t h0)
        have hb := oneSeg machine _ _ (step7_zero (h+1) t h1)
        have hab : silentSegment machine (cfg 6 h t) (cfg 6 (h+2) t) 2 := by
          have ht := segAdd machine _ _ _ 1 1 ha hb
          have heq : h+1+1=h+2 := by omega
          simpa [heq] using ht
        exact segAdd machine _ _ _ 2 n hab hseg

/-- Every state-93 configuration with a right-zero tail reaches an actual
exit of this selector block after a positive finite silent segment. -/
theorem scan93_dispatch (k : Nat) (h : Int) (t : Int → Bool)
    (hz : ∀ p ≥ h+(k : Int), t p=false) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ n≤2*k+4 ∧ Dispatch e.state ∧
      silentSegment machine (cfg 93 h t) e n := by
  cases h0 : t h with
  | true =>
    refine ⟨2,cfg 259 (h+1+1) (put t (h+1) false),by omega,by omega,?_,?_⟩
    · simp [Dispatch,cfg]
    · exact segAdd machine _ _ _ 1 1 (oneSeg machine _ _ (step93_one h t h0))
        (oneSeg machine _ _ (step94 (h+1) t))
  | false =>
    have hz' : ∀ p ≥ (h+1)+(k : Int), t p=false := by
      intro p hp
      apply hz p
      omega
    obtain ⟨n,e,hn,hbound,he,hseg⟩ := scan6_dispatch k (h+1) t hz'
    refine ⟨1+n,e,by omega,by omega,he,?_⟩
    exact segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step93_zero h t h0)) hseg

/-- Any actual blank-start visit to state 93 leaves the block in positive
finite silent time. This assumes the visit and does not assert correctness
of the subsequent dispatch. -/
theorem reachable_93_to_dispatch (time : Nat) (hstate : (machine.system.run time).state=93) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ Dispatch e.state ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨b,hb⟩ := run_has_right_zero time
  let h := (machine.system.run time).head
  let k := (max b h-h).toNat
  have hk : b ≤ h+(k : Int) := by
    have hn : 0 ≤ max b h-h := by omega
    have he : (k : Int)=max b h-h := Int.toNat_of_nonneg hn
    omega
  have hz : ∀ p ≥ h+(k : Int), (machine.system.run time).tape p=false := by
    intro p hp
    exact hb p (le_trans hk hp)
  obtain ⟨n,e,hn,_,he,hseg⟩ := scan93_dispatch k h (machine.system.run time).tape hz
  have hcfg : machine.system.run time = cfg 93 h (machine.system.run time).tape := by
    cases hc : machine.system.run time with
    | mk state head tape =>
      simp only [hc,cfg] at hstate ⊢
      simp only [h,hc,cfg] at *
      cases hstate
      rfl
  exact ⟨n,e,hn,he,by rw [hcfg]; exact hseg⟩

/-- Composes the previous prepared exceptional path with actual-run
finite-support progress beyond the state-93 boundary. -/
theorem reachable_exceptional_to_dispatch (time : Nat) (back : Int → Bool) (gap : Int)
    (left values : List Nat)
    (hconfig : machine.system.run time =
      cfg 30 (gap+1+((NativeHalfState1Layout.leftSuffix left).length : Int))
        (NativeHalfCycleTape.prior (UnarySuffixShift.before back gap (NativeHalfState1Layout.leftSuffix left))
          (gap+1+((NativeHalfState1Layout.leftSuffix left).length : Int)) (false :: UnaryBank.encode values))) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ Dispatch e.state ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,c,hn,hstate,hseg⟩ := reachable_exceptional_to_93 time back gap left values hconfig
  have hrun : machine.system.run (time+n)=c := by
    rw [EventSystem.run_add,← PASoundness.ScalarWordRefinement.advance_ofBeep]
    exact hseg.1
  have hnext : (machine.system.run (time+n)).state=93 := by rw [hrun]; exact hstate
  obtain ⟨m,e,hm,he,hmore⟩ := reachable_93_to_dispatch (time+n) hnext
  refine ⟨n+m,e,by omega,he,?_⟩
  apply segAdd machine _ _ _ n m hseg
  rw [← hrun]
  exact hmore

/-- The non-97 dispatch rows all take one silent transition to the next
actual control boundary. State 97 is kept separate because its leftward
scan requires a marker invariant, not merely finite tape support. -/
def Exit (q : Fin 284) : Prop := q=97 ∨ q=99 ∨ q=166 ∨ q=42 ∨ q=15 ∨ q=16

theorem dispatch_row (q : Fin 284) (hq : q=259 ∨ q=260 ∨ q=261) (b : Bool) :
    (machine.table.row q b).beep=false ∧ Exit (machine.table.row q b).next := by
  rcases hq with hq | hq | hq <;> subst q <;> cases b <;> unfold Exit <;> decide +kernel

theorem dispatch_to_exit (c : Config 284) (hc : Dispatch c.state) :
    ∃ (n : Nat) (e : Config 284), n≤1 ∧ Exit e.state ∧ silentSegment machine c e n := by
  by_cases h97 : c.state=97
  · refine ⟨0,c,by omega,?_,?_⟩
    · simp [Exit,h97]
    · simp [silentSegment,W,PASoundness.WordEventSystem.advance,PASoundness.WordEventSystem.wordFrom]
  · have hother : c.state=259 ∨ c.state=260 ∨ c.state=261 := by
      rcases hc with h | h | h | h
      · contradiction
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    obtain ⟨hbeep,hexit⟩ := dispatch_row c.state hother (c.tape c.head)
    let e := (machine.step c).1
    have hstep : machine.step c=(e,false) := by
      dsimp [e]
      have hb : (machine.step c).2=false := hbeep
      cases he : machine.step c with
      | mk config beep => simp_all
    refine ⟨1,e,by omega,?_,oneSeg machine _ _ hstep⟩
    change Exit (machine.table.row c.state (c.tape c.head)).next
    exact hexit

/-- Every actual state-93 visit reaches a next control boundary silently;
only the state-97 branch retains a future marker obligation. -/
theorem reachable_93_to_exit (time : Nat) (hstate : (machine.system.run time).state=93) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ Exit e.state ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,c,hn,hdispatch,hseg⟩ := reachable_93_to_dispatch time hstate
  obtain ⟨m,e,_,he,hmore⟩ := dispatch_to_exit c hdispatch
  exact ⟨n+m,e,by omega,he,segAdd machine _ _ _ n m hseg hmore⟩

/-- The prepared exceptional boundary also reaches one of those same
physical exits, provided that boundary occurs on the blank-start run. -/
theorem reachable_exceptional_to_exit (time : Nat) (back : Int → Bool) (gap : Int)
    (left values : List Nat)
    (hconfig : machine.system.run time =
      cfg 30 (gap+1+((NativeHalfState1Layout.leftSuffix left).length : Int))
        (NativeHalfCycleTape.prior (UnarySuffixShift.before back gap (NativeHalfState1Layout.leftSuffix left))
          (gap+1+((NativeHalfState1Layout.leftSuffix left).length : Int)) (false :: UnaryBank.encode values))) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ Exit e.state ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,c,hn,hdispatch,hseg⟩ := reachable_exceptional_to_dispatch time back gap left values hconfig
  obtain ⟨m,e,_,he,hmore⟩ := dispatch_to_exit c hdispatch
  exact ⟨n+m,e,by omega,he,segAdd machine _ _ _ n m hseg hmore⟩

end Shared.Beeping.NPcoNP.NativeHalfState93Progress
