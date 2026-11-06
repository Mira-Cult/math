import Shared.Beeping.NPcoNP.NativeHalfState93Progress
import Shared.Beeping.NPcoNP.NativeHalfState97Progress

/-! A marker strictly left of state 93 survives its rightward dispatch. If
that dispatch takes the state-97 branch, the marker forces the leftward scan
to exit. Every actual state-93 entry supplies such a marker. No global
marker invariant for arbitrary state-97 visits is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState93Marker

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.NativeHalfState97Progress

set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

/-- The state-6 scan does not overwrite a marker to its left. On its
state-97 exit the marker is at or to the left of the resulting head. -/
theorem scan6_preserves_marker (k : Nat) (h p : Int) (t : Int → Bool)
    (hp : p < h) (hm : t p = true)
    (hz : ∀ q ≥ h+(k : Int), t q=false) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ n≤2*k+3 ∧ Dispatch e.state ∧
      e.tape p=true ∧ (e.state=97 → p≤e.head) ∧
      silentSegment machine (cfg 6 h t) e n := by
  induction k generalizing h with
  | zero =>
    have hv : t h=false := hz h (by simp)
    refine ⟨1,cfg 97 (h-1) (put t h true),by omega,by omega,?_,?_,?_,?_⟩
    · simp [Dispatch,cfg]
    · change put t h true p=true
      rw [put_other _ _ _ _ (by omega)]
      exact hm
    · intro _; simp only [cfg]; omega
    · exact oneSeg machine _ _ (step6_zero h t hv)
  | succ k ih =>
    cases h0 : t h with
    | false =>
      refine ⟨1,cfg 97 (h-1) (put t h true),by omega,by omega,?_,?_,?_,?_⟩
      · simp [Dispatch,cfg]
      · change put t h true p=true
        rw [put_other _ _ _ _ (by omega)]
        exact hm
      · intro _; simp only [cfg]; omega
      · exact oneSeg machine _ _ (step6_zero h t h0)
    | true =>
      cases h1 : t (h+1) with
      | true =>
        have ha := oneSeg machine _ _ (step6_one h t h0)
        have hb := oneSeg machine _ _ (step7_one (h+1) t h1)
        cases h2 : t (h+1+1) with
        | false =>
          refine ⟨3,cfg 261 (h+1+1+1) t,by omega,by omega,?_,hm,?_,?_⟩
          · simp [Dispatch,cfg]
          · simp [cfg]
          · have hc := oneSeg machine _ _ (step8_zero (h+1+1) t h2)
            simpa using segAdd machine _ _ _ 2 1 (segAdd machine _ _ _ 1 1 ha hb) hc
        | true =>
          refine ⟨3,cfg 260 (h+1+1+1) t,by omega,by omega,?_,hm,?_,?_⟩
          · simp [Dispatch,cfg]
          · simp [cfg]
          · have hc := oneSeg machine _ _ (step8_one (h+1+1) t h2)
            simpa using segAdd machine _ _ _ 2 1 (segAdd machine _ _ _ 1 1 ha hb) hc
      | false =>
        have hz' : ∀ q ≥ (h+2)+(k : Int), t q=false := by
          intro q hq
          apply hz q
          push_cast at *
          omega
        obtain ⟨n,e,hn,hbound,he,hmark,hpos,hseg⟩ := ih (h+2) (by omega) hz'
        refine ⟨2+n,e,by omega,by omega,he,hmark,hpos,?_⟩
        have ha := oneSeg machine _ _ (step6_one h t h0)
        have hb := oneSeg machine _ _ (step7_zero (h+1) t h1)
        have hab : silentSegment machine (cfg 6 h t) (cfg 6 (h+2) t) 2 := by
          have ht := segAdd machine _ _ _ 1 1 ha hb
          have heq : h+1+1=h+2 := by omega
          simpa [heq] using ht
        exact segAdd machine _ _ _ 2 n hab hseg

/-- State-93 dispatch retains the same left marker, with a usable head
position if state 97 is selected. -/
theorem scan93_preserves_marker (k : Nat) (h p : Int) (t : Int → Bool)
    (hp : p < h) (hm : t p=true)
    (hz : ∀ q ≥ h+(k : Int), t q=false) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ n≤2*k+4 ∧ Dispatch e.state ∧
      e.tape p=true ∧ (e.state=97 → p≤e.head) ∧
      silentSegment machine (cfg 93 h t) e n := by
  cases h0 : t h with
  | true =>
    refine ⟨2,cfg 259 (h+1+1) (put t (h+1) false),by omega,by omega,?_,?_,?_,?_⟩
    · simp [Dispatch,cfg]
    · change put t (h+1) false p=true
      rw [put_other _ _ _ _ (by omega)]
      exact hm
    · simp [cfg]
    · exact segAdd machine _ _ _ 1 1 (oneSeg machine _ _ (step93_one h t h0))
        (oneSeg machine _ _ (step94 (h+1) t))
  | false =>
    have hz' : ∀ q ≥ (h+1)+(k : Int), t q=false := by
      intro q hq
      apply hz q
      omega
    obtain ⟨n,e,hn,hbound,he,hmark,hpos,hseg⟩ :=
      scan6_preserves_marker k (h+1) p t (by omega) hm hz'
    refine ⟨1+n,e,by omega,by omega,he,hmark,hpos,?_⟩
    exact segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step93_zero h t h0)) hseg

/-- For a reachable state-93 visit, a left marker forces a silent segment
past state 97 as well as the rightward scan. The remaining exits are genuine
control states 83, 259, 260 and 261; no claim is made about their continuation. -/
theorem reachable_93_marked_progress (time : Nat)
    (hstate : (machine.system.run time).state=93)
    (p : Int) (hp : p < (machine.system.run time).head)
    (hm : (machine.system.run time).tape p=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧
      (e.state=83 ∨ e.state=259 ∨ e.state=260 ∨ e.state=261) ∧
      e.tape p=true ∧ silentSegment machine (machine.system.run time) e n := by
  let c := machine.system.run time
  obtain ⟨b,hb⟩ := run_has_right_zero time
  let k := (max b c.head-c.head).toNat
  have hk : b ≤ c.head+(k : Int) := by
    have hn : 0 ≤ max b c.head-c.head := by omega
    have he : (k : Int)=max b c.head-c.head := Int.toNat_of_nonneg hn
    omega
  have hz : ∀ q ≥ c.head+(k : Int), c.tape q=false := by
    intro q hq
    exact hb q (le_trans hk hq)
  have hc : c=cfg 93 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hs : c.state=93 := hstate
    simpa only [hs] using he
  obtain ⟨n,d,hn,_,hd,hmark,hpos,hseg⟩ :=
    scan93_preserves_marker k c.head p c.tape hp hm hz
  have hseg' : silentSegment machine c d n := by rw [hc]; exact hseg
  by_cases h97 : d.state=97
  · have hp' : p ≤ d.head := hpos h97
    let j := (d.head-p).toNat
    have hj : d.head-(j : Int)=p := by
      have hn' : 0 ≤ d.head-p := by omega
      have he : (j : Int)=d.head-p := Int.toNat_of_nonneg hn'
      omega
    have hmark' : d.tape (d.head-(j : Int))=true := by rw [hj]; exact hmark
    obtain ⟨m,hmpos,_,hscan⟩ := scan_to_one j d.head d.tape hmark'
    have hd' : d=cfg 97 d.head d.tape := by
      have he : d=cfg d.state d.head d.tape := by cases d; rfl
      simpa only [h97] using he
    refine ⟨n+m,cfg 83 (d.head-(m : Int)) d.tape,by omega,?_,hmark,?_⟩
    · simp [cfg]
    · apply segAdd machine _ _ _ n m hseg'
      rw [hd']
      exact hscan
  · have hother : d.state=259 ∨ d.state=260 ∨ d.state=261 := by
      rcases hd with h | h | h | h
      · contradiction
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact ⟨n,d,hn,Or.inr hother,hmark,hseg'⟩

/-- Every literal transition entering 93 writes a one and moves right. -/
theorem enters93_write_left_one (q : Fin 284) (b : Bool)
    (h : (machine.table.row q b).next=93) :
    (machine.table.row q b).write=true ∧
      (machine.table.row q b).move=.right := by
  have hcheck : ∀ (q : Fin 284) (b : Bool),
      (machine.table.row q b).next=93 →
        (machine.table.row q b).write=true ∧
          (machine.table.row q b).move=.right := by decide
  exact hcheck q b h

/-- The preceding transition supplies the marker on every actual visit. -/
theorem reachable_93_left_one (time : Nat)
    (hstate : (machine.system.run time).state=93) :
    (machine.system.run time).tape ((machine.system.run time).head-1)=true := by
  cases time with
  | zero =>
    have hs : (machine.system.run 0).state.val=0 := machine_starts_zero.1
    have hv := congrArg Fin.val hstate
    rw [hs] at hv
    contradiction
  | succ time =>
    let c := machine.system.run time
    let r := machine.table.row c.state (c.tape c.head)
    have hn : r.next=93 := by
      change ((machine.step c).1).state=93 at hstate
      exact hstate
    obtain ⟨hw,hm⟩ := enters93_write_left_one c.state (c.tape c.head) hn
    change ((machine.step c).1).tape (((machine.step c).1).head-1)=true
    simp [Machine.step,r,hm,hw,Move.apply,Config.write]

/-- Any actual visit to 93 silently reaches 83, 259, 260, or 261 in
positive finite time. This proves progress through the state-97 branch,
without assuming a marker; it does not establish global refinement. -/
theorem reachable_93_progress (time : Nat)
    (hstate : (machine.system.run time).state=93) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧
      (e.state=83 ∨ e.state=259 ∨ e.state=260 ∨ e.state=261) ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,e,hn,he,_,hseg⟩ := reachable_93_marked_progress time hstate
    ((machine.system.run time).head-1) (by omega) (reachable_93_left_one time hstate)
  exact ⟨n,e,hn,he,hseg⟩

end Shared.Beeping.NPcoNP.NativeHalfState93Marker
