import Shared.Beeping.NPcoNP.NativeHalfSweep

/-! Exact silent scan segments for the actual 284-state machine's paid
blank-tape bootstrap. These are arbitrary-length tape lemmas, not a proof of
the full bootstrap or its eventual exit. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284Scans

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem row4_one : machine.table.row 4 true = ⟨true,.right,5,false⟩ := by decide
theorem row5_zero : machine.table.row 5 false = ⟨false,.right,4,false⟩ := by decide
theorem row2_one : machine.table.row 2 true = ⟨false,.left,4,false⟩ := by decide
theorem row4_zero : machine.table.row 4 false = ⟨true,.left,2,false⟩ := by decide

theorem step4_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 4 h t)=(cfg 5 (h+1) t,false) := by
  have hw : (⟨4,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row4_one,Move.apply,hw]

theorem step5_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 5 h t)=(cfg 4 (h+1) t,false) := by
  have hw : (⟨5,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row5_zero,Move.apply,hw]

theorem step2_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 2 h t)=(cfg 4 (h-1) (put t h false),false) := by
  have hw : (⟨2,h,t⟩ : Config 284).write false=put t h false := rfl
  simp [cfg,Machine.step,ht,row2_one,Move.apply,hw]

theorem step4_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 4 h t)=(cfg 2 (h-1) (put t h true),false) := by
  have hw : (⟨4,h,t⟩ : Config 284).write true=put t h true := rfl
  simp [cfg,Machine.step,ht,row4_zero,Move.apply,hw]

theorem row0_one : machine.table.row 0 true = ⟨true,.left,3,false⟩ := by decide
theorem row3_zero : machine.table.row 3 false = ⟨true,.left,0,false⟩ := by decide

theorem step0_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 0 h t)=(cfg 3 (h-1) t,false) := by
  have hw : (⟨0,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row0_one,Move.apply,hw]

theorem step3_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 3 h t)=(cfg 0 (h-1) (put t h true),false) := by
  have hw : (⟨3,h,t⟩ : Config 284).write true=put t h true := rfl
  simp [cfg,Machine.step,ht,row3_zero,Move.apply,hw]

/-- The state-4/5 scan crosses `n` alternating one-zero pairs, preserving
the entire tape and emitting no events. Its exact cost is `2*n`. -/
theorem scan_right (n : Nat) (h : Int) (t : Int → Bool)
    (hs : ∀ i < n, t (h+2*(i : Int))=true ∧ t (h+2*(i : Int)+1)=false) :
    silentSegment machine (cfg 4 h t) (cfg 4 (h+2*(n : Int)) t) (2*n) := by
  induction n generalizing h with
  | zero => simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]
  | succ n ih =>
    have h0 : t h=true := by simpa using (hs 0 (by omega)).1
    have h1 : t (h+1)=false := by simpa using (hs 0 (by omega)).2
    have hs' : ∀ i < n, t ((h+2)+2*(i : Int))=true ∧
        t ((h+2)+2*(i : Int)+1)=false := by
      intro i hi
      have hh := hs (i+1) (by omega)
      have he : (h+2)+2*(i : Int)=h+2*((i+1 : Nat) : Int) := by push_cast; omega
      rw [he]
      exact hh
    have ha := oneSeg machine _ _ (step4_one h t h0)
    have hb := oneSeg machine _ _ (step5_zero (h+1) t h1)
    have hab : silentSegment machine (cfg 4 h t) (cfg 4 (h+2) t) 2 := by
      have he : h+1+1=h+2 := by omega
      simpa [he] using segAdd machine _ _ _ 1 1 ha hb
    have hr := segAdd machine _ _ _ 2 (2*n) hab (ih (h+2) hs')
    have he : (h+2)+2*(n : Int)=h+2*((n+1 : Nat) : Int) := by push_cast; omega
    have hn : 2+2*n=2*(n+1) := by omega
    simpa only [he,hn,Nat.succ_eq_add_one] using hr

/-- The tape effect of the backward bootstrap rewrite, written as finite
updates; cells outside the traversed pairs are untouched. -/
def leftEffect : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0,t,_ => t
  | n+1,t,h => leftEffect n (put (put t h false) (h-1) true) (h-2)

/-- The finite rewrite does not touch cells outside its traversed interval. -/
theorem leftEffect_outside (n : Nat) (h p : Int) (t : Int → Bool)
    (hp : h < p ∨ p ≤ h-2*(n : Int)) : leftEffect n t h p=t p := by
  induction n generalizing h t with
  | zero => rfl
  | succ n ih =>
    have hout : (h-2) < p ∨ p ≤ (h-2)-2*(n : Int) := by
      push_cast at hp
      omega
    rw [leftEffect, ih (h-2) (put (put t h false) (h-1) true) hout]
    rw [put_other _ _ _ _ (by push_cast at hp; omega),
      put_other _ _ _ _ (by push_cast at hp; omega)]

/-- State 2/4 turns each leftward one-zero pair into zero-one, in exactly
two silent transitions per pair. -/
theorem scan_left (n : Nat) (h : Int) (t : Int → Bool)
    (hs : ∀ i < n, t (h-2*(i : Int))=true ∧ t (h-2*(i : Int)-1)=false) :
    silentSegment machine (cfg 2 h t) (cfg 2 (h-2*(n : Int)) (leftEffect n t h)) (2*n) := by
  induction n generalizing h t with
  | zero => simp [leftEffect,silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]
  | succ n ih =>
    have h0 : t h=true := by simpa using (hs 0 (by omega)).1
    have h1 : t (h-1)=false := by simpa using (hs 0 (by omega)).2
    let t' := put (put t h false) (h-1) true
    have h1' : put t h false (h-1)=false := by rw [put_other _ _ _ _ (by omega)]; exact h1
    have hs' : ∀ i < n, t' ((h-2)-2*(i : Int))=true ∧
        t' ((h-2)-2*(i : Int)-1)=false := by
      intro i hi
      have hh := hs (i+1) (by omega)
      have ha : t' ((h-2)-2*(i : Int))=t ((h-2)-2*(i : Int)) := by
        dsimp [t']; rw [put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
      have hb : t' ((h-2)-2*(i : Int)-1)=t ((h-2)-2*(i : Int)-1) := by
        dsimp [t']; rw [put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
      rw [ha,hb]
      have he : (h-2)-2*(i : Int)=h-2*((i+1 : Nat) : Int) := by push_cast; omega
      rw [he]
      exact hh
    have ha := oneSeg machine _ _ (step2_one h t h0)
    have hb := oneSeg machine _ _ (step4_zero (h-1) (put t h false) h1')
    have hab : silentSegment machine (cfg 2 h t) (cfg 2 (h-2) t') 2 := by
      have he : h-1-1=h-2 := by omega
      simpa [he,t'] using segAdd machine _ _ _ 1 1 ha hb
    have hr := segAdd machine _ _ _ 2 (2*n) hab (ih (h-2) t' hs')
    have he : (h-2)-2*(n : Int)=h-2*((n+1 : Nat) : Int) := by push_cast; omega
    have hn : 2+2*n=2*(n+1) := by omega
    simpa only [leftEffect,he,hn,Nat.succ_eq_add_one,t'] using hr

/-- Tape update performed by repeated state-0/3 leftward filling. -/
def fillEffect : Nat → (Int → Bool) → Int → (Int → Bool)
  | 0,t,_ => t
  | n+1,t,h => fillEffect n (put t (h-1) true) (h-2)

/-- Filling leaves every cell outside the traversed interval untouched. -/
theorem fillEffect_outside (n : Nat) (h p : Int) (t : Int → Bool)
    (hp : h < p ∨ p ≤ h-2*(n : Int)) : fillEffect n t h p=t p := by
  induction n generalizing h t with
  | zero => rfl
  | succ n ih =>
    have hout : (h-2) < p ∨ p ≤ (h-2)-2*(n : Int) := by
      push_cast at hp
      omega
    rw [fillEffect, ih (h-2) (put t (h-1) true) hout]
    rw [put_other _ _ _ _ (by push_cast at hp; omega)]

/-- State 0/3 fills the zero of each leftward one-zero pair. -/
theorem scan_fill_left (n : Nat) (h : Int) (t : Int → Bool)
    (hs : ∀ i < n, t (h-2*(i : Int))=true ∧ t (h-2*(i : Int)-1)=false) :
    silentSegment machine (cfg 0 h t) (cfg 0 (h-2*(n : Int)) (fillEffect n t h)) (2*n) := by
  induction n generalizing h t with
  | zero => simp [fillEffect,silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]
  | succ n ih =>
    have h0 : t h=true := by simpa using (hs 0 (by omega)).1
    have h1 : t (h-1)=false := by simpa using (hs 0 (by omega)).2
    let t' := put t (h-1) true
    have hs' : ∀ i < n, t' ((h-2)-2*(i : Int))=true ∧
        t' ((h-2)-2*(i : Int)-1)=false := by
      intro i hi
      have hh := hs (i+1) (by omega)
      have ha : t' ((h-2)-2*(i : Int))=t ((h-2)-2*(i : Int)) := by
        dsimp [t']; rw [put_other _ _ _ _ (by omega)]
      have hb : t' ((h-2)-2*(i : Int)-1)=t ((h-2)-2*(i : Int)-1) := by
        dsimp [t']; rw [put_other _ _ _ _ (by omega)]
      rw [ha,hb]
      have he : (h-2)-2*(i : Int)=h-2*((i+1 : Nat) : Int) := by push_cast; omega
      rw [he]
      exact hh
    have ha := oneSeg machine _ _ (step0_one h t h0)
    have hb := oneSeg machine _ _ (step3_zero (h-1) t h1)
    have hab : silentSegment machine (cfg 0 h t) (cfg 0 (h-2) t') 2 := by
      have he : h-1-1=h-2 := by omega
      simpa [he,t'] using segAdd machine _ _ _ 1 1 ha hb
    have hr := segAdd machine _ _ _ 2 (2*n) hab (ih (h-2) t' hs')
    have he : (h-2)-2*(n : Int)=h-2*((n+1 : Nat) : Int) := by push_cast; omega
    have hn : 2+2*n=2*(n+1) := by omega
    simpa only [fillEffect,he,hn,Nat.succ_eq_add_one,t'] using hr

end Shared.Beeping.NPcoNP.Bootstrap284Scans
