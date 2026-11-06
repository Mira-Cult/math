import Shared.Beeping.NPcoNP.Bootstrap284Checkpoint

/-! A checked finite-window replay. The bounds are verified for each writing
action and then proved to preserve the full unbounded tape outside the window. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284WindowReplay
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284Certificate
open Shared.Beeping.NPcoNP.Bootstrap284FastEffects
open Shared.Beeping.NPcoNP.Bootstrap284FastReplay
open Shared.Beeping.NPcoNP.Bootstrap284Checkpoint

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- All cells a writing action can touch lie in the proposed window. -/
def safe (lo : Int) (width : Nat) (op : Op) (c : Config 284) : Bool :=
  match op with
  | .single => decide (lo≤c.head ∧ c.head<lo+(width : Int))
  | .right _ => true
  | .left n | .fill n =>
      decide (lo≤c.head-2*(n : Int)+1 ∧ c.head<lo+(width : Int))

theorem execute_preserves (lo : Int) (width : Nat) (op : Op) (c e : Config 284) (n : Nat)
    (hwindow : InWindow lo width c.tape) (hsafe : safe lo width op c=true)
    (he : executeFast op c=some (e,n)) : InWindow lo width e.tape := by
  cases op with
  | single =>
    have hh : lo≤c.head ∧ c.head<lo+(width : Int) := by simpa [safe] using hsafe
    simp only [executeFast] at he
    split at he
    · contradiction
    · simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,_⟩ := he
      intro p hp
      have hne : p≠c.head := by omega
      change ((machine.step c).1).tape p=false
      simp [Machine.step,Config.write,hne,hwindow p hp]
  | right k =>
    simp only [executeFast] at he
    split at he
    · simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,_⟩ := he
      exact hwindow
    · contradiction
  | left k =>
    have hh : lo≤c.head-2*(k : Int)+1 ∧ c.head<lo+(width : Int) := by simpa [safe] using hsafe
    simp only [executeFast] at he
    split at he
    · simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,_⟩ := he
      intro p hp
      change fastLeft k c.tape c.head p=false
      have hn : ¬ (c.head-2*(k : Int)<p ∧ p≤c.head) := by omega
      simp only [fastLeft,if_neg hn]
      exact hwindow p hp
    · contradiction
  | fill k =>
    have hh : lo≤c.head-2*(k : Int)+1 ∧ c.head<lo+(width : Int) := by simpa [safe] using hsafe
    simp only [executeFast] at he
    split at he
    · simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,_⟩ := he
      intro p hp
      change fastFill k c.tape c.head p=false
      have hn : ¬ (c.head-2*(k : Int)<p ∧ p≤c.head ∧ (c.head-p)%2=1) := by omega
      simp only [fastFill,if_neg hn]
      exact hwindow p hp
    · contradiction

/-- Reject an action if it could write beyond the window. -/
def executeWindow (lo : Int) (width : Nat) (op : Op) (c : Config 284) : Option (Config 284 × Nat) :=
  if safe lo width op c then executeFast op c else none

def replayWindow (lo : Int) (width : Nat) : List Op → Config 284 → Option (Config 284 × Nat)
  | [],c => some (c,0)
  | op::ops,c => do
    let (d,n) ← executeWindow lo width op c
    let (e,m) ← replayWindow lo width ops d
    pure (e,n+m)

/-- Every accepted finite-window trace is a real silent segment and keeps
its output tape blank outside the window. -/
theorem replayWindow_sound (lo : Int) (width : Nat) (ops : List Op)
    (c e : Config 284) (n : Nat) (hwindow : InWindow lo width c.tape)
    (he : replayWindow lo width ops c=some (e,n)) :
    silentSegment machine c e n ∧ InWindow lo width e.tape := by
  induction ops generalizing c n with
  | nil =>
    simp only [replayWindow,Option.some.injEq,Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    exact ⟨by simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom],hwindow⟩
  | cons op ops ih =>
    cases hs : executeWindow lo width op c with
    | none => simp [replayWindow,hs] at he
    | some d =>
      rcases d with ⟨d,k⟩
      have hsafe : safe lo width op c=true := by
        by_cases hv : safe lo width op c=true
        · exact hv
        · have : safe lo width op c=false := by cases h : safe lo width op c <;> simp_all
          simp [executeWindow,this] at hs
      have hfast : executeFast op c=some (d,k) := by simpa [executeWindow,hsafe] using hs
      have hd := execute_preserves lo width op c d k hwindow hsafe hfast
      cases ht : replayWindow lo width ops d with
      | none => simp [replayWindow,hs,ht] at he
      | some f =>
        rcases f with ⟨f,l⟩
        simp [replayWindow,hs,ht] at he
        obtain ⟨rfl,rfl⟩ := he
        obtain ⟨hsegment,hout⟩ := ih d l hd ht
        have hone : silentSegment machine c d k := by
          exact replayFast_sound [op] c d k (by simp [replayFast,hfast])
        exact ⟨segAdd machine _ _ _ k l hone hsegment,hout⟩
end Shared.Beeping.NPcoNP.Bootstrap284WindowReplay
