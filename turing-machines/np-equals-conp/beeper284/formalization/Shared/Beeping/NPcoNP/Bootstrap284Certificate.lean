import Shared.Beeping.NPcoNP.Bootstrap284Effects

/-! A finite executable certificate language for silent bootstrap segments.
Acceptance of a trace is proved to imply the exact literal-machine segment.
This file does not claim that a full blank-start certificate has been supplied. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284Certificate

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284Scans

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

inductive Op where
  | single | right (n : Nat) | left (n : Nat) | fill (n : Nat)
  deriving Repr, DecidableEq

def rightOK (n : Nat) (h : Int) (t : Int → Bool) : Bool :=
  (List.range n).all fun i => t (h+2*(i : Int)) && !(t (h+2*(i : Int)+1))

def leftOK (n : Nat) (h : Int) (t : Int → Bool) : Bool :=
  (List.range n).all fun i => t (h-2*(i : Int)) && !(t (h-2*(i : Int)-1))

theorem rightOK_sound {n : Nat} {h : Int} {t : Int → Bool} (ha : rightOK n h t=true) :
    ∀ i<n, t (h+2*(i : Int))=true ∧ t (h+2*(i : Int)+1)=false := by
  intro i hi
  have hb := (List.all_eq_true.mp ha) i (List.mem_range.mpr hi)
  simpa only [Bool.and_eq_true,Bool.not_eq_true'] using hb

theorem leftOK_sound {n : Nat} {h : Int} {t : Int → Bool} (ha : leftOK n h t=true) :
    ∀ i<n, t (h-2*(i : Int))=true ∧ t (h-2*(i : Int)-1)=false := by
  intro i hi
  have hb := (List.all_eq_true.mp ha) i (List.mem_range.mpr hi)
  simpa only [Bool.and_eq_true,Bool.not_eq_true'] using hb

/-- A single certificate action, or failure if its finite guards do not hold.
`single` accepts a literal row only when that row has no beep. -/
def execute (op : Op) (c : Config 284) : Option (Config 284 × Nat) :=
  match op with
  | .single => if (machine.step c).2 then none else some ((machine.step c).1,1)
  | .right n => if 0<n ∧ c.state=4 ∧ rightOK n c.head c.tape then
      some (cfg 4 (c.head+2*(n : Int)) c.tape,2*n) else none
  | .left n => if 0<n ∧ c.state=2 ∧ leftOK n c.head c.tape then
      some (cfg 2 (c.head-2*(n : Int)) (leftEffect n c.tape c.head),2*n) else none
  | .fill n => if 0<n ∧ c.state=0 ∧ leftOK n c.head c.tape then
      some (cfg 0 (c.head-2*(n : Int)) (fillEffect n c.tape c.head),2*n) else none

theorem execute_sound (op : Op) (c e : Config 284) (n : Nat)
    (he : execute op c=some (e,n)) : silentSegment machine c e n := by
  cases op with
  | single =>
    simp only [execute] at he
    split at he
    · contradiction
    · rename_i hb
      have hb' : (machine.step c).2=false := by cases h : (machine.step c).2 <;> simp_all
      cases hs : machine.step c with
      | mk d b =>
        have : b=false := by simpa [hs] using hb'
        subst b
        simp [hs] at he
        obtain ⟨rfl,rfl⟩ := he
        exact oneSeg machine _ _ hs
  | right k =>
    simp only [execute] at he
    split at he
    · rename_i hg
      obtain ⟨_,hq,hok⟩ := hg
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      have hc : c=cfg 4 c.head c.tape := by
        have hh : c=cfg c.state c.head c.tape := by cases c; rfl
        simpa only [hq] using hh
      rw [hc]
      exact scan_right k _ _ (rightOK_sound hok)
    · contradiction
  | left k =>
    simp only [execute] at he
    split at he
    · rename_i hg
      obtain ⟨_,hq,hok⟩ := hg
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      have hc : c=cfg 2 c.head c.tape := by
        have hh : c=cfg c.state c.head c.tape := by cases c; rfl
        simpa only [hq] using hh
      rw [hc]
      exact scan_left k _ _ (leftOK_sound hok)
    · contradiction
  | fill k =>
    simp only [execute] at he
    split at he
    · rename_i hg
      obtain ⟨_,hq,hok⟩ := hg
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      have hc : c=cfg 0 c.head c.tape := by
        have hh : c=cfg c.state c.head c.tape := by cases c; rfl
        simpa only [hq] using hh
      rw [hc]
      exact scan_fill_left k _ _ (leftOK_sound hok)
    · contradiction

/-- Every accepted action represents a positive number of literal steps. -/
theorem execute_positive (op : Op) (c e : Config 284) (n : Nat)
    (he : execute op c=some (e,n)) : 0<n := by
  cases op <;> simp only [execute] at he <;> split at he
  all_goals simp_all <;> omega

/-- Execute a finite sequence and add the exact physical transition costs. -/
def replay : List Op → Config 284 → Option (Config 284 × Nat)
  | [],c => some (c,0)
  | op::ops,c => do
    let (d,n) ← execute op c
    let (e,m) ← replay ops d
    pure (e,n+m)

theorem replay_sound (ops : List Op) (c e : Config 284) (n : Nat)
    (he : replay ops c=some (e,n)) : silentSegment machine c e n := by
  induction ops generalizing c n with
  | nil =>
    simp only [replay,Option.some.injEq,Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]
  | cons op ops ih =>
    cases hs : execute op c with
    | none => simp [replay,hs] at he
    | some d =>
      rcases d with ⟨d,k⟩
      cases ht : replay ops d with
      | none => simp [replay,hs,ht] at he
      | some f =>
        rcases f with ⟨f,l⟩
        simp [replay,hs,ht] at he
        obtain ⟨rfl,rfl⟩ := he
        exact segAdd machine _ _ _ k l (execute_sound op c d k hs) (ih d l ht)

/-- Accepted sequences have at least one physical step per action, so an
unbounded sequence of accepted actions cannot hide in zero-time stuttering. -/
theorem replay_cost_ge_length (ops : List Op) (c e : Config 284) (n : Nat)
    (he : replay ops c=some (e,n)) : ops.length ≤ n := by
  induction ops generalizing c e n with
  | nil => simp
  | cons op ops ih =>
    cases hs : execute op c with
    | none => simp [replay,hs] at he
    | some d =>
      rcases d with ⟨d,k⟩
      cases ht : replay ops d with
      | none => simp [replay,hs,ht] at he
      | some f =>
        rcases f with ⟨f,l⟩
        have hp := execute_positive op c d k hs
        have hl := ih d f l ht
        simp [replay,hs,ht] at he
        obtain ⟨_,rfl⟩ := he
        simp only [List.length_cons]
        omega

end Shared.Beeping.NPcoNP.Bootstrap284Certificate
