import Shared.PNP.Record285.InitializationSweeps
import Shared.PNP.Record285.BootstrapChecker

/-! Compact, checked literal-machine run segments. The checker accepts only
finite silent steps and the proved arbitrary-length run and pair sweeps. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.InitializationChecker
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.BootstrapChecker (silent_compose)
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.InitializationSweeps

theorem physical_step_eq (c : Config 285) :
    PhysicalNumeric.step Record285.machine c = PhysicalNumeric.step NumericTables.target c := by
  simp only [PhysicalNumeric.step, ArtifactEndpoint.literal_rows]

theorem numeric_silent (time : Nat) (c : Config 285) :
    silent Record285.machine time c = silent NumericTables.target time c := by
  induction time generalizing c with
  | zero => change some c = some c; rfl
  | succ time ih =>
    simp only [silent, physical_step_eq, ih]

inductive Command where
  | single
  | leftPair (kind : LeftPair) (k : Nat)
  | rightPair (kind : RightPair) (k : Nat)
  | leftRun (kind : LeftRun) (k : Nat)
  | rightRun (kind : RightRun) (k : Nat)
  deriving DecidableEq

def pairLast (side k : Nat) : Bool := (side / (2*4^k)).testBit 0
def pairTail (side k : Nat) : Nat := side / 4^(k+1)
def pairFast (b : Bool) (k : Nat) (last : Bool) (tail : Nat) : Nat :=
  (bitVal (!b)+2*bitVal b)*rep4 k + 4^k*(bitVal (!b)+2*bitVal last+4*tail)
def pairPush (k digit value : Nat) : Nat := 4^k*value + digit*rep4 k

def runLast (side k : Nat) : Bool := (side / 2^k).testBit 0
def runTail (side k : Nat) : Nat := side / 2^(k+1)
def runFast (b : Bool) (k : Nat) (last : Bool) (tail : Nat) : Nat :=
  bitVal b*(2^k-1) + 2^k*(bitVal last+2*tail)
def runPush (k : Nat) (b : Bool) (value : Nat) : Nat :=
  2^k*value + bitVal b*(2^k-1)

def execute (cmd : Command) (c : Config 285) : Option (Nat × Config 285) :=
  match cmd with
  | .single =>
    let next := PhysicalNumeric.step NumericTables.target c
    if next.2 then none else some (1,next.1)
  | .leftPair kind k =>
    let s := leftSpec kind
    let last := pairLast c.left k
    let rest := pairTail c.left k
    if c.state = s.q ∧ c.read = s.read ∧ c.left = pairFast s.read k last rest then
      some (2*(k+1),⟨s.q,c.head-2*(k+1),rest,last,pairPush (k+1) (InitializationSweeps.digit s) c.right⟩)
    else none
  | .rightPair kind k =>
    let s := rightSpec kind
    let last := pairLast c.right k
    let rest := pairTail c.right k
    if c.state = s.q ∧ c.read = s.read ∧ c.right = pairFast s.read k last rest then
      some (2*(k+1),⟨s.q,c.head+2*(k+1),pairPush (k+1) (InitializationSweeps.digit s) c.left,last,rest⟩)
    else none
  | .leftRun kind k =>
    let s := leftRunSpec kind
    let last := runLast c.left k
    let rest := runTail c.left k
    if c.state = s.q ∧ c.read = s.read ∧ c.left = runFast s.read k last rest then
      some (k+1,⟨s.q,c.head-(k+1),rest,last,runPush (k+1) s.write c.right⟩)
    else none
  | .rightRun kind k =>
    let s := rightRunSpec kind
    let last := runLast c.right k
    let rest := runTail c.right k
    if c.state = s.q ∧ c.read = s.read ∧ c.right = runFast s.read k last rest then
      some (k+1,⟨s.q,c.head+(k+1),runPush (k+1) s.write c.left,last,rest⟩)
    else none

/-- An accepted command is exactly the recorded number of literal physical
transitions, and none is marked. -/
theorem execute_sound (cmd : Command) (c d : Config 285) (time : Nat)
    (h : execute cmd c = some (time,d)) : silent Record285.machine time c = some d := by
  cases cmd with
  | single =>
    simp only [execute] at h
    cases hs : PhysicalNumeric.step NumericTables.target c with
    | mk next flag =>
      cases flag with
      | true => simp [hs] at h
      | false =>
        simp [hs] at h
        rcases h with ⟨rfl,rfl⟩
        simp only [silent, physical_step_eq, hs, Bool.false_eq_true, if_false]
  | leftPair kind k =>
    simp only [execute] at h
    split at h
    next hc =>
      rcases c with ⟨q,head,left,read,right⟩
      dsimp only at hc
      rcases hc with ⟨hq,hr,hl⟩
      subst q; subst read
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := left_sweep kind k (pairLast left k) (pairTail left k) right head
      dsimp only at hs
      rw [pairPattern_closed] at hs
      change silent _ _ ⟨_,_,pairFast _ _ _ _,_,_⟩ = _ at hs
      rw [← hl] at hs
      simpa only [push_closed, pairPush] using hs
    next _ => contradiction
  | rightPair kind k =>
    simp only [execute] at h
    split at h
    next hc =>
      rcases c with ⟨q,head,left,read,right⟩
      dsimp only at hc
      rcases hc with ⟨hq,hr,hl⟩
      subst q; subst read
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := right_sweep kind k (pairLast right k) (pairTail right k) left head
      dsimp only at hs
      rw [pairPattern_closed] at hs
      change silent _ _ ⟨_,_,_,_,pairFast _ _ _ _⟩ = _ at hs
      rw [← hl] at hs
      simpa only [push_closed, pairPush] using hs
    next _ => contradiction
  | leftRun kind k =>
    simp only [execute] at h
    split at h
    next hc =>
      rcases c with ⟨q,head,left,read,right⟩
      dsimp only at hc
      rcases hc with ⟨hq,hr,hl⟩
      subst q; subst read
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := left_run kind k (runLast left k) (runTail left k) right head
      dsimp only at hs
      rw [runPattern_closed] at hs
      change silent _ _ ⟨_,_,runFast _ _ _ _,_,_⟩ = _ at hs
      rw [← hl] at hs
      simpa only [pushBit_closed, runPush] using hs
    next _ => contradiction
  | rightRun kind k =>
    simp only [execute] at h
    split at h
    next hc =>
      rcases c with ⟨q,head,left,read,right⟩
      dsimp only at hc
      rcases hc with ⟨hq,hr,hl⟩
      subst q; subst read
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := right_run kind k (runLast right k) (runTail right k) left head
      dsimp only at hs
      rw [runPattern_closed] at hs
      change silent _ _ ⟨_,_,_,_,runFast _ _ _ _⟩ = _ at hs
      rw [← hl] at hs
      simpa only [pushBit_closed, runPush] using hs
    next _ => contradiction

def verify : List Command → Config 285 → Option (Nat × Config 285)
  | [], c => some (0,c)
  | cmd::rest, c => do
    let (time,next) ← execute cmd c
    let (later,final) ← verify rest next
    pure (time+later,final)

theorem verify_sound (cmds : List Command) (c d : Config 285) (time : Nat)
    (h : verify cmds c = some (time,d)) : silent Record285.machine time c = some d := by
  induction cmds generalizing c d time with
  | nil =>
    simp only [verify, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩; rfl
  | cons cmd rest ih =>
    simp only [verify] at h
    cases hfirst : execute cmd c with
    | none => simp [hfirst] at h
    | some first =>
      rcases first with ⟨duration,next⟩
      cases hrest : verify rest next with
      | none => simp [hfirst,hrest] at h
      | some last =>
        rcases last with ⟨later,final⟩
        simp only [hfirst,hrest,bind,Option.bind] at h
        rcases h with ⟨rfl,rfl⟩
        rw [silent_add, execute_sound _ _ _ _ hfirst]
        exact ih next d later hrest

end Shared.PNP.Record285.InitializationChecker
