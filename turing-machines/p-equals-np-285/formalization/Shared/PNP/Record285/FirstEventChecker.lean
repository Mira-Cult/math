import Shared.PNP.Record285.InitializationChecker

/-! An additional verified sweep for the first post-initialization event.
The wrapped initialization commands retain their existing exact soundness. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.FirstEventChecker
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.InitializationChecker

def q36 : Fin 285 := ⟨36,by decide⟩

theorem row36 : Record285.machine.table.row q36 true = ⟨true,.right,q36,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]
  decide

inductive Command where
  | old (cmd : InitializationChecker.Command)
  | scan36 (k : Nat)
  deriving DecidableEq

def execute (cmd : Command) (c : Config 285) : Option (Nat × Config 285) :=
  match cmd with
  | .old cmd => InitializationChecker.execute cmd c
  | .scan36 k =>
    let last := runLast c.right k
    let rest := runTail c.right k
    if c.state = q36 ∧ c.read = true ∧ c.right = runFast true k last rest then
      some (k+1, ⟨q36,c.head+(k+1),runPush (k+1) true c.left,last,rest⟩)
    else none

theorem execute_sound (cmd : Command) (c d : Config 285) (time : Nat)
    (h : execute cmd c = some (time,d)) : silent Record285.machine time c = some d := by
  cases cmd with
  | old cmd => exact InitializationChecker.execute_sound cmd c d time h
  | scan36 k =>
    simp only [execute] at h
    split at h
    next hc =>
      rcases c with ⟨q,head,left,read,right⟩
      dsimp only at hc
      rcases hc with ⟨hq,hr,hl⟩
      subst q; subst read
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hs := run_sweep_right Record285.machine q36 true true row36 k
        (runLast right k) (runTail right k) left head
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

end Shared.PNP.Record285.FirstEventChecker
