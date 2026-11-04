import Shared.PNP.Record285.PythonControlReferenceEvaluator

/-! The reference branch-loop header and its complete-store initialization. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceBranch
open Shared.Beeping
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem Silent)
open Shared.PNP.Record285.PythonControlReferenceAction (outerReference)
open Shared.PNP.Record285.PythonControlReferenceClock

def outer : List Loop := [⟨31,140⟩,⟨28,146⟩]
def pending (s : Store) : Status := .live ⟨82,s,outerReference⟩
def head (s : Store) : Status := .live ⟨34,s,outer⟩
def done (s : Store) : Status := .live ⟨82,s,outer⟩
def prepared (s : Store) : Store :=
  put (put (put (put (put (put s "branches" (s "branches"-1)) "left" 0)
    "right" 0) "state" 0) "steps" (s "n")) "choices" (s "branches"-1)

theorem rows : code[34]?=lines6[4]? ∧ code[35]?=lines7[0]? ∧
    code[36]?=lines7[1]? ∧ code[37]?=lines7[2]? ∧ code[38]?=lines7[3]? ∧
    code[39]?=lines7[4]? ∧ code[40]?=lines8[0]? ∧ seek code 35 12=82 := by decide

theorem head_step (s : Store) : pySystem.step (head s) = pySystem.step (pending s) := by rfl

theorem zero_branch (s : Store) (hz : s "branches"=0) : Silent (pending s) (done s) 1 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,pending,done,outerReference,outer,
      settle,advance,rows,lines6,eval,hz]
  · intro t ht
    have : t=0 := by omega
    subst t
    simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,pending,outerReference,outer,
      settle,advance,rows,lines6,eval,hz]

theorem positive_branch (s : Store) (hp : 0 < s "branches") :
    Silent (pending s) (PythonControlReferenceClock.head (prepared s)) 7 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,pending,PythonControlReferenceClock.head,
      outerReference,outer,settle,advance,rows,lines6,lines7,lines8,eval,simple,op,augOp,put,
      prepared,show s "branches" ≠ 0 by omega,show 1 ≤ s "branches" by omega]
  · intro t ht
    have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,pending,outerReference,outer,
        settle,advance,rows,lines6,lines7,lines8,eval,simple,op,augOp,put,
        show s "branches" ≠ 0 by omega,show 1 ≤ s "branches" by omega]

end Shared.PNP.Record285.PythonControlReferenceBranch
