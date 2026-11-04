import Shared.PNP.Record285.PythonControlActionMeaning

/-! The typed candidate evaluator's bounded-clock header. All claims are
about the partial source interpreter, not CPython or the physical machine. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlClock
open Shared.Beeping
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip
open Shared.PNP.Record285.PythonControlActionMeaning

def pending (s : Store) : Status := .live ⟨131,s,context⟩
def head (s : Store) : Status := .live ⟨91,s,Shared.PNP.Record285.PythonControlCandidate.frames⟩
def done (s : Store) : Status := .live ⟨131,s,Shared.PNP.Record285.PythonControlCandidate.frames⟩
def prepared (s : Store) : Store := put (put s "steps" (s "steps"-1)) "digit" (s "program")

theorem rows : code[91]?=lines18[1]? ∧ code[92]?=lines18[2]? ∧
    code[93]?=lines18[3]? ∧ seek code 92 12=131 := by decide

theorem head_step (s : Store) : pySystem.step (head s) = pySystem.step (pending s) := by rfl

theorem zero_tick (s : Store) (hz : s "steps"=0) : Silent (pending s) (done s) 1 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,pending,done,context,settle,advance,
      rows,lines18,eval,hz,Shared.PNP.Record285.PythonControlCandidate.frames]
  · intro t ht
    have ht0 : t=0 := by omega
    subst t
    simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,pending,context,settle,
      advance,rows,lines18,eval,hz]

theorem positive_tick (s : Store) (hp : 0 < s "steps") :
    Silent (pending s) (.live ⟨94,prepared s,context⟩) 3 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,pending,context,settle,advance,rows,
      lines18,lines19,eval,simple,op,augOp,put,prepared,show s "steps" ≠ 0 by omega,
      show 1 ≤ s "steps" by omega]
  · intro t ht
    have hc : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hc with rfl|rfl|rfl <;>
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,pending,context,settle,
        advance,rows,lines18,lines19,eval,simple,op,augOp,put,prepared,
        show s "steps" ≠ 0 by omega,show 1 ≤ s "steps" by omega]

end Shared.PNP.Record285.PythonControlClock
