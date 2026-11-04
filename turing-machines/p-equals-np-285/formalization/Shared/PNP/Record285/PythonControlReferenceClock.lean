import Shared.PNP.Record285.PythonControlReferenceActionMeaning

/-! The reference clock header consumes one choice bit and prepares the exact
record stream. This is still inside the typed partial interpreter. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceClock
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem Silent)
open Shared.PNP.Record285.PythonControlRelocation (referenceBase)
open Shared.PNP.Record285.PythonControlReferenceAction (outerReference)
open Shared.PNP.Record285.PythonControlRelocationTransfer (referenceEntry)

def pending (s : Store) : Status := .live ⟨82,s,referenceBase⟩
def head (s : Store) : Status := .live ⟨41,s,outerReference⟩
def done (s : Store) : Status := .live ⟨82,s,outerReference⟩
def prepared (s : Store) : Store :=
  put (put (put (put s "steps" (s "steps"-1)) "state" (s "state"+s "choices"%2))
    "choices" (s "choices"/2)) "digit" (s "radix"+s "remaining")
def duration (s : Store) : Nat := 5+s "choices"%2

theorem rows : code[41]?=lines8[1]? ∧ code[42]?=lines8[2]? ∧
    code[43]?=lines8[3]? ∧ code[44]?=lines8[4]? ∧ code[45]?=lines9[0]? ∧
    code[46]?=lines9[1]? ∧ seek code 42 16=82 ∧ jumpFalse code 43 20=45 := by decide

theorem head_step (s : Store) : pySystem.step (head s) = pySystem.step (pending s) := by rfl

theorem zero_tick (s : Store) (hz : s "steps"=0) : Silent (pending s) (done s) 1 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,pending,done,referenceBase,outerReference,
      settle,advance,rows,lines8,eval,hz]
  · intro t ht
    have ht0 : t=0 := by omega
    subst t
    simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,pending,referenceBase,outerReference,
      settle,advance,rows,lines8,eval,hz]

theorem positive_tick (s : Store) (hp : 0 < s "steps") :
    Silent (pending s) (referenceEntry (prepared s)) (duration s) := by
  have hm : s "choices"%2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hz : s "choices"%2=0
  · constructor
    · simp [Silent,pySystem,EventSystem.advance,step,pending,referenceEntry,referenceBase,
        outerReference,settle,advance,rows,lines8,lines9,eval,simple,op,augOp,put,prepared,
        duration,show s "steps" ≠ 0 by omega,show 1 ≤ s "steps" by omega,hz]
      funext key
      by_cases ha : key="steps" <;> by_cases hb : key="state" <;>
        by_cases hc : key="choices" <;> by_cases hd : key="digit" <;>
        simp [put,ha,hb,hc,hd,hz]
    · intro t ht
      have ht5 : t<5 := by simpa [duration,hz] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,pending,referenceBase,
          outerReference,settle,advance,rows,lines8,lines9,eval,simple,op,augOp,put,
          show s "steps" ≠ 0 by omega,show 1 ≤ s "steps" by omega,hz]
  · have ho : s "choices"%2=1 := by omega
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,pending,referenceEntry,referenceBase,
        outerReference,settle,advance,rows,lines8,lines9,eval,simple,op,augOp,put,prepared,
        duration,show s "steps" ≠ 0 by omega,show 1 ≤ s "steps" by omega,ho]
    · intro t ht
      have ht6 : t<6 := by simpa [duration,ho] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,pending,referenceBase,
          outerReference,settle,advance,rows,lines8,lines9,eval,simple,op,augOp,put,
          show s "steps" ≠ 0 by omega,show 1 ≤ s "steps" by omega,ho]

end Shared.PNP.Record285.PythonControlReferenceClock
