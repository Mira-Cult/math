import Shared.PNP.Record285.PythonControl
import Shared.PNP.Record285.PythonCandidateSetup
import Shared.Beeping.Refinement

/-! Execute the actual typed candidate-setup lines in the partial control-flow
model. This is a finite segment, not yet an unbounded source refinement. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlCandidate
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonCandidateSetup
open Shared.PNP.Record285.PythonControl

def frames : List Loop := [⟨31,140⟩,⟨28,146⟩]

def system (s : Store) : EventSystem Status :=
  ⟨.live ⟨82,s,frames⟩,step code⟩

def last (s : Store) : Status := .live ⟨91,output s,frames⟩

theorem rows :
    code[82]? = lines16[2]? ∧ code[83]? = lines16[3]? ∧ code[84]? = lines16[4]? ∧
    code[85]? = lines17[0]? ∧ code[86]? = lines17[1]? ∧ code[87]? = lines17[2]? ∧
    code[88]? = lines17[3]? ∧ code[89]? = lines17[4]? ∧ code[90]? = lines18[0]? := by decide

theorem guard_jump : jumpFalse code 88 12 = 90 := by decide

/-- The supplied enclosing loop frames match the actual typed source's
outer and inner loop boundaries. -/
theorem frame_exits : seek code 29 4 = 146 ∧ seek code 32 8 = 140 := by decide

/-- The exact instruction count depends on the scanned input bit. -/
def duration (s : Store) : Nat :=
  if (frame (s "radix") (s "remaining"))%2=0 then 8 else 9

/-- Starting at the real candidate block with the enclosing loop frames,
execution reaches the evaluator entry with the exact full store. -/
theorem segment (s : Store) (hradix : 0 < s "radix") :
    (system s).advance (.live ⟨82,s,frames⟩) (duration s) = last s := by
  have hpos : 1 ≤ 2*(s "remaining"*s "radix") + s "radix" := by omega
  have hmod : (2*(s "remaining"*s "radix") + s "radix" - 1)%2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hz : (2*(s "remaining"*s "radix") + s "radix" - 1)%2 = 0
  · simp [duration,Shared.PNP.Record285.Source.frame,hz,EventSystem.advance,system,
      step,frames,settle,advance,rows,lines16,lines17,lines18,eval,simple,op,augOp,
      guard_jump,put,hpos,last,output]
    funext key
    simp [put]
    by_cases hk : key = "right" <;> by_cases hs : key = "state" <;> simp [hk,hs]

  · have hone : (2*(s "remaining"*s "radix") + s "radix" - 1)%2 = 1 := by omega
    simp [duration,Shared.PNP.Record285.Source.frame,hone,EventSystem.advance,system,
      step,frames,settle,advance,rows,lines16,lines17,lines18,eval,simple,op,augOp,
      guard_jump,put,hpos,last,output]
    funext key
    simp [put]
    by_cases hk : key = "right" <;> by_cases hs : key = "state" <;> simp [hk,hs]


/-- No marked call occurs during the candidate-initialization segment. -/
theorem segment_silent (s : Store) (hradix : 0 < s "radix") :
    ∀ t, t < duration s → ¬ (system s).BeepFrom (.live ⟨82,s,frames⟩) t := by
  have hpos : 1 ≤ 2*(s "remaining"*s "radix") + s "radix" := by omega
  have hmod : (2*(s "remaining"*s "radix") + s "radix" - 1)%2 < 2 := Nat.mod_lt _ (by decide)
  intro t ht
  by_cases hz : (2*(s "remaining"*s "radix") + s "radix" - 1)%2 = 0
  · have ht8 : t < 8 := by simpa [duration,frame,hz] using ht
    have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
    rcases hc with h|h|h|h|h|h|h|h <;> subst t <;>
      simp [EventSystem.BeepFrom,EventSystem.advance,system,step,frames,settle,
        advance,rows,lines16,lines17,lines18,eval,simple,op,augOp,guard_jump,put,hpos,hz]
  · have hone : (2*(s "remaining"*s "radix") + s "radix" - 1)%2 = 1 := by omega
    have ht9 : t < 9 := by simpa [duration,frame,hone] using ht
    have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 := by omega
    rcases hc with h|h|h|h|h|h|h|h|h <;> subst t <;>
      simp [EventSystem.BeepFrom,EventSystem.advance,system,step,frames,settle,
        advance,rows,lines16,lines17,lines18,eval,simple,op,augOp,guard_jump,put,hpos,hone]

end Shared.PNP.Record285.PythonControlCandidate
