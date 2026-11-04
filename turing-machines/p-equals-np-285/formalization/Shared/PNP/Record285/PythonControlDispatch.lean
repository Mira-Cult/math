import Shared.PNP.Record285.PythonControlComparison

/-! Actual typed controller dispatch after a completed comparison, including
input advancement, candidate advancement, and the next marked-call boundary. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlDispatch
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem Silent)
open Shared.PNP.Record285.PythonControlCandidate (frames)

def outer : List Loop := [⟨28,146⟩]
def dispatch (s : Store) : Status := .live ⟨131,s,frames⟩
def nextInput (s : Store) : Status := .live ⟨140,s,frames⟩
def nextCandidate (s : Store) : Status := .live ⟨140,s,outer⟩
def beforeBeep (s : Store) : Status := .live ⟨29,s,outer⟩
def remainingStore (s : Store) : Store := put s "remaining" (s "remaining"-1)
def nextBlockStore (s : Store) : Store :=
  put (put (put s "radix" (2*s "radix")) "n" (s "n"+1)) "remaining" (2*s "radix"-1)
def nextCandidateStore (s : Store) : Store :=
  let pair := advanceCandidate (s "program") (s "exponent")
  put (put s "program" pair.1) "exponent" pair.2

theorem rows : code[28]?=lines5[3]? ∧ code[131]?=lines26[1]? ∧
    code[132]?=lines26[2]? ∧ code[133]?=lines26[3]? ∧ code[134]?=lines26[4]? ∧
    code[135]?=lines27[0]? ∧ code[136]?=lines27[1]? ∧ code[137]?=lines27[2]? ∧
    code[138]?=lines27[3]? ∧ code[139]?=lines27[4]? ∧ code[140]?=lines28[0]? ∧
    code[141]?=lines28[1]? ∧ code[142]?=lines28[2]? ∧ code[143]?=lines28[3]? ∧
    code[144]?=lines28[4]? ∧ code[145]?=lines29[0]? := by decide

theorem flow : jumpFalse code 131 12=133 ∧ jumpFalse code 133 12=136 ∧
    seek code 136 12=140 ∧ jumpFalse code 140 8=144 ∧
    seek code 144 8=146 ∧ seek code 29 4=146 := by decide

theorem failed (s : Store) (h : s "expected" ≠ 0) :
    Silent (dispatch s) (nextCandidate s) 2 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,dispatch,nextCandidate,frames,outer,settle,
      advance,rows,flow,lines26,eval,h]
  · intro t ht
    have hc : t=0 ∨ t=1 := by omega
    rcases hc with rfl|rfl <;>
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,dispatch,frames,outer,settle,
        advance,rows,flow,lines26,eval,h]

theorem successful_remaining (s : Store) (he : s "expected"=0) (hr : 0<s "remaining") :
    Silent (dispatch s) (nextInput (remainingStore s)) 4 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,dispatch,nextInput,frames,settle,advance,
      rows,flow,lines26,lines27,eval,op,simple,augOp,put,he,show s "remaining" ≠ 0 by omega,
      show 1 ≤ s "remaining" by omega,remainingStore]
  · intro t ht
    have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    rcases hc with rfl|rfl|rfl|rfl <;>
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,dispatch,frames,settle,advance,
        rows,flow,lines26,lines27,eval,op,simple,augOp,put,he,show s "remaining" ≠ 0 by omega,
        show 1 ≤ s "remaining" by omega]

theorem successful_block (s : Store) (he : s "expected"=0) (hr : s "remaining"=0)
    (hradix : 0<s "radix") : Silent (dispatch s) (nextInput (nextBlockStore s)) 6 := by
  have hp : 1 ≤ 2*s "radix" := by omega
  have hp' : 1 ≤ s "radix"*2 := by omega
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,dispatch,nextInput,frames,settle,advance,
      rows,flow,lines26,lines27,eval,op,simple,augOp,put,he,hr,hp,hp',nextBlockStore]
    funext key
    by_cases hb : key="radix" <;> by_cases hn : key="n" <;> by_cases hm : key="remaining" <;>
      simp [put,hb,hn,hm,Nat.mul_comm]
  · intro t ht
    have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,dispatch,frames,settle,advance,
        rows,flow,lines26,lines27,eval,op,simple,augOp,put,he,hr,hp,hp']

theorem candidate_advance (s : Store) :
    Silent (nextCandidate s) (beforeBeep (nextCandidateStore s))
      (if s "program"=0 then 4 else 5) := by
  by_cases hz : s "program"=0
  · constructor
    · simp [Silent,pySystem,EventSystem.advance,step,nextCandidate,beforeBeep,outer,settle,
        advance,rows,flow,lines5,lines28,lines29,eval,op,simple,augOp,put,hz,
        nextCandidateStore,advanceCandidate]
    · intro t ht
      have ht4 : t<4 := by simpa [hz] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
      rcases hc with rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,nextCandidate,outer,settle,
          advance,rows,flow,lines5,lines28,lines29,eval,op,simple,augOp,put,hz]
  · have hp : 1 ≤ s "program" := by omega
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,nextCandidate,beforeBeep,outer,settle,
        advance,rows,flow,lines5,lines28,lines29,eval,op,simple,augOp,put,hz,hp,
        nextCandidateStore,advanceCandidate]
    · intro t ht
      have ht5 : t<5 := by simpa [hz] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,nextCandidate,outer,settle,
          advance,rows,flow,lines5,lines28,lines29,eval,op,simple,augOp,put,hz,hp]

end Shared.PNP.Record285.PythonControlDispatch
