import Shared.PNP.Record285.PythonControlDispatch

/-! Outer-loop bootstrap and marked event, with exact finite event accounting. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlBegin
open Shared.Beeping
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem Silent)
open Shared.PNP.Record285.PythonControlCandidate (frames)
open Shared.PNP.Record285.PythonControlDispatch
open Shared.PNP.Record285.PythonControlReferenceComplete (initial)

def reset (s : Store) : Store := put (put (put s "n" 0) "radix" 1) "remaining" 0

def startStore : Store := put (put (fun _ => 0) "program" 0) "exponent" 1

def Marked (a b : Status) (n mark : Nat) : Prop :=
  pySystem.advance a n=b ∧ ∀ t, t<n → (pySystem.BeepFrom a t ↔ t=mark)

theorem rows : code[27]?=lines5[2]? ∧ code[28]?=lines5[3]? ∧ code[29]?=lines5[4]? ∧
    code[30]?=lines6[0]? ∧ code[31]?=lines6[1]? ∧ seek code 29 4=146 ∧ seek code 32 8=140 := by decide

theorem input_next (s : Store) : Silent (nextInput s) (initial s) 1 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,nextInput,initial,frames,outer,PythonControlReferenceBranch.outer,settle,advance,
      rows,lines6,eval]
  · intro t ht
    have : t=0 := by omega
    subst t
    simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,nextInput,frames,outer,settle,
      advance,rows,lines6,eval]

theorem begin_segment (s : Store) : Marked (beforeBeep s) (initial (reset s)) 3 0 := by
  constructor
  · simp [Marked,pySystem,EventSystem.advance,step,beforeBeep,initial,reset,frames,outer,PythonControlReferenceBranch.outer,settle,
      advance,rows,lines5,lines6,eval,simple,values,assignAll,put]
  · intro t ht
    have hc : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hc with rfl|rfl|rfl <;>
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,beforeBeep,frames,outer,settle,
        advance,rows,lines5,lines6,eval,simple,values,assignAll,put]

theorem startup_segment : Marked mainSystem.initial (initial (reset startStore)) 5 2 := by
  constructor
  · simp [Marked,pySystem,mainSystem,EventSystem.advance,step,initial,reset,startStore,
      frames,outer,PythonControlReferenceBranch.outer,settle,advance,rows,lines5,lines6,eval,simple,values,assignAll,put]
  · intro t ht
    have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl <;>
      simp [pySystem,mainSystem,EventSystem.BeepFrom,EventSystem.advance,step,startStore,
        frames,outer,PythonControlReferenceBranch.outer,settle,advance,rows,lines5,lines6,eval,simple,values,assignAll,put]

end Shared.PNP.Record285.PythonControlBegin
