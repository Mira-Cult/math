import Shared.PNP.Record285.PythonControlReferenceDecode
import Shared.PNP.Record285.PythonControlAction

/-! Finite typed reference write/move and state-update actions, with the
reference evaluator's distinct HALT behavior and enclosing stack. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceAction
open Shared.Beeping
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem Silent silent_trans)
open Shared.PNP.Record285.PythonControlRelocation (referenceBase)
open Shared.PNP.Record285.PythonControlAction (prepared duration orientedLeft orientedRight continued continueDuration decoded decoded_fields)
open Shared.PNP.Record285.PythonControlRelocationTransfer (referenceEntry referenceExit)

theorem rows : code[65]?=lines13[0]? ∧ code[66]?=lines13[1]? ∧
    code[67]?=lines13[2]? ∧ code[68]?=lines13[3]? ∧ code[69]?=lines13[4]? ∧
    code[70]?=lines14[0]? ∧ code[71]?=lines14[1]? := by decide

theorem flow : jumpFalse code 65 20=68 ∧ jumpFalse code 69 20=72 := by decide

theorem reference_prepare (s : Store) (hd : s "direction" ≤ 1) (hw : s "write" ≤ 1) :
    Silent (.live ⟨65,s,referenceBase⟩) (.live ⟨72,prepared s,referenceBase⟩) (duration s) := by
  by_cases hdir : s "direction"=0
  · by_cases hwrite : s "write"=0
    · constructor
      · simp [Silent,pySystem,EventSystem.advance,step,referenceBase,settle,advance,rows,flow,
          lines13,lines14,eval,op,simple,values,assignAll,augOp,put,hdir,hwrite,duration,
          prepared,orientedLeft,orientedRight]
        funext key
        by_cases hl : key="left" <;> by_cases hr : key="right" <;>
          by_cases hw : key="write" <;> by_cases hd : key="direction" <;>
          simp [put,hl,hr,hw,hd,hdir,hwrite] <;> omega
      · intro t ht
        have ht3 : t<3 := by simpa [duration,hdir,hwrite] using ht
        have hc : t=0 ∨ t=1 ∨ t=2 := by omega
        rcases hc with rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,referenceBase,settle,advance,
            rows,flow,lines13,lines14,eval,op,simple,values,assignAll,augOp,put,hdir,hwrite]
    · have hwrite1 : s "write"=1 := by omega
      constructor
      · simp [Silent,pySystem,EventSystem.advance,step,referenceBase,settle,advance,rows,flow,
          lines13,lines14,eval,op,simple,values,assignAll,augOp,put,hdir,hwrite1,duration,
          prepared,orientedLeft,orientedRight]
        funext key
        by_cases hl : key="left" <;> by_cases hr : key="right" <;>
          by_cases hw : key="write" <;> by_cases hd : key="direction" <;>
          simp [put,hl,hr,hw,hd,hdir,hwrite1] <;> omega
      · intro t ht
        have ht5 : t<5 := by simpa [duration,hdir,hwrite1] using ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,referenceBase,settle,advance,
            rows,flow,lines13,lines14,eval,op,simple,values,assignAll,augOp,put,hdir,hwrite1]
  · have hdir1 : s "direction"=1 := by omega
    by_cases hwrite : s "write"=0
    · constructor
      · simp [Silent,pySystem,EventSystem.advance,step,referenceBase,settle,advance,rows,flow,
          lines13,lines14,eval,op,simple,values,assignAll,augOp,put,hdir1,hwrite,duration,
          prepared,orientedLeft,orientedRight]
        funext key
        by_cases hl : key="left" <;> by_cases hr : key="right" <;>
          by_cases hw : key="write" <;> by_cases hd : key="direction" <;>
          simp [put,hl,hr,hw,hd,hdir1,hwrite] <;> omega
      · intro t ht
        have ht5 : t<5 := by simpa [duration,hdir1,hwrite] using ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,referenceBase,settle,advance,
            rows,flow,lines13,lines14,eval,op,simple,values,assignAll,augOp,put,hdir1,hwrite]
    · have hwrite1 : s "write"=1 := by omega
      constructor
      · simp [Silent,pySystem,EventSystem.advance,step,referenceBase,settle,advance,rows,flow,
          lines13,lines14,eval,op,simple,values,assignAll,augOp,put,hdir1,hwrite1,duration,
          prepared,orientedLeft,orientedRight]
        funext key
        by_cases hl : key="left" <;> by_cases hr : key="right" <;>
          by_cases hw : key="write" <;> by_cases hd : key="direction" <;>
          simp [put,hl,hr,hw,hd,hdir1,hwrite1] <;> omega
      · intro t ht
        have ht7 : t<7 := by simpa [duration,hdir1,hwrite1] using ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,referenceBase,settle,advance,
            rows,flow,lines13,lines14,eval,op,simple,values,assignAll,augOp,put,hdir1,hwrite1]



theorem tailRows : code[72]?=lines14[2]? ∧ code[73]?=lines14[3]? ∧
    code[74]?=lines14[4]? ∧ code[75]?=lines15[0]? ∧ code[76]?=lines15[1]? ∧
    code[77]?=lines15[2]? ∧ code[78]?=lines15[3]? ∧ code[79]?=lines15[4]? ∧
    code[80]?=lines16[0]? ∧ code[81]?=lines16[1]? := by decide

theorem tailFlow : jumpFalse code 72 20=78 ∧ jumpFalse code 74 24=76 ∧
    seek code 78 20=82 := by decide

theorem reference_continue_segment (s : Store) (hs : 0 < s "state") :
    Silent (.live ⟨72,s,referenceBase⟩) (.live ⟨82,continued s,referenceBase⟩) (continueDuration s) := by
  have hmod : s "right"%2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hz : s "right"%2=0
  · constructor
    · simp [Silent,pySystem,EventSystem.advance,step,referenceBase,settle,advance,tailRows,tailFlow,
        lines14,lines15,eval,op,simple,augOp,put,show s "state" ≠ 0 by omega,
        show 1 ≤ s "state" by omega,hz,continueDuration,continued]
    · intro t ht
      have ht5 : t<5 := by simpa [continueDuration,hz] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,referenceBase,settle,advance,
          tailRows,tailFlow,lines14,lines15,eval,op,simple,augOp,put,
          show s "state" ≠ 0 by omega,show 1 ≤ s "state" by omega,hz]
  · have hone : s "right"%2=1 := by omega
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,referenceBase,settle,advance,tailRows,tailFlow,
        lines14,lines15,eval,op,simple,augOp,put,show s "state" ≠ 0 by omega,
        show 1 ≤ s "state" by omega,hone,continueDuration,continued]
      funext key
      by_cases hr : key="right" <;> by_cases hs : key="state" <;> simp [put,hr,hs]
    · intro t ht
      have ht6 : t<6 := by simpa [continueDuration,hone] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,referenceBase,settle,advance,
          tailRows,tailFlow,lines14,lines15,eval,op,simple,augOp,put,
          show s "state" ≠ 0 by omega,show 1 ≤ s "state" by omega,hone]


def outerReference : List Loop := [⟨34,82⟩,⟨31,140⟩,⟨28,146⟩]
def referenceHalted (s : Store) : Store :=
  put (put (put s "right" (s "right"/2)) "expected" 1) "branches" 0

theorem reference_halt_segment (s : Store) (hs : s "state"=0) :
    Silent (.live ⟨72,s,referenceBase⟩) (.live ⟨82,referenceHalted s,outerReference⟩) 5 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,referenceBase,outerReference,settle,advance,
      tailRows,tailFlow,lines14,lines15,lines16,eval,op,simple,augOp,put,hs,referenceHalted]
  · intro t ht
    have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl <;>
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,referenceBase,outerReference,
        settle,advance,tailRows,tailFlow,lines14,lines15,lines16,eval,op,simple,augOp,put,hs]

theorem reference_action_terminates (s : Store) :
    let d := decoded s
    let p := prepared d
    ∃ n, 0 < n ∧ Silent (referenceEntry s)
      (if d "state"=0 then
        .live ⟨82,referenceHalted p,outerReference⟩
       else .live ⟨82,continued p,referenceBase⟩) n := by
  let d := decoded s
  let p := prepared d
  obtain ⟨n,hn,hdecode⟩ := Shared.PNP.Record285.PythonControlReferenceDecode.reference_record_terminates s
  change Silent (referenceEntry s) (referenceExit d) n at hdecode
  have hf := decoded_fields s
  have hw : d "write" ≤ 1 := by
    change decoded s "write" ≤ 1
    rw [hf.1]; have hh := Nat.mod_lt (Shared.PNP.Record285.Source.popUnary
      (Shared.PNP.Record285.Source.skipUnary (s "state") (s "digit"))).1 (by decide : 0<2); omega
  have hd : d "direction" ≤ 1 := by
    change decoded s "direction" ≤ 1
    rw [hf.2.1]; have hh := Nat.mod_lt ((Shared.PNP.Record285.Source.popUnary
      (Shared.PNP.Record285.Source.skipUnary (s "state") (s "digit"))).1/2) (by decide : 0<2); omega
  have hprep := reference_prepare d hd hw
  have hpstate : p "state" = d "state" := by simp [p,prepared,put]
  change ∃ n, 0 < n ∧ Silent (referenceEntry s)
    (if d "state"=0 then
      .live ⟨82,referenceHalted p,outerReference⟩
     else .live ⟨82,continued p,referenceBase⟩) n
  by_cases hz : d "state"=0
  · have hhalt := reference_halt_segment p (by omega)
    refine ⟨n+duration d+5,by have := hn; omega,?_⟩
    simp only [hz,if_true]
    exact silent_trans (silent_trans hdecode hprep) hhalt
  · have hlive := reference_continue_segment p (by omega)
    refine ⟨n+duration d+continueDuration p,by have := hn; omega,?_⟩
    simp only [hz,if_false]
    exact silent_trans (silent_trans hdecode hprep) hlive


end Shared.PNP.Record285.PythonControlReferenceAction
