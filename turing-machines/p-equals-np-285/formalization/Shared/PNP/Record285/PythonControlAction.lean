import Shared.PNP.Record285.PythonControlDecode

/-! Write/move setup in the typed candidate evaluator. This is a partial
natural-number interpreter theorem, not a CPython semantics theorem. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlAction
open Shared.Beeping
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip

def orientedLeft (s : Store) : Nat := if s "direction"=0 then s "left" else s "right"
def orientedRight (s : Store) : Nat := if s "direction"=0 then s "right" else s "left"

def prepared (s : Store) : Store :=
  put (put (put (put s "direction" 0) "write" 0)
    "left" (2*orientedLeft s+s "write")) "right" (orientedRight s)

def duration (s : Store) : Nat := 3+2*s "direction"+2*s "write"

theorem rows : code[112]?=lines22[2]? ∧ code[113]?=lines22[3]? ∧
    code[114]?=lines22[4]? ∧ code[115]?=lines23[0]? ∧ code[116]?=lines23[1]? ∧
    code[117]?=lines23[2]? ∧ code[118]?=lines23[3]? := by decide

theorem flow : jumpFalse code 112 16=115 ∧ jumpFalse code 116 16=119 := by decide

/-- Write and direction flags are bits, as guaranteed by record decoding.
The typed lines orient the tape, write the bit, and retain the full store. -/
theorem prepare (s : Store) (hd : s "direction" ≤ 1) (hw : s "write" ≤ 1) :
    Silent (.live ⟨112,s,context⟩) (.live ⟨119,prepared s,context⟩) (duration s) := by
  by_cases hdir : s "direction"=0
  · by_cases hwrite : s "write"=0
    · constructor
      · simp [Silent,pySystem,EventSystem.advance,step,context,settle,advance,rows,flow,
          lines22,lines23,eval,op,simple,values,assignAll,augOp,put,hdir,hwrite,duration,
          prepared,orientedLeft,orientedRight]
        funext key
        by_cases hl : key="left" <;> by_cases hr : key="right" <;>
          by_cases hw : key="write" <;> by_cases hd : key="direction" <;>
          simp [put,hl,hr,hw,hd,hdir,hwrite] <;> omega
      · intro t ht
        have ht3 : t<3 := by simpa [duration,hdir,hwrite] using ht
        have hc : t=0 ∨ t=1 ∨ t=2 := by omega
        rcases hc with rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,context,settle,advance,
            rows,flow,lines22,lines23,eval,op,simple,values,assignAll,augOp,put,hdir,hwrite]
    · have hwrite1 : s "write"=1 := by omega
      constructor
      · simp [Silent,pySystem,EventSystem.advance,step,context,settle,advance,rows,flow,
          lines22,lines23,eval,op,simple,values,assignAll,augOp,put,hdir,hwrite1,duration,
          prepared,orientedLeft,orientedRight]
        funext key
        by_cases hl : key="left" <;> by_cases hr : key="right" <;>
          by_cases hw : key="write" <;> by_cases hd : key="direction" <;>
          simp [put,hl,hr,hw,hd,hdir,hwrite1] <;> omega
      · intro t ht
        have ht5 : t<5 := by simpa [duration,hdir,hwrite1] using ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,context,settle,advance,
            rows,flow,lines22,lines23,eval,op,simple,values,assignAll,augOp,put,hdir,hwrite1]
  · have hdir1 : s "direction"=1 := by omega
    by_cases hwrite : s "write"=0
    · constructor
      · simp [Silent,pySystem,EventSystem.advance,step,context,settle,advance,rows,flow,
          lines22,lines23,eval,op,simple,values,assignAll,augOp,put,hdir1,hwrite,duration,
          prepared,orientedLeft,orientedRight]
        funext key
        by_cases hl : key="left" <;> by_cases hr : key="right" <;>
          by_cases hw : key="write" <;> by_cases hd : key="direction" <;>
          simp [put,hl,hr,hw,hd,hdir1,hwrite] <;> omega
      · intro t ht
        have ht5 : t<5 := by simpa [duration,hdir1,hwrite] using ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,context,settle,advance,
            rows,flow,lines22,lines23,eval,op,simple,values,assignAll,augOp,put,hdir1,hwrite]
    · have hwrite1 : s "write"=1 := by omega
      constructor
      · simp [Silent,pySystem,EventSystem.advance,step,context,settle,advance,rows,flow,
          lines22,lines23,eval,op,simple,values,assignAll,augOp,put,hdir1,hwrite1,duration,
          prepared,orientedLeft,orientedRight]
        funext key
        by_cases hl : key="left" <;> by_cases hr : key="right" <;>
          by_cases hw : key="write" <;> by_cases hd : key="direction" <;>
          simp [put,hl,hr,hw,hd,hdir1,hwrite1] <;> omega
      · intro t ht
        have ht7 : t<7 := by simpa [duration,hdir1,hwrite1] using ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,context,settle,advance,
            rows,flow,lines22,lines23,eval,op,simple,values,assignAll,augOp,put,hdir1,hwrite1]

theorem tailRows : code[119]?=lines23[4]? ∧ code[120]?=lines24[0]? ∧
    code[121]?=lines24[1]? ∧ code[122]?=lines24[2]? ∧ code[123]?=lines24[3]? ∧
    code[124]?=lines24[4]? ∧ code[125]?=lines25[0]? ∧ code[126]?=lines25[1]? ∧
    code[127]?=lines25[2]? ∧ code[128]?=lines25[3]? ∧ code[129]?=lines25[4]? ∧
    code[130]?=lines26[0]? := by decide

theorem tailFlow : jumpFalse code 119 16=125 ∧ jumpFalse code 121 20=123 ∧
    jumpFalse code 126 20=129 ∧ seek code 125 16=131 ∧ seek code 129 20=130 := by decide

def continued (s : Store) : Store :=
  put (put s "state" (s "state"-1+2*(s "right"%2))) "right" (s "right"/2)

def continueDuration (s : Store) : Nat := 5+s "right"%2

/-- A positive decoded next state updates the full virtual tape and selector,
returns to the candidate clock boundary, and emits no event. -/
theorem continue_segment (s : Store) (hs : 0 < s "state") :
    Silent (.live ⟨119,s,context⟩) (.live ⟨131,continued s,context⟩) (continueDuration s) := by
  have hmod : s "right"%2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hz : s "right"%2=0
  · constructor
    · simp [Silent,pySystem,EventSystem.advance,step,context,settle,advance,tailRows,tailFlow,
        lines23,lines24,eval,op,simple,augOp,put,show s "state" ≠ 0 by omega,
        show 1 ≤ s "state" by omega,hz,continueDuration,continued]
    · intro t ht
      have ht5 : t<5 := by simpa [continueDuration,hz] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,context,settle,advance,
          tailRows,tailFlow,lines23,lines24,eval,op,simple,augOp,put,
          show s "state" ≠ 0 by omega,show 1 ≤ s "state" by omega,hz]
  · have hone : s "right"%2=1 := by omega
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,context,settle,advance,tailRows,tailFlow,
        lines23,lines24,eval,op,simple,augOp,put,show s "state" ≠ 0 by omega,
        show 1 ≤ s "state" by omega,hone,continueDuration,continued]
      funext key
      by_cases hr : key="right" <;> by_cases hs : key="state" <;> simp [put,hr,hs]
    · intro t ht
      have ht6 : t<6 := by simpa [continueDuration,hone] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,context,settle,advance,
          tailRows,tailFlow,lines23,lines24,eval,op,simple,augOp,put,
          show s "state" ≠ 0 by omega,show 1 ≤ s "state" by omega,hone]

def halted (s : Store) : Store :=
  put (put s "right" (s "right"/2)) "expected" (if s "expected"=0 then 1 else 0)

def haltDuration (s : Store) : Nat := if s "expected"=0 then 5 else 6

/-- A zero decoded next state performs the source's mismatch toggle and
breaks the bounded candidate loop, silently and with the full store fixed. -/
theorem halt_segment (s : Store) (hs : s "state"=0) :
    Silent (.live ⟨119,s,context⟩)
      (.live ⟨131,halted s,Shared.PNP.Record285.PythonControlCandidate.frames⟩) (haltDuration s) := by
  by_cases he : s "expected"=0
  · constructor
    · simp [Silent,pySystem,EventSystem.advance,step,context,settle,advance,tailRows,tailFlow,
        lines23,lines24,lines25,lines26,eval,op,simple,augOp,put,hs,he,haltDuration,halted,
        Shared.PNP.Record285.PythonControlCandidate.frames]
    · intro t ht
      have ht5 : t<5 := by simpa [haltDuration,he] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,context,settle,advance,
          tailRows,tailFlow,lines23,lines24,lines25,lines26,eval,op,simple,augOp,put,hs,he]
  · constructor
    · simp [Silent,pySystem,EventSystem.advance,step,context,settle,advance,tailRows,tailFlow,
        lines23,lines24,lines25,lines26,eval,op,simple,augOp,put,hs,he,haltDuration,halted,
        Shared.PNP.Record285.PythonControlCandidate.frames]
    · intro t ht
      have ht6 : t<6 := by simpa [haltDuration,he] using ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,context,settle,advance,
          tailRows,tailFlow,lines23,lines24,lines25,lines26,eval,op,simple,augOp,put,hs,he]

/-- The exact decoded store after the record-selection block. -/
def decoded (s : Store) : Store :=
  let stream := Shared.PNP.Record285.Source.skipUnary (s "state") (s "digit")
  let record := Shared.PNP.Record285.Source.popUnary stream
  Shared.PNP.Record285.PythonControlDecode.storeOf s record.2
    (Shared.PNP.Record285.PythonInlineDecoder.bumpN record.1 ⟨false,false,0⟩)

theorem decoded_fields (s : Store) :
    let packed := (Shared.PNP.Record285.Source.popUnary
      (Shared.PNP.Record285.Source.skipUnary (s "state") (s "digit"))).1
    decoded s "write" = packed%2 ∧ decoded s "direction" = (packed/2)%2 ∧
      decoded s "state" = packed/4 ∧ decoded s "left" = s "left" ∧
      decoded s "right" = s "right" ∧ decoded s "expected" = s "expected" := by
  let stream := Shared.PNP.Record285.Source.skipUnary (s "state") (s "digit")
  let d := Shared.PNP.Record285.PythonInlineDecoder.bumpN
    (Shared.PNP.Record285.Source.popUnary stream).1 ⟨false,false,0⟩
  have hf := Shared.PNP.Record285.PythonInlineDecoder.read_fields stream
  rw [Shared.PNP.Record285.PythonInlineDecoder.read_correct] at hf
  change (if d.write then 1 else 0) = (Shared.PNP.Record285.Source.popUnary stream).1%2 ∧
    (if d.direction then 1 else 0) = ((Shared.PNP.Record285.Source.popUnary stream).1/2)%2 ∧
    d.state = (Shared.PNP.Record285.Source.popUnary stream).1/4 ∧ _ at hf
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [decoded,Shared.PNP.Record285.PythonControlDecode.storeOf,put,stream,d] using hf.1
  · simpa [decoded,Shared.PNP.Record285.PythonControlDecode.storeOf,put,stream,d] using hf.2.1
  · simpa [decoded,Shared.PNP.Record285.PythonControlDecode.storeOf,put,stream,d] using hf.2.2.1
  · simp [decoded,Shared.PNP.Record285.PythonControlDecode.storeOf,put]
  · simp [decoded,Shared.PNP.Record285.PythonControlDecode.storeOf,put]
  · simp [decoded,Shared.PNP.Record285.PythonControlDecode.storeOf,put]

/-- The entire decoded action, including the HALT or continuation path,
terminates silently with the exact complete post-store and loop stack. -/
theorem candidate_action_terminates (s : Store) :
    let d := decoded s
    let p := prepared d
    ∃ n, 0 < n ∧ Silent (.live ⟨94,s,context⟩)
      (if d "state"=0 then
        .live ⟨131,halted p,Shared.PNP.Record285.PythonControlCandidate.frames⟩
       else .live ⟨131,continued p,context⟩) n := by
  let d := decoded s
  let p := prepared d
  obtain ⟨n,hn,hdecode⟩ := Shared.PNP.Record285.PythonControlDecode.candidate_record_terminates s
  change Silent (.live ⟨94,s,context⟩) (.live ⟨112,d,context⟩) n at hdecode
  have hf := decoded_fields s
  have hw : d "write" ≤ 1 := by
    change decoded s "write" ≤ 1
    rw [hf.1]; have hh := Nat.mod_lt (Shared.PNP.Record285.Source.popUnary
      (Shared.PNP.Record285.Source.skipUnary (s "state") (s "digit"))).1 (by decide : 0<2); omega
  have hd : d "direction" ≤ 1 := by
    change decoded s "direction" ≤ 1
    rw [hf.2.1]; have hh := Nat.mod_lt ((Shared.PNP.Record285.Source.popUnary
      (Shared.PNP.Record285.Source.skipUnary (s "state") (s "digit"))).1/2) (by decide : 0<2); omega
  have hprep := prepare d hd hw
  have hpstate : p "state" = d "state" := by simp [p,prepared,put]
  change ∃ n, 0 < n ∧ Silent (.live ⟨94,s,context⟩)
    (if d "state"=0 then
      .live ⟨131,halted p,Shared.PNP.Record285.PythonControlCandidate.frames⟩
     else .live ⟨131,continued p,context⟩) n
  by_cases hz : d "state"=0
  · have hhalt := halt_segment p (by omega)
    refine ⟨n+duration d+haltDuration p,by have := hn; omega,?_⟩
    simp only [hz,if_true]
    exact silent_trans (silent_trans hdecode hprep) hhalt
  · have hlive := continue_segment p (by omega)
    refine ⟨n+duration d+continueDuration p,by have := hn; omega,?_⟩
    simp only [hz,if_false]
    exact silent_trans (silent_trans hdecode hprep) hlive

end Shared.PNP.Record285.PythonControlAction
