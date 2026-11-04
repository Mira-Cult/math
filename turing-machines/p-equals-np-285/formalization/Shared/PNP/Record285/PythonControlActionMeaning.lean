import Shared.PNP.Record285.PythonControlAction

/-! Semantic handoff from the complete typed candidate action to the verified
source virtual transition. Python parser and unbounded loop equivalence remain
separate obligations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlActionMeaning
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControlAction
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip

def before (s : Store) : SimState := ⟨s "left",s "right",s "state",0⟩
def after (s : Store) : SimState := ⟨s "left",s "right",s "state",0⟩

/-- The decoded state is zero exactly when the source transition halts. -/
theorem halts_iff (s : Store) :
    simStep (s "digit") (before s) = none ↔ decoded s "state"=0 := by
  let packed := (popUnary (skipUnary (s "state") (s "digit"))).1
  have hf := decoded_fields s
  have hs : decoded s "state" = packed/4 := hf.2.2.1
  simp only [simStep,before,Nat.zero_mod,Nat.add_zero]
  change (if packed/4=0 then none else some _) = none ↔ _
  simp [←hs]

/-- For every non-HALT action, the typed code's complete left/right numeric
tapes and selector are exactly the source virtual successor. -/
theorem continue_matches (s : Store) (next : SimState)
    (h : simStep (s "digit") (before s) = some next) :
    after (continued (prepared (decoded s))) = next ∧
      (continued (prepared (decoded s))) "expected" = s "expected" := by
  let packed := (popUnary (skipUnary (s "state") (s "digit"))).1
  let d := decoded s
  have hf := decoded_fields s
  change d "write" = packed%2 ∧ d "direction" = (packed/2)%2 ∧ d "state" = packed/4 ∧
    d "left" = s "left" ∧ d "right" = s "right" ∧ d "expected" = s "expected" at hf
  dsimp only [d] at hf
  simp only [simStep,before,Nat.zero_mod,Nat.add_zero] at h
  change (if packed/4=0 then none else some ⟨
    2*(if (packed/2)%2=0 then s "left" else s "right")+packed%2,
    (if (packed/2)%2=0 then s "right" else s "left")/2,
    packed/4-1+2*((if (packed/2)%2=0 then s "right" else s "left")%2),0⟩) = some next at h
  by_cases hz : packed/4=0
  · simp [hz] at h
  · simp only [hz,if_false,Option.some.injEq] at h
    subst next
    constructor
    · simp [after,continued,prepared,put,orientedLeft,orientedRight,
        hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1]
    · simp [continued,prepared,put,hf.2.2.2.2.2]

/-- On HALT, the source mismatch bit is toggled and all candidate-loop
control leaves are silent; the record-action segment supplies its timing. -/
theorem halt_matches (s : Store) :
    (halted (prepared (decoded s))) "expected" =
      (if s "expected"=0 then 1 else 0) := by
  have hf := decoded_fields s
  simp [halted,prepared,put,hf.2.2.2.2.2]

/-- Neither action branch changes the remaining clock or candidate program. -/
theorem action_control_fields (s : Store) :
    (continued (prepared (decoded s))) "steps" = s "steps" ∧
    (continued (prepared (decoded s))) "program" = s "program" ∧
    (halted (prepared (decoded s))) "steps" = s "steps" ∧
    (halted (prepared (decoded s))) "program" = s "program" := by
  simp [continued,halted,prepared,decoded,Shared.PNP.Record285.PythonControlDecode.storeOf,put]

/-- A complete action of the typed candidate evaluator advances silently to
the correct HALT or continuing source transition, with the correct loop stack
and the full post-store fixed by the preceding segment theorem. -/
theorem candidate_action_matches (s : Store) :
    ∃ n out loops, 0 < n ∧ Silent (.live ⟨94,s,context⟩) (.live ⟨131,out,loops⟩) n ∧
      out "steps" = s "steps" ∧ out "program" = s "program" ∧
      match simStep (s "digit") (before s) with
      | none => loops = Shared.PNP.Record285.PythonControlCandidate.frames ∧
          out "expected" = (if s "expected"=0 then 1 else 0)
      | some next => loops = context ∧ after out = next ∧ out "expected" = s "expected" := by
  let d := decoded s
  let p := prepared d
  obtain ⟨n,hn,hsegment⟩ := candidate_action_terminates s
  change Silent (.live ⟨94,s,context⟩)
    (if d "state"=0 then
      .live ⟨131,halted p,Shared.PNP.Record285.PythonControlCandidate.frames⟩
     else .live ⟨131,continued p,context⟩) n at hsegment
  by_cases hz : d "state"=0
  · have hnone : simStep (s "digit") (before s) = none := (halts_iff s).2 hz
    simp only [hz,if_true] at hsegment
    refine ⟨n,halted p,Shared.PNP.Record285.PythonControlCandidate.frames,hn,hsegment,
      (action_control_fields s).2.2.1,(action_control_fields s).2.2.2,?_⟩
    simp only [hnone]
    exact ⟨trivial,halt_matches s⟩
  · cases hr : simStep (s "digit") (before s) with
    | none => exact False.elim (hz ((halts_iff s).1 hr))
    | some next =>
      simp only [hz,if_false] at hsegment
      obtain ⟨hnext,hexpected⟩ := continue_matches s next hr
      refine ⟨n,continued p,context,hn,hsegment,
        (action_control_fields s).1,(action_control_fields s).2.1,?_⟩
      simp only [hr]
      exact ⟨trivial,hnext,hexpected⟩

end Shared.PNP.Record285.PythonControlActionMeaning
