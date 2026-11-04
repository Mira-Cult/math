import Shared.PNP.Record285.PythonControlReferenceAction
import Shared.PNP.Record285.PythonControlActionMeaning

/-! The reference virtual action agrees with the verified source transition;
its halt path also records acceptance and clears the branch counter. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceActionMeaning
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip
open Shared.PNP.Record285.PythonControlAction
open Shared.PNP.Record285.PythonControlActionMeaning
open Shared.PNP.Record285.PythonControlReferenceAction
open Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonControlRelocationTransfer

theorem preserved_fields (s : Store) :
    (continued (prepared (decoded s))) "steps" = s "steps" ∧
    (continued (prepared (decoded s))) "program" = s "program" ∧
    (continued (prepared (decoded s))) "choices" = s "choices" ∧
    (continued (prepared (decoded s))) "branches" = s "branches" ∧
    (referenceHalted (prepared (decoded s))) "steps" = s "steps" ∧
    (referenceHalted (prepared (decoded s))) "program" = s "program" ∧
    (referenceHalted (prepared (decoded s))) "choices" = s "choices" := by
  simp [continued,referenceHalted,prepared,decoded,
    Shared.PNP.Record285.PythonControlDecode.storeOf,put]

theorem input_fields (s : Store) :
    (continued (prepared (decoded s))) "radix" = s "radix" ∧
    (continued (prepared (decoded s))) "remaining" = s "remaining" ∧
    (referenceHalted (prepared (decoded s))) "radix" = s "radix" ∧
    (referenceHalted (prepared (decoded s))) "remaining" = s "remaining" := by
  simp [continued,referenceHalted,prepared,decoded,
    Shared.PNP.Record285.PythonControlDecode.storeOf,put]

theorem named_fields (s : Store) :
    (continued (prepared (decoded s))) "n" = s "n" ∧
    (continued (prepared (decoded s))) "exponent" = s "exponent" ∧
    (referenceHalted (prepared (decoded s))) "n" = s "n" ∧
    (referenceHalted (prepared (decoded s))) "exponent" = s "exponent" := by
  simp [continued,referenceHalted,prepared,decoded,
    Shared.PNP.Record285.PythonControlDecode.storeOf,put]

theorem reference_action_matches (s : Store) :
    ∃ n out loops, 0 < n ∧ Silent (referenceEntry s) (.live ⟨82,out,loops⟩) n ∧
      out "steps" = s "steps" ∧ out "program" = s "program" ∧ out "choices" = s "choices" ∧
      out "radix" = s "radix" ∧ out "remaining" = s "remaining" ∧
      out "n" = s "n" ∧ out "exponent" = s "exponent" ∧
      match simStep (s "digit") (before s) with
      | none => loops = outerReference ∧ out "expected" = 1 ∧ out "branches" = 0
      | some next => loops = referenceBase ∧ after out = next ∧
          out "expected" = s "expected" ∧ out "branches" = s "branches" := by
  let d := decoded s
  let p := prepared d
  obtain ⟨n,hn,hsegment⟩ := reference_action_terminates s
  change Silent (referenceEntry s)
    (if d "state"=0 then .live ⟨82,referenceHalted p,outerReference⟩
     else .live ⟨82,continued p,referenceBase⟩) n at hsegment
  have hp := preserved_fields s
  have hi := input_fields s
  have hname := named_fields s
  by_cases hz : d "state"=0
  · have hnone : simStep (s "digit") (before s) = none := (halts_iff s).2 hz
    simp only [hz,if_true] at hsegment
    refine ⟨n,referenceHalted p,outerReference,hn,hsegment,hp.2.2.2.2.1,
      hp.2.2.2.2.2.1,hp.2.2.2.2.2.2,hi.2.2.1,hi.2.2.2,hname.2.2.1,hname.2.2.2,?_⟩
    simp [hnone,referenceHalted,put]
  · cases hr : simStep (s "digit") (before s) with
    | none => exact False.elim (hz ((halts_iff s).1 hr))
    | some next =>
      simp only [hz,if_false] at hsegment
      obtain ⟨hnext,hexpected⟩ := continue_matches s next hr
      refine ⟨n,continued p,referenceBase,hn,hsegment,hp.1,hp.2.1,hp.2.2.1,
        hi.1,hi.2.1,hname.1,hname.2.1,?_⟩
      simp only [hr]
      exact ⟨trivial,hnext,hexpected,hp.2.2.2.1⟩

end Shared.PNP.Record285.PythonControlReferenceActionMeaning
