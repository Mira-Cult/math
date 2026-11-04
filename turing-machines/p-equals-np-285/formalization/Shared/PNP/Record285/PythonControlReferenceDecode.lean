import Shared.PNP.Record285.PythonControlGuardedDecode

/-! The complete typed reference decoder executes the same silent, full-store
segment as the candidate decoder, without a boundary premise. This does not
yet cover reference branch selection or the full unbounded controller. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceDecode
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControlSkip
open Shared.PNP.Record285.PythonControlDecode
open Shared.PNP.Record285.PythonControlGuarded
open Shared.PNP.Record285.PythonControlGuardedDecode
open Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonControlRelocationTransfer

theorem reference_record_terminates (s : Store) :
    let stream := skipUnary (s "state") (s "digit")
    ∃ n, 0 < n ∧ Silent (referenceEntry s)
      (referenceExit (storeOf s (popUnary stream).2
        (PythonInlineDecoder.bumpN (popUnary stream).1 ⟨false,false,0⟩))) n := by
  let stream := skipUnary (s "state") (s "digit")
  let out := storeOf s (popUnary stream).2
    (PythonInlineDecoder.bumpN (popUnary stream).1 ⟨false,false,0⟩)
  obtain ⟨n,hn,hguard⟩ := PythonControlGuardedDecode.candidate_record_terminates s
  refine ⟨n,hn,?_⟩
  apply PythonControlRelocationCandidate.transfer_segment s out n
  · simpa [candidateEntry,candidateExit,candidateBase,context,stream,out] using hguard.1
  · simpa [candidateEntry,candidateBase,context] using hguard.2

theorem reference_record_fields (s : Store) :
    let stream := skipUnary (s "state") (s "digit")
    let record := popUnary stream
    ∃ n out, 0 < n ∧ Silent (referenceEntry s) (referenceExit out) n ∧
      out "write" = record.1%2 ∧ out "direction" = (record.1/2)%2 ∧
      out "state" = record.1/4 ∧ out "digit" = record.2 ∧
      ∀ key, key ≠ "write" → key ≠ "direction" → key ≠ "state" → key ≠ "digit" → out key = s key := by
  let stream := skipUnary (s "state") (s "digit")
  let d := PythonInlineDecoder.bumpN (popUnary stream).1 ⟨false,false,0⟩
  let out := storeOf s (popUnary stream).2 d
  obtain ⟨n,hn,hsegment⟩ := reference_record_terminates s
  have hf := PythonInlineDecoder.read_fields stream
  rw [PythonInlineDecoder.read_correct] at hf
  change (if d.write then 1 else 0) = (popUnary stream).1%2 ∧
    (if d.direction then 1 else 0) = ((popUnary stream).1/2)%2 ∧
    d.state = (popUnary stream).1/4 ∧ _ at hf
  refine ⟨n,out,hn,hsegment,?_,?_,?_,?_,?_⟩
  · simpa [out,storeOf,put] using hf.1
  · simpa [out,storeOf,put] using hf.2.1
  · simpa [out,storeOf,put] using hf.2.2.1
  · simp [out,storeOf,put,stream]
  · intro key hw hd hs hdi
    simp [out,storeOf,put,hw,hd,hs,hdi]


end Shared.PNP.Record285.PythonControlReferenceDecode
