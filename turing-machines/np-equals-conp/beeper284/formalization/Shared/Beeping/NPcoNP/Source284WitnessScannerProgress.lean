import Shared.Beeping.NPcoNP.Source284WitnessScannerRun
import Shared.Beeping.NPcoNP.Source284WitnessInputBound

/-! Total finite progress for the concrete four-logical-state source
witness scanner. Every natural certificate has a virtual-zero-terminated
frame. This is a source-evaluator result; it is not the full witness decoder,
cutoff guard, canonical bit-time proof, or physical beeper refinement. -/

namespace Shared.Beeping.NPcoNP.Source284WitnessScannerProgress

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284WitnessScanner
open Shared.Beeping.NPcoNP.Source284WitnessScannerRun
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic
open Shared.Beeping.NPcoNP.Source284Parser
open Shared.Beeping.NPcoNP.Source284Relative

/-- Every natural certificate reaches the scanner's continuing boundary in
positive finite time. The frame length is the source parser's actual length,
and the run is bounded linearly by the certificate's binary size. The
existential decomposition is a proof of progress, not runtime oracle data. -/
theorem scanner_total_progress (input certificate tail : Nat) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = certificate ∧
      w.length = Source284Parser.length certificate ∧
      0 < 2*w.length+2 ∧
      2*w.length+2 ≤ 2*Nat.size certificate+2 ∧
      Source284Relative.run (encode 4 table tail)
        (Source284Relative.initial input certificate) (2*w.length+2) =
          ⟨2*pushPairs input w, suffix, 7⟩ := by
  obtain ⟨w, suffix, hw⟩ := encodeFrame_surjective certificate
  have hlen : Source284Parser.length certificate = w.length := by
    rw [← hw]
    simp [Source284Parser.length, parse_encodeFrame]
  have hsize : w.length ≤ Nat.size certificate := by
    rw [← hlen]
    exact Shared.Beeping.NPcoNP.Source284WitnessInputBound.parsed_length_le_size certificate
  refine ⟨w, suffix, hw, hlen.symm, by omega, by omega, ?_⟩
  rw [← hw]
  exact source_scan_frame w input suffix tail

end Shared.Beeping.NPcoNP.Source284WitnessScannerProgress
