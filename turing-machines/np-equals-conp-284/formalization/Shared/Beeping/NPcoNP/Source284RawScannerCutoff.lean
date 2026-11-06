import Shared.Beeping.NPcoNP.Source284ScannerCutoffBridge
import Shared.Beeping.NPcoNP.Source284Truncation

/-! The finite source scanner observes the witness-window rejection bit
without first physically truncating the certificate. This is a fixed-time
observation: the wrapper must still build and run a variable cutoff counter,
route the observed state, preserve boundaries, and implement the verifier. -/
namespace Shared.Beeping.NPcoNP.Source284RawScannerCutoff

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284BitWindow
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284WitnessScanner
open Shared.Beeping.NPcoNP.Source284ScannerCutoffBridge

/-- The state after this exact finite scan depends on the same low window as
the decoder, even for arbitrary high certificate bits. Nothing erases those
bits, and only the control state is asserted equal. -/
theorem raw_source_reject (limit certificate input tail : Nat) :
    (Source284Relative.run (encode 4 table tail)
      (Source284Relative.initial input certificate) (2*limit+2)).state = 5 ↔
      Shared.Beeping.NPcoNP.Source284WitnessWindow.decode limit certificate = none := by
  have h : Window (2*limit+2) (initial input certificate)
      (initial input (certificate % 2^(2*limit+2))) := by
    exact ⟨rfl, agree_truncate _ _, agree_refl _ _⟩
  have hr := run_window (encode 4 table tail) (2*limit+2) 0 _ _ (by simpa using h)
  rw [hr.1]
  simpa [Shared.Beeping.NPcoNP.Source284WitnessWindow.width] using
    source_window_reject limit certificate input tail

end Shared.Beeping.NPcoNP.Source284RawScannerCutoff
