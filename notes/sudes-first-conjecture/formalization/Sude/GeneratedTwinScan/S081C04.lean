import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13054)) 170393645 170426413 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 170393645 170426413).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13054 170393645 170426413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13056)) 170426413 170459181 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 170426413 170459181).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13056 170426413 170459181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13057)) 170459181 170491949 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 170459181 170491949).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13057 170459181 170491949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13058)) 170491949 170524717 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 170491949 170524717).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13058 170491949 170524717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 170393645 170459181).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 170393645 ≤ 170426413)
    (by decide : 170426413 ≤ 170459181) block0 block1

theorem join_0_1 : (twinPrimeSegment 170459181 170524717).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 170459181 ≤ 170491949)
    (by decide : 170491949 ≤ 170524717) block2 block3

theorem join_1_0 : (twinPrimeSegment 170393645 170524717).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 170393645 ≤ 170459181)
    (by decide : 170459181 ≤ 170524717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 170393645 170524717).card = 484 := join_1_0

end S081C04
end Sude.GeneratedTwinScan
