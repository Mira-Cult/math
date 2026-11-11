import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13347)) 178126893 178159661 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 178126893 178159661).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13347 178126893 178159661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13348)) 178159661 178192429 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 178159661 178192429).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13348 178159661 178192429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13350)) 178192429 178225197 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 178192429 178225197).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13350 178192429 178225197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13351)) 178225197 178257965 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 178225197 178257965).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13351 178225197 178257965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 178126893 178192429).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 178126893 ≤ 178159661)
    (by decide : 178159661 ≤ 178192429) block0 block1

theorem join_0_1 : (twinPrimeSegment 178192429 178257965).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 178192429 ≤ 178225197)
    (by decide : 178225197 ≤ 178257965) block2 block3

theorem join_1_0 : (twinPrimeSegment 178126893 178257965).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 178126893 ≤ 178192429)
    (by decide : 178192429 ≤ 178257965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 178126893 178257965).card = 496 := join_1_0

end S084C15
end Sude.GeneratedTwinScan
