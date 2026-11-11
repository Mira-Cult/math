import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12485)) 155844653 155877421 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 155844653 155877421).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12485 155844653 155877421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12486)) 155877421 155910189 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 155877421 155910189).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12486 155877421 155910189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12487)) 155910189 155942957 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 155910189 155942957).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12487 155910189 155942957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12489)) 155942957 155975725 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 155942957 155975725).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12489 155942957 155975725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 155844653 155910189).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 155844653 ≤ 155877421)
    (by decide : 155877421 ≤ 155910189) block0 block1

theorem join_0_1 : (twinPrimeSegment 155910189 155975725).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 155910189 ≤ 155942957)
    (by decide : 155942957 ≤ 155975725) block2 block3

theorem join_1_0 : (twinPrimeSegment 155844653 155975725).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 155844653 ≤ 155910189)
    (by decide : 155910189 ≤ 155975725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 155844653 155975725).card = 496 := join_1_0

end S074C05
end Sude.GeneratedTwinScan
