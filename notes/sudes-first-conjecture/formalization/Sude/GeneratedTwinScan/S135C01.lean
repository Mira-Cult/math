import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16830)) 283246637 283279405 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 283246637 283279405).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16830 283246637 283279405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16831)) 283279405 283312173 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 283279405 283312173).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16831 283279405 283312173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16832)) 283312173 283344941 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 283312173 283344941).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16832 283312173 283344941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16833)) 283344941 283377709 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 283344941 283377709).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16833 283344941 283377709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 283246637 283312173).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 283246637 ≤ 283279405)
    (by decide : 283279405 ≤ 283312173) block0 block1

theorem join_0_1 : (twinPrimeSegment 283312173 283377709).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 283312173 ≤ 283344941)
    (by decide : 283344941 ≤ 283377709) block2 block3

theorem join_1_0 : (twinPrimeSegment 283246637 283377709).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 283246637 ≤ 283312173)
    (by decide : 283312173 ≤ 283377709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 283246637 283377709).card = 457 := join_1_0

end S135C01
end Sude.GeneratedTwinScan
