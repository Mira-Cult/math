import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19110)) 365166637 365199405 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 365166637 365199405).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19110 365166637 365199405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19111)) 365199405 365232173 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 365199405 365232173).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19111 365199405 365232173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19111)) 365232173 365264941 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 365232173 365264941).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19111 365232173 365264941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19112)) 365264941 365297709 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 365264941 365297709).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19112 365264941 365297709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 365166637 365232173).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 365166637 ≤ 365199405)
    (by decide : 365199405 ≤ 365232173) block0 block1

theorem join_0_1 : (twinPrimeSegment 365232173 365297709).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 365232173 ≤ 365264941)
    (by decide : 365264941 ≤ 365297709) block2 block3

theorem join_1_0 : (twinPrimeSegment 365166637 365297709).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 365166637 ≤ 365232173)
    (by decide : 365232173 ≤ 365297709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 365166637 365297709).card = 429 := join_1_0

end S174C02
end Sude.GeneratedTwinScan
