import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16304)) 265814061 265846829 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 265814061 265846829).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16304 265814061 265846829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16305)) 265846829 265879597 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 265846829 265879597).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16305 265846829 265879597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16306)) 265879597 265912365 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 265879597 265912365).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16306 265879597 265912365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16307)) 265912365 265945133 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 265912365 265945133).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16307 265912365 265945133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 265814061 265879597).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 265814061 ≤ 265846829)
    (by decide : 265846829 ≤ 265879597) block0 block1

theorem join_0_1 : (twinPrimeSegment 265879597 265945133).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 265879597 ≤ 265912365)
    (by decide : 265912365 ≤ 265945133) block2 block3

theorem join_1_0 : (twinPrimeSegment 265814061 265945133).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 265814061 ≤ 265879597)
    (by decide : 265879597 ≤ 265945133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 265814061 265945133).card = 476 := join_1_0

end S126C12
end Sude.GeneratedTwinScan
