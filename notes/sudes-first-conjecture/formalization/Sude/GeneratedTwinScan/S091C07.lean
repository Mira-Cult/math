import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13848)) 191758381 191791149 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 191758381 191791149).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13848 191758381 191791149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13850)) 191791149 191823917 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 191791149 191823917).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13850 191791149 191823917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13851)) 191823917 191856685 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 191823917 191856685).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13851 191823917 191856685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13852)) 191856685 191889453 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 191856685 191889453).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13852 191856685 191889453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 191758381 191823917).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 191758381 ≤ 191791149)
    (by decide : 191791149 ≤ 191823917) block0 block1

theorem join_0_1 : (twinPrimeSegment 191823917 191889453).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 191823917 ≤ 191856685)
    (by decide : 191856685 ≤ 191889453) block2 block3

theorem join_1_0 : (twinPrimeSegment 191758381 191889453).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 191758381 ≤ 191823917)
    (by decide : 191823917 ≤ 191889453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 191758381 191889453).card = 510 := join_1_0

end S091C07
end Sude.GeneratedTwinScan
