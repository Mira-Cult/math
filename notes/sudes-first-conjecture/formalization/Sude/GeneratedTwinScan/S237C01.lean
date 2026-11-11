import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22297)) 497156141 497188909 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 497156141 497188909).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22297 497156141 497188909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22298)) 497188909 497221677 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 497188909 497221677).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22298 497188909 497221677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22299)) 497221677 497254445 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 497221677 497254445).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22299 497221677 497254445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22299)) 497254445 497287213 = 87 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 497254445 497287213).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22299 497254445 497287213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 497156141 497221677).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 497156141 ≤ 497188909)
    (by decide : 497188909 ≤ 497221677) block0 block1

theorem join_0_1 : (twinPrimeSegment 497221677 497287213).card = 183 := by
  simpa using combineTwinPrimeSegments (by decide : 497221677 ≤ 497254445)
    (by decide : 497254445 ≤ 497287213) block2 block3

theorem join_1_0 : (twinPrimeSegment 497156141 497287213).card = 390 := by
  simpa using combineTwinPrimeSegments (by decide : 497156141 ≤ 497221677)
    (by decide : 497221677 ≤ 497287213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 497156141 497287213).card = 390 := join_1_0

end S237C01
end Sude.GeneratedTwinScan
