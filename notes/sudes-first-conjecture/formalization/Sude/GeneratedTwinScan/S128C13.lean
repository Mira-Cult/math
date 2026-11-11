import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16436)) 270139437 270172205 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 270139437 270172205).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16436 270139437 270172205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16437)) 270172205 270204973 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 270172205 270204973).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16437 270172205 270204973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16438)) 270204973 270237741 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 270204973 270237741).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16438 270204973 270237741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16439)) 270237741 270270509 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 270237741 270270509).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16439 270237741 270270509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 270139437 270204973).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 270139437 ≤ 270172205)
    (by decide : 270172205 ≤ 270204973) block0 block1

theorem join_0_1 : (twinPrimeSegment 270204973 270270509).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 270204973 ≤ 270237741)
    (by decide : 270237741 ≤ 270270509) block2 block3

theorem join_1_0 : (twinPrimeSegment 270139437 270270509).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 270139437 ≤ 270204973)
    (by decide : 270204973 ≤ 270270509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 270139437 270270509).card = 479 := join_1_0

end S128C13
end Sude.GeneratedTwinScan
