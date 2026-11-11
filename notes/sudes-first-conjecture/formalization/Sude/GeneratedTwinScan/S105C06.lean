import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14866)) 220987437 221020205 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 220987437 221020205).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14866 220987437 221020205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14867)) 221020205 221052973 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 221020205 221052973).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14867 221020205 221052973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14868)) 221052973 221085741 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 221052973 221085741).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14868 221052973 221085741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14870)) 221085741 221118509 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 221085741 221118509).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14870 221085741 221118509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 220987437 221052973).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 220987437 ≤ 221020205)
    (by decide : 221020205 ≤ 221052973) block0 block1

theorem join_0_1 : (twinPrimeSegment 221052973 221118509).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 221052973 ≤ 221085741)
    (by decide : 221085741 ≤ 221118509) block2 block3

theorem join_1_0 : (twinPrimeSegment 220987437 221118509).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 220987437 ≤ 221052973)
    (by decide : 221052973 ≤ 221118509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 220987437 221118509).card = 457 := join_1_0

end S105C06
end Sude.GeneratedTwinScan
