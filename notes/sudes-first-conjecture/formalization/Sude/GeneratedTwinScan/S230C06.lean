import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21980)) 483131437 483164205 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 483131437 483164205).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21980 483131437 483164205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21981)) 483164205 483196973 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 483164205 483196973).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21981 483164205 483196973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21982)) 483196973 483229741 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 483196973 483229741).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21982 483196973 483229741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21983)) 483229741 483262509 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 483229741 483262509).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21983 483229741 483262509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 483131437 483196973).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 483131437 ≤ 483164205)
    (by decide : 483164205 ≤ 483196973) block0 block1

theorem join_0_1 : (twinPrimeSegment 483196973 483262509).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 483196973 ≤ 483229741)
    (by decide : 483229741 ≤ 483262509) block2 block3

theorem join_1_0 : (twinPrimeSegment 483131437 483262509).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 483131437 ≤ 483196973)
    (by decide : 483196973 ≤ 483262509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 483131437 483262509).card = 435 := join_1_0

end S230C06
end Sude.GeneratedTwinScan
