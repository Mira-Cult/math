import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16098)) 259129389 259162157 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 259129389 259162157).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16098 259129389 259162157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16099)) 259162157 259194925 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 259162157 259194925).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16099 259162157 259194925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16100)) 259194925 259227693 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 259194925 259227693).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16100 259194925 259227693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16101)) 259227693 259260461 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 259227693 259260461).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16101 259227693 259260461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 259129389 259194925).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 259129389 ≤ 259162157)
    (by decide : 259162157 ≤ 259194925) block0 block1

theorem join_0_1 : (twinPrimeSegment 259194925 259260461).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 259194925 ≤ 259227693)
    (by decide : 259227693 ≤ 259260461) block2 block3

theorem join_1_0 : (twinPrimeSegment 259129389 259260461).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 259129389 ≤ 259194925)
    (by decide : 259194925 ≤ 259260461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 259129389 259260461).card = 484 := join_1_0

end S123C09
end Sude.GeneratedTwinScan
