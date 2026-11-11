import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21468)) 460849197 460881965 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 460849197 460881965).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21468 460849197 460881965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21468)) 460881965 460914733 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 460881965 460914733).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21468 460881965 460914733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21469)) 460914733 460947501 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 460914733 460947501).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21469 460914733 460947501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21470)) 460947501 460980269 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 460947501 460980269).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21470 460947501 460980269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 460849197 460914733).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 460849197 ≤ 460881965)
    (by decide : 460881965 ≤ 460914733) block0 block1

theorem join_0_1 : (twinPrimeSegment 460914733 460980269).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 460914733 ≤ 460947501)
    (by decide : 460947501 ≤ 460980269) block2 block3

theorem join_1_0 : (twinPrimeSegment 460849197 460980269).card = 411 := by
  simpa using combineTwinPrimeSegments (by decide : 460849197 ≤ 460914733)
    (by decide : 460914733 ≤ 460980269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 460849197 460980269).card = 411 := join_1_0

end S219C12
end Sude.GeneratedTwinScan
