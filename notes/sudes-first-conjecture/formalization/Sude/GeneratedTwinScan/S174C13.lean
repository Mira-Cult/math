import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19147)) 366608429 366641197 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 366608429 366641197).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19147 366608429 366641197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19148)) 366641197 366673965 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 366641197 366673965).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19148 366641197 366673965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19149)) 366673965 366706733 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 366673965 366706733).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19149 366673965 366706733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19150)) 366706733 366739501 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 366706733 366739501).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19150 366706733 366739501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 366608429 366673965).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 366608429 ≤ 366641197)
    (by decide : 366641197 ≤ 366673965) block0 block1

theorem join_0_1 : (twinPrimeSegment 366673965 366739501).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 366673965 ≤ 366706733)
    (by decide : 366706733 ≤ 366739501) block2 block3

theorem join_1_0 : (twinPrimeSegment 366608429 366739501).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 366608429 ≤ 366673965)
    (by decide : 366673965 ≤ 366739501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 366608429 366739501).card = 427 := join_1_0

end S174C13
end Sude.GeneratedTwinScan
