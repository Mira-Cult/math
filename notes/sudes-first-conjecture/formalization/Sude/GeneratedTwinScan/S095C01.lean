import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14120)) 199360557 199393325 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 199360557 199393325).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14120 199360557 199393325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14121)) 199393325 199426093 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 199393325 199426093).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14121 199393325 199426093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14122)) 199426093 199458861 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 199426093 199458861).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14122 199426093 199458861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14124)) 199458861 199491629 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 199458861 199491629).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14124 199458861 199491629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 199360557 199426093).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 199360557 ≤ 199393325)
    (by decide : 199393325 ≤ 199426093) block0 block1

theorem join_0_1 : (twinPrimeSegment 199426093 199491629).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 199426093 ≤ 199458861)
    (by decide : 199458861 ≤ 199491629) block2 block3

theorem join_1_0 : (twinPrimeSegment 199360557 199491629).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 199360557 ≤ 199426093)
    (by decide : 199426093 ≤ 199491629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 199360557 199491629).card = 480 := join_1_0

end S095C01
end Sude.GeneratedTwinScan
