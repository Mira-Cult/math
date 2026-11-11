import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16943)) 287047725 287080493 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 287047725 287080493).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16943 287047725 287080493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16944)) 287080493 287113261 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 287080493 287113261).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16944 287080493 287113261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16945)) 287113261 287146029 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 287113261 287146029).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16945 287113261 287146029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16946)) 287146029 287178797 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 287146029 287178797).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16946 287146029 287178797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 287047725 287113261).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 287047725 ≤ 287080493)
    (by decide : 287080493 ≤ 287113261) block0 block1

theorem join_0_1 : (twinPrimeSegment 287113261 287178797).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 287113261 ≤ 287146029)
    (by decide : 287146029 ≤ 287178797) block2 block3

theorem join_1_0 : (twinPrimeSegment 287047725 287178797).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 287047725 ≤ 287113261)
    (by decide : 287113261 ≤ 287178797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 287047725 287178797).card = 470 := join_1_0

end S136C14
end Sude.GeneratedTwinScan
