import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13440)) 180617261 180650029 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 180617261 180650029).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13440 180617261 180650029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13441)) 180650029 180682797 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 180650029 180682797).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13441 180650029 180682797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13443)) 180682797 180715565 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 180682797 180715565).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13443 180682797 180715565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13444)) 180715565 180748333 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 180715565 180748333).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13444 180715565 180748333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 180617261 180682797).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 180617261 ≤ 180650029)
    (by decide : 180650029 ≤ 180682797) block0 block1

theorem join_0_1 : (twinPrimeSegment 180682797 180748333).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 180682797 ≤ 180715565)
    (by decide : 180715565 ≤ 180748333) block2 block3

theorem join_1_0 : (twinPrimeSegment 180617261 180748333).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 180617261 ≤ 180682797)
    (by decide : 180682797 ≤ 180748333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 180617261 180748333).card = 496 := join_1_0

end S086C02
end Sude.GeneratedTwinScan
