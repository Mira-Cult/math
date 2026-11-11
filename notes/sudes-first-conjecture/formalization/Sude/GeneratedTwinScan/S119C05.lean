import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15819)) 250216493 250249261 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 250216493 250249261).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15819 250216493 250249261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15820)) 250249261 250282029 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 250249261 250282029).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15820 250249261 250282029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15821)) 250282029 250314797 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 250282029 250314797).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15821 250282029 250314797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15822)) 250314797 250347565 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 250314797 250347565).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15822 250314797 250347565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 250216493 250282029).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 250216493 ≤ 250249261)
    (by decide : 250249261 ≤ 250282029) block0 block1

theorem join_0_1 : (twinPrimeSegment 250282029 250347565).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 250282029 ≤ 250314797)
    (by decide : 250314797 ≤ 250347565) block2 block3

theorem join_1_0 : (twinPrimeSegment 250216493 250347565).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 250216493 ≤ 250282029)
    (by decide : 250282029 ≤ 250347565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 250216493 250347565).card = 475 := join_1_0

end S119C05
end Sude.GeneratedTwinScan
