import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21523)) 463208493 463241261 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 463208493 463241261).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21523 463208493 463241261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21523)) 463241261 463274029 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 463241261 463274029).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21523 463241261 463274029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21524)) 463274029 463306797 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 463274029 463306797).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21524 463274029 463306797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21525)) 463306797 463339565 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 463306797 463339565).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21525 463306797 463339565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 463208493 463274029).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 463208493 ≤ 463241261)
    (by decide : 463241261 ≤ 463274029) block0 block1

theorem join_0_1 : (twinPrimeSegment 463274029 463339565).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 463274029 ≤ 463306797)
    (by decide : 463306797 ≤ 463339565) block2 block3

theorem join_1_0 : (twinPrimeSegment 463208493 463339565).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 463208493 ≤ 463274029)
    (by decide : 463274029 ≤ 463339565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 463208493 463339565).card = 427 := join_1_0

end S220C14
end Sude.GeneratedTwinScan
