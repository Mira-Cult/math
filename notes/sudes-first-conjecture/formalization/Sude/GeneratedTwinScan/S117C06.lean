import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15690)) 246153261 246186029 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 246153261 246186029).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15690 246153261 246186029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15691)) 246186029 246218797 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 246186029 246218797).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15691 246186029 246218797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15692)) 246218797 246251565 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 246218797 246251565).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15692 246218797 246251565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15693)) 246251565 246284333 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 246251565 246284333).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15693 246251565 246284333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 246153261 246218797).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 246153261 ≤ 246186029)
    (by decide : 246186029 ≤ 246218797) block0 block1

theorem join_0_1 : (twinPrimeSegment 246218797 246284333).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 246218797 ≤ 246251565)
    (by decide : 246251565 ≤ 246284333) block2 block3

theorem join_1_0 : (twinPrimeSegment 246153261 246284333).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 246153261 ≤ 246218797)
    (by decide : 246218797 ≤ 246284333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 246153261 246284333).card = 474 := join_1_0

end S117C06
end Sude.GeneratedTwinScan
