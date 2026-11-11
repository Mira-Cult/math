import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12816)) 164233261 164266029 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 164233261 164266029).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12816 164233261 164266029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12817)) 164266029 164298797 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 164266029 164298797).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12817 164266029 164298797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12819)) 164298797 164331565 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 164298797 164331565).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12819 164298797 164331565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12820)) 164331565 164364333 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 164331565 164364333).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12820 164331565 164364333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 164233261 164298797).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 164233261 ≤ 164266029)
    (by decide : 164266029 ≤ 164298797) block0 block1

theorem join_0_1 : (twinPrimeSegment 164298797 164364333).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 164298797 ≤ 164331565)
    (by decide : 164331565 ≤ 164364333) block2 block3

theorem join_1_0 : (twinPrimeSegment 164233261 164364333).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 164233261 ≤ 164298797)
    (by decide : 164298797 ≤ 164364333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 164233261 164364333).card = 473 := join_1_0

end S078C05
end Sude.GeneratedTwinScan
