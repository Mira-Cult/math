import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21526)) 463339565 463372333 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 463339565 463372333).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21526 463339565 463372333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21526)) 463372333 463405101 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 463372333 463405101).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21526 463372333 463405101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21527)) 463405101 463437869 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 463405101 463437869).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21527 463405101 463437869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21528)) 463437869 463470637 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 463437869 463470637).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21528 463437869 463470637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 463339565 463405101).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 463339565 ≤ 463372333)
    (by decide : 463372333 ≤ 463405101) block0 block1

theorem join_0_1 : (twinPrimeSegment 463405101 463470637).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 463405101 ≤ 463437869)
    (by decide : 463437869 ≤ 463470637) block2 block3

theorem join_1_0 : (twinPrimeSegment 463339565 463470637).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 463339565 ≤ 463405101)
    (by decide : 463405101 ≤ 463470637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 463339565 463470637).card = 440 := join_1_0

end S220C15
end Sude.GeneratedTwinScan
