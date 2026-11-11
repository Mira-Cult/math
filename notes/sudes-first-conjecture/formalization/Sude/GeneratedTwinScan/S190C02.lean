import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19968)) 398721069 398753837 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 398721069 398753837).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19968 398721069 398753837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19969)) 398753837 398786605 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 398753837 398786605).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19969 398753837 398786605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19970)) 398786605 398819373 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 398786605 398819373).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19970 398786605 398819373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19971)) 398819373 398852141 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 398819373 398852141).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19971 398819373 398852141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 398721069 398786605).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 398721069 ≤ 398753837)
    (by decide : 398753837 ≤ 398786605) block0 block1

theorem join_0_1 : (twinPrimeSegment 398786605 398852141).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 398786605 ≤ 398819373)
    (by decide : 398819373 ≤ 398852141) block2 block3

theorem join_1_0 : (twinPrimeSegment 398721069 398852141).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 398721069 ≤ 398786605)
    (by decide : 398786605 ≤ 398852141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 398721069 398852141).card = 427 := join_1_0

end S190C02
end Sude.GeneratedTwinScan
