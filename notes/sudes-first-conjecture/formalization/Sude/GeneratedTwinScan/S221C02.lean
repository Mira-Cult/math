import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21535)) 463732781 463765549 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 463732781 463765549).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21535 463732781 463765549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21535)) 463765549 463798317 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 463765549 463798317).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21535 463765549 463798317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21536)) 463798317 463831085 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 463798317 463831085).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21536 463798317 463831085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21537)) 463831085 463863853 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 463831085 463863853).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21537 463831085 463863853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 463732781 463798317).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 463732781 ≤ 463765549)
    (by decide : 463765549 ≤ 463798317) block0 block1

theorem join_0_1 : (twinPrimeSegment 463798317 463863853).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 463798317 ≤ 463831085)
    (by decide : 463831085 ≤ 463863853) block2 block3

theorem join_1_0 : (twinPrimeSegment 463732781 463863853).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 463732781 ≤ 463798317)
    (by decide : 463798317 ≤ 463863853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 463732781 463863853).card = 440 := join_1_0

end S221C02
end Sude.GeneratedTwinScan
