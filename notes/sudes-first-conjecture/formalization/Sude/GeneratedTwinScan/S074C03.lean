import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12474)) 155582509 155615277 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 155582509 155615277).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12474 155582509 155615277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12475)) 155615277 155648045 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 155615277 155648045).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12475 155615277 155648045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12477)) 155648045 155680813 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 155648045 155680813).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12477 155648045 155680813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12478)) 155680813 155713581 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 155680813 155713581).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12478 155680813 155713581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 155582509 155648045).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 155582509 ≤ 155615277)
    (by decide : 155615277 ≤ 155648045) block0 block1

theorem join_0_1 : (twinPrimeSegment 155648045 155713581).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 155648045 ≤ 155680813)
    (by decide : 155680813 ≤ 155713581) block2 block3

theorem join_1_0 : (twinPrimeSegment 155582509 155713581).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 155582509 ≤ 155648045)
    (by decide : 155648045 ≤ 155713581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 155582509 155713581).card = 496 := join_1_0

end S074C03
end Sude.GeneratedTwinScan
