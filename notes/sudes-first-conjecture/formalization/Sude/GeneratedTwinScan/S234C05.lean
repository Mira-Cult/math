import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22168)) 491388973 491421741 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 491388973 491421741).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22168 491388973 491421741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22168)) 491421741 491454509 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 491421741 491454509).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22168 491421741 491454509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22169)) 491454509 491487277 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 491454509 491487277).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22169 491454509 491487277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22170)) 491487277 491520045 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 491487277 491520045).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22170 491487277 491520045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 491388973 491454509).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 491388973 ≤ 491421741)
    (by decide : 491421741 ≤ 491454509) block0 block1

theorem join_0_1 : (twinPrimeSegment 491454509 491520045).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 491454509 ≤ 491487277)
    (by decide : 491487277 ≤ 491520045) block2 block3

theorem join_1_0 : (twinPrimeSegment 491388973 491520045).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 491388973 ≤ 491454509)
    (by decide : 491454509 ≤ 491520045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 491388973 491520045).card = 442 := join_1_0

end S234C05
end Sude.GeneratedTwinScan
