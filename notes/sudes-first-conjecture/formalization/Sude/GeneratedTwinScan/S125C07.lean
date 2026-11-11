import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16220)) 263061549 263094317 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 263061549 263094317).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16220 263061549 263094317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16221)) 263094317 263127085 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 263094317 263127085).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16221 263094317 263127085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16222)) 263127085 263159853 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 263127085 263159853).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16222 263127085 263159853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16223)) 263159853 263192621 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 263159853 263192621).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16223 263159853 263192621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 263061549 263127085).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 263061549 ≤ 263094317)
    (by decide : 263094317 ≤ 263127085) block0 block1

theorem join_0_1 : (twinPrimeSegment 263127085 263192621).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 263127085 ≤ 263159853)
    (by decide : 263159853 ≤ 263192621) block2 block3

theorem join_1_0 : (twinPrimeSegment 263061549 263192621).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 263061549 ≤ 263127085)
    (by decide : 263127085 ≤ 263192621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 263061549 263192621).card = 464 := join_1_0

end S125C07
end Sude.GeneratedTwinScan
