import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20547)) 422182957 422215725 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 422182957 422215725).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20547 422182957 422215725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20548)) 422215725 422248493 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 422215725 422248493).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20548 422215725 422248493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20549)) 422248493 422281261 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 422248493 422281261).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20549 422248493 422281261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20550)) 422281261 422314029 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 422281261 422314029).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20550 422281261 422314029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 422182957 422248493).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 422182957 ≤ 422215725)
    (by decide : 422215725 ≤ 422248493) block0 block1

theorem join_0_1 : (twinPrimeSegment 422248493 422314029).card = 187 := by
  simpa using combineTwinPrimeSegments (by decide : 422248493 ≤ 422281261)
    (by decide : 422281261 ≤ 422314029) block2 block3

theorem join_1_0 : (twinPrimeSegment 422182957 422314029).card = 404 := by
  simpa using combineTwinPrimeSegments (by decide : 422182957 ≤ 422248493)
    (by decide : 422248493 ≤ 422314029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 422182957 422314029).card = 404 := join_1_0

end S201C05
end Sude.GeneratedTwinScan
