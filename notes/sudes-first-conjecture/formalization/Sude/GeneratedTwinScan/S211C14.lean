import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21080)) 444334125 444366893 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 444334125 444366893).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21080 444334125 444366893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21080)) 444366893 444399661 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 444366893 444399661).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21080 444366893 444399661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21081)) 444399661 444432429 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 444399661 444432429).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21081 444399661 444432429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21082)) 444432429 444465197 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 444432429 444465197).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21082 444432429 444465197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 444334125 444399661).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 444334125 ≤ 444366893)
    (by decide : 444366893 ≤ 444399661) block0 block1

theorem join_0_1 : (twinPrimeSegment 444399661 444465197).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 444399661 ≤ 444432429)
    (by decide : 444432429 ≤ 444465197) block2 block3

theorem join_1_0 : (twinPrimeSegment 444334125 444465197).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 444334125 ≤ 444399661)
    (by decide : 444399661 ≤ 444465197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 444334125 444465197).card = 440 := join_1_0

end S211C14
end Sude.GeneratedTwinScan
