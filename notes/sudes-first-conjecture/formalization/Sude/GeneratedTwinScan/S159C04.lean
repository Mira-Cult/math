import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18275)) 333971501 334004269 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 333971501 334004269).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18275 333971501 334004269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18276)) 334004269 334037037 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 334004269 334037037).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18276 334004269 334037037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18277)) 334037037 334069805 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 334037037 334069805).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18277 334037037 334069805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18278)) 334069805 334102573 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 334069805 334102573).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18278 334069805 334102573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 333971501 334037037).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 333971501 ≤ 334004269)
    (by decide : 334004269 ≤ 334037037) block0 block1

theorem join_0_1 : (twinPrimeSegment 334037037 334102573).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 334037037 ≤ 334069805)
    (by decide : 334069805 ≤ 334102573) block2 block3

theorem join_1_0 : (twinPrimeSegment 333971501 334102573).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 333971501 ≤ 334037037)
    (by decide : 334037037 ≤ 334102573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 333971501 334102573).card = 458 := join_1_0

end S159C04
end Sude.GeneratedTwinScan
