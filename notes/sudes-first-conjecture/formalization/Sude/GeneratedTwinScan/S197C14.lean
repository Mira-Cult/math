import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20371)) 414973997 415006765 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 414973997 415006765).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20371 414973997 415006765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20372)) 415006765 415039533 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 415006765 415039533).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20372 415006765 415039533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20373)) 415039533 415072301 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 415039533 415072301).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20373 415039533 415072301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20374)) 415072301 415105069 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 415072301 415105069).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20374 415072301 415105069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 414973997 415039533).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 414973997 ≤ 415006765)
    (by decide : 415006765 ≤ 415039533) block0 block1

theorem join_0_1 : (twinPrimeSegment 415039533 415105069).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 415039533 ≤ 415072301)
    (by decide : 415072301 ≤ 415105069) block2 block3

theorem join_1_0 : (twinPrimeSegment 414973997 415105069).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 414973997 ≤ 415039533)
    (by decide : 415039533 ≤ 415105069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 414973997 415105069).card = 421 := join_1_0

end S197C14
end Sude.GeneratedTwinScan
