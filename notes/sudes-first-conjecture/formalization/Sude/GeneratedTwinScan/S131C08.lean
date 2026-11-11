import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16607)) 275775533 275808301 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 275775533 275808301).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16607 275775533 275808301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16608)) 275808301 275841069 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 275808301 275841069).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16608 275808301 275841069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16609)) 275841069 275873837 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 275841069 275873837).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16609 275841069 275873837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16610)) 275873837 275906605 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 275873837 275906605).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16610 275873837 275906605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 275775533 275841069).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 275775533 ≤ 275808301)
    (by decide : 275808301 ≤ 275841069) block0 block1

theorem join_0_1 : (twinPrimeSegment 275841069 275906605).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 275841069 ≤ 275873837)
    (by decide : 275873837 ≤ 275906605) block2 block3

theorem join_1_0 : (twinPrimeSegment 275775533 275906605).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 275775533 ≤ 275841069)
    (by decide : 275841069 ≤ 275906605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 275775533 275906605).card = 455 := join_1_0

end S131C08
end Sude.GeneratedTwinScan
