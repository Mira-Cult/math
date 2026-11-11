import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21160)) 447741997 447774765 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 447741997 447774765).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21160 447741997 447774765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21161)) 447774765 447807533 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 447774765 447807533).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21161 447774765 447807533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21162)) 447807533 447840301 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 447807533 447840301).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21162 447807533 447840301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21163)) 447840301 447873069 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 447840301 447873069).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21163 447840301 447873069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 447741997 447807533).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 447741997 ≤ 447774765)
    (by decide : 447774765 ≤ 447807533) block0 block1

theorem join_0_1 : (twinPrimeSegment 447807533 447873069).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 447807533 ≤ 447840301)
    (by decide : 447840301 ≤ 447873069) block2 block3

theorem join_1_0 : (twinPrimeSegment 447741997 447873069).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 447741997 ≤ 447807533)
    (by decide : 447807533 ≤ 447873069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 447741997 447873069).card = 447 := join_1_0

end S213C08
end Sude.GeneratedTwinScan
