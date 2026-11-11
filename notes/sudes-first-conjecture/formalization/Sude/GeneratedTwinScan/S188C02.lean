import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19863)) 394526765 394559533 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 394526765 394559533).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19863 394526765 394559533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19864)) 394559533 394592301 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 394559533 394592301).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19864 394559533 394592301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19865)) 394592301 394625069 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 394592301 394625069).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19865 394592301 394625069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19865)) 394625069 394657837 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 394625069 394657837).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19865 394625069 394657837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 394526765 394592301).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 394526765 ≤ 394559533)
    (by decide : 394559533 ≤ 394592301) block0 block1

theorem join_0_1 : (twinPrimeSegment 394592301 394657837).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 394592301 ≤ 394625069)
    (by decide : 394625069 ≤ 394657837) block2 block3

theorem join_1_0 : (twinPrimeSegment 394526765 394657837).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 394526765 ≤ 394592301)
    (by decide : 394592301 ≤ 394657837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 394526765 394657837).card = 420 := join_1_0

end S188C02
end Sude.GeneratedTwinScan
