import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22019)) 484835373 484868141 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 484835373 484868141).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22019 484835373 484868141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22020)) 484868141 484900909 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 484868141 484900909).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22020 484868141 484900909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22021)) 484900909 484933677 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 484900909 484933677).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22021 484900909 484933677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22021)) 484933677 484966445 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 484933677 484966445).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22021 484933677 484966445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 484835373 484900909).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 484835373 ≤ 484868141)
    (by decide : 484868141 ≤ 484900909) block0 block1

theorem join_0_1 : (twinPrimeSegment 484900909 484966445).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 484900909 ≤ 484933677)
    (by decide : 484933677 ≤ 484966445) block2 block3

theorem join_1_0 : (twinPrimeSegment 484835373 484966445).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 484835373 ≤ 484900909)
    (by decide : 484900909 ≤ 484966445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 484835373 484966445).card = 418 := join_1_0

end S231C03
end Sude.GeneratedTwinScan
