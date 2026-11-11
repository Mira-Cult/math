import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21477)) 461242413 461275181 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 461242413 461275181).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21477 461242413 461275181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21478)) 461275181 461307949 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 461275181 461307949).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21478 461275181 461307949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21478)) 461307949 461340717 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 461307949 461340717).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21478 461307949 461340717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21479)) 461340717 461373485 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 461340717 461373485).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21479 461340717 461373485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 461242413 461307949).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 461242413 ≤ 461275181)
    (by decide : 461275181 ≤ 461307949) block0 block1

theorem join_0_1 : (twinPrimeSegment 461307949 461373485).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 461307949 ≤ 461340717)
    (by decide : 461340717 ≤ 461373485) block2 block3

theorem join_1_0 : (twinPrimeSegment 461242413 461373485).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 461242413 ≤ 461307949)
    (by decide : 461307949 ≤ 461373485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 461242413 461373485).card = 429 := join_1_0

end S219C15
end Sude.GeneratedTwinScan
