import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17166)) 294649901 294682669 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 294649901 294682669).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17166 294649901 294682669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17167)) 294682669 294715437 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 294682669 294715437).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17167 294682669 294715437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17168)) 294715437 294748205 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 294715437 294748205).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17168 294715437 294748205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17169)) 294748205 294780973 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 294748205 294780973).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17169 294748205 294780973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 294649901 294715437).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 294649901 ≤ 294682669)
    (by decide : 294682669 ≤ 294715437) block0 block1

theorem join_0_1 : (twinPrimeSegment 294715437 294780973).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 294715437 ≤ 294748205)
    (by decide : 294748205 ≤ 294780973) block2 block3

theorem join_1_0 : (twinPrimeSegment 294649901 294780973).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 294649901 ≤ 294715437)
    (by decide : 294715437 ≤ 294780973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 294649901 294780973).card = 445 := join_1_0

end S140C08
end Sude.GeneratedTwinScan
