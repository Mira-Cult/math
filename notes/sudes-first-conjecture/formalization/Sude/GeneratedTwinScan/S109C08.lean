import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15154)) 229638189 229670957 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 229638189 229670957).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15154 229638189 229670957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15155)) 229670957 229703725 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 229670957 229703725).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15155 229670957 229703725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15157)) 229703725 229736493 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 229703725 229736493).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15157 229703725 229736493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15158)) 229736493 229769261 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 229736493 229769261).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15158 229736493 229769261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 229638189 229703725).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 229638189 ≤ 229670957)
    (by decide : 229670957 ≤ 229703725) block0 block1

theorem join_0_1 : (twinPrimeSegment 229703725 229769261).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 229703725 ≤ 229736493)
    (by decide : 229736493 ≤ 229769261) block2 block3

theorem join_1_0 : (twinPrimeSegment 229638189 229769261).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 229638189 ≤ 229703725)
    (by decide : 229703725 ≤ 229769261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 229638189 229769261).card = 456 := join_1_0

end S109C08
end Sude.GeneratedTwinScan
