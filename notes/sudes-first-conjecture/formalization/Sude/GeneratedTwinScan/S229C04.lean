import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21927)) 480772141 480804909 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 480772141 480804909).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21927 480772141 480804909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21928)) 480804909 480837677 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 480804909 480837677).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21928 480804909 480837677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21928)) 480837677 480870445 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 480837677 480870445).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21928 480837677 480870445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21929)) 480870445 480903213 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 480870445 480903213).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21929 480870445 480903213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 480772141 480837677).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 480772141 ≤ 480804909)
    (by decide : 480804909 ≤ 480837677) block0 block1

theorem join_0_1 : (twinPrimeSegment 480837677 480903213).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 480837677 ≤ 480870445)
    (by decide : 480870445 ≤ 480903213) block2 block3

theorem join_1_0 : (twinPrimeSegment 480772141 480903213).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 480772141 ≤ 480837677)
    (by decide : 480837677 ≤ 480903213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 480772141 480903213).card = 412 := join_1_0

end S229C04
end Sude.GeneratedTwinScan
