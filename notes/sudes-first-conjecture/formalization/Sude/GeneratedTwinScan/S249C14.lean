import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22892)) 524025901 524058669 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 524025901 524058669).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22892 524025901 524058669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22893)) 524058669 524091437 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 524058669 524091437).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22893 524058669 524091437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22893)) 524091437 524124205 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 524091437 524124205).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22893 524091437 524124205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22894)) 524124205 524156973 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 524124205 524156973).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22894 524124205 524156973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 524025901 524091437).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 524025901 ≤ 524058669)
    (by decide : 524058669 ≤ 524091437) block0 block1

theorem join_0_1 : (twinPrimeSegment 524091437 524156973).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 524091437 ≤ 524124205)
    (by decide : 524124205 ≤ 524156973) block2 block3

theorem join_1_0 : (twinPrimeSegment 524025901 524156973).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 524025901 ≤ 524091437)
    (by decide : 524091437 ≤ 524156973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 524025901 524156973).card = 449 := join_1_0

end S249C14
end Sude.GeneratedTwinScan
