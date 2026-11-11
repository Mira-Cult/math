import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19949)) 397934637 397967405 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 397934637 397967405).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19949 397934637 397967405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19949)) 397967405 398000173 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 397967405 398000173).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19949 397967405 398000173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19950)) 398000173 398032941 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 398000173 398032941).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19950 398000173 398032941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19951)) 398032941 398065709 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 398032941 398065709).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19951 398032941 398065709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 397934637 398000173).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 397934637 ≤ 397967405)
    (by decide : 397967405 ≤ 398000173) block0 block1

theorem join_0_1 : (twinPrimeSegment 398000173 398065709).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 398000173 ≤ 398032941)
    (by decide : 398032941 ≤ 398065709) block2 block3

theorem join_1_0 : (twinPrimeSegment 397934637 398065709).card = 402 := by
  simpa using combineTwinPrimeSegments (by decide : 397934637 ≤ 398000173)
    (by decide : 398000173 ≤ 398065709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 397934637 398065709).card = 402 := join_1_0

end S189C12
end Sude.GeneratedTwinScan
