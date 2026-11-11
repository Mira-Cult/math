import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132775981 132808749 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 132775981 132808749).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132775981 132808749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132808749 132841517 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 132808749 132841517).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132808749 132841517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132841517 132874285 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 132841517 132874285).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132841517 132874285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132874285 132907053 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 132874285 132907053).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132874285 132907053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 132775981 132841517).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 132775981 ≤ 132808749)
    (by decide : 132808749 ≤ 132841517) block0 block1

theorem join_0_1 : (twinPrimeSegment 132841517 132907053).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 132841517 ≤ 132874285)
    (by decide : 132874285 ≤ 132907053) block2 block3

theorem join_1_0 : (twinPrimeSegment 132775981 132907053).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 132775981 ≤ 132841517)
    (by decide : 132841517 ≤ 132907053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 132775981 132907053).card = 493 := join_1_0

end S063C05
end Sude.GeneratedTwinScan
