import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17570)) 308674605 308707373 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 308674605 308707373).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17570 308674605 308707373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17571)) 308707373 308740141 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 308707373 308740141).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17571 308707373 308740141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17571)) 308740141 308772909 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 308740141 308772909).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17571 308740141 308772909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17572)) 308772909 308805677 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 308772909 308805677).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17572 308772909 308805677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 308674605 308740141).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 308674605 ≤ 308707373)
    (by decide : 308707373 ≤ 308740141) block0 block1

theorem join_0_1 : (twinPrimeSegment 308740141 308805677).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 308740141 ≤ 308772909)
    (by decide : 308772909 ≤ 308805677) block2 block3

theorem join_1_0 : (twinPrimeSegment 308674605 308805677).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 308674605 ≤ 308740141)
    (by decide : 308740141 ≤ 308805677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 308674605 308805677).card = 486 := join_1_0

end S147C03
end Sude.GeneratedTwinScan
