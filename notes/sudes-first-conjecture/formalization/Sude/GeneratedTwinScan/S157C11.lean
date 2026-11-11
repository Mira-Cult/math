import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18185)) 330694701 330727469 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 330694701 330727469).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18185 330694701 330727469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18186)) 330727469 330760237 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 330727469 330760237).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18186 330727469 330760237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18187)) 330760237 330793005 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 330760237 330793005).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18187 330760237 330793005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18188)) 330793005 330825773 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 330793005 330825773).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18188 330793005 330825773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 330694701 330760237).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 330694701 ≤ 330727469)
    (by decide : 330727469 ≤ 330760237) block0 block1

theorem join_0_1 : (twinPrimeSegment 330760237 330825773).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 330760237 ≤ 330793005)
    (by decide : 330793005 ≤ 330825773) block2 block3

theorem join_1_0 : (twinPrimeSegment 330694701 330825773).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 330694701 ≤ 330760237)
    (by decide : 330760237 ≤ 330825773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 330694701 330825773).card = 430 := join_1_0

end S157C11
end Sude.GeneratedTwinScan
