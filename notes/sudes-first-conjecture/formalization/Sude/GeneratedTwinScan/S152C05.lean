import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17873)) 319422509 319455277 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 319422509 319455277).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17873 319422509 319455277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17874)) 319455277 319488045 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 319455277 319488045).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17874 319455277 319488045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17875)) 319488045 319520813 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 319488045 319520813).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17875 319488045 319520813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17876)) 319520813 319553581 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 319520813 319553581).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17876 319520813 319553581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 319422509 319488045).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 319422509 ≤ 319455277)
    (by decide : 319455277 ≤ 319488045) block0 block1

theorem join_0_1 : (twinPrimeSegment 319488045 319553581).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 319488045 ≤ 319520813)
    (by decide : 319520813 ≤ 319553581) block2 block3

theorem join_1_0 : (twinPrimeSegment 319422509 319553581).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 319422509 ≤ 319488045)
    (by decide : 319488045 ≤ 319553581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 319422509 319553581).card = 447 := join_1_0

end S152C05
end Sude.GeneratedTwinScan
