import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19594)) 383909933 383942701 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 383909933 383942701).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19594 383909933 383942701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19595)) 383942701 383975469 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 383942701 383975469).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19595 383942701 383975469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19596)) 383975469 384008237 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 383975469 384008237).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19596 383975469 384008237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19596)) 384008237 384041005 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 384008237 384041005).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19596 384008237 384041005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 383909933 383975469).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 383909933 ≤ 383942701)
    (by decide : 383942701 ≤ 383975469) block0 block1

theorem join_0_1 : (twinPrimeSegment 383975469 384041005).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 383975469 ≤ 384008237)
    (by decide : 384008237 ≤ 384041005) block2 block3

theorem join_1_0 : (twinPrimeSegment 383909933 384041005).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 383909933 ≤ 383975469)
    (by decide : 383975469 ≤ 384041005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 383909933 384041005).card = 457 := join_1_0

end S183C01
end Sude.GeneratedTwinScan
