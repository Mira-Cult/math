import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21819)) 476053549 476086317 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 476053549 476086317).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21819 476053549 476086317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21820)) 476086317 476119085 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 476086317 476119085).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21820 476086317 476119085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21820)) 476119085 476151853 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 476119085 476151853).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21820 476119085 476151853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21821)) 476151853 476184621 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 476151853 476184621).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21821 476151853 476184621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 476053549 476119085).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 476053549 ≤ 476086317)
    (by decide : 476086317 ≤ 476119085) block0 block1

theorem join_0_1 : (twinPrimeSegment 476119085 476184621).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 476119085 ≤ 476151853)
    (by decide : 476151853 ≤ 476184621) block2 block3

theorem join_1_0 : (twinPrimeSegment 476053549 476184621).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 476053549 ≤ 476119085)
    (by decide : 476119085 ≤ 476184621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 476053549 476184621).card = 431 := join_1_0

end S227C00
end Sude.GeneratedTwinScan
