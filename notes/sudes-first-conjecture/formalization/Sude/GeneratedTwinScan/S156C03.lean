import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18099)) 327548973 327581741 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 327548973 327581741).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18099 327548973 327581741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18100)) 327581741 327614509 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 327581741 327614509).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18100 327581741 327614509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18101)) 327614509 327647277 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 327614509 327647277).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18101 327614509 327647277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18101)) 327647277 327680045 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 327647277 327680045).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18101 327647277 327680045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 327548973 327614509).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 327548973 ≤ 327581741)
    (by decide : 327581741 ≤ 327614509) block0 block1

theorem join_0_1 : (twinPrimeSegment 327614509 327680045).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 327614509 ≤ 327647277)
    (by decide : 327647277 ≤ 327680045) block2 block3

theorem join_1_0 : (twinPrimeSegment 327548973 327680045).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 327548973 ≤ 327614509)
    (by decide : 327614509 ≤ 327680045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 327548973 327680045).card = 429 := join_1_0

end S156C03
end Sude.GeneratedTwinScan
