import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17170)) 294780973 294813741 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 294780973 294813741).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17170 294780973 294813741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17171)) 294813741 294846509 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 294813741 294846509).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17171 294813741 294846509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17172)) 294846509 294879277 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 294846509 294879277).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17172 294846509 294879277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17173)) 294879277 294912045 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 294879277 294912045).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17173 294879277 294912045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 294780973 294846509).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 294780973 ≤ 294813741)
    (by decide : 294813741 ≤ 294846509) block0 block1

theorem join_0_1 : (twinPrimeSegment 294846509 294912045).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 294846509 ≤ 294879277)
    (by decide : 294879277 ≤ 294912045) block2 block3

theorem join_1_0 : (twinPrimeSegment 294780973 294912045).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 294780973 ≤ 294846509)
    (by decide : 294846509 ≤ 294912045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 294780973 294912045).card = 434 := join_1_0

end S140C09
end Sude.GeneratedTwinScan
