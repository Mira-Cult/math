import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20503)) 420347949 420380717 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 420347949 420380717).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20503 420347949 420380717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20503)) 420380717 420413485 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 420380717 420413485).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20503 420380717 420413485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20504)) 420413485 420446253 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 420413485 420446253).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20504 420413485 420446253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20505)) 420446253 420479021 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 420446253 420479021).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20505 420446253 420479021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 420347949 420413485).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 420347949 ≤ 420380717)
    (by decide : 420380717 ≤ 420413485) block0 block1

theorem join_0_1 : (twinPrimeSegment 420413485 420479021).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 420413485 ≤ 420446253)
    (by decide : 420446253 ≤ 420479021) block2 block3

theorem join_1_0 : (twinPrimeSegment 420347949 420479021).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 420347949 ≤ 420413485)
    (by decide : 420413485 ≤ 420479021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 420347949 420479021).card = 451 := join_1_0

end S200C07
end Sude.GeneratedTwinScan
