import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20080)) 403177517 403210285 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 403177517 403210285).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20080 403177517 403210285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20080)) 403210285 403243053 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 403210285 403243053).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20080 403210285 403243053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20081)) 403243053 403275821 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 403243053 403275821).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20081 403243053 403275821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20082)) 403275821 403308589 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 403275821 403308589).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20082 403275821 403308589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 403177517 403243053).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 403177517 ≤ 403210285)
    (by decide : 403210285 ≤ 403243053) block0 block1

theorem join_0_1 : (twinPrimeSegment 403243053 403308589).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 403243053 ≤ 403275821)
    (by decide : 403275821 ≤ 403308589) block2 block3

theorem join_1_0 : (twinPrimeSegment 403177517 403308589).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 403177517 ≤ 403243053)
    (by decide : 403243053 ≤ 403308589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 403177517 403308589).card = 436 := join_1_0

end S192C04
end Sude.GeneratedTwinScan
