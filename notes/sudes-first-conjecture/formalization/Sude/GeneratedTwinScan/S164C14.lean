import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18595)) 345767981 345800749 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 345767981 345800749).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18595 345767981 345800749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18596)) 345800749 345833517 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 345800749 345833517).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18596 345800749 345833517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18597)) 345833517 345866285 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 345833517 345866285).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18597 345833517 345866285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18598)) 345866285 345899053 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 345866285 345899053).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18598 345866285 345899053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 345767981 345833517).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 345767981 ≤ 345800749)
    (by decide : 345800749 ≤ 345833517) block0 block1

theorem join_0_1 : (twinPrimeSegment 345833517 345899053).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 345833517 ≤ 345866285)
    (by decide : 345866285 ≤ 345899053) block2 block3

theorem join_1_0 : (twinPrimeSegment 345767981 345899053).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 345767981 ≤ 345833517)
    (by decide : 345833517 ≤ 345899053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 345767981 345899053).card = 454 := join_1_0

end S164C14
end Sude.GeneratedTwinScan
