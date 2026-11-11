import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17692)) 312999981 313032749 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 312999981 313032749).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17692 312999981 313032749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17693)) 313032749 313065517 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 313032749 313065517).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17693 313032749 313065517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17694)) 313065517 313098285 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 313065517 313098285).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17694 313065517 313098285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17695)) 313098285 313131053 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 313098285 313131053).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17695 313098285 313131053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 312999981 313065517).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 312999981 ≤ 313032749)
    (by decide : 313032749 ≤ 313065517) block0 block1

theorem join_0_1 : (twinPrimeSegment 313065517 313131053).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 313065517 ≤ 313098285)
    (by decide : 313098285 ≤ 313131053) block2 block3

theorem join_1_0 : (twinPrimeSegment 312999981 313131053).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 312999981 ≤ 313065517)
    (by decide : 313065517 ≤ 313131053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 312999981 313131053).card = 452 := join_1_0

end S149C04
end Sude.GeneratedTwinScan
