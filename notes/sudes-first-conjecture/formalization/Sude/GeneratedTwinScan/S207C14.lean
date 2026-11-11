import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20880)) 435945517 435978285 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 435945517 435978285).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20880 435945517 435978285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20880)) 435978285 436011053 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 435978285 436011053).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20880 435978285 436011053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20881)) 436011053 436043821 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 436011053 436043821).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20881 436011053 436043821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20882)) 436043821 436076589 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 436043821 436076589).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20882 436043821 436076589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 435945517 436011053).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 435945517 ≤ 435978285)
    (by decide : 435978285 ≤ 436011053) block0 block1

theorem join_0_1 : (twinPrimeSegment 436011053 436076589).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 436011053 ≤ 436043821)
    (by decide : 436043821 ≤ 436076589) block2 block3

theorem join_1_0 : (twinPrimeSegment 435945517 436076589).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 435945517 ≤ 436011053)
    (by decide : 436011053 ≤ 436076589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 435945517 436076589).card = 443 := join_1_0

end S207C14
end Sude.GeneratedTwinScan
