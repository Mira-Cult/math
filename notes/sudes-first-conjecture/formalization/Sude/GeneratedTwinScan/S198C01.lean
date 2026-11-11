import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20381)) 415367213 415399981 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 415367213 415399981).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20381 415367213 415399981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20382)) 415399981 415432749 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 415399981 415432749).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20382 415399981 415432749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20382)) 415432749 415465517 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 415432749 415465517).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20382 415432749 415465517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20383)) 415465517 415498285 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 415465517 415498285).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20383 415465517 415498285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 415367213 415432749).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 415367213 ≤ 415399981)
    (by decide : 415399981 ≤ 415432749) block0 block1

theorem join_0_1 : (twinPrimeSegment 415432749 415498285).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 415432749 ≤ 415465517)
    (by decide : 415465517 ≤ 415498285) block2 block3

theorem join_1_0 : (twinPrimeSegment 415367213 415498285).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 415367213 ≤ 415432749)
    (by decide : 415432749 ≤ 415498285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 415367213 415498285).card = 463 := join_1_0

end S198C01
end Sude.GeneratedTwinScan
