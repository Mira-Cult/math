import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22300)) 497287213 497319981 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 497287213 497319981).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22300 497287213 497319981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22301)) 497319981 497352749 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 497319981 497352749).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22301 497319981 497352749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22302)) 497352749 497385517 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 497352749 497385517).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22302 497352749 497385517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22302)) 497385517 497418285 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 497385517 497418285).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22302 497385517 497418285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 497287213 497352749).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 497287213 ≤ 497319981)
    (by decide : 497319981 ≤ 497352749) block0 block1

theorem join_0_1 : (twinPrimeSegment 497352749 497418285).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 497352749 ≤ 497385517)
    (by decide : 497385517 ≤ 497418285) block2 block3

theorem join_1_0 : (twinPrimeSegment 497287213 497418285).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 497287213 ≤ 497352749)
    (by decide : 497352749 ≤ 497418285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 497287213 497418285).card = 444 := join_1_0

end S237C02
end Sude.GeneratedTwinScan
