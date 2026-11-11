import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19055)) 363069485 363102253 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 363069485 363102253).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19055 363069485 363102253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19056)) 363102253 363135021 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 363102253 363135021).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19056 363102253 363135021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19056)) 363135021 363167789 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 363135021 363167789).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19056 363135021 363167789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19057)) 363167789 363200557 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 363167789 363200557).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19057 363167789 363200557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 363069485 363135021).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 363069485 ≤ 363102253)
    (by decide : 363102253 ≤ 363135021) block0 block1

theorem join_0_1 : (twinPrimeSegment 363135021 363200557).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 363135021 ≤ 363167789)
    (by decide : 363167789 ≤ 363200557) block2 block3

theorem join_1_0 : (twinPrimeSegment 363069485 363200557).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 363069485 ≤ 363135021)
    (by decide : 363135021 ≤ 363200557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 363069485 363200557).card = 439 := join_1_0

end S173C02
end Sude.GeneratedTwinScan
