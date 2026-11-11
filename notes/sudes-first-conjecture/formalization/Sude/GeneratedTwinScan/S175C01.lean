import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19161)) 367132717 367165485 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 367132717 367165485).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19161 367132717 367165485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19162)) 367165485 367198253 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 367165485 367198253).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19162 367165485 367198253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19163)) 367198253 367231021 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 367198253 367231021).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19163 367198253 367231021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19164)) 367231021 367263789 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 367231021 367263789).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19164 367231021 367263789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 367132717 367198253).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 367132717 ≤ 367165485)
    (by decide : 367165485 ≤ 367198253) block0 block1

theorem join_0_1 : (twinPrimeSegment 367198253 367263789).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 367198253 ≤ 367231021)
    (by decide : 367231021 ≤ 367263789) block2 block3

theorem join_1_0 : (twinPrimeSegment 367132717 367263789).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 367132717 ≤ 367198253)
    (by decide : 367198253 ≤ 367263789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 367132717 367263789).card = 467 := join_1_0

end S175C01
end Sude.GeneratedTwinScan
