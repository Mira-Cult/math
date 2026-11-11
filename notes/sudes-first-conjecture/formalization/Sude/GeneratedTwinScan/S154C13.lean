import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18019)) 324665389 324698157 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 324665389 324698157).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18019 324665389 324698157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18020)) 324698157 324730925 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 324698157 324730925).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18020 324698157 324730925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18021)) 324730925 324763693 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 324730925 324763693).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18021 324730925 324763693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18022)) 324763693 324796461 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 324763693 324796461).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18022 324763693 324796461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 324665389 324730925).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 324665389 ≤ 324698157)
    (by decide : 324698157 ≤ 324730925) block0 block1

theorem join_0_1 : (twinPrimeSegment 324730925 324796461).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 324730925 ≤ 324763693)
    (by decide : 324763693 ≤ 324796461) block2 block3

theorem join_1_0 : (twinPrimeSegment 324665389 324796461).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 324665389 ≤ 324730925)
    (by decide : 324730925 ≤ 324796461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 324665389 324796461).card = 462 := join_1_0

end S154C13
end Sude.GeneratedTwinScan
