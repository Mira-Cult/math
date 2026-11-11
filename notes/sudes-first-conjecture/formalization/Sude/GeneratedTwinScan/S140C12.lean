import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17181)) 295174189 295206957 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 295174189 295206957).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17181 295174189 295206957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17182)) 295206957 295239725 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 295206957 295239725).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17182 295206957 295239725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17183)) 295239725 295272493 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 295239725 295272493).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17183 295239725 295272493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17184)) 295272493 295305261 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 295272493 295305261).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17184 295272493 295305261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 295174189 295239725).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 295174189 ≤ 295206957)
    (by decide : 295206957 ≤ 295239725) block0 block1

theorem join_0_1 : (twinPrimeSegment 295239725 295305261).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 295239725 ≤ 295272493)
    (by decide : 295272493 ≤ 295305261) block2 block3

theorem join_1_0 : (twinPrimeSegment 295174189 295305261).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 295174189 ≤ 295239725)
    (by decide : 295239725 ≤ 295305261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 295174189 295305261).card = 457 := join_1_0

end S140C12
end Sude.GeneratedTwinScan
