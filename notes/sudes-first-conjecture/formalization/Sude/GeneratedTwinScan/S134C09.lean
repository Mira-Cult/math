import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16799)) 282198061 282230829 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 282198061 282230829).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16799 282198061 282230829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16800)) 282230829 282263597 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 282230829 282263597).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16800 282230829 282263597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16801)) 282263597 282296365 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 282263597 282296365).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16801 282263597 282296365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16802)) 282296365 282329133 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 282296365 282329133).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16802 282296365 282329133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 282198061 282263597).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 282198061 ≤ 282230829)
    (by decide : 282230829 ≤ 282263597) block0 block1

theorem join_0_1 : (twinPrimeSegment 282263597 282329133).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 282263597 ≤ 282296365)
    (by decide : 282296365 ≤ 282329133) block2 block3

theorem join_1_0 : (twinPrimeSegment 282198061 282329133).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 282198061 ≤ 282263597)
    (by decide : 282263597 ≤ 282329133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 282198061 282329133).card = 485 := join_1_0

end S134C09
end Sude.GeneratedTwinScan
