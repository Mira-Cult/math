import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19192)) 368312365 368345133 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 368312365 368345133).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19192 368312365 368345133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19193)) 368345133 368377901 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 368345133 368377901).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19193 368345133 368377901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19194)) 368377901 368410669 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 368377901 368410669).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19194 368377901 368410669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19194)) 368410669 368443437 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 368410669 368443437).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19194 368410669 368443437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 368312365 368377901).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 368312365 ≤ 368345133)
    (by decide : 368345133 ≤ 368377901) block0 block1

theorem join_0_1 : (twinPrimeSegment 368377901 368443437).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 368377901 ≤ 368410669)
    (by decide : 368410669 ≤ 368443437) block2 block3

theorem join_1_0 : (twinPrimeSegment 368312365 368443437).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 368312365 ≤ 368377901)
    (by decide : 368377901 ≤ 368443437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 368312365 368443437).card = 430 := join_1_0

end S175C10
end Sude.GeneratedTwinScan
