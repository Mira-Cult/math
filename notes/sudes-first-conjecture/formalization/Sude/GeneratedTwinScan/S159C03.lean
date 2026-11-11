import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18272)) 333840429 333873197 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 333840429 333873197).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18272 333840429 333873197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18273)) 333873197 333905965 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 333873197 333905965).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18273 333873197 333905965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18273)) 333905965 333938733 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 333905965 333938733).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18273 333905965 333938733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18274)) 333938733 333971501 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 333938733 333971501).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18274 333938733 333971501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 333840429 333905965).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 333840429 ≤ 333873197)
    (by decide : 333873197 ≤ 333905965) block0 block1

theorem join_0_1 : (twinPrimeSegment 333905965 333971501).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 333905965 ≤ 333938733)
    (by decide : 333938733 ≤ 333971501) block2 block3

theorem join_1_0 : (twinPrimeSegment 333840429 333971501).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 333840429 ≤ 333905965)
    (by decide : 333905965 ≤ 333971501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 333840429 333971501).card = 446 := join_1_0

end S159C03
end Sude.GeneratedTwinScan
