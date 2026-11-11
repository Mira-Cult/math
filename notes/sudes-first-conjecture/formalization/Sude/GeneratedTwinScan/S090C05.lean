import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13763)) 189399085 189431853 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 189399085 189431853).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13763 189399085 189431853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13764)) 189431853 189464621 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 189431853 189464621).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13764 189431853 189464621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13765)) 189464621 189497389 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 189464621 189497389).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13765 189464621 189497389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13766)) 189497389 189530157 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 189497389 189530157).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13766 189497389 189530157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 189399085 189464621).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 189399085 ≤ 189431853)
    (by decide : 189431853 ≤ 189464621) block0 block1

theorem join_0_1 : (twinPrimeSegment 189464621 189530157).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 189464621 ≤ 189497389)
    (by decide : 189497389 ≤ 189530157) block2 block3

theorem join_1_0 : (twinPrimeSegment 189399085 189530157).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 189399085 ≤ 189464621)
    (by decide : 189464621 ≤ 189530157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 189399085 189530157).card = 478 := join_1_0

end S090C05
end Sude.GeneratedTwinScan
