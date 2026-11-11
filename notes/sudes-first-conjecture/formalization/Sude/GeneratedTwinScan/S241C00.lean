import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22482)) 505413677 505446445 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 505413677 505446445).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22482 505413677 505446445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22482)) 505446445 505479213 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 505446445 505479213).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22482 505446445 505479213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22483)) 505479213 505511981 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 505479213 505511981).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22483 505479213 505511981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22484)) 505511981 505544749 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 505511981 505544749).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22484 505511981 505544749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 505413677 505479213).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 505413677 ≤ 505446445)
    (by decide : 505446445 ≤ 505479213) block0 block1

theorem join_0_1 : (twinPrimeSegment 505479213 505544749).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 505479213 ≤ 505511981)
    (by decide : 505511981 ≤ 505544749) block2 block3

theorem join_1_0 : (twinPrimeSegment 505413677 505544749).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 505413677 ≤ 505479213)
    (by decide : 505479213 ≤ 505544749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 505413677 505544749).card = 446 := join_1_0

end S241C00
end Sude.GeneratedTwinScan
