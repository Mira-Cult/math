import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20579)) 423493677 423526445 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 423493677 423526445).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20579 423493677 423526445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20580)) 423526445 423559213 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 423526445 423559213).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20580 423526445 423559213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20581)) 423559213 423591981 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 423559213 423591981).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20581 423559213 423591981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20582)) 423591981 423624749 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 423591981 423624749).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20582 423591981 423624749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 423493677 423559213).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 423493677 ≤ 423526445)
    (by decide : 423526445 ≤ 423559213) block0 block1

theorem join_0_1 : (twinPrimeSegment 423559213 423624749).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 423559213 ≤ 423591981)
    (by decide : 423591981 ≤ 423624749) block2 block3

theorem join_1_0 : (twinPrimeSegment 423493677 423624749).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 423493677 ≤ 423559213)
    (by decide : 423559213 ≤ 423624749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 423493677 423624749).card = 459 := join_1_0

end S201C15
end Sude.GeneratedTwinScan
