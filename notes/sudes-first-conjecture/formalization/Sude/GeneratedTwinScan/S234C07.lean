import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22173)) 491651117 491683885 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 491651117 491683885).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22173 491651117 491683885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22174)) 491683885 491716653 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 491683885 491716653).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22174 491683885 491716653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22175)) 491716653 491749421 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 491716653 491749421).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22175 491716653 491749421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22176)) 491749421 491782189 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 491749421 491782189).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22176 491749421 491782189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 491651117 491716653).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 491651117 ≤ 491683885)
    (by decide : 491683885 ≤ 491716653) block0 block1

theorem join_0_1 : (twinPrimeSegment 491716653 491782189).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 491716653 ≤ 491749421)
    (by decide : 491749421 ≤ 491782189) block2 block3

theorem join_1_0 : (twinPrimeSegment 491651117 491782189).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 491651117 ≤ 491716653)
    (by decide : 491716653 ≤ 491782189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 491651117 491782189).card = 437 := join_1_0

end S234C07
end Sude.GeneratedTwinScan
