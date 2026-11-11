import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21495)) 462028845 462061613 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 462028845 462061613).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21495 462028845 462061613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21496)) 462061613 462094381 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 462061613 462094381).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21496 462061613 462094381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21497)) 462094381 462127149 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 462094381 462127149).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21497 462094381 462127149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21497)) 462127149 462159917 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 462127149 462159917).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21497 462127149 462159917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 462028845 462094381).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 462028845 ≤ 462061613)
    (by decide : 462061613 ≤ 462094381) block0 block1

theorem join_0_1 : (twinPrimeSegment 462094381 462159917).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 462094381 ≤ 462127149)
    (by decide : 462127149 ≤ 462159917) block2 block3

theorem join_1_0 : (twinPrimeSegment 462028845 462159917).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 462028845 ≤ 462094381)
    (by decide : 462094381 ≤ 462159917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 462028845 462159917).card = 457 := join_1_0

end S220C05
end Sude.GeneratedTwinScan
