import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19182)) 367919149 367951917 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 367919149 367951917).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19182 367919149 367951917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19182)) 367951917 367984685 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 367951917 367984685).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19182 367951917 367984685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19183)) 367984685 368017453 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 367984685 368017453).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19183 367984685 368017453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19184)) 368017453 368050221 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 368017453 368050221).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19184 368017453 368050221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 367919149 367984685).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 367919149 ≤ 367951917)
    (by decide : 367951917 ≤ 367984685) block0 block1

theorem join_0_1 : (twinPrimeSegment 367984685 368050221).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 367984685 ≤ 368017453)
    (by decide : 368017453 ≤ 368050221) block2 block3

theorem join_1_0 : (twinPrimeSegment 367919149 368050221).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 367919149 ≤ 367984685)
    (by decide : 367984685 ≤ 368050221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 367919149 368050221).card = 423 := join_1_0

end S175C07
end Sude.GeneratedTwinScan
