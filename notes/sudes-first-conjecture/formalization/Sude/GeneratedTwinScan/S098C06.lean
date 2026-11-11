import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14364)) 206307373 206340141 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 206307373 206340141).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14364 206307373 206340141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14365)) 206340141 206372909 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 206340141 206372909).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14365 206340141 206372909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14366)) 206372909 206405677 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 206372909 206405677).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14366 206372909 206405677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14367)) 206405677 206438445 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 206405677 206438445).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14367 206405677 206438445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 206307373 206372909).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 206307373 ≤ 206340141)
    (by decide : 206340141 ≤ 206372909) block0 block1

theorem join_0_1 : (twinPrimeSegment 206372909 206438445).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 206372909 ≤ 206405677)
    (by decide : 206405677 ≤ 206438445) block2 block3

theorem join_1_0 : (twinPrimeSegment 206307373 206438445).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 206307373 ≤ 206372909)
    (by decide : 206372909 ≤ 206438445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 206307373 206438445).card = 484 := join_1_0

end S098C06
end Sude.GeneratedTwinScan
