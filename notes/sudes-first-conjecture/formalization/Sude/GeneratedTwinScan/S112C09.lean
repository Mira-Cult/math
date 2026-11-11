import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15365)) 236060717 236093485 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 236060717 236093485).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15365 236060717 236093485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15366)) 236093485 236126253 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 236093485 236126253).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15366 236093485 236126253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15367)) 236126253 236159021 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 236126253 236159021).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15367 236126253 236159021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15368)) 236159021 236191789 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 236159021 236191789).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15368 236159021 236191789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 236060717 236126253).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 236060717 ≤ 236093485)
    (by decide : 236093485 ≤ 236126253) block0 block1

theorem join_0_1 : (twinPrimeSegment 236126253 236191789).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 236126253 ≤ 236159021)
    (by decide : 236159021 ≤ 236191789) block2 block3

theorem join_1_0 : (twinPrimeSegment 236060717 236191789).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 236060717 ≤ 236126253)
    (by decide : 236126253 ≤ 236191789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 236060717 236191789).card = 489 := join_1_0

end S112C09
end Sude.GeneratedTwinScan
