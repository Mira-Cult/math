import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21348)) 455737389 455770157 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 455737389 455770157).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21348 455737389 455770157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21349)) 455770157 455802925 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 455770157 455802925).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21349 455770157 455802925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21350)) 455802925 455835693 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 455802925 455835693).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21350 455802925 455835693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21351)) 455835693 455868461 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 455835693 455868461).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21351 455835693 455868461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 455737389 455802925).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 455737389 ≤ 455770157)
    (by decide : 455770157 ≤ 455802925) block0 block1

theorem join_0_1 : (twinPrimeSegment 455802925 455868461).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 455802925 ≤ 455835693)
    (by decide : 455835693 ≤ 455868461) block2 block3

theorem join_1_0 : (twinPrimeSegment 455737389 455868461).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 455737389 ≤ 455802925)
    (by decide : 455802925 ≤ 455868461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 455737389 455868461).card = 444 := join_1_0

end S217C05
end Sude.GeneratedTwinScan
