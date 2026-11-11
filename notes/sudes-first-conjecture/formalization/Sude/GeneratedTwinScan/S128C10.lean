import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16424)) 269746221 269778989 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 269746221 269778989).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16424 269746221 269778989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16425)) 269778989 269811757 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 269778989 269811757).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16425 269778989 269811757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16426)) 269811757 269844525 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 269811757 269844525).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16426 269811757 269844525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16427)) 269844525 269877293 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 269844525 269877293).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16427 269844525 269877293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 269746221 269811757).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 269746221 ≤ 269778989)
    (by decide : 269778989 ≤ 269811757) block0 block1

theorem join_0_1 : (twinPrimeSegment 269811757 269877293).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 269811757 ≤ 269844525)
    (by decide : 269844525 ≤ 269877293) block2 block3

theorem join_1_0 : (twinPrimeSegment 269746221 269877293).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 269746221 ≤ 269811757)
    (by decide : 269811757 ≤ 269877293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 269746221 269877293).card = 453 := join_1_0

end S128C10
end Sude.GeneratedTwinScan
