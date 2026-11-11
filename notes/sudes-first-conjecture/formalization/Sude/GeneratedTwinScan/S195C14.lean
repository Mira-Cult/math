import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20268)) 410779693 410812461 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 410779693 410812461).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20268 410779693 410812461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20269)) 410812461 410845229 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 410812461 410845229).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20269 410812461 410845229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20270)) 410845229 410877997 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 410845229 410877997).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20270 410845229 410877997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20270)) 410877997 410910765 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 410877997 410910765).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20270 410877997 410910765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 410779693 410845229).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 410779693 ≤ 410812461)
    (by decide : 410812461 ≤ 410845229) block0 block1

theorem join_0_1 : (twinPrimeSegment 410845229 410910765).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 410845229 ≤ 410877997)
    (by decide : 410877997 ≤ 410910765) block2 block3

theorem join_1_0 : (twinPrimeSegment 410779693 410910765).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 410779693 ≤ 410845229)
    (by decide : 410845229 ≤ 410910765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 410779693 410910765).card = 450 := join_1_0

end S195C14
end Sude.GeneratedTwinScan
