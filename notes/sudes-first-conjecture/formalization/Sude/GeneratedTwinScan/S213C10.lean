import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21166)) 448004141 448036909 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 448004141 448036909).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21166 448004141 448036909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21167)) 448036909 448069677 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 448036909 448069677).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21167 448036909 448069677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21168)) 448069677 448102445 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 448069677 448102445).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21168 448069677 448102445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21169)) 448102445 448135213 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 448102445 448135213).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21169 448102445 448135213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 448004141 448069677).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 448004141 ≤ 448036909)
    (by decide : 448036909 ≤ 448069677) block0 block1

theorem join_0_1 : (twinPrimeSegment 448069677 448135213).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 448069677 ≤ 448102445)
    (by decide : 448102445 ≤ 448135213) block2 block3

theorem join_1_0 : (twinPrimeSegment 448004141 448135213).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 448004141 ≤ 448069677)
    (by decide : 448069677 ≤ 448135213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 448004141 448135213).card = 428 := join_1_0

end S213C10
end Sude.GeneratedTwinScan
