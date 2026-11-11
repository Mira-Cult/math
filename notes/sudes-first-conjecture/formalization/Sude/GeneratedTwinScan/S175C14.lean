import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19205)) 368836653 368869421 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 368836653 368869421).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19205 368836653 368869421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19206)) 368869421 368902189 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 368869421 368902189).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19206 368869421 368902189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19207)) 368902189 368934957 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 368902189 368934957).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19207 368902189 368934957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19208)) 368934957 368967725 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 368934957 368967725).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19208 368934957 368967725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 368836653 368902189).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 368836653 ≤ 368869421)
    (by decide : 368869421 ≤ 368902189) block0 block1

theorem join_0_1 : (twinPrimeSegment 368902189 368967725).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 368902189 ≤ 368934957)
    (by decide : 368934957 ≤ 368967725) block2 block3

theorem join_1_0 : (twinPrimeSegment 368836653 368967725).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 368836653 ≤ 368902189)
    (by decide : 368902189 ≤ 368967725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 368836653 368967725).card = 425 := join_1_0

end S175C14
end Sude.GeneratedTwinScan
