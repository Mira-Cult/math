import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22583)) 510001197 510033965 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 510001197 510033965).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22583 510001197 510033965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22584)) 510033965 510066733 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 510033965 510066733).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22584 510033965 510066733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22585)) 510066733 510099501 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 510066733 510099501).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22585 510066733 510099501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22586)) 510099501 510132269 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 510099501 510132269).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22586 510099501 510132269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 510001197 510066733).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 510001197 ≤ 510033965)
    (by decide : 510033965 ≤ 510066733) block0 block1

theorem join_0_1 : (twinPrimeSegment 510066733 510132269).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 510066733 ≤ 510099501)
    (by decide : 510099501 ≤ 510132269) block2 block3

theorem join_1_0 : (twinPrimeSegment 510001197 510132269).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 510001197 ≤ 510066733)
    (by decide : 510066733 ≤ 510132269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 510001197 510132269).card = 439 := join_1_0

end S243C03
end Sude.GeneratedTwinScan
