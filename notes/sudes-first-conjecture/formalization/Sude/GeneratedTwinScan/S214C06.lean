import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21204)) 449577005 449609773 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 449577005 449609773).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21204 449577005 449609773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21204)) 449609773 449642541 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 449609773 449642541).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21204 449609773 449642541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21205)) 449642541 449675309 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 449642541 449675309).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21205 449642541 449675309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21206)) 449675309 449708077 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 449675309 449708077).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21206 449675309 449708077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 449577005 449642541).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 449577005 ≤ 449609773)
    (by decide : 449609773 ≤ 449642541) block0 block1

theorem join_0_1 : (twinPrimeSegment 449642541 449708077).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 449642541 ≤ 449675309)
    (by decide : 449675309 ≤ 449708077) block2 block3

theorem join_1_0 : (twinPrimeSegment 449577005 449708077).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 449577005 ≤ 449642541)
    (by decide : 449642541 ≤ 449708077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 449577005 449708077).card = 447 := join_1_0

end S214C06
end Sude.GeneratedTwinScan
