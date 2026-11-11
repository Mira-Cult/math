import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12882)) 165937197 165969965 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 165937197 165969965).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12882 165937197 165969965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12884)) 165969965 166002733 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 165969965 166002733).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12884 165969965 166002733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12885)) 166002733 166035501 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 166002733 166035501).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12885 166002733 166035501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12886)) 166035501 166068269 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 166035501 166068269).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12886 166035501 166068269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 165937197 166002733).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 165937197 ≤ 165969965)
    (by decide : 165969965 ≤ 166002733) block0 block1

theorem join_0_1 : (twinPrimeSegment 166002733 166068269).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 166002733 ≤ 166035501)
    (by decide : 166035501 ≤ 166068269) block2 block3

theorem join_1_0 : (twinPrimeSegment 165937197 166068269).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 165937197 ≤ 166002733)
    (by decide : 166002733 ≤ 166068269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 165937197 166068269).card = 463 := join_1_0

end S079C02
end Sude.GeneratedTwinScan
