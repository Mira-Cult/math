import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16256)) 264241197 264273965 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 264241197 264273965).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16256 264241197 264273965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16257)) 264273965 264306733 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 264273965 264306733).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16257 264273965 264306733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16258)) 264306733 264339501 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 264306733 264339501).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16258 264306733 264339501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16259)) 264339501 264372269 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 264339501 264372269).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16259 264339501 264372269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 264241197 264306733).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 264241197 ≤ 264273965)
    (by decide : 264273965 ≤ 264306733) block0 block1

theorem join_0_1 : (twinPrimeSegment 264306733 264372269).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 264306733 ≤ 264339501)
    (by decide : 264339501 ≤ 264372269) block2 block3

theorem join_1_0 : (twinPrimeSegment 264241197 264372269).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 264241197 ≤ 264306733)
    (by decide : 264306733 ≤ 264372269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 264241197 264372269).card = 443 := join_1_0

end S126C00
end Sude.GeneratedTwinScan
