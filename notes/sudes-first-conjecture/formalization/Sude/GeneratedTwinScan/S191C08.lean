import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20040)) 401604653 401637421 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 401604653 401637421).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20040 401604653 401637421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20041)) 401637421 401670189 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 401637421 401670189).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20041 401637421 401670189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20042)) 401670189 401702957 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 401670189 401702957).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20042 401670189 401702957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20043)) 401702957 401735725 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 401702957 401735725).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20043 401702957 401735725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 401604653 401670189).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 401604653 ≤ 401637421)
    (by decide : 401637421 ≤ 401670189) block0 block1

theorem join_0_1 : (twinPrimeSegment 401670189 401735725).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 401670189 ≤ 401702957)
    (by decide : 401702957 ≤ 401735725) block2 block3

theorem join_1_0 : (twinPrimeSegment 401604653 401735725).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 401604653 ≤ 401670189)
    (by decide : 401670189 ≤ 401735725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 401604653 401735725).card = 448 := join_1_0

end S191C08
end Sude.GeneratedTwinScan
