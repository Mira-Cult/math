import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19297)) 372375597 372408365 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 372375597 372408365).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19297 372375597 372408365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19298)) 372408365 372441133 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 372408365 372441133).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19298 372408365 372441133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19299)) 372441133 372473901 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 372441133 372473901).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19299 372441133 372473901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19300)) 372473901 372506669 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 372473901 372506669).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19300 372473901 372506669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 372375597 372441133).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 372375597 ≤ 372408365)
    (by decide : 372408365 ≤ 372441133) block0 block1

theorem join_0_1 : (twinPrimeSegment 372441133 372506669).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 372441133 ≤ 372473901)
    (by decide : 372473901 ≤ 372506669) block2 block3

theorem join_1_0 : (twinPrimeSegment 372375597 372506669).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 372375597 ≤ 372441133)
    (by decide : 372441133 ≤ 372506669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 372375597 372506669).card = 428 := join_1_0

end S177C09
end Sude.GeneratedTwinScan
