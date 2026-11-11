import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22458)) 504365101 504397869 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 504365101 504397869).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22458 504365101 504397869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22459)) 504397869 504430637 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 504397869 504430637).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22459 504397869 504430637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22460)) 504430637 504463405 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 504430637 504463405).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22460 504430637 504463405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22460)) 504463405 504496173 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 504463405 504496173).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22460 504463405 504496173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 504365101 504430637).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 504365101 ≤ 504397869)
    (by decide : 504397869 ≤ 504430637) block0 block1

theorem join_0_1 : (twinPrimeSegment 504430637 504496173).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 504430637 ≤ 504463405)
    (by decide : 504463405 ≤ 504496173) block2 block3

theorem join_1_0 : (twinPrimeSegment 504365101 504496173).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 504365101 ≤ 504430637)
    (by decide : 504430637 ≤ 504496173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 504365101 504496173).card = 434 := join_1_0

end S240C08
end Sude.GeneratedTwinScan
