import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22455)) 504234029 504266797 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 504234029 504266797).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22455 504234029 504266797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22456)) 504266797 504299565 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 504266797 504299565).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22456 504266797 504299565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22457)) 504299565 504332333 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 504299565 504332333).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22457 504299565 504332333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22458)) 504332333 504365101 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 504332333 504365101).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22458 504332333 504365101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 504234029 504299565).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 504234029 ≤ 504266797)
    (by decide : 504266797 ≤ 504299565) block0 block1

theorem join_0_1 : (twinPrimeSegment 504299565 504365101).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 504299565 ≤ 504332333)
    (by decide : 504332333 ≤ 504365101) block2 block3

theorem join_1_0 : (twinPrimeSegment 504234029 504365101).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 504234029 ≤ 504299565)
    (by decide : 504299565 ≤ 504365101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 504234029 504365101).card = 440 := join_1_0

end S240C07
end Sude.GeneratedTwinScan
