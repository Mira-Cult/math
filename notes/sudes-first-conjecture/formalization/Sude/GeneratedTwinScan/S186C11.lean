import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19787)) 391512109 391544877 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 391512109 391544877).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19787 391512109 391544877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19788)) 391544877 391577645 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 391544877 391577645).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19788 391544877 391577645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19789)) 391577645 391610413 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 391577645 391610413).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19789 391577645 391610413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19789)) 391610413 391643181 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 391610413 391643181).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19789 391610413 391643181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 391512109 391577645).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 391512109 ≤ 391544877)
    (by decide : 391544877 ≤ 391577645) block0 block1

theorem join_0_1 : (twinPrimeSegment 391577645 391643181).card = 191 := by
  simpa using combineTwinPrimeSegments (by decide : 391577645 ≤ 391610413)
    (by decide : 391610413 ≤ 391643181) block2 block3

theorem join_1_0 : (twinPrimeSegment 391512109 391643181).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 391512109 ≤ 391577645)
    (by decide : 391577645 ≤ 391643181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 391512109 391643181).card = 420 := join_1_0

end S186C11
end Sude.GeneratedTwinScan
