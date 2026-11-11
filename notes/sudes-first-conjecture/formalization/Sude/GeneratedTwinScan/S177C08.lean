import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19294)) 372244525 372277293 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 372244525 372277293).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19294 372244525 372277293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19295)) 372277293 372310061 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 372277293 372310061).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19295 372277293 372310061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19296)) 372310061 372342829 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 372310061 372342829).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19296 372310061 372342829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19297)) 372342829 372375597 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 372342829 372375597).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19297 372342829 372375597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 372244525 372310061).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 372244525 ≤ 372277293)
    (by decide : 372277293 ≤ 372310061) block0 block1

theorem join_0_1 : (twinPrimeSegment 372310061 372375597).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 372310061 ≤ 372342829)
    (by decide : 372342829 ≤ 372375597) block2 block3

theorem join_1_0 : (twinPrimeSegment 372244525 372375597).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 372244525 ≤ 372310061)
    (by decide : 372310061 ≤ 372375597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 372244525 372375597).card = 471 := join_1_0

end S177C08
end Sude.GeneratedTwinScan
