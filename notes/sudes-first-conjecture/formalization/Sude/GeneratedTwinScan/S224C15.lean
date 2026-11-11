import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21720)) 471728173 471760941 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 471728173 471760941).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21720 471728173 471760941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21720)) 471760941 471793709 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 471760941 471793709).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21720 471760941 471793709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21721)) 471793709 471826477 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 471793709 471826477).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21721 471793709 471826477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21722)) 471826477 471859245 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 471826477 471859245).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21722 471826477 471859245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 471728173 471793709).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 471728173 ≤ 471760941)
    (by decide : 471760941 ≤ 471793709) block0 block1

theorem join_0_1 : (twinPrimeSegment 471793709 471859245).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 471793709 ≤ 471826477)
    (by decide : 471826477 ≤ 471859245) block2 block3

theorem join_1_0 : (twinPrimeSegment 471728173 471859245).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 471728173 ≤ 471793709)
    (by decide : 471793709 ≤ 471859245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 471728173 471859245).card = 443 := join_1_0

end S224C15
end Sude.GeneratedTwinScan
