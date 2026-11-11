import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15033)) 225968173 226000941 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 225968173 226000941).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15033 225968173 226000941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15034)) 226000941 226033709 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 226000941 226033709).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15034 226000941 226033709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15035)) 226033709 226066477 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 226033709 226066477).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15035 226033709 226066477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15036)) 226066477 226099245 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 226066477 226099245).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15036 226066477 226099245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 225968173 226033709).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 225968173 ≤ 226000941)
    (by decide : 226000941 ≤ 226033709) block0 block1

theorem join_0_1 : (twinPrimeSegment 226033709 226099245).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 226033709 ≤ 226066477)
    (by decide : 226066477 ≤ 226099245) block2 block3

theorem join_1_0 : (twinPrimeSegment 225968173 226099245).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 225968173 ≤ 226033709)
    (by decide : 226033709 ≤ 226099245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 225968173 226099245).card = 438 := join_1_0

end S107C12
end Sude.GeneratedTwinScan
