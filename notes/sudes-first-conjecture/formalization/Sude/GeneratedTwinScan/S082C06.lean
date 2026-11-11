import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13144)) 172752941 172785709 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 172752941 172785709).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13144 172752941 172785709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13146)) 172785709 172818477 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 172785709 172818477).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13146 172785709 172818477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13147)) 172818477 172851245 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 172818477 172851245).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13147 172818477 172851245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13148)) 172851245 172884013 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 172851245 172884013).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13148 172851245 172884013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 172752941 172818477).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 172752941 ≤ 172785709)
    (by decide : 172785709 ≤ 172818477) block0 block1

theorem join_0_1 : (twinPrimeSegment 172818477 172884013).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 172818477 ≤ 172851245)
    (by decide : 172851245 ≤ 172884013) block2 block3

theorem join_1_0 : (twinPrimeSegment 172752941 172884013).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 172752941 ≤ 172818477)
    (by decide : 172818477 ≤ 172884013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 172752941 172884013).card = 446 := join_1_0

end S082C06
end Sude.GeneratedTwinScan
