import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20952)) 438960173 438992941 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 438960173 438992941).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20952 438960173 438992941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20952)) 438992941 439025709 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 438992941 439025709).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20952 438992941 439025709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20953)) 439025709 439058477 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 439025709 439058477).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20953 439025709 439058477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20954)) 439058477 439091245 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 439058477 439091245).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20954 439058477 439091245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 438960173 439025709).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 438960173 ≤ 438992941)
    (by decide : 438992941 ≤ 439025709) block0 block1

theorem join_0_1 : (twinPrimeSegment 439025709 439091245).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 439025709 ≤ 439058477)
    (by decide : 439058477 ≤ 439091245) block2 block3

theorem join_1_0 : (twinPrimeSegment 438960173 439091245).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 438960173 ≤ 439025709)
    (by decide : 439025709 ≤ 439091245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 438960173 439091245).card = 447 := join_1_0

end S209C05
end Sude.GeneratedTwinScan
