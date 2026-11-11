import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18290)) 334495789 334528557 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 334495789 334528557).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18290 334495789 334528557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18291)) 334528557 334561325 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 334528557 334561325).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18291 334528557 334561325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18291)) 334561325 334594093 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 334561325 334594093).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18291 334561325 334594093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18292)) 334594093 334626861 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 334594093 334626861).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18292 334594093 334626861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 334495789 334561325).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 334495789 ≤ 334528557)
    (by decide : 334528557 ≤ 334561325) block0 block1

theorem join_0_1 : (twinPrimeSegment 334561325 334626861).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 334561325 ≤ 334594093)
    (by decide : 334594093 ≤ 334626861) block2 block3

theorem join_1_0 : (twinPrimeSegment 334495789 334626861).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 334495789 ≤ 334561325)
    (by decide : 334561325 ≤ 334626861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 334495789 334626861).card = 450 := join_1_0

end S159C08
end Sude.GeneratedTwinScan
