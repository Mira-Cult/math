import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15922)) 253493293 253526061 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 253493293 253526061).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15922 253493293 253526061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15923)) 253526061 253558829 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 253526061 253558829).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15923 253526061 253558829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15924)) 253558829 253591597 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 253558829 253591597).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15924 253558829 253591597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15925)) 253591597 253624365 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 253591597 253624365).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15925 253591597 253624365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 253493293 253558829).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 253493293 ≤ 253526061)
    (by decide : 253526061 ≤ 253558829) block0 block1

theorem join_0_1 : (twinPrimeSegment 253558829 253624365).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 253558829 ≤ 253591597)
    (by decide : 253591597 ≤ 253624365) block2 block3

theorem join_1_0 : (twinPrimeSegment 253493293 253624365).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 253493293 ≤ 253558829)
    (by decide : 253558829 ≤ 253624365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 253493293 253624365).card = 492 := join_1_0

end S120C14
end Sude.GeneratedTwinScan
