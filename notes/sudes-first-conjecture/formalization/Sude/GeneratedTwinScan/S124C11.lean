import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16171)) 261488685 261521453 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 261488685 261521453).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16171 261488685 261521453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16172)) 261521453 261554221 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 261521453 261554221).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16172 261521453 261554221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16173)) 261554221 261586989 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 261554221 261586989).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16173 261554221 261586989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16174)) 261586989 261619757 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 261586989 261619757).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16174 261586989 261619757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 261488685 261554221).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 261488685 ≤ 261521453)
    (by decide : 261521453 ≤ 261554221) block0 block1

theorem join_0_1 : (twinPrimeSegment 261554221 261619757).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 261554221 ≤ 261586989)
    (by decide : 261586989 ≤ 261619757) block2 block3

theorem join_1_0 : (twinPrimeSegment 261488685 261619757).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 261488685 ≤ 261554221)
    (by decide : 261554221 ≤ 261619757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 261488685 261619757).card = 469 := join_1_0

end S124C11
end Sude.GeneratedTwinScan
