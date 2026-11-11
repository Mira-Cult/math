import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20206)) 408289325 408322093 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 408289325 408322093).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20206 408289325 408322093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20207)) 408322093 408354861 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 408322093 408354861).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20207 408322093 408354861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20208)) 408354861 408387629 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 408354861 408387629).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20208 408354861 408387629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20209)) 408387629 408420397 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 408387629 408420397).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20209 408387629 408420397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 408289325 408354861).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 408289325 ≤ 408322093)
    (by decide : 408322093 ≤ 408354861) block0 block1

theorem join_0_1 : (twinPrimeSegment 408354861 408420397).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 408354861 ≤ 408387629)
    (by decide : 408387629 ≤ 408420397) block2 block3

theorem join_1_0 : (twinPrimeSegment 408289325 408420397).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 408289325 ≤ 408354861)
    (by decide : 408354861 ≤ 408420397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 408289325 408420397).card = 442 := join_1_0

end S194C11
end Sude.GeneratedTwinScan
