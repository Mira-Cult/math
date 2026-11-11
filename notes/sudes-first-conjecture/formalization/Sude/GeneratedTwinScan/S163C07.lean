import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18514)) 342753325 342786093 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 342753325 342786093).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18514 342753325 342786093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18515)) 342786093 342818861 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 342786093 342818861).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18515 342786093 342818861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18516)) 342818861 342851629 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 342818861 342851629).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18516 342818861 342851629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18517)) 342851629 342884397 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 342851629 342884397).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18517 342851629 342884397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 342753325 342818861).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 342753325 ≤ 342786093)
    (by decide : 342786093 ≤ 342818861) block0 block1

theorem join_0_1 : (twinPrimeSegment 342818861 342884397).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 342818861 ≤ 342851629)
    (by decide : 342851629 ≤ 342884397) block2 block3

theorem join_1_0 : (twinPrimeSegment 342753325 342884397).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 342753325 ≤ 342818861)
    (by decide : 342818861 ≤ 342884397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 342753325 342884397).card = 455 := join_1_0

end S163C07
end Sude.GeneratedTwinScan
