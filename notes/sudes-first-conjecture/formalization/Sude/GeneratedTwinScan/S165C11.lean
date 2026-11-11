import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18641)) 347471917 347504685 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 347471917 347504685).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18641 347471917 347504685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18642)) 347504685 347537453 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 347504685 347537453).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18642 347504685 347537453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18643)) 347537453 347570221 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 347537453 347570221).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18643 347537453 347570221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18644)) 347570221 347602989 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 347570221 347602989).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18644 347570221 347602989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 347471917 347537453).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 347471917 ≤ 347504685)
    (by decide : 347504685 ≤ 347537453) block0 block1

theorem join_0_1 : (twinPrimeSegment 347537453 347602989).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 347537453 ≤ 347570221)
    (by decide : 347570221 ≤ 347602989) block2 block3

theorem join_1_0 : (twinPrimeSegment 347471917 347602989).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 347471917 ≤ 347537453)
    (by decide : 347537453 ≤ 347602989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 347471917 347602989).card = 448 := join_1_0

end S165C11
end Sude.GeneratedTwinScan
