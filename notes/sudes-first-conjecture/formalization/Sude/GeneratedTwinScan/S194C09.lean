import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20200)) 408027181 408059949 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 408027181 408059949).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20200 408027181 408059949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20201)) 408059949 408092717 = 91 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 408059949 408092717).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20201 408059949 408092717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20202)) 408092717 408125485 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 408092717 408125485).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20202 408092717 408125485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20202)) 408125485 408158253 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 408125485 408158253).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20202 408125485 408158253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 408027181 408092717).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 408027181 ≤ 408059949)
    (by decide : 408059949 ≤ 408092717) block0 block1

theorem join_0_1 : (twinPrimeSegment 408092717 408158253).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 408092717 ≤ 408125485)
    (by decide : 408125485 ≤ 408158253) block2 block3

theorem join_1_0 : (twinPrimeSegment 408027181 408158253).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 408027181 ≤ 408092717)
    (by decide : 408092717 ≤ 408158253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 408027181 408158253).card = 421 := join_1_0

end S194C09
end Sude.GeneratedTwinScan
