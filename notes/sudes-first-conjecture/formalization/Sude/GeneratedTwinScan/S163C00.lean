import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18489)) 341835821 341868589 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 341835821 341868589).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18489 341835821 341868589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18490)) 341868589 341901357 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 341868589 341901357).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18490 341868589 341901357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18491)) 341901357 341934125 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 341901357 341934125).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18491 341901357 341934125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18492)) 341934125 341966893 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 341934125 341966893).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18492 341934125 341966893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 341835821 341901357).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 341835821 ≤ 341868589)
    (by decide : 341868589 ≤ 341901357) block0 block1

theorem join_0_1 : (twinPrimeSegment 341901357 341966893).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 341901357 ≤ 341934125)
    (by decide : 341934125 ≤ 341966893) block2 block3

theorem join_1_0 : (twinPrimeSegment 341835821 341966893).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 341835821 ≤ 341901357)
    (by decide : 341901357 ≤ 341966893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 341835821 341966893).card = 473 := join_1_0

end S163C00
end Sude.GeneratedTwinScan
