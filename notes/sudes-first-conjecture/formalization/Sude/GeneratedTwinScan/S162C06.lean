import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18454)) 340525101 340557869 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 340525101 340557869).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18454 340525101 340557869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18455)) 340557869 340590637 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 340557869 340590637).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18455 340557869 340590637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18455)) 340590637 340623405 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 340590637 340623405).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18455 340590637 340623405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18456)) 340623405 340656173 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 340623405 340656173).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18456 340623405 340656173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 340525101 340590637).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 340525101 ≤ 340557869)
    (by decide : 340557869 ≤ 340590637) block0 block1

theorem join_0_1 : (twinPrimeSegment 340590637 340656173).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 340590637 ≤ 340623405)
    (by decide : 340623405 ≤ 340656173) block2 block3

theorem join_1_0 : (twinPrimeSegment 340525101 340656173).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 340525101 ≤ 340590637)
    (by decide : 340590637 ≤ 340656173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 340525101 340656173).card = 439 := join_1_0

end S162C06
end Sude.GeneratedTwinScan
