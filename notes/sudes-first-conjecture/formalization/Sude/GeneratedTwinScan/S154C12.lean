import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18015)) 324534317 324567085 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 324534317 324567085).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18015 324534317 324567085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18016)) 324567085 324599853 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 324567085 324599853).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18016 324567085 324599853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18017)) 324599853 324632621 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 324599853 324632621).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18017 324599853 324632621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18018)) 324632621 324665389 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 324632621 324665389).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18018 324632621 324665389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 324534317 324599853).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 324534317 ≤ 324567085)
    (by decide : 324567085 ≤ 324599853) block0 block1

theorem join_0_1 : (twinPrimeSegment 324599853 324665389).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 324599853 ≤ 324632621)
    (by decide : 324632621 ≤ 324665389) block2 block3

theorem join_1_0 : (twinPrimeSegment 324534317 324665389).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 324534317 ≤ 324599853)
    (by decide : 324599853 ≤ 324665389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 324534317 324665389).card = 457 := join_1_0

end S154C12
end Sude.GeneratedTwinScan
