import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19955)) 398196781 398229549 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 398196781 398229549).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19955 398196781 398229549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19956)) 398229549 398262317 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 398229549 398262317).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19956 398229549 398262317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19957)) 398262317 398295085 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 398262317 398295085).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19957 398262317 398295085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19958)) 398295085 398327853 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 398295085 398327853).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19958 398295085 398327853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 398196781 398262317).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 398196781 ≤ 398229549)
    (by decide : 398229549 ≤ 398262317) block0 block1

theorem join_0_1 : (twinPrimeSegment 398262317 398327853).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 398262317 ≤ 398295085)
    (by decide : 398295085 ≤ 398327853) block2 block3

theorem join_1_0 : (twinPrimeSegment 398196781 398327853).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 398196781 ≤ 398262317)
    (by decide : 398262317 ≤ 398327853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 398196781 398327853).card = 426 := join_1_0

end S189C14
end Sude.GeneratedTwinScan
