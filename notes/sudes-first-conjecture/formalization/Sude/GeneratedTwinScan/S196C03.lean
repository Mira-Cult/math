import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20284)) 411435053 411467821 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 411435053 411467821).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20284 411435053 411467821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20285)) 411467821 411500589 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 411467821 411500589).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20285 411467821 411500589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20286)) 411500589 411533357 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 411500589 411533357).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20286 411500589 411533357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20287)) 411533357 411566125 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 411533357 411566125).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20287 411533357 411566125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 411435053 411500589).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 411435053 ≤ 411467821)
    (by decide : 411467821 ≤ 411500589) block0 block1

theorem join_0_1 : (twinPrimeSegment 411500589 411566125).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 411500589 ≤ 411533357)
    (by decide : 411533357 ≤ 411566125) block2 block3

theorem join_1_0 : (twinPrimeSegment 411435053 411566125).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 411435053 ≤ 411500589)
    (by decide : 411500589 ≤ 411566125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 411435053 411566125).card = 465 := join_1_0

end S196C03
end Sude.GeneratedTwinScan
