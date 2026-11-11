import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16472)) 271319085 271351853 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 271319085 271351853).card = 147 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16472 271319085 271351853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16473)) 271351853 271384621 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 271351853 271384621).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16473 271351853 271384621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16474)) 271384621 271417389 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 271384621 271417389).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16474 271384621 271417389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16475)) 271417389 271450157 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 271417389 271450157).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16475 271417389 271450157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 271319085 271384621).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 271319085 ≤ 271351853)
    (by decide : 271351853 ≤ 271384621) block0 block1

theorem join_0_1 : (twinPrimeSegment 271384621 271450157).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 271384621 ≤ 271417389)
    (by decide : 271417389 ≤ 271450157) block2 block3

theorem join_1_0 : (twinPrimeSegment 271319085 271450157).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 271319085 ≤ 271384621)
    (by decide : 271384621 ≤ 271450157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 271319085 271450157).card = 496 := join_1_0

end S129C06
end Sude.GeneratedTwinScan
