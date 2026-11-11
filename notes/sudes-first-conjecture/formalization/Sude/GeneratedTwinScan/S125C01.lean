import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16195)) 262275117 262307885 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 262275117 262307885).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16195 262275117 262307885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16196)) 262307885 262340653 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 262307885 262340653).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16196 262307885 262340653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16197)) 262340653 262373421 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 262340653 262373421).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16197 262340653 262373421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16198)) 262373421 262406189 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 262373421 262406189).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16198 262373421 262406189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 262275117 262340653).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 262275117 ≤ 262307885)
    (by decide : 262307885 ≤ 262340653) block0 block1

theorem join_0_1 : (twinPrimeSegment 262340653 262406189).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 262340653 ≤ 262373421)
    (by decide : 262373421 ≤ 262406189) block2 block3

theorem join_1_0 : (twinPrimeSegment 262275117 262406189).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 262275117 ≤ 262340653)
    (by decide : 262340653 ≤ 262406189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 262275117 262406189).card = 449 := join_1_0

end S125C01
end Sude.GeneratedTwinScan
