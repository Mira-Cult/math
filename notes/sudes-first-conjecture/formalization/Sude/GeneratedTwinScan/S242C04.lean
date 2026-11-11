import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22540)) 508035117 508067885 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 508035117 508067885).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22540 508035117 508067885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22541)) 508067885 508100653 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 508067885 508100653).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22541 508067885 508100653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22541)) 508100653 508133421 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 508100653 508133421).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22541 508100653 508133421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22542)) 508133421 508166189 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 508133421 508166189).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22542 508133421 508166189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 508035117 508100653).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 508035117 ≤ 508067885)
    (by decide : 508067885 ≤ 508100653) block0 block1

theorem join_0_1 : (twinPrimeSegment 508100653 508166189).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 508100653 ≤ 508133421)
    (by decide : 508133421 ≤ 508166189) block2 block3

theorem join_1_0 : (twinPrimeSegment 508035117 508166189).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 508035117 ≤ 508100653)
    (by decide : 508100653 ≤ 508166189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 508035117 508166189).card = 460 := join_1_0

end S242C04
end Sude.GeneratedTwinScan
