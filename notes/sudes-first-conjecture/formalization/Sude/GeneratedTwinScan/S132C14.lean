import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16694)) 278659117 278691885 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 278659117 278691885).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16694 278659117 278691885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16695)) 278691885 278724653 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 278691885 278724653).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16695 278691885 278724653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16696)) 278724653 278757421 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 278724653 278757421).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16696 278724653 278757421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16697)) 278757421 278790189 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 278757421 278790189).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16697 278757421 278790189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 278659117 278724653).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 278659117 ≤ 278691885)
    (by decide : 278691885 ≤ 278724653) block0 block1

theorem join_0_1 : (twinPrimeSegment 278724653 278790189).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 278724653 ≤ 278757421)
    (by decide : 278757421 ≤ 278790189) block2 block3

theorem join_1_0 : (twinPrimeSegment 278659117 278790189).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 278659117 ≤ 278724653)
    (by decide : 278724653 ≤ 278790189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 278659117 278790189).card = 471 := join_1_0

end S132C14
end Sude.GeneratedTwinScan
