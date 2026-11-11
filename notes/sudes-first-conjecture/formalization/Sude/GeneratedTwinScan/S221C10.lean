import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21559)) 464781357 464814125 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 464781357 464814125).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21559 464781357 464814125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21560)) 464814125 464846893 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 464814125 464846893).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21560 464814125 464846893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21561)) 464846893 464879661 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 464846893 464879661).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21561 464846893 464879661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21561)) 464879661 464912429 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 464879661 464912429).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21561 464879661 464912429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 464781357 464846893).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 464781357 ≤ 464814125)
    (by decide : 464814125 ≤ 464846893) block0 block1

theorem join_0_1 : (twinPrimeSegment 464846893 464912429).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 464846893 ≤ 464879661)
    (by decide : 464879661 ≤ 464912429) block2 block3

theorem join_1_0 : (twinPrimeSegment 464781357 464912429).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 464781357 ≤ 464846893)
    (by decide : 464846893 ≤ 464912429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 464781357 464912429).card = 419 := join_1_0

end S221C10
end Sude.GeneratedTwinScan
