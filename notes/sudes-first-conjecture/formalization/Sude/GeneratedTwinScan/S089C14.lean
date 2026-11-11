import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13730)) 188481581 188514349 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 188481581 188514349).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13730 188481581 188514349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13731)) 188514349 188547117 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 188514349 188547117).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13731 188514349 188547117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13732)) 188547117 188579885 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 188547117 188579885).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13732 188547117 188579885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13733)) 188579885 188612653 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 188579885 188612653).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13733 188579885 188612653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 188481581 188547117).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 188481581 ≤ 188514349)
    (by decide : 188514349 ≤ 188547117) block0 block1

theorem join_0_1 : (twinPrimeSegment 188547117 188612653).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 188547117 ≤ 188579885)
    (by decide : 188579885 ≤ 188612653) block2 block3

theorem join_1_0 : (twinPrimeSegment 188481581 188612653).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 188481581 ≤ 188547117)
    (by decide : 188547117 ≤ 188612653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 188481581 188612653).card = 454 := join_1_0

end S089C14
end Sude.GeneratedTwinScan
