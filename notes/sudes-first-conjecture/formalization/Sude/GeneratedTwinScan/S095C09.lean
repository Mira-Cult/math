import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14157)) 200409133 200441901 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 200409133 200441901).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14157 200409133 200441901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14158)) 200441901 200474669 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 200441901 200474669).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14158 200441901 200474669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14160)) 200474669 200507437 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 200474669 200507437).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14160 200474669 200507437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14161)) 200507437 200540205 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 200507437 200540205).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14161 200507437 200540205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 200409133 200474669).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 200409133 ≤ 200441901)
    (by decide : 200441901 ≤ 200474669) block0 block1

theorem join_0_1 : (twinPrimeSegment 200474669 200540205).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 200474669 ≤ 200507437)
    (by decide : 200507437 ≤ 200540205) block2 block3

theorem join_1_0 : (twinPrimeSegment 200409133 200540205).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 200409133 ≤ 200474669)
    (by decide : 200474669 ≤ 200540205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 200409133 200540205).card = 460 := join_1_0

end S095C09
end Sude.GeneratedTwinScan
