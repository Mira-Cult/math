import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21250)) 451543085 451575853 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 451543085 451575853).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21250 451543085 451575853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21251)) 451575853 451608621 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 451575853 451608621).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21251 451575853 451608621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21251)) 451608621 451641389 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 451608621 451641389).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21251 451608621 451641389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21252)) 451641389 451674157 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 451641389 451674157).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21252 451641389 451674157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 451543085 451608621).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 451543085 ≤ 451575853)
    (by decide : 451575853 ≤ 451608621) block0 block1

theorem join_0_1 : (twinPrimeSegment 451608621 451674157).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 451608621 ≤ 451641389)
    (by decide : 451641389 ≤ 451674157) block2 block3

theorem join_1_0 : (twinPrimeSegment 451543085 451674157).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 451543085 ≤ 451608621)
    (by decide : 451608621 ≤ 451674157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 451543085 451674157).card = 432 := join_1_0

end S215C05
end Sude.GeneratedTwinScan
