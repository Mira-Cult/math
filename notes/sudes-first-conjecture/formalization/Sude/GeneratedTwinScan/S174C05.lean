import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19120)) 365559853 365592621 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 365559853 365592621).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19120 365559853 365592621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19121)) 365592621 365625389 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 365592621 365625389).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19121 365592621 365625389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19122)) 365625389 365658157 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 365625389 365658157).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19122 365625389 365658157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19123)) 365658157 365690925 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 365658157 365690925).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19123 365658157 365690925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 365559853 365625389).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 365559853 ≤ 365592621)
    (by decide : 365592621 ≤ 365625389) block0 block1

theorem join_0_1 : (twinPrimeSegment 365625389 365690925).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 365625389 ≤ 365658157)
    (by decide : 365658157 ≤ 365690925) block2 block3

theorem join_1_0 : (twinPrimeSegment 365559853 365690925).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 365559853 ≤ 365625389)
    (by decide : 365625389 ≤ 365690925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 365559853 365690925).card = 430 := join_1_0

end S174C05
end Sude.GeneratedTwinScan
