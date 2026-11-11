import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20138)) 405536813 405569581 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 405536813 405569581).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20138 405536813 405569581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20139)) 405569581 405602349 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 405569581 405602349).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20139 405569581 405602349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20140)) 405602349 405635117 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 405602349 405635117).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20140 405602349 405635117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20141)) 405635117 405667885 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 405635117 405667885).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20141 405635117 405667885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 405536813 405602349).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 405536813 ≤ 405569581)
    (by decide : 405569581 ≤ 405602349) block0 block1

theorem join_0_1 : (twinPrimeSegment 405602349 405667885).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 405602349 ≤ 405635117)
    (by decide : 405635117 ≤ 405667885) block2 block3

theorem join_1_0 : (twinPrimeSegment 405536813 405667885).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 405536813 ≤ 405602349)
    (by decide : 405602349 ≤ 405667885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 405536813 405667885).card = 422 := join_1_0

end S193C06
end Sude.GeneratedTwinScan
