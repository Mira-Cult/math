import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22391)) 501350445 501383213 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 501350445 501383213).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22391 501350445 501383213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22392)) 501383213 501415981 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 501383213 501415981).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22392 501383213 501415981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22393)) 501415981 501448749 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 501415981 501448749).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22393 501415981 501448749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22393)) 501448749 501481517 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 501448749 501481517).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22393 501448749 501481517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 501350445 501415981).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 501350445 ≤ 501383213)
    (by decide : 501383213 ≤ 501415981) block0 block1

theorem join_0_1 : (twinPrimeSegment 501415981 501481517).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 501415981 ≤ 501448749)
    (by decide : 501448749 ≤ 501481517) block2 block3

theorem join_1_0 : (twinPrimeSegment 501350445 501481517).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 501350445 ≤ 501415981)
    (by decide : 501415981 ≤ 501481517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 501350445 501481517).card = 429 := join_1_0

end S239C01
end Sude.GeneratedTwinScan
