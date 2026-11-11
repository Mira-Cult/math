import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19291)) 372113453 372146221 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 372113453 372146221).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19291 372113453 372146221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19291)) 372146221 372178989 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 372146221 372178989).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19291 372146221 372178989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19292)) 372178989 372211757 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 372178989 372211757).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19292 372178989 372211757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19293)) 372211757 372244525 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 372211757 372244525).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19293 372211757 372244525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 372113453 372178989).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 372113453 ≤ 372146221)
    (by decide : 372146221 ≤ 372178989) block0 block1

theorem join_0_1 : (twinPrimeSegment 372178989 372244525).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 372178989 ≤ 372211757)
    (by decide : 372211757 ≤ 372244525) block2 block3

theorem join_1_0 : (twinPrimeSegment 372113453 372244525).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 372113453 ≤ 372178989)
    (by decide : 372178989 ≤ 372244525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 372113453 372244525).card = 442 := join_1_0

end S177C07
end Sude.GeneratedTwinScan
