import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18311)) 335282221 335314989 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 335282221 335314989).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18311 335282221 335314989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18312)) 335314989 335347757 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 335314989 335347757).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18312 335314989 335347757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18313)) 335347757 335380525 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 335347757 335380525).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18313 335347757 335380525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18314)) 335380525 335413293 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 335380525 335413293).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18314 335380525 335413293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 335282221 335347757).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 335282221 ≤ 335314989)
    (by decide : 335314989 ≤ 335347757) block0 block1

theorem join_0_1 : (twinPrimeSegment 335347757 335413293).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 335347757 ≤ 335380525)
    (by decide : 335380525 ≤ 335413293) block2 block3

theorem join_1_0 : (twinPrimeSegment 335282221 335413293).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 335282221 ≤ 335347757)
    (by decide : 335347757 ≤ 335413293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 335282221 335413293).card = 426 := join_1_0

end S159C14
end Sude.GeneratedTwinScan
