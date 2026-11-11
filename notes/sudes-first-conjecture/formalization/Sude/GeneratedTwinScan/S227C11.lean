import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21852)) 477495341 477528109 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 477495341 477528109).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21852 477495341 477528109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21853)) 477528109 477560877 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 477528109 477560877).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21853 477528109 477560877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21853)) 477560877 477593645 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 477560877 477593645).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21853 477560877 477593645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21854)) 477593645 477626413 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 477593645 477626413).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21854 477593645 477626413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 477495341 477560877).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 477495341 ≤ 477528109)
    (by decide : 477528109 ≤ 477560877) block0 block1

theorem join_0_1 : (twinPrimeSegment 477560877 477626413).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 477560877 ≤ 477593645)
    (by decide : 477593645 ≤ 477626413) block2 block3

theorem join_1_0 : (twinPrimeSegment 477495341 477626413).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 477495341 ≤ 477560877)
    (by decide : 477560877 ≤ 477626413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 477495341 477626413).card = 442 := join_1_0

end S227C11
end Sude.GeneratedTwinScan
