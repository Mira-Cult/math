import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19978)) 399114285 399147053 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 399114285 399147053).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19978 399114285 399147053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19979)) 399147053 399179821 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 399147053 399179821).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19979 399147053 399179821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19980)) 399179821 399212589 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 399179821 399212589).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19980 399179821 399212589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19981)) 399212589 399245357 = 87 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 399212589 399245357).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19981 399212589 399245357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 399114285 399179821).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 399114285 ≤ 399147053)
    (by decide : 399147053 ≤ 399179821) block0 block1

theorem join_0_1 : (twinPrimeSegment 399179821 399245357).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 399179821 ≤ 399212589)
    (by decide : 399212589 ≤ 399245357) block2 block3

theorem join_1_0 : (twinPrimeSegment 399114285 399245357).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 399114285 ≤ 399179821)
    (by decide : 399179821 ≤ 399245357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 399114285 399245357).card = 414 := join_1_0

end S190C05
end Sude.GeneratedTwinScan
