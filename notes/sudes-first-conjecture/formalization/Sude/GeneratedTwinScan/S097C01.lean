import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14268)) 203554861 203587629 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 203554861 203587629).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14268 203554861 203587629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14269)) 203587629 203620397 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 203587629 203620397).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14269 203587629 203620397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14270)) 203620397 203653165 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 203620397 203653165).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14270 203620397 203653165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14271)) 203653165 203685933 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 203653165 203685933).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14271 203653165 203685933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 203554861 203620397).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 203554861 ≤ 203587629)
    (by decide : 203587629 ≤ 203620397) block0 block1

theorem join_0_1 : (twinPrimeSegment 203620397 203685933).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 203620397 ≤ 203653165)
    (by decide : 203653165 ≤ 203685933) block2 block3

theorem join_1_0 : (twinPrimeSegment 203554861 203685933).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 203554861 ≤ 203620397)
    (by decide : 203620397 ≤ 203685933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 203554861 203685933).card = 487 := join_1_0

end S097C01
end Sude.GeneratedTwinScan
