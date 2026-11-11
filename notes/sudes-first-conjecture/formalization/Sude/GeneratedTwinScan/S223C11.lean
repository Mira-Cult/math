import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21659)) 469106733 469139501 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 469106733 469139501).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21659 469106733 469139501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21660)) 469139501 469172269 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 469139501 469172269).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21660 469139501 469172269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21661)) 469172269 469205037 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 469172269 469205037).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21661 469172269 469205037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21661)) 469205037 469237805 = 87 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 469205037 469237805).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21661 469205037 469237805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 469106733 469172269).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 469106733 ≤ 469139501)
    (by decide : 469139501 ≤ 469172269) block0 block1

theorem join_0_1 : (twinPrimeSegment 469172269 469237805).card = 188 := by
  simpa using combineTwinPrimeSegments (by decide : 469172269 ≤ 469205037)
    (by decide : 469205037 ≤ 469237805) block2 block3

theorem join_1_0 : (twinPrimeSegment 469106733 469237805).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 469106733 ≤ 469172269)
    (by decide : 469172269 ≤ 469237805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 469106733 469237805).card = 415 := join_1_0

end S223C11
end Sude.GeneratedTwinScan
