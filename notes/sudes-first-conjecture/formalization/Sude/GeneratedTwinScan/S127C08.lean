import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16352)) 267386925 267419693 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 267386925 267419693).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16352 267386925 267419693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16353)) 267419693 267452461 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 267419693 267452461).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16353 267419693 267452461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16354)) 267452461 267485229 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 267452461 267485229).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16354 267452461 267485229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16355)) 267485229 267517997 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 267485229 267517997).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16355 267485229 267517997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 267386925 267452461).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 267386925 ≤ 267419693)
    (by decide : 267419693 ≤ 267452461) block0 block1

theorem join_0_1 : (twinPrimeSegment 267452461 267517997).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 267452461 ≤ 267485229)
    (by decide : 267485229 ≤ 267517997) block2 block3

theorem join_1_0 : (twinPrimeSegment 267386925 267517997).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 267386925 ≤ 267452461)
    (by decide : 267452461 ≤ 267517997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 267386925 267517997).card = 421 := join_1_0

end S127C08
end Sude.GeneratedTwinScan
