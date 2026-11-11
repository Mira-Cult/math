import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20908)) 437125165 437157933 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 437125165 437157933).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20908 437125165 437157933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20909)) 437157933 437190701 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 437157933 437190701).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20909 437157933 437190701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20909)) 437190701 437223469 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 437190701 437223469).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20909 437190701 437223469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20910)) 437223469 437256237 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 437223469 437256237).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20910 437223469 437256237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 437125165 437190701).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 437125165 ≤ 437157933)
    (by decide : 437157933 ≤ 437190701) block0 block1

theorem join_0_1 : (twinPrimeSegment 437190701 437256237).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 437190701 ≤ 437223469)
    (by decide : 437223469 ≤ 437256237) block2 block3

theorem join_1_0 : (twinPrimeSegment 437125165 437256237).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 437125165 ≤ 437190701)
    (by decide : 437190701 ≤ 437256237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 437125165 437256237).card = 430 := join_1_0

end S208C07
end Sude.GeneratedTwinScan
