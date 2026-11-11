import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17288)) 298844205 298876973 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 298844205 298876973).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17288 298844205 298876973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17289)) 298876973 298909741 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 298876973 298909741).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17289 298876973 298909741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17289)) 298909741 298942509 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 298909741 298942509).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17289 298909741 298942509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17290)) 298942509 298975277 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 298942509 298975277).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17290 298942509 298975277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 298844205 298909741).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 298844205 ≤ 298876973)
    (by decide : 298876973 ≤ 298909741) block0 block1

theorem join_0_1 : (twinPrimeSegment 298909741 298975277).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 298909741 ≤ 298942509)
    (by decide : 298942509 ≤ 298975277) block2 block3

theorem join_1_0 : (twinPrimeSegment 298844205 298975277).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 298844205 ≤ 298909741)
    (by decide : 298909741 ≤ 298975277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 298844205 298975277).card = 439 := join_1_0

end S142C08
end Sude.GeneratedTwinScan
