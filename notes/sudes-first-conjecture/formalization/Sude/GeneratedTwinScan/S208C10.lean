import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20917)) 437518381 437551149 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 437518381 437551149).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20917 437518381 437551149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20918)) 437551149 437583917 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 437551149 437583917).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20918 437551149 437583917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20919)) 437583917 437616685 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 437583917 437616685).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20919 437583917 437616685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20920)) 437616685 437649453 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 437616685 437649453).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20920 437616685 437649453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 437518381 437583917).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 437518381 ≤ 437551149)
    (by decide : 437551149 ≤ 437583917) block0 block1

theorem join_0_1 : (twinPrimeSegment 437583917 437649453).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 437583917 ≤ 437616685)
    (by decide : 437616685 ≤ 437649453) block2 block3

theorem join_1_0 : (twinPrimeSegment 437518381 437649453).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 437518381 ≤ 437583917)
    (by decide : 437583917 ≤ 437649453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 437518381 437649453).card = 440 := join_1_0

end S208C10
end Sude.GeneratedTwinScan
