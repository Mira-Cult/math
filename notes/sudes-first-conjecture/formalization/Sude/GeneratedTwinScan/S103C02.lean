import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14707)) 216268845 216301613 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 216268845 216301613).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14707 216268845 216301613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14708)) 216301613 216334381 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 216301613 216334381).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14708 216301613 216334381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14709)) 216334381 216367149 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 216334381 216367149).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14709 216334381 216367149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14710)) 216367149 216399917 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 216367149 216399917).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14710 216367149 216399917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 216268845 216334381).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 216268845 ≤ 216301613)
    (by decide : 216301613 ≤ 216334381) block0 block1

theorem join_0_1 : (twinPrimeSegment 216334381 216399917).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 216334381 ≤ 216367149)
    (by decide : 216367149 ≤ 216399917) block2 block3

theorem join_1_0 : (twinPrimeSegment 216268845 216399917).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 216268845 ≤ 216334381)
    (by decide : 216334381 ≤ 216399917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 216268845 216399917).card = 488 := join_1_0

end S103C02
end Sude.GeneratedTwinScan
