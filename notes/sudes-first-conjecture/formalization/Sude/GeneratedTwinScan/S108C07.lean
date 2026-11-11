import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15081)) 227409965 227442733 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 227409965 227442733).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15081 227409965 227442733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15082)) 227442733 227475501 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 227442733 227475501).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15082 227442733 227475501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15083)) 227475501 227508269 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 227475501 227508269).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15083 227475501 227508269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15084)) 227508269 227541037 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 227508269 227541037).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15084 227508269 227541037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 227409965 227475501).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 227409965 ≤ 227442733)
    (by decide : 227442733 ≤ 227475501) block0 block1

theorem join_0_1 : (twinPrimeSegment 227475501 227541037).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 227475501 ≤ 227508269)
    (by decide : 227508269 ≤ 227541037) block2 block3

theorem join_1_0 : (twinPrimeSegment 227409965 227541037).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 227409965 ≤ 227475501)
    (by decide : 227475501 ≤ 227541037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 227409965 227541037).card = 463 := join_1_0

end S108C07
end Sude.GeneratedTwinScan
