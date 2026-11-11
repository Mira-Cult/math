import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20455)) 418381869 418414637 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 418381869 418414637).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20455 418381869 418414637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20455)) 418414637 418447405 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 418414637 418447405).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20455 418414637 418447405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20456)) 418447405 418480173 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 418447405 418480173).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20456 418447405 418480173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20457)) 418480173 418512941 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 418480173 418512941).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20457 418480173 418512941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 418381869 418447405).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 418381869 ≤ 418414637)
    (by decide : 418414637 ≤ 418447405) block0 block1

theorem join_0_1 : (twinPrimeSegment 418447405 418512941).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 418447405 ≤ 418480173)
    (by decide : 418480173 ≤ 418512941) block2 block3

theorem join_1_0 : (twinPrimeSegment 418381869 418512941).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 418381869 ≤ 418447405)
    (by decide : 418447405 ≤ 418512941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 418381869 418512941).card = 454 := join_1_0

end S199C08
end Sude.GeneratedTwinScan
