import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22766)) 518258733 518291501 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 518258733 518291501).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22766 518258733 518291501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22766)) 518291501 518324269 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 518291501 518324269).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22766 518291501 518324269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22767)) 518324269 518357037 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 518324269 518357037).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22767 518324269 518357037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22768)) 518357037 518389805 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 518357037 518389805).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22768 518357037 518389805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 518258733 518324269).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 518258733 ≤ 518291501)
    (by decide : 518291501 ≤ 518324269) block0 block1

theorem join_0_1 : (twinPrimeSegment 518324269 518389805).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 518324269 ≤ 518357037)
    (by decide : 518357037 ≤ 518389805) block2 block3

theorem join_1_0 : (twinPrimeSegment 518258733 518389805).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 518258733 ≤ 518324269)
    (by decide : 518324269 ≤ 518389805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 518258733 518389805).card = 455 := join_1_0

end S247C02
end Sude.GeneratedTwinScan
