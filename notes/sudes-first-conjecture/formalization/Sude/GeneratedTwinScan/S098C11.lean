import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14387)) 206962733 206995501 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 206962733 206995501).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14387 206962733 206995501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14388)) 206995501 207028269 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 206995501 207028269).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14388 206995501 207028269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14389)) 207028269 207061037 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 207028269 207061037).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14389 207028269 207061037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14390)) 207061037 207093805 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 207061037 207093805).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14390 207061037 207093805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 206962733 207028269).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 206962733 ≤ 206995501)
    (by decide : 206995501 ≤ 207028269) block0 block1

theorem join_0_1 : (twinPrimeSegment 207028269 207093805).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 207028269 ≤ 207061037)
    (by decide : 207061037 ≤ 207093805) block2 block3

theorem join_1_0 : (twinPrimeSegment 206962733 207093805).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 206962733 ≤ 207028269)
    (by decide : 207028269 ≤ 207093805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 206962733 207093805).card = 457 := join_1_0

end S098C11
end Sude.GeneratedTwinScan
