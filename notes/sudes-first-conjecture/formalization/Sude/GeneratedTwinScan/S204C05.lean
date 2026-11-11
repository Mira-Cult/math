import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20700)) 428474413 428507181 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 428474413 428507181).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20700 428474413 428507181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20701)) 428507181 428539949 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 428507181 428539949).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20701 428507181 428539949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20701)) 428539949 428572717 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 428539949 428572717).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20701 428539949 428572717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20702)) 428572717 428605485 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 428572717 428605485).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20702 428572717 428605485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 428474413 428539949).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 428474413 ≤ 428507181)
    (by decide : 428507181 ≤ 428539949) block0 block1

theorem join_0_1 : (twinPrimeSegment 428539949 428605485).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 428539949 ≤ 428572717)
    (by decide : 428572717 ≤ 428605485) block2 block3

theorem join_1_0 : (twinPrimeSegment 428474413 428605485).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 428474413 ≤ 428539949)
    (by decide : 428539949 ≤ 428605485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 428474413 428605485).card = 424 := join_1_0

end S204C05
end Sude.GeneratedTwinScan
