import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13720)) 188219437 188252205 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 188219437 188252205).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13720 188219437 188252205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13721)) 188252205 188284973 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 188252205 188284973).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13721 188252205 188284973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13722)) 188284973 188317741 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 188284973 188317741).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13722 188284973 188317741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13724)) 188317741 188350509 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 188317741 188350509).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13724 188317741 188350509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 188219437 188284973).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 188219437 ≤ 188252205)
    (by decide : 188252205 ≤ 188284973) block0 block1

theorem join_0_1 : (twinPrimeSegment 188284973 188350509).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 188284973 ≤ 188317741)
    (by decide : 188317741 ≤ 188350509) block2 block3

theorem join_1_0 : (twinPrimeSegment 188219437 188350509).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 188219437 ≤ 188284973)
    (by decide : 188284973 ≤ 188350509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 188219437 188350509).card = 474 := join_1_0

end S089C12
end Sude.GeneratedTwinScan
