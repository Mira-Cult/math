import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17101)) 292421677 292454445 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 292421677 292454445).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17101 292421677 292454445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17102)) 292454445 292487213 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 292454445 292487213).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17102 292454445 292487213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17103)) 292487213 292519981 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 292487213 292519981).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17103 292487213 292519981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17104)) 292519981 292552749 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 292519981 292552749).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17104 292519981 292552749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 292421677 292487213).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 292421677 ≤ 292454445)
    (by decide : 292454445 ≤ 292487213) block0 block1

theorem join_0_1 : (twinPrimeSegment 292487213 292552749).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 292487213 ≤ 292519981)
    (by decide : 292519981 ≤ 292552749) block2 block3

theorem join_1_0 : (twinPrimeSegment 292421677 292552749).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 292421677 ≤ 292487213)
    (by decide : 292487213 ≤ 292552749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 292421677 292552749).card = 429 := join_1_0

end S139C07
end Sude.GeneratedTwinScan
