import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14980)) 224395309 224428077 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 224395309 224428077).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14980 224395309 224428077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14982)) 224428077 224460845 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 224428077 224460845).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14982 224428077 224460845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14983)) 224460845 224493613 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 224460845 224493613).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14983 224460845 224493613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14984)) 224493613 224526381 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 224493613 224526381).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14984 224493613 224526381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 224395309 224460845).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 224395309 ≤ 224428077)
    (by decide : 224428077 ≤ 224460845) block0 block1

theorem join_0_1 : (twinPrimeSegment 224460845 224526381).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 224460845 ≤ 224493613)
    (by decide : 224493613 ≤ 224526381) block2 block3

theorem join_1_0 : (twinPrimeSegment 224395309 224526381).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 224395309 ≤ 224460845)
    (by decide : 224460845 ≤ 224526381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 224395309 224526381).card = 455 := join_1_0

end S107C00
end Sude.GeneratedTwinScan
