import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21888)) 479068205 479100973 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 479068205 479100973).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21888 479068205 479100973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21889)) 479100973 479133741 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 479100973 479133741).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21889 479100973 479133741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21889)) 479133741 479166509 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 479133741 479166509).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21889 479133741 479166509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21890)) 479166509 479199277 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 479166509 479199277).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21890 479166509 479199277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 479068205 479133741).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 479068205 ≤ 479100973)
    (by decide : 479100973 ≤ 479133741) block0 block1

theorem join_0_1 : (twinPrimeSegment 479133741 479199277).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 479133741 ≤ 479166509)
    (by decide : 479166509 ≤ 479199277) block2 block3

theorem join_1_0 : (twinPrimeSegment 479068205 479199277).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 479068205 ≤ 479133741)
    (by decide : 479133741 ≤ 479199277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 479068205 479199277).card = 439 := join_1_0

end S228C07
end Sude.GeneratedTwinScan
