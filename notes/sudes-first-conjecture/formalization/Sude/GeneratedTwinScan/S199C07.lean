import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20451)) 418250797 418283565 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 418250797 418283565).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20451 418250797 418283565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20452)) 418283565 418316333 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 418283565 418316333).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20452 418283565 418316333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20453)) 418316333 418349101 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 418316333 418349101).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20453 418316333 418349101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20454)) 418349101 418381869 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 418349101 418381869).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20454 418349101 418381869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 418250797 418316333).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 418250797 ≤ 418283565)
    (by decide : 418283565 ≤ 418316333) block0 block1

theorem join_0_1 : (twinPrimeSegment 418316333 418381869).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 418316333 ≤ 418349101)
    (by decide : 418349101 ≤ 418381869) block2 block3

theorem join_1_0 : (twinPrimeSegment 418250797 418381869).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 418250797 ≤ 418316333)
    (by decide : 418316333 ≤ 418381869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 418250797 418381869).card = 463 := join_1_0

end S199C07
end Sude.GeneratedTwinScan
