import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21045)) 442892333 442925101 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 442892333 442925101).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21045 442892333 442925101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21046)) 442925101 442957869 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 442925101 442957869).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21046 442925101 442957869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21047)) 442957869 442990637 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 442957869 442990637).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21047 442957869 442990637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21048)) 442990637 443023405 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 442990637 443023405).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21048 442990637 443023405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 442892333 442957869).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 442892333 ≤ 442925101)
    (by decide : 442925101 ≤ 442957869) block0 block1

theorem join_0_1 : (twinPrimeSegment 442957869 443023405).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 442957869 ≤ 442990637)
    (by decide : 442990637 ≤ 443023405) block2 block3

theorem join_1_0 : (twinPrimeSegment 442892333 443023405).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 442892333 ≤ 442957869)
    (by decide : 442957869 ≤ 443023405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 442892333 443023405).card = 438 := join_1_0

end S211C03
end Sude.GeneratedTwinScan
