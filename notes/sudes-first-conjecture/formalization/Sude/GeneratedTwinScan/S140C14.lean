import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17189)) 295436333 295469101 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 295436333 295469101).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17189 295436333 295469101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17190)) 295469101 295501869 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 295469101 295501869).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17190 295469101 295501869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17191)) 295501869 295534637 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 295501869 295534637).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17191 295501869 295534637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17192)) 295534637 295567405 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 295534637 295567405).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17192 295534637 295567405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 295436333 295501869).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 295436333 ≤ 295469101)
    (by decide : 295469101 ≤ 295501869) block0 block1

theorem join_0_1 : (twinPrimeSegment 295501869 295567405).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 295501869 ≤ 295534637)
    (by decide : 295534637 ≤ 295567405) block2 block3

theorem join_1_0 : (twinPrimeSegment 295436333 295567405).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 295436333 ≤ 295501869)
    (by decide : 295501869 ≤ 295567405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 295436333 295567405).card = 466 := join_1_0

end S140C14
end Sude.GeneratedTwinScan
