import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21897)) 479461421 479494189 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 479461421 479494189).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21897 479461421 479494189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21898)) 479494189 479526957 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 479494189 479526957).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21898 479494189 479526957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21898)) 479526957 479559725 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 479526957 479559725).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21898 479526957 479559725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21899)) 479559725 479592493 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 479559725 479592493).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21899 479559725 479592493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 479461421 479526957).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 479461421 ≤ 479494189)
    (by decide : 479494189 ≤ 479526957) block0 block1

theorem join_0_1 : (twinPrimeSegment 479526957 479592493).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 479526957 ≤ 479559725)
    (by decide : 479559725 ≤ 479592493) block2 block3

theorem join_1_0 : (twinPrimeSegment 479461421 479592493).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 479461421 ≤ 479526957)
    (by decide : 479526957 ≤ 479592493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 479461421 479592493).card = 442 := join_1_0

end S228C10
end Sude.GeneratedTwinScan
