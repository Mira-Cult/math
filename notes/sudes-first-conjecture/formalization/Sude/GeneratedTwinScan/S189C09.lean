import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19939)) 397541421 397574189 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 397541421 397574189).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19939 397541421 397574189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19940)) 397574189 397606957 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 397574189 397606957).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19940 397574189 397606957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19940)) 397606957 397639725 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 397606957 397639725).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19940 397606957 397639725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19941)) 397639725 397672493 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 397639725 397672493).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19941 397639725 397672493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 397541421 397606957).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 397541421 ≤ 397574189)
    (by decide : 397574189 ≤ 397606957) block0 block1

theorem join_0_1 : (twinPrimeSegment 397606957 397672493).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 397606957 ≤ 397639725)
    (by decide : 397639725 ≤ 397672493) block2 block3

theorem join_1_0 : (twinPrimeSegment 397541421 397672493).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 397541421 ≤ 397606957)
    (by decide : 397606957 ≤ 397672493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 397541421 397672493).card = 426 := join_1_0

end S189C09
end Sude.GeneratedTwinScan
