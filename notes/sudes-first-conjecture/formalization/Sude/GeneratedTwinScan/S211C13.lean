import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21076)) 444203053 444235821 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 444203053 444235821).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21076 444203053 444235821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21077)) 444235821 444268589 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 444235821 444268589).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21077 444235821 444268589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21078)) 444268589 444301357 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 444268589 444301357).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21078 444268589 444301357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21079)) 444301357 444334125 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 444301357 444334125).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21079 444301357 444334125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 444203053 444268589).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 444203053 ≤ 444235821)
    (by decide : 444235821 ≤ 444268589) block0 block1

theorem join_0_1 : (twinPrimeSegment 444268589 444334125).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 444268589 ≤ 444301357)
    (by decide : 444301357 ≤ 444334125) block2 block3

theorem join_1_0 : (twinPrimeSegment 444203053 444334125).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 444203053 ≤ 444268589)
    (by decide : 444268589 ≤ 444334125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 444203053 444334125).card = 425 := join_1_0

end S211C13
end Sude.GeneratedTwinScan
