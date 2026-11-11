import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18265)) 333578285 333611053 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 333578285 333611053).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18265 333578285 333611053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18265)) 333611053 333643821 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 333611053 333643821).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18265 333611053 333643821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18266)) 333643821 333676589 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 333643821 333676589).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18266 333643821 333676589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18267)) 333676589 333709357 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 333676589 333709357).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18267 333676589 333709357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 333578285 333643821).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 333578285 ≤ 333611053)
    (by decide : 333611053 ≤ 333643821) block0 block1

theorem join_0_1 : (twinPrimeSegment 333643821 333709357).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 333643821 ≤ 333676589)
    (by decide : 333676589 ≤ 333709357) block2 block3

theorem join_1_0 : (twinPrimeSegment 333578285 333709357).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 333578285 ≤ 333643821)
    (by decide : 333643821 ≤ 333709357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 333578285 333709357).card = 440 := join_1_0

end S159C01
end Sude.GeneratedTwinScan
