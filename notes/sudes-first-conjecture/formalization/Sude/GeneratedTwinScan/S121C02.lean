import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15938)) 254017581 254050349 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 254017581 254050349).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15938 254017581 254050349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15939)) 254050349 254083117 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 254050349 254083117).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15939 254050349 254083117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15941)) 254083117 254115885 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 254083117 254115885).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15941 254083117 254115885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15942)) 254115885 254148653 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 254115885 254148653).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15942 254115885 254148653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 254017581 254083117).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 254017581 ≤ 254050349)
    (by decide : 254050349 ≤ 254083117) block0 block1

theorem join_0_1 : (twinPrimeSegment 254083117 254148653).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 254083117 ≤ 254115885)
    (by decide : 254115885 ≤ 254148653) block2 block3

theorem join_1_0 : (twinPrimeSegment 254017581 254148653).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 254017581 ≤ 254083117)
    (by decide : 254083117 ≤ 254148653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 254017581 254148653).card = 437 := join_1_0

end S121C02
end Sude.GeneratedTwinScan
