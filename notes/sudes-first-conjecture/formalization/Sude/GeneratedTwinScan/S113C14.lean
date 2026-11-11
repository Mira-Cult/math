import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15454)) 238813229 238845997 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 238813229 238845997).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15454 238813229 238845997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15455)) 238845997 238878765 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 238845997 238878765).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15455 238845997 238878765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15456)) 238878765 238911533 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 238878765 238911533).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15456 238878765 238911533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15457)) 238911533 238944301 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 238911533 238944301).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15457 238911533 238944301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 238813229 238878765).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 238813229 ≤ 238845997)
    (by decide : 238845997 ≤ 238878765) block0 block1

theorem join_0_1 : (twinPrimeSegment 238878765 238944301).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 238878765 ≤ 238911533)
    (by decide : 238911533 ≤ 238944301) block2 block3

theorem join_1_0 : (twinPrimeSegment 238813229 238944301).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 238813229 ≤ 238878765)
    (by decide : 238878765 ≤ 238944301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 238813229 238944301).card = 470 := join_1_0

end S113C14
end Sude.GeneratedTwinScan
