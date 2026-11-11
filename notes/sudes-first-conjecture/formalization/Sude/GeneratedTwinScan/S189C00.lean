import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19909)) 396361773 396394541 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 396361773 396394541).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19909 396361773 396394541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19910)) 396394541 396427309 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 396394541 396427309).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19910 396394541 396427309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19911)) 396427309 396460077 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 396427309 396460077).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19911 396427309 396460077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19912)) 396460077 396492845 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 396460077 396492845).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19912 396460077 396492845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 396361773 396427309).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 396361773 ≤ 396394541)
    (by decide : 396394541 ≤ 396427309) block0 block1

theorem join_0_1 : (twinPrimeSegment 396427309 396492845).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 396427309 ≤ 396460077)
    (by decide : 396460077 ≤ 396492845) block2 block3

theorem join_1_0 : (twinPrimeSegment 396361773 396492845).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 396361773 ≤ 396427309)
    (by decide : 396427309 ≤ 396492845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 396361773 396492845).card = 457 := join_1_0

end S189C00
end Sude.GeneratedTwinScan
