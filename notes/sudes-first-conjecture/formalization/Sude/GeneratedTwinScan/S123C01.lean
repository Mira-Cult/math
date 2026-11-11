import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16065)) 258080813 258113581 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 258080813 258113581).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16065 258080813 258113581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16066)) 258113581 258146349 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 258113581 258146349).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16066 258113581 258146349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16067)) 258146349 258179117 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 258146349 258179117).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16067 258146349 258179117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16068)) 258179117 258211885 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 258179117 258211885).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16068 258179117 258211885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 258080813 258146349).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 258080813 ≤ 258113581)
    (by decide : 258113581 ≤ 258146349) block0 block1

theorem join_0_1 : (twinPrimeSegment 258146349 258211885).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 258146349 ≤ 258179117)
    (by decide : 258179117 ≤ 258211885) block2 block3

theorem join_1_0 : (twinPrimeSegment 258080813 258211885).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 258080813 ≤ 258146349)
    (by decide : 258146349 ≤ 258211885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 258080813 258211885).card = 460 := join_1_0

end S123C01
end Sude.GeneratedTwinScan
