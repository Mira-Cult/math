import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14875)) 221249581 221282349 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 221249581 221282349).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14875 221249581 221282349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14876)) 221282349 221315117 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 221282349 221315117).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14876 221282349 221315117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14877)) 221315117 221347885 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 221315117 221347885).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14877 221315117 221347885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14878)) 221347885 221380653 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 221347885 221380653).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14878 221347885 221380653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 221249581 221315117).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 221249581 ≤ 221282349)
    (by decide : 221282349 ≤ 221315117) block0 block1

theorem join_0_1 : (twinPrimeSegment 221315117 221380653).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 221315117 ≤ 221347885)
    (by decide : 221347885 ≤ 221380653) block2 block3

theorem join_1_0 : (twinPrimeSegment 221249581 221380653).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 221249581 ≤ 221315117)
    (by decide : 221315117 ≤ 221380653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 221249581 221380653).card = 487 := join_1_0

end S105C08
end Sude.GeneratedTwinScan
