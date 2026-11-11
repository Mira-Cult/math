import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14022)) 196608045 196640813 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 196608045 196640813).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14022 196608045 196640813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14024)) 196640813 196673581 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 196640813 196673581).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14024 196640813 196673581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14025)) 196673581 196706349 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 196673581 196706349).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14025 196673581 196706349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14026)) 196706349 196739117 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 196706349 196739117).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14026 196706349 196739117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 196608045 196673581).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 196608045 ≤ 196640813)
    (by decide : 196640813 ≤ 196673581) block0 block1

theorem join_0_1 : (twinPrimeSegment 196673581 196739117).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 196673581 ≤ 196706349)
    (by decide : 196706349 ≤ 196739117) block2 block3

theorem join_1_0 : (twinPrimeSegment 196608045 196739117).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 196608045 ≤ 196673581)
    (by decide : 196673581 ≤ 196739117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 196608045 196739117).card = 464 := join_1_0

end S093C12
end Sude.GeneratedTwinScan
