import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17644)) 311296045 311328813 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 311296045 311328813).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17644 311296045 311328813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17645)) 311328813 311361581 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 311328813 311361581).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17645 311328813 311361581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17646)) 311361581 311394349 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 311361581 311394349).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17646 311361581 311394349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17647)) 311394349 311427117 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 311394349 311427117).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17647 311394349 311427117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 311296045 311361581).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 311296045 ≤ 311328813)
    (by decide : 311328813 ≤ 311361581) block0 block1

theorem join_0_1 : (twinPrimeSegment 311361581 311427117).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 311361581 ≤ 311394349)
    (by decide : 311394349 ≤ 311427117) block2 block3

theorem join_1_0 : (twinPrimeSegment 311296045 311427117).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 311296045 ≤ 311361581)
    (by decide : 311361581 ≤ 311427117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 311296045 311427117).card = 417 := join_1_0

end S148C07
end Sude.GeneratedTwinScan
