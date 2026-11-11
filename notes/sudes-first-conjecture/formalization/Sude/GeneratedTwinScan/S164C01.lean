import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18549)) 344064045 344096813 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 344064045 344096813).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18549 344064045 344096813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18550)) 344096813 344129581 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 344096813 344129581).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18550 344096813 344129581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18551)) 344129581 344162349 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 344129581 344162349).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18551 344129581 344162349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18552)) 344162349 344195117 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 344162349 344195117).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18552 344162349 344195117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 344064045 344129581).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 344064045 ≤ 344096813)
    (by decide : 344096813 ≤ 344129581) block0 block1

theorem join_0_1 : (twinPrimeSegment 344129581 344195117).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 344129581 ≤ 344162349)
    (by decide : 344162349 ≤ 344195117) block2 block3

theorem join_1_0 : (twinPrimeSegment 344064045 344195117).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 344064045 ≤ 344129581)
    (by decide : 344129581 ≤ 344195117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 344064045 344195117).card = 504 := join_1_0

end S164C01
end Sude.GeneratedTwinScan
