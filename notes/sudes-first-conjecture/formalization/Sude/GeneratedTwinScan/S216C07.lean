import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21305)) 453902381 453935149 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 453902381 453935149).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21305 453902381 453935149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21306)) 453935149 453967917 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 453935149 453967917).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21306 453935149 453967917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21307)) 453967917 454000685 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 453967917 454000685).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21307 453967917 454000685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21308)) 454000685 454033453 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 454000685 454033453).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21308 454000685 454033453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 453902381 453967917).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 453902381 ≤ 453935149)
    (by decide : 453935149 ≤ 453967917) block0 block1

theorem join_0_1 : (twinPrimeSegment 453967917 454033453).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 453967917 ≤ 454000685)
    (by decide : 454000685 ≤ 454033453) block2 block3

theorem join_1_0 : (twinPrimeSegment 453902381 454033453).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 453902381 ≤ 453967917)
    (by decide : 453967917 ≤ 454033453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 453902381 454033453).card = 429 := join_1_0

end S216C07
end Sude.GeneratedTwinScan
