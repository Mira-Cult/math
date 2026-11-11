import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18457)) 340656173 340688941 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 340656173 340688941).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18457 340656173 340688941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18458)) 340688941 340721709 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 340688941 340721709).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18458 340688941 340721709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18459)) 340721709 340754477 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 340721709 340754477).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18459 340721709 340754477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18460)) 340754477 340787245 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 340754477 340787245).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18460 340754477 340787245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 340656173 340721709).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 340656173 ≤ 340688941)
    (by decide : 340688941 ≤ 340721709) block0 block1

theorem join_0_1 : (twinPrimeSegment 340721709 340787245).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 340721709 ≤ 340754477)
    (by decide : 340754477 ≤ 340787245) block2 block3

theorem join_1_0 : (twinPrimeSegment 340656173 340787245).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 340656173 ≤ 340721709)
    (by decide : 340721709 ≤ 340787245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 340656173 340787245).card = 448 := join_1_0

end S162C07
end Sude.GeneratedTwinScan
