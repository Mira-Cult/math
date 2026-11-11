import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21504)) 462422061 462454829 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 462422061 462454829).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21504 462422061 462454829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21505)) 462454829 462487597 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 462454829 462487597).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21505 462454829 462487597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21506)) 462487597 462520365 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 462487597 462520365).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21506 462487597 462520365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21507)) 462520365 462553133 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 462520365 462553133).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21507 462520365 462553133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 462422061 462487597).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 462422061 ≤ 462454829)
    (by decide : 462454829 ≤ 462487597) block0 block1

theorem join_0_1 : (twinPrimeSegment 462487597 462553133).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 462487597 ≤ 462520365)
    (by decide : 462520365 ≤ 462553133) block2 block3

theorem join_1_0 : (twinPrimeSegment 462422061 462553133).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 462422061 ≤ 462487597)
    (by decide : 462487597 ≤ 462553133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 462422061 462553133).card = 424 := join_1_0

end S220C08
end Sude.GeneratedTwinScan
