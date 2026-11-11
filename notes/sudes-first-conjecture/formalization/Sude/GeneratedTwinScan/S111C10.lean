import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15301)) 234094637 234127405 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 234094637 234127405).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15301 234094637 234127405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15302)) 234127405 234160173 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 234127405 234160173).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15302 234127405 234160173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15303)) 234160173 234192941 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 234160173 234192941).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15303 234160173 234192941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15304)) 234192941 234225709 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 234192941 234225709).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15304 234192941 234225709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 234094637 234160173).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 234094637 ≤ 234127405)
    (by decide : 234127405 ≤ 234160173) block0 block1

theorem join_0_1 : (twinPrimeSegment 234160173 234225709).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 234160173 ≤ 234192941)
    (by decide : 234192941 ≤ 234225709) block2 block3

theorem join_1_0 : (twinPrimeSegment 234094637 234225709).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 234094637 ≤ 234160173)
    (by decide : 234160173 ≤ 234225709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 234094637 234225709).card = 473 := join_1_0

end S111C10
end Sude.GeneratedTwinScan
