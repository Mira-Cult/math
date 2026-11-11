import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13254)) 175636525 175669293 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 175636525 175669293).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13254 175636525 175669293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13255)) 175669293 175702061 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 175669293 175702061).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13255 175669293 175702061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13256)) 175702061 175734829 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 175702061 175734829).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13256 175702061 175734829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13257)) 175734829 175767597 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 175734829 175767597).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13257 175734829 175767597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 175636525 175702061).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 175636525 ≤ 175669293)
    (by decide : 175669293 ≤ 175702061) block0 block1

theorem join_0_1 : (twinPrimeSegment 175702061 175767597).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 175702061 ≤ 175734829)
    (by decide : 175734829 ≤ 175767597) block2 block3

theorem join_1_0 : (twinPrimeSegment 175636525 175767597).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 175636525 ≤ 175702061)
    (by decide : 175702061 ≤ 175767597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 175636525 175767597).card = 462 := join_1_0

end S083C12
end Sude.GeneratedTwinScan
