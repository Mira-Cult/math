import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17491)) 305922093 305954861 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 305922093 305954861).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17491 305922093 305954861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17492)) 305954861 305987629 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 305954861 305987629).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17492 305954861 305987629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17493)) 305987629 306020397 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 305987629 306020397).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17493 305987629 306020397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17494)) 306020397 306053165 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 306020397 306053165).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17494 306020397 306053165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 305922093 305987629).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 305922093 ≤ 305954861)
    (by decide : 305954861 ≤ 305987629) block0 block1

theorem join_0_1 : (twinPrimeSegment 305987629 306053165).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 305987629 ≤ 306020397)
    (by decide : 306020397 ≤ 306053165) block2 block3

theorem join_1_0 : (twinPrimeSegment 305922093 306053165).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 305922093 ≤ 305987629)
    (by decide : 305987629 ≤ 306053165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 305922093 306053165).card = 447 := join_1_0

end S145C14
end Sude.GeneratedTwinScan
