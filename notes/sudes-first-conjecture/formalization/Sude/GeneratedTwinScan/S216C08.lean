import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21308)) 454033453 454066221 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 454033453 454066221).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21308 454033453 454066221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21309)) 454066221 454098989 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 454066221 454098989).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21309 454066221 454098989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21310)) 454098989 454131757 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 454098989 454131757).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21310 454098989 454131757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21311)) 454131757 454164525 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 454131757 454164525).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21311 454131757 454164525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 454033453 454098989).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 454033453 ≤ 454066221)
    (by decide : 454066221 ≤ 454098989) block0 block1

theorem join_0_1 : (twinPrimeSegment 454098989 454164525).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 454098989 ≤ 454131757)
    (by decide : 454131757 ≤ 454164525) block2 block3

theorem join_1_0 : (twinPrimeSegment 454033453 454164525).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 454033453 ≤ 454098989)
    (by decide : 454098989 ≤ 454164525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 454033453 454164525).card = 436 := join_1_0

end S216C08
end Sude.GeneratedTwinScan
