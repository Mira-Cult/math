import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21972)) 482738221 482770989 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 482738221 482770989).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21972 482738221 482770989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21972)) 482770989 482803757 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 482770989 482803757).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21972 482770989 482803757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21973)) 482803757 482836525 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 482803757 482836525).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21973 482803757 482836525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21974)) 482836525 482869293 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 482836525 482869293).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21974 482836525 482869293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 482738221 482803757).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 482738221 ≤ 482770989)
    (by decide : 482770989 ≤ 482803757) block0 block1

theorem join_0_1 : (twinPrimeSegment 482803757 482869293).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 482803757 ≤ 482836525)
    (by decide : 482836525 ≤ 482869293) block2 block3

theorem join_1_0 : (twinPrimeSegment 482738221 482869293).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 482738221 ≤ 482803757)
    (by decide : 482803757 ≤ 482869293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 482738221 482869293).card = 420 := join_1_0

end S230C03
end Sude.GeneratedTwinScan
