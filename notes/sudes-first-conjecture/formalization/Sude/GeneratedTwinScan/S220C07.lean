import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21501)) 462290989 462323757 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 462290989 462323757).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21501 462290989 462323757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21502)) 462323757 462356525 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 462323757 462356525).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21502 462323757 462356525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21503)) 462356525 462389293 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 462356525 462389293).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21503 462356525 462389293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21504)) 462389293 462422061 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 462389293 462422061).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21504 462389293 462422061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 462290989 462356525).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 462290989 ≤ 462323757)
    (by decide : 462323757 ≤ 462356525) block0 block1

theorem join_0_1 : (twinPrimeSegment 462356525 462422061).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 462356525 ≤ 462389293)
    (by decide : 462389293 ≤ 462422061) block2 block3

theorem join_1_0 : (twinPrimeSegment 462290989 462422061).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 462290989 ≤ 462356525)
    (by decide : 462356525 ≤ 462422061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 462290989 462422061).card = 448 := join_1_0

end S220C07
end Sude.GeneratedTwinScan
