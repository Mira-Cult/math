import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19889)) 395575341 395608109 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 395575341 395608109).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19889 395575341 395608109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19890)) 395608109 395640877 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 395608109 395640877).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19890 395608109 395640877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19891)) 395640877 395673645 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 395640877 395673645).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19891 395640877 395673645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19892)) 395673645 395706413 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 395673645 395706413).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19892 395673645 395706413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 395575341 395640877).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 395575341 ≤ 395608109)
    (by decide : 395608109 ≤ 395640877) block0 block1

theorem join_0_1 : (twinPrimeSegment 395640877 395706413).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 395640877 ≤ 395673645)
    (by decide : 395673645 ≤ 395706413) block2 block3

theorem join_1_0 : (twinPrimeSegment 395575341 395706413).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 395575341 ≤ 395640877)
    (by decide : 395640877 ≤ 395706413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 395575341 395706413).card = 436 := join_1_0

end S188C10
end Sude.GeneratedTwinScan
