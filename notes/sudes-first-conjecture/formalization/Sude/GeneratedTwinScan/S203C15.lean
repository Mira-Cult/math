import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20681)) 427687981 427720749 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 427687981 427720749).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20681 427687981 427720749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20682)) 427720749 427753517 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 427720749 427753517).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20682 427720749 427753517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20682)) 427753517 427786285 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 427753517 427786285).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20682 427753517 427786285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20683)) 427786285 427819053 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 427786285 427819053).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20683 427786285 427819053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 427687981 427753517).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 427687981 ≤ 427720749)
    (by decide : 427720749 ≤ 427753517) block0 block1

theorem join_0_1 : (twinPrimeSegment 427753517 427819053).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 427753517 ≤ 427786285)
    (by decide : 427786285 ≤ 427819053) block2 block3

theorem join_1_0 : (twinPrimeSegment 427687981 427819053).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 427687981 ≤ 427753517)
    (by decide : 427753517 ≤ 427819053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 427687981 427819053).card = 428 := join_1_0

end S203C15
end Sude.GeneratedTwinScan
