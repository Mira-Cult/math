import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17584)) 309198893 309231661 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 309198893 309231661).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17584 309198893 309231661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17585)) 309231661 309264429 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 309231661 309264429).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17585 309231661 309264429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17586)) 309264429 309297197 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 309264429 309297197).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17586 309264429 309297197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17587)) 309297197 309329965 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 309297197 309329965).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17587 309297197 309329965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 309198893 309264429).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 309198893 ≤ 309231661)
    (by decide : 309231661 ≤ 309264429) block0 block1

theorem join_0_1 : (twinPrimeSegment 309264429 309329965).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 309264429 ≤ 309297197)
    (by decide : 309297197 ≤ 309329965) block2 block3

theorem join_1_0 : (twinPrimeSegment 309198893 309329965).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 309198893 ≤ 309264429)
    (by decide : 309264429 ≤ 309329965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 309198893 309329965).card = 436 := join_1_0

end S147C07
end Sude.GeneratedTwinScan
