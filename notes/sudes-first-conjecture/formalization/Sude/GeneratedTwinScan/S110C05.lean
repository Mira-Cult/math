import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15211)) 231342125 231374893 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 231342125 231374893).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15211 231342125 231374893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15212)) 231374893 231407661 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 231374893 231407661).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15212 231374893 231407661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15213)) 231407661 231440429 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 231407661 231440429).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15213 231407661 231440429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15214)) 231440429 231473197 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 231440429 231473197).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15214 231440429 231473197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 231342125 231407661).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 231342125 ≤ 231374893)
    (by decide : 231374893 ≤ 231407661) block0 block1

theorem join_0_1 : (twinPrimeSegment 231407661 231473197).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 231407661 ≤ 231440429)
    (by decide : 231440429 ≤ 231473197) block2 block3

theorem join_1_0 : (twinPrimeSegment 231342125 231473197).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 231342125 ≤ 231407661)
    (by decide : 231407661 ≤ 231473197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 231342125 231473197).card = 503 := join_1_0

end S110C05
end Sude.GeneratedTwinScan
