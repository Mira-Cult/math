import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21333)) 455082029 455114797 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 455082029 455114797).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21333 455082029 455114797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21334)) 455114797 455147565 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 455114797 455147565).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21334 455114797 455147565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21334)) 455147565 455180333 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 455147565 455180333).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21334 455147565 455180333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21335)) 455180333 455213101 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 455180333 455213101).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21335 455180333 455213101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 455082029 455147565).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 455082029 ≤ 455114797)
    (by decide : 455114797 ≤ 455147565) block0 block1

theorem join_0_1 : (twinPrimeSegment 455147565 455213101).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 455147565 ≤ 455180333)
    (by decide : 455180333 ≤ 455213101) block2 block3

theorem join_1_0 : (twinPrimeSegment 455082029 455213101).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 455082029 ≤ 455147565)
    (by decide : 455147565 ≤ 455213101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 455082029 455213101).card = 457 := join_1_0

end S217C00
end Sude.GeneratedTwinScan
