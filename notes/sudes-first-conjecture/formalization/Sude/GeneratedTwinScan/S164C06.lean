import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18567)) 344719405 344752173 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 344719405 344752173).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18567 344719405 344752173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18568)) 344752173 344784941 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 344752173 344784941).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18568 344752173 344784941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18569)) 344784941 344817709 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 344784941 344817709).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18569 344784941 344817709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18570)) 344817709 344850477 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 344817709 344850477).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18570 344817709 344850477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 344719405 344784941).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 344719405 ≤ 344752173)
    (by decide : 344752173 ≤ 344784941) block0 block1

theorem join_0_1 : (twinPrimeSegment 344784941 344850477).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 344784941 ≤ 344817709)
    (by decide : 344817709 ≤ 344850477) block2 block3

theorem join_1_0 : (twinPrimeSegment 344719405 344850477).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 344719405 ≤ 344784941)
    (by decide : 344784941 ≤ 344850477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 344719405 344850477).card = 463 := join_1_0

end S164C06
end Sude.GeneratedTwinScan
