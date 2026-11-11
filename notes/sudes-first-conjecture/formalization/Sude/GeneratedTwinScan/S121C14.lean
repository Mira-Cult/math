import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15988)) 255590445 255623213 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 255590445 255623213).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15988 255590445 255623213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15989)) 255623213 255655981 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 255623213 255655981).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15989 255623213 255655981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15990)) 255655981 255688749 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 255655981 255688749).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15990 255655981 255688749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15991)) 255688749 255721517 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 255688749 255721517).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15991 255688749 255721517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 255590445 255655981).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 255590445 ≤ 255623213)
    (by decide : 255623213 ≤ 255655981) block0 block1

theorem join_0_1 : (twinPrimeSegment 255655981 255721517).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 255655981 ≤ 255688749)
    (by decide : 255688749 ≤ 255721517) block2 block3

theorem join_1_0 : (twinPrimeSegment 255590445 255721517).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 255590445 ≤ 255655981)
    (by decide : 255655981 ≤ 255721517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 255590445 255721517).card = 457 := join_1_0

end S121C14
end Sude.GeneratedTwinScan
