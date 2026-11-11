import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22837)) 521535533 521568301 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 521535533 521568301).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22837 521535533 521568301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22838)) 521568301 521601069 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 521568301 521601069).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22838 521568301 521601069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22839)) 521601069 521633837 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 521601069 521633837).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22839 521601069 521633837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22840)) 521633837 521666605 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 521633837 521666605).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22840 521633837 521666605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 521535533 521601069).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 521535533 ≤ 521568301)
    (by decide : 521568301 ≤ 521601069) block0 block1

theorem join_0_1 : (twinPrimeSegment 521601069 521666605).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 521601069 ≤ 521633837)
    (by decide : 521633837 ≤ 521666605) block2 block3

theorem join_1_0 : (twinPrimeSegment 521535533 521666605).card = 411 := by
  simpa using combineTwinPrimeSegments (by decide : 521535533 ≤ 521601069)
    (by decide : 521601069 ≤ 521666605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 521535533 521666605).card = 411 := join_1_0

end S248C11
end Sude.GeneratedTwinScan
