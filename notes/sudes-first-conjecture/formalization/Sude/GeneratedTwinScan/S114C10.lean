import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15505)) 240386093 240418861 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 240386093 240418861).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15505 240386093 240418861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15506)) 240418861 240451629 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 240418861 240451629).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15506 240418861 240451629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15507)) 240451629 240484397 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 240451629 240484397).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15507 240451629 240484397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15508)) 240484397 240517165 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 240484397 240517165).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15508 240484397 240517165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 240386093 240451629).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 240386093 ≤ 240418861)
    (by decide : 240418861 ≤ 240451629) block0 block1

theorem join_0_1 : (twinPrimeSegment 240451629 240517165).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 240451629 ≤ 240484397)
    (by decide : 240484397 ≤ 240517165) block2 block3

theorem join_1_0 : (twinPrimeSegment 240386093 240517165).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 240386093 ≤ 240451629)
    (by decide : 240451629 ≤ 240517165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 240386093 240517165).card = 479 := join_1_0

end S114C10
end Sude.GeneratedTwinScan
