import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15598)) 243269677 243302445 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 243269677 243302445).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15598 243269677 243302445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15599)) 243302445 243335213 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 243302445 243335213).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15599 243302445 243335213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15600)) 243335213 243367981 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 243335213 243367981).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15600 243335213 243367981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15601)) 243367981 243400749 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 243367981 243400749).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15601 243367981 243400749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 243269677 243335213).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 243269677 ≤ 243302445)
    (by decide : 243302445 ≤ 243335213) block0 block1

theorem join_0_1 : (twinPrimeSegment 243335213 243400749).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 243335213 ≤ 243367981)
    (by decide : 243367981 ≤ 243400749) block2 block3

theorem join_1_0 : (twinPrimeSegment 243269677 243400749).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 243269677 ≤ 243335213)
    (by decide : 243335213 ≤ 243400749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 243269677 243400749).card = 458 := join_1_0

end S116C00
end Sude.GeneratedTwinScan
