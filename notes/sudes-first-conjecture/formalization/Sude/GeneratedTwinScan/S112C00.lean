import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15326)) 234881069 234913837 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 234881069 234913837).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15326 234881069 234913837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15327)) 234913837 234946605 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 234913837 234946605).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15327 234913837 234946605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15329)) 234946605 234979373 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 234946605 234979373).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15329 234946605 234979373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15330)) 234979373 235012141 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 234979373 235012141).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15330 234979373 235012141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 234881069 234946605).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 234913837)
    (by decide : 234913837 ≤ 234946605) block0 block1

theorem join_0_1 : (twinPrimeSegment 234946605 235012141).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 234946605 ≤ 234979373)
    (by decide : 234979373 ≤ 235012141) block2 block3

theorem join_1_0 : (twinPrimeSegment 234881069 235012141).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 234946605)
    (by decide : 234946605 ≤ 235012141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 234881069 235012141).card = 472 := join_1_0

end S112C00
end Sude.GeneratedTwinScan
