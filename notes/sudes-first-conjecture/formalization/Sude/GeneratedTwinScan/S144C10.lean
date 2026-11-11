import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17416)) 303300653 303333421 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 303300653 303333421).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17416 303300653 303333421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17417)) 303333421 303366189 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 303333421 303366189).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17417 303333421 303366189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17418)) 303366189 303398957 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 303366189 303398957).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17418 303366189 303398957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17419)) 303398957 303431725 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 303398957 303431725).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17419 303398957 303431725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 303300653 303366189).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 303300653 ≤ 303333421)
    (by decide : 303333421 ≤ 303366189) block0 block1

theorem join_0_1 : (twinPrimeSegment 303366189 303431725).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 303366189 ≤ 303398957)
    (by decide : 303398957 ≤ 303431725) block2 block3

theorem join_1_0 : (twinPrimeSegment 303300653 303431725).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 303300653 ≤ 303366189)
    (by decide : 303366189 ≤ 303431725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 303300653 303431725).card = 443 := join_1_0

end S144C10
end Sude.GeneratedTwinScan
