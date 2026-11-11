import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15860)) 251527213 251559981 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 251527213 251559981).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15860 251527213 251559981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15861)) 251559981 251592749 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 251559981 251592749).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15861 251559981 251592749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15862)) 251592749 251625517 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 251592749 251625517).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15862 251592749 251625517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15863)) 251625517 251658285 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 251625517 251658285).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15863 251625517 251658285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 251527213 251592749).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 251527213 ≤ 251559981)
    (by decide : 251559981 ≤ 251592749) block0 block1

theorem join_0_1 : (twinPrimeSegment 251592749 251658285).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 251592749 ≤ 251625517)
    (by decide : 251625517 ≤ 251658285) block2 block3

theorem join_1_0 : (twinPrimeSegment 251527213 251658285).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 251527213 ≤ 251592749)
    (by decide : 251592749 ≤ 251658285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 251527213 251658285).card = 481 := join_1_0

end S119C15
end Sude.GeneratedTwinScan
