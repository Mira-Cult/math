import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20291)) 411697197 411729965 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 411697197 411729965).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20291 411697197 411729965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20291)) 411729965 411762733 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 411729965 411762733).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20291 411729965 411762733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20292)) 411762733 411795501 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 411762733 411795501).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20292 411762733 411795501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20293)) 411795501 411828269 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 411795501 411828269).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20293 411795501 411828269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 411697197 411762733).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 411697197 ≤ 411729965)
    (by decide : 411729965 ≤ 411762733) block0 block1

theorem join_0_1 : (twinPrimeSegment 411762733 411828269).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 411762733 ≤ 411795501)
    (by decide : 411795501 ≤ 411828269) block2 block3

theorem join_1_0 : (twinPrimeSegment 411697197 411828269).card = 398 := by
  simpa using combineTwinPrimeSegments (by decide : 411697197 ≤ 411762733)
    (by decide : 411762733 ≤ 411828269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 411697197 411828269).card = 398 := join_1_0

end S196C05
end Sude.GeneratedTwinScan
