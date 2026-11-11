import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22215)) 493486125 493518893 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 493486125 493518893).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22215 493486125 493518893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22216)) 493518893 493551661 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 493518893 493551661).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22216 493518893 493551661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22216)) 493551661 493584429 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 493551661 493584429).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22216 493551661 493584429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22217)) 493584429 493617197 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 493584429 493617197).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22217 493584429 493617197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 493486125 493551661).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 493486125 ≤ 493518893)
    (by decide : 493518893 ≤ 493551661) block0 block1

theorem join_0_1 : (twinPrimeSegment 493551661 493617197).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 493551661 ≤ 493584429)
    (by decide : 493584429 ≤ 493617197) block2 block3

theorem join_1_0 : (twinPrimeSegment 493486125 493617197).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 493486125 ≤ 493551661)
    (by decide : 493551661 ≤ 493617197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 493486125 493617197).card = 422 := join_1_0

end S235C05
end Sude.GeneratedTwinScan
