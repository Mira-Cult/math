import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18602)) 346030125 346062893 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 346030125 346062893).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18602 346030125 346062893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18603)) 346062893 346095661 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 346062893 346095661).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18603 346062893 346095661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18604)) 346095661 346128429 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 346095661 346128429).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18604 346095661 346128429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18605)) 346128429 346161197 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 346128429 346161197).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18605 346128429 346161197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 346030125 346095661).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 346030125 ≤ 346062893)
    (by decide : 346062893 ≤ 346095661) block0 block1

theorem join_0_1 : (twinPrimeSegment 346095661 346161197).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 346095661 ≤ 346128429)
    (by decide : 346128429 ≤ 346161197) block2 block3

theorem join_1_0 : (twinPrimeSegment 346030125 346161197).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 346030125 ≤ 346095661)
    (by decide : 346095661 ≤ 346161197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 346030125 346161197).card = 427 := join_1_0

end S165C00
end Sude.GeneratedTwinScan
