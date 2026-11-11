import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13332)) 177733677 177766445 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 177733677 177766445).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13332 177733677 177766445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13334)) 177766445 177799213 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 177766445 177799213).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13334 177766445 177799213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13335)) 177799213 177831981 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 177799213 177831981).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13335 177799213 177831981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13336)) 177831981 177864749 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 177831981 177864749).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13336 177831981 177864749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 177733677 177799213).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 177733677 ≤ 177766445)
    (by decide : 177766445 ≤ 177799213) block0 block1

theorem join_0_1 : (twinPrimeSegment 177799213 177864749).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 177799213 ≤ 177831981)
    (by decide : 177831981 ≤ 177864749) block2 block3

theorem join_1_0 : (twinPrimeSegment 177733677 177864749).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 177733677 ≤ 177799213)
    (by decide : 177799213 ≤ 177864749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 177733677 177864749).card = 482 := join_1_0

end S084C12
end Sude.GeneratedTwinScan
