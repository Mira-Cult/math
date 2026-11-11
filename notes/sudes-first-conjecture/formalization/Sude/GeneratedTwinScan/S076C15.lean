import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12703)) 161349677 161382445 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 161349677 161382445).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12703 161349677 161382445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12704)) 161382445 161415213 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 161382445 161415213).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12704 161382445 161415213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12706)) 161415213 161447981 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 161415213 161447981).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12706 161415213 161447981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12707)) 161447981 161480749 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 161447981 161480749).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12707 161447981 161480749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 161349677 161415213).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 161349677 ≤ 161382445)
    (by decide : 161382445 ≤ 161415213) block0 block1

theorem join_0_1 : (twinPrimeSegment 161415213 161480749).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 161415213 ≤ 161447981)
    (by decide : 161447981 ≤ 161480749) block2 block3

theorem join_1_0 : (twinPrimeSegment 161349677 161480749).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 161349677 ≤ 161415213)
    (by decide : 161415213 ≤ 161480749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 161349677 161480749).card = 460 := join_1_0

end S076C15
end Sude.GeneratedTwinScan
