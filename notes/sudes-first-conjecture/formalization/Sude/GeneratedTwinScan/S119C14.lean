import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15856)) 251396141 251428909 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 251396141 251428909).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15856 251396141 251428909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15857)) 251428909 251461677 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 251428909 251461677).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15857 251428909 251461677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15858)) 251461677 251494445 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 251461677 251494445).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15858 251461677 251494445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15859)) 251494445 251527213 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 251494445 251527213).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15859 251494445 251527213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 251396141 251461677).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 251396141 ≤ 251428909)
    (by decide : 251428909 ≤ 251461677) block0 block1

theorem join_0_1 : (twinPrimeSegment 251461677 251527213).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 251461677 ≤ 251494445)
    (by decide : 251494445 ≤ 251527213) block2 block3

theorem join_1_0 : (twinPrimeSegment 251396141 251527213).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 251396141 ≤ 251461677)
    (by decide : 251461677 ≤ 251527213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 251396141 251527213).card = 451 := join_1_0

end S119C14
end Sude.GeneratedTwinScan
