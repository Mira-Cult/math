import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20538)) 421789741 421822509 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 421789741 421822509).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20538 421789741 421822509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20539)) 421822509 421855277 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 421822509 421855277).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20539 421822509 421855277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20539)) 421855277 421888045 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 421855277 421888045).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20539 421855277 421888045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20540)) 421888045 421920813 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 421888045 421920813).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20540 421888045 421920813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 421789741 421855277).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 421789741 ≤ 421822509)
    (by decide : 421822509 ≤ 421855277) block0 block1

theorem join_0_1 : (twinPrimeSegment 421855277 421920813).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 421855277 ≤ 421888045)
    (by decide : 421888045 ≤ 421920813) block2 block3

theorem join_1_0 : (twinPrimeSegment 421789741 421920813).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 421789741 ≤ 421855277)
    (by decide : 421855277 ≤ 421920813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 421789741 421920813).card = 460 := join_1_0

end S201C02
end Sude.GeneratedTwinScan
