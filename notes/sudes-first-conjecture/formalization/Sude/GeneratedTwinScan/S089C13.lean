import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13725)) 188350509 188383277 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 188350509 188383277).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13725 188350509 188383277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13726)) 188383277 188416045 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 188383277 188416045).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13726 188383277 188416045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13727)) 188416045 188448813 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 188416045 188448813).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13727 188416045 188448813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13728)) 188448813 188481581 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 188448813 188481581).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13728 188448813 188481581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 188350509 188416045).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 188350509 ≤ 188383277)
    (by decide : 188383277 ≤ 188416045) block0 block1

theorem join_0_1 : (twinPrimeSegment 188416045 188481581).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 188416045 ≤ 188448813)
    (by decide : 188448813 ≤ 188481581) block2 block3

theorem join_1_0 : (twinPrimeSegment 188350509 188481581).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 188350509 ≤ 188416045)
    (by decide : 188416045 ≤ 188481581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 188350509 188481581).card = 467 := join_1_0

end S089C13
end Sude.GeneratedTwinScan
