import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16416)) 269484077 269516845 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 269484077 269516845).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16416 269484077 269516845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16417)) 269516845 269549613 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 269516845 269549613).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16417 269516845 269549613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16418)) 269549613 269582381 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 269549613 269582381).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16418 269549613 269582381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16419)) 269582381 269615149 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 269582381 269615149).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16419 269582381 269615149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 269484077 269549613).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 269484077 ≤ 269516845)
    (by decide : 269516845 ≤ 269549613) block0 block1

theorem join_0_1 : (twinPrimeSegment 269549613 269615149).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 269549613 ≤ 269582381)
    (by decide : 269582381 ≤ 269615149) block2 block3

theorem join_1_0 : (twinPrimeSegment 269484077 269615149).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 269484077 ≤ 269549613)
    (by decide : 269549613 ≤ 269615149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 269484077 269615149).card = 443 := join_1_0

end S128C08
end Sude.GeneratedTwinScan
