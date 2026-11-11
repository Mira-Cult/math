import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22120)) 489291821 489324589 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 489291821 489324589).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22120 489291821 489324589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22121)) 489324589 489357357 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 489324589 489357357).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22121 489324589 489357357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22122)) 489357357 489390125 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 489357357 489390125).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22122 489357357 489390125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22122)) 489390125 489422893 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 489390125 489422893).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22122 489390125 489422893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 489291821 489357357).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 489291821 ≤ 489324589)
    (by decide : 489324589 ≤ 489357357) block0 block1

theorem join_0_1 : (twinPrimeSegment 489357357 489422893).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 489357357 ≤ 489390125)
    (by decide : 489390125 ≤ 489422893) block2 block3

theorem join_1_0 : (twinPrimeSegment 489291821 489422893).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 489291821 ≤ 489357357)
    (by decide : 489357357 ≤ 489422893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 489291821 489422893).card = 434 := join_1_0

end S233C05
end Sude.GeneratedTwinScan
