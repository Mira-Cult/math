import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17093)) 292159533 292192301 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 292159533 292192301).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17093 292159533 292192301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17094)) 292192301 292225069 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 292192301 292225069).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17094 292192301 292225069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17095)) 292225069 292257837 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 292225069 292257837).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17095 292225069 292257837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17096)) 292257837 292290605 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 292257837 292290605).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17096 292257837 292290605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 292159533 292225069).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 292159533 ≤ 292192301)
    (by decide : 292192301 ≤ 292225069) block0 block1

theorem join_0_1 : (twinPrimeSegment 292225069 292290605).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 292225069 ≤ 292257837)
    (by decide : 292257837 ≤ 292290605) block2 block3

theorem join_1_0 : (twinPrimeSegment 292159533 292290605).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 292159533 ≤ 292225069)
    (by decide : 292225069 ≤ 292290605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 292159533 292290605).card = 433 := join_1_0

end S139C05
end Sude.GeneratedTwinScan
