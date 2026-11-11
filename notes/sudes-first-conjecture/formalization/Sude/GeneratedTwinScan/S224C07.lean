import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21695)) 470679597 470712365 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 470679597 470712365).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21695 470679597 470712365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21696)) 470712365 470745133 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 470712365 470745133).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21696 470712365 470745133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21697)) 470745133 470777901 = 91 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 470745133 470777901).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21697 470745133 470777901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21698)) 470777901 470810669 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 470777901 470810669).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21698 470777901 470810669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 470679597 470745133).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 470679597 ≤ 470712365)
    (by decide : 470712365 ≤ 470745133) block0 block1

theorem join_0_1 : (twinPrimeSegment 470745133 470810669).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 470745133 ≤ 470777901)
    (by decide : 470777901 ≤ 470810669) block2 block3

theorem join_1_0 : (twinPrimeSegment 470679597 470810669).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 470679597 ≤ 470745133)
    (by decide : 470745133 ≤ 470810669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 470679597 470810669).card = 418 := join_1_0

end S224C07
end Sude.GeneratedTwinScan
