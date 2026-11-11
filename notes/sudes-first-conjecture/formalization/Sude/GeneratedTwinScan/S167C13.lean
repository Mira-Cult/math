import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18760)) 351928365 351961133 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 351928365 351961133).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18760 351928365 351961133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18761)) 351961133 351993901 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 351961133 351993901).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18761 351961133 351993901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18762)) 351993901 352026669 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 351993901 352026669).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18762 351993901 352026669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18763)) 352026669 352059437 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 352026669 352059437).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18763 352026669 352059437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 351928365 351993901).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 351928365 ≤ 351961133)
    (by decide : 351961133 ≤ 351993901) block0 block1

theorem join_0_1 : (twinPrimeSegment 351993901 352059437).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 351993901 ≤ 352026669)
    (by decide : 352026669 ≤ 352059437) block2 block3

theorem join_1_0 : (twinPrimeSegment 351928365 352059437).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 351928365 ≤ 351993901)
    (by decide : 351993901 ≤ 352059437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 351928365 352059437).card = 453 := join_1_0

end S167C13
end Sude.GeneratedTwinScan
