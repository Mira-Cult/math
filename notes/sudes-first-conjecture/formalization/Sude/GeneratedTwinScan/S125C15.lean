import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16252)) 264110125 264142893 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 264110125 264142893).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16252 264110125 264142893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16253)) 264142893 264175661 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 264142893 264175661).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16253 264142893 264175661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16254)) 264175661 264208429 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 264175661 264208429).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16254 264175661 264208429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16255)) 264208429 264241197 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 264208429 264241197).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16255 264208429 264241197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 264110125 264175661).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 264110125 ≤ 264142893)
    (by decide : 264142893 ≤ 264175661) block0 block1

theorem join_0_1 : (twinPrimeSegment 264175661 264241197).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 264175661 ≤ 264208429)
    (by decide : 264208429 ≤ 264241197) block2 block3

theorem join_1_0 : (twinPrimeSegment 264110125 264241197).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 264110125 ≤ 264175661)
    (by decide : 264175661 ≤ 264241197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 264110125 264241197).card = 478 := join_1_0

end S125C15
end Sude.GeneratedTwinScan
