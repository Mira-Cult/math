import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19253)) 370671661 370704429 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 370671661 370704429).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19253 370671661 370704429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19254)) 370704429 370737197 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 370704429 370737197).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19254 370704429 370737197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19255)) 370737197 370769965 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 370737197 370769965).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19255 370737197 370769965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19256)) 370769965 370802733 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 370769965 370802733).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19256 370769965 370802733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 370671661 370737197).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 370671661 ≤ 370704429)
    (by decide : 370704429 ≤ 370737197) block0 block1

theorem join_0_1 : (twinPrimeSegment 370737197 370802733).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 370737197 ≤ 370769965)
    (by decide : 370769965 ≤ 370802733) block2 block3

theorem join_1_0 : (twinPrimeSegment 370671661 370802733).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 370671661 ≤ 370737197)
    (by decide : 370737197 ≤ 370802733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 370671661 370802733).card = 457 := join_1_0

end S176C12
end Sude.GeneratedTwinScan
