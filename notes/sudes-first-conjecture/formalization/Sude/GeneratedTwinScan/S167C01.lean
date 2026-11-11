import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18718)) 350355501 350388269 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 350355501 350388269).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18718 350355501 350388269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18719)) 350388269 350421037 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 350388269 350421037).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18719 350388269 350421037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18720)) 350421037 350453805 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 350421037 350453805).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18720 350421037 350453805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18721)) 350453805 350486573 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 350453805 350486573).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18721 350453805 350486573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 350355501 350421037).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 350355501 ≤ 350388269)
    (by decide : 350388269 ≤ 350421037) block0 block1

theorem join_0_1 : (twinPrimeSegment 350421037 350486573).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 350421037 ≤ 350453805)
    (by decide : 350453805 ≤ 350486573) block2 block3

theorem join_1_0 : (twinPrimeSegment 350355501 350486573).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 350355501 ≤ 350421037)
    (by decide : 350421037 ≤ 350486573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 350355501 350486573).card = 433 := join_1_0

end S167C01
end Sude.GeneratedTwinScan
