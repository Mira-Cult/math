import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15873)) 251920429 251953197 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 251920429 251953197).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15873 251920429 251953197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15874)) 251953197 251985965 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 251953197 251985965).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15874 251953197 251985965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15875)) 251985965 252018733 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 251985965 252018733).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15875 251985965 252018733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15876)) 252018733 252051501 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 252018733 252051501).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15876 252018733 252051501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 251920429 251985965).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 251920429 ≤ 251953197)
    (by decide : 251953197 ≤ 251985965) block0 block1

theorem join_0_1 : (twinPrimeSegment 251985965 252051501).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 251985965 ≤ 252018733)
    (by decide : 252018733 ≤ 252051501) block2 block3

theorem join_1_0 : (twinPrimeSegment 251920429 252051501).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 251920429 ≤ 251985965)
    (by decide : 251985965 ≤ 252051501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 251920429 252051501).card = 491 := join_1_0

end S120C02
end Sude.GeneratedTwinScan
