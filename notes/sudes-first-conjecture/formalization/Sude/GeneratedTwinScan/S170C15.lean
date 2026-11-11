import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18934)) 358481965 358514733 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 358481965 358514733).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18934 358481965 358514733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18935)) 358514733 358547501 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 358514733 358547501).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18935 358514733 358547501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18936)) 358547501 358580269 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 358547501 358580269).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18936 358547501 358580269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18937)) 358580269 358613037 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 358580269 358613037).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18937 358580269 358613037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 358481965 358547501).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 358481965 ≤ 358514733)
    (by decide : 358514733 ≤ 358547501) block0 block1

theorem join_0_1 : (twinPrimeSegment 358547501 358613037).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 358547501 ≤ 358580269)
    (by decide : 358580269 ≤ 358613037) block2 block3

theorem join_1_0 : (twinPrimeSegment 358481965 358613037).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 358481965 ≤ 358547501)
    (by decide : 358547501 ≤ 358613037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 358481965 358613037).card = 464 := join_1_0

end S170C15
end Sude.GeneratedTwinScan
