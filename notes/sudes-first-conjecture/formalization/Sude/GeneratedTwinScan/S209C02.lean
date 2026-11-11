import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20942)) 438566957 438599725 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 438566957 438599725).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20942 438566957 438599725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20943)) 438599725 438632493 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 438599725 438632493).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20943 438599725 438632493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20944)) 438632493 438665261 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 438632493 438665261).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20944 438632493 438665261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20945)) 438665261 438698029 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 438665261 438698029).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20945 438665261 438698029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 438566957 438632493).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 438566957 ≤ 438599725)
    (by decide : 438599725 ≤ 438632493) block0 block1

theorem join_0_1 : (twinPrimeSegment 438632493 438698029).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 438632493 ≤ 438665261)
    (by decide : 438665261 ≤ 438698029) block2 block3

theorem join_1_0 : (twinPrimeSegment 438566957 438698029).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 438566957 ≤ 438632493)
    (by decide : 438632493 ≤ 438698029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 438566957 438698029).card = 473 := join_1_0

end S209C02
end Sude.GeneratedTwinScan
