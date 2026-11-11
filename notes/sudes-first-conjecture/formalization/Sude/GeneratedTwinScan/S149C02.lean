import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17685)) 312737837 312770605 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 312737837 312770605).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17685 312737837 312770605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17686)) 312770605 312803373 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 312770605 312803373).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17686 312770605 312803373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17687)) 312803373 312836141 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 312803373 312836141).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17687 312803373 312836141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17688)) 312836141 312868909 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 312836141 312868909).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17688 312836141 312868909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 312737837 312803373).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 312737837 ≤ 312770605)
    (by decide : 312770605 ≤ 312803373) block0 block1

theorem join_0_1 : (twinPrimeSegment 312803373 312868909).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 312803373 ≤ 312836141)
    (by decide : 312836141 ≤ 312868909) block2 block3

theorem join_1_0 : (twinPrimeSegment 312737837 312868909).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 312737837 ≤ 312803373)
    (by decide : 312803373 ≤ 312868909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 312737837 312868909).card = 456 := join_1_0

end S149C02
end Sude.GeneratedTwinScan
