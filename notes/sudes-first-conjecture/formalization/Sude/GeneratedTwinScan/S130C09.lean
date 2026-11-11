import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16548)) 273809453 273842221 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 273809453 273842221).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16548 273809453 273842221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16549)) 273842221 273874989 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 273842221 273874989).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16549 273842221 273874989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16550)) 273874989 273907757 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 273874989 273907757).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16550 273874989 273907757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16551)) 273907757 273940525 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 273907757 273940525).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16551 273907757 273940525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 273809453 273874989).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 273809453 ≤ 273842221)
    (by decide : 273842221 ≤ 273874989) block0 block1

theorem join_0_1 : (twinPrimeSegment 273874989 273940525).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 273874989 ≤ 273907757)
    (by decide : 273907757 ≤ 273940525) block2 block3

theorem join_1_0 : (twinPrimeSegment 273809453 273940525).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 273809453 ≤ 273874989)
    (by decide : 273874989 ≤ 273940525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 273809453 273940525).card = 458 := join_1_0

end S130C09
end Sude.GeneratedTwinScan
