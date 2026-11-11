import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17265)) 298057773 298090541 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 298057773 298090541).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17265 298057773 298090541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17266)) 298090541 298123309 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 298090541 298123309).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17266 298090541 298123309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17267)) 298123309 298156077 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 298123309 298156077).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17267 298123309 298156077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17268)) 298156077 298188845 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 298156077 298188845).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17268 298156077 298188845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 298057773 298123309).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 298057773 ≤ 298090541)
    (by decide : 298090541 ≤ 298123309) block0 block1

theorem join_0_1 : (twinPrimeSegment 298123309 298188845).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 298123309 ≤ 298156077)
    (by decide : 298156077 ≤ 298188845) block2 block3

theorem join_1_0 : (twinPrimeSegment 298057773 298188845).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 298057773 ≤ 298123309)
    (by decide : 298123309 ≤ 298188845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 298057773 298188845).card = 437 := join_1_0

end S142C02
end Sude.GeneratedTwinScan
