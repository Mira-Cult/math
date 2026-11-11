import Sude.FiniteTwinOddBaseData
import Mathlib.Data.List.Sort

namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem finiteTwinOddBase_sorted : finiteTwinOddBase.SortedLT := by
  decide +kernel

theorem finiteTwinOddBase_length : finiteTwinOddBase.length = 3511 := by
  decide +kernel

end
end Sude
