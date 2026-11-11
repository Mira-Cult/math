import Sude.FTTTargetList
import Sude.GeneratedFTT.R0000
import Sude.GeneratedFTT.R0001
import Sude.GeneratedFTT.R0002
import Sude.GeneratedFTT.R0003
import Sude.GeneratedFTT.R0004
import Sude.GeneratedFTT.R0005
import Sude.GeneratedFTT.R0006
import Sude.GeneratedFTT.R0007
import Sude.GeneratedFTT.R0008
import Sude.GeneratedFTT.R0009
import Sude.GeneratedFTT.R0010
import Sude.GeneratedFTT.R0011
import Sude.GeneratedFTT.R0012
import Sude.GeneratedFTT.R0013
import Sude.GeneratedFTT.R0014
import Sude.GeneratedFTT.R0015
import Sude.GeneratedFTT.R0016
import Sude.GeneratedFTT.R0017
import Sude.GeneratedFTT.R0018
import Sude.GeneratedFTT.R0019
import Sude.GeneratedFTT.R0020
import Sude.GeneratedFTT.R0021
import Sude.GeneratedFTT.R0022
import Sude.GeneratedFTT.R0023
import Sude.GeneratedFTT.R0024
import Sude.GeneratedFTT.R0025
import Sude.GeneratedFTT.R0026
import Sude.GeneratedFTT.R0027
import Sude.GeneratedFTT.R0028
import Sude.GeneratedFTT.R0029
import Sude.GeneratedFTT.R0030
import Sude.GeneratedFTT.R0031
import Sude.GeneratedFTT.R0032
import Sude.GeneratedFTT.R0033
import Sude.GeneratedFTT.R0034
import Sude.GeneratedFTT.R0035
import Sude.GeneratedFTT.R0036
import Sude.GeneratedFTT.R0037
import Sude.GeneratedFTT.R0038
import Sude.GeneratedFTT.R0039
import Sude.GeneratedFTT.R0040
import Sude.GeneratedFTT.R0041
import Sude.GeneratedFTT.R0042
import Sude.GeneratedFTT.R0043
import Sude.GeneratedFTT.R0044
import Sude.GeneratedFTT.R0045
import Sude.GeneratedFTT.R0046
import Sude.GeneratedFTT.R0047
import Sude.GeneratedFTT.R0048
import Sude.GeneratedFTT.R0049

/-! First 1250 source FTT rows; pool identities remain open. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def first1250Batches : List (List TargetRow) := [
  R0000.rows,
  R0001.rows,
  R0002.rows,
  R0003.rows,
  R0004.rows,
  R0005.rows,
  R0006.rows,
  R0007.rows,
  R0008.rows,
  R0009.rows,
  R0010.rows,
  R0011.rows,
  R0012.rows,
  R0013.rows,
  R0014.rows,
  R0015.rows,
  R0016.rows,
  R0017.rows,
  R0018.rows,
  R0019.rows,
  R0020.rows,
  R0021.rows,
  R0022.rows,
  R0023.rows,
  R0024.rows,
  R0025.rows,
  R0026.rows,
  R0027.rows,
  R0028.rows,
  R0029.rows,
  R0030.rows,
  R0031.rows,
  R0032.rows,
  R0033.rows,
  R0034.rows,
  R0035.rows,
  R0036.rows,
  R0037.rows,
  R0038.rows,
  R0039.rows,
  R0040.rows,
  R0041.rows,
  R0042.rows,
  R0043.rows,
  R0044.rows,
  R0045.rows,
  R0046.rows,
  R0047.rows,
  R0048.rows,
  R0049.rows
]
def first1250Rows : List TargetRow := first1250Batches.flatten

theorem first1250_valid : ∀ row ∈ first1250Rows, TargetRowValid row := by
  intro row h
  simp only [first1250Rows, List.mem_flatten] at h
  obtain ⟨batch, hbatch, hrow⟩ := h
  simp only [first1250Batches, List.mem_cons, List.not_mem_nil, or_false] at hbatch
  rcases hbatch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact R0000.rows_valid row hrow
  · exact R0001.rows_valid row hrow
  · exact R0002.rows_valid row hrow
  · exact R0003.rows_valid row hrow
  · exact R0004.rows_valid row hrow
  · exact R0005.rows_valid row hrow
  · exact R0006.rows_valid row hrow
  · exact R0007.rows_valid row hrow
  · exact R0008.rows_valid row hrow
  · exact R0009.rows_valid row hrow
  · exact R0010.rows_valid row hrow
  · exact R0011.rows_valid row hrow
  · exact R0012.rows_valid row hrow
  · exact R0013.rows_valid row hrow
  · exact R0014.rows_valid row hrow
  · exact R0015.rows_valid row hrow
  · exact R0016.rows_valid row hrow
  · exact R0017.rows_valid row hrow
  · exact R0018.rows_valid row hrow
  · exact R0019.rows_valid row hrow
  · exact R0020.rows_valid row hrow
  · exact R0021.rows_valid row hrow
  · exact R0022.rows_valid row hrow
  · exact R0023.rows_valid row hrow
  · exact R0024.rows_valid row hrow
  · exact R0025.rows_valid row hrow
  · exact R0026.rows_valid row hrow
  · exact R0027.rows_valid row hrow
  · exact R0028.rows_valid row hrow
  · exact R0029.rows_valid row hrow
  · exact R0030.rows_valid row hrow
  · exact R0031.rows_valid row hrow
  · exact R0032.rows_valid row hrow
  · exact R0033.rows_valid row hrow
  · exact R0034.rows_valid row hrow
  · exact R0035.rows_valid row hrow
  · exact R0036.rows_valid row hrow
  · exact R0037.rows_valid row hrow
  · exact R0038.rows_valid row hrow
  · exact R0039.rows_valid row hrow
  · exact R0040.rows_valid row hrow
  · exact R0041.rows_valid row hrow
  · exact R0042.rows_valid row hrow
  · exact R0043.rows_valid row hrow
  · exact R0044.rows_valid row hrow
  · exact R0045.rows_valid row hrow
  · exact R0046.rows_valid row hrow
  · exact R0047.rows_valid row hrow
  · exact R0048.rows_valid row hrow
  · exact R0049.rows_valid row hrow

theorem first1250_orders : first1250Rows.map TargetRow.order =
    (List.range 1250).map (fun i => 2001 + 2 * i) := by
  decide +kernel

/-- Exact coverage of all odd orders from 2001 through 4499. -/
theorem first1250_cover (n : ℕ) (hlo : 2001 ≤ n) (hhi : n ≤ 4499)
    (hodd : n % 2 = 1) :
    ∃ row ∈ first1250Rows, row.order = n ∧ TargetRowValid row := by
  have hmem : n ∈ first1250Rows.map TargetRow.order := by
    rw [first1250_orders]
    apply List.mem_map.mpr
    refine ⟨(n - 2001) / 2, ?_, ?_⟩
    · simp only [List.mem_range]
      omega
    · omega
  obtain ⟨row, hrow, hord⟩ := List.mem_map.mp hmem
  exact ⟨row, hrow, hord, first1250_valid row hrow⟩

end Sude.Lucas.Generated
