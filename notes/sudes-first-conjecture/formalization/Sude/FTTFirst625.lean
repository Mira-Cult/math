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

/-! First 625 source FTT rows; pool identities remain open. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def first625Batches : List (List TargetRow) := [
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
  R0024.rows
]
def first625Rows : List TargetRow := first625Batches.flatten

theorem first625_valid : ∀ row ∈ first625Rows, TargetRowValid row := by
  intro row h
  simp only [first625Rows, List.mem_flatten] at h
  obtain ⟨batch, hbatch, hrow⟩ := h
  simp only [first625Batches, List.mem_cons, List.not_mem_nil, or_false] at hbatch
  rcases hbatch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

theorem first625_orders : first625Rows.map TargetRow.order =
    (List.range 625).map (fun i => 2001 + 2 * i) := by
  decide +kernel

/-- Exact coverage of all odd orders from 2001 through 3249. -/
theorem first625_cover (n : ℕ) (hlo : 2001 ≤ n) (hhi : n ≤ 3249)
    (hodd : n % 2 = 1) :
    ∃ row ∈ first625Rows, row.order = n ∧ TargetRowValid row := by
  have hmem : n ∈ first625Rows.map TargetRow.order := by
    rw [first625_orders]
    apply List.mem_map.mpr
    refine ⟨(n - 2001) / 2, ?_, ?_⟩
    · simp only [List.mem_range]
      omega
    · omega
  obtain ⟨row, hrow, hord⟩ := List.mem_map.mp hmem
  exact ⟨row, hrow, hord, first625_valid row hrow⟩

end Sude.Lucas.Generated
