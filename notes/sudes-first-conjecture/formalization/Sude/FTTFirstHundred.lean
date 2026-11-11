import Sude.FTTBounds
import Sude.GeneratedFTT.R0000
import Sude.GeneratedFTT.R0001
import Sude.GeneratedFTT.R0002
import Sude.GeneratedFTT.R0003

/-! The first 100 FTT rows, including their recursive target-prime certificates.
The source row's X and T remain unconnected to the actual pool. -/
namespace Sude.Lucas.Generated

def firstHundredRows : List TargetRow :=
  R0000.rows ++ R0001.rows ++ R0002.rows ++ R0003.rows

theorem firstHundred_valid : ∀ row ∈ firstHundredRows, TargetRowValid row := by
  intro row h
  have h1 : row ∈ R0000.rows ∨ row ∈ R0001.rows ++ R0002.rows ++ R0003.rows :=
    List.mem_append.mp h
  rcases h1 with h0 | h1
  · exact R0000.rows_valid row h0
  have h2 : row ∈ R0001.rows ∨ row ∈ R0002.rows ++ R0003.rows := List.mem_append.mp h1
  rcases h2 with h1 | h2
  · exact R0001.rows_valid row h1
  have h3 : row ∈ R0002.rows ∨ row ∈ R0003.rows := List.mem_append.mp h2
  rcases h3 with h2 | h3
  · exact R0002.rows_valid row h2
  · exact R0003.rows_valid row h3

theorem firstHundred_orders : firstHundredRows.map TargetRow.order =
    (List.range 100).map (fun i => 2001 + 2 * i) := by
  decide +kernel

/-- Every odd order from 2001 through 2199 occurs with all target primes,
compatibility, and numerical row bounds checked for the literal X and T. -/
theorem firstHundred_cover (n : ℕ) (hlo : 2001 ≤ n) (hhi : n ≤ 2199)
    (hodd : n % 2 = 1) :
    ∃ row ∈ firstHundredRows, row.order = n ∧ TargetRowValid row := by
  have hmem : n ∈ firstHundredRows.map TargetRow.order := by
    rw [firstHundred_orders]
    apply List.mem_map.mpr
    refine ⟨(n - 2001) / 2, ?_, ?_⟩
    · simp only [List.mem_range]
      omega
    · omega
  obtain ⟨row, hrow, hord⟩ := List.mem_map.mp hmem
  exact ⟨row, hrow, hord, firstHundred_valid row hrow⟩

end Sude.Lucas.Generated
