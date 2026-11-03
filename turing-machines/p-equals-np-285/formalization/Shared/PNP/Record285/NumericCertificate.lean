import Shared.PNP.Record285.NumericChunks

/-! Kernel certificate for the generated numeric tables. Concrete equality to
frozen text files is a separate obligation. Checks are split to bound memory. -/
namespace Shared.PNP.Record285.NumericCertificate
open Shared.Beeping.Machines
open Shared.PNP.Record285.Quotient
open Shared.PNP.Record285.NumericChunks

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem chunk_sound (start count : Nat) (hcheck : rowsCheck start count = true)
    (q : Fin 286) (hmem : q.val ∈ List.range' start count) (b : Bool) :
    NumericTables.target.table.row (Companion.quotientMap q) b =
      mappedRow Companion.quotientMap ((NumericTables.source.entering Companion.beepState).table.row q b) := by
  have hall : ∀ i ∈ List.range' start count, (if h : i < 286 then
      let q : Fin 286 := ⟨i,h⟩
      decide (NumericTables.target.table.row (Companion.quotientMap q) false =
        mappedRow Companion.quotientMap ((NumericTables.source.entering Companion.beepState).table.row q false)) &&
      decide (NumericTables.target.table.row (Companion.quotientMap q) true =
        mappedRow Companion.quotientMap ((NumericTables.source.entering Companion.beepState).table.row q true))
    else false) = true := List.all_eq_true.mp hcheck
  have hc := hall q.val hmem
  simp only [dif_pos q.isLt, Bool.and_eq_true, decide_eq_true_eq] at hc
  cases b with
  | false => exact hc.1
  | true => exact hc.2

theorem chunk_interval (start count : Nat) (hcheck : rowsCheck start count = true)
    (q : Fin 286) (hlo : start ≤ q.val) (hhi : q.val < start + count) (b : Bool) :
    NumericTables.target.table.row (Companion.quotientMap q) b =
      mappedRow Companion.quotientMap ((NumericTables.source.entering Companion.beepState).table.row q b) := by
  apply chunk_sound start count hcheck q ?_ b
  simp only [List.mem_range']
  refine ⟨q.val - start, ?_, ?_⟩ <;> omega

/-- The exact event-coloured quotient is checked for every source row. -/
theorem numeric_quotient :
    check (NumericTables.source.entering Companion.beepState) NumericTables.target
      Companion.quotientMap = true := by
  apply check_complete
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro q b
  have hq := q.isLt
  by_cases h0 : q.val < 16
  · exact chunk_interval 0 16 chunk0 q (by omega) (by omega) b
  by_cases h1 : q.val < 32
  · exact chunk_interval 16 16 chunk1 q (by omega) (by omega) b
  by_cases h2 : q.val < 48
  · exact chunk_interval 32 16 chunk2 q (by omega) (by omega) b
  by_cases h3 : q.val < 64
  · exact chunk_interval 48 16 chunk3 q (by omega) (by omega) b
  by_cases h4 : q.val < 80
  · exact chunk_interval 64 16 chunk4 q (by omega) (by omega) b
  by_cases h5 : q.val < 96
  · exact chunk_interval 80 16 chunk5 q (by omega) (by omega) b
  by_cases h6 : q.val < 112
  · exact chunk_interval 96 16 chunk6 q (by omega) (by omega) b
  by_cases h7 : q.val < 128
  · exact chunk_interval 112 16 chunk7 q (by omega) (by omega) b
  by_cases h8 : q.val < 144
  · exact chunk_interval 128 16 chunk8 q (by omega) (by omega) b
  by_cases h9 : q.val < 160
  · exact chunk_interval 144 16 chunk9 q (by omega) (by omega) b
  by_cases h10 : q.val < 176
  · exact chunk_interval 160 16 chunk10 q (by omega) (by omega) b
  by_cases h11 : q.val < 192
  · exact chunk_interval 176 16 chunk11 q (by omega) (by omega) b
  by_cases h12 : q.val < 208
  · exact chunk_interval 192 16 chunk12 q (by omega) (by omega) b
  by_cases h13 : q.val < 224
  · exact chunk_interval 208 16 chunk13 q (by omega) (by omega) b
  by_cases h14 : q.val < 240
  · exact chunk_interval 224 16 chunk14 q (by omega) (by omega) b
  by_cases h15 : q.val < 256
  · exact chunk_interval 240 16 chunk15 q (by omega) (by omega) b
  by_cases h16 : q.val < 272
  · exact chunk_interval 256 16 chunk16 q (by omega) (by omega) b
  exact chunk_interval 272 14 chunk17 q (by omega) (by omega) b

end Shared.PNP.Record285.NumericCertificate
