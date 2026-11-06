import Shared.Beeping.NPcoNP.Source284GraphParserInit
import Shared.Beeping.NPcoNP.Source284GraphParserTotal

/-! Parser initialization composed with the checked finite register graph.
The theorem starts at an arbitrary supplied bank satisfying the work-zero
premise. It does not establish physical reachability or whole-program
correctness. -/
namespace Shared.Beeping.NPcoNP.Source284GraphParserComplete

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphParserInit
open Shared.Beeping.NPcoNP.Source284GraphParserTotal
open Shared.Beeping.NPcoNP.Source284Parser

/-- Starting at graph PC 10 with zero work register, parser initialization
and the entire marker/payload loop finish in finite positive silent time.
The parsed values are those of the executable source parser. Register 0 is
cleared, registers 5 and 6 hold the source result, and the remaining bank
is represented by the unchanged base bank `b` in `header`. -/
theorem parser_from_pc10 (b : B) (hz : b 10 = 0) :
    ∃ k, 0 < k ∧
      target.system.advance ⟨pc10,b⟩ k =
        ⟨23,header b 0 (length (b 0)) (description (b 0))⟩ ∧
      target.system.wordFrom ⟨pc10,b⟩ k = [] := by
  let d := b r5 + b r6 + 3
  let c := target.system.advance ⟨pc10,b⟩ d
  have hi := parser_init b
  dsimp only at hi
  obtain ⟨hd, hpc, h5, h6, hrest, hw⟩ := hi
  have hc : c = ⟨13, header b (b 0) 0 1⟩ := by
    have hstate : c.state = (13 : Fin 185) := by simpa [c,d,pc13] using hpc
    have hv5 : c.bank 5 = 0 := by simpa [c,d,r5] using h5
    have hv6 : c.bank 6 = 1 := by simpa [c,d,r6] using h6
    have hother (i : Fin 12) (h₅ : i ≠ 5) (h₆ : i ≠ 6) : c.bank i = b i := by
      exact hrest i (by simpa [r5] using h₅) (by simpa [r6] using h₆)
    have hbank : c.bank = header b (b 0) 0 1 := by
      funext i
      fin_cases i <;> simp [header, write, hv5, hv6, hother]
    cases hcfg : c with
    | mk state bank =>
      simp only [hcfg] at hstate hbank
      cases hstate
      cases hbank
      rfl
  obtain ⟨l, hl, ha, hw'⟩ := loop b (b 0) 0 1 hz
  refine ⟨d+l, by omega, ?_, ?_⟩
  · rw [target.system.advance_add]
    change target.system.advance c l = _
    rw [hc, ha]
    rfl
  · rw [target.system.wordFrom_add]
    change target.system.wordFrom ⟨pc10,b⟩ d ++ target.system.wordFrom c l = []
    rw [hw, hc, hw']
    rfl

end Shared.Beeping.NPcoNP.Source284GraphParserComplete
