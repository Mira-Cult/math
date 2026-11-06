import Shared.Beeping.NPcoNP.Grammar284HalfReserved
import Shared.Beeping.NPcoNP.Grammar284ReservedOrdinary

/-! Finite coverage of the graph rows by ordinary instructions or native
HALF entries. The beep row 0 and root row 184 are explicitly excluded. -/
namespace Shared.Beeping.NPcoNP.Grammar284ReservedCoverage
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeHalfZeroGeneralScan
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000

def rowCheck (row : Fin 185) : Bool :=
  if row=0 ∨ row=184 then true else
  match graphLeaf row with
  | none => false
  | some (_,name) => match namedOperation name with
    | some _ => true
    | none => match operationEntry name with
      | none => false
      | some q => (q == entryAt 0) || (q == entryAt 1) || (q == entryAt 2) || (q == entryAt 3)

theorem all_rows_checked : (List.finRange 185).all rowCheck=true := by decide

theorem covered (row : Fin 185) (hzero : row≠0) (hroot : row≠184)
    (path : Path) (name : String) (leaf : graphLeaf row=some (path,name)) :
    (∃ n inc, namedOperation name=some (n,inc)) ∨
      ∃ k, k≤3 ∧ operationEntry name=some (entryAt k) := by
  have hh := List.all_eq_true.mp all_rows_checked row (List.mem_finRange row)
  simp only [rowCheck,hzero,hroot,or_self,if_false,leaf] at hh
  cases hn : namedOperation name with
  | some pair =>
    rcases pair with ⟨n,inc⟩
    exact Or.inl ⟨n,inc,rfl⟩
  | none =>
    simp only [hn] at hh
    cases he : operationEntry name with
    | none => simp [he] at hh
    | some q =>
      simp only [he,Bool.or_eq_true,beq_iff_eq] at hh
      rcases hh with ((h0 | h1) | h2) | h3
      · exact Or.inr ⟨0,by decide,by simpa [h0] using he⟩
      · exact Or.inr ⟨1,by decide,by simpa [h1] using he⟩
      · exact Or.inr ⟨2,by decide,by simpa [h2] using he⟩
      · exact Or.inr ⟨3,by decide,by simpa [h3] using he⟩

#print axioms covered
end Shared.Beeping.NPcoNP.Grammar284ReservedCoverage
