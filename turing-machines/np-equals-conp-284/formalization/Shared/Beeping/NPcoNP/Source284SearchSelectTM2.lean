import Shared.Beeping.NPcoNP.Source284BoundedSearchTM2
import Shared.ComplexityBridge.TM2ListLookup
import Shared.ComplexityBridge.TM2EmptyConstant

/-! Extract a charged, total tagged coordinate from the list-valued bounded
countdown search. The false tag marks failure and the true tag marks a live
coordinate. This is a search selector, not a complete countdown-table compiler. -/
namespace Shared.Beeping.NPcoNP.Source284SearchSelectTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284BoundedSearchTM2
open Shared.Beeping.NPcoNP.Source284CountdownSearch

abbrev Result := Bool × Coord

def tag (p : Coord) : Result := (true,p)

theorem tag_isPolyTime : ComplexityTheory.IsPolyTime tag := by
  have ht : ComplexityTheory.IsPolyTime (fun _ : Coord => true) := TM2Constant.isPolyTime true
  have hi : ComplexityTheory.IsPolyTime (id : Coord → Coord) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  exact TM2GuardAllStep.pair_isPolyTime (fun _ : Coord => true) id ht hi

def tagged (p : Input) : List Result := (searchMatches p).map tag

theorem tagged_isPolyTime : ComplexityTheory.IsPolyTime tagged := by
  exact TM2Compose.isPolyTime_comp searchMatches (fun xs : List Coord => xs.map tag)
    searchMatches_isPolyTime (TM2ContextMapGeneric.listMap_isPolyTime tag tag_isPolyTime)

/-- Zero indices and the default marker are explicit finite encoded data. -/
def select (p : Input) : Result :=
  TM2ListLookup.lookup (tagged p, (0, (false,(0,0))))

theorem select_isPolyTime : ComplexityTheory.IsPolyTime select := by
  let zero : Input → Nat := fun _ => 0
  let no : Input → Bool := fun _ => false
  let zpair : Input → Coord := fun _ => (0,0)
  let fallback : Input → Result := fun _ => (false,(0,0))
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hn : ComplexityTheory.IsPolyTime no := TM2Constant.isPolyTime false
  have hp : ComplexityTheory.IsPolyTime zpair := TM2GuardAllStep.pair_isPolyTime zero zero hz hz
  have hf : ComplexityTheory.IsPolyTime fallback := TM2GuardAllStep.pair_isPolyTime no zpair hn hp
  have hr := TM2GuardAllStep.pair_isPolyTime zero fallback hz hf
  have harg := TM2GuardAllStep.pair_isPolyTime tagged (fun p => (zero p,fallback p)) tagged_isPolyTime hr
  exact TM2Compose.isPolyTime_comp (fun p => (tagged p,(zero p,fallback p)))
    (TM2ListLookup.lookup (β := Result)) harg TM2ListLookup.lookup_isPolyTime

/-- A true tag identifies exactly the unique live coordinate, and false
signals that no live coordinate was found. -/
theorem select_correct (nTokens eTokens : List Bool) (s : Nat) :
    select ((nTokens,eTokens),s) =
      match search nTokens.length eTokens.length s with
      | none => (false,(0,0))
      | some p => (true,p) := by
  let xs := searchMatches ((nTokens,eTokens),s)
  have hm (p : Coord) : p ∈ xs ↔ search nTokens.length eTokens.length s = some p := by
    cases p with
    | mk e q => exact searchMatches_mem_iff_search nTokens eTokens s e q
  cases hs : search nTokens.length eTokens.length s with
  | none =>
    have hx : xs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      have := (hm p).1 hp
      rw [hs] at this
      contradiction
    change TM2ListLookup.lookup (xs.map tag, (0,(false,(0,0)))) = _
    simp [TM2ListLookup.lookup, hx, hs]
  | some p =>
    have hmem : p ∈ xs := (hm p).2 hs
    cases hx : xs with
    | nil => simp [hx] at hmem
    | cons h tail =>
      have hh : h ∈ xs := by rw [hx]; simp
      have hs' : search nTokens.length eTokens.length s = some h := (hm h).1 hh
      have heq : h = p := Option.some.inj (hs'.symm.trans hs)
      change TM2ListLookup.lookup (xs.map tag, (0,(false,(0,0)))) = _
      simp [TM2ListLookup.lookup, hx, heq, tag, hs]

end Shared.Beeping.NPcoNP.Source284SearchSelectTM2
