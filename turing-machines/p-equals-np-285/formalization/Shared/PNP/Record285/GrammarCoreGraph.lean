import Shared.PNP.Record285.GrammarControlGraph

/-! A finite checker for a producer core graph against the literal machine's
verified unfolded grammar. The checker eliminates only break/continue leaves;
it compares both outgoing test outcomes and never assumes register values. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarAdministrative
open Shared.PNP.Record285.GrammarControlGraph

structure CoreRow where
  edge : Edge
  no : Nat
  yes : Nat
  deriving DecidableEq, Repr

/-- Resolve at most `fuel` control-only actions. `none` is rejected, including
fuel exhaustion; no arithmetic action or event can be skipped. -/
def settle : Nat → List Bool → Option (List Bool)
  | 0, _ => none
  | fuel+1, pc => do
    let row ← lookup pc
    if isAdministrative row.edge then
      let next ← row.no
      settle fuel next
    else
      pure pc

def checkRow (source : Array CoreRow) (positions : Array (List Bool)) (i : Nat) : Bool :=
  match source[i]?, positions[i]? with
  | some spec, some pc =>
    match lookup pc, positions[spec.no]?, positions[spec.yes]? with
    | some row, some no, some yes =>
      decide (row.edge = spec.edge) && !isAdministrative row.edge &&
      decide (row.no.bind (settle 3) = some no) &&
      decide (row.yes.bind (settle 3) = some yes)
    | _, _, _ => false
  | _, _ => false

def check (source : Array CoreRow) (positions : Array (List Bool)) : Bool :=
  decide (source.size = positions.size) &&
  decide (positions[0]? = some [false]) &&
  (List.range source.size).all (checkRow source positions)

/-- The finite check exposes the exact local row obligation for every source
index. In particular there is no assumption about either test outcome. -/
theorem check_at (source : Array CoreRow) (positions : Array (List Bool))
    (h : check source positions = true) (i : Nat) (hi : i < source.size) :
    checkRow source positions i = true := by
  have h' : (List.range source.size).all (checkRow source positions) = true := by
    simp only [check,Bool.and_eq_true_iff] at h
    exact h.2
  exact List.all_eq_true.mp h' i (List.mem_range.mpr hi)

/-- An accepted row has the same operation and both certified successors.
Missing rows, missing targets and exhausted control-only runs are rejected. -/
theorem checkRow_sound (source : Array CoreRow) (positions : Array (List Bool))
    (i : Nat) (spec : CoreRow) (pc : List Bool)
    (hs : source[i]? = some spec) (hp : positions[i]? = some pc)
    (h : checkRow source positions i = true) :
    ∃ row no yes, lookup pc = some row ∧ row.edge = spec.edge ∧
      isAdministrative row.edge = false ∧
      positions[spec.no]? = some no ∧ positions[spec.yes]? = some yes ∧
      row.no.bind (settle 3) = some no ∧ row.yes.bind (settle 3) = some yes := by
  simp only [checkRow,hs,hp] at h
  cases hr : lookup pc with
  | none => simp [hr] at h
  | some row =>
    cases hn : positions[spec.no]? with
    | none => simp [hr,hn] at h
    | some no =>
      cases hy : positions[spec.yes]? with
      | none => simp [hr,hn,hy] at h
      | some yes =>
        simp only [hr,hn,hy,Bool.and_eq_true_iff,decide_eq_true_eq] at h
        have ha : isAdministrative row.edge = false := by
          cases hc : isAdministrative row.edge <;> simp [hc] at h ⊢
        exact ⟨row,no,yes,rfl,h.1.1.1,ha,rfl,rfl,h.1.2,h.2⟩

end Shared.PNP.Record285.GrammarCoreGraph
