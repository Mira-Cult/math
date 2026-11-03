import Shared.PNP.Record285.GrammarAcyclic

/-! Every grammar path has the corresponding literal preserving prefix and
exact final physical row, including non-preserving control leaves. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch

theorem walk_leaf_step (n : Nat) (b : Bool) (bs : List Bool) (found e : Edge)
    (he : nodeEdge n b = some found) (hleaf : isLeaf found = true)
    (hwalk : walk n (b::bs) = some e) : bs = [] ∧ found = e := by
  cases found <;> cases bs <;> simp [isLeaf,walk,he] at * <;> assumption

/-- At a leaf, the prior prefix reaches its parent by literal preserving
transitions and the final row agrees with that exact grammar operation. -/
theorem direct_leaf (n : Nat) (b : Bool) (bs : List Bool) (found e : Edge)
    (he : nodeEdge n b = some found) (hleaf : isLeaf found = true)
    (hwalk : walk n (b::bs) = some e) :
    ∃ pre bit parent row, b::bs = pre++[bit] ∧
      route (state n) pre = some (state parent) ∧ nodeEdge parent bit = some e ∧
      expected e bit = some row ∧ Record285.machine.table.row (state parent) bit = row := by
  obtain ⟨hbs,hfound⟩ := walk_leaf_step n b bs found e he hleaf hwalk
  subst bs
  subst e
  obtain ⟨row,hexpected,hrow⟩ := edge_verified n b found he
  refine ⟨[],b,n,row,by simp,by simp [route],he,hexpected,?_⟩
  rw [ArtifactEndpoint.literal_rows]
  exact hrow

theorem walk_final_edge (code : List Bool) (n : Nat) (e : Edge)
    (hwalk : walk n code = some e) :
    ∃ pre bit parent row, code = pre++[bit] ∧
      route (state n) pre = some (state parent) ∧ nodeEdge parent bit = some e ∧
      expected e bit = some row ∧ Record285.machine.table.row (state parent) bit = row := by
  induction code generalizing n with
  | nil => simp [walk] at hwalk
  | cons b bs ih =>
    cases he : nodeEdge n b with
    | none => simp [walk,he] at hwalk
    | some found =>
      cases found with
      | node j =>
        have hw : walk j bs = some e := by simpa only [walk,he] using hwalk
        obtain ⟨row,hexpected,hrow⟩ := edge_verified n b (.node j) he
        simp only [expected] at hexpected
        split at hexpected
        next hj =>
          simp only [Option.some.injEq] at hexpected
          rw [← hexpected] at hrow
          obtain ⟨pre,bit,parent,last,hcode,hroute,hedge,hexp,hlast⟩ := ih j hw
          refine ⟨b::pre,bit,parent,last,?_,?_,hedge,hexp,hlast⟩
          · simp only [List.cons_append,hcode]
          · simpa [route,hrow] using hroute
        next hj => contradiction
      | inc j => exact direct_leaf n b bs (.inc j) e he rfl hwalk
      | dec j => exact direct_leaf n b bs (.dec j) e he rfl hwalk
      | half j => exact direct_leaf n b bs (.half j) e he rfl hwalk
      | beep => exact direct_leaf n b bs .beep e he rfl hwalk
      | brk j => exact direct_leaf n b bs (.brk j) e he rfl hwalk
      | cont j => exact direct_leaf n b bs (.cont j) e he rfl hwalk

theorem root_final_edge (code : List Bool) (e : Edge) (hwalk : walk 162 code = some e) :
    ∃ pre bit parent row, code = pre++[bit] ∧
      route treeRoot pre = some (state parent) ∧ nodeEdge parent bit = some e ∧
      expected e bit = some row ∧ Record285.machine.table.row (state parent) bit = row := by
  have h := walk_final_edge code 162 e hwalk
  simpa only [root_state] using h

end Shared.PNP.Record285.Grammar
