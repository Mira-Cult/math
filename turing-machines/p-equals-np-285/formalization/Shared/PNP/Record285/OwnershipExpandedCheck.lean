import Shared.PNP.Record285.OwnershipEndpoint

/-! Check that a primitive ownership graph expands every atomic move into a
decrement/increment loop, and otherwise preserves both control outcomes. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore

def expansionRow (logical expanded : Array Row) (mapping : Array Nat) (i : Nat) : Bool :=
  match logical[i]?, mapping[i]? with
  | some row, some pc =>
    match expanded[pc]?, mapping[row.no]?, mapping[row.yes]? with
    | some target, some no, some yes =>
      match row.action with
      | .move src dst =>
        match expanded[target.no]? with
        | some body =>
          decide (src ≠ dst ∧ target.action = .dec src ∧ target.yes = no ∧ row.no = row.yes ∧
            body.action = .inc dst ∧ body.no = pc ∧ body.yes = pc)
        | none => false
      | _ => decide (target.action = row.action ∧ target.no = no ∧ target.yes = yes)
    | _, _, _ => false
  | _, _ => false

def expansionCheck (logical expanded : Array Row) (mapping : Array Nat) : Bool :=
  decide (logical.size = mapping.size ∧ mapping[0]? = some 0) &&
    (List.range logical.size).all (expansionRow logical expanded mapping)

def ExpansionMatch (expanded : Array Row) (row : Row) (pc : Nat) (target : Row) (no yes : Nat) : Prop :=
  match row.action with
  | .move src dst =>
    ∃ body, expanded[target.no]? = some body ∧ src ≠ dst ∧ target.action = .dec src ∧
      target.yes = no ∧ row.no = row.yes ∧ body.action = .inc dst ∧ body.no = pc ∧ body.yes = pc
  | _ => target.action = row.action ∧ target.no = no ∧ target.yes = yes

theorem expansionRow_sound (logical expanded : Array Row) (mapping : Array Nat)
    (i pc : Nat) (row : Row) (hr : logical[i]? = some row) (hp : mapping[i]? = some pc)
    (h : expansionRow logical expanded mapping i = true) :
    ∃ target no yes, expanded[pc]? = some target ∧ mapping[row.no]? = some no ∧
      mapping[row.yes]? = some yes ∧ ExpansionMatch expanded row pc target no yes := by
  simp only [expansionRow,hr,hp] at h
  cases ht : expanded[pc]? with
  | none => simp [ht] at h
  | some target =>
    cases hn : mapping[row.no]? with
    | none => simp [ht,hn] at h
    | some no =>
      cases hy : mapping[row.yes]? with
      | none => simp [ht,hn,hy] at h
      | some yes =>
        refine ⟨target,no,yes,rfl,rfl,rfl,?_⟩
        cases row with
        | mk action rn ry =>
          cases action with
          | inc i => simpa [ht,hn,hy,ExpansionMatch] using h
          | dec i => simpa [ht,hn,hy,ExpansionMatch] using h
          | half i => simpa [ht,hn,hy,ExpansionMatch] using h
          | beep => simpa [ht,hn,hy,ExpansionMatch] using h
          | move src dst =>
            cases hb : expanded[target.no]? with
            | none => simp [ht,hn,hy,hb] at h
            | some body =>
              have hh : src ≠ dst ∧ target.action = .dec src ∧ target.yes = no ∧ rn = ry ∧
                  body.action = .inc dst ∧ body.no = pc ∧ body.yes = pc := by
                simpa [ht,hn,hy,hb] using h
              exact ⟨body,hb,hh⟩

end Shared.PNP.Record285.OwnershipCore
