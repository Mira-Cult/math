import Shared.Beeping.NPcoNP.GrammarGraph284

/-! A staged, generic certificate for administrative jump contraction.
Every original row is checked for a successful target traversal, including
unreachable jumps; each retained output is separately checked against the
candidate graph. Numbering equality is an explicit premise. This does not
assert any producer-specific graph or establish the numbering certificate. -/
namespace Shared.Beeping.NPcoNP.Grammar284

/-- The exact output construction used for one retained row. -/
def contractRow (rows : Array Row) (mapping : Array (Option Nat)) (i : Nat) : Option Row := do
  let row ← rows[i]?
  let dst ← row.targets.mapM (target rows mapping (rows.size+1))
  pure ⟨row.op, dst⟩

/-- Check that the target traversal terminates successfully at this row. -/
def targetCheck (rows : Array Row) (mapping : Array (Option Nat)) (i : Nat) : Bool :=
  (target rows mapping (rows.size+1) i).isSome

/-- Compare one retained output, rejecting missing kept or output entries. -/
def contractRowCheck (rows : Array Row) (n : Numbering) (out : Array Row) (i : Nat) : Bool :=
  match n.kept[i]?, out[i]? with
  | some k, some r => contractRow rows n.map k == some r
  | _, _ => false

/-- A bounded consecutive shard of Boolean checks. -/
def contractCheckShard (f : Nat → Bool) (lo len : Nat) : Bool :=
  (List.range len).all fun i => f (lo+i)

theorem contractCheckShard_sound (f : Nat → Bool) (lo len i : Nat)
    (h : contractCheckShard f lo len = true) (hlo : lo ≤ i) (hhi : i < lo+len) :
    f i = true := by
  have ha := List.all_eq_true.mp h
  have hm : i-lo ∈ List.range len := by simp; omega
  have hh := ha (i-lo) hm
  simpa [Nat.add_sub_of_le hlo] using hh

theorem contractRowCheck_sound (rows : Array Row) (n : Numbering) (out : Array Row)
    (i : Nat) (hk : i < n.kept.size) (ho : i < out.size)
    (h : contractRowCheck rows n out i = true) :
    contractRow rows n.map n.kept[i] = some out[i] := by
  simpa [contractRowCheck, hk, ho] using h

private theorem mapM_some_of_each {α β : Type} (f : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, (f x).isSome = true) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    have ha := h a (by simp)
    cases hfa : f a with
    | none => simp [hfa] at ha
    | some b =>
      obtain ⟨bs, hbs⟩ := ih (by
        intro x hx
        exact h x (by simp [hx]))
      exact ⟨b::bs, by simp [hfa, hbs]⟩

private theorem mapM_of_forall₂ {α β : Type} (f : α → Option β)
    {xs : List α} {ys : List β} (h : List.Forall₂ (fun x y => f x = some y) xs ys) :
    xs.mapM f = some ys := by
  induction h with
  | nil => rfl
  | cons h hs ih => simp [h, ih]

/-- A sound finite contraction certificate. `hchecks` covers *every* input
row, matching the original all-jump cycle check, not merely reachable rows. -/
theorem contract_of_checked (rows : Array Row) (n : Numbering) (out : Graph)
    (hnum : number rows = n)
    (hne : n.kept.isEmpty = false)
    (hchecks : ∀ i < rows.size, targetCheck rows n.map i = true)
    (hentry : target rows n.map (rows.size+1) 0 = some out.entry)
    (hsize : n.kept.size = out.rows.size)
    (houts : ∀ i < n.kept.size, contractRowCheck rows n out.rows i = true) :
    contract rows = some out := by
  have hsuccessful : ∃ ys, (List.range rows.size).mapM
      (target rows n.map (rows.size+1)) = some ys := by
    apply mapM_some_of_each
    intro i hi
    exact hchecks i (List.mem_range.mp hi)
  obtain ⟨ys, hys⟩ := hsuccessful
  have hout : n.kept.toList.mapM (contractRow rows n.map) = some out.rows.toList := by
    apply mapM_of_forall₂
    apply List.forall₂_iff_get.mpr
    constructor
    · simpa using hsize
    · intro i hi ho
      have hk : i < n.kept.size := by simpa using hi
      have hr : i < out.rows.size := by simpa using ho
      simpa using contractRowCheck_sound rows n out.rows i hk hr (houts i hk)
  cases out with
  | mk entry result =>
    simp only at hentry hsize houts hout ⊢
    change n.kept.toList.mapM (fun i => do
      let row ← rows[i]?
      let dst ← row.targets.mapM (target rows n.map (rows.size+1))
      pure ⟨row.op, dst⟩) = some result.toList at hout
    simp only [contract, hnum, hne, Bool.false_eq_true, ↓reduceIte, hys,
      Option.bind_some, hentry]
    rw [hout]
    simp

end Shared.Beeping.NPcoNP.Grammar284
