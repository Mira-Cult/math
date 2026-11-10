import PASoundness.M236FastTable

/-! A finite grammar graph whose edges carry the full expected literal table
row and event. The generated instance remains untrusted until checked. -/
namespace PASoundness.M236.Grammar
open Shared.Beeping.Machines

inductive Edge where
  | node (child : Fin 158)
  | leaf (name : String) (target : Fin 237) (write : Bool)
      (move : Move) (event : Option Bool)
  deriving DecidableEq, Repr

structure Node where
  state : Fin 237
  zero : Edge
  one : Edge
  deriving DecidableEq, Repr

def edge (nodes : Vector Node 158) (i : Fin 158) (b : Bool) : Edge :=
  if b then nodes[i].one else nodes[i].zero

def expected (nodes : Vector Node 158) (b : Bool) : Edge → Row 237 × Option Bool
  | .node j => (⟨b, .right, nodes[j].state, false⟩, none)
  | .leaf _ target write move event => (⟨write, move, target, false⟩, event)

def rowValid (nodes : Vector Node 158) (i : Fin 158) (b : Bool) : Prop :=
  (FastTable.row nodes[i].state b, FastTable.event nodes[i].state b) = expected nodes b (edge nodes i b)

instance (nodes : Vector Node 158) (i : Fin 158) (b : Bool) : Decidable (rowValid nodes i b) := inferInstanceAs (Decidable (_ = _))

/-- A path chooses left/right edges and ends exactly at a grammar leaf. -/
inductive LeafPath (nodes : Vector Node 158) : Fin 158 → List Bool → Prop where
  | leaf (i : Fin 158) (b : Bool) (name : String) (target : Fin 237)
      (write : Bool) (move : Move) (event : Option Bool)
      (h : edge nodes i b = .leaf name target write move event) :
      LeafPath nodes i [b]
  | step (i j : Fin 158) (b : Bool) (tail : List Bool)
      (h : edge nodes i b = .node j) (rest : LeafPath nodes j tail) :
      LeafPath nodes i (b :: tail)

def childDecreases (nodes : Vector Node 158) (i : Fin 158) (b : Bool) : Prop :=
  match edge nodes i b with
  | .node j => j.val < i.val
  | .leaf .. => True

instance (nodes : Vector Node 158) (i : Fin 158) (b : Bool) : Decidable (childDecreases nodes i b) := by
  unfold childDecreases
  cases edge nodes i b <;> infer_instance

/-- All leaf paths enumerated with an explicit recursion fuel. -/
def paths (nodes : Vector Node 158) : Nat → Fin 158 → List (List Bool)
  | 0, _ => []
  | fuel + 1, i =>
      let follow (b : Bool) :=
        match edge nodes i b with
        | .node j => (paths nodes fuel j).map (b :: ·)
        | .leaf .. => [[b]]
      follow false ++ follow true

theorem path_length (ns : Vector Node 158)
    (hdec : ∀ (i : Fin 158) (b : Bool), childDecreases ns i b)
    {i : Fin 158} {word : List Bool} (h : LeafPath ns i word) : word.length ≤ i.val + 1 := by
  induction h with
  | leaf i b name target write move event he => simp
  | step i j b tail he rest ih =>
    have hd := hdec i b
    simp only [childDecreases, he] at hd
    simp only [List.length_cons]
    omega

theorem path_in_paths (ns : Vector Node 158) {i : Fin 158} {word : List Bool}
    (h : LeafPath ns i word) : ∀ fuel, word.length ≤ fuel → word ∈ paths ns fuel i := by
  induction h with
  | leaf i b name target write move event he =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      cases b <;> simp [paths, he]
  | step i j b tail he rest ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hf' : tail.length ≤ fuel := by simp only [List.length_cons, Nat.succ_le_succ_iff] at hf; exact hf
      have hm := ih fuel hf'
      cases b <;> simp [paths, he, hm]

theorem paths_sound (ns : Vector Node 158) (fuel : Nat) (i : Fin 158) (word : List Bool)
    (h : word ∈ paths ns fuel i) : LeafPath ns i word := by
  induction fuel generalizing i word with
  | zero => simp [paths] at h
  | succ fuel ih =>
    simp only [paths, List.mem_append] at h
    rcases h with h | h
    · cases he : edge ns i false with
      | node j =>
        simp only [he, List.mem_map] at h
        obtain ⟨tail, ht, rfl⟩ := h
        exact LeafPath.step i j false tail he (ih j tail ht)
      | leaf name target write move event =>
        simp only [he, List.mem_singleton] at h
        subst word
        exact LeafPath.leaf i false name target write move event he
    · cases he : edge ns i true with
      | node j =>
        simp only [he, List.mem_map] at h
        obtain ⟨tail, ht, rfl⟩ := h
        exact LeafPath.step i j true tail he (ih j tail ht)
      | leaf name target write move event =>
        simp only [he, List.mem_singleton] at h
        subst word
        exact LeafPath.leaf i true name target write move event he

end PASoundness.M236.Grammar
