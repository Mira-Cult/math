import PASoundness.M236ControlSuccessor
import Mathlib.Data.List.Nodup
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Control

theorem grammar_paths_nodup (nodes : Vector Grammar.Node 158) :
    ∀ fuel i, (Grammar.paths nodes fuel i).Nodup := by
  intro fuel
  induction fuel with
  | zero => intro i; simp [Grammar.paths]
  | succ fuel ih =>
    intro i
    simp only [Grammar.paths, List.nodup_append]
    have hleft : (match Grammar.edge nodes i false with
      | .node j => (Grammar.paths nodes fuel j).map (false :: ·)
      | .leaf .. => [[false]]).Nodup := by
      cases he : Grammar.edge nodes i false with
      | node j => exact (ih j).map (by intro a b h; simpa using h)
      | leaf name target write move event => simp
    have hright : (match Grammar.edge nodes i true with
      | .node j => (Grammar.paths nodes fuel j).map (true :: ·)
      | .leaf .. => [[true]]).Nodup := by
      cases he : Grammar.edge nodes i true with
      | node j => exact (ih j).map (by intro a b h; simpa using h)
      | leaf name target write move event => simp
    refine ⟨hleft, hright, ?_⟩
    intro a ha b hb
    cases he : Grammar.edge nodes i false with
    | node j =>
      simp only [he, List.mem_map] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      cases hf : Grammar.edge nodes i true with
      | node k =>
        simp only [hf, List.mem_map] at hb
        obtain ⟨y, hy, rfl⟩ := hb
        simp
      | leaf name target write move event =>
        simp only [hf, List.mem_singleton] at hb
        subst b
        simp
    | leaf name target write move event =>
      simp only [he, List.mem_singleton] at ha
      subst a
      cases hf : Grammar.edge nodes i true with
      | node k =>
        simp only [hf, List.mem_map] at hb
        obtain ⟨y, hy, rfl⟩ := hb
        simp
      | leaf name target write move event =>
        simp only [hf, List.mem_singleton] at hb
        subst b
        simp

theorem adjacent_nodup_keys : (adjacentPaths.map Prod.fst).Nodup := by
  rw [adjacent_domain]
  exact grammar_paths_nodup Grammar.nodes 158 157

theorem adjacent_functional (word next next' : List Bool)
    (h : (word, next) ∈ adjacentPaths) (h' : (word, next') ∈ adjacentPaths) : next = next' := by
  have hp := List.inj_on_of_nodup_map adjacent_nodup_keys h h' rfl
  exact congrArg Prod.snd hp


/-- Resolving any fixed finite prefix rule has at most one destination. -/
theorem resolved_successor_functional (prefixFn : List Bool → Option (List Bool))
    (word next next' source source' : List Bool)
    (hp : prefixFn word = some source) (hp' : prefixFn word = some source')
    (h : resolveZeros Grammar.nodes 158 157 source = some next)
    (h' : resolveZeros Grammar.nodes 158 157 source' = some next') : next = next' := by
  rw [hp] at hp'
  cases hp'
  rw [h] at h'
  exact Option.some.inj h'

/-- The decoded zero branch also has at most one resolved destination. -/
theorem zero_successor_functional (word next next' tail tail' : List Bool) (bit bit' : Bool)
    (hd : decodeZero word = some (bit, tail)) (hd' : decodeZero word = some (bit', tail'))
    (h : resolveZeros Grammar.nodes 158 157 tail = some next)
    (h' : resolveZeros Grammar.nodes 158 157 tail' = some next') : next = next' := by
  rw [hd] at hd'
  cases hd'
  rw [h] at h'
  exact Option.some.inj h'
end PASoundness.M236.Control
