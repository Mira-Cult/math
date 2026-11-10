import PASoundness.M236UnaryAnchor
import PASoundness.M236Grammar
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Grammar
open PASoundness.M236.UnaryAnchor

def encodeRuns : List Bool → Nat → Option (List (Fin 6))
  | [], count => if count = 0 then some [] else none
  | true :: tail, count =>
      if h : count < 6 then (encodeRuns tail 0).map (⟨count, h⟩ :: ·) else none
  | false :: tail, count =>
      if count + 1 < 6 then encodeRuns tail (count + 1) else none

private theorem replicate_shift (n : Nat) (tail : List Bool) :
    List.replicate n false ++ false :: tail = List.replicate (n + 1) false ++ tail := by
  rw [List.replicate_succ]
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append] at *; rw [ih]

theorem encodeRuns_sound (bits : List Bool) (count : Nat) (runs : List (Fin 6))
    (h : encodeRuns bits count = some runs) :
    counterWord runs = List.replicate count false ++ bits := by
  induction bits generalizing count runs with
  | nil =>
    simp only [encodeRuns] at h
    split at h
    next hc => simp only [Option.some.injEq] at h; subst runs; simp [counterWord, hc]
    next _ => contradiction
  | cons bit tail ih =>
    cases bit with
    | false =>
      simp only [encodeRuns] at h
      split at h
      next hb =>
        have hh := ih (count + 1) runs h
        rw [hh]
        exact (replicate_shift count tail).symm
      next _ => contradiction
    | true =>
      simp only [encodeRuns] at h
      split at h
      next hb =>
        cases he : encodeRuns tail 0 with
        | none => simp [he] at h
        | some xs =>
          simp only [he, Option.map_some, Option.some.injEq] at h
          subst runs
          have ht := ih 0 xs he
          simp only [counterWord, ht, List.replicate_zero, List.nil_append]
      next _ => contradiction
/-- A path is usable by the return counter when its reversed, root-prefixed
word admits bounded run encoding and the resulting root prefix has two bits. -/
def codecOK (word : List Bool) : Bool :=
  match encodeRuns ([true, true, false] ++ word).reverse 0 with
  | none => false
  | some runs =>
      match counterPush runs [] with
      | true :: _ :: _ => true
      | _ => false

theorem checked_codecs : completePaths.all codecOK = true := by decide

/-- Every literal graph leaf path has a proved bounded-run representation and
its root-prefix condition is independent of register values. -/
theorem leaf_path_codec (word : List Bool) (h : LeafPath nodes 157 word) :
    ∃ (runs : List (Fin 6)) (bit : Bool) (pcTail : List Bool),
      counterWord runs = ([true, true, false] ++ word).reverse ∧
      counterPush runs [] = true :: bit :: pcTail := by
  have hm := every_leaf_path word h
  have hok := (List.all_eq_true.mp checked_codecs) word hm
  unfold codecOK at hok
  cases he : encodeRuns ([true, true, false] ++ word).reverse 0 with
  | none => simp only [he, Bool.false_eq_true] at hok
  | some runs =>
    simp only [he] at hok
    cases hp : counterPush runs [] with
    | nil => simp [hp] at hok
    | cons first rest =>
      cases first with
      | false => simp [hp] at hok
      | true =>
        cases rest with
        | nil => simp [hp] at hok
        | cons bit pcTail =>
          refine ⟨runs, bit, pcTail, ?_, hp⟩
          simpa using encodeRuns_sound ([true, true, false] ++ word).reverse 0 runs he

end PASoundness.M236.Grammar
