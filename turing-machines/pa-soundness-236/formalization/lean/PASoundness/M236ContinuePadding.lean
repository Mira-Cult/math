import PASoundness.M236RestartAlignment
/-! Physical traversal after a checked continue return with finite padding. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Continue
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def fitsPadding (residual : List Bool) : Bool :=
  match Control.resolveZeros Grammar.nodes 158 157 residual with
  | none => false
  | some next => decide (next <+: residual ++ List.replicate 2 false)

def paddingOK (word : List Bool) : Bool :=
  let pre := word.dropLast
  match pathName 157 word with
  | some "_continue.1" =>
    match candidate1 pre with
    | some (_, _, _, residual) => fitsPadding residual
    | none => false
  | some "_continue.2" =>
    match candidate2 pre with
    | some (_, _, _, _, residual) => fitsPadding residual
    | none => false
  | some "_continue.3" =>
    match candidate3 pre with
    | some (_, _, _, _, _, residual) => fitsPadding residual
    | none => false
  | _ => true

/-- Two zero cells suffice for every resolved literal continue destination. -/
theorem padding_checked : Grammar.completePaths.all paddingOK = true := by decide

theorem padding1_prefix (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none))
    (first : Nat) (runs : List (Fin 6)) (bit : Bool) (residual next : List Bool)
    (hcan : candidate1 pre = some (first, runs, bit, residual))
    (hnext : Control.resolveZeros Grammar.nodes 158 157 residual = some next) :
    next <+: residual ++ List.replicate 2 false := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp padding_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold paddingOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  unfold fitsPadding at hc
  rw [hnext] at hc
  exact of_decide_eq_true hc

theorem padding2_prefix (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none))
    (first second : Nat) (runs : List (Fin 6)) (bit : Bool) (residual next : List Bool)
    (hcan : candidate2 pre = some (first, second, runs, bit, residual))
    (hnext : Control.resolveZeros Grammar.nodes 158 157 residual = some next) :
    next <+: residual ++ List.replicate 2 false := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp padding_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold paddingOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  unfold fitsPadding at hc
  rw [hnext] at hc
  exact of_decide_eq_true hc

theorem padding3_prefix (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none))
    (first second third : Nat) (runs : List (Fin 6)) (bit : Bool) (residual next : List Bool)
    (hcan : candidate3 pre = some (first, second, third, runs, bit, residual))
    (hnext : Control.resolveZeros Grammar.nodes 158 157 residual = some next) :
    next <+: residual ++ List.replicate 2 false := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp padding_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold paddingOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, hcan] at hc
  unfold fitsPadding at hc
  rw [hnext] at hc
  exact of_decide_eq_true hc

/-- A resolved literal leaf is physically traversed when the full tape has
its checked two-zero padding. Its possible final event is preserved. -/
theorem physical_follow_padded (residual next : List Bool)
    (hnext : Control.resolveZeros Grammar.nodes 158 157 residual = some next)
    (hprefix : next <+: residual ++ List.replicate 2 false)
    (extra : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head, ⟨left, residual ++ (List.replicate (2 + extra) false ++ tail)⟩⟩ c) :
    ∃ (pre : List Bool) (j : Fin 158) (last : Bool) (name : String)
      (target : Fin 237) (write : Bool) (move : Move) (event : Option Bool) (finish : Config 237),
      next = pre ++ [last] ∧ Grammar.edge Grammar.nodes j last = .leaf name target write move event ∧
      (machineWordSystem raw rawLabels).Block c next.length finish event.toList ∧
      Related ⟨target, move.apply (head + (pre.length : Int)),
        Grammar.finalTape pre last write move left
          ((residual ++ List.replicate 2 false).drop next.length ++ (List.replicate extra false ++ tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) next.length (mapConfig finish) event.toList ∧
      0 < next.length := by
  obtain ⟨rest, he⟩ := hprefix
  have hr : rest = (residual ++ List.replicate 2 false).drop next.length := by
    rw [← he]
    simp
  subst rest
  have htape : residual ++ (List.replicate (2 + extra) false ++ tail) =
      next ++ ((residual ++ List.replicate 2 false).drop next.length ++ (List.replicate extra false ++ tail)) := by
    calc
      _ = (residual ++ List.replicate 2 false) ++ (List.replicate extra false ++ tail) := by
        rw [← List.replicate_append_replicate]
        simp [List.append_assoc]
      _ = (next ++ (residual ++ List.replicate 2 false).drop next.length) ++
          (List.replicate extra false ++ tail) := congrArg
            (fun xs : List Bool => xs ++ (List.replicate extra false ++ tail)) he.symm
      _ = _ := by simp [List.append_assoc]
  rw [htape] at hrel
  have hh : Related ⟨Grammar.nodes[157].state, head,
      ⟨left, next ++ ((residual ++ List.replicate 2 false).drop next.length ++
        (List.replicate extra false ++ tail))⟩⟩ c := by
    simpa only [Grammar.root_state] using hrel
  exact Grammar.physical_follow_leaf (Control.resolveZeros_sound Grammar.nodes 158 157 residual next hnext)
    head left ((residual ++ List.replicate 2 false).drop next.length ++ (List.replicate extra false ++ tail)) c hh
end PASoundness.M236.Continue
