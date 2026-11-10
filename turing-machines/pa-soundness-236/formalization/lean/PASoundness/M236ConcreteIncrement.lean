import PASoundness.M236RootIncrement
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Redispatch
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- The checked finite grammar contains a named increment path for each of
the nine registers. These witnesses do not assert source-program reachability. -/
theorem named_increment_path_exists (r : Fin 9) :
    ∃ (word : List Bool) (write : Bool), Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none) := by
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 := by omega
  rcases hr with h | h | h | h | h | h | h | h | h <;> subst r
  · refine ⟨[false, false, false, true, true, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
    apply Preparation.NamedPath.step 31 2 false _ _ (by decide)
    apply Preparation.NamedPath.step 2 1 true _ _ (by decide)
    apply Preparation.NamedPath.step 1 0 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 0 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, false, true, false, true, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
    apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
    apply Preparation.NamedPath.step 30 4 false _ _ (by decide)
    apply Preparation.NamedPath.step 4 3 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 3 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, false, false, true, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
    apply Preparation.NamedPath.step 31 2 false _ _ (by decide)
    apply Preparation.NamedPath.step 2 1 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 1 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, false, true, true, false, true, true, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
    apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
    apply Preparation.NamedPath.step 30 29 true _ _ (by decide)
    apply Preparation.NamedPath.step 29 24 false _ _ (by decide)
    apply Preparation.NamedPath.step 24 23 true _ _ (by decide)
    apply Preparation.NamedPath.step 23 22 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 22 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, false, true, true, true, true, true, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
    apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
    apply Preparation.NamedPath.step 30 29 true _ _ (by decide)
    apply Preparation.NamedPath.step 29 28 true _ _ (by decide)
    apply Preparation.NamedPath.step 28 27 true _ _ (by decide)
    apply Preparation.NamedPath.step 27 26 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 26 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, true, false, true, true, true, true, false, true, false, true, true], true, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
    apply Preparation.NamedPath.step 140 82 false _ _ (by decide)
    apply Preparation.NamedPath.step 82 81 true _ _ (by decide)
    apply Preparation.NamedPath.step 81 80 true _ _ (by decide)
    apply Preparation.NamedPath.step 80 79 true _ _ (by decide)
    apply Preparation.NamedPath.step 79 78 true _ _ (by decide)
    apply Preparation.NamedPath.step 78 48 false _ _ (by decide)
    apply Preparation.NamedPath.step 48 47 true _ _ (by decide)
    apply Preparation.NamedPath.step 47 46 false _ _ (by decide)
    apply Preparation.NamedPath.step 46 45 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 45 true _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, false, true, true, false, false, true, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
    apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
    apply Preparation.NamedPath.step 30 29 true _ _ (by decide)
    apply Preparation.NamedPath.step 29 24 false _ _ (by decide)
    apply Preparation.NamedPath.step 24 21 false _ _ (by decide)
    apply Preparation.NamedPath.step 21 20 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 20 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, true, false, true, false, true, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
    apply Preparation.NamedPath.step 140 82 false _ _ (by decide)
    apply Preparation.NamedPath.step 82 81 true _ _ (by decide)
    apply Preparation.NamedPath.step 81 38 false _ _ (by decide)
    apply Preparation.NamedPath.step 38 37 true _ _ (by decide)
    exact Preparation.NamedPath.leaf 37 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
  · refine ⟨[false, true, false, false, true, false, false, true, false, false], false, ?_⟩
    apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
    apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
    apply Preparation.NamedPath.step 140 82 false _ _ (by decide)
    apply Preparation.NamedPath.step 82 36 false _ _ (by decide)
    apply Preparation.NamedPath.step 36 25 true _ _ (by decide)
    apply Preparation.NamedPath.step 25 14 false _ _ (by decide)
    apply Preparation.NamedPath.step 14 11 false _ _ (by decide)
    apply Preparation.NamedPath.step 11 10 true _ _ (by decide)
    apply Preparation.NamedPath.step 10 9 false _ _ (by decide)
    exact Preparation.NamedPath.leaf 9 false _ (by decide) ⟨_, _, _, _, _, rfl⟩
/-- Materialize a finite zipper as a full two-way tape with blank background. -/
def realizeConfig {n : Nat} (z : Configuration n) : Config n :=
  ⟨z.state, z.head, fun x =>
    if z.head ≤ x then z.tape.right.getD (x - z.head).toNat false
    else z.tape.left.getD (z.head - x - 1).toNat false⟩

/-- The materialized full tape represents exactly the finite zipper. -/
theorem realize_related {n : Nat} (z : Configuration n) : Related z (realizeConfig z) := by
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro i
    change (if z.head ≤ z.head + (i : Int) then
      z.tape.right.getD (z.head + (i : Int) - z.head).toNat false
      else z.tape.left.getD (z.head - (z.head + (i : Int)) - 1).toNat false) = _
    have h : z.head ≤ z.head + (i : Int) := by omega
    have he : z.head + (i : Int) - z.head = (i : Int) := by omega
    simp [h, he]
  · intro i
    change (if z.head ≤ z.head - (i : Int) - 1 then
      z.tape.right.getD (z.head - (i : Int) - 1 - z.head).toNat false
      else z.tape.left.getD (z.head - (z.head - (i : Int) - 1) - 1).toNat false) = _
    have h : ¬ z.head ≤ z.head - (i : Int) - 1 := by omega
    have he : z.head - (z.head - (i : Int) - 1) - 1 = (i : Int) := by omega
    simp [h, he]

/-- The explicitly described finite root tape as a full two-way configuration. -/
def rootConfig (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat)
    (gap : Nat) (word : List Bool) (head : Int) (left tail : List Bool) : Config 237 :=
  realizeConfig ⟨79, head,
    ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
      word ++ false :: false :: (List.replicate gap false ++ true :: false ::
        selectedPayload registers r reserve tail)⟩⟩

/-- Each of the nine registers has a concrete grammar path and a concrete
finite-support ordinary tape on which the selected quotient performs the
corresponding silent increment and returns to its root. -/
theorem concrete_register_increment (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (reserve : List Nat) (gap : Nat) (head : Int) (left tail : List Bool) :
    ∃ (word : List Bool) (write : Bool) (time : Nat) (endHead : Int) (scratch : Nat)
      (pcTail : List Bool) (finish : Config 237),
      Preparation.NamedPath Grammar.nodes 157 word
        (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none) ∧
      0 < time ∧
      (machineWordSystem raw rawLabels).Block
        (rootConfig registers r reserve gap word head left tail) time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block
        (mapConfig (rootConfig registers r reserve gap word head left tail)) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  obtain ⟨word, write, hpath⟩ := named_increment_path_exists r
  let c := rootConfig registers r reserve gap word head left tail
  have hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          selectedPayload registers r reserve tail)⟩⟩ c := realize_related _
  obtain ⟨time, endHead, scratch, pcTail, finish, ht, hp, hr, hq, hd⟩ :=
    physical_root_increment registers r reserve gap word write hpath head left tail c hrel
  exact ⟨word, write, time, endHead, scratch, pcTail, finish, hpath, ht, hp, hr, hq, hd⟩
end PASoundness.M236.Redispatch
