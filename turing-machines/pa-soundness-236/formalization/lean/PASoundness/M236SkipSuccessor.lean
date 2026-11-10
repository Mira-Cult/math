import PASoundness.M236GrammarSuccessor
/-! Checked finite grammar successors and their physical traversal. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

/-- Resolve a finite root-path prefix by reading zero after it is exhausted.
The fuel is an implementation bound for the checked finite grammar. -/
def resolveZeros (nodes : Vector Grammar.Node 158) : Nat → Fin 158 → List Bool → Option (List Bool)
  | 0, _, _ => none
  | fuel + 1, i, bits =>
    let bit := bits.headD false
    let rest := bits.drop 1
    match Grammar.edge nodes i bit with
    | .node j => (resolveZeros nodes fuel j rest).map (bit :: ·)
    | .leaf .. => some [bit]

theorem resolveZeros_sound (nodes : Vector Grammar.Node 158) (fuel : Nat)
    (i : Fin 158) (bits word : List Bool) (h : resolveZeros nodes fuel i bits = some word) :
    Grammar.LeafPath nodes i word := by
  induction fuel generalizing i bits word with
  | zero => simp [resolveZeros] at h
  | succ fuel ih =>
    simp only [resolveZeros] at h
    cases he : Grammar.edge nodes i (bits.headD false) with
    | node j =>
      rw [he] at h
      change (resolveZeros nodes fuel j (bits.drop 1)).map (bits.headD false :: ·) = some word at h
      cases hr : resolveZeros nodes fuel j (bits.drop 1) with
      | none =>
        rw [hr] at h
        contradiction
      | some tail =>
        rw [hr] at h
        have heq : bits.headD false :: tail = word := Option.some.inj h
        subst word
        exact Grammar.LeafPath.step i j (bits.headD false) tail he (ih j (bits.drop 1) tail hr)
    | leaf name target write move event =>
      rw [he] at h
      have heq : [bits.headD false] = word := Option.some.inj h
      subst word
      exact Grammar.LeafPath.leaf i (bits.headD false) name target write move event he

def skipOK (word : List Bool) : Bool :=
  match decodeZero word with
  | none => true
  | some (_, tail) =>
    match resolveZeros Grammar.nodes 158 157 tail with
    | none => false
    | some next => decide (tail ++ List.replicate (next.length - tail.length) false = next ∧
        next.length - tail.length ≤ 5)

/-- Kernel-checked finite graph coverage; paths lacking a zero-return decoding
are intentionally outside this check. -/
theorem skip_checked : Grammar.completePaths.all skipOK = true := by decide

/-- Every named decrement zero return resolves to an actual literal grammar
leaf by at most five additional zero bits. -/
theorem decrement_skipped_leaf (r : Fin 9) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none)) :
    ∃ (bit : Bool) (tail next : List Bool),
      decodeZero word = some (bit, tail) ∧
      resolveZeros Grammar.nodes 158 157 tail = some next ∧
      Grammar.LeafPath Grammar.nodes 157 next ∧
      tail ++ List.replicate (next.length - tail.length) false = next ∧
      next.length - tail.length ≤ 5 := by
  obtain ⟨bit, tail, hd⟩ := decodeZero_named r word write hpath
  have hm := Grammar.every_leaf_path word (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp skip_checked) word hm
  unfold skipOK at hc
  rw [hd] at hc
  cases hn : resolveZeros Grammar.nodes 158 157 tail with
  | none => simp [hn] at hc
  | some next =>
    simp only [hn] at hc
    have hh := of_decide_eq_true hc
    exact ⟨bit, tail, next, hd, hn, resolveZeros_sound Grammar.nodes 158 157 tail next hn, hh⟩

/-- Given five finite blank cells after a zero-branch return, the resolved
skipped successor leaf is physically traversed with its exact event word. -/
theorem physical_skipped_follow (r : Fin 9) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (bit : Bool) (pcTail : List Bool) (hdecode : decodeZero word = some (bit, pcTail))
    (padding : Nat) (hspace : 5 ≤ padding) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head, ⟨left, pcTail ++ (List.replicate padding false ++ tail)⟩⟩ c) :
    ∃ (next pre : List Bool) (j : Fin 158) (last : Bool) (name : String)
      (target : Fin 237) (write2 : Bool) (move : Move) (event : Option Bool) (finish : Config 237),
      resolveZeros Grammar.nodes 158 157 pcTail = some next ∧
      next = pre ++ [last] ∧ Grammar.edge Grammar.nodes j last = .leaf name target write2 move event ∧
      (machineWordSystem raw rawLabels).Block c next.length finish event.toList ∧
      Related ⟨target, move.apply (head + (pre.length : Int)),
        Grammar.finalTape pre last write2 move left
          (List.replicate (padding - (next.length - pcTail.length)) false ++ tail)⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) next.length
        (mapConfig finish) event.toList ∧ 0 < next.length := by
  obtain ⟨b, p, next, hd, hn, hl, he, hbound⟩ := decrement_skipped_leaf r word write hpath
  rw [hdecode] at hd
  cases hd
  let need := next.length - pcTail.length
  have he' : pcTail ++ List.replicate need false = next := he
  have hneed : need ≤ padding := by dsimp [need]; omega
  have hn' : need + (padding - need) = padding := by omega
  have htape : pcTail ++ (List.replicate padding false ++ tail) =
      next ++ (List.replicate (padding - (next.length - pcTail.length)) false ++ tail) := by
    change pcTail ++ (List.replicate padding false ++ tail) =
      next ++ (List.replicate (padding - need) false ++ tail)
    calc
      _ = pcTail ++ ((List.replicate need false ++ List.replicate (padding - need) false) ++ tail) := by
        rw [List.replicate_append_replicate, hn']
      _ = (pcTail ++ List.replicate need false) ++ (List.replicate (padding - need) false ++ tail) := by
        simp only [List.append_assoc]
      _ = next ++ (List.replicate (padding - need) false ++ tail) := by rw [he']
  rw [htape] at hrel
  have hroot : Related ⟨Grammar.nodes[157].state, head,
      ⟨left, next ++ (List.replicate (padding - (next.length - pcTail.length)) false ++ tail)⟩⟩ c := by
    simpa only [Grammar.root_state] using hrel
  obtain ⟨pre, j, last, name, target, write2, move, event, finish, hw, hedge, hp, hr, hq, ht⟩ :=
    Grammar.physical_follow_leaf hl head left
      (List.replicate (padding - (next.length - pcTail.length)) false ++ tail) c hroot
  exact ⟨next, pre, j, last, name, target, write2, move, event, finish, hn, hw, hedge, hp, hr, hq, ht⟩

/-- A zero decrement followed by its skipped grammar successor is a pair of
positive literal segments when the displayed finite gap bound holds. -/
theorem physical_zero_to_skipped (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap : Nat) (hgap : 2 ≤ gap)
    (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: false ::
          Redispatch.selectedPayload registers r reserve tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (scratch1 scratch2 : Nat) (bit : Bool)
      (pcTail next pre : List Bool) (j : Fin 158) (last : Bool) (name : String)
      (target : Fin 237) (write2 : Bool) (move : Move) (event : Option Bool) (mid finish : Config 237),
      decodeZero word = some (bit, pcTail) ∧ 0 < time ∧
      (machineWordSystem raw rawLabels).Block c time mid [] ∧
      (machineWordSystem raw rawLabels).Block c (time + next.length) finish event.toList ∧
      resolveZeros Grammar.nodes 158 157 pcTail = some next ∧ next = pre ++ [last] ∧
      Grammar.edge Grammar.nodes j last = .leaf name target write2 move event ∧
      Related ⟨target, move.apply (endHead + (pre.length : Int)),
        Grammar.finalTape pre last write2 move (false :: true :: true :: (List.replicate 7 false ++ left))
          (List.replicate ((gap + (scratch2 + scratch1 + 3)) - (next.length - pcTail.length)) false ++
            true :: false :: (bank (UnaryNine.values registers ++ reserve) ++ false :: tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (time + next.length)
        (mapConfig finish) event.toList ∧ 0 < next.length := by
  obtain ⟨time, endHead, scratch1, scratch2, bit, pcTail, mid, hdecode, ht, hp, hr, hq, hd, hout⟩ :=
    physical_root_zero_decoded registers r hzero reserve gap word write hpath head left tail c hrel
  have hspace : 5 ≤ gap + (scratch2 + scratch1 + 3) := by omega
  obtain ⟨next, pre, j, last, name, target, write2, move, event, finish, hn, hw, hedge, hp2, hr2, hq2, ht2⟩ :=
    physical_skipped_follow r word write hpath bit pcTail hdecode (gap + (scratch2 + scratch1 + 3))
      hspace endHead (false :: true :: true :: (List.replicate 7 false ++ left))
      (true :: false :: (bank (UnaryNine.values registers ++ reserve) ++ false :: tail)) mid hr
  refine ⟨time, endHead, scratch1, scratch2, bit, pcTail, next, pre, j, last, name, target, write2, move, event, mid, finish,
    hdecode, ht, hp, ?_, hn, hw, hedge, hr2, ?_, ht2⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hp2
  · simpa using hq.trans (machineWordSystem machine machineLabels) hq2
end PASoundness.M236.Control
