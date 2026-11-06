import Shared.Beeping.NPcoNP.Grammar284ControlSelector

/-! Deterministic parsing of a completed grammar leaf from a control word.
The continuation/reserve boundary is not determined by the control word. -/
namespace Shared.Beeping.NPcoNP.Grammar284LeafPrefix
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ControlSelector
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- Read a grammar path until its first operation, returning the unused word.
A node with no remaining bit or an invalid node index fails. -/
def parseLeaf (g : Grammar) : Leaf → List Bool → Option (String × List Bool)
  | .op name, suffix => some (name,suffix)
  | .node _, [] => none
  | .node i, bit::suffix => do
      let pair ← g.nodes[i]?
      parseLeaf g (if bit then pair.2 else pair.1) suffix

theorem walk_parses_leaf (g : Grammar) {start last : Leaf} {path : List Bool}
    (walk : Walk g start path last) (name : String) (finish : last=.op name)
    (suffix : List Bool) : parseLeaf g start (path++suffix)=some (name,suffix) := by
  induction walk with
  | stop leaf =>
    subst leaf
    simp [parseLeaf]
  | left i path last walk ih =>
    have hget : g.nodes[i.val]? = some (g.nodes[i.val]'i.isLt) := by simp
    simpa [parseLeaf,hget] using ih finish
  | right i path last walk ih =>
    have hget : g.nodes[i.val]? = some (g.nodes[i.val]'i.isLt) := by simp
    simpa [parseLeaf,hget] using ih finish

/-- Two complete leaf paths that are prefixes of the same word must be the
same path and name, with the same unparsed suffix. -/
theorem leaf_prefix_unique (g : Grammar) (start : Leaf) (p q s t : List Bool)
    (name name' : String) (hp : Walk g start p (.op name))
    (hq : Walk g start q (.op name')) (word : p++s=q++t) :
    p=q ∧ name=name' ∧ s=t := by
  have h1 := walk_parses_leaf g hp name rfl s
  have h2 := walk_parses_leaf g hq name' rfl t
  rw [word] at h1
  rw [h2] at h1
  have he : (name,s)=(name',t) := Option.some.inj h1.symm
  have hn : name=name' := congrArg Prod.fst he
  have ht : s=t := congrArg Prod.snd he
  subst t
  have hpq : p=q := List.append_cancel_right word
  exact ⟨hpq,hn,rfl⟩

/-- Equality of two encoded control words determines their completed
prepared leaf path and operation. It does not determine the continuation. -/
theorem controlWord_leaf_unique (p q c d : List Bool) (name name' : String)
    (hp : PreparedWalk p (.op name)) (hq : PreparedWalk q (.op name'))
    (word : controlWord p c=controlWord q d) : p=q ∧ name=name' := by
  obtain ⟨raw,hp',hwp⟩ := hp
  obtain ⟨raw',hq',hwq⟩ := hq
  have he : raw++(c++encode (List.replicate (14-(p++c).count false) 0)) =
      raw'++(d++encode (List.replicate (14-(q++d).count false) 0)) := by
    have hh := word
    simp only [controlWord] at hh
    rw [hp',hq'] at hh
    simp only [List.append_assoc] at hh
    rw [hp',hq']
    simpa only [List.append_assoc] using List.append_cancel_left hh
  obtain ⟨hraw,hname,_hsuffix⟩ := leaf_prefix_unique producerGrammar (.node producerGrammar.root)
    raw raw' _ _ name name' hwp hwq he
  exact ⟨by rw [hp',hq',hraw],hname⟩

/-- Whenever reserve remains, moving one complete zero block from reserve
into the continuation leaves the encoded control word unchanged. -/
theorem move_reserve_block (p c : List Bool) (budget : (p++c).count false<14) :
    controlWord p c = controlWord p (c++encode [0]) := by
  have hc : (p++(c++encode [0])).count false=(p++c).count false+1 := by
    simp [List.count_append,encode,block,Nat.add_assoc]
  have hn : 14-(p++c).count false = (14-(p++c).count false-1)+1 := by omega
  have hpad : encode (List.replicate (14-(p++c).count false) 0) =
      encode [0] ++ encode (List.replicate (14-(p++c).count false-1) 0) := by
    conv_lhs => rw [hn,List.replicate_succ]
    simp [encode,block]
  have hd : 14-((p++c).count false+1)=14-(p++c).count false-1 := by omega
  dsimp only [controlWord]
  rw [hc,hd,hpad]
  simp only [List.append_assoc]

/-- With two units of spare zero budget, both distinct splits satisfy the
selector's existing continuation budget. -/
theorem valid_reserve_collision (p c : List Bool) (budget : (p++c).count false≤12) :
    controlWord p c = controlWord p (c++encode [0]) ∧ c≠c++encode [0] ∧
      (p++c).count false≤13 ∧ (p++(c++encode [0])).count false≤13 := by
  refine ⟨move_reserve_block p c (by omega),?_,by omega,?_⟩
  · intro he
    have hl := congrArg List.length he
    simp [encode,block] at hl
  · have hc : (p++(c++encode [0])).count false=(p++c).count false+1 := by
      simp [List.count_append,encode,block,Nat.add_assoc]
    rw [hc]
    omega

#print axioms valid_reserve_collision
#print axioms move_reserve_block

/-- Concrete non-injectivity of the continuation boundary: one zero block
can be moved from reserve into the continuation without changing the word. -/
theorem continuation_reserve_collision :
    controlWord preparedPrefix [] = controlWord preparedPrefix (encode [0]) ∧
      ([] : List Bool) ≠ encode [0] ∧
      (preparedPrefix++([] : List Bool)).count false≤13 ∧
      (preparedPrefix++encode [0]).count false≤13 := by decide

#print axioms walk_parses_leaf
#print axioms leaf_prefix_unique
#print axioms controlWord_leaf_unique
#print axioms continuation_reserve_collision
end Shared.Beeping.NPcoNP.Grammar284LeafPrefix
