import Shared.Beeping.NPcoNP.Grammar284ExpansionPaths

/-! Completeness of successful finite grammar expansion for operation walks. -/
namespace Shared.Beeping.NPcoNP.Grammar284ExpansionComplete
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- A successful expansion retains every leaf already in its accumulator. -/
theorem expand_preserves (nodes : Array (Leaf × Leaf)) (fuel : Nat)
    (leaf : Leaf) (path : Path) (ancestors : List Nat) (acc out : Expansion)
    (success : expand nodes fuel leaf path ancestors acc = some out) :
    ∀ entry, entry ∈ acc.leaves.toList → entry ∈ out.leaves.toList := by
  induction fuel generalizing leaf path ancestors acc out with
  | zero => simp [expand] at success
  | succ fuel ih =>
    cases leaf with
    | op name =>
      simp [expand] at success
      subst out
      intro entry member
      simpa only [Array.toList_push, List.mem_append, List.mem_singleton] using Or.inl member
    | node i =>
      cases hc : ancestors.contains i with
      | true =>
        have hi : i ∈ ancestors := by simpa using hc
        simp [expand,hi] at success
      | false =>
        have hi : i ∉ ancestors := by simpa using hc
        cases hn : nodes[i]? with
        | none => simp [expand,hi,hn] at success
        | some pair =>
          let acc' : Expansion := { acc with starts := acc.starts.push (path,acc.leaves.size) }
          cases hl : expand nodes fuel pair.1 (path ++ [false]) (i::ancestors) acc' with
          | none => simp [expand,hi,hn,acc',hl] at success
          | some middle =>
            have hr : expand nodes fuel pair.2 (path ++ [true]) (i::ancestors) middle = some out := by
              simpa [expand,hi,hn,acc',hl] using success
            intro entry member
            have hm : entry ∈ middle.leaves.toList := ih pair.1 _ _ acc' middle hl entry (by simpa [acc'] using member)
            exact ih pair.2 _ _ middle out hr entry hm

/-- If an expansion succeeds, each operation reached by a grammar walk is
present in its resulting leaf list, with its entire accumulated path. -/
theorem expand_contains_walk (g : Grammar) (fuel : Nat) (leaf : Leaf)
    (base suffix : Path) (name : String) (ancestors : List Nat) (acc out : Expansion)
    (success : expand g.nodes fuel leaf base ancestors acc = some out)
    (walk : Walk g leaf suffix (.op name)) :
    (base++suffix,name) ∈ out.leaves.toList := by
  induction fuel generalizing leaf base suffix ancestors acc out with
  | zero => simp [expand] at success
  | succ fuel ih =>
    cases leaf with
    | op n =>
      cases walk with
      | stop =>
        simp [expand] at success
        subst out
        simp
    | node i =>
      cases hc : ancestors.contains i with
      | true =>
        have hi : i ∈ ancestors := by simpa using hc
        simp [expand,hi] at success
      | false =>
        have hi : i ∉ ancestors := by simpa using hc
        cases hn : g.nodes[i]? with
        | none => simp [expand,hi,hn] at success
        | some pair =>
          let acc' : Expansion := { acc with starts := acc.starts.push (base,acc.leaves.size) }
          cases hl : expand g.nodes fuel pair.1 (base ++ [false]) (i::ancestors) acc' with
          | none => simp [expand,hi,hn,acc',hl] at success
          | some middle =>
            have hr : expand g.nodes fuel pair.2 (base ++ [true]) (i::ancestors) middle = some out := by
              simpa [expand,hi,hn,acc',hl] using success
            cases walk with
            | left j rest last sub =>
              have hp : g.nodes[j.val]'j.isLt=pair := by
                exact (Array.getElem?_eq_some_iff.mp hn).2
              have hw : Walk g pair.1 rest (.op name) := by simpa [hp] using sub
              have hm := ih pair.1 (base++[false]) rest (j.val::ancestors) acc' middle hl hw
              have result := expand_preserves g.nodes fuel pair.2 (base++[true]) (j.val::ancestors) middle out hr _ hm
              simpa [List.append_assoc] using result
            | right j rest last sub =>
              have hp : g.nodes[j.val]'j.isLt=pair := by
                exact (Array.getElem?_eq_some_iff.mp hn).2
              have hw : Walk g pair.2 rest (.op name) := by simpa [hp] using sub
              have hm := ih pair.2 (base++[true]) rest (j.val::ancestors) middle out hr hw
              simpa [List.append_assoc] using hm

/-- The certified expansion contains exactly the completed prepared walks. -/
theorem expanded_leaf_iff (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e) (path : Path) (name : String) :
    (path,name) ∈ e.leaves.toList ↔ PreparedWalk path (.op name) := by
  constructor
  · intro member
    exact Grammar284ExpansionPaths.expanded_leaf_follows e expanded (path,name) member
  · intro walk
    obtain ⟨raw,he,hw⟩ := walk
    rw [he]
    exact expand_contains_walk producerGrammar 53 (.node producerGrammar.root)
      [true,true,false] raw name [] {} e expanded hw

#print axioms expand_preserves
#print axioms expand_contains_walk
#print axioms expanded_leaf_iff
end Shared.Beeping.NPcoNP.Grammar284ExpansionComplete
