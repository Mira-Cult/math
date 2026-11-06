import Shared.Beeping.NPcoNP.Grammar284ParseSource
/-! Kernel-checked path bounds and finite descent for the parsed 284 producer
grammar. These concern its raw tree; physical preparation and the dispatcher
are separate refinement obligations. -/
namespace Shared.Beeping.NPcoNP.Grammar284Depth

open Shared.Beeping.NPcoNP.Grammar284
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

abbrev Metric := Nat × Nat

def leafMetric (ms : Array Metric) : Leaf → Option Metric
  | .op _ => some (0,0)
  | .node i => ms[i]?

def extendMetrics (ms : Array Metric) (pair : Leaf × Leaf) : Option (Array Metric) := do
  let l ← leafMetric ms pair.1
  let r ← leafMetric ms pair.2
  pure (ms.push (1+max l.1 r.1, max (1+l.2) r.2))

def calculateMetrics (g : Grammar) : Option (Array Metric) :=
  g.nodes.foldl (fun acc pair => acc.bind (fun ms => extendMetrics ms pair)) (some #[])


def rowValid (g : Grammar) (ms : Array Metric) (i : Fin g.nodes.size) : Bool :=
  match ms[i.val]?, leafMetric ms (g.nodes[i.val]'i.isLt).1, leafMetric ms (g.nodes[i.val]'i.isLt).2 with
  | some p, some l, some r =>
    decide (p.1 = 1+max l.1 r.1) && decide (p.2 = max (1+l.2) r.2)
  | _, _, _ => false

def validMetrics (g : Grammar) (ms : Array Metric) : Bool :=
  (List.finRange g.nodes.size).all (rowValid g ms)

def producerMetrics : Array Metric := (calculateMetrics producerGrammar).getD #[]

inductive Walk (g : Grammar) : Leaf → List Bool → Leaf → Prop
  | stop (leaf : Leaf) : Walk g leaf [] leaf
  | left (i : Fin g.nodes.size) (path : List Bool) (last : Leaf) :
      Walk g (g.nodes[i.val]'i.isLt).1 path last → Walk g (.node i.val) (false::path) last
  | right (i : Fin g.nodes.size) (path : List Bool) (last : Leaf) :
      Walk g (g.nodes[i.val]'i.isLt).2 path last → Walk g (.node i.val) (true::path) last

theorem row_of_valid (g : Grammar) (ms : Array Metric) (h : validMetrics g ms = true)
    (i : Fin g.nodes.size) : rowValid g ms i = true := by
  apply (List.all_eq_true.mp h)
  simp

theorem path_bounded (g : Grammar) (ms : Array Metric) (hv : validMetrics g ms = true)
    {leaf : Leaf} {path : List Bool} {last : Leaf} (hp : Walk g leaf path last)
    (m : Metric) (hm : leafMetric ms leaf = some m) :
    path.length ≤ m.1 ∧ path.count false ≤ m.2 := by
  induction hp generalizing m with
  | stop leaf =>
    simp
  | left i path last hp ih =>
    have hr := row_of_valid g ms hv i
    have hm' : ms[i.val]? = some m := by simpa [leafMetric] using hm
    cases hl : leafMetric ms (g.nodes[i.val]'i.isLt).1 with
    | none => simp [rowValid,hm',hl] at hr
    | some l =>
      cases hrm : leafMetric ms (g.nodes[i.val]'i.isLt).2 with
      | none => simp [rowValid,hm',hl,hrm] at hr
      | some r =>
        simp [rowValid,hm',hl,hrm] at hr
        obtain ⟨h1,h2⟩ := ih l hl
        simp only [List.length_cons, List.count_cons_self]
        omega
  | right i path last hp ih =>
    have hr := row_of_valid g ms hv i
    have hm' : ms[i.val]? = some m := by simpa [leafMetric] using hm
    cases hl : leafMetric ms (g.nodes[i.val]'i.isLt).1 with
    | none => simp [rowValid,hm',hl] at hr
    | some l =>
      cases hrm : leafMetric ms (g.nodes[i.val]'i.isLt).2 with
      | none => simp [rowValid,hm',hl,hrm] at hr
      | some r =>
        simp [rowValid,hm',hl,hrm] at hr
        obtain ⟨h1,h2⟩ := ih r hrm
        simp only [List.length_cons, List.count_cons_of_ne (by decide : true ≠ false)]
        omega

set_option maxRecDepth 131072 in
set_option maxHeartbeats 30000000 in
theorem producer_valid : validMetrics producerGrammar producerMetrics = true := by decide

theorem producer_size : producerMetrics.size = producerGrammar.nodes.size := by decide

theorem producer_root_metric : leafMetric producerMetrics (.node producerGrammar.root) = some (52,10) := by decide

theorem producer_path_bound (path : List Bool) (last : Leaf)
    (hp : Walk producerGrammar (.node producerGrammar.root) path last) :
    path.length ≤ 52 ∧ path.count false ≤ 10 := by
  exact path_bounded producerGrammar producerMetrics producer_valid hp (52,10) producer_root_metric

#print axioms producer_path_bound

theorem exists_leaf_of_budget (g : Grammar) (ms : Array Metric)
    (hv : validMetrics g ms = true) (hs : ms.size = g.nodes.size) :
    ∀ n (leaf : Leaf) (m : Metric), m.1<n → leafMetric ms leaf = some m →
      ∃ path name, Walk g leaf path (.op name) := by
  intro n
  induction n with
  | zero =>
    intro leaf m hlt hm
    omega
  | succ n ih =>
    intro leaf m hlt hm
    cases leaf with
    | op name => exact ⟨[],name,Walk.stop _⟩
    | node idx =>
      have hm' : ms[idx]? = some m := by simpa [leafMetric] using hm
      have hi : idx < g.nodes.size := by
        have h := (Array.getElem?_eq_some_iff.mp hm').choose
        simpa [hs] using h
      let i : Fin g.nodes.size := ⟨idx, hi⟩
      have hr := row_of_valid g ms hv i
      cases hl : leafMetric ms (g.nodes[i.val]'i.isLt).1 with
      | none => simp [rowValid,hm',hl,i] at hr
      | some l =>
        cases hrm : leafMetric ms (g.nodes[i.val]'i.isLt).2 with
        | none => simp [rowValid,hm',hl,hrm,i] at hr
        | some r =>
          simp [rowValid,hm',hl,hrm,i] at hr
          have hltl : l.1<n := by omega
          obtain ⟨path,name,hpath⟩ := ih _ l hltl hl
          exact ⟨false::path,name,Walk.left i path (.op name) hpath⟩

theorem producer_path_to_leaf :
    ∃ path name, Walk producerGrammar (.node producerGrammar.root) path (.op name) := by
  exact exists_leaf_of_budget producerGrammar producerMetrics producer_valid producer_size 53 _ (52,10)
    (by decide) producer_root_metric

#print axioms producer_path_to_leaf

theorem node_children (g : Grammar) (ms : Array Metric) (hv : validMetrics g ms = true)
    (i : Fin g.nodes.size) (m : Metric) (hm : ms[i.val]? = some m) :
    ∃ l r, leafMetric ms (g.nodes[i.val]'i.isLt).1 = some l ∧
      leafMetric ms (g.nodes[i.val]'i.isLt).2 = some r ∧
      m.1 = 1+max l.1 r.1 ∧ m.2 = max (1+l.2) r.2 := by
  have hr := row_of_valid g ms hv i
  cases hl : leafMetric ms (g.nodes[i.val]'i.isLt).1 with
  | none => simp [rowValid,hm,hl] at hr
  | some l =>
    cases hright : leafMetric ms (g.nodes[i.val]'i.isLt).2 with
    | none => simp [rowValid,hm,hl,hright] at hr
    | some r =>
      simp [rowValid,hm,hl,hright] at hr
      exact ⟨l,r,rfl,rfl,hr.1,hr.2⟩

theorem walk_end_metric (g : Grammar) (ms : Array Metric) (hv : validMetrics g ms = true)
    {leaf last : Leaf} {path : List Bool} (hp : Walk g leaf path last)
    (m : Metric) (hm : leafMetric ms leaf = some m) :
    ∃ final, leafMetric ms last = some final := by
  induction hp generalizing m with
  | stop leaf => exact ⟨m,hm⟩
  | left i path last hp ih =>
    have hm' : ms[i.val]?=some m := by simpa [leafMetric] using hm
    obtain ⟨l,r,hl,hr,hheight,hzero⟩ := node_children g ms hv i m hm'
    exact ih l hl
  | right i path last hp ih =>
    have hm' : ms[i.val]?=some m := by simpa [leafMetric] using hm
    obtain ⟨l,r,hl,hr,hheight,hzero⟩ := node_children g ms hv i m hm'
    exact ih r hr

theorem walk_append (g : Grammar) {a b c : Leaf} {p q : List Bool}
    (hp : Walk g a p b) (hq : Walk g b q c) : Walk g a (p++q) c := by
  induction hp with
  | stop => simpa using hq
  | left i p b hp ih =>
    simp only [List.cons_append]
    exact Walk.left i _ _ (ih hq)
  | right i p b hp ih =>
    simp only [List.cons_append]
    exact Walk.right i _ _ (ih hq)

theorem producer_prefix_finishes (path : List Bool) (last : Leaf)
    (hp : Walk producerGrammar (.node producerGrammar.root) path last) :
    ∃ suffix name, Walk producerGrammar last suffix (.op name) ∧
      path.length + suffix.length ≤ 52 ∧
      path.count false + suffix.count false ≤ 10 := by
  obtain ⟨m,hm⟩ := walk_end_metric producerGrammar producerMetrics producer_valid hp (52,10) producer_root_metric
  obtain ⟨suffix,name,hfinish⟩ := exists_leaf_of_budget producerGrammar producerMetrics
    producer_valid producer_size (m.1+1) last m (by omega) hm
  have hall := producer_path_bound (path++suffix) (.op name) (walk_append producerGrammar hp hfinish)
  simp only [List.length_append,List.count_append] at hall
  exact ⟨suffix,name,hfinish,hall.1,hall.2⟩

#print axioms producer_prefix_finishes

def follow (g : Grammar) : Leaf → List Bool → Option Leaf
  | leaf, [] => some leaf
  | .op _, _::_ => none
  | .node i, b::path => do
      let pair ← g.nodes[i]?
      follow g (if b then pair.2 else pair.1) path

theorem follow_sound (g : Grammar) (path : List Bool) (leaf last : Leaf)
    (h : follow g leaf path = some last) : Walk g leaf path last := by
  induction path generalizing leaf with
  | nil =>
    simp [follow] at h
    subst last
    exact Walk.stop leaf
  | cons b path ih =>
    cases leaf with
    | op name => simp [follow] at h
    | node idx =>
      cases he : g.nodes[idx]? with
      | none => simp [follow,he] at h
      | some pair =>
        obtain ⟨hi, hget⟩ := Array.getElem?_eq_some_iff.mp he
        let i : Fin g.nodes.size := ⟨idx,hi⟩
        cases b with
        | false =>
          have hh : follow g pair.1 path=some last := by simpa [follow,he] using h
          have ht : Walk g (g.nodes[i.val]'i.isLt).1 path last := by
            change Walk g (g.nodes[idx]'hi).1 path last
            rw [hget]
            exact ih pair.1 hh
          exact Walk.left i path last ht
        | true =>
          have hh : follow g pair.2 path=some last := by simpa [follow,he] using h
          have ht : Walk g (g.nodes[i.val]'i.isLt).2 path last := by
            change Walk g (g.nodes[idx]'hi).2 path last
            rw [hget]
            exact ih pair.2 hh
          exact Walk.right i path last ht

def heightWitness : List Bool :=
  "1100111111111111111111010111111101011111111111011010".toList.map (fun c => c == '1')
def leftWitness : List Bool :=
  "11001111111111010111110101100100".toList.map (fun c => c == '1')

theorem height_witness :
    Walk producerGrammar (.node producerGrammar.root) heightWitness (.op "3.$coalesced.8.inc") ∧
      heightWitness.length=52 := by
  constructor
  · apply follow_sound
    decide
  · decide

theorem left_witness :
    Walk producerGrammar (.node producerGrammar.root) leftWitness (.op "3.$coalesced.10.inc") ∧
      leftWitness.count false=10 := by
  constructor
  · apply follow_sound
    decide
  · decide

#print axioms height_witness
#print axioms left_witness

/-- The parser-bound embedded source has the same universal raw tree bound. -/
theorem parsed_source_path_bound (g : Grammar)
    (hparse : Shared.Beeping.NPcoNP.Grammar284ParseSource.parse
      Shared.Beeping.NPcoNP.Grammar284.SourceChars.source.toList = some g)
    (path : List Bool) (last : Leaf)
    (hp : Walk g (.node g.root) path last) :
    path.length ≤ 52 ∧ path.count false ≤ 10 := by
  rw [Shared.Beeping.NPcoNP.Grammar284ParseSource.parse_embedded_source] at hparse
  cases hparse
  exact producer_path_bound path last hp

#print axioms parsed_source_path_bound

/-- A single valid grammar-child traversal, forgetting the direction bit. -/
def Edge (g : Grammar) (source target : Leaf) : Prop :=
  ∃ i : Fin g.nodes.size, source=.node i.val ∧
    (target=(g.nodes[i.val]'i.isLt).1 ∨ target=(g.nodes[i.val]'i.isLt).2)

theorem edge_walk (g : Grammar) {source target : Leaf} (h : Edge g source target) :
    ∃ b, Walk g source [b] target := by
  obtain ⟨i,he,hleft | hright⟩ := h
  · subst source
    subst target
    exact ⟨false,Walk.left i [] _ (Walk.stop _)⟩
  · subst source
    subst target
    exact ⟨true,Walk.right i [] _ (Walk.stop _)⟩

theorem chain_walk (g : Grammar) (f : Nat → Leaf)
    (hstep : ∀ n, Edge g (f n) (f (n+1))) :
    ∀ n, ∃ path, path.length=n ∧ Walk g (f 0) path (f n) := by
  intro n
  induction n with
  | zero => exact ⟨[],rfl,Walk.stop _⟩
  | succ n ih =>
    obtain ⟨path,hlen,hpath⟩ := ih
    obtain ⟨b,hnext⟩ := edge_walk g (hstep n)
    refine ⟨path++[b],?_,walk_append g hpath hnext⟩
    simp [hlen]

/-- No infinite sequence can keep descending from the actual grammar root. -/
theorem producer_no_infinite_descent (f : Nat → Leaf)
    (hstart : f 0 = .node producerGrammar.root)
    (hstep : ∀ n, Edge producerGrammar (f n) (f (n+1))) : False := by
  obtain ⟨path,hlen,hpath⟩ := chain_walk producerGrammar f hstep 53
  rw [hstart] at hpath
  have hb := (producer_path_bound path (f 53) hpath).1
  omega

#print axioms producer_no_infinite_descent

/-- The actual graph expander seeds the raw grammar path with `110`. -/
def preparedPrefix : List Bool := [true,true,false]

def PreparedWalk (path : List Bool) (last : Leaf) : Prop :=
  ∃ raw, path=preparedPrefix++raw ∧ Walk producerGrammar (.node producerGrammar.root) raw last

/-- This bound includes the expander's three-bit prefix and its one zero.
It does not yet prove that a physical tape encodes this path. -/
theorem prepared_path_bound (path : List Bool) (last : Leaf)
    (hp : PreparedWalk path last) :
    path.length≤55 ∧ path.count false≤11 := by
  obtain ⟨raw,rfl,hw⟩ := hp
  have hb := producer_path_bound raw last hw
  simp [preparedPrefix,List.count_append] at ⊢
  omega

/-- The extra two counted slots turn the prepared zero bound into 13.
The connection of these slots to literal dispatcher rows remains separate. -/
theorem prepared_counted_budget (path : List Bool) (last : Leaf)
    (hp : PreparedWalk path last) : path.count false+2≤13 := by
  have h := (prepared_path_bound path last hp).2
  omega

theorem prepared_height_witness :
    PreparedWalk (preparedPrefix++heightWitness) (.op "3.$coalesced.8.inc") ∧
      (preparedPrefix++heightWitness).length=55 := by
  refine ⟨⟨heightWitness,rfl,height_witness.1⟩,?_⟩
  simp [preparedPrefix,height_witness.2]

theorem prepared_zero_witness :
    PreparedWalk (preparedPrefix++leftWitness) (.op "3.$coalesced.10.inc") ∧
      (preparedPrefix++leftWitness).count false=11 := by
  refine ⟨⟨leftWitness,rfl,left_witness.1⟩,?_⟩
  simp [preparedPrefix,left_witness.2]

#print axioms prepared_path_bound
#print axioms prepared_counted_budget
#print axioms prepared_height_witness
#print axioms prepared_zero_witness

end Shared.Beeping.NPcoNP.Grammar284Depth
