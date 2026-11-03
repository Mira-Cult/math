import Shared.PNP.Record285.GrammarGraph

/-! Every producer grammar node points strictly backward, giving a finite
structural bound on reaching a leaf for any input-bit stream. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar

def earlier (n : Nat) : Edge → Bool
  | .node j => decide (j < n)
  | _ => true

def earlierNodeAt (xs : Array Node) (n : Nat) : Bool :=
  match xs[n]? with
  | none => false
  | some p => earlier n p.1 && earlier n p.2

def earlierNode (n : Nat) : Bool := earlierNodeAt fastNodes n

theorem all_earlier : (List.range 163).all earlierNode = true := by decide

attribute [local irreducible] fastNodes

theorem checked_earlier (n : Nat) (hn : n < 163) : earlierNode n = true :=
  List.all_eq_true.mp all_earlier n (List.mem_range.mpr hn)

theorem earlier_of_lookup (xs : Array Node) (n : Nat) (b : Bool) (e : Edge)
    (h : (xs[n]?).map (fun p => if b then p.2 else p.1) = some e)
    (hc : earlierNodeAt xs n = true) : earlier n e = true := by
  cases hn : xs[n]? with
  | none => simp [hn] at h
  | some pair =>
    simp only [earlierNodeAt,hn,Bool.and_eq_true] at hc
    cases b with
    | false =>
      simp only [hn,Option.map_some,Bool.false_eq_true,if_false,Option.some.injEq] at h
      subst e
      exact hc.1
    | true =>
      simp only [hn,Option.map_some,if_true,Option.some.injEq] at h
      subst e
      exact hc.2

theorem node_edge_decreases (n : Nat) (b : Bool) (j : Nat) (hn : n < 163)
    (h : nodeEdge n b = some (.node j)) : j < n := by
  have hh : (fastNodes[n]?).map (fun p => if b then p.2 else p.1) = some (.node j) := by
    simpa only [nodeEdge,nodes_fast] using h
  have he := earlier_of_lookup fastNodes n b (.node j) hh (checked_earlier n hn)
  simpa only [earlier,decide_eq_true_eq] using he

theorem array_has_entry {α : Type} (xs : Array α) (n : Nat) (h : n < xs.size) :
    ∃ v, xs[n]? = some v := by
  exact ⟨xs[n],Array.getElem?_eq_getElem h⟩

theorem node_edge_exists (n : Nat) (b : Bool) (hn : n < 163) :
    ∃ e, nodeEdge n b = some e := by
  have hb : n < fastNodes.size := by simpa only [nodes_size] using hn
  obtain ⟨p,hp⟩ := array_has_entry fastNodes n hb
  refine ⟨if b then p.2 else p.1,?_⟩
  simp only [nodeEdge,nodes_fast,hp,Option.map_some]

/-- Seek a leaf by consuming one input bit at each node. No machine time bound
is inferred here; this is the finite control-grammar bound. -/
def descend : Nat → Nat → (Nat → Bool) → Nat → Option (Edge × Nat)
  | 0,_,_,_ => none
  | fuel+1,n,input,pos =>
    match nodeEdge n (input pos) with
    | none => none
    | some (.node j) => descend fuel j input (pos+1)
    | some e => some (e,pos+1)

theorem descend_terminates (fuel n : Nat) (input : Nat → Bool) (pos : Nat)
    (hn : n < 163) (hf : n < fuel) :
    ∃ e endPos, descend fuel n input pos = some (e,endPos) := by
  induction fuel generalizing n pos with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨e,he⟩ := node_edge_exists n (input pos) hn
    cases e with
    | node j =>
      have hj := node_edge_decreases n (input pos) j hn he
      have hsub : j < fuel := by omega
      have hjbound : j < 163 := by omega
      obtain ⟨result,endPos,hres⟩ := ih j (pos+1) hjbound hsub
      exact ⟨result,endPos,by simpa only [descend,he] using hres⟩
    | inc j => exact ⟨.inc j,pos+1,by simp [descend,he]⟩
    | dec j => exact ⟨.dec j,pos+1,by simp [descend,he]⟩
    | half j => exact ⟨.half j,pos+1,by simp [descend,he]⟩
    | beep => exact ⟨.beep,pos+1,by simp [descend,he]⟩
    | brk j => exact ⟨.brk j,pos+1,by simp [descend,he]⟩
    | cont j => exact ⟨.cont j,pos+1,by simp [descend,he]⟩

def isLeaf : Edge → Bool
  | .node _ => false
  | _ => true

/-- Any successful descent consumed a positive number of bits, consumed at
most its fuel, and returned an operation rather than another grammar node. -/
theorem descend_bound (fuel n : Nat) (input : Nat → Bool) (pos : Nat) (e : Edge) (endPos : Nat)
    (h : descend fuel n input pos = some (e,endPos)) :
    pos < endPos ∧ endPos ≤ pos+fuel ∧ isLeaf e = true := by
  induction fuel generalizing n pos with
  | zero => simp [descend] at h
  | succ fuel ih =>
    cases he : nodeEdge n (input pos) with
    | none => simp [descend,he] at h
    | some found =>
      cases found with
      | node j =>
        have h' : descend fuel j input (pos+1) = some (e,endPos) := by
          simpa only [descend,he] using h
        have hb := ih j (pos+1) h'
        exact ⟨by omega,by omega,hb.2.2⟩
      | inc j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨by omega,by omega,rfl⟩
      | dec j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨by omega,by omega,rfl⟩
      | half j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨by omega,by omega,rfl⟩
      | beep =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨by omega,by omega,rfl⟩
      | brk j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨by omega,by omega,rfl⟩
      | cont j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨by omega,by omega,rfl⟩

/-- Bits consumed by a grammar descent, in dispatcher order. -/
def window (input : Nat → Bool) (pos : Nat) : Nat → List Bool
  | 0 => []
  | n+1 => input pos :: window input (pos+1) n

theorem descend_trace (fuel n : Nat) (input : Nat → Bool) (pos : Nat) (e : Edge) (endPos : Nat)
    (h : descend fuel n input pos = some (e,endPos)) :
    ∃ len, 0 < len ∧ len ≤ fuel ∧ endPos = pos+len ∧
      walk n (window input pos len) = some e := by
  induction fuel generalizing n pos with
  | zero => simp [descend] at h
  | succ fuel ih =>
    cases he : nodeEdge n (input pos) with
    | none => simp [descend,he] at h
    | some found =>
      cases found with
      | node j =>
        have h' : descend fuel j input (pos+1) = some (e,endPos) := by
          simpa only [descend,he] using h
        obtain ⟨len,hpos,hbound,hend,hwalk⟩ := ih j (pos+1) h'
        refine ⟨len+1,by omega,by omega,by omega,?_⟩
        simpa only [window,walk,he] using hwalk
      | inc j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨1,by omega,by omega,by omega,by simp [window,walk,he]⟩
      | dec j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨1,by omega,by omega,by omega,by simp [window,walk,he]⟩
      | half j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨1,by omega,by omega,by omega,by simp [window,walk,he]⟩
      | beep =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨1,by omega,by omega,by omega,by simp [window,walk,he]⟩
      | brk j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨1,by omega,by omega,by omega,by simp [window,walk,he]⟩
      | cont j =>
        simp only [descend,he,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨1,by omega,by omega,by omega,by simp [window,walk,he]⟩

/-- Every bit stream reaches some grammar leaf within at most 163 node
lookups starting from the producer's root. -/
theorem root_descend_terminates (input : Nat → Bool) (pos : Nat) :
    ∃ e endPos, descend 163 162 input pos = some (e,endPos) ∧
      pos < endPos ∧ endPos ≤ pos+163 ∧ isLeaf e = true := by
  obtain ⟨e,endPos,h⟩ := descend_terminates 163 162 input pos (by decide) (by decide)
  exact ⟨e,endPos,h,descend_bound 163 162 input pos e endPos h⟩

/-- Any bit stream has a finite grammar path from the producer root to an
operation leaf, with an explicit bound of 163 consumed bits. -/
theorem root_walk_terminates (input : Nat → Bool) (pos : Nat) :
    ∃ e len, 0 < len ∧ len ≤ 163 ∧ isLeaf e = true ∧
      walk 162 (window input pos len) = some e := by
  obtain ⟨e,endPos,h,_,_,hleaf⟩ := root_descend_terminates input pos
  obtain ⟨len,hpos,hbound,_,hwalk⟩ := descend_trace 163 162 input pos e endPos h
  exact ⟨e,len,hpos,hbound,hleaf,hwalk⟩

end Shared.PNP.Record285.Grammar
