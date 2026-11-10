import PASoundness.PAtoCompactSuccTermTotality

/-! Finite K witness introduction for binary term graphs. -/
namespace PASoundness.PAtoCompactTermZeroGuarded

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def binaryTerm {α : Type} (add : Bool) (t u : Peano.language.Term α) : Peano.language.Term α :=
  if add then .func .add ![t, u] else .func .mul ![t, u]

def binaryRel (add : Bool) (b x y out : Nat) : Formula :=
  if add then addAt b x y out else mulAt b x y out

/-- Actual K introduction of a binary graph, from its two concrete child
graphs and the allocated arithmetic relation. This does not prove that the
premises are inhabited. -/
def binary_from_witness {α : Type} (v : α → Nat) (add : Bool)
    (t u : Peano.language.Term α) (b out : Nat) :
    KDerivation (imp (domainAt b out).encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v u (b+1) (b+64+termCost t)).encode
          (imp (binaryRel add b b (b+1) out).encode
            (termGraph v (binaryTerm add t u) out b).encode)))) := by
  let T := termGraph v t b (b+64)
  let U := termGraph v u (b+1) (b+64+termCost t)
  let R := binaryRel add b b (b+1) out
  let inner := andF T (andF U R)
  let outer := Formula.ex (b+1) inner
  have hr (k : Nat) (hk : k < b+2) : k ∉ R.binders := by
    intro h
    cases add <;> simp only [R, binaryRel, Bool.false_eq_true, ↓reduceIte] at h
    · have hh := mulAt_private b b (b+1) out k h; omega
    · have hh := addAt_private b b (b+1) out k h; omega
  have hi : b+1 ∉ inner.binders := by
    simp only [inner, andF_binders, Finset.mem_union, not_or]
    exact ⟨termGraph_below_not_binder v t b (b+64) (b+1) (by omega),
      termGraph_below_not_binder v u (b+1) (b+64+termCost t) (b+1) (by omega),
      hr (b+1) (by omega)⟩
  have ho : b ∉ outer.binders := by
    simp only [outer, Formula.binders, Finset.mem_insert, not_or]
    refine ⟨by omega, ?_⟩
    simp only [inner, andF_binders, Finset.mem_union, not_or]
    exact ⟨termGraph_below_not_binder v t b (b+64) b (by omega),
      termGraph_below_not_binder v u (b+1) (b+64+termCost t) b (by omega),
      hr b (by omega)⟩
  have hI := existsIntroduce (b+1) inner hi
  have hO := existsIntroduce b outer ho
  apply Context.closeEmpty
  repeat apply Context.deduction
  let Γ := [R.encode, U.encode, T.encode, (domainAt b out).encode]
  have hR : Context Γ R.encode := .hypothesis (by simp [Γ])
  have hU : Context Γ U.encode := .hypothesis (by simp [Γ])
  have hT : Context Γ T.encode := .hypothesis (by simp [Γ])
  have hD : Context Γ (domainAt b out).encode := .hypothesis (by simp [Γ])
  have hmatrix : Context Γ inner.encode := by
    have h := Context.conjunctionIntro hT (Context.conjunctionIntro hU hR)
    simpa [inner, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
  have he : Context Γ (existsCode b outer.encode) := .mp (.mp hmatrix (.closed hI)) (.closed hO)
  have h := Context.conjunctionIntro hD he
  cases add <;> simpa [Γ, binaryTerm, binaryRel, termGraph, T, U, R, inner, outer,
    andF, CompactNamed.Formula.not, Formula.encode, both, neg, existsCode] using h

/-- Compose explicit child and operation existence proofs. Vacuity inputs
are finite K proofs and keep all witness-freshness obligations visible. -/
def binary_total_from_children {α : Type} (v : α → Nat) (add : Bool)
    (t u : Peano.language.Term α) (b out : Nat) (g : Formula) (hout : out < b)
    (child1 : KDerivation (imp g.encode
      (existsCode b (termGraph v t b (b+64)).encode)))
    (child2 : KDerivation (imp g.encode
      (existsCode (b+1) (termGraph v u (b+1) (b+64+termCost t)).encode)))
    (operation : KDerivation (imp (termGraph v t b (b+64)).encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (existsCode out (andF (domainAt b out) (binaryRel add b b (b+1) out)).encode))))
    (vgb : KDerivation (imp g.encode (allCode b g.encode)))
    (vgb1 : KDerivation (imp g.encode (allCode (b+1) g.encode)))
    (vgo : KDerivation (imp g.encode (allCode out g.encode)))
    (vtb1 : KDerivation (imp (termGraph v t b (b+64)).encode
      (allCode (b+1) (termGraph v t b (b+64)).encode)))
    (vto : KDerivation (imp (termGraph v t b (b+64)).encode
      (allCode out (termGraph v t b (b+64)).encode)))
    (vuo : KDerivation (imp (termGraph v u (b+1) (b+64+termCost t)).encode
      (allCode out (termGraph v u (b+1) (b+64+termCost t)).encode)))
    (vg1 : KDerivation (imp (existsCode out (termGraph v (binaryTerm add t u) out b).encode)
      (allCode b (existsCode out (termGraph v (binaryTerm add t u) out b).encode))))
    (vg2 : KDerivation (imp (existsCode out (termGraph v (binaryTerm add t u) out b).encode)
      (allCode (b+1) (existsCode out (termGraph v (binaryTerm add t u) out b).encode))))
    (vgo' : KDerivation (imp (existsCode out (termGraph v (binaryTerm add t u) out b).encode)
      (allCode out (existsCode out (termGraph v (binaryTerm add t u) out b).encode)))) :
    KDerivation (imp g.encode (existsCode out (termGraph v (binaryTerm add t u) out b).encode)) := by
  let T := (termGraph v t b (b+64)).encode
  let U := (termGraph v u (b+1) (b+64+termCost t)).encode
  let N := (andF (domainAt b out) (binaryRel add b b (b+1) out)).encode
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [g.encode]
  have h1 : Context Γ (existsCode b T) := .mp (Context.head [] _) (.closed child1)
  apply Context.existsElim vg1 _ h1
  apply generalizeOne b vgb
  apply Context.deduction
  let Δ := [T, g.encode]
  have hg : Context Δ g.encode := .hypothesis (by simp [Δ])
  have h2 : Context Δ (existsCode (b+1) U) := .mp hg (.closed child2)
  apply Context.existsElim vg2 _ h2
  apply Context.generalize (b+1)
  · intro q hq
    change q ∈ [T, g.encode] at hq
    by_cases he : q = T
    · subst q; exact vtb1
    · have he' : q = g.encode := by simpa [he] using hq
      subst q; exact vgb1
  apply Context.deduction
  let Θ := [U, T, g.encode]
  have hu : Context Θ U := .hypothesis (by simp [Θ])
  have ht : Context Θ T := .hypothesis (by simp [Θ])
  have hn : Context Θ (existsCode out N) := .mp hu (.mp ht (.closed operation))
  apply Context.existsElim vgo' _ hn
  apply Context.generalize out
  · intro q hq
    change q ∈ [U, T, g.encode] at hq
    by_cases he : q = U
    · subst q; exact vuo
    · by_cases he' : q = T
      · subst q; exact vto
      · have he'' : q = g.encode := by simpa [he, he'] using hq
        subst q; exact vgo
  apply Context.deduction
  let Ξ := [N, U, T, g.encode]
  have hn' : Context Ξ (both (domainAt b out).encode (binaryRel add b b (b+1) out).encode) := by
    have h : Context Ξ N := .hypothesis (by simp [Ξ])
    simpa [N, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
  have hu' : Context Ξ U := .hypothesis (by simp [Ξ])
  have ht' : Context Ξ T := .hypothesis (by simp [Ξ])
  have hgraph : Context Ξ (termGraph v (binaryTerm add t u) out b).encode :=
    .mp (Context.conjunctionRight hn') (.mp hu' (.mp ht'
      (.mp (Context.conjunctionLeft hn') (.closed (binary_from_witness v add t u b out)))))
  have hi := existsIntroduce out (termGraph v (binaryTerm add t u) out b)
    (termGraph_below_not_binder v _ out b out hout)
  exact .mp hgraph (.closed hi)

end PASoundness.PAtoCompactTermZeroGuarded

#print axioms PASoundness.PAtoCompactTermZeroGuarded.binary_from_witness
#print axioms PASoundness.PAtoCompactTermZeroGuarded.binary_total_from_children
