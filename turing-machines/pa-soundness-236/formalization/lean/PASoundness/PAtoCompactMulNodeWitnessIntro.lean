import PASoundness.PAtoCompactMulTermTransportWitness
import PASoundness.PAtoCompactTermZeroGuarded
import PASoundness.PAtoCompactAddTermBody

/-! Capture-safe construction of a multiplication term graph from two
explicit, possibly aliased child witnesses. This constructs no multiplication
output and establishes no arithmetic axiom. -/
namespace PASoundness.PAtoCompactMulNodeWitnessIntro

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactTermGraphReplace PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactScopedAlphaInvariant PASoundness.PAtoCompactVariableTermTotality
open PASoundness.PAtoCompactMulTermTransportWitness PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactFreeNames

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The two child graphs and product relation with the node's private names
allocated above `base`. -/
def body {α : Type} (v : α → Nat) (t u : Peano.language.Term α)
    (x y base out : Nat) : Formula :=
  andF (termGraph v t x (base+64))
    (andF (termGraph v u y (base+64+termCost t)) (mulAt base x y out))

theorem below_not_binder {α : Type} (v : α → Nat) (t u : Peano.language.Term α)
    (x y base out k : Nat) (hk : k < base+2) : k ∉ (body v t u x y base out).binders := by
  intro h
  simp only [body, andF_binders, Finset.mem_union] at h
  rcases h with ht | hu | hm
  · have hb := termGraph_binder_range v t x (base+64) k ht
    omega
  · have hb := termGraph_binder_range v u y (base+64+termCost t) k hu
    omega
  · exact mulAt_below_not_binder base x y out k hk hm

/-- Replacement changes the two witness names and output, and applies the
same free-name renaming to each child graph. Capture by destination names is
checked separately when existentially binding the witnesses. -/
theorem replace_body {α : Type} [DecidableEq α] (v : α → Nat) (t u : Peano.language.Term α)
    (x y base out a b : Nat) (ha : a < base+2) :
    replace a b (body v t u x y base out) =
      body (rename a b ∘ v) t u (rename a b x) (rename a b y) base (rename a b out) := by
  unfold body andF
  simp only [CompactNamed.Formula.not, replace]
  rw [replace_termGraph v t x (base+64) a b (by omega)]
  rw [replace_termGraph v u y (base+64+termCost t) a b (by omega)]
  rw [replace_mulAt base x y out a b ha]

/-- The output and both witnesses lie below the parent allocator; they may
coincide as labels or represent the same object. The two child graphs use the
private bases required by the generated multiplication node. -/
def from_witnesses {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (base out x y : Nat)
    (hout : out < base) (hx : x < base) (hy : y < base)
    (ht : ∀ a ∈ t.varFinset, v a < base) (hu : ∀ a ∈ u.varFinset, v a < base) :
    KDerivation (imp (domainAt base out).encode
      (imp (termGraph v t x (base+64)).encode
        (imp (termGraph v u y (base+64+termCost t)).encode
          (imp (mulAt base x y out).encode
            (termGraph v (binaryTerm false t u) out base).encode)))) := by
  let N := body v t u base (base+1) base out
  have hb : base ∉ N.binders := below_not_binder v t u base (base+1) base out base (by omega)
  have hb1 : base+1 ∉ N.binders := below_not_binder v t u base (base+1) base out (base+1) (by omega)
  have hxn : x ∉ N.binders := below_not_binder v t u base (base+1) base out x (by omega)
  have hyn : y ∉ N.binders := below_not_binder v t u base (base+1) base out y (by omega)
  have hfirst : replace base x N = body v t u x (base+1) base out := by
    dsimp [N]
    rw [replace_body v t u base (base+1) base out base x (by omega)]
    have htv : ∀ a ∈ t.varFinset, (rename base x ∘ v) a = v a := by
      intro a ha
      simp [Function.comp_apply, rename, show v a ≠ base by have := ht a ha; omega]
    have huv : ∀ a ∈ u.varFinset, (rename base x ∘ v) a = v a := by
      intro a ha
      simp [Function.comp_apply, rename, show v a ≠ base by have := hu a ha; omega]
    unfold body
    rw [termGraph_name_agree t _ v htv, termGraph_name_agree u _ v huv]
    simp [rename, show out ≠ base by omega]
  have hsecond : replace (base+1) y (replace base x N) = body v t u x y base out := by
    rw [hfirst, replace_body v t u x (base+1) base out (base+1) y (by omega)]
    have htv : ∀ a ∈ t.varFinset, (rename (base+1) y ∘ v) a = v a := by
      intro a ha
      simp [Function.comp_apply, rename, show v a ≠ base+1 by have := ht a ha; omega]
    have huv : ∀ a ∈ u.varFinset, (rename (base+1) y ∘ v) a = v a := by
      intro a ha
      simp [Function.comp_apply, rename, show v a ≠ base+1 by have := hu a ha; omega]
    unfold body
    rw [termGraph_name_agree t _ v htv, termGraph_name_agree u _ v huv]
    simp [rename, show out ≠ base+1 by omega, show x ≠ base+1 by omega]
  have hi := exists_from_instance (base+1) y (replace base x N) (by omega)
    (by simpa only [replace_binders] using hb1)
    (by simpa only [replace_binders] using hyn)
  rw [hsecond] at hi
  have ho := exists_from_instance base x (.ex (base+1) N) (by omega)
    (by simpa [Formula.binders, show base ≠ base+1 by omega] using hb)
    (by simpa [Formula.binders, show x ≠ base+1 by omega] using hxn)
  change KDerivation (imp (existsCode (base+1) (replace base x N).encode)
    (existsCode base (Formula.ex (base+1) N).encode)) at ho
  have he := compose hi ho
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(mulAt base x y out).encode, (termGraph v u y (base+64+termCost t)).encode,
    (termGraph v t x (base+64)).encode, (domainAt base out).encode]
  have hR : Context Γ (mulAt base x y out).encode := .head _ _
  have hU : Context Γ (termGraph v u y (base+64+termCost t)).encode := .hypothesis (by simp [Γ])
  have hT : Context Γ (termGraph v t x (base+64)).encode := .hypothesis (by simp [Γ])
  have hD : Context Γ (domainAt base out).encode := .hypothesis (by simp [Γ])
  have hbody : Context Γ (body v t u x y base out).encode := by
    have h := Context.conjunctionIntro hT (Context.conjunctionIntro hU hR)
    simpa [body, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
  have hex := Context.mp hbody (.closed he)
  have hh := Context.conjunctionIntro hD hex
  simpa [N, body, binaryTerm, termGraph, andF, CompactNamed.Formula.not,
    Formula.encode, both, neg, existsCode] using hh

theorem from_witnesses_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (base out x y : Nat)
    (hout : out < base) (hx : x < base) (hy : y < base)
    (ht : ∀ a ∈ t.varFinset, v a < base) (hu : ∀ a ∈ u.varFinset, v a < base) :
    theoremCode (certificate (from_witnesses v t u base out x y hout hx hy ht hu)) =
      imp (domainAt base out).encode (imp (termGraph v t x (base+64)).encode
        (imp (termGraph v u y (base+64+termCost t)).encode (imp (mulAt base x y out).encode
          (termGraph v (binaryTerm false t u) out base).encode))) := certificate_correct _

end PASoundness.PAtoCompactMulNodeWitnessIntro

#print axioms PASoundness.PAtoCompactMulNodeWitnessIntro.body
#print axioms PASoundness.PAtoCompactMulNodeWitnessIntro.below_not_binder
#print axioms PASoundness.PAtoCompactMulNodeWitnessIntro.replace_body
#print axioms PASoundness.PAtoCompactMulNodeWitnessIntro.from_witnesses
#print axioms PASoundness.PAtoCompactMulNodeWitnessIntro.from_witnesses_certificate
