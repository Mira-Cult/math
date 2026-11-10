import PASoundness.PAtoCompactPAAddSuccSharedDiamondPoint
import PASoundness.PAtoCompactFreeVacuity

/-! Eliminate the internal arithmetic-diamond witnesses while retaining the
same output for both term graphs. No premise about existence is asserted. -/
namespace PASoundness.PAtoCompactPAAddSuccSharedDiamondPack

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactPAAddSuccSharedDiamondPoint PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact conjunction of a source-graph pair and arithmetic diamond. -/
def diamond (t u : Peano.Term) (e x y z sy q : Nat) : Nat :=
  both (domainAt e sy).encode (both (domainAt e z).encode
    (both (domainAt e q).encode (both (termGraph id t x e).encode
      (both (termGraph id u y e).encode (both (succAt e y sy).encode
        (both (addAt e x y z).encode (both (succAt e z q).encode
          (addAt e x sy q).encode)))))))

/-- Eliminate an existential from a closed implication when its conclusion
is vacuous in the bound name. -/
def drop_exists (x a b : Nat) (h : KDerivation (imp a b))
    (hv : KDerivation (imp b (allCode x b))) :
    KDerivation (imp (existsCode x a) b) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.existsElim hv
  · exact .closed (.generalize x h)
  · exact .head [] _

/-- From a nested arithmetic diamond, return the exact shared-output graph
pair needed by the equality-frame constructor. The caller still has to
construct the input diamond; the four internal labels are syntactically fresh. -/
noncomputable def shared_from_diamond (t u : Peano.Term) (q : Nat)
    (ht : ∀ a ∈ t.varFinset, a < q) (hu : ∀ a ∈ u.varFinset, a < q) :
    let x := q+1
    let y := q+2
    let z := q+3
    let sy := q+4
    let e := q+100
    let left := Peano.add t (Peano.succ u)
    let right := Peano.succ (Peano.add t u)
    KDerivation (imp (existsCode x (existsCode y (existsCode z (existsCode sy
      (existsCode q (diamond t u e x y z sy q))))))
      (existsCode q (andF (termGraph id left q (q+2))
        (termGraph id right q (q+2+termCost left))).encode)) := by
  let x := q+1
  let y := q+2
  let z := q+3
  let sy := q+4
  let e := q+100
  let left := binaryTerm true t (.func .succ ![u])
  let right := (.func .succ ![binaryTerm true t u] : Peano.Term)
  let pair := andF (termGraph id left q (q+2))
    (termGraph id right q (q+2+termCost left))
  let E := Formula.ex q pair
  have hl : ∀ a ∈ left.varFinset, id a < q := by
    intro a ha
    have h : a ∈ t.varFinset ∨ a ∈ u.varFinset := by
      simpa [left, binaryTerm, Term.varFinset] using ha
    rcases h with h | h
    · exact ht a h
    · exact hu a h
  have hr : ∀ a ∈ right.varFinset, id a < q := by
    intro a ha
    have h : a ∈ t.varFinset ∨ a ∈ u.varFinset := by
      simpa [right, binaryTerm, Term.varFinset] using ha
    rcases h with h | h
    · exact ht a h
    · exact hu a h
  have hpairfree (k : Nat) (hk : q < k) : k ∉ pair.free := by
    intro h
    simp only [pair, andF_free, Finset.mem_union] at h
    rcases h with h | h
    · have hf := termGraph_free_subset id left q (q+2) h
      rcases Finset.mem_union.mp hf with hf | hf
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hf
        have hh := hl a ha
        simp only [id_eq] at he hh
        omega
      · have hh := Finset.mem_singleton.mp hf
        omega
    · have hf := termGraph_free_subset id right q (q+2+termCost left) h
      rcases Finset.mem_union.mp hf with hf | hf
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hf
        have hh := hr a ha
        simp only [id_eq] at he hh
        omega
      · have hh := Finset.mem_singleton.mp hf
        omega
  have hEfree (k : Nat) (hk : q < k) : k ∉ E.free := by
    intro h
    have hp : k ∈ pair.free := (Finset.mem_erase.mp h).2
    exact hpairfree k hk hp
  have hdiamond := shared_graphs_of_diamond id t u e e e x y sy z q
    (by dsimp [e,x]; omega) (by dsimp [e,y]; omega) (by dsimp [e,sy]; omega)
    (by dsimp [e,z]; omega) (by dsimp [e]; omega)
    (by dsimp [e,x]; omega) (by dsimp [e,y]; omega) (by dsimp [e,sy]; omega) (by dsimp [e]; omega)
    (by dsimp [e,x]; omega) (by dsimp [e,y]; omega) (by dsimp [e,z]; omega) (by dsimp [e]; omega)
    (by intro a ha; have := ht a ha; dsimp [e]; omega)
    (by intro a ha; have := hu a ha; dsimp [e]; omega)
    (by intro a ha; have := ht a ha; dsimp [e]; omega)
    (by intro a ha; have := hu a ha; dsimp [e]; omega)
    (by intro a ha; have := ht a ha; dsimp [e]; omega)
    (by intro a ha; have := hu a ha; dsimp [e]; omega)
  have hL := (termGraph_base_transport id left e (q+2) q (by dsimp [e]; omega)
    (by omega) (by intro a ha; have h := hl a ha; simp only [id_eq] at h ⊢; dsimp [e]; omega)
    (by intro a ha; have h := hl a ha; simp only [id_eq] at h ⊢; omega)).1
  have hR := (termGraph_base_transport id right e (q+2+termCost left) q
    (by dsimp [e]; omega) (by omega)
    (by intro a ha; have h := hr a ha; simp only [id_eq] at h ⊢; dsimp [e]; omega)
    (by intro a ha; have h := hr a ha; simp only [id_eq] at h ⊢; omega)).1
  have hpoint : KDerivation (imp (diamond t u e x y z sy q) pair.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [diamond t u e x y z sy q]
    have h := Context.head [] (diamond t u e x y z sy q)
    have hDsy := Context.conjunctionLeft h
    have h₁ := Context.conjunctionRight h
    have hDz := Context.conjunctionLeft h₁
    have h₂ := Context.conjunctionRight h₁
    have hDq := Context.conjunctionLeft h₂
    have h₃ := Context.conjunctionRight h₂
    have hGt := Context.conjunctionLeft h₃
    have h₄ := Context.conjunctionRight h₃
    have hGu := Context.conjunctionLeft h₄
    have h₅ := Context.conjunctionRight h₄
    have hS1 := Context.conjunctionLeft h₅
    have h₆ := Context.conjunctionRight h₅
    have hA1 := Context.conjunctionLeft h₆
    have h₇ := Context.conjunctionRight h₆
    have hS2 := Context.conjunctionLeft h₇
    have hA2 := Context.conjunctionRight h₇
    have hh := Context.mp hA2 (Context.mp hS2 (Context.mp hA1 (Context.mp hS1
      (Context.mp hGu (Context.mp hGt (Context.mp hDq (Context.mp hDz
        (Context.mp hDsy (.closed hdiamond)))))))))
    have hp : Context Γ (both (termGraph id left q e).encode (termGraph id right q e).encode) := by
      simpa [Γ, left, right, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hh
    have hleft := Context.mp (Context.conjunctionLeft hp) (.closed hL)
    have hright := Context.mp (Context.conjunctionRight hp) (.closed hR)
    have hc := Context.conjunctionIntro hleft hright
    simpa [pair, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hc
  have hq := existsCongr q hpoint
  have hsy := drop_exists sy _ E.encode hq (free_vacuity sy E (hEfree sy (by dsimp [sy]; omega)))
  have hz := drop_exists z _ E.encode hsy (free_vacuity z E (hEfree z (by dsimp [z]; omega)))
  have hy := drop_exists y _ E.encode hz (free_vacuity y E (hEfree y (by dsimp [y]; omega)))
  have hx := drop_exists x _ E.encode hy (free_vacuity x E (hEfree x (by dsimp [x]; omega)))
  simpa [x, y, z, sy, e, left, right, E, pair, Peano.add, Peano.succ, binaryTerm,
    Formula.encode, existsCode] using hx

end PASoundness.PAtoCompactPAAddSuccSharedDiamondPack

#print axioms PASoundness.PAtoCompactPAAddSuccSharedDiamondPack.shared_from_diamond
