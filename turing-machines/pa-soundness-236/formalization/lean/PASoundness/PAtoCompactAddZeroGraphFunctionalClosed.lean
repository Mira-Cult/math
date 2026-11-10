import PASoundness.PAtoCompactAddZeroGraphProjection
import PASoundness.PAtoCompactScopedVacuity
import PASoundness.PAtoCompactAllTermTransport
import PASoundness.PAtoCompactAddZeroQuotientChain

/-! Functionality of right-zero addition graphs through two distinct child
witnesses. The child graph functionality and pointwise quotient chain are
finite K proof inputs; the graph projections and vacuity are constructed. -/
namespace PASoundness.PAtoCompactAddZeroGraphFunctionalClosed
open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactScopedVacuity PASoundness.PAtoCompactAddZeroGraphProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- Both graph outputs are compared after projecting their actual child
witnesses. Quotient-chain and child-functionality inputs remain explicit. -/
noncomputable def functionality_of_child_and_chain {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α) (b c p q e : Nat) (g : Formula)
    (hbc : b < c) (hp : p < b) (hq : q < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) (hgb : b ∉ g.free) (hgc : c ∉ g.free)
    (child : KDerivation (imp g.encode (imp (termGraph v t b (b+64)).encode
      (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (next : KDerivation (imp (termGraph v t b (b+64)).encode
      (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
        (imp (equivAt e b c).encode (imp (equivAt b b p).encode
          (imp (equivAt c c q).encode (equivAt b p q).encode)))))) :
    KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
        (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q c).encode
          (equivAt b p q).encode))) := by
  let s : Peano.language.Term α := binaryTerm true t (.func .zero Fin.elim0)
  let A := (termGraph v s p b).encode
  let B := (termGraph v s q c).encode
  let C := (andF (termGraph v t b (b+64)) (equivAt b b p)).encode
  let D := (andF (termGraph v t c (c+64)) (equivAt c c q)).encode
  let E := (equivAt b p q).encode
  have hvb : ∀ a ∈ s.varFinset, b ≠ v a := by
    intro a ha
    have ha' : a ∈ t.varFinset := by simpa [s, binaryTerm, Term.varFinset] using ha
    have h := hv a ha'; omega
  have hvc : ∀ a ∈ s.varFinset, c ≠ v a := by
    intro a ha
    have ha' : a ∈ t.varFinset := by simpa [s, binaryTerm, Term.varFinset] using ha
    have h := hv a ha'; omega
  have hbody : c ∉ (andF (termGraph v t b (b+64)) (equivAt b b p)).free := by
    intro hh
    rw [andF_free, Finset.mem_union] at hh
    rcases hh with hh | hh
    · have hh := termGraph_free_subset v t b (b+64) hh
      rcases Finset.mem_union.mp hh with hh | hh
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
        have h := hv a ha; omega
      · have he := Finset.mem_singleton.mp hh; omega
    · have hh := equivAt_free b b p hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      omega
  have heb : b ∉ (equivAt b p q).free := by
    intro hh
    have hh := equivAt_free b p q hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  have hec : c ∉ (equivAt b p q).free := by
    intro hh
    have hh := equivAt_free b p q hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  have project1 := project_child v t b p hp hv
  have project2 := project_child v t c q (by omega) (by intro a ha; have := hv a ha; omega)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [B,A,g.encode]
  have hA : Context Γ A := .hypothesis (by simp [Γ])
  have hB : Context Γ B := .head _ _
  have hExA : Context Γ (existsCode b C) := .mp hA (.closed project1)
  apply Context.existsElim (free_vacuity b _ heb) _ hExA
  apply Context.generalize b
  · intro n hn
    change n ∈ [B,A,g.encode] at hn
    by_cases h : n = B
    · subst n; exact termGraph_vacuity v s q c b (by omega) hvb
    · by_cases h' : n = A
      · subst n; exact termGraph_vacuity v s p b b (by omega) hvb
      · have h'' : n = g.encode := by simpa [h, h'] using hn
        subst n; exact free_vacuity b g hgb
  apply Context.deduction
  let Δ := [C,B,A,g.encode]
  have hB' : Context Δ B := .hypothesis (by simp [Δ])
  have hExB : Context Δ (existsCode c D) := .mp hB' (.closed project2)
  apply Context.existsElim (free_vacuity c _ hec) _ hExB
  apply Context.generalize c
  · intro n hn
    change n ∈ [C,B,A,g.encode] at hn
    by_cases h : n = C
    · subst n; exact free_vacuity c _ hbody
    · by_cases h' : n = B
      · subst n; exact termGraph_vacuity v s q c c (by omega) hvc
      · by_cases h'' : n = A
        · subst n; exact termGraph_vacuity v s p b c (by omega) hvc
        · have hlast : n = g.encode := by simpa [h, h', h''] using hn
          subst n; exact free_vacuity c g hgc
  apply Context.deduction
  let Θ := [D,C,B,A,g.encode]
  have hD : Context Θ D := .head _ _
  have hC : Context Θ C := .hypothesis (by simp [Θ])
  have hA' : Context Θ A := .hypothesis (by simp [Θ])
  have hg : Context Θ g.encode := .hypothesis (by simp [Θ])
  have hc1 : Context Θ (termGraph v t b (b+64)).encode := Context.conjunctionLeft hC
  have he1 : Context Θ (equivAt b b p).encode := Context.conjunctionRight hC
  have hc2 : Context Θ (termGraph v t c (c+64)).encode := Context.conjunctionLeft hD
  have he2 : Context Θ (equivAt c c q).encode := Context.conjunctionRight hD
  have he := Context.mp hc2 (Context.mp hc1 (Context.mp hg (.closed child)))
  exact .mp he2 (.mp he1 (.mp he (.mp hA' (.mp hc1 (.closed next)))))

/-- Actual right-zero graph functionality at distinct allocators, from the
stated child-graph functionality alone. The common comparison base is c+1. -/
noncomputable def functionality_of_child {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α) (b c p q : Nat) (g : Formula)
    (hbc : b < c) (hp : p < b) (hq : q < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) (hgb : b ∉ g.free) (hgc : c ∉ g.free)
    (child : KDerivation (imp g.encode (imp (termGraph v t b (b+64)).encode
      (imp (termGraph v t c (c+64)).encode (equivAt (c+1) b c).encode)))) :
    KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
        (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q c).encode
          (equivAt b p q).encode))) :=
  functionality_of_child_and_chain v t b c p q (c+1) g hbc hp hq hv hgb hgc child
    (PASoundness.PAtoCompactAddZeroQuotientChain.pointwise v t b c p q hbc hp hq)

end PASoundness.PAtoCompactAddZeroGraphFunctionalClosed
#print axioms PASoundness.PAtoCompactAddZeroGraphFunctionalClosed.functionality_of_child_and_chain
#print axioms PASoundness.PAtoCompactAddZeroGraphFunctionalClosed.functionality_of_child
