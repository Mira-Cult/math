import PASoundness.PAtoCompactFormulaFullTruth
import PASoundness.PAtoCompactGraphMeaning
import PASoundness.PAtoCompactBijectionMeaning
import PASoundness.PAtoCompactOrderMeaning
import PASoundness.PAtoCompactTermGraphTruth
import PASoundness.PAtoCompactConcreteBridge
import PASoundness.PAtoCompactVacuousHandler

/-! A standard-HF check of whether unguarded translated open equality axioms
can be K theorems. This is a diagnostic about the concrete translation, not a
proof of PA soundness or machine acceptance. -/
namespace PASoundness.PAtoCompactOpenAxiomCounterexample

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphMeaning PASoundness.PAtoCompactBijectionMeaning
open PASoundness.PAtoCompactOrderMeaning PASoundness.HFCoding
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermRenamingSemantics
open PASoundness.PAtoCompactTermGraphTruth PASoundness.PAtoCompactFormulaTranslation
open PASoundness.CompactMatrix (Environment bit update)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The HF set coded by 5 has incomparable members 0 and 2, so it cannot be
order-isomorphic under membership to any finite ordinal. -/
theorem five_not_equivalent_ordinal (ρ : Environment) (n : Nat)
    (h0 : ρ 0 = 5) (h1 : ρ 1 = (ordinal n).code) :
    ¬ equivalentFormula.Realize ρ := by
  intro he
  change ∃ g, ¬ (bijectionFormula.Realize (update ρ 6 g) →
    ¬ orderFormula.Realize (update ρ 6 g)) at he
  obtain ⟨g, hg⟩ := he
  have hb : bijectionFormula.Realize (update ρ 6 g) := by
    by_contra h
    exact hg (fun hb => (h hb).elim)
  have ho : orderFormula.Realize (update ρ 6 g) := by
    by_contra h
    exact hg (fun _ => h)
  have h23 : ∀ η, (graphFormula 6 2 3).Realize η ↔ graphRel (η 6) (η 2) (η 3) := by
    intro η; exact graphFormula_realize_iff 6 2 3 η (by decide) (by decide) (by decide)
  have h24 : ∀ η, (graphFormula 6 2 4).Realize η ↔ graphRel (η 6) (η 2) (η 4) := by
    intro η; exact graphFormula_realize_iff 6 2 4 η (by decide) (by decide) (by decide)
  have h43 : ∀ η, (graphFormula 6 4 3).Realize η ↔ graphRel (η 6) (η 4) (η 3) := by
    intro η; exact graphFormula_realize_iff 6 4 3 η (by decide) (by decide) (by decide)
  have h45 : ∀ η, (graphFormula 6 4 5).Realize η ↔ graphRel (η 6) (η 4) (η 5) := by
    intro η; exact graphFormula_realize_iff 6 4 5 η (by decide) (by decide) (by decide)
  have ⟨hf, hr⟩ := (bijection_meaning (update ρ 6 g) graphRel h23 h24 h43).mp hb
  have horder := (order_meaning (update ρ 6 g) graphRel h23 h45).mp ho
  have hm0 : bit (update ρ 6 g 0) 0 = true := by simpa [update, h0] using (show bit 5 0 = true by decide)
  have hm2 : bit (update ρ 6 g 0) 2 = true := by simpa [update, h0] using (show bit 5 2 = true by decide)
  obtain ⟨b, hbmem, hgb, _⟩ := hf 0 hm0
  obtain ⟨d, hdmem, hgd, _⟩ := hf 2 hm2
  have hbd : b ≠ d := by
    intro h
    subst d
    obtain ⟨a, _, _, hu⟩ := hr b hbmem
    have h0a := hu 0 hm0 hgb
    have h2a := hu 2 hm2 hgd
    omega
  have hb' : (⟨b⟩ : Object) ∈ ordinal n := by
    change bit (ordinal n).code b = true
    simpa [update, h1] using hbmem
  have hd' : (⟨d⟩ : Object) ∈ ordinal n := by
    change bit (ordinal n).code d = true
    simpa [update, h1] using hdmem
  obtain ⟨i, hi, hbi⟩ := (mem_ordinal _ _).mp hb'
  obtain ⟨j, hj, hdj⟩ := (mem_ordinal _ _).mp hd'
  have hbcode : b = (ordinal i).code := congrArg Object.code hbi
  have hdcode : d = (ordinal j).code := congrArg Object.code hdj
  have hij : i ≠ j := by
    intro h
    subst j
    apply hbd
    exact hbcode.trans hdcode.symm
  by_cases hlt : i < j
  · have hrel : bit d b = true := by
      rw [hbcode, hdcode]
      exact ordinal_member hlt
    have hbad : bit 2 0 = true := (horder 0 2 b d hm0 hm2 hbmem hdmem hgb hgd).mpr hrel
    have hfalse : bit 2 0 = false := by decide
    rw [hfalse] at hbad
    cases hbad
  · have hlt' : j < i := by omega
    have hrel : bit b d = true := by
      rw [hbcode, hdcode]
      exact ordinal_member hlt'
    have hbad : bit 0 2 = true := (horder 2 0 d b hm2 hm0 hdmem hbmem hgd hgb).mpr hrel
    have hfalse : bit 0 2 = false := by decide
    rw [hfalse] at hbad
    cases hbad

/-- No renamed equivalence instance can relate an input coded by 5 to an
ordinal output, under the stated syntactic-name conditions. -/
theorem five_not_equivAt_ordinal (base x y n : Nat) (ρ : Environment)
    (hxy : x ≠ y) (hx : x < base + 2) (hy : y < base + 2)
    (h0 : ρ x = 5) (h1 : ρ y = (ordinal n).code) :
    ¬ (equivAt base x y).Realize ρ := by
  intro h
  unfold equivAt at h
  rw [mapNames_realize _ (twoMap_injective base 0 1 x y (by decide) hxy hx hy),
    normalizeBottom_realize] at h
  apply five_not_equivalent_ordinal (ρ ∘ twoMap base 0 1 x y) n ?_ ?_ h
  · simpa [Function.comp_def, twoMap] using h0
  · simpa [Function.comp_def, twoMap] using h1

/-- The logical equality-reflexivity leaf for the free variable 0. -/
def openReflexivity : Peano.Formula := (FirstOrder.Language.Term.var 0 : Peano.Term).equal (.var 0)

/-- Its concrete translation fails at an HF assignment taking the variable
to the two-element antichain coded by 5. -/
theorem translated_open_reflexivity_false (ρ : Environment) (h0 : ρ 0 = 5) :
    ¬ (PASoundness.CompactMatrix.decode (code openReflexivity)).Realize ρ := by
  rw [show code openReflexivity = (formula openReflexivity).encode by rfl,
    Formula.encode_realize]
  intro h
  change (CompactNamed.Formula.ex 1 (.ex 2
    (andF (termGraph (Sum.elim id Fin.elim0) (.var (.inl 0)) 1 3)
      (andF (termGraph (Sum.elim id Fin.elim0) (.var (.inl 0)) 2 67)
        (equivAt 131 1 2))))).Realize ρ at h
  obtain ⟨a, b, hab⟩ := h
  let η := update (update ρ 1 a) 2 b
  have hleft := ((andF_realize _ _ η).mp hab).1
  change (andF (domainAt 3 1) (equivAt 3 0 1)).Realize η at hleft
  have hdom := ((andF_realize _ _ η).mp hleft).1
  have heq := ((andF_realize _ _ η).mp hleft).2
  obtain ⟨n, hn⟩ := (domainAt_iff 3 1 (by omega) η).mp hdom
  apply five_not_equivAt_ordinal 3 0 1 n η (by decide) (by decide) (by decide) ?_ hn heq
  simpa [η, update] using h0

/-- The unguarded handler structure cannot be inhabited: its equality
reflexivity leaf would contradict K soundness at this HF assignment. -/
theorem no_unguarded_handlers : ¬ Nonempty PAtoCompactConcreteBridge.Handlers := by
  rintro ⟨h⟩
  let ρ : Environment := fun _ => 5
  have hc : Certificates.logicalDecode (.eqRefl (.var 0)) = some openReflexivity := rfl
  have d := h.logical (.eqRefl (.var 0)) openReflexivity hc
  exact translated_open_reflexivity_false ρ rfl (CompactSemantics.derivation_sound d ρ)

/-- The narrowed unguarded logical interface is impossible for the same
reason; the failure is already in its equality-reflexivity field. -/
theorem no_unguarded_four_logical : ¬ Nonempty PAtoCompactVacuousHandler.FourLogical := by
  rintro ⟨h⟩
  let ρ : Environment := fun _ => 5
  have d : CompactProof.KDerivation (code openReflexivity) := h.eqRefl (.var 0)
  exact translated_open_reflexivity_false ρ rfl (CompactSemantics.derivation_sound d ρ)

end PASoundness.PAtoCompactOpenAxiomCounterexample

#print axioms PASoundness.PAtoCompactOpenAxiomCounterexample.translated_open_reflexivity_false
#print axioms PASoundness.PAtoCompactOpenAxiomCounterexample.no_unguarded_handlers
#print axioms PASoundness.PAtoCompactOpenAxiomCounterexample.no_unguarded_four_logical
