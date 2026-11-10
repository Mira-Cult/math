import PASoundness.PAtoCompactPAAddSuccSharedDiamondPack
import PASoundness.PAtoCompactMulZeroAxiomFrameShared
import PASoundness.PAtoCompactGuardedBridge

/-! A supplied guarded existential witness package and its pointwise
shared-output graphs yield the literal guarded equality. The package and
pointwise graph proof remain explicit K proof-data inputs. -/
namespace PASoundness.PAtoCompactGuardedEqualityDiamondAdapter

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactMulZeroAxiomFrameShared PASoundness.PAtoCompactPAAddSuccSharedDiamondPack
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Construct the guarded equality from a caller-supplied package of four
internal witnesses and one common output, provided the package entails both
actual term graphs at the indicated bases. No package existence, arithmetic
identity, or graph functionality is derived by this adapter. -/
noncomputable def guarded_of_diamond (left right : Peano.Term) (body : Nat)
    (point : let A := left.equal right
      let q := guardBase A
      KDerivation (imp body (andF (termGraph id left q (q+2))
        (termGraph id right q (q+2+termCost left))).encode))
    (package : let A := left.equal right
      let q := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode (q+1) (existsCode (q+2) (existsCode (q+3)
          (existsCode (q+4) (existsCode q body))))))) :
    KDerivation (guardedCode (left.equal right)) := by
  let A := left.equal right
  let q := guardBase A
  let pair := andF (termGraph id left q (q+2))
    (termGraph id right q (q+2+termCost left))
  let E := Formula.ex q pair
  have hscope : q = scopeBase A Fin.elim0 := by simp [q, guardBase, scopeBase]
  have hl : ∀ a ∈ left.varFinset, a < q := by
    intro a ha
    have hf : a ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inl ha
    have hh := free_lt_scopeBase A Fin.elim0 a hf
    omega
  have hr : ∀ a ∈ right.varFinset, a < q := by
    intro a ha
    have hf : a ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inr ha
    have hh := free_lt_scopeBase A Fin.elim0 a hf
    omega
  have hEfree (k : Nat) (hk : q < k) : k ∉ E.free := by
    intro he
    have hp : k ∈ pair.free := (Finset.mem_erase.mp he).2
    simp only [pair, andF_free, Finset.mem_union] at hp
    rcases hp with hp | hp
    · have hf := termGraph_free_subset id left q (q+2) hp
      rcases Finset.mem_union.mp hf with hf | hf
      · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hf
        have hh := hl a ha
        simp only [id_eq] at heq
        omega
      · have hh := Finset.mem_singleton.mp hf
        omega
    · have hf := termGraph_free_subset id right q (q+2+termCost left) hp
      rcases Finset.mem_union.mp hf with hf | hf
      · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hf
        have hh := hr a ha
        simp only [id_eq] at heq
        omega
      · have hh := Finset.mem_singleton.mp hf
        omega
  have hp : KDerivation (imp body pair.encode) := by simpa [A, q, pair] using point
  have hq := existsCongr q hp
  have h4 := drop_exists (q+4) _ E.encode hq (free_vacuity (q+4) E (hEfree (q+4) (by omega)))
  have h3 := drop_exists (q+3) _ E.encode h4 (free_vacuity (q+3) E (hEfree (q+3) (by omega)))
  have h2 := drop_exists (q+2) _ E.encode h3 (free_vacuity (q+2) E (hEfree (q+2) (by omega)))
  have h1 := drop_exists (q+1) _ E.encode h2 (free_vacuity (q+1) E (hEfree (q+1) (by omega)))
  have hex : KDerivation (imp (guardFormula A).encode E.encode) := by
    have hpack : KDerivation (imp (guardFormula A).encode
        (existsCode (q+1) (existsCode (q+2) (existsCode (q+3)
          (existsCode (q+4) (existsCode q body)))))) := by simpa [A, q] using package
    exact compose hpack (by simpa [E, Formula.encode, existsCode] using h1)
  have hframe := shared_graphs_to_frame left right q hl hr
  have hresult := compose hex (by simpa [E, pair, Formula.encode, existsCode] using hframe)
  unfold guardedCode code
  rw [original_shape]
  change KDerivation (imp (guardFormula A).encode (equalityFrame id left right (scopeBase A Fin.elim0)).encode)
  rw [← hscope]
  exact hresult

end PASoundness.PAtoCompactGuardedEqualityDiamondAdapter

#print axioms PASoundness.PAtoCompactGuardedEqualityDiamondAdapter.guarded_of_diamond
