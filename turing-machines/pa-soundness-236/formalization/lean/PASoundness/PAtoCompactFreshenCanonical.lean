import PASoundness.CompactFreshen
import PASoundness.PAtoCompactMapNamesCongr

/-! Allocation-count invariant for the existing capture-safe freshener.
This does not identify the freshened outputs of alpha-variant inputs. -/
namespace PASoundness.PAtoCompactFreshenCanonical

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation

/-- Count quantifier occurrences, including repeated or shadowed names. -/
def quantifierCount : Formula → Nat
  | .truth | .bottom | .member _ _ | .equal _ _ => 0
  | .imp a b => quantifierCount a + quantifierCount b
  | .all _ a | .ex _ a => quantifierCount a + 1

/-- The freshener consumes exactly one name for each quantifier occurrence. -/
theorem freshen_next (f : Formula) (start : Nat)
    (hn : ∀ v ∈ f.names, v < start) :
    (freshen f start hn).next = start + quantifierCount f := by
  induction f generalizing start with
  | truth | bottom | member | equal => rfl
  | imp a b ia ib =>
      change (freshen b (freshen a start (fun v hv => hn v (Finset.mem_union_left _ hv))).next
        (fun v hv => (hn v (Finset.mem_union_right _ hv)).trans_le
          (freshen a start (fun v hv => hn v (Finset.mem_union_left _ hv))).next_ge)).next =
        start + (quantifierCount a + quantifierCount b)
      rw [ib, ia]
      omega
  | all x a ia | ex x a ia =>
      change (freshen a start (fun v hv => hn v (Finset.mem_insert_of_mem hv))).next + 1 =
        start + (quantifierCount a + 1)
      rw [ia]
      omega

/-- Global name mapping leaves the number of binder occurrences unchanged,
even when the mapping is not injective. -/
theorem quantifierCount_mapNames (g : Nat → Nat) (f : Formula) :
    quantifierCount (mapNames g f) = quantifierCount f := by
  induction f with
  | truth | bottom | member | equal => rfl
  | imp a b ia ib => simp [mapNames, quantifierCount, ia, ib]
  | all x a ia | ex x a ia => simp [mapNames, quantifierCount, ia]

/-- Original and globally renamed inputs consume the same allocation range
when both satisfy the freshener's stated input-name bounds. This theorem says
nothing about equality of the resulting formulas. -/
theorem freshen_next_mapNames (g : Nat → Nat) (f : Formula) (start : Nat)
    (hf : ∀ v ∈ f.names, v < start)
    (hg : ∀ v ∈ (mapNames g f).names, v < start) :
    (freshen (mapNames g f) start hg).next = (freshen f start hf).next := by
  rw [freshen_next, freshen_next, quantifierCount_mapNames]

/-- A common freshened formula gives literal K proof data in both directions.
The syntactic equality of the freshened outputs is an explicit premise. -/
def commonFreshening (a b : Formula) (start : Nat)
    (ha : ∀ v ∈ a.names, v < start) (hb : ∀ v ∈ b.names, v < start)
    (he : (freshen a start ha).formula = (freshen b start hb).formula) :
    ProofEquiv a b := by
  have h : ProofEquiv (freshen a start ha).formula b := by
    rw [he]
    exact (freshen b start hb).equivalent.symm
  exact (freshen a start ha).equivalent.trans h

end PASoundness.PAtoCompactFreshenCanonical

#print axioms PASoundness.PAtoCompactFreshenCanonical.freshen_next
#print axioms PASoundness.PAtoCompactFreshenCanonical.quantifierCount_mapNames
#print axioms PASoundness.PAtoCompactFreshenCanonical.freshen_next_mapNames
#print axioms PASoundness.PAtoCompactFreshenCanonical.commonFreshening
