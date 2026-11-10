import PASoundness.PAtoCompactAllTermTransport
import PASoundness.PAtoCompactScopedAlphaInvariant
import PASoundness.PAtoCompactTermGraphReplace

/-! Rebind and rebase an existential term-graph witness.  The construction is
finite K proof data and does not assert that such a witness exists. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PASoundness.PAtoCompactPAAddZeroNecessityCanonical

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactScopedAlphaInvariant PASoundness.PAtoCompactTermGraphReplace
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactFreeNames

/-- Rebase a right equality-frame witness and rename its bound output to the
canonical lower fresh name. Source variables must lie strictly below `b`. -/
noncomputable def right_to_canonical (t : Peano.Term) (b p : Nat)
    (hp : b + 1 < p) (ht : ∀ a ∈ t.varFinset, a < b) :
    KDerivation (imp (existsCode (b + 1) (termGraph id t (b + 1) p).encode)
      (existsCode b (termGraph id t b (b + 2)).encode)) := by
  let f := termGraph id t (b + 1) (b + 2)
  have htransport : KDerivation (imp (termGraph id t (b + 1) p).encode f.encode) := by
    exact (termGraph_base_transport id t p (b + 2) (b + 1) hp (by omega)
      (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
      (by intro a ha; have := ht a ha; simp only [id_eq]; omega)).1
  have hsource : b + 1 ∉ f.binders := by
    exact termGraph_below_not_binder id t (b + 1) (b + 2) (b + 1) (by omega)
  have htarget : b ∉ f.names := by
    intro h
    rw [Formula.names_eq_free_union_binders] at h
    rcases Finset.mem_union.mp h with hf | hb
    · have hs := termGraph_free_subset id t (b + 1) (b + 2) hf
      rcases Finset.mem_union.mp hs with hi | hi
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hi
        have hh := ht a ha
        simp only [id_eq] at he
        omega
      · have hh := Finset.mem_singleton.mp hi
        omega
    · exact (termGraph_below_not_binder id t (b + 1) (b + 2) b (by omega)) hb
  have hreplace : replace (b + 1) b f = termGraph id t b (b + 2) := by
    dsimp [f]
    rw [replace_termGraph id t (b + 1) (b + 2) (b + 1) b (by omega)]
    simp only [rename, ↓reduceIte]
    apply termGraph_name_agree
    intro a ha
    have hh := ht a ha
    simp [rename, show a ≠ b + 1 by omega]
  have ha := (existentialAlpha (b + 1) b f (by omega) hsource htarget).1
  rw [hreplace] at ha
  exact compose (existsCongr (b + 1) htransport) ha

theorem right_to_canonical_certificate (t : Peano.Term) (b p : Nat)
    (hp : b + 1 < p) (ht : ∀ a ∈ t.varFinset, a < b) :
    theoremCode (certificate (right_to_canonical t b p hp ht)) =
      imp (existsCode (b + 1) (termGraph id t (b + 1) p).encode)
        (existsCode b (termGraph id t b (b + 2)).encode) := certificate_correct _

end PASoundness.PAtoCompactPAAddZeroNecessityCanonical

#print axioms PASoundness.PAtoCompactPAAddZeroNecessityCanonical.right_to_canonical
#print axioms PASoundness.PAtoCompactPAAddZeroNecessityCanonical.right_to_canonical_certificate
