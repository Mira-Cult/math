import PASoundness.PAtoCompactScopedEqualityReplace
import PASoundness.CompactFreshen
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactTemplateBlockShift

/-! A scoped universal's generated binder can be moved to a genuinely fresh
name by finite K proofs. Alignment with a separately generated scoped body
remains an independent obligation. -/
namespace PASoundness.PAtoCompactVacuousUniversal

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.CompactDerivations PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactTemplateBlockShift

/-- Active de Bruijn-level names are never bound by the generated scoped
formula. No injectivity of the active environment is required. -/
theorem active_not_binder {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :
    ∀ (bound : Fin n → Nat) (i : Fin n),
      bound i ∉ (scopedFormula n φ bound).binders := by
  induction φ with
  | falsum =>
      intro bound i
      simp [scopedFormula, Formula.binders]
  | @equal n t u =>
      intro bound i h
      rw [scoped_equal_frame] at h
      have hge := equalityFrame_binders_ge (Sum.elim id bound) t u
        (scopeBase (.equal t u) bound) (bound i) h
      have hlt := bound_lt_scopeBase (.equal t u) bound i
      omega
  | rel r ts => exact nomatch r
  | imp a b iha ihb =>
      intro bound i h
      simp only [scopedFormula, Formula.binders, Finset.mem_union] at h
      cases h with
      | inl h => exact iha bound i h
      | inr h => exact ihb bound i h
  | @all n body ih =>
      intro bound i h
      let x := scopeBase (.all body) bound
      have hlt : bound i < x := bound_lt_scopeBase (.all body) bound i
      change bound i ∈ (Formula.all x (.imp (domainAt (x+1) x)
        (scopedFormula (n+1) body (Fin.snoc bound x)))).binders at h
      simp only [Formula.binders, Finset.mem_insert, Finset.mem_union] at h
      rcases h with he | hd | hs
      · omega
      · have hp := domainAt_private (x+1) x (bound i) hd
        omega
      · have hn := ih (Fin.snoc bound x) (Fin.castSucc i)
        apply hn
        simpa using hs

/-- The binder chosen for a source universal. -/
def universalName {n : Nat} (body : Peano.language.BoundedFormula Nat (n+1))
    (bound : Fin n → Nat) : Nat := scopeBase (.all body) bound

/-- The generated candidate-guarded body below that universal. -/
def universalBody {n : Nat} (body : Peano.language.BoundedFormula Nat (n+1))
    (bound : Fin n → Nat) : Formula :=
  let x := universalName body bound
  .imp (domainAt (x+1) x) (scopedFormula (n+1) body (Fin.snoc bound x))

/-- The same universal body with its candidate guard allocated at a
separately chosen base. -/
def universalBodyAt {n : Nat} (body : Peano.language.BoundedFormula Nat (n+1))
    (bound : Fin n → Nat) (base : Nat) : Formula :=
  let x := universalName body bound
  .imp (domainAt base x) (scopedFormula (n+1) body (Fin.snoc bound x))

/-- K-equivalence of the generated universal with a version using a new
candidate-guard base, preserving the existing bound name. -/
def universal_rebase_guard {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat) (base : Nat)
    (hb : universalName body bound < base + 32) :
    KDerivation (imp (scopedFormula n (.all body) bound).encode
      (Formula.all (universalName body bound) (universalBodyAt body bound base)).encode) ×
    KDerivation (imp (Formula.all (universalName body bound) (universalBodyAt body bound base)).encode
      (scopedFormula n (.all body) bound).encode) := by
  let x := universalName body bound
  have oldnew := domainAt_transport (x+1) base x (by omega) hb
  have newold := domainAt_transport base (x+1) x hb (by omega)
  have idbody := identity (scopedFormula (n+1) body (Fin.snoc bound x)).encode
  exact ⟨allCongr x (implicationCongr newold idbody),
    allCongr x (implicationCongr oldnew idbody)⟩

/-- Renaming an operand below a candidate guard's private block commutes
with its construction. This is a syntactic identity; target freshness is a
separate condition when the replacement is used under a quantifier. -/
theorem replace_domainAt (base x z : Nat) (hx : x < base) :
    replace x z (domainAt base x) = domainAt base z := by
  have hn : x ∉ (domainAt base x).binders := by
    intro h
    have hp := domainAt_private base x x h
    omega
  rw [← PAtoCompactAlphaMapOne.map_eq_replace x z _ hn]
  have hs : ∀ i < 64, rename x z (base + i) = base + i := by
    intro i hi
    simp [rename, show base + i ≠ x by omega]
  simpa [rename] using domainAt_shift (rename x z) base base x hs

/-- The original universal name remains unbound in a body with a guard
allocated above that name. -/
theorem universalName_not_high_body_binder {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat)
    (base : Nat) (hb : universalName body bound < base + 2) :
    universalName body bound ∉ (universalBodyAt body bound base).binders := by
  let x := universalName body bound
  change x ∉ (Formula.imp (domainAt base x)
    (scopedFormula (n+1) body (Fin.snoc bound x))).binders
  simp only [Formula.binders, Finset.mem_union, not_or]
  constructor
  · intro h
    have hp := domainAt_private base x x h
    omega
  · have hn := active_not_binder body (Fin.snoc bound x) (Fin.last n)
    simpa using hn

/-- Alpha-move a universal after its guard has been rebased above the old
name. The new name must be absent from the entire rebased body. -/
def high_universal_alpha {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat)
    (base z : Nat) (hb : universalName body bound < base)
    (hne : universalName body bound ≠ z) (hz : z ∉ (universalBodyAt body bound base).names) :
    ProofEquiv (Formula.all (universalName body bound) (universalBodyAt body bound base))
      (Formula.all z (.imp (domainAt base z)
        (replace (universalName body bound) z
          (scopedFormula (n+1) body (Fin.snoc bound (universalName body bound)))))) := by
  have h := ProofEquiv.alphaAll (universalName body bound) z (universalBodyAt body bound base)
    hne (universalName_not_high_body_binder body bound base (by omega)) hz
  simpa only [universalBodyAt, replace, replace_domainAt base (universalName body bound) z hb] using h

/-- If the renamed children have K implications both ways, rebasing both
candidate guards to the same high block and alpha-moving both outer binders
constructs K implications between the original generated universals. -/
def universals_of_common_child {n m : Nat}
    (a : Peano.language.BoundedFormula Nat (n+1)) (ab : Fin n → Nat)
    (b : Peano.language.BoundedFormula Nat (m+1)) (bb : Fin m → Nat)
    (base z : Nat)
    (hbasea : universalName a ab < base) (hbaseb : universalName b bb < base)
    (hza : universalName a ab ≠ z) (hzb : universalName b bb ≠ z)
    (hna : z ∉ (universalBodyAt a ab base).names) (hnb : z ∉ (universalBodyAt b bb base).names)
    (hforward : KDerivation (imp
      (replace (universalName a ab) z
        (scopedFormula (n+1) a (Fin.snoc ab (universalName a ab)))).encode
      (replace (universalName b bb) z
        (scopedFormula (m+1) b (Fin.snoc bb (universalName b bb)))).encode))
    (hbackward : KDerivation (imp
      (replace (universalName b bb) z
        (scopedFormula (m+1) b (Fin.snoc bb (universalName b bb)))).encode
      (replace (universalName a ab) z
        (scopedFormula (n+1) a (Fin.snoc ab (universalName a ab)))).encode)) :
    KDerivation (imp (scopedFormula n (.all a) ab).encode
      (scopedFormula m (.all b) bb).encode) ×
    KDerivation (imp (scopedFormula m (.all b) bb).encode
      (scopedFormula n (.all a) ab).encode) := by
  have ra := universal_rebase_guard a ab base (by omega)
  have rb := universal_rebase_guard b bb base (by omega)
  have aa := high_universal_alpha a ab base z hbasea hza hna
  have ba := high_universal_alpha b bb base z hbaseb hzb hnb
  have hf := allCongr z (implicationCongr (identity (domainAt base z).encode) hforward)
  have hr := allCongr z (implicationCongr (identity (domainAt base z).encode) hbackward)
  exact ⟨compose ra.1 (compose aa.forward (compose hf (compose ba.backward rb.2))),
    compose rb.1 (compose ba.forward (compose hr (compose aa.backward ra.2)))⟩

/-- The enclosing name is not bound within the generated body. -/
theorem universalName_not_body_binder {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat) :
    universalName body bound ∉ (universalBody body bound).binders := by
  let x := universalName body bound
  change x ∉ (Formula.imp (domainAt (x+1) x)
    (scopedFormula (n+1) body (Fin.snoc bound x))).binders
  simp only [Formula.binders, Finset.mem_union, not_or]
  constructor
  · intro h
    have hp := domainAt_private (x+1) x x h
    omega
  · have hn := active_not_binder body (Fin.snoc bound x) (Fin.last n)
    simpa using hn

/-- A canonical name outside both the body and its enclosing binder. -/
def universalFresh {n : Nat} (body : Peano.language.BoundedFormula Nat (n+1))
    (bound : Fin n → Nat) : Nat :=
  max ((universalBody body bound).names.sup id) (universalName body bound) + 1

theorem universalName_lt_fresh {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat) :
    universalName body bound < universalFresh body bound := by
  unfold universalFresh
  omega

theorem universalFresh_not_body_names {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat) :
    universalFresh body bound ∉ (universalBody body bound).names := by
  intro h
  have hl : universalFresh body bound ≤ (universalBody body bound).names.sup id := by
    simpa using (Finset.le_sup (f := id) h)
  unfold universalFresh at *
  omega

/-- Move an actual generated universal to any supplied name absent from its
whole body. The target can be chosen jointly with another universal. -/
def universal_to_name {n : Nat} (body : Peano.language.BoundedFormula Nat (n+1))
    (bound : Fin n → Nat) (z : Nat)
    (hne : universalName body bound ≠ z)
    (hz : z ∉ (universalBody body bound).names) :
    ProofEquiv (scopedFormula n (.all body) bound)
      (.all z (replace (universalName body bound) z (universalBody body bound))) := by
  change ProofEquiv (.all (universalName body bound) (universalBody body bound)) _
  exact ProofEquiv.alphaAll _ _ _ hne (universalName_not_body_binder body bound) hz

/-- Construct both finite K alpha directions for the actual generated
universal, moving its binder above every name of its guarded body. -/
def universal_to_fresh {n : Nat} (body : Peano.language.BoundedFormula Nat (n+1))
    (bound : Fin n → Nat) :
    ProofEquiv (scopedFormula n (.all body) bound)
      (.all (universalFresh body bound)
        (replace (universalName body bound) (universalFresh body bound)
          (universalBody body bound))) := by
  exact universal_to_name body bound (universalFresh body bound)
    (Nat.ne_of_lt (universalName_lt_fresh body bound)) (universalFresh_not_body_names body bound)

/-- Align two generated universals after their guarded bodies have been
translated to the same fresh binder. Both body implications are explicit
finite K proof inputs; this does not construct their alignment. -/
def universals_of_common_body {n m : Nat}
    (a : Peano.language.BoundedFormula Nat (n+1)) (ab : Fin n → Nat)
    (b : Peano.language.BoundedFormula Nat (m+1)) (bb : Fin m → Nat) (z : Nat)
    (hza : universalName a ab ≠ z) (hzb : universalName b bb ≠ z)
    (hna : z ∉ (universalBody a ab).names) (hnb : z ∉ (universalBody b bb).names)
    (hforward : KDerivation (imp
      (replace (universalName a ab) z (universalBody a ab)).encode
      (replace (universalName b bb) z (universalBody b bb)).encode))
    (hbackward : KDerivation (imp
      (replace (universalName b bb) z (universalBody b bb)).encode
      (replace (universalName a ab) z (universalBody a ab)).encode)) :
    KDerivation (imp (scopedFormula n (.all a) ab).encode
      (scopedFormula m (.all b) bb).encode) ×
    KDerivation (imp (scopedFormula m (.all b) bb).encode
      (scopedFormula n (.all a) ab).encode) := by
  have ha := universal_to_name a ab z hza hna
  have hb := universal_to_name b bb z hzb hnb
  exact ⟨CompactDerivations.compose ha.forward
      (CompactDerivations.compose (CompactDerivations.allCongr z hforward) hb.backward),
    CompactDerivations.compose hb.forward
      (CompactDerivations.compose (CompactDerivations.allCongr z hbackward) ha.backward)⟩

theorem universal_to_fresh_forward_certificate {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat) :
    theoremCode (certificate (universal_to_fresh body bound).forward) =
      imp (scopedFormula n (.all body) bound).encode
        (Formula.all (universalFresh body bound)
          (replace (universalName body bound) (universalFresh body bound)
            (universalBody body bound))).encode := certificate_correct _

theorem universal_to_fresh_backward_certificate {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat) :
    theoremCode (certificate (universal_to_fresh body bound).backward) =
      imp (Formula.all (universalFresh body bound)
          (replace (universalName body bound) (universalFresh body bound)
            (universalBody body bound))).encode
        (scopedFormula n (.all body) bound).encode := certificate_correct _

end PASoundness.PAtoCompactVacuousUniversal

#print axioms PASoundness.PAtoCompactVacuousUniversal.active_not_binder
#print axioms PASoundness.PAtoCompactVacuousUniversal.universal_rebase_guard
#print axioms PASoundness.PAtoCompactVacuousUniversal.replace_domainAt
#print axioms PASoundness.PAtoCompactVacuousUniversal.universalName_not_high_body_binder
#print axioms PASoundness.PAtoCompactVacuousUniversal.high_universal_alpha
#print axioms PASoundness.PAtoCompactVacuousUniversal.universals_of_common_child
#print axioms PASoundness.PAtoCompactVacuousUniversal.universalName_not_body_binder
#print axioms PASoundness.PAtoCompactVacuousUniversal.universal_to_name
#print axioms PASoundness.PAtoCompactVacuousUniversal.universal_to_fresh
#print axioms PASoundness.PAtoCompactVacuousUniversal.universals_of_common_body
#print axioms PASoundness.PAtoCompactVacuousUniversal.universal_to_fresh_forward_certificate
#print axioms PASoundness.PAtoCompactVacuousUniversal.universal_to_fresh_backward_certificate
