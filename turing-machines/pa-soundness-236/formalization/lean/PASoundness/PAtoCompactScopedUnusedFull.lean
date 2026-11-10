import PASoundness.PAtoCompactScopedActiveAll
import PASoundness.PAtoCompactScopedUnusedLevel

namespace PASoundness.PAtoCompactScopedUnusedFull

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactScopedAlphaInvariant PASoundness.PAtoCompactVacuousQuantifierFree

/-- A frame depends on its name map only for variables occurring in its terms. -/
theorem frame_name_agree {α : Type} [DecidableEq α]
    (t u : Peano.language.Term α) (v w : α → Nat) (base : Nat)
    (ht : ∀ a ∈ t.varFinset, v a = w a)
    (hu : ∀ a ∈ u.varFinset, v a = w a) :
    equalityFrame v t u base = equalityFrame w t u base := by
  unfold equalityFrame
  rw [termGraph_name_agree t v w ht, termGraph_name_agree u v w hu]

/-- Relabeling the source terms and changing their name map preserves the
entire equality frame if names agree on occurring variables. -/
theorem frame_relabel_name_agree {α β : Type} [DecidableEq α]
    (t u : Peano.language.Term α) (r : α → β) (v : α → Nat) (w : β → Nat) (base : Nat)
    (ht : ∀ a ∈ t.varFinset, v a = w (r a))
    (hu : ∀ a ∈ u.varFinset, v a = w (r a)) :
    equalityFrame w (t.relabel r) (u.relabel r) base = equalityFrame v t u base := by
  rw [frame_relabel]
  exact (frame_name_agree t u v (w ∘ r) base ht hu).symm

/-- K alignment of equality frames for matching names and independently
allocated bases, including different source variable types. -/
noncomputable def paired_frame_relabel {α β : Type} [DecidableEq α]
    (t u : Peano.language.Term α) (r : α → β) (v : α → Nat) (w : β → Nat) (b c : Nat)
    (ht : ∀ a ∈ t.varFinset, v a = w (r a))
    (hu : ∀ a ∈ u.varFinset, v a = w (r a))
    (htb : ∀ a ∈ t.varFinset, v a < b) (hub : ∀ a ∈ u.varFinset, v a < b)
    (htc : ∀ a ∈ t.varFinset, w (r a) < c) (huc : ∀ a ∈ u.varFinset, w (r a) < c) :
    KBoth (equalityFrame v t u b) (equalityFrame w (t.relabel r) (u.relabel r) c) := by
  rw [frame_relabel_name_agree t u r v w c ht hu]
  exact equalityFrame_base_transport v t u b c htb hub
    (by intro a ha; rw [ht a ha]; exact htc a ha)
    (by intro a ha; rw [hu a ha]; exact huc a ha)

/-- Equality scopes at different depths align if their source-variable maps
agree on occurring variables and the target names fit the target allocation. -/
noncomputable def paired_scoped_equal {n m : Nat}
    (t u : Peano.language.Term (Nat ⊕ Fin n)) (r : Nat ⊕ Fin n → Nat ⊕ Fin m)
    (b : Fin n → Nat) (c : Fin m → Nat)
    (ht : ∀ a ∈ t.varFinset, Sum.elim id b a = Sum.elim id c (r a))
    (hu : ∀ a ∈ u.varFinset, Sum.elim id b a = Sum.elim id c (r a))
    (htb : ∀ a ∈ t.varFinset, Sum.elim id b a < scopeBase (.equal t u) b)
    (hub : ∀ a ∈ u.varFinset, Sum.elim id b a < scopeBase (.equal t u) b)
    (htc : ∀ a ∈ t.varFinset, Sum.elim id c (r a) < scopeBase (.equal (t.relabel r) (u.relabel r)) c)
    (huc : ∀ a ∈ u.varFinset, Sum.elim id c (r a) < scopeBase (.equal (t.relabel r) (u.relabel r)) c) :
    KBoth (scopedFormula n (.equal t u) b)
      (scopedFormula m (.equal (t.relabel r) (u.relabel r)) c) := by
  rw [scoped_equal_frame, scoped_equal_frame]
  exact paired_frame_relabel t u r (Sum.elim id b) (Sum.elim id c) _ _ ht hu htb hub htc huc

end PASoundness.PAtoCompactScopedUnusedFull

namespace PASoundness.PAtoCompactScopedUnusedFull
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedUnusedLevel
open PASoundness.PAtoCompactScopedActiveAll PASoundness.PAtoCompactVacuousUniversal
open PASoundness.PAtoCompactVacuousUniversalFresh PASoundness.PAtoCompactVacuousQuantifierFree

/-- Uniform unused-level insertion for a body; the inserted name is arbitrary. -/
def InsertIH {n : Nat} (body : Peano.language.BoundedFormula Nat n) : Type :=
  ∀ (x z : Nat) (bound : Fin n → Nat), x ∉ body.freeVarFinset →
    KBoth (scopedFormula n body bound)
      (scopedFormula (1+n) (body.relabel (bindName x))
        (Fin.append (fun _ : Fin 1 => z) bound))

/-- The universal constructor, conditional only on the body induction
hypothesis. A common alpha binder is selected above both child name sets. -/
noncomputable def unused_universal_step {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (ih : InsertIH body)
    (x z : Nat) (bound : Fin n → Nat)
    (hx : x ∉ (.all body : Peano.language.BoundedFormula Nat n).freeVarFinset) :
    KBoth (scopedFormula n (.all body) bound)
      (scopedFormula (1+n) ((.all body : Peano.language.BoundedFormula Nat n).relabel (bindName x))
        (Fin.append (fun _ : Fin 1 => z) bound)) := by
  let ext : Fin (1+n) → Nat := Fin.append (fun _ : Fin 1 => z) bound
  let rb : Peano.language.BoundedFormula Nat ((1+n)+1) := body.relabel (bindName x)
  let p := universalName body bound
  let q := universalName rb ext
  let v := commonName body bound rb ext
  let F := scopedFormula (n+1) body (Fin.snoc bound p)
  let G := scopedFormula ((1+n)+1) rb (Fin.snoc ext q)
  have hpv : p < v := by dsimp [v, commonName, p, q]; omega
  have hqv : q < v := by dsimp [v, commonName, p, q]; omega
  have hvF : v ∉ F.names := by
    intro h
    have hs : v ≤ (F.names ∪ G.names).sup id := Finset.le_sup (f := id) (Finset.mem_union_left _ h)
    dsimp [v, commonName, p, q, F, G] at hs
    omega
  have hvG : v ∉ G.names := by
    intro h
    have hs : v ≤ (F.names ∪ G.names).sup id := Finset.le_sup (f := id) (Finset.mem_union_right _ h)
    dsimp [v, commonName, p, q, F, G] at hs
    omega
  have hpFree : p ∉ body.freeVarFinset := by
    intro h
    have h' : p ∈ (.all body : Peano.language.BoundedFormula Nat n).freeVarFinset := by simpa using h
    have ht := free_lt_scopeBase (.all body) bound p h'
    dsimp [p, universalName] at ht
    omega
  have hqFree : q ∉ rb.freeVarFinset := by
    intro h
    have h' : q ∈ (.all rb : Peano.language.BoundedFormula Nat (1+n)).freeVarFinset := by simpa using h
    have ht := free_lt_scopeBase (.all rb) ext q h'
    dsimp [q, universalName] at ht
    omega
  have leftRaw := scoped_active_replace body (Fin.snoc bound p) (Fin.last n) v
    (by simpa using hpFree) (by simpa using hpv) (by simpa [F] using hvF)
  have rightRaw := scoped_active_replace rb (Fin.snoc ext q) (Fin.last (1+n)) v
    (by simpa using hqFree) (by simpa using hqv) (by simpa [G] using hvG)
  have hboundp : ∀ j, bound j ≠ p := by
    intro j
    exact Nat.ne_of_lt (show bound j < p from bound_lt_scopeBase (.all body) bound j)
  have hboundq : ∀ j, ext j ≠ q := by
    intro j
    exact Nat.ne_of_lt (show ext j < q from bound_lt_scopeBase (.all rb) ext j)
  have envp := rename_snoc_nonhit bound p v hboundp
  have envq := rename_snoc_nonhit ext q v hboundq
  have left : KBoth (replace p v F) (scopedFormula (n+1) body (Fin.snoc bound v)) := by
    simpa [F, envp] using leftRaw
  have right : KBoth (replace q v G) (scopedFormula ((1+n)+1) rb (Fin.snoc ext v)) := by
    simpa [G, envq] using rightRaw
  have hxBody : x ∉ body.freeVarFinset := by simpa using hx
  have middle := ih x z (Fin.snoc bound v) hxBody
  rw [Fin.append_snoc] at middle
  have middle' : KBoth (scopedFormula (n+1) body (Fin.snoc bound v))
      (scopedFormula ((1+n)+1) rb (Fin.snoc ext v)) := by
    exact middle
  have childF := compose left.1 (compose middle'.1 right.2)
  have childB := compose right.1 (compose middle'.2 left.2)
  have result := universals_of_common_child_auto body bound rb ext childF childB
  simpa [KBoth, BoundedFormula.relabel_all, rb, ext, Nat.add_assoc] using result

#print axioms PASoundness.PAtoCompactScopedUnusedFull.unused_universal_step
end PASoundness.PAtoCompactScopedUnusedFull

namespace PASoundness.PAtoCompactScopedUnusedFull
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedUnusedLevel
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactEqualityGraphTruth
open PASoundness.PAtoCompactVacuousQuantifierFree

/-- Unused-level insertion at an equality node, including changing allocation
bases. The extra label may duplicate any existing label. -/
noncomputable def unused_equal {n : Nat}
    (t u : Peano.language.Term (Nat ⊕ Fin n)) (x z : Nat) (bound : Fin n → Nat)
    (hx : x ∉ (.equal t u : Peano.language.BoundedFormula Nat n).freeVarFinset) :
    KBoth (scopedFormula n (.equal t u) bound)
      (scopedFormula (1+n) ((.equal t u : Peano.language.BoundedFormula Nat n).relabel (bindName x))
        (Fin.append (fun _ : Fin 1 => z) bound)) := by
  let ext : Fin (1+n) → Nat := Fin.append (fun _ : Fin 1 => z) bound
  let r := BoundedFormula.relabelAux (bindName x) n
  have ht : Sum.inl x ∉ t.varFinset := by
    intro h
    apply hx
    change x ∈ t.varFinsetLeft ∪ u.varFinsetLeft
    exact Finset.mem_union_left _ (inl_mem_left t x h)
  have hu : Sum.inl x ∉ u.varFinset := by
    intro h
    apply hx
    change x ∈ t.varFinsetLeft ∪ u.varFinsetLeft
    exact Finset.mem_union_right _ (inl_mem_left u x h)
  have heqT := inserted_term_name_agree t x z bound ht
  have heqU := inserted_term_name_agree u x z bound hu
  have hbase : scopeBase (.equal (t.relabel r) (u.relabel r)) ext =
      max (scopeBase (.equal t u) bound) (z+1) := by
    change scopeBase ((.equal t u : Peano.language.BoundedFormula Nat n).relabel (bindName x))
      (Fin.append (fun _ : Fin 1 => z) bound) = _
    exact inserted_scopeBase (.equal t u) x z bound hx
  change KBoth (scopedFormula n (.equal t u) bound)
    (scopedFormula (1+n) (.equal (t.relabel r) (u.relabel r)) ext)
  apply paired_scoped_equal t u r bound ext
  · intro a ha
    exact (heqT a ha).symm
  · intro a ha
    exact (heqU a ha).symm
  · exact eq_left_name_lt t u bound
  · exact eq_right_name_lt t u bound
  · intro a ha
    change (Sum.elim id ext ∘ r) a < _
    rw [heqT a ha, hbase]
    have h := eq_left_name_lt t u bound a ha
    omega
  · intro a ha
    change (Sum.elim id ext ∘ r) a < _
    rw [heqU a ha, hbase]
    have h := eq_right_name_lt t u bound a ha
    omega

#print axioms PASoundness.PAtoCompactScopedUnusedFull.unused_equal
end PASoundness.PAtoCompactScopedUnusedFull

namespace PASoundness.PAtoCompactScopedUnusedFull
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedUnusedLevel
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedVacuousAxiom
open PASoundness.PAtoCompactGuardedGeneralizationAlignment

/-- Inserting a source bound level that is not used by the formula preserves
its generated scoped formula up to finite K proof, at any depth and with any
inserted name (including aliases of existing active names). -/
noncomputable def scoped_unused {n : Nat}
    (φ : Peano.language.BoundedFormula Nat n) : InsertIH φ := by
  induction φ with
  | falsum =>
      intro x z bound hx
      exact ⟨identity 1, identity 1⟩
  | equal t u =>
      intro x z bound hx
      exact unused_equal t u x z bound hx
  | rel r ts => exact nomatch r
  | imp a b ia ib =>
      intro x z bound hx
      have hxa : x ∉ a.freeVarFinset := by
        intro h; apply hx; simp [BoundedFormula.freeVarFinset, h]
      have hxb : x ∉ b.freeVarFinset := by
        intro h; apply hx; simp [BoundedFormula.freeVarFinset, h]
      have da := ia x z bound hxa
      have db := ib x z bound hxb
      change KBoth (.imp (scopedFormula _ a bound) (scopedFormula _ b bound))
        (.imp (scopedFormula _ (a.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => z) bound))
          (scopedFormula _ (b.relabel (bindName x)) (Fin.append (fun _ : Fin 1 => z) bound)))
      exact ⟨implicationCongr da.2 db.1, implicationCongr da.1 db.2⟩
  | all body ih =>
      exact unused_universal_step body ih

/-- The entire guarded vacuous logical axiom family has finite K proofs.
The source variable must be absent from the source formula's free variables. -/
noncomputable def vacuous_all (φ : Peano.Formula) (x : Nat) (hx : x ∉ φ.freeVarFinset) :
    KDerivation (guardedCode (φ.imp (FOL.allAt x φ))) := by
  apply vacuous_of_body_alignment φ x hx
  have eqenv : (Fin.append (fun _ : Fin 1 => topName x φ) (Fin.elim0 : Fin 0 → Nat)) =
      Fin.snoc Fin.elim0 (topName x φ) := by
    funext i
    fin_cases i
    rfl
  have h := scoped_unused φ x (topName x φ) Fin.elim0 hx
  change KDerivation (imp (scopedFormula 0 φ Fin.elim0).encode
    (scopedFormula 1 (BoundedFormula.relabel (bindName x) φ) (Fin.snoc Fin.elim0 (topName x φ))).encode)
  simpa only [Nat.add_zero, eqenv] using h.1

theorem vacuous_all_certificate (φ : Peano.Formula) (x : Nat) (hx : x ∉ φ.freeVarFinset) :
    theoremCode (certificate (vacuous_all φ x hx)) =
      guardedCode (φ.imp (FOL.allAt x φ)) := certificate_correct _

#print axioms PASoundness.PAtoCompactScopedUnusedFull.scoped_unused
#print axioms PASoundness.PAtoCompactScopedUnusedFull.vacuous_all
#print axioms PASoundness.PAtoCompactScopedUnusedFull.vacuous_all_certificate
end PASoundness.PAtoCompactScopedUnusedFull
