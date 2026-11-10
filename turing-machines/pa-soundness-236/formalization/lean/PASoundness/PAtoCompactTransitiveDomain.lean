import PASoundness.PAtoCompactTransitiveClosure

/-! K successor closure for the definable one-level transitive-member
fragment. It does not establish least/greatest subset properties, extensional
uniqueness, a PA domain, or induction. Compact code 1 is literally
`member 0 0`; ordinary falsity is model-dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactTransitiveDomain
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Every immediate member of x satisfies the displayed transitivity code. -/
def membersTransitiveCode (x b p q : Nat) : Nat :=
  allCode b (imp (member x b) (transitiveCode b p q))

def oneLevelTransitiveCode (x b p q : Nat) : Nat :=
  both (transitiveCode x p q) (membersTransitiveCode x b p q)

def namedTransitive (x p q : Nat) : CompactNamed.Formula :=
  .all p (.all q (transitiveBody x p q))

def namedMembersTransitive (x b p q : Nat) : CompactNamed.Formula :=
  .all b (.imp (.member x b) (namedTransitive b p q))

/-- Instantiate the explicit every-member-transitive condition. -/
def member_transitive_instance (x b p q v : Nat)
    (hbx : b ≠ x) (hbv : b ≠ v) (hbp : b ≠ p) (hbq : b ≠ q)
    (hvp : v ≠ p) (hvq : v ≠ q) :
    KDerivation (imp (membersTransitiveCode x b p q)
      (imp (member x v) (transitiveCode v p q))) := by
  let f : CompactNamed.Formula := .imp (.member x b) (namedTransitive b p q)
  have h := CompactNamed.universalInstance b v f hbv
    (by simp [f, namedTransitive, transitiveBody, CompactNamed.Formula.binders, hbp, hbq])
    (by simp [f, namedTransitive, transitiveBody, CompactNamed.Formula.binders, hvp, hvq])
  simpa [f, membersTransitiveCode, namedTransitive, transitiveBody, transitiveCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    hbx, hbv, hbp, hbq, hvp, hvq, Ne.symm hbx, Ne.symm hbv, Ne.symm hbp,
    Ne.symm hbq, Ne.symm hvp, Ne.symm hvq] using h

/-- Equality transports transitivity in K, with both names distinct from the
transitivity formula's bound labels. No extensionality axiom is used. -/
def transitive_equal_transport (v x p q : Nat)
    (hvp : v ≠ p) (hvq : v ≠ q) (hxp : x ≠ p) (hxq : x ≠ q) :
    KDerivation (imp (equal v x) (imp (transitiveCode x p q) (transitiveCode v p q))) := by
  let f := namedTransitive v p q
  have h := (CompactNamed.equalityReplace v x f
    (by simp [f, namedTransitive, transitiveBody, CompactNamed.Formula.binders, hvp, hvq])
    (by simp [f, namedTransitive, transitiveBody, CompactNamed.Formula.binders, hxp, hxq])).2
  simpa [f, namedTransitive, transitiveBody, transitiveCode, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, hvp, hvq, hxp, hxq,
    Ne.symm hvp, Ne.symm hvq, Ne.symm hxp, Ne.symm hxq] using h

/-- Fresh-name vacuity for the one-level member condition. -/
def members_transitive_vacuity (x b p q v : Nat)
    (hvx : v ≠ x) (hvb : v ≠ b) (hvp : v ≠ p) (hvq : v ≠ q) :
    KDerivation (imp (membersTransitiveCode x b p q) (allCode v (membersTransitiveCode x b p q))) := by
  let f := namedMembersTransitive x b p q
  have hv : v ∉ f.names := by
    simp [f, namedMembersTransitive, namedTransitive, transitiveBody, CompactNamed.Formula.names,
      hvx, hvb, hvp, hvq]
  have h := f.vacuity v hv
  simpa [f, namedMembersTransitive, namedTransitive, transitiveBody, membersTransitiveCode,
    transitiveCode, CompactNamed.Formula.encode] using h

/-- A successor of a transitive set whose members are transitive also has
only transitive immediate members. This is literal K proof data under the
explicit graphs and pairwise fresh syntax names. -/
def successor_members_transitive (x y w b p q v : Nat)
    (fresh : [x,y,w,b,p,q,v].Nodup) :
    KDerivation (imp (transitiveCode x p q) (imp (membersTransitiveCode x b p q)
      (imp (successorCode x y w) (membersTransitiveCode y v p q)))) := by
  have hwx : w ≠ x := by intro h; subst w; simp at fresh
  have hwy : w ≠ y := by intro h; subst w; simp at fresh
  have hwv : w ≠ v := by intro h; subst w; simp at fresh
  have hbx : b ≠ x := by intro h; subst b; simp at fresh
  have hbv : b ≠ v := by intro h; subst b; simp at fresh
  have hbp : b ≠ p := by intro h; subst b; simp at fresh
  have hbq : b ≠ q := by intro h; subst b; simp at fresh
  have hvx : v ≠ x := by intro h; subst v; simp at fresh
  have hvy : v ≠ y := by intro h; subst v; simp at fresh
  have hvw : v ≠ w := by intro h; subst v; simp at fresh
  have hvb : v ≠ b := by intro h; subst v; simp at fresh
  have hvp : v ≠ p := by intro h; subst v; simp at fresh
  have hvq : v ≠ q := by intro h; subst v; simp at fresh
  have hxp : x ≠ p := by intro h; subst p; simp at fresh
  have hxq : x ≠ q := by intro h; subst q; simp at fresh
  let T := transitiveCode x p q
  let M := membersTransitiveCode x b p q
  let S := successorCode x y w
  let Γ := [S,M,T]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (member y v) (transitiveCode v p q)) := by
    apply Context.deduction
    have hv : Context (member y v :: Γ) (member y v) := Context.head Γ _
    have hsplit : Context (member y v :: Γ) (either (equal v x) (member x v)) :=
      .mp hv (.mp (Context.under hs (member y v)) (.closed (successor_inspect x y w v hwx hwy hwv)))
    apply Context.disjunctionElim hsplit
    · have he : Context (equal v x :: member y v :: Γ) (equal v x) := Context.head _ _
      exact .mp (Context.under (Context.under ht (member y v)) (equal v x))
        (.mp he (.closed (transitive_equal_transport v x p q hvp hvq hxp hxq)))
    · have hxv : Context (member x v :: member y v :: Γ) (member x v) := Context.head _ _
      exact .mp hxv (.mp (Context.under (Context.under hm (member y v)) (member x v))
        (.closed (member_transitive_instance x b p q v hbx hbv hbp hbq hvp hvq)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = S
    · subst h
      exact successor_vacuity x y w v hvx hvy hvw
    · by_cases h2 : h = M
      · subst h
        exact members_transitive_vacuity x b p q v hvx hvb hvp hvq
      · have h3 : h = T := (hh.resolve_left h1).resolve_left h2
        subst h
        exact transitive_vacuity x p q v hvx hvp hvq
  have hout : Context Γ (membersTransitiveCode y v p q) := Context.generalize v hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hout

/-- Successor closure for the explicit transitive/one-level-member fragment.
Fresh labels r,s represent the output's outer transitivity quantifiers; its
member-transitivity quantifiers retain p,q. Thus the output is the same
mathematical shape with explicitly displayed, potentially different binder
labels, rather than a claim of a single closed PA-domain predicate. -/
def successor_one_level_transitive (x y w b p q v r s : Nat)
    (fresh : [x,y,w,b,p,q,v,r,s].Nodup) :
    KDerivation (imp (oneLevelTransitiveCode x b p q) (imp (successorCode x y w)
      (both (transitiveCode y r s) (membersTransitiveCode y v p q)))) := by
  have hwx : w ≠ x := by intro h; subst w; simp at fresh
  have hwy : w ≠ y := by intro h; subst w; simp at fresh
  have hpx : p ≠ x := by intro h; subst p; simp at fresh
  have hpq : p ≠ q := by intro h; subst p; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hf : ∀ t ∈ [r,s], ∀ z ∈ [x,y,w,p,q], t ≠ z := by
    intro a ha z hz he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hz
    rcases ha with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl | rfl <;> subst a <;> simp at fresh
  have h7 : [x,y,w,b,p,q,v].Nodup := by
    exact List.Nodup.sublist (List.sublist_append_left [x,y,w,b,p,q,v] [r,s]) fresh
  have hOuter := successor_transitive_closed x y w p q r s hwx hwy hpx hpq hqx hf
  have hMembers := successor_members_transitive x y w b p q v h7
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode x y w, oneLevelTransitiveCode x b p q]
  have hs : Context Γ (successorCode x y w) := .hypothesis (by simp [Γ])
  have hd : Context Γ (oneLevelTransitiveCode x b p q) := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode x p q) := Context.conjunctionLeft hd
  have hm : Context Γ (membersTransitiveCode x b p q) := Context.conjunctionRight hd
  have hy : Context Γ (transitiveCode y r s) := .mp hs (.mp ht (.closed hOuter))
  have hyMembers : Context Γ (membersTransitiveCode y v p q) := .mp hs (.mp hm (.mp ht (.closed hMembers)))
  exact Context.conjunctionIntro hy hyMembers

theorem successor_one_level_transitive_certificate (x y w b p q v r s : Nat)
    (fresh : [x,y,w,b,p,q,v,r,s].Nodup) :
    theoremCode (certificate (successor_one_level_transitive x y w b p q v r s fresh)) =
      imp (oneLevelTransitiveCode x b p q) (imp (successorCode x y w)
        (both (transitiveCode y r s) (membersTransitiveCode y v p q))) :=
  certificate_correct (successor_one_level_transitive x y w b p q v r s fresh)

/-- Every immediate member of a standard finite ordinal is itself transitive.
This semantic fact is independent of the K construction above. -/
theorem ordinal_members_transitive (x b p q n : Nat) (ρ : CompactMatrix.Environment)
    (hxb : x ≠ b) (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q)
    (hx : ρ x = (HFCoding.ordinal n).code) :
    (CompactMatrix.decode (membersTransitiveCode x b p q)).Realize ρ := by
  simp only [membersTransitiveCode, CompactSemantics.realize_all, CompactSemantics.realize_imp,
    CompactSemantics.realize_member]
  intro v hv
  have hv' : (⟨v⟩ : HFCoding.Object) ∈ HFCoding.ordinal n := by
    change CompactMatrix.bit (HFCoding.ordinal n).code v = true
    simpa only [CompactSemantics.update_same, CompactSemantics.update_other ρ b x v hxb, hx] using hv
  obtain ⟨i, _, hi⟩ := (HFCoding.mem_ordinal ⟨v⟩ n).mp hv'
  apply ordinal_transitive_true b p q i (CompactMatrix.update ρ b v) hbp hbq hpq
  simpa only [CompactSemantics.update_same] using congrArg HFCoding.Object.code hi

/-- Finite ordinals satisfy the displayed one-level fragment in standard HF
semantics; this does not prove closure of least/greatest subset properties. -/
theorem ordinal_one_level_transitive (x b p q n : Nat) (ρ : CompactMatrix.Environment)
    (hxb : x ≠ b) (hxp : x ≠ p) (hxq : x ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q)
    (hx : ρ x = (HFCoding.ordinal n).code) :
    (CompactMatrix.decode (oneLevelTransitiveCode x b p q)).Realize ρ := by
  rw [oneLevelTransitiveCode, CompactSemantics.realize_both]
  exact ⟨ordinal_transitive_true x p q n ρ hxp hxq hpq hx,
    ordinal_members_transitive x b p q n ρ hxb hbp hbq hpq hx⟩

end PASoundness.PAtoCompactTransitiveDomain
