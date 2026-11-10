import PASoundness.PAtoCompactTransitiveDomain

/-! Constructive K member and predecessor closure for the one-level
transitive-member fragment. Least/greatest subset closure, uniqueness,
induction and a full PA interpretation are not asserted. Code 1 is literally
`member 0 0`; its ordinary falsity reading is model-dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPredecessorDomain
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveDomain

/-- Every member of a transitive set whose members are transitive again has
the one-level transitive-member fragment. All six syntax names are distinct;
no extensionality or semantic-soundness premise is used. -/
def member_one_level_transitive (x m b p q v : Nat)
    (fresh : [x,m,b,p,q,v].Nodup) :
    KDerivation (imp (oneLevelTransitiveCode x b p q) (imp (member x m)
      (oneLevelTransitiveCode m v p q))) := by
  have hbx : b ≠ x := by intro h; subst b; simp at fresh
  have hbm : b ≠ m := by intro h; subst b; simp at fresh
  have hbv : b ≠ v := by intro h; subst b; simp at fresh
  have hbp : b ≠ p := by intro h; subst b; simp at fresh
  have hbq : b ≠ q := by intro h; subst b; simp at fresh
  have hmp : m ≠ p := by intro h; subst m; simp at fresh
  have hmq : m ≠ q := by intro h; subst m; simp at fresh
  have hpx : p ≠ x := by intro h; subst p; simp at fresh
  have hpm : p ≠ m := by intro h; subst p; simp at fresh
  have hpq : p ≠ q := by intro h; subst p; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hqm : q ≠ m := by intro h; subst q; simp at fresh
  have hqv : q ≠ v := by intro h; subst q; simp at fresh
  have hvx : v ≠ x := by intro h; subst v; simp at fresh
  have hvm : v ≠ m := by intro h; subst v; simp at fresh
  have hvb : v ≠ b := by intro h; subst v; simp at fresh
  have hvp : v ≠ p := by intro h; subst v; simp at fresh
  have hvq : v ≠ q := by intro h; subst v; simp at fresh
  let D := oneLevelTransitiveCode x b p q
  let X := member x m
  let Γ := [X,D]
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode x p q) := Context.conjunctionLeft hd
  have hm : Context Γ (membersTransitiveCode x b p q) := Context.conjunctionRight hd
  have htm : Context Γ (transitiveCode m p q) := .mp hx (.mp hm
    (.closed (member_transitive_instance x b p q m hbx hbm hbp hbq hmp hmq)))
  have hpoint : Context Γ (imp (member m v) (transitiveCode v p q)) := by
    apply Context.deduction
    have hmv : Context (member m v :: Γ) (member m v) := Context.head Γ _
    have hxv : Context (member m v :: Γ) (member x v) := .mp hmv
      (.mp (Context.under hx (member m v)) (.mp (Context.under ht (member m v))
        (.closed (transitive_chain x p q m v hpx hpm hpq hqx hqm hqv))))
    exact .mp hxv (.mp (Context.under hm (member m v))
      (.closed (member_transitive_instance x b p q v hbx hbv hbp hbq hvp hvq)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = X
    · subst h
      exact membershipVacuity x m v hvx hvm
    · have he' : h = D := hh.resolve_left he
      subst h
      let f := CompactNamed.Formula.imp
        (CompactNamed.Formula.imp (namedTransitive x p q) (.imp (namedMembersTransitive x b p q) .bottom)) .bottom
      have hf : v ∉ f.names := by
        simp [f, namedTransitive, namedMembersTransitive, transitiveBody,
          CompactNamed.Formula.names, hvx, hvb, hvp, hvq]
      have hh := f.vacuity v hf
      simpa [D, f, oneLevelTransitiveCode, namedTransitive, namedMembersTransitive,
        membersTransitiveCode, transitiveCode, transitiveBody, CompactNamed.Formula.encode,
        CompactProof.both, CompactProof.neg] using hh
  have hmembers : Context Γ (membersTransitiveCode m v p q) := Context.generalize v hv hpoint
  have hout : Context Γ (oneLevelTransitiveCode m v p q) := Context.conjunctionIntro htm hmembers
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hout

/-- An explicit successor graph makes its input m a member of x, so predecessor
closure follows from the member-closure theorem. -/
def predecessor_one_level_transitive (x m w b p q v : Nat)
    (fresh : [x,m,b,p,q,v].Nodup) (hwm : w ≠ m) (hwx : w ≠ x) :
    KDerivation (imp (oneLevelTransitiveCode x b p q) (imp (successorCode m x w)
      (oneLevelTransitiveCode m v p q))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode m x w, oneLevelTransitiveCode x b p q]
  have hs : Context Γ (successorCode m x w) := .hypothesis (by simp [Γ])
  have hd : Context Γ (oneLevelTransitiveCode x b p q) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member x m) := .mp hs (.closed (successor_contains_input m x w hwm hwx))
  exact .mp hm (.mp hd (.closed (member_one_level_transitive x m b p q v fresh)))

theorem predecessor_one_level_transitive_certificate (x m w b p q v : Nat)
    (fresh : [x,m,b,p,q,v].Nodup) (hwm : w ≠ m) (hwx : w ≠ x) :
    theoremCode (certificate (predecessor_one_level_transitive x m w b p q v fresh hwm hwx)) =
      imp (oneLevelTransitiveCode x b p q) (imp (successorCode m x w)
        (oneLevelTransitiveCode m v p q)) :=
  certificate_correct (predecessor_one_level_transitive x m w b p q v fresh hwm hwx)

/-- Separately, every member of a standard finite ordinal satisfies the
one-level fragment in standard HF semantics. -/
theorem ordinal_member_one_level_transitive (x m b p q v n : Nat)
    (ρ : CompactMatrix.Environment) (fresh : [x,m,b,p,q,v].Nodup)
    (hx : ρ x = (HFCoding.ordinal n).code)
    (hm : CompactMatrix.bit (ρ x) (ρ m) = true) :
    (CompactMatrix.decode (oneLevelTransitiveCode m v p q)).Realize ρ := by
  have hmv : m ≠ v := by intro h; subst m; simp at fresh
  have hmp : m ≠ p := by intro h; subst m; simp at fresh
  have hmq : m ≠ q := by intro h; subst m; simp at fresh
  have hvp : v ≠ p := by intro h; subst v; simp at fresh
  have hvq : v ≠ q := by intro h; subst v; simp at fresh
  have hpq : p ≠ q := by intro h; subst p; simp at fresh
  have hm' : (⟨ρ m⟩ : HFCoding.Object) ∈ HFCoding.ordinal n := by
    change CompactMatrix.bit (HFCoding.ordinal n).code (ρ m) = true
    simpa only [hx] using hm
  obtain ⟨i, _, hi⟩ := (HFCoding.mem_ordinal ⟨ρ m⟩ n).mp hm'
  exact ordinal_one_level_transitive m v p q i ρ hmv hmp hmq hvp hvq hpq
    (congrArg HFCoding.Object.code hi)

end PASoundness.PAtoCompactPredecessorDomain
