import PASoundness.PAtoCompactTransitiveSuccessor

/-! Constructive K transitivity closure for the explicit successor graph.
This does not establish witness totality, quotient extensionality or induction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactTransitiveClosure
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactTransitiveSuccessor

/-- The reverse direction of a successor graph, instantiated at q. -/
def successor_include (x y w q : Nat) (hwx : w ≠ x) (hwy : w ≠ y) (hwq : w ≠ q) :
    KDerivation (imp (successorCode x y w)
      (imp (either (equal q x) (member x q)) (member y q))) := by
  let body := namedSuccessorBody x y w
  have hinst := CompactNamed.universalInstance w q body hwq
    (by simp [body, namedSuccessorBody, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [body, namedSuccessorBody, namedBoth, namedEither, CompactNamed.Formula.binders])
  have hstep : KDerivation (imp (successorCode x y w)
      (both (imp (member y q) (either (equal q x) (member x q)))
        (imp (either (equal q x) (member x q)) (member y q)))) := by
    simpa [body, namedSuccessorBody, namedBoth, namedEither, successorCode,
      CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
      CompactProof.both, CompactProof.neg, CompactDerivations.either,
      hwx, hwy, hwq, Ne.symm hwx, Ne.symm hwy, Ne.symm hwq] using hinst
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionRight (.mp (Context.head [] (successorCode x y w)) (.closed hstep))

/-- Instantiate transitivity at any two named elements, with capture-safe
quantifier labels. -/
def transitive_chain (x p q a b : Nat)
    (hpx : p ≠ x) (hpa : p ≠ a) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqa : q ≠ a) (hqb : q ≠ b) :
    KDerivation (imp (transitiveCode x p q)
      (imp (member x a) (imp (member a b) (member x b)))) := by
  let body := transitiveBody x p q
  have hfirst := CompactNamed.universalInstance p a (.all q body) hpa
    (by simp [body, transitiveBody, CompactNamed.Formula.binders, hpq])
    (by simp [body, transitiveBody, CompactNamed.Formula.binders, Ne.symm hqa])
  have hfirst' : KDerivation (imp (transitiveCode x p q)
      (allCode q (imp (member x a) (imp (member a q) (member x q))))) := by
    simpa [transitiveCode, body, transitiveBody, CompactNamed.Formula.encode,
      CompactNamed.replace, CompactNamed.rename, hpx, hpa, hpq, hqx, hqa,
      Ne.symm hpx, Ne.symm hpa, Ne.symm hpq, Ne.symm hqx, Ne.symm hqa] using hfirst
  have hsecond := CompactNamed.universalInstance q b (transitiveBody x a q) hqb
    (by simp [transitiveBody, CompactNamed.Formula.binders])
    (by simp [transitiveBody, CompactNamed.Formula.binders])
  have hsecond' : KDerivation (imp (allCode q (imp (member x a) (imp (member a q) (member x q))))
      (imp (member x a) (imp (member a b) (member x b)))) := by
    simpa [transitiveBody, CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
      hqx, hqa, hqb, Ne.symm hqx, Ne.symm hqa, Ne.symm hqb] using hsecond
  exact compose hfirst' hsecond'

/-- One arbitrary-element transitivity step for the successor, proved with
literal K proof data. Names are kept explicit to avoid accidental capture. -/
def successor_transitive_pointwise (x y w p q a b : Nat)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwa : w ≠ a) (hwb : w ≠ b)
    (hpx : p ≠ x) (hpa : p ≠ a) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqa : q ≠ a) (hqb : q ≠ b) :
    KDerivation (imp (transitiveCode x p q) (imp (successorCode x y w)
      (imp (member y a) (imp (member a b) (member y b))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member a b, member y a, successorCode x y w, transitiveCode x p q]
  have hab : Context Γ (member a b) := .hypothesis (by simp [Γ])
  have hya : Context Γ (member y a) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode x y w) := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode x p q) := .hypothesis (by simp [Γ])
  have hsplit : Context Γ (either (equal a x) (member x a)) :=
    .mp hya (.mp hs (.closed (successor_inspect x y w a hwx hwy hwa)))
  have hback : Context Γ (imp (either (equal b x) (member x b)) (member y b)) :=
    .mp hs (.closed (successor_include x y w b hwx hwy hwb))
  have hcase : Context Γ (member x b) := by
    apply Context.disjunctionElim hsplit
    · have he : Context (equal a x :: Γ) (equal a x) := Context.head Γ (equal a x)
      exact .mp (Context.under hab (equal a x)) (.mp he (.closed (memberLeftEquality a x b)))
    · have hm : Context (member x a :: Γ) (member x a) := Context.head Γ (member x a)
      exact .mp (Context.under hab (member x a)) (.mp hm
        (.mp (Context.under ht (member x a))
          (.closed (transitive_chain x p q a b hpx hpa hpq hqx hqa hqb))))
  exact .mp (Context.disjunctionRight (a := equal b x) hcase) hback

/-- Fresh-name vacuity for the displayed transitivity formula. -/
def transitive_vacuity (x p q r : Nat) (hrx : r ≠ x) (hrp : r ≠ p) (hrq : r ≠ q) :
    KDerivation (imp (transitiveCode x p q) (allCode r (transitiveCode x p q))) := by
  let f : CompactNamed.Formula := .all p (.all q (transitiveBody x p q))
  have hr : r ∉ f.names := by
    simp [f, transitiveBody, CompactNamed.Formula.names, hrx, hrp, hrq]
  have h := f.vacuity r hr
  simpa [f, transitiveBody, transitiveCode, CompactNamed.Formula.encode] using h

/-- Fresh-name vacuity for the displayed successor graph. -/
def successor_vacuity (x y w r : Nat) (hrx : r ≠ x) (hry : r ≠ y) (hrw : r ≠ w) :
    KDerivation (imp (successorCode x y w) (allCode r (successorCode x y w))) := by
  let f : CompactNamed.Formula := .all w (namedSuccessorBody x y w)
  have hr : r ∉ f.names := by
    simp [f, namedSuccessorBody, namedBoth, namedEither, CompactNamed.Formula.names, hrx, hry, hrw]
  have h := f.vacuity r hr
  simpa [f, namedSuccessorBody, namedBoth, namedEither, successorCode, CompactNamed.Formula.encode,
    CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

/-- Constructive K transitivity closure: a successor witness for a transitive
input is transitive. The output binder names a,b do not occur
in either premise; p,q are distinct from x and each other. -/
def successor_transitive_closed (x y w p q a b : Nat)
    (hwx : w ≠ x) (hwy : w ≠ y) (hpx : p ≠ x) (hpq : p ≠ q) (hqx : q ≠ x)
    (hf : ∀ t ∈ [a,b], ∀ z ∈ [x,y,w,p,q], t ≠ z) :
    KDerivation (imp (transitiveCode x p q)
      (imp (successorCode x y w) (transitiveCode y a b))) := by
  have hax : a ≠ x := hf a (by simp) x (by simp)
  have hay : a ≠ y := hf a (by simp) y (by simp)
  have haw : a ≠ w := hf a (by simp) w (by simp)
  have hap : a ≠ p := hf a (by simp) p (by simp)
  have haq : a ≠ q := hf a (by simp) q (by simp)
  have hbx : b ≠ x := hf b (by simp) x (by simp)
  have hby : b ≠ y := hf b (by simp) y (by simp)
  have hbw : b ≠ w := hf b (by simp) w (by simp)
  have hbp : b ≠ p := hf b (by simp) p (by simp)
  have hbq : b ≠ q := hf b (by simp) q (by simp)
  let Γ := [successorCode x y w, transitiveCode x p q]
  have ht : Context Γ (transitiveCode x p q) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode x y w) := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (member y a) (imp (member a b) (member y b))) :=
    .mp hs (.mp ht (.closed (successor_transitive_pointwise x y w p q a b hwx hwy
      (Ne.symm haw) (Ne.symm hbw) hpx (Ne.symm hap) hpq hqx (Ne.symm haq) (Ne.symm hbq))))
  have hvb : ∀ h, h ∈ Γ → KDerivation (imp h (allCode b h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = successorCode x y w
    · subst h
      exact successor_vacuity x y w b hbx hby hbw
    · have he' : h = transitiveCode x p q := hh.resolve_left he
      subst h
      exact transitive_vacuity x p q b hbx hbp hbq
  have hva : ∀ h, h ∈ Γ → KDerivation (imp h (allCode a h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = successorCode x y w
    · subst h
      exact successor_vacuity x y w a hax hay haw
    · have he' : h = transitiveCode x p q := hh.resolve_left he
      subst h
      exact transitive_vacuity x p q a hax hap haq
  have hclosed : Context Γ (transitiveCode y a b) :=
    Context.generalize a hva (Context.generalize b hvb hpoint)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hclosed

theorem successor_transitive_certificate (x y w p q a b : Nat)
    (hwx : w ≠ x) (hwy : w ≠ y) (hpx : p ≠ x) (hpq : p ≠ q) (hqx : q ≠ x)
    (hf : ∀ t ∈ [a,b], ∀ z ∈ [x,y,w,p,q], t ≠ z) :
    theoremCode (certificate (successor_transitive_closed x y w p q a b hwx hwy hpx hpq hqx hf)) =
      imp (transitiveCode x p q) (imp (successorCode x y w) (transitiveCode y a b)) :=
  certificate_correct (successor_transitive_closed x y w p q a b hwx hwy hpx hpq hqx hf)

/-- Constructive K self-membership implication. Here code 1 is literally
`member 0 0`, so this theorem says `member x x → member 0 0`; it is not an
unqualified claim that every K model has irreflexive membership.
Proof construction contributed by Codex agent `/root/reverse_design/soundness_strength`. -/
def self_membership_implies_code_one (x : Nat) : KDerivation (imp (member x x) 1) := by
  by_cases hx : x = 0
  · subst x
    exact CompactHilbertBasis.identity 1
  · let a := x + 1
    let b := x + 2
    have ha0 : a ≠ 0 := by dsimp [a]; omega
    have hb0 : b ≠ 0 := by dsimp [b]; omega
    have hax : a ≠ x := by dsimp [a]; omega
    have hbx : b ≠ x := by dsimp [b]; omega
    have hab : a ≠ b := by dsimp [a,b]; omega
    let f : CompactNamed.Formula := .imp (.member 0 0) (.all a (.all b (.equal a b)))
    have hi := CompactNamed.universalInstance 0 x f (Ne.symm hx)
      (by simp [f, CompactNamed.Formula.binders, Ne.symm ha0, Ne.symm hb0])
      (by simp [f, CompactNamed.Formula.binders, Ne.symm hax, Ne.symm hbx])
    have hg : KDerivation (allCode 0 (imp 1 (allCode a (allCode b (equal a b))))) :=
      .generalize 0 (explosion _)
    have ht : KDerivation (imp (member x x) (allCode a (allCode b (equal a b)))) := by
      apply KDerivation.mp hg
      simpa [f, CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename, Ne.symm hx,
        hax, hbx, Ne.symm hax, Ne.symm hbx, ha0, hb0, Ne.symm ha0, Ne.symm hb0,
        show member 0 0 = 1 by rfl] using hi
    have h1 := CompactNamed.universalInstance a x (.all b (.equal a b)) hax
      (by simp [CompactNamed.Formula.binders, hab])
      (by simp [CompactNamed.Formula.binders, Ne.symm hbx])
    have h2 := CompactNamed.universalInstance b 0 (.equal x b) hb0
      (by simp [CompactNamed.Formula.binders]) (by simp [CompactNamed.Formula.binders])
    have hi1 : KDerivation (imp (allCode a (allCode b (equal a b))) (allCode b (equal x b))) := by
      simpa [CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
        hax, hab, Ne.symm hab, hbx, Ne.symm hbx] using h1
    have hi2 : KDerivation (imp (allCode b (equal x b)) (equal x 0)) := by
      simpa [CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
        hb0, hbx, Ne.symm hbx] using h2
    apply Context.closeEmpty
    apply Context.deduction
    have hs : Context [member x x] (member x x) := .hypothesis (by simp)
    have he : Context [member x x] (equal x 0) :=
      .mp (.mp (.mp hs (.closed ht)) (.closed hi1)) (.closed hi2)
    exact Context.memCongr he he hs

/-- The previous conditional injectivity proof needs only the explicitly
transitive-domain premise: K already constructs the code-one implication.
This does not establish that the domain has unique representatives. -/
def successor_injective_on_transitive (x u y v w p q : Nat)
    (hwx : w ≠ x) (hwu : w ≠ u) (hwy : w ≠ y) (hwv : w ≠ v)
    (hpx : p ≠ x) (hpu : p ≠ u) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqu : q ≠ u) :
    KDerivation (imp (transitiveCode x p q)
      (imp (successorCode x y w) (imp (successorCode u v w)
        (imp (equal y v) (equal x u))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  have ht : Context [transitiveCode x p q] (transitiveCode x p q) := Context.head [] _
  have h := successor_injective_from_transitive x u y v w p q
    hwx hwu hwy hwv hpx hpu hpq hqx hqu
  exact .mp (.closed (self_membership_implies_code_one x)) (.mp ht (.closed h))

theorem successor_injective_on_transitive_certificate (x u y v w p q : Nat)
    (hwx : w ≠ x) (hwu : w ≠ u) (hwy : w ≠ y) (hwv : w ≠ v)
    (hpx : p ≠ x) (hpu : p ≠ u) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqu : q ≠ u) :
    theoremCode (certificate (successor_injective_on_transitive x u y v w p q
      hwx hwu hwy hwv hpx hpu hpq hqx hqu)) =
      imp (transitiveCode x p q) (imp (successorCode x y w)
        (imp (successorCode u v w) (imp (equal y v) (equal x u)))) :=
  certificate_correct (successor_injective_on_transitive x u y v w p q
    hwx hwu hwy hwv hpx hpu hpq hqx hqu)

/-- Separate standard-model confirmation: an ordinal successor witness is
transitive. This is not used in the syntactic K construction. -/
theorem ordinal_successor_transitive_true (x y w a b n : Nat)
    (ρ : CompactMatrix.Environment) (hxw : x ≠ w) (hyw : y ≠ w)
    (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b)
    (hx : ρ x = (HFCoding.ordinal n).code)
    (hs : (CompactMatrix.decode (successorCode x y w)).Realize ρ) :
    (CompactMatrix.decode (transitiveCode y a b)).Realize ρ := by
  have hy := (ordinal_successor_relation x y w n ρ hxw hyw hx).mp hs
  exact ordinal_transitive_true y a b (n+1) ρ hya hyb hab hy

end PASoundness.PAtoCompactTransitiveClosure
