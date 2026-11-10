import PASoundness.CompactFreshen

/-!
Literal K derivations for moving quantifiers across implication and inserting
fresh vacuous quantifiers. These are proof constructors, with all side
conditions justified by named-syntax freshness and binder separation.
-/
namespace PASoundness.CompactNamed

open CompactProof CompactHilbertBasis CompactDerivations
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Same-variable instantiation is derived via a fresh alpha conversion, so
it uses no primitive substitution rule not present in the compact machine. -/
def allSpecialize (x : Nat) (f : Formula) (hx : x ∉ f.binders) :
    KDerivation (imp (allCode x f.encode) f.encode) := by
  let y := f.names.sup id + x + 1
  have hyn : y ∉ f.names := by
    intro hm
    have hh : y ≤ f.names.sup id := Finset.le_sup (f := id) hm
    dsimp [y] at hh
    omega
  have hxy : x ≠ y := by dsimp [y]; omega
  have halpha := (universalAlpha x y f hxy hx hyn).1
  have hi := universalInstance y x (replace x y f) (Ne.symm hxy)
    (by simpa only [replace_binders] using
      (show y ∉ f.binders from fun h => hyn (f.binders_subset_names h)))
    (by simpa only [replace_binders] using hx)
  rw [replace_roundtrip x y f hyn] at hi
  exact compose halpha hi

def existsIntroduce (x : Nat) (f : Formula) (hx : x ∉ f.binders) :
    KDerivation (imp f.encode (existsCode x f.encode)) :=
  compose (doubleNegIntro f.encode) (contrapose (allSpecialize x f.not
    (by simpa [Formula.not, Formula.binders] using hx)))

namespace ProofEquiv

def vacuousAll (x : Nat) (f : Formula) (hx : x ∉ f.names) :
    ProofEquiv f (.all x f) :=
  ⟨f.vacuity x hx, allSpecialize x f (fun h => hx (f.binders_subset_names h)),
    vacuousAll_semantics x f hx⟩

def vacuousExists (x : Nat) (f : Formula) (hx : x ∉ f.names) :
    ProofEquiv f (.ex x f) :=
  ⟨existsIntroduce x f (fun h => hx (f.binders_subset_names h)),
    Context.closeEmpty (Context.deduction (Context.existsElim (f.vacuity x hx)
      (.closed (.generalize x (identity f.encode)))
      (Context.head [] (existsCode x f.encode)))),vacuousExists_semantics x f hx⟩

end ProofEquiv

private def notImplies (a b : Nat) : KDerivation (imp (neg a) (imp a b)) :=
  Context.closeEmpty (Context.deduction (Context.deduction (Context.explode b
    (.mp (Context.head [neg a] a) (Context.under (Context.head [] (neg a)) a)))))

private def implicationCases {a b c : Nat}
    (hna : KDerivation (imp (neg a) c)) (hb : KDerivation (imp b c)) :
    KDerivation (imp (imp a b) c) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hs : Context [imp a b] (either (neg a) b) := Context.deduction
    (.mp (Context.dne (Context.head [imp a b] (neg (neg a))))
      (Context.under (Context.head [] (imp a b)) (neg (neg a))))
  exact Context.disjunctionElim hs
    (.mp (Context.head [imp a b] (neg a)) (.closed hna))
    (.mp (Context.head [imp a b] b) (.closed hb))

private def appliedFormula (a b : Nat) : KDerivation (imp a (imp (imp a b) b)) :=
  Context.closeEmpty (Context.deduction (Context.deduction
    (.mp (Context.under (Context.head [] a) (imp a b)) (Context.head [a] (imp a b)))))

private def negImpFormula (a b : Nat) :
    KDerivation (imp a (imp (neg b) (neg (imp a b)))) :=
  Context.closeEmpty (Context.deduction (Context.deduction (Context.deduction
    (.mp (.mp (Context.under (Context.under (Context.head [] a) (neg b)) (imp a b))
      (Context.head [neg b,a] (imp a b)))
      (Context.under (Context.head [a] (neg b)) (imp a b))))))

/-- Move a universal binder out of the consequent. -/
def implicationAllRight (x : Nat) (a b : Formula) (hx : x ∉ a.names) :
    ProofEquiv (.imp a (.all x b)) (.all x (.imp a b)) := by
  have hv := a.vacuity x hx
  constructor
  · exact implicationCases
      (compose (negationVacuity x hv) (allCongr x (notImplies a.encode b.encode)))
      (allCongr x (weakening b.encode a.encode))
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    exact Context.allMP (.mp (Context.head [allCode x (imp a.encode b.encode)] a.encode)
      (.closed hv))
      (Context.under (Context.head [] (allCode x (imp a.encode b.encode))) a.encode)

  · exact implicationAllRight_semantics x a b hx

/-- Move an existential binder out of the antecedent, reversing polarity. -/
def implicationExistsLeft (x : Nat) (a b : Formula) (hx : x ∉ b.names) :
    ProofEquiv (.imp (.ex x a) b) (.all x (.imp a b)) := by
  have hv := b.vacuity x hx
  constructor
  · exact implicationCases
      (compose (doubleNegElim (allCode x (neg a.encode)))
        (allCongr x (notImplies a.encode b.encode)))
      (compose hv (allCongr x (weakening b.encode a.encode)))
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    exact Context.existsElim hv
      (Context.under (Context.head [] (allCode x (imp a.encode b.encode)))
        (existsCode x a.encode))
      (Context.head [allCode x (imp a.encode b.encode)] (existsCode x a.encode))

  · exact implicationExistsLeft_semantics x a b hx

/-- Move a universal binder out of the antecedent. The no-shadowing condition
is supplied by arbitrary-formula freshening, not assumed for input syntax. -/
def implicationAllLeft (x : Nat) (a b : Formula)
    (hxa : x ∉ a.binders) (hxb : x ∉ b.names) :
    ProofEquiv (.imp (.all x a) b) (.ex x (.imp a b)) := by
  have hbind : x ∉ (Formula.imp a b).binders := by
    simp only [Formula.binders, Finset.mem_union, not_or]
    exact ⟨hxa,fun h => hxb (b.binders_subset_names h)⟩
  have hin := existsIntroduce x (.imp a b) hbind
  constructor
  · exact implicationCases
      (compose (contrapose (allCongr x (doubleNegElim a.encode)))
        (existsCongr x (notImplies a.encode b.encode)))
      (compose (weakening b.encode a.encode) hin)
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    exact Context.existsElim (b.vacuity x hxb)
      (Context.allMP (Context.head [existsCode x (imp a.encode b.encode)] (allCode x a.encode))
        (.closed (.generalize x (appliedFormula a.encode b.encode))))
      (Context.under (Context.head [] (existsCode x (imp a.encode b.encode)))
        (allCode x a.encode))

  · exact implicationAllLeft_semantics x a b hxb

/-- Move an existential binder out of the consequent. -/
def implicationExistsRight (x : Nat) (a b : Formula)
    (hxa : x ∉ a.names) (hxb : x ∉ b.binders) :
    ProofEquiv (.imp a (.ex x b)) (.ex x (.imp a b)) := by
  have hbind : x ∉ (Formula.imp a b).binders := by
    simp only [Formula.binders, Finset.mem_union, not_or]
    exact ⟨fun h => hxa (a.binders_subset_names h),hxb⟩
  have hin := existsIntroduce x (.imp a b) hbind
  constructor
  · exact implicationCases
      (compose (notImplies a.encode b.encode) hin)
      (existsCongr x (weakening b.encode a.encode))
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.dne
    apply Context.deduction
    have hA : Context [neg (existsCode x b.encode),a.encode,
        existsCode x (imp a.encode b.encode)] (allCode x a.encode) :=
      .mp (Context.under
        (Context.head [existsCode x (imp a.encode b.encode)] a.encode)
        (neg (existsCode x b.encode))) (.closed (a.vacuity x hxa))
    have hnB : Context [neg (existsCode x b.encode),a.encode,
        existsCode x (imp a.encode b.encode)] (allCode x (neg b.encode)) :=
      Context.dne (Context.head [a.encode,existsCode x (imp a.encode b.encode)]
        (neg (existsCode x b.encode)))
    have hnI := Context.allMP hnB
      (Context.allMP hA (.closed (.generalize x (negImpFormula a.encode b.encode))))
    exact .mp hnI (Context.under (Context.under
      (Context.head [] (existsCode x (imp a.encode b.encode))) a.encode)
      (neg (existsCode x b.encode)))

  · exact implicationExistsRight_semantics x a b hxa

end PASoundness.CompactNamed
