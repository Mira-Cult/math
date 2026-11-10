import PASoundness.CompactHilbertBasis

/-!
Constructive derived rules of the exact compact numeric calculus. Temporary
hypotheses are finite proof data with only assumption, closed theorem, and MP
constructors. Deduction expands to actual AX7/MP certificates; it is not a
semantic completeness premise. The construction follows the corresponding
finite proofs in recovered PA238 NumericHilbert238.v and checks them anew.
-/
namespace PASoundness.CompactDerivations

open CompactProof CompactHilbertBasis
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def existsEqual (x y : Nat) : KDerivation (existsCode x (equal x y)) := by
  change KDerivation (axiomCode 0 x y 0 0)
  exact .axiom ⟨0, by decide⟩ x y 0 0

def allDistribution (x a b : Nat) :
    KDerivation (imp (allCode x (imp a b)) (imp (allCode x a) (allCode x b))) := by
  change KDerivation (axiomCode 1 x a b 0)
  exact .axiom ⟨1, by decide⟩ x a b 0

def memberRightEquality (x y z : Nat) :
    KDerivation (imp (member x y) (imp (equal y z) (member x z))) := by
  change KDerivation (axiomCode 2 x y z 0)
  exact .axiom ⟨2, by decide⟩ x y z 0

def allCommute (x y a : Nat) :
    KDerivation (imp (allCode x (allCode y a)) (allCode y (allCode x a))) := by
  change KDerivation (axiomCode 3 x y a 0)
  exact .axiom ⟨3, by decide⟩ x y a 0

def memberLeftEquality (x y z : Nat) :
    KDerivation (imp (equal x y) (imp (member x z) (member y z))) := by
  change KDerivation (axiomCode 4 x y z 0)
  exact .axiom ⟨4, by decide⟩ x y z 0

def existsAll (x a : Nat) : KDerivation (imp (existsCode x (allCode x a)) a) := by
  change KDerivation (axiomCode 5 x a 0 0)
  exact .axiom ⟨5, by decide⟩ x a 0 0

def equalityEuclidean (x y z : Nat) :
    KDerivation (imp (equal x y) (imp (equal x z) (equal y z))) := by
  change KDerivation (axiomCode 6 x y z 0)
  exact .axiom ⟨6, by decide⟩ x y z 0

inductive Context (Γ : List Nat) : Nat → Type where
  | hypothesis {a : Nat} : a ∈ Γ → Context Γ a
  | closed {a : Nat} : KDerivation a → Context Γ a
  | mp {a b : Nat} : Context Γ a → Context Γ (imp a b) → Context Γ b

namespace Context

def weaken {Γ Δ : List Nat} {a : Nat} (d : Context Γ a)
    (h : ∀ b, b ∈ Γ → b ∈ Δ) : Context Δ a :=
  match d with
  | .hypothesis hb => .hypothesis (h _ hb)
  | .closed d => .closed d
  | .mp da di => .mp (weaken da h) (weaken di h)

def close {Γ : List Nat} {a : Nat} (d : Context Γ a)
    (h : ∀ b, b ∈ Γ → KDerivation b) : KDerivation a :=
  match d with
  | .hypothesis hb => h _ hb
  | .closed d => d
  | .mp da di => .mp (close da h) (close di h)

def closeEmpty {a : Nat} (d : Context [] a) : KDerivation a :=
  close d (fun _ h => False.elim (List.not_mem_nil h))

def lift {Γ : List Nat} {a : Nat} (d : Context Γ a) (h : Nat) : Context Γ (imp h a) :=
  .mp d (.closed (weakening a h))

def under {Γ : List Nat} {a : Nat} (d : Context Γ a) (h : Nat) : Context (h :: Γ) a :=
  weaken d (fun _ hm => List.mem_cons_of_mem h hm)

def head (Γ : List Nat) (a : Nat) : Context (a :: Γ) a :=
  .hypothesis (List.mem_cons_self ..)

/-- Finite deduction, with the MP branch expanded through the proved S basis. -/
def deduction {Γ : List Nat} {h a : Nat} (d : Context (h :: Γ) a) :
    Context Γ (imp h a) :=
  match d with
  | @Context.hypothesis _ a ha =>
    if he : a = h then by subst a; exact .closed (identity h)
    else lift (.hypothesis ((List.mem_cons.mp ha).resolve_left he)) h
  | .closed d => lift (.closed d) h
  | @Context.mp _ a b da di =>
    .mp (deduction da) (.mp (deduction di) (.closed (distribution h a b)))

def apply {Γ : List Nat} {a b : Nat} (d : Context (a :: Γ) b) (ha : Context Γ a) :
    Context Γ b := .mp ha (deduction d)

/-- Literal code-one explosion uses AX5 and weakening; no HF semantic premise. -/
def explode {Γ : List Nat} (a : Nat) (h : Context Γ 1) : Context Γ a := by
  have hk : Context Γ (imp 1 (existsCode 0 (allCode 0 a))) :=
    .closed (weakening 1 (allCode 0 (neg (allCode 0 a))))
  exact .mp (.mp h hk) (.closed (existsAll 0 a))

end Context

def explosion (a : Nat) : KDerivation (imp 1 a) :=
  Context.closeEmpty (Context.deduction (Context.explode a (Context.head [] 1)))

def doubleNegElim (a : Nat) : KDerivation (imp (neg (neg a)) a) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.mp (a := imp (neg a) a)
  · apply Context.deduction
    apply Context.explode a
    exact .mp (Context.head [neg (neg a)] (neg a))
      (Context.under (Context.head [] (neg (neg a))) (neg a))
  · exact .closed (peirce a 1)

def doubleNegIntro (a : Nat) : KDerivation (imp a (neg (neg a))) :=
  Context.closeEmpty (Context.deduction (Context.deduction
    (.mp (Context.under (Context.head [] a) (neg a)) (Context.head [a] (neg a)))))

namespace Context

def dne {Γ : List Nat} {a : Nat} (d : Context Γ (neg (neg a))) : Context Γ a :=
  .mp d (.closed (doubleNegElim a))

def conjunctionIntro {Γ : List Nat} {a b : Nat}
    (ha : Context Γ a) (hb : Context Γ b) : Context Γ (both a b) :=
  deduction (.mp (under hb (imp a (neg b)))
    (.mp (under ha (imp a (neg b))) (head Γ (imp a (neg b)))))

def conjunctionLeft {Γ : List Nat} {a b : Nat}
    (h : Context Γ (both a b)) : Context Γ a := by
  apply dne
  apply deduction
  apply Context.mp (a := imp a (neg b))
  · apply deduction
    apply explode (neg b)
    exact .mp (head (neg a :: Γ) a) (under (head Γ (neg a)) a)
  · exact under h (neg a)

def conjunctionRight {Γ : List Nat} {a b : Nat}
    (h : Context Γ (both a b)) : Context Γ b :=
  dne (deduction (.mp (lift (head Γ (neg b)) a) (under h (neg b))))

def contrapose {Γ : List Nat} {a b : Nat} (h : Context Γ (imp a b)) :
    Context Γ (imp (neg b) (neg a)) :=
  deduction (deduction (.mp
    (.mp (head (neg b :: Γ) a) (under (under h (neg b)) a))
    (under (head Γ (neg b)) a)))

def implicationCongr {Γ : List Nat} {a a' b b' : Nat}
    (ha : Context Γ (imp a' a)) (hb : Context Γ (imp b b')) :
    Context Γ (imp (imp a b) (imp a' b')) := by
  apply deduction
  apply deduction
  exact .mp
    (.mp (.mp (head (imp a b :: Γ) a') (under (under ha (imp a b)) a'))
      (under (head Γ (imp a b)) a'))
    (under (under hb (imp a b)) a')

end Context

def contrapose {a b : Nat} (d : KDerivation (imp a b)) :
    KDerivation (imp (neg b) (neg a)) :=
  Context.closeEmpty (Context.contrapose (.closed d))

def compose {a b c : Nat} (hab : KDerivation (imp a b))
    (hbc : KDerivation (imp b c)) : KDerivation (imp a c) :=
  .mp hbc (.mp hab (composition a b c))

def implicationCongr {a a' b b' : Nat}
    (ha : KDerivation (imp a' a)) (hb : KDerivation (imp b b')) :
    KDerivation (imp (imp a b) (imp a' b')) :=
  Context.closeEmpty (Context.implicationCongr (.closed ha) (.closed hb))

def allCongr (x : Nat) {a b : Nat} (d : KDerivation (imp a b)) :
    KDerivation (imp (allCode x a) (allCode x b)) :=
  .mp (.generalize x d) (allDistribution x a b)

def existsCongr (x : Nat) {a b : Nat} (d : KDerivation (imp a b)) :
    KDerivation (imp (existsCode x a) (existsCode x b)) :=
  contrapose (allCongr x (contrapose d))

/-- Classical disjunction in the unchanged implication/bottom representation. -/
def either (a b : Nat) := imp (neg a) b

namespace Context

def disjunctionLeft {Γ : List Nat} {a b : Nat} (ha : Context Γ a) :
    Context Γ (either a b) :=
  deduction (explode b (.mp (under ha (neg a)) (head Γ (neg a))))

def disjunctionRight {Γ : List Nat} {a b : Nat} (hb : Context Γ b) :
    Context Γ (either a b) := lift hb (neg a)

def disjunctionElim {Γ : List Nat} {a b c : Nat} (h : Context Γ (either a b))
    (ha : Context (a :: Γ) c) (hb : Context (b :: Γ) c) : Context Γ c := by
  apply dne
  apply deduction
  have hac := deduction ha
  have hbc := deduction hb
  have hna : Context (neg c :: Γ) (neg a) := deduction
    (.mp (.mp (head (neg c :: Γ) a) (under (under hac (neg c)) a))
      (under (head Γ (neg c)) a))
  exact .mp (.mp (.mp hna (under h (neg c))) (under hbc (neg c)))
    (head Γ (neg c))

def allMP {Γ : List Nat} {x a b : Nat} (ha : Context Γ (allCode x a))
    (hab : Context Γ (allCode x (imp a b))) : Context Γ (allCode x b) :=
  .mp ha (.mp hab (.closed (allDistribution x a b)))

/-- Generalization in a finite context consumes explicit vacuity proofs. -/
def generalize {Γ : List Nat} {a : Nat} (x : Nat)
    (hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode x h)))
    (d : Context Γ a) : Context Γ (allCode x a) :=
  match d with
  | .hypothesis ha => .mp (.hypothesis ha) (.closed (hv _ ha))
  | .closed d => .closed (.generalize x d)
  | .mp da di => allMP (generalize x hv da) (generalize x hv di)

end Context

/-- AX8's two atomic vacuity conjuncts are projected from its exact gated bundle. -/
def atomicVacuity (a b x : Nat) (hxa : x ≠ a) (hxb : x ≠ b) :
    KDerivation (both (imp (equal a b) (allCode x (equal a b)))
      (imp (member a b) (allCode x (member a b)))) := by
  have bundle := KDerivation.axiom (⟨8, by decide⟩ : Fin 9) a b x 0
  simp only [axiomCode, show ¬ (x = a ∨ x = b) from not_or_intro hxa hxb,
    ↓reduceIte] at bundle
  exact Context.closeEmpty (Context.conjunctionRight (.closed bundle))

def equalityVacuity (a b x : Nat) (hxa : x ≠ a) (hxb : x ≠ b) :
    KDerivation (imp (equal a b) (allCode x (equal a b))) :=
  Context.closeEmpty (Context.conjunctionLeft (.closed (atomicVacuity a b x hxa hxb)))

def membershipVacuity (a b x : Nat) (hxa : x ≠ a) (hxb : x ≠ b) :
    KDerivation (imp (member a b) (allCode x (member a b))) :=
  Context.closeEmpty (Context.conjunctionRight (.closed (atomicVacuity a b x hxa hxb)))

def negationVacuity (x : Nat) {a : Nat} (hv : KDerivation (imp a (allCode x a))) :
    KDerivation (imp (neg a) (allCode x (neg a))) :=
  compose (compose (contrapose (existsAll x a))
    (doubleNegElim (allCode x (neg (allCode x a))))) (allCongr x (contrapose hv))

def implicationVacuity (x : Nat) {a b : Nat}
    (ha : KDerivation (imp a (allCode x a)))
    (hb : KDerivation (imp b (allCode x b))) :
    KDerivation (imp (imp a b) (allCode x (imp a b))) := by
  have hB := compose hb (allCongr x (weakening b a))
  have hn : KDerivation (imp (neg a) (imp a b)) := Context.closeEmpty
    (Context.deduction (Context.deduction (Context.explode b
      (.mp (Context.head [neg a] a) (Context.under (Context.head [] (neg a)) a)))))
  have hA := compose (negationVacuity x ha) (allCongr x hn)
  apply Context.closeEmpty
  apply Context.deduction
  have hs : Context [imp a b] (either (neg a) b) := Context.deduction
    (.mp (Context.dne (Context.head [imp a b] (neg (neg a))))
      (Context.under (Context.head [] (imp a b)) (neg (neg a))))
  exact Context.disjunctionElim hs
    (.mp (Context.head [imp a b] (neg a)) (.closed hA))
    (.mp (Context.head [imp a b] b) (.closed hB))

def universalVacuity (x y : Nat) {a : Nat}
    (hv : KDerivation (imp a (allCode x a))) :
    KDerivation (imp (allCode y a) (allCode x (allCode y a))) :=
  compose (allCongr y hv) (allCommute y x a)

def contrapositionFormula (a b : Nat) :
    KDerivation (imp (imp a b) (imp (neg b) (neg a))) :=
  Context.closeEmpty (Context.deduction (Context.contrapose (Context.head [] (imp a b))))

namespace Context

/-- Existential elimination uses a constructed vacuity theorem for its conclusion. -/
def existsElim {Γ : List Nat} {x a b : Nat}
    (hv : KDerivation (imp b (allCode x b)))
    (hi : Context Γ (allCode x (imp a b)))
    (he : Context Γ (existsCode x a)) : Context Γ b := by
  apply dne
  apply deduction
  have hn : Context (neg b :: Γ) (allCode x (neg b)) :=
    .mp (head Γ (neg b)) (.closed (negationVacuity x hv))
  have hc : Context (neg b :: Γ) (allCode x (imp (neg b) (neg a))) :=
    allMP (under hi (neg b)) (.closed (.generalize x (contrapositionFormula a b)))
  exact .mp (allMP hn hc) (under he (neg b))

end Context

def equalityReflexive (a : Nat) : KDerivation (equal a a) := by
  have hf : a+1 ≠ a := by omega
  have hd : KDerivation (imp (equal (a+1) a) (equal a a)) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h := Context.head [] (equal (a+1) a)
    exact .mp h (.mp h (.closed (equalityEuclidean (a+1) a a)))
  exact Context.closeEmpty (Context.existsElim (equalityVacuity a a (a+1) hf hf)
    (.closed (.generalize (a+1) hd)) (.closed (existsEqual (a+1) a)))

def equalitySymmetry (a b : Nat) : KDerivation (imp (equal a b) (equal b a)) :=
  Context.closeEmpty (Context.deduction
    (.mp (.closed (equalityReflexive a))
      (.mp (Context.head [] (equal a b)) (.closed (equalityEuclidean a b a)))))

def equalityTransitive (a b c : Nat) :
    KDerivation (imp (equal a b) (imp (equal b c) (equal a c))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hba : Context [equal b c, equal a b] (equal b a) :=
    .mp (Context.under (Context.head [] (equal a b)) (equal b c))
      (.closed (equalitySymmetry a b))
  exact .mp (Context.head [equal a b] (equal b c))
    (.mp hba (.closed (equalityEuclidean b a c)))

namespace Context

def eqSymm {Γ : List Nat} {a b : Nat} (h : Context Γ (equal a b)) :
    Context Γ (equal b a) := .mp h (.closed (equalitySymmetry a b))

def eqTrans {Γ : List Nat} {a b c : Nat}
    (h : Context Γ (equal a b)) (h' : Context Γ (equal b c)) :
    Context Γ (equal a c) := .mp h' (.mp h (.closed (equalityTransitive a b c)))

def eqCongr {Γ : List Nat} {a b c d : Nat}
    (hac : Context Γ (equal a c)) (hbd : Context Γ (equal b d))
    (hab : Context Γ (equal a b)) : Context Γ (equal c d) :=
  eqTrans (eqTrans (eqSymm hac) hab) hbd

def memCongr {Γ : List Nat} {a b c d : Nat}
    (hac : Context Γ (equal a c)) (hbd : Context Γ (equal b d))
    (hab : Context Γ (member a b)) : Context Γ (member c d) :=
  .mp hbd (.mp (.mp hab (.mp hac (.closed (memberLeftEquality a c b))))
    (.closed (memberRightEquality c b d)))

end Context

def conditionalImplicationCongr {e a a' b b' : Nat}
    (ha : KDerivation (imp e (imp a' a)))
    (hb : KDerivation (imp e (imp b b'))) :
    KDerivation (imp e (imp (imp a b) (imp a' b'))) :=
  Context.closeEmpty (Context.deduction (Context.implicationCongr
    (.mp (Context.head [] e) (.closed ha)) (.mp (Context.head [] e) (.closed hb))))

def conditionalAllCongr {e a b : Nat} (x : Nat)
    (hv : KDerivation (imp e (allCode x e)))
    (hi : KDerivation (imp e (imp a b))) :
    KDerivation (imp e (imp (allCode x a) (allCode x b))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.allMP (Context.head [e] (allCode x a))
    (Context.allMP
      (.mp (Context.under (Context.head [] e) (allCode x a)) (.closed hv))
      (.closed (.generalize x hi)))

end PASoundness.CompactDerivations
