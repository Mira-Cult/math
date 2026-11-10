import PASoundness.CompactQuantifiers

/-!
A constructive prenex pass for every scope-separated named formula, assembled
from the four proved quantifier-movement schemas. Arbitrary input is handled
by `freshen` before this pass. Both directions are literal K derivations.
-/
namespace PASoundness.CompactNamed

open CompactProof CompactDerivations
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def IsQF : Formula → Prop
  | .all _ _ | .ex _ _ => False
  | .imp a b => IsQF a ∧ IsQF b
  | _ => True

def IsPrenex : Formula → Prop
  | .all _ a | .ex _ a => IsPrenex a
  | f => IsQF f

theorem qf_binders (f : Formula) (h : IsQF f) : f.binders = ∅ := by
  induction f with
  | truth | bottom | member | equal => rfl
  | all | ex => contradiction
  | imp a b ia ib => simp [Formula.binders, ia h.1, ib h.2]

theorem qf_separated (f : Formula) (h : IsQF f) : Separated f := by
  induction f with
  | truth | bottom | member | equal => trivial
  | all | ex => contradiction
  | imp a b ia ib =>
    refine ⟨ia h.1, ib h.2, ?_, ?_⟩ <;> simp [qf_binders _ h.1, qf_binders _ h.2]

theorem qf_prenex (f : Formula) (h : IsQF f) : IsPrenex f := by
  cases f <;> try exact h
  all_goals contradiction

def wrap : Polarity → Nat → Formula → Formula
  | .all, x, a => .all x a
  | .ex, x, a => .ex x a

@[simp] theorem wrap_names (q : Polarity) (x : Nat) (a : Formula) :
    (wrap q x a).names = insert x a.names := by cases q <;> rfl

@[simp] theorem wrap_binders (q : Polarity) (x : Nat) (a : Formula) :
    (wrap q x a).binders = insert x a.binders := by cases q <;> rfl

@[simp] theorem wrap_prenex (q : Polarity) (x : Nat) (a : Formula) :
    IsPrenex (wrap q x a) ↔ IsPrenex a := by cases q <;> rfl

@[simp] theorem wrap_separated (q : Polarity) (x : Nat) (a : Formula) :
    Separated (wrap q x a) ↔ Separated a ∧ x ∉ a.binders := by cases q <;> rfl

def ProofEquiv.quantifier (q : Polarity) (x : Nat) {a b : Formula}
    (h : ProofEquiv a b) : ProofEquiv (wrap q x a) (wrap q x b) :=
  match q with | .all => h.universal x | .ex => h.existential x

structure PrenexResult (f : Formula) where
  formula : Formula
  equivalent : ProofEquiv f formula
  prenex : IsPrenex formula
  names_eq : formula.names = f.names
  binders_eq : formula.binders = f.binders
  separated : Separated formula

namespace PrenexResult

def ofQF (f : Formula) (h : IsQF f) : PrenexResult f :=
  ⟨f,.refl f,qf_prenex f h,rfl,rfl,qf_separated f h⟩

def wrap (q : Polarity) (x : Nat) {f : Formula} (h : PrenexResult f)
    (hx : x ∉ f.binders) : PrenexResult (CompactNamed.wrap q x f) :=
  ⟨CompactNamed.wrap q x h.formula, h.equivalent.quantifier q x,
    (wrap_prenex ..).mpr h.prenex, by simp [h.names_eq], by simp [h.binders_eq],
    (wrap_separated ..).mpr ⟨h.separated,by simpa only [h.binders_eq] using hx⟩⟩

def transport {f g : Formula} (h : ProofEquiv f g)
    (hn : g.names = f.names) (hb : g.binders = f.binders) (r : PrenexResult g) :
    PrenexResult f :=
  ⟨r.formula,h.trans r.equivalent,r.prenex,r.names_eq.trans hn,
    r.binders_eq.trans hb,r.separated⟩

end PrenexResult

private theorem names_pullRight (q : Polarity) (x : Nat) (a b : Formula) :
    (wrap q x (.imp a b)).names = (Formula.imp a (wrap q x b)).names := by
  ext v
  simp only [wrap_names, Formula.names, Finset.mem_union, Finset.mem_insert]
  tauto

private theorem binders_pullRight (q : Polarity) (x : Nat) (a b : Formula) :
    (wrap q x (.imp a b)).binders = (Formula.imp a (wrap q x b)).binders := by
  ext v
  simp only [wrap_binders, Formula.binders, Finset.mem_union, Finset.mem_insert]
  tauto

private theorem names_pullLeft (q : Polarity) (x : Nat) (a b : Formula) :
    (wrap q.flip x (.imp a b)).names = (Formula.imp (wrap q x a) b).names := by
  ext v
  simp only [wrap_names, Formula.names, Finset.mem_union, Finset.mem_insert]
  tauto

private theorem binders_pullLeft (q : Polarity) (x : Nat) (a b : Formula) :
    (wrap q.flip x (.imp a b)).binders = (Formula.imp (wrap q x a) b).binders := by
  ext v
  simp only [wrap_binders, Formula.binders, Finset.mem_union, Finset.mem_insert]
  tauto

private theorem separated_right_body (q : Polarity) (x : Nat) (a b : Formula)
    (hs : Separated (.imp a (wrap q x b))) : Separated (.imp a b) := by
  have hh := (wrap_separated q x b).mp hs.2.1
  refine ⟨hs.1,hh.1,?_,?_⟩
  · intro v hv hm
    exact hs.2.2.1 v hv (by simpa only [wrap_names] using Finset.mem_insert_of_mem hm)
  · intro v hv
    exact hs.2.2.2 v (by simpa only [wrap_binders] using Finset.mem_insert_of_mem hv)

private theorem separated_left_body (q : Polarity) (x : Nat) (a b : Formula)
    (hs : Separated (.imp (wrap q x a) b)) : Separated (.imp a b) := by
  have hh := (wrap_separated q x a).mp hs.1
  refine ⟨hh.1,hs.2.1,?_,?_⟩
  · intro v hv
    exact hs.2.2.1 v (by simpa only [wrap_binders] using Finset.mem_insert_of_mem hv)
  · intro v hv hm
    exact hs.2.2.2 v hv (by simpa only [wrap_names] using Finset.mem_insert_of_mem hm)

private def pullRight (a : Formula) (ha : IsQF a) (b : Formula)
    (hb : IsPrenex b) (hs : Separated (.imp a b)) : PrenexResult (.imp a b) :=
  match b with
  | .truth => .ofQF _ ⟨ha,trivial⟩
  | .bottom => .ofQF _ ⟨ha,trivial⟩
  | .member x y => .ofQF _ ⟨ha,trivial⟩
  | .equal x y => .ofQF _ ⟨ha,trivial⟩
  | .imp b c => .ofQF _ ⟨ha,hb⟩
  | .all x b => by
      have hs' := separated_right_body .all x a b hs
      let r := pullRight a ha b hb hs'
      have hxa : x ∉ a.names := hs.2.2.2 x (Finset.mem_insert_self ..)
      have hxb : x ∉ b.binders := hs.2.1.2
      have hx : x ∉ (Formula.imp a b).binders := by
        simp only [Formula.binders, Finset.mem_union, not_or]
        exact ⟨fun h => hxa (a.binders_subset_names h),hxb⟩
      exact .transport (implicationAllRight x a b hxa)
        (names_pullRight .all x a b) (binders_pullRight .all x a b) (r.wrap .all x hx)
  | .ex x b => by
      have hs' := separated_right_body .ex x a b hs
      let r := pullRight a ha b hb hs'
      have hxa : x ∉ a.names := hs.2.2.2 x (Finset.mem_insert_self ..)
      have hxb : x ∉ b.binders := hs.2.1.2
      have hx : x ∉ (Formula.imp a b).binders := by
        simp only [Formula.binders, Finset.mem_union, not_or]
        exact ⟨fun h => hxa (a.binders_subset_names h),hxb⟩
      exact .transport (implicationExistsRight x a b hxa hxb)
        (names_pullRight .ex x a b) (binders_pullRight .ex x a b) (r.wrap .ex x hx)

private def pullLeft (a : Formula) (ha : IsPrenex a) (b : Formula)
    (hb : IsPrenex b) (hs : Separated (.imp a b)) : PrenexResult (.imp a b) :=
  match a with
  | .truth => pullRight .truth ha b hb hs
  | .bottom => pullRight .bottom ha b hb hs
  | .member x y => pullRight (.member x y) ha b hb hs
  | .equal x y => pullRight (.equal x y) ha b hb hs
  | .imp c d => pullRight (.imp c d) ha b hb hs
  | .all x a => by
      have hs' := separated_left_body .all x a b hs
      let r := pullLeft a ha b hb hs'
      have hxb : x ∉ b.names := hs.2.2.1 x (Finset.mem_insert_self ..)
      have hxa : x ∉ a.binders := hs.1.2
      have hx : x ∉ (Formula.imp a b).binders := by
        simp only [Formula.binders, Finset.mem_union, not_or]
        exact ⟨hxa,fun h => hxb (b.binders_subset_names h)⟩
      exact .transport (implicationAllLeft x a b hxa hxb)
        (names_pullLeft .all x a b) (binders_pullLeft .all x a b) (r.wrap .ex x hx)
  | .ex x a => by
      have hs' := separated_left_body .ex x a b hs
      let r := pullLeft a ha b hb hs'
      have hxb : x ∉ b.names := hs.2.2.1 x (Finset.mem_insert_self ..)
      have hxa : x ∉ a.binders := hs.1.2
      have hx : x ∉ (Formula.imp a b).binders := by
        simp only [Formula.binders, Finset.mem_union, not_or]
        exact ⟨hxa,fun h => hxb (b.binders_subset_names h)⟩
      exact .transport (implicationExistsLeft x a b hxb)
        (names_pullLeft .ex x a b) (binders_pullLeft .ex x a b) (r.wrap .all x hx)

/-- Proof-producing prenex conversion, preserving exactly the finite sets of
names and binders after scope separation. -/
def prenex (f : Formula) (hs : Separated f) : PrenexResult f :=
  match f with
  | .truth => .ofQF _ trivial
  | .bottom => .ofQF _ trivial
  | .member a b => .ofQF _ trivial
  | .equal a b => .ofQF _ trivial
  | .all x a => (prenex a hs.1).wrap .all x hs.2
  | .ex x a => (prenex a hs.1).wrap .ex x hs.2
  | .imp a b => by
      let ra := prenex a hs.1
      let rb := prenex b hs.2.1
      have hnew : Separated (.imp ra.formula rb.formula) := by
        refine ⟨ra.separated,rb.separated,?_,?_⟩
        · simpa only [ra.binders_eq, rb.names_eq] using hs.2.2.1
        · simpa only [rb.binders_eq, ra.names_eq] using hs.2.2.2
      exact .transport (.implication ra.equivalent rb.equivalent)
        (by simp only [Formula.names,ra.names_eq,rb.names_eq])
        (by simp only [Formula.binders,ra.binders_eq,rb.binders_eq])
        (pullLeft ra.formula ra.prenex rb.formula rb.prenex hnew)

end PASoundness.CompactNamed
