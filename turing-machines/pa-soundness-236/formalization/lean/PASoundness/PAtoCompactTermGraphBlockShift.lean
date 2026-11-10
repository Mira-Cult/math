import PASoundness.PAtoCompactTemplateBlockShift

/-! Raw syntactic term-graph block shift. This concerns syntax only and does
not assert K alpha equivalence. -/

namespace PASoundness.PAtoCompactTermGraphBlockShift

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMapNamesCongr

def BlockShift (g : Nat → Nat) (b c size : Nat) : Prop :=
  ∀ i, i < size → g (b + i) = c + i

/-- Literal template transport requirements for one raw renaming map. -/
structure TemplateShifts (g : Nat → Nat) : Prop where
  domain : ∀ b c x, BlockShift g b c 64 →
    mapNames g (domainAt b x) = domainAt c (g x)
  equiv : ∀ b c x y, BlockShift g b c 64 →
    mapNames g (equivAt b x y) = equivAt c (g x) (g y)
  zero : ∀ b c x, BlockShift g b c 64 →
    mapNames g (zeroAt b x) = zeroAt c (g x)
  succ : ∀ b c x y, BlockShift g b c 64 →
    mapNames g (succAt b x y) = succAt c (g x) (g y)
  add : ∀ b c x y z, BlockShift g b c 64 →
    mapNames g (addAt b x y z) = addAt c (g x) (g y) (g z)
  mul : ∀ b c x y z, BlockShift g b c 64 →
    mapNames g (mulAt b x y z) = mulAt c (g x) (g y) (g z)

/-- Once the six literal templates shift, raw graph block shift follows by
term recursion. The output label is renamed, including recursive witnesses. -/
theorem termGraph_shift_of_templates {α : Type} (g : Nat → Nat)
    (ht : TemplateShifts g) (v : α → Nat) (t : Peano.language.Term α) :
    ∀ out b c, BlockShift g b c (termCost t) →
      mapNames g (termGraph v t out b) = termGraph (g ∘ v) t (g out) c := by
  induction t with
  | var a =>
      intro out b c hs
      have hs64 : BlockShift g b c 64 := hs
      simp only [termGraph, mapNames_andF, ht.domain b c out hs64,
        ht.equiv b c (v a) out hs64, Function.comp_apply]
  | @func l f ts ih =>
      cases f with
      | zero =>
          intro out b c hs
          have hs64 : BlockShift g b c 64 := hs
          simp only [termGraph, mapNames_andF, ht.domain b c out hs64,
            ht.zero b c out hs64]
      | succ =>
          intro out b c hs
          have hs64 : BlockShift g b c 64 := by
            intro i hi; apply hs i; simp only [termCost]; omega
          have hchild : BlockShift g (b + 64) (c + 64) (termCost (ts 0)) := by
            intro i hi
            have h := hs (64 + i) (by simp only [termCost]; omega)
            simpa only [Nat.add_assoc] using h
          have hb : g b = c := by simpa using hs64 0 (by omega)
          simp only [termGraph, mapNames_andF, mapNames, ht.domain b c out hs64,
            ht.succ b c b out hs64, ih 0 b (b + 64) (c + 64) hchild, hb]
      | add =>
          intro out b c hs
          have hs64 : BlockShift g b c 64 := by
            intro i hi; apply hs i; simp only [termCost]; omega
          have hchild0 : BlockShift g (b + 64) (c + 64) (termCost (ts 0)) := by
            intro i hi
            have h := hs (64 + i) (by simp only [termCost]; omega)
            simpa only [Nat.add_assoc] using h
          have hchild1 : BlockShift g (b + 64 + termCost (ts 0))
              (c + 64 + termCost (ts 0)) (termCost (ts 1)) := by
            intro i hi
            have h := hs (64 + termCost (ts 0) + i) (by simp only [termCost]; omega)
            simpa only [Nat.add_assoc] using h
          have hb : g b = c := by simpa using hs64 0 (by omega)
          have hb1 : g (b + 1) = c + 1 := hs64 1 (by omega)
          simp only [termGraph, mapNames_andF, mapNames, ht.domain b c out hs64,
            ht.add b c b (b + 1) out hs64, ih 0 b (b + 64) (c + 64) hchild0,
            ih 1 (b + 1) (b + 64 + termCost (ts 0))
              (c + 64 + termCost (ts 0)) hchild1, hb, hb1]

      | mul =>
          intro out b c hs
          have hs64 : BlockShift g b c 64 := by
            intro i hi; apply hs i; simp only [termCost]; omega
          have hchild0 : BlockShift g (b + 64) (c + 64) (termCost (ts 0)) := by
            intro i hi
            have h := hs (64 + i) (by simp only [termCost]; omega)
            simpa only [Nat.add_assoc] using h
          have hchild1 : BlockShift g (b + 64 + termCost (ts 0))
              (c + 64 + termCost (ts 0)) (termCost (ts 1)) := by
            intro i hi
            have h := hs (64 + termCost (ts 0) + i) (by simp only [termCost]; omega)
            simpa only [Nat.add_assoc] using h
          have hb : g b = c := by simpa using hs64 0 (by omega)
          have hb1 : g (b + 1) = c + 1 := hs64 1 (by omega)
          simp only [termGraph, mapNames_andF, mapNames, ht.domain b c out hs64,
            ht.mul b c b (b + 1) out hs64, ih 0 b (b + 64) (c + 64) hchild0,
            ih 1 (b + 1) (b + 64 + termCost (ts 0))
              (c + 64 + termCost (ts 0)) hchild1, hb, hb1]

/-- All six concrete named templates satisfy the raw shift identities. -/
theorem templateShifts (g : Nat → Nat) : TemplateShifts g := by
  constructor
  · intro b c x hs
    exact PAtoCompactTemplateBlockShift.domainAt_shift g b c x hs
  · intro b c x y hs
    exact PAtoCompactTemplateBlockShift.equivAt_shift g b c x y hs
  · intro b c x hs
    exact PAtoCompactTemplateBlockShift.zeroAt_shift g b c x hs
  · intro b c x y hs
    exact PAtoCompactTemplateBlockShift.succAt_shift g b c x y hs
  · intro b c x y z hs
    exact PAtoCompactTemplateBlockShift.addAt_shift g b c x y z hs
  · intro b c x y z hs
    exact PAtoCompactTemplateBlockShift.mulAt_shift g b c x y z hs

/-- Full raw block-shift law for generated term graphs. No injectivity,
freshness, or K-equivalence claim is made. -/
theorem termGraph_shift {α : Type} (g : Nat → Nat) (v : α → Nat)
    (t : Peano.language.Term α) (out b c : Nat)
    (hs : BlockShift g b c (termCost t)) :
    mapNames g (termGraph v t out b) = termGraph (g ∘ v) t (g out) c :=
  termGraph_shift_of_templates g (templateShifts g) v t out b c hs

end PASoundness.PAtoCompactTermGraphBlockShift

#print axioms PASoundness.PAtoCompactTermGraphBlockShift.termGraph_shift_of_templates
#print axioms PASoundness.PAtoCompactTermGraphBlockShift.templateShifts
#print axioms PASoundness.PAtoCompactTermGraphBlockShift.termGraph_shift
