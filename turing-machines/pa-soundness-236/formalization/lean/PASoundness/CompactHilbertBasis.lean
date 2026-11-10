import PASoundness.CompactProof

/-!
Finite AX7/MP certificates for an ordinary implicational Hilbert basis.
Ported from the explicit dependency closure of NumericHilbert238.v in the
recovered PA238 source archive. The Coq source states that its bounded
unification search independently recomputed detachment edges; B/S target
formulas were read from Jeff's CD254 at c132d7eae8158cd3a9850ea3eb7251158c3dd821.
This module checks the displayed proof objects anew in Lean, against the exact
compact numeric axiom and modus ponens constructors. No Coq theorem is trusted.
Source file SHA-256: fd577e5737cfa733c924bb832d2742ab7ead223c3837a27956c97d0076401223
-/
namespace PASoundness.CompactHilbertBasis
open CompactProof
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def mpCode (a b : Nat) (da : KDerivation a) (dab : KDerivation (imp a b)) :
    KDerivation b := .mp da dab

private def ax7 (a b c u : Nat) :
    KDerivation (imp (imp (imp c u) a) (imp (imp a c) (imp b c))) := by
  change KDerivation (axiomCode 7 a b c u)
  exact .axiom ⟨7, by decide⟩ a b c u

private def r8_certificate_0 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 p1) p2) (imp (imp p2 p0) (imp p3 p0))) :=
  (ax7 p2 p3 p0 p1)

private def r8_certificate_1 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) (imp p2 p1)) (imp p1 p3)) (imp p4 (imp p1 p3))) :=
  (mpCode (imp (imp (imp p1 p3) p0) (imp (imp p0 p1) (imp p2 p1))) (imp (imp (imp (imp p0 p1) (imp p2 p1)) (imp p1 p3)) (imp p4 (imp p1 p3)))
    (r8_certificate_0 p1 p3 p0 p2)
    (r8_certificate_0 (imp p1 p3) p0 (imp (imp p0 p1) (imp p2 p1)) p4))

private def r8_certificate_2 (p0 p1 p2 p3 p4 p5 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 p2)) (imp (imp p3 p1) (imp p4 p1))) (imp p5 (imp (imp p3 p1) (imp p4 p1)))) :=
  (mpCode (imp (imp (imp (imp p3 p1) (imp p4 p1)) (imp p1 p2)) (imp p0 (imp p1 p2))) (imp (imp (imp p0 (imp p1 p2)) (imp (imp p3 p1) (imp p4 p1))) (imp p5 (imp (imp p3 p1) (imp p4 p1))))
    (r8_certificate_1 p3 p1 p4 p2 p0)
    (r8_certificate_0 (imp (imp p3 p1) (imp p4 p1)) (imp p1 p2) (imp p0 (imp p1 p2)) p5))

private def r8_certificate_3 (p0 p1 p2 : Nat) :
  KDerivation (imp p0 (imp (imp p1 p2) (imp p2 (imp p1 p2)))) :=
  (mpCode (imp (imp (imp (imp 0 p2) (imp p1 p2)) (imp p2 (imp p1 p2))) (imp (imp p1 p2) (imp p2 (imp p1 p2)))) (imp p0 (imp (imp p1 p2) (imp p2 (imp p1 p2))))
    (r8_certificate_1 0 p2 p1 (imp p1 p2) (imp p1 p2))
    (r8_certificate_1 (imp 0 p2) (imp p1 p2) p2 (imp p2 (imp p1 p2)) p0))

private def r8_certificate_4 (p0 p1 : Nat) :
  KDerivation (imp (imp p0 p1) (imp p1 (imp p0 p1))) :=
  (mpCode (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) (imp (imp p0 p1) (imp p1 (imp p0 p1)))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_3 (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) p0 p1))

private def r8_certificate_5 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) (imp p1 (imp p0 p1))) p2) (imp p3 p2)) :=
  (mpCode (imp (imp p2 0) (imp (imp p0 p1) (imp p1 (imp p0 p1)))) (imp (imp (imp (imp p0 p1) (imp p1 (imp p0 p1))) p2) (imp p3 p2))
    (r8_certificate_3 (imp p2 0) p0 p1)
    (r8_certificate_0 p2 0 (imp (imp p0 p1) (imp p1 (imp p0 p1))) p3))

private def r8_certificate_7 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 p0)) p1) (imp p2 p1)) :=
  (mpCode (imp (imp p1 p0) (imp p0 (imp p1 p0))) (imp (imp (imp p0 (imp p1 p0)) p1) (imp p2 p1))
    (r8_certificate_4 p1 p0)
    (r8_certificate_0 p1 p0 (imp p0 (imp p1 p0)) p2))

private def r8_certificate_12 (p0 p1 p2 : Nat) :
  KDerivation (imp p0 (imp (imp p1 p2) (imp p2 p2))) :=
  (mpCode (imp (imp (imp 0 (imp (imp p2 p2) 0)) (imp p2 p2)) (imp (imp p1 p2) (imp p2 p2))) (imp p0 (imp (imp p1 p2) (imp p2 p2)))
    (r8_certificate_7 0 (imp p2 p2) (imp p1 p2))
    (r8_certificate_2 (imp 0 (imp (imp p2 p2) 0)) p2 p2 p1 p2 p0))

private def r8_certificate_14 (p0 p1 : Nat) :
  KDerivation (imp (imp p0 p1) (imp p1 p1)) :=
  (mpCode (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) (imp (imp p0 p1) (imp p1 p1))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_12 (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) p0 p1))

private def r8_certificate_18 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp p0 p0) p1) (imp p2 p1)) :=
  (mpCode (imp (imp p1 p0) (imp p0 p0)) (imp (imp (imp p0 p0) p1) (imp p2 p1))
    (r8_certificate_14 p1 p0)
    (r8_certificate_0 p1 p0 (imp p0 p0) p2))

private def r8_certificate_20 (p0 p1 : Nat) :
  KDerivation (imp (imp p0 p1) (imp p0 p1)) :=
  (mpCode (imp (imp (imp (imp 0 0) (imp 0 (imp 0 0))) p1) (imp p0 p1)) (imp (imp p0 p1) (imp p0 p1))
    (r8_certificate_5 0 0 p1 p0)
    (r8_certificate_14 (imp (imp (imp 0 0) (imp 0 (imp 0 0))) p1) (imp p0 p1)))

private def r8_certificate_22 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp p0 p1) p0) (imp p2 p0)) :=
  (mpCode (imp (imp p0 p1) (imp p0 p1)) (imp (imp (imp p0 p1) p0) (imp p2 p0))
    (r8_certificate_20 p0 p1)
    (r8_certificate_0 p0 p1 (imp p0 p1) p2))

private def r8_certificate_24 (p0 p1 : Nat) :
  KDerivation (imp p0 (imp p1 p1)) :=
  (mpCode (imp (imp p1 p1) (imp p1 p1)) (imp p0 (imp p1 p1))
    (r8_certificate_20 p1 p1)
    (r8_certificate_18 p1 (imp p1 p1) p0))

private def r8_certificate_25 (p0 : Nat) :
  KDerivation (imp p0 p0) :=
  (mpCode (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) (imp p0 p0)
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_24 (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) p0))

private def r8_certificate_29 (p0 p1 p2 : Nat) :
  KDerivation (imp p0 (imp p1 (imp p2 p1))) :=
  (mpCode (imp (imp (imp p1 p1) (imp p2 p1)) (imp p1 (imp p2 p1))) (imp p0 (imp p1 (imp p2 p1)))
    (r8_certificate_18 p1 (imp p2 p1) p1)
    (r8_certificate_1 p1 p1 p2 (imp p2 p1) p0))

private def r8_certificate_36 (p0 p1 : Nat) :
  KDerivation (imp p0 (imp p1 p0)) :=
  (mpCode (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) (imp p0 (imp p1 p0))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_29 (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) p0 p1))

private def r8_certificate_37 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 p0)) p2) (imp p3 p2)) :=
  (mpCode (imp (imp p2 0) (imp p0 (imp p1 p0))) (imp (imp (imp p0 (imp p1 p0)) p2) (imp p3 p2))
    (r8_certificate_29 (imp p2 0) p0 p1)
    (r8_certificate_0 p2 0 (imp p0 (imp p1 p0)) p3))

private def r8_certificate_54 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 p1) (imp p1 p2)) (imp p3 (imp p1 p2))) :=
  (mpCode (imp (imp (imp p1 p2) p1) (imp p0 p1)) (imp (imp (imp p0 p1) (imp p1 p2)) (imp p3 (imp p1 p2)))
    (r8_certificate_22 p1 p2 p0)
    (r8_certificate_0 (imp p1 p2) p1 (imp p0 p1) p3))

private def r8_certificate_67 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp p0 (imp (imp (imp p1 (imp p2 p3)) p2) (imp p4 p2))) :=
  (mpCode (imp (imp (imp p2 p3) (imp p1 (imp p2 p3))) (imp (imp (imp p1 (imp p2 p3)) p2) (imp p4 p2))) (imp p0 (imp (imp (imp p1 (imp p2 p3)) p2) (imp p4 p2)))
    (r8_certificate_0 p2 p3 (imp p1 (imp p2 p3)) p4)
    (r8_certificate_37 (imp p2 p3) p1 (imp (imp (imp p1 (imp p2 p3)) p2) (imp p4 p2)) p0))

private def r8_certificate_82 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 p2)) (imp p3 p1)) (imp p4 (imp p3 p1))) :=
  (mpCode (imp (imp (imp p3 p1) (imp p1 p2)) (imp p0 (imp p1 p2))) (imp (imp (imp p0 (imp p1 p2)) (imp p3 p1)) (imp p4 (imp p3 p1)))
    (r8_certificate_54 p3 p1 p2 p0)
    (r8_certificate_0 (imp p3 p1) (imp p1 p2) (imp p0 (imp p1 p2)) p4))

private def r8_certificate_88 (p0 p1 p2 p3 p4 p5 : Nat) :
  KDerivation (imp (imp (imp (imp (imp p0 (imp p1 p2)) p1) (imp p3 p1)) p4) (imp p5 p4)) :=
  (mpCode (imp (imp p4 0) (imp (imp (imp p0 (imp p1 p2)) p1) (imp p3 p1))) (imp (imp (imp (imp (imp p0 (imp p1 p2)) p1) (imp p3 p1)) p4) (imp p5 p4))
    (r8_certificate_67 (imp p4 0) p0 p1 p2 p3)
    (r8_certificate_0 p4 0 (imp (imp (imp p0 (imp p1 p2)) p1) (imp p3 p1)) p5))

private def r8_certificate_116 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp (imp (imp (imp p1 p2) p3) p2) (imp p1 p2))) :=
  (mpCode (imp (imp (imp p2 0) (imp (imp p1 p2) p3)) (imp (imp (imp (imp p1 p2) p3) p2) (imp p1 p2))) (imp p0 (imp (imp (imp (imp p1 p2) p3) p2) (imp p1 p2)))
    (r8_certificate_0 p2 0 (imp (imp p1 p2) p3) p1)
    (r8_certificate_82 (imp p2 0) (imp p1 p2) p3 (imp (imp (imp p1 p2) p3) p2) p0))

private def r8_certificate_120 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) p2) p1) (imp p0 p1)) :=
  (mpCode (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) (imp (imp (imp (imp p0 p1) p2) p1) (imp p0 p1))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_116 (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) p0 p1 p2))

private def r8_certificate_122 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 p1) (imp (imp p0 p1) p2)) (imp p3 (imp (imp p0 p1) p2))) :=
  (mpCode (imp (imp (imp (imp p0 p1) p2) p1) (imp p0 p1)) (imp (imp (imp p0 p1) (imp (imp p0 p1) p2)) (imp p3 (imp (imp p0 p1) p2)))
    (r8_certificate_120 p0 p1 p2)
    (r8_certificate_0 (imp (imp p0 p1) p2) p1 (imp p0 p1) p3))

private def r8_certificate_168 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp p0 (imp p1 (imp (imp (imp p2 (imp p3 p4)) p3) p3))) :=
  (mpCode (imp (imp (imp (imp p2 (imp p3 p4)) p3) (imp (imp (imp p2 (imp p3 p4)) p3) p3)) (imp p1 (imp (imp (imp p2 (imp p3 p4)) p3) p3))) (imp p0 (imp p1 (imp (imp (imp p2 (imp p3 p4)) p3) p3)))
    (r8_certificate_122 (imp p2 (imp p3 p4)) p3 p3 p1)
    (r8_certificate_88 p2 p3 p4 (imp (imp p2 (imp p3 p4)) p3) (imp p1 (imp (imp (imp p2 (imp p3 p4)) p3) p3)) p0))

private def r8_certificate_170 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp (imp (imp p1 (imp p2 p3)) p2) p2)) :=
  (mpCode (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) (imp p0 (imp (imp (imp p1 (imp p2 p3)) p2) p2))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_168 (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) p0 p1 p2 p3))

private def r8_certificate_174 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 p2)) p1) p1) :=
  (mpCode (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) (imp (imp (imp p0 (imp p1 p2)) p1) p1)
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_170 (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) p0 p1 p2))

private def r8_certificate_176 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp p0 (imp p1 (imp p0 p2))) (imp p3 (imp p1 (imp p0 p2)))) :=
  (mpCode (imp (imp (imp p1 (imp p0 p2)) p0) p0) (imp (imp p0 (imp p1 (imp p0 p2))) (imp p3 (imp p1 (imp p0 p2))))
    (r8_certificate_174 p1 p0 p2)
    (r8_certificate_0 (imp p1 (imp p0 p2)) p0 p0 p3))

private def r8_certificate_183 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp (imp p1 p2) (imp (imp (imp p2 p3) p1) p2))) :=
  (mpCode (imp (imp (imp p2 p3) p1) (imp (imp p1 p2) (imp (imp (imp p2 p3) p1) p2))) (imp p0 (imp (imp p1 p2) (imp (imp (imp p2 p3) p1) p2)))
    (r8_certificate_0 p2 p3 p1 (imp (imp p2 p3) p1))
    (r8_certificate_176 (imp (imp p2 p3) p1) (imp p1 p2) p2 p0))

private def r8_certificate_188 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 p1) (imp (imp (imp p1 p2) p0) p1)) :=
  (mpCode (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) (imp (imp p0 p1) (imp (imp (imp p1 p2) p0) p1))
    (r8_certificate_0 0 0 0 0)
    (r8_certificate_183 (imp (imp (imp 0 0) 0) (imp (imp 0 0) (imp 0 0))) p0 p1 p2))

private def r8_certificate_196 (p0 p1 : Nat) :
  KDerivation (imp (imp (imp p0 p1) p0) p0) :=
  (mpCode (imp p0 p0) (imp (imp (imp p0 p1) p0) p0)
    (r8_certificate_25 p0)
    (r8_certificate_188 p0 p0 p1))

private def r8_certificate_4463 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 p2)) p1) (imp p3 p1)) :=
  (mpCode (imp (imp p1 p2) (imp p0 (imp p1 p2))) (imp (imp (imp p0 (imp p1 p2)) p1) (imp p3 p1))
    (r8_certificate_36 (imp p1 p2) p0)
    (r8_certificate_0 p1 p2 (imp p0 (imp p1 p2)) p3))

private def r8_certificate_4464 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp p0 p1) (imp p2 (imp p1 p3))) (imp p4 (imp p2 (imp p1 p3)))) :=
  (mpCode (imp (imp (imp p2 (imp p1 p3)) p1) (imp p0 p1)) (imp (imp (imp p0 p1) (imp p2 (imp p1 p3))) (imp p4 (imp p2 (imp p1 p3))))
    (r8_certificate_4463 p2 p1 p3 p0)
    (r8_certificate_0 (imp p2 (imp p1 p3)) p1 (imp p0 p1) p4))

private def r8_certificate_4467 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 (imp p0 p1)) (imp p2 (imp p0 p1))) :=
  (mpCode (imp (imp (imp p0 p1) p0) p0) (imp (imp p0 (imp p0 p1)) (imp p2 (imp p0 p1)))
    (r8_certificate_196 p0 p1)
    (r8_certificate_0 (imp p0 p1) p0 p0 p2))

private def r8_certificate_4468 (p0 p1 p2 : Nat) :
  KDerivation (imp p0 (imp (imp p1 (imp p1 p2)) (imp p1 p2))) :=
  (mpCode (imp (imp p1 (imp p1 p2)) (imp (imp p1 (imp p1 p2)) (imp p1 p2))) (imp p0 (imp (imp p1 (imp p1 p2)) (imp p1 p2)))
    (r8_certificate_4467 p1 p2 (imp p1 (imp p1 p2)))
    (r8_certificate_122 p1 (imp p1 p2) (imp p1 p2) p0))

private def r8_certificate_4469 (p0 p1 : Nat) :
  KDerivation (imp (imp p0 (imp p0 p1)) (imp p0 p1)) :=
  (mpCode (imp (imp 0 (imp (imp (imp p0 (imp p0 p1)) (imp p0 p1)) 0)) (imp (imp p0 (imp p0 p1)) (imp p0 p1))) (imp (imp p0 (imp p0 p1)) (imp p0 p1))
    (r8_certificate_4468 (imp 0 (imp (imp (imp p0 (imp p0 p1)) (imp p0 p1)) 0)) p0 p1)
    (r8_certificate_174 0 (imp (imp p0 (imp p0 p1)) (imp p0 p1)) 0))

private def r8_certificate_4470 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp p0 p1) (imp p1 p2)) (imp p1 p2)) :=
  (mpCode (imp (imp (imp p0 p1) (imp p1 p2)) (imp (imp (imp p0 p1) (imp p1 p2)) (imp p1 p2))) (imp (imp (imp p0 p1) (imp p1 p2)) (imp p1 p2))
    (r8_certificate_54 p0 p1 p2 (imp (imp p0 p1) (imp p1 p2)))
    (r8_certificate_4469 (imp (imp p0 p1) (imp p1 p2)) (imp p1 p2)))

private def r8_certificate_4471 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 p1) (imp p2 p0)) (imp p3 (imp p2 p0))) :=
  (mpCode (imp (imp (imp p2 p0) (imp p0 p1)) (imp p0 p1)) (imp (imp (imp p0 p1) (imp p2 p0)) (imp p3 (imp p2 p0)))
    (r8_certificate_4470 p2 p0 p1)
    (r8_certificate_0 (imp p2 p0) (imp p0 p1) (imp p0 p1) p3))

private def r8_certificate_4472 (p0 p1 p2 : Nat) :
  KDerivation (imp p0 (imp p1 (imp p2 p0))) :=
  (mpCode (imp (imp (imp p0 (imp p1 (imp p2 p0))) (imp p2 p0)) (imp p1 (imp p2 p0))) (imp p0 (imp p1 (imp p2 p0)))
    (r8_certificate_4471 p0 (imp p1 (imp p2 p0)) p2 p1)
    (r8_certificate_120 p0 (imp p1 (imp p2 p0)) (imp p2 p0)))

private def r8_certificate_4473 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 (imp p2 p3))) p2) (imp p4 p2)) :=
  (mpCode (imp (imp p2 (imp p1 (imp p2 p3))) (imp p0 (imp p1 (imp p2 p3)))) (imp (imp (imp p0 (imp p1 (imp p2 p3))) p2) (imp p4 p2))
    (r8_certificate_176 p2 p1 p3 p0)
    (r8_certificate_0 p2 (imp p1 (imp p2 p3)) (imp p0 (imp p1 (imp p2 p3))) p4))

private def r8_certificate_4474 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 (imp p2 p3))) p2) p2) :=
  (mpCode (imp (imp (imp p0 (imp p1 (imp p2 p3))) p2) (imp (imp (imp p0 (imp p1 (imp p2 p3))) p2) p2)) (imp (imp (imp p0 (imp p1 (imp p2 p3))) p2) p2)
    (r8_certificate_4473 p0 p1 p2 p3 (imp (imp p0 (imp p1 (imp p2 p3))) p2))
    (r8_certificate_4469 (imp (imp p0 (imp p1 (imp p2 p3))) p2) p2))

private def r8_certificate_4475 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp p0 (imp p1 (imp p2 (imp p0 p3)))) (imp p4 (imp p1 (imp p2 (imp p0 p3))))) :=
  (mpCode (imp (imp (imp p1 (imp p2 (imp p0 p3))) p0) p0) (imp (imp p0 (imp p1 (imp p2 (imp p0 p3)))) (imp p4 (imp p1 (imp p2 (imp p0 p3)))))
    (r8_certificate_4474 p1 p2 p0 p3)
    (r8_certificate_0 (imp p1 (imp p2 (imp p0 p3))) p0 p0 p4))

private def r8_certificate_4476 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp p0 (imp p1 (imp p2 (imp p0 p3)))) (imp p1 (imp p2 (imp p0 p3)))) :=
  (mpCode (imp (imp p0 (imp p1 (imp p2 (imp p0 p3)))) (imp (imp p0 (imp p1 (imp p2 (imp p0 p3)))) (imp p1 (imp p2 (imp p0 p3))))) (imp (imp p0 (imp p1 (imp p2 (imp p0 p3)))) (imp p1 (imp p2 (imp p0 p3))))
    (r8_certificate_4475 p0 p1 p2 p3 (imp p0 (imp p1 (imp p2 (imp p0 p3)))))
    (r8_certificate_4469 (imp p0 (imp p1 (imp p2 (imp p0 p3)))) (imp p1 (imp p2 (imp p0 p3)))))

private def r8_certificate_4477 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 (imp p1 (imp p0 p2))) (imp p1 (imp p0 p2))) :=
  (mpCode (imp (imp p0 (imp p1 (imp p0 p2))) (imp (imp p0 (imp p1 (imp p0 p2))) (imp p1 (imp p0 p2)))) (imp (imp p0 (imp p1 (imp p0 p2))) (imp p1 (imp p0 p2)))
    (r8_certificate_176 p0 p1 p2 (imp p0 (imp p1 (imp p0 p2))))
    (r8_certificate_4469 (imp p0 (imp p1 (imp p0 p2))) (imp p1 (imp p0 p2))))

private def r8_certificate_4478 (p0 p1 p2 p3 p4 p5 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 p2)) (imp p3 (imp p2 p4))) (imp p5 (imp p3 (imp p2 p4)))) :=
  (mpCode (imp (imp (imp p3 (imp p2 p4)) (imp p1 p2)) (imp p0 (imp p1 p2))) (imp (imp (imp p0 (imp p1 p2)) (imp p3 (imp p2 p4))) (imp p5 (imp p3 (imp p2 p4))))
    (r8_certificate_82 p3 p2 p4 p1 p0)
    (r8_certificate_0 (imp p3 (imp p2 p4)) (imp p1 p2) (imp p0 (imp p1 p2)) p5))

private def r8_certificate_4479 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp (imp (imp p1 p2) p3) (imp p2 p3))) :=
  (mpCode (imp (imp (imp p3 0) (imp p1 p2)) (imp (imp (imp p1 p2) p3) (imp p2 p3))) (imp p0 (imp (imp (imp p1 p2) p3) (imp p2 p3)))
    (r8_certificate_0 p3 0 (imp p1 p2) p2)
    (r8_certificate_4478 (imp p3 0) p1 p2 (imp (imp p1 p2) p3) p3 p0))

private def r8_certificate_4480 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp p0 p1) p2) (imp p1 p2)) :=
  (mpCode (imp (imp 0 (imp (imp (imp (imp p0 p1) p2) (imp p1 p2)) 0)) (imp (imp (imp p0 p1) p2) (imp p1 p2))) (imp (imp (imp p0 p1) p2) (imp p1 p2))
    (r8_certificate_4479 (imp 0 (imp (imp (imp (imp p0 p1) p2) (imp p1 p2)) 0)) p0 p1 p2)
    (r8_certificate_174 0 (imp (imp (imp p0 p1) p2) (imp p1 p2)) 0))

private def r8_certificate_4481 (p0 p1 p2 : Nat) :
  KDerivation (imp p0 (imp (imp p0 p1) (imp p2 p1))) :=
  (mpCode (imp (imp (imp p1 0) p0) (imp (imp p0 p1) (imp p2 p1))) (imp p0 (imp (imp p0 p1) (imp p2 p1)))
    (r8_certificate_0 p1 0 p0 p2)
    (r8_certificate_4480 (imp p1 0) p0 (imp (imp p0 p1) (imp p2 p1))))

private def r8_certificate_4482 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp (imp (imp p0 p1) (imp p2 p1)) p3) p0) (imp (imp p0 p1) (imp p2 p1))) :=
  (mpCode (imp p0 (imp (imp p0 p1) (imp p2 p1))) (imp (imp (imp (imp (imp p0 p1) (imp p2 p1)) p3) p0) (imp (imp p0 p1) (imp p2 p1)))
    (r8_certificate_4481 p0 p1 p2)
    (r8_certificate_188 p0 (imp (imp p0 p1) (imp p2 p1)) p3))

private def r8_certificate_4483 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) p2) (imp (imp p1 p3) p1)) (imp p0 p1)) :=
  (mpCode (imp (imp (imp p1 p3) p1) (imp p0 p1)) (imp (imp (imp (imp p0 p1) p2) (imp (imp p1 p3) p1)) (imp p0 p1))
    (r8_certificate_22 p1 p3 p0)
    (r8_certificate_188 (imp (imp p1 p3) p1) (imp p0 p1) p2))

private def r8_certificate_4484 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) p2) (imp (imp p3 (imp p1 p4)) p1)) (imp p0 p1)) :=
  (mpCode (imp (imp (imp p3 (imp p1 p4)) p1) (imp p0 p1)) (imp (imp (imp (imp p0 p1) p2) (imp (imp p3 (imp p1 p4)) p1)) (imp p0 p1))
    (r8_certificate_4463 p3 p1 p4 p0)
    (r8_certificate_188 (imp (imp p3 (imp p1 p4)) p1) (imp p0 p1) p2))

private def r8_certificate_4485 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp (imp (imp p0 p1) p2) (imp p3 p2)) p0) (imp p4 p0)) :=
  (mpCode (imp (imp p0 p1) (imp (imp (imp p0 p1) p2) (imp p3 p2))) (imp (imp (imp (imp (imp p0 p1) p2) (imp p3 p2)) p0) (imp p4 p0))
    (r8_certificate_4481 (imp p0 p1) p2 p3)
    (r8_certificate_0 p0 p1 (imp (imp (imp p0 p1) p2) (imp p3 p2)) p4))

private def r8_certificate_4486 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp (imp (imp p0 p1) p2) (imp p3 p2)) p0) p0) :=
  (mpCode (imp (imp (imp (imp (imp p0 p1) p2) (imp p3 p2)) p0) (imp (imp (imp (imp (imp p0 p1) p2) (imp p3 p2)) p0) p0)) (imp (imp (imp (imp (imp p0 p1) p2) (imp p3 p2)) p0) p0)
    (r8_certificate_4485 p0 p1 p2 p3 (imp (imp (imp (imp p0 p1) p2) (imp p3 p2)) p0))
    (r8_certificate_4469 (imp (imp (imp (imp p0 p1) p2) (imp p3 p2)) p0) p0))

private def r8_certificate_4487 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp (imp (imp p0 (imp (imp p1 p2) p3)) (imp p1 p2)) p4) p2) (imp p1 p2)) :=
  (mpCode (imp (imp (imp (imp (imp (imp (imp p0 (imp (imp p1 p2) p3)) (imp p1 p2)) p4) p2) (imp p1 p2)) (imp (imp p0 (imp (imp p1 p2) p3)) (imp p1 p2))) (imp (imp p0 (imp (imp p1 p2) p3)) (imp p1 p2))) (imp (imp (imp (imp (imp p0 (imp (imp p1 p2) p3)) (imp p1 p2)) p4) p2) (imp p1 p2))
    (r8_certificate_4486 (imp (imp p0 (imp (imp p1 p2) p3)) (imp p1 p2)) p4 p2 p1)
    (r8_certificate_4484 (imp (imp (imp (imp p0 (imp (imp p1 p2) p3)) (imp p1 p2)) p4) p2) (imp p1 p2) (imp (imp p0 (imp (imp p1 p2) p3)) (imp p1 p2)) p0 p3))

private def r8_certificate_4488 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 (imp (imp (imp p1 p2) p1) p3)) (imp (imp p1 p2) p1)) p1) :=
  (mpCode (imp (imp (imp (imp (imp p0 (imp (imp (imp p1 p2) p1) p3)) (imp (imp p1 p2) p1)) p1) p1) (imp (imp p1 p2) p1)) (imp (imp (imp p0 (imp (imp (imp p1 p2) p1) p3)) (imp (imp p1 p2) p1)) p1)
    (r8_certificate_4487 p0 (imp p1 p2) p1 p3 p1)
    (r8_certificate_4483 (imp (imp p0 (imp (imp (imp p1 p2) p1) p3)) (imp (imp p1 p2) p1)) p1 p1 p2))

private def r8_certificate_4489 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 p1) (imp (imp (imp p0 p2) p0) p1)) :=
  (mpCode (imp (imp (imp (imp p0 p1) (imp (imp (imp p0 p2) p0) p1)) (imp (imp p0 p2) p0)) p0) (imp (imp p0 p1) (imp (imp (imp p0 p2) p0) p1))
    (r8_certificate_4488 (imp p0 p1) p0 p2 p1)
    (r8_certificate_4482 p0 p1 (imp (imp p0 p2) p0) (imp (imp p0 p2) p0)))

private def r8_certificate_4490 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp (imp p0 (imp p1 p2)) p3) (imp p1 (imp p1 p2))) (imp p0 (imp p1 p2))) :=
  (mpCode (imp (imp p1 (imp p1 p2)) (imp p0 (imp p1 p2))) (imp (imp (imp (imp p0 (imp p1 p2)) p3) (imp p1 (imp p1 p2))) (imp p0 (imp p1 p2)))
    (r8_certificate_4467 p1 p2 p0)
    (r8_certificate_188 (imp p1 (imp p1 p2)) (imp p0 (imp p1 p2)) p3))

private def r8_certificate_4491 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 p1) p0) (imp (imp p0 p2) (imp p3 p2))) :=
  (mpCode (imp p0 (imp (imp p0 p2) (imp p3 p2))) (imp (imp (imp p0 p1) p0) (imp (imp p0 p2) (imp p3 p2)))
    (r8_certificate_4481 p0 p2 p3)
    (r8_certificate_4489 p0 (imp (imp p0 p2) (imp p3 p2)) p1))

private def r8_certificate_4492 (p0 p1 : Nat) :
  KDerivation (imp p0 (imp (imp p0 p1) p1)) :=
  (mpCode (imp (imp (imp p0 (imp (imp p0 p1) p1)) p0) (imp (imp p0 p1) (imp (imp p0 p1) p1))) (imp p0 (imp (imp p0 p1) p1))
    (r8_certificate_4491 p0 (imp (imp p0 p1) p1) p1 (imp p0 p1))
    (r8_certificate_4490 p0 (imp p0 p1) p1 p0))

private def r8_certificate_4493 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp p0 p1) p0) (imp (imp p0 p2) p2)) :=
  (mpCode (imp p0 (imp (imp p0 p2) p2)) (imp (imp (imp p0 p1) p0) (imp (imp p0 p2) p2))
    (r8_certificate_4492 p0 p2)
    (r8_certificate_4489 p0 (imp (imp p0 p2) p2) p1))

private def r8_certificate_4494 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) p1) (imp p0 p2)) (imp p3 (imp p0 p2))) :=
  (mpCode (imp (imp (imp p0 p2) p0) (imp (imp p0 p1) p1)) (imp (imp (imp (imp p0 p1) p1) (imp p0 p2)) (imp p3 (imp p0 p2)))
    (r8_certificate_4493 p0 p2 p1)
    (r8_certificate_0 (imp p0 p2) p0 (imp (imp p0 p1) p1) p3))

private def r8_certificate_4495 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) p1) (imp p0 p2)) (imp p0 p2)) :=
  (mpCode (imp (imp (imp (imp p0 p1) p1) (imp p0 p2)) (imp (imp (imp (imp p0 p1) p1) (imp p0 p2)) (imp p0 p2))) (imp (imp (imp (imp p0 p1) p1) (imp p0 p2)) (imp p0 p2))
    (r8_certificate_4494 p0 p1 p2 (imp (imp (imp p0 p1) p1) (imp p0 p2)))
    (r8_certificate_4469 (imp (imp (imp p0 p1) p1) (imp p0 p2)) (imp p0 p2)))

private def r8_certificate_4496 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp (imp p0 (imp p1 p2)) p3) p2) (imp p0 (imp p1 p2))) :=
  (mpCode (imp p2 (imp p0 (imp p1 p2))) (imp (imp (imp (imp p0 (imp p1 p2)) p3) p2) (imp p0 (imp p1 p2)))
    (r8_certificate_4472 p2 p0 p1)
    (r8_certificate_188 p2 (imp p0 (imp p1 p2)) p3))

private def r8_certificate_4497 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp p1 (imp (imp p0 p2) (imp p3 p2)))) :=
  (mpCode (imp (imp (imp p0 (imp p1 (imp (imp p0 p2) (imp p3 p2)))) p0) (imp (imp p0 p2) (imp p3 p2))) (imp p0 (imp p1 (imp (imp p0 p2) (imp p3 p2))))
    (r8_certificate_4491 p0 (imp p1 (imp (imp p0 p2) (imp p3 p2))) p2 p3)
    (r8_certificate_4496 p0 p1 (imp (imp p0 p2) (imp p3 p2)) p0))

private def r8_certificate_4498 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp (imp (imp (imp p0 p1) p1) p2) (imp p3 p2))) :=
  (mpCode (imp (imp (imp p0 p1) p1) (imp p0 (imp (imp (imp (imp p0 p1) p1) p2) (imp p3 p2)))) (imp p0 (imp (imp (imp (imp p0 p1) p1) p2) (imp p3 p2)))
    (r8_certificate_4497 (imp (imp p0 p1) p1) p0 p2 p3)
    (r8_certificate_4495 p0 p1 (imp (imp (imp (imp p0 p1) p1) p2) (imp p3 p2))))

private def r8_certificate_4499 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) p1) p2) (imp p0 p2)) :=
  (mpCode (imp p0 (imp (imp (imp (imp p0 p1) p1) p2) (imp p0 p2))) (imp (imp (imp (imp p0 p1) p1) p2) (imp p0 p2))
    (r8_certificate_4498 p0 p1 p2 p0)
    (r8_certificate_4477 p0 (imp (imp (imp p0 p1) p1) p2) p2))

private def r8_certificate_4500 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 p1) (imp p2 (imp p1 p3))) (imp p2 (imp p1 p3))) :=
  (mpCode (imp (imp (imp p0 p1) (imp p2 (imp p1 p3))) (imp (imp (imp p0 p1) (imp p2 (imp p1 p3))) (imp p2 (imp p1 p3)))) (imp (imp (imp p0 p1) (imp p2 (imp p1 p3))) (imp p2 (imp p1 p3)))
    (r8_certificate_4464 p0 p1 p2 p3 (imp (imp p0 p1) (imp p2 (imp p1 p3))))
    (r8_certificate_4469 (imp (imp p0 p1) (imp p2 (imp p1 p3))) (imp p2 (imp p1 p3))))

private def r8_certificate_4501 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp p0 (imp p1 (imp (imp (imp p2 p0) p3) (imp p4 p3)))) :=
  (mpCode (imp (imp p2 p0) (imp p1 (imp (imp (imp p2 p0) p3) (imp p4 p3)))) (imp p0 (imp p1 (imp (imp (imp p2 p0) p3) (imp p4 p3))))
    (r8_certificate_4497 (imp p2 p0) p1 p3 p4)
    (r8_certificate_4480 p2 p0 (imp p1 (imp (imp (imp p2 p0) p3) (imp p4 p3)))))

private def r8_certificate_4502 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp p0 (imp (imp (imp p1 (imp (imp p0 p2) p2)) p3) (imp p4 p3))) :=
  (mpCode (imp (imp (imp p0 p2) p2) (imp p0 (imp (imp (imp p1 (imp (imp p0 p2) p2)) p3) (imp p4 p3)))) (imp p0 (imp (imp (imp p1 (imp (imp p0 p2) p2)) p3) (imp p4 p3)))
    (r8_certificate_4501 (imp (imp p0 p2) p2) p0 p1 p3 p4)
    (r8_certificate_4495 p0 p2 (imp (imp (imp p1 (imp (imp p0 p2) p2)) p3) (imp p4 p3))))

private def r8_certificate_4503 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp p0 (imp (imp (imp p1 p2) p3) p3)) p4) (imp p2 p4)) :=
  (mpCode (imp (imp p1 p2) (imp (imp (imp p0 (imp (imp (imp p1 p2) p3) p3)) p4) (imp p2 p4))) (imp (imp (imp p0 (imp (imp (imp p1 p2) p3) p3)) p4) (imp p2 p4))
    (r8_certificate_4502 (imp p1 p2) p0 p3 p4 p2)
    (r8_certificate_4500 p1 p2 (imp (imp p0 (imp (imp (imp p1 p2) p3) p3)) p4) p4))

private def r8_certificate_4504 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 p1) p2) (imp (imp (imp p3 p0) p2) p2)) :=
  (mpCode (imp (imp (imp (imp (imp p0 p1) p2) (imp (imp (imp p3 p0) p2) p2)) p1) (imp p0 p1)) (imp (imp (imp p0 p1) p2) (imp (imp (imp p3 p0) p2) p2))
    (r8_certificate_4503 (imp (imp p0 p1) p2) p3 p0 p2 p1)
    (r8_certificate_4482 (imp p0 p1) p2 (imp (imp p3 p0) p2) p1))

private def r8_certificate_4505 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp (imp (imp p0 p1) p1) p2) p0) (imp (imp p0 p1) p1)) :=
  (mpCode (imp p0 (imp (imp p0 p1) p1)) (imp (imp (imp (imp (imp p0 p1) p1) p2) p0) (imp (imp p0 p1) p1))
    (r8_certificate_4492 p0 p1)
    (r8_certificate_188 p0 (imp (imp p0 p1) p1) p2))

private def r8_certificate_4506 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp p0 p1) (imp p2 p0)) (imp p2 p0)) :=
  (mpCode (imp (imp (imp p0 p1) (imp p2 p0)) (imp (imp (imp p0 p1) (imp p2 p0)) (imp p2 p0))) (imp (imp (imp p0 p1) (imp p2 p0)) (imp p2 p0))
    (r8_certificate_4471 p0 p1 p2 (imp (imp p0 p1) (imp p2 p0)))
    (r8_certificate_4469 (imp (imp p0 p1) (imp p2 p0)) (imp p2 p0)))

private def r8_certificate_4507 (p0 p1 p2 : Nat) :
  KDerivation (imp p0 (imp p1 (imp (imp p0 p2) p2))) :=
  (mpCode (imp (imp (imp p0 p2) p2) (imp p0 (imp p1 (imp (imp p0 p2) p2)))) (imp p0 (imp p1 (imp (imp p0 p2) p2)))
    (r8_certificate_4472 (imp (imp p0 p2) p2) p0 p1)
    (r8_certificate_4495 p0 p2 (imp p1 (imp (imp p0 p2) p2))))

private def r8_certificate_4508 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp p1 (imp (imp (imp p2 p0) p3) p3))) :=
  (mpCode (imp (imp p2 p0) (imp p1 (imp (imp (imp p2 p0) p3) p3))) (imp p0 (imp p1 (imp (imp (imp p2 p0) p3) p3)))
    (r8_certificate_4507 (imp p2 p0) p1 p3)
    (r8_certificate_4480 p2 p0 (imp p1 (imp (imp (imp p2 p0) p3) p3))))

private def r8_certificate_4509 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp (imp (imp p1 (imp (imp p0 p2) p2)) p3) p3)) :=
  (mpCode (imp (imp (imp p0 p2) p2) (imp p0 (imp (imp (imp p1 (imp (imp p0 p2) p2)) p3) p3))) (imp p0 (imp (imp (imp p1 (imp (imp p0 p2) p2)) p3) p3))
    (r8_certificate_4508 (imp (imp p0 p2) p2) p0 p1 p3)
    (r8_certificate_4495 p0 p2 (imp (imp (imp p1 (imp (imp p0 p2) p2)) p3) p3)))

private def r8_certificate_4510 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 (imp (imp (imp p1 p2) p3) p3)) p1) p1) :=
  (mpCode (imp (imp p1 p2) (imp (imp (imp p0 (imp (imp (imp p1 p2) p3) p3)) p1) p1)) (imp (imp (imp p0 (imp (imp (imp p1 p2) p3) p3)) p1) p1)
    (r8_certificate_4509 (imp p1 p2) p0 p3 p1)
    (r8_certificate_4506 p1 p2 (imp (imp p0 (imp (imp (imp p1 p2) p3) p3)) p1)))

private def r8_certificate_4511 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 (imp (imp (imp p0 p1) p2) p2)) (imp (imp (imp p0 p1) p2) p2)) :=
  (mpCode (imp (imp (imp (imp p0 (imp (imp (imp p0 p1) p2) p2)) (imp (imp (imp p0 p1) p2) p2)) p0) p0) (imp (imp p0 (imp (imp (imp p0 p1) p2) p2)) (imp (imp (imp p0 p1) p2) p2))
    (r8_certificate_4510 (imp p0 (imp (imp (imp p0 p1) p2) p2)) p0 p1 p2)
    (r8_certificate_4505 p0 (imp (imp (imp p0 p1) p2) p2) p0))

private def r8_certificate_4512 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 p2)) (imp p3 p1)) (imp p3 p1)) :=
  (mpCode (imp (imp (imp p0 (imp p1 p2)) (imp p3 p1)) (imp (imp (imp p0 (imp p1 p2)) (imp p3 p1)) (imp p3 p1))) (imp (imp (imp p0 (imp p1 p2)) (imp p3 p1)) (imp p3 p1))
    (r8_certificate_82 p0 p1 p2 p3 (imp (imp p0 (imp p1 p2)) (imp p3 p1)))
    (r8_certificate_4469 (imp (imp p0 (imp p1 p2)) (imp p3 p1)) (imp p3 p1)))

private def r8_certificate_4513 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp p0 (imp (imp (imp p1 (imp p2 p3)) p4) p4)) p2) p2) :=
  (mpCode (imp (imp p1 (imp p2 p3)) (imp (imp (imp p0 (imp (imp (imp p1 (imp p2 p3)) p4) p4)) p2) p2)) (imp (imp (imp p0 (imp (imp (imp p1 (imp p2 p3)) p4) p4)) p2) p2)
    (r8_certificate_4509 (imp p1 (imp p2 p3)) p0 p4 p2)
    (r8_certificate_4512 p1 p2 p3 (imp (imp p0 (imp (imp (imp p1 (imp p2 p3)) p4) p4)) p2)))

private def r8_certificate_4514 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp p0 p1) (imp (imp (imp p2 (imp p0 p3)) p1) p1)) :=
  (mpCode (imp (imp (imp (imp p0 p1) (imp (imp (imp p2 (imp p0 p3)) p1) p1)) p0) p0) (imp (imp p0 p1) (imp (imp (imp p2 (imp p0 p3)) p1) p1))
    (r8_certificate_4513 (imp p0 p1) p2 p0 p3 p1)
    (r8_certificate_4482 p0 p1 (imp (imp p2 (imp p0 p3)) p1) p0))

private def r8_certificate_4515 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) (imp p0 p2)) p1) p1) :=
  (mpCode (imp (imp p0 p1) (imp (imp (imp (imp p0 p1) (imp p0 p2)) p1) p1)) (imp (imp (imp (imp p0 p1) (imp p0 p2)) p1) p1)
    (r8_certificate_4514 p0 p1 (imp p0 p1) p2)
    (r8_certificate_4511 (imp p0 p1) (imp p0 p2) p1))

private def r8_certificate_4516 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp p0 (imp (imp p1 p2) (imp p1 p3))) p2) p2) :=
  (mpCode (imp (imp (imp (imp p1 p2) (imp p1 p3)) p2) p2) (imp (imp (imp p0 (imp (imp p1 p2) (imp p1 p3))) p2) p2)
    (r8_certificate_4515 p1 p2 p3)
    (r8_certificate_4504 (imp (imp p1 p2) (imp p1 p3)) p2 p2 p0))

private def r8_certificate_4517 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 (imp p1 p2)) (imp (imp p1 p0) (imp p1 p2))) :=
  (mpCode (imp (imp (imp (imp p0 (imp p1 p2)) (imp (imp p1 p0) (imp p1 p2))) p0) p0) (imp (imp p0 (imp p1 p2)) (imp (imp p1 p0) (imp p1 p2)))
    (r8_certificate_4516 (imp p0 (imp p1 p2)) p1 p0 p2)
    (r8_certificate_4482 p0 (imp p1 p2) (imp p1 p0) p0))

private def r8_certificate_4518 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp p0 p1) (imp p0 (imp (imp p1 p2) (imp p3 p2)))) :=
  (mpCode (imp p1 (imp p0 (imp (imp p1 p2) (imp p3 p2)))) (imp (imp p0 p1) (imp p0 (imp (imp p1 p2) (imp p3 p2))))
    (r8_certificate_4497 p1 p0 p2 p3)
    (r8_certificate_4517 p1 p0 (imp (imp p1 p2) (imp p3 p2))))

private def r8_certificate_4519 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp (imp p0 p1) (imp (imp p1 p2) (imp p3 p2)))) :=
  (mpCode (imp (imp (imp p0 p1) p1) (imp (imp p0 p1) (imp (imp p1 p2) (imp p3 p2)))) (imp p0 (imp (imp p0 p1) (imp (imp p1 p2) (imp p3 p2))))
    (r8_certificate_4518 (imp p0 p1) p1 p2 p3)
    (r8_certificate_4499 p0 p1 (imp (imp p0 p1) (imp (imp p1 p2) (imp p3 p2)))))

private def r8_certificate_4520 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 p1) (imp (imp p1 p2) (imp p0 p2))) :=
  (mpCode (imp p0 (imp (imp p0 p1) (imp (imp p1 p2) (imp p0 p2)))) (imp (imp p0 p1) (imp (imp p1 p2) (imp p0 p2)))
    (r8_certificate_4519 p0 p1 p2 p0)
    (r8_certificate_4476 p0 (imp p0 p1) (imp p1 p2) p2))

private def r8_certificate_4526 (p0 p1 p2 p3 p4 : Nat) :
  KDerivation (imp (imp (imp p0 (imp p1 p2)) p1) (imp (imp p1 p3) (imp p4 p3))) :=
  (mpCode (imp (imp (imp p0 (imp p1 p2)) p1) p1) (imp (imp (imp p0 (imp p1 p2)) p1) (imp (imp p1 p3) (imp p4 p3)))
    (r8_certificate_174 p0 p1 p2)
    (r8_certificate_4518 (imp (imp p0 (imp p1 p2)) p1) p1 p3 p4))

private def r8_certificate_4527 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) (imp p2 p1)) p3) (imp p0 p3)) :=
  (mpCode (imp (imp (imp (imp (imp (imp p0 p1) (imp p2 p1)) p3) (imp p0 p3)) p0) (imp (imp p0 p1) (imp p2 p1))) (imp (imp (imp (imp p0 p1) (imp p2 p1)) p3) (imp p0 p3))
    (r8_certificate_4526 (imp (imp (imp p0 p1) (imp p2 p1)) p3) p0 p3 p1 p2)
    (r8_certificate_4482 (imp (imp p0 p1) (imp p2 p1)) p3 p0 p0))

private def r8_certificate_4528 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 p1) (imp p0 (imp p2 p1))) :=
  (mpCode (imp (imp (imp (imp p0 p1) (imp p2 p1)) (imp p2 p1)) (imp p0 (imp p2 p1))) (imp (imp p0 p1) (imp p0 (imp p2 p1)))
    (r8_certificate_4527 p0 p1 p2 (imp p2 p1))
    (r8_certificate_4499 (imp p0 p1) (imp p2 p1) (imp p0 (imp p2 p1))))

private def r8_certificate_4529 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp p0 p1) (imp p2 (imp p0 (imp p3 p1)))) :=
  (mpCode (imp (imp p0 p1) (imp p0 (imp p3 p1))) (imp (imp p0 p1) (imp p2 (imp p0 (imp p3 p1))))
    (r8_certificate_4528 p0 p1 p3)
    (r8_certificate_4528 (imp p0 p1) (imp p0 (imp p3 p1)) p2))

private def r8_certificate_4530 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp p0 (imp p1 p2)) (imp p0 (imp p1 (imp p3 p2)))) :=
  (mpCode (imp (imp p1 p2) (imp p0 (imp p1 (imp p3 p2)))) (imp (imp p0 (imp p1 p2)) (imp p0 (imp p1 (imp p3 p2))))
    (r8_certificate_4529 p1 p2 p0 p3)
    (r8_certificate_4517 (imp p1 p2) p0 (imp p1 (imp p3 p2))))

private def r8_certificate_4531 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp p0 (imp (imp p0 (imp p1 p2)) (imp p1 (imp p3 p2)))) :=
  (mpCode (imp (imp (imp p0 (imp p1 p2)) (imp p1 p2)) (imp (imp p0 (imp p1 p2)) (imp p1 (imp p3 p2)))) (imp p0 (imp (imp p0 (imp p1 p2)) (imp p1 (imp p3 p2))))
    (r8_certificate_4530 (imp p0 (imp p1 p2)) p1 p2 p3)
    (r8_certificate_4499 p0 (imp p1 p2) (imp (imp p0 (imp p1 p2)) (imp p1 (imp p3 p2)))))

private def r8_certificate_4532 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 (imp p1 p2)) (imp p1 (imp p0 p2))) :=
  (mpCode (imp p0 (imp (imp p0 (imp p1 p2)) (imp p1 (imp p0 p2)))) (imp (imp p0 (imp p1 p2)) (imp p1 (imp p0 p2)))
    (r8_certificate_4531 p0 p1 p2 p0)
    (r8_certificate_4476 p0 (imp p0 (imp p1 p2)) p1 p2))

private def r8_certificate_4533 (p0 p1 p2 p3 : Nat) :
  KDerivation (imp (imp (imp (imp p0 p1) (imp p2 p1)) p3) (imp (imp p2 p0) p3)) :=
  (mpCode (imp (imp p2 p0) (imp (imp p0 p1) (imp p2 p1))) (imp (imp (imp (imp p0 p1) (imp p2 p1)) p3) (imp (imp p2 p0) p3))
    (r8_certificate_4520 p2 p0 p1)
    (r8_certificate_4520 (imp p2 p0) (imp (imp p0 p1) (imp p2 p1)) p3))

private def r8_certificate_4534 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 p1) (imp (imp p0 (imp p1 p2)) (imp p0 p2))) :=
  (mpCode (imp (imp (imp p1 p2) (imp p0 p2)) (imp (imp p0 (imp p1 p2)) (imp p0 p2))) (imp (imp p0 p1) (imp (imp p0 (imp p1 p2)) (imp p0 p2)))
    (r8_certificate_4517 (imp p1 p2) p0 p2)
    (r8_certificate_4533 p1 p2 p0 (imp (imp p0 (imp p1 p2)) (imp p0 p2))))

private def r8_certificate_4535 (p0 p1 p2 : Nat) :
  KDerivation (imp (imp p0 (imp p1 p2)) (imp (imp p0 p1) (imp p0 p2))) :=
  (mpCode (imp (imp p0 p1) (imp (imp p0 (imp p1 p2)) (imp p0 p2))) (imp (imp p0 (imp p1 p2)) (imp (imp p0 p1) (imp p0 p2)))
    (r8_certificate_4534 p0 p1 p2)
    (r8_certificate_4532 (imp p0 p1) (imp p0 (imp p1 p2)) (imp p0 p2)))

def identity (a : Nat) : KDerivation (imp a a) := r8_certificate_25 a

def weakening (a b : Nat) : KDerivation (imp a (imp b a)) := r8_certificate_36 a b

def peirce (a b : Nat) : KDerivation (imp (imp (imp a b) a) a) := r8_certificate_196 a b

def composition (a b c : Nat) :
    KDerivation (imp (imp a b) (imp (imp b c) (imp a c))) := r8_certificate_4520 a b c

def distribution (a b c : Nat) :
    KDerivation (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) := r8_certificate_4535 a b c

end PASoundness.CompactHilbertBasis
