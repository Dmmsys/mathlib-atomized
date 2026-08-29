/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!

# The normalized Moore complex and the alternating face map complex are homotopy equivalent

In this file, when the category `A` is abelian, we obtain the homotopy equivalence
`homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` between the
normalized Moore complex and the alternating face map complex of a simplicial object in `A`.

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Preadditive Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] (X : SimplicialObject C)

/--
Definition of `homotopyPToId` / `homotopyPToId` 的定义

English:
definition homotopyPToId
  signature: : forall q : Nat, Homotopy (P q : K[X] ⟶ _) (𝟙 _)

中文:
定义 homotopyPToId
  签名: : 对任意 q : 自然数, Homotopy (P q : K[X] ⟶ _) (𝟙 _)
-/
noncomputable def homotopyPToId : forall q : Nat, Homotopy (P q : K[X] ⟶ _) (𝟙 _)
  | 0 => Homotopy.refl _
  | q + 1 => by
    refine
      Homotopy.trans (Homotopy.ofEq ?_)
        (Homotopy.trans
          (Homotopy.add (homotopyPToId q) (Homotopy.compLeft (homotopyHσToZero q) (P q)))
          (Homotopy.ofEq ?_))
    · simp only [P_succ, comp_add, comp_id]
    · simp only [add_zero, comp_zero]

/--
Definition of `homotopyQToZero` / `homotopyQToZero` 的定义

English:
definition homotopyQToZero
  signature: (q : Nat)
  body: Homotopy.equivSubZero.toFun (homotopyPToId X q).symm

中文:
定义 homotopyQToZero
  签名: (q : 自然数)
  定义体: Homotopy.equivSubZero.toFun (homotopyPToId X q).symm

Depends on / 依赖: Homotopy, Homotopy.equivSubZero.toFun, equivSubZero, homotopyPToId
-/
def homotopyQToZero (q : Nat) : Homotopy (Q q : K[X] ⟶ _) 0 :=
  Homotopy.equivSubZero.toFun (homotopyPToId X q).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `homotopyPToId_eventually_constant` / 定理 `homotopyPToId_eventually_constant`

English:
theorem homotopyPToId_eventually_constant
  given: {q n : Nat} (hqn : n < q)
  proof: by
  simp only [homotopyHσToZero, AlternatingFaceMapComplex.obj_X, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, add_zero,
    Homotopy.nullHomotopy'_hom, ComplexShape.down_Rel, hσ'_eq_zero hqn (c_mk (n + 1) n rfl),
    dite_eq_ite, ite_self, comp

中文:
定理 homotopyPToId_eventually_constant
  条件: {q n : 自然数} (hqn : n < q)
  证明: by
  simp only [homotopyHσToZero, AlternatingFaceMapComplex.obj_X, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, add_zero,
    Homotopy.nullHomotopy'_hom, ComplexShape.down_Rel, hσ'_eq_zero hqn (c_mk (n + 1) n rfl),
    dite_eq_ite, ite_self, comp

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj_X, ComplexShape, ComplexShape.down_Rel, Homotopy, Homotopy.add_hom, Homotopy.compLeft_hom, Homotopy.nullHomotopy, Homotopy.ofEq_hom, Homotopy.trans_hom, Pi.zero_apply, _eq_zero, _hom, add_hom, add_zero, c_mk, compLeft_hom, comp_zero, dite_eq_ite, down_Rel
-/
theorem homotopyPToId_eventually_constant {q n : Nat} (hqn : n < q) :
    ((homotopyPToId X (q + 1)).hom n (n + 1) : X _⦋n⦌ ⟶ X _⦋n + 1⦌) =
      (homotopyPToId X q).hom n (n + 1) := by
  simp only [homotopyHσToZero, AlternatingFaceMapComplex.obj_X, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, add_zero,
    Homotopy.nullHomotopy'_hom, ComplexShape.down_Rel, hσ'_eq_zero hqn (c_mk (n + 1) n rfl),
    dite_eq_ite, ite_self, comp_zero, zero_add, homotopyPToId]

/-- Construction of the homotopy from `PInfty` to the identity using eventually
(termwise) constant homotopies from `P q` to the identity for all `q` -/
@[simps]
/--
Definition of `homotopyPInftyToId` / `homotopyPInftyToId` 的定义

English:
definition homotopyPInftyToId
  signature: : Homotopy (PInfty : K[X] ⟶ _) (𝟙 _) where
  body: (homotopyPToId X (j + 1)).hom i j
  zero i j hij := Homotopy.zero _ i j hij
  comm n := by
    rcases n with _ | n
    · simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        PInfty_f, P_f_0_eq, zero_add] using (homotopyPToId X 2).comm 0
    · simpa only [Homotopy.dNext_

中文:
定义 homotopyPInftyToId
  签名: : Homotopy (PInfty : K[X] ⟶ _) (𝟙 _) where
  定义体: (homotopyPToId X (j + 1)).hom i j
  zero i j hij := Homotopy.zero _ i j hij
  comm n := by
    rcases n with _ | n
    · simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        PInfty_f, P_f_0_eq, zero_add] using (homotopyPToId X 2).comm 0
    · simpa only [Homotopy.dNext_

Depends on / 依赖: homotopyPToId
-/
def homotopyPInftyToId : Homotopy (PInfty : K[X] ⟶ _) (𝟙 _) where
  hom i j := (homotopyPToId X (j + 1)).hom i j
  zero i j hij := Homotopy.zero _ i j hij
  comm n := by
    rcases n with _ | n
    · simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        PInfty_f, P_f_0_eq, zero_add] using (homotopyPToId X 2).comm 0
    · simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
          HomologicalComplex.id_f, PInfty_f, ← P_is_eventually_constant (le_refl <| n + 1),
          homotopyPToId_eventually_constant X (Nat.lt_add_one (Nat.succ n)),
          Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
        using (homotopyPToId X (n + 2)).comm (n + 1)


/-- The inclusion of the Moore complex in the alternating face map complex
is a homotopy equivalence -/
@[simps]
/--
Definition of `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` / `homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` 的定义

English:
definition homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  signature: {A : Type*} [Category* A]
  body: inclusionOfMooreComplexMap Y
  inv := PInftyToNormalizedMooreComplex Y
  homotopyHomInvId := Homotopy.ofEq (splitMonoInclusionOfMooreComplexMap Y).id
  homotopyInvHomId := Homotopy.trans
      (Homotopy.ofEq (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y))
      (homotopyPInftyToI

中文:
定义 homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  签名: {A : 类型} [Category* A]
  定义体: inclusionOfMooreComplexMap Y
  inv := PInftyToNormalizedMooreComplex Y
  homotopyHomInvId := Homotopy.ofEq (splitMonoInclusionOfMooreComplexMap Y).id
  homotopyInvHomId := Homotopy.trans
      (Homotopy.ofEq (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y))
      (homotopyPInftyToI

Depends on / 依赖: inclusionOfMooreComplexMap
-/
def homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex {A : Type*} [Category* A]
    [Abelian A] {Y : SimplicialObject A} :
    HomotopyEquiv ((normalizedMooreComplex A).obj Y) ((alternatingFaceMapComplex A).obj Y) where
  hom := inclusionOfMooreComplexMap Y
  inv := PInftyToNormalizedMooreComplex Y
  homotopyHomInvId := Homotopy.ofEq (splitMonoInclusionOfMooreComplexMap Y).id
  homotopyInvHomId := Homotopy.trans
      (Homotopy.ofEq (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y))
      (homotopyPInftyToId Y)

end DoldKan

end AlgebraicTopology
