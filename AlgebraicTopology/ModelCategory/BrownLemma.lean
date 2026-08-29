/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# The factorization lemma by K. S. Brown

In a model category, any morphism `f : X ⟶ Y` between
cofibrant objects can be factored as `i ≫ p`
with `i` a cofibration and `p` a trivial fibration
which has a section `s` that is a cofibration.
In order to state this, we introduce a structure
`CofibrantBrownFactorization f` with the data
of such morphisms `i`, `p` and `s` with the expected
properties, and show it is nonempty.
Moreover, if `f` is a weak equivalence, then all the
morphisms `i`, `p` and `s` are weak equivalences.
(We also obtain the dual results about morphisms
between fibrant objects.)

## References
* [Brown, Kenneth S., *Abstract homotopy theory and generalized sheaf cohomology*, §I.1][brown-1973]

-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]
  {X Y : C} (f : X ⟶ Y)

/--
Definition of `CofibrantBrownFactorization` / `CofibrantBrownFactorization` 的定义

English:
structure CofibrantBrownFactorization
  parameters: extends
  axioms and operations (3):
    - s : Y ⟶ Z
    - s_p : s ≫ p = 𝟙 Y  [default: by cat_disch]
    - cofibration_s : Cofibration s  [default: by infer_instance]

中文:
结构 CofibrantBrownFactorization
  参数: extends
  公理与运算 (3 个):
    - s : Y ⟶ Z
    - s_p : s ≫ p = 𝟙 Y  [默认: by cat_disch]
    - cofibration_s : Cofibration s  [默认: by infer_instance]

Depends on / 依赖: Cofibration, cat_disch, cofibration_s, infer_instance
-/
structure CofibrantBrownFactorization extends
    MapFactorizationData (cofibrations C) (trivialFibrations C) f where
  /-- a cofibration that is a section of `p` -/
  s : Y ⟶ Z
  s_p : s ≫ p = 𝟙 Y := by cat_disch
  cofibration_s : Cofibration s := by infer_instance

namespace CofibrantBrownFactorization

attribute [reassoc (attr := simp)] s_p
attribute [instance] cofibration_s

variable (h : CofibrantBrownFactorization f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WeakEquivalence
  signature: f] : WeakEquivalence h.i
  body: weakEquivalence_of_postcomp_of_fac h.fac

中文:
实例 [WeakEquivalence
  签名: f] : WeakEquivalence h.i
  定义体: weakEquivalence_of_postcomp_of_fac h.fac

Depends on / 依赖: h.fac, weakEquivalence_of_postcomp_of_fac
-/
instance [WeakEquivalence f] : WeakEquivalence h.i :=
  weakEquivalence_of_postcomp_of_fac h.fac

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WeakEquivalence h.s
  body: weakEquivalence_of_postcomp_of_fac h.s_p

中文:
实例 :
  签名: WeakEquivalence h.s
  定义体: weakEquivalence_of_postcomp_of_fac h.s_p

Depends on / 依赖: h.s_p, weakEquivalence_of_postcomp_of_fac
-/
instance : WeakEquivalence h.s :=
  weakEquivalence_of_postcomp_of_fac h.s_p

set_option backward.isDefEq.respectTransparency false in
/-- The term in `CofibrantBrownFactorization f` that is deduced from
a factorization of `coprod.desc f (𝟙 Y) : X ⨿ Y ⟶ Y`
as a cofibration followed by a trivial fibration. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: [IsCofibrant X] [IsCofibrant Y]
  body: h.Z
  i := coprod.inl ≫ h.i
  p := h.p
  s := coprod.inr ≫ h.i
  hi := by rw [← cofibration_iff]; infer_instance
  hp := by rw [mem_trivialFibrations_iff]; constructor <;> infer_instance

中文:
定义 mk'
  签名: [IsCofibrant X] [IsCofibrant Y]
  定义体: h.Z
  i := coprod.inl ≫ h.i
  p := h.p
  s := coprod.inr ≫ h.i
  hi := by rw [← cofibration_iff]; infer_instance
  hp := by rw [mem_trivialFibrations_iff]; constructor <;> infer_instance
-/
noncomputable def mk' [IsCofibrant X] [IsCofibrant Y]
    (h : MapFactorizationData (cofibrations C) (trivialFibrations C) (coprod.desc f (𝟙 Y))) :
    CofibrantBrownFactorization f where
  Z := h.Z
  i := coprod.inl ≫ h.i
  p := h.p
  s := coprod.inr ≫ h.i
  hi := by rw [← cofibration_iff]; infer_instance
  hp := by rw [mem_trivialFibrations_iff]; constructor <;> infer_instance

variable (h : MapFactorizationData (cofibrations C) (trivialFibrations C) (coprod.desc f (𝟙 Y)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofibrant
  signature: X] [IsCofibrant Y] :
  body: ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

中文:
实例 [IsCofibrant
  签名: X] [IsCofibrant Y] :
  定义体: ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.factorizationData, factorizationData
-/
instance [IsCofibrant X] [IsCofibrant Y] :
    Nonempty (CofibrantBrownFactorization f) :=
  ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

end CofibrantBrownFactorization

/--
Definition of `FibrantBrownFactorization` / `FibrantBrownFactorization` 的定义

English:
structure FibrantBrownFactorization
  parameters: extends
  axioms and operations (3):
    - r : Z ⟶ X
    - i_r : i ≫ r = 𝟙 X  [default: by cat_disch]
    - fibration_r : Fibration r  [default: by infer_instance]

中文:
结构 FibrantBrownFactorization
  参数: extends
  公理与运算 (3 个):
    - r : Z ⟶ X
    - i_r : i ≫ r = 𝟙 X  [默认: by cat_disch]
    - fibration_r : Fibration r  [默认: by infer_instance]

Depends on / 依赖: Fibration, cat_disch, fibration_r, infer_instance
-/
structure FibrantBrownFactorization extends
    MapFactorizationData (trivialCofibrations C) (fibrations C) f where
  /-- a fibration that is a retraction of `i` -/
  r : Z ⟶ X
  i_r : i ≫ r = 𝟙 X := by cat_disch
  fibration_r : Fibration r := by infer_instance

namespace FibrantBrownFactorization

attribute [reassoc (attr := simp)] i_r
attribute [instance] fibration_r

variable (h : FibrantBrownFactorization f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WeakEquivalence
  signature: f] : WeakEquivalence h.p
  body: weakEquivalence_of_precomp_of_fac h.fac

中文:
实例 [WeakEquivalence
  签名: f] : WeakEquivalence h.p
  定义体: weakEquivalence_of_precomp_of_fac h.fac

Depends on / 依赖: h.fac, weakEquivalence_of_precomp_of_fac
-/
instance [WeakEquivalence f] : WeakEquivalence h.p :=
  weakEquivalence_of_precomp_of_fac h.fac

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WeakEquivalence h.r
  body: weakEquivalence_of_precomp_of_fac h.i_r

中文:
实例 :
  签名: WeakEquivalence h.r
  定义体: weakEquivalence_of_precomp_of_fac h.i_r

Depends on / 依赖: h.i_r, weakEquivalence_of_precomp_of_fac
-/
instance : WeakEquivalence h.r :=
  weakEquivalence_of_precomp_of_fac h.i_r

set_option backward.isDefEq.respectTransparency false in
/-- The term in `CofibrantBrownFactorization f` that is deduced from
a factorization of `prod.lift f (𝟙 X) : X ⟶ Y ⨯ X`
as a cofibration followed by a trivial fibration. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: [IsFibrant X] [IsFibrant Y]
  body: h.Z
  i := h.i
  p := h.p ≫ prod.fst
  r := h.p ≫ prod.snd
  hi := by rw [mem_trivialCofibrations_iff]; constructor <;> infer_instance
  hp := by rw [← fibration_iff]; infer_instance

中文:
定义 mk'
  签名: [IsFibrant X] [IsFibrant Y]
  定义体: h.Z
  i := h.i
  p := h.p ≫ prod.fst
  r := h.p ≫ prod.snd
  hi := by rw [mem_trivialCofibrations_iff]; constructor <;> infer_instance
  hp := by rw [← fibration_iff]; infer_instance
-/
noncomputable def mk' [IsFibrant X] [IsFibrant Y]
    (h : MapFactorizationData (trivialCofibrations C) (fibrations C) (prod.lift f (𝟙 X))) :
    FibrantBrownFactorization f where
  Z := h.Z
  i := h.i
  p := h.p ≫ prod.fst
  r := h.p ≫ prod.snd
  hi := by rw [mem_trivialCofibrations_iff]; constructor <;> infer_instance
  hp := by rw [← fibration_iff]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFibrant
  signature: X] [IsFibrant Y] :
  body: ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

中文:
实例 [IsFibrant
  签名: X] [IsFibrant Y] :
  定义体: ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.factorizationData, factorizationData
-/
instance [IsFibrant X] [IsFibrant Y] :
    Nonempty (FibrantBrownFactorization f) :=
  ⟨.mk' f (MorphismProperty.factorizationData _ _ _)⟩

end FibrantBrownFactorization

end HomotopicalAlgebra
