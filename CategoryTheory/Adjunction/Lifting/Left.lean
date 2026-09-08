/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Coequalizer

/-!
# Adjoint lifting

This file gives two constructions for building left adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.

The adjoint triangle theorem concerns a functor `U : B ⥤ C` with a left adjoint `F` such
that `ε_X : FUX ⟶ X` is a regular epi. Then for any category `A` with coequalizers of reflexive
pairs, a functor `R : A ⥤ B` has a left adjoint if (and only if) the composite `R ⋙ U` does.
Note that the condition on `U` regarding `ε_X` is automatically satisfied in the case when `U` is
a monadic functor, giving the corollary: `isRightAdjoint_triangle_lift_monadic`, i.e. if `U` is
monadic, `A` has reflexive coequalizers then `R : A ⥤ B` has a left adjoint provided `R ⋙ U` does.

The adjoint lifting theorem says that given a commutative square of functors (up to isomorphism):

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      R
```

where `V` is monadic, `U` has a left adjoint, and `A` has reflexive coequalizers, then if `R` has a
left adjoint then `Q` has a left adjoint.

## Implementation

It is more convenient to prove this theorem by assuming we are given the explicit adjunction rather
than just a functor known to be a right adjoint. In docstrings, we write `(η, ε)` for the unit
and counit of the adjunction `adj₁ : F ⊣ U` and `(ι, δ)` for the unit and counit of the adjunction
`adj₂ : F' ⊣ R ⋙ U`.

This file has been adapted to `Mathlib/CategoryTheory/Adjunction/Lifting/Right.lean`.
Please try to keep them in sync.

## TODO

- Dualise to lift right adjoints through monads (by reversing 2-cells).
- Investigate whether it is possible to give a more explicit description of the lifted adjoint,
  especially in the case when the isomorphism `comm` is `Iso.refl _`

## References
* https://ncatlab.org/nlab/show/adjoint+triangle+theorem
* https://ncatlab.org/nlab/show/adjoint+lifting+theorem
* Adjoint Lifting Theorems for Categories of Algebras (PT Johnstone, 1975)
* A unified approach to the lifting of adjoints (AJ Power, 1988)
-/

@[expose] public section


namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

-- Hide implementation details in this namespace
namespace LiftLeftAdjoint

variable {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A)
variable (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U)

set_option backward.isDefEq.respectTransparency false in
/-- To show that `ε_X` is a coequalizer for `(FUε_X, ε_FUX)`, it suffices to assume it's always a
coequalizer of something (i.e. a regular epi).
-/
/-
**CategoryTheory.LiftLeftAdjoint.counitCoequalises** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.LiftLeftAdjoint`。
形式化陈述：counitCoequalises (h : forall X : B, RegularEpi (adj₁.counit.app X)) (X : 
B) : IsColimit (Cofork.ofπ (adj₁.counit.app X) (adj₁.counit_naturality _))
参数：h : forall X : B, RegularEpi (adj₁.counit.app X)；X : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show that `ε_X` is a coequalizer for `(FUε_X, ε_FUX)`, it suffices to assume 
it's always a
coequalizer of something (i.e. a regular epi).
-/
def counitCoequalises (h : ∀ X : B, RegularEpi (adj₁.counit.app X)) (X : B) :
    IsColimit (Cofork.ofπ (adj₁.counit.app X) (adj₁.counit_naturality _)) :=
  Cofork.IsColimit.mk' _ fun s => by
    have := fun Y ↦ h Y |>.epi
    refine ⟨((h X).desc' s.π ?_).1, ?_, ?_⟩
    · rw [← cancel_epi (adj₁.counit.app (h X).W)]
      rw [← adj₁.counit_naturality_assoc (h X).left]
      dsimp
      rw [← dsimp% s.condition, ← F.map_comp_assoc, ← U.map_comp, RegularEpi.w, U.map_comp,
        F.map_comp_assoc, s.condition, ← adj₁.counit_naturality_assoc (h X).right]
    · apply ((h X).desc' s.π _).2
    · intro m hm
      rw [← cancel_epi (adj₁.counit.app X)]
      apply hm.trans ((h _).desc' s.π _).2.symm

/-- (Implementation)
To construct the left adjoint, we use the coequalizer of `F' U ε_Y` with the composite

`F' U F U X ⟶ F' U F U R F' U X ⟶ F' U R F' U X ⟶ F' U X`

where the first morphism is `F' U F ι_UX`, the second is `F' U ε_RF'UX`, and the third is `δ_F'UX`.
We will show that this coequalizer exists and that it forms the object map for a left adjoint to
`R`.
-/
/-
**CategoryTheory.LiftLeftAdjoint.otherMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.LiftLeftAdjoint`。
形式化陈述：otherMap (X) : F'.obj (U.obj (F.obj (U.obj X))) ⟶ F'.obj (U.obj X)
参数：X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation)
To construct the left adjoint, we use the coequalizer of `F' U ε_Y` with the com
posite

`F' U F U X ⟶ F' U F U R F' U X ⟶ F' U R F' U X ⟶ F' U X`

where the first morphism is `F' U F ι_UX`, the second is `F' U ε_RF'UX`, and the
 third is `δ_F'UX`.
We will show that this coequalizer exists and that it forms the object map for a
 left adjoint to
`R`.
-/
def otherMap (X) : F'.obj (U.obj (F.obj (U.obj X))) ⟶ F'.obj (U.obj X) :=
  F'.map (U.map (F.map (adj₂.unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _

set_option backward.defeqAttrib.useBackward true in
/-- `(F'Uε_X, otherMap X)` is a reflexive pair: in particular if `A` has reflexive coequalizers then
this pair has a coequalizer.
-/
/-
**CategoryTheory.LiftLeftAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lift
LeftAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(F'Uε_X, otherMap X)` is a reflexive pair: in particular if `A` has reflexive c
oequalizers then
this pair has a coequalizer.
-/
instance (X : B) :
    IsReflexivePair (F'.map (U.map (adj₁.counit.app X))) (otherMap _ _ adj₁ adj₂ X) :=
  IsReflexivePair.mk' (F'.map (adj₁.unit.app (U.obj X)))
    (by
      rw [← F'.map_comp, adj₁.right_triangle_components]
      apply F'.map_id)
    (by
      dsimp [otherMap]
      rw [← F'.map_comp_assoc, U.map_comp, adj₁.unit_naturality_assoc,
        adj₁.right_triangle_components, comp_id, adj₂.left_triangle_components])

variable [HasReflexiveCoequalizers A]

/-- Construct the object part of the desired left adjoint as the coequalizer of `F'Uε_Y` with
`otherMap`.
-/
/-
**CategoryTheory.LiftLeftAdjoint.constructLeftAdjointObj** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.LiftLeftAdjoint`。
形式化陈述：constructLeftAdjointObj (Y : B) : A
参数：Y : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the object part of the desired left adjoint as the coequalizer of `F'U
ε_Y` with
`otherMap`.
-/
noncomputable def constructLeftAdjointObj (Y : B) : A :=
  coequalizer (F'.map (U.map (adj₁.counit.app Y))) (otherMap _ _ adj₁ adj₂ Y)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The homset equivalence which helps show that `R` is a right adjoint. -/
@[simps!]
/-
**CategoryTheory.LiftLeftAdjoint.constructLeftAdjointEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.LiftLeftAdjoint`。
形式化陈述：constructLeftAdjointEquiv (h : forall X : B, RegularEpi (adj₁.counit.app X
)) (Y : A) (X : B) : (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃ (X ⟶ R.obj 
Y)
参数：h : forall X : B, RegularEpi (adj₁.counit.app X)；Y : A；X : B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The homset equivalence which helps show that `R` is a right adjoint.
-/
noncomputable def constructLeftAdjointEquiv (h : ∀ X : B, RegularEpi (adj₁.counit.app X)) (Y : A)
    (X : B) : (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
  calc
    (constructLeftAdjointObj _ _ adj₁ adj₂ X ⟶ Y) ≃
        { f : F'.obj (U.obj X) ⟶ Y //
          F'.map (U.map (adj₁.counit.app X)) ≫ f = otherMap _ _ adj₁ adj₂ _ ≫ f } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) _
    _ ≃ { g : U.obj X ⟶ U.obj (R.obj Y) //
          U.map (F.map g ≫ adj₁.counit.app _) = U.map (adj₁.counit.app _) ≫ g } := by
      apply (adj₂.homEquiv _ _).subtypeEquiv _
      intro f
      rw [← (adj₂.homEquiv _ _).injective.eq_iff, eq_comm, adj₂.homEquiv_naturality_left,
        otherMap, assoc, adj₂.homEquiv_naturality_left, ← adj₂.counit_naturality,
        adj₂.homEquiv_naturality_left, adj₂.homEquiv_unit, adj₂.right_triangle_components,
        comp_id, Functor.comp_map, ← U.map_comp, assoc]
      dsimp
      rw [← adj₁.counit_naturality]
      simp [dsimp% adj₂.homEquiv_unit _ _ f ]
    _ ≃ { z : F.obj (U.obj X) ⟶ R.obj Y // _ } := by
      apply (adj₁.homEquiv _ _).symm.subtypeEquiv
      intro g
      rw [← (adj₁.homEquiv _ _).symm.injective.eq_iff, adj₁.homEquiv_counit,
        adj₁.homEquiv_counit, adj₁.homEquiv_counit, F.map_comp, assoc, U.map_comp, F.map_comp,
        assoc, adj₁.counit_naturality, adj₁.counit_naturality_assoc]
      apply eq_comm
    _ ≃ (X ⟶ R.obj Y) := (Cofork.IsColimit.homIso (counitCoequalises adj₁ h X) _).symm

attribute [local simp] Adjunction.homEquiv_counit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Construct the left adjoint to `R`, with object map `constructLeftAdjointObj`. -/
/-
**CategoryTheory.LiftLeftAdjoint.constructLeftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.LiftLeftAdjoint`。
形式化陈述：constructLeftAdjoint (h : forall X : B, RegularEpi (adj₁.counit.app X)) : 
B ⥤ A
参数：h : forall X : B, RegularEpi (adj₁.counit.app X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the left adjoint to `R`, with object map `constructLeftAdjointObj`.
-/
noncomputable def constructLeftAdjoint (h : ∀ X : B, RegularEpi (adj₁.counit.app X)) : B ⥤ A := by
  refine Adjunction.leftAdjointOfEquiv (fun X Y => constructLeftAdjointEquiv R _ adj₁ adj₂ h Y X) ?_
  intro X Y Y' g h
  rw [constructLeftAdjointEquiv_apply, constructLeftAdjointEquiv_apply,
    Equiv.symm_apply_eq, Subtype.ext_iff]
  dsimp
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [Cofork.IsColimit.homIso_natural, Cofork.IsColimit.homIso_natural]
  erw [adj₂.homEquiv_naturality_right]
  simp_rw [Functor.comp_map]
  -- This used to be `simp`, but we need `cat_disch` after https://github.com/leanprover/lean4/pull/2644
  cat_disch

end LiftLeftAdjoint

/-- The adjoint triangle theorem: Suppose `U : B ⥤ C` has a left adjoint `F` such that each counit
`ε_X : FUX ⟶ X` is a regular epimorphism. Then if a category `A` has coequalizers of reflexive
pairs, then a functor `R : A ⥤ B` has a left adjoint if the composite `R ⋙ U` does.

Note the converse is true (with weaker assumptions), by `Adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
/-
**CategoryTheory.isRightAdjoint_triangle_lift** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：isRightAdjoint_triangle_lift {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F
 ⊣ U) (h : forall X : B, RegularEpi (adj₁.counit.app X)) [HasReflexiveCoequalize
rs A] [(R ⋙ U).IsRightAdjoint] : R.IsRightAdjoint where exists_leftAdjoint
参数：R : A ⥤ B；adj₁ : F ⊣ U；h : forall X : B, RegularEpi (adj₁.counit.app X)；R ⋙ U
。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjoint triangle theorem: Suppose `U : B ⥤ C` has a left adjoint `F` such th
at each counit
`ε_X : FUX ⟶ X` is a regular epimorphism. Then if a category `A` has coequalizer
s of reflexive
pairs, then a functor `R : A ⥤ B` has a left adjoint if the composite `R ⋙ U` do
es.

Note the converse is true (with weaker assumptions), by `Adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
lemma isRightAdjoint_triangle_lift {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
    (h : ∀ X : B, RegularEpi (adj₁.counit.app X)) [HasReflexiveCoequalizers A]
    [(R ⋙ U).IsRightAdjoint] : R.IsRightAdjoint where
  exists_leftAdjoint :=
    ⟨LiftLeftAdjoint.constructLeftAdjoint R _ adj₁ (Adjunction.ofIsRightAdjoint _) h,
      ⟨Adjunction.adjunctionOfEquivLeft _ _⟩⟩

/-- If `R ⋙ U` has a left adjoint, the domain of `R` has reflexive coequalizers and `U` is a monadic
functor, then `R` has a left adjoint.
This is a special case of `isRightAdjoint_triangle_lift` which is often more useful in practice.
-/
/-
**CategoryTheory.isRightAdjoint_triangle_lift_monadic** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory`。
形式化陈述：isRightAdjoint_triangle_lift_monadic (U : B ⥤ C) [MonadicRightAdjoint U] {
R : A ⥤ B} [HasReflexiveCoequalizers A] [(R ⋙ U).IsRightAdjoint] : R.IsRightAdjo
int
参数：U : B ⥤ C；R ⋙ U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsEquivalenceAlgebraToMonadMonadicAdjunctionCompariso
n`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   (R : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.isRightAdjoint`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Monad.Algebra.Hom.mk.congr_simp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} {A B : T.Algebr
a}   (f f_1 : A.A ⟶ B.A) (e_f : f = …
· 使用定理 `CategoryTheory.Monad.adj_counit`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] (T : CategoryTheory.Monad C),   T.adj.counit = { app := fun
 Y => { f := Y.a, h :…
· 使用定理 `CategoryTheory.Monad.FreeCoequalizer.condition`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} (X : T.Algebra)
,   CategoryTheory.CategoryStruct.co…
· 使用引理 `CategoryTheory.isRightAdjoint_triangle_lift`：isRightAdjoint_triangle_lif
t {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U) (h : forall X : B, RegularE
pi (adj₁.counit.app X)) [HasRefle…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
If `R ⋙ U` has a left adjoint, the domain of `R` has reflexive coequalizers and 
`U` is a monadic
functor, then `R` has a left adjoint.
This is a special case of `isRightAdjoint_triangle_lift` which is often more use
ful in practice.
-/
lemma isRightAdjoint_triangle_lift_monadic (U : B ⥤ C) [MonadicRightAdjoint U] {R : A ⥤ B}
    [HasReflexiveCoequalizers A] [(R ⋙ U).IsRightAdjoint] : R.IsRightAdjoint := by
  let R' : A ⥤ _ := R ⋙ Monad.comparison (monadicAdjunction U)
  rsuffices : R'.IsRightAdjoint
  · let : (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv).IsRightAdjoint := by
      infer_instance
    refine ((Adjunction.ofIsRightAdjoint
      (R' ⋙ (Monad.comparison (monadicAdjunction U)).inv)).ofNatIsoRight ?_).isRightAdjoint
    exact Functor.isoWhiskerLeft R (Monad.comparison _).asEquivalence.unitIso.symm ≪≫ R.rightUnitor
  let : (R' ⋙ Monad.forget (monadicAdjunction U).toMonad).IsRightAdjoint := by
    refine ((Adjunction.ofIsRightAdjoint (R ⋙ U)).ofNatIsoRight ?_).isRightAdjoint
    exact Functor.isoWhiskerLeft R (Monad.comparisonForget (monadicAdjunction U)).symm
  let : ∀ X, RegularEpi ((Monad.adj (monadicAdjunction U).toMonad).counit.app X) := by
    intro X
    simp only [Monad.adj_counit]
    exact ⟨_, _, _, _, Monad.beckAlgebraCoequalizer X⟩
  exact isRightAdjoint_triangle_lift R' (Monad.adj _) this

variable {D : Type u₄}
variable [Category.{v₄} D]

/-- Suppose we have a commutative square of functors

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      R
```

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` has a left adjoint such that
each component of the counit is a regular epi.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
/-
**CategoryTheory.isRightAdjoint_square_lift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：isRightAdjoint_square_lift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
 (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [V.IsRightAdjoint] [R.IsRightAdjoint]
 (h : forall X, RegularEpi ((Adjunction.ofIsRightAdjoint V).counit.app X)) [HasR
eflexiveCoequalizers A] : Q.IsRightAdjoint
参数：Q : A ⥤ B；V : B ⥤ D；U : A ⥤ C；R : C ⥤ D；comm : U ⋙ R ≅ Q ⋙ V；h : forall X, Re
gularEpi ((Adjunction.ofIsRightAdjoint V).counit.app X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.isRightAdjoint`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.isRightAdjoint_triangle_lift`：isRightAdjoint_triangle_lif
t {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U) (h : forall X : B, RegularE
pi (adj₁.counit.app X)) [HasRefle…

--- 原说明 ---
Suppose we have a commutative square of functors

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      R
```

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` has a left 
adjoint such that
each component of the counit is a regular epi.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
lemma isRightAdjoint_square_lift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [V.IsRightAdjoint] [R.IsRightAdjoint]
    (h : ∀ X, RegularEpi ((Adjunction.ofIsRightAdjoint V).counit.app X))
    [HasReflexiveCoequalizers A] :
    Q.IsRightAdjoint :=
  have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift Q (Adjunction.ofIsRightAdjoint V) h

/-- Suppose we have a commutative square of functors

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      R
```

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` is monadic.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
/-
**CategoryTheory.isRightAdjoint_square_lift_monadic** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory`。
形式化陈述：isRightAdjoint_square_lift_monadic (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R 
: C ⥤ D) (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [MonadicRightAdjoint V] [R.Is
RightAdjoint] [HasReflexiveCoequalizers A] : Q.IsRightAdjoint
参数：Q : A ⥤ B；V : B ⥤ D；U : A ⥤ C；R : C ⥤ D；comm : U ⋙ R ≅ Q ⋙ V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.isRightAdjoint`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.isRightAdjoint_triangle_lift_monadic`：isRightAdjoint_tria
ngle_lift_monadic (U : B ⥤ C) [MonadicRightAdjoint U] {R : A ⥤ B} [HasReflexiveC
oequalizers A] [(R ⋙ U).IsRightAdjoint] :…

--- 原说明 ---
Suppose we have a commutative square of functors

```
      Q
    A → B
  U ↓   ↓ V
    C → D
      R
```

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` is monadic.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
lemma isRightAdjoint_square_lift_monadic (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [U.IsRightAdjoint] [MonadicRightAdjoint V] [R.IsRightAdjoint]
    [HasReflexiveCoequalizers A] : Q.IsRightAdjoint :=
  have := ((Adjunction.ofIsRightAdjoint (U ⋙ R)).ofNatIsoRight comm).isRightAdjoint
  isRightAdjoint_triangle_lift_monadic V

end CategoryTheory

