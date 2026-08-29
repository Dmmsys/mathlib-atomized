/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.Data.Matrix.DMatrix
public import Mathlib.Data.Matrix.Mul

/-!
# Matrices over a category.

When `C` is a preadditive category, `Mat_ C` is the preadditive category
whose objects are finite tuples of objects in `C`, and
whose morphisms are matrices of morphisms from `C`.

There is a functor `Mat_.embedding : C ⥤ Mat_ C` sending morphisms to one-by-one matrices.

`Mat_ C` has finite biproducts.

## The additive envelope

We show that this construction is the "additive envelope" of `C`,
in the sense that any additive functor `F : C ⥤ D` to a category `D` with biproducts
lifts to a functor `Mat_.lift F : Mat_ C ⥤ D`,
Moreover, this functor is unique (up to natural isomorphisms) amongst functors `L : Mat_ C ⥤ D`
such that `embedding C ⋙ L ≅ F`.
(As we don't have 2-category theory, we can't explicitly state that `Mat_ C` is
the initial object in the 2-category of categories under `C` which have biproducts.)

As a consequence, when `C` already has finite biproducts we have `Mat_ C ≌ C`.

## Future work

We should provide a more convenient `Mat R`, when `R` is a ring,
as a category with objects `n : FinType`,
and whose morphisms are matrices with components in `R`.

Ideally this would conveniently interact with both `Mat_` and `Matrix`.

-/

@[expose] public section


open CategoryTheory CategoryTheory.Preadditive

noncomputable section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]

/--
Definition of `Mat_` / `Mat_` 的定义

English:
structure Mat_
  parameters: where
  axioms and operations (3):
    - ι : Type
    - [fintype : Fintype ι]
    - X : ι -> C

中文:
结构 Mat_
  参数: where
  公理与运算 (3 个):
    - ι : 类型
    - [fintype : 有限类型 ι]
    - X : ι -> C
-/
structure Mat_ where
  /-- The index type `ι` -/
  ι : Type
  [fintype : Fintype ι]
  /-- The map from `ι` to objects in `C` -/
  X : ι -> C

attribute [instance] Mat_.fintype

namespace Mat_

variable {C}

/--
Definition of `Hom` / `Hom` 的定义

English:
definition Hom
  signature: (M N : Mat_ C)
  body: DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

中文:
定义 态射
  签名: (M N : Mat_ C)
  定义体: DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

Depends on / 依赖: DMatrix
-/
def Hom (M N : Mat_ C) : Type v₁ :=
  DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

namespace Hom

open scoped Classical in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (M : Mat_ C)
  body: fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0

中文:
定义 id
  签名: (M : Mat_ C)
  定义体: fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0

Depends on / 依赖: Fintype, Fintype.ofEquiv, congr_arg, eqToHom, equivTreesOfNumNodesEq, ofEquiv
-/
def id (M : Mat_ C) : Hom M M := fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {M N K : Mat_ C} (f : Hom M N) (g : Hom N K)
  body: fun i k =>
  ∑ j : N.ι, f i j ≫ g j k

中文:
定义 comp
  签名: {M N K : Mat_ C} (f : 态射 M N) (g : 态射 N K)
  定义体: fun i k =>
  ∑ j : N.ι, f i j ≫ g j k
-/
def comp {M N K : Mat_ C} (f : Hom M N) (g : Hom N K) : Hom M K := fun i k =>
  ∑ j : N.ι, f i j ≫ g j k

end Hom

section

attribute [local simp] Hom.id Hom.comp

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{v₁} (Mat_ C)
  body: Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp f := by
    classical
    simp +unfoldPartialApp [dite_comp]
  comp_id f := by
    classical
    simp +unfoldPartialApp [comp_dite]
  assoc f g h := by
    apply DMatrix.ext
    intros
    simp_rw [Hom.comp, sum_comp, comp_sum, Category.assoc]
    rw [Finset.sum_comm]

@[ext]

中文:
实例 :
  签名: 范畴.{v₁} (Mat_ C)
  定义体: Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp f := by
    classical
    simp +unfoldPartialApp [dite_comp]
  comp_id f := by
    classical
    simp +unfoldPartialApp [comp_dite]
  assoc f g h := by
    apply DMatrix.ext
    intros
    simp_rw [Hom.comp, sum_comp, comp_sum, Category.assoc]
    rw [Finset.sum_comm]

@[ext]
-/
instance : Category.{v₁} (Mat_ C) where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp f := by
    classical
    simp +unfoldPartialApp [dite_comp]
  comp_id f := by
    classical
    simp +unfoldPartialApp [comp_dite]
  assoc f g h := by
    apply DMatrix.ext
    intros
    simp_rw [Hom.comp, sum_comp, comp_sum, Category.assoc]
    rw [Finset.sum_comm]

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {M N : Mat_ C} (f g : M ⟶ N) (H : forall i j, f i j = g i j)
  statement: f = g
  proof: DMatrix.ext_iff.mp H

中文:
定理 hom_ext
  条件: {M N : Mat_ C} (f g : M ⟶ N) (H : 对任意 i j, f i j = g i j)
  结论: f = g
  证明: DMatrix.ext_iff.mp H

Depends on / 依赖: DMatrix, DMatrix.ext_iff.mp, ext_iff
-/
theorem hom_ext {M N : Mat_ C} (f g : M ⟶ N) (H : forall i j, f i j = g i j) : f = g :=
  DMatrix.ext_iff.mp H

open scoped Classical in
/--
theorem `id_def` / 定理 `id_def`

English:
theorem id_def
  given: (M : Mat_ C)
  proof: rfl

中文:
定理 id_def
  条件: (M : Mat_ C)
  证明: rfl
-/
theorem id_def (M : Mat_ C) :
    (𝟙 M : Hom M M) = fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0 :=
  rfl

open scoped Classical in
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (M : Mat_ C) (i j : M.ι)
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (M : Mat_ C) (i j : M.ι)
  证明: rfl

@[simp]
-/
theorem id_apply (M : Mat_ C) (i j : M.ι) :
    (𝟙 M : Hom M M) i j = if h : i = j then eqToHom (congr_arg M.X h) else 0 :=
  rfl

@[simp]
/--
theorem `id_apply_self` / 定理 `id_apply_self`

English:
theorem id_apply_self
  given: (M : Mat_ C) (i : M.ι)
  statement: (𝟙 M : Hom M M) i i = 𝟙 _
  proof: by simp [id_apply]

@[simp]

中文:
定理 id_apply_self
  条件: (M : Mat_ C) (i : M.ι)
  结论: (𝟙 M : 态射 M M) i i = 𝟙 _
  证明: by simp [id_apply]

@[simp]

Depends on / 依赖: id_apply
-/
theorem id_apply_self (M : Mat_ C) (i : M.ι) : (𝟙 M : Hom M M) i i = 𝟙 _ := by simp [id_apply]

@[simp]
/--
theorem `id_apply_of_ne` / 定理 `id_apply_of_ne`

English:
theorem id_apply_of_ne
  given: (M : Mat_ C) (i j : M.ι) (h : i != j)
  statement: (𝟙 M : Hom M M) i j = 0
  proof: by
  simp [id_apply, h]

中文:
定理 id_apply_of_ne
  条件: (M : Mat_ C) (i j : M.ι) (h : i != j)
  结论: (𝟙 M : 态射 M M) i j = 0
  证明: by
  simp [id_apply, h]

Depends on / 依赖: id_apply
-/
theorem id_apply_of_ne (M : Mat_ C) (i j : M.ι) (h : i != j) : (𝟙 M : Hom M M) i j = 0 := by
  simp [id_apply, h]

/--
theorem `comp_def` / 定理 `comp_def`

English:
theorem comp_def
  given: {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K)
  proof: rfl

@[simp]

中文:
定理 comp_def
  条件: {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K)
  证明: rfl

@[simp]
-/
theorem comp_def {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N.ι, f i j ≫ g j k :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k)
  proof: rfl

中文:
定理 comp_apply
  条件: {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k)
  证明: rfl
-/
theorem comp_apply {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k :=
  rfl

instance (M N : Mat_ C) : Inhabited (M ⟶ N) :=
  ⟨fun i j => (0 : M.X i ⟶ N.X j)⟩

end

instance (M N : Mat_ C) : AddCommGroup (M ⟶ N) :=
inferInstanceAs AddCommGroup (DMatrix M.ι N.ι _)

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: {M N : Mat_ C} (f g : M ⟶ N) (i j)
  statement: (f + g) i j = f i j + g i j
  proof: rfl

中文:
定理 add_apply
  条件: {M N : Mat_ C} (f g : M ⟶ N) (i j)
  结论: (f + g) i j = f i j + g i j
  证明: rfl
-/
theorem add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (Mat_ C)
  body: by ext; simp [Finset.sum_add_distrib]
  comp_add M N K f g g' := by ext; simp [Finset.sum_add_distrib]

中文:
实例 :
  签名: 预加性 (Mat_ C)
  定义体: by ext; simp [Finset.sum_add_distrib]
  comp_add M N K f g g' := by ext; simp [Finset.sum_add_distrib]

Depends on / 依赖: Finset, Finset.sum_add_distrib, comp_add, sum_add_distrib
-/
instance : Preadditive (Mat_ C) where
  add_comp M N K f f' g := by ext; simp [Finset.sum_add_distrib]
  comp_add M N K f g g' := by ext; simp [Finset.sum_add_distrib]

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Instance `hasFiniteBiproducts` / 实例 `hasFiniteBiproducts`

English:
instance hasFiniteBiproducts
  signature: : HasFiniteBiproducts (Mat_ C) where
  body: { has_biproduct := fun f =>
        hasBiproduct_of_total
          { pt := ⟨Σ j, (f j).ι, fun p => (f p.1).X p.2⟩
            π := fun j x y => by
              refine if h : x.1 = j then ?_ else 0
              refine if h' : @Eq.ndrec (Fin n) x.1 (fun j => (f j).ι) x.2 _ h = y then ?_ else 0
              apply eqToHom
              subst h h'
              rfl
            -- Notice we were careful not to use `subst` until we had a goal in `Prop`.
            ι := fun j x y => by
              refine if h : y.1 = j then ?_ else 0
              refine if h' : @Eq.ndrec _ y.1 (fun j => (f j).ι) y.2 _ h = x then ?_ else 0
              apply eqToHom
              subst h h'
              rfl
            ι_π := fun j j' => by
              ext x y
              dsimp
              simp_rw [dite_comp, comp_dite]
              simp only [ite_self, dite_eq_ite, Limits.comp_zero, Limits.zero_comp,
                eqToHom_trans]
              rw [← Finset.univ_sigma_univ]; rw [Finset.sum_sigma]
              dsimp +instances
              simp only [if_true, Finset.sum_dite_irrel, Finset.mem_univ,
                Finset.sum_const_zero, Finset.sum_dite_eq']
              split_ifs with h h'
              · subst h h'
                simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Mat_.id_apply_self]
              · subst h
                rw [eqToHom_refl]; rw [id_apply_of_ne _ _ _ h']
              · rfl }
          (by
            dsimp
            ext1 ⟨i, j⟩
            rintro ⟨i', j'⟩
            rw [Finset.sum_apply]; rw [Finset.sum_apply]
            dsimp
            rw [Finset.sum_eq_single i]; rotate_left
            · intro b _ hb
              apply Finset.sum_eq_zero
              intro x _
              rw [dif_neg hb.symm]; rw [zero_comp]
            · intro hi
              simp at hi
            rw [Finset.sum_eq_single j]; rotate_left
            · intro b _ hb
              rw [dif_pos rfl]; rw [dif_neg]; rw [zero_comp]
              simp only
              tauto
            · intro hj
              simp at hj
            simp only [eqToHom_refl, dite_eq_ite, ite_true, Category.id_comp,
              Sigma.mk.inj_iff, id_def]
            by_cases h : i' = i
            · subst h
              rw [dif_pos rfl]
              simp only [heq_eq_eq, true_and]
              by_cases h : j' = j
              · subst h
                simp
              · rw [dif_neg h, dif_neg (Ne.symm h)]
            · rw [dif_neg h, dif_neg]
              tauto) }

中文:
实例 hasFiniteBiproducts
  签名: : 有FiniteBiproducts (Mat_ C) where
  定义体: { has_biproduct := fun f =>
        hasBiproduct_of_total
          { pt := ⟨Σ j, (f j).ι, fun p => (f p.1).X p.2⟩
            π := fun j x y => by
              refine if h : x.1 = j then ?_ else 0
              refine if h' : @Eq.ndrec (Fin n) x.1 (fun j => (f j).ι) x.2 _ h = y then ?_ else 0
              apply eqToHom
              subst h h'
              rfl
            -- Notice we were careful not to use `subst` until we had a goal in `Prop`.
            ι := fun j x y => by
              refine if h : y.1 = j then ?_ else 0
              refine if h' : @Eq.ndrec _ y.1 (fun j => (f j).ι) y.2 _ h = x then ?_ else 0
              apply eqToHom
              subst h h'
              rfl
            ι_π := fun j j' => by
              ext x y
              dsimp
              simp_rw [dite_comp, comp_dite]
              simp only [ite_self, dite_eq_ite, Limits.comp_zero, Limits.zero_comp,
                eqToHom_trans]
              rw [← Finset.univ_sigma_univ]; rw [Finset.sum_sigma]
              dsimp +instances
              simp only [if_true, Finset.sum_dite_irrel, Finset.mem_univ,
                Finset.sum_const_zero, Finset.sum_dite_eq']
              split_ifs with h h'
              · subst h h'
                simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Mat_.id_apply_self]
              · subst h
                rw [eqToHom_refl]; rw [id_apply_of_ne _ _ _ h']
              · rfl }
          (by
            dsimp
            ext1 ⟨i, j⟩
            rintro ⟨i', j'⟩
            rw [Finset.sum_apply]; rw [Finset.sum_apply]
            dsimp
            rw [Finset.sum_eq_single i]; rotate_left
            · intro b _ hb
              apply Finset.sum_eq_zero
              intro x _
              rw [dif_neg hb.symm]; rw [zero_comp]
            · intro hi
              simp at hi
            rw [Finset.sum_eq_single j]; rotate_left
            · intro b _ hb
              rw [dif_pos rfl]; rw [dif_neg]; rw [zero_comp]
              simp only
              tauto
            · intro hj
              simp at hj
            simp only [eqToHom_refl, dite_eq_ite, ite_true, Category.id_comp,
              Sigma.mk.inj_iff, id_def]
            by_cases h : i' = i
            · subst h
              rw [dif_pos rfl]
              simp only [heq_eq_eq, true_and]
              by_cases h : j' = j
              · subst h
                simp
              · rw [dif_neg h, dif_neg (Ne.symm h)]
            · rw [dif_neg h, dif_neg]
              tauto) }

Depends on / 依赖: Eq.ndrec, eqToHom, hasBiproduct_of_total, has_biproduct
-/
instance hasFiniteBiproducts : HasFiniteBiproducts (Mat_ C) where
  out n :=
    { has_biproduct := fun f =>
        hasBiproduct_of_total
          { pt := ⟨Σ j, (f j).ι, fun p => (f p.1).X p.2⟩
            π := fun j x y => by
              refine if h : x.1 = j then ?_ else 0
              refine if h' : @Eq.ndrec (Fin n) x.1 (fun j => (f j).ι) x.2 _ h = y then ?_ else 0
              apply eqToHom
              subst h h'
              rfl
            -- Notice we were careful not to use `subst` until we had a goal in `Prop`.
            ι := fun j x y => by
              refine if h : y.1 = j then ?_ else 0
              refine if h' : @Eq.ndrec _ y.1 (fun j => (f j).ι) y.2 _ h = x then ?_ else 0
              apply eqToHom
              subst h h'
              rfl
            ι_π := fun j j' => by
              ext x y
              dsimp
              simp_rw [dite_comp, comp_dite]
              simp only [ite_self, dite_eq_ite, Limits.comp_zero, Limits.zero_comp,
                eqToHom_trans]
              rw [← Finset.univ_sigma_univ]; rw [Finset.sum_sigma]
              dsimp +instances
              simp only [if_true, Finset.sum_dite_irrel, Finset.mem_univ,
                Finset.sum_const_zero, Finset.sum_dite_eq']
              split_ifs with h h'
              · subst h h'
                simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Mat_.id_apply_self]
              · subst h
                rw [eqToHom_refl]; rw [id_apply_of_ne _ _ _ h']
              · rfl }
          (by
            dsimp
            ext1 ⟨i, j⟩
            rintro ⟨i', j'⟩
            rw [Finset.sum_apply]; rw [Finset.sum_apply]
            dsimp
            rw [Finset.sum_eq_single i]; rotate_left
            · intro b _ hb
              apply Finset.sum_eq_zero
              intro x _
              rw [dif_neg hb.symm]; rw [zero_comp]
            · intro hi
              simp at hi
            rw [Finset.sum_eq_single j]; rotate_left
            · intro b _ hb
              rw [dif_pos rfl]; rw [dif_neg]; rw [zero_comp]
              simp only
              tauto
            · intro hj
              simp at hj
            simp only [eqToHom_refl, dite_eq_ite, ite_true, Category.id_comp,
              Sigma.mk.inj_iff, id_def]
            by_cases h : i' = i
            · subst h
              rw [dif_pos rfl]
              simp only [heq_eq_eq, true_and]
              by_cases h : j' = j
              · subst h
                simp
              · rw [dif_neg h, dif_neg (Ne.symm h)]
            · rw [dif_neg h, dif_neg]
              tauto) }

end Mat_

namespace Functor

variable {C} {D : Type*} [Category.{v₁} D] [Preadditive D]

attribute [local simp] Mat_.id_apply eqToHom_map

/-- A functor induces a functor of matrix categories.
-/
@[simps]
/--
Definition of `mapMat_` / `mapMat_` 的定义

English:
definition mapMat_
  signature: (F : C ⥤ D) [Functor.Additive F]
  body: ⟨M.ι, fun i => F.obj (M.X i)⟩
  map f i j := F.map (f i j)

中文:
定义 mapMat_
  签名: (F : C ⥤ D) [函子.加性 F]
  定义体: ⟨M.ι, fun i => F.obj (M.X i)⟩
  map f i j := F.map (f i j)

Depends on / 依赖: F.obj
-/
def mapMat_ (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ Mat_ D where
  obj M := ⟨M.ι, fun i => F.obj (M.X i)⟩
  map f i j := F.map (f i j)

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor induces the identity functor on matrix categories.
-/
@[simps!]
/--
Definition of `mapMatId` / `mapMatId` 的定义

English:
definition mapMatId
  signature: : (𝟭 C).mapMat_ ≅ 𝟭 (Mat_ C)
  body: NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
    classical
    ext
    cases M; cases N
    simp [comp_dite, dite_comp]

中文:
定义 mapMatId
  签名: : (𝟭 C).mapMat_ ≅ 𝟭 (Mat_ C)
  定义体: NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
    classical
    ext
    cases M; cases N
    simp [comp_dite, dite_comp]

Depends on / 依赖: NatIso, NatIso.ofComponents, classical, comp_dite, dite_comp, eqToIso, ofComponents
-/
def mapMatId : (𝟭 C).mapMat_ ≅ 𝟭 (Mat_ C) :=
  NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
    classical
    ext
    cases M; cases N
    simp [comp_dite, dite_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Composite functors induce composite functors on matrix categories.
-/
@[simps!]
/--
Definition of `mapMatComp` / `mapMatComp` 的定义

English:
definition mapMatComp
  signature: {E : Type*} [Category.{v₁} E] [Preadditive E] (F : C ⥤ D) [Functor.Additive F]
  body: NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
    classical
    ext
    cases M; cases N
    simp [comp_dite, dite_comp]

中文:
定义 mapMatComp
  签名: {E : 类型} [范畴.{v₁} E] [预加性 E] (F : C ⥤ D) [函子.加性 F]
  定义体: NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
    classical
    ext
    cases M; cases N
    simp [comp_dite, dite_comp]

Depends on / 依赖: NatIso, NatIso.ofComponents, classical, comp_dite, dite_comp, eqToIso, ofComponents
-/
def mapMatComp {E : Type*} [Category.{v₁} E] [Preadditive E] (F : C ⥤ D) [Functor.Additive F]
    (G : D ⥤ E) [Functor.Additive G] : (F ⋙ G).mapMat_ ≅ F.mapMat_ ⋙ G.mapMat_ :=
  NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
    classical
    ext
    cases M; cases N
    simp [comp_dite, dite_comp]

end Functor

namespace Mat_

set_option backward.isDefEq.respectTransparency.types false in
/-- The embedding of `C` into `Mat_ C` as one-by-one matrices.
(We index the summands by `PUnit`.) -/
@[simps]
/--
Definition of `embedding` / `embedding` 的定义

English:
definition embedding
  signature: : C ⥤ Mat_ C where
  body: ⟨PUnit, fun _ => X⟩
  map f _ _ := f
  map_id _ := by ext ⟨⟩; simp
  map_comp _ _ := by ext ⟨⟩; simp

中文:
定义 embedding
  签名: : C ⥤ Mat_ C where
  定义体: ⟨PUnit, fun _ => X⟩
  map f _ _ := f
  map_id _ := by ext ⟨⟩; simp
  map_comp _ _ := by ext ⟨⟩; simp
-/
def embedding : C ⥤ Mat_ C where
  obj X := ⟨PUnit, fun _ => X⟩
  map f _ _ := f
  map_id _ := by ext ⟨⟩; simp
  map_comp _ _ := by ext ⟨⟩; simp

namespace Embedding

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (embedding C).Faithful
  body: congr_fun (congr_fun h PUnit.unit) PUnit.unit

中文:
实例 :
  签名: (embedding C).忠实
  定义体: congr_fun (congr_fun h PUnit.unit) PUnit.unit

Depends on / 依赖: PUnit.unit, congr_fun
-/
instance : (embedding C).Faithful where
  map_injective h := congr_fun (congr_fun h PUnit.unit) PUnit.unit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (embedding C).Full
  body: ⟨f PUnit.unit PUnit.unit, rfl⟩

中文:
实例 :
  签名: (embedding C).满
  定义体: ⟨f PUnit.unit PUnit.unit, rfl⟩

Depends on / 依赖: PUnit.unit
-/
instance : (embedding C).Full where map_surjective f := ⟨f PUnit.unit PUnit.unit, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Additive (embedding C)

中文:
实例 :
  签名: 函子.加性 (embedding C)
-/
instance : Functor.Additive (embedding C) where

end Embedding

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] : Inhabited (Mat_ C)
  body: ⟨(embedding C).obj default⟩

中文:
实例 [可居
  签名: C] : 可居 (Mat_ C)
  定义体: ⟨(embedding C).obj default⟩

Depends on / 依赖: embedding
-/
instance [Inhabited C] : Inhabited (Mat_ C) :=
  ⟨(embedding C).obj default⟩

open CategoryTheory.Limits

variable {C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- Every object in `Mat_ C` is isomorphic to the biproduct of its summands.
-/
@[simps]
/--
Definition of `isoBiproductEmbedding` / `isoBiproductEmbedding` 的定义

English:
definition isoBiproductEmbedding
  signature: (M : Mat_ C)
  body: biproduct.lift fun i j _ => if h : j = i then eqToHom (congr_arg M.X h) else 0
  inv := biproduct.desc fun i _ k => if h : i = k then eqToHom (congr_arg M.X h) else 0
  hom_inv_id := by
    simp only [biproduct.lift_desc]
    funext i j
    dsimp [id_def]
    rw [Finset.sum_apply]; rw [Finset.sum_apply]; rw [Finset.sum_eq_single i]; rotate_left
    · intro b _ hb
      dsimp
      rw [Fintype.univ_ofSubsingleton]; rw [Finset.sum_singleton]; rw [dif_neg hb.symm]; rw [zero_comp]
    · intro h
      simp at h
    simp
  inv_hom_id := by
    apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    simp only [Category.id_comp, Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      biproduct.ι_π]
    ext ⟨⟩ ⟨⟩
    simp only [embedding, comp_apply, comp_dite, dite_comp, comp_zero, zero_comp,
      Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]
    split_ifs with h
    · subst h
      simp
    · rfl

中文:
定义 isoBiproductEmbedding
  签名: (M : Mat_ C)
  定义体: biproduct.lift fun i j _ => if h : j = i then eqToHom (congr_arg M.X h) else 0
  inv := biproduct.desc fun i _ k => if h : i = k then eqToHom (congr_arg M.X h) else 0
  hom_inv_id := by
    simp only [biproduct.lift_desc]
    funext i j
    dsimp [id_def]
    rw [Finset.sum_apply]; rw [Finset.sum_apply]; rw [Finset.sum_eq_single i]; rotate_left
    · intro b _ hb
      dsimp
      rw [Fintype.univ_ofSubsingleton]; rw [Finset.sum_singleton]; rw [dif_neg hb.symm]; rw [zero_comp]
    · intro h
      simp at h
    simp
  inv_hom_id := by
    apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    simp only [Category.id_comp, Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      biproduct.ι_π]
    ext ⟨⟩ ⟨⟩
    simp only [embedding, comp_apply, comp_dite, dite_comp, comp_zero, zero_comp,
      Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]
    split_ifs with h
    · subst h
      simp
    · rfl

Depends on / 依赖: biproduct, biproduct.lift, congr_arg, eqToHom
-/
def isoBiproductEmbedding (M : Mat_ C) : M ≅ ⨁ fun i => (embedding C).obj (M.X i) where
  hom := biproduct.lift fun i j _ => if h : j = i then eqToHom (congr_arg M.X h) else 0
  inv := biproduct.desc fun i _ k => if h : i = k then eqToHom (congr_arg M.X h) else 0
  hom_inv_id := by
    simp only [biproduct.lift_desc]
    funext i j
    dsimp [id_def]
    rw [Finset.sum_apply]; rw [Finset.sum_apply]; rw [Finset.sum_eq_single i]; rotate_left
    · intro b _ hb
      dsimp
      rw [Fintype.univ_ofSubsingleton]; rw [Finset.sum_singleton]; rw [dif_neg hb.symm]; rw [zero_comp]
    · intro h
      simp at h
    simp
  inv_hom_id := by
    apply biproduct.hom_ext
    intro i
    apply biproduct.hom_ext'
    intro j
    simp only [Category.id_comp, Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      biproduct.ι_π]
    ext ⟨⟩ ⟨⟩
    simp only [embedding, comp_apply, comp_dite, dite_comp, comp_zero, zero_comp,
      Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]
    split_ifs with h
    · subst h
      simp
    · rfl

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D]

/-- This instance can be found using `Functor.hasBiproduct_of_preserves'`, but it is faster
to keep it here. -/
instance (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) :
    HasBiproduct (fun i => F.obj ((embedding C).obj (M.X i))) :=
  F.hasBiproduct_of_preserves _

/--
Definition of `additiveObjIsoBiproduct` / `additiveObjIsoBiproduct` 的定义

English:
definition additiveObjIsoBiproduct
  signature: (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C)
  body: F.mapIso (isoBiproductEmbedding M) ≪≫ F.mapBiproduct _

中文:
定义 additiveObjIsoBiproduct
  签名: (F : Mat_ C ⥤ D) [函子.加性 F] (M : Mat_ C)
  定义体: F.mapIso (isoBiproductEmbedding M) ≪≫ F.mapBiproduct _

Depends on / 依赖: F.mapBiproduct, F.mapIso, isoBiproductEmbedding, mapBiproduct, mapIso
-/
def additiveObjIsoBiproduct (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) :
    F.obj M ≅ ⨁ fun i => F.obj ((embedding C).obj (M.X i)) :=
  F.mapIso (isoBiproductEmbedding M) ≪≫ F.mapBiproduct _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `additiveObjIsoBiproduct_hom_π` / 引理 `additiveObjIsoBiproduct_hom_π`

English:
lemma additiveObjIsoBiproduct_hom_π
  given: (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι)
  proof: by
  dsimp [additiveObjIsoBiproduct]
  rw [biproduct.lift_π]; rw [Category.assoc]
  erw [biproduct.lift_π, ← F.map_comp]
  simp

中文:
引理 additiveObjIsoBiproduct_hom_π
  条件: (F : Mat_ C ⥤ D) [函子.加性 F] (M : Mat_ C) (i : M.ι)
  证明: by
  dsimp [additiveObjIsoBiproduct]
  rw [biproduct.lift_π]; rw [Category.assoc]
  erw [biproduct.lift_π, ← F.map_comp]
  simp

Depends on / 依赖: Category, Category.assoc, F.map_comp, additiveObjIsoBiproduct, biproduct, biproduct.lift_, map_comp
-/
lemma additiveObjIsoBiproduct_hom_π (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι) :
    (additiveObjIsoBiproduct F M).hom ≫ biproduct.π _ i =
      F.map (M.isoBiproductEmbedding.hom ≫ biproduct.π _ i) := by
  dsimp [additiveObjIsoBiproduct]
  rw [biproduct.lift_π]; rw [Category.assoc]
  erw [biproduct.lift_π, ← F.map_comp]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_additiveObjIsoBiproduct_inv` / 引理 `ι_additiveObjIsoBiproduct_inv`

English:
lemma ι_additiveObjIsoBiproduct_inv
  given: (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι)
  proof: by
  dsimp [additiveObjIsoBiproduct, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, ← F.map_comp]

中文:
引理 ι_additiveObjIsoBiproduct_inv
  条件: (F : Mat_ C ⥤ D) [函子.加性 F] (M : Mat_ C) (i : M.ι)
  证明: by
  dsimp [additiveObjIsoBiproduct, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, ← F.map_comp]

Depends on / 依赖: F.map_comp, Functor, Functor.mapBicone, Functor.mapBiproduct, additiveObjIsoBiproduct, biproduct, mapBicone, mapBiproduct, map_comp
-/
lemma ι_additiveObjIsoBiproduct_inv (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι) :
    biproduct.ι _ i ≫ (additiveObjIsoBiproduct F M).inv =
      F.map (biproduct.ι _ i ≫ M.isoBiproductEmbedding.inv) := by
  dsimp [additiveObjIsoBiproduct, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, ← F.map_comp]

variable [HasFiniteBiproducts D]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `additiveObjIsoBiproduct_naturality` / 定理 `additiveObjIsoBiproduct_naturality`

English:
theorem additiveObjIsoBiproduct_naturality
  statement: (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C}
  proof: by
  classical
  ext i : 1
  simp only [Category.assoc, additiveObjIsoBiproduct_hom_π, isoBiproductEmbedding_hom,
    biproduct.lift_π, biproduct.matrix_π,
    ← cancel_epi (additiveObjIsoBiproduct F M).inv, Iso.inv_hom_id_assoc]
  ext j : 1
  simp only [ι_additiveObjIsoBiproduct_inv_assoc, isoBiproductEmbedding_inv,
    biproduct.ι_desc, ← F.map_comp]
  congr 1
  funext ⟨⟩ ⟨⟩
  simp [comp_apply, dite_comp, comp_dite]

@[reassoc]

中文:
定理 additiveObjIsoBiproduct_naturality
  结论: (F : Mat_ C ⥤ D) [函子.加性 F] {M N : Mat_ C}
  证明: by
  classical
  ext i : 1
  simp only [Category.assoc, additiveObjIsoBiproduct_hom_π, isoBiproductEmbedding_hom,
    biproduct.lift_π, biproduct.matrix_π,
    ← cancel_epi (additiveObjIsoBiproduct F M).inv, Iso.inv_hom_id_assoc]
  ext j : 1
  simp only [ι_additiveObjIsoBiproduct_inv_assoc, isoBiproductEmbedding_inv,
    biproduct.ι_desc, ← F.map_comp]
  congr 1
  funext ⟨⟩ ⟨⟩
  simp [comp_apply, dite_comp, comp_dite]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, F.map_comp, Iso.inv_hom_id_assoc, additiveObjIsoBiproduct, biproduct, biproduct.lift_, biproduct.matrix_, cancel_epi, classical, comp_apply, comp_dite, dite_comp, inv_hom_id_assoc, isoBiproductEmbedding_hom, isoBiproductEmbedding_inv, map_comp
-/
theorem additiveObjIsoBiproduct_naturality (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C}
    (f : M ⟶ N) :
    F.map f ≫ (additiveObjIsoBiproduct F N).hom =
      (additiveObjIsoBiproduct F M).hom ≫
        biproduct.matrix fun i j => F.map ((embedding C).map (f i j)) := by
  classical
  ext i : 1
  simp only [Category.assoc, additiveObjIsoBiproduct_hom_π, isoBiproductEmbedding_hom,
    biproduct.lift_π, biproduct.matrix_π,
    ← cancel_epi (additiveObjIsoBiproduct F M).inv, Iso.inv_hom_id_assoc]
  ext j : 1
  simp only [ι_additiveObjIsoBiproduct_inv_assoc, isoBiproductEmbedding_inv,
    biproduct.ι_desc, ← F.map_comp]
  congr 1
  funext ⟨⟩ ⟨⟩
  simp [comp_apply, dite_comp, comp_dite]

@[reassoc]
/--
theorem `additiveObjIsoBiproduct_naturality'` / 定理 `additiveObjIsoBiproduct_naturality'`

English:
theorem additiveObjIsoBiproduct_naturality'
  statement: (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C}
  proof: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [additiveObjIsoBiproduct_naturality]

中文:
定理 additiveObjIsoBiproduct_naturality'
  结论: (F : Mat_ C ⥤ D) [函子.加性 F] {M N : Mat_ C}
  证明: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [additiveObjIsoBiproduct_naturality]

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, Iso.inv_comp_eq, additiveObjIsoBiproduct_naturality, eq_comp_inv, inv_comp_eq
-/
theorem additiveObjIsoBiproduct_naturality' (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C}
    (f : M ⟶ N) :
    (additiveObjIsoBiproduct F M).inv ≫ F.map f =
      biproduct.matrix (fun i j => F.map ((embedding C).map (f i j)) :) ≫
        (additiveObjIsoBiproduct F N).inv := by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [additiveObjIsoBiproduct_naturality]

attribute [local simp] biproduct.lift_desc

/-- Any additive functor `C ⥤ D` to a category `D` with finite biproducts extends to
a functor `Mat_ C ⥤ D`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (F : C ⥤ D) [Functor.Additive F]
  body: ⨁ fun i => F.obj (X.X i)
  map f := biproduct.matrix fun i j => F.map (f i j)
  map_id X := by
    ext i j
    by_cases h : j = i
    · subst h; simp
    · simp [h]

中文:
定义 lift
  签名: (F : C ⥤ D) [函子.加性 F]
  定义体: ⨁ fun i => F.obj (X.X i)
  map f := biproduct.matrix fun i j => F.map (f i j)
  map_id X := by
    ext i j
    by_cases h : j = i
    · subst h; simp
    · simp [h]

Depends on / 依赖: F.obj
-/
def lift (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ D where
  obj X := ⨁ fun i => F.obj (X.X i)
  map f := biproduct.matrix fun i j => F.map (f i j)
  map_id X := by
    ext i j
    by_cases h : j = i
    · subst h; simp
    · simp [h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `lift_additive` / 实例 `lift_additive`

English:
instance lift_additive
  signature: (F : C ⥤ D) [Functor.Additive F]

中文:
实例 lift_additive
  签名: (F : C ⥤ D) [函子.加性 F]
-/
instance lift_additive (F : C ⥤ D) [Functor.Additive F] : Functor.Additive (lift F) where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An additive functor `C ⥤ D` factors through its lift to `Mat_ C ⥤ D`. -/
@[simps!]
/--
Definition of `embeddingLiftIso` / `embeddingLiftIso` 的定义

English:
definition embeddingLiftIso
  signature: (F : C ⥤ D) [Functor.Additive F]
  body: NatIso.ofComponents
    (fun X =>
      { hom := biproduct.desc fun _ => 𝟙 (F.obj X)
        inv := biproduct.lift fun _ => 𝟙 (F.obj X) })

中文:
定义 embeddingLiftIso
  签名: (F : C ⥤ D) [函子.加性 F]
  定义体: NatIso.ofComponents
    (fun X =>
      { hom := biproduct.desc fun _ => 𝟙 (F.obj X)
        inv := biproduct.lift fun _ => 𝟙 (F.obj X) })

Depends on / 依赖: F.obj, NatIso, NatIso.ofComponents, biproduct, biproduct.desc, biproduct.lift, ofComponents
-/
def embeddingLiftIso (F : C ⥤ D) [Functor.Additive F] : embedding C ⋙ lift F ≅ F :=
  NatIso.ofComponents
    (fun X =>
      { hom := biproduct.desc fun _ => 𝟙 (F.obj X)
        inv := biproduct.lift fun _ => 𝟙 (F.obj X) })

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `liftUnique` / `liftUnique` 的定义

English:
definition liftUnique
  signature: (F : C ⥤ D) [Functor.Additive F] (L : Mat_ C ⥤ D) [Functor.Additive L]
  body: NatIso.ofComponents
    (fun M =>
      additiveObjIsoBiproduct L M ≪≫
        (biproduct.mapIso fun i => α.app (M.X i)) ≪≫
          (biproduct.mapIso fun i => (embeddingLiftIso F).symm.app (M.X i)) ≪≫
            (additiveObjIsoBiproduct (lift F) M).symm)
    fun f => by
      dsimp only [Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom]
      simp only [additiveObjIsoBiproduct_naturality_assoc]
      simp only [biproduct.matrix_map_assoc, Category.assoc]
      simp only [additiveObjIsoBiproduct_naturality']
      simp only [biproduct.map_matrix_assoc]
      congr 3
      ext j k
      apply biproduct.hom_ext
      rintro ⟨⟩
      dsimp
      simpa using α.hom.naturality (f j k)

中文:
定义 liftUnique
  签名: (F : C ⥤ D) [函子.加性 F] (L : Mat_ C ⥤ D) [函子.加性 L]
  定义体: NatIso.ofComponents
    (fun M =>
      additiveObjIsoBiproduct L M ≪≫
        (biproduct.mapIso fun i => α.app (M.X i)) ≪≫
          (biproduct.mapIso fun i => (embeddingLiftIso F).symm.app (M.X i)) ≪≫
            (additiveObjIsoBiproduct (lift F) M).symm)
    fun f => by
      dsimp only [Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom]
      simp only [additiveObjIsoBiproduct_naturality_assoc]
      simp only [biproduct.matrix_map_assoc, Category.assoc]
      simp only [additiveObjIsoBiproduct_naturality']
      simp only [biproduct.map_matrix_assoc]
      congr 3
      ext j k
      apply biproduct.hom_ext
      rintro ⟨⟩
      dsimp
      simpa using α.hom.naturality (f j k)

Depends on / 依赖: Category, Category.assoc, Iso.symm_hom, Iso.trans_hom, NatIso, NatIso.ofComponents, additiveObjIsoBiproduct, additiveObjIsoBiproduct_naturality, additiveObjIsoBiproduct_naturality_assoc, biproduct, biproduct.mapIso, biproduct.mapIso_hom, biproduct.map_matrix_assoc, biproduct.matrix_map_assoc, embeddingLiftIso, mapIso, mapIso_hom, map_matrix_assoc, matrix_map_assoc, ofComponents
-/
def liftUnique (F : C ⥤ D) [Functor.Additive F] (L : Mat_ C ⥤ D) [Functor.Additive L]
    (α : embedding C ⋙ L ≅ F) : L ≅ lift F :=
  NatIso.ofComponents
    (fun M =>
      additiveObjIsoBiproduct L M ≪≫
        (biproduct.mapIso fun i => α.app (M.X i)) ≪≫
          (biproduct.mapIso fun i => (embeddingLiftIso F).symm.app (M.X i)) ≪≫
            (additiveObjIsoBiproduct (lift F) M).symm)
    fun f => by
      dsimp only [Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom]
      simp only [additiveObjIsoBiproduct_naturality_assoc]
      simp only [biproduct.matrix_map_assoc, Category.assoc]
      simp only [additiveObjIsoBiproduct_naturality']
      simp only [biproduct.map_matrix_assoc]
      congr 3
      ext j k
      apply biproduct.hom_ext
      rintro ⟨⟩
      dsimp
      simpa using α.hom.naturality (f j k)

-- TODO is there some uniqueness statement for the natural isomorphism in `liftUnique`?
/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {F G : Mat_ C ⥤ D} [Functor.Additive F] [Functor.Additive G]
  body: liftUnique (embedding C ⋙ G) _ α ≪≫ (liftUnique _ _ (Iso.refl _)).symm

中文:
定义 ext
  签名: {F G : Mat_ C ⥤ D} [函子.加性 F] [函子.加性 G]
  定义体: liftUnique (embedding C ⋙ G) _ α ≪≫ (liftUnique _ _ (Iso.refl _)).symm

Depends on / 依赖: Iso.refl, embedding, liftUnique
-/
def ext {F G : Mat_ C ⥤ D} [Functor.Additive F] [Functor.Additive G]
    (α : embedding C ⋙ F ≅ embedding C ⋙ G) : F ≅ G :=
  liftUnique (embedding C ⋙ G) _ α ≪≫ (liftUnique _ _ (Iso.refl _)).symm

/--
Definition of `equivalenceSelfOfHasFiniteBiproductsAux` / `equivalenceSelfOfHasFiniteBiproductsAux` 的定义

English:
definition equivalenceSelfOfHasFiniteBiproductsAux
  signature: [HasFiniteBiproducts C]
  body: Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (embeddingLiftIso _).symm _ ≪≫ Functor.associator _ _ _

中文:
定义 equivalenceSelfOfHasFiniteBiproductsAux
  签名: [有FiniteBiproducts C]
  定义体: Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (embeddingLiftIso _).symm _ ≪≫ Functor.associator _ _ _

Depends on / 依赖: Functor, Functor.associator, Functor.isoWhiskerRight, Functor.leftUnitor, Functor.rightUnitor, associator, embeddingLiftIso, isoWhiskerRight, leftUnitor, rightUnitor
-/
def equivalenceSelfOfHasFiniteBiproductsAux [HasFiniteBiproducts C] :
    embedding C ⋙ 𝟭 (Mat_ C) ≅ embedding C ⋙ lift (𝟭 C) ⋙ embedding C :=
  Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (embeddingLiftIso _).symm _ ≪≫ Functor.associator _ _ _

/--
Definition of `equivalenceSelfOfHasFiniteBiproducts` / `equivalenceSelfOfHasFiniteBiproducts` 的定义

English:
definition equivalenceSelfOfHasFiniteBiproducts
  signature: (C : Type (u₁ + 1)) [LargeCategory C] [Preadditive C]
  body: Equivalence.mk
    (-- I suspect this is already an adjoint equivalence, but it seems painful to verify.
      lift
      (𝟭 C))
    (embedding C) (ext equivalenceSelfOfHasFiniteBiproductsAux) (embeddingLiftIso (𝟭 C))

@[simp]

中文:
定义 equivalenceSelfOfHasFiniteBiproducts
  签名: (C : 类型 (u₁ + 1)) [大范畴 C] [预加性 C]
  定义体: Equivalence.mk
    (-- I suspect this is already an adjoint equivalence, but it seems painful to verify.
      lift
      (𝟭 C))
    (embedding C) (ext equivalenceSelfOfHasFiniteBiproductsAux) (embeddingLiftIso (𝟭 C))

@[simp]

Depends on / 依赖: Equivalence, Equivalence.mk, adjoint, already, embedding, embeddingLiftIso, equivalence, equivalenceSelfOfHasFiniteBiproductsAux, painful, suspect, verify
-/
def equivalenceSelfOfHasFiniteBiproducts (C : Type (u₁ + 1)) [LargeCategory C] [Preadditive C]
    [HasFiniteBiproducts C] : Mat_ C ≌ C :=
  Equivalence.mk
    (-- I suspect this is already an adjoint equivalence, but it seems painful to verify.
      lift
      (𝟭 C))
    (embedding C) (ext equivalenceSelfOfHasFiniteBiproductsAux) (embeddingLiftIso (𝟭 C))

@[simp]
/--
theorem `equivalenceSelfOfHasFiniteBiproducts_functor` / 定理 `equivalenceSelfOfHasFiniteBiproducts_functor`

English:
theorem equivalenceSelfOfHasFiniteBiproducts_functor
  statement: {C : Type (u₁ + 1)} [LargeCategory C]
  proof: rfl

@[simp]

中文:
定理 equivalenceSelfOfHasFiniteBiproducts_functor
  结论: {C : 类型 (u₁ + 1)} [大范畴 C]
  证明: rfl

@[simp]
-/
theorem equivalenceSelfOfHasFiniteBiproducts_functor {C : Type (u₁ + 1)} [LargeCategory C]
    [Preadditive C] [HasFiniteBiproducts C] :
    (equivalenceSelfOfHasFiniteBiproducts C).functor = lift (𝟭 C) :=
  rfl

@[simp]
/--
theorem `equivalenceSelfOfHasFiniteBiproducts_inverse` / 定理 `equivalenceSelfOfHasFiniteBiproducts_inverse`

English:
theorem equivalenceSelfOfHasFiniteBiproducts_inverse
  statement: {C : Type (u₁ + 1)} [LargeCategory C]
  proof: rfl

中文:
定理 equivalenceSelfOfHasFiniteBiproducts_inverse
  结论: {C : 类型 (u₁ + 1)} [大范畴 C]
  证明: rfl
-/
theorem equivalenceSelfOfHasFiniteBiproducts_inverse {C : Type (u₁ + 1)} [LargeCategory C]
    [Preadditive C] [HasFiniteBiproducts C] :
    (equivalenceSelfOfHasFiniteBiproducts C).inverse = embedding C :=
  rfl

end Mat_

universe u

/-- A type synonym for `Fintype`, which we will equip with a category structure
where the morphisms are matrices with components in `R`. -/
@[nolint unusedArguments]
/--
Definition of `Mat` / `Mat` 的定义

English:
definition Mat
  signature: (_ : Type u)
  body: FintypeCat.{u}
deriving Inhabited

中文:
定义 Mat
  签名: (_ : 类型u)
  定义体: FintypeCat.{u}
deriving Inhabited

Depends on / 依赖: FintypeCat
-/
def Mat (_ : Type u) :=
  FintypeCat.{u}
deriving Inhabited

instance (R : Type u) : CoeSort (Mat R) (Type u) :=
  FintypeCat.instCoeSort

open Matrix

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] FintypeCat.fintype in
open scoped Classical in
instance (R : Type u) [Semiring R] : Category (Mat R) where
  Hom X Y := Matrix X Y R
  id X := (1 : Matrix X X R)
  comp {X Y Z} f g := (show Matrix X Y R from f) * (show Matrix Y Z R from g)
  assoc := by intros; simp [Matrix.mul_assoc]

namespace Mat

section

variable {R : Type u} [Semiring R]

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {X Y : Mat R} (f g : X ⟶ Y) (h : forall i j, f i j = g i j)
  statement: f = g
  proof: Matrix.ext_iff.mp h

中文:
定理 hom_ext
  条件: {X Y : Mat R} (f g : X ⟶ Y) (h : 对任意 i j, f i j = g i j)
  结论: f = g
  证明: Matrix.ext_iff.mp h

Depends on / 依赖: Matrix, Matrix.ext_iff.mp, ext_iff
-/
theorem hom_ext {X Y : Mat R} (f g : X ⟶ Y) (h : forall i j, f i j = g i j) : f = g :=
  Matrix.ext_iff.mp h

variable (R)

open scoped Classical in
/--
theorem `id_def` / 定理 `id_def`

English:
theorem id_def
  given: (M : Mat R)
  statement: 𝟙 M = fun i j => if i = j then 1 else 0
  proof: rfl

中文:
定理 id_def
  条件: (M : Mat R)
  结论: 𝟙 M = fun i j => if i = j then 1 else 0
  证明: rfl
-/
theorem id_def (M : Mat R) : 𝟙 M = fun i j => if i = j then 1 else 0 :=
  rfl

open scoped Classical in
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (M : Mat R) (i j : M)
  statement: (𝟙 M : Matrix M M R) i j = if i = j then 1 else 0
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (M : Mat R) (i j : M)
  结论: (𝟙 M : 矩阵 M M R) i j = if i = j then 1 else 0
  证明: rfl

@[simp]
-/
theorem id_apply (M : Mat R) (i j : M) : (𝟙 M : Matrix M M R) i j = if i = j then 1 else 0 :=
  rfl

@[simp]
/--
theorem `id_apply_self` / 定理 `id_apply_self`

English:
theorem id_apply_self
  given: (M : Mat R) (i : M)
  statement: (𝟙 M : Matrix M M R) i i = 1
  proof: by simp [id_apply]

@[simp]

中文:
定理 id_apply_self
  条件: (M : Mat R) (i : M)
  结论: (𝟙 M : 矩阵 M M R) i i = 1
  证明: by simp [id_apply]

@[simp]

Depends on / 依赖: id_apply
-/
theorem id_apply_self (M : Mat R) (i : M) : (𝟙 M : Matrix M M R) i i = 1 := by simp [id_apply]

@[simp]
/--
theorem `id_apply_of_ne` / 定理 `id_apply_of_ne`

English:
theorem id_apply_of_ne
  given: (M : Mat R) (i j : M) (h : i != j)
  statement: (𝟙 M : Matrix M M R) i j = 0
  proof: by
  simp [id_apply, h]

中文:
定理 id_apply_of_ne
  条件: (M : Mat R) (i j : M) (h : i != j)
  结论: (𝟙 M : 矩阵 M M R) i j = 0
  证明: by
  simp [id_apply, h]

Depends on / 依赖: id_apply
-/
theorem id_apply_of_ne (M : Mat R) (i j : M) (h : i != j) : (𝟙 M : Matrix M M R) i j = 0 := by
  simp [id_apply, h]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] FintypeCat.fintype in
/--
theorem `comp_def` / 定理 `comp_def`

English:
theorem comp_def
  given: {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K)
  proof: rfl

中文:
定理 comp_def
  条件: {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K)
  证明: rfl
-/
theorem comp_def {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N, f i j * g j k :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] FintypeCat.fintype in
@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) (i k)
  proof: rfl

中文:
定理 comp_apply
  条件: {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) (i k)
  证明: rfl
-/
theorem comp_apply {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N, f i j * g j k :=
  rfl

instance (M N : Mat R) : Inhabited (M ⟶ N) :=
  ⟨fun (_ : M) (_ : N) => (0 : R)⟩

end

variable (R : Type) [Ring R]

open Opposite

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `CategoryTheory.Mat.equivalenceSingleObj`. -/
@[simps]
/--
Definition of `equivalenceSingleObjInverse` / `equivalenceSingleObjInverse` 的定义

English:
definition equivalenceSingleObjInverse
  signature: : Mat_ (SingleObj Rᵐᵒᵖ) ⥤ Mat R where
  body: FintypeCat.of X.ι
  map f i j := MulOpposite.unop (f i j)
  map_id X := by
    ext
    simp only [Mat_.id_def, id_def]
    split_ifs <;> rfl
  map_comp f g := by
    -- Porting note: this proof was automatic in mathlib3
    ext
    simp only [Mat_.comp_apply, comp_apply]
    convert! Finset.unop_sum _ _

中文:
定义 equivalenceSingleObjInverse
  签名: : Mat_ (SingleObj Rᵐᵒᵖ) ⥤ Mat R where
  定义体: FintypeCat.of X.ι
  map f i j := MulOpposite.unop (f i j)
  map_id X := by
    ext
    simp only [Mat_.id_def, id_def]
    split_ifs <;> rfl
  map_comp f g := by
    -- Porting note: this proof was automatic in mathlib3
    ext
    simp only [Mat_.comp_apply, comp_apply]
    convert! Finset.unop_sum _ _

Depends on / 依赖: FintypeCat, FintypeCat.of
-/
def equivalenceSingleObjInverse : Mat_ (SingleObj Rᵐᵒᵖ) ⥤ Mat R where
  obj X := FintypeCat.of X.ι
  map f i j := MulOpposite.unop (f i j)
  map_id X := by
    ext
    simp only [Mat_.id_def, id_def]
    split_ifs <;> rfl
  map_comp f g := by
    -- Porting note: this proof was automatic in mathlib3
    ext
    simp only [Mat_.comp_apply, comp_apply]
    convert! Finset.unop_sum _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (equivalenceSingleObjInverse R).Faithful
  body: by
    ext
    apply_fun MulOpposite.unop using MulOpposite.unop_injective
    exact congr_fun (congr_fun w _) _

中文:
实例 :
  签名: (equivalenceSingleObjInverse R).忠实
  定义体: by
    ext
    apply_fun MulOpposite.unop using MulOpposite.unop_injective
    exact congr_fun (congr_fun w _) _

Depends on / 依赖: MulOpposite, MulOpposite.unop, MulOpposite.unop_injective, apply_fun, congr_fun, unop_injective
-/
instance : (equivalenceSingleObjInverse R).Faithful where
  map_injective w := by
    ext
    apply_fun MulOpposite.unop using MulOpposite.unop_injective
    exact congr_fun (congr_fun w _) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (equivalenceSingleObjInverse R).Full
  body: ⟨fun i j => MulOpposite.op (f i j), rfl⟩

中文:
实例 :
  签名: (equivalenceSingleObjInverse R).满
  定义体: ⟨fun i j => MulOpposite.op (f i j), rfl⟩

Depends on / 依赖: MulOpposite, MulOpposite.op
-/
instance : (equivalenceSingleObjInverse R).Full where
  map_surjective f := ⟨fun i j => MulOpposite.op (f i j), rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] FintypeCat.fintype in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (equivalenceSingleObjInverse R).EssSurj
  body: ⟨{ ι := X
        X := fun _ => PUnit.unit }, ⟨eqToIso (by cases X; congr)⟩⟩

中文:
实例 :
  签名: (equivalenceSingleObjInverse R).本质满射
  定义体: ⟨{ ι := X
        X := fun _ => PUnit.unit }, ⟨eqToIso (by cases X; congr)⟩⟩

Depends on / 依赖: PUnit.unit, eqToIso
-/
instance : (equivalenceSingleObjInverse R).EssSurj where
  mem_essImage X :=
    ⟨{ ι := X
        X := fun _ => PUnit.unit }, ⟨eqToIso (by cases X; congr)⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (equivalenceSingleObjInverse R).IsEquivalence

中文:
实例 :
  签名: (equivalenceSingleObjInverse R).是等价
-/
instance : (equivalenceSingleObjInverse R).IsEquivalence where

/--
Definition of `equivalenceSingleObj` / `equivalenceSingleObj` 的定义

English:
definition equivalenceSingleObj
  signature: : Mat R ≌ Mat_ (SingleObj Rᵐᵒᵖ)
  body: (equivalenceSingleObjInverse R).asEquivalence.symm

中文:
定义 equivalenceSingleObj
  签名: : Mat R ≌ Mat_ (SingleObj Rᵐᵒᵖ)
  定义体: (equivalenceSingleObjInverse R).asEquivalence.symm

Depends on / 依赖: asEquivalence, asEquivalence.symm, equivalenceSingleObjInverse
-/
def equivalenceSingleObj : Mat R ≌ Mat_ (SingleObj Rᵐᵒᵖ) :=
  (equivalenceSingleObjInverse R).asEquivalence.symm

instance (X Y : Mat R) : AddCommGroup (X ⟶ Y) :=
inferInstanceAs AddCommGroup (Matrix X Y R)

variable {R}

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: {M N : Mat R} (f g : M ⟶ N) (i j)
  statement: (f + g) i j = f i j + g i j
  proof: rfl

中文:
定理 add_apply
  条件: {M N : Mat R} (f g : M ⟶ N) (i j)
  结论: (f + g) i j = f i j + g i j
  证明: rfl
-/
theorem add_apply {M N : Mat R} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
  rfl

attribute [local simp] add_mul mul_add Finset.sum_add_distrib

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (Mat R)

中文:
实例 :
  签名: 预加性 (Mat R)
-/
instance : Preadditive (Mat R) where

-- TODO show `Mat R` has biproducts, and that `biprod.map` "is" forming a block diagonal matrix.
end Mat

end CategoryTheory
