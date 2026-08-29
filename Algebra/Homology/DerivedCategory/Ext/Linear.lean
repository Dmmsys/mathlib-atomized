/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Ext-modules in linear categories

In this file, we show that if `C` is an `R`-linear abelian category,
then there is an `R`-module structure on the groups `Ext X Y n`
for `X` and `Y` in `C` and `n : ℕ`.

-/

@[expose] public section

universe w' w t v u

namespace CategoryTheory

namespace Abelian

namespace Ext

section Ring

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : Nat}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (Ext X Y n)
  body: letI := HasDerivedCategory.standard C
  Equiv.module R homEquiv

中文:
实例 :
  签名: 模 R (Ext X Y n)
  定义体: letI := HasDerivedCategory.standard C
  Equiv.module R homEquiv

Depends on / 依赖: Equiv.module, HasDerivedCategory, HasDerivedCategory.standard, homEquiv, module, standard
-/
noncomputable instance : Module R (Ext X Y n) :=
  letI := HasDerivedCategory.standard C
  Equiv.module R homEquiv

/--
lemma `smul_eq_comp_mk₀` / 引理 `smul_eq_comp_mk₀`

English:
lemma smul_eq_comp_mk₀
  given: (x : Ext X Y n) (r : R)
  proof: by
  let := HasDerivedCategory.standard C
  ext
  apply ((Equiv.linearEquiv R homEquiv).map_smul r x).trans
  change r • homEquiv x = (x.comp (mk₀ (r • 𝟙 Y)) (add_zero _)).hom
  rw [comp_hom]; rw [mk₀_hom]; rw [Functor.map_smul]; rw [Functor.map_id]; rw [ShiftedHom.mk₀_smul]; rw [ShiftedHom.comp_smu

中文:
引理 smul_eq_comp_mk₀
  条件: (x : Ext X Y n) (r : R)
  证明: by
  let := HasDerivedCategory.standard C
  ext
  apply ((Equiv.linearEquiv R homEquiv).map_smul r x).trans
  change r • homEquiv x = (x.comp (mk₀ (r • 𝟙 Y)) (add_zero _)).hom
  rw [comp_hom]; rw [mk₀_hom]; rw [Functor.map_smul]; rw [Functor.map_id]; rw [ShiftedHom.mk₀_smul]; rw [ShiftedHom.comp_smu

Depends on / 依赖: Equiv.linearEquiv, Functor, Functor.map_id, Functor.map_smul, HasDerivedCategory, HasDerivedCategory.standard, ShiftedHom, ShiftedHom.comp_mk, ShiftedHom.comp_smul, ShiftedHom.mk, add_zero, comp_hom, comp_smul, homEquiv, linearEquiv, map_id, map_smul, standard, x.comp
-/
lemma smul_eq_comp_mk₀ (x : Ext X Y n) (r : R) :
    r • x = x.comp (mk₀ (r • 𝟙 Y)) (add_zero _) := by
  let := HasDerivedCategory.standard C
  ext
  apply ((Equiv.linearEquiv R homEquiv).map_smul r x).trans
  change r • homEquiv x = (x.comp (mk₀ (r • 𝟙 Y)) (add_zero _)).hom
  rw [comp_hom]; rw [mk₀_hom]; rw [Functor.map_smul]; rw [Functor.map_id]; rw [ShiftedHom.mk₀_smul]; rw [ShiftedHom.comp_smul]; rw [ShiftedHom.comp_mk₀_id]

@[simp]
/--
lemma `smul_hom` / 引理 `smul_hom`

English:
lemma smul_hom
  given: (x : Ext X Y n) (r : R) [HasDerivedCategory C]
  proof: by
  simp [smul_eq_comp_mk₀]

@[simp]

中文:
引理 smul_hom
  条件: (x : Ext X Y n) (r : R) [HasDerivedCategory C]
  证明: by
  simp [smul_eq_comp_mk₀]

@[simp]
-/
lemma smul_hom (x : Ext X Y n) (r : R) [HasDerivedCategory C] :
    (r • x).hom = r • x.hom := by
  simp [smul_eq_comp_mk₀]

@[simp]
/--
lemma `comp_smul` / 引理 `comp_smul`

English:
lemma comp_smul
  statement: {X Y Z : C} {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b)
  proof: by
  let := HasDerivedCategory.standard C
  aesop

@[simp]

中文:
引理 comp_smul
  结论: {X Y Z : C} {a b : 自然数} (α : Ext X Y a) (β : Ext Y Z b)
  证明: by
  let := HasDerivedCategory.standard C
  aesop

@[simp]

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard
-/
lemma comp_smul {X Y Z : C} {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b)
    {c : Nat} (h : a + b = c) (r : R) :
    α.comp (r • β) h = r • α.comp β h := by
  let := HasDerivedCategory.standard C
  aesop

@[simp]
/--
lemma `smul_comp` / 引理 `smul_comp`

English:
lemma smul_comp
  statement: {X Y Z : C} {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b)
  proof: by
  let := HasDerivedCategory.standard C
  aesop

中文:
引理 smul_comp
  结论: {X Y Z : C} {a b : 自然数} (α : Ext X Y a) (β : Ext Y Z b)
  证明: by
  let := HasDerivedCategory.standard C
  aesop

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard
-/
lemma smul_comp {X Y Z : C} {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b)
    {c : Nat} (h : a + b = c) (r : R) :
    (r • α).comp β h = r • α.comp β h := by
  let := HasDerivedCategory.standard C
  aesop

open DerivedCategory in
/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the `R`-linear
equivalence between `Ext.{w} X Y n` and a type of morphisms in the derived category
of the `R`-linear abelian category `C`. -/
@[simps]
/--
Definition of `homLinearEquiv` / `homLinearEquiv` 的定义

English:
definition homLinearEquiv
  signature: [HasDerivedCategory.{w'} C]
  body: homAddEquiv
  map_smul' := by simp

中文:
定义 homLinearEquiv
  签名: [HasDerivedCategory.{w'} C]
  定义体: homAddEquiv
  map_smul' := by simp

Depends on / 依赖: homAddEquiv
-/
noncomputable def homLinearEquiv [HasDerivedCategory.{w'} C] :
    Ext X Y n ≃ₗ[R]
      ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : Int) where
  __ := homAddEquiv
  map_smul' := by simp

/--
lemma `mk₀_smul` / 引理 `mk₀_smul`

English:
lemma mk₀_smul
  given: (r : R) (f : X ⟶ Y)
  statement: mk₀ (r • f) = r • mk₀ f
  proof: by
  let := HasDerivedCategory.standard C
  aesop

中文:
引理 mk₀_smul
  条件: (r : R) (f : X ⟶ Y)
  结论: mk₀ (r • f) = r • mk₀ f
  证明: by
  let := HasDerivedCategory.standard C
  aesop

Depends on / 依赖: HasDerivedCategory, HasDerivedCategory.standard, standard
-/
lemma mk₀_smul (r : R) (f : X ⟶ Y) : mk₀ (r • f) = r • mk₀ f := by
  let := HasDerivedCategory.standard C
  aesop

/-- The linear equivalence `Ext X Y 0 ≃ₜ[R] (X ⟶ Y)`. -/
@[simps! symm_apply]
/--
Definition of `linearEquiv₀` / `linearEquiv₀` 的定义

English:
definition linearEquiv₀
  signature: :
  body: addEquiv₀
  map_smul' m x := homEquiv₀.symm.injective (by simp [mk₀_smul])

@[simp]

中文:
定义 linearEquiv₀
  签名: :
  定义体: addEquiv₀
  map_smul' m x := homEquiv₀.symm.injective (by simp [mk₀_smul])

@[simp]
-/
noncomputable def linearEquiv₀ :
    Ext X Y 0 ≃ₗ[R] (X ⟶ Y) where
  toAddEquiv := addEquiv₀
  map_smul' m x := homEquiv₀.symm.injective (by simp [mk₀_smul])

@[simp]
/--
lemma `mk₀_linearEquiv₀_apply` / 引理 `mk₀_linearEquiv₀_apply`

English:
lemma mk₀_linearEquiv₀_apply
  given: (f : Ext X Y 0)
  proof: addEquiv₀.left_inv f

中文:
引理 mk₀_linearEquiv₀_apply
  条件: (f : Ext X Y 0)
  证明: addEquiv₀.left_inv f
-/
lemma mk₀_linearEquiv₀_apply (f : Ext X Y 0) :
    mk₀ (linearEquiv₀ (R := R) f) = f :=
  addEquiv₀.left_inv f

end Ring

section CommRing

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The composition of `Ext`, as a bilinear map. -/
@[simps!]
/--
Definition of `bilinearCompOfLinear` / `bilinearCompOfLinear` 的定义

English:
definition bilinearCompOfLinear
  signature: (R : Type t) [CommRing R] [Linear R C] (X Y Z : C)
  body: { toFun β := α.comp β h
      map_add' := by simp
      map_smul' := by simp }
  map_add' := by aesop
  map_smul' := by aesop

中文:
定义 bilinearCompOfLinear
  签名: (R : 类型 t) [交换环 R] [线性 R C] (X Y Z : C)
  定义体: { toFun β := α.comp β h
      map_add' := by simp
      map_smul' := by simp }
  map_add' := by aesop
  map_smul' := by aesop

Depends on / 依赖: map_add, map_smul
-/
noncomputable def bilinearCompOfLinear (R : Type t) [CommRing R] [Linear R C] (X Y Z : C)
    (a b c : Nat) (h : a + b = c) :
    Ext X Y a ->ₗ[R] Ext Y Z b ->ₗ[R] Ext X Z c where
  toFun α :=
    { toFun β := α.comp β h
      map_add' := by simp
      map_smul' := by simp }
  map_add' := by aesop
  map_smul' := by aesop

/--
Definition of `postcompOfLinear` / `postcompOfLinear` 的定义

English:
abbreviation postcompOfLinear
  signature: {Y Z : C} {n : Nat} (β : Ext Y Z n)
  body: (bilinearCompOfLinear R X Y Z a n b h).flip β

中文:
缩写 postcompOfLinear
  签名: {Y Z : C} {n : 自然数} (β : Ext Y Z n)
  定义体: (bilinearCompOfLinear R X Y Z a n b h).flip β

Depends on / 依赖: bilinearCompOfLinear
-/
noncomputable abbrev postcompOfLinear {Y Z : C} {n : Nat} (β : Ext Y Z n)
    (R : Type t) [CommRing R] [Linear R C] (X : C) {a b : Nat} (h : a + n = b) :
    Ext X Y a ->ₗ[R] Ext X Z b :=
  (bilinearCompOfLinear R X Y Z a n b h).flip β

/--
Definition of `precompOfLinear` / `precompOfLinear` 的定义

English:
abbreviation precompOfLinear
  signature: {X Y : C} {n : Nat} (α : Ext X Y n)
  body: bilinearCompOfLinear R X Y Z n a b h α

中文:
缩写 precompOfLinear
  签名: {X Y : C} {n : 自然数} (α : Ext X Y n)
  定义体: bilinearCompOfLinear R X Y Z n a b h α

Depends on / 依赖: bilinearCompOfLinear
-/
noncomputable abbrev precompOfLinear {X Y : C} {n : Nat} (α : Ext X Y n)
    (R : Type t) [CommRing R] [Linear R C] (Z : C) {a b : Nat} (h : n + a = b) :
    Ext Y Z a ->ₗ[R] Ext X Z b :=
  bilinearCompOfLinear R X Y Z n a b h α

end CommRing

end Ext

end Abelian

end CategoryTheory
