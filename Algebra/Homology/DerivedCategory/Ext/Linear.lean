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

variable {X Y : C} {n : ℕ}

/-
**CategoryTheory.Abelian.Ext.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Abelian.
Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Module R (Ext X Y n) :=
  letI := HasDerivedCategory.standard C
  Equiv.module R homEquiv
/-
**CategoryTheory.Abelian.Ext.smul_eq_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_eq_comp_mk₀ (x : Ext X Y n) (r : R) :
    r • x = x.comp (mk₀ (r • 𝟙 Y)) (add_zero _) := by
  let := HasDerivedCategory.standard C
  ext
  apply ((Equiv.linearEquiv R homEquiv).map_smul r x).trans
  change r • homEquiv x = (x.comp (mk₀ (r • 𝟙 Y)) (add_zero _)).hom
  rw [comp_hom, mk₀_hom, Functor.map_smul, Functor.map_id, ShiftedHom.mk₀_smul,
    ShiftedHom.comp_smul, ShiftedHom.comp_mk₀_id]

@[simp]
/-
**CategoryTheory.Abelian.Ext.smul_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Abelian.Ext`。
形式化陈述：smul_hom (x : Ext X Y n) (r : R) [HasDerivedCategory C] : (r • x).hom = r 
• x.hom
参数：x : Ext X Y n；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀`：smul_eq_comp_mk₀ (x : Ext X
 Y n) (r : R) : r • x = x.comp (mk₀ (r • 𝟙 Y)) (add_zero _)
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_hom`：mk₀_hom [HasDerivedCategory.{w'} C] 
(f : X ⟶ Y) : (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map 
f)
· 使用定理 `CategoryTheory.ShiftedHom.mk₀.congr_simp`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2
 : CategoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
· 使用定理 `DerivedCategory.instLinearSingleFunctor`：∀ (R : Type t) [inst : Ring R] 
(C : Type u) [inst_1 : CategoryTheory.Category.{v, u} C]   [inst_2 : CategoryThe
ory.Abelian C] [inst_3 : Cate…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_smul`：mk₀_smul (m₀ : M) (hm₀ : m₀ = 0) (r 
: R) {f : X ⟶ Y} : mk₀ m₀ hm₀ (r • f) = r • mk₀ m₀ hm₀ f
· 使用引理 `CategoryTheory.ShiftedHom.comp_smul`：comp_smul [forall (a : M), Functor.
Linear R (shiftFunctor C a)] (r : R) {a b c : M} (α : ShiftedHom X Y a) (β : Shi
ftedHom Y Z b) (h : b + a…
· 使用定理 `DerivedCategory.instLinearShiftFunctorInt`：∀ (R : Type t) [inst : Ring R
] (C : Type u) [inst_1 : CategoryTheory.Category.{v, u} C]   [inst_2 : CategoryT
heory.Abelian C] [inst_3 : Cate…
· 使用引理 `CategoryTheory.ShiftedHom.comp_mk₀_id`：comp_mk₀_id {a : M} (f : ShiftedH
om X Y a) (m₀ : M) (hm₀ : m₀ = 0) : f.comp (mk₀ m₀ hm₀ (𝟙 Y)) (by rw [hm₀, zero_
add]) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_hom (x : Ext X Y n) (r : R) [HasDerivedCategory C] :
    (r • x).hom = r • x.hom := by
  simp [smul_eq_comp_mk₀]

@[simp]
/-
**CategoryTheory.Abelian.Ext.comp_smul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Abelian.Ext`。
形式化陈述：comp_smul {X Y Z : C} {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b) {c : Nat
} (h : a + b = c) (r : R) : α.comp (r • β) h = r • α.comp β h
参数：α : Ext X Y a；β : Ext Y Z b；h : a + b = c；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.Abelian.Ext.smul_hom`：smul_hom (x : Ext X Y n) (r : R) [H
asDerivedCategory C] : (r • x).hom = r • x.hom
· 使用引理 `CategoryTheory.ShiftedHom.comp_smul`：comp_smul [forall (a : M), Functor.
Linear R (shiftFunctor C a)] (r : R) {a b c : M} (α : ShiftedHom X Y a) (β : Shi
ftedHom Y Z b) (h : b + a…
· 使用定理 `DerivedCategory.instLinearShiftFunctorInt`：∀ (R : Type t) [inst : Ring R
] (C : Type u) [inst_1 : CategoryTheory.Category.{v, u} C]   [inst_2 : CategoryT
heory.Abelian C] [inst_3 : Cate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_smul {X Y Z : C} {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b)
    {c : ℕ} (h : a + b = c) (r : R) :
    α.comp (r • β) h = r • α.comp β h := by
  let := HasDerivedCategory.standard C
  aesop

@[simp]
/-
**CategoryTheory.Abelian.Ext.smul_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Abelian.Ext`。
形式化陈述：smul_comp {X Y Z : C} {a b : Nat} (α : Ext X Y a) (β : Ext Y Z b) {c : Nat
} (h : a + b = c) (r : R) : (r • α).comp β h = r • α.comp β h
参数：α : Ext X Y a；β : Ext Y Z b；h : a + b = c；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.Abelian.Ext.smul_hom`：smul_hom (x : Ext X Y n) (r : R) [H
asDerivedCategory C] : (r • x).hom = r • x.hom
· 使用引理 `CategoryTheory.ShiftedHom.smul_comp`：smul_comp (r : R) {a b c : M} (α : 
ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) : (r • α).comp β h = r 
• α.comp β h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_comp {X Y Z : C} {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b)
    {c : ℕ} (h : a + b = c) (r : R) :
    (r • α).comp β h = r • α.comp β h := by
  let := HasDerivedCategory.standard C
  aesop

open DerivedCategory in
/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the `R`-linear
equivalence between `Ext.{w} X Y n` and a type of morphisms in the derived category
of the `R`-linear abelian category `C`. -/
@[simps]
/-
**CategoryTheory.Abelian.Ext.homLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Abelian.Ext`。
形式化陈述：homLinearEquiv [HasDerivedCategory.{w'} C] : Ext X Y n ≃ₗ[R] ShiftedHom ((
singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : Int) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the `R`-
linear
equivalence between `Ext.{w} X Y n` and a type of morphisms in the derived categ
ory
of the `R`-linear abelian category `C`.
-/
noncomputable def homLinearEquiv [HasDerivedCategory.{w'} C] :
    Ext X Y n ≃ₗ[R]
      ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) where
  __ := homAddEquiv
  map_smul' := by simp
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_smul (r : R) (f : X ⟶ Y) : mk₀ (r • f) = r • mk₀ f := by
  let := HasDerivedCategory.standard C
  aesop

/-- The linear equivalence `Ext X Y 0 ≃ₜ[R] (X ⟶ Y)`. -/
@[simps! symm_apply]
/-
**CategoryTheory.Abelian.Ext.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Abelian.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence `Ext X Y 0 ≃ₜ[R] (X ⟶ Y)`.
-/
noncomputable def linearEquiv₀ :
    Ext X Y 0 ≃ₗ[R] (X ⟶ Y) where
  toAddEquiv := addEquiv₀
  map_smul' m x := homEquiv₀.symm.injective (by simp [mk₀_smul])

@[simp]
/-
**CategoryTheory.Abelian.Ext.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Abelia
n.Ext`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_linearEquiv₀_apply (f : Ext X Y 0) :
    mk₀ (linearEquiv₀ (R := R) f) = f :=
  addEquiv₀.left_inv f

end Ring

section CommRing

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The composition of `Ext`, as a bilinear map. -/
@[simps!]
/-
**CategoryTheory.Abelian.Ext.bilinearCompOfLinear** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Abelian.Ext`。
形式化陈述：bilinearCompOfLinear (R : Type t) [CommRing R] [Linear R C] (X Y Z : C) (a
 b c : Nat) (h : a + b = c) : Ext X Y a ->ₗ[R] Ext Y Z b ->ₗ[R] Ext X Z c where 
toFun α
参数：R : Type t；X Y Z : C；a b c : Nat；h : a + b = c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `Ext`, as a bilinear map.
-/
noncomputable def bilinearCompOfLinear (R : Type t) [CommRing R] [Linear R C] (X Y Z : C)
    (a b c : ℕ) (h : a + b = c) :
    Ext X Y a →ₗ[R] Ext Y Z b →ₗ[R] Ext X Z c where
  toFun α :=
    { toFun β := α.comp β h
      map_add' := by simp
      map_smul' := by simp }
  map_add' := by aesop
  map_smul' := by aesop

/-- The postcomposition `Ext X Y a →ₗ[R] Ext X Z b` with `β : Ext Y Z n` when `a + n = b`. -/
/-
**CategoryTheory.Abelian.Ext.postcompOfLinear** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Abelian.Ext`。
形式化陈述：postcompOfLinear {Y Z : C} {n : Nat} (β : Ext Y Z n) (R : Type t) [CommRin
g R] [Linear R C] (X : C) {a b : Nat} (h : a + n = b) : Ext X Y a ->ₗ[R] Ext X Z
 b
参数：β : Ext Y Z n；R : Type t；X : C；h : a + n = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The postcomposition `Ext X Y a →ₗ[R] Ext X Z b` with `β : Ext Y Z n` when `a + n
 = b`.
-/
noncomputable abbrev postcompOfLinear {Y Z : C} {n : ℕ} (β : Ext Y Z n)
    (R : Type t) [CommRing R] [Linear R C] (X : C) {a b : ℕ} (h : a + n = b) :
    Ext X Y a →ₗ[R] Ext X Z b :=
  (bilinearCompOfLinear R X Y Z a n b h).flip β

/-- The precomposition `Ext Y Z a →ₗ[R] Ext X Z b` with `α : Ext X Y n` when `n + a = b`. -/
/-
**CategoryTheory.Abelian.Ext.precompOfLinear** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Abelian.Ext`。
形式化陈述：precompOfLinear {X Y : C} {n : Nat} (α : Ext X Y n) (R : Type t) [CommRing
 R] [Linear R C] (Z : C) {a b : Nat} (h : n + a = b) : Ext Y Z a ->ₗ[R] Ext X Z 
b
参数：α : Ext X Y n；R : Type t；Z : C；h : n + a = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precomposition `Ext Y Z a →ₗ[R] Ext X Z b` with `α : Ext X Y n` when `n + a 
= b`.
-/
noncomputable abbrev precompOfLinear {X Y : C} {n : ℕ} (α : Ext X Y n)
    (R : Type t) [CommRing R] [Linear R C] (Z : C) {a b : ℕ} (h : n + a = b) :
    Ext Y Z a →ₗ[R] Ext X Z b :=
  bilinearCompOfLinear R X Y Z n a b h α

end CommRing

end Ext

end Abelian

end CategoryTheory

