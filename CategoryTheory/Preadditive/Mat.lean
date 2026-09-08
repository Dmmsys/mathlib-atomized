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

/-- An object in `Mat_ C` is a finite tuple of objects in `C`.
-/
/-
**CategoryTheory.Mat_** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：Type u₁ → Type (max 1 u₁)
参数：max 1 u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object in `Mat_ C` is a finite tuple of objects in `C`.
-/
structure Mat_ where
  /-- The index type `ι` -/
  ι : Type
  [fintype : Fintype ι]
  /-- The map from `ι` to objects in `C` -/
  X : ι → C

attribute [instance] Mat_.fintype

namespace Mat_

variable {C}

/-- A morphism in `Mat_ C` is a dependently typed matrix of morphisms. -/
/-
**CategoryTheory.Mat_.Hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：Hom (M N : Mat_ C) : Type v₁
参数：M N : Mat_ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `Mat_ C` is a dependently typed matrix of morphisms.
-/
def Hom (M N : Mat_ C) : Type v₁ :=
  DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j

namespace Hom

open scoped Classical in
/-- The identity matrix consists of identity morphisms on the diagonal, and zeros elsewhere. -/
/-
**CategoryTheory.Mat_.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mat_.Hom`
。
形式化陈述：id (M : Mat_ C) : Hom M M
参数：M : Mat_ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity matrix consists of identity morphisms on the diagonal, and zeros el
sewhere.
-/
def id (M : Mat_ C) : Hom M M := fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0

/-- Composition of matrices using matrix multiplication. -/
/-
**CategoryTheory.Mat_.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mat_.Ho
m`。
形式化陈述：comp {M N K : Mat_ C} (f : Hom M N) (g : Hom N K) : Hom M K
参数：f : Hom M N；g : Hom N K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of matrices using matrix multiplication.
-/
def comp {M N K : Mat_ C} (f : Hom M N) (g : Hom N K) : Hom M K := fun i k =>
  ∑ j : N.ι, f i j ≫ g j k

end Hom

section

attribute [local simp] Hom.id Hom.comp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Mat_.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat_`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Mat_.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：hom_ext {M N : Mat_ C} (f g : M ⟶ N) (H : forall i j, f i j = g i j) : f =
 g
参数：f g : M ⟶ N；H : forall i j, f i j = g i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DMatrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem hom_ext {M N : Mat_ C} (f g : M ⟶ N) (H : ∀ i j, f i j = g i j) : f = g :=
  DMatrix.ext_iff.mp H

open scoped Classical in
/-
**CategoryTheory.Mat_.id_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：id_def (M : Mat_ C) : (𝟙 M : Hom M M) = fun i j => if h : i = j then eqToH
om (congr_arg M.X h) else 0
参数：M : Mat_ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_def (M : Mat_ C) :
    (𝟙 M : Hom M M) = fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0 :=
  rfl

open scoped Classical in
/-
**CategoryTheory.Mat_.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：id_apply (M : Mat_ C) (i j : M.ι) : (𝟙 M : Hom M M) i j = if h : i = j the
n eqToHom (congr_arg M.X h) else 0
参数：M : Mat_ C；i j : M.ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (M : Mat_ C) (i j : M.ι) :
    (𝟙 M : Hom M M) i j = if h : i = j then eqToHom (congr_arg M.X h) else 0 :=
  rfl

@[simp]
/-
**CategoryTheory.Mat_.id_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ma
t_`。
形式化陈述：id_apply_self (M : Mat_ C) (i : M.ι) : (𝟙 M : Hom M M) i i = 𝟙 _
参数：M : Mat_ C；i : M.ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_apply_self (M : Mat_ C) (i : M.ι) : (𝟙 M : Hom M M) i i = 𝟙 _ := by simp [id_apply]

@[simp]
/-
**CategoryTheory.Mat_.id_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.M
at_`。
形式化陈述：id_apply_of_ne (M : Mat_ C) (i j : M.ι) (h : i != j) : (𝟙 M : Hom M M) i j
 = 0
参数：M : Mat_ C；i j : M.ι；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_apply_of_ne (M : Mat_ C) (i j : M.ι) (h : i ≠ j) : (𝟙 M : Hom M M) i j = 0 := by
  simp [id_apply, h]
/-
**CategoryTheory.Mat_.comp_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：comp_def {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) : f ≫ g = fun i k => ∑ j
 : N.ι, f i j ≫ g j k
参数：f : M ⟶ N；g : N ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_def {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N.ι, f i j ≫ g j k :=
  rfl

@[simp]
/-
**CategoryTheory.Mat_.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat_`
。
形式化陈述：comp_apply {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) : (f ≫ g) i k = 
∑ j : N.ι, f i j ≫ g j k
参数：f : M ⟶ N；g : N ⟶ K；i k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k :=
  rfl
/-
**CategoryTheory.Mat_.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat_`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M N : Mat_ C) : Inhabited (M ⟶ N) :=
  ⟨fun i j => (0 : M.X i ⟶ N.X j)⟩

end

/-
**CategoryTheory.Mat_.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat_`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M N : Mat_ C) : AddCommGroup (M ⟶ N) :=
  inferInstanceAs <| AddCommGroup (DMatrix M.ι N.ι _)

@[simp]
/-
**CategoryTheory.Mat_.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j
参数：f g : M ⟶ N；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
  rfl
/-
**CategoryTheory.Mat_.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat_`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (Mat_ C) where
  add_comp M N K f f' g := by ext; simp [Finset.sum_add_distrib]
  comp_add M N K f g g' := by ext; simp [Finset.sum_add_distrib]

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- We now prove that `Mat_ C` has finite biproducts.

Be warned, however, that `Mat_ C` is not necessarily Krull-Schmidt,
and so the internal indexing of a biproduct may have nothing to do with the external indexing,
even though the construction we give uses a sigma type.
See however `isoBiproductEmbedding`.
-/
/-
**CategoryTheory.Mat_.hasFiniteBiproducts** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Mat_`。
形式化陈述：hasFiniteBiproducts : HasFiniteBiproducts (Mat_ C) where out n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasBiproduct_of_total`：hasBiproduct_of_total {f : 
J -> C} (b : Bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) : HasBiproduct 
f
· 使用定理 `CategoryTheory.Mat_.hom_ext`：hom_ext {M N : Mat_ C} (f g : M ⟶ N) (H : f
orall i j, f i j = g i j) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.dite_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {P : Prop} [inst_1 : Decidable P] {X Y Z : C} (g : P → (Z ⟶ Y))   (g'
 : ¬P → (Z ⟶ Y…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_sigma_univ`：∀ {ι : Type u_1} {κ : ι → Type u_3} [inst : (i :
 ι) → Fintype (κ i)] [inst_1 : Fintype ι],   (Finset.univ.sigma fun x => Finset.
univ) = Fins…
· 使用定理 `Finset.sum_sigma`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid 
β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : Sigma σ
 → β),…
· 使用定理 `Finset.sum_dite_irrel`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] (p : Prop) [inst_1 : Decidable p] (s : Finset ι)   (f : p → ι → M) (g : 
¬p → ι → M)…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Mat_.id_apply_self`：id_apply_self (M : Mat_ C) (i : M.ι) 
: (𝟙 M : Hom M M) i i = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Mat_.id_apply_of_ne`：id_apply_of_ne (M : Mat_ C) (i j : M
.ι) (h : i != j) : (𝟙 M : Hom M M) i j = 0
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
We now prove that `Mat_ C` has finite biproducts.

Be warned, however, that `Mat_ C` is not necessarily Krull-Schmidt,
and so the internal indexing of a biproduct may have nothing to do with the exte
rnal indexing,
even though the construction we give uses a sigma type.
See however `isoBiproductEmbedding`.
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
              rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
              dsimp +instances
              simp only [if_true, Finset.sum_dite_irrel, Finset.mem_univ,
                Finset.sum_const_zero, Finset.sum_dite_eq']
              split_ifs with h h'
              · subst h h'
                simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Mat_.id_apply_self]
              · subst h
                rw [eqToHom_refl, id_apply_of_ne _ _ _ h']
              · rfl }
          (by
            dsimp
            ext1 ⟨i, j⟩
            rintro ⟨i', j'⟩
            rw [Finset.sum_apply, Finset.sum_apply]
            dsimp
            rw [Finset.sum_eq_single i]; rotate_left
            · intro b _ hb
              apply Finset.sum_eq_zero
              intro x _
              rw [dif_neg hb.symm, zero_comp]
            · intro hi
              simp at hi
            rw [Finset.sum_eq_single j]; rotate_left
            · intro b _ hb
              rw [dif_pos rfl, dif_neg, zero_comp]
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
/-
**CategoryTheory.Functor.mapMat_** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：mapMat_ (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ Mat_ D where obj M
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor induces a functor of matrix categories.
-/
def mapMat_ (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ Mat_ D where
  obj M := ⟨M.ι, fun i => F.obj (M.X i)⟩
  map f i j := F.map (f i j)

set_option backward.isDefEq.respectTransparency false in
/-- The identity functor induces the identity functor on matrix categories.
-/
@[simps!]
/-
**CategoryTheory.Functor.mapMatId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：mapMatId : (𝟭 C).mapMat_ ≅ 𝟭 (Mat_ C)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instAdditiveId`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C],   (Catego
ryTheory.Functor.id C).Addi…

--- 原说明 ---
The identity functor induces the identity functor on matrix categories.
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
/-
**CategoryTheory.Functor.mapMatComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：mapMatComp {E : Type*} [Category.{v₁} E] [Preadditive E] (F : C ⥤ D) [Func
tor.Additive F] (G : D ⥤ E) [Functor.Additive G] : (F ⋙ G).mapMat_ ≅ F.mapMat_ ⋙
 G.mapMat_
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instAdditiveComp`：∀ {C : Type u_1} {D : Type u_2}
 [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
Composite functors induce composite functors on matrix categories.
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
/-
**CategoryTheory.Mat_.embedding** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：embedding : C ⥤ Mat_ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of `C` into `Mat_ C` as one-by-one matrices.
(We index the summands by `PUnit`.)
-/
def embedding : C ⥤ Mat_ C where
  obj X := ⟨PUnit, fun _ => X⟩
  map f _ _ := f
  map_id _ := by ext ⟨⟩; simp
  map_comp _ _ := by ext ⟨⟩; simp

namespace Embedding

/-
**CategoryTheory.Mat_.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat_.
Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (embedding C).Faithful where
  map_injective h := congr_fun (congr_fun h PUnit.unit) PUnit.unit
/-
**CategoryTheory.Mat_.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat_.
Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (embedding C).Full where map_surjective f := ⟨f PUnit.unit PUnit.unit, rfl⟩
/-
**CategoryTheory.Mat_.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat_.
Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Additive (embedding C) where

end Embedding

/-
**CategoryTheory.Mat_.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat_`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Mat_.isoBiproductEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Mat_`。
形式化陈述：isoBiproductEmbedding (M : Mat_ C) : M ≅ ⨁ fun i => (embedding C).obj (M.X
 i) where hom
参数：M : Mat_ C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every object in `Mat_ C` is isomorphic to the biproduct of its summands.
-/
def isoBiproductEmbedding (M : Mat_ C) : M ≅ ⨁ fun i => (embedding C).obj (M.X i) where
  hom := biproduct.lift fun i j _ => if h : j = i then eqToHom (congr_arg M.X h) else 0
  inv := biproduct.desc fun i _ k => if h : i = k then eqToHom (congr_arg M.X h) else 0
  hom_inv_id := by
    simp only [biproduct.lift_desc]
    funext i j
    dsimp [id_def]
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single i]; rotate_left
    · intro b _ hb
      dsimp
      rw [Fintype.univ_ofSubsingleton, Finset.sum_singleton, dif_neg hb.symm, zero_comp]
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
/-
**CategoryTheory.Mat_.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat_`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance can be found using `Functor.hasBiproduct_of_preserves'`, but it is
 faster
to keep it here.
-/
instance (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) :
    HasBiproduct (fun i => F.obj ((embedding C).obj (M.X i))) :=
  F.hasBiproduct_of_preserves _

/-- Every `M` is a direct sum of objects from `C`, and `F` preserves biproducts. -/
/-
**CategoryTheory.Mat_.additiveObjIsoBiproduct** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Mat_`。
形式化陈述：additiveObjIsoBiproduct (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C)
 : F.obj M ≅ ⨁ fun i => F.obj ((embedding C).obj (M.X i))
参数：F : Mat_ C ⥤ D；M : Mat_ C。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mat_.instHasBiproductιObjEmbeddingXOfAdditive`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Pread
ditive C] {D : Type u₁}   [inst_2 : CategoryTheory…

--- 原说明 ---
Every `M` is a direct sum of objects from `C`, and `F` preserves biproducts.
-/
def additiveObjIsoBiproduct (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) :
    F.obj M ≅ ⨁ fun i => F.obj ((embedding C).obj (M.X i)) :=
  F.mapIso (isoBiproductEmbedding M) ≪≫ F.mapBiproduct _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Mat_.additiveObjIsoBiproduct_hom_** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Mat_`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma additiveObjIsoBiproduct_hom_π (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι) :
    (additiveObjIsoBiproduct F M).hom ≫ biproduct.π _ i =
      F.map (M.isoBiproductEmbedding.hom ≫ biproduct.π _ i) := by
  dsimp [additiveObjIsoBiproduct]
  rw [biproduct.lift_π, Category.assoc]
  erw [biproduct.lift_π, ← F.map_comp]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Mat_.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mat_`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_additiveObjIsoBiproduct_inv (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι) :
    biproduct.ι _ i ≫ (additiveObjIsoBiproduct F M).inv =
      F.map (biproduct.ι _ i ≫ M.isoBiproductEmbedding.inv) := by
  dsimp [additiveObjIsoBiproduct, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, ← F.map_comp]

variable [HasFiniteBiproducts D]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Mat_.additiveObjIsoBiproduct_naturality** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Mat_`。
形式化陈述：additiveObjIsoBiproduct_naturality (F : Mat_ C ⥤ D) [Functor.Additive F] {
M N : Mat_ C} (f : M ⟶ N) : F.map f ≫ (additiveObjIsoBiproduct F N).hom = (addit
iveObjIsoBiproduct F M).hom ≫ biproduct.matrix fun i j => F.map ((embedding C).m
ap (f i j))
参数：F : Mat_ C ⥤ D；f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Mat_.instHasBiproductιObjEmbeddingXOfAdditive`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Pread
ditive C] {D : Type u₁}   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Mat_.additiveObjIsoBiproduct_hom_π`：additiveObjIsoBiprodu
ct_hom_π (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι) : (additiv
eObjIsoBiproduct F M).hom ≫ biproduct.π…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Mat_.isoBiproductEmbedding_hom`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Preadditive C]   (M 
: CategoryTheory.Mat_ C),   M.isoBi…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.matrix_π`：∀ {J : Type} [inst : Finite J]
 {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.Category.{
v, u} C]   [inst_3 : CategoryT…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Mat_.ι_additiveObjIsoBiproduct_inv_assoc`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Preadditiv
e C] {D : Type u₁}   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Mat_.isoBiproductEmbedding_inv`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Preadditive C]   (M 
: CategoryTheory.Mat_ C),   M.isoBi…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
（共 41 条，此处仅展示前 30 条）
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
/-
**CategoryTheory.Mat_.additiveObjIsoBiproduct_naturality'** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Mat_`。
形式化陈述：additiveObjIsoBiproduct_naturality' (F : Mat_ C ⥤ D) [Functor.Additive F] 
{M N : Mat_ C} (f : M ⟶ N) : (additiveObjIsoBiproduct F M).inv ≫ F.map f = bipro
duct.matrix (fun i j => F.map ((embedding C).map (f i j)) :) ≫ (additiveObjIsoBi
product F N).inv
参数：F : Mat_ C ⥤ D；f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mat_.instHasBiproductιObjEmbeddingXOfAdditive`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Pread
ditive C] {D : Type u₁}   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Mat_.additiveObjIsoBiproduct_naturality`：additiveObjIsoBi
product_naturality (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C} (f : M ⟶
 N) : F.map f ≫ (additiveObjIsoBiproduct F N…
-/
theorem additiveObjIsoBiproduct_naturality' (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C}
    (f : M ⟶ N) :
    (additiveObjIsoBiproduct F M).inv ≫ F.map f =
      biproduct.matrix (fun i j => F.map ((embedding C).map (f i j)) :) ≫
        (additiveObjIsoBiproduct F N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, additiveObjIsoBiproduct_naturality]

attribute [local simp] biproduct.lift_desc

/-- Any additive functor `C ⥤ D` to a category `D` with finite biproducts extends to
a functor `Mat_ C ⥤ D`. -/
@[simps]
/-
**CategoryTheory.Mat_.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：lift (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ D where obj X
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any additive functor `C ⥤ D` to a category `D` with finite biproducts extends to
a functor `Mat_ C ⥤ D`.
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
/-
**CategoryTheory.Mat_.lift_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ma
t_`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Preadditive C] {D : Type u₁}   [inst_2 : CategoryTheory.Category.{v₁,
 u₁} D] [inst_3 : CategoryTheory.Preadditive D]   [inst_4 : CategoryTheory.Limit
s.HasFiniteBiproducts D] (F : CategoryTheory.Functor C D) [inst_5 : F.Additive],
   (CategoryTheory.Mat_.lift F).Additive
参数：F : CategoryTheory.Functor C D；CategoryTheory.Mat_.lift F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biproduct.matrix_π`：∀ {J : Type} [inst : Finite J]
 {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.Category.{
v, u} C]   [inst_3 : CategoryT…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance lift_additive (F : C ⥤ D) [Functor.Additive F] : Functor.Additive (lift F) where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An additive functor `C ⥤ D` factors through its lift to `Mat_ C ⥤ D`. -/
@[simps!]
/-
**CategoryTheory.Mat_.embeddingLiftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Mat_`。
形式化陈述：embeddingLiftIso (F : C ⥤ D) [Functor.Additive F] : embedding C ⋙ lift F ≅
 F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive functor `C ⥤ D` factors through its lift to `Mat_ C ⥤ D`.
-/
def embeddingLiftIso (F : C ⥤ D) [Functor.Additive F] : embedding C ⋙ lift F ≅ F :=
  NatIso.ofComponents
    (fun X =>
      { hom := biproduct.desc fun _ => 𝟙 (F.obj X)
        inv := biproduct.lift fun _ => 𝟙 (F.obj X) })

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `Mat_.lift F` is the unique additive functor `L : Mat_ C ⥤ D` such that `F ≅ embedding C ⋙ L`.
-/
/-
**CategoryTheory.Mat_.liftUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mat_`
。
形式化陈述：liftUnique (F : C ⥤ D) [Functor.Additive F] (L : Mat_ C ⥤ D) [Functor.Addi
tive L] (α : embedding C ⋙ L ≅ F) : L ≅ lift F
参数：F : C ⥤ D；L : Mat_ C ⥤ D；α : embedding C ⋙ L ≅ F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mat_.instHasBiproductιObjEmbeddingXOfAdditive`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Pread
ditive C] {D : Type u₁}   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Mat_.lift_additive`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Preadditive C] {D : Type u₁}   [
inst_2 : CategoryTheory…

--- 原说明 ---
`Mat_.lift F` is the unique additive functor `L : Mat_ C ⥤ D` such that `F ≅ emb
edding C ⋙ L`.
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
/-- Two additive functors `Mat_ C ⥤ D` are naturally isomorphic if
their precompositions with `embedding C` are naturally isomorphic as functors `C ⥤ D`. -/
/-
**CategoryTheory.Mat_.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：ext {F G : Mat_ C ⥤ D} [Functor.Additive F] [Functor.Additive G] (α : embe
dding C ⋙ F ≅ embedding C ⋙ G) : F ≅ G
参数：α : embedding C ⋙ F ≅ embedding C ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two additive functors `Mat_ C ⥤ D` are naturally isomorphic if
their precompositions with `embedding C` are naturally isomorphic as functors `C
 ⥤ D`.
-/
def ext {F G : Mat_ C ⥤ D} [Functor.Additive F] [Functor.Additive G]
    (α : embedding C ⋙ F ≅ embedding C ⋙ G) : F ≅ G :=
  liftUnique (embedding C ⋙ G) _ α ≪≫ (liftUnique _ _ (Iso.refl _)).symm

/-- Natural isomorphism needed in the construction of `equivalenceSelfOfHasFiniteBiproducts`.
-/
/-
**CategoryTheory.Mat_.equivalenceSelfOfHasFiniteBiproductsAux** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：equivalenceSelfOfHasFiniteBiproductsAux [HasFiniteBiproducts C] : embeddin
g C ⋙ 𝟭 (Mat_ C) ≅ embedding C ⋙ lift (𝟭 C) ⋙ embedding C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instAdditiveId`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C],   (Catego
ryTheory.Functor.id C).Addi…

--- 原说明 ---
Natural isomorphism needed in the construction of `equivalenceSelfOfHasFiniteBip
roducts`.
-/
def equivalenceSelfOfHasFiniteBiproductsAux [HasFiniteBiproducts C] :
    embedding C ⋙ 𝟭 (Mat_ C) ≅ embedding C ⋙ lift (𝟭 C) ⋙ embedding C :=
  Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (embeddingLiftIso _).symm _ ≪≫ Functor.associator _ _ _

/--
A preadditive category that already has finite biproducts is equivalent to its additive envelope.

Note that we only prove this for a large category;
otherwise there are universe issues that I haven't attempted to sort out.
-/
/-
**CategoryTheory.Mat_.equivalenceSelfOfHasFiniteBiproducts** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Mat_`。
形式化陈述：equivalenceSelfOfHasFiniteBiproducts (C : Type (u₁ + 1)) [LargeCategory C]
 [Preadditive C] [HasFiniteBiproducts C] : Mat_ C ≌ C
参数：C : Type (u₁ + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instAdditiveId`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C],   (Catego
ryTheory.Functor.id C).Addi…

--- 原说明 ---
A preadditive category that already has finite biproducts is equivalent to its a
dditive envelope.

Note that we only prove this for a large category;
otherwise there are universe issues that I haven't attempted to sort out.
-/
def equivalenceSelfOfHasFiniteBiproducts (C : Type (u₁ + 1)) [LargeCategory C] [Preadditive C]
    [HasFiniteBiproducts C] : Mat_ C ≌ C :=
  Equivalence.mk
    (-- I suspect this is already an adjoint equivalence, but it seems painful to verify.
      lift
      (𝟭 C))
    (embedding C) (ext equivalenceSelfOfHasFiniteBiproductsAux) (embeddingLiftIso (𝟭 C))

@[simp]
/-
**CategoryTheory.Mat_.equivalenceSelfOfHasFiniteBiproducts_functor** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：equivalenceSelfOfHasFiniteBiproducts_functor {C : Type (u₁ + 1)} [LargeCat
egory C] [Preadditive C] [HasFiniteBiproducts C] : (equivalenceSelfOfHasFiniteBi
products C).functor = lift (𝟭 C)
参数：u₁ + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivalenceSelfOfHasFiniteBiproducts_functor {C : Type (u₁ + 1)} [LargeCategory C]
    [Preadditive C] [HasFiniteBiproducts C] :
    (equivalenceSelfOfHasFiniteBiproducts C).functor = lift (𝟭 C) :=
  rfl

@[simp]
/-
**CategoryTheory.Mat_.equivalenceSelfOfHasFiniteBiproducts_inverse** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Mat_`。
形式化陈述：equivalenceSelfOfHasFiniteBiproducts_inverse {C : Type (u₁ + 1)} [LargeCat
egory C] [Preadditive C] [HasFiniteBiproducts C] : (equivalenceSelfOfHasFiniteBi
products C).inverse = embedding C
参数：u₁ + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Mat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Mat (_ : Type u)
参数：_ : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `Fintype`, which we will equip with a category structure
where the morphisms are matrices with components in `R`.
-/
def Mat (_ : Type u) :=
  FintypeCat.{u}
deriving Inhabited
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type u) : CoeSort (Mat R) (Type u) :=
  FintypeCat.instCoeSort

open Matrix

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] FintypeCat.fintype in
open scoped Classical in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type u) [Semiring R] : Category (Mat R) where
  Hom X Y := Matrix X Y R
  id X := (1 : Matrix X X R)
  comp {X Y Z} f g := (show Matrix X Y R from f) * (show Matrix Y Z R from g)
  assoc := by intros; simp [Matrix.mul_assoc]

namespace Mat

section

variable {R : Type u} [Semiring R]

@[ext]
/-
**CategoryTheory.Mat.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat`。
形式化陈述：hom_ext {X Y : Mat R} (f g : X ⟶ Y) (h : forall i j, f i j = g i j) : f = 
g
参数：f g : X ⟶ Y；h : forall i j, f i j = g i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem hom_ext {X Y : Mat R} (f g : X ⟶ Y) (h : ∀ i j, f i j = g i j) : f = g :=
  Matrix.ext_iff.mp h

variable (R)

open scoped Classical in
/-
**CategoryTheory.Mat.id_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat`。
形式化陈述：id_def (M : Mat R) : 𝟙 M = fun i j => if i = j then 1 else 0
参数：M : Mat R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_def (M : Mat R) : 𝟙 M = fun i j => if i = j then 1 else 0 :=
  rfl

open scoped Classical in
/-
**CategoryTheory.Mat.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat`。
形式化陈述：id_apply (M : Mat R) (i j : M) : (𝟙 M : Matrix M M R) i j = if i = j then 
1 else 0
参数：M : Mat R；i j : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (M : Mat R) (i j : M) : (𝟙 M : Matrix M M R) i j = if i = j then 1 else 0 :=
  rfl

@[simp]
/-
**CategoryTheory.Mat.id_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat
`。
形式化陈述：id_apply_self (M : Mat R) (i : M) : (𝟙 M : Matrix M M R) i i = 1
参数：M : Mat R；i : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_apply_self (M : Mat R) (i : M) : (𝟙 M : Matrix M M R) i i = 1 := by simp [id_apply]

@[simp]
/-
**CategoryTheory.Mat.id_apply_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ma
t`。
形式化陈述：id_apply_of_ne (M : Mat R) (i j : M) (h : i != j) : (𝟙 M : Matrix M M R) i
 j = 0
参数：M : Mat R；i j : M；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_apply_of_ne (M : Mat R) (i j : M) (h : i ≠ j) : (𝟙 M : Matrix M M R) i j = 0 := by
  simp [id_apply, h]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] FintypeCat.fintype in
/-
**CategoryTheory.Mat.comp_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat`。
形式化陈述：comp_def {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) : f ≫ g = fun i k => ∑ j 
: N, f i j * g j k
参数：f : M ⟶ N；g : N ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_def {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N, f i j * g j k :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] FintypeCat.fintype in
@[simp]
/-
**CategoryTheory.Mat.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat`。
形式化陈述：comp_apply {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) (i k) : (f ≫ g) i k = ∑
 j : N, f i j * g j k
参数：f : M ⟶ N；g : N ⟶ K；i k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N, f i j * g j k :=
  rfl
/-
**CategoryTheory.Mat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M N : Mat R) : Inhabited (M ⟶ N) :=
  ⟨fun (_ : M) (_ : N) => (0 : R)⟩

end

variable (R : Type) [Ring R]

open Opposite

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `CategoryTheory.Mat.equivalenceSingleObj`. -/
@[simps]
/-
**CategoryTheory.Mat.equivalenceSingleObjInverse** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Mat`。
形式化陈述：equivalenceSingleObjInverse : Mat_ (SingleObj Rᵐᵒᵖ) ⥤ Mat R where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `CategoryTheory.Mat.equivalenceSingleObj`.
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
/-
**CategoryTheory.Mat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (equivalenceSingleObjInverse R).Faithful where
  map_injective w := by
    ext
    apply_fun MulOpposite.unop using MulOpposite.unop_injective
    exact congr_fun (congr_fun w _) _
/-
**CategoryTheory.Mat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (equivalenceSingleObjInverse R).Full where
  map_surjective f := ⟨fun i j => MulOpposite.op (f i j), rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] FintypeCat.fintype in
/-
**CategoryTheory.Mat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (equivalenceSingleObjInverse R).EssSurj where
  mem_essImage X :=
    ⟨{  ι := X
        X := fun _ => PUnit.unit }, ⟨eqToIso (by cases X; congr)⟩⟩
/-
**CategoryTheory.Mat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (equivalenceSingleObjInverse R).IsEquivalence where

/-- The categorical equivalence between the category of matrices over a ring,
and the category of matrices over that ring considered as a single-object category. -/
/-
**CategoryTheory.Mat.equivalenceSingleObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Mat`。
形式化陈述：equivalenceSingleObj : Mat R ≌ Mat_ (SingleObj Rᵐᵒᵖ)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Mat.instIsEquivalenceMat_SingleObjMulOppositeEquivalenceS
ingleObjInverse`：∀ (R : Type) [inst : Ring R], (CategoryTheory.Mat.equivalenceSi
ngleObjInverse R).IsEquivalence

--- 原说明 ---
The categorical equivalence between the category of matrices over a ring,
and the category of matrices over that ring considered as a single-object catego
ry.
-/
def equivalenceSingleObj : Mat R ≌ Mat_ (SingleObj Rᵐᵒᵖ) :=
  (equivalenceSingleObjInverse R).asEquivalence.symm
/-
**CategoryTheory.Mat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : Mat R) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs <| AddCommGroup (Matrix X Y R)

variable {R}

@[simp]
/-
**CategoryTheory.Mat.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mat`。
形式化陈述：add_apply {M N : Mat R} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j
参数：f g : M ⟶ N；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply {M N : Mat R} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
  rfl

attribute [local simp] add_mul mul_add Finset.sum_add_distrib
/-
**CategoryTheory.Mat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (Mat R) where

-- TODO show `Mat R` has biproducts, and that `biprod.map` "is" forming a block diagonal matrix.
end Mat

end CategoryTheory

