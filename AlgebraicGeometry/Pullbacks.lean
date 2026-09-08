/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Fibred products of schemes

In this file we construct the fibred product of schemes via gluing.
We roughly follow [har77] Theorem 3.3.

In particular, the main construction is to show that for an open cover `{ Uᵢ }` of `X`, if there
exist fibred products `Uᵢ ×[Z] Y` for each `i`, then there exists a fibred product `X ×[Z] Y`.

Then, for constructing the fibred product for arbitrary schemes `X, Y, Z`, we can use the
construction to reduce to the case where `X, Y, Z` are all affine, where fibred products are
constructed via tensor products.

-/

@[expose] public section


universe u v w

noncomputable section

open CategoryTheory Functor CartesianMonoidalCategory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

namespace Pullback

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover.{u} X) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ i, HasPullback (𝒰.f i ≫ f) g]

/-- The intersection of `Uᵢ ×[Z] Y` and `Uⱼ ×[Z] Y` is given by (Uᵢ ×[Z] Y) ×[X] Uⱼ -/
@[instance_reducible]
/-
**AlgebraicGeometry.Scheme.Pullback.v** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme.Pullback`。
形式化陈述：v (i j : 𝒰.I₀) : Scheme
参数：i j : 𝒰.I₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intersection of `Uᵢ ×[Z] Y` and `Uⱼ ×[Z] Y` is given by (Uᵢ ×[Z] Y) ×[X] Uⱼ
-/
def v (i j : 𝒰.I₀) : Scheme :=
  pullback ((pullback.fst (𝒰.f i ≫ f) g) ≫ 𝒰.f i) (𝒰.f j)

/-- The canonical transition map `(Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ` given by the fact
that pullbacks are associative and symmetric. -/
/-
**AlgebraicGeometry.Scheme.Pullback.t** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme.Pullback`。
形式化陈述：t (i j : 𝒰.I₀) : v 𝒰 f g i j ⟶ v 𝒰 f g j i
参数：i j : 𝒰.I₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical transition map `(Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ` given b
y the fact
that pullbacks are associative and symmetric.
-/
def t (i j : 𝒰.I₀) : v 𝒰 f g i j ⟶ v 𝒰 f g j i := by
  have : HasPullback (pullback.snd _ _ ≫ 𝒰.f i ≫ f) g :=
    hasPullback_assoc_symm (𝒰.f j) (𝒰.f i) (𝒰.f i ≫ f) g
  have : HasPullback (pullback.snd _ _ ≫ 𝒰.f j ≫ f) g :=
    hasPullback_assoc_symm (𝒰.f i) (𝒰.f j) (𝒰.f j ≫ f) g
  refine (pullbackSymmetry ..).hom ≫ (pullbackAssoc ..).inv ≫ ?_
  refine ?_ ≫ (pullbackAssoc ..).hom ≫ (pullbackSymmetry ..).hom
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · rw [pullbackSymmetry_hom_comp_snd_assoc, pullback.condition_assoc, Category.comp_id]
  · rw [Category.comp_id, Category.id_comp]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t_fst_fst** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.Pullback`。
形式化陈述：t_fst_fst (i j : 𝒰.I₀) : t 𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.fst _ _
 = pullback.snd _ _
参数：i j : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_hom_snd_fst`：pullbackAssoc_hom_snd_f
st [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd`：pullbackSymmetry_ho
m_comp_snd [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.snd g f = p
ullback.fst f g
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_fst_fst`：pullbackAssoc_inv_fst_f
st [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t_fst_fst (i j : 𝒰.I₀) : t 𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
    pullback.snd _ _ := by
  simp only [t, Category.assoc, pullbackSymmetry_hom_comp_fst_assoc, pullbackAssoc_hom_snd_fst,
    pullback.lift_fst_assoc, pullbackSymmetry_hom_comp_snd, pullbackAssoc_inv_fst_fst,
    pullbackSymmetry_hom_comp_fst]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.Pullback`。
形式化陈述：t_fst_snd (i j : 𝒰.I₀) : t 𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.snd _ _
 = pullback.fst _ _ ≫ pullback.snd _ _
参数：i j : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_hom_snd_snd`：pullbackAssoc_hom_snd_s
nd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_snd`：pullbackAssoc_inv_snd [HasP
ullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullback.fst _
 _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackA…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t_fst_snd (i j : 𝒰.I₀) :
    t 𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t, Category.assoc, pullbackSymmetry_hom_comp_fst_assoc, pullbackAssoc_hom_snd_snd,
    pullback.lift_snd, Category.comp_id, pullbackAssoc_inv_snd, pullbackSymmetry_hom_comp_snd_assoc]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t_snd** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Pullback`。
形式化陈述：t_snd (i j : 𝒰.I₀) : t 𝒰 f g i j ≫ pullback.snd _ _ = pullback.fst _ _ ≫ p
ullback.fst _ _
参数：i j : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd`：pullbackSymmetry_ho
m_comp_snd [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.snd g f = p
ullback.fst f g
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_hom_fst`：pullbackAssoc_hom_fst [HasP
ullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullback.fst _
 _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackA…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_fst_snd`：pullbackAssoc_inv_fst_s
nd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t_snd (i j : 𝒰.I₀) : t 𝒰 f g i j ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [t, Category.assoc, pullbackSymmetry_hom_comp_snd, pullbackAssoc_hom_fst,
    pullback.lift_fst_assoc, pullbackSymmetry_hom_comp_fst, pullbackAssoc_inv_fst_snd,
    pullbackSymmetry_hom_comp_snd_assoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme.Pullback`。
形式化陈述：t_id (i : 𝒰.I₀) : t 𝒰 f g i i = 𝟙 _
参数：i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t_fst_fst`：t_fst_fst (i j : 𝒰.I₀) : t 
𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.snd _ _
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t_fst_snd`：t_fst_snd (i j : 𝒰.I₀) : t 
𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.sn
d _ _
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t_snd`：t_snd (i j : 𝒰.I₀) : t 𝒰 f g i 
j ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.fst _ _
-/
theorem t_id (i : 𝒰.I₀) : t 𝒰 f g i i = 𝟙 _ := by
  apply pullback.hom_ext <;> rw [Category.id_comp]
  · apply pullback.hom_ext
    · rw [← cancel_mono (𝒰.f i)]; simp only [pullback.condition, Category.assoc, t_fst_fst]
    · simp only [Category.assoc, t_fst_snd]
  · rw [← cancel_mono (𝒰.f i)]; simp only [pullback.condition, t_snd, Category.assoc]

/-- The inclusion map of `V i j = (Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ Uᵢ ×[Z] Y` -/
/-
**AlgebraicGeometry.Scheme.Pullback.fV** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeo
metry.Scheme.Pullback`。
形式化陈述：fV (i j : 𝒰.I₀) : v 𝒰 f g i j ⟶ pullback (𝒰.f i ≫ f) g
参数：i j : 𝒰.I₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map of `V i j = (Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ Uᵢ ×[Z] Y`
-/
abbrev fV (i j : 𝒰.I₀) : v 𝒰 f g i j ⟶ pullback (𝒰.f i ≫ f) g :=
  pullback.fst _ _

/-- The map `((Xᵢ ×[Z] Y) ×[X] Xⱼ) ×[Xᵢ ×[Z] Y] ((Xᵢ ×[Z] Y) ×[X] Xₖ)` ⟶
`((Xⱼ ×[Z] Y) ×[X] Xₖ) ×[Xⱼ ×[Z] Y] ((Xⱼ ×[Z] Y) ×[X] Xᵢ)` needed for gluing -/
/-
**AlgebraicGeometry.Scheme.Pullback.t'** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Pullback`。
形式化陈述：t' (i j k : 𝒰.I₀) : pullback (fV 𝒰 f g i j) (fV 𝒰 f g i k) ⟶ pullback (fV 
𝒰 f g j k) (fV 𝒰 f g j i)
参数：i j k : 𝒰.I₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `((Xᵢ ×[Z] Y) ×[X] Xⱼ) ×[Xᵢ ×[Z] Y] ((Xᵢ ×[Z] Y) ×[X] Xₖ)` ⟶
`((Xⱼ ×[Z] Y) ×[X] Xₖ) ×[Xⱼ ×[Z] Y] ((Xⱼ ×[Z] Y) ×[X] Xᵢ)` needed for gluing
-/
def t' (i j k : 𝒰.I₀) :
    pullback (fV 𝒰 f g i j) (fV 𝒰 f g i k) ⟶ pullback (fV 𝒰 f g j k) (fV 𝒰 f g j i) := by
  refine (pullbackRightPullbackFstIso ..).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso ..).inv
  refine pullback.map _ _ _ _ (t 𝒰 f g i j) (𝟙 _) (𝟙 _) ?_ ?_
  · simp_rw [Category.comp_id, t_fst_fst_assoc, ← pullback.condition]
  · rw [Category.comp_id, Category.id_comp]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_fst** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.Scheme.Pullback`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y 
⟶ Z)   [inst : ∀ (i : 𝒰.I₀), CategoryTheory.Limits.HasPullback (CategoryTheory.C
ategoryStruct.comp (𝒰.f i) f) g]   (i j k : 𝒰.I₀),   CategoryTheory.CategoryStru
ct.comp (AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k)       (CategoryTheory
.CategoryStruct.comp         (CategoryTheory.Limits.pullback.fst (AlgebraicGeome
try.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.Pullback.f
V 𝒰 f g j i))         (CategoryTheory.CategoryStruct.comp           (CategoryThe
ory.Limits.pullback.fst             (CategoryTheory.CategoryStruct.comp         
      (CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰
.f j) f) g) (𝒰.f j))             (𝒰.f k))           (CategoryTheory.Limits.pullb
ack.fst (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g))) =     CategoryTheory
.CategoryStruct.comp       (CategoryTheory.Limits.pullback.fst (AlgebraicGeometr
y.Scheme.Pullback.fV 𝒰 f g i j)         (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 
f g i k))       (CategoryTheory.Limits.pullback.snd         (CategoryTheory.Cate
goryStruct.comp           (CategoryTheory.Limits.pullback.fst (CategoryTheory.Ca
tegoryStruct.comp (𝒰.f i) f) g) (𝒰.f i))         (𝒰.f j))
参数：𝒰 : X.OpenCover；f : X ⟶ Z；g : Y ⟶ Z；i : 𝒰.I₀；CategoryTheory.CategoryStruct.co
mp (𝒰.f i) f；i j k : 𝒰.I₀；AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k；Categ
oryTheory.CategoryStruct.comp         (CategoryTheory.Limits.pullback.fst (Algeb
raicGeometry.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.P
ullback.fV 𝒰 f g j i))         (CategoryTheory.CategoryStruct.comp           (Ca
tegoryTheory.Limits.pullback.fst             (CategoryTheory.CategoryStruct.comp
               (CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruc
t.comp (𝒰.f j) f) g) (𝒰.f j))             (𝒰.f k))           (CategoryTheory.Lim
its.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g))；CategoryTheo
ry.Limits.pullback.fst (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i j)         
(AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i k)；CategoryTheory.Limits.pullback.
snd         (CategoryTheory.CategoryStruct.comp           (CategoryTheory.Limits
.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰.f i) f) g) (𝒰.f i))        
 (𝒰.f j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst_assoc`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) 
(g : Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t_fst_fst`：t_fst_fst (i j : 𝒰.I₀) : t 
𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.snd _ _
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_fst_fst_fst (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.Scheme.Pullback`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y 
⟶ Z)   [inst : ∀ (i : 𝒰.I₀), CategoryTheory.Limits.HasPullback (CategoryTheory.C
ategoryStruct.comp (𝒰.f i) f) g]   (i j k : 𝒰.I₀),   CategoryTheory.CategoryStru
ct.comp (AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k)       (CategoryTheory
.CategoryStruct.comp         (CategoryTheory.Limits.pullback.fst (AlgebraicGeome
try.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.Pullback.f
V 𝒰 f g j i))         (CategoryTheory.CategoryStruct.comp           (CategoryThe
ory.Limits.pullback.fst             (CategoryTheory.CategoryStruct.comp         
      (CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰
.f j) f) g) (𝒰.f j))             (𝒰.f k))           (CategoryTheory.Limits.pullb
ack.snd (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g))) =     CategoryTheory
.CategoryStruct.comp       (CategoryTheory.Limits.pullback.fst (AlgebraicGeometr
y.Scheme.Pullback.fV 𝒰 f g i j)         (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 
f g i k))       (CategoryTheory.CategoryStruct.comp         (CategoryTheory.Limi
ts.pullback.fst           (CategoryTheory.CategoryStruct.comp             (Categ
oryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰.f i) f) g) 
(𝒰.f i))           (𝒰.f j))         (CategoryTheory.Limits.pullback.snd (Categor
yTheory.CategoryStruct.comp (𝒰.f i) f) g))
参数：𝒰 : X.OpenCover；f : X ⟶ Z；g : Y ⟶ Z；i : 𝒰.I₀；CategoryTheory.CategoryStruct.co
mp (𝒰.f i) f；i j k : 𝒰.I₀；AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k；Categ
oryTheory.CategoryStruct.comp         (CategoryTheory.Limits.pullback.fst (Algeb
raicGeometry.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.P
ullback.fV 𝒰 f g j i))         (CategoryTheory.CategoryStruct.comp           (Ca
tegoryTheory.Limits.pullback.fst             (CategoryTheory.CategoryStruct.comp
               (CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruc
t.comp (𝒰.f j) f) g) (𝒰.f j))             (𝒰.f k))           (CategoryTheory.Lim
its.pullback.snd (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g))；CategoryTheo
ry.Limits.pullback.fst (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i j)         
(AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i k)；CategoryTheory.CategoryStruct.c
omp         (CategoryTheory.Limits.pullback.fst           (CategoryTheory.Catego
ryStruct.comp             (CategoryTheory.Limits.pullback.fst (CategoryTheory.Ca
tegoryStruct.comp (𝒰.f i) f) g) (𝒰.f i))           (𝒰.f j))         (CategoryThe
ory.Limits.pullback.snd (CategoryTheory.CategoryStruct.comp (𝒰.f i) f) g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst_assoc`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) 
(g : Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t_fst_snd`：t_fst_snd (i j : 𝒰.I₀) : t 
𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.sn
d _ _
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_fst_fst_snd (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t'_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.Pullback`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y 
⟶ Z)   [inst : ∀ (i : 𝒰.I₀), CategoryTheory.Limits.HasPullback (CategoryTheory.C
ategoryStruct.comp (𝒰.f i) f) g]   (i j k : 𝒰.I₀),   CategoryTheory.CategoryStru
ct.comp (AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k)       (CategoryTheory
.CategoryStruct.comp         (CategoryTheory.Limits.pullback.fst (AlgebraicGeome
try.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.Pullback.f
V 𝒰 f g j i))         (CategoryTheory.Limits.pullback.snd           (CategoryThe
ory.CategoryStruct.comp             (CategoryTheory.Limits.pullback.fst (Categor
yTheory.CategoryStruct.comp (𝒰.f j) f) g) (𝒰.f j))           (𝒰.f k))) =     Cat
egoryTheory.CategoryStruct.comp       (CategoryTheory.Limits.pullback.snd (Algeb
raicGeometry.Scheme.Pullback.fV 𝒰 f g i j)         (AlgebraicGeometry.Scheme.Pul
lback.fV 𝒰 f g i k))       (CategoryTheory.Limits.pullback.snd         (Category
Theory.CategoryStruct.comp           (CategoryTheory.Limits.pullback.fst (Catego
ryTheory.CategoryStruct.comp (𝒰.f i) f) g) (𝒰.f i))         (𝒰.f k))
参数：𝒰 : X.OpenCover；f : X ⟶ Z；g : Y ⟶ Z；i : 𝒰.I₀；CategoryTheory.CategoryStruct.co
mp (𝒰.f i) f；i j k : 𝒰.I₀；AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k；Categ
oryTheory.CategoryStruct.comp         (CategoryTheory.Limits.pullback.fst (Algeb
raicGeometry.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.P
ullback.fV 𝒰 f g j i))         (CategoryTheory.Limits.pullback.snd           (Ca
tegoryTheory.CategoryStruct.comp             (CategoryTheory.Limits.pullback.fst
 (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g) (𝒰.f j))           (𝒰.f k))；C
ategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i 
j)         (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i k)；CategoryTheory.Limit
s.pullback.snd         (CategoryTheory.CategoryStruct.comp           (CategoryTh
eory.Limits.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰.f i) f) g) (𝒰.f 
i))         (𝒰.f k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd`：pullbackR
ightPullbackFstIso_inv_snd_snd : (pullbackRightPullbackFstIso f g f').inv ≫ pull
back.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd`：pullbackRight
PullbackFstIso_hom_snd : (pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd
 _ _ = pullback.snd f' (pullback.fst f g) ≫ pul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_fst_snd (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd, Category.comp_id,
    pullbackRightPullbackFstIso_hom_snd]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t'_snd_fst_fst** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.Scheme.Pullback`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y 
⟶ Z)   [inst : ∀ (i : 𝒰.I₀), CategoryTheory.Limits.HasPullback (CategoryTheory.C
ategoryStruct.comp (𝒰.f i) f) g]   (i j k : 𝒰.I₀),   CategoryTheory.CategoryStru
ct.comp (AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k)       (CategoryTheory
.CategoryStruct.comp         (CategoryTheory.Limits.pullback.snd (AlgebraicGeome
try.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.Pullback.f
V 𝒰 f g j i))         (CategoryTheory.CategoryStruct.comp           (CategoryThe
ory.Limits.pullback.fst             (CategoryTheory.CategoryStruct.comp         
      (CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰
.f j) f) g) (𝒰.f j))             (𝒰.f i))           (CategoryTheory.Limits.pullb
ack.fst (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g))) =     CategoryTheory
.CategoryStruct.comp       (CategoryTheory.Limits.pullback.fst (AlgebraicGeometr
y.Scheme.Pullback.fV 𝒰 f g i j)         (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 
f g i k))       (CategoryTheory.Limits.pullback.snd         (CategoryTheory.Cate
goryStruct.comp           (CategoryTheory.Limits.pullback.fst (CategoryTheory.Ca
tegoryStruct.comp (𝒰.f i) f) g) (𝒰.f i))         (𝒰.f j))
参数：𝒰 : X.OpenCover；f : X ⟶ Z；g : Y ⟶ Z；i : 𝒰.I₀；CategoryTheory.CategoryStruct.co
mp (𝒰.f i) f；i j k : 𝒰.I₀；AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k；Categ
oryTheory.CategoryStruct.comp         (CategoryTheory.Limits.pullback.snd (Algeb
raicGeometry.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.P
ullback.fV 𝒰 f g j i))         (CategoryTheory.CategoryStruct.comp           (Ca
tegoryTheory.Limits.pullback.fst             (CategoryTheory.CategoryStruct.comp
               (CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruc
t.comp (𝒰.f j) f) g) (𝒰.f j))             (𝒰.f i))           (CategoryTheory.Lim
its.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g))；CategoryTheo
ry.Limits.pullback.fst (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i j)         
(AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i k)；CategoryTheory.Limits.pullback.
snd         (CategoryTheory.CategoryStruct.comp           (CategoryTheory.Limits
.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰.f i) f) g) (𝒰.f i))        
 (𝒰.f j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t_fst_fst`：t_fst_fst (i j : 𝒰.I₀) : t 
𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.snd _ _
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_snd_fst_fst (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t'_snd_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.Scheme.Pullback`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y 
⟶ Z)   [inst : ∀ (i : 𝒰.I₀), CategoryTheory.Limits.HasPullback (CategoryTheory.C
ategoryStruct.comp (𝒰.f i) f) g]   (i j k : 𝒰.I₀),   CategoryTheory.CategoryStru
ct.comp (AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k)       (CategoryTheory
.CategoryStruct.comp         (CategoryTheory.Limits.pullback.snd (AlgebraicGeome
try.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.Pullback.f
V 𝒰 f g j i))         (CategoryTheory.CategoryStruct.comp           (CategoryThe
ory.Limits.pullback.fst             (CategoryTheory.CategoryStruct.comp         
      (CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰
.f j) f) g) (𝒰.f j))             (𝒰.f i))           (CategoryTheory.Limits.pullb
ack.snd (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g))) =     CategoryTheory
.CategoryStruct.comp       (CategoryTheory.Limits.pullback.fst (AlgebraicGeometr
y.Scheme.Pullback.fV 𝒰 f g i j)         (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 
f g i k))       (CategoryTheory.CategoryStruct.comp         (CategoryTheory.Limi
ts.pullback.fst           (CategoryTheory.CategoryStruct.comp             (Categ
oryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰.f i) f) g) 
(𝒰.f i))           (𝒰.f j))         (CategoryTheory.Limits.pullback.snd (Categor
yTheory.CategoryStruct.comp (𝒰.f i) f) g))
参数：𝒰 : X.OpenCover；f : X ⟶ Z；g : Y ⟶ Z；i : 𝒰.I₀；CategoryTheory.CategoryStruct.co
mp (𝒰.f i) f；i j k : 𝒰.I₀；AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k；Categ
oryTheory.CategoryStruct.comp         (CategoryTheory.Limits.pullback.snd (Algeb
raicGeometry.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.P
ullback.fV 𝒰 f g j i))         (CategoryTheory.CategoryStruct.comp           (Ca
tegoryTheory.Limits.pullback.fst             (CategoryTheory.CategoryStruct.comp
               (CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruc
t.comp (𝒰.f j) f) g) (𝒰.f j))             (𝒰.f i))           (CategoryTheory.Lim
its.pullback.snd (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g))；CategoryTheo
ry.Limits.pullback.fst (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i j)         
(AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i k)；CategoryTheory.CategoryStruct.c
omp         (CategoryTheory.Limits.pullback.fst           (CategoryTheory.Catego
ryStruct.comp             (CategoryTheory.Limits.pullback.fst (CategoryTheory.Ca
tegoryStruct.comp (𝒰.f i) f) g) (𝒰.f i))           (𝒰.f j))         (CategoryThe
ory.Limits.pullback.snd (CategoryTheory.CategoryStruct.comp (𝒰.f i) f) g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t_fst_snd`：t_fst_snd (i j : 𝒰.I₀) : t 
𝒰 f g i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.sn
d _ _
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_snd_fst_snd (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.t'_snd_snd** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.Pullback`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y 
⟶ Z)   [inst : ∀ (i : 𝒰.I₀), CategoryTheory.Limits.HasPullback (CategoryTheory.C
ategoryStruct.comp (𝒰.f i) f) g]   (i j k : 𝒰.I₀),   CategoryTheory.CategoryStru
ct.comp (AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k)       (CategoryTheory
.CategoryStruct.comp         (CategoryTheory.Limits.pullback.snd (AlgebraicGeome
try.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.Pullback.f
V 𝒰 f g j i))         (CategoryTheory.Limits.pullback.snd           (CategoryThe
ory.CategoryStruct.comp             (CategoryTheory.Limits.pullback.fst (Categor
yTheory.CategoryStruct.comp (𝒰.f j) f) g) (𝒰.f j))           (𝒰.f i))) =     Cat
egoryTheory.CategoryStruct.comp       (CategoryTheory.Limits.pullback.fst (Algeb
raicGeometry.Scheme.Pullback.fV 𝒰 f g i j)         (AlgebraicGeometry.Scheme.Pul
lback.fV 𝒰 f g i k))       (CategoryTheory.CategoryStruct.comp         (Category
Theory.Limits.pullback.fst           (CategoryTheory.CategoryStruct.comp        
     (CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰.
f i) f) g) (𝒰.f i))           (𝒰.f j))         (CategoryTheory.Limits.pullback.f
st (CategoryTheory.CategoryStruct.comp (𝒰.f i) f) g))
参数：𝒰 : X.OpenCover；f : X ⟶ Z；g : Y ⟶ Z；i : 𝒰.I₀；CategoryTheory.CategoryStruct.co
mp (𝒰.f i) f；i j k : 𝒰.I₀；AlgebraicGeometry.Scheme.Pullback.t' 𝒰 f g i j k；Categ
oryTheory.CategoryStruct.comp         (CategoryTheory.Limits.pullback.snd (Algeb
raicGeometry.Scheme.Pullback.fV 𝒰 f g j k)           (AlgebraicGeometry.Scheme.P
ullback.fV 𝒰 f g j i))         (CategoryTheory.Limits.pullback.snd           (Ca
tegoryTheory.CategoryStruct.comp             (CategoryTheory.Limits.pullback.fst
 (CategoryTheory.CategoryStruct.comp (𝒰.f j) f) g) (𝒰.f j))           (𝒰.f i))；C
ategoryTheory.Limits.pullback.fst (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i 
j)         (AlgebraicGeometry.Scheme.Pullback.fV 𝒰 f g i k)；CategoryTheory.Categ
oryStruct.comp         (CategoryTheory.Limits.pullback.fst           (CategoryTh
eory.CategoryStruct.comp             (CategoryTheory.Limits.pullback.fst (Catego
ryTheory.CategoryStruct.comp (𝒰.f i) f) g) (𝒰.f i))           (𝒰.f j))         (
CategoryTheory.Limits.pullback.fst (CategoryTheory.CategoryStruct.comp (𝒰.f i) f
) g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t_snd`：t_snd (i j : 𝒰.I₀) : t 𝒰 f g i 
j ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.fst _ _
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem t'_snd_snd (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]
/-
**AlgebraicGeometry.Scheme.Pullback.cocycle_fst_fst_fst** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：cocycle_fst_fst_fst (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 
𝒰 f g k i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.
fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _
参数：i j k : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_fst`：∀ {X Y Z : AlgebraicGe
ometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀),
 CategoryTheory.Limits.HasPullback (Ca…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_fst_snd`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀), Cat
egoryTheory.Limits.HasPullback (Ca…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_snd_snd`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀), Cat
egoryTheory.Limits.HasPullback (Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cocycle_fst_fst_fst (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
      pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [t'_fst_fst_fst, t'_fst_snd, t'_snd_snd]
/-
**AlgebraicGeometry.Scheme.Pullback.cocycle_fst_fst_snd** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：cocycle_fst_fst_snd (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 
𝒰 f g k i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.
fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _
参数：i j k : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_snd`：∀ {X Y Z : AlgebraicGe
ometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀),
 CategoryTheory.Limits.HasPullback (Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cocycle_fst_fst_snd (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
      pullback.snd _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t'_fst_fst_snd]
/-
**AlgebraicGeometry.Scheme.Pullback.cocycle_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Pullback`。
形式化陈述：cocycle_fst_snd (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f 
g k i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.snd 
_ _
参数：i j k : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_fst_snd`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀), Cat
egoryTheory.Limits.HasPullback (Ca…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_snd_snd`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀), Cat
egoryTheory.Limits.HasPullback (Ca…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_fst`：∀ {X Y Z : AlgebraicGe
ometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀),
 CategoryTheory.Limits.HasPullback (Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cocycle_fst_snd (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t'_fst_snd, t'_snd_snd, t'_fst_fst_fst]
/-
**AlgebraicGeometry.Scheme.Pullback.cocycle_snd_fst_fst** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：cocycle_snd_fst_fst (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 
𝒰 f g k i j ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.
snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _
参数：i j k : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_snd_fst_fst`：∀ {X Y Z : AlgebraicGe
ometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀),
 CategoryTheory.Limits.HasPullback (Ca…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_fst_snd`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀), Cat
egoryTheory.Limits.HasPullback (Ca…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_snd_snd`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀), Cat
egoryTheory.Limits.HasPullback (Ca…
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cocycle_snd_fst_fst (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫
      pullback.fst _ _ = pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [pullback.condition_assoc, t'_snd_fst_fst, t'_fst_snd, t'_snd_snd]
/-
**AlgebraicGeometry.Scheme.Pullback.cocycle_snd_fst_snd** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：cocycle_snd_fst_snd (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 
𝒰 f g k i j ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.
snd _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _
参数：i j k : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_snd_fst_snd`：∀ {X Y Z : AlgebraicGe
ometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀),
 CategoryTheory.Limits.HasPullback (Ca…
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cocycle_snd_fst_snd (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [pullback.condition_assoc, t'_snd_fst_snd]
/-
**AlgebraicGeometry.Scheme.Pullback.cocycle_snd_snd** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Pullback`。
形式化陈述：cocycle_snd_snd (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f 
g k i j ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd 
_ _
参数：i j k : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_snd_snd`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀), Cat
egoryTheory.Limits.HasPullback (Ca…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_fst_fst_fst`：∀ {X Y Z : AlgebraicGe
ometry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀),
 CategoryTheory.Limits.HasPullback (Ca…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t'_fst_snd`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (𝒰 : X.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z)   [inst : ∀ (i : 𝒰.I₀), Cat
egoryTheory.Limits.HasPullback (Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cocycle_snd_snd (i j k : 𝒰.I₀) :
    t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp only [t'_snd_snd, t'_fst_fst_fst, t'_fst_snd]

-- `by tidy` should solve it, but it times out.
/-
**AlgebraicGeometry.Scheme.Pullback.cocycle** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme.Pullback`。
形式化陈述：cocycle (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j 
= 𝟙 _
参数：i j k : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.cocycle_fst_fst_fst`：cocycle_fst_fst_f
st (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.
fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.cocycle_fst_fst_snd`：cocycle_fst_fst_s
nd (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.
fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.cocycle_fst_snd`：cocycle_fst_snd (i j 
k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst _ _ 
≫ pullback.snd _ _ = pullback.fst _ _ ≫…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.cocycle_snd_fst_fst`：cocycle_snd_fst_f
st (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.
snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.cocycle_snd_fst_snd`：cocycle_snd_fst_s
nd (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.
snd _ _ ≫ pullback.fst _ _ ≫ pullback.snd _…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.cocycle_snd_snd`：cocycle_snd_snd (i j 
k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd _ _ 
≫ pullback.snd _ _ = pullback.snd _ _ ≫…
-/
theorem cocycle (i j k : 𝒰.I₀) : t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j = 𝟙 _ := by
  apply pullback.hom_ext <;> rw [Category.id_comp]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp_rw [Category.assoc, cocycle_fst_fst_fst 𝒰 f g i j k]
      · simp_rw [Category.assoc, cocycle_fst_fst_snd 𝒰 f g i j k]
    · simp_rw [Category.assoc, cocycle_fst_snd 𝒰 f g i j k]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp_rw [Category.assoc, cocycle_snd_fst_fst 𝒰 f g i j k]
      · simp_rw [Category.assoc, cocycle_snd_fst_snd 𝒰 f g i j k]
    · simp_rw [Category.assoc, cocycle_snd_snd 𝒰 f g i j k]

/-- Given `Uᵢ ×[Z] Y`, this is the glued fibred product `X ×[Z] Y`. -/
@[simps U V f t t', simps -isSimp J]
/-
**AlgebraicGeometry.Scheme.Pullback.gluing** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme.Pullback`。
形式化陈述：gluing : Scheme.GlueData.{u} where J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.t_id`：t_id (i : 𝒰.I₀) : t 𝒰 f g i i = 
𝟙 _
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.cocycle`：cocycle (i j k : 𝒰.I₀) : t' 𝒰
 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j = 𝟙 _

--- 原说明 ---
Given `Uᵢ ×[Z] Y`, this is the glued fibred product `X ×[Z] Y`.
-/
def gluing : Scheme.GlueData.{u} where
  J := 𝒰.I₀
  U i := pullback (𝒰.f i ≫ f) g
  V := fun ⟨i, j⟩ => v 𝒰 f g i j
  -- `p⁻¹(Uᵢ ∩ Uⱼ)` where `p : Uᵢ ×[Z] Y ⟶ Uᵢ ⟶ X`.
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  f_open := inferInstance
  t i j := t 𝒰 f g i j
  t_id i := t_id 𝒰 f g i
  t' i j k := t' 𝒰 f g i j k
  t_fac i j k := by
    apply pullback.hom_ext
    on_goal 1 => apply pullback.hom_ext
    all_goals
      simp only [t'_snd_fst_fst, t'_snd_fst_snd, t'_snd_snd, t_fst_fst, t_fst_snd, t_snd,
        Category.assoc]
  cocycle i j k := cocycle 𝒰 f g i j k

@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.gluing_** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma gluing_ι (j : 𝒰.I₀) :
    (gluing 𝒰 f g).ι j = Multicoequalizer.π (gluing 𝒰 f g).diagram j := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The first projection from the glued scheme into `X`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.p1** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Pullback`。
形式化陈述：p1 : (gluing 𝒰 f g).glued ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection from the glued scheme into `X`.
-/
def p1 : (gluing 𝒰 f g).glued ⟶ X := by
  apply Multicoequalizer.desc (gluing 𝒰 f g).diagram _ fun i ↦ pullback.fst _ _ ≫ 𝒰.f i
  simp [t_fst_fst_assoc, ← pullback.condition]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The second projection from the glued scheme into `Y`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.p2** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Pullback`。
形式化陈述：p2 : (gluing 𝒰 f g).glued ⟶ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection from the glued scheme into `Y`.
-/
def p2 : (gluing 𝒰 f g).glued ⟶ Y := by
  apply Multicoequalizer.desc _ _ fun i ↦ pullback.snd _ _
  simp [t_fst_snd]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.p_comm** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Pullback`。
形式化陈述：p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f g ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.hom_ext`：hom_ext {W : C} (i j : m
ulticoequalizer I ⟶ W) (h : forall b, Multicoequalizer.π I b ≫ i = Multicoequali
zer.π I b ≫ j) : i = j
· 使用定理 `AlgebraicGeometry.Scheme.GlueData.instHasMulticoequalizerDiagram`：∀ (D :
 AlgebraicGeometry.Scheme.GlueData), CategoryTheory.Limits.HasMulticoequalizer D
.diagram
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.Multicofork.ofπ_ι_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MultispanShape}   (I : 
CategoryTheory.Limits.MultispanIn…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f g ≫ g := by
  apply Multicoequalizer.hom_ext
  simp [p1, p2, pullback.condition]

variable (s : PullbackCone f g)

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation)
The canonical map `(s.X ×[X] Uᵢ) ×[s.X] (s.X ×[X] Uⱼ) ⟶ (Uᵢ ×[Z] Y) ×[X] Uⱼ`

This is used in `gluedLift`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.gluedLiftPullbackMap** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：gluedLiftPullbackMap (i j : 𝒰.I₀) : pullback ((𝒰.pullback₁ s.fst).f i) ((𝒰
.pullback₁ s.fst).f j) ⟶ (gluing 𝒰 f g).V ⟨i, j⟩
参数：i j : 𝒰.I₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g

--- 原说明 ---
(Implementation)
The canonical map `(s.X ×[X] Uᵢ) ×[s.X] (s.X ×[X] Uⱼ) ⟶ (Uᵢ ×[Z] Y) ×[X] Uⱼ`

This is used in `gluedLift`.
-/
def gluedLiftPullbackMap (i j : 𝒰.I₀) :
    pullback ((𝒰.pullback₁ s.fst).f i) ((𝒰.pullback₁ s.fst).f j) ⟶
      (gluing 𝒰 f g).V ⟨i, j⟩ := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine pullback.map _ _ _ _ ?_ (𝟙 _) (𝟙 _) ?_ ?_
  · exact (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition
  · simpa using! pullback.condition
  · simp only [Category.comp_id, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.gluedLiftPullbackMap_fst** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：gluedLiftPullbackMap_fst (i j : 𝒰.I₀) : gluedLiftPullbackMap 𝒰 f g s i j ≫
 pullback.fst _ _ = pullback.fst _ _ ≫ (pullbackSymmetry _ _).hom ≫ pullback.map
 _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition
参数：i j : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gluedLiftPullbackMap_fst (i j : 𝒰.I₀) :
    gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫
        (pullbackSymmetry _ _).hom ≫
          pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition := by
  simp [gluedLiftPullbackMap]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.gluedLiftPullbackMap_snd** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：gluedLiftPullbackMap_snd (i j : 𝒰.I₀) : gluedLiftPullbackMap 𝒰 f g s i j ≫
 pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _
参数：i j : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd`：pullbackRight
PullbackFstIso_hom_snd : (pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd
 _ _ = pullback.snd f' (pullback.fst f g) ≫ pul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gluedLiftPullbackMap_snd (i j : 𝒰.I₀) :
    gluedLiftPullbackMap 𝒰 f g s i j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp [gluedLiftPullbackMap]

set_option backward.isDefEq.respectTransparency false in
/-- The lifted map `s.X ⟶ (gluing 𝒰 f g).glued` in order to show that `(gluing 𝒰 f g).glued` is
indeed the pullback.

Given a pullback cone `s`, we have the maps `s.fst ⁻¹' Uᵢ ⟶ Uᵢ` and
`s.fst ⁻¹' Uᵢ ⟶ s.X ⟶ Y` that we may lift to a map `s.fst ⁻¹' Uᵢ ⟶ Uᵢ ×[Z] Y`.

to glue these into a map `s.X ⟶ Uᵢ ×[Z] Y`, we need to show that the maps agree on
`(s.fst ⁻¹' Uᵢ) ×[s.X] (s.fst ⁻¹' Uⱼ) ⟶ Uᵢ ×[Z] Y`. This is achieved by showing that both of these
maps factors through `gluedLiftPullbackMap`.
-/
/-
**AlgebraicGeometry.Scheme.Pullback.gluedLift** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.Pullback`。
形式化陈述：gluedLift : s.pt ⟶ (gluing 𝒰 f g).glued
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g

--- 原说明 ---
The lifted map `s.X ⟶ (gluing 𝒰 f g).glued` in order to show that `(gluing 𝒰 f g
).glued` is
indeed the pullback.

Given a pullback cone `s`, we have the maps `s.fst ⁻¹' Uᵢ ⟶ Uᵢ` and
`s.fst ⁻¹' Uᵢ ⟶ s.X ⟶ Y` that we may lift to a map `s.fst ⁻¹' Uᵢ ⟶ Uᵢ ×[Z] Y`.

to glue these into a map `s.X ⟶ Uᵢ ×[Z] Y`, we need to show that the maps agree 
on
`(s.fst ⁻¹' Uᵢ) ×[s.X] (s.fst ⁻¹' Uⱼ) ⟶ Uᵢ ×[Z] Y`. This is achieved by showing 
that both of these
maps factors through `gluedLiftPullbackMap`.
-/
def gluedLift : s.pt ⟶ (gluing 𝒰 f g).glued := by
  fapply Cover.glueMorphisms (𝒰.pullback₁ s.fst)
  · exact fun i ↦ (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (Category.id_comp _).symm s.condition ≫ (gluing 𝒰 f g).ι i
  intro i j
  rw [← gluedLiftPullbackMap_fst_assoc, ← gluing_f, ← (gluing 𝒰 f g).glue_condition i j,
    gluing_t, gluing_f]
  simp_rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp_rw [Category.assoc]
  · rw [t_fst_fst, gluedLiftPullbackMap_snd]
    congr 1
    rw [← Iso.inv_comp_eq, pullbackSymmetry_inv_comp_snd, pullback.lift_fst, Category.comp_id]
  · rw [t_fst_snd, gluedLiftPullbackMap_fst_assoc, pullback.lift_snd, pullback.lift_snd]
    simp_rw [pullbackSymmetry_hom_comp_snd_assoc]
    exact pullback.condition_assoc _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.gluedLift_p1** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.Pullback`。
形式化陈述：gluedLift_p1 : gluedLift 𝒰 f g s ≫ p1 𝒰 f g = s.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.instIsIsoFromGlued`：∀ {X : AlgebraicGeome
try.Scheme} (𝒰 : X.OpenCover), CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Co
ver.fromGlued 𝒰)
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.hom_ext`：hom_ext {W : C} (i j : m
ulticoequalizer I ⟶ W) (h : forall b, Multicoequalizer.π I b ≫ i = Multicoequali
zer.π I b ≫ j) : i = j
· 使用定理 `AlgebraicGeometry.Scheme.GlueData.instHasMulticoequalizerDiagram`：∀ (D :
 AlgebraicGeometry.Scheme.GlueData), CategoryTheory.Limits.HasMulticoequalizer D
.diagram
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.π_desc_assoc`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MultispanShape}
   (I : CategoryTheory.Limits.MultispanIn…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Cover.glueMorphisms.congr_simp`：∀ {X : Algebrai
cGeometry.Scheme} (𝒰 : X.OpenCover) {Y : AlgebraicGeometry.Scheme} (f f_1 : (x :
 𝒰.I₀) → 𝒰.X x ⟶ Y)   (e_f : f = f_1)   (hf :…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms`：ι_glueMorphisms (𝒰 : Ope
nCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y) (hf : forall x y, pullback.
fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gluedLift_p1 : gluedLift 𝒰 f g s ≫ p1 𝒰 f g = s.fst := by
  rw [← cancel_epi (Cover.fromGlued <| 𝒰.pullback₁ s.fst)]
  apply Multicoequalizer.hom_ext
  intro b
  simp_rw [Cover.fromGlued, Multicoequalizer.π_desc_assoc, gluedLift, ← Category.assoc]
  simp_rw [Cover.ι_glueMorphisms (𝒰.pullback₁ s.fst)]
  simp [p1, pullback.condition]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.gluedLift_p2** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.Pullback`。
形式化陈述：gluedLift_p2 : gluedLift 𝒰 f g s ≫ p2 𝒰 f g = s.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.instIsIsoFromGlued`：∀ {X : AlgebraicGeome
try.Scheme} (𝒰 : X.OpenCover), CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Co
ver.fromGlued 𝒰)
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.hom_ext`：hom_ext {W : C} (i j : m
ulticoequalizer I ⟶ W) (h : forall b, Multicoequalizer.π I b ≫ i = Multicoequali
zer.π I b ≫ j) : i = j
· 使用定理 `AlgebraicGeometry.Scheme.GlueData.instHasMulticoequalizerDiagram`：∀ (D :
 AlgebraicGeometry.Scheme.GlueData), CategoryTheory.Limits.HasMulticoequalizer D
.diagram
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.π_desc_assoc`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MultispanShape}
   (I : CategoryTheory.Limits.MultispanIn…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Cover.glueMorphisms.congr_simp`：∀ {X : Algebrai
cGeometry.Scheme} (𝒰 : X.OpenCover) {Y : AlgebraicGeometry.Scheme} (f f_1 : (x :
 𝒰.I₀) → 𝒰.X x ⟶ Y)   (e_f : f = f_1)   (hf :…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms`：ι_glueMorphisms (𝒰 : Ope
nCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y) (hf : forall x y, pullback.
fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gluedLift_p2 : gluedLift 𝒰 f g s ≫ p2 𝒰 f g = s.snd := by
  rw [← cancel_epi (Cover.fromGlued <| 𝒰.pullback₁ s.fst)]
  apply Multicoequalizer.hom_ext
  intro b
  simp_rw [Cover.fromGlued, Multicoequalizer.π_desc_assoc, gluedLift, ← Category.assoc]
  simp_rw [(Cover.ι_glueMorphisms <| 𝒰.pullback₁ s.fst)]
  simp [p2]

set_option backward.isDefEq.respectTransparency.types false in
/-- (Implementation)
The canonical map `(W ×[X] Uᵢ) ×[W] (Uⱼ ×[Z] Y) ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ = V j i` where `W` is
the glued fibred product.

This is used in `lift_comp_ι`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.pullbackFst** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation)
The canonical map `(W ×[X] Uᵢ) ×[W] (Uⱼ ×[Z] Y) ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ = V j i` w
here `W` is
the glued fibred product.

This is used in `lift_comp_ι`.
-/
def pullbackFstιToV (i j : 𝒰.I₀) :
    pullback (pullback.fst (p1 𝒰 f g) (𝒰.f i)) ((gluing 𝒰 f g).ι j) ⟶
      v 𝒰 f g j i :=
  (pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso (p1 𝒰 f g) (𝒰.f i) _).hom ≫
    (pullback.congrHom (Multicoequalizer.π_desc ..) rfl).hom

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.pullbackFst** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackFstιToV_fst (i j : 𝒰.I₀) :
    pullbackFstιToV 𝒰 f g i j ≫ pullback.fst _ _ = pullback.snd _ _ := by
  simp [pullbackFstιToV, p1]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.pullbackFst** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackFstιToV_snd (i j : 𝒰.I₀) :
    pullbackFstιToV 𝒰 f g i j ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp [pullbackFstιToV, p1]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- We show that the map `W ×[X] Uᵢ ⟶ Uᵢ ×[Z] Y ⟶ W` is the first projection, where the
first map is given by the lift of `W ×[X] Uᵢ ⟶ Uᵢ` and `W ×[X] Uᵢ ⟶ W ⟶ Y`.

It suffices to show that the two map agrees when restricted onto `Uⱼ ×[Z] Y`. In this case,
both maps factor through `V j i` via `pullback_fst_ι_to_V` -/
/-
**AlgebraicGeometry.Scheme.Pullback.lift_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We show that the map `W ×[X] Uᵢ ⟶ Uᵢ ×[Z] Y ⟶ W` is the first projection, where 
the
first map is given by the lift of `W ×[X] Uᵢ ⟶ Uᵢ` and `W ×[X] Uᵢ ⟶ W ⟶ Y`.

It suffices to show that the two map agrees when restricted onto `Uⱼ ×[Z] Y`. In
 this case,
both maps factor through `V j i` via `pullback_fst_ι_to_V`
-/
theorem lift_comp_ι (i : 𝒰.I₀) :
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ p2 𝒰 f g)
          (by rw [← pullback.condition_assoc, Category.assoc, p_comm]) ≫
        (gluing 𝒰 f g).ι i =
      (pullback.fst _ _ : pullback (p1 𝒰 f g) (𝒰.f i) ⟶ _) := by
  apply Cover.hom_ext ((gluing 𝒰 f g).openCover.pullback₁ (pullback.fst _ _))
  intro j
  dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f]
  trans pullbackFstιToV 𝒰 f g i j ≫ fV 𝒰 f g j i ≫ (gluing 𝒰 f g).ι _
  · rw [← show _ = fV 𝒰 f g j i ≫ _ from (gluing 𝒰 f g).glue_condition j i]
    simp_rw [← Category.assoc]
    congr 1
    rw [gluing_f, gluing_t]
    apply pullback.hom_ext <;> simp_rw [Category.assoc]
    · simp_rw [t_fst_fst, pullback.lift_fst, pullbackFstιToV_snd, GlueData.openCover_f]
    · simp_rw [t_fst_snd, pullback.lift_snd, pullbackFstιToV_fst_assoc, pullback.condition_assoc,
        GlueData.openCover_f, p2]
      simp
  · rw [pullback.condition, ← Category.assoc]
    simp_rw [pullbackFstιToV_fst, GlueData.openCover_f]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism between `W ×[X] Uᵢ` and `Uᵢ ×[X] Y`. That is, the preimage of `Uᵢ` in
`W` along `p1` is indeed `Uᵢ ×[X] Y`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme.Pullback`。
形式化陈述：pullbackP1Iso (i : 𝒰.I₀) : pullback (p1 𝒰 f g) (𝒰.f i) ≅ pullback (𝒰.f i ≫
 f) g
参数：i : 𝒰.I₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between `W ×[X] Uᵢ` and `Uᵢ ×[X] Y`. That is, the prei
mage of `Uᵢ` in
`W` along `p1` is indeed `Uᵢ ×[X] Y`.
-/
def pullbackP1Iso (i : 𝒰.I₀) : pullback (p1 𝒰 f g) (𝒰.f i) ≅ pullback (𝒰.f i ≫ f) g := by
  fconstructor
  · exact
      pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ p2 𝒰 f g)
        (by rw [← pullback.condition_assoc, Category.assoc, p_comm])
  · exact pullback.lift ((gluing 𝒰 f g).ι i) (pullback.fst _ _)
      (by rw [gluing_ι, p1, Multicoequalizer.π_desc])
  · apply pullback.hom_ext
    · simpa using lift_comp_ι 𝒰 f g i
    · simp_rw [Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp]
  · apply pullback.hom_ext
    · simp_rw [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · simp [p2]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_hom_fst** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：pullbackP1Iso_hom_fst (i : 𝒰.I₀) : (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.
fst _ _ = pullback.snd _ _
参数：i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackP1Iso_hom_fst (i : 𝒰.I₀) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.fst _ _ = pullback.snd _ _ := by
  simp_rw [pullbackP1Iso, pullback.lift_fst]

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_hom_snd** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：pullbackP1Iso_hom_snd (i : 𝒰.I₀) : (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.
snd _ _ = pullback.fst _ _ ≫ p2 𝒰 f g
参数：i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackP1Iso_hom_snd (i : 𝒰.I₀) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ pullback.snd _ _ = pullback.fst _ _ ≫ p2 𝒰 f g := by
  simp_rw [pullbackP1Iso, pullback.lift_snd]

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_inv_fst** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：pullbackP1Iso_inv_fst (i : 𝒰.I₀) : (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.
fst _ _ = (gluing 𝒰 f g).ι i
参数：i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackP1Iso_inv_fst (i : 𝒰.I₀) :
    (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.fst _ _ = (gluing 𝒰 f g).ι i := by
  simp_rw [pullbackP1Iso, pullback.lift_fst]

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_inv_snd** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：pullbackP1Iso_inv_snd (i : 𝒰.I₀) : (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.
snd _ _ = pullback.fst _ _
参数：i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackP1Iso_inv_snd (i : 𝒰.I₀) :
    (pullbackP1Iso 𝒰 f g i).inv ≫ pullback.snd _ _ = pullback.fst _ _ := by
  simp_rw [pullbackP1Iso, pullback.lift_snd]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso_hom_** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackP1Iso_hom_ι (i : 𝒰.I₀) :
    (pullbackP1Iso 𝒰 f g i).hom ≫ Multicoequalizer.π (gluing 𝒰 f g).diagram i =
    pullback.fst _ _ := by
  rw [← gluing_ι, ← pullbackP1Iso_inv_fst, Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The glued scheme (`(gluing 𝒰 f g).glued`) is indeed the pullback of `f` and `g`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.gluedIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme.Pullback`。
形式化陈述：gluedIsLimit : IsLimit (PullbackCone.mk _ _ (p_comm 𝒰 f g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.p_comm`：p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f
 g ≫ g

--- 原说明 ---
The glued scheme (`(gluing 𝒰 f g).glued`) is indeed the pullback of `f` and `g`.
-/
def gluedIsLimit : IsLimit (PullbackCone.mk _ _ (p_comm 𝒰 f g)) := by
  apply PullbackCone.isLimitAux'
  intro s
  refine ⟨gluedLift 𝒰 f g s, gluedLift_p1 𝒰 f g s, gluedLift_p2 𝒰 f g s, ?_⟩
  intro m h₁ h₂
  simp_rw [PullbackCone.mk_pt, PullbackCone.mk_π_app] at h₁ h₂
  apply Cover.hom_ext <| 𝒰.pullback₁ s.fst
  intro i
  rw [gluedLift, (Cover.ι_glueMorphisms <| 𝒰.pullback₁ s.fst)]
  dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, PullbackCone.mk_pt, PreZeroHypercover.pullback₁_f, gluing_ι]
  rw [← cancel_epi
    (pullbackRightPullbackFstIso (p1 𝒰 f g) (𝒰.f i) m ≪≫ pullback.congrHom h₁ rfl).hom,
    Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
    Category.comp_id, pullbackRightPullbackFstIso_hom_fst_assoc, pullback.condition]
  conv_lhs => rhs; rw [← pullbackP1Iso_hom_ι]
  simp_rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp_rw [Category.assoc, pullbackP1Iso_hom_fst, pullback.lift_fst, Category.comp_id,
      pullbackSymmetry_hom_comp_fst, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd]
  · simp_rw [Category.assoc, pullbackP1Iso_hom_snd, pullback.lift_snd,
      pullbackSymmetry_hom_comp_snd_assoc, pullback.lift_fst_assoc, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst_assoc, ← pullback.condition_assoc, h₂]

include 𝒰 in
/-
**AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：hasPullback_of_cover : HasPullback f g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.p_comm`：p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f
 g ≫ g
-/
theorem hasPullback_of_cover : HasPullback f g :=
  ⟨⟨⟨_, gluedIsLimit 𝒰 f g⟩⟩⟩
/-
**AlgebraicGeometry.Scheme.Pullback.affine_hasPullback** 是 Mathlib 中的一个实例，位于命名空间
 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：affine_hasPullback {A B C : CommRingCat} (f : Spec A ⟶ Spec C) (g : Spec B
 ⟶ Spec C) : HasPullback f g
参数：f : Spec A ⟶ Spec C；g : Spec B ⟶ Spec C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.full`：AlgebraicGeometry.Scheme.Spec.Full
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
-/
instance affine_hasPullback {A B C : CommRingCat}
    (f : Spec A ⟶ Spec C)
    (g : Spec B ⟶ Spec C) : HasPullback f g := by
  rw [← Scheme.Spec.map_preimage f, ← Scheme.Spec.map_preimage g]
  exact ⟨⟨⟨_, isLimitOfHasPullbackOfPreservesLimit
    Scheme.Spec (Scheme.Spec.preimage f) (Scheme.Spec.preimage g)⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.affine_affine_hasPullback** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：affine_affine_hasPullback {B C : CommRingCat} {X : Scheme} (f : X ⟶ Spec C
) (g : Spec B ⟶ Spec C) : HasPullback f g
参数：f : X ⟶ Spec C；g : Spec B ⟶ Spec C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover`：hasPullback_of_c
over : HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
-/
theorem affine_affine_hasPullback {B C : CommRingCat} {X : Scheme}
    (f : X ⟶ Spec C) (g : Spec B ⟶ Spec C) :
    HasPullback f g :=
  hasPullback_of_cover X.affineCover f g
/-
**AlgebraicGeometry.Scheme.Pullback.base_affine_hasPullback** 是 Mathlib 中的一个实例，位
于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：base_affine_hasPullback {C : CommRingCat} {X Y : Scheme} (f : X ⟶ Spec C) 
(g : Y ⟶ Spec C) : HasPullback f g
参数：f : X ⟶ Spec C；g : Y ⟶ Spec C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover`：hasPullback_of_c
over : HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.affine_affine_hasPullback`：affine_affi
ne_hasPullback {B C : CommRingCat} {X : Scheme} (f : X ⟶ Spec C) (g : Spec B ⟶ S
pec C) : HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
-/
instance base_affine_hasPullback {C : CommRingCat} {X Y : Scheme} (f : X ⟶ Spec C)
    (g : Y ⟶ Spec C) : HasPullback f g :=
  @hasPullback_symmetry _ _ _ _ _ _ _
    (@hasPullback_of_cover _ _ _ Y.affineCover g f fun _ =>
      @hasPullback_symmetry _ _ _ _ _ _ _ <| affine_affine_hasPullback _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.left_affine_comp_pullback_hasPullback** 是 Ma
thlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：left_affine_comp_pullback_hasPullback {X Y Z : Scheme} (f : X ⟶ Z) (g : Y 
⟶ Z) (i : Z.affineCover.I₀) : HasPullback ((Z.affineCover.pullback₁ f).f i ≫ f) 
g
参数：f : X ⟶ Z；g : Y ⟶ Z；i : Z.affineCover.I₀。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.hasPullback_assoc_symm`：hasPullback_assoc_symm [Ha
sPullback f₁ (g₃ ≫ f₂)] : HasPullback (g₂ ≫ f₃) f₄
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
-/
instance left_affine_comp_pullback_hasPullback {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    (i : Z.affineCover.I₀) : HasPullback ((Z.affineCover.pullback₁ f).f i ≫ f) g := by
  simpa [pullback.condition] using
    hasPullback_assoc_symm f (Z.affineCover.f i) (Z.affineCover.f i) g

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Pullback.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  hasPullback_of_cover (Z.affineCover.pullback₁ f) f g
/-
**AlgebraicGeometry.Scheme.Pullback.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasPullbacks Scheme :=
  hasPullbacks_of_hasLimit_cospan _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine** 是 M
athlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：isAffine_of_isAffine_isAffine_isAffine {X Y Z : Scheme} (f : X ⟶ Z) (g : Y
 ⟶ Z) [IsAffine X] [IsAffine Y] [IsAffine Z] : IsAffine (pullback f g)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_naturality`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp f Y.toSpecΓ =     Cate
goryTheory.CategoryStruct.comp X.…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `AlgebraicGeometry.IsAffine.affine`：∀ {X : AlgebraicGeometry.Scheme} [sel
f : AlgebraicGeometry.IsAffine X], CategoryTheory.IsIso X.toSpecΓ
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.instIsAffineObjOppositeCommRingCatSchemeSpec`：∀ (R : C
ommRingCatᵒᵖ), AlgebraicGeometry.IsAffine (AlgebraicGeometry.Scheme.Spec.obj R)
-/
instance isAffine_of_isAffine_isAffine_isAffine {X Y Z : Scheme}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsAffine X] [IsAffine Y] [IsAffine Z] :
    IsAffine (pullback f g) :=
  .of_isIso
    (pullback.map f g (Spec.map (Γ.map f.op)) (Spec.map (Γ.map g.op))
        X.toSpecΓ Y.toSpecΓ Z.toSpecΓ
        (Scheme.toSpecΓ_naturality f) (Scheme.toSpecΓ_naturality g) ≫
      (PreservesPullback.iso Scheme.Spec _ _).inv)

-- The converse is also true. See `Scheme.isEmpty_pullback_iff`.
/-
**AlgebraicGeometry.Scheme.Pullback._root_.AlgebraicGeometry.Scheme.isEmpty_pull
back** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgebraicGeometry.Scheme.isEmpty_pullback
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (H : Disjoint (Set.range f) (Set.range g)) : IsEmpty ↑(Limits.pullback f g) :=
  isEmpty_of_commSq (IsPullback.of_hasPullback f g).toCommSq H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an open cover `{ Xᵢ }` of `X`, then `X ×[Z] Y` is covered by `Xᵢ ×[Z] Y`. -/
@[simps! I₀ X f]
/-
**AlgebraicGeometry.Scheme.Pullback.openCoverOfLeft** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Pullback`。
形式化陈述：openCoverOfLeft (𝒰 : OpenCover.{v} X) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover 
(pullback f g) where I₀
参数：𝒰 : OpenCover.{v} X；f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g

--- 原说明 ---
Given an open cover `{ Xᵢ }` of `X`, then `X ×[Z] Y` is covered by `Xᵢ ×[Z] Y`.
-/
def openCoverOfLeft (𝒰 : OpenCover.{v} X) (f : X ⟶ Z) (g : Y ⟶ Z) :
    OpenCover (pullback f g) where
  I₀ := 𝒰.I₀
  X i := pullback (𝒰.f i ≫ f) g
  f i := pullback.map (𝒰.f i ≫ f) g f g (𝒰.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)
  mem₀ := by
    rw [ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ ?_⟩
    · let 𝒱 := ((gluing 𝒰.ulift f g).openCover.pushforwardIso
              (limit.isoLimitCone ⟨_, gluedIsLimit 𝒰.ulift f g⟩).inv).copy
          𝒰.ulift.I₀ (fun i => pullback (𝒰.ulift.f i ≫ f) g)
          (fun i => pullback.map _ _ _ _ (𝒰.ulift.f i) (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp))
          (Equiv.refl 𝒰.ulift.I₀) (fun _ => Iso.refl _) fun i ↦ by
        simp_rw [Cover.pushforwardIso_I₀, Cover.pushforwardIso_f, GlueData.openCover_f,
          GlueData.openCover_I₀, gluing_J]
        exact pullback.hom_ext (by simp [p1]) (by simp [p2])
      obtain ⟨i, x, rfl⟩ := 𝒱.exists_eq x
      exact ⟨_, x, rfl⟩
    · dsimp
      have : pullback.map (𝒰.f i ≫ f) g f g (𝒰.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp) =
        (pullbackSymmetry _ _).hom ≫ (pullbackLeftPullbackSndIso _ _ _).inv ≫
          pullback.fst _ _ ≫ (pullbackSymmetry _ _).hom := by aesop
      rw [this]
      infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an open cover `{ Yᵢ }` of `Y`, then `X ×[Z] Y` is covered by `X ×[Z] Yᵢ`. -/
@[simps! I₀ X f]
/-
**AlgebraicGeometry.Scheme.Pullback.openCoverOfRight** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：openCoverOfRight (𝒰 : OpenCover.{v} Y) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover
.{v} (pullback f g)
参数：𝒰 : OpenCover.{v} Y；f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Given an open cover `{ Yᵢ }` of `Y`, then `X ×[Z] Y` is covered by `X ×[Z] Yᵢ`.
-/
def openCoverOfRight (𝒰 : OpenCover.{v} Y) (f : X ⟶ Z) (g : Y ⟶ Z) :
    OpenCover.{v} (pullback f g) := by
  fapply
    ((openCoverOfLeft 𝒰 g f).pushforwardIso (pullbackSymmetry _ _).hom).copy 𝒰.I₀
      (fun i => pullback f (𝒰.f i ≫ g))
      (fun i => pullback.map _ _ _ _ (𝟙 _) (𝒰.f i) (𝟙 _) (by simp) (Category.comp_id _))
      (Equiv.refl _) fun i => pullbackSymmetry _ _
  intro i
  dsimp
  apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given an open cover `{ Xᵢ }` of `X` and an open cover `{ Yⱼ }` of `Y`, then
`X ×[Z] Y` is covered by `Xᵢ ×[Z] Yⱼ`. -/
@[simps! I₀ X f]
/-
**AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：openCoverOfLeftRight (𝒰X : OpenCover.{v} X) (𝒰Y : OpenCover.{w} Y) (f : X 
⟶ Z) (g : Y ⟶ Z) : OpenCover.{max v w} (pullback f g)
参数：𝒰X : OpenCover.{v} X；𝒰Y : OpenCover.{w} Y；f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given an open cover `{ Xᵢ }` of `X` and an open cover `{ Yⱼ }` of `Y`, then
`X ×[Z] Y` is covered by `Xᵢ ×[Z] Yⱼ`.
-/
def openCoverOfLeftRight (𝒰X : OpenCover.{v} X) (𝒰Y : OpenCover.{w} Y) (f : X ⟶ Z) (g : Y ⟶ Z) :
    OpenCover.{max v w} (pullback f g) := by
  fapply
    Cover.copy ((openCoverOfLeft 𝒰X f g).bind fun x => openCoverOfRight 𝒰Y (𝒰X.f x ≫ f) g)
      (𝒰X.I₀ × 𝒰Y.I₀) (fun ij => pullback (𝒰X.f ij.1 ≫ f) (𝒰Y.f ij.2 ≫ g))
      (fun ij =>
        pullback.map _ _ _ _ (𝒰X.f ij.1) (𝒰Y.f ij.2) (𝟙 _) (Category.comp_id _)
          (Category.comp_id _))
      (Equiv.sigmaEquivProd _ _).symm fun _ => Iso.refl _
  rintro ⟨i, j⟩
  apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). Use `openCoverOfBase` instead. -/
@[simps! f]
/-
**AlgebraicGeometry.Scheme.Pullback.openCoverOfBase'** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：openCoverOfBase' (𝒰 : OpenCover.{v} Z) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover
.{v} (pullback f g)
参数：𝒰 : OpenCover.{v} Z；f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…

--- 原说明 ---
(Implementation). Use `openCoverOfBase` instead.
-/
def openCoverOfBase' (𝒰 : OpenCover.{v} Z) (f : X ⟶ Z) (g : Y ⟶ Z) :
    OpenCover.{v} (pullback f g) := by
  apply (openCoverOfLeft (𝒰.pullback₁ f) f g).bind
  intro i
  haveI := ((IsPullback.of_hasPullback (pullback.snd g (𝒰.f i))
    (pullback.snd f (𝒰.f i))).paste_horiz (IsPullback.of_hasPullback _ _)).flip
  refine
    @coverOfIsIso _ _ _ _ _
      (f := (pullbackSymmetry (pullback.snd f (𝒰.f i)) (pullback.snd g (𝒰.f i))).hom ≫
        (limit.isoLimitCone ⟨_, this.isLimit⟩).inv ≫
        pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) ?_ ?_) inferInstance
  · simp [← pullback.condition]
  · simp only [Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Given an open cover `{ Zᵢ }` of `Z`, then `X ×[Z] Y` is covered by `Xᵢ ×[Zᵢ] Yᵢ`, where
  `Xᵢ = X ×[Z] Zᵢ` and `Yᵢ = Y ×[Z] Zᵢ` is the preimage of `Zᵢ` in `X` and `Y`. -/
@[simps! I₀ X f]
/-
**AlgebraicGeometry.Scheme.Pullback.openCoverOfBase** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Pullback`。
形式化陈述：openCoverOfBase (𝒰 : OpenCover.{v} Z) (f : X ⟶ Z) (g : Y ⟶ Z) : OpenCover.
{v} (pullback f g)
参数：𝒰 : OpenCover.{v} Z；f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given an open cover `{ Zᵢ }` of `Z`, then `X ×[Z] Y` is covered by `Xᵢ ×[Zᵢ] Yᵢ`
, where
  `Xᵢ = X ×[Z] Zᵢ` and `Yᵢ = Y ×[Z] Zᵢ` is the preimage of `Zᵢ` in `X` and `Y`.
-/
def openCoverOfBase (𝒰 : OpenCover.{v} Z) (f : X ⟶ Z) (g : Y ⟶ Z) :
    OpenCover.{v} (pullback f g) := by
  apply
    (openCoverOfBase' 𝒰 f g).copy 𝒰.I₀
      (fun i =>
        pullback (pullback.snd _ _ : pullback f (𝒰.f i) ⟶ _)
          (pullback.snd _ _ : pullback g (𝒰.f i) ⟶ _))
      (fun i =>
        pullback.map _ _ _ _ (pullback.fst _ _) (pullback.fst _ _) (𝒰.f i)
          pullback.condition.symm pullback.condition.symm)
      ((Equiv.prodPUnit 𝒰.I₀).symm.trans (Equiv.sigmaEquivProd 𝒰.I₀ PUnit).symm) fun _ => Iso.refl _
  intro i
  rw [Iso.refl_hom, Category.id_comp, openCoverOfBase'_f]
  ext : 1 <;>
  · simp only [limit.lift_π, PullbackCone.mk_π_app, Equiv.trans_apply, Category.assoc,
    limit.lift_π_assoc, cospan_left, Category.comp_id,
      limit.isoLimitCone_inv_π_assoc, PullbackCone.π_app_left, IsPullback.cone_fst,
      pullbackSymmetry_hom_comp_snd_assoc, limit.isoLimitCone_inv_π,
      PullbackCone.π_app_right, IsPullback.cone_snd, pullbackSymmetry_hom_comp_fst_assoc]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: generalize to covers in subcanonical topologies
open pullback in
attribute [local simp] condition condition_assoc in
/-
**AlgebraicGeometry.Scheme.Pullback._root_.AlgebraicGeometry.Scheme.isPullback_o
f_openCover** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.Scheme.isPullback_of_openCover
    {W : Scheme.{u}} (fWX : W ⟶ X) (fWY : W ⟶ Y) (fXZ : X ⟶ Z) (fYZ : Y ⟶ Z) (𝒰 : X.OpenCover)
    (H : ∀ i, IsPullback (𝒰.pullbackHom fWX i) ((𝒰.pullback₁ fWX).f i ≫ fWY) (𝒰.f i ≫ fXZ) fYZ) :
    IsPullback fWX fWY fXZ fYZ := by
  have h : fWX ≫ fXZ = fWY ≫ fYZ :=
    Scheme.Cover.hom_ext (𝒰.pullback₁ fWX) _ _ fun i ↦ by simpa using (H i).w
  suffices IsIso (lift fWX fWY h) from .of_iso_pullback ⟨h⟩ (asIso (lift _ _ h)) (by simp) (by simp)
  have H₁ (i : _) : IsIso ((openCoverOfLeft 𝒰 fXZ fYZ).pullbackHom (lift fWX fWY h) i) := by
    let f := map (𝒰.f i ≫ fXZ) fYZ fXZ fYZ (𝒰.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)
    have : IsPullback (fst (𝒰.f i ≫ fXZ) fYZ) f (𝒰.f i) (fst _ _) := by
      simpa [← IsPullback.paste_vert_iff (.of_hasPullback _ _), f] using .of_hasPullback _ _
    have H' : IsPullback (fst fWX (𝒰.f i)) (lift (snd _ _) (fst _ _ ≫ fWY) (by simp [← h]))
        (lift fWX fWY h) f := by
      rw [← IsPullback.paste_vert_iff this.flip (by ext <;> simp [f])]
      simpa using .of_hasPullback _ _
    convert! (inferInstance : IsIso (H'.isoPullback.inv ≫ (H i).isoPullback.hom))
    aesop (add simp [Iso.eq_inv_comp, Scheme.Cover.pullbackHom])
  exact MorphismProperty.of_zeroHypercover_target (P := .isomorphisms Scheme)
    (Scheme.Pullback.openCoverOfLeft 𝒰 fXZ fYZ) H₁

variable (f : X ⟶ Y) (𝒰 : OpenCover.{u} Y) (𝒱 : ∀ i, OpenCover.{w} ((𝒰.pullback₁ f).X i))

/--
Given `𝒰 i` covering `Y` and `𝒱 i j` covering `𝒰 i`, this is the open cover
`𝒱 i j₁ ×[𝒰 i] 𝒱 i j₂` ranging over all `i`, `j₁`, `j₂`.
-/
noncomputable
/-
**AlgebraicGeometry.Scheme.Pullback.diagonalCover** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme.Pullback`。
形式化陈述：diagonalCover : (pullback.diagonalObj f).OpenCover
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
-/
def diagonalCover : (pullback.diagonalObj f).OpenCover :=
  (openCoverOfBase 𝒰 f f).bind
    fun i ↦ openCoverOfLeftRight (𝒱 i) (𝒱 i) (𝒰.pullbackHom _ _) (𝒰.pullbackHom _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The image of `𝒱 i j₁ ×[𝒰 i] 𝒱 i j₂` in `diagonalCover` with `j₁ = j₂` -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Pullback.diagonalCoverDiagonalRange** 是 Mathlib 中的一个定
义，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：diagonalCoverDiagonalRange : (pullback.diagonalObj f).Opens
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
-/
def diagonalCoverDiagonalRange : (pullback.diagonalObj f).Opens :=
  ⨆ i : Σ i, (𝒱 i).I₀, ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.diagonalCover_map** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：diagonalCover_map (I) : (diagonalCover f 𝒰 𝒱).f I = pullback.map _ _ _ _ (
(𝒱 I.fst).f _ ≫ pullback.fst _ _) ((𝒱 I.fst).f _ ≫ pullback.fst _ _) (𝒰.f _) (by
 simp) (by simp)
参数：I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma diagonalCover_map (I) : (diagonalCover f 𝒰 𝒱).f I =
    pullback.map _ _ _ _
    ((𝒱 I.fst).f _ ≫ pullback.fst _ _) ((𝒱 I.fst).f _ ≫ pullback.fst _ _) (𝒰.f _)
    (by simp)
    (by simp) := by
  cases I
  ext1 <;> simp [diagonalCover, Cover.pullbackHom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction of the diagonal `X ⟶ X ×ₛ X` to `𝒱 i j ×[𝒰 i] 𝒱 i j` is the diagonal
`𝒱 i j ⟶ 𝒱 i j ×[𝒰 i] 𝒱 i j`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Pullback.diagonalRestrictIsoDiagonal** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：diagonalRestrictIsoDiagonal (i j) : Arrow.mk (pullback.diagonal f ∣_ ((dia
gonalCover f 𝒰 𝒱).f ⟨i, j, j⟩).opensRange) ≅ Arrow.mk (pullback.diagonal ((𝒱 i).
f j ≫ pullback.snd _ _))
参数：i j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
-/
def diagonalRestrictIsoDiagonal (i j) :
    Arrow.mk (pullback.diagonal f ∣_ ((diagonalCover f 𝒰 𝒱).f ⟨i, j, j⟩).opensRange) ≅
    Arrow.mk (pullback.diagonal ((𝒱 i).f j ≫ pullback.snd _ _)) := by
  refine (morphismRestrictOpensRange _ _).trans ?_
  refine Arrow.isoMk ?_ (Iso.refl _) ?_
  · exact pullback.congrHom rfl (diagonalCover_map _ _ _ _) ≪≫
      pullbackDiagonalMapIso _ _ _ _ ≪≫ (asIso (pullback.diagonal _)).symm
  have H : pullback.snd (pullback.diagonal f) ((diagonalCover f 𝒰 𝒱).f ⟨i, (j, j)⟩) ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
    rw [← cancel_mono ((𝒱 i).f _)]
    apply pullback.hom_ext
    · trans pullback.snd (pullback.diagonal f) ((diagonalCover f 𝒰 𝒱).f ⟨i, (j, j)⟩) ≫
        (diagonalCover f 𝒰 𝒱).f _ ≫ pullback.snd _ _
      · simp [diagonalCover_map]
      symm
      trans pullback.snd (pullback.diagonal f) ((diagonalCover f 𝒰 𝒱).f ⟨i, (j, j)⟩) ≫
        (diagonalCover f 𝒰 𝒱).f _ ≫ pullback.fst _ _
      · simp [diagonalCover_map]
      · rw [← pullback.condition_assoc, ← pullback.condition_assoc]
        simp
    · simp [pullback.condition, Cover.pullbackHom]
  dsimp [Cover.pullbackHom] at H ⊢
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    simp only [← Category.assoc, IsIso.comp_inv_eq]
    apply pullback.hom_ext <;> simp [H]
  · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
    simp only [← Category.assoc, IsIso.comp_inv_eq]
    apply pullback.hom_ext <;> simp [H]

end Pullback

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-
**AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X Y S X' Y' S' : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) (f' 
: X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X')   (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : Cate
goryTheory.CategoryStruct.comp f i₃ = CategoryTheory.CategoryStruct.comp i₁ f') 
  (e₂ : CategoryTheory.CategoryStruct.comp g i₃ = CategoryTheory.CategoryStruct.
comp i₂ g')   [AlgebraicGeometry.IsOpenImmersion i₁] [AlgebraicGeometry.IsOpenIm
mersion i₂] [CategoryTheory.Mono i₃],   AlgebraicGeometry.IsOpenImmersion (Categ
oryTheory.Limits.pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂)
参数：f : X ⟶ S；g : Y ⟶ S；f' : X' ⟶ S'；g' : Y' ⟶ S'；i₁ : X ⟶ X'；i₂ : Y ⟶ Y'；i₃ : S 
⟶ S'；e₁ : CategoryTheory.CategoryStruct.comp f i₃ = CategoryTheory.CategoryStruc
t.comp i₁ f'；e₂ : CategoryTheory.CategoryStruct.comp g i₃ = CategoryTheory.Categ
oryStruct.comp i₂ g'；CategoryTheory.Limits.pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback_map_eq_pullbackFstFstIso_inv`：pullback_ma
p_eq_pullbackFstFstIso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X'
 ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y')…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instSndScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
-/
instance Scheme.pullback_map_isOpenImmersion {X Y S X' Y' S' : Scheme}
    (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [IsOpenImmersion i₁] [IsOpenImmersion i₂] [Mono i₃] :
    IsOpenImmersion (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) := by
  rw [pullback_map_eq_pullbackFstFstIso_inv]
  infer_instance

section CartesianMonoidalCategory
variable {S : Scheme}

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CartesianMonoidalCategory (Over S) := Over.cartesianMonoidalCategory _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory (Over S) := .ofCartesianMonoidalCategory

end CartesianMonoidalCategory

section Spec

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

open TensorProduct Algebra.TensorProduct CommRingCat RingHomClass

/-- The isomorphism between the fibred product of two schemes `Spec S` and `Spec T`
over a scheme `Spec R` and the `Spec` of the tensor product `S ⊗[R] T`. -/
noncomputable
/-
**AlgebraicGeometry.pullbackSpecIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
`。
形式化陈述：pullbackSpecIso : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
 (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅ Spec (.of <| S otimes[R] T)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pullbackSpecIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅ Spec (.of <| S ⊗[R] T) :=
  letI H := IsLimit.equivIsoLimit (PullbackCone.eta _)
    (PushoutCocone.isColimitEquivIsLimitOp _ (CommRingCat.pushoutCoconeIsColimit R S T))
  limit.isoLimitCone ⟨_, isLimitPullbackConeMapOfIsLimit Scheme.Spec _ H⟩

/--
The composition of the inverse of the isomorphism `pullbackSpecIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the first projection is
the morphism `Spec (S ⊗[R] T) ⟶ Spec S` obtained by applying `Spec.map` to the ring morphism
`s ↦ s ⊗ₜ[R] 1`.
-/
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.pullbackSpecIso_inv_fst** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：pullbackSpecIso_inv_fst : (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ =
 Spec.map (ofHom includeLeftRingHom)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…

--- 原说明 ---
The composition of the inverse of the isomorphism `pullbackSpecIso R S T` (from 
the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the first pro
jection is
the morphism `Spec (S ⊗[R] T) ⟶ Spec S` obtained by applying `Spec.map` to the r
ing morphism
`s ↦ s ⊗ₜ[R] 1`.
-/
lemma pullbackSpecIso_inv_fst :
    (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ = Spec.map (ofHom includeLeftRingHom) :=
  limit.isoLimitCone_inv_π _ _

@[reassoc]
/-
**AlgebraicGeometry.pullbackSpecIso_inv_fst'** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：pullbackSpecIso_inv_fst' : (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ 
= Spec.map (ofHom (algebraMap S _))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.pullbackSpecIso_inv_fst`：pullbackSpecIso_inv_fst : (pu
llbackSpecIso R S T).inv ≫ pullback.fst _ _ = Spec.map (ofHom includeLeftRingHom
)
-/
lemma pullbackSpecIso_inv_fst' :
    (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ = Spec.map (ofHom (algebraMap S _)) :=
  pullbackSpecIso_inv_fst ..

/--
The composition of the inverse of the isomorphism `pullbackSpecIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the second projection is
the morphism `Spec (S ⊗[R] T) ⟶ Spec T` obtained by applying `Spec.map` to the ring morphism
`t ↦ 1 ⊗ₜ[R] t`.
-/
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.pullbackSpecIso_inv_snd** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：pullbackSpecIso_inv_snd : (pullbackSpecIso R S T).inv ≫ pullback.snd _ _ =
 Spec.map (ofHom (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…

--- 原说明 ---
The composition of the inverse of the isomorphism `pullbackSpecIso R S T` (from 
the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the second pr
ojection is
the morphism `Spec (S ⊗[R] T) ⟶ Spec T` obtained by applying `Spec.map` to the r
ing morphism
`t ↦ 1 ⊗ₜ[R] t`.
-/
lemma pullbackSpecIso_inv_snd :
    (pullbackSpecIso R S T).inv ≫ pullback.snd _ _ =
      Spec.map (ofHom (R := T) (S := S ⊗[R] T) (toRingHom includeRight)) :=
  limit.isoLimitCone_inv_π _ _

/--
The composition of the isomorphism `pullbackSpecIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the morphism
`Spec (S ⊗[R] T) ⟶ Spec S` obtained by applying `Spec.map` to the ring morphism `s ↦ s ⊗ₜ[R] 1`
is the first projection.
-/
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.pullbackSpecIso_hom_fst** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：pullbackSpecIso_hom_fst : (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom in
cludeLeftRingHom) = pullback.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.pullbackSpecIso_inv_fst`：pullbackSpecIso_inv_fst : (pu
llbackSpecIso R S T).inv ≫ pullback.fst _ _ = Spec.map (ofHom includeLeftRingHom
)
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …

--- 原说明 ---
The composition of the isomorphism `pullbackSpecIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the morphism
`Spec (S ⊗[R] T) ⟶ Spec S` obtained by applying `Spec.map` to the ring morphism 
`s ↦ s ⊗ₜ[R] 1`
is the first projection.
-/
lemma pullbackSpecIso_hom_fst :
    (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom includeLeftRingHom) = pullback.fst _ _ := by
  rw [← pullbackSpecIso_inv_fst, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.pullbackSpecIso_hom_fst'** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：pullbackSpecIso_hom_fst' : (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom (
algebraMap S _)) = pullback.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.pullbackSpecIso_hom_fst`：pullbackSpecIso_hom_fst : (pu
llbackSpecIso R S T).hom ≫ Spec.map (ofHom includeLeftRingHom) = pullback.fst _ 
_
-/
lemma pullbackSpecIso_hom_fst' :
    (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom (algebraMap S _)) = pullback.fst _ _ :=
  pullbackSpecIso_hom_fst ..

/--
The composition of the isomorphism `pullbackSpecIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the morphism
`Spec (S ⊗[R] T) ⟶ Spec T` obtained by applying `Spec.map` to the ring morphism `t ↦ 1 ⊗ₜ[R] t`
is the second projection.
-/
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.pullbackSpecIso_hom_snd** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：pullbackSpecIso_hom_snd : (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom (t
oRingHom includeRight)) = pullback.snd _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.pullbackSpecIso_inv_snd`：pullbackSpecIso_inv_snd : (pu
llbackSpecIso R S T).inv ≫ pullback.snd _ _ = Spec.map (ofHom (R
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …

--- 原说明 ---
The composition of the isomorphism `pullbackSpecIso R S T` (from the pullback of
`Spec S ⟶ Spec R` and `Spec T ⟶ Spec R` to `Spec (S ⊗[R] T)`) with the morphism
`Spec (S ⊗[R] T) ⟶ Spec T` obtained by applying `Spec.map` to the ring morphism 
`t ↦ 1 ⊗ₜ[R] t`
is the second projection.
-/
lemma pullbackSpecIso_hom_snd :
    (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom (toRingHom includeRight)) = pullback.snd _ _ := by
  rw [← pullbackSpecIso_inv_snd, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.pullbackSpecIso_hom_base** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：pullbackSpecIso_hom_base : (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom (
algebraMap R _)) = pullback.fst _ _ ≫ Spec.map (ofHom (algebraMap _ _))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `AlgebraicGeometry.pullbackSpecIso_hom_fst_assoc`：∀ (R S T : Type u) [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T] [inst_3 : Algebra R 
S]   [inst_4 : Algebra R T] {Z : Alge…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackSpecIso_hom_base :
    (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom (algebraMap R _)) =
      pullback.fst _ _ ≫ Spec.map (ofHom (algebraMap _ _)) := by
  simp [Algebra.TensorProduct.algebraMap_def]
/-
**AlgebraicGeometry.isPullback_SpecMap_of_isPushout** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：isPullback_SpecMap_of_isPushout {A B C P : CommRingCat} (f : A ⟶ B) (g : A
 ⟶ C) (inl : B ⟶ P) (inr : C ⟶ P) (h : IsPushout f g inl inr) : IsPullback (Spec
.map inl) (Spec.map inr) (Spec.map f) (Spec.map g)
参数：f : A ⟶ B；g : A ⟶ C；inl : B ⟶ P；inr : C ⟶ P；h : IsPushout f g inl inr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPushout.op`：op (h : IsPushout f g inl inr) : IsPullback
 inr.op inl.op g.op f.op
-/
lemma isPullback_SpecMap_of_isPushout {A B C P : CommRingCat} (f : A ⟶ B) (g : A ⟶ C)
    (inl : B ⟶ P) (inr : C ⟶ P) (h : IsPushout f g inl inr) :
    IsPullback (Spec.map inl) (Spec.map inr) (Spec.map f) (Spec.map g) :=
  IsPullback.map Scheme.Spec h.op.flip
/-
**AlgebraicGeometry.isPullback_SpecMap_pushout** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry`。
形式化陈述：isPullback_SpecMap_pushout {A B C : CommRingCat} (f : A ⟶ B) (g : A ⟶ C) :
 IsPullback (Spec.map (pushout.inl f g)) (Spec.map (pushout.inr f g)) (Spec.map 
f) (Spec.map g)
参数：f : A ⟶ B；g : A ⟶ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.isPullback_SpecMap_of_isPushout`：isPullback_SpecMap_of
_isPushout {A B C P : CommRingCat} (f : A ⟶ B) (g : A ⟶ C) (inl : B ⟶ P) (inr : 
C ⟶ P) (h : IsPushout f g inl inr) : Is…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
-/
lemma isPullback_SpecMap_pushout {A B C : CommRingCat} (f : A ⟶ B) (g : A ⟶ C) :
    IsPullback (Spec.map (pushout.inl f g))
      (Spec.map (pushout.inr f g)) (Spec.map f) (Spec.map g) := by
  apply isPullback_SpecMap_of_isPushout
  exact IsPushout.of_hasPushout f g
/-
**AlgebraicGeometry.diagonal_SpecMap** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：diagonal_SpecMap : pullback.diagonal (Spec.map (CommRingCat.ofHom (algebra
Map R S))) = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R : S otim
es[R] S ->ₐ[R] S).toRingHom) ≫ (pullbackSpecIso R S S).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.pullbackSpecIso_inv_fst`：pullbackSpecIso_inv_fst : (pu
llbackSpecIso R S T).inv ≫ pullback.fst _ _ = Spec.map (ofHom includeLeftRingHom
)
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用引理 `AlgebraicGeometry.pullbackSpecIso_inv_snd`：pullbackSpecIso_inv_snd : (pu
llbackSpecIso R S T).inv ≫ pullback.snd _ _ = Spec.map (ofHom (R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma diagonal_SpecMap :
    pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom) ≫
        (pullbackSpecIso R S S).inv := by
  ext1 <;> simp only [pullback.diagonal_fst, pullback.diagonal_snd, ← Spec.map_comp, ← Spec.map_id,
    AlgHom.toRingHom_eq_coe, Category.assoc, pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd]
  · congr 1; ext x; change x = Algebra.TensorProduct.lmul' R (S := S) (x ⊗ₜ[R] 1); simp
  · congr 1; ext x; change x = Algebra.TensorProduct.lmul' R (S := S) (1 ⊗ₜ[R] x); simp

end Spec

namespace Scheme
variable {M S T : Scheme.{u}} [M.Over S] {f : T ⟶ S}

@[simps]
/-
**AlgebraicGeometry.Scheme.canonicallyOverPullback** 是 Mathlib 中的一个实例，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：canonicallyOverPullback : (pullback (M ↘ S) f).CanonicallyOver T where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance canonicallyOverPullback : (pullback (M ↘ S) f).CanonicallyOver T where
  hom := pullback.snd (M ↘ S) f

@[simps! -isSimp mul one]
/-
**AlgebraicGeometry.Scheme.monObjAsOverPullback** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：monObjAsOverPullback [MonObj (asOver M S)] : MonObj (asOver (pullback (M ↘
 S) f) T)
参数：asOver M S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
-/
instance monObjAsOverPullback [MonObj (asOver M S)] : MonObj (asOver (pullback (M ↘ S) f) T) := by
  unfold asOver OverClass.asOver at *; exact Over.monObjMkPullbackSnd
/-
**AlgebraicGeometry.Scheme.isCommMonObj_asOver_pullback** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：isCommMonObj_asOver_pullback [MonObj (asOver M S)] [IsCommMonObj (asOver M
 S)] : IsCommMonObj (asOver (pullback (M ↘ S) f) T)
参数：asOver M S；asOver M S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
-/
instance isCommMonObj_asOver_pullback [MonObj (asOver M S)] [IsCommMonObj (asOver M S)] :
    IsCommMonObj (asOver (pullback (M ↘ S) f) T) := by
  unfold asOver OverClass.asOver at *; exact Over.isCommMonObj_mk_pullbackSnd
/-
**AlgebraicGeometry.Scheme.GrpObjAsOverPullback** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：GrpObjAsOverPullback [GrpObj (asOver M S)] : GrpObj (asOver (pullback (M ↘
 S) f) T)
参数：asOver M S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
-/
instance GrpObjAsOverPullback [GrpObj (asOver M S)] : GrpObj (asOver (pullback (M ↘ S) f) T) := by
  unfold asOver OverClass.asOver at *; exact Over.grpObjMkPullbackSnd
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pullback.fst (M ↘ S) (𝟙 S)).IsOver S := ⟨pullback.condition.trans (by simp)⟩
/-
**AlgebraicGeometry.Scheme.isMonHom_fst_id_right** 是 Mathlib 中的一个实例，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：isMonHom_fst_id_right [MonObj (asOver M S)] : IsMonHom ((pullback.fst (M ↘
 S) (𝟙 S)).asOver S)
参数：asOver M S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.instIsOverFstOverInferInstanceOverClassId`：∀ {M
 S : AlgebraicGeometry.Scheme} [inst : M.Over S],   AlgebraicGeometry.Scheme.Hom
.IsOver (CategoryTheory.Limits.pullback.fst (M ↘ S) (Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
-/
instance isMonHom_fst_id_right [MonObj (asOver M S)] :
    IsMonHom ((pullback.fst (M ↘ S) (𝟙 S)).asOver S) := by
  unfold asOver OverClass.asOver at *; exact Over.isMonHom_pullbackFst_id_right

end AlgebraicGeometry.Scheme

