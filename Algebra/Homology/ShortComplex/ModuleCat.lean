/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Homology and exactness of short complexes of modules

In this file, the homology of a short complex `S` of abelian groups is identified
with the quotient of `LinearMap.ker S.g` by the image of the morphism
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`.

-/

@[expose] public section

universe v u

variable {R : Type u} [Ring R]

namespace CategoryTheory

open Limits

namespace ShortComplex

/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (forget₂ (ModuleCat.{v} R) Ab).PreservesHomology where

/-- Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
linear maps `f` and `g` and the vanishing of their composition. -/
@[simps]
/-
**CategoryTheory.ShortComplex.moduleCatMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ShortComplex`。
形式化陈述：moduleCatMk {X₁ X₂ X₃ : Type v} [AddCommGroup X₁] [AddCommGroup X₂] [AddCo
mmGroup X₃] [Module R X₁] [Module R X₂] [Module R X₃] (f : X₁ ->ₗ[R] X₂) (g : X₂
 ->ₗ[R] X₃) (hfg : g.comp f = 0) : ShortComplex (ModuleCat.{v} R)
参数：f : X₁ ->ₗ[R] X₂；g : X₂ ->ₗ[R] X₃；hfg : g.comp f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
linear maps `f` and `g` and the vanishing of their composition.
-/
def moduleCatMk {X₁ X₂ X₃ : Type v} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    [Module R X₁] [Module R X₂] [Module R X₃] (f : X₁ →ₗ[R] X₂) (g : X₂ →ₗ[R] X₃)
    (hfg : g.comp f = 0) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.hom_ext hfg)

variable (S : ShortComplex (ModuleCat.{v} R))

@[simp]
/-
**CategoryTheory.ShortComplex.moduleCat_zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：moduleCat_zero_apply (x : S.X₁) : S.g (S.f x) = 0
参数：x : S.X₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero_apply`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (
X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `ModuleCat.forget₂_addCommGrp_additive`：∀ {R : Type u} [inst : Ring R], (
CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat).Additive
-/
lemma moduleCat_zero_apply (x : S.X₁) : S.g (S.f x) = 0 :=
  S.zero_apply x
/-
**CategoryTheory.ShortComplex.moduleCat_exact_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：moduleCat_exact_iff : S.Exact ↔ forall (x₂ : S.X₂) (_ : S.g x₂ = 0), exist
s (x₁ : S.X₁), S.f x₁ = x₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_hasForget`：exact_iff_of_hasForg
et [S.HasHomology] : S.Exact ↔ forall (x₂ : (forget₂ C Ab).obj S.X₂) (_ : ((forg
et₂ C Ab).map S.g) x₂ = 0), exists (x₁ :…
· 使用定理 `ModuleCat.forget₂_addCommGrp_additive`：∀ {R : Type u} [inst : Ring R], (
CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat).Additive
· 使用定理 `CategoryTheory.ShortComplex.instPreservesHomologyModuleCatAbForget₂Linea
rMapIdCarrierAddMonoidHomCarrier`：∀ {R : Type u} [inst : Ring R], (CategoryTheor
y.forget₂ (ModuleCat R) Ab).PreservesHomology
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma moduleCat_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
  S.exact_iff_of_hasForget
/-
**CategoryTheory.ShortComplex.moduleCat_exact_iff_ker_sub_range** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：moduleCat_exact_iff_ker_sub_range : S.Exact ↔ LinearMap.ker S.g.hom <= Lin
earMap.range S.f.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.moduleCat_exact_iff`：moduleCat_exact_iff : S
.Exact ↔ forall (x₂ : S.X₂) (_ : S.g x₂ = 0), exists (x₁ : S.X₁), S.f x₁ = x₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma moduleCat_exact_iff_ker_sub_range :
    S.Exact ↔ LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom := by
  rw [moduleCat_exact_iff]
  aesop
/-
**CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：moduleCat_exact_iff_range_eq_ker : S.Exact ↔ LinearMap.range S.f.hom = Lin
earMap.ker S.g.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.moduleCat_exact_iff_ker_sub_range`：moduleCat
_exact_iff_ker_sub_range : S.Exact ↔ LinearMap.ker S.g.hom <= LinearMap.range S.
f.hom
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ShortComplex.moduleCat_zero_apply`：moduleCat_zero_apply (
x : S.X₁) : S.g (S.f x) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma moduleCat_exact_iff_range_eq_ker :
    S.Exact ↔ LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  rw [moduleCat_exact_iff_ker_sub_range]
  aesop

variable {S}
/-
**CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {S : CategoryTheory.ShortComplex (ModuleCat
 R)},   S.Exact → (ModuleCat.Hom.hom S.f).range = (ModuleCat.Hom.hom S.g).ker
参数：ModuleCat R；ModuleCat.Hom.hom S.f；ModuleCat.Hom.hom S.g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Exact.moduleCat_range_eq_ker (hS : S.Exact) :
    LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hS
/-
**CategoryTheory.ShortComplex.ShortExact.moduleCat_injective_f** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {S : CategoryTheory.ShortComplex (ModuleCat
 R)},   S.ShortExact → Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom 
S.f)
参数：ModuleCat R；CategoryTheory.ConcreteCategory.hom S.f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.injective_f`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}  
 [inst_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `ModuleCat.forget₂_addCommGrp_additive`：∀ {R : Type u} [inst : Ring R], (
CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat).Additive
· 使用定理 `CategoryTheory.ShortComplex.instPreservesHomologyModuleCatAbForget₂Linea
rMapIdCarrierAddMonoidHomCarrier`：∀ {R : Type u} [inst : Ring R], (CategoryTheor
y.forget₂ (ModuleCat R) Ab).PreservesHomology
· 使用定理 `ModuleCat.instHasZeroObject`：∀ {R : Type u} [inst : Ring R], CategoryThe
ory.Limits.HasZeroObject (ModuleCat R)
-/
lemma ShortExact.moduleCat_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  hS.injective_f
/-
**CategoryTheory.ShortComplex.ShortExact.moduleCat_surjective_g** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {S : CategoryTheory.ShortComplex (ModuleCat
 R)},   S.ShortExact → Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom
 S.g)
参数：ModuleCat R；CategoryTheory.ConcreteCategory.hom S.g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.surjective_g`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w} 
  [inst_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `ModuleCat.forget₂_addCommGrp_additive`：∀ {R : Type u} [inst : Ring R], (
CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat).Additive
· 使用定理 `CategoryTheory.ShortComplex.instPreservesHomologyModuleCatAbForget₂Linea
rMapIdCarrierAddMonoidHomCarrier`：∀ {R : Type u} [inst : Ring R], (CategoryTheor
y.forget₂ (ModuleCat R) Ab).PreservesHomology
· 使用定理 `ModuleCat.instHasZeroObject`：∀ {R : Type u} [inst : Ring R], CategoryThe
ory.Limits.HasZeroObject (ModuleCat R)
-/
lemma ShortExact.moduleCat_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  hS.surjective_g

variable (S)
/-
**CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat
 R)),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory.hom S.f) ⇑(Ca
tegoryTheory.ConcreteCategory.hom S.g)
参数：S : CategoryTheory.ShortComplex (ModuleCat R)；CategoryTheory.ConcreteCategory
.hom S.f；CategoryTheory.ConcreteCategory.hom S.g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker`：moduleCat_
exact_iff_range_eq_ker : S.Exact ↔ LinearMap.range S.f.hom = LinearMap.ker S.g.h
om
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ShortExact.moduleCat_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [moduleCat_exact_iff_range_eq_ker, LinearMap.exact_iff]
  tauto

/-- Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
morphisms `f` and `g` and the assumption `LinearMap.range f ≤ LinearMap.ker g`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.moduleCatMkOfKerLERange** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ShortComplex`。
形式化陈述：moduleCatMkOfKerLERange {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂
 ⟶ X₃) (hfg : LinearMap.range f.hom <= LinearMap.ker g.hom) : ShortComplex (Modu
leCat.{v} R)
参数：f : X₁ ⟶ X₂；g : X₂ ⟶ X₃；hfg : LinearMap.range f.hom <= LinearMap.ker g.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
morphisms `f` and `g` and the assumption `LinearMap.range f ≤ LinearMap.ker g`.
-/
def moduleCatMkOfKerLERange {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hfg : LinearMap.range f.hom ≤ LinearMap.ker g.hom) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk f g (by aesop)
/-
**CategoryTheory.ShortComplex.Exact.moduleCat_of_range_eq_ker** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ShortComplex.Exact`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {X₁ X₂ X₃ : ModuleCat R} (f : X₁ ⟶ X₂) (g :
 X₂ ⟶ X₃)   (hfg : (ModuleCat.Hom.hom f).range = (ModuleCat.Hom.hom g).ker),   (
CategoryTheory.ShortComplex.moduleCatMkOfKerLERange f g ⋯).Exact
参数：f : X₁ ⟶ X₂；g : X₂ ⟶ X₃；hfg : (ModuleCat.Hom.hom f).range = (ModuleCat.Hom.ho
m g).ker；CategoryTheory.ShortComplex.moduleCatMkOfKerLERange f g ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Exact.moduleCat_of_range_eq_ker {X₁ X₂ X₃ : ModuleCat.{v} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : LinearMap.range f.hom = LinearMap.ker g.hom) :
    (moduleCatMkOfKerLERange f g (by rw [hfg])).Exact := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using! hfg

/-- The canonical linear map `S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`. -/
/-
**CategoryTheory.ShortComplex.moduleCatToCycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：moduleCatToCycles : S.X₁ ->ₗ[R] LinearMap.ker S.g.hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.moduleCat_zero_apply`：moduleCat_zero_apply (
x : S.X₁) : S.g (S.f x) = 0

--- 原说明 ---
The canonical linear map `S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`.
-/
abbrev moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g.hom :=
  S.f.hom.codRestrict _ <| S.moduleCat_zero_apply

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit left homology data of a short complex of modules that is
given by a kernel and a quotient given by the `LinearMap` API. The projections to `K` and `H` are
not simp lemmas because the generic lemmas about `LeftHomologyData` are more useful here. -/
@[simps! K H i_hom π_hom]
/-
**CategoryTheory.ShortComplex.moduleCatLeftHomologyData** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：moduleCatLeftHomologyData : S.LeftHomologyData where K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit left homology data of a short complex of modules that is
given by a kernel and a quotient given by the `LinearMap` API. The projections t
o `K` and `H` are
not simp lemmas because the generic lemmas about `LeftHomologyData` are more use
ful here.
-/
def moduleCatLeftHomologyData : S.LeftHomologyData where
  K := ModuleCat.of R (LinearMap.ker S.g.hom)
  H := ModuleCat.of R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
  i := ModuleCat.ofHom (LinearMap.ker S.g.hom).subtype
  π := ModuleCat.ofHom (LinearMap.range S.moduleCatToCycles).mkQ
  wi := by aesop
  hi := ModuleCat.kernelIsLimit _
  wπ := by aesop
  hπ := ModuleCat.cokernelIsColimit (ModuleCat.ofHom S.moduleCatToCycles)

@[simp]
/-
**CategoryTheory.ShortComplex.moduleCatLeftHomologyData_f'_hom** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat
 R)),   ModuleCat.Hom.hom S.moduleCatLeftHomologyData.f' = S.moduleCatToCycles
参数：S : CategoryTheory.ShortComplex (ModuleCat R)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma moduleCatLeftHomologyData_f'_hom :
    S.moduleCatLeftHomologyData.f'.hom = S.moduleCatToCycles := rfl

@[simp]
/-
**CategoryTheory.ShortComplex.moduleCatLeftHomologyData_descH_hom** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：moduleCatLeftHomologyData_descH_hom {M : ModuleCat R} (φ : S.moduleCatLeft
HomologyData.K ⟶ M) (h : S.moduleCatLeftHomologyData.f' ≫ φ = 0) : (S.moduleCatL
eftHomologyData.descH φ h).hom = (LinearMap.range <| ModuleCat.Hom.hom _).liftQ 
φ.hom (LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.1 h)
参数：φ : S.moduleCatLeftHomologyData.K ⟶ M；h : S.moduleCatLeftHomologyData.f' ≫ φ 
= 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma moduleCatLeftHomologyData_descH_hom {M : ModuleCat R}
    (φ : S.moduleCatLeftHomologyData.K ⟶ M) (h : S.moduleCatLeftHomologyData.f' ≫ φ = 0) :
    (S.moduleCatLeftHomologyData.descH φ h).hom =
      (LinearMap.range <| ModuleCat.Hom.hom _).liftQ
         φ.hom (LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.1 h) := rfl

@[simp]
/-
**CategoryTheory.ShortComplex.moduleCatLeftHomologyData_liftK_hom** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：moduleCatLeftHomologyData_liftK_hom {M : ModuleCat R} (φ : M ⟶ S.X₂) (h : 
φ ≫ S.g = 0) : (S.moduleCatLeftHomologyData.liftK φ h).hom = φ.hom.codRestrict (
LinearMap.ker S.g.hom) (fun m => congr($h m))
参数：φ : M ⟶ S.X₂；h : φ ≫ S.g = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma moduleCatLeftHomologyData_liftK_hom {M : ModuleCat R} (φ : M ⟶ S.X₂) (h : φ ≫ S.g = 0) :
    (S.moduleCatLeftHomologyData.liftK φ h).hom =
      φ.hom.codRestrict (LinearMap.ker S.g.hom) (fun m => congr($h m)) := rfl

/-- Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.cycles` of the homology API and the more concrete description as
`LinearMap.ker S.g`. -/
/-
**CategoryTheory.ShortComplex.moduleCatCyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：moduleCatCyclesIso : S.cycles ≅ S.moduleCatLeftHomologyData.K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.cycles` of the homology API and the more concrete description as
`LinearMap.ker S.g`.
-/
noncomputable def moduleCatCyclesIso : S.cycles ≅ S.moduleCatLeftHomologyData.K :=
  S.moduleCatLeftHomologyData.cyclesIso

@[reassoc (attr := simp, elementwise)]
/-
**CategoryTheory.ShortComplex.moduleCatCyclesIso_hom_i** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：moduleCatCyclesIso_hom_i : S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomol
ogyData.i = S.iCycles
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i`：cycle
sIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma moduleCatCyclesIso_hom_i :
    S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.i = S.iCycles :=
  S.moduleCatLeftHomologyData.cyclesIso_hom_comp_i

@[reassoc (attr := simp, elementwise)]
/-
**CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_iCycles** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：moduleCatCyclesIso_inv_iCycles : S.moduleCatCyclesIso.inv ≫ S.iCycles = S.
moduleCatLeftHomologyData.i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles`
：cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma moduleCatCyclesIso_inv_iCycles :
    S.moduleCatCyclesIso.inv ≫ S.iCycles = S.moduleCatLeftHomologyData.i :=
  S.moduleCatLeftHomologyData.cyclesIso_inv_comp_iCycles

@[reassoc (attr := simp, elementwise)]
/-
**CategoryTheory.ShortComplex.toCycles_moduleCatCyclesIso_hom** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：toCycles_moduleCatCyclesIso_hom : S.toCycles ≫ S.moduleCatCyclesIso.hom = 
S.moduleCatLeftHomologyData.f'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instMonoI`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.moduleCatCyclesIso_hom_i`：moduleCatCyclesIso
_hom_i : S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.i = S.iCycles
· 使用引理 `CategoryTheory.ShortComplex.toCycles_i`：toCycles_i : S.toCycles ≫ S.iCyc
les = S.f
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.f'_i`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C]   {S : CategoryTheory.Sho…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toCycles_moduleCatCyclesIso_hom :
    S.toCycles ≫ S.moduleCatCyclesIso.hom = S.moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono S.moduleCatLeftHomologyData.i]

/-- Given a short complex `S` of modules, this is the isomorphism between the abstract `S.opcycles`
of the homology API and the more concrete description as `S.X₂ ⧸ LinearMap.range S.f.hom`. -/
/-
**CategoryTheory.ShortComplex.moduleCatOpcyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：moduleCatOpcyclesIso : S.opcycles ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range
 S.f.hom)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a short complex `S` of modules, this is the isomorphism between the abstra
ct `S.opcycles`
of the homology API and the more concrete description as `S.X₂ ⧸ LinearMap.range
 S.f.hom`.
-/
noncomputable def moduleCatOpcyclesIso :
    S.opcycles ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  S.opcyclesIsoCokernel ≪≫ ModuleCat.cokernelIsoRangeQuotient _

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：pOpcycles_comp_moduleCatOpcyclesIso_hom : S.pOpcycles ≫ S.moduleCatOpcycle
sIso.hom = ModuleCat.ofHom (Submodule.mkQ _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.opcyclesIsoCokernel_hom`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.p_descOpcycles_assoc`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C]   (S : CategoryTheory.Sho…
· 使用定理 `ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom`：cokernel_π_cokernelIs
oRangeQuotient_hom : cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = ofHom (Li
nearMap.range f.hom).mkQ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pOpcycles_comp_moduleCatOpcyclesIso_hom :
    S.pOpcycles ≫ S.moduleCatOpcyclesIso.hom = ModuleCat.ofHom (Submodule.mkQ _) := by
  simp [moduleCatOpcyclesIso]
/-
**CategoryTheory.ShortComplex.moduleCat_pOpcycles_eq_iff** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex`。
形式化陈述：moduleCat_pOpcycles_eq_iff (x y : S.X₂) : S.pOpcycles x = S.pOpcycles y ↔ 
x - y in LinearMap.range S.f.hom
参数：x y : S.X₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom_appl
y`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
) (x : ↑S.X₂),   (CategoryTheory.ConcreteCategory.hom S.moduleC…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inj
ective f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
-/
theorem moduleCat_pOpcycles_eq_iff (x y : S.X₂) :
    S.pOpcycles x = S.pOpcycles y ↔ x - y ∈ LinearMap.range S.f.hom :=
  Iff.trans ⟨fun h => by simpa using congr(S.moduleCatOpcyclesIso.hom $h),
    fun h => (ModuleCat.mono_iff_injective S.moduleCatOpcyclesIso.hom).1 inferInstance (by simpa)⟩
    (Submodule.Quotient.eq _)
/-
**CategoryTheory.ShortComplex.moduleCat_pOpcycles_eq_zero_iff** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：moduleCat_pOpcycles_eq_zero_iff (x : S.X₂) : S.pOpcycles x = 0 ↔ x in Line
arMap.range S.f.hom
参数：x : S.X₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `CategoryTheory.ShortComplex.moduleCat_pOpcycles_eq_iff`：moduleCat_pOpcyc
les_eq_iff (x y : S.X₂) : S.pOpcycles x = S.pOpcycles y ↔ x - y in LinearMap.ran
ge S.f.hom
-/
theorem moduleCat_pOpcycles_eq_zero_iff (x : S.X₂) :
    S.pOpcycles x = 0 ↔ x ∈ LinearMap.range S.f.hom := by
  simpa using moduleCat_pOpcycles_eq_iff _ x 0

/-- Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.homology` of the homology API and the more explicit
quotient of `LinearMap.ker S.g` by the image of
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g`. -/
/-
**CategoryTheory.ShortComplex.moduleCatHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：moduleCatHomologyIso : S.homology ≅ S.moduleCatLeftHomologyData.H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.homology` of the homology API and the more explicit
quotient of `LinearMap.ker S.g` by the image of
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g`.
-/
noncomputable def moduleCatHomologyIso :
    S.homology ≅ S.moduleCatLeftHomologyData.H :=
  S.moduleCatLeftHomologyData.homologyIso

@[reassoc (attr := simp, elementwise)]
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_moduleCatCyclesIso_hom :
    S.homologyπ ≫ S.moduleCatHomologyIso.hom =
      S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π :=
  S.moduleCatLeftHomologyData.homologyπ_comp_homologyIso_hom

@[reassoc (attr := simp, elementwise)]
/-
**CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma moduleCatCyclesIso_inv_π :
    S.moduleCatCyclesIso.inv ≫ S.homologyπ =
       S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv :=
  S.moduleCatLeftHomologyData.π_comp_homologyIso_inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ShortComplex.exact_iff_surjective_moduleCatToCycles** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_surjective_moduleCatToCycles : S.Exact ↔ Function.Surjective S.m
oduleCatToCycles
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff_epi_f'`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.P
readditive C]   {S : CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma exact_iff_surjective_moduleCatToCycles :
    S.Exact ↔ Function.Surjective S.moduleCatToCycles := by
  simp [S.moduleCatLeftHomologyData.exact_iff_epi_f',
    ModuleCat.epi_iff_surjective, moduleCatLeftHomologyData_K]

end ShortComplex

end CategoryTheory

section

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

open CategoryTheory

/-- Given a linear map `f : M → N`, we can obtain a short complex `0 → ker(f) → M → N`. -/
/-
**LinearMap.shortComplexKer** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearMap.shortComplexKer (f : M ->ₗ[R] N) : ShortComplex (ModuleCat.{v} R
) where f
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linear map `f : M → N`, we can obtain a short complex `0 → ker(f) → M → 
N`.
-/
abbrev LinearMap.shortComplexKer (f : M →ₗ[R] N) : ShortComplex (ModuleCat.{v} R) where
  f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
  g := ModuleCat.ofHom.{v} f
  zero := by ext; simp
/-
**LinearMap.shortExact_shortComplexKer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.shortExact_shortComplexKer {f : M ->ₗ[R] N} (h : Function.Surjec
tive f) : f.shortComplexKer.ShortExact where exact
参数：h : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ModuleCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inj
ective f
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
-/
theorem LinearMap.shortExact_shortComplexKer {f : M →ₗ[R] N} (h : Function.Surjective f) :
    f.shortComplexKer.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    fun _ ↦ by simp [shortComplexKer]
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker f).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr h

variable {L : Type v} [AddCommGroup L] [Module R L]

/-- The short complex in `ModuleCat` obtained from two linear map with composition equal to zero. -/
/-
**ModuleCat.shortComplexOfCompEqZero** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ModuleCat.shortComplexOfCompEqZero (f : M ->ₗ[R] N) (g : N ->ₗ[R] L) (eq0 
: g.comp f = 0) : ShortComplex (ModuleCat.{v} R) where f
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] L；eq0 : g.comp f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex in `ModuleCat` obtained from two linear map with composition e
qual to zero.
-/
abbrev ModuleCat.shortComplexOfCompEqZero (f : M →ₗ[R] N) (g : N →ₗ[R] L) (eq0 : g.comp f = 0) :
    ShortComplex (ModuleCat.{v} R) where
  f := ModuleCat.ofHom f
  g := ModuleCat.ofHom g
/-
**ModuleCat.shortComplex_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModuleCat.shortComplex_exact (S : ShortComplex (ModuleCat.{v} R)) (exac : 
Function.Exact S.f S.g) : S.Exact
参数：S : ShortComplex (ModuleCat.{v} R)；exac : Function.Exact S.f S.g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
-/
lemma ModuleCat.shortComplex_exact (S : ShortComplex (ModuleCat.{v} R))
    (exac : Function.Exact S.f S.g) : S.Exact :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
/-
**ModuleCat.shortComplex_shortExact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModuleCat.shortComplex_shortExact (S : ShortComplex (ModuleCat.{v} R)) (ex
ac : Function.Exact S.f S.g) (inj : Function.Injective S.f) (surj : Function.Sur
jective S.g) : S.ShortExact where exact
参数：S : ShortComplex (ModuleCat.{v} R)；exac : Function.Exact S.f S.g；inj : Functi
on.Injective S.f；surj : Function.Surjective S.g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
· 使用定理 `ModuleCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inj
ective f
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
-/
lemma ModuleCat.shortComplex_shortExact (S : ShortComplex (ModuleCat.{v} R))
    (exac : Function.Exact S.f S.g) (inj : Function.Injective S.f)
    (surj : Function.Surjective S.g) : S.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
  mono_f := (ModuleCat.mono_iff_injective _).mpr inj
  epi_g := (ModuleCat.epi_iff_surjective _).mpr surj

variable {M' N' L' : Type*} [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup L']
  [Module R M'] [Module R N'] [Module R L']

variable (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') (eL : L ≃ₗ[R] L') (f : M' →ₗ[R] N') (g : N' →ₗ[R] L')

/--
Suppose that `f` and `g` are linear maps that compose to zero, and that `eM`, `eN`, and `eL`
indicated in the diagram below are linear equivalences to modules that all belong to the same
universe. Then this is the short complex in `ModuleCat` given by the bottom row in the diagram.
M --f--> N --g--> L
|        |        |
eM       eN       eL
|        |        |
v        v        v
M'-----> N'-----> L'
This complex is exact when we have `Function.Exact f g`, see
`ModuleCat.shortComplexOfConj_exact`.
-/
/-
**ModuleCat.shortComplexOfConj** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ModuleCat.shortComplexOfConj (eq0 : g ∘ₗ f = 0) : ShortComplex (ModuleCat.
{v} R)
参数：eq0 : g ∘ₗ f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose that `f` and `g` are linear maps that compose to zero, and that `eM`, `e
N`, and `eL`
indicated in the diagram below are linear equivalences to modules that all belon
g to the same
universe. Then this is the short complex in `ModuleCat` given by the bottom row 
in the diagram.
M --f--> N --g--> L
|        |        |
eM       eN       eL
|        |        |
v        v        v
M'-----> N'-----> L'
This complex is exact when we have `Function.Exact f g`, see
`ModuleCat.shortComplexOfConj_exact`.
-/
abbrev ModuleCat.shortComplexOfConj (eq0 : g ∘ₗ f = 0) :
    ShortComplex (ModuleCat.{v} R) :=
  ModuleCat.shortComplexOfCompEqZero ((eN.symm.comp f).comp eM.toLinearMap)
    (eL.symm.comp (g.comp eN.toLinearMap)) (by
      ext x
      simpa using LinearMap.congr_fun eq0 (eM x))
/-
**exact_conj_of_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exact_conj_of_exact (exact : Function.Exact f g) : Function.Exact
    ((eN.symm.comp f).comp eM.toLinearMap) (eL.symm.comp (g.comp eN.toLinearMap)) := by
  rwa [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.postcomp_exact_iff_exact,
    LinearEquiv.conj_symm_exact_iff_exact]
/-
**ModuleCat.shortComplexOfConj_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModuleCat.shortComplexOfConj_exact (exact : Function.Exact f g) : (ModuleC
at.shortComplexOfConj eM eN eL f g exact.linearMap_comp_eq_zero).Exact
参数：exact : Function.Exact f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.shortComplex_exact`：ModuleCat.shortComplex_exact (S : ShortCom
plex (ModuleCat.{v} R)) (exac : Function.Exact S.f S.g) : S.Exact
· 使用定理 `Function.Exact.linearMap_comp_eq_zero`：∀ {R : Type u_1} {M : Type u_2} {
N : Type u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMonoid N] [i…
· 使用定理 `_private.Mathlib.Algebra.Homology.ShortComplex.ModuleCat.0.exact_conj_of
_exact`：∀ {R : Type u} [inst : Ring R] {M : Type v} [inst_1 : AddCommGroup M] [i
nst_2 : _root_.Module R M] {N : Type v}   [inst_3 : AddCommGroup N] …
-/
lemma ModuleCat.shortComplexOfConj_exact (exact : Function.Exact f g) :
    (ModuleCat.shortComplexOfConj eM eN eL f g exact.linearMap_comp_eq_zero).Exact :=
  ModuleCat.shortComplex_exact _ (exact_conj_of_exact eM eN eL f g exact)
/-
**ModuleCat.shortComplexOfConj_shortExact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModuleCat.shortComplexOfConj_shortExact (exact : Function.Exact f g) (inj 
: Function.Injective f) (surj : Function.Surjective g) : (ModuleCat.shortComplex
OfConj eM eN eL f g exact.linearMap_comp_eq_zero).ShortExact
参数：exact : Function.Exact f g；inj : Function.Injective f；surj : Function.Surject
ive g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.shortComplex_shortExact`：ModuleCat.shortComplex_shortExact (S 
: ShortComplex (ModuleCat.{v} R)) (exac : Function.Exact S.f S.g) (inj : Functio
n.Injective S.f) (surj …
· 使用定理 `Function.Exact.linearMap_comp_eq_zero`：∀ {R : Type u_1} {M : Type u_2} {
N : Type u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMonoid N] [i…
· 使用定理 `_private.Mathlib.Algebra.Homology.ShortComplex.ModuleCat.0.exact_conj_of
_exact`：∀ {R : Type u} [inst : Ring R] {M : Type v} [inst_1 : AddCommGroup M] [i
nst_2 : _root_.Module R M] {N : Type v}   [inst_3 : AddCommGroup N] …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
lemma ModuleCat.shortComplexOfConj_shortExact (exact : Function.Exact f g)
    (inj : Function.Injective f) (surj : Function.Surjective g) :
    (ModuleCat.shortComplexOfConj eM eN eL f g exact.linearMap_comp_eq_zero).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ (exact_conj_of_exact eM eN eL f g exact) ?_ ?_
  all_goals simpa

end

