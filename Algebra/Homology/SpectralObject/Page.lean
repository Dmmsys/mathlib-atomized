/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Cycles
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.ComposableArrows.Three

/-!
# Spectral objects in abelian categories

Let `X` be a spectral object index by the category `ι`
in the abelian category `C`. The purpose of this file
is to introduce the homology `X.E` of the short complex `X.shortComplex`
`(X.H n₀).obj (mk₁ f₃) ⟶ (X.H n₁).obj (mk₁ f₂) ⟶ (X.H n₂).obj (mk₁ f₁)`
when `f₁`, `f₂` and `f₃` are composable morphisms in `ι` and the
equalities `n₀ + 1 = n₁` and `n₁ + 1 = n₂` hold (both maps in the
short complex are given by `X.δ`). All the relevant objects in the
spectral sequence attached to spectral objects can be defined
in terms of this homology `X.E`: the objects in all pages, including
the page at infinity.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (n₀ n₁ n₂ : ℤ)

/-- The short complex consisting of the composition of
two morphisms `X.δ`, given three composable morphisms `f₁`, `f₂`
and `f₃` in `ι`, and three consecutive integers. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.shortComplex** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
形式化陈述：shortComplex (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex consisting of the composition of
two morphisms `X.δ`, given three composable morphisms `f₁`, `f₂`
and `f₃` in `ι`, and three consecutive integers.
-/
def shortComplex (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₂)
  X₃ := (X.H n₂).obj (mk₁ f₁)
  f := X.δ f₂ f₃ n₀ n₁
  g := X.δ f₁ f₂ n₁ n₂

/-- The homology of the short complex `shortComplex` consisting of
two morphisms `X.δ`. In the documentation, we shorten it as `E^n₁(f₁, f₂, f₃)` -/
/-
**CategoryTheory.Abelian.SpectralObject.E** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Abelian.SpectralObject`。
形式化陈述：E (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homology of the short complex `shortComplex` consisting of
two morphisms `X.δ`. In the documentation, we shorten it as `E^n₁(f₁, f₂, f₃)`
-/
noncomputable def E (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) : C :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homology
/-
**CategoryTheory.Abelian.SpectralObject.isZero_E_of_isZero_H** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：isZero_E_of_isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂))) (hn₁ : n₀ + 1 = 
n₁
参数：h : IsZero ((X.H n₁).obj (mk₁ f₂))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_isZero_homology`：exact_iff_isZero_
homology [S.HasHomology] : S.Exact ↔ IsZero S.homology
· 使用引理 `CategoryTheory.ShortComplex.exact_of_isZero_X₂`：exact_of_isZero_X₂ (h : 
IsZero S.X₂) : S.Exact
-/
lemma isZero_E_of_isZero_H (h : IsZero ((X.H n₁).obj (mk₁ f₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsZero (X.E f₁ f₂ f₃ n₀ n₁ n₂) :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).exact_iff_isZero_homology.1
    (ShortComplex.exact_of_isZero_X₂ _ h)

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  {i' j' k' l' : ι} (f₁' : i' ⟶ j') (f₂' : j' ⟶ k') (f₃' : k' ⟶ l')
  {i'' j'' k'' l'' : ι} (f₁'' : i'' ⟶ j'') (f₂'' : j'' ⟶ k'') (f₃'' : k'' ⟶ l'')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')
  (β : mk₃ f₁' f₂' f₃' ⟶ mk₃ f₁'' f₂'' f₃'')
  (γ : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁'' f₂'' f₃'')
  (n₀ n₁ n₂ : ℤ)

/-- The functoriality of `shortComplex` with respect to morphisms
in `ComposableArrows ι 3`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.shortComplexMap** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：shortComplexMap (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functoriality of `shortComplex` with respect to morphisms
in `ComposableArrows ι 3`.
-/
def shortComplexMap (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ ⟶
      X.shortComplex f₁' f₂' f₃' n₀ n₁ n₂ where
  τ₁ := (X.H n₀).map (homMk₁ (α.app 2) (α.app 3) (naturality' α 2 3))
  τ₂ := (X.H n₁).map (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2))
  τ₃ := (X.H n₂).map (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
  comm₁₂ := δ_naturality ..
  comm₂₃ := δ_naturality ..

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.shortComplexMap_id** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：shortComplexMap_id (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.hom_ext`：hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ 
= g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) : f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma shortComplexMap_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplexMap f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  ext
  all_goals dsimp; convert! (X.H _).map_id _; cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc, simp]
/-
**CategoryTheory.Abelian.SpectralObject.shortComplexMap_comp** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：shortComplexMap_comp (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.hom_ext`：hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ 
= g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma shortComplexMap_comp (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.shortComplexMap f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) n₀ n₁ n₂ hn₁ hn₂ =
    X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
      X.shortComplexMap f₁' f₂' f₃' f₁'' f₂'' f₃'' β n₀ n₁ n₂ hn₁ hn₂ := by
  ext
  all_goals dsimp; rw [← Functor.map_comp]; congr 1; cat_disch

/-- The functoriality of `E` with respect to morphisms
in `ComposableArrows ι 3`. -/
/-
**CategoryTheory.Abelian.SpectralObject.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Abelian.SpectralObject`。
形式化陈述：map (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functoriality of `E` with respect to morphisms
in `ComposableArrows ι 3`.
-/
noncomputable def map (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.E f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.homologyMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂)

@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.map_id** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Abelian.SpectralObject`。
形式化陈述：map_id (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Abelian.SpectralObject.shortComplexMap_id`：shortComplexMa
p_id (hn₁ : n₀ + 1 = n₁
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_id`：homologyMap_id [HasHomology 
S] : homologyMap (𝟙 S) = 𝟙 _
-/
lemma map_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁ f₂ f₃ (𝟙 _) n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  dsimp only [map]
  simp [shortComplexMap_id, ShortComplex.homologyMap_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, simp]
/-
**CategoryTheory.Abelian.SpectralObject.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Abelian.SpectralObject`。
形式化陈述：map_comp (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Abelian.SpectralObject.shortComplexMap_comp`：shortComplex
Map_comp (hn₁ : n₀ + 1 = n₁
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_comp`：homologyMap_comp [HasHomol
ogy S₁] [HasHomology S₂] [HasHomology S₃] (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) : homolo
gyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁'' f₂'' f₃'' (α ≫ β) n₀ n₁ n₂ hn₁ hn₂ =
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
      X.map f₁' f₂' f₃' f₁'' f₂'' f₃'' β n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp only [map]
  simp [shortComplexMap_comp, ShortComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.isIso_map** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
形式化陈述：isIso_map (h₀ : IsIso ((X.H n₀).map ((functorArrows ι 2 3 3).map α))) (h₁ 
: IsIso ((X.H n₁).map ((functorArrows ι 1 2 3).map α))) (h₂ : IsIso ((X.H n₂).ma
p ((functorArrows ι 0 1 3).map α))) (hn₁ : n₀ + 1 = n₁
参数：h₀ : IsIso ((X.H n₀).map ((functorArrows ι 2 3 3).map α))；h₁ : IsIso ((X.H n₁
).map ((functorArrows ι 1 2 3).map α))；h₂ : IsIso ((X.H n₂).map ((functorArrows 
ι 0 1 3).map α))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.isIso_of_isIso`：isIso_of_isIso (f : S₁ ⟶ S₂)
 [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃] : IsIso f
· 使用定理 `CategoryTheory.ShortComplex.QuasiIso.isIso`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {S₁ S₂ : CategoryTheory…
-/
lemma isIso_map
    (h₀ : IsIso ((X.H n₀).map ((functorArrows ι 2 3 3).map α)))
    (h₁ : IsIso ((X.H n₁).map ((functorArrows ι 1 2 3).map α)))
    (h₂ : IsIso ((X.H n₂).map ((functorArrows ι 0 1 3).map α)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) := by
  have : IsIso (shortComplexMap X f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂) := by
    apply +allowSynthFailures ShortComplex.isIso_of_isIso <;> assumption
  dsimp [map]
  infer_instance

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_eq_zero_of_isIso₁ (hf : IsIso f) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ = 0 := by
  simpa only [Preadditive.IsIso.comp_left_eq_zero] using X.zero₃ f g _ rfl n₀ n₁
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_eq_zero_of_isIso₂ (hg : IsIso g) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ = 0 := by
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using X.zero₁ f g _ rfl n₀ n₁

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.isZero_H_obj_of_isIso** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：isZero_H_obj_of_isIso {i j : ι} (f : i ⟶ j) (hf : IsIso f) (n : Int) : IsZ
ero ((X.H n).obj (mk₁ f))
参数：f : i ⟶ j；hf : IsIso f；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.zero₂`：zero₂ (fg : i ⟶ k) (h : f ≫
 g = fg) (n₀ : Int) : (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫ (X.H n₀).map (twoδ₁Toδ
₀ f g fg h) = 0
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
-/
lemma isZero_H_obj_of_isIso {i j : ι} (f : i ⟶ j) (hf : IsIso f) (n : ℤ) :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine IsZero.of_iso ?_ ((X.H n).mapIso e.symm)
  have h := X.zero₂ (𝟙 i) (𝟙 i) (𝟙 i) (by simp) n
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← h]
  congr 1
  cat_disch

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- `E^n₁(f₁, f₂, f₃)` identifies to the cokernel
of `δToCycles : H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.leftHomologyDataShortComplex** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：leftHomologyDataShortComplex (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.kernelSequenceCycles_exact`：kernel
SequenceCycles_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoFKernelSequenceCycles`：∀ {
C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…

--- 原说明 ---
`E^n₁(f₁, f₂, f₃)` identifies to the cokernel
of `δToCycles : H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)`.
-/
noncomputable def leftHomologyDataShortComplex
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).LeftHomologyData := by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  have : hi.lift (KernelFork.ofι _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).zero) =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ :=
    Fork.IsLimit.hom_ext hi (by simpa using! hi.fac _ .zero)
  exact {
    K := X.cycles f₁ f₂ n₁
    H := cokernel (X.δToCycles f₁ f₂ f₃ n₀ n₁)
    i := X.iCycles f₁ f₂ n₁
    π := cokernel.π _
    wi := by simp
    hi := hi
    wπ := by rw [this]; simp
    hπ := by
      refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).2
        (cokernelIsCokernel (X.δToCycles f₁ f₂ f₃ n₀ n₁))
      · exact parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa) (by simp)
      · exact Cofork.ext (Iso.refl _) }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.leftHomologyDataShortComplex_f'** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：leftHomologyDataShortComplex_f' (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `CategoryTheory.Abelian.SpectralObject.kernelSequenceCycles_exact`：kernel
SequenceCycles_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoFKernelSequenceCycles`：∀ {
C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [in
st_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.SpectralObject.kernelSequenceCycles_f`：∀ {C : Typ
e u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Abelian.SpectralObject.δToCycles_iCycles`：δToCycles_iCycl
es (hn₁ : n₀ + 1 = n₁) : X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.iCycles f₁ f₂ n₁ = X
.δ f₂ f₃ n₀ n₁ hn₁
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma leftHomologyDataShortComplex_f' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.leftHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).f' =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  let hi := (X.kernelSequenceCycles_exact f₁ f₂ _ _ hn₂).fIsKernel
  exact Fork.IsLimit.hom_ext hi (by simpa using! hi.fac _ .zero)

/-- The cycles of the short complex `shortComplex` at `E^{n₁}(f₁, f₂, f₃)`
identifies to `Z^{n₁}(f₁, f₂)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.cyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesIso (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cycles of the short complex `shortComplex` at `E^{n₁}(f₁, f₂, f₃)`
identifies to `Z^{n₁}(f₁, f₂)`.
-/
noncomputable def cyclesIso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).cycles ≅ X.cycles f₁ f₂ n₁ :=
  (X.leftHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂).cyclesIso

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesIso_inv_i** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesIso_inv_i (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles`
：cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i
-/
lemma cyclesIso_inv_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles = X.iCycles f₁ f₂ n₁ :=
  ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesIso_hom_i** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesIso_hom_i (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i`：cycle
sIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles
-/
lemma cyclesIso_hom_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.iCycles f₁ f₂ n₁ =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles :=
  ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

/-- The epimorphism `Z^{n₁}(f₁, f₂) ⟶ E^{n₁}(f₁, f₂, f₃)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The epimorphism `Z^{n₁}(f₁, f₂) ⟶ E^{n₁}(f₁, f₂, f₃)`.
-/
noncomputable def πE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.cycles f₁ f₂ n₁ ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).inv ≫
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).homologyπ

set_option backward.isDefEq.respectTransparency false in
deriving instance Epi for πE

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δToCycles_cyclesIso_inv (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).toCycles := by
  simp [← cancel_mono (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂).iCycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δToCycles_πE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ = 0 := by
  simp [πE]

/-- The (exact) sequence `H^{n-1}(f₃) ⟶ Z^n(f₁, f₂) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceCyclesE** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceCyclesE (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.δToCycles_πE`：δToCycles_πE (hn₁ : 
n₀ + 1 = n₁

--- 原说明 ---
The (exact) sequence `H^{n-1}(f₃) ⟶ Z^n(f₁, f₂) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`.
-/
noncomputable def cokernelSequenceCyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.δToCycles_πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

set_option backward.isDefEq.respectTransparency false in
/-- The short complex `H^{n-1}(f₃) ⟶ Z^n(f₁, f₂) ⟶ E^n(f₁, f₂, f₃)` identifies
to the cokernel sequence of the definition of the homology of the short
complex `shortComplex` as a cokernel of `ShortComplex.toCycles`. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceCyclesEIso** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceCyclesEIso (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `H^{n-1}(f₃) ⟶ Z^n(f₁, f₂) ⟶ E^n(f₁, f₂, f₃)` identifies
to the cokernel sequence of the definition of the homology of the short
complex `shortComplex` as a cokernel of `ShortComplex.toCycles`.
-/
noncomputable def cokernelSequenceCyclesEIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≅ ShortComplex.mk _ _
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).toCycles_comp_homologyπ :=
  ShortComplex.isoMk (Iso.refl _) (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂).symm
    (Iso.refl _) (by simp) (by simp [πE])
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceCyclesE_exact** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.ShortComplex.toCycles_comp_homologyπ`：toCycles_comp_homol
ogyπ : S.toCycles ≫ S.homologyπ = 0
· 使用引理 `CategoryTheory.ShortComplex.exact_of_g_is_cokernel`：exact_of_g_is_cokern
el (hS : IsColimit (CokernelCofork.ofπ S.g S.zero)) [S.HasHomology] : S.Exact
-/
lemma cokernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).Exact :=
  ShortComplex.exact_of_iso (X.cokernelSequenceCyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.homologyIsCokernel _))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceCyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- `E^n₁(f₁, f₂, f₃)` identifies to the kernel
of `δFromOpcycles : opZ^{n₁}(f₂, f₃) ⟶ H^{n₂}(f₁)`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.rightHomologyDataShortComplex** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：rightHomologyDataShortComplex (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cokernelSequenceOpcycles_exact`：co
kernelSequenceOpcycles_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiGCokernelSequenceOpcycles`：
∀ {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   
[inst_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…

--- 原说明 ---
`E^n₁(f₁, f₂, f₃)` identifies to the kernel
of `δFromOpcycles : opZ^{n₁}(f₂, f₃) ⟶ H^{n₂}(f₁)`.
-/
noncomputable def rightHomologyDataShortComplex
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).RightHomologyData := by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  have : hp.desc (CokernelCofork.ofπ _ (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).zero) =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ :=
    Cofork.IsColimit.hom_ext hp (by simpa using! hp.fac _ .one)
  exact {
    Q := X.opcycles f₂ f₃ n₁
    H := kernel (X.δFromOpcycles f₁ f₂ f₃ n₁ n₂)
    p := X.pOpcycles f₂ f₃ n₁
    ι := kernel.ι _
    wp := by simp
    hp := hp
    wι := by rw [this]; simp
    hι := by
      refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).2
        (kernelIsKernel (X.δFromOpcycles f₁ f₂ f₃ n₁ n₂))
      · exact parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa) (by simp)
      · exact Fork.ext (Iso.refl _) }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.rightHomologyDataShortComplex_g'** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：rightHomologyDataShortComplex_g' (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cokernelSequenceOpcycles_exact`：co
kernelSequenceOpcycles_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiGCokernelSequenceOpcycles`：
∀ {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   
[inst_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Abelian.SpectralObject.cokernelSequenceOpcycles_g`：∀ {C :
 Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Abelian.SpectralObject.pOpcycles_δFromOpcycles`：pOpcycles
_δFromOpcycles (hn₁ : n₀ + 1 = n₁) : X.pOpcycles f₂ f₃ n₀ ≫ X.δFromOpcycles f₁ f
₂ f₃ n₀ n₁ hn₁ = X.δ f₁ f₂ n₀ n₁ hn₁
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma rightHomologyDataShortComplex_g'
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).g' =
      X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ := by
  let hp := (X.cokernelSequenceOpcycles_exact f₂ f₃ _ _ hn₁).gIsCokernel
  exact Cofork.IsColimit.hom_ext hp (by simpa using! hp.fac _ .one)

/-- The opcycles of the short complex `shortComplex` at `E^{n₁}(f₁, f₂, f₃)`
identifies to `opZ^{n₁}(f₂, f₃)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesIso (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opcycles of the short complex `shortComplex` at `E^{n₁}(f₁, f₂, f₃)`
identifies to `opZ^{n₁}(f₂, f₃)`.
-/
noncomputable def opcyclesIso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).opcycles ≅ X.opcycles f₂ f₃ n₁ :=
  (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).opcyclesIso

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.p_opcyclesIso_hom** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：p_opcyclesIso_hom (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso
_hom`：pOpcycles_comp_opcyclesIso_hom : S.pOpcycles ≫ h.opcyclesIso.hom = h.p
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma p_opcyclesIso_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles ≫
      (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
    X.pOpcycles f₂ f₃ n₁ :=
  ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.p_opcyclesIso_inv** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：p_opcyclesIso_inv (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv`：p_
comp_opcyclesIso_inv : h.p ≫ h.opcyclesIso.inv = S.pOpcycles
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
-/
lemma p_opcyclesIso_inv (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.pOpcycles f₂ f₃ n₁ ≫ (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles :=
  (X.rightHomologyDataShortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).p_comp_opcyclesIso_inv

set_option backward.isDefEq.respectTransparency false in
/-- The monomorphism `E^{n₁}(f₁, f₂, f₃) ⟶ opZ^{n₁}(f₂, f₃) ⟶ `. -/
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monomorphism `E^{n₁}(f₁, f₂, f₃) ⟶ opZ^{n₁}(f₂, f₃) ⟶ `.
-/
noncomputable def ιE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.opcycles f₂ f₃ n₁ :=
  (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι ≫
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom
  deriving Mono

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesIso_hom_** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opcyclesIso_hom_δFromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ =
      (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).fromOpcycles := by
  simp [← cancel_epi (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιE_δFromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.δFromOpcycles f₁ f₂ f₃ n₁ n₂ hn₂ = 0 := by
  simp [ιE]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πE_ιE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.iCycles f₁ f₂ n₁ ≫ X.pOpcycles f₂ f₃ n₁ := by
  simp [πE, ιE]

/-- The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ opZ^n(f₂, f₃) ⟶ H^{n+1}(f₁)`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceOpcyclesE** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceOpcyclesE (hn₁ : n₀ + 1 = n₁
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.SpectralObject.ιE_δFromOpcycles`：ιE_δFromOpcycles
 (hn₁ : n₀ + 1 = n₁

--- 原说明 ---
The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ opZ^n(f₂, f₃) ⟶ H^{n+1}(f₁)`.
-/
noncomputable def kernelSequenceOpcyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.ιE_δFromOpcycles f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

set_option backward.isDefEq.respectTransparency false in
/-- The short complex `E^n(f₁, f₂, f₃) ⟶ opZ^n(f₂, f₃) ⟶ H^{n+1}(f₁)` identifies
to the kernel sequence of the definition of the homology of the short
complex `shortComplex` as a kernel of `ShortComplex.fromOpcycles`. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceOpcyclesEIso** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceOpcyclesEIso (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex `E^n(f₁, f₂, f₃) ⟶ opZ^n(f₂, f₃) ⟶ H^{n+1}(f₁)` identifies
to the kernel sequence of the definition of the homology of the short
complex `shortComplex` as a kernel of `ShortComplex.fromOpcycles`.
-/
noncomputable def kernelSequenceOpcyclesEIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≅
      ShortComplex.mk _ _
        (X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).homologyι_comp_fromOpcycles :=
  Iso.symm (ShortComplex.isoMk (Iso.refl _) (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)
    (Iso.refl _) (by simp [ιE]) (by simp))
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceOpcyclesE_exact** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceOpcyclesE_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.ShortComplex.homologyι_comp_fromOpcycles`：homologyι_comp_
fromOpcycles : S.homologyι ≫ S.fromOpcycles = 0
· 使用引理 `CategoryTheory.ShortComplex.exact_of_f_is_kernel`：exact_of_f_is_kernel (
hS : IsLimit (KernelFork.ofι S.f S.zero)) [S.HasHomology] : S.Exact
-/
lemma kernelSequenceOpcyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).Exact :=
  ShortComplex.exact_of_iso (X.kernelSequenceOpcyclesEIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).symm
    (ShortComplex.exact_of_f_is_kernel _ (ShortComplex.homologyIsKernel _))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.kernelSequenceOpcyclesE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp; infer_instance

/-- The (exact) sequence `H^n(f₁) ⊞ H^{n-1}(f₃) ⟶ H^n(f₁ ≫ f₂) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceE** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceE (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (exact) sequence `H^n(f₁) ⊞ H^{n-1}(f₃) ⟶ H^n(f₁ ≫ f₂) ⟶ E^n(f₁, f₂, f₃) ⟶ 0
`.
-/
noncomputable def cokernelSequenceE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁) ⊞ (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₁₂)
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := biprod.desc ((X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)) (X.δ f₁₂ f₃ n₀ n₁)
  g := X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceE_exact** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceE_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.A
belian C]   (S : CategoryTheory.ShortComplex C),   …
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C},   …
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cokernelSequenceCyclesE_exact`：cok
ernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.exact₂`：exact₂ (n₀ : Int) : (X.sc₂
 f g fg h n₀).Exact
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.δ_toCycles`：δ_toCycles (hn₁ : n₀ +
 1 = n₁
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Abelian.SpectralObject.toCycles_i`：toCycles_i (n : Int) :
 X.toCycles f g fg h n ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.biprod.lift_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [in
st_2 : CategoryTheory.Limits…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
lemma cokernelSequenceE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceCyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁) (by simpa using! hx₂)
  dsimp at y₁ hy₁
  let z := π₁ ≫ x₂ - y₁ ≫ X.δ f₁₂ f₃ n₀ n₁
  obtain ⟨A₂, π₂, _, x₁, hx₁⟩ := (X.exact₂ f₁ f₂ f₁₂ h₁₂ n₁).exact_up_to_refinements z (by
      have : z ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ = 0 := by simp [z, hy₁]
      simpa only [zero_comp, Category.assoc, toCycles_i] using! this =≫ X.iCycles f₁ f₂ n₁)
  dsimp at x₁ hx₁
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, biprod.lift x₁ (π₂ ≫ y₁), by simp [z, ← hx₁]⟩

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f₁₂) ⟶ A)
  (h : (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ x = 0)
  (hn₁ : n₀ + 1 = n₁) (h' : X.δ f₁₂ f₃ n₀ n₁ hn₁ ≫ x = 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Constructor for morphisms for `E^{n₁}(f₁, f₂, f₃)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.descE** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Abelian.SpectralObject`。
形式化陈述：descE (hn₂ : n₁ + 1 = n₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms for `E^{n₁}(f₁, f₂, f₃)`.
-/
noncomputable def descE (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ A :=
  (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).desc x (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.toCycles_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toCycles_πE_descE (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.descE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ x h hn₁ h' hn₂ = x := by
  dsimp only [descE]
  rw [← Category.assoc]
  apply (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂).g_desc

end

/-- The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ H^n(f₂ ≫ f₃) ⟶ H^n(f₃) ⊞ H^{n+1}(f₁)`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceE** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceE (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ H^n(f₂ ≫ f₃) ⟶ H^n(f₃) ⊞ H^{n+1}(f₁)
`.
-/
noncomputable def kernelSequenceE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := (X.H n₁).obj (mk₁ f₂₃)
  X₃ := (X.H n₁).obj (mk₁ f₃) ⊞ (X.H n₂).obj (mk₁ f₁)
  f := X.ιE f₁ f₂ f₃ n₀ n₁ n₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁
  g := biprod.lift ((X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)) (X.δ f₁ f₂₃ n₁ n₂)
  zero := by ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.kernelSequenceE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceE_exact** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceE_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.A
belian C]   (S : CategoryTheory.ShortComplex C),   …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C},   …
· 使用引理 `CategoryTheory.Abelian.SpectralObject.kernelSequenceOpcyclesE_exact`：ker
nelSequenceOpcyclesE_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.SpectralObject.fromOpcyles_δ`：fromOpcyles_δ (hn₁ 
: n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.liftOpcycles_fromOpcycles_assoc`：∀
 {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [
inst_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.Abelian.SpectralObject.liftOpcycles_fromOpcycles`：liftOpc
ycles_fromOpcycles : X.liftOpcycles f g fg h x hx ≫ X.fromOpcycles f g fg h n = 
x
-/
lemma kernelSequenceE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceOpcyclesE_exact f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements
      (X.liftOpcycles f₂ f₃ f₂₃ h₂₃ x₂ (by simpa using hx₂ =≫ biprod.fst)) (by
        dsimp
        rw [← X.fromOpcyles_δ f₁ f₂ f₃ f₂₃ h₂₃ n₁ n₂,
          X.liftOpcycles_fromOpcycles_assoc]
        simpa using hx₂ =≫ biprod.snd)
  dsimp at x₁ hx₁
  refine ⟨A₁, π₁, inferInstance, x₁, ?_⟩
  dsimp
  rw [← reassoc_of% hx₁, liftOpcycles_fromOpcycles]

section

variable {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ f₂₃))
  (h : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃) = 0)
  (hn₂ : n₁ + 1 = n₂)
  (h' : x ≫ X.δ f₁ f₂₃ n₁ n₂ hn₂ = 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Constructor for morphisms to `E^{n₁}(f₁, f₂, f₃)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.liftE** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Abelian.SpectralObject`。
形式化陈述：liftE (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms to `E^{n₁}(f₁, f₂, f₃)`.
-/
noncomputable def liftE (hn₁ : n₀ + 1 = n₁ := by lia) :
    A ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).lift x (by cat_disch)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.liftE_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftE_ιE_fromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.liftE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ x h hn₂ h' hn₁ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
      X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁ = x := by
  apply (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).lift_f

end

end

section

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  {i₀' i₁' i₂' i₃' : ι}
  (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesIso_inv_cyclesMap** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesIso_inv_cyclesMap (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂') (hβ : β = homMk₂ (α.
app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia)) (naturality' α 
1 2 (by lia) (by lia))) (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁
参数：β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂'；hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (na
turality' α 0 1 (by lia) (by lia)) (naturality' α 1 2 (by lia) (by lia))；n₀ n₁ n
₂ : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.instMonoICycles`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   (S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ ≫ S₂.
iCycles = S₁.iCycles ≫ φ.τ₂
· 使用定理 `CategoryTheory.Abelian.SpectralObject.shortComplexMap_τ₂`：∀ {C : Type u_
1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.cyclesIso_inv_i_assoc`：∀ {C : Type
 u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesIso_inv_i`：cyclesIso_inv_i (
hn₁ : n₀ + 1 = n₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesMap_i`：cyclesMap_i (α : mk₂ 
f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : Int) (hβ : β = homMk₁ (α.app 1) (α.ap
p 2) (naturality' α 1 2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesIso_inv_cyclesMap
    (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia)))
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      ShortComplex.cyclesMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) =
    X.cyclesMap f₁ f₂ f₁' f₂' β n₁ ≫ (X.cyclesIso f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂).inv := by
  subst hβ
  simp [← cancel_mono (ShortComplex.iCycles _), cyclesMap_i]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesMap_opcyclesIso_hom** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesMap_opcyclesIso_hom (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃') (hγ : γ = homMk₂
 (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2) (naturality' α 2 3)
参数：γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ShortComplex.instEpiPOpcycles`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   (S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.p_opcyclesMap_assoc`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.shortComplexMap_τ₂`：∀ {C : Type u_
1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesIso_hom`：p_opcyclesIso_h
om (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesIso_hom_assoc`：∀ {C : Ty
pe u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesMap`：p_opcyclesMap (α : 
mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : Int) (hβ : β = homMk₁ (α.app 0) (
α.app 1) (naturality' α 0 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesMap_opcyclesIso_hom
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃')
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2)
      (naturality' α 2 3) := by cat_disch)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex.opcyclesMap (X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂) ≫
      (X.opcyclesIso f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂).hom =
    (X.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.opcyclesMap f₂ f₃ f₂' f₃' γ n₁ := by
  subst hγ
  simp [← cancel_epi (ShortComplex.pOpcycles _), p_opcyclesMap]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πE_map (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂') (n₀ n₁ n₂ : ℤ)
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia)) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ =
      X.cyclesMap f₁ f₂ f₁' f₂' β n₁ ≫ X.πE f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ := by
  simp [πE, map, X.cyclesIso_inv_cyclesMap_assoc f₁ f₂ f₃ f₁' f₂' f₃' α β hβ n₀ n₁ n₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.map_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ιE
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃') (n₀ n₁ n₂ : ℤ)
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2)
      (naturality' α 2 3) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.opcyclesMap f₂ f₃ f₂' f₃' γ n₁ := by
  simp [ιE, map, X.opcyclesMap_opcyclesIso_hom f₁ f₂ f₃ f₁' f₂' f₃' α γ hγ n₀ n₁ n₂ hn₁ hn₂]

end

section

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
  (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ n₂ : ℤ)

/-- The map `opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesToE** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesToE (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃)`.
-/
noncomputable def opcyclesToE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcycles f₁₂ f₃ n₁ ⟶ X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  X.descOpcycles _ _ _ _ hn₁ (X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂) (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.p_opcyclesToE** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Abelian.SpectralObject`。
形式化陈述：p_opcyclesToE (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_descOpcycles`：p_descOpcycles : X
.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma p_opcyclesToE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.pOpcycles f₁₂ f₃ n₁ ≫ X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ =
      X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  simp [opcyclesToE]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesToE_** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opcyclesToE_ιE (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.opcyclesMap f₁₂ f₃ f₂ f₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) n₁ := by
  simpa [← cancel_epi (X.pOpcycles f₁₂ f₃ n₁)] using (X.p_opcyclesMap ..).symm
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂) :=
  epi_of_epi_fac (X.p_opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂)

/-- The (exact) sequence `H^n(f₁) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceOpcyclesE** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceOpcyclesE (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (exact) sequence `H^n(f₁) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`.
-/
noncomputable def cokernelSequenceOpcyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁)
  X₂ := X.opcycles f₁₂ f₃ n₁
  X₃ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  f := (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ X.pOpcycles f₁₂ f₃ n₁
  g := X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.cokernelSequenceOpcyclesE_exact** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cokernelSequenceOpcyclesE_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.A
belian C]   (S : CategoryTheory.ShortComplex C),   …
· 使用引理 `CategoryTheory.surjective_up_to_refinements_of_epi`：surjective_up_to_ref
inements_of_epi (f : X ⟶ Y) [Epi f] {A : C} (y : A ⟶ Y) : exists (A' : C) (π : A
' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y =…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiPOpcycles`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C},   …
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cokernelSequenceE_exact`：cokernelS
equenceE_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesToE`：p_opcyclesToE (hn₁ 
: n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
（共 32 条，此处仅展示前 30 条）
-/
lemma cokernelSequenceOpcyclesE_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.pOpcycles f₁₂ f₃ n₁) x₂
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂).exact_up_to_refinements y₂
      (by simpa only [Category.assoc, p_opcyclesToE, hx₂, comp_zero]
        using! hy₂.symm =≫ X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂)
  dsimp at y₁ hy₁
  obtain ⟨a, b, rfl⟩ : ∃ a b, y₁ = a ≫ biprod.inl + b ≫ biprod.inr :=
    ⟨y₁ ≫ biprod.fst, y₁ ≫ biprod.snd, by ext <;> simp⟩
  simp only [Preadditive.add_comp, Category.assoc, biprod.inl_desc, biprod.inr_desc] at hy₁
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, a, ?_⟩
  simp [Category.assoc, hy₂, reassoc_of% hy₁, Preadditive.add_comp, δ_pOpcycles,
    comp_zero, add_zero]

-- TODO: add dual statement to `cokernelSequenceOpcyclesE_exact`?

/-- The map `E^n(f₁, f₂, f₃) ⟶ Z^n(f₁, f₂ ≫ f₃)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.EToCycles** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Abelian.SpectralObject`。
形式化陈述：EToCycles (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `E^n(f₁, f₂, f₃) ⟶ Z^n(f₁, f₂ ≫ f₃)`.
-/
noncomputable def EToCycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ X.cycles f₁ f₂₃ n₁ :=
  X.liftCycles _ _ _ _ hn₂
    (X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁) (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.EToCycles_i** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Abelian.SpectralObject`。
形式化陈述：EToCycles_i (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.liftCycles_i`：liftCycles_i : X.lif
tCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma EToCycles_i (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.iCycles f₁ f₂₃ n₁ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁ := by
  simp [EToCycles]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma πE_EToCycles (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂ =
      X.cyclesMap f₁ f₂ f₁ f₂₃ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) n₁ := by
  simpa [← cancel_mono (X.iCycles f₁ f₂₃ n₁)] using (X.cyclesMap_i ..).symm
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂) :=
  mono_of_mono_fac (X.EToCycles_i f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

/-- The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ Z^n(f₁, f₂ ≫ f₃) ⟶ H^n(f₃)`. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceCyclesE** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceCyclesE (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (exact) sequence `0 ⟶ E^n(f₁, f₂, f₃) ⟶ Z^n(f₁, f₂ ≫ f₃) ⟶ H^n(f₃)`.
-/
noncomputable def kernelSequenceCyclesE
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C where
  X₁ := X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  X₂ := X.cycles f₁ f₂₃ n₁
  X₃ := (X.H n₁).obj (mk₁ f₃)
  f := X.EToCycles f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂
  g := X.iCycles f₁ f₂₃ n₁ ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.kernelSequenceCyclesE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.kernelSequenceCyclesE_exact** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：kernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.A
belian C]   (S : CategoryTheory.ShortComplex C),   …
· 使用定理 `CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   {S : CategoryTheory.ShortComplex C},   …
· 使用引理 `CategoryTheory.Abelian.SpectralObject.kernelSequenceE_exact`：kernelSeque
nceE_exact (hn₁ : n₀ + 1 = n₁
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.iCycles_δ`：iCycles_δ (hn₁ : n₀ + 1
 = n₁
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoICycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.EToCycles_i`：EToCycles_i (hn₁ : n₀
 + 1 = n₁
-/
lemma kernelSequenceCyclesE_exact (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.kernelSequenceCyclesE f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceE_exact f₁ f₂ f₃ f₂₃ h₂₃ n₀ n₁ n₂).exact_up_to_refinements
      (x₂ ≫ X.iCycles f₁ f₂₃ n₁) (by cat_disch)
  exact ⟨A₁, π₁, inferInstance, x₁, by simpa [← cancel_mono (X.iCycles ..)]⟩

end

section

variable {i j : ι} (f : i ⟶ j) {i' j' : ι} (f' : i' ⟶ j')

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- An homology data for `X.shortComplex n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)`,
expressing `H^n₁(f)` as the homology of this short complex,
see `EIsoH`. -/
@[simps!]
/-
**CategoryTheory.Abelian.SpectralObject.homologyDataIdId** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：homologyDataIdId (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁
参数：n₀ n₁ n₂ : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An homology data for `X.shortComplex n₀ n₁ n₂ hn₁ hn₂ (𝟙 i) f (𝟙 j)`,
expressing `H^n₁(f)` as the homology of this short complex,
see `EIsoH`.
-/
noncomputable def homologyDataIdId (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplex (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).HomologyData :=
  (ShortComplex.HomologyData.ofZeros (X.shortComplex (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂)
    (X.δ_eq_zero_of_isIso₂ f (𝟙 j) inferInstance n₀ n₁ hn₁)
    (X.δ_eq_zero_of_isIso₁ (𝟙 i) f inferInstance n₁ n₂ hn₂))

/-- For any morphism `f : i ⟶ j`, this is the isomorphism from
`E^n₁(𝟙 i, f, 𝟙 j)` to `H^n₁(f)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.EIsoH** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Abelian.SpectralObject`。
形式化陈述：EIsoH (n₀ n₁ n₂ : Int) (hn₁ : n₀ + 1 = n₁
参数：n₀ n₁ n₂ : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any morphism `f : i ⟶ j`, this is the isomorphism from
`E^n₁(𝟙 i, f, 𝟙 j)` to `H^n₁(f)`.
-/
noncomputable def EIsoH (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.E (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ ≅ (X.H n₁).obj (mk₁ f) :=
  (X.homologyDataIdId ..).left.homologyIso

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.EIsoH_hom_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：EIsoH_hom_naturality (α : mk₁ f ⟶ mk₁ f') (β : mk₃ (𝟙 _) f (𝟙 _) ⟶ mk₃ (𝟙 
_) f' (𝟙 _)) (n₀ n₁ n₂ : Int) (hβ : β = homMk₃ (α.app 0) (α.app 0) (α.app 1) (α.
app 1) (by simp) (naturality' α 0 1) (by simp [Precomp.obj, Precomp.map])
参数：α : mk₁ f ⟶ mk₁ f'；β : mk₃ (𝟙 _) f (𝟙 _) ⟶ mk₃ (𝟙 _) f' (𝟙 _)；n₀ n₁ n₂ : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyMapData.homologyMap_comm`：homolo
gyMap_comm : homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom ≫ γ.φH
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
-/
lemma EIsoH_hom_naturality
    (α : mk₁ f ⟶ mk₁ f') (β : mk₃ (𝟙 _) f (𝟙 _) ⟶ mk₃ (𝟙 _) f' (𝟙 _))
    (n₀ n₁ n₂ : ℤ)
    (hβ : β = homMk₃ (α.app 0) (α.app 0) (α.app 1) (α.app 1)
      (by simp) (naturality' α 0 1) (by simp [Precomp.obj, Precomp.map]) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map (𝟙 _) f (𝟙 _) (𝟙 _) f' (𝟙 _) β n₀ n₁ n₂ hn₁ hn₂ ≫
      (X.EIsoH f' n₀ n₁ n₂ hn₁ hn₂).hom =
    (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (X.H n₁).map α := by
  obtain rfl : α = homMk₁ (β.app 1) (β.app 2) (naturality' β 1 2) := by
    subst hβ
    exact hom_ext₁ rfl rfl
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (X.shortComplexMap _ _ _ _ _ _ β n₀ n₁ n₂ hn₁ hn₂) ..).homologyMap_comm

end

section

variable {i₀ i₁ : ι} (f : i₀ ⟶ i₁) (n₀ n₁ : ℤ)

/-- The isomorphism `Z^n(𝟙 _, f) ≅ H^n(f)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.cyclesIsoH** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesIsoH (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `Z^n(𝟙 _, f) ≅ H^n(f)`.
-/
noncomputable def cyclesIsoH (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.cycles (𝟙 i₀) f n₀ ≅ (X.H n₀).obj (mk₁ f) :=
  (X.cyclesIso (𝟙 i₀) f (𝟙 i₁) (n₀ - 1) n₀ n₁ (by lia) hn₁).symm ≪≫
    (X.homologyDataIdId ..).left.cyclesIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesIsoH_inv** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesIsoH_inv (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoICycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.toCycles_i`：toCycles_i (n : Int) :
 X.toCycles f g fg h n ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesIso_hom_i`：cyclesIso_hom_i (
hn₁ : n₀ + 1 = n₁
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles`
：cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesIsoH_inv (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cyclesIsoH f n₀ n₁ hn₁).inv = X.toCycles (𝟙 _) f f (by simp) n₀ := by
  rw [← cancel_mono (X.iCycles (𝟙 _) f n₀), toCycles_i]
  dsimp [cyclesIsoH]
  simp only [Category.assoc, cyclesIso_hom_i, homologyDataIdId_left_i,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, ← Functor.map_id]
  congr 1
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesIsoH_hom_inv_id** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesIsoH_inv`：cyclesIsoH_inv (hn
₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma cyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cyclesIsoH f n₀ n₁ hn₁).hom ≫
      X.toCycles (𝟙 _) f f (by simp) n₀ = 𝟙 _ := by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesIsoH_inv_hom_id** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesIsoH_inv_hom_id (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesIsoH_inv`：cyclesIsoH_inv (hn
₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma cyclesIsoH_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.toCycles (𝟙 _) f f (by simp) n₀ ≫
      (X.cyclesIsoH f n₀ n₁ hn₁).hom = 𝟙 _ := by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).inv_hom_id

/-- The isomorphism `opZ^n(f, 𝟙 _) ≅ H^n(f)`. -/
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesIsoH** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesIsoH (hn₁ : n₀ + 1 = n₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `opZ^n(f, 𝟙 _) ≅ H^n(f)`.
-/
noncomputable def opcyclesIsoH (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.opcycles f (𝟙 i₁) n₁ ≅ (X.H n₁).obj (mk₁ f) :=
  (X.opcyclesIso (𝟙 i₀) f (𝟙 i₁) n₀ n₁ (n₁ + 1) hn₁ (by lia)).symm ≪≫
    (X.homologyDataIdId ..).right.opcyclesIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesIsoH_hom** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesIsoH_hom (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiPOpcycles`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_fromOpcycles`：p_fromOpcycles (n 
: Int) : X.pOpcycles f g n ≫ X.fromOpcycles f g fg h n = (X.H n).map (twoδ₂Toδ₁ 
f g fg h)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesIso_inv_assoc`：∀ {C : Ty
pe u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso
_hom`：pOpcycles_comp_opcyclesIso_hom : S.pOpcycles ≫ h.opcyclesIso.hom = h.p
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.opcyclesIsoH f n₀ n₁ hn₁).hom = X.fromOpcycles f (𝟙 _) f (by simp) n₁ := by
  rw [← cancel_epi (X.pOpcycles f (𝟙 _) n₁), p_fromOpcycles]
  dsimp [opcyclesIsoH]
  simp only [p_opcyclesIso_inv_assoc, homologyDataIdId_right_p, ← Functor.map_id,
    ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom]
  congr 1
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesIsoH_hom_inv_id** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.opcyclesIsoH_hom`：opcyclesIsoH_hom
 (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma opcyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) :
      X.fromOpcycles f (𝟙 _) f (by simp) n₁ ≫
        (X.opcyclesIsoH f n₀ n₁ hn₁).inv = 𝟙 _ := by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesIsoH_inv_hom_id** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesIsoH_inv_hom_id (hn₁ : n₀ + 1 = n₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.SpectralObject.opcyclesIsoH_hom`：opcyclesIsoH_hom
 (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma opcyclesIsoH_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.opcyclesIsoH f n₀ n₁ hn₁).inv ≫
      X.fromOpcycles f (𝟙 _) f (by simp) n₁ = 𝟙 _ := by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).inv_hom_id

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) {i j : ι} (f : i ⟶ j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.cyclesIsoH_hom_EIsoH_inv** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：cyclesIsoH_hom_EIsoH_inv : (X.cyclesIsoH f n₁ n₂ hn₂).hom ≫ (X.EIsoH f n₀ 
n₁ n₂ hn₁ hn₂).inv = X.πE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
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
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoICycles`：∀ {C : Type u_1} 
{ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesIso_hom_i`：cyclesIso_hom_i (
hn₁ : n₀ + 1 = n₁
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles`
：cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i
· 使用引理 `CategoryTheory.Abelian.SpectralObject.toCycles_i`：toCycles_i (n : Int) :
 X.toCycles f g fg h n ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `CategoryTheory.Abelian.SpectralObject.cyclesIsoH_inv`：cyclesIsoH_inv (hn
₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.cyclesIsoH_inv_hom_id_assoc`：∀ {C 
: Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.instEpiπ`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   {S : CategoryTheory.Sho…
（共 32 条，此处仅展示前 30 条）
-/
lemma cyclesIsoH_hom_EIsoH_inv :
    (X.cyclesIsoH f n₁ n₂ hn₂).hom ≫ (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).inv =
      X.πE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ := by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂).left
  have : h.cyclesIso.inv =
      X.toCycles (𝟙 i) f f (by simp) n₁ ≫
        (X.cyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).inv := by
    rw [← cancel_mono (X.cyclesIso ..).hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← cancel_mono (X.iCycles ..), Category.assoc, cyclesIso_hom_i ..,
      h.cyclesIso_inv_comp_iCycles, toCycles_i]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₀ = n₁ - 1 := by lia
  rw [← cancel_epi (X.cyclesIsoH f n₁ n₂ hn₂).inv,
    cyclesIsoH_inv .., cyclesIsoH_inv_hom_id_assoc ..]
  dsimp [EIsoH]
  rw [← cancel_epi h.π, h.π_comp_homologyIso_inv]
  simp [πE, h, this]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.EIsoH_hom_opcyclesIsoH_inv** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：EIsoH_hom_opcyclesIsoH_inv : (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (X.opcycle
sIsoH f n₀ n₁ hn₁).inv = X.ιE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiPOpcycles`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesIso_inv_assoc`：∀ {C : Ty
pe u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso
_hom`：pOpcycles_comp_opcyclesIso_hom : S.pOpcycles ≫ h.opcyclesIso.hom = h.p
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_fromOpcycles`：p_fromOpcycles (n 
: Int) : X.pOpcycles f g n ≫ X.fromOpcycles f g fg h n = (X.H n).map (twoδ₂Toδ₁ 
f g fg h)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
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
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.opcyclesIsoH_hom`：opcyclesIsoH_hom
 (hn₁ : n₀ + 1 = n₁
· 使用引理 `CategoryTheory.Abelian.SpectralObject.opcyclesIsoH_inv_hom_id`：opcyclesI
soH_inv_hom_id (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.ShortComplex.HomologyData.left_homologyIso_eq_right_homol
ogyIso_trans_iso_symm`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] 
[inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {S : CategoryTheory.ShortC
omp…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyData.homologyIso_hom_comp_ι`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComp…
（共 31 条，此处仅展示前 30 条）
-/
lemma EIsoH_hom_opcyclesIsoH_inv :
    (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (X.opcyclesIsoH f n₀ n₁ hn₁).inv =
      X.ιE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ := by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂)
  have : h.right.opcyclesIso.hom =
      (X.opcyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).hom ≫
        X.fromOpcycles f (𝟙 j) f (by simp) n₁ := by
    rw [← cancel_epi (X.opcyclesIso ..).inv, Iso.inv_hom_id_assoc,
      ← cancel_epi (X.pOpcycles ..), p_opcyclesIso_inv_assoc ..,
      h.right.pOpcycles_comp_opcyclesIso_hom, p_fromOpcycles]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₂ = n₁ + 1 := by lia
  rw [← cancel_mono (X.opcyclesIsoH f n₀ n₁ hn₁).hom, Category.assoc,
    opcyclesIsoH_hom .., opcyclesIsoH_inv_hom_id ..]
  dsimp [EIsoH, ιE]
  rw [Category.assoc, ← this,
    h.left_homologyIso_eq_right_homologyIso_trans_iso_symm,
    ← ShortComplex.RightHomologyData.homologyIso_hom_comp_ι]
  simp [h]

end

section

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃)
    (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesMap_three** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opcyclesMap_threeδ₂Toδ₁_opcyclesToE
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesMap _ _ _ _ (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃) n₁ ≫
      X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ = 0 := by
  rw [← cancel_epi (X.pOpcycles ..), comp_zero,
    p_opcyclesMap_assoc _ _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)]
  simp

/-- The short exact sequence
`0 ⟶ opZ^(f₁, f₂ ≫ f₃) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ H^n(f₁, f₂, f₃) ⟶ 0`. -/
@[simps]
/-
**CategoryTheory.Abelian.SpectralObject.shortComplexOpcyclesThree** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short exact sequence
`0 ⟶ opZ^(f₁, f₂ ≫ f₃) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ H^n(f₁, f₂, f₃) ⟶ 0`.
-/
noncomputable def shortComplexOpcyclesThreeδ₂Toδ₁
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _
    (X.opcyclesMap_threeδ₂Toδ₁_opcyclesToE f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).f := by
  dsimp
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  replace hx := hx =≫ X.fromOpcycles f₁₂ f₃ _ rfl n₁
  rw [zero_comp, Category.assoc,
    X.opcyclesMap_fromOpcycles f₁ f₂₃ f₁₂ f₃ (f₁₂ ≫ f₃) (by cat_disch) _ rfl _ (𝟙 _) n₁
      (by simp) (by cat_disch), Functor.map_id, Category.comp_id] at hx
  rw [← cancel_mono (X.fromOpcycles f₁ f₂₃ (f₁₂ ≫ f₃) (by cat_disch) n₁), hx, zero_comp]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Abelian.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Epi (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).g := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Abelian.SpectralObject.shortComplexOpcyclesThree** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shortComplexOpcyclesThreeδ₂Toδ₁_exact
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).Exact := by
  let φ : X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ ⟶
      (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂) :=
    { τ₁ := X.pOpcycles f₁ f₂₃ n₁
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id, X.p_opcyclesMap _ _ _ _ _ (twoδ₂Toδ₁ f₁ f₂ f₁₂)] }
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact X.cokernelSequenceOpcyclesE_exact f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂
/-
**CategoryTheory.Abelian.SpectralObject.shortComplexOpcyclesThree** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Abelian.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma shortComplexOpcyclesThreeδ₂Toδ₁_shortExact
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).ShortExact where
  exact := X.shortComplexOpcyclesThreeδ₂Toδ₁_exact ..

end

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  {i₀' i₁' i₂' i₃' : ι} (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (f₁₂' : i₀' ⟶ i₂') (h₁₂' : f₁' ≫ f₂' = f₁₂')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Abelian.SpectralObject.opcyclesToE_map** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Abelian.SpectralObject`。
形式化陈述：opcyclesToE_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') (β : mk₂ f₁₂ f₃ ⟶ mk₂
 f₁₂' f₃') (n₀ n₁ n₂ : Int) (h₀ : β.app 0 = α.app 0
参数：α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃'；β : mk₂ f₁₂ f₃ ⟶ mk₂ f₁₂' f₃'；n₀ n₁ n₂ : I
nt。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instMonoιE`：∀ {C : Type u_2} {ι : 
Type u_4} [inst : CategoryTheory.Category.{u_1, u_2} C]   [inst_1 : CategoryTheo
ry.Category.{u_3, u_4} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.opcyclesToE_ιE`：opcyclesToE_ιE (hn
₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Abelian.SpectralObject.instEpiPOpcycles`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesToE_assoc`：∀ {C : Type u
_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CategoryTheory.Abelian.SpectralObject.πE_map_assoc`：∀ {C : Type u_1} {ι 
: Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.πE_ιE`：πE_ιE (hn₁ : n₀ + 1 = n₁
· 使用定理 `CategoryTheory.Abelian.SpectralObject.cyclesMap_i_assoc`：∀ {C : Type u_1
} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.toCycles_i_assoc`：∀ {C : Type u_1}
 {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesMap_assoc`：∀ {C : Type u
_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} ι] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Abelian.SpectralObject.p_opcyclesMap`：p_opcyclesMap (α : 
mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : Int) (hβ : β = homMk₁ (α.app 0) (
α.app 1) (naturality' α 0 1)
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用引理 `CategoryTheory.ComposableArrows.hom_ext₁`：hom_ext₁ {F G : ComposableArro
ws C 1} {φ φ' : F ⟶ G} (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
 φ = φ'
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ComposableArrows.homMk₁.congr_simp`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {F G : CategoryTheory.ComposableArrows
 C 1}   (left left_1 :     F.obj' 0 Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesToE_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') (β : mk₂ f₁₂ f₃ ⟶ mk₂ f₁₂' f₃')
    (n₀ n₁ n₂ : ℤ) (h₀ : β.app 0 = α.app 0 := by cat_disch) (h₁ : β.app 1 = α.app 2 := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫ X.map _ _ _ _ _ _ α _ _ _ =
      X.opcyclesMap _ _ _ _ β _ ≫ X.opcyclesToE f₁' f₂' f₃' f₁₂' h₁₂' n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← cancel_mono (X.ιE ..), Category.assoc, Category.assoc, opcyclesToE_ιE ..,
    ← cancel_epi (X.pOpcycles ..), p_opcyclesToE_assoc ..,
    X.πE_map_assoc _ _ _ _ _ _ _
      (homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1) (naturality' α 1 2)) ..,
    πE_ιE .., X.cyclesMap_i_assoc .., toCycles_i_assoc,
    X.p_opcyclesMap_assoc .., X.p_opcyclesMap ..,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  ext
  · simpa [h₀] using naturality' α 0 1
  · simp [h₁]

end SpectralObject

end Abelian

end CategoryTheory

