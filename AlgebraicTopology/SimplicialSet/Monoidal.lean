/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# The monoidal category structure on simplicial sets

This file defines an instance of chosen finite products
for the category `SSet`. It follows from the fact
the `SSet` if a category of functors to the category
of types and that the category of types have chosen
finite products. As a result, we obtain a monoidal
category structure on `SSet`.

-/

@[expose] public section

universe u

open Simplicial CategoryTheory MonoidalCategory CartesianMonoidalCategory
  Limits SimplicialObject.Truncated

namespace SSet

@[simp]
/-
**SSet.leftUnitor_hom_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：leftUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (𝟙_ _
 otimes K).obj Δ) : dsimp% (fun_ K).hom.app Δ x = x.2
参数：K : SSet.{u}；x : (𝟙_ _ otimes K).obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (𝟙_ _ ⊗ K).obj Δ) :
    dsimp% (λ_ K).hom.app Δ x = x.2 := rfl

@[simp]
/-
**SSet.leftUnitor_inv_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：leftUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj
 Δ) : dsimp% (fun_ K).inv.app Δ x = ⟨PUnit.unit, x⟩
参数：K : SSet.{u}；x : K.obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
    dsimp% (λ_ K).inv.app Δ x = ⟨PUnit.unit, x⟩ := rfl

@[simp]
/-
**SSet.rightUnitor_hom_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：rightUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (K o
times 𝟙_ _).obj Δ) : dsimp% (ρ_ K).hom.app Δ x = x.1
参数：K : SSet.{u}；x : (K otimes 𝟙_ _).obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ 𝟙_ _).obj Δ) :
    dsimp% (ρ_ K).hom.app Δ x = x.1 := rfl

@[simp]
/-
**SSet.rightUnitor_inv_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：rightUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.ob
j Δ) : dsimp% (ρ_ K).inv.app Δ x = ⟨x, PUnit.unit⟩
参数：K : SSet.{u}；x : K.obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
    dsimp% (ρ_ K).inv.app Δ x = ⟨x, PUnit.unit⟩ := rfl

@[simp]
/-
**SSet.tensorHom_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：tensorHom_app_apply {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') {Δ : 
SimplexCategoryᵒᵖ} (x : (K otimes L).obj Δ) : dsimp% (f otimesₘ g).app Δ x = ⟨f.
app Δ x.1, g.app Δ x.2⟩
参数：f : K ⟶ K'；g : L ⟶ L'；x : (K otimes L).obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorHom_app_apply {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    dsimp% (f ⊗ₘ g).app Δ x = ⟨f.app Δ x.1, g.app Δ x.2⟩ := rfl

@[simp]
/-
**SSet.whiskerLeft_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：whiskerLeft_app_apply (K : SSet.{u}) {L L' : SSet.{u}} (g : L ⟶ L') {Δ : S
implexCategoryᵒᵖ} (x : (K otimes L).obj Δ) : dsimp% (K ◁ g).app Δ x = ⟨x.1, g.ap
p Δ x.2⟩
参数：K : SSet.{u}；g : L ⟶ L'；x : (K otimes L).obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_app_apply (K : SSet.{u}) {L L' : SSet.{u}} (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    dsimp% (K ◁ g).app Δ x = ⟨x.1, g.app Δ x.2⟩ := rfl

@[simp]
/-
**SSet.whiskerRight_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：whiskerRight_app_apply {K K' : SSet.{u}} (f : K ⟶ K') (L : SSet.{u}) {Δ : 
SimplexCategoryᵒᵖ} (x : (K otimes L).obj Δ) : dsimp% (f ▷ L).app Δ x = ⟨f.app Δ 
x.1, x.2⟩
参数：f : K ⟶ K'；L : SSet.{u}；x : (K otimes L).obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_app_apply {K K' : SSet.{u}} (f : K ⟶ K') (L : SSet.{u})
    {Δ : SimplexCategoryᵒᵖ} (x : (K ⊗ L).obj Δ) :
    dsimp% (f ▷ L).app Δ x = ⟨f.app Δ x.1, x.2⟩ := rfl

@[simp]
/-
**SSet.associator_hom_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：associator_hom_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (
(K otimes L) otimes M).obj Δ) : dsimp% (α_ K L M).hom.app Δ x = ⟨x.1.1, x.1.2, x
.2⟩
参数：K L M : SSet.{u}；x : ((K otimes L) otimes M).obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_hom_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
    (x : ((K ⊗ L) ⊗ M).obj Δ) :
    dsimp% (α_ K L M).hom.app Δ x = ⟨x.1.1, x.1.2, x.2⟩ := rfl

@[simp]
/-
**SSet.associator_inv_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：associator_inv_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (
K otimes L otimes M).obj Δ) : dsimp% (α_ K L M).inv.app Δ x = ⟨⟨x.1, x.2.1⟩, x.2
.2⟩
参数：K L M : SSet.{u}；x : (K otimes L otimes M).obj Δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_inv_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
    (x : (K ⊗ L ⊗ M).obj Δ) :
    dsimp% (α_ K L M).inv.app Δ x = ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(𝟙_ SSet ⟶ K) ≃ K _⦋0⦌`. -/
/-
**SSet.unitHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：unitHomEquiv (K : SSet.{u}) : (𝟙_ _ ⟶ K) ≃ K _⦋0⦌ where toFun φ
参数：K : SSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(𝟙_ SSet ⟶ K) ≃ K _⦋0⦌`.
-/
def unitHomEquiv (K : SSet.{u}) : (𝟙_ _ ⟶ K) ≃ K _⦋0⦌ where
  toFun φ := φ.app _ PUnit.unit
  invFun x :=
    { app := fun Δ => ↾fun _ => K.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op x
      naturality := fun Δ Δ' f => by
        ext ⟨⟩
        dsimp
        rw [← Functor.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ ⟨⟩
    dsimp [-Monoidal.tensorUnit_obj]
    rw [← NatTrans.naturality_apply]
    rfl
  right_inv x := by simp

/-- The object `Δ[0]` is terminal in `SSet`. -/
/-
**SSet.stdSimplex.isTerminalObj** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object `Δ[0]` is terminal in `SSet`.
-/
def stdSimplex.isTerminalObj₀ : IsTerminal (Δ[0] : SSet.{u}) :=
  IsTerminal.ofUniqueHom (fun _ ↦ SSet.const (obj₀Equiv.symm 0))
    (fun _ _ ↦ by
      ext ⟨n⟩
      exact objEquiv.injective (by ext; simp))

@[ext]
/-
**SSet.stdSimplex.ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：ext {n d : Nat} (x y : Δ[n] _⦋d⦌) (h : forall (i : Fin (d + 1)), x i = y i
) : x = y
参数：x y : Δ[n] _⦋d⦌；h : forall (i : Fin (d + 1)), x i = y i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
lemma stdSimplex.ext₀ {X : SSet.{u}} {f g : X ⟶ Δ[0]} : f = g :=
  isTerminalObj₀.hom_ext _ _
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    [Finite (X.obj n)] [Finite (Y.obj n)] :
    Finite ((X ⊗ Y).obj n) :=
  inferInstanceAs (Finite (X.obj n × Y.obj n))
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝟙_ SSet.{u}).Finite :=
  finite_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasDimensionLE (𝟙_ SSet.{u}) 0 :=
  (hasDimensionLT_iff_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit) _).1 inferInstance
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : opFunctor.{u}.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

namespace Subcomplex

/-- The external product of subcomplexes of simplicial sets. -/
@[simps]
/-
**SSet.Subcomplex.prod** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：prod {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) : (X otimes Y)
.Subcomplex where obj Δ
参数：A : X.Subcomplex；B : Y.Subcomplex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The external product of subcomplexes of simplicial sets.
-/
def prod {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) : (X ⊗ Y).Subcomplex where
  obj Δ := (A.obj Δ).prod (B.obj Δ)
  map i _ hx := ⟨A.map i hx.1, B.map i hx.2⟩
/-
**SSet.Subcomplex.prod_monotone** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：prod_monotone {X Y : SSet.{u}} {A₁ A₂ : X.Subcomplex} (hX : A₁ <= A₂) {B₁ 
B₂ : Y.Subcomplex} (hY : B₁ <= B₂) : A₁.prod B₁ <= A₂.prod B₂
参数：hX : A₁ <= A₂；hY : B₁ <= B₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma prod_monotone {X Y : SSet.{u}}
    {A₁ A₂ : X.Subcomplex} (hX : A₁ ≤ A₂) {B₁ B₂ : Y.Subcomplex} (hY : B₁ ≤ B₂) :
    A₁.prod B₁ ≤ A₂.prod B₂ :=
  fun _ _ hx => ⟨hX _ hx.1, hY _ hx.2⟩
/-
**SSet.Subcomplex.prod_le_top_prod** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：prod_le_top_prod {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) : 
A.prod B <= (⊤ : X.Subcomplex).prod B
参数：A : X.Subcomplex；B : Y.Subcomplex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.prod_monotone`：prod_monotone {X Y : SSet.{u}} {A₁ A₂ : X
.Subcomplex} (hX : A₁ <= A₂) {B₁ B₂ : Y.Subcomplex} (hY : B₁ <= B₂) : A₁.prod B₁
 <= A₂.prod B₂
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma prod_le_top_prod {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    A.prod B ≤ (⊤ : X.Subcomplex).prod B :=
  prod_monotone le_top (by rfl)
/-
**SSet.Subcomplex.prod_le_prod_top** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：prod_le_prod_top {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) : 
A.prod B <= A.prod ⊤
参数：A : X.Subcomplex；B : Y.Subcomplex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.prod_monotone`：prod_monotone {X Y : SSet.{u}} {A₁ A₂ : X
.Subcomplex} (hX : A₁ <= A₂) {B₁ B₂ : Y.Subcomplex} (hY : B₁ <= B₂) : A₁.prod B₁
 <= A₂.prod B₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma prod_le_prod_top {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    A.prod B ≤ A.prod ⊤ :=
  prod_monotone (by rfl) le_top

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.range_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：range_tensorHom {X₁ X₂ Y₁ Y₂ : SSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) : r
ange (f₁ otimesₘ f₂) = (range f₁).prod (range f₂)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.eq_iff_fst_eq_snd_eq`：∀ {α : Type u_1} {β : Type u_2} {p q : α × β}
, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma range_tensorHom {X₁ X₂ Y₁ Y₂ : SSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    range (f₁ ⊗ₘ f₂) = (range f₁).prod (range f₂) := by
  ext m ⟨y₁, y₂⟩
  constructor
  · rintro ⟨⟨x₁, x₂⟩, h⟩
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    exact ⟨⟨x₁, h.1⟩, ⟨x₂, h.2⟩⟩
  · rintro ⟨⟨x₁, rfl⟩, ⟨x₂, rfl⟩⟩
    exact ⟨⟨x₁, x₂⟩, rfl⟩

/-- The isomorphism `(A.prod B).toSSet ≅ A.toSSet ⊗ B.toSSet`. -/
@[simps]
/-
**SSet.Subcomplex.prodIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：prodIso {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) : (A.prod B
).toSSet ≅ A otimes B where hom
参数：A : X.Subcomplex；B : Y.Subcomplex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `(A.prod B).toSSet ≅ A.toSSet ⊗ B.toSSet`.
-/
def prodIso {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    (A.prod B).toSSet ≅ A ⊗ B where
  hom := CartesianMonoidalCategory.lift
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.fst _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.snd _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
  inv := lift (A.ι ⊗ₘ B.ι) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact ⟨Subtype.coe_prop _, Subtype.coe_prop _⟩)

end Subcomplex

/-- The inclusion `X ⟶ X ⊗ Δ[1]` which is `0` on the second factor. -/
/-
**SSet.** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `X ⟶ X ⊗ Δ[1]` which is `0` on the second factor.
-/
noncomputable def ι₀ {X : SSet.{u}} : X ⟶ X ⊗ Δ[1] :=
  lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 0))

@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₀ ≫ f ▷ _ = f ≫ ι₀ := rfl

@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_fst (X : SSet.{u}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_snd (X : SSet.{u}) : ι₀ ≫ snd X _ = const (stdSimplex.obj₀Equiv.{u}.symm 0) := rfl

@[simp]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_app_fst {X : SSet.{u}} {m} (x : X.obj m) : dsimp% (ι₀.app _ x).1 = x := rfl

@[simp]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₀_app_snd_apply {X : SSet.{u}} {m : ℕ} (x : X _⦋m⦌) (k : Fin (m + 1)) :
    dsimp% (ι₀.app _ x).2 k = 0 := rfl

/-- The inclusion `X ⟶ X ⊗ Δ[1]` which is `1` on the second factor. -/
/-
**SSet.** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `X ⟶ X ⊗ Δ[1]` which is `1` on the second factor.
-/
noncomputable def ι₁ {X : SSet.{u}} : X ⟶ X ⊗ Δ[1] :=
  lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 1))

@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_fst (X : SSet.{u}) : ι₁ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_snd (X : SSet.{u}) : ι₁ ≫ snd X _ = (const (stdSimplex.obj₀Equiv.{u}.symm 1)) := rfl

@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₁ ≫ f ▷ _ = f ≫ ι₁ := rfl

@[simp]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_app_fst {X : SSet.{u}} {m} (x : X.obj m) : dsimp% (ι₁.app _ x).1 = x := rfl

@[simp]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_app_snd_apply {X : SSet.{u}} {m : ℕ} (x : X _⦋m⦌) (k : Fin (m + 1)) :
    dsimp% (ι₁.app _ x).2 k = 1 := rfl

section

variable (X Y : SSet.{u})

section

variable {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) (z : (X ⊗ Y).obj m)
/-
**SSet.prod_map_fst** 是 Mathlib 中的一个定理，位于命名空间 `SSet`。
形式化陈述：∀ (X Y : _root_.SSet) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)   (z : (Catego
ryTheory.MonoidalCategoryStruct.tensorObj X Y).obj m),   ((CategoryTheory.Concre
teCategory.hom (CategoryTheory.MonoidalCategoryStruct.tensorHom (X.map f) (Y.map
 f))) z).1 =     (CategoryTheory.ConcreteCategory.hom (X.map f)) z.1
参数：X Y : _root_.SSet；f : m ⟶ n；z : (CategoryTheory.MonoidalCategoryStruct.tensor
Obj X Y).obj m；(CategoryTheory.ConcreteCategory.hom (CategoryTheory.MonoidalCate
goryStruct.tensorHom (X.map f) (Y.map f))) z；CategoryTheory.ConcreteCategory.hom
 (X.map f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp high, grind =] lemma prod_map_fst : dsimp% ((X ⊗ Y).map f z).1 = X.map f z.1 := rfl
/-
**SSet.prod_map_snd** 是 Mathlib 中的一个定理，位于命名空间 `SSet`。
形式化陈述：∀ (X Y : _root_.SSet) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)   (z : (Catego
ryTheory.MonoidalCategoryStruct.tensorObj X Y).obj m),   ((CategoryTheory.Concre
teCategory.hom (CategoryTheory.MonoidalCategoryStruct.tensorHom (X.map f) (Y.map
 f))) z).2 =     (CategoryTheory.ConcreteCategory.hom (Y.map f)) z.2
参数：X Y : _root_.SSet；f : m ⟶ n；z : (CategoryTheory.MonoidalCategoryStruct.tensor
Obj X Y).obj m；(CategoryTheory.ConcreteCategory.hom (CategoryTheory.MonoidalCate
goryStruct.tensorHom (X.map f) (Y.map f))) z；CategoryTheory.ConcreteCategory.hom
 (Y.map f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp high, grind =] lemma prod_map_snd : dsimp% ((X ⊗ Y).map f z).2 = Y.map f z.2 := rfl

end

/-
**SSet.prod_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma prod_δ_fst {n : ℕ} (i : Fin (n + 2)) (z : (X ⊗ Y : SSet.{u}) _⦋n + 1⦌) :
    dsimp% ((X ⊗ Y).δ i z).1 = X.δ i z.1 := rfl
/-
**SSet.prod_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma prod_δ_snd {n : ℕ} (i : Fin (n + 2)) (z : (X ⊗ Y : SSet.{u}) _⦋n + 1⦌) :
    dsimp% ((X ⊗ Y).δ i z).2 = Y.δ i z.2 := rfl
/-
**SSet.prod_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma prod_σ_fst {n : ℕ} (i : Fin (n + 1)) (z : (X ⊗ Y : SSet.{u}) _⦋n⦌) :
    dsimp% ((X ⊗ Y).σ i z).1 = X.σ i z.1 := rfl
/-
**SSet.prod_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma prod_σ_snd {n : ℕ} (i : Fin (n + 1)) (z : (X ⊗ Y : SSet.{u}) _⦋n⦌) :
    dsimp% ((X ⊗ Y).σ i z).2 = Y.σ i z.2 := rfl

end

section

namespace Subcomplex

variable {X Y : SSet.{u}} (S : X.Subcomplex) (T : Y.Subcomplex)

/-- Given `S ≤ X` and `T ≤ Y`, this is the subcomplex of `X ⊗ Y` given by `(X ⊗ T) ⊔ (S ⊗ Y)`. -/
/-
**SSet.Subcomplex.unionProd** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：unionProd : (X otimes Y).Subcomplex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `S ≤ X` and `T ≤ Y`, this is the subcomplex of `X ⊗ Y` given by `(X ⊗ T) ⊔
 (S ⊗ Y)`.
-/
def unionProd : (X ⊗ Y).Subcomplex := ((⊤ : X.Subcomplex).prod T) ⊔ (S.prod ⊤)

set_option backward.defeqAttrib.useBackward true in
/-
**SSet.Subcomplex.mem_unionProd_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：mem_unionProd_iff {n : SimplexCategoryᵒᵖ} (x : (X otimes Y).obj n) : dsimp
% x in (unionProd S T).obj _ ↔ x.2 in T.obj _ ∨ x.1 in S.obj _
参数：x : (X otimes Y).obj n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_unionProd_iff {n : SimplexCategoryᵒᵖ} (x : (X ⊗ Y).obj n) :
    dsimp% x ∈ (unionProd S T).obj _ ↔ x.2 ∈ T.obj _ ∨ x.1 ∈ S.obj _ := by
  dsimp [unionProd, Set.prod]
  cat_disch
/-
**SSet.Subcomplex.top_prod_le_unionProd** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex`。
形式化陈述：top_prod_le_unionProd : (⊤ : X.Subcomplex).prod T <= S.unionProd T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma top_prod_le_unionProd : (⊤ : X.Subcomplex).prod T ≤ S.unionProd T := le_sup_left
/-
**SSet.Subcomplex.prod_top_le_unionProd** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex`。
形式化陈述：prod_top_le_unionProd : (S.prod ⊤) <= S.unionProd T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma prod_top_le_unionProd : (S.prod ⊤) ≤ S.unionProd T := le_sup_right
/-
**SSet.Subcomplex.prod_le_unionProd** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：prod_le_unionProd : S.prod T <= S.unionProd T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SSet.Subcomplex.prod_le_prod_top`：prod_le_prod_top {X Y : SSet.{u}} (A :
 X.Subcomplex) (B : Y.Subcomplex) : A.prod B <= A.prod ⊤
· 使用引理 `SSet.Subcomplex.prod_top_le_unionProd`：prod_top_le_unionProd : (S.prod ⊤
) <= S.unionProd T
-/
lemma prod_le_unionProd : S.prod T ≤ S.unionProd T :=
  (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)
/-
**SSet.Subcomplex.preimage_op_unionProd** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex`。
形式化陈述：preimage_op_unionProd : (unionProd S T).op.preimage (Functor.LaxMonoidal.μ
 opFunctor _ _) = unionProd S.op T.op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_op_unionProd :
    (unionProd S T).op.preimage (Functor.LaxMonoidal.μ opFunctor _ _) =
      unionProd S.op T.op := rfl
/-
**SSet.Subcomplex.preimage_unionProd** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`
。
形式化陈述：preimage_unionProd {X' Y' : SSet.{u}} (f : X' ⟶ X) (g : Y' ⟶ Y) : (unionPr
od S T).preimage (f otimesₘ g) = unionProd (S.preimage f) (T.preimage g)
参数：f : X' ⟶ X；g : Y' ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_unionProd {X' Y' : SSet.{u}} (f : X' ⟶ X) (g : Y' ⟶ Y) :
    (unionProd S T).preimage (f ⊗ₘ g) =
      unionProd (S.preimage f) (T.preimage g) := rfl

namespace unionProd

/-- The inclusion `X ⊗ T ⟶ S.unionProd T` as simplicial sets. -/
/-
**SSet.Subcomplex.unionProd.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.unionPro
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `X ⊗ T ⟶ S.unionProd T` as simplicial sets.
-/
noncomputable def ι₁ : X ⊗ T ⟶ S.unionProd T :=
  lift (X ◁ T.ι) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inl ⟨Set.mem_univ _, Subtype.coe_prop _⟩)

/-- The inclusion `S ⊗ Y ⟶ S.unionProd T` as simplicial sets -/
/-
**SSet.Subcomplex.unionProd.** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.unionPro
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `S ⊗ Y ⟶ S.unionProd T` as simplicial sets
-/
noncomputable def ι₂ : (S : SSet.{u}) ⊗ Y ⟶ (unionProd S T : SSet.{u}) :=
  lift (S.ι ▷ Y) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inr ⟨Subtype.coe_prop _, Set.mem_univ _⟩)

@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.unionProd.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.unionPro
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₁_ι : ι₁ S T ≫ (unionProd S T).ι = X ◁ T.ι := rfl

@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.unionProd.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.unionPro
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι₂_ι : ι₂ S T ≫ (unionProd S T).ι = S.ι ▷ Y := rfl
/-
**SSet.Subcomplex.unionProd.bicartSq** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.
unionProd`。
形式化陈述：bicartSq : BicartSq (S.prod T) ((⊤ : X.Subcomplex).prod T) (S.prod ⊤) (uni
onProd S T) where sup_eq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `trivial`：True
-/
lemma bicartSq : BicartSq (S.prod T) ((⊤ : X.Subcomplex).prod T) (S.prod ⊤) (unionProd S T) where
  sup_eq := rfl
  inf_eq := by
    ext n ⟨x, y⟩
    change _ ∧ _ ↔ _
    simp [prod, Set.prod, Membership.mem, Set.Mem, Set.ofPred]
    tauto
/-
**SSet.Subcomplex.unionProd.isPushout** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex
.unionProd`。
形式化陈述：isPushout : IsPushout (S.ι ▷ (T : SSet)) ((S : SSet) ◁ T.ι) (unionProd.ι₁ 
S T) (unionProd.ι₂ S T)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.of_iso`：of_iso (h : IsPushout f g inl inr) {Z' 
X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e
₁ : Z ≅ Z') (e₂ : X ≅…
· 使用引理 `Lattice.BicartSq.le₁₂`：le₁₂ : x₁ <= x₂
· 使用引理 `SSet.Subcomplex.unionProd.bicartSq`：bicartSq : BicartSq (S.prod T) ((⊤ :
 X.Subcomplex).prod T) (S.prod ⊤) (unionProd S T) where sup_eq
· 使用引理 `Lattice.BicartSq.le₁₃`：le₁₃ : x₁ <= x₃
· 使用引理 `Lattice.BicartSq.le₂₄`：le₂₄ : x₂ <= x₄
· 使用引理 `Lattice.BicartSq.le₃₄`：le₃₄ : x₃ <= x₄
· 使用定理 `SSet.Subcomplex.BicartSq.isPushout`：∀ {X : _root_.SSet} {A₁ A₂ A₃ A₄ : X
.Subcomplex} (sq : A₁.BicartSq A₂ A₃ A₄),   CategoryTheory.IsPushout (SSet.Subco
mplex.homOfLE ⋯) (SSet.S…
-/
lemma isPushout : IsPushout (S.ι ▷ (T : SSet)) ((S : SSet) ◁ T.ι)
    (unionProd.ι₁ S T) (unionProd.ι₂ S T) :=
  (bicartSq S T).isPushout.of_iso (S.prodIso T)
    (prodIso _ _ ≪≫ whiskerRightIso (topIso X) _)
    (prodIso _ _ ≪≫ whiskerLeftIso _ (topIso Y))
    (Iso.refl _) rfl rfl rfl rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Subcomplex.unionProd.preimage_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex
.unionProd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_β_hom : (unionProd S T).preimage (β_ _ _).hom = unionProd T S := by
  ext n ⟨x, y⟩
  dsimp
  simp only [mem_unionProd_iff, preimage_obj, Monoidal.tensorObj_obj,
    dsimp% Set.mem_preimage (f := (β_ Y X).hom.app n)]
  tauto

@[simp]
/-
**SSet.Subcomplex.unionProd.preimage_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex
.unionProd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_β_inv : (unionProd S T).preimage (β_ _ _).inv = unionProd T S := by
  apply preimage_β_hom

@[simp]
/-
**SSet.Subcomplex.unionProd.image_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.un
ionProd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_β_hom : (unionProd S T).image (β_ _ _).hom = unionProd T S := by
  rw [← preimage_β_hom, preimage_image_of_isIso]

@[simp]
/-
**SSet.Subcomplex.unionProd.image_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.un
ionProd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_β_inv : (unionProd S T).image (β_ _ _).inv = unionProd T S := by
  apply image_β_hom

/-- The isomorphism `unionProd S T ≅ unionProd T S` as simplicial sets. -/
@[simps]
/-
**SSet.Subcomplex.unionProd.symmIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.u
nionProd`。
形式化陈述：symmIso : (unionProd S T : SSet) ≅ (unionProd T S : SSet) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `unionProd S T ≅ unionProd T S` as simplicial sets.
-/
noncomputable def symmIso : (unionProd S T : SSet) ≅ (unionProd T S : SSet) where
  hom := lift ((unionProd S T).ι ≫ (β_ _ _).hom) (by simp [range_comp])
  inv := lift ((unionProd T S).ι ≫ (β_ _ _).hom) (by simp [range_comp])

end unionProd

end Subcomplex

end

namespace Truncated

variable (n : ℕ)

open MonoidalCategory

/-
**SSet.Truncated.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (truncation.{u} n).Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj _).Monoidal

variable {n} {X Y : Truncated.{u} n}

@[simp]
/-
**SSet.Truncated.tensor_map_apply_fst** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`
。
形式化陈述：tensor_map_apply_fst {d e : (SimplexCategory.Truncated n)ᵒᵖ} (f : d ⟶ e) (
x : (X otimes Y : Truncated _).obj d) : dsimp% ((X otimes Y : Truncated _).map f
 x).1 = X.map f x.1
参数：SimplexCategory.Truncated n；f : d ⟶ e；x : (X otimes Y : Truncated _).obj d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensor_map_apply_fst {d e : (SimplexCategory.Truncated n)ᵒᵖ}
    (f : d ⟶ e) (x : (X ⊗ Y : Truncated _).obj d) :
    dsimp% ((X ⊗ Y : Truncated _).map f x).1 = X.map f x.1 := rfl

@[simp]
/-
**SSet.Truncated.tensor_map_apply_snd** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`
。
形式化陈述：tensor_map_apply_snd {d e : (SimplexCategory.Truncated n)ᵒᵖ} (f : d ⟶ e) (
x : (X otimes Y : Truncated _).obj d) : dsimp% ((X otimes Y : Truncated _).map f
 x).2 = Y.map f x.2
参数：SimplexCategory.Truncated n；f : d ⟶ e；x : (X otimes Y : Truncated _).obj d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensor_map_apply_snd {d e : (SimplexCategory.Truncated n)ᵒᵖ}
    (f : d ⟶ e) (x : (X ⊗ Y : Truncated _).obj d) :
    dsimp% ((X ⊗ Y : Truncated _).map f x).2 = Y.map f x.2 := rfl

end Truncated

end SSet

