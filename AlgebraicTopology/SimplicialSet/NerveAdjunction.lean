/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# The adjunction between the nerve and the homotopy category functor

We define an adjunction `nerveAdjunction : hoFunctor ⊣ nerveFunctor` between the functor that
takes a simplicial set to its homotopy category and the functor that takes a category to its nerve.

Up to natural isomorphism, this is constructed as the composite of two other adjunctions,
namely `nerve₂Adj : hoFunctor₂ ⊣ nerveFunctor₂` between analogously-defined functors involving
the category of 2-truncated simplicial sets and `coskAdj 2 : truncation 2 ⊣ Truncated.cosk 2`. The
aforementioned natural isomorphism

`cosk₂Iso : nerveFunctor ≅ nerveFunctor₂ ⋙ Truncated.cosk 2`

exists because nerves of categories are 2-coskeletal.

We also prove that `nerveFunctor` is fully faithful, demonstrating that `nerveAdjunction` is
reflective. Since the category of simplicial sets is cocomplete, we conclude in
`Mathlib/CategoryTheory/Category/Cat/Colimit.lean` that the category of categories has colimits.

Finally we show that `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` preserves finite cartesian products; note
that it fails to preserve infinite products.

-/

@[expose] public section

universe u

open CategoryTheory Nerve Simplicial SimplicialObject.Truncated
  SimplexCategory.Truncated Opposite Limits

namespace SSet

namespace Truncated

section liftOfStrictSegal
/-! The goal of this section is to define `SSet.Truncated.liftOfStrictSegal`
which allows to construct of morphism `X ⟶ Y` of `2`-truncated simplicial sets
from the data of maps on `0`- and `1`-simplices when `Y` is strict Segal.
-/

variable {n : ℕ} {X Y : Truncated.{u} 2} (f₀ : X _⦋0⦌₂ → Y _⦋0⦌₂) (f₁ : X _⦋1⦌₂ → Y _⦋1⦌₂)
  (hδ₁ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₁ x))
  (hδ₀ : ∀ (x : X _⦋1⦌₂), f₀ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₁ x))
  (H : ∀ (x : X _⦋2⦌₂) (y : Y _⦋2⦌₂), f₁ (X.map (δ₂ 2).op x) = Y.map (δ₂ 2).op y →
    f₁ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op y →
      f₁ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op y)
  (hσ : ∀ (x : X _⦋0⦌₂), f₁ (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₀ x))
  (hY : Y.StrictSegal)

namespace liftOfStrictSegal

/-- Auxiliary definition for `SSet.Truncated.liftOfStrictSegal`. -/
/-
**SSet.Truncated.liftOfStrictSegal.f** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.l
iftOfStrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `SSet.Truncated.liftOfStrictSegal`.
-/
def f₂ (x : X _⦋2⦌₂) : Y _⦋2⦌₂ :=
  (hY.spineEquiv 2).symm
    (.mk₂ (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 2).op x)))
      (Y.spine 1 (by simp) (f₁ (X.map (δ₂ 0).op x))) (by
        simp only [spine_vertex]
        rw [← δ₂_one_eq_const, ← δ₂_zero_eq_const, ← hδ₁, ← hδ₀]
        simp only [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_δ₂_two]))

@[simp]
/-
**SSet.Truncated.liftOfStrictSegal.spineEquiv_f** 是 Mathlib 中的一个引理，位于命名空间 `SSet.
Truncated.liftOfStrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spineEquiv_f₂_arrow_zero (x : X _⦋2⦌₂) :
    ((hY.spineEquiv 2) (f₂ f₀ f₁ hδ₁ hδ₀ hY x)).arrow 0 = f₁ (X.map (δ₂ 2).op x) := by
  simp [f₂]

@[simp]
/-
**SSet.Truncated.liftOfStrictSegal.spineEquiv_f** 是 Mathlib 中的一个引理，位于命名空间 `SSet.
Truncated.liftOfStrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spineEquiv_f₂_arrow_one (x : X _⦋2⦌₂) :
    ((hY.spineEquiv 2) (f₂ f₀ f₁ hδ₁ hδ₀ hY x)).arrow 1 = f₁ (X.map (δ₂ 0).op x) := by
  simp [f₂]

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.liftOfStrictSegal.h** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.l
iftOfStrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hδ'₀ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 0).op x) = Y.map (δ₂ 0).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) := by
  simp [← spineEquiv_f₂_arrow_one f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_one_eq_δ]

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.liftOfStrictSegal.h** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.l
iftOfStrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hδ'₂ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 2).op x) = Y.map (δ₂ 2).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) := by
  simp [← spineEquiv_f₂_arrow_zero f₀ f₁ hδ₁ hδ₀ hY, StrictSegal.spineEquiv,
    SimplexCategory.mkOfSucc_zero_eq_δ]

include H in
/-
**SSet.Truncated.liftOfStrictSegal.h** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.l
iftOfStrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hδ'₁ (x : X _⦋2⦌₂) :
    f₁ (X.map (δ₂ 1).op x) = Y.map (δ₂ 1).op (f₂ f₀ f₁ hδ₁ hδ₀ hY x) :=
  H x (f₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₂ f₀ f₁ hδ₁ hδ₀ hY x) (hδ'₀ f₀ f₁ hδ₁ hδ₀ hY x)

set_option backward.isDefEq.respectTransparency.types false in
include hσ in
/-
**SSet.Truncated.liftOfStrictSegal.h** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.l
iftOfStrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hσ'₀ (x : X _⦋1⦌₂) :
    f₂ f₀ f₁ hδ₁ hδ₀ hY (X.map (σ₂ 0).op x) = Y.map (σ₂ 0).op (f₁ x) := by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    dsimp [StrictSegal.spineEquiv]
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero, op_comp,
      Functor.map_comp_apply, hσ, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← Functor.map_comp_apply, ← op_comp, δ₂_two_comp_σ₂_zero,
      op_comp, Functor.map_comp_apply, hδ₁]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_one_eq_δ,
      ← Functor.map_comp_apply, ← op_comp]

set_option backward.isDefEq.respectTransparency.types false in
include hσ in
/-
**SSet.Truncated.liftOfStrictSegal.h** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.l
iftOfStrictSegal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hσ'₁ (x : X _⦋1⦌₂) :
    f₂ f₀ f₁ hδ₁ hδ₀ hY (X.map (σ₂ 1).op x) = Y.map (σ₂ 1).op (f₁ x) := by
  apply (hY.spineEquiv 2).injective
  ext i
  fin_cases i
  · dsimp
    rw [spineEquiv_f₂_arrow_zero]
    simp [StrictSegal.spineEquiv, SimplexCategory.mkOfSucc_zero_eq_δ,
      ← Functor.map_comp_apply, ← op_comp]
  · dsimp
    rw [spineEquiv_f₂_arrow_one]
    dsimp [StrictSegal.spineEquiv]
    rw [← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one, op_comp,
      Functor.map_comp_apply, hσ, SimplexCategory.mkOfSucc_one_eq_δ,
      ← Functor.map_comp_apply, ← op_comp, δ₂_zero_comp_σ₂_one,
      op_comp, Functor.map_comp_apply, hδ₀]

/-- Auxiliary definition for `SSet.Truncated.liftOfStrictSegal`. -/
/-
**SSet.Truncated.liftOfStrictSegal.app** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated
.liftOfStrictSegal`。
形式化陈述：app (n : (SimplexCategory.Truncated 2)ᵒᵖ) : X.obj n ⟶ Y.obj n
参数：n : (SimplexCategory.Truncated 2)ᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `SSet.Truncated.liftOfStrictSegal`.
-/
def app (n : (SimplexCategory.Truncated 2)ᵒᵖ) : X.obj n ⟶ Y.obj n := by
  obtain ⟨⟨n⟩, hn⟩ := n
  match n with
  | 0 => exact ↾f₀
  | 1 => exact ↾f₁
  | 2 => exact ↾(f₂ f₀ f₁ hδ₁ hδ₀ hY)

/-- The property of morphisms in `SimplexCategory.Truncated 2` for
which `liftOfStrictSegal.app` is natural. -/
/-
**SSet.Truncated.liftOfStrictSegal.naturalityProperty** 是 Mathlib 中的一个缩写定义，位于命名空
间 `SSet.Truncated.liftOfStrictSegal`。
形式化陈述：naturalityProperty : MorphismProperty (SimplexCategory.Truncated 2)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of morphisms in `SimplexCategory.Truncated 2` for
which `liftOfStrictSegal.app` is natural.
-/
abbrev naturalityProperty : MorphismProperty (SimplexCategory.Truncated 2) :=
  (MorphismProperty.naturalityProperty (app f₀ f₁ hδ₁ hδ₀ hY)).unop

include H hσ in
/-
**SSet.Truncated.liftOfStrictSegal.naturalityProperty_eq_top** 是 Mathlib 中的一个引理，
位于命名空间 `SSet.Truncated.liftOfStrictSegal`。
形式化陈述：naturalityProperty_eq_top : naturalityProperty f₀ f₁ hδ₁ hδ₀ hY = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimplexCategory.Truncated.morphismProperty_eq_top`：∀ {d : ℕ} (W : Catego
ryTheory.MorphismProperty (SimplexCategory.Truncated d)) [W.IsMultiplicative],  
 (∀ (n : ℕ) (hn : n < d) (i : Fin (n + …
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `SSet.Truncated.liftOfStrictSegal.hδ'₀`：∀ {X Y : SSet.Truncated 2}   (f₀ 
:     X.obj (Opposite.op { obj := { len := 0 }, property := _proof_11✝ }) →     
  Y.obj (Opposite.op { obj …
· 使用定理 `SSet.Truncated.liftOfStrictSegal.hδ'₁`：∀ {X Y : SSet.Truncated 2}   (f₀ 
:     X.obj (Opposite.op { obj := { len := 0 }, property := _proof_11✝ }) →     
  Y.obj (Opposite.op { obj …
· 使用定理 `SSet.Truncated.liftOfStrictSegal.hδ'₂`：∀ {X Y : SSet.Truncated 2}   (f₀ 
:     X.obj (Opposite.op { obj := { len := 0 }, property := _proof_11✝ }) →     
  Y.obj (Opposite.op { obj …
· 使用定理 `SSet.Truncated.liftOfStrictSegal.hσ'₀`：∀ {X Y : SSet.Truncated 2}   (f₀ 
:     X.obj (Opposite.op { obj := { len := 0 }, property := _proof_11✝ }) →     
  Y.obj (Opposite.op { obj …
· 使用定理 `SSet.Truncated.liftOfStrictSegal.hσ'₁`：∀ {X Y : SSet.Truncated 2}   (f₀ 
:     X.obj (Opposite.op { obj := { len := 0 }, property := _proof_11✝ }) →     
  Y.obj (Opposite.op { obj …
-/
lemma naturalityProperty_eq_top :
    naturalityProperty f₀ f₁ hδ₁ hδ₀ hY = ⊤ := by
  refine SimplexCategory.Truncated.morphismProperty_eq_top _
    (fun n hn i ↦ ?_) (fun n hn i ↦ ?_)
  · obtain _ | _ | n := n
    · fin_cases i
      · ext; apply hδ₀
      · ext; apply hδ₁
    · fin_cases i
      · ext; apply hδ'₀ f₀ f₁ hδ₁ hδ₀ hY
      · ext; apply hδ'₁ f₀ f₁ hδ₁ hδ₀ H hY
      · ext; apply hδ'₂ f₀ f₁ hδ₁ hδ₀ hY
    · lia
  · obtain _ | _ | n := n
    · fin_cases i
      ext; apply hσ
    · fin_cases i
      · ext; apply hσ'₀ f₀ f₁ hδ₁ hδ₀ hσ hY
      · ext; apply hσ'₁ f₀ f₁ hδ₁ hδ₀ hσ hY
    · lia

end liftOfStrictSegal

open liftOfStrictSegal in
/-- Constructor for morphisms `X ⟶ Y` between `2`-truncated simplicial sets from
the data of maps on `0`- and `1`-simplices when `Y` is strict Segal. -/
/-
**SSet.Truncated.liftOfStrictSegal** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
形式化陈述：liftOfStrictSegal : X ⟶ Y where app
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms `X ⟶ Y` between `2`-truncated simplicial sets from
the data of maps on `0`- and `1`-simplices when `Y` is strict Segal.
-/
def liftOfStrictSegal : X ⟶ Y where
  app := liftOfStrictSegal.app f₀ f₁ hδ₁ hδ₀ hY
  naturality _ _ φ :=
    (liftOfStrictSegal.naturalityProperty_eq_top f₀ f₁ hδ₁ hδ₀ H hσ hY).symm.le
      φ.unop (by simp)

@[simp]
/-
**SSet.Truncated.liftOfStrictSegal_app_0** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncat
ed`。
形式化陈述：liftOfStrictSegal_app_0 : (liftOfStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (o
p ⦋0⦌₂) = ↾f₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma liftOfStrictSegal_app_0 :
    (liftOfStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (op ⦋0⦌₂) = ↾f₀ := rfl

@[simp]
/-
**SSet.Truncated.liftOfStrictSegal_app_1** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncat
ed`。
形式化陈述：liftOfStrictSegal_app_1 : (liftOfStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (o
p ⦋1⦌₂) = ↾f₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma liftOfStrictSegal_app_1 :
    (liftOfStrictSegal f₀ f₁ hδ₁ hδ₀ H hσ hY).app (op ⦋1⦌₂) = ↾f₁ := rfl

end liftOfStrictSegal

namespace HomotopyCategory

variable {X : Truncated.{u} 2} {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- Given a `2`-truncated simplicial set `X` and a category `C`,
this is the functor `X.HomotopyCategory ⥤ C` corresponding to
a morphism `X ⟶ (truncation 2).obj (nerve C)`. -/
/-
**SSet.Truncated.HomotopyCategory.descOfTruncation** 是 Mathlib 中的一个定义，位于命名空间 `SS
et.Truncated.HomotopyCategory`。
形式化陈述：descOfTruncation (φ : X ⟶ (truncation 2).obj (nerve C)) : X.HomotopyCatego
ry ⥤ C
参数：φ : X ⟶ (truncation 2).obj (nerve C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `2`-truncated simplicial set `X` and a category `C`,
this is the functor `X.HomotopyCategory ⥤ C` corresponding to
a morphism `X ⟶ (truncation 2).obj (nerve C)`.
-/
def descOfTruncation (φ : X ⟶ (truncation 2).obj (nerve C)) :
    X.HomotopyCategory ⥤ C :=
  lift (fun x ↦ nerveEquiv (φ.app _ x)) (fun e ↦ nerve.homEquiv (e.map φ))
    (fun x ↦ by simpa using! nerve.homEquiv_id (φ.app _ x))
      (fun h ↦ nerve.homEquiv_comp (h.map φ))

@[simp]
/-
**SSet.Truncated.HomotopyCategory.descOfTruncation_obj_mk** 是 Mathlib 中的一个引理，位于命
名空间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：descOfTruncation_obj_mk (φ : X ⟶ (truncation 2).obj (nerve C)) (x : X _⦋0⦌
₂) : (descOfTruncation φ).obj (mk x) = nerveEquiv (φ.app _ x)
参数：φ : X ⟶ (truncation 2).obj (nerve C)；x : X _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma descOfTruncation_obj_mk (φ : X ⟶ (truncation 2).obj (nerve C)) (x : X _⦋0⦌₂) :
    (descOfTruncation φ).obj (mk x) = nerveEquiv (φ.app _ x) := rfl

@[simp]
/-
**SSet.Truncated.HomotopyCategory.descOfTruncation_map_homMk** 是 Mathlib 中的一个引理，
位于命名空间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：descOfTruncation_map_homMk (φ : X ⟶ (truncation 2).obj (nerve C)) {x₀ x₁ :
 X _⦋0⦌₂} (e : Edge x₀ x₁) : (descOfTruncation φ).map (homMk e) = nerve.homEquiv
 (e.map φ)
参数：φ : X ⟶ (truncation 2).obj (nerve C)；e : Edge x₀ x₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma descOfTruncation_map_homMk (φ : X ⟶ (truncation 2).obj (nerve C))
    {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) :
    (descOfTruncation φ).map (homMk e) = nerve.homEquiv (e.map φ) :=
  Category.id_comp _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**SSet.Truncated.HomotopyCategory.descOfTruncation_comp** 是 Mathlib 中的一个引理，位于命名空
间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：descOfTruncation_comp {X' : Truncated.{u} 2} (ψ : X ⟶ X') (φ : X' ⟶ (trunc
ation 2).obj (nerve C)) : descOfTruncation (ψ ≫ φ) = mapHomotopyCategory ψ ⋙ des
cOfTruncation φ
参数：ψ : X ⟶ X'；φ : X' ⟶ (truncation 2).obj (nerve C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.HomotopyCategory.functor_ext`：functor_ext {F G : V.Homoto
pyCategory ⥤ D} (h₁ : forall (x : V _⦋0⦌₂), F.obj (mk x) = G.obj (mk x)) (h₂ : f
orall ⦃x y : V _⦋0⦌₂⦄ (e : Edge x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SSet.Truncated.HomotopyCategory.descOfTruncation_map_homMk`：descOfTrunca
tion_map_homMk (φ : X ⟶ (truncation 2).obj (nerve C)) {x₀ x₁ : X _⦋0⦌₂} (e : Edg
e x₀ x₁) : (descOfTruncation φ).map (homMk e) = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma descOfTruncation_comp {X' : Truncated.{u} 2} (ψ : X ⟶ X')
    (φ : X' ⟶ (truncation 2).obj (nerve C)) :
    descOfTruncation (ψ ≫ φ) = mapHomotopyCategory ψ ⋙ descOfTruncation φ :=
  functor_ext (fun _ ↦ by simp) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a `2`-truncated simplicial set `X` and a category `C`,
this is the morphism `X ⟶ (truncation 2).obj (nerve C)` corresponding
to a functor `X.HomotopyCategory ⥤ C`. -/
/-
**SSet.Truncated.HomotopyCategory.homToNerveMk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.T
runcated.HomotopyCategory`。
形式化陈述：homToNerveMk (F : X.HomotopyCategory ⥤ C) : X ⟶ (truncation 2).obj (nerve 
C)
参数：F : X.HomotopyCategory ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a `2`-truncated simplicial set `X` and a category `C`,
this is the morphism `X ⟶ (truncation 2).obj (nerve C)` corresponding
to a functor `X.HomotopyCategory ⥤ C`.
-/
def homToNerveMk (F : X.HomotopyCategory ⥤ C) : X ⟶ (truncation 2).obj (nerve C) :=
  liftOfStrictSegal (fun x ↦ nerveEquiv.symm (F.obj (mk x)))
    (fun f ↦ ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f))))
    (fun f ↦ ComposableArrows.ext₀ rfl)
    (fun f ↦ ComposableArrows.ext₀ rfl)
    (fun x y h₂ h₀ ↦ by
      have h' {a b : X _⦋0⦌₂} (e : Edge a b) :
          ComposableArrows.mk₁ (F.map (homMk (Edge.mk' e.edge))) =
            ComposableArrows.mk₁ (F.map (homMk e)) :=
        ComposableArrows.arrowEquiv.injective
          (congr_arg F.mapArrow.obj (congr_arrowMk_homMk (Edge.mk' e.edge) e rfl))
      obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, h, rfl⟩ := Edge.CompStruct.exists_of_simplex x
      dsimp at h₀ h₂ ⊢
      have : ComposableArrows.mk₂ (F.map (homMk e₀₁)) (F.map (homMk e₁₂)) = y := by
        rw [h.d₂, h'] at h₂
        rw [h.d₀, h'] at h₀
        refine (spine_bijective (X := (truncation 2).obj (nerve C)) _ _).injective ?_
        ext i
        fin_cases i
        · dsimp
          simp only [SimplexCategory.mkOfSucc_zero_eq_δ, ← h₂]
          apply nerve.δ₂_mk₂_eq
        · dsimp
          simp only [SimplexCategory.mkOfSucc_one_eq_δ, ← h₀]
          apply nerve.δ₀_mk₂_eq
      rw [h.d₁, ← this]
      have := (nerve.δ₁_mk₂_eq (F.map (homMk e₀₁)) (F.map (homMk e₁₂))).symm
      rwa [← Functor.map_comp, homMk_comp_homMk h, ← h'] at this)
    (fun x ↦ ComposableArrows.arrowEquiv.injective
      ((congr_arg F.mapArrow.obj
        (congr_arrowMk_homMk (Edge.mk' (X.map (σ₂ 0).op x)) (Edge.id x) rfl)).trans (by aesop)))
    ((Nerve.strictSegal C).truncation 1)

@[simp]
/-
**SSet.Truncated.HomotopyCategory.homToNerveMk_app_zero** 是 Mathlib 中的一个引理，位于命名空
间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：homToNerveMk_app_zero (F : X.HomotopyCategory ⥤ C) (x : X _⦋0⦌₂) : (homToN
erveMk F).app _ x = nerveEquiv.symm (F.obj (mk x))
参数：F : X.HomotopyCategory ⥤ C；x : X _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homToNerveMk_app_zero (F : X.HomotopyCategory ⥤ C) (x : X _⦋0⦌₂) :
    (homToNerveMk F).app _ x = nerveEquiv.symm (F.obj (mk x)) := rfl
/-
**SSet.Truncated.HomotopyCategory.homToNerveMk_app_one** 是 Mathlib 中的一个引理，位于命名空间
 `SSet.Truncated.HomotopyCategory`。
形式化陈述：homToNerveMk_app_one (F : X.HomotopyCategory ⥤ C) (f : X _⦋1⦌₂) : (homToNe
rveMk F).app _ f = ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f)))
参数：F : X.HomotopyCategory ⥤ C；f : X _⦋1⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homToNerveMk_app_one (F : X.HomotopyCategory ⥤ C) (f : X _⦋1⦌₂) :
    (homToNerveMk F).app _ f =
      ComposableArrows.mk₁ (F.map (homMk (Truncated.Edge.mk' f))) :=
  rfl

@[simp]
/-
**SSet.Truncated.HomotopyCategory.homToNerveMk_app_edge** 是 Mathlib 中的一个引理，位于命名空
间 `SSet.Truncated.HomotopyCategory`。
形式化陈述：homToNerveMk_app_edge (F : X.HomotopyCategory ⥤ C) {x y : X _⦋0⦌₂} (e : Ed
ge x y) : (homToNerveMk F).app _ e.edge = ComposableArrows.mk₁ (F.map (homMk e))
参数：F : X.HomotopyCategory ⥤ C；e : Edge x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Truncated.HomotopyCategory.homToNerveMk_app_one`：homToNerveMk_app_o
ne (F : X.HomotopyCategory ⥤ C) (f : X _⦋1⦌₂) : (homToNerveMk F).app _ f = Compo
sableArrows.mk₁ (F.map (homMk (Truncated.E…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk`：congr_arrowMk_homMk
 {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁) {y₀ y₁ : V _⦋0⦌₂} (e' : Edge y₀ y₁) (h : e.e
dge = e'.edge) : Arrow.mk (homMk e) = Arr…
-/
lemma homToNerveMk_app_edge (F : X.HomotopyCategory ⥤ C) {x y : X _⦋0⦌₂} (e : Edge x y) :
    (homToNerveMk F).app _ e.edge =
      ComposableArrows.mk₁ (F.map (homMk e)) := by
  rw [homToNerveMk_app_one]
  exact ComposableArrows.arrowEquiv.injective
    (congr_arg F.mapArrow.obj (congr_arrowMk_homMk (Edge.mk' e.edge) e rfl))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a `2`-truncated simplicial set `X` and a category `C`,
this is the bijection between morphism `X.HomotopyCategory ⥤ C`
and `X ⟶ (truncation 2).obj (nerve C)` which is part of the adjunction
`SSet.Truncated.nerve₂Adj`. -/
/-
**SSet.Truncated.HomotopyCategory.functorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.T
runcated.HomotopyCategory`。
形式化陈述：functorEquiv : (X.HomotopyCategory ⥤ C) ≃ (X ⟶ (truncation 2).obj (nerve C
)) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `2`-truncated simplicial set `X` and a category `C`,
this is the bijection between morphism `X.HomotopyCategory ⥤ C`
and `X ⟶ (truncation 2).obj (nerve C)` which is part of the adjunction
`SSet.Truncated.nerve₂Adj`.
-/
def functorEquiv :
    (X.HomotopyCategory ⥤ C) ≃ (X ⟶ (truncation 2).obj (nerve C)) where
  toFun := homToNerveMk
  invFun := descOfTruncation
  left_inv F :=
    functor_ext (fun x ↦ by simp) (fun x y f ↦ by
      dsimp
      simp only [Category.comp_id, Category.id_comp, descOfTruncation_map_homMk,
        homToNerveMk_app_zero]
      exact nerve.homEquiv.symm.injective (Edge.ext (by cat_disch)))
  right_inv φ :=
    IsStrictSegal.hom_ext (fun s ↦ by
      obtain ⟨x₀, x₁, f, rfl⟩ := Edge.exists_of_simplex s
      dsimp [nerve.homEquiv]
      simp only [homToNerveMk_app_edge, descOfTruncation_obj_mk,
        descOfTruncation_map_homMk]
      refine ComposableArrows.ext₁ ?_ ?_ rfl
      · dsimp [nerveEquiv, ComposableArrows.right]
        simp only [← f.src_eq, NatTrans.naturality_apply]
        rfl
      · dsimp [nerveEquiv, ComposableArrows.right]
        simp only [← f.tgt_eq, NatTrans.naturality_apply]
        rfl)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**SSet.Truncated.HomotopyCategory.homToNerveMk_comp** 是 Mathlib 中的一个引理，位于命名空间 `S
Set.Truncated.HomotopyCategory`。
形式化陈述：homToNerveMk_comp {D : Type u} [SmallCategory D] (F : X.HomotopyCategory ⥤
 C) (G : C ⥤ D) : homToNerveMk (F ⋙ G) = homToNerveMk F ≫ (truncation 2).map (ne
rveMap G)
参数：F : X.HomotopyCategory ⥤ C；G : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Truncated.IsStrictSegal.hom_ext`：∀ {n : ℕ} {X Y : SSet.Truncated (n
 + 1)} [Y.IsStrictSegal] {f g : X ⟶ Y},   (∀ (x : X.obj (Opposite.op { obj := { 
len := 1 }, property := ⋯ …
· 使用定理 `SSet.StrictSegal.instIsStrictSegalObjTruncatedHAddNatOfNatTruncationOfIs
StrictSegal`：∀ {X : _root_.SSet} [X.IsStrictSegal] (n : ℕ), ((SSet.truncation (n
 + 1)).obj X).IsStrictSegal
· 使用引理 `SSet.Truncated.Edge.exists_of_simplex`：exists_of_simplex (s : X _⦋1⦌₂) :
 exists (x₀ x₁ : X _⦋0⦌₂) (e : Edge x₀ x₁), e.edge = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Truncated.HomotopyCategory.homToNerveMk_app_edge`：homToNerveMk_app_
edge (F : X.HomotopyCategory ⥤ C) {x y : X _⦋0⦌₂} (e : Edge x y) : (homToNerveMk
 F).app _ e.edge = ComposableArrows.mk₁ (F.…
· 使用引理 `CategoryTheory.ComposableArrows.ext₁`：ext₁ {F G : ComposableArrows C 1} 
(left : F.left = G.left) (right : F.right = G.right) (w : F.hom = eqToHom left ≫
 G.hom ≫ eqToHom right.sym…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ComposableArrows.mk₁_map`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] {X₀ X₁ : C} (f : X₀ ⟶ X₁) {X Y : Fin (1 + 1)}   
(g : X ⟶ Y), (CategoryTheory.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma homToNerveMk_comp {D : Type u} [SmallCategory D]
    (F : X.HomotopyCategory ⥤ C) (G : C ⥤ D) :
    homToNerveMk (F ⋙ G) = homToNerveMk F ≫ (truncation 2).map (nerveMap G) :=
  IsStrictSegal.hom_ext (fun s ↦ by
    obtain ⟨x₀, x₁, f, rfl⟩ := Edge.exists_of_simplex s
    dsimp
    simp only [homToNerveMk_app_edge, Functor.comp_map]
    exact ComposableArrows.ext₁ rfl rfl (by aesop))

end HomotopyCategory

/-- The adjunction between the 2-truncated homotopy category functor
and the 2-truncated nerve functor. -/
/-
**SSet.Truncated.nerve** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the 2-truncated homotopy category functor
and the 2-truncated nerve functor.
-/
def nerve₂Adj : hoFunctor₂.{u} ⊣ nerveFunctor₂ :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (Cat.Hom.equivFunctor _ _).trans HomotopyCategory.functorEquiv
      homEquiv_naturality_left_symm _ _ := by ext1; exact HomotopyCategory.descOfTruncation_comp _ _
      homEquiv_naturality_right _ _ := HomotopyCategory.homToNerveMk_comp _ _ }

end Truncated

end SSet

namespace CategoryTheory

namespace nerve

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `C ⥤ D` that is reconstructed for a morphism
between the `2`-truncated nerves. -/
@[simps]
/-
**CategoryTheory.nerve.functorOfNerveMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.nerve`。
形式化陈述：functorOfNerveMap (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of 
D)) : C ⥤ D where obj x
参数：φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The functor `C ⥤ D` that is reconstructed for a morphism
between the `2`-truncated nerves.
-/
def functorOfNerveMap (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D)) :
    C ⥤ D where
  obj x := nerveEquiv (φ.app (op ⟨⦋0⦌, by simp⟩) (nerveEquiv.symm x))
  map f := nerve.homEquiv ((nerve.edgeMk f).toTruncated.map φ)
  map_id x := by
    rw [edgeMk_id, SSet.Edge.toTruncated_id, SSet.Truncated.Edge.map_id]
    exact nerve.homEquiv_id _
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact (nerve.homEquiv_comp (h.toTruncated.map φ)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.nerve.nerveFunctor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ne
rve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nerveFunctor₂_map_functorOfNerveMap
    (φ : nerveFunctor₂.obj (.of C) ⟶ nerveFunctor₂.obj (.of D)) :
    nerveFunctor₂.map (functorOfNerveMap φ).toCatHom = φ :=
  SSet.Truncated.IsStrictSegal.hom_ext (fun f ↦ by
    obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective f
    exact (nerveMap_app_mk₁ _ _).trans ((nerve.mk₁_homEquiv_apply _).trans
      (ComposableArrows.mk₁_hom _)))

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.nerve.functorOfNerveMap_nerveFunctor** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorOfNerveMap_nerveFunctor₂_map (F : C ⥤ D) :
    functorOfNerveMap ((SSet.truncation 2).map (nerveMap F)) = F :=
  Functor.ext (fun x ↦ by cat_disch) (fun x y f ↦ by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
/-- The `2`-truncated nerve functor is fully faithful. -/
/-
**CategoryTheory.nerve.fullyFaithfulNerveFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `2`-truncated nerve functor is fully faithful.
-/
def fullyFaithfulNerveFunctor₂ : nerveFunctor₂.{u, u}.FullyFaithful where
  preimage φ := (functorOfNerveMap φ).toCatHom
  map_preimage _ := nerveFunctor₂_map_functorOfNerveMap _
  preimage_map _ := by ext1; exact functorOfNerveMap_nerveFunctor₂_map _
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : nerveFunctor₂.{u, u}.Faithful :=
  (fullyFaithfulNerveFunctor₂).faithful
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : nerveFunctor₂.{u, u}.Full :=
  (fullyFaithfulNerveFunctor₂).full
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Reflective nerveFunctor₂.{u, u} := Reflective.mk _ SSet.Truncated.nerve₂Adj

end nerve

open SSet

/-- The adjunction between the nerve functor and the homotopy category functor is, up to
isomorphism, the composite of the adjunctions `SSet.coskAdj 2` and `nerve₂Adj`. -/
/-
**CategoryTheory.nerveAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：nerveAdjunction : hoFunctor ⊣ nerveFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the nerve functor and the homotopy category functor is, u
p to
isomorphism, the composite of the adjunctions `SSet.coskAdj 2` and `nerve₂Adj`.
-/
noncomputable def nerveAdjunction : hoFunctor ⊣ nerveFunctor :=
  Adjunction.ofNatIsoRight ((SSet.coskAdj 2).comp Truncated.nerve₂Adj) Nerve.cosk₂Iso.symm


/-- Repleteness exists for full and faithful functors but not fully faithful functors, which is
why we do this inefficiently. -/
/-
**CategoryTheory.nerveFunctor.faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.nerveFunctor`。
形式化陈述：CategoryTheory.nerveFunctor.Faithful
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.of_iso`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {F F' : CategoryTh…
· 使用定理 `CategoryTheory.Functor.Faithful.comp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.nerve.instFaithfulCatTruncatedOfNatNatNerveFunctor₂`：Cate
goryTheory.Nerve.nerveFunctor₂.Faithful
· 使用定理 `SSet.Truncated.cosk.faithful`：∀ (n : ℕ), (SSet.Truncated.cosk n).Faithfu
l

--- 原说明 ---
Repleteness exists for full and faithful functors but not fully faithful functor
s, which is
why we do this inefficiently.
-/
instance nerveFunctor.faithful : nerveFunctor.{u, u}.Faithful :=
  Functor.Faithful.of_iso Nerve.cosk₂Iso.symm
/-
**CategoryTheory.nerveFunctor.full** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ner
veFunctor`。
形式化陈述：CategoryTheory.nerveFunctor.Full
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.of_iso`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F F' : CategoryTh…
· 使用定理 `CategoryTheory.Functor.Full.comp`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.nerve.instFullCatTruncatedOfNatNatNerveFunctor₂`：Category
Theory.Nerve.nerveFunctor₂.Full
· 使用定理 `SSet.Truncated.cosk.full`：∀ (n : ℕ), (SSet.Truncated.cosk n).Full
-/
instance nerveFunctor.full : nerveFunctor.{u, u}.Full :=
  Functor.Full.of_iso Nerve.cosk₂Iso.symm

/-- The nerve functor is both full and faithful and thus is fully faithful. -/
/-
**CategoryTheory.nerveFunctor.fullyfaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.nerveFunctor`。
形式化陈述：CategoryTheory.nerveFunctor.FullyFaithful
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.nerveFunctor.full`：CategoryTheory.nerveFunctor.Full
· 使用定理 `CategoryTheory.nerveFunctor.faithful`：CategoryTheory.nerveFunctor.Faithf
ul

--- 原说明 ---
The nerve functor is both full and faithful and thus is fully faithful.
-/
noncomputable def nerveFunctor.fullyfaithful : nerveFunctor.FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _
/-
**CategoryTheory.nerveAdjunction.isIso_counit** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.nerveAdjunction`。
形式化陈述：CategoryTheory.IsIso CategoryTheory.nerveAdjunction.counit
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.nerveFunctor.full`：CategoryTheory.nerveFunctor.Full
· 使用定理 `CategoryTheory.nerveFunctor.faithful`：CategoryTheory.nerveFunctor.Faithf
ul
-/
instance nerveAdjunction.isIso_counit : IsIso nerveAdjunction.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- The counit map of `nerveAdjunction` is an isomorphism since the nerve functor is fully
faithful. -/
/-
**CategoryTheory.nerveFunctorCompHoFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory`。
形式化陈述：nerveFunctorCompHoFunctorIso : nerveFunctor.{u, u} ⋙ hoFunctor ≅ 𝟭 Cat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.nerveAdjunction.isIso_counit`：CategoryTheory.IsIso Catego
ryTheory.nerveAdjunction.counit

--- 原说明 ---
The counit map of `nerveAdjunction` is an isomorphism since the nerve functor is
 fully
faithful.
-/
noncomputable def nerveFunctorCompHoFunctorIso : nerveFunctor.{u, u} ⋙ hoFunctor ≅ 𝟭 Cat :=
  asIso (nerveAdjunction.counit)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Reflective nerveFunctor where
  L := hoFunctor
  adj := nerveAdjunction

section

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C D : Type u) [Category.{u} C] [Category.{u} D] :
    IsIso (prodComparison (nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor)
      (Cat.of C) (Cat.of D)) := by
  let iso : nerveFunctor ⋙ hoFunctor ⋙ nerveFunctor ≅ nerveFunctor :=
    (nerveFunctor.associator hoFunctor nerveFunctor).symm ≪≫
      Functor.isoWhiskerRight nerveFunctorCompHoFunctorIso nerveFunctor ≪≫
        nerveFunctor.leftUnitor
  exact IsIso.of_isIso_fac_right (prodComparison_natural_of_natTrans iso.hom).symm

namespace hoFunctor

/-
**CategoryTheory.hoFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.hoFunctor`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : hoFunctor.IsLeftAdjoint := nerveAdjunction.isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.hoFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.hoFunctor`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C D : Type u) [Category.{u} C] [Category.{u} D] :
    IsIso (prodComparison hoFunctor (nerve C) (nerve D)) := by
  have : IsIso (nerveFunctor.map (prodComparison hoFunctor (nerve C) (nerve D))) := by
    have : IsIso (prodComparison (hoFunctor ⋙ nerveFunctor) (nerve C) (nerve D)) :=
      IsIso.of_isIso_fac_left
        (prodComparison_comp nerveFunctor (hoFunctor ⋙ nerveFunctor)
          (A := Cat.of C) (B := Cat.of D)).symm
    exact IsIso.of_isIso_fac_right (prodComparison_comp hoFunctor nerveFunctor).symm
  exact isIso_of_fully_faithful nerveFunctor _
/-
**CategoryTheory.hoFunctor.isIso_prodComparison_stdSimplex.** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.hoFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_prodComparison_stdSimplex.{w} (n m : ℕ) :
    IsIso (prodComparison hoFunctor (Δ[n] : SSet.{w}) Δ[m]) :=
  IsIso.of_isIso_fac_right (prodComparison_natural.{w}
    hoFunctor (stdSimplex.isoNerve n).hom (stdSimplex.isoNerve m).hom).symm
/-
**CategoryTheory.hoFunctor.isIso_prodComparison_of_stdSimplex** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.hoFunctor`。
形式化陈述：isIso_prodComparison_of_stdSimplex {D : SSet.{u}} (X : SSet.{u}) (H : fora
ll m, IsIso (prodComparison hoFunctor D Δ[m])) : IsIso (prodComparison hoFunctor
 D X)
参数：X : SSet.{u}；H : forall m, IsIso (prodComparison hoFunctor D Δ[m])。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Limits.isIso_app_coconePt_of_preservesColimit`：isIso_app_
coconePt_of_preservesColimit {C D J : Type*} [Category* C] [Category* D] [Catego
ry* J] (K : J ⥤ C) {L L' : C ⥤ D} (α : L ⟶ L') [Is…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.isLeftAdjoint_prod_functor`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.C
artesianMonoidalCategory C] (A : C)   [CategoryTheory.Clo…
· 使用定理 `CategoryTheory.hoFunctor.instIsLeftAdjointSSetCatHoFunctor`：SSet.hoFunct
or.IsLeftAdjoint
-/
lemma isIso_prodComparison_of_stdSimplex {D : SSet.{u}} (X : SSet.{u})
    (H : ∀ m, IsIso (prodComparison hoFunctor D Δ[m])) :
    IsIso (prodComparison hoFunctor D X) := by
  have : IsIso (Functor.whiskerLeft (CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda)
      (prodComparisonNatTrans hoFunctor.{u} D)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun x ↦ H (x.left).len
  exact isIso_app_coconePt_of_preservesColimit _ (prodComparisonNatTrans hoFunctor _) _
    (Presheaf.isColimitTautologicalCocone' X)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.hoFunctor.isIso_prodComparison** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.hoFunctor`。
形式化陈述：isIso_prodComparison (X Y : SSet) : IsIso (prodComparison hoFunctor.{u} X 
Y)
参数：X Y : SSet。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.hoFunctor.isIso_prodComparison_of_stdSimplex`：isIso_prodC
omparison_of_stdSimplex {D : SSet.{u}} (X : SSet.{u}) (H : forall m, IsIso (prod
Comparison hoFunctor D Δ[m])) : IsIso (prodCompar…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用引理 `CategoryTheory.Cat.ext`：ext {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F.toFu
nctor = G.toFunctor) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prodComparison_fst`：prodComparison_fst : prodCompa
rison F A B ≫ prod.fst = F.map prod.fst
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.braiding_hom`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] (P Q : C) [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct P Q]   [inst_2 : Categor…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.prodComparison_snd`：prodComparison_snd : prodCompa
rison F A B ≫ prod.snd = F.map prod.snd
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIso_prodComparison (X Y : SSet) :
    IsIso (prodComparison hoFunctor.{u} X Y) := isIso_prodComparison_of_stdSimplex _ fun m ↦ by
  convert_to IsIso (hoFunctor.map (prod.braiding _ _).hom ≫
    prodComparison hoFunctor Δ[m] X ≫ (prod.braiding _ _).hom)
  · ext <;> simp [← Functor.map_comp]
  suffices IsIso (prodComparison hoFunctor Δ[m] X) by infer_instance
  exact isIso_prodComparison_of_stdSimplex _ (isIso_prodComparison_stdSimplex _)

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of simplicial sets `X` and
`Y`. -/
/-
**CategoryTheory.hoFunctor.preservesBinaryProduct** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.hoFunctor`。
形式化陈述：preservesBinaryProduct (X Y : SSet) : PreservesLimit (pair X Y) hoFunctor
参数：X Y : SSet。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitPair.of_iso_prod_comparison`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The functor `hoFunctor : SSet ⥤ Cat` preserves binary products of simplicial set
s `X` and
`Y`.
-/
instance preservesBinaryProduct (X Y : SSet) :
    PreservesLimit (pair X Y) hoFunctor :=
  PreservesLimitPair.of_iso_prod_comparison hoFunctor X Y

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves limits of functors out of
`Discrete WalkingPair`. -/
/-
**CategoryTheory.hoFunctor.preservesBinaryProducts** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.hoFunctor`。
形式化陈述：preservesBinaryProducts : PreservesLimitsOfShape (Discrete WalkingPair) ho
Functor where preservesLimit {F}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t

--- 原说明 ---
The functor `hoFunctor : SSet ⥤ Cat` preserves limits of functors out of
`Discrete WalkingPair`.
-/
instance preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) hoFunctor where
  preservesLimit {F} := preservesLimit_of_iso_diagram hoFunctor (diagramIsoPair F).symm

/-- The functor `hoFunctor : SSet ⥤ Cat` preserves finite products of simplicial sets. -/
/-
**CategoryTheory.hoFunctor.preservesFiniteProducts** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.hoFunctor`。
形式化陈述：preservesFiniteProducts : PreservesFiniteProducts hoFunctor
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesFiniteProducts.of_preserves_binary_and_te
rminal`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [
inst_1 : CategoryTheory.Category.{v', u'} D]   (F : CategoryTheory.F…
· 使用定理 `SSet.hoFunctor.preservesTerminal'`：CategoryTheory.Limits.PreservesLimits
OfShape (CategoryTheory.Discrete PEmpty.{1}) SSet.hoFunctor
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…

--- 原说明 ---
The functor `hoFunctor : SSet ⥤ Cat` preserves finite products of simplicial set
s.
-/
instance preservesFiniteProducts : PreservesFiniteProducts hoFunctor :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

end hoFunctor

end

end CategoryTheory

