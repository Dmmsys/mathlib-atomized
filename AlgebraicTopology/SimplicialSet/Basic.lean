/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.FinCases

/-!
# Simplicial sets

A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to call these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

-/

@[expose] public section

universe v u

open CategoryTheory Limits Functor ConcreteCategory

open Simplicial

/-- The category of simplicial sets.
This is the category of contravariant functors from
`SimplexCategory` to `Type u`. -/
/-
**SSet** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：SSet : Type (u + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of simplicial sets.
This is the category of contravariant functors from
`SimplexCategory` to `Type u`.
-/
abbrev SSet : Type (u + 1) :=
  SimplicialObject (Type u)

namespace SSet

@[ext]
/-
**SSet.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : forall n, f.app n = g.app n) : f =
 g
参数：w : forall n, f.app n = g.app n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SimplicialObject.hom_ext`：hom_ext {X Y : SimplicialObject
 C} (f g : X ⟶ Y) (h : forall (n : SimplexCategoryᵒᵖ), f.app n = g.app n) : f = 
g
-/
lemma hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) : f = g :=
  SimplicialObject.hom_ext _ _ w

@[simp]
/-
**SSet.id_app** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：id_app (X : SSet) (n : SimplexCategoryᵒᵖ) : NatTrans.app (𝟙 X) n = 𝟙 _
参数：X : SSet；n : SimplexCategoryᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_app (X : SSet) (n : SimplexCategoryᵒᵖ) :
    NatTrans.app (𝟙 X) n = 𝟙 _ := rfl

@[simp, reassoc]
/-
**SSet.comp_app** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：comp_app {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) : 
(f ≫ g).app n = f.app n ≫ g.app n
参数：f : X ⟶ Y；g : Y ⟶ Z；n : SimplexCategoryᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_app {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- The constant map of simplicial sets `X ⟶ Y` induced by a simplex `y : Y _[0]`. -/
@[simps]
/-
**SSet.const** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：const {X Y : SSet.{u}} (y : Y _⦋0⦌) : X ⟶ Y where app n
参数：y : Y _⦋0⦌。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant map of simplicial sets `X ⟶ Y` induced by a simplex `y : Y _[0]`.
-/
def const {X Y : SSet.{u}} (y : Y _⦋0⦌) : X ⟶ Y where
  app n := ↾fun _ ↦ Y.map (n.unop.const _ 0).op y
  naturality _ _ _ := by
    ext
    dsimp
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    rfl

@[simp]
/-
**SSet.comp_const** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：comp_const {X Y Z : SSet.{u}} (f : X ⟶ Y) (z : Z _⦋0⦌) : f ≫ const z = con
st z
参数：f : X ⟶ Y；z : Z _⦋0⦌。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_const {X Y Z : SSet.{u}} (f : X ⟶ Y) (z : Z _⦋0⦌) :
    f ≫ const z = const z := rfl

@[simp]
/-
**SSet.const_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：const_comp {X Y Z : SSet.{u}} (y : Y _⦋0⦌) (g : Y ⟶ Z) : const (X
参数：y : Y _⦋0⦌；g : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.hom_ext`：hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : forall n, f.app n 
= g.app n) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.const_app`：∀ {X Y : _root_.SSet} (y : Y.obj (Opposite.op { len := 0
 })) (n : SimplexCategoryᵒᵖ),   (SSet.const y).app n =     TypeCat.ofHom fun x =
> (C…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma const_comp {X Y Z : SSet.{u}} (y : Y _⦋0⦌) (g : Y ⟶ Z) :
    const (X := X) y ≫ g = const (g.app _ y) := by
  cat_disch

/-- The ulift functor `SSet.{u} ⥤ SSet.{max u v}` on simplicial sets. -/
/-
**SSet.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：uliftFunctor : SSet.{u} ⥤ SSet.{max u v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ulift functor `SSet.{u} ⥤ SSet.{max u v}` on simplicial sets.
-/
def uliftFunctor : SSet.{u} ⥤ SSet.{max u v} :=
  (SimplicialObject.whiskering _ _).obj CategoryTheory.uliftFunctor.{v, u}

/-- The functor which sends `n : SimplexCategoryᵒᵖ` to the evaluation
functor `SSet.{u} ⥤ Type u` on the object `n`. -/
/-
**SSet.evaluation** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：CategoryTheory.Functor SimplexCategoryᵒᵖ (CategoryTheory.Functor _root_.SS
et (Type u))
参数：CategoryTheory.Functor _root_.SSet (Type u)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends `n : SimplexCategoryᵒᵖ` to the evaluation
functor `SSet.{u} ⥤ Type u` on the object `n`.
-/
protected abbrev evaluation : SimplexCategoryᵒᵖ ⥤ SSet.{u} ⥤ Type u :=
  evaluation _ _

/-- Truncated simplicial sets. -/
/-
**SSet.Truncated** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：Truncated (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Truncated simplicial sets.
-/
abbrev Truncated (n : ℕ) := SimplicialObject.Truncated (Type u) n

namespace Truncated

/-- The ulift functor `SSet.Truncated.{u} ⥤ SSet.Truncated.{max u v}` on truncated
simplicial sets. -/
/-
**SSet.Truncated.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
形式化陈述：uliftFunctor (k : Nat) : SSet.Truncated.{u} k ⥤ SSet.Truncated.{max u v} k
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ulift functor `SSet.Truncated.{u} ⥤ SSet.Truncated.{max u v}` on truncated
simplicial sets.
-/
def uliftFunctor (k : ℕ) : SSet.Truncated.{u} k ⥤ SSet.Truncated.{max u v} k :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

@[ext]
/-
**SSet.Truncated.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`。
形式化陈述：hom_ext {n : Nat} {X Y : Truncated n} {f g : X ⟶ Y} (w : forall n, f.app n
 = g.app n) : f = g
参数：w : forall n, f.app n = g.app n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {n : ℕ} {X Y : Truncated n} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) :
    f = g :=
  NatTrans.ext (funext w)

/-- Further truncation of truncated simplicial sets. -/
/-
**SSet.Truncated.trunc** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.Truncated`。
形式化陈述：trunc (n m : Nat) (h : m <= n
参数：n m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Further truncation of truncated simplicial sets.
-/
abbrev trunc (n m : ℕ) (h : m ≤ n := by lia) :
    SSet.Truncated n ⥤ SSet.Truncated m :=
  SimplicialObject.Truncated.trunc (Type u) n m

@[simp]
/-
**SSet.Truncated.id_app** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`。
形式化陈述：id_app {n : Nat} (X : Truncated n) (d : (SimplexCategory.Truncated n)ᵒᵖ) :
 NatTrans.app (𝟙 X) d = 𝟙 _
参数：X : Truncated n；d : (SimplexCategory.Truncated n)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_app {n : ℕ} (X : Truncated n) (d : (SimplexCategory.Truncated n)ᵒᵖ) :
    NatTrans.app (𝟙 X) d = 𝟙 _ :=
  rfl

@[simp, reassoc]
/-
**SSet.Truncated.comp_app** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated`。
形式化陈述：comp_app {n : Nat} {X Y Z : Truncated n} (f : X ⟶ Y) (g : Y ⟶ Z) (d : (Sim
plexCategory.Truncated n)ᵒᵖ) : (f ≫ g).app d = f.app d ≫ g.app d
参数：f : X ⟶ Y；g : Y ⟶ Z；d : (SimplexCategory.Truncated n)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_app {n : ℕ} {X Y Z : Truncated n} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : (SimplexCategory.Truncated n)ᵒᵖ) :
    (f ≫ g).app d = f.app d ≫ g.app d :=
  rfl

end Truncated

/-- The truncation functor on simplicial sets. -/
/-
**SSet.truncation** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：truncation (n : Nat) : SSet ⥤ SSet.Truncated n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The truncation functor on simplicial sets.
-/
abbrev truncation (n : ℕ) : SSet ⥤ SSet.Truncated n := SimplicialObject.truncation n

/-- For all `m ≤ n`, `truncation m` factors through `SSet.Truncated n`. -/
/-
**SSet.truncationCompTrunc** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：truncationCompTrunc {n m : Nat} (h : m <= n) : truncation n ⋙ Truncated.tr
unc n m ≅ truncation m
参数：h : m <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For all `m ≤ n`, `truncation m` factors through `SSet.Truncated n`.
-/
def truncationCompTrunc {n m : ℕ} (h : m ≤ n) :
    truncation n ⋙ Truncated.trunc n m ≅ truncation m :=
  Iso.refl _

open SimplexCategory

noncomputable section

/-- The n-skeleton as a functor `SSet.Truncated n ⥤ SSet`. -/
/-
**SSet.Truncated.sk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
形式化陈述：(n : ℕ) → CategoryTheory.Functor (SSet.Truncated n) _root_.SSet
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-skeleton as a functor `SSet.Truncated n ⥤ SSet`.
-/
protected abbrev Truncated.sk (n : ℕ) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.sk n

/-- The n-coskeleton as a functor `SSet.Truncated n ⥤ SSet`. -/
/-
**SSet.Truncated.cosk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated`。
形式化陈述：(n : ℕ) → CategoryTheory.Functor (SSet.Truncated n) _root_.SSet
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-coskeleton as a functor `SSet.Truncated n ⥤ SSet`.
-/
protected abbrev Truncated.cosk (n : ℕ) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.cosk n

/-- The n-skeleton as an endofunctor on `SSet`. -/
/-
**SSet.sk** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：sk (n : Nat) : SSet.{u} ⥤ SSet.{u}
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-skeleton as an endofunctor on `SSet`.
-/
abbrev sk (n : ℕ) : SSet.{u} ⥤ SSet.{u} := SimplicialObject.sk n

/-- The n-coskeleton as an endofunctor on `SSet`. -/
/-
**SSet.cosk** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：cosk (n : Nat) : SSet.{u} ⥤ SSet.{u}
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-coskeleton as an endofunctor on `SSet`.
-/
abbrev cosk (n : ℕ) : SSet.{u} ⥤ SSet.{u} := SimplicialObject.cosk n

end

section adjunctions

/-- The adjunction between the n-skeleton and n-truncation. -/
/-
**SSet.skAdj** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：skAdj (n : Nat) : Truncated.sk n ⊣ truncation.{u} n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the n-skeleton and n-truncation.
-/
noncomputable def skAdj (n : ℕ) : Truncated.sk n ⊣ truncation.{u} n :=
  SimplicialObject.skAdj n

/-- The adjunction between n-truncation and the n-coskeleton. -/
/-
**SSet.coskAdj** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：coskAdj (n : Nat) : truncation.{u} n ⊣ Truncated.cosk n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between n-truncation and the n-coskeleton.
-/
noncomputable def coskAdj (n : ℕ) : truncation.{u} n ⊣ Truncated.cosk n :=
  SimplicialObject.coskAdj n

namespace Truncated

/-
**SSet.Truncated.cosk_reflective** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Truncated`。
形式化陈述：cosk_reflective (n) : IsIso (coskAdj n).counit
参数：n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance cosk_reflective (n) : IsIso (coskAdj n).counit :=
  SimplicialObject.Truncated.cosk_reflective n
/-
**SSet.Truncated.sk_coreflective** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Truncated`。
形式化陈述：sk_coreflective (n) : IsIso (skAdj n).unit
参数：n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance sk_coreflective (n) : IsIso (skAdj n).unit :=
  SimplicialObject.Truncated.sk_coreflective n

/-- Since `Truncated.inclusion` is fully faithful, so is right Kan extension along it. -/
/-
**SSet.Truncated.cosk.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.co
sk`。
形式化陈述：(n : ℕ) → (SSet.Truncated.cosk n).FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since `Truncated.inclusion` is fully faithful, so is right Kan extension along i
t.
-/
noncomputable def cosk.fullyFaithful (n) :
    (Truncated.cosk n).FullyFaithful :=
  SimplicialObject.Truncated.cosk.fullyFaithful n
/-
**SSet.Truncated.cosk.full** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Truncated.cosk`。
形式化陈述：∀ (n : ℕ), (SSet.Truncated.cosk n).Full
参数：n : ℕ；SSet.Truncated.cosk n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.Truncated.cosk.full`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1 :     ∀ (F : CategoryThe
ory.Functor (SimplexCategory.Truncated n)…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance cosk.full (n) : (Truncated.cosk n).Full :=
  SimplicialObject.Truncated.cosk.full n
/-
**SSet.Truncated.cosk.faithful** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Truncated.cosk`。
形式化陈述：∀ (n : ℕ), (SSet.Truncated.cosk n).Faithful
参数：n : ℕ；SSet.Truncated.cosk n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.Truncated.cosk.faithful`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1 :     ∀ (F : Categor
yTheory.Functor (SimplexCategory.Truncated n)…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance cosk.faithful (n) : (Truncated.cosk n).Faithful :=
  SimplicialObject.Truncated.cosk.faithful n
/-
**SSet.Truncated.coskAdj.reflective** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.co
skAdj`。
形式化陈述：(n : ℕ) → CategoryTheory.Reflective (SSet.Truncated.cosk n)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance coskAdj.reflective (n) : Reflective (Truncated.cosk n) :=
  SimplicialObject.Truncated.coskAdj.reflective n

/-- Since `Truncated.inclusion` is fully faithful, so is left Kan extension along it. -/
/-
**SSet.Truncated.sk.fullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.sk`。
形式化陈述：(n : ℕ) → (SSet.Truncated.sk n).FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since `Truncated.inclusion` is fully faithful, so is left Kan extension along it
.
-/
noncomputable def sk.fullyFaithful (n) :
    (Truncated.sk n).FullyFaithful := SimplicialObject.Truncated.sk.fullyFaithful n
/-
**SSet.Truncated.sk.full** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Truncated.sk`。
形式化陈述：∀ (n : ℕ), (SSet.Truncated.sk n).Full
参数：n : ℕ；SSet.Truncated.sk n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.Truncated.sk.full`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1 :     ∀ (F : CategoryTheor
y.Functor (SimplexCategory.Truncated n)…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance sk.full (n) : (Truncated.sk n).Full := SimplicialObject.Truncated.sk.full n
/-
**SSet.Truncated.sk.faithful** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Truncated.sk`。
形式化陈述：∀ (n : ℕ), (SSet.Truncated.sk n).Faithful
参数：n : ℕ；SSet.Truncated.sk n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.Truncated.sk.faithful`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] (n : ℕ)   [inst_1 :     ∀ (F : CategoryT
heory.Functor (SimplexCategory.Truncated n)…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance sk.faithful (n) : (Truncated.sk n).Faithful :=
  SimplicialObject.Truncated.sk.faithful n
/-
**SSet.Truncated.skAdj.coreflective** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.sk
Adj`。
形式化陈述：(n : ℕ) → CategoryTheory.Coreflective (SSet.Truncated.sk n)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance skAdj.coreflective (n) : Coreflective (Truncated.sk n) :=
  SimplicialObject.Truncated.skAdj.coreflective n

end Truncated

end adjunctions

/-- The category of augmented simplicial sets, as a particular case of
augmented simplicial objects. -/
/-
**SSet.Augmented** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：Augmented
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of augmented simplicial sets, as a particular case of
augmented simplicial objects.
-/
abbrev Augmented :=
  SimplicialObject.Augmented (Type u)

section applications
variable {S : SSet}

/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_δ_apply {n} {i j : Fin (n + 2)} (H : i ≤ j) (x : S _⦋n + 2⦌) :
    S.δ i (S.δ j.succ x) = S.δ j (S.δ i.castSucc x) := congr_hom (S.δ_comp_δ H) x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_δ'_apply {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j)
    (x : S _⦋n + 2⦌) : S.δ i (S.δ j x) =
      S.δ (j.pred H.ne_zero) (S.δ i.castSucc x) :=
  congr_hom (S.δ_comp_δ' H) x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_δ''_apply {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j)
    (x : S _⦋n + 2⦌) :
    S.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) (S.δ j.succ x) =
      S.δ j (S.δ i x) := congr_hom (S.δ_comp_δ'' H) x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_δ_self_apply {n} {i : Fin (n + 2)} (x : S _⦋n + 2⦌) :
    S.δ i (S.δ i.castSucc x) = S.δ i (S.δ i.succ x) := congr_hom S.δ_comp_δ_self x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_δ_self'_apply {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i)
    (x : S _⦋n + 2⦌) : S.δ i (S.δ j x) = S.δ i (S.δ i.succ x) := congr_hom (S.δ_comp_δ_self' H) x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_σ_of_le_apply {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j)
    (x : S _⦋n + 1⦌) :
    S.δ (Fin.castSucc i) (S.σ j.succ x) = S.σ j (S.δ i x) := congr_hom (S.δ_comp_σ_of_le H) x

@[simp]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_σ_self_apply {n} (i : Fin (n + 1)) (x : S _⦋n⦌) : S.δ i.castSucc (S.σ i x) = x :=
  congr_hom S.δ_comp_σ_self x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_σ_self'_apply {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i)
    (x : S _⦋n⦌) : S.δ j (S.σ i x) = x := congr_hom (S.δ_comp_σ_self' H) x

@[simp]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_σ_succ_apply {n} (i : Fin (n + 1)) (x : S _⦋n⦌) : S.δ i.succ (S.σ i x) = x :=
  congr_hom S.δ_comp_σ_succ x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_σ_succ'_apply {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) (x : S _⦋n⦌) :
    S.δ j (S.σ i x) = x := congr_hom (S.δ_comp_σ_succ' H) x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_σ_of_gt_apply {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i)
    (x : S _⦋n + 1⦌) : S.δ i.succ (S.σ (Fin.castSucc j) x) = S.σ j (S.δ i x) :=
  congr_hom (S.δ_comp_σ_of_gt H) x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_σ_of_gt'_apply {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
    (x : S _⦋n + 1⦌) : S.δ i (S.σ j x) =
      S.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le)))
        (S.δ (i.pred H.ne_zero) x) :=
  congr_hom (S.δ_comp_σ_of_gt' H) x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_comp_σ_apply {n} {i j : Fin (n + 1)} (H : i ≤ j) (x : S _⦋n⦌) :
    S.σ i.castSucc (S.σ j x) = S.σ j.succ (S.σ i x) := congr_hom (S.σ_comp_σ H) x

variable {T : SSet} (f : S ⟶ T)

open Opposite
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_naturality_apply {n : ℕ} (i : Fin (n + 2)) (x : S _⦋n + 1⦌) :
    f.app (op ⦋n⦌) (S.δ i x) = T.δ i (f.app (op ⦋n + 1⦌) x) := by
  change (S.δ i ≫ f.app (op ⦋n⦌)) x = (f.app (op ⦋n + 1⦌) ≫ T.δ i) x
  exact congr_hom (SimplicialObject.δ_naturality f i) x
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_naturality_apply {n : ℕ} (i : Fin (n + 1)) (x : S _⦋n⦌) :
    f.app (op ⦋n + 1⦌) (S.σ i x) = T.σ i (f.app (op ⦋n⦌) x) := by
  change (S.σ i ≫ f.app (op ⦋n + 1⦌)) x = (f.app (op ⦋n⦌) ≫ T.σ i) x
  exact congr_hom (SimplicialObject.σ_naturality f i) x

end applications

end SSet

