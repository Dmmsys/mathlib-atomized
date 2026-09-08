/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!

# The nerve of a category

This file provides the definition of the nerve of a category `C`,
which is a simplicial set `nerve C` (see [goerss-jardine-2009], Example I.1.4).
By definition, the type of `n`-simplices of `nerve C` is `ComposableArrows C n`,
which is the category `Fin (n + 1) ⥤ C`.

## References
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]

-/

@[expose] public section

open CategoryTheory Category Simplicial Opposite

universe v u

namespace CategoryTheory

/-- The nerve of a category -/
@[simps -isSimp]
/-
**CategoryTheory.nerve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：nerve (C : Type u) [Category.{v} C] : SSet.{max u v} where obj Δ
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nerve of a category
-/
def nerve (C : Type u) [Category.{v} C] : SSet.{max u v} where
  obj Δ := ComposableArrows C (Δ.unop.len)
  map f := ↾fun x ↦ x.whiskerLeft (SimplexCategory.toCat.map f.unop).toFunctor
  -- `aesop` can prove these but is slow, help it out:
  map_id _ := rfl
  map_comp _ _ := rfl

attribute [simp] nerve_obj
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type*} [Category* C] {Δ : SimplexCategoryᵒᵖ} : Category ((nerve C).obj Δ) :=
  inferInstanceAs <| Category (ComposableArrows C (Δ.unop.len))

section

variable {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)

/-- Given a functor `C ⥤ D`, we obtain a morphism `nerve C ⟶ nerve D` of simplicial sets. -/
@[simps -isSimp]
/-
**CategoryTheory.nerveMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：nerveMap {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) : ne
rve C ⟶ nerve D
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `C ⥤ D`, we obtain a morphism `nerve C ⟶ nerve D` of simplicial 
sets.
-/
def nerveMap {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) : nerve C ⟶ nerve D :=
  { app _ := ↾fun X ↦ (F.mapComposableArrows _).obj X }
/-
**CategoryTheory.nerveMap_app_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nerveMap_app_mk₀ (x : C) :
    (nerveMap F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      ComposableArrows.mk₀ (F.obj x) :=
  ComposableArrows.ext₀ rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerveMap_app_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nerveMap_app_mk₁ {x y : C} (f : x ⟶ y) :
    (nerveMap F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) :=
  ComposableArrows.ext₁ rfl rfl (by simp [nerveMap_app])

end

/-- The nerve of a category, as a functor `Cat ⥤ SSet` -/
@[simps]
/-
**CategoryTheory.nerveFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：nerveFunctor : Cat.{v, u} ⥤ SSet where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nerve of a category, as a functor `Cat ⥤ SSet`
-/
def nerveFunctor : Cat.{v, u} ⥤ SSet where
  obj C := nerve C
  map F := nerveMap F.toFunctor

/-- The 0-simplices of the nerve of a category are equivalent to the objects of the category. -/
/-
**CategoryTheory.nerveEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：nerveEquiv {C : Type u} [Category.{v} C] : ComposableArrows C 0 ≃ C where 
toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 0-simplices of the nerve of a category are equivalent to the objects of the 
category.
-/
def nerveEquiv {C : Type u} [Category.{v} C] : ComposableArrows C 0 ≃ C where
  toFun f := f.obj ⟨0, by lia⟩
  invFun f := ComposableArrows.mk₀ f
  left_inv f := ComposableArrows.ext₀ rfl

namespace nerve

set_option backward.isDefEq.respectTransparency.types false in
/-- Nerves of finite non-empty ordinals are representable functors. -/
/-
**CategoryTheory.nerve.representableBy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.nerve`。
形式化陈述：representableBy {n : Nat} (α : Type u) [Preorder α] (e : α ≃o Fin (n + 1))
 : (nerve α).RepresentableBy ⦋n⦌ where homEquiv
参数：α : Type u；e : α ≃o Fin (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Nerves of finite non-empty ordinals are representable functors.
-/
def representableBy {n : ℕ} (α : Type u) [Preorder α] (e : α ≃o Fin (n + 1)) :
    (nerve α).RepresentableBy ⦋n⦌ where
  homEquiv := SimplexCategory.homEquivFunctor.trans
    { toFun F := F ⋙ e.symm.monotone.functor
      invFun F := F ⋙ e.monotone.functor
      left_inv F := Functor.ext (fun x ↦ by simp)
      right_inv F := Functor.ext (fun x ↦ by simp) }
  homEquiv_comp _ _ := rfl

variable {C : Type u} [Category.{v} C] {n : ℕ}
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_obj {n : ℕ} (i : Fin (n + 2)) (x : ComposableArrows C (n + 1)) (j : Fin (n + 1)) :
    ((nerve C).δ i x).obj j = x.obj (i.succAbove j) :=
  rfl
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_obj {n : ℕ} (i : Fin (n + 1)) (x : ComposableArrows C n) (j : Fin (n + 2)) :
    ((nerve C).σ i x).obj j = x.obj (i.predAbove j) :=
  rfl
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₀_eq {x : ComposableArrows C (n + 1)} : (nerve C).δ (0 : Fin (n + 2)) x = x.δ₀ := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ₀_mk₀_eq (x : C) : (nerve C).σ (0 : Fin 1) (.mk₀ x) = .mk₁ (𝟙 x) :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

section

variable {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ₂_mk₂_eq : (nerve C).δ 2 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ f :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ₀_mk₂_eq : (nerve C).δ 0 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ g :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ₁_mk₂_eq : (nerve C).δ 1 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ (f ≫ g) :=
  ComposableArrows.ext₁ rfl rfl (by simp; rfl)

end

@[ext]
/-
**CategoryTheory.nerve.ext_of_isThin** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.n
erve`。
形式化陈述：ext_of_isThin [Quiver.IsThin C] {n : SimplexCategoryᵒᵖ} {x y : (nerve C).o
bj n} (h : x.obj = y.obj) : x = y
参数：nerve C；h : x.obj = y.obj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.ext`：ext {F G : ComposableArrows C n} (h
 : forall i, F.obj i = G.obj i) (w : forall (i : Nat) (hi : i < n), F.map' i (i 
+ 1) = eqToHom (h _) ≫ G.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext_of_isThin [Quiver.IsThin C] {n : SimplexCategoryᵒᵖ} {x y : (nerve C).obj n}
    (h : x.obj = y.obj) :
    x = y :=
  ComposableArrows.ext (by simp [h]) (by subsingleton)

open SSet

@[simp]
/-
**CategoryTheory.nerve.left_edge** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve
`。
形式化陈述：left_edge {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) : Composab
leArrows.left (n
参数：e : (nerve C).Edge x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Edge.src_eq`：src_eq (e : Edge x₀ x₁) : X.δ 1 e.edge = x₀
-/
lemma left_edge {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) :
    ComposableArrows.left (n := 1) e.edge = nerveEquiv x := by
  simp only [← e.src_eq]
  rfl

@[simp]
/-
**CategoryTheory.nerve.right_edge** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerv
e`。
形式化陈述：right_edge {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) : Composa
bleArrows.right (n
参数：e : (nerve C).Edge x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Edge.tgt_eq`：tgt_eq (e : Edge x₀ x₁) : X.δ 0 e.edge = x₁
-/
lemma right_edge {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) :
    ComposableArrows.right (n := 1) e.edge = nerveEquiv y := by
  simp only [← e.tgt_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_two (x : ComposableArrows C 2) :
    (nerve C).δ 2 x = .mk₁ (x.map' 0 1) :=
  ComposableArrows.ext₁ rfl rfl (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_zero (x : ComposableArrows C 2) :
    (nerve C).δ 0 x = .mk₁ (x.map' 1 2) :=
  ComposableArrows.ext₁ rfl rfl (by cat_disch)

section

attribute [local ext (iff := false)] ComposableArrows.ext₀ ComposableArrows.ext₁

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Bijection between edges in the nerve of category and morphisms in the category. -/
@[simps -isSimp]
/-
**CategoryTheory.nerve.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.nerve`
。
形式化陈述：homEquiv {x y : ComposableArrows C 0} : (nerve C).Edge x y ≃ (nerveEquiv x
 ⟶ nerveEquiv y) where toFun e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bijection between edges in the nerve of category and morphisms in the category.
-/
def homEquiv {x y : ComposableArrows C 0} :
    (nerve C).Edge x y ≃ (nerveEquiv x ⟶ nerveEquiv y) where
  toFun e := eqToHom (by simp) ≫ e.edge.hom ≫ eqToHom (by simp)
  invFun f := .mk (ComposableArrows.mk₁ f) (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
  left_inv e := by cat_disch
  right_inv f := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.nerve.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₁_homEquiv_apply {x y : ComposableArrows C 0} (e : (nerve C).Edge x y) :
    ComposableArrows.mk₁ (homEquiv e) = ComposableArrows.mk₁ e.edge.hom := by
  simp [homEquiv, ComposableArrows.mk₁_eqToHom_comp, ComposableArrows.mk₁_comp_eqToHom]

set_option backward.defeqAttrib.useBackward true in
/-- Constructor for edges in the nerve of a category. (See also `homEquiv`.) -/
/-
**CategoryTheory.nerve.edgeMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.nerve`。
形式化陈述：edgeMk {x y : C} (f : x ⟶ y) : (nerve C).Edge (nerveEquiv.symm x) (nerveEq
uiv.symm y)
参数：f : x ⟶ y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Constructor for edges in the nerve of a category. (See also `homEquiv`.)
-/
def edgeMk {x y : C} (f : x ⟶ y) : (nerve C).Edge (nerveEquiv.symm x) (nerveEquiv.symm y) :=
  Edge.mk (ComposableArrows.mk₁ f)

@[simp]
/-
**CategoryTheory.nerve.edgeMk_edge** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ner
ve`。
形式化陈述：edgeMk_edge {x y : C} (f : x ⟶ y) : (edgeMk f).edge = ComposableArrows.mk₁
 f
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma edgeMk_edge {x y : C} (f : x ⟶ y) : (edgeMk f).edge = ComposableArrows.mk₁ f := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.nerve.edgeMk_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve
`。
形式化陈述：edgeMk_id (x : C) : edgeMk (𝟙 x) = .id _
参数：x : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Edge.ext`：ext {e e' : Edge x₀ x₁} (h : e.edge = e'.edge) : e = e'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.ComposableArrows.ext₁`：ext₁ {F G : ComposableArrows C 1} 
(left : F.left = G.left) (right : F.right = G.right) (w : F.hom = eqToHom left ≫
 G.hom ≫ eqToHom right.sym…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma edgeMk_id (x : C) : edgeMk (𝟙 x) = .id _ := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerve.edgeMk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.nerve`。
形式化陈述：edgeMk_surjective {x y : C} : Function.Surjective (edgeMk : (x ⟶ y) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `SSet.Edge.ext`：ext {e e' : Edge x₀ x₁} (h : e.edge = e'.edge) : e = e'
· 使用引理 `CategoryTheory.ComposableArrows.ext₁`：ext₁ {F G : ComposableArrows C 1} 
(left : F.left = G.left) (right : F.right = G.right) (w : F.hom = eqToHom left ≫
 G.hom ≫ eqToHom right.sym…
· 使用引理 `CategoryTheory.nerve.right_edge`：right_edge {x y : ComposableArrows C 0}
 (e : (nerve C).Edge x y) : ComposableArrows.right (n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma edgeMk_surjective {x y : C} :
    Function.Surjective (edgeMk : (x ⟶ y) → _) :=
  fun e ↦ ⟨eqToHom (by simp) ≫ homEquiv e ≫ eqToHom (by simp), by cat_disch⟩

@[simp]
/-
**CategoryTheory.nerve.homEquiv_edgeMk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.nerve`。
形式化陈述：homEquiv_edgeMk {x y : C} (f : x ⟶ y) : homEquiv (edgeMk f) = f
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma homEquiv_edgeMk {x y : C} (f : x ⟶ y) :
    homEquiv (edgeMk f) = f :=
  homEquiv.symm.injective (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerve.homEquiv_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ner
ve`。
形式化陈述：homEquiv_id (x : ComposableArrows C 0) : homEquiv (Edge.id x) = 𝟙 _
参数：x : ComposableArrows C 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma homEquiv_id (x : ComposableArrows C 0) :
    homEquiv (Edge.id x) = 𝟙 _ := by
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x
  dsimp [homEquiv]
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerve.nonempty_compStruct_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.nerve`。
形式化陈述：nonempty_compStruct_iff {x₀ x₁ x₂ : C} (f₀₁ : x₀ ⟶ x₁) (f₁₂ : x₁ ⟶ x₂) (f₀
₂ : x₀ ⟶ x₂) : Nonempty (Edge.CompStruct (edgeMk f₀₁) (edgeMk f₁₂) (edgeMk f₀₂))
 ↔ f₀₁ ≫ f₁₂ = f₀₂
参数：f₀₁ : x₀ ⟶ x₁；f₁₂ : x₁ ⟶ x₂；f₀₂ : x₀ ⟶ x₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.ComposableArrows.ext₁`：ext₁ {F G : ComposableArrows C 1} 
(left : F.left = G.left) (right : F.right = G.right) (w : F.hom = eqToHom left ≫
 G.hom ≫ eqToHom right.sym…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Arrow.mk_inj`：mk_inj (A B : T) {f g : A ⟶ B} : Arrow.mk f
 = Arrow.mk g ↔ f = g
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `SSet.Edge.CompStruct.d₁`：d₁ : X.δ 1 h.simplex = e₀₂.edge
· 使用引理 `SSet.Edge.CompStruct.d₀`：d₀ : X.δ 0 h.simplex = e₁₂.edge
· 使用引理 `SSet.Edge.CompStruct.d₂`：d₂ : X.δ 2 h.simplex = e₀₁.edge
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.ComposableArrows.ext₂_of_arrow`：ext₂_of_arrow {f g : Comp
osableArrows C 2} (h₀₁ : Arrow.mk (f.map' 0 1) = Arrow.mk (g.map' 0 1)) (h₁₂ : A
rrow.mk (f.map' 1 2) = Arrow.mk (g.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.nerve.δ₂_two`：δ₂_two (x : ComposableArrows C 2) : (nerve 
C).δ 2 x = .mk₁ (x.map' 0 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.nerve.δ₂_zero`：δ₂_zero (x : ComposableArrows C 2) : (nerv
e C).δ 0 x = .mk₁ (x.map' 1 2)
-/
lemma nonempty_compStruct_iff {x₀ x₁ x₂ : C}
    (f₀₁ : x₀ ⟶ x₁) (f₁₂ : x₁ ⟶ x₂) (f₀₂ : x₀ ⟶ x₂) :
    Nonempty (Edge.CompStruct (edgeMk f₀₁) (edgeMk f₁₂) (edgeMk f₀₂)) ↔
      f₀₁ ≫ f₁₂ = f₀₂ := by
  let h' : Edge.CompStruct (edgeMk f₀₁) (edgeMk f₁₂) (edgeMk (f₀₁ ≫ f₁₂)) :=
      Edge.CompStruct.mk (ComposableArrows.mk₂ f₀₁ f₁₂)
        (by cat_disch) (by cat_disch) (by cat_disch)
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h ↦ ⟨by rwa [← h]⟩⟩
  rw [← Arrow.mk_inj]
  apply ComposableArrows.arrowEquiv.symm.injective
  convert_to! (nerve C).δ 1 h'.simplex = (nerve C).δ 1 h.simplex
  · exact (h'.d₁).symm
  · exact (h.d₁).symm
  · have h₀ := h.d₀
    have h₂ := h.d₂
    have h'₀ := h'.d₀
    have h'₂ := h'.d₂
    simp only [δ₂_zero, δ₂_two, edgeMk_edge] at h₀ h₂ h'₀ h'₂
    exact congr_arg _ (ComposableArrows.ext₂_of_arrow
      (ComposableArrows.arrowEquiv.symm.injective
        (by simp [-Edge.CompStruct.d₂, h'₂, ← h₂]))
      (ComposableArrows.arrowEquiv.symm.injective
        (by simp [-Edge.CompStruct.d₀, h'₀, ← h₀])))
/-
**CategoryTheory.nerve.homEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.n
erve`。
形式化陈述：homEquiv_comp {x₀ x₁ x₂ : ComposableArrows C 0} {e₀₁ : (nerve C).Edge x₀ x
₁} {e₁₂ : (nerve C).Edge x₁ x₂} {e₀₂ : (nerve C).Edge x₀ x₂} (h : Edge.CompStruc
t e₀₁ e₁₂ e₀₂) : homEquiv e₀₁ ≫ homEquiv e₁₂ = homEquiv e₀₂
参数：nerve C；nerve C；nerve C；h : Edge.CompStruct e₀₁ e₁₂ e₀₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用引理 `CategoryTheory.nerve.edgeMk_surjective`：edgeMk_surjective {x y : C} : Fu
nction.Surjective (edgeMk : (x ⟶ y) -> _)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `CategoryTheory.nerve.homEquiv_edgeMk`：homEquiv_edgeMk {x y : C} (f : x ⟶
 y) : homEquiv (edgeMk f) = f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.nerve.nonempty_compStruct_iff`：nonempty_compStruct_iff {x
₀ x₁ x₂ : C} (f₀₁ : x₀ ⟶ x₁) (f₁₂ : x₁ ⟶ x₂) (f₀₂ : x₀ ⟶ x₂) : Nonempty (Edge.Co
mpStruct (edgeMk f₀₁) (edgeMk f₁₂)…
-/
lemma homEquiv_comp {x₀ x₁ x₂ : ComposableArrows C 0}
    {e₀₁ : (nerve C).Edge x₀ x₁}
    {e₁₂ : (nerve C).Edge x₁ x₂} {e₀₂ : (nerve C).Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homEquiv e₀₁ ≫ homEquiv e₁₂ = homEquiv e₀₂ := by
  obtain ⟨x₀, rfl⟩ := nerveEquiv.symm.surjective x₀
  obtain ⟨x₁, rfl⟩ := nerveEquiv.symm.surjective x₁
  obtain ⟨x₂, rfl⟩ := nerveEquiv.symm.surjective x₂
  obtain ⟨f₀₁, rfl⟩ := edgeMk_surjective e₀₁
  obtain ⟨f₁₂, rfl⟩ := edgeMk_surjective e₁₂
  obtain ⟨f₀₂, rfl⟩ := edgeMk_surjective e₀₂
  convert! (nerve.nonempty_compStruct_iff _ _ _).1 ⟨h⟩ <;> apply homEquiv_edgeMk

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.nerve.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.nerve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_zero_nerveEquiv_symm (x : C) :
    (nerve C).σ 0 (nerveEquiv.symm x) = ComposableArrows.mk₁ (𝟙 x) := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.nerve.homEquiv_edgeMk_map_nerveMap** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.nerve`。
形式化陈述：homEquiv_edgeMk_map_nerveMap {D : Type u} [Category.{v} D] {x y : C} (f : 
x ⟶ y) (F : C ⥤ D) : dsimp% homEquiv ((edgeMk f).map (nerveMap F)) = F.map f
参数：f : x ⟶ y；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_edgeMk_map_nerveMap {D : Type u} [Category.{v} D] {x y : C}
    (f : x ⟶ y) (F : C ⥤ D) :
    dsimp% homEquiv ((edgeMk f).map (nerveMap F)) = F.map f := by
  simp [homEquiv, nerveMap_app]

end

end nerve

end CategoryTheory

/-- The functor `PartOrd ⥤ SSet` which sends a partially ordered type to its nerve. -/
@[simps]
/-
**PartOrd.nerveFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PartOrd.nerveFunctor : PartOrd.{u} ⥤ SSet.{u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `PartOrd ⥤ SSet` which sends a partially ordered type to its nerve.
-/
def PartOrd.nerveFunctor : PartOrd.{u} ⥤ SSet.{u} where
  obj X := nerve X
  map f := nerveMap f.hom.monotone.functor
