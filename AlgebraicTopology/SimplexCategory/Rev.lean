/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# The covariant involution of the simplex category

In this file, we introduce the functor `rev : SimplexCategory ⥤ SimplexCategory`
which, via the equivalence between the simplex category and the
category of nonempty finite linearly ordered types, corresponds to
the *covariant* functor which sends a type `α` to `αᵒᵈ`.

-/

@[expose] public section

open CategoryTheory

namespace SimplexCategory

set_option backward.isDefEq.respectTransparency.types false in
/-- The covariant involution `rev : SimplexCategory ⥤ SimplexCategory` which,
via the equivalence between the simplex category and the
category of nonempty finite linearly ordered types, corresponds to
the *covariant* functor which sends a type `α` to `αᵒᵈ`.
This functor sends the object `⦋n⦌` to `⦋n⦌` and a map `f : ⦋n⦌ ⟶ ⦋m⦌`
is sent to the monotone map `(i : Fin (n + 1)) ↦ (f i.rev).rev`. -/
@[simps obj, simps -isSimp map, implicit_reducible]
/-
**SimplexCategory.rev** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：rev : SimplexCategory ⥤ SimplexCategory where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The covariant involution `rev : SimplexCategory ⥤ SimplexCategory` which,
via the equivalence between the simplex category and the
category of nonempty finite linearly ordered types, corresponds to
the *covariant* functor which sends a type `α` to `αᵒᵈ`.
This functor sends the object `⦋n⦌` to `⦋n⦌` and a map `f : ⦋n⦌ ⟶ ⦋m⦌`
is sent to the monotone map `(i : Fin (n + 1)) ↦ (f i.rev).rev`.
-/
def rev : SimplexCategory ⥤ SimplexCategory where
  obj n := n
  map {n m} f := Hom.mk ⟨fun i ↦ (f i.rev).rev, fun i j hij ↦ by
    rw [Fin.rev_le_rev]
    exact f.toOrderHom.monotone (by rwa [Fin.rev_le_rev])⟩

@[simp]
/-
**SimplexCategory.rev_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：rev_map_apply {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) : 
(rev.map f).toOrderHom (a
参数：f : n ⟶ m；i : Fin (n.len + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rev_map_apply {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (rev.map f).toOrderHom (a := n) (b := m) i = (f.toOrderHom i.rev).rev :=
  rfl

@[simp]
/-
**SimplexCategory.rev_map_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rev_map_δ {n : ℕ} (i : Fin (n + 2)) :
    rev.map (δ i) = δ i.rev := by
  ext j : 3
  simp [δ, Fin.succAbove_rev_right, Fin.rev_rev, rev_map_apply]

@[simp]
/-
**SimplexCategory.rev_map_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rev_map_σ {n : ℕ} (i : Fin (n + 1)) :
    rev.map (σ i) = σ i.rev := by
  ext j : 3
  simp [σ, Fin.predAbove_rev_right, Fin.rev_rev, rev_map_apply]

/-- The functor `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`
is a covariant involution. -/
@[simps! hom_app inv_app]
/-
**SimplexCategory.revCompRevIso** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：revCompRevIso : rev ⋙ rev ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`
is a covariant involution.
-/
def revCompRevIso : rev ⋙ rev ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

@[simp]
/-
**SimplexCategory.rev_map_rev_map** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
形式化陈述：rev_map_rev_map {n m : SimplexCategory} (f : n ⟶ m) : rev.map (rev.map f) 
= f
参数：f : n ⟶ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rev_map_rev_map {n m : SimplexCategory} (f : n ⟶ m) :
    rev.map (rev.map f) = f := by
  aesop

/-- The functor `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`
as an equivalence of category. -/
@[simps]
/-
**SimplexCategory.revEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：revEquivalence : SimplexCategory ≌ SimplexCategory where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`
as an equivalence of category.
-/
def revEquivalence : SimplexCategory ≌ SimplexCategory where
  functor := rev
  inverse := rev
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso
/-
**SimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : rev.IsEquivalence := revEquivalence.isEquivalence_functor

end SimplexCategory

