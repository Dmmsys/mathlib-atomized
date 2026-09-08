/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Algebra.Order.Monoid.Basic

/-! # The range of a MonoidWithZeroHom

Given a `MonoidWithZeroHom` `f : A → B` whose codomain `B` is a `LinearOrderedCommGroupWithZero`,
we provide some order properties of the `MonoidWithZeroHom.ValueGroup₀` as defined in
`Mathlib.Algebra.GroupWithZero.Range`.

-/

@[expose] public section

namespace MonoidWithZeroHom

variable {A B : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero B] {f : A →*₀ B}

namespace ValueGroup₀

open WithZero

variable (f) in
/-- The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as a homomorphism of monoids with zero. -/
/-
**MonoidWithZeroHom.ValueGroup₀.orderMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间
 `MonoidWithZeroHom.ValueGroup₀`。
形式化陈述：orderMonoidWithZeroHom : ValueGroup₀ f ->*₀o WithZero Bˣ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of `ValueGroup₀ f` into `WithZero Bˣ` as a homomorphism of monoids
 with zero.
-/
def orderMonoidWithZeroHom : ValueGroup₀ f →*₀o WithZero Bˣ where
  __ := WithZero.map' (valueGroup f).subtype
  monotone' := map'_strictMono (Subtype.strictMono_coe _) |>.monotone
/-
**MonoidWithZeroHom.ValueGroup₀.monoidWithZeroHom_strictMono** 是 Mathlib 中的一个引理，
位于命名空间 `MonoidWithZeroHom.ValueGroup₀`。
形式化陈述：monoidWithZeroHom_strictMono : StrictMono (orderMonoidWithZeroHom f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.map'_strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOneClass β] 
{f : α →* β}, …
· 使用定理 `Subtype.strictMono_coe`：Subtype.strictMono_coe [Preorder α] (p : α -> Pr
op) : StrictMono ((↑) : Subtype p -> α)
-/
lemma monoidWithZeroHom_strictMono :
    StrictMono (orderMonoidWithZeroHom f) :=
  map'_strictMono (Subtype.strictMono_coe _)
/-
**MonoidWithZeroHom.ValueGroup₀.embedding_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `
MonoidWithZeroHom.ValueGroup₀`。
形式化陈述：embedding_strictMono : StrictMono (embedding (f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.withZeroUnits_apply`：∀ {α : Type u_1} [inst : LinearOrderedComm
GroupWithZero α] (n : WithZero αˣ),   OrderIso.withZeroUnits n = WithZero.recZer
oCoe 0 Units.val n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.monoidWithZeroHom_strictMono`：monoidWithZe
roHom_strictMono : StrictMono (orderMonoidWithZeroHom f)
-/
lemma embedding_strictMono : StrictMono (embedding (f := f)) := by
  intro x y hxy
  rw [← monoidWithZeroHom_strictMono.lt_iff_lt] at hxy
  simpa using! (OrderEmbedding.lt_iff_lt (OrderIso.withZeroUnits.toOrderEmbedding)).mpr hxy
/-
**MonoidWithZeroHom.ValueGroup₀.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom.Va
lueGroup₀`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedMonoid (ValueGroup₀ f) :=
  Function.Injective.isOrderedMonoid embedding (map_mul _) embedding_strictMono.le_iff_le
/-
**MonoidWithZeroHom.ValueGroup₀.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidWithZeroHom.Va
lueGroup₀`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrderedCommGroupWithZero (ValueGroup₀ f) where
  isBot_zero _ := by simp
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simp only [← (embedding_strictMono (f := f)).lt_iff_lt, map_mul] at *
    exact (mul_lt_mul_iff_of_pos_left ha).mpr hbc
/-
**MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos** 是 Mathlib 中的一个引理，位于命名空间 `Mo
noidWithZeroHom.ValueGroup₀`。
形式化陈述：embedding_unit_pos (a : (ValueGroup₀ f)ˣ) : 0 < embedding a.1
参数：a : (ValueGroup₀ f)ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma embedding_unit_pos (a : (ValueGroup₀ f)ˣ) :
    0 < embedding a.1 := by
  conv_lhs => rw [← map_zero f, ← ValueGroup₀.embedding_restrict₀ (0 : A)]
  rw [embedding_strictMono.lt_iff_lt]
  simp
/-
**MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero** 是 Mathlib 中的一个引理，位于命名空间
 `MonoidWithZeroHom.ValueGroup₀`。
形式化陈述：embedding_unit_ne_zero (a : (ValueGroup₀ f)ˣ) : embedding a.1 != 0
参数：a : (ValueGroup₀ f)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos`：embedding_unit_pos (a 
: (ValueGroup₀ f)ˣ) : 0 < embedding a.1
-/
lemma embedding_unit_ne_zero (a : (ValueGroup₀ f)ˣ) :
    embedding a.1 ≠ 0 := (embedding_unit_pos a).ne.symm

end ValueGroup₀

end MonoidWithZeroHom

