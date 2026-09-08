/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot, Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Algebra

/-!
# Prime fields

A prime field is a field that does not contain any nontrivial subfield. Prime fields are `ℚ` in
characteristic `0` and `ZMod p` in characteristic `p` with `p` a prime number. Any field `K`
contains a unique prime field: it is the smallest field contained in `K`.

## Results

* The fields `ℚ` and `ZMod p` are prime fields. These are stated as the instances that says that
  the corresponding `Subfield` type is a `Subsingleton`.
* `Subfield.bot_eq_of_charZero` : the smallest subfield of a field of characteristic `0` is (the
  image of) `ℚ`.
* `Subfield.bot_eq_of_zMod_algebra`: the smallest subfield of a field of characteristic `p` is (the
  image of) `ZMod p`.

-/

public section

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (Subfield ℚ) := subsingleton_of_top_le_bot fun x _ ↦
  have h := Subsingleton.elim ((⊥ : Subfield ℚ).subtype.comp (Rat.castHom _)) (.id _ : ℚ →+* ℚ)
  (congr($h x) : _ = x) ▸ Subtype.prop _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : ℕ) [hp : Fact (Nat.Prime p)] : Subsingleton (Subfield (ZMod p)) :=
  subsingleton_of_top_le_bot fun x _ ↦
    have h := Subsingleton.elim ((⊥ : Subfield (ZMod p)).subtype.comp
      (ZMod.castHom dvd_rfl _)) (.id _ : ZMod p →+* ZMod p)
    (congr($h x) : _ = x) ▸ Subtype.prop _

/--
The smallest subfield of a field of characteristic `0` is (the image of) `ℚ`.
-/
/-
**Subfield.bot_eq_of_charZero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.bot_eq_of_charZero {K : Type*} [Field K] [CharZero K] : (⊥ : Subf
ield K) = (algebraMap Rat K).fieldRange
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.map_bot`：map_bot (f : K ->+* L) : (⊥ : Subfield K).map f = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `subsingleton_iff_bot_eq_top`：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ 
: α) ↔ Subsingleton α
· 使用定理 `instSubsingletonSubfieldRat`：Subsingleton (Subfield ℚ)
· 使用定理 `RingHom.fieldRange_eq_map`：fieldRange_eq_map : f.fieldRange = Subfield.m
ap f ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The smallest subfield of a field of characteristic `0` is (the image of) `ℚ`.
-/
theorem Subfield.bot_eq_of_charZero {K : Type*} [Field K] [CharZero K] :
    (⊥ : Subfield K) = (algebraMap ℚ K).fieldRange := by
  rw [eq_comm, eq_bot_iff, ← Subfield.map_bot (algebraMap ℚ K),
    subsingleton_iff_bot_eq_top.mpr inferInstance, ← RingHom.fieldRange_eq_map]

/--
The smallest subfield of a field of characteristic `p` is (the image of) `ZMod p`.
Note that the fact that the field `K` is of characteristic `p` is stated by the fact that it is
`ZMod p`-algebra.
-/
/-
**Subfield.bot_eq_of_zMod_algebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.bot_eq_of_zMod_algebra {K : Type*} (p : Nat) [hp : Fact (Nat.Prim
e p)] [Field K] [Algebra (ZMod p) K] : (⊥ : Subfield K) = (algebraMap (ZMod p) K
).fieldRange
参数：p : Nat；Nat.Prime p；ZMod p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.map_bot`：map_bot (f : K ->+* L) : (⊥ : Subfield K).map f = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `subsingleton_iff_bot_eq_top`：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ 
: α) ↔ Subsingleton α
· 使用定理 `instSubsingletonSubfieldZMod`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Subsi
ngleton (Subfield (ZMod p))
· 使用定理 `RingHom.fieldRange_eq_map`：fieldRange_eq_map : f.fieldRange = Subfield.m
ap f ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The smallest subfield of a field of characteristic `p` is (the image of) `ZMod p
`.
Note that the fact that the field `K` is of characteristic `p` is stated by the 
fact that it is
`ZMod p`-algebra.
-/
theorem Subfield.bot_eq_of_zMod_algebra {K : Type*} (p : ℕ) [hp : Fact (Nat.Prime p)]
    [Field K] [Algebra (ZMod p) K] :
    (⊥ : Subfield K) = (algebraMap (ZMod p) K).fieldRange := by
  rw [eq_comm, eq_bot_iff, ← Subfield.map_bot (algebraMap (ZMod p) K),
    subsingleton_iff_bot_eq_top.mpr inferInstance, ← RingHom.fieldRange_eq_map]
