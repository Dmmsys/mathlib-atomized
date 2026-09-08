/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Logic.UnivLE
public import Mathlib.SetTheory.Ordinal.Univ

/-!
# UnivLE and cardinals
-/

public section

noncomputable section

universe u v

open Cardinal

/-
**univLE_iff_cardinal_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：univLE_iff_cardinal_le : UnivLE.{u, v} ↔ univ.{u, v + 1} <= univ.{v, u + 1
}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_univ`：lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.univ_umax`：univ_umax : univ.{u, max (u + 1) v} = univ.{u, v}
· 使用定理 `Cardinal.lift_lt_univ'`：lift_lt_univ' (c : Cardinal) : lift.{max (u + 1)
 v, u} c < univ.{u, v}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_univ'`：lt_univ' {c} : c < univ.{u, v} ↔ exists c', c = lift.
{max (u + 1) v, u} c'
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem univLE_iff_cardinal_le : UnivLE.{u, v} ↔ univ.{u, v + 1} ≤ univ.{v, u + 1} := by
  simp_rw [univLE_iff, small_iff_lift_mk_lt_univ]
  contrapose!
  -- strange: simp_rw [univ_umax.{v,u}] doesn't work
  refine ⟨fun ⟨α, le⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [univ_umax.{v, u}, ← lift_le.{u + 1}, lift_univ, lift_lift] at le
    exact le.trans_lt (lift_lt_univ'.{u, v + 1} #α)
  · obtain ⟨⟨α⟩, h⟩ := lt_univ'.mp h; use α
    rw [univ_umax.{v, u}, ← lift_le.{u + 1}, lift_univ, lift_lift]
    exact h.le
/-
**univLE_iff_exists_embedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：univLE_iff_exists_embedding : UnivLE.{u, v} ↔ Nonempty (Ordinal.{u} ↪ Ordi
nal.{v})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `univLE_iff_cardinal_le`：univLE_iff_cardinal_le : UnivLE.{u, v} ↔ univ.{u
, v + 1} <= univ.{v, u + 1}
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
-/
theorem univLE_iff_exists_embedding : UnivLE.{u, v} ↔ Nonempty (Ordinal.{u} ↪ Ordinal.{v}) := by
  rw [univLE_iff_cardinal_le]
  exact lift_mk_le'
/-
**Ordinal.univLE_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ordinal.univLE_of_injective {f : Ordinal.{u} -> Ordinal.{v}} (h : f.Inject
ive) : UnivLE.{u, v}
参数：h : f.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `univLE_iff_exists_embedding`：univLE_iff_exists_embedding : UnivLE.{u, v}
 ↔ Nonempty (Ordinal.{u} ↪ Ordinal.{v})
-/
theorem Ordinal.univLE_of_injective {f : Ordinal.{u} → Ordinal.{v}} (h : f.Injective) :
    UnivLE.{u, v} :=
  univLE_iff_exists_embedding.2 ⟨f, h⟩

/-- Together with transitivity, this shows `UnivLE` is a total preorder. -/
/-
**univLE_total** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：univLE_total : UnivLE.{u, v} ∨ UnivLE.{v, u}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a

--- 原说明 ---
Together with transitivity, this shows `UnivLE` is a total preorder.
-/
theorem univLE_total : UnivLE.{u, v} ∨ UnivLE.{v, u} := by
  simp_rw [univLE_iff_cardinal_le]; apply le_total
