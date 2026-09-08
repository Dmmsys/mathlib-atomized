/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.ScottContinuity.Prod

/-!

# Scott continuity on complete lattices

## Main results

- `scottContinuous_iff_map_sSup`: A function is Scott continuous if and only if it commutes with
  `sSup` on directed sets.

-/

public section

variable {α β : Type*}

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β]

/-- `f` is Scott continuous if and only if it commutes with `sSup` on directed sets -/
/-
**scottContinuous_iff_map_sSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：scottContinuous_iff_map_sSup {f : α -> β} : ScottContinuous f ↔ forall ⦃d 
: Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d -> f (sSup d) = sSup (f '' d) wher
e mp h _ d₁ d₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isLUB_iff_sSup_eq`：isLUB_iff_sSup_eq : IsLUB s a ↔ sSup s = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`f` is Scott continuous if and only if it commutes with `sSup` on directed sets
-/
lemma scottContinuous_iff_map_sSup {f : α → β} :
    ScottContinuous f ↔
      ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → f (sSup d) = sSup (f '' d) where
  mp h _ d₁ d₂ := by rw [IsLUB.sSup_eq (h d₁ d₂ (isLUB_iff_sSup_eq.mpr rfl))]
  mpr h _ d₁ d₂ _ hda := by rw [isLUB_iff_sSup_eq, ← (h d₁ d₂), IsLUB.sSup_eq hda]

alias ⟨ScottContinuous.map_sSup, ScottContinuous.of_map_sSup⟩ :=
  scottContinuous_iff_map_sSup

end CompleteLattice

/-!
In a complete linear order, the Scott Topology coincides with the Upper topology, see
`Topology.IsScott.scott_eq_upper_of_completeLinearOrder`
-/

section CompleteLinearOrder

variable [CompleteLinearOrder β]

/-
**scottContinuous_inf_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：scottContinuous_inf_right (a : β) : ScottContinuous fun b => a ⊓ b
参数：a : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ScottContinuous.of_map_sSup`：∀ {α : Type u_1} {β : Type u_2} [inst : Com
pleteLattice α] [inst_1 : CompleteLattice β] {f : α → β},   (∀ ⦃d : Set α⦄, d.No
nempty → Directed…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_sSup_eq`：inf_sSup_eq [Frame α] {s : Set α} {a : α} : a ⊓ sSup s = ⨆ 
b in s, a ⊓ b
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
-/
lemma scottContinuous_inf_right (a : β) : ScottContinuous fun b ↦ a ⊓ b :=
  .of_map_sSup (fun d _ _ ↦ by rw [inf_sSup_eq, sSup_image])
/-
**scottContinuous_inf_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：scottContinuous_inf_left (b : β) : ScottContinuous fun a => a ⊓ b
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ScottContinuous.of_map_sSup`：∀ {α : Type u_1} {β : Type u_2} [inst : Com
pleteLattice α] [inst_1 : CompleteLattice β] {f : α → β},   (∀ ⦃d : Set α⦄, d.No
nempty → Directed…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_inf_eq`：∀ {α : Type u} [inst : Order.Frame α] {s : Set α} {b : α}, 
sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
-/
lemma scottContinuous_inf_left (b : β) : ScottContinuous fun a ↦ a ⊓ b :=
  .of_map_sSup (fun d _ _ ↦ by rw [sSup_inf_eq, sSup_image])

/- The meet operation is Scott continuous -/
/-
**ScottContinuous.inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The meet operation is Scott continuous
-/
lemma ScottContinuous.inf₂ : ScottContinuous fun (a, b) => (a ⊓ b : β) :=
  ScottContinuous.fromProd (fun a => scottContinuous_inf_right a) scottContinuous_inf_left

end CompleteLinearOrder

