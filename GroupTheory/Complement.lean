/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Complements

In this file we define the complement of a subgroup.

## Main definitions

- `Subgroup.IsComplement S T` where `S` and `T` are subsets of `G` states that every `g : G` can be
  written uniquely as a product `s * t` for `s ∈ S`, `t ∈ T`.
- `H.LeftTransversal` where `H` is a subgroup of `G` is the type of all left-complements of `H`,
  i.e. the set of all `S : Set G` that contain exactly one element of each left coset of `H`.
- `H.RightTransversal` where `H` is a subgroup of `G` is the set of all right-complements of `H`,
  i.e. the set of all `T : Set G` that contain exactly one element of each right coset of `H`.

## Main results

- `isComplement'_of_coprime` : Subgroups of coprime order are complements.
-/

@[expose] public section

open Function Set
open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G] (H K : Subgroup G) (S T : Set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
This notion generalizes left transversals, right transversals, and complementary subgroups.

If `S` and `T` are `SetLike`s such as `Subgroup`s, see `isComplement_iff_bijective` for a
more ergonomic way to unfold.
-/
@[to_additive /-- `S` and `T` are complements if `(+) : S × T → G` is a bijection

If `S` and `T` are `SetLike`s such as `AddSubgroup`s, see `isComplement_iff_bijective` for a
more ergonomic way to unfold. -/]
/-
**Subgroup.IsComplement** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：IsComplement : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsComplement : Prop :=
  Function.Bijective fun x : S × T => x.1.1 * x.2.1

/-- `H` and `K` are complements if `(*) : H × K → G` is a bijection -/
@[to_additive /-- `H` and `K` are complements if `(+) : H × K → G` is a bijection -/]
/-
**Subgroup.IsComplement'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Subgroup`。
形式化陈述：IsComplement'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H` and `K` are complements if `(*) : H × K → G` is a bijection
-/
abbrev IsComplement' :=
  IsComplement (H : Set G) (K : Set G)

variable {H K S T}

/-- The correct way to unfold `IsComplement` for `SetLike`s such as `Subgroup`s -/
@[to_additive /-- The correct way to unfold `IsComplement` for `SetLike`s such as `AddSubgroup`s -/]
/-
**Subgroup.isComplement_iff_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_iff_bijective {S : Type*} [SetLike S G] (s t : S) : IsComplem
ent (G
参数：s t : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The correct way to unfold `IsComplement` for `SetLike`s such as `Subgroup`s
-/
theorem isComplement_iff_bijective {S : Type*} [SetLike S G] (s t : S) :
    IsComplement (G := G) s t ↔ Function.Bijective fun x : s × t => (x.1 : G) * (x.2 : G) :=
  Iff.rfl

@[to_additive]
/-
**Subgroup.isComplement'_def** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsComplement' K ↔ 
Subgroup.IsComplement ↑H ↑K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isComplement'_def : IsComplement' H K ↔ IsComplement (H : Set G) (K : Set G) :=
  Iff.rfl

@[to_additive]
/-
**Subgroup.isComplement_iff_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_iff_existsUnique : IsComplement S T ↔ forall g : G, exists! x
 : S × T, x.1.1 * x.2.1 = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
-/
theorem isComplement_iff_existsUnique :
    IsComplement S T ↔ ∀ g : G, ∃! x : S × T, x.1.1 * x.2.1 = g :=
  Function.bijective_iff_existsUnique _

@[to_additive]
/-
**Subgroup.IsComplement.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCompl
ement`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {S T : Set G}, Subgroup.IsComplement S T
 → ∀ (g : G), ∃! x, ↑x.1 * ↑x.2 = g
参数：g : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.isComplement_iff_existsUnique`：isComplement_iff_existsUnique : 
IsComplement S T ↔ forall g : G, exists! x : S × T, x.1.1 * x.2.1 = g
-/
theorem IsComplement.existsUnique (h : IsComplement S T) (g : G) :
    ∃! x : S × T, x.1.1 * x.2.1 = g :=
  isComplement_iff_existsUnique.mp h g

@[to_additive]
/-
**Subgroup.IsComplement'.symm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComplement'`
。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsComplement' K → 
K.IsComplement' H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.isComplement'_def`：∀ {G : Type u_1} [inst : Group G] {H K : Sub
group G}, H.IsComplement' K ↔ Subgroup.IsComplement ↑H ↑K
· 使用定理 `Subgroup.isComplement_iff_bijective`：isComplement_iff_bijective {S : Typ
e*} [SetLike S G] (s t : S) : IsComplement (G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.bijective_comp`：bijective_comp (e : α ≃ β) (f : β -> γ) : Bijectiv
e (f ∘ e) ↔ Bijective f
· 使用定理 `Equiv.comp_bijective`：comp_bijective (f : α -> β) (e : β ≃ γ) : Bijectiv
e (e ∘ f) ↔ Bijective f
-/
theorem IsComplement'.symm (h : IsComplement' H K) : IsComplement' K H := by
  let ϕ : H × K ≃ K × H :=
    Equiv.mk (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => ⟨x.2⁻¹, x.1⁻¹⟩)
      (fun x => Prod.ext (inv_inv _) (inv_inv _)) fun x => Prod.ext (inv_inv _) (inv_inv _)
  let ψ : G ≃ G := Equiv.mk (fun g : G => g⁻¹) (fun g : G => g⁻¹) inv_inv inv_inv
  suffices hf : (ψ ∘ fun x : H × K => x.1.1 * x.2.1) = (fun x : K × H => x.1.1 * x.2.1) ∘ ϕ by
    rwa [isComplement'_def, isComplement_iff_bijective, ← Equiv.bijective_comp ϕ, ← hf,
      ψ.comp_bijective]
  exact funext fun x => mul_inv_rev _ _

@[to_additive]
/-
**Subgroup.isComplement'_comm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsComplement' K ↔ 
K.IsComplement' H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsComplement'.symm`：∀ {G : Type u_1} [inst : Group G] {H K : Su
bgroup G}, H.IsComplement' K → K.IsComplement' H
-/
theorem isComplement'_comm : IsComplement' H K ↔ IsComplement' K H :=
  ⟨IsComplement'.symm, IsComplement'.symm⟩

@[to_additive]
/-
**Subgroup.isComplement_univ_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_univ_singleton {g : G} : IsComplement (univ : Set G) {g}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem isComplement_univ_singleton {g : G} : IsComplement (univ : Set G) {g} :=
  ⟨fun ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ h => Prod.ext (Subtype.ext (mul_right_cancel h)) rfl, fun x =>
    ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩

@[to_additive]
/-
**Subgroup.isComplement_singleton_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_singleton_univ {g : G} : IsComplement ({g} : Set G) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem isComplement_singleton_univ {g : G} : IsComplement ({g} : Set G) univ :=
  ⟨fun ⟨⟨_, rfl⟩, _⟩ ⟨⟨_, rfl⟩, _⟩ h => Prod.ext rfl (Subtype.ext (mul_left_cancel h)), fun x =>
    ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩

@[to_additive]
/-
**Subgroup.isComplement_singleton_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_singleton_left {g : G} : IsComplement {g} S ↔ S = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subgroup.isComplement_singleton_univ`：isComplement_singleton_univ {g : G
} : IsComplement ({g} : Set G) univ
-/
theorem isComplement_singleton_left {g : G} : IsComplement {g} S ↔ S = univ := by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => (congr_arg _ h).mpr isComplement_singleton_univ⟩
  obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x)
  rwa [← mul_left_cancel hy]

@[to_additive]
/-
**Subgroup.isComplement_singleton_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_singleton_right {g : G} : IsComplement S {g} ↔ S = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.isComplement_univ_singleton`：isComplement_univ_singleton {g : G
} : IsComplement (univ : Set G) {g}
-/
theorem isComplement_singleton_right {g : G} : IsComplement S {g} ↔ S = univ := by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => h ▸ isComplement_univ_singleton⟩
  obtain ⟨y, hy⟩ := h.2 (x * g)
  conv_rhs at hy => rw [← show y.2.1 = g from y.2.2]
  rw [← mul_right_cancel hy]
  exact y.1.2

@[to_additive]
/-
**Subgroup.isComplement_univ_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_univ_left : IsComplement univ S ↔ exists g : G, S = {g}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_eq_singleton_iff_nonempty_subsingleton`：exists_eq_singleton_i
ff_nonempty_subsingleton : (exists a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `Subgroup.isComplement_univ_singleton`：isComplement_univ_singleton {g : G
} : IsComplement (univ : Set G) {g}
-/
theorem isComplement_univ_left : IsComplement univ S ↔ ∃ g : G, S = {g} := by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.2.1, a.2.2⟩
  · have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : Set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
      h.1 ((inv_mul_cancel a).trans (inv_mul_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).2
  · rintro ⟨g, rfl⟩
    exact isComplement_univ_singleton

@[to_additive]
/-
**Subgroup.isComplement_univ_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_univ_right : IsComplement S univ ↔ exists g : G, S = {g}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_eq_singleton_iff_nonempty_subsingleton`：exists_eq_singleton_i
ff_nonempty_subsingleton : (exists a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `Subgroup.isComplement_singleton_univ`：isComplement_singleton_univ {g : G
} : IsComplement ({g} : Set G) univ
-/
theorem isComplement_univ_right : IsComplement S univ ↔ ∃ g : G, S = {g} := by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.1.1, a.1.2⟩
  · have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : Set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
      h.1 ((mul_inv_cancel a).trans (mul_inv_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).1
  · rintro ⟨g, rfl⟩
    exact isComplement_singleton_univ

@[to_additive]
/-
**Subgroup.IsComplement.mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComplement`
。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {S T : Set G}, Subgroup.IsComplement S T
 → S * T = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `Subgroup.IsComplement.existsUnique`：∀ {G : Type u_1} [inst : Group G] {S
 T : Set G}, Subgroup.IsComplement S T → ∀ (g : G), ∃! x, ↑x.1 * ↑x.2 = g
-/
lemma IsComplement.mul_eq (h : IsComplement S T) : S * T = univ :=
  eq_univ_of_forall fun x ↦ by simpa [mem_mul] using (h.existsUnique x).exists

@[to_additive (attr := simp)]
/-
**Subgroup.not_isComplement_empty_left** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：not_isComplement_empty_left : ¬ IsComplement ∅ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_mul`：empty_mul : ∅ * s = ∅
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.IsComplement.mul_eq`：∀ {G : Type u_1} [inst : Group G] {S T : S
et G}, Subgroup.IsComplement S T → S * T = Set.univ
-/
lemma not_isComplement_empty_left : ¬ IsComplement ∅ T :=
  fun h ↦ by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive (attr := simp)]
/-
**Subgroup.not_isComplement_empty_right** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：not_isComplement_empty_right : ¬ IsComplement S ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mul_empty`：mul_empty : s * ∅ = ∅
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.IsComplement.mul_eq`：∀ {G : Type u_1} [inst : Group G] {S T : S
et G}, Subgroup.IsComplement S T → S * T = Set.univ
-/
lemma not_isComplement_empty_right : ¬ IsComplement S ∅ :=
  fun h ↦ by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive]
/-
**Subgroup.IsComplement.nonempty_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComp
lement`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {S T : Set G}, Subgroup.IsComplement S T
 → S.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma IsComplement.nonempty_left (hst : IsComplement S T) : S.Nonempty := by
  contrapose! hst; simp [hst]

@[to_additive]
/-
**Subgroup.IsComplement.nonempty_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCom
plement`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {S T : Set G}, Subgroup.IsComplement S T
 → T.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma IsComplement.nonempty_right (hst : IsComplement S T) : T.Nonempty := by
  contrapose! hst; simp [hst]
/-
**Subgroup.IsComplement.pairwiseDisjoint_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p.IsComplement`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {S T : Set G}, Subgroup.IsComplement S T
 → S.PairwiseDisjoint fun x => x • T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[to_additive] lemma IsComplement.pairwiseDisjoint_smul (hst : IsComplement S T) :
    S.PairwiseDisjoint (· • T) := fun a ha b hb hab ↦ disjoint_iff_forall_ne.2 <| by
  rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
  exact hst.1.ne (a₁ := (⟨a, ha⟩, ⟨c, hc⟩)) (a₂ := (⟨b, hb⟩, ⟨d, hd⟩)) (by simp [hab])

@[to_additive AddSubgroup.IsComplement.card_mul_card]
/-
**Subgroup.IsComplement.card_mul_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComp
lement`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {S T : Set G}, Subgroup.IsComplement S T
 → Nat.card ↑S * Nat.card ↑T = Nat.card G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
lemma IsComplement.card_mul_card (h : IsComplement S T) : Nat.card S * Nat.card T = Nat.card G :=
  (Nat.card_prod _ _).symm.trans <| Nat.card_congr <| Equiv.ofBijective _ h

@[to_additive]
/-
**Subgroup.isComplement'_top_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G], ⊤.IsComplement' ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isComplement_univ_singleton`：isComplement_univ_singleton {g : G
} : IsComplement (univ : Set G) {g}
-/
theorem isComplement'_top_bot : IsComplement' (⊤ : Subgroup G) ⊥ :=
  isComplement_univ_singleton

@[to_additive]
/-
**Subgroup.isComplement'_bot_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G], ⊥.IsComplement' ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isComplement_singleton_univ`：isComplement_singleton_univ {g : G
} : IsComplement ({g} : Set G) univ
-/
theorem isComplement'_bot_top : IsComplement' (⊥ : Subgroup G) ⊤ :=
  isComplement_singleton_univ

@[to_additive (attr := simp)]
/-
**Subgroup.isComplement'_bot_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G}, ⊥.IsComplement' H ↔ H 
= ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.isComplement_singleton_left`：isComplement_singleton_left {g : G
} : IsComplement {g} S ↔ S = univ
· 使用定理 `Subgroup.coe_eq_univ`：coe_eq_univ {H : Subgroup G} : (H : Set G) = Set.u
niv ↔ H = ⊤
-/
theorem isComplement'_bot_left : IsComplement' ⊥ H ↔ H = ⊤ :=
  isComplement_singleton_left.trans coe_eq_univ

@[to_additive (attr := simp)]
/-
**Subgroup.isComplement'_bot_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G}, H.IsComplement' ⊥ ↔ H 
= ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.isComplement_singleton_right`：isComplement_singleton_right {g :
 G} : IsComplement S {g} ↔ S = univ
· 使用定理 `Subgroup.coe_eq_univ`：coe_eq_univ {H : Subgroup G} : (H : Set G) = Set.u
niv ↔ H = ⊤
-/
theorem isComplement'_bot_right : IsComplement' H ⊥ ↔ H = ⊤ :=
  isComplement_singleton_right.trans coe_eq_univ

@[to_additive (attr := simp)]
/-
**Subgroup.isComplement'_top_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G}, ⊤.IsComplement' H ↔ H 
= ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.isComplement_univ_left`：isComplement_univ_left : IsComplement u
niv S ↔ exists g : G, S = {g}
· 使用定理 `Subgroup.coe_eq_singleton`：coe_eq_singleton {H : Subgroup G} : (exists g
 : G, (H : Set G) = {g}) ↔ H = ⊥
-/
theorem isComplement'_top_left : IsComplement' ⊤ H ↔ H = ⊥ :=
  isComplement_univ_left.trans coe_eq_singleton

@[to_additive (attr := simp)]
/-
**Subgroup.isComplement'_top_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G}, H.IsComplement' ⊤ ↔ H 
= ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.isComplement_univ_right`：isComplement_univ_right : IsComplement
 S univ ↔ exists g : G, S = {g}
· 使用定理 `Subgroup.coe_eq_singleton`：coe_eq_singleton {H : Subgroup G} : (exists g
 : G, (H : Set G) = {g}) ↔ H = ⊥
-/
theorem isComplement'_top_right : IsComplement' H ⊤ ↔ H = ⊥ :=
  isComplement_univ_right.trans coe_eq_singleton

@[to_additive]
/-
**Subgroup.isComplement_iff_existsUnique_inv_mul_mem** 是 Mathlib 中的一个引理，位于命名空间 `
Subgroup`。
形式化陈述：isComplement_iff_existsUnique_inv_mul_mem : IsComplement S T ↔ forall g, e
xists! s : S, (s : G)⁻¹ * g in T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Subgroup.isComplement_iff_existsUnique`：isComplement_iff_existsUnique : 
IsComplement S T ↔ forall g : G, exists! x : S × T, x.1.1 * x.2.1 = g
-/
lemma isComplement_iff_existsUnique_inv_mul_mem :
    IsComplement S T ↔ ∀ g, ∃! s : S, (s : G)⁻¹ * g ∈ T := by
  convert! isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(x, ⟨_, hx⟩), by simp, by aesop⟩
  · exact ⟨x.1, by simp [← hx], fun y hy ↦ (Prod.ext_iff.1 <| by simpa using hx' (y, ⟨_, hy⟩)).1⟩

@[to_additive]
/-
**Subgroup.isComplement_iff_existsUnique_mul_inv_mem** 是 Mathlib 中的一个引理，位于命名空间 `
Subgroup`。
形式化陈述：isComplement_iff_existsUnique_mul_inv_mem : IsComplement S T ↔ forall g, e
xists! t : T, g * (t : G)⁻¹ in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Subgroup.isComplement_iff_existsUnique`：isComplement_iff_existsUnique : 
IsComplement S T ↔ forall g : G, exists! x : S × T, x.1.1 * x.2.1 = g
-/
lemma isComplement_iff_existsUnique_mul_inv_mem :
    IsComplement S T ↔ ∀ g, ∃! t : T, g * (t : G)⁻¹ ∈ S := by
  convert! isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(⟨_, hx⟩, x), by simp, by aesop⟩
  · exact ⟨x.2, by simp [← hx], fun y hy ↦ (Prod.ext_iff.1 <| by simpa using hx' (⟨_, hy⟩, y)).2⟩

@[to_additive]
/-
**Subgroup.isComplement_subgroup_right_iff_existsUnique_quotientGroupMk** 是 Math
lib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_subgroup_right_iff_existsUnique_quotientGroupMk : IsComplemen
t S H ↔ forall q : G ⧸ H, exists! s : S, QuotientGroup.mk s.1 = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isComplement_subgroup_right_iff_existsUnique_quotientGroupMk :
    IsComplement S H ↔ ∀ q : G ⧸ H, ∃! s : S, QuotientGroup.mk s.1 = q := by
  simp_rw [isComplement_iff_existsUnique_inv_mul_mem, SetLike.mem_coe, ← QuotientGroup.eq,
    QuotientGroup.forall_mk]

set_option linter.docPrime false in
@[to_additive]
/-
**Subgroup.isComplement_subgroup_left_iff_existsUnique_quotientMk''** 是 Mathlib 
中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_subgroup_left_iff_existsUnique_quotientMk'' : IsComplement H 
T ↔ forall q : Quotient (QuotientGroup.rightRel H), exists! t : T, Quotient.mk''
 t.1 = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isComplement_subgroup_left_iff_existsUnique_quotientMk'' :
    IsComplement H T ↔
      ∀ q : Quotient (QuotientGroup.rightRel H), ∃! t : T, Quotient.mk'' t.1 = q := by
  simp_rw [isComplement_iff_existsUnique_mul_inv_mem, SetLike.mem_coe,
    ← QuotientGroup.rightRel_apply, ← Quotient.eq'', Quotient.forall]

@[to_additive]
/-
**Subgroup.isComplement_subgroup_right_iff_bijective** 是 Mathlib 中的一个引理，位于命名空间 `
Subgroup`。
形式化陈述：isComplement_subgroup_right_iff_bijective : IsComplement S H ↔ Bijective (
S.domRestrict (QuotientGroup.mk : G -> G ⧸ H))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Subgroup.isComplement_subgroup_right_iff_existsUnique_quotientGroupMk`：i
sComplement_subgroup_right_iff_existsUnique_quotientGroupMk : IsComplement S H ↔
 forall q : G ⧸ H, exists! s : S, QuotientGroup.mk s.1 = q
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
-/
lemma isComplement_subgroup_right_iff_bijective :
    IsComplement S H ↔ Bijective (S.domRestrict (QuotientGroup.mk : G → G ⧸ H)) :=
  isComplement_subgroup_right_iff_existsUnique_quotientGroupMk.trans
    (bijective_iff_existsUnique (S.domRestrict QuotientGroup.mk)).symm

@[to_additive]
/-
**Subgroup.isComplement_subgroup_left_iff_bijective** 是 Mathlib 中的一个引理，位于命名空间 `S
ubgroup`。
形式化陈述：isComplement_subgroup_left_iff_bijective : IsComplement H T ↔ Bijective (T
.domRestrict (Quotient.mk'' : G -> Quotient (QuotientGroup.rightRel H)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用引理 `Subgroup.isComplement_subgroup_left_iff_existsUnique_quotientMk''`：isCom
plement_subgroup_left_iff_existsUnique_quotientMk'' : IsComplement H T ↔ forall 
q : Quotient (QuotientGroup.rightRel H), exists! t : T,…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
-/
lemma isComplement_subgroup_left_iff_bijective :
    IsComplement H T ↔
      Bijective (T.domRestrict (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel H))) :=
  isComplement_subgroup_left_iff_existsUnique_quotientMk''.trans
    (bijective_iff_existsUnique (T.domRestrict Quotient.mk'')).symm

@[to_additive]
/-
**Subgroup.IsComplement.card_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCompleme
nt`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G} {S : Set G}, Subgroup.I
sComplement S ↑H → Nat.card ↑S = H.index
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subgroup.isComplement_subgroup_right_iff_bijective`：isComplement_subgrou
p_right_iff_bijective : IsComplement S H ↔ Bijective (S.domRestrict (QuotientGro
up.mk : G -> G ⧸ H))
-/
lemma IsComplement.card_left (h : IsComplement S H) : Nat.card S = H.index :=
  Nat.card_congr <| .ofBijective _ <| isComplement_subgroup_right_iff_bijective.mp h

@[to_additive]
/-
**Subgroup.IsComplement.ncard_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComplem
ent`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G} {S : Set G}, Subgroup.I
sComplement S ↑H → S.ncard = H.index
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Subgroup.IsComplement.card_left`：∀ {G : Type u_1} [inst : Group G] {H : 
Subgroup G} {S : Set G}, Subgroup.IsComplement S ↑H → Nat.card ↑S = H.index
-/
theorem IsComplement.ncard_left (h : IsComplement S H) : S.ncard = H.index := by
  rw [← Nat.card_coe_set_eq, h.card_left]

@[to_additive]
/-
**Subgroup.IsComplement.card_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComplem
ent`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G} {T : Set G}, Subgroup.I
sComplement (↑H) T → Nat.card ↑T = H.index
参数：↑H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subgroup.isComplement_subgroup_left_iff_bijective`：isComplement_subgroup
_left_iff_bijective : IsComplement H T ↔ Bijective (T.domRestrict (Quotient.mk''
 : G -> Quotient (QuotientGroup.rightRe…
-/
lemma IsComplement.card_right (h : IsComplement H T) : Nat.card T = H.index :=
  Nat.card_congr <| (Equiv.ofBijective _ <| isComplement_subgroup_left_iff_bijective.mp h).trans <|
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H

@[to_additive]
/-
**Subgroup.IsComplement.ncard_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComple
ment`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G} {T : Set G}, Subgroup.I
sComplement (↑H) T → T.ncard = H.index
参数：↑H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Subgroup.IsComplement.card_right`：∀ {G : Type u_1} [inst : Group G] {H :
 Subgroup G} {T : Set G}, Subgroup.IsComplement (↑H) T → Nat.card ↑T = H.index
-/
theorem IsComplement.ncard_right (h : IsComplement H T) : T.ncard = H.index := by
  rw [← Nat.card_coe_set_eq, h.card_right]

@[to_additive]
/-
**Subgroup.isComplement_range_left** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_range_left {f : G ⧸ H -> G} (hf : forall q, ↑(f q) = q) : IsC
omplement (range f) H
参数：hf : forall q, ↑(f q) = q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.isComplement_subgroup_right_iff_bijective`：isComplement_subgrou
p_right_iff_bijective : IsComplement S H ↔ Bijective (S.domRestrict (QuotientGro
up.mk : G -> G ⧸ H))
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isComplement_range_left {f : G ⧸ H → G} (hf : ∀ q, ↑(f q) = q) :
    IsComplement (range f) H := by
  rw [isComplement_subgroup_right_iff_bijective]
  refine ⟨?_, fun q ↦ ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
  exact Subtype.ext <| congr_arg f <| ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]
/-
**Subgroup.isComplement_range_right** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isComplement_range_right {f : Quotient (QuotientGroup.rightRel H) -> G} (h
f : forall q, Quotient.mk'' (f q) = q) : IsComplement H (range f)
参数：QuotientGroup.rightRel H；hf : forall q, Quotient.mk'' (f q) = q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.isComplement_subgroup_left_iff_bijective`：isComplement_subgroup
_left_iff_bijective : IsComplement H T ↔ Bijective (T.domRestrict (Quotient.mk''
 : G -> Quotient (QuotientGroup.rightRe…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isComplement_range_right {f : Quotient (QuotientGroup.rightRel H) → G}
    (hf : ∀ q, Quotient.mk'' (f q) = q) : IsComplement H (range f) := by
  rw [isComplement_subgroup_left_iff_bijective]
  refine ⟨?_, fun q ↦ ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
  exact Subtype.ext <| congr_arg f <| ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]
/-
**Subgroup.exists_isComplement_left** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：exists_isComplement_left (H : Subgroup G) (g : G) : exists S, IsComplement
 S H ∧ g in S
参数：H : Subgroup G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用引理 `Subgroup.isComplement_range_left`：isComplement_range_left {f : G ⧸ H -> 
G} (hf : forall q, ↑(f q) = q) : IsComplement (range f) H
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_isComplement_left (H : Subgroup G) (g : G) : ∃ S, IsComplement S H ∧ g ∈ S := by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_left fun q ↦ ?_,
    QuotientGroup.mk g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · simp [Function.update, dif_neg hq, q.out_eq']

@[to_additive]
/-
**Subgroup.exists_isComplement_right** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：exists_isComplement_right (H : Subgroup G) (g : G) : exists T, IsComplemen
t H T ∧ g in T
参数：H : Subgroup G；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用引理 `Subgroup.isComplement_range_right`：isComplement_range_right {f : Quotien
t (QuotientGroup.rightRel H) -> G} (hf : forall q, Quotient.mk'' (f q) = q) : Is
Complement H (range f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_isComplement_right (H : Subgroup G) (g : G) :
    ∃ T, IsComplement H T ∧ g ∈ T := by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_right fun q ↦ ?_,
    Quotient.mk'' g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · simp [Function.update, dif_neg hq, q.out_eq']

/-- Given two subgroups `H' ⊆ H`, there exists a left transversal to `H'` inside `H`. -/
@[to_additive /-- Given two subgroups `H' ⊆ H`, there exists a transversal to `H'` inside `H` -/]
/-
**Subgroup.exists_left_transversal_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：exists_left_transversal_of_le {H' H : Subgroup G} (h : H' <= H) : exists S
 : Set G, S * H' = H ∧ Nat.card S * Nat.card H' = Nat.card H
参数：h : H' <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.subgroupOf_map_subtype`：subgroupOf_map_subtype (H K : Subgroup 
G) : (H.subgroupOf K).map K.subtype = H ⊓ K
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Subgroup.exists_isComplement_left`：exists_isComplement_left (H : Subgrou
p G) (g : G) : exists S, IsComplement S H ∧ g in S
· 使用定理 `Set.image_mul`：image_mul : m '' (s * t) = m '' s * m '' t
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.IsComplement.mul_eq`：∀ {G : Type u_1} [inst : Group G] {S T : S
et G}, Subgroup.IsComplement S T → S * T = Set.univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Subgroup.IsComplement.card_mul_card`：∀ {G : Type u_1} [inst : Group G] {
S T : Set G}, Subgroup.IsComplement S T → Nat.card ↑S * Nat.card ↑T = Nat.card G
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype

--- 原说明 ---
Given two subgroups `H' ⊆ H`, there exists a left transversal to `H'` inside `H`
.
-/
lemma exists_left_transversal_of_le {H' H : Subgroup G} (h : H' ≤ H) :
    ∃ S : Set G, S * H' = H ∧ Nat.card S * Nat.card H' = Nat.card H := by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_left 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (S * H'') = H.subtype '' S * H''.map H.subtype := image_mul H.subtype
    rw [← this, cmem.mul_eq]
    simp
  · rw [← cmem.card_mul_card]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

/-- Given two subgroups `H' ⊆ H`, there exists a right transversal to `H'` inside `H`. -/
@[to_additive /-- Given two subgroups `H' ⊆ H`, there exists a transversal to `H'` inside `H` -/]
/-
**Subgroup.exists_right_transversal_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：exists_right_transversal_of_le {H' H : Subgroup G} (h : H' <= H) : exists 
S : Set G, H' * S = H ∧ Nat.card H' * Nat.card S = Nat.card H
参数：h : H' <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.subgroupOf_map_subtype`：subgroupOf_map_subtype (H K : Subgroup 
G) : (H.subgroupOf K).map K.subtype = H ⊓ K
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Subgroup.exists_isComplement_right`：exists_isComplement_right (H : Subgr
oup G) (g : G) : exists T, IsComplement H T ∧ g in T
· 使用定理 `Set.image_mul`：image_mul : m '' (s * t) = m '' s * m '' t
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.IsComplement.mul_eq`：∀ {G : Type u_1} [inst : Group G] {S T : S
et G}, Subgroup.IsComplement S T → S * T = Set.univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Subgroup.IsComplement.card_mul_card`：∀ {G : Type u_1} [inst : Group G] {
S T : Set G}, Subgroup.IsComplement S T → Nat.card ↑S * Nat.card ↑T = Nat.card G
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype

--- 原说明 ---
Given two subgroups `H' ⊆ H`, there exists a right transversal to `H'` inside `H
`.
-/
lemma exists_right_transversal_of_le {H' H : Subgroup G} (h : H' ≤ H) :
    ∃ S : Set G, H' * S = H ∧ Nat.card H' * Nat.card S = Nat.card H := by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_right 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (H'' * S) = H''.map H.subtype * H.subtype '' S := image_mul H.subtype
    rw [← this, cmem.mul_eq]
    simp
  · have : Nat.card H'' * Nat.card S = Nat.card H := cmem.card_mul_card
    rw [← this]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

namespace IsComplement

/-- The equivalence `G ≃ S × T`, such that the inverse is  `(*) : S × T → G` -/
/-
**Subgroup.IsComplement.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.IsComplement`。
形式化陈述：equiv {S T : Set G} (hST : IsComplement S T) : G ≃ S × T
参数：hST : IsComplement S T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence `G ≃ S × T`, such that the inverse is  `(*) : S × T → G`
-/
noncomputable def equiv {S T : Set G} (hST : IsComplement S T) : G ≃ S × T :=
  (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).symm

variable (hST : IsComplement S T) (hHT : IsComplement H T) (hSK : IsComplement S K)
/-
**Subgroup.IsComplement.equiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsC
omplement`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {S T : Set G} (hST : Subgroup.IsCompleme
nt S T) (x : ↑S × ↑T),   hST.equiv.symm x = ↑x.1 * ↑x.2
参数：hST : Subgroup.IsComplement S T；x : ↑S × ↑T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem equiv_symm_apply (x : S × T) : (hST.equiv.symm x : G) = x.1.1 * x.2.1 := rfl

@[simp]
/-
**Subgroup.IsComplement.equiv_fst_mul_equiv_snd** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup.IsComplement`。
形式化陈述：equiv_fst_mul_equiv_snd (g : G) : ↑(hST.equiv g).fst * (hST.equiv g).snd =
 g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem equiv_fst_mul_equiv_snd (g : G) : ↑(hST.equiv g).fst * (hST.equiv g).snd = g :=
  (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).right_inv g
/-
**Subgroup.IsComplement.equiv_fst_eq_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
.IsComplement`。
形式化陈述：equiv_fst_eq_mul_inv (g : G) : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd
 : G)⁻¹
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_mul_inv_of_mul_eq`：eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹
· 使用定理 `Subgroup.IsComplement.equiv_fst_mul_equiv_snd`：equiv_fst_mul_equiv_snd (
g : G) : ↑(hST.equiv g).fst * (hST.equiv g).snd = g
-/
theorem equiv_fst_eq_mul_inv (g : G) : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹ :=
  eq_mul_inv_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)
/-
**Subgroup.IsComplement.equiv_snd_eq_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
.IsComplement`。
形式化陈述：equiv_snd_eq_inv_mul (g : G) : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G
)⁻¹ * g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_inv_mul_of_mul_eq`：eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c
· 使用定理 `Subgroup.IsComplement.equiv_fst_mul_equiv_snd`：equiv_fst_mul_equiv_snd (
g : G) : ↑(hST.equiv g).fst * (hST.equiv g).snd = g
-/
theorem equiv_snd_eq_inv_mul (g : G) : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g :=
  eq_inv_mul_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)
/-
**Subgroup.IsComplement.equiv_fst_eq_iff_leftCosetEquivalence** 是 Mathlib 中的一个定理
，位于命名空间 `Subgroup.IsComplement`。
形式化陈述：equiv_fst_eq_iff_leftCosetEquivalence {g₁ g₂ : G} : (hSK.equiv g₁).fst = (
hSK.equiv g₂).fst ↔ LeftCosetEquivalence K g₁ g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LeftCosetEquivalence.eq_1`：∀ {α : Type u_1} [inst : Mul α] (s : Set α) (
a b : α), LeftCosetEquivalence s a b = (a • s = b • s)
· 使用定理 `leftCoset_eq_iff`：leftCoset_eq_iff {x y : α} : x • (s : Set α) = y • s ↔
 x⁻¹ * y in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.IsComplement.equiv_fst_mul_equiv_snd`：equiv_fst_mul_equiv_snd (
g : G) : ↑(hST.equiv g).fst * (hST.equiv g).snd = g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Subgroup.coe_inv`：coe_inv (x : H) : ↑(x⁻¹ : H) = (x⁻¹ : G)
· 使用定理 `Subgroup.coe_mul`：coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subgroup.isComplement_iff_existsUnique_inv_mul_mem`：isComplement_iff_exi
stsUnique_inv_mul_mem : IsComplement S T ↔ forall g, exists! s : S, (s : G)⁻¹ * 
g in T
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_mul_inv`：equiv_fst_eq_mul_inv (g : G)
 : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `mul_mem_cancel_right`：mul_mem_cancel_right {x y : G} (h : x in H) : y * 
x in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
theorem equiv_fst_eq_iff_leftCosetEquivalence {g₁ g₂ : G} :
    (hSK.equiv g₁).fst = (hSK.equiv g₂).fst ↔ LeftCosetEquivalence K g₁ g₂ := by
  rw [LeftCosetEquivalence, leftCoset_eq_iff]
  constructor
  · intro h
    rw [← hSK.equiv_fst_mul_equiv_snd g₂, ← hSK.equiv_fst_mul_equiv_snd g₁, ← h,
      mul_inv_rev, ← mul_assoc, inv_mul_cancel_right, ← coe_inv, ← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_inv_mul_mem.1 hSK g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_right h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp [← mul_assoc]
/-
**Subgroup.IsComplement.equiv_snd_eq_iff_rightCosetEquivalence** 是 Mathlib 中的一个定
理，位于命名空间 `Subgroup.IsComplement`。
形式化陈述：equiv_snd_eq_iff_rightCosetEquivalence {g₁ g₂ : G} : (hHT.equiv g₁).snd = 
(hHT.equiv g₂).snd ↔ RightCosetEquivalence H g₁ g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RightCosetEquivalence.eq_1`：∀ {α : Type u_1} [inst : Mul α] (s : Set α) 
(a b : α),   RightCosetEquivalence s a b = (MulOpposite.op a • s = MulOpposite.o
p b • s)
· 使用定理 `rightCoset_eq_iff`：rightCoset_eq_iff {x y : α} : op x • (s : Set α) = op
 y • s ↔ y * x⁻¹ in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.IsComplement.equiv_fst_mul_equiv_snd`：equiv_fst_mul_equiv_snd (
g : G) : ↑(hST.equiv g).fst * (hST.equiv g).snd = g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Subgroup.coe_inv`：coe_inv (x : H) : ↑(x⁻¹ : H) = (x⁻¹ : G)
· 使用定理 `Subgroup.coe_mul`：coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subgroup.isComplement_iff_existsUnique_mul_inv_mem`：isComplement_iff_exi
stsUnique_mul_inv_mem : IsComplement S T ↔ forall g, exists! t : T, g * (t : G)⁻
¹ in S
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_inv_mul`：equiv_snd_eq_inv_mul (g : G)
 : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `mul_mem_cancel_left`：mul_mem_cancel_left {x y : G} (h : x in H) : x * y 
in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem equiv_snd_eq_iff_rightCosetEquivalence {g₁ g₂ : G} :
    (hHT.equiv g₁).snd = (hHT.equiv g₂).snd ↔ RightCosetEquivalence H g₁ g₂ := by
  rw [RightCosetEquivalence, rightCoset_eq_iff]
  constructor
  · intro h
    rw [← hHT.equiv_fst_mul_equiv_snd g₂, ← hHT.equiv_fst_mul_equiv_snd g₁, ← h,
      mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← coe_inv, ← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_mul_inv_mem.1 hHT g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_left h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul, mul_assoc]; simp
/-
**Subgroup.IsComplement.leftCosetEquivalence_equiv_fst** 是 Mathlib 中的一个定理，位于命名空间
 `Subgroup.IsComplement`。
形式化陈述：leftCosetEquivalence_equiv_fst (g : G) : LeftCosetEquivalence K g ((hSK.eq
uiv g).fst : G)
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_mul_inv`：equiv_fst_eq_mul_inv (g : G)
 : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem leftCosetEquivalence_equiv_fst (g : G) :
    LeftCosetEquivalence K g ((hSK.equiv g).fst : G) := by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [equiv_fst_eq_mul_inv]; simp [LeftCosetEquivalence, leftCoset_eq_iff]
/-
**Subgroup.IsComplement.rightCosetEquivalence_equiv_snd** 是 Mathlib 中的一个定理，位于命名空
间 `Subgroup.IsComplement`。
形式化陈述：rightCosetEquivalence_equiv_snd (g : G) : RightCosetEquivalence H g ((hHT.
equiv g).snd : G)
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RightCosetEquivalence.eq_1`：∀ {α : Type u_1} [inst : Mul α] (s : Set α) 
(a b : α),   RightCosetEquivalence s a b = (MulOpposite.op a • s = MulOpposite.o
p b • s)
· 使用定理 `rightCoset_eq_iff`：rightCoset_eq_iff {x y : α} : op x • (s : Set α) = op
 y • s ↔ y * x⁻¹ in s
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_inv_mul`：equiv_snd_eq_inv_mul (g : G)
 : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem rightCosetEquivalence_equiv_snd (g : G) :
    RightCosetEquivalence H g ((hHT.equiv g).snd : G) := by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [RightCosetEquivalence, rightCoset_eq_iff, equiv_snd_eq_inv_mul]; simp

set_option backward.isDefEq.respectTransparency false in
/-
**Subgroup.IsComplement.equiv_fst_eq_self_of_mem_of_one_mem** 是 Mathlib 中的一个定理，位
于命名空间 `Subgroup.IsComplement`。
形式化陈述：equiv_fst_eq_self_of_mem_of_one_mem {g : G} (h1 : 1 in T) (hg : g in S) : 
(hST.equiv g).fst = ⟨g, hg⟩
参数：h1 : 1 in T；hg : g in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.IsComplement.equiv.eq_1`：∀ {G : Type u_1} [inst : Group G] {S T
 : Set G} (hST : Subgroup.IsComplement S T),   hST.equiv = (Equiv.ofBijective (f
un x => ↑x.1 * ↑x.2) h…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Function.leftInverse_surjInv`：leftInverse_surjInv (hf : Bijective f) : L
eftInverse (surjInv hf.2) f
· 使用定理 `Equiv.ofBijective.eq_1`：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : Fu
nction.Bijective f),   Equiv.ofBijective f hf = { toFun := f, invFun := Function
.surjInv ⋯, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem equiv_fst_eq_self_of_mem_of_one_mem {g : G} (h1 : 1 ∈ T) (hg : g ∈ S) :
    (hST.equiv g).fst = ⟨g, hg⟩ := by
  have : hST.equiv.symm (⟨g, hg⟩, ⟨1, h1⟩) = g := by
    rw [equiv, Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**Subgroup.IsComplement.equiv_snd_eq_self_of_mem_of_one_mem** 是 Mathlib 中的一个定理，位
于命名空间 `Subgroup.IsComplement`。
形式化陈述：equiv_snd_eq_self_of_mem_of_one_mem {g : G} (h1 : 1 in S) (hg : g in T) : 
(hST.equiv g).snd = ⟨g, hg⟩
参数：h1 : 1 in S；hg : g in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.IsComplement.equiv.eq_1`：∀ {G : Type u_1} [inst : Group G] {S T
 : Set G} (hST : Subgroup.IsComplement S T),   hST.equiv = (Equiv.ofBijective (f
un x => ↑x.1 * ↑x.2) h…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Function.leftInverse_surjInv`：leftInverse_surjInv (hf : Bijective f) : L
eftInverse (surjInv hf.2) f
· 使用定理 `Equiv.ofBijective.eq_1`：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : Fu
nction.Bijective f),   Equiv.ofBijective f hf = { toFun := f, invFun := Function
.surjInv ⋯, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem equiv_snd_eq_self_of_mem_of_one_mem {g : G} (h1 : 1 ∈ S) (hg : g ∈ T) :
    (hST.equiv g).snd = ⟨g, hg⟩ := by
  have : hST.equiv.symm (⟨1, h1⟩, ⟨g, hg⟩) = g := by
    rw [equiv, Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]
/-
**Subgroup.IsComplement.equiv_snd_eq_one_of_mem_of_one_mem** 是 Mathlib 中的一个定理，位于
命名空间 `Subgroup.IsComplement`。
形式化陈述：equiv_snd_eq_one_of_mem_of_one_mem {g : G} (h1 : 1 in T) (hg : g in S) : (
hST.equiv g).snd = ⟨1, h1⟩
参数：h1 : 1 in T；hg : g in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_inv_mul`：equiv_snd_eq_inv_mul (g : G)
 : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_self_of_mem_of_one_mem`：equiv_fst_eq_
self_of_mem_of_one_mem {g : G} (h1 : 1 in T) (hg : g in S) : (hST.equiv g).fst =
 ⟨g, hg⟩
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
theorem equiv_snd_eq_one_of_mem_of_one_mem {g : G} (h1 : 1 ∈ T) (hg : g ∈ S) :
    (hST.equiv g).snd = ⟨1, h1⟩ := by
  ext
  rw [equiv_snd_eq_inv_mul, equiv_fst_eq_self_of_mem_of_one_mem _ h1 hg, inv_mul_cancel]
/-
**Subgroup.IsComplement.equiv_fst_eq_one_of_mem_of_one_mem** 是 Mathlib 中的一个定理，位于
命名空间 `Subgroup.IsComplement`。
形式化陈述：equiv_fst_eq_one_of_mem_of_one_mem {g : G} (h1 : 1 in S) (hg : g in T) : (
hST.equiv g).fst = ⟨1, h1⟩
参数：h1 : 1 in S；hg : g in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_mul_inv`：equiv_fst_eq_mul_inv (g : G)
 : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_self_of_mem_of_one_mem`：equiv_snd_eq_
self_of_mem_of_one_mem {g : G} (h1 : 1 in S) (hg : g in T) : (hST.equiv g).snd =
 ⟨g, hg⟩
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
-/
theorem equiv_fst_eq_one_of_mem_of_one_mem {g : G} (h1 : 1 ∈ S) (hg : g ∈ T) :
    (hST.equiv g).fst = ⟨1, h1⟩ := by
  ext
  rw [equiv_fst_eq_mul_inv, equiv_snd_eq_self_of_mem_of_one_mem _ h1 hg, mul_inv_cancel]
/-
**Subgroup.IsComplement.equiv_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCo
mplement`。
形式化陈述：equiv_mul_right (g : G) (k : K) : hSK.equiv (g * k) = ((hSK.equiv g).fst, 
(hSK.equiv g).snd * k)
参数：g : G；k : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_iff_leftCosetEquivalence`：equiv_fst_e
q_iff_leftCosetEquivalence {g₁ g₂ : G} : (hSK.equiv g₁).fst = (hSK.equiv g₂).fst
 ↔ LeftCosetEquivalence K g₁ g₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subgroup.coe_mul`：coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_inv_mul`：equiv_snd_eq_inv_mul (g : G)
 : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem equiv_mul_right (g : G) (k : K) :
    hSK.equiv (g * k) = ((hSK.equiv g).fst, (hSK.equiv g).snd * k) := by
  have : (hSK.equiv (g * k)).fst = (hSK.equiv g).fst :=
    hSK.equiv_fst_eq_iff_leftCosetEquivalence.2
      (by simp [LeftCosetEquivalence, leftCoset_eq_iff])
  ext
  · rw [this]
  · rw [coe_mul, equiv_snd_eq_inv_mul, this, equiv_snd_eq_inv_mul, mul_assoc]
/-
**Subgroup.IsComplement.equiv_mul_right_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up.IsComplement`。
形式化陈述：equiv_mul_right_of_mem {g k : G} (h : k in K) : hSK.equiv (g * k) = ((hSK.
equiv g).fst, (hSK.equiv g).snd * ⟨k, h⟩)
参数：h : k in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsComplement.equiv_mul_right`：equiv_mul_right (g : G) (k : K) :
 hSK.equiv (g * k) = ((hSK.equiv g).fst, (hSK.equiv g).snd * k)
-/
theorem equiv_mul_right_of_mem {g k : G} (h : k ∈ K) :
    hSK.equiv (g * k) = ((hSK.equiv g).fst, (hSK.equiv g).snd * ⟨k, h⟩) :=
  equiv_mul_right _ g ⟨k, h⟩
/-
**Subgroup.IsComplement.equiv_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCom
plement`。
形式化陈述：equiv_mul_left (h : H) (g : G) : hHT.equiv (h * g) = (h * (hHT.equiv g).fs
t, (hHT.equiv g).snd)
参数：h : H；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_iff_rightCosetEquivalence`：equiv_snd_
eq_iff_rightCosetEquivalence {g₁ g₂ : G} : (hHT.equiv g₁).snd = (hHT.equiv g₂).s
nd ↔ RightCosetEquivalence H g₁ g₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `op_smul_coe_set`：op_smul_coe_set [Group G] [SetLike S G] [SubgroupClass 
S G] {s : S} {a : G} (ha : a in s) : MulOpposite.op a • (s : Set G) = s
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subgroup.coe_mul`：coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_mul_inv`：equiv_fst_eq_mul_inv (g : G)
 : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem equiv_mul_left (h : H) (g : G) :
    hHT.equiv (h * g) = (h * (hHT.equiv g).fst, (hHT.equiv g).snd) := by
  have : (hHT.equiv (h * g)).2 = (hHT.equiv g).2 := hHT.equiv_snd_eq_iff_rightCosetEquivalence.2 ?_
  · ext
    · rw [coe_mul, equiv_fst_eq_mul_inv, this, equiv_fst_eq_mul_inv, mul_assoc]
    · rw [this]
  · simp [RightCosetEquivalence, ← smul_smul]
/-
**Subgroup.IsComplement.equiv_mul_left_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p.IsComplement`。
形式化陈述：equiv_mul_left_of_mem {h g : G} (hh : h in H) : hHT.equiv (h * g) = (⟨h, h
h⟩ * (hHT.equiv g).fst, (hHT.equiv g).snd)
参数：hh : h in H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsComplement.equiv_mul_left`：equiv_mul_left (h : H) (g : G) : h
HT.equiv (h * g) = (h * (hHT.equiv g).fst, (hHT.equiv g).snd)
-/
theorem equiv_mul_left_of_mem {h g : G} (hh : h ∈ H) :
    hHT.equiv (h * g) = (⟨h, hh⟩ * (hHT.equiv g).fst, (hHT.equiv g).snd) :=
  equiv_mul_left _ ⟨h, hh⟩ g

set_option backward.isDefEq.respectTransparency false in
/-
**Subgroup.IsComplement.equiv_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCompleme
nt`。
形式化陈述：equiv_one (hs1 : 1 in S) (ht1 : 1 in T) : hST.equiv 1 = (⟨1, hs1⟩, ⟨1, ht1
⟩)
参数：hs1 : 1 in S；ht1 : 1 in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.ofBijective_apply`：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : F
unction.Bijective f) (a : α), (Equiv.ofBijective f hf) a = f a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_one (hs1 : 1 ∈ S) (ht1 : 1 ∈ T) :
    hST.equiv 1 = (⟨1, hs1⟩, ⟨1, ht1⟩) := by
  rw [← Equiv.eq_symm_apply]; simp [equiv]
/-
**Subgroup.IsComplement.equiv_fst_eq_self_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sub
group.IsComplement`。
形式化陈述：equiv_fst_eq_self_iff_mem {g : G} (h1 : 1 in T) : ((hST.equiv g).fst : G) 
= g ↔ g in S
参数：h1 : 1 in T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_self_of_mem_of_one_mem`：equiv_fst_eq_
self_of_mem_of_one_mem {g : G} (h1 : 1 in T) (hg : g in S) : (hST.equiv g).fst =
 ⟨g, hg⟩
-/
theorem equiv_fst_eq_self_iff_mem {g : G} (h1 : 1 ∈ T) :
    ((hST.equiv g).fst : G) = g ↔ g ∈ S := by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_fst_eq_self_of_mem_of_one_mem h1 h]
/-
**Subgroup.IsComplement.equiv_snd_eq_self_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sub
group.IsComplement`。
形式化陈述：equiv_snd_eq_self_iff_mem {g : G} (h1 : 1 in S) : ((hST.equiv g).snd : G) 
= g ↔ g in T
参数：h1 : 1 in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_self_of_mem_of_one_mem`：equiv_snd_eq_
self_of_mem_of_one_mem {g : G} (h1 : 1 in S) (hg : g in T) : (hST.equiv g).snd =
 ⟨g, hg⟩
-/
theorem equiv_snd_eq_self_iff_mem {g : G} (h1 : 1 ∈ S) :
    ((hST.equiv g).snd : G) = g ↔ g ∈ T := by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_snd_eq_self_of_mem_of_one_mem h1 h]
/-
**Subgroup.IsComplement.coe_equiv_fst_eq_one_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `
Subgroup.IsComplement`。
形式化陈述：coe_equiv_fst_eq_one_iff_mem {g : G} (h1 : 1 in S) : ((hST.equiv g).fst : 
G) = 1 ↔ g in T
参数：h1 : 1 in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_mul_inv`：equiv_fst_eq_mul_inv (g : G)
 : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_self_iff_mem`：equiv_snd_eq_self_iff_m
em {g : G} (h1 : 1 in S) : ((hST.equiv g).snd : G) = g ↔ g in T
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_equiv_fst_eq_one_iff_mem {g : G} (h1 : 1 ∈ S) :
    ((hST.equiv g).fst : G) = 1 ↔ g ∈ T := by
  rw [equiv_fst_eq_mul_inv, mul_inv_eq_one, eq_comm, equiv_snd_eq_self_iff_mem _ h1]
/-
**Subgroup.IsComplement.coe_equiv_snd_eq_one_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `
Subgroup.IsComplement`。
形式化陈述：coe_equiv_snd_eq_one_iff_mem {g : G} (h1 : 1 in T) : ((hST.equiv g).snd : 
G) = 1 ↔ g in S
参数：h1 : 1 in T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_inv_mul`：equiv_snd_eq_inv_mul (g : G)
 : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_self_iff_mem`：equiv_fst_eq_self_iff_m
em {g : G} (h1 : 1 in T) : ((hST.equiv g).fst : G) = g ↔ g in S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_equiv_snd_eq_one_iff_mem {g : G} (h1 : 1 ∈ T) :
    ((hST.equiv g).snd : G) = 1 ↔ g ∈ S := by
  rw [equiv_snd_eq_inv_mul, inv_mul_eq_one, equiv_fst_eq_self_iff_mem _ h1]

/-- A left transversal is in bijection with left cosets. -/
@[to_additive /-- A left transversal is in bijection with left cosets. -/]
/-
**Subgroup.IsComplement.leftQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.Is
Complement`。
形式化陈述：leftQuotientEquiv (hS : IsComplement S H) : G ⧸ H ≃ S
参数：hS : IsComplement S H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A left transversal is in bijection with left cosets.
-/
noncomputable def leftQuotientEquiv (hS : IsComplement S H) : G ⧸ H ≃ S :=
  (Equiv.ofBijective _ (isComplement_subgroup_right_iff_bijective.mp hS)).symm

/-- A left transversal is finite iff the subgroup has finite index. -/
@[to_additive /-- A left transversal is finite iff the subgroup has finite index. -/]
/-
**Subgroup.IsComplement.finite_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCo
mplement`。
形式化陈述：finite_left_iff (h : IsComplement S H) : Finite S ↔ H.FiniteIndex
参数：h : IsComplement S H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `Subgroup.finiteIndex_of_finite_quotient`：finiteIndex_of_finite_quotient 
[Finite (G ⧸ H)] : FiniteIndex H

--- 原说明 ---
A left transversal is finite iff the subgroup has finite index.
-/
theorem finite_left_iff (h : IsComplement S H) : Finite S ↔ H.FiniteIndex := by
  rw [← h.leftQuotientEquiv.finite_iff]
  exact ⟨fun _ ↦ finiteIndex_of_finite_quotient, fun _ ↦ finite_quotient_of_finiteIndex⟩

@[to_additive]
/-
**Subgroup.IsComplement.finite_left** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsComple
ment`。
形式化陈述：finite_left [H.FiniteIndex] (hS : IsComplement S H) : S.Finite
参数：hS : IsComplement S H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.IsComplement.finite_left_iff`：finite_left_iff (h : IsComplement
 S H) : Finite S ↔ H.FiniteIndex
-/
lemma finite_left [H.FiniteIndex] (hS : IsComplement S H) : S.Finite := hS.finite_left_iff.2 ‹_›

@[to_additive]
/-
**Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv** 是 Mathlib 中的一个定理，位于命
名空间 `Subgroup.IsComplement`。
形式化陈述：quotientGroupMk_leftQuotientEquiv (hS : IsComplement S H) (q : G ⧸ H) : Qu
otient.mk'' (leftQuotientEquiv hS q : G) = q
参数：hS : IsComplement S H；q : G ⧸ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem quotientGroupMk_leftQuotientEquiv (hS : IsComplement S H) (q : G ⧸ H) :
    Quotient.mk'' (leftQuotientEquiv hS q : G) = q :=
  hS.leftQuotientEquiv.symm_apply_apply q

@[to_additive]
/-
**Subgroup.IsComplement.leftQuotientEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup.IsComplement`。
形式化陈述：leftQuotientEquiv_apply {f : G ⧸ H -> G} (hf : forall q, (f q : G ⧸ H) = q
) (q : G ⧸ H) : (leftQuotientEquiv (isComplement_range_left hf) q : G) = f q
参数：hf : forall q, (f q : G ⧸ H) = q；q : G ⧸ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Subgroup.isComplement_range_left`：isComplement_range_left {f : G ⧸ H -> 
G} (hf : forall q, ↑(f q) = q) : IsComplement (range f) H
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
-/
theorem leftQuotientEquiv_apply {f : G ⧸ H → G} (hf : ∀ q, (f q : G ⧸ H) = q) (q : G ⧸ H) :
    (leftQuotientEquiv (isComplement_range_left hf) q : G) = f q := by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (leftQuotientEquiv (isComplement_range_left hf)).eq_symm_apply.mp (hf q).symm

/-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/
@[to_additive /-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/]
/-
**Subgroup.IsComplement.toLeftFun** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.IsCompleme
nt`。
形式化陈述：toLeftFun (hS : IsComplement S H) : G -> S
参数：hS : IsComplement S H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
noncomputable def toLeftFun (hS : IsComplement S H) : G → S := leftQuotientEquiv hS ∘ Quotient.mk''

@[to_additive]
/-
**Subgroup.IsComplement.inv_toLeftFun_mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p.IsComplement`。
形式化陈述：inv_toLeftFun_mul_mem (hS : IsComplement S H) (g : G) : (toLeftFun hS g : 
G)⁻¹ * g in H
参数：hS : IsComplement S H；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `Quotient.exact'`：exact' {a b : α} : (Quotient.mk'' a : Quotient s₁) = Qu
otient.mk'' b -> s₁ a b
· 使用定理 `Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv`：quotientGroupMk
_leftQuotientEquiv (hS : IsComplement S H) (q : G ⧸ H) : Quotient.mk'' (leftQuot
ientEquiv hS q : G) = q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem inv_toLeftFun_mul_mem (hS : IsComplement S H) (g : G) :
    (toLeftFun hS g : G)⁻¹ * g ∈ H :=
  QuotientGroup.leftRel_apply.mp <| Quotient.exact' <| quotientGroupMk_leftQuotientEquiv _ _

@[to_additive]
/-
**Subgroup.IsComplement.inv_mul_toLeftFun_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p.IsComplement`。
形式化陈述：inv_mul_toLeftFun_mem (hS : IsComplement S H) (g : G) : g⁻¹ * toLeftFun hS
 g in H
参数：hS : IsComplement S H；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `Subgroup.IsComplement.inv_toLeftFun_mul_mem`：inv_toLeftFun_mul_mem (hS :
 IsComplement S H) (g : G) : (toLeftFun hS g : G)⁻¹ * g in H
-/
theorem inv_mul_toLeftFun_mem (hS : IsComplement S H) (g : G) :
    g⁻¹ * toLeftFun hS g ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (inv_toLeftFun_mul_mem hS g))

/-- A right transversal is in bijection with right cosets. -/
@[to_additive /-- A right transversal is in bijection with right cosets. -/]
/-
**Subgroup.IsComplement.rightQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.I
sComplement`。
形式化陈述：rightQuotientEquiv (hT : IsComplement H T) : Quotient (QuotientGroup.right
Rel H) ≃ T
参数：hT : IsComplement H T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
A right transversal is in bijection with right cosets.
-/
noncomputable def rightQuotientEquiv (hT : IsComplement H T) :
    Quotient (QuotientGroup.rightRel H) ≃ T :=
  (Equiv.ofBijective _ (isComplement_subgroup_left_iff_bijective.mp hT)).symm

/-- A right transversal is finite iff the subgroup has finite index. -/
@[to_additive /-- A right transversal is finite iff the subgroup has finite index. -/]
/-
**Subgroup.IsComplement.finite_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsC
omplement`。
形式化陈述：finite_right_iff (h : IsComplement H T) : Finite T ↔ H.FiniteIndex
参数：h : IsComplement H T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `Subgroup.finiteIndex_of_finite_quotient`：finiteIndex_of_finite_quotient 
[Finite (G ⧸ H)] : FiniteIndex H

--- 原说明 ---
A right transversal is finite iff the subgroup has finite index.
-/
theorem finite_right_iff (h : IsComplement H T) : Finite T ↔ H.FiniteIndex := by
  rw [← h.rightQuotientEquiv.finite_iff,
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).finite_iff]
  exact ⟨fun _ ↦ finiteIndex_of_finite_quotient, fun _ ↦ finite_quotient_of_finiteIndex⟩

@[to_additive]
/-
**Subgroup.IsComplement.finite_right** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsCompl
ement`。
形式化陈述：finite_right [H.FiniteIndex] (hT : IsComplement H T) : T.Finite
参数：hT : IsComplement H T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.IsComplement.finite_right_iff`：finite_right_iff (h : IsCompleme
nt H T) : Finite T ↔ H.FiniteIndex
-/
lemma finite_right [H.FiniteIndex] (hT : IsComplement H T) : T.Finite := hT.finite_right_iff.2 ‹_›

@[to_additive]
/-
**Subgroup.IsComplement.mk''_rightQuotientEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup.IsComplement`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G} {T : Set G} (hT : Subgr
oup.IsComplement (↑H) T)   (q : Quotient (QuotientGroup.rightRel H)), Quotient.m
k'' ↑(hT.rightQuotientEquiv q) = q
参数：hT : Subgroup.IsComplement (↑H) T；q : Quotient (QuotientGroup.rightRel H)；hT.
rightQuotientEquiv q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem mk''_rightQuotientEquiv (hT : IsComplement H T)
     (q : Quotient (QuotientGroup.rightRel H)) : Quotient.mk'' (rightQuotientEquiv hT q : G) = q :=
  (rightQuotientEquiv hT).symm_apply_apply q

@[to_additive]
/-
**Subgroup.IsComplement.rightQuotientEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subg
roup.IsComplement`。
形式化陈述：rightQuotientEquiv_apply {f : Quotient (QuotientGroup.rightRel H) -> G} (h
f : forall q, Quotient.mk'' (f q) = q) (q : Quotient (QuotientGroup.rightRel H))
 : (rightQuotientEquiv (isComplement_range_right hf) q : G) = f q
参数：QuotientGroup.rightRel H；hf : forall q, Quotient.mk'' (f q) = q；q : Quotient 
(QuotientGroup.rightRel H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Subgroup.isComplement_range_right`：isComplement_range_right {f : Quotien
t (QuotientGroup.rightRel H) -> G} (hf : forall q, Quotient.mk'' (f q) = q) : Is
Complement H (range f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
-/
theorem rightQuotientEquiv_apply {f : Quotient (QuotientGroup.rightRel H) → G}
    (hf : ∀ q, Quotient.mk'' (f q) = q) (q : Quotient (QuotientGroup.rightRel H)) :
    (rightQuotientEquiv (isComplement_range_right hf) q : G) = f q := by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (rightQuotientEquiv (isComplement_range_right hf)).eq_symm_apply.1 (hf q).symm

/-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/
@[to_additive /-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/]
/-
**Subgroup.IsComplement.toRightFun** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.IsComplem
ent`。
形式化陈述：toRightFun (hT : IsComplement H T) : G -> T
参数：hT : IsComplement H T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
noncomputable def toRightFun (hT : IsComplement H T) : G → T := rightQuotientEquiv hT ∘ .mk''

@[to_additive]
/-
**Subgroup.IsComplement.mul_inv_toRightFun_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up.IsComplement`。
形式化陈述：mul_inv_toRightFun_mem (hT : IsComplement H T) (g : G) : g * (toRightFun h
T g : G)⁻¹ in H
参数：hT : IsComplement H T；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.rightRel_apply`：rightRel_apply {x y : α} : rightRel s x y 
↔ y * x⁻¹ in s
· 使用定理 `Quotient.exact'`：exact' {a b : α} : (Quotient.mk'' a : Quotient s₁) = Qu
otient.mk'' b -> s₁ a b
· 使用定理 `Subgroup.IsComplement.mk''_rightQuotientEquiv`：∀ {G : Type u_1} [inst : 
Group G] {H : Subgroup G} {T : Set G} (hT : Subgroup.IsComplement (↑H) T)   (q :
 Quotient (QuotientGroup.rightRel H…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem mul_inv_toRightFun_mem (hT : IsComplement H T) (g : G) :
    g * (toRightFun hT g : G)⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.mp <| Quotient.exact' <| mk''_rightQuotientEquiv _ _

@[to_additive]
/-
**Subgroup.IsComplement.toRightFun_mul_inv_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up.IsComplement`。
形式化陈述：toRightFun_mul_inv_mem (hT : IsComplement H T) (g : G) : (toRightFun hT g 
: G) * g⁻¹ in H
参数：hT : IsComplement H T；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `Subgroup.IsComplement.mul_inv_toRightFun_mem`：mul_inv_toRightFun_mem (hT
 : IsComplement H T) (g : G) : g * (toRightFun hT g : G)⁻¹ in H
-/
theorem toRightFun_mul_inv_mem (hT : IsComplement H T) (g : G) :
    (toRightFun hT g : G) * g⁻¹ ∈ H :=
  (congr_arg (· ∈ H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (mul_inv_toRightFun_mem hT g))

@[to_additive]
/-
**Subgroup.IsComplement.encard_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComple
ment`。
形式化陈述：encard_left [H.FiniteIndex] (h : IsComplement S H) : S.encard = H.index
参数：h : IsComplement S H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用引理 `Subgroup.IsComplement.finite_left`：finite_left [H.FiniteIndex] (hS : IsC
omplement S H) : S.Finite
· 使用定理 `Subgroup.IsComplement.ncard_left`：∀ {G : Type u_1} [inst : Group G] {H :
 Subgroup G} {S : Set G}, Subgroup.IsComplement S ↑H → S.ncard = H.index
-/
theorem encard_left [H.FiniteIndex] (h : IsComplement S H) : S.encard = H.index := by
  rw [← h.finite_left.cast_ncard_eq, h.ncard_left]

@[to_additive]
/-
**Subgroup.IsComplement.encard_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCompl
ement`。
形式化陈述：encard_right [H.FiniteIndex] (h : IsComplement H T) : T.encard = H.index
参数：h : IsComplement H T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
· 使用引理 `Subgroup.IsComplement.finite_right`：finite_right [H.FiniteIndex] (hT : I
sComplement H T) : T.Finite
· 使用定理 `Subgroup.IsComplement.ncard_right`：∀ {G : Type u_1} [inst : Group G] {H 
: Subgroup G} {T : Set G}, Subgroup.IsComplement (↑H) T → T.ncard = H.index
-/
theorem encard_right [H.FiniteIndex] (h : IsComplement H T) : T.encard = H.index := by
  rw [← h.finite_right.cast_ncard_eq, h.ncard_right]

end IsComplement

section Action

open scoped Pointwise
open MulAction

/-- The collection of left transversals of a subgroup -/
@[to_additive /-- The collection of left transversals of a subgroup. -/]
/-
**Subgroup.LeftTransversal** 是 Mathlib 中的一个缩写定义，位于命名空间 `Subgroup`。
形式化陈述：LeftTransversal (H : Subgroup G)
参数：H : Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The collection of left transversals of a subgroup
-/
abbrev LeftTransversal (H : Subgroup G) := {S : Set G // IsComplement S H}

/-- The collection of right transversals of a subgroup -/
@[to_additive /-- The collection of right transversals of a subgroup. -/]
/-
**Subgroup.RightTransversal** 是 Mathlib 中的一个缩写定义，位于命名空间 `Subgroup`。
形式化陈述：RightTransversal (H : Subgroup G)
参数：H : Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The collection of right transversals of a subgroup
-/
abbrev RightTransversal (H : Subgroup G) := {T : Set G // IsComplement H T}

variable {F : Type*} [Group F] [MulAction F G] [QuotientAction F H]

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : MulAction F H.LeftTransversal where
  smul f T :=
    ⟨f • (T : Set G), by
      refine isComplement_iff_existsUnique_inv_mul_mem.mpr fun g => ?_
      obtain ⟨t, ht1, ht2⟩ := isComplement_iff_existsUnique_inv_mul_mem.mp T.2 (f⁻¹ • g)
      refine ⟨⟨f • (t : G), Set.smul_mem_smul_set t.2⟩, ?_, ?_⟩
      · exact smul_inv_smul f g ▸ QuotientAction.inv_mul_mem f ht1
      · rintro ⟨-, t', ht', rfl⟩ h
        replace h := QuotientAction.inv_mul_mem f⁻¹ h
        simp only [Subtype.ext_iff, smul_left_cancel_iff, inv_smul_smul] at h ⊢
        exact Subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)⟩
  one_smul T := Subtype.ext (one_smul F (T : Set G))
  mul_smul f₁ f₂ T := Subtype.ext (mul_smul f₁ f₂ (T : Set G))

@[to_additive]
/-
**Subgroup.smul_toLeftFun** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_toLeftFun (f : F) (S : H.LeftTransversal) (g : G) : (f • (S.2.toLeftF
un g : G)) = (f • S).2.toLeftFun (f • g)
参数：f : F；S : H.LeftTransversal；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用引理 `Subgroup.isComplement_iff_existsUnique_inv_mul_mem`：isComplement_iff_exi
stsUnique_inv_mul_mem : IsComplement S T ↔ forall g, exists! s : S, (s : G)⁻¹ * 
g in T
· 使用定理 `MulAction.QuotientAction.inv_mul_mem`：∀ {G : Type u} {X : Type v} {inst 
: Group G} {inst_1 : Monoid X} {inst_2 : MulAction X G} {H : Subgroup G}   [self
 : MulAction.QuotientActio…
· 使用定理 `Subgroup.IsComplement.inv_toLeftFun_mul_mem`：inv_toLeftFun_mul_mem (hS :
 IsComplement S H) (g : G) : (toLeftFun hS g : G)⁻¹ * g in H
-/
theorem smul_toLeftFun (f : F) (S : H.LeftTransversal) (g : G) :
    (f • (S.2.toLeftFun g : G)) = (f • S).2.toLeftFun (f • g) :=
  Subtype.ext_iff.mp <| @ExistsUnique.unique (↥(f • (S : Set G))) (fun s => (↑s)⁻¹ * f • g ∈ H)
    (isComplement_iff_existsUnique_inv_mul_mem.mp (f • S).2 (f • g))
    ⟨f • (S.2.toLeftFun g : G), Set.smul_mem_smul_set (Subtype.coe_prop _)⟩
      ((f • S).2.toLeftFun (f • g))
    (QuotientAction.inv_mul_mem f (S.2.inv_toLeftFun_mul_mem g))
      ((f • S).2.inv_toLeftFun_mul_mem (f • g))

@[to_additive]
/-
**Subgroup.smul_leftQuotientEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_leftQuotientEquiv (f : F) (S : H.LeftTransversal) (q : G ⧸ H) : f • (
S.2.leftQuotientEquiv q : G) = (f • S).2.leftQuotientEquiv (f • q)
参数：f : F；S : H.LeftTransversal；q : G ⧸ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.smul_toLeftFun`：smul_toLeftFun (f : F) (S : H.LeftTransversal) 
(g : G) : (f • (S.2.toLeftFun g : G)) = (f • S).2.toLeftFun (f • g)
-/
theorem smul_leftQuotientEquiv (f : F) (S : H.LeftTransversal) (q : G ⧸ H) :
    f • (S.2.leftQuotientEquiv q : G) = (f • S).2.leftQuotientEquiv (f • q) :=
  Quotient.inductionOn' q fun g => smul_toLeftFun f S g

@[to_additive]
/-
**Subgroup.smul_apply_eq_smul_apply_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
`。
形式化陈述：smul_apply_eq_smul_apply_inv_smul (f : F) (S : H.LeftTransversal) (q : G ⧸
 H) : ((f • S).2.leftQuotientEquiv q : G) = f • (S.2.leftQuotientEquiv (f⁻¹ • q)
 : G)
参数：f : F；S : H.LeftTransversal；q : G ⧸ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.smul_leftQuotientEquiv`：smul_leftQuotientEquiv (f : F) (S : H.L
eftTransversal) (q : G ⧸ H) : f • (S.2.leftQuotientEquiv q : G) = (f • S).2.left
QuotientEquiv (f • q)
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
theorem smul_apply_eq_smul_apply_inv_smul (f : F) (S : H.LeftTransversal) (q : G ⧸ H) :
    ((f • S).2.leftQuotientEquiv q : G) = f • (S.2.leftQuotientEquiv (f⁻¹ • q) : G) := by
  rw [smul_leftQuotientEquiv, smul_inv_smul]

end Action

@[to_additive]
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inhabited H.LeftTransversal :=
  ⟨⟨Set.range Quotient.out, isComplement_range_left Quotient.out_eq'⟩⟩

@[to_additive]
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inhabited H.RightTransversal :=
  ⟨⟨Set.range Quotient.out, isComplement_range_right Quotient.out_eq'⟩⟩
/-
**Subgroup.IsComplement'.isCompl** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComplemen
t'`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsComplement' K → 
IsCompl H K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `codisjoint_iff_le_sup`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_
1 : OrderTop α] {a b : α}, Codisjoint a b ↔ ⊤ ≤ a ⊔ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subgroup.mul_mem_sup`：mul_mem_sup {S T : Subgroup G} {x y : G} (hx : x i
n S) (hy : y in T) : x * y in S ⊔ T
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem IsComplement'.isCompl (h : IsComplement' H K) : IsCompl H K := by
  refine
    ⟨disjoint_iff_inf_le.mpr fun g ⟨p, q⟩ =>
        let x : H × K := ⟨⟨g, p⟩, 1⟩
        let y : H × K := ⟨1, g, q⟩
        Subtype.ext_iff.mp
          (Prod.ext_iff.mp (show x = y from h.1 ((mul_one g).trans (one_mul g).symm))).1,
      codisjoint_iff_le_sup.mpr fun g _ => ?_⟩
  obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g
  exact Subgroup.mul_mem_sup h.2 k.2
/-
**Subgroup.IsComplement'.sup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsComple
ment'`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsComplement' K → 
H ⊔ K = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `Subgroup.IsComplement'.isCompl`：∀ {G : Type u_1} [inst : Group G] {H K :
 Subgroup G}, H.IsComplement' K → IsCompl H K
-/
theorem IsComplement'.sup_eq_top (h : IsComplement' H K) : H ⊔ K = ⊤ :=
  h.isCompl.sup_eq_top
/-
**Subgroup.IsComplement'.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCompleme
nt'`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsComplement' K → 
Disjoint H K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Subgroup.IsComplement'.isCompl`：∀ {G : Type u_1} [inst : Group G] {H K :
 Subgroup G}, H.IsComplement' K → IsCompl H K
-/
theorem IsComplement'.disjoint (h : IsComplement' H K) : Disjoint H K :=
  h.isCompl.disjoint
/-
**Subgroup.IsComplement'.index_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCom
plement'`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsComplement' K → 
K.index = Nat.card ↥H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.IsComplement.card_left`：∀ {G : Type u_1} [inst : Group G] {H : 
Subgroup G} {S : Set G}, Subgroup.IsComplement S ↑H → Nat.card ↑S = H.index
-/
theorem IsComplement'.index_eq_card (h : IsComplement' H K) : K.index = Nat.card H :=
  h.card_left.symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- If `H` and `K` are complementary with `K` normal, then `G ⧸ K` is isomorphic to `H`. -/
@[simps!]
/-
**Subgroup.IsComplement'.QuotientMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.Is
Complement'`。
形式化陈述：{G : Type u_1} → [inst : Group G] → {H K : Subgroup G} → [inst_1 : K.Norma
l] → H.IsComplement' K → G ⧸ K ≃* ↥H
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `H` and `K` are complementary with `K` normal, then `G ⧸ K` is isomorphic to 
`H`.
-/
noncomputable def IsComplement'.QuotientMulEquiv [K.Normal] (h : H.IsComplement' K) :
    G ⧸ K ≃* H :=
  MulEquiv.symm
  { h.leftQuotientEquiv.symm with
    map_mul' := fun _ _ ↦ rfl }
/-
**Subgroup.IsComplement'.card_mul_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsCom
plement'`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsComplement' K → 
Nat.card ↥H * Nat.card ↥K = Nat.card G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsComplement.card_mul_card`：∀ {G : Type u_1} [inst : Group G] {
S T : Set G}, Subgroup.IsComplement S T → Nat.card ↑S * Nat.card ↑T = Nat.card G
-/
theorem IsComplement'.card_mul_card (h : IsComplement' H K) :
    Nat.card H * Nat.card K = Nat.card G :=
  IsComplement.card_mul_card h

@[deprecated (since := "2026-08-06")]
alias IsComplement.card_mul := IsComplement.card_mul_card

@[deprecated (since := "2026-08-06")]
alias IsComplement'.card_mul := IsComplement'.card_mul_card
/-
**Subgroup.isComplement'_of_disjoint_and_mul_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `
Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, Disjoint H K → ↑H * 
↑K = Set.univ → H.IsComplement' K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mul_injective_of_disjoint`：mul_injective_of_disjoint {H₁ H₂ : S
ubgroup G} (h : Disjoint H₁ H₂) : Function.Injective (fun g => g.1 * g.2 : H₁ × 
H₂ -> G)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
-/
theorem isComplement'_of_disjoint_and_mul_eq_univ (h1 : Disjoint H K)
    (h2 : ↑H * ↑K = (Set.univ : Set G)) : IsComplement' H K := by
  refine ⟨mul_injective_of_disjoint h1, fun g => ?_⟩
  obtain ⟨h, hh, k, hk, hg⟩ := Set.eq_univ_iff_forall.mp h2 g
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hg⟩
/-
**Subgroup.isComplement'_of_card_mul_and_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Sub
group`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G} [Finite G],   Nat.car
d ↥H * Nat.card ↥K = Nat.card G → Disjoint H K → H.IsComplement' K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.bijective_iff_injective_and_card`：∀ {α : Type u_1} {β : Type u_2} [F
inite β] (f : α → β),   Function.Bijective f ↔ Function.Injective f ∧ Nat.card α
 = Nat.card β
· 使用定理 `Subgroup.mul_injective_of_disjoint`：mul_injective_of_disjoint {H₁ H₂ : S
ubgroup G} (h : Disjoint H₁ H₂) : Function.Injective (fun g => g.1 * g.2 : H₁ × 
H₂ -> G)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
-/
theorem isComplement'_of_card_mul_and_disjoint [Finite G]
    (h1 : Nat.card H * Nat.card K = Nat.card G) (h2 : Disjoint H K) :
    IsComplement' H K :=
  (Nat.bijective_iff_injective_and_card _).mpr
    ⟨mul_injective_of_disjoint h2, (Nat.card_prod H K).trans h1⟩
/-
**Subgroup.isComplement'_iff_card_mul_and_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Su
bgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G} [Finite G],   H.IsCom
plement' K ↔ Nat.card ↥H * Nat.card ↥K = Nat.card G ∧ Disjoint H K
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsComplement'.card_mul_card`：∀ {G : Type u_1} [inst : Group G] 
{H K : Subgroup G}, H.IsComplement' K → Nat.card ↥H * Nat.card ↥K = Nat.card G
· 使用定理 `Subgroup.IsComplement'.disjoint`：∀ {G : Type u_1} [inst : Group G] {H K 
: Subgroup G}, H.IsComplement' K → Disjoint H K
· 使用定理 `Subgroup.isComplement'_of_card_mul_and_disjoint`：∀ {G : Type u_1} [inst 
: Group G] {H K : Subgroup G} [Finite G],   Nat.card ↥H * Nat.card ↥K = Nat.card
 G → Disjoint H K → H.IsComplement' K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isComplement'_iff_card_mul_and_disjoint [Finite G] :
    IsComplement' H K ↔ Nat.card H * Nat.card K = Nat.card G ∧ Disjoint H K :=
  ⟨fun h => ⟨h.card_mul_card, h.disjoint⟩, fun h => isComplement'_of_card_mul_and_disjoint h.1 h.2⟩
/-
**Subgroup.isComplement'_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G} [Finite G],   Nat.car
d ↥H * Nat.card ↥K = Nat.card G → (Nat.card ↥H).Coprime (Nat.card ↥K) → H.IsComp
lement' K
参数：Nat.card ↥H；Nat.card ↥K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isComplement'_of_card_mul_and_disjoint`：∀ {G : Type u_1} [inst 
: Group G] {H K : Subgroup G} [Finite G],   Nat.card ↥H * Nat.card ↥K = Nat.card
 G → Disjoint H K → H.IsComplement' K
· 使用引理 `Subgroup.disjoint_of_coprime_natCard`：disjoint_of_coprime_natCard (h : N
at.card H |>.Coprime <| Nat.card K) : Disjoint H K
-/
theorem isComplement'_of_coprime [Finite G]
    (h1 : Nat.card H * Nat.card K = Nat.card G)
    (h2 : Nat.Coprime (Nat.card H) (Nat.card K)) : IsComplement' H K :=
  isComplement'_of_card_mul_and_disjoint h1 <| disjoint_of_coprime_natCard h2
/-
**Subgroup.isComplement'_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G} {α : Type u_2} [inst_1 
: MulAction G α] (a : α),   (∀ (h : ↥H), h • a = a → h = 1) → (∀ (g : G), ∃ h, h
 • g • a = a) → H.IsComplement' (MulAction.stabilizer G a)
参数：a : α；∀ (h : ↥H), h • a = a → h = 1；∀ (g : G), ∃ h, h • g • a = a；MulAction.s
tabilizer G a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.isComplement_iff_existsUnique`：isComplement_iff_existsUnique : 
IsComplement S T ↔ forall g : G, exists! x : S × T, x.1.1 * x.2.1 = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `eq_inv_of_mul_eq_one_right`：eq_inv_of_mul_eq_one_right (h : a * b = 1) :
 b = a⁻¹
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.smul_def`：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [ins
t_1 : MulAction G α] {S : Subgroup G} (g : ↥S) (m : α),   g • m = ↑g • m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `right_eq_mul`：right_eq_mul : b = a * b ↔ a = 1
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Subgroup.coe_mul`：coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y
· 使用定理 `Subgroup.coe_one`：coe_one : ((1 : H) : G) = 1
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem isComplement'_stabilizer {α : Type*} [MulAction G α] (a : α)
    (h1 : ∀ h : H, h • a = a → h = 1) (h2 : ∀ g : G, ∃ h : H, h • g • a = a) :
    IsComplement' H (MulAction.stabilizer G a) := by
  refine isComplement_iff_existsUnique.mpr fun g => ?_
  obtain ⟨h, hh⟩ := h2 g
  have hh' : (↑h * g) • a = a := by rwa [mul_smul]
  refine ⟨⟨h⁻¹, h * g, hh'⟩, inv_mul_cancel_left ↑h g, ?_⟩
  rintro ⟨h', g, hg : g • a = a⟩ rfl
  specialize h1 (h * h') (by rwa [mul_smul, smul_def h', ← hg, ← mul_smul, hg])
  refine Prod.ext (eq_inv_of_mul_eq_one_right h1) (Subtype.ext ?_)
  rwa [Subtype.ext_iff, coe_one, coe_mul, ← right_eq_mul, mul_assoc (↑h) (↑h') g] at h1

end Subgroup

