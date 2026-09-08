/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.Data.Set.Restrict

/-!
# Functions over sets

This file contains basic results on the following predicates of functions and sets:

* `Set.EqOn f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `Set.MapsTo f s t` : `f` sends every point of `s` to a point of `t`;
* `Set.InjOn f s` : restriction of `f` to `s` is injective;
* `Set.SurjOn f s t` : every point in `s` has a preimage in `s`;
* `Set.BijOn f s t` : `f` is a bijection between `s` and `t`;
* `Set.LeftInvOn f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `Set.RightInvOn f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `Set.InvOn f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `Set.LeftInvOn f' f s` and `Set.RightInvOn f' f t`.
-/

@[expose] public section

variable {α β γ δ : Type*} {ι : Sort*} {π : α → Type*}

open Equiv Equiv.Perm Function

namespace Set

/-! ### Equality on a set -/
section equality

variable {s s₁ s₂ : Set α} {f₁ f₂ f₃ : α → β} {g : β → γ} {a : α}

/-- This lemma exists for use by `grind`/`aesop` as a forward rule. -/
@[aesop safe forward, grind →]
/-
**Set.EqOn.eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β} {a : α}, Set.E
qOn f₁ f₂ s → a ∈ s → f₁ a = f₂ a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma exists for use by `grind`/`aesop` as a forward rule.
-/
lemma EqOn.eq_of_mem (h : s.EqOn f₁ f₂) (ha : a ∈ s) : f₁ a = f₂ a :=
  h ha

@[simp]
/-
**Set.eqOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_empty (f₁ f₂ : α -> β) : EqOn f₁ f₂ ∅
参数：f₁ f₂ : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqOn_empty (f₁ f₂ : α → β) : EqOn f₁ f₂ ∅ := fun _ => False.elim

@[simp]
/-
**Set.eqOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_singleton : Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eqOn_singleton : Set.EqOn f₁ f₂ {a} ↔ f₁ a = f₂ a := by
  simp [Set.EqOn]

@[simp]
/-
**Set.eqOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_univ (f₁ f₂ : α -> β) : EqOn f₁ f₂ univ ↔ f₁ = f₂
参数：f₁ f₂ : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eqOn_univ (f₁ f₂ : α → β) : EqOn f₁ f₂ univ ↔ f₁ = f₂ := by
  simp [EqOn, funext_iff]

@[symm]
/-
**Set.EqOn.symm** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β}, Set.EqOn f₁ f
₂ s → Set.EqOn f₂ f₁ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem EqOn.symm (h : EqOn f₁ f₂ s) : EqOn f₂ f₁ s := fun _ hx => (h hx).symm
/-
**Set.eqOn_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_comm : EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem eqOn_comm : EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s :=
  ⟨EqOn.symm, EqOn.symm⟩

-- This cannot be tagged as `@[refl]` with the current argument order.
-- See note below at `EqOn.trans`.
/-
**Set.eqOn_refl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_refl (f : α -> β) (s : Set α) : EqOn f f s
参数：f : α -> β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqOn_refl (f : α → β) (s : Set α) : EqOn f f s := fun _ _ => rfl

-- Note: this was formerly tagged with `@[trans]`, and although the `trans` attribute accepted it
-- the `trans` tactic could not use it.
-- An update to the trans tactic coming in https://github.com/leanprover-community/mathlib4/pull/7014 will reject this attribute.
-- It can be restored by changing the argument order from `EqOn f₁ f₂ s` to `EqOn s f₁ f₂`.
-- This change will be made separately: [zulip](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Reordering.20arguments.20of.20.60Set.2EEqOn.60/near/390467581).
/-
**Set.EqOn.trans** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : α → β}, Set.EqOn f
₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun _ hx =>
  (h₁ hx).trans (h₂ hx)
/-
**Set.EqOn.image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β}, Set.EqOn f₁ f
₂ s → f₁ '' s = f₂ '' s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EqOn.image_eq (heq : EqOn f₁ f₂ s) : f₁ '' s = f₂ '' s := by grind

/-- Variant of `EqOn.image_eq`, for one function being the identity. -/
/-
**Set.EqOn.image_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {f : α → α}, Set.EqOn f id s → f '' s = s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `EqOn.image_eq`, for one function being the identity.
-/
theorem EqOn.image_eq_self {f : α → α} (h : Set.EqOn f id s) : f '' s = s := by grind
/-
**Set.EqOn.inter_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β},   Set.EqOn f₁
 f₂ s → ∀ (t : Set β), s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t
参数：t : Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EqOn.inter_preimage_eq (heq : EqOn f₁ f₂ s) (t : Set β) : s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t := by
  grind
/-
**Set.EqOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : α → β}, s₁ ⊆ s₂ →
 Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EqOn.mono (hs : s₁ ⊆ s₂) (hf : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ s₁ := fun _ hx => hf (hs hx)

@[simp]
/-
**Set.eqOn_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_union : EqOn f₁ f₂ (s₁ union s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_or_left`：forall₂_or_left : (forall x, p x ∨ q x -> r x) ↔ (foral
l x, p x -> r x) ∧ forall x, q x -> r x
-/
theorem eqOn_union : EqOn f₁ f₂ (s₁ ∪ s₂) ↔ EqOn f₁ f₂ s₁ ∧ EqOn f₁ f₂ s₂ :=
  forall₂_or_left
/-
**Set.EqOn.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : α → β},   Set.EqO
n f₁ f₂ s₁ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ (s₁ ∪ s₂)
参数：s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eqOn_union`：eqOn_union : EqOn f₁ f₂ (s₁ union s₂) ↔ EqOn f₁ f₂ s₁ ∧ 
EqOn f₁ f₂ s₂
-/
theorem EqOn.union (h₁ : EqOn f₁ f₂ s₁) (h₂ : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ (s₁ ∪ s₂) :=
  eqOn_union.2 ⟨h₁, h₂⟩
/-
**Set.EqOn.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {f₁ f₂ : α → β}
 {g : β → γ},   Set.EqOn f₁ f₂ s → Set.EqOn (g ∘ f₁) (g ∘ f₂) s
参数：g ∘ f₁；g ∘ f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem EqOn.comp_left (h : s.EqOn f₁ f₂) : s.EqOn (g ∘ f₁) (g ∘ f₂) := fun _ ha =>
  congr_arg _ <| h ha
/-
**Set.EqOn.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {f₁ f₂ : α → β}
 {g : β → γ},   Set.EqOn f₁ f₂ s → Set.EqOn (g ∘ f₁) (g ∘ f₂) s
参数：g ∘ f₁；g ∘ f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem EqOn.comp_left₂ {α β δ γ} {op : α → β → δ} {a₁ a₂ : γ → α}
    {b₁ b₂ : γ → β} {s : Set γ} (ha : s.EqOn a₁ a₂) (hb : s.EqOn b₁ b₂) :
    s.EqOn (fun x ↦ op (a₁ x) (b₁ x)) (fun x ↦ op (a₂ x) (b₂ x)) :=
  fun _ hx ↦ congr_arg₂ _ (ha hx) (hb hx)

@[simp]
/-
**Set.eqOn_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_range {ι : Sort*} {f : ι -> α} {g₁ g₂ : α -> β} : EqOn g₁ g₂ (range f
) ↔ g₁ ∘ f = g₂ ∘ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem eqOn_range {ι : Sort*} {f : ι → α} {g₁ g₂ : α → β} :
    EqOn g₁ g₂ (range f) ↔ g₁ ∘ f = g₂ ∘ f :=
  forall_mem_range.trans <| funext_iff.symm

alias ⟨EqOn.comp_eq, _⟩ := eqOn_range

end equality

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ : α → β} {g g₁ g₂ : β → γ}
  {f' f₁' f₂' : β → α} {g' : γ → β} {a : α} {b : β}

section MapsTo

/-
**Set.mapsTo_iff_image_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iff_image_subset : MapsTo f s t ↔ f '' s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem mapsTo_iff_image_subset : MapsTo f s t ↔ f '' s ⊆ t :=
  image_subset_iff.symm
/-
**Set.MapsTo.subset_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.M
apsTo f s t → s ⊆ f ⁻¹' t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.subset_preimage (hf : MapsTo f s t) : s ⊆ f ⁻¹' t := hf
/-
**Set.mapsTo_iff_subset_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_iff_subset_preimage : MapsTo f s t ↔ s subseteq f ⁻¹' t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mapsTo_iff_subset_preimage : MapsTo f s t ↔ s ⊆ f ⁻¹' t := Iff.rfl
/-
**Set.mapsTo_prodMap_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_prodMap_diagonal : MapsTo (Prod.map f f) (diagonal α) (diagonal β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_iff_subset_preimage`：mapsTo_iff_subset_preimage : MapsTo f s 
t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.diagonal_subset_iff`：diagonal_subset_iff {s} : diagonal α subseteq s
 ↔ forall x, (x, x) in s
-/
theorem mapsTo_prodMap_diagonal : MapsTo (Prod.map f f) (diagonal α) (diagonal β) :=
  mapsTo_iff_subset_preimage.mpr <| diagonal_subset_iff.2 fun _ => rfl

@[simp]
/-
**Set.mapsTo_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_singleton {x : α} : MapsTo f {x} t ↔ f x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mapsTo_iff_subset_preimage`：mapsTo_iff_subset_preimage : MapsTo f s 
t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem mapsTo_singleton {x : α} : MapsTo f {x} t ↔ f x ∈ t :=
  mapsTo_iff_subset_preimage.trans singleton_subset_iff
/-
**Set.mapsTo_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_empty (f : α -> β) (t : Set β) : MapsTo f ∅ t
参数：f : α -> β；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapsTo_empty (f : α → β) (t : Set β) : MapsTo f ∅ t :=
  fun _ ↦ False.elim
/-
**Set.mapsTo_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.MapsTo f s ∅ 
↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem mapsTo_empty_iff : MapsTo f s ∅ ↔ s = ∅ := by
  simp [mapsTo_iff_image_subset, subset_empty_iff]

/-- If `f` maps `s` to `t` and `s` is non-empty, `t` is non-empty. -/
/-
**Set.MapsTo.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.M
apsTo f s t → s.Nonempty → t.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty

--- 原说明 ---
If `f` maps `s` to `t` and `s` is non-empty, `t` is non-empty.
-/
theorem MapsTo.nonempty (h : MapsTo f s t) (hs : s.Nonempty) : t.Nonempty :=
  (hs.image f).mono (mapsTo_iff_image_subset.mp h)
/-
**Set.MapsTo.image_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.M
apsTo f s t → f '' s ⊆ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
-/
theorem MapsTo.image_subset (h : MapsTo f s t) : f '' s ⊆ t :=
  mapsTo_iff_image_subset.1 h
/-
**Set.MapsTo.congr** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f₁ f₂ : α → β},  
 Set.MapsTo f₁ s t → Set.EqOn f₁ f₂ s → Set.MapsTo f₂ s t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.congr (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s) : MapsTo f₂ s t := fun _ hx =>
  h hx ▸ h₁ hx
/-
**Set.EqOn.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {f 
: α → β} {g₁ g₂ : β → γ},   Set.EqOn g₁ g₂ t → Set.MapsTo f s t → Set.EqOn (g₁ ∘
 f) (g₂ ∘ f) s
参数：g₁ ∘ f；g₂ ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EqOn.comp_right (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t) : s.EqOn (g₁ ∘ f) (g₂ ∘ f) :=
  fun _ ha => hg <| hf ha
/-
**Set.EqOn.mapsTo_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f₁ f₂ : α → β},  
 Set.EqOn f₁ f₂ s → (Set.MapsTo f₁ s t ↔ Set.MapsTo f₂ s t)
参数：Set.MapsTo f₁ s t ↔ Set.MapsTo f₂ s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f₁ f₂ : α → β},   Set.MapsTo f₁ s t → Set.EqOn f₁ f₂ s → Set.MapsTo f₂ s t
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem EqOn.mapsTo_iff (H : EqOn f₁ f₂ s) : MapsTo f₁ s t ↔ MapsTo f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
/-
**Set.MapsTo.comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {p 
: Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.MapsTo f s t → Set.Ma
psTo (g ∘ f) s p
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.comp (h₁ : MapsTo g t p) (h₂ : MapsTo f s t) : MapsTo (g ∘ f) s p := fun _ h =>
  h₁ (h₂ h)
/-
**Set.mapsTo_id** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_id (s : Set α) : MapsTo id s s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapsTo_id (s : Set α) : MapsTo id s s := fun _ => id
/-
**Set.MapsTo.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.MapsTo f s s → ∀ (n : ℕ), Se
t.MapsTo f^[n] s s
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.iterate {f : α → α} {s : Set α} (h : MapsTo f s s) : ∀ n, MapsTo f^[n] s s
  | 0 => fun _ => id
  | n + 1 => (MapsTo.iterate h n).comp h
/-
**Set.MapsTo.iterate_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {s : Set α} (h : Set.MapsTo f s s) (n : ℕ),  
 (Set.MapsTo.restrict f s s h)^[n] = Set.MapsTo.restrict f^[n] s s ⋯
参数：h : Set.MapsTo f s s；n : ℕ；Set.MapsTo.restrict f s s h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.MapsTo.iterate`：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.MapsTo
 f s s → ∀ (n : ℕ), Set.MapsTo f^[n] s s
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Set.MapsTo.coe_iterate_restrict`：∀ {α : Type u_1} {s : Set α} {f : α → α
} (h : Set.MapsTo f s s) (x : ↑s) (k : ℕ),   ↑((Set.MapsTo.restrict f s s h)^[k]
 x) = f^[k] ↑x
-/
theorem MapsTo.iterate_restrict {f : α → α} {s : Set α} (h : MapsTo f s s) (n : ℕ) :
    (h.restrict f s s)^[n] = (h.iterate n).restrict _ _ _ := by
  ext
  simpa using coe_iterate_restrict _ _ _
/-
**Set.mapsTo_of_subsingleton'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mapsTo_of_subsingleton' [Subsingleton β] (f : α -> β) (h : s.Nonempty -> t
.Nonempty) : MapsTo f s t
参数：f : α -> β；h : s.Nonempty -> t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsingleton.mem_iff_nonempty`：mem_iff_nonempty {α : Type*} [Subsingleto
n α] {s : Set α} {x : α} : x in s ↔ s.Nonempty
-/
lemma mapsTo_of_subsingleton' [Subsingleton β] (f : α → β) (h : s.Nonempty → t.Nonempty) :
    MapsTo f s t :=
  fun a ha ↦ Subsingleton.mem_iff_nonempty.2 <| h ⟨a, ha⟩
/-
**Set.mapsTo_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mapsTo_of_subsingleton [Subsingleton α] (f : α -> α) (s : Set α) : MapsTo 
f s s
参数：f : α -> α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mapsTo_of_subsingleton'`：mapsTo_of_subsingleton' [Subsingleton β] (f
 : α -> β) (h : s.Nonempty -> t.Nonempty) : MapsTo f s t
-/
lemma mapsTo_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : MapsTo f s s :=
  mapsTo_of_subsingleton' _ id

@[gcongr]
/-
**Set.MapsTo.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂ t₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.mono (hf : MapsTo f s₁ t₁) (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) : MapsTo f s₂ t₂ :=
  fun _ hx => ht (hf <| hs hx)
/-
**Set.MapsTo.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t : Set β} {f : α → β}, S
et.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.mono_left (hf : MapsTo f s₁ t) (hs : s₂ ⊆ s₁) : MapsTo f s₂ t := fun _ hx =>
  hf (hs hx)
/-
**Set.MapsTo.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t₂ : Set β} {f : α → β}, S
et.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.mono_right (hf : MapsTo f s t₁) (ht : t₁ ⊆ t₂) : MapsTo f s t₂ := fun _ hx =>
  ht (hf hx)
/-
**Set.MapsTo.union_union** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   Set.MapsTo f s₁ t₁ → Set.MapsTo f s₂ t₂ → Set.MapsTo f (s₁ ∪ s₂) (t₁ ∪ t₂)
参数：s₁ ∪ s₂；t₁ ∪ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem MapsTo.union_union (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∪ s₂) (t₁ ∪ t₂) := fun _ hx =>
  hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr <| h₂ hx
/-
**Set.MapsTo.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t : Set β} {f : α → β},  
 Set.MapsTo f s₁ t → Set.MapsTo f s₂ t → Set.MapsTo f (s₁ ∪ s₂) t
参数：s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.union_union`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → Set.MapsTo f s₂ t₂ → Set.Map
sTo f (s₁ ∪ …
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
-/
theorem MapsTo.union (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t) : MapsTo f (s₁ ∪ s₂) t :=
  union_self t ▸ h₁.union_union h₂

@[simp]
/-
**Set.mapsTo_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_union : MapsTo f (s₁ union s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.MapsTo.union`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t : S
et β} {f : α → β},   Set.MapsTo f s₁ t → Set.MapsTo f s₂ t → Set.MapsTo f (s₁ ∪ 
s₂) t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mapsTo_union : MapsTo f (s₁ ∪ s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t :=
  ⟨fun h =>
    ⟨h.mono subset_union_left (Subset.refl t),
      h.mono subset_union_right (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩
/-
**Set.MapsTo.inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t₂ : Set β} {f : α → β},  
 Set.MapsTo f s t₁ → Set.MapsTo f s t₂ → Set.MapsTo f s (t₁ ∩ t₂)
参数：t₁ ∩ t₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MapsTo.inter (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂) : MapsTo f s (t₁ ∩ t₂) := fun _ hx =>
  ⟨h₁ hx, h₂ hx⟩
/-
**Set.MapsTo.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β},   Set
.MapsTo f s t → ∀ (x : α), Set.MapsTo f (insert x s) (insert (f x) t)
参数：x : α；insert x s；insert (f x) t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.MapsTo.mono_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t
₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
lemma MapsTo.insert (h : MapsTo f s t) (x : α) : MapsTo f (insert x s) (insert (f x) t) := by
  simpa [← singleton_union] using h.mono_right subset_union_right
/-
**Set.MapsTo.inter_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   Set.MapsTo f s₁ t₁ → Set.MapsTo f s₂ t₂ → Set.MapsTo f (s₁ ∩ s₂) (t₁ ∩ t₂)
参数：s₁ ∩ s₂；t₁ ∩ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MapsTo.inter_inter (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) :
    MapsTo f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun _ hx => ⟨h₁ hx.1, h₂ hx.2⟩

@[simp]
/-
**Set.mapsTo_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_inter : MapsTo f s (t₁ inter t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.MapsTo.inter`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t₂ : S
et β} {f : α → β},   Set.MapsTo f s t₁ → Set.MapsTo f s t₂ → Set.MapsTo f s (t₁ 
∩ t₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mapsTo_inter : MapsTo f s (t₁ ∩ t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂ :=
  ⟨fun h =>
    ⟨h.mono (Subset.refl s) inter_subset_left,
      h.mono (Subset.refl s) inter_subset_right⟩,
    fun h => h.1.inter h.2⟩
/-
**Set.mapsTo_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α), Set.MapsTo f s Se
t.univ
参数：f : α → β；s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
@[simp] theorem mapsTo_univ (f : α → β) (s : Set α) : MapsTo f s univ := fun _ _ => trivial
/-
**Set.mapsTo_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_range (f : α -> β) (s : Set α) : MapsTo f s (range f)
参数：f : α -> β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem mapsTo_range (f : α → β) (s : Set α) : MapsTo f s (range f) :=
  (mapsTo_image f s).mono (Subset.refl s) (image_subset_range _ _)

@[simp]
/-
**Set.mapsTo_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mapsTo_image_iff {f : α -> β} {g : γ -> α} {s : Set γ} {t : Set β} : MapsT
o f (g '' s) t ↔ MapsTo (f ∘ g) s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mapsTo_image_iff {f : α → β} {g : γ → α} {s : Set γ} {t : Set β} :
    MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t :=
  ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h _ ⟨_, hc⟩ => hc.2 ▸ h hc.1⟩
/-
**Set.MapsTo.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {f 
: α → β} (g : β → γ),   Set.MapsTo f s t → Set.MapsTo (g ∘ f) s (g '' t)
参数：g : β → γ；g ∘ f；g '' t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MapsTo.comp_left (g : β → γ) (hf : MapsTo f s t) : MapsTo (g ∘ f) s (g '' t) :=
  fun x hx ↦ ⟨f x, hf hx, rfl⟩
/-
**Set.MapsTo.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {g : β → γ} {s : Set β} {t 
: Set γ},   Set.MapsTo g s t → ∀ (f : α → β), Set.MapsTo (g ∘ f) (f ⁻¹' s) t
参数：f : α → β；g ∘ f；f ⁻¹' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MapsTo.comp_right {s : Set β} {t : Set γ} (hg : MapsTo g s t) (f : α → β) :
    MapsTo (g ∘ f) (f ⁻¹' s) t := fun _ hx ↦ hg hx

@[simp]
/-
**Set.mapsTo_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mapsTo_univ_iff : MapsTo f univ t ↔ forall x, f x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
lemma mapsTo_univ_iff : MapsTo f univ t ↔ ∀ x, f x ∈ t :=
  ⟨fun h _ => h (mem_univ _), fun h x _ => h x⟩
/-
**Set.mapsTo_univ_iff_range_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mapsTo_univ_iff_range_subset : MapsTo f univ t ↔ range f subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Set.mapsTo_univ_iff`：mapsTo_univ_iff : MapsTo f univ t ↔ forall x, f x i
n t
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
-/
lemma mapsTo_univ_iff_range_subset : MapsTo f univ t ↔ range f ⊆ t :=
  mapsTo_univ_iff.trans range_subset_iff.symm

@[simp]
/-
**Set.mapsTo_range_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mapsTo_range_iff {g : ι -> α} : MapsTo f (range g) t ↔ forall i, f (g i) i
n t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
lemma mapsTo_range_iff {g : ι → α} : MapsTo f (range g) t ↔ ∀ i, f (g i) ∈ t :=
  forall_mem_range
/-
**Set.MapsTo.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β},   Set
.MapsTo f s t → Set.MapsTo f sᶜ tᶜ → ∀ {x : α}, f x ∈ t ↔ x ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
-/
theorem MapsTo.mem_iff (h : MapsTo f s t) (hc : MapsTo f sᶜ tᶜ) {x} : f x ∈ t ↔ x ∈ s :=
  ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩

end MapsTo

/-! ### Injectivity on a set -/
section injOn

/-
**Set.Subsingleton.injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.Subsingleton → ∀ (f : α → β
), Set.InjOn f s
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subsingleton.injOn (hs : s.Subsingleton) (f : α → β) : InjOn f s := fun _ hx _ hy _ =>
  hs hx hy

@[simp]
/-
**Set.injOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_empty (f : α -> β) : InjOn f ∅
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), Set.InjOn f s
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
-/
theorem injOn_empty (f : α → β) : InjOn f ∅ :=
  subsingleton_empty.injOn f
@[simp]
/-
**Set.injOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_singleton (f : α -> β) (a : α) : InjOn f {a}
参数：f : α -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), Set.InjOn f s
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem injOn_singleton (f : α → β) (a : α) : InjOn f {a} :=
  subsingleton_singleton.injOn f
/-
**Set.injOn_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a b : α}, Set.InjOn f {a, b} 
↔ f a = f b → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma injOn_pair {b : α} : InjOn f {a, b} ↔ f a = f b → a = b := by unfold InjOn; aesop
/-
**Set.injOn_of_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} (s : Set α), (∀ (x y : α), f x
 = f y ↔ x = y) → Set.InjOn f s
参数：s : Set α；∀ (x y : α), f x = f y ↔ x = y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
@[simp low] lemma injOn_of_eq_iff_eq (s : Set α) (h : ∀ x y, f x = f y ↔ x = y) : Set.InjOn f s :=
  fun x _ y _ => (h x y).mp
/-
**Set.InjOn.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x y : α}, Set.Inj
On f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
参数：f x = f y ↔ x = y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem InjOn.eq_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x = f y ↔ x = y :=
  ⟨h hx hy, fun h => h ▸ rfl⟩
/-
**Set.InjOn.ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x y : α}, Set.Inj
On f s → x ∈ s → y ∈ s → (f x ≠ f y ↔ x ≠ y)
参数：f x ≠ f y ↔ x ≠ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
-/
theorem InjOn.ne_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x ≠ f y ↔ x ≠ y :=
  (h.eq_iff hx hy).not

alias ⟨_, InjOn.ne⟩ := InjOn.ne_iff
/-
**Set.InjOn.congr** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β}, Set.InjOn f₁ 
s → Set.EqOn f₁ f₂ s → Set.InjOn f₂ s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem InjOn.congr (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s) : InjOn f₂ s := fun _ hx _ hy =>
  h hx ▸ h hy ▸ h₁ hx hy
/-
**Set.EqOn.injOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β}, Set.EqOn f₁ f
₂ s → (Set.InjOn f₁ s ↔ Set.InjOn f₂ s)
参数：Set.InjOn f₁ s ↔ Set.InjOn f₂ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α 
→ β}, Set.InjOn f₁ s → Set.EqOn f₁ f₂ s → Set.InjOn f₂ s
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem EqOn.injOn_iff (H : EqOn f₁ f₂ s) : InjOn f₁ s ↔ InjOn f₂ s :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

@[gcongr]
/-
**Set.InjOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α → β}, s₁ ⊆ s₂ → Set
.InjOn f s₂ → Set.InjOn f s₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem InjOn.mono (h : s₁ ⊆ s₂) (ht : InjOn f s₂) : InjOn f s₁ := fun _ hx _ hy H =>
  ht (h hx) (h hy) H
/-
**Set.injOn_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_union (h : Disjoint s₁ s₂) : InjOn f (s₁ union s₂) ↔ InjOn f s₁ ∧ In
jOn f s₂ ∧ forall x in s₁, forall y in s₂, f x != f y
参数：h : Disjoint s₁ s₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem injOn_union (h : Disjoint s₁ s₂) :
    InjOn f (s₁ ∪ s₂) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ ∀ x ∈ s₁, ∀ y ∈ s₂, f x ≠ f y := by
  refine ⟨fun H => ⟨H.mono subset_union_left, H.mono subset_union_right, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain rfl : x = y := H (Or.inl hx) (Or.inr hy) hxy
    exact h.le_bot ⟨hx, hy⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts [h₁ hx hy hxy, (h₁₂ _ hx _ hy hxy).elim, (h₁₂ _ hy _ hx hxy.symm).elim, h₂ hx hy hxy]
/-
**Set.injOn_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_insert {f : α -> β} {s : Set α} {a : α} (has : a ∉ s) : Set.InjOn f 
(insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s
参数：has : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.injOn_union`：injOn_union (h : Disjoint s₁ s₂) : InjOn f (s₁ union s₂
) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ forall x in s₁, forall y in s₂, f x != f y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem injOn_insert {f : α → β} {s : Set α} {a : α} (has : a ∉ s) :
    Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s := by
  rw [← union_singleton, injOn_union (disjoint_singleton_right.2 has)]
  simp
/-
**Set.injOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.InjOn f Set.univ ↔ Functi
on.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma injOn_univ : InjOn f univ ↔ Injective f := by simp [InjOn, Injective]
/-
**Set.injOn_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_of_injective (h : Injective f) {s : Set α} : InjOn f s
参数：h : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem injOn_of_injective (h : Injective f) {s : Set α} : InjOn f s := fun _ _ _ _ hxy => h hxy

alias _root_.Function.Injective.injOn := injOn_of_injective

-- A specialization of `injOn_of_injective` for `Subtype.val`.
/-
**Set.injOn_subtype_val** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_subtype_val {p : α -> Prop} {s : Set {x // p x}} : Set.InjOn Subtype
.val s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem injOn_subtype_val {p : α → Prop} {s : Set {x // p x}} : Set.InjOn Subtype.val s :=
  Subtype.coe_injective.injOn
/-
**Set.injOn_id** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：injOn_id (s : Set α) : InjOn id s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
lemma injOn_id (s : Set α) : InjOn id s := injective_id.injOn
/-
**Set.InjOn.comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {f 
: α → β} {g : β → γ},   Set.InjOn g t → Set.InjOn f s → Set.MapsTo f s t → Set.I
njOn (g ∘ f) s
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem InjOn.comp (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s :=
  fun _ hx _ hy heq => hf hx hy <| hg (h hx) (h hy) heq
/-
**Set.InjOn.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {f : α → β} {g 
: β → γ}, Set.InjOn (g ∘ f) s → Set.InjOn f s
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma InjOn.of_comp (h : InjOn (g ∘ f) s) : InjOn f s :=
  fun _ hx _ hy heq ↦ h hx hy (by simp [heq])
/-
**Set.InjOn.image_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {f : α → β} {g 
: β → γ},   Set.InjOn (g ∘ f) s → Set.InjOn g (f '' s)
参数：g ∘ f；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma InjOn.image_of_comp (h : InjOn (g ∘ f) s) : InjOn g (f '' s) :=
  forall_mem_image.2 fun _x hx ↦ forall_mem_image.2 fun _y hy heq ↦ congr_arg f <| h hx hy heq
/-
**Set.InjOn.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {f : α → β} {g 
: β → γ},   Set.InjOn f s → (Set.InjOn (g ∘ f) s ↔ Set.InjOn g (f '' s))
参数：Set.InjOn (g ∘ f) s ↔ Set.InjOn g (f '' s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.image_of_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{s : Set α} {f : α → β} {g : β → γ},   Set.InjOn (g ∘ f) s → Set.InjOn g (f '' s
)
· 使用定理 `Set.InjOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {f : α → β} {g : β → γ},   Set.InjOn g t → Set.InjOn f s → Set.Ma
psTo…
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
lemma InjOn.comp_iff (hf : InjOn f s) : InjOn (g ∘ f) s ↔ InjOn g (f '' s) :=
  ⟨image_of_comp, fun h ↦ InjOn.comp h hf <| mapsTo_image f s⟩
/-
**Set.InjOn.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.InjOn f s → Set.MapsTo f s s
 → ∀ (n : ℕ), Set.InjOn f^[n] s
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma InjOn.iterate {f : α → α} {s : Set α} (h : InjOn f s) (hf : MapsTo f s s) :
    ∀ n, InjOn f^[n] s
  | 0 => injOn_id _
  | (n + 1) => (h.iterate hf n).comp h hf
/-
**Set.injOn_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：injOn_of_subsingleton [Subsingleton α] (f : α -> β) (s : Set α) : InjOn f 
s
参数：f : α -> β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
-/
lemma injOn_of_subsingleton [Subsingleton α] (f : α → β) (s : Set α) : InjOn f s :=
  (injective_of_subsingleton _).injOn
/-
**Set._root_.Function.Injective.injOn_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.injOn_range (h : Injective (g ∘ f)) : InjOn g (range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ H
  exact congr_arg f (h H)
/-
**Set._root_.Set.InjOn.injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.InjOn.injective_iff (s : Set β) (h : InjOn g s) (hs : range f ⊆ s) :
    Injective (g ∘ f) ↔ Injective f :=
  ⟨(·.of_comp), fun h _ ↦ by aesop⟩
/-
**Set.exists_injOn_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_injOn_iff_injective [Nonempty β] : (exists f : α -> β, InjOn f s) ↔
 exists f : s -> β, Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.injective`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α 
→ β}, Set.InjOn f s → Function.Injective (s.domRestrict f)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.PiSetCoe.canLift'`：∀ (ι : Type u) (α : Type v) [Nonempty α] (s : Set
 ι), CanLift (↑s → α) (ι → α) (fun f i => f ↑i) fun x => True
· 使用定理 `trivial`：True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
-/
theorem exists_injOn_iff_injective [Nonempty β] :
    (∃ f : α → β, InjOn f s) ↔ ∃ f : s → β, Injective f :=
  ⟨fun ⟨_, hf⟩ => ⟨_, hf.injective⟩,
   fun ⟨f, hf⟩ => by
    lift f to α → β using trivial
    exact ⟨f, injOn_iff_injective.2 hf⟩⟩
/-
**Set.injOn_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_preimage {B : Set (Set β)} (hB : B subseteq 𝒫 range f) : InjOn (prei
mage f) B
参数：Set β；hB : B subseteq 𝒫 range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.preimage_eq_preimage'`：preimage_eq_preimage' {s t : Set α} {f : β ->
 α} (hs : s subseteq range f) (ht : t subseteq range f) : f ⁻¹' s = f ⁻¹' t ↔ s 
= t
-/
theorem injOn_preimage {B : Set (Set β)} (hB : B ⊆ 𝒫 range f) : InjOn (preimage f) B :=
  fun _ hs _ ht hst => (preimage_eq_preimage' (hB hs) (hB ht)).1 hst
/-
**Set.InjOn.mem_of_mem_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set α} {f : α → β} {x : α},   Set.
InjOn f s → s₁ ⊆ s → x ∈ s → f x ∈ f '' s₁ → x ∈ s₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem InjOn.mem_of_mem_image {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (h : x ∈ s) (h₁ : f x ∈ f '' s₁) :
    x ∈ s₁ :=
  let ⟨_, h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'
/-
**Set.InjOn.mem_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set α} {f : α → β} {x : α},   Set.
InjOn f s → s₁ ⊆ s → x ∈ s → (f x ∈ f '' s₁ ↔ x ∈ s₁)
参数：f x ∈ f '' s₁ ↔ x ∈ s₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.mem_of_mem_image`：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set 
α} {f : α → β} {x : α},   Set.InjOn f s → s₁ ⊆ s → x ∈ s → f x ∈ f '' s₁ → x ∈ s
₁
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem InjOn.mem_image_iff {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (hx : x ∈ s) :
    f x ∈ f '' s₁ ↔ x ∈ s₁ :=
  ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩
/-
**Set.InjOn.preimage_image_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set α} {f : α → β}, Set.InjOn f s 
→ s₁ ⊆ s → f ⁻¹' f '' s₁ ∩ s = s₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.InjOn.mem_of_mem_image`：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set 
α} {f : α → β} {x : α},   Set.InjOn f s → s₁ ⊆ s → x ∈ s → f x ∈ f '' s₁ → x ∈ s
₁
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem InjOn.preimage_image_inter (hf : InjOn f s) (hs : s₁ ⊆ s) : f ⁻¹' f '' s₁ ∩ s = s₁ :=
  ext fun _ => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩
/-
**Set.EqOn.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {f₁
 f₂ : α → β} {g : β → γ},   Set.EqOn (g ∘ f₁) (g ∘ f₂) s → Set.InjOn g t → Set.M
apsTo f₁ s t → Set.MapsTo f₂ s t → Set.EqOn f₁ f₂ s
参数：g ∘ f₁；g ∘ f₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EqOn.cancel_left (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t)
    (hf₂ : s.MapsTo f₂ t) : s.EqOn f₁ f₂ := fun _ ha => hg (hf₁ ha) (hf₂ ha) (h ha)
/-
**Set.InjOn.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {f₁
 f₂ : α → β} {g : β → γ},   Set.InjOn g t → Set.MapsTo f₁ s t → Set.MapsTo f₂ s 
t → (Set.EqOn (g ∘ f₁) (g ∘ f₂) s ↔ Set.EqOn f₁ f₂ s)
参数：Set.EqOn (g ∘ f₁) (g ∘ f₂) s ↔ Set.EqOn f₁ f₂ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.cancel_left`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s 
: Set α} {t : Set β} {f₁ f₂ : α → β} {g : β → γ},   Set.EqOn (g ∘ f₁) (g ∘ f₂) s
 → Set.Inj…
· 使用定理 `Set.EqOn.comp_left`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : 
Set α} {f₁ f₂ : α → β} {g : β → γ},   Set.EqOn f₁ f₂ s → Set.EqOn (g ∘ f₁) (g ∘ 
f₂) s
-/
theorem InjOn.cancel_left (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t) :
    s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂ :=
  ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩
/-
**Set.InjOn.image_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s t u : Set α},   Set.InjOn f
 u → s ⊆ u → t ⊆ u → f '' (s ∩ t) = f '' s ∩ f '' t
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.image_inter_subset`：image_inter_subset (f : α -> β) (s t : Set α) : 
f '' (s inter t) subseteq f '' s inter f '' t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma InjOn.image_inter {s t u : Set α} (hf : u.InjOn f) (hs : s ⊆ u) (ht : t ⊆ u) :
    f '' (s ∩ t) = f '' s ∩ f '' t := by
  apply Subset.antisymm (image_inter_subset _ _ _)
  intro x ⟨⟨y, ys, hy⟩, ⟨z, zt, hz⟩⟩
  have : y = z := by
    apply hf (hs ys) (ht zt)
    rwa [← hz] at hy
  rw [← this] at zt
  exact ⟨y, ⟨ys, zt⟩, hy⟩
/-
**Set.InjOn.image** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.InjOn f s → S
et.InjOn (Set.image f) (𝒫 s)
参数：Set.image f；𝒫 s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.preimage_image_inter`：∀ {α : Type u_1} {β : Type u_2} {s s₁ : 
Set α} {f : α → β}, Set.InjOn f s → s₁ ⊆ s → f ⁻¹' f '' s₁ ∩ s = s₁
-/
lemma InjOn.image (h : s.InjOn f) : s.powerset.InjOn (image f) :=
  fun s₁ hs₁ s₂ hs₂ h' ↦ by rw [← h.preimage_image_inter hs₁, h', h.preimage_image_inter hs₂]
/-
**Set.InjOn.image_eq_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ : Set α} {f : α → β},   Set.InjOn
 f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁ = s₂)
参数：f '' s₁ = f '' s₂ ↔ s₁ = s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Set.InjOn.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}
, Set.InjOn f s → Set.InjOn (Set.image f) (𝒫 s)
-/
theorem InjOn.image_eq_image_iff (h : s.InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    f '' s₁ = f '' s₂ ↔ s₁ = s₂ :=
  h.image.eq_iff h₁ h₂
/-
**Set.InjOn.image_subset_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ : Set α} {f : α → β},   Set.InjOn
 f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂)
参数：f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.preimage_image_inter`：∀ {α : Type u_1} {β : Type u_2} {s s₁ : 
Set α} {f : α → β}, Set.InjOn f s → s₁ ⊆ s → f ⁻¹' f '' s₁ ∩ s = s₁
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma InjOn.image_subset_image_iff (h : s.InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂ := by
  refine ⟨fun h' ↦ ?_, image_mono⟩
  rw [← h.preimage_image_inter h₁, ← h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')
/-
**Set.InjOn.image_ssubset_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ : Set α} {f : α → β},   Set.InjOn
 f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ ⊂ f '' s₂ ↔ s₁ ⊂ s₂)
参数：f '' s₁ ⊂ f '' s₂ ↔ s₁ ⊂ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.InjOn.image_subset_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ 
s₂ : Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ ⊆ f '' s₂ 
↔ s₁ ⊆ s₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma InjOn.image_ssubset_image_iff (h : s.InjOn f) (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) :
    f '' s₁ ⊂ f '' s₂ ↔ s₁ ⊂ s₂ := by
  simp_rw [ssubset_def, h.image_subset_image_iff h₁ h₂, h.image_subset_image_iff h₂ h₁]

-- TODO: can this move to a better place?
/-
**Set._root_.Disjoint.image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.image {s t u : Set α} {f : α → β} (h : Disjoint s t) (hf : u.InjOn f)
    (hs : s ⊆ u) (ht : t ⊆ u) : Disjoint (f '' s) (f '' t) := by
  rw [disjoint_iff_inter_eq_empty] at h ⊢
  rw [← hf.image_inter hs ht, h, image_empty]
/-
**Set.InjOn.image_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {t : Set α},   Set
.InjOn f s → f '' (s \ t) = f '' s \ f '' (s ∩ t)
参数：s \ t；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Disjoint.image`：∀ {α : Type u_1} {β : Type u_2} {s t u : Set α} {f : α →
 β},   Disjoint s t → Set.InjOn f u → s ⊆ u → t ⊆ u → Disjoint (f '' s) (f '' t)
· 使用引理 `Set.disjoint_sdiff_inter`：disjoint_sdiff_inter : Disjoint (s \ t) (s int
er t)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.sdiff_subset_iff`：sdiff_subset_iff {s t u : Set α} : s \ t subseteq 
u ↔ s subseteq t union u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Set.inter_union_sdiff`：inter_union_sdiff (s t : Set α) : s inter t union
 s \ t = s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma InjOn.image_sdiff {t : Set α} (h : s.InjOn f) : f '' (s \ t) = f '' s \ f '' (s ∩ t) := by
  refine subset_antisymm (subset_sdiff.2 ⟨image_mono sdiff_subset, ?_⟩)
    (sdiff_subset_iff.2 (by rw [← image_union, inter_union_sdiff]))
  exact Disjoint.image disjoint_sdiff_inter h sdiff_subset inter_subset_left

@[deprecated (since := "2026-06-03")] alias InjOn.image_diff := InjOn.image_sdiff
/-
**Set.InjOn.image_sdiff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {t : Set α},   Set
.InjOn f s → t ⊆ s → f '' (s \ t) = f '' s \ f '' t
参数：s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.InjOn.image_sdiff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β} {t : Set α},   Set.InjOn f s → f '' (s \ t) = f '' s \ f '' (s ∩ t)
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
-/
lemma InjOn.image_sdiff_subset {f : α → β} {t : Set α} (h : InjOn f s) (hst : t ⊆ s) :
    f '' (s \ t) = f '' s \ f '' t := by
  rw [h.image_sdiff, inter_eq_self_of_subset_right hst]

@[deprecated (since := "2026-06-03")] alias InjOn.image_diff_subset := InjOn.image_sdiff_subset

alias image_sdiff_of_injOn := InjOn.image_sdiff_subset

@[deprecated (since := "2026-06-03")] alias image_diff_of_injOn := image_sdiff_of_injOn
/-
**Set.InjOn.imageFactorization_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.InjOn f s → F
unction.Injective (Set.imageFactorization f s)
参数：Set.imageFactorization f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
-/
theorem InjOn.imageFactorization_injective (h : InjOn f s) :
    Injective (s.imageFactorization f) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ h' ↦ by simpa [imageFactorization, h.eq_iff hx hy] using h'
/-
**Set.imageFactorization_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Function.Injectiv
e (Set.imageFactorization f s) ↔ Set.InjOn f s
参数：Set.imageFactorization f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Set.InjOn.imageFactorization_injective`：∀ {α : Type u_1} {β : Type u_2} 
{s : Set α} {f : α → β}, Set.InjOn f s → Function.Injective (Set.imageFactorizat
ion f s)
-/
@[simp] theorem imageFactorization_injective_iff : Injective (s.imageFactorization f) ↔ InjOn f s :=
  ⟨fun h x hx y hy _ ↦ by simpa using @h ⟨x, hx⟩ ⟨y, hy⟩ (by simpa [imageFactorization]),
    InjOn.imageFactorization_injective⟩

end injOn

section graphOn
variable {x : α × β}

/-
**Set.graphOn_univ_inj** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：graphOn_univ_inj {g : α -> β} : univ.graphOn f = univ.graphOn g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma graphOn_univ_inj {g : α → β} : univ.graphOn f = univ.graphOn g ↔ f = g := by simp
/-
**Set.graphOn_univ_injective** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：graphOn_univ_injective : Injective (univ.graphOn : (α -> β) -> Set (α × β)
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.graphOn_univ_inj`：graphOn_univ_inj {g : α -> β} : univ.graphOn f = u
niv.graphOn g ↔ f = g
-/
lemma graphOn_univ_injective : Injective (univ.graphOn : (α → β) → Set (α × β)) :=
  fun _f _g ↦ graphOn_univ_inj.1
/-
**Set.exists_eq_graphOn_image_fst** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_eq_graphOn_image_fst [Nonempty β] {s : Set (α × β)} : (exists f : α
 -> β, s = graphOn f (Prod.fst '' s)) ↔ InjOn Prod.fst s
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.InjOn.image_of_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{s : Set α} {f : α → β} {g : β → γ},   Set.InjOn (g ∘ f) s → Set.InjOn g (f '' s
)
· 使用引理 `Set.injOn_id`：injOn_id (s : Set α) : InjOn id s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Set.graphOn.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), S
et.graphOn f s = (fun x => (x, f x)) '' s
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.EqOn.image_eq_self`：∀ {α : Type u_1} {s : Set α} {f : α → α}, Set.Eq
On f id s → f '' s = s
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma exists_eq_graphOn_image_fst [Nonempty β] {s : Set (α × β)} :
    (∃ f : α → β, s = graphOn f (Prod.fst '' s)) ↔ InjOn Prod.fst s := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨f, hf⟩
    rw [hf]
    exact InjOn.image_of_comp <| injOn_id _
  · have : ∀ x ∈ Prod.fst '' s, ∃ y, (x, y) ∈ s := forall_mem_image.2 fun (x, y) h ↦ ⟨y, h⟩
    choose! f hf using this
    rw [forall_mem_image] at hf
    use f
    rw [graphOn, image_image, EqOn.image_eq_self]
    exact fun x hx ↦ h (hf hx) hx rfl
/-
**Set.exists_eq_graphOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_eq_graphOn [Nonempty β] {s : Set (α × β)} : (exists f t, s = graphO
n f t) ↔ InjOn Prod.fst s
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.image_fst_graphOn`：image_fst_graphOn (f : α -> β) (s : Set α) : Prod
.fst '' graphOn f s = s
· 使用引理 `Set.exists_eq_graphOn_image_fst`：exists_eq_graphOn_image_fst [Nonempty β
] {s : Set (α × β)} : (exists f : α -> β, s = graphOn f (Prod.fst '' s)) ↔ InjOn
 Prod.fst s
-/
lemma exists_eq_graphOn [Nonempty β] {s : Set (α × β)} :
    (∃ f t, s = graphOn f t) ↔ InjOn Prod.fst s :=
  .trans ⟨fun ⟨f, t, hs⟩ ↦ ⟨f, by rw [hs, image_fst_graphOn]⟩, fun ⟨f, hf⟩ ↦ ⟨f, _, hf⟩⟩
    exists_eq_graphOn_image_fst

end graphOn

/-! ### Surjectivity on a set -/
section surjOn

/-
**Set.SurjOn.subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.S
urjOn f s t → t ⊆ Set.range f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem SurjOn.subset_range (h : SurjOn f s t) : t ⊆ range f :=
  Subset.trans h <| image_subset_range f s
/-
**Set.surjOn_iff_exists_map_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_iff_exists_map_subtype : SurjOn f s t ↔ exists (t' : Set β) (g : s 
-> t'), t subseteq t' ∧ Surjective g ∧ forall x : s, f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Set.surjective_mapsTo_image_restrict`：surjective_mapsTo_image_restrict (
f : α -> β) (s : Set α) : Surjective ((mapsTo_image f s).restrict f s (f '' s))
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
-/
theorem surjOn_iff_exists_map_subtype :
    SurjOn f s t ↔ ∃ (t' : Set β) (g : s → t'), t ⊆ t' ∧ Surjective g ∧ ∀ x : s, f x = g x :=
  ⟨fun h =>
    ⟨_, (mapsTo_image f s).restrict f s _, h, surjective_mapsTo_image_restrict _ _, fun _ => rfl⟩,
    fun ⟨t', g, htt', hg, hfg⟩ y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by rw [hfg, hx, Subtype.coe_mk]⟩⟩
/-
**Set.surjOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_empty (f : α -> β) (s : Set α) : SurjOn f s ∅
参数：f : α -> β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem surjOn_empty (f : α → β) (s : Set α) : SurjOn f s ∅ :=
  empty_subset _
/-
**Set.surjOn_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {t : Set β} {f : α → β}, Set.SurjOn f ∅ t 
↔ t = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem surjOn_empty_iff : SurjOn f ∅ t ↔ t = ∅ := by
  simp [SurjOn, subset_empty_iff]
/-
**Set.surjOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {b : β}, Set.SurjO
n f s {b} ↔ b ∈ f '' s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
@[simp] lemma surjOn_singleton : SurjOn f s {b} ↔ b ∈ f '' s := singleton_subset_iff
/-
**Set.surjOn_univ_of_subsingleton_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} [Subsingleton β] [
Nonempty β],   Set.SurjOn f s Set.univ ↔ s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_unique`：nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty
 α] : Nonempty (Unique α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_unique`：univ_unique [Unique α] : @Set.univ α = {default}
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma surjOn_univ_of_subsingleton_nonempty [Subsingleton β] [Nonempty β] :
    SurjOn f s univ ↔ s.Nonempty := by
  cases nonempty_unique β; simp [univ_unique, Subsingleton.elim (f _) default, Set.Nonempty]
/-
**Set.surjOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f '' s)
参数：f : α -> β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem surjOn_image (f : α → β) (s : Set α) : SurjOn f s (f '' s) :=
  Subset.rfl
/-
**Set.SurjOn.comap_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.S
urjOn f s t → t.Nonempty → s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s : 
Set α}, (f '' s).Nonempty → s.Nonempty
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
-/
theorem SurjOn.comap_nonempty (h : SurjOn f s t) (ht : t.Nonempty) : s.Nonempty :=
  (ht.mono h).of_image
/-
**Set.SurjOn.nonempty_or_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.S
urjOn f s t → s.Nonempty ∨ t = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.SurjOn.comap_nonempty`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {
t : Set β} {f : α → β}, Set.SurjOn f s t → t.Nonempty → s.Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma SurjOn.nonempty_or_eq_empty (h : SurjOn f s t) :
    s.Nonempty ∨ t = ∅ := by
  by_contra!
  exact (h.comap_nonempty this.2).ne_empty this.1
/-
**Set.SurjOn.congr** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f₁ f₂ : α → β},  
 Set.SurjOn f₁ s t → Set.EqOn f₁ f₂ s → Set.SurjOn f₂ s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.SurjOn.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t 
: Set β), Set.SurjOn f s t = (t ⊆ f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
-/
theorem SurjOn.congr (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s) : SurjOn f₂ s t := by
  rwa [SurjOn, ← H.image_eq]
/-
**Set.EqOn.surjOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f₁ f₂ : α → β},  
 Set.EqOn f₁ f₂ s → (Set.SurjOn f₁ s t ↔ Set.SurjOn f₂ s t)
参数：Set.SurjOn f₁ s t ↔ Set.SurjOn f₂ s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f₁ f₂ : α → β},   Set.SurjOn f₁ s t → Set.EqOn f₁ f₂ s → Set.SurjOn f₂ s t
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem EqOn.surjOn_iff (h : EqOn f₁ f₂ s) : SurjOn f₁ s t ↔ SurjOn f₂ s t :=
  ⟨fun H => H.congr h, fun H => H.congr h.symm⟩

@[gcongr]
/-
**Set.SurjOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂ t₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem SurjOn.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : SurjOn f s₁ t₂) : SurjOn f s₂ t₁ :=
  Subset.trans ht <| Subset.trans hf <| image_mono hs
/-
**Set.SurjOn.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t₂ : Set β} {f : α → β},  
 Set.SurjOn f s t₁ → Set.SurjOn f s t₂ → Set.SurjOn f s (t₁ ∪ t₂)
参数：t₁ ∪ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem SurjOn.union (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂) : SurjOn f s (t₁ ∪ t₂) := fun _ hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx
/-
**Set.SurjOn.union_union** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   Set.SurjOn f s₁ t₁ → Set.SurjOn f s₂ t₂ → Set.SurjOn f (s₁ ∪ s₂) (t₁ ∪ t₂)
参数：s₁ ∪ s₂；t₁ ∪ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.union`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t₂ : S
et β} {f : α → β},   Set.SurjOn f s t₁ → Set.SurjOn f s t₂ → Set.SurjOn f s (t₁ 
∪ t₂)
· 使用定理 `Set.SurjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂
 t₁
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem SurjOn.union_union (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) :
    SurjOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  (h₁.mono subset_union_left (Subset.refl _)).union
    (h₂.mono subset_union_right (Subset.refl _))
/-
**Set.SurjOn.inter_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   Set.SurjOn f s₁ t₁ → Set.SurjOn f s₂ t₂ → Set.InjOn f (s₁ ∪ s₂) → Set.SurjO
n f (s₁ ∩ s₂) (t₁ ∩ t₂)
参数：s₁ ∪ s₂；s₁ ∩ s₂；t₁ ∩ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem SurjOn.inter_inter (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) (t₁ ∩ t₂) := by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) heq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩
/-
**Set.SurjOn.inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t : Set β} {f : α → β},  
 Set.SurjOn f s₁ t → Set.SurjOn f s₂ t → Set.InjOn f (s₁ ∪ s₂) → Set.SurjOn f (s
₁ ∩ s₂) t
参数：s₁ ∪ s₂；s₁ ∩ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.inter_inter`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.SurjOn f s₁ t₁ → Set.SurjOn f s₂ t₂ → Set.Inj
On f (s₁ ∪ s…
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
theorem SurjOn.inter (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) t :=
  inter_self t ▸ h₁.inter_inter h₂ h
/-
**Set.surjOn_id** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：surjOn_id (s : Set α) : SurjOn id s s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
-/
lemma surjOn_id (s : Set α) : SurjOn id s s := by simp [SurjOn]
/-
**Set.SurjOn.comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {p 
: Set γ} {f : α → β} {g : β → γ},   Set.SurjOn g t p → Set.SurjOn f s t → Set.Su
rjOn (g ∘ f) s p
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem SurjOn.comp (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
  Subset.trans hg <| Subset.trans (image_mono hf) <| image_comp g f s ▸ Subset.refl _
/-
**Set.SurjOn.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {p 
: Set γ} {f : α → β} {g : β → γ},   Set.SurjOn (g ∘ f) s p → Set.MapsTo f s t → 
Set.SurjOn g t p
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma SurjOn.of_comp (h : SurjOn (g ∘ f) s p) (hr : MapsTo f s t) : SurjOn g t p := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := h hz
  exact ⟨f x, hr hx, rfl⟩
/-
**Set.surjOn_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：surjOn_comp_iff : SurjOn (g ∘ f) s p ↔ SurjOn g (f '' s) p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.of_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : 
Set α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.SurjOn (g ∘ f) s p
 → Set.M…
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Set.SurjOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.SurjOn g t p → Set.Su
rjOn …
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
-/
lemma surjOn_comp_iff : SurjOn (g ∘ f) s p ↔ SurjOn g (f '' s) p :=
  ⟨fun h ↦ h.of_comp <| mapsTo_image f s, fun h ↦ h.comp <| surjOn_image _ _⟩
/-
**Set.SurjOn.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.SurjOn f s s → ∀ (n : ℕ), Se
t.SurjOn f^[n] s s
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma SurjOn.iterate {f : α → α} {s : Set α} (h : SurjOn f s s) : ∀ n, SurjOn f^[n] s s
  | 0 => surjOn_id _
  | (n + 1) => (h.iterate n).comp h
/-
**Set.SurjOn.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {f 
: α → β},   Set.SurjOn f s t → ∀ (g : β → γ), Set.SurjOn (g ∘ f) s (g '' t)
参数：g : β → γ；g ∘ f；g '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.SurjOn.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t 
: Set β), Set.SurjOn f s t = (t ⊆ f '' s)
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma SurjOn.comp_left (hf : SurjOn f s t) (g : β → γ) : SurjOn (g ∘ f) s (g '' t) := by
  rw [SurjOn, image_comp g f]; exact image_mono hf
/-
**Set.SurjOn.comp_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {g : β → γ} {s 
: Set β} {t : Set γ},   Function.Surjective f → Set.SurjOn g s t → Set.SurjOn (g
 ∘ f) (f ⁻¹' s) t
参数：g ∘ f；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.SurjOn.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t 
: Set β), Set.SurjOn f s t = (t ⊆ f '' s)
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
-/
lemma SurjOn.comp_right {s : Set β} {t : Set γ} (hf : Surjective f) (hg : SurjOn g s t) :
    SurjOn (g ∘ f) (f ⁻¹' s) t := by
  rwa [SurjOn, image_comp g f, image_preimage_eq _ hf]
/-
**Set.surjOn_of_subsingleton'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：surjOn_of_subsingleton' [Subsingleton β] (f : α -> β) (h : t.Nonempty -> s
.Nonempty) : SurjOn f s t
参数：f : α -> β；h : t.Nonempty -> s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsingleton.mem_iff_nonempty`：mem_iff_nonempty {α : Type*} [Subsingleto
n α] {s : Set α} {x : α} : x in s ↔ s.Nonempty
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
lemma surjOn_of_subsingleton' [Subsingleton β] (f : α → β) (h : t.Nonempty → s.Nonempty) :
    SurjOn f s t :=
  fun _ ha ↦ Subsingleton.mem_iff_nonempty.2 <| (h ⟨_, ha⟩).image _
/-
**Set.surjOn_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：surjOn_of_subsingleton [Subsingleton α] (f : α -> α) (s : Set α) : SurjOn 
f s s
参数：f : α -> α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.surjOn_of_subsingleton'`：surjOn_of_subsingleton' [Subsingleton β] (f
 : α -> β) (h : t.Nonempty -> s.Nonempty) : SurjOn f s t
-/
lemma surjOn_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : SurjOn f s s :=
  surjOn_of_subsingleton' _ id
/-
**Set.surjOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.SurjOn f Set.univ Set.uni
v ↔ Function.Surjective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma surjOn_univ : SurjOn f univ univ ↔ Surjective f := by
  simp [Surjective, SurjOn, subset_def]
/-
**Set._root_.Function.Surjective.surjOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.Function.Surjective.surjOn (hf : Surjective f) : SurjOn f univ t :=
  (surjOn_univ.2 hf).mono .rfl (subset_univ _)
/-
**Set.SurjOn.surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.SurjOn f s Se
t.univ → Function.Surjective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.surjOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.SurjOn
 f Set.univ Set.univ ↔ Function.Surjective f
· 使用定理 `Set.SurjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂
 t₁
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
lemma SurjOn.surjective (hf : SurjOn f s .univ) : f.Surjective :=
  surjOn_univ.1 <| hf.mono s.subset_univ .rfl
/-
**Set.SurjOn.image_eq_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.S
urjOn f s t → Set.MapsTo f s t → f '' s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
-/
theorem SurjOn.image_eq_of_mapsTo (h₁ : SurjOn f s t) (h₂ : MapsTo f s t) : f '' s = t :=
  eq_of_subset_of_subset h₂.image_subset h₁
/-
**Set.image_eq_iff_surjOn_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_eq_iff_surjOn_mapsTo : f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Set.SurjOn.image_eq_of_mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set 
α} {t : Set β} {f : α → β}, Set.SurjOn f s t → Set.MapsTo f s t → f '' s = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem image_eq_iff_surjOn_mapsTo : f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t := by
  refine ⟨?_, fun h => h.1.image_eq_of_mapsTo h.2⟩
  rintro rfl
  exact ⟨s.surjOn_image f, s.mapsTo_image f⟩
/-
**Set.SurjOn.image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t t₁ : Set β} {f : α → β}, Se
t.SurjOn f s t → t₁ ⊆ t → f '' f ⁻¹' t₁ = t₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `Set.mem_range_of_mem_image`：mem_range_of_mem_image (f : α -> β) (s) {x :
 β} (h : x in f '' s) : x in range f
-/
lemma SurjOn.image_preimage (h : Set.SurjOn f s t) (ht : t₁ ⊆ t) : f '' f ⁻¹' t₁ = t₁ :=
  image_preimage_eq_iff.2 fun _ hx ↦ mem_range_of_mem_image f s <| h <| ht hx
/-
**Set.SurjOn.mapsTo_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β},   Set
.SurjOn f s t → Function.Injective f → Set.MapsTo f sᶜ tᶜ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SurjOn.mapsTo_compl (h : SurjOn f s t) (h' : Injective f) : MapsTo f sᶜ tᶜ :=
  fun _ hs ht =>
  let ⟨_, hx', HEq⟩ := h ht
  hs <| h' HEq ▸ hx'
/-
**Set.MapsTo.surjOn_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β},   Set
.MapsTo f s t → Function.Surjective f → Set.SurjOn f sᶜ tᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem MapsTo.surjOn_compl (h : MapsTo f s t) (h' : Surjective f) : SurjOn f sᶜ tᶜ :=
  h'.forall.2 fun _ ht => (mem_image_of_mem _) fun hs => ht (h hs)
/-
**Set.EqOn.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {f 
: α → β} {g₁ g₂ : β → γ},   Set.EqOn (g₁ ∘ f) (g₂ ∘ f) s → Set.SurjOn f s t → Se
t.EqOn g₁ g₂ t
参数：g₁ ∘ f；g₂ ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EqOn.cancel_right (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t) : t.EqOn g₁ g₂ := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha
/-
**Set.SurjOn.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {f 
: α → β} {g₁ g₂ : β → γ},   Set.SurjOn f s t → Set.MapsTo f s t → (Set.EqOn (g₁ 
∘ f) (g₂ ∘ f) s ↔ Set.EqOn g₁ g₂ t)
参数：Set.EqOn (g₁ ∘ f) (g₂ ∘ f) s ↔ Set.EqOn g₁ g₂ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.cancel_right`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s
 : Set α} {t : Set β} {f : α → β} {g₁ g₂ : β → γ},   Set.EqOn (g₁ ∘ f) (g₂ ∘ f) 
s → Set.Sur…
· 使用定理 `Set.EqOn.comp_right`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s :
 Set α} {t : Set β} {f : α → β} {g₁ g₂ : β → γ},   Set.EqOn g₁ g₂ t → Set.MapsTo
 f s t → …
-/
theorem SurjOn.cancel_right (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ t.EqOn g₁ g₂ :=
  ⟨fun h => h.cancel_right hf, fun h => h.comp_right hf'⟩
/-
**Set.eqOn_comp_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_comp_right_iff : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.cancel_right`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{s : Set α} {t : Set β} {f : α → β} {g₁ g₂ : β → γ},   Set.SurjOn f s t → Set.Ma
psTo f s t → …
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem eqOn_comp_right_iff : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂ :=
  (s.surjOn_image f).cancel_right <| s.mapsTo_image f
/-
**Set.SurjOn.forall** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {p : β
 → Prop},   Set.SurjOn f s t → Set.MapsTo f s t → ((∀ y ∈ t, p y) ↔ ∀ x ∈ s, p (
f x))
参数：(∀ y ∈ t, p y) ↔ ∀ x ∈ s, p (f x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SurjOn.forall {p : β → Prop} (hf : s.SurjOn f t) (hf' : s.MapsTo f t) :
    (∀ y ∈ t, p y) ↔ (∀ x ∈ s, p (f x)) :=
  ⟨fun H x hx ↦ H (f x) (hf' hx), fun H _y hy ↦ let ⟨x, hx, hxy⟩ := hf hy; hxy ▸ H x hx⟩
/-
**Set._root_.Subtype.coind_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subtype.coind_surjective {α β} {f : α → β} {p : Set β} (h : ∀ a, f a ∈ p)
    (hf : Set.SurjOn f Set.univ p) :
    (Subtype.coind f h).Surjective := fun ⟨_, hb⟩ ↦
  let ⟨a, _, ha⟩ := hf hb
  ⟨a, Subtype.coe_injective ha⟩
/-
**Set._root_.Subtype.coind_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subtype.coind_bijective {α β} {f : α → β} {p : Set β} (h : ∀ a, f a ∈ p)
    (hf_inj : f.Injective) (hf_surj : Set.SurjOn f Set.univ p) :
    (Subtype.coind f h).Bijective :=
  ⟨Subtype.coind_injective h hf_inj, Subtype.coind_surjective h hf_surj⟩

end surjOn

/-! ### Bijectivity -/
section bijOn

/-
**Set.BijOn.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.B
ijOn f s t → Set.MapsTo f s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem BijOn.mapsTo (h : BijOn f s t) : MapsTo f s t :=
  h.left
/-
**Set.BijOn.injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.B
ijOn f s t → Set.InjOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem BijOn.injOn (h : BijOn f s t) : InjOn f s :=
  h.right.left
/-
**Set.BijOn.surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.B
ijOn f s t → Set.SurjOn f s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem BijOn.surjOn (h : BijOn f s t) : SurjOn f s t :=
  h.right.right
/-
**Set.BijOn.mk** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β},   Set
.MapsTo f s t → Set.InjOn f s → Set.SurjOn f s t → Set.BijOn f s t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BijOn.mk (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t) : BijOn f s t :=
  ⟨h₁, h₂, h₃⟩
/-
**Set.bijOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bijOn_empty (f : α -> β) : BijOn f ∅ ∅
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_empty`：mapsTo_empty (f : α -> β) (t : Set β) : MapsTo f ∅ t
· 使用定理 `Set.injOn_empty`：injOn_empty (f : α -> β) : InjOn f ∅
· 使用定理 `Set.surjOn_empty`：surjOn_empty (f : α -> β) (s : Set α) : SurjOn f s ∅
-/
theorem bijOn_empty (f : α → β) : BijOn f ∅ ∅ :=
  ⟨mapsTo_empty f ∅, injOn_empty f, surjOn_empty f ∅⟩
/-
**Set.bijOn_empty_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.BijOn f s ∅ ↔
 s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.bijOn_empty`：bijOn_empty (f : α -> β) : BijOn f ∅ ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem bijOn_empty_iff_left : BijOn f s ∅ ↔ s = ∅ :=
  ⟨fun h ↦ by simpa using h.mapsTo, by rintro rfl; exact bijOn_empty f⟩
/-
**Set.bijOn_empty_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {t : Set β} {f : α → β}, Set.BijOn f ∅ t ↔
 t = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `Set.bijOn_empty`：bijOn_empty (f : α -> β) : BijOn f ∅ ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] theorem bijOn_empty_iff_right : BijOn f ∅ t ↔ t = ∅ :=
  ⟨fun h ↦ by simpa using h.surjOn, by rintro rfl; exact bijOn_empty f⟩
/-
**Set.bijOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : α} {b : β}, Set.BijOn f {
a} {b} ↔ f a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma bijOn_singleton : BijOn f {a} {b} ↔ f a = b := by simp [BijOn, eq_comm]
/-
**Set.BijOn.inter_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   Set.BijOn f s₁ t₁ → Set.MapsTo f s₂ t₂ → s₁ ∩ f ⁻¹' t₂ ⊆ s₂ → Set.BijOn f (
s₁ ∩ s₂) (t₁ ∩ t₂)
参数：s₁ ∩ s₂；t₁ ∩ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.inter_inter`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → Set.MapsTo f s₂ t₂ → Set.Map
sTo f (s₁ ∩ …
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem BijOn.inter_mapsTo (h₁ : BijOn f s₁ t₁) (h₂ : MapsTo f s₂ t₂) (h₃ : s₁ ∩ f ⁻¹' t₂ ⊆ s₂) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.mapsTo.inter_inter h₂, h₁.injOn.mono inter_subset_left, fun _ hy =>
    let ⟨x, hx, hxy⟩ := h₁.surjOn hy.1
    ⟨x, ⟨hx, h₃ ⟨hx, hxy.symm.subst hy.2⟩⟩, hxy⟩⟩
/-
**Set.MapsTo.inter_bijOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   Set.MapsTo f s₁ t₁ → Set.BijOn f s₂ t₂ → s₂ ∩ f ⁻¹' t₁ ⊆ s₁ → Set.BijOn f (
s₁ ∩ s₂) (t₁ ∩ t₂)
参数：s₁ ∩ s₂；t₁ ∩ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.inter_mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.BijOn f s₁ t₁ → Set.MapsTo f s₂ t₂ → s₁ ∩ f ⁻
¹' t₂ ⊆ s₂ →…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem MapsTo.inter_bijOn (h₁ : MapsTo f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h₃ : s₂ ∩ f ⁻¹' t₁ ⊆ s₁) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  inter_comm s₂ s₁ ▸ inter_comm t₂ t₁ ▸ h₂.inter_mapsTo h₁ h₃
/-
**Set.BijOn.inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   Set.BijOn f s₁ t₁ → Set.BijOn f s₂ t₂ → Set.InjOn f (s₁ ∪ s₂) → Set.BijOn f
 (s₁ ∩ s₂) (t₁ ∩ t₂)
参数：s₁ ∪ s₂；s₁ ∩ s₂；t₁ ∩ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.inter_inter`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → Set.MapsTo f s₂ t₂ → Set.Map
sTo f (s₁ ∩ …
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.SurjOn.inter_inter`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.SurjOn f s₁ t₁ → Set.SurjOn f s₂ t₂ → Set.Inj
On f (s₁ ∪ s…
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem BijOn.inter (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.mapsTo.inter_inter h₂.mapsTo, h₁.injOn.mono inter_subset_left,
    h₁.surjOn.inter_inter h₂.surjOn h⟩
/-
**Set.BijOn.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β
},   Set.BijOn f s₁ t₁ → Set.BijOn f s₂ t₂ → Set.InjOn f (s₁ ∪ s₂) → Set.BijOn f
 (s₁ ∪ s₂) (t₁ ∪ t₂)
参数：s₁ ∪ s₂；s₁ ∪ s₂；t₁ ∪ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.union_union`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → Set.MapsTo f s₂ t₂ → Set.Map
sTo f (s₁ ∪ …
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.SurjOn.union_union`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.SurjOn f s₁ t₁ → Set.SurjOn f s₂ t₂ → Set.Sur
jOn f (s₁ ∪ …
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem BijOn.union (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    BijOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨h₁.mapsTo.union_union h₂.mapsTo, h, h₁.surjOn.union_union h₂.surjOn⟩
/-
**Set.BijOn.subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.B
ijOn f s t → t ⊆ Set.range f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.subset_range`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.SurjOn f s t → t ⊆ Set.range f
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem BijOn.subset_range (h : BijOn f s t) : t ⊆ range f :=
  h.surjOn.subset_range
/-
**Set.InjOn.bijOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.InjOn f s → S
et.BijOn f s (f '' s)
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mk`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f
 : α → β},   Set.MapsTo f s t → Set.InjOn f s → Set.SurjOn f s t → Set.BijOn f s
 t
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem InjOn.bijOn_image (h : InjOn f s) : BijOn f s (f '' s) :=
  BijOn.mk (mapsTo_image f s) h (Subset.refl _)
/-
**Set.SurjOn.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.S
urjOn f s t → Set.SurjOn f (f ⁻¹' t) t
参数：f ⁻¹' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Set.SurjOn.subset_range`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.SurjOn f s t → t ⊆ Set.range f
-/
theorem SurjOn.preimage (h : SurjOn f s t) : SurjOn f (f ⁻¹' t) t := by
  intro u hu
  rw [image_preimage_eq_inter_range]
  exact ⟨hu, mem_range.mpr (subset_range h hu)⟩
/-
**Set.BijOn.congr** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f₁ f₂ : α → β},  
 Set.BijOn f₁ s t → Set.EqOn f₁ f₂ s → Set.BijOn f₂ s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mk`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f
 : α → β},   Set.MapsTo f s t → Set.InjOn f s → Set.SurjOn f s t → Set.BijOn f s
 t
· 使用定理 `Set.MapsTo.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f₁ f₂ : α → β},   Set.MapsTo f₁ s t → Set.EqOn f₁ f₂ s → Set.MapsTo f₂ s t
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.InjOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α 
→ β}, Set.InjOn f₁ s → Set.EqOn f₁ f₂ s → Set.InjOn f₂ s
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.SurjOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f₁ f₂ : α → β},   Set.SurjOn f₁ s t → Set.EqOn f₁ f₂ s → Set.SurjOn f₂ s t
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem BijOn.congr (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s) : BijOn f₂ s t :=
  BijOn.mk (h₁.mapsTo.congr h) (h₁.injOn.congr h) (h₁.surjOn.congr h)
/-
**Set.EqOn.bijOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f₁ f₂ : α → β},  
 Set.EqOn f₁ f₂ s → (Set.BijOn f₁ s t ↔ Set.BijOn f₂ s t)
参数：Set.BijOn f₁ s t ↔ Set.BijOn f₂ s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f₁ f₂ : α → β},   Set.BijOn f₁ s t → Set.EqOn f₁ f₂ s → Set.BijOn f₂ s t
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem EqOn.bijOn_iff (H : EqOn f₁ f₂ s) : BijOn f₁ s t ↔ BijOn f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩
/-
**Set.BijOn.image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β}, Set.B
ijOn f s t → f '' s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.image_eq_of_mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set 
α} {t : Set β} {f : α → β}, Set.SurjOn f s t → Set.MapsTo f s t → f '' s = t
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
-/
theorem BijOn.image_eq (h : BijOn f s t) : f '' s = t :=
  h.surjOn.image_eq_of_mapsTo h.mapsTo
/-
**Set.BijOn.forall** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {p : β
 → Prop},   Set.BijOn f s t → ((∀ b ∈ t, p b) ↔ ∀ a ∈ s, p (f a))
参数：(∀ b ∈ t, p b) ↔ ∀ a ∈ s, p (f a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
lemma BijOn.forall {p : β → Prop} (hf : BijOn f s t) : (∀ b ∈ t, p b) ↔ ∀ a ∈ s, p (f a) where
  mp h _ ha := h _ <| hf.mapsTo ha
  mpr h b hb := by obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact h _ ha
/-
**Set.BijOn.exists** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {p : β
 → Prop},   Set.BijOn f s t → ((∃ b ∈ t, p b) ↔ ∃ a ∈ s, p (f a))
参数：(∃ b ∈ t, p b) ↔ ∃ a ∈ s, p (f a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
-/
lemma BijOn.exists {p : β → Prop} (hf : BijOn f s t) : (∃ b ∈ t, p b) ↔ ∃ a ∈ s, p (f a) where
  mp := by rintro ⟨b, hb, h⟩; obtain ⟨a, ha, rfl⟩ := hf.surjOn hb; exact ⟨a, ha, h⟩
  mpr := by rintro ⟨a, ha, h⟩; exact ⟨f a, hf.mapsTo ha, h⟩
/-
**Set._root_.Equiv.image_eq_iff_bijOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Equiv.image_eq_iff_bijOn (e : α ≃ β) : e '' s = t ↔ BijOn e s t :=
  ⟨fun h ↦ ⟨(mapsTo_image e s).mono_right h.subset, e.injective.injOn, h ▸ surjOn_image e s⟩,
  BijOn.image_eq⟩
/-
**Set.bijOn_id** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：bijOn_id (s : Set α) : BijOn id s s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mapsTo_id`：mapsTo_id (s : Set α) : MapsTo id s s
· 使用引理 `Set.injOn_id`：injOn_id (s : Set α) : InjOn id s
· 使用引理 `Set.surjOn_id`：surjOn_id (s : Set α) : SurjOn id s s
-/
lemma bijOn_id (s : Set α) : BijOn id s s := ⟨s.mapsTo_id, s.injOn_id, s.surjOn_id⟩
/-
**Set.BijOn.comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set α} {t : Set β} {p 
: Set γ} {f : α → β} {g : β → γ},   Set.BijOn g t p → Set.BijOn f s t → Set.BijO
n (g ∘ f) s p
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mk`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f
 : α → β},   Set.MapsTo f s t → Set.InjOn f s → Set.SurjOn f s t → Set.BijOn f s
 t
· 使用定理 `Set.MapsTo.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.Ma
psTo …
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.InjOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {f : α → β} {g : β → γ},   Set.InjOn g t → Set.InjOn f s → Set.Ma
psTo…
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.SurjOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.SurjOn g t p → Set.Su
rjOn …
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem BijOn.comp (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
  BijOn.mk (hg.mapsTo.comp hf.mapsTo) (hg.injOn.comp hf.injOn hf.mapsTo) (hg.surjOn.comp hf.surjOn)

/-- If `f : α → β` and `g : β → γ` and if `f` is injective on `s`, then `f ∘ g` is a bijection
on `s` iff  `g` is a bijection on `f '' s`. -/
/-
**Set.bijOn_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bijOn_comp_iff (hf : InjOn f s) : BijOn (g ∘ f) s p ↔ BijOn g (f '' s) p
参数：hf : InjOn f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f : α → β` and `g : β → γ` and if `f` is injective on `s`, then `f ∘ g` is a
 bijection
on `s` iff  `g` is a bijection on `f '' s`.
-/
theorem bijOn_comp_iff (hf : InjOn f s) : BijOn (g ∘ f) s p ↔ BijOn g (f '' s) p := by
  simp only [BijOn, InjOn.comp_iff, surjOn_comp_iff, mapsTo_image_iff, hf]

/--
If we have a commutative square

```
α --f--> β
|        |
p₁       p₂
|        |
\/       \/
γ --g--> δ
```

and `f` induces a bijection from `s : Set α` to `t : Set β`, then `g`
induces a bijection from the image of `s` to the image of `t`, as long as `g` is
is injective on the image of `s`.
-/
/-
**Set.bijOn_image_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bijOn_image_image {p₁ : α -> γ} {p₂ : β -> δ} {g : γ -> δ} (comm : forall 
a, p₂ (f a) = g (p₁ a)) (hbij : BijOn f s t) (hinj : InjOn g (p₁ '' s)) : BijOn 
g (p₁ '' s) (p₂ '' t)
参数：comm : forall a, p₂ (f a) = g (p₁ a)；hbij : BijOn f s t；hinj : InjOn g (p₁ ''
 s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If we have a commutative square

```
α --f--> β
|        |
p₁       p₂
|        |
\/       \/
γ --g--> δ
```

and `f` induces a bijection from `s : Set α` to `t : Set β`, then `g`
induces a bijection from the image of `s` to the image of `t`, as long as `g` is
is injective on the image of `s`.
-/
theorem bijOn_image_image {p₁ : α → γ} {p₂ : β → δ} {g : γ → δ} (comm : ∀ a, p₂ (f a) = g (p₁ a))
    (hbij : BijOn f s t) (hinj : InjOn g (p₁ '' s)) : BijOn g (p₁ '' s) (p₂ '' t) := by
  obtain ⟨h1, h2, h3⟩ := hbij
  refine ⟨?_, hinj, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨f a, h1 ha, by rw [comm a]⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := h3 hb
    grind
/-
**Set.BijOn.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.BijOn f s s → ∀ (n : ℕ), Set
.BijOn f^[n] s s
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BijOn.iterate {f : α → α} {s : Set α} (h : BijOn f s s) : ∀ n, BijOn f^[n] s s
  | 0 => s.bijOn_id
  | (n + 1) => (h.iterate n).comp h
/-
**Set.bijOn_of_subsingleton'** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：bijOn_of_subsingleton' [Subsingleton α] [Subsingleton β] (f : α -> β) (h :
 s.Nonempty ↔ t.Nonempty) : BijOn f s t
参数：f : α -> β；h : s.Nonempty ↔ t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mapsTo_of_subsingleton'`：mapsTo_of_subsingleton' [Subsingleton β] (f
 : α -> β) (h : s.Nonempty -> t.Nonempty) : MapsTo f s t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.injOn_of_subsingleton`：injOn_of_subsingleton [Subsingleton α] (f : α
 -> β) (s : Set α) : InjOn f s
· 使用引理 `Set.surjOn_of_subsingleton'`：surjOn_of_subsingleton' [Subsingleton β] (f
 : α -> β) (h : t.Nonempty -> s.Nonempty) : SurjOn f s t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma bijOn_of_subsingleton' [Subsingleton α] [Subsingleton β] (f : α → β)
    (h : s.Nonempty ↔ t.Nonempty) : BijOn f s t :=
  ⟨mapsTo_of_subsingleton' _ h.1, injOn_of_subsingleton _ _, surjOn_of_subsingleton' _ h.2⟩
/-
**Set.bijOn_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：bijOn_of_subsingleton [Subsingleton α] (f : α -> α) (s : Set α) : BijOn f 
s s
参数：f : α -> α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.bijOn_of_subsingleton'`：bijOn_of_subsingleton' [Subsingleton α] [Sub
singleton β] (f : α -> β) (h : s.Nonempty ↔ t.Nonempty) : BijOn f s t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma bijOn_of_subsingleton [Subsingleton α] (f : α → α) (s : Set α) : BijOn f s s :=
  bijOn_of_subsingleton' _ Iff.rfl
/-
**Set.BijOn.bijective** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} (h : S
et.BijOn f s t),   Function.Bijective (Set.MapsTo.restrict f s t ⋯)
参数：h : Set.BijOn f s t；Set.MapsTo.restrict f s t ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem BijOn.bijective (h : BijOn f s t) : Bijective (h.mapsTo.restrict f s t) :=
  ⟨fun x y h' => Subtype.ext <| h.injOn x.2 y.2 <| Subtype.ext_iff.1 h', fun ⟨_, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.surjOn hy
    ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
/-
**Set.bijOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.BijOn f Set.univ Set.univ
 ↔ Function.Bijective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma bijOn_univ : BijOn f univ univ ↔ Bijective f := by simp [Bijective, BijOn]

protected alias ⟨_, _root_.Function.Bijective.bijOn_univ⟩ := bijOn_univ
/-
**Set._root_.Function.Injective.bijOn_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.Injective.bijOn_image (hf : f.Injective) : BijOn f s (f '' s) :=
  hf.injOn.bijOn_image
/-
**Set._root_.Function.Surjective.surjOn_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Set`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.Surjective.surjOn_preimage (hf : f.Surjective) : SurjOn f (f ⁻¹' t) t :=
  hf.surjOn.preimage
/-
**Set._root_.Function.Bijective.bijOn_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.Bijective.bijOn_preimage (hf : f.Bijective) : BijOn f (f ⁻¹' t) t :=
  ⟨fun _ ↦ id, hf.injective.injOn, hf.surjective.surjOn_preimage⟩
/-
**Set.BijOn.compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β},   Set
.BijOn f s t → Function.Bijective f → Set.BijOn f sᶜ tᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.mapsTo_compl`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β},   Set.SurjOn f s t → Function.Injective f → Set.MapsTo f s
ᶜ tᶜ
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Set.MapsTo.surjOn_compl`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β},   Set.MapsTo f s t → Function.Surjective f → Set.SurjOn f 
sᶜ tᶜ
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem BijOn.compl (hst : BijOn f s t) (hf : Bijective f) : BijOn f sᶜ tᶜ :=
  ⟨hst.surjOn.mapsTo_compl hf.1, hf.1.injOn, hst.mapsTo.surjOn_compl hf.2⟩
/-
**Set.BijOn.subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {r : S
et β},   Set.BijOn f s t → r ⊆ t → Set.BijOn f (s ∩ f ⁻¹' r) r
参数：s ∩ f ⁻¹' r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem BijOn.subset_right {r : Set β} (hf : BijOn f s t) (hrt : r ⊆ t) :
    BijOn f (s ∩ f ⁻¹' r) r := by
  refine ⟨inter_subset_right, hf.injOn.mono inter_subset_left, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := hf.surjOn (hrt hx)
  exact ⟨y, ⟨hy, hx⟩, rfl⟩
/-
**Set.BijOn.subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {r : S
et α},   Set.BijOn f s t → r ⊆ s → Set.BijOn f r (f '' r)
参数：f '' r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
-/
theorem BijOn.subset_left {r : Set α} (hf : BijOn f s t) (hrs : r ⊆ s) :
    BijOn f r (f '' r) :=
  (hf.injOn.mono hrs).bijOn_image
/-
**Set.BijOn.insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {a : α
},   a ∉ s → f a ∉ t → (Set.BijOn f (insert a s) (insert (f a) t) ↔ Set.BijOn f 
s t)
参数：Set.BijOn f (insert a s) (insert (f a) t) ↔ Set.BijOn f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.BijOn.union`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.BijOn f s₁ t₁ → Set.BijOn f s₂ t₂ → Set.InjOn f (s₁ 
∪ s₂)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.bijOn_singleton`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : α}
 {b : β}, Set.BijOn f {a} {b} ↔ f a = b
· 使用定理 `Set.injOn_insert`：injOn_insert {f : α -> β} {s : Set α} {a : α} (has : a
 ∉ s) : Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem BijOn.insert_iff (ha : a ∉ s) (hfa : f a ∉ t) :
    BijOn f (insert a s) (insert (f a) t) ↔ BijOn f s t where
  mp h := by
    have := congrArg (· \ {f a}) (image_insert_eq ▸ h.image_eq)
    simp only [mem_singleton_iff, insert_sdiff_of_mem] at this
    rw [sdiff_singleton_eq_self hfa, sdiff_singleton_eq_self] at this
    · exact ⟨by simp [← this, mapsTo_iff_image_subset], h.injOn.mono (subset_insert ..),
        by simp [← this, surjOn_image]⟩
    simp only [mem_image, not_exists, not_and]
    intro x hx
    rw [h.injOn.eq_iff (by simp [hx]) (by simp)]
    exact ha ∘ (· ▸ hx)
  mpr h := by
    repeat rw [insert_eq]
    refine (bijOn_singleton.mpr rfl).union h ?_
    simp only [singleton_union, injOn_insert fun x ↦ (hfa (h.mapsTo x)), h.injOn, mem_image,
      not_exists, not_and, true_and]
    exact fun _ hx h₂ ↦ hfa (h₂ ▸ h.mapsTo hx)
/-
**Set.BijOn.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {a : α
},   Set.BijOn f s t → f a ∉ t → Set.BijOn f (insert a s) (insert (f a) t)
参数：insert a s；insert (f a) t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.BijOn.insert_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : S
et β} {f : α → β} {a : α},   a ∉ s → f a ∉ t → (Set.BijOn f (insert a s) (insert
 (f a) t) …
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
-/
theorem BijOn.insert (h₁ : BijOn f s t) (h₂ : f a ∉ t) :
    BijOn f (insert a s) (insert (f a) t) :=
  (insert_iff (h₂ <| h₁.mapsTo ·) h₂).mpr h₁
/-
**Set.BijOn.sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {a : α
},   Set.BijOn f s t → a ∈ s → Set.BijOn f (s \ {a}) (t \ {f a})
参数：s \ {a}；t \ {f a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.InjOn.image_sdiff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β} {t : Set α},   Set.InjOn f s → f '' (s \ t) = f '' s \ f '' (s ∩ t)
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.BijOn.subset_left`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : 
Set β} {f : α → β} {r : Set α},   Set.BijOn f s t → r ⊆ s → Set.BijOn f r (f '' 
r)
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
theorem BijOn.sdiff_singleton (h₁ : BijOn f s t) (h₂ : a ∈ s) :
    BijOn f (s \ {a}) (t \ {f a}) := by
  convert! h₁.subset_left sdiff_subset
  simp [h₁.injOn.image_sdiff, h₁.image_eq, h₂, inter_eq_self_of_subset_right]

end bijOn

/-! ### left inverse -/
namespace LeftInvOn

/-
**Set.LeftInvOn.eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：eqOn (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s
参数：h : LeftInvOn f' f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqOn (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s :=
  h
/-
**Set.LeftInvOn.eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：eq (h : LeftInvOn f' f s) {x} (hx : x in s) : f' (f x) = x
参数：h : LeftInvOn f' f s；hx : x in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq (h : LeftInvOn f' f s) {x} (hx : x ∈ s) : f' (f x) = x :=
  h hx
/-
**Set.LeftInvOn.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t) (heq 
: EqOn f₁' f₂' t) : LeftInvOn f₂' f s
参数：h₁ : LeftInvOn f₁' f s；h₁' : MapsTo f s t；heq : EqOn f₁' f₂' t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t)
    (heq : EqOn f₁' f₂' t) : LeftInvOn f₂' f s := fun _ hx => heq (h₁' hx) ▸ h₁ hx
/-
**Set.LeftInvOn.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s) : LeftInvOn f₁'
 f₂ s
参数：h₁ : LeftInvOn f₁' f₁ s；heq : EqOn f₁ f₂ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s) : LeftInvOn f₁' f₂ s :=
  fun _ hx => heq hx ▸ h₁ hx
/-
**Set.LeftInvOn.injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：injOn (h : LeftInvOn f₁' f s) : InjOn f s
参数：h : LeftInvOn f₁' f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injOn (h : LeftInvOn f₁' f s) : InjOn f s := fun x₁ h₁ x₂ h₂ heq =>
  calc
    x₁ = f₁' (f x₁) := Eq.symm <| h h₁
    _ = f₁' (f x₂) := congr_arg f₁' heq
    _ = x₂ := h h₂
/-
**Set.LeftInvOn.surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：surjOn (h : LeftInvOn f' f s) (hf : MapsTo f s t) : SurjOn f' t s
参数：h : LeftInvOn f' f s；hf : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem surjOn (h : LeftInvOn f' f s) (hf : MapsTo f s t) : SurjOn f' t s := fun x hx =>
  ⟨f x, hf hx, h hx⟩
/-
**Set.LeftInvOn.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：mapsTo (h : LeftInvOn f' f s) (hf : SurjOn f s t) : MapsTo f' t s
参数：h : LeftInvOn f' f s；hf : SurjOn f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mapsTo (h : LeftInvOn f' f s) (hf : SurjOn f s t) :
    MapsTo f' t s := fun y hy => by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]
/-
**Set.LeftInvOn._root_.Set.leftInvOn_id** 是 Mathlib 中的一个引理，位于命名空间 `Set.LeftInvOn
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.leftInvOn_id (s : Set α) : LeftInvOn id id s := fun _ _ ↦ rfl
/-
**Set.LeftInvOn.comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t)
 : LeftInvOn (f' ∘ g') (g ∘ f) s
参数：hf' : LeftInvOn f' f s；hg' : LeftInvOn g' g t；hf : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
    LeftInvOn (f' ∘ g') (g ∘ f) s := fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_arg f' (hg' (hf h))
    _ = x := hf' h
/-
**Set.LeftInvOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：mono (hf : LeftInvOn f' f s) (ht : s₁ subseteq s) : LeftInvOn f' f s₁
参数：hf : LeftInvOn f' f s；ht : s₁ subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono (hf : LeftInvOn f' f s) (ht : s₁ ⊆ s) : LeftInvOn f' f s₁ := fun _ hx =>
  hf (ht hx)
/-
**Set.LeftInvOn.image_inter'** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：image_inter' (hf : LeftInvOn f' f s) : f '' (s₁ inter s) = f' ⁻¹' s₁ inter
 f '' s
参数：hf : LeftInvOn f' f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem image_inter' (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' s₁ ∩ f '' s := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact ⟨by rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact mem_image_of_mem _ ⟨by rwa [← hf h], h⟩
/-
**Set.LeftInvOn.image_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：image_inter (hf : LeftInvOn f' f s) : f '' (s₁ inter s) = f' ⁻¹' (s₁ inter
 s) inter f '' s
参数：hf : LeftInvOn f' f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.LeftInvOn.image_inter'`：image_inter' (hf : LeftInvOn f' f s) : f '' 
(s₁ inter s) = f' ⁻¹' s₁ inter f '' s
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem image_inter (hf : LeftInvOn f' f s) :
    f '' (s₁ ∩ s) = f' ⁻¹' (s₁ ∩ s) ∩ f '' s := by
  rw [hf.image_inter']
  refine Subset.antisymm ?_ (inter_subset_inter_left _ (preimage_mono inter_subset_left))
  rintro _ ⟨h₁, x, hx, rfl⟩; exact ⟨⟨h₁, by rwa [hf hx]⟩, mem_image_of_mem _ hx⟩
/-
**Set.LeftInvOn.image_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：image_image (hf : LeftInvOn f' f s) : f' '' f '' s = s
参数：hf : LeftInvOn f' f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
-/
theorem image_image (hf : LeftInvOn f' f s) : f' '' f '' s = s := by
  rw [Set.image_image, image_congr hf, image_id']
/-
**Set.LeftInvOn.image_image'** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：image_image' (hf : LeftInvOn f' f s) (hs : s₁ subseteq s) : f' '' f '' s₁ 
= s₁
参数：hf : LeftInvOn f' f s；hs : s₁ subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.image_image`：image_image (hf : LeftInvOn f' f s) : f' '' f
 '' s = s
· 使用定理 `Set.LeftInvOn.mono`：mono (hf : LeftInvOn f' f s) (ht : s₁ subseteq s) : 
LeftInvOn f' f s₁
-/
theorem image_image' (hf : LeftInvOn f' f s) (hs : s₁ ⊆ s) : f' '' f '' s₁ = s₁ :=
  (hf.mono hs).image_image

end LeftInvOn

/-! ### Right inverse -/
section RightInvOn
namespace RightInvOn

/-
**Set.RightInvOn.eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t
参数：h : RightInvOn f' f t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t :=
  h
/-
**Set.RightInvOn.eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：eq (h : RightInvOn f' f t) {y} (hy : y in t) : f (f' y) = y
参数：h : RightInvOn f' f t；hy : y in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq (h : RightInvOn f' f t) {y} (hy : y ∈ t) : f (f' y) = y :=
  h hy
/-
**Set.RightInvOn._root_.Set.LeftInvOn.rightInvOn_image** 是 Mathlib 中的一个定理，位于命名空间
 `Set.RightInvOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.LeftInvOn.rightInvOn_image (h : LeftInvOn f' f s) : RightInvOn f' f (f '' s) :=
  fun _y ⟨_x, hx, heq⟩ => heq ▸ (congr_arg f <| h.eq hx)
/-
**Set.RightInvOn.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：congr_left (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t) : RightInvOn f
₂' f t
参数：h₁ : RightInvOn f₁' f t；heq : EqOn f₁' f₂' t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.congr_right`：congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : 
EqOn f₁ f₂ s) : LeftInvOn f₁' f₂ s
-/
theorem congr_left (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t) :
    RightInvOn f₂' f t :=
  h₁.congr_right heq
/-
**Set.RightInvOn.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：congr_right (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ 
f₂ s) : RightInvOn f' f₂ t
参数：h₁ : RightInvOn f' f₁ t；hg : MapsTo f' t s；heq : EqOn f₁ f₂ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.congr_left`：congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β
} (h₁' : MapsTo f s t) (heq : EqOn f₁' f₂' t) : LeftInvOn f₂' f s
-/
theorem congr_right (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s) :
    RightInvOn f' f₂ t :=
  LeftInvOn.congr_left h₁ hg heq
/-
**Set.RightInvOn.surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' t s) : SurjOn f s t
参数：hf : RightInvOn f' f t；hf' : MapsTo f' t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.surjOn`：surjOn (h : LeftInvOn f' f s) (hf : MapsTo f s t) 
: SurjOn f' t s
-/
theorem surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' t s) : SurjOn f s t :=
  LeftInvOn.surjOn hf hf'
/-
**Set.RightInvOn.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：mapsTo (h : RightInvOn f' f t) (hf : SurjOn f' t s) : MapsTo f s t
参数：h : RightInvOn f' f t；hf : SurjOn f' t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.mapsTo`：mapsTo (h : LeftInvOn f' f s) (hf : SurjOn f s t) 
: MapsTo f' t s
-/
theorem mapsTo (h : RightInvOn f' f t) (hf : SurjOn f' t s) : MapsTo f s t :=
  LeftInvOn.mapsTo h hf
/-
**Set.RightInvOn._root_.Set.rightInvOn_id** 是 Mathlib 中的一个引理，位于命名空间 `Set.RightIn
vOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.rightInvOn_id (s : Set α) : RightInvOn id id s := fun _ _ ↦ rfl
/-
**Set.RightInvOn.comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p
 t) : RightInvOn (f' ∘ g') (g ∘ f) p
参数：hf : RightInvOn f' f t；hg : RightInvOn g' g p；g'pt : MapsTo g' p t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.comp`：comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g 
t) (hf : MapsTo f s t) : LeftInvOn (f' ∘ g') (g ∘ f) s
-/
theorem comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
    RightInvOn (f' ∘ g') (g ∘ f) p :=
  LeftInvOn.comp hg hf g'pt
/-
**Set.RightInvOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：mono (hf : RightInvOn f' f t) (ht : t₁ subseteq t) : RightInvOn f' f t₁
参数：hf : RightInvOn f' f t；ht : t₁ subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.mono`：mono (hf : LeftInvOn f' f s) (ht : s₁ subseteq s) : 
LeftInvOn f' f s₁
-/
theorem mono (hf : RightInvOn f' f t) (ht : t₁ ⊆ t) : RightInvOn f' f t₁ :=
  LeftInvOn.mono hf ht
end RightInvOn

/-
**Set.InjOn.rightInvOn_of_leftInvOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {f' : 
β → α},   Set.InjOn f s → Set.LeftInvOn f f' t → Set.MapsTo f s t → Set.MapsTo f
' t s → Set.RightInvOn f f' s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem InjOn.rightInvOn_of_leftInvOn (hf : InjOn f s) (hf' : LeftInvOn f f' t)
    (h₁ : MapsTo f s t) (h₂ : MapsTo f' t s) : RightInvOn f f' s := fun _ h =>
  hf (h₂ <| h₁ h) h (hf' (h₁ h))
/-
**Set.eqOn_of_leftInvOn_of_rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_of_leftInvOn_of_rightInvOn (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn 
f₂' f t) (h : MapsTo f₂' t s) : EqOn f₁' f₂' t
参数：h₁ : LeftInvOn f₁' f s；h₂ : RightInvOn f₂' f t；h : MapsTo f₂' t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eqOn_of_leftInvOn_of_rightInvOn (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t)
    (h : MapsTo f₂' t s) : EqOn f₁' f₂' t := fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_arg f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)
/-
**Set.SurjOn.leftInvOn_of_rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {f' : 
β → α},   Set.SurjOn f s t → Set.RightInvOn f f' s → Set.LeftInvOn f f' t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem SurjOn.leftInvOn_of_rightInvOn (hf : SurjOn f s t) (hf' : RightInvOn f f' s) :
    LeftInvOn f f' t := fun y hy => by
  let ⟨x, hx, heq⟩ := hf hy
  rw [← heq, hf' hx]
/-
**Set.image_eq_preimage_of_leftInvOn_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_eq_preimage_of_leftInvOn_injOn {f : α -> β} {g : β -> α} {s : Set α}
 (hgf : LeftInvOn g f s) (ginj : Set.InjOn g (g ⁻¹' s)) : f '' s = g ⁻¹' s
参数：hgf : LeftInvOn g f s；ginj : Set.InjOn g (g ⁻¹' s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.InjOn.rightInvOn_of_leftInvOn`：∀ {α : Type u_1} {β : Type u_2} {s : 
Set α} {t : Set β} {f : α → β} {f' : β → α},   Set.InjOn f s → Set.LeftInvOn f f
' t → Set.MapsTo f s t …
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem image_eq_preimage_of_leftInvOn_injOn {f : α → β} {g : β → α} {s : Set α}
    (hgf : LeftInvOn g f s) (ginj : Set.InjOn g (g ⁻¹' s)) : f '' s = g ⁻¹' s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_preimage, hgf hy]; exact hy
  · intro hx
    refine ⟨g x, hx, Set.InjOn.rightInvOn_of_leftInvOn ginj hgf (Set.mapsTo_preimage g s) ?_ hx⟩
    intro y hy
    simpa [hgf hy] using hy

@[deprecated (since := "2026-03-27")]
alias image_eq_preimage_of_leftInvOn_injOn_mapsTo := image_eq_preimage_of_leftInvOn_injOn

end RightInvOn

/-! ### Two-side inverses -/
namespace InvOn

/-
**Set.InvOn._root_.Set.invOn_id** 是 Mathlib 中的一个引理，位于命名空间 `Set.InvOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.invOn_id (s : Set α) : InvOn id id s s := ⟨s.leftInvOn_id, s.rightInvOn_id⟩
/-
**Set.InvOn.comp** 是 Mathlib 中的一个引理，位于命名空间 `Set.InvOn`。
形式化陈述：comp (hf : InvOn f' f s t) (hg : InvOn g' g t p) (fst : MapsTo f s t) (g'p
t : MapsTo g' p t) : InvOn (f' ∘ g') (g ∘ f) s p
参数：hf : InvOn f' f s t；hg : InvOn g' g t p；fst : MapsTo f s t；g'pt : MapsTo g' p
 t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.comp`：comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g 
t) (hf : MapsTo f s t) : LeftInvOn (f' ∘ g') (g ∘ f) s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.RightInvOn.comp`：comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g
 p) (g'pt : MapsTo g' p t) : RightInvOn (f' ∘ g') (g ∘ f) p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma comp (hf : InvOn f' f s t) (hg : InvOn g' g t p) (fst : MapsTo f s t)
    (g'pt : MapsTo g' p t) :
    InvOn (f' ∘ g') (g ∘ f) s p :=
  ⟨hf.1.comp hg.1 fst, hf.2.comp hg.2 g'pt⟩

@[symm]
/-
**Set.InvOn.symm** 是 Mathlib 中的一个定理，位于命名空间 `Set.InvOn`。
形式化陈述：symm (h : InvOn f' f s t) : InvOn f f' t s
参数：h : InvOn f' f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem symm (h : InvOn f' f s t) : InvOn f f' t s :=
  ⟨h.right, h.left⟩
/-
**Set.InvOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.InvOn`。
形式化陈述：mono (h : InvOn f' f s t) (hs : s₁ subseteq s) (ht : t₁ subseteq t) : InvO
n f' f s₁ t₁
参数：h : InvOn f' f s t；hs : s₁ subseteq s；ht : t₁ subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.mono`：mono (hf : LeftInvOn f' f s) (ht : s₁ subseteq s) : 
LeftInvOn f' f s₁
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.RightInvOn.mono`：mono (hf : RightInvOn f' f t) (ht : t₁ subseteq t) 
: RightInvOn f' f t₁
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mono (h : InvOn f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : InvOn f' f s₁ t₁ :=
  ⟨h.1.mono hs, h.2.mono ht⟩

/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `mapsTo` arguments can be deduced from
`surjOn` statements using `LeftInvOn.mapsTo` and `RightInvOn.mapsTo`. -/
/-
**Set.InvOn.bijOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.InvOn`。
形式化陈述：bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s) : Bij
On f s t
参数：h : InvOn f' f s t；hf : MapsTo f s t；hf' : MapsTo f' t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.RightInvOn.surjOn`：surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' 
t s) : SurjOn f s t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and
 `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `mapsTo` arguments ca
n be deduced from
`surjOn` statements using `LeftInvOn.mapsTo` and `RightInvOn.mapsTo`.
-/
theorem bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s) : BijOn f s t :=
  ⟨hf, h.left.injOn, h.right.surjOn hf'⟩

end InvOn

end Set

/-! ### `invFunOn` is a left/right inverse -/
namespace Function

variable {s : Set α} {f : α → β} {a : α} {b : β}

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `Function.Embedding.invOfMemRange`. -/
/-
**Function.invFunOn** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：invFunOn [Nonempty α] (f : α -> β) (s : Set α) (b : β) : α
参数：f : α -> β；s : Set α；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the inverse for a function `f` on domain `s`. This function is a right
 inverse of `f`
on `f '' s`. For a computable version, see `Function.Embedding.invOfMemRange`.
-/
noncomputable def invFunOn [Nonempty α] (f : α → β) (s : Set α) (b : β) : α :=
  open scoped Classical in
  if h : ∃ a, a ∈ s ∧ f a = b then Classical.choose h else Classical.choice ‹Nonempty α›

variable [Nonempty α]
/-
**Function.invFunOn_pos** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFunOn_pos (h : exists a in s, f a = b) : invFunOn f s b in s ∧ f (invFu
nOn f s b) = b
参数：h : exists a in s, f a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.invFunOn.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Nonempty
 α] (f : α → β) (s : Set α) (b : β),   Function.invFunOn f s b = if h : ∃ a ∈ s,
 f a = b the…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem invFunOn_pos (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s ∧ f (invFunOn f s b) = b := by
  rw [invFunOn, dif_pos h]
  exact Classical.choose_spec h
/-
**Function.invFunOn_mem** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFunOn_mem (h : exists a in s, f a = b) : invFunOn f s b in s
参数：h : exists a in s, f a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.invFunOn_pos`：invFunOn_pos (h : exists a in s, f a = b) : invFu
nOn f s b in s ∧ f (invFunOn f s b) = b
-/
theorem invFunOn_mem (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s :=
  (invFunOn_pos h).left
/-
**Function.invFunOn_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFunOn_eq (h : exists a in s, f a = b) : f (invFunOn f s b) = b
参数：h : exists a in s, f a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.invFunOn_pos`：invFunOn_pos (h : exists a in s, f a = b) : invFu
nOn f s b in s ∧ f (invFunOn f s b) = b
-/
theorem invFunOn_eq (h : ∃ a ∈ s, f a = b) : f (invFunOn f s b) = b :=
  (invFunOn_pos h).right
/-
**Function.invFunOn_neg** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFunOn_neg (h : ¬exists a in s, f a = b) : invFunOn f s b = Classical.ch
oice ‹Nonempty α›
参数：h : ¬exists a in s, f a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.invFunOn.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Nonempty
 α] (f : α → β) (s : Set α) (b : β),   Function.invFunOn f s b = if h : ∃ a ∈ s,
 f a = b the…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem invFunOn_neg (h : ¬∃ a ∈ s, f a = b) : invFunOn f s b = Classical.choice ‹Nonempty α› := by
  rw [invFunOn, dif_neg h]

@[simp]
/-
**Function.invFunOn_apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFunOn_apply_mem (h : a in s) : invFunOn f s (f a) in s
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.invFunOn_mem`：invFunOn_mem (h : exists a in s, f a = b) : invFu
nOn f s b in s
-/
theorem invFunOn_apply_mem (h : a ∈ s) : invFunOn f s (f a) ∈ s :=
  invFunOn_mem ⟨a, h, rfl⟩
/-
**Function.invFunOn_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：invFunOn_apply_eq (h : a in s) : f (invFunOn f s (f a)) = f a
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.invFunOn_eq`：invFunOn_eq (h : exists a in s, f a = b) : f (invF
unOn f s b) = b
-/
theorem invFunOn_apply_eq (h : a ∈ s) : f (invFunOn f s (f a)) = f a :=
  invFunOn_eq ⟨a, h, rfl⟩

end Function

open Function

namespace Set

variable {s s₁ s₂ : Set α} {t : Set β} {f : α → β}

/-
**Set.InjOn.leftInvOn_invFunOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} [inst : Nonempty α
],   Set.InjOn f s → Set.LeftInvOn (Function.invFunOn f s) f s
参数：Function.invFunOn f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.invFunOn_apply_mem`：invFunOn_apply_mem (h : a in s) : invFunOn 
f s (f a) in s
· 使用定理 `Function.invFunOn_apply_eq`：invFunOn_apply_eq (h : a in s) : f (invFunOn
 f s (f a)) = f a
-/
theorem InjOn.leftInvOn_invFunOn [Nonempty α] (h : InjOn f s) : LeftInvOn (invFunOn f s) f s :=
  fun _a ha => h (invFunOn_apply_mem ha) ha (invFunOn_apply_eq ha)
/-
**Set.InjOn.invFunOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α → β} [inst : Nonemp
ty α],   Set.InjOn f s₂ → s₁ ⊆ s₂ → Function.invFunOn f s₂ '' f '' s₁ = s₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.image_image'`：image_image' (hf : LeftInvOn f' f s) (hs : s
₁ subseteq s) : f' '' f '' s₁ = s₁
· 使用定理 `Set.InjOn.leftInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {f : α → β} [inst : Nonempty α],   Set.InjOn f s → Set.LeftInvOn (Function.inv
FunOn f s) f s
-/
theorem InjOn.invFunOn_image [Nonempty α] (h : InjOn f s₂) (ht : s₁ ⊆ s₂) :
    invFunOn f s₂ '' f '' s₁ = s₁ :=
  h.leftInvOn_invFunOn.image_image' ht
/-
**Set._root_.Function.leftInvOn_invFunOn_of_subset_image_image** 是 Mathlib 中的一个定
理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.leftInvOn_invFunOn_of_subset_image_image [Nonempty α]
    (h : s ⊆ (invFunOn f s) '' f '' s) : LeftInvOn (invFunOn f s) f s :=
  fun x hx ↦ by
    obtain ⟨-, ⟨x, hx', rfl⟩, rfl⟩ := h hx
    rw [invFunOn_apply_eq (f := f) hx']
/-
**Set.injOn_iff_invFunOn_image_image_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injOn_iff_invFunOn_image_image_eq_self [Nonempty α] : InjOn f s ↔ (invFunO
n f s) '' f '' s = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.invFunOn_image`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α
} {f : α → β} [inst : Nonempty α],   Set.InjOn f s₂ → s₁ ⊆ s₂ → Function.invFunO
n f s₂ '' f ''…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `Function.leftInvOn_invFunOn_of_subset_image_image`：∀ {α : Type u_1} {β :
 Type u_2} {s : Set α} {f : α → β} [inst : Nonempty α],   s ⊆ Function.invFunOn 
f s '' f '' s → Set.LeftInvOn (Function…
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem injOn_iff_invFunOn_image_image_eq_self [Nonempty α] :
    InjOn f s ↔ (invFunOn f s) '' f '' s = s :=
  ⟨fun h ↦ h.invFunOn_image Subset.rfl, fun h ↦
    (Function.leftInvOn_invFunOn_of_subset_image_image h.symm.subset).injOn⟩
/-
**Set._root_.Function.invFunOn_injOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.invFunOn_injOn_image [Nonempty α] (f : α → β) (s : Set α) :
    Set.InjOn (invFunOn f s) (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ he
  rw [← invFunOn_apply_eq (f := f) hx, he, invFunOn_apply_eq (f := f) hx']
/-
**Set._root_.Function.invFunOn_image_image_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.invFunOn_image_image_subset [Nonempty α] (f : α → β) (s : Set α) :
    (invFunOn f s) '' f '' s ⊆ s := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact invFunOn_apply_mem hx
/-
**Set.SurjOn.rightInvOn_invFunOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} [inst 
: Nonempty α],   Set.SurjOn f s t → Set.RightInvOn (Function.invFunOn f s) f t
参数：Function.invFunOn f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.invFunOn_eq`：invFunOn_eq (h : exists a in s, f a = b) : f (invF
unOn f s b) = b
-/
theorem SurjOn.rightInvOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    RightInvOn (invFunOn f s) f t := fun _y hy => invFunOn_eq <| h hy
/-
**Set.BijOn.invOn_invFunOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} [inst 
: Nonempty α],   Set.BijOn f s t → Set.InvOn (Function.invFunOn f s) f s t
参数：Function.invFunOn f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.leftInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {f : α → β} [inst : Nonempty α],   Set.InjOn f s → Set.LeftInvOn (Function.inv
FunOn f s) f s
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.SurjOn.rightInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.RightI
nvOn (Function.invFu…
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem BijOn.invOn_invFunOn [Nonempty α] (h : BijOn f s t) : InvOn (invFunOn f s) f s t :=
  ⟨h.injOn.leftInvOn_invFunOn, h.surjOn.rightInvOn_invFunOn⟩
/-
**Set.SurjOn.invOn_invFunOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} [inst 
: Nonempty α],   Set.SurjOn f s t → Set.InvOn (Function.invFunOn f s) f (Functio
n.invFunOn f s '' t) t
参数：Function.invFunOn f s；Function.invFunOn f s '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.SurjOn.rightInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.RightI
nvOn (Function.invFu…
-/
theorem SurjOn.invOn_invFunOn [Nonempty α] (h : SurjOn f s t) :
    InvOn (invFunOn f s) f (invFunOn f s '' t) t := by
  refine ⟨?_, h.rightInvOn_invFunOn⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.rightInvOn_invFunOn hy]
/-
**Set.SurjOn.mapsTo_invFunOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} [inst 
: Nonempty α],   Set.SurjOn f s t → Set.MapsTo (Function.invFunOn f s) t s
参数：Function.invFunOn f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Function.invFunOn_mem`：invFunOn_mem (h : exists a in s, f a = b) : invFu
nOn f s b in s
-/
theorem SurjOn.mapsTo_invFunOn [Nonempty α] (h : SurjOn f s t) : MapsTo (invFunOn f s) t s :=
  fun _y hy => mem_preimage.2 <| invFunOn_mem <| h hy

/-- This lemma is a special case of `rightInvOn_invFunOn.image_image'`; it may make more sense
to use the other lemma directly in an application. -/
/-
**Set.SurjOn.image_invFunOn_image_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjO
n`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} [inst 
: Nonempty α] {r : Set β},   Set.SurjOn f s t → r ⊆ t → f '' Function.invFunOn f
 s '' r = r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.image_image'`：image_image' (hf : LeftInvOn f' f s) (hs : s
₁ subseteq s) : f' '' f '' s₁ = s₁
· 使用定理 `Set.SurjOn.rightInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.RightI
nvOn (Function.invFu…

--- 原说明 ---
This lemma is a special case of `rightInvOn_invFunOn.image_image'`; it may make 
more sense
to use the other lemma directly in an application.
-/
theorem SurjOn.image_invFunOn_image_of_subset [Nonempty α] {r : Set β} (hf : SurjOn f s t)
    (hrt : r ⊆ t) : f '' f.invFunOn s '' r = r :=
  hf.rightInvOn_invFunOn.image_image' hrt

/-- This lemma is a special case of `rightInvOn_invFunOn.image_image`; it may make more sense
to use the other lemma directly in an application. -/
/-
**Set.SurjOn.image_invFunOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} [inst 
: Nonempty α],   Set.SurjOn f s t → f '' Function.invFunOn f s '' t = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.image_image`：image_image (hf : LeftInvOn f' f s) : f' '' f
 '' s = s
· 使用定理 `Set.SurjOn.rightInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.RightI
nvOn (Function.invFu…

--- 原说明 ---
This lemma is a special case of `rightInvOn_invFunOn.image_image`; it may make m
ore sense
to use the other lemma directly in an application.
-/
theorem SurjOn.image_invFunOn_image [Nonempty α] (hf : SurjOn f s t) :
    f '' f.invFunOn s '' t = t :=
  hf.rightInvOn_invFunOn.image_image
/-
**Set.SurjOn.bijOn_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} [inst 
: Nonempty α],   Set.SurjOn f s t → Set.BijOn f (Function.invFunOn f s '' t) t
参数：Function.invFunOn f s '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InvOn.bijOn`：bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : M
apsTo f' t s) : BijOn f s t
· 使用定理 `Set.SurjOn.invOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {
t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.InvOn (Func
tion.invFunOn f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.SurjOn.rightInvOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.RightI
nvOn (Function.invFu…
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem SurjOn.bijOn_subset [Nonempty α] (h : SurjOn f s t) : BijOn f (invFunOn f s '' t) t := by
  refine h.invOn_invFunOn.bijOn ?_ (mapsTo_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.rightInvOn_invFunOn hy]
/-
**Set.surjOn_iff_exists_bijOn_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：surjOn_iff_exists_bijOn_subset : SurjOn f s t ↔ exists s' subseteq s, BijO
n f s' t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Set.bijOn_empty`：bijOn_empty (f : α -> β) : BijOn f ∅ ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.SurjOn.comap_nonempty`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {
t : Set β} {f : α → β}, Set.SurjOn f s t → t.Nonempty → s.Nonempty
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.SurjOn.mapsTo_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} 
{t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.MapsTo (Fu
nction.invFunOn …
· 使用定理 `Set.SurjOn.bijOn_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.BijOn f (Func
tion.invFunOn…
· 使用定理 `Set.SurjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂
 t₁
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem surjOn_iff_exists_bijOn_subset : SurjOn f s t ↔ ∃ s' ⊆ s, BijOn f s' t := by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bijOn_empty f⟩
    · intro h
      have : Nonempty α := ⟨Classical.choose (h.comap_nonempty ht)⟩
      exact ⟨_, h.mapsTo_invFunOn.image_subset, h.bijOn_subset⟩
  · rintro ⟨s', hs', hfs'⟩
    exact hfs'.surjOn.mono hs' (Subset.refl _)

alias ⟨SurjOn.exists_bijOn_subset, _⟩ := Set.surjOn_iff_exists_bijOn_subset

variable (f s)
/-
**Set.exists_subset_bijOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_subset_bijOn : exists s' subseteq s, BijOn f s' (f '' s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.surjOn_iff_exists_bijOn_subset`：surjOn_iff_exists_bijOn_subset : Sur
jOn f s t ↔ exists s' subseteq s, BijOn f s' t
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
-/
lemma exists_subset_bijOn : ∃ s' ⊆ s, BijOn f s' (f '' s) :=
  surjOn_iff_exists_bijOn_subset.mp (surjOn_image f s)
/-
**Set.exists_image_eq_and_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_image_eq_and_injOn : exists u, f '' u = f '' s ∧ InjOn f u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.exists_subset_bijOn`：exists_subset_bijOn : exists s' subseteq s, Bij
On f s' (f '' s)
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
-/
lemma exists_image_eq_and_injOn : ∃ u, f '' u = f '' s ∧ InjOn f u :=
  let ⟨u, _, hfu⟩ := exists_subset_bijOn s f
  ⟨u, hfu.image_eq, hfu.injOn⟩

variable {f s}
/-
**Set.exists_image_eq_injOn_of_subset_range** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_image_eq_injOn_of_subset_range (ht : t subseteq range f) : exists s
, f '' s = t ∧ InjOn f s
参数：ht : t subseteq range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.exists_image_eq_and_injOn`：exists_image_eq_and_injOn : exists u, f '
' u = f '' s ∧ InjOn f u
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
-/
lemma exists_image_eq_injOn_of_subset_range (ht : t ⊆ range f) :
    ∃ s, f '' s = t ∧ InjOn f s :=
  image_preimage_eq_of_subset ht ▸ exists_image_eq_and_injOn _ _

/-- If `f` maps `s` bijectively to `t` and a set `t'` is contained in the image of some `s₁ ⊇ s`,
then `s₁` has a subset containing `s` that `f` maps bijectively to `t'`. -/
/-
**Set.BijOn.exists_extend_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set α} {t : Set β} {f : α → β} {t'
 : Set β},   Set.BijOn f s t → s ⊆ s₁ → t ⊆ t' → Set.SurjOn f s₁ t' → ∃ s', s ⊆ 
s' ∧ s' ⊆ s₁ ∧ Set.BijOn f s' t'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.exists_subset_bijOn`：exists_subset_bijOn : exists s' subseteq s, Bij
On f s' (f '' s)
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
· 使用定理 `Set.image_sdiff_preimage`：image_sdiff_preimage {f : α -> β} {s : Set α} 
{t : Set β} : f '' (s \ f ⁻¹' t) = f '' s \ t
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.injOn_union`：injOn_union (h : Disjoint s₁ s₂) : InjOn f (s₁ union s₂
) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ forall x in s₁, forall y in s₂, f x != f y
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t

--- 原说明 ---
If `f` maps `s` bijectively to `t` and a set `t'` is contained in the image of s
ome `s₁ ⊇ s`,
then `s₁` has a subset containing `s` that `f` maps bijectively to `t'`.
-/
theorem BijOn.exists_extend_of_subset {t' : Set β} (h : BijOn f s t) (hss₁ : s ⊆ s₁) (htt' : t ⊆ t')
    (ht' : SurjOn f s₁ t') : ∃ s', s ⊆ s' ∧ s' ⊆ s₁ ∧ Set.BijOn f s' t' := by
  obtain ⟨r, hrss, hbij⟩ := exists_subset_bijOn ((s₁ ∩ f ⁻¹' t') \ f ⁻¹' t) f
  rw [image_sdiff_preimage, image_inter_preimage] at hbij
  refine ⟨s ∪ r, subset_union_left, ?_, ?_, ?_, fun y hyt' ↦ ?_⟩
  · exact union_subset hss₁ <| hrss.trans <| sdiff_subset.trans inter_subset_left
  · rw [mapsTo_iff_image_subset, image_union, hbij.image_eq, h.image_eq, union_subset_iff]
    exact ⟨htt', sdiff_subset.trans inter_subset_right⟩
  · rw [injOn_union, and_iff_right h.injOn, and_iff_right hbij.injOn]
    · refine fun x hxs y hyr hxy ↦ (hrss hyr).2 ?_
      rw [← h.image_eq]
      exact ⟨x, hxs, hxy⟩
    exact (subset_sdiff.1 hrss).2.symm.mono_left h.mapsTo
  rw [image_union, h.image_eq, hbij.image_eq, union_sdiff_self]
  exact .inr ⟨ht' hyt', hyt'⟩

/-- If `f` maps `s` bijectively to `t`, and `t'` is a superset of `t` contained in the range of `f`,
then `f` maps some superset of `s` bijectively to `t'`. -/
/-
**Set.BijOn.exists_extend** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {t' : 
Set β},   Set.BijOn f s t → t ⊆ t' → t' ⊆ Set.range f → ∃ s', s ⊆ s' ∧ Set.BijOn
 f s' t'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.BijOn.exists_extend_of_subset`：∀ {α : Type u_1} {β : Type u_2} {s s₁
 : Set α} {t : Set β} {f : α → β} {t' : Set β},   Set.BijOn f s t → s ⊆ s₁ → t ⊆
 t' → Set.SurjOn f s₁ t…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
If `f` maps `s` bijectively to `t`, and `t'` is a superset of `t` contained in t
he range of `f`,
then `f` maps some superset of `s` bijectively to `t'`.
-/
theorem BijOn.exists_extend {t' : Set β} (h : BijOn f s t) (htt' : t ⊆ t') (ht' : t' ⊆ range f) :
    ∃ s', s ⊆ s' ∧ BijOn f s' t' := by
  simpa using h.exists_extend_of_subset (subset_univ s) htt' (by simpa [SurjOn])
/-
**Set.InjOn.exists_subset_injOn_subset_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.I
njOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {r : Set α},   Set
.InjOn f r → r ⊆ s → ∃ u, r ⊆ u ∧ u ⊆ s ∧ f '' u = f '' s ∧ Set.InjOn f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.exists_extend_of_subset`：∀ {α : Type u_1} {β : Type u_2} {s s₁
 : Set α} {t : Set β} {f : α → β} {t' : Set β},   Set.BijOn f s t → s ⊆ s₁ → t ⊆
 t' → Set.SurjOn f s₁ t…
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
-/
theorem InjOn.exists_subset_injOn_subset_range_eq {r : Set α} (hinj : InjOn f r) (hrs : r ⊆ s) :
    ∃ u : Set α, r ⊆ u ∧ u ⊆ s ∧ f '' u = f '' s ∧ InjOn f u := by
  obtain ⟨u, hru, hus, h⟩ := hinj.bijOn_image.exists_extend_of_subset hrs
    (image_mono hrs) Subset.rfl
  exact ⟨u, hru, hus, h.image_eq, h.injOn⟩
/-
**Set.preimage_invFun_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_invFun_of_mem [n : Nonempty α] {f : α -> β} (hf : Injective f) {s
 : Set α} (h : Classical.choice n in s) : invFun f ⁻¹' s = f '' s union (range f
)ᶜ
参数：hf : Injective f；h : Classical.choice n in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Function.invFun_neg`：invFun_neg (h : ¬exists a, f a = b) : invFun f b = 
Classical.choice ‹_›
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem preimage_invFun_of_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∈ s) : invFun f ⁻¹' s = f '' s ∪ (range f)ᶜ := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · simp only [mem_preimage, mem_union, mem_compl_iff, mem_range_self, not_true, or_false,
      leftInverse_invFun hf _, hf.mem_set_image]
  · simp only [mem_preimage, invFun_neg hx, h, hx, mem_union, mem_compl_iff, not_false_iff, or_true]
/-
**Set.preimage_invFun_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_invFun_of_notMem [n : Nonempty α] {f : α -> β} (hf : Injective f)
 {s : Set α} (h : Classical.choice n ∉ s) : invFun f ⁻¹' s = f '' s
参数：hf : Injective f；h : Classical.choice n ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.invFun_neg`：invFun_neg (h : ¬exists a, f a = b) : invFun f b = 
Classical.choice ‹_›
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_invFun_of_notMem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∉ s) : invFun f ⁻¹' s = f '' s := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, leftInverse_invFun hf, hf.mem_set_image]
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, invFun_neg hx, h, this]
/-
**Set.BijOn.symm** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β} {g : β
 → α},   Set.InvOn f g t s → Set.BijOn f s t → Set.BijOn g t s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.RightInvOn.mapsTo`：mapsTo (h : RightInvOn f' f t) (hf : SurjOn f' t 
s) : MapsTo f s t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.RightInvOn.surjOn`：surjOn (hf : RightInvOn f' f t) (hf' : MapsTo f' 
t s) : SurjOn f s t
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
-/
lemma BijOn.symm {g : β → α} (h : InvOn f g t s) (hf : BijOn f s t) : BijOn g t s :=
  ⟨h.2.mapsTo hf.surjOn, h.1.injOn, h.2.surjOn hf.mapsTo⟩
/-
**Set.bijOn_comm** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：bijOn_comm {g : β -> α} (h : InvOn f g t s) : BijOn f s t ↔ BijOn g t s
参数：h : InvOn f g t s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} 
{f : α → β} {g : β → α},   Set.InvOn f g t s → Set.BijOn f s t → Set.BijOn g t s
· 使用定理 `Set.InvOn.symm`：symm (h : InvOn f' f s t) : InvOn f f' t s
-/
lemma bijOn_comm {g : β → α} (h : InvOn f g t s) : BijOn f s t ↔ BijOn g t s :=
  ⟨BijOn.symm h, BijOn.symm h.symm⟩

/-- If `t ⊆ f '' s`, there exists a preimage of `t` under `f` contained in `s` such that
`f` restricted to `u` is injective. -/
/-
**Set.SurjOn.exists_subset_injOn_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f : α → β},   Set
.SurjOn f s t → ∃ u ⊆ s, Set.InjOn f u ∧ f '' u = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `t ⊆ f '' s`, there exists a preimage of `t` under `f` contained in `s` such 
that
`f` restricted to `u` is injective.
-/
lemma SurjOn.exists_subset_injOn_image_eq (hfs : s.SurjOn f t) :
    ∃ u ⊆ s, u.InjOn f ∧ f '' u = t := by
  choose x hmem heq using hfs
  exact ⟨range (fun a : t ↦ x a.2), by grind, fun _ ↦ by grind, by aesop⟩

end Set

namespace Function

open Set

variable {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : Set α}

/-
**Function.Injective.comp_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {g : β → γ} {s 
: Set α},   Function.Injective g → Set.InjOn f s → Set.InjOn (g ∘ f) s
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {f : α → β} {g : β → γ},   Set.InjOn g t → Set.InjOn f s → Set.Ma
psTo…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem Injective.comp_injOn (hg : Injective g) (hf : s.InjOn f) : s.InjOn (g ∘ f) :=
  hg.injOn.comp hf (mapsTo_univ _ _)
/-
**Function.LeftInverse.leftInvOn** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInverse
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {g : β → α}, Function.LeftInve
rse f g → ∀ (s : Set β), Set.LeftInvOn f g s
参数：s : Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LeftInverse.leftInvOn {g : β → α} (h : LeftInverse f g) (s : Set β) : LeftInvOn f g s :=
  fun x _ => h x
/-
**Function.RightInverse.rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `Function.RightInve
rse`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {g : β → α}, Function.RightInv
erse f g → ∀ (s : Set α), Set.RightInvOn f g s
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RightInverse.rightInvOn {g : β → α} (h : RightInverse f g) (s : Set α) :
    RightInvOn f g s := fun x _ => h x
/-
**Function.LeftInverse.rightInvOn_range** 是 Mathlib 中的一个定理，位于命名空间 `Function.Left
Inverse`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {g : β → α}, Function.LeftInve
rse f g → Set.RightInvOn f g (Set.range g)
参数：Set.range g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem LeftInverse.rightInvOn_range {g : β → α} (h : LeftInverse f g) :
    RightInvOn f g (range g) :=
  forall_mem_range.2 fun i => congr_arg g (h i)

namespace Semiconj

/-
**Function.Semiconj.mapsTo_image** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：mapsTo_image (h : Semiconj f fa fb) (ha : MapsTo fa s t) : MapsTo fb (f ''
 s) (f '' t)
参数：h : Semiconj f fa fb；ha : MapsTo fa s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapsTo_image (h : Semiconj f fa fb) (ha : MapsTo fa s t) : MapsTo fb (f '' s) (f '' t) :=
  fun _y ⟨x, hx, hy⟩ => hy ▸ ⟨fa x, ha hx, h x⟩
/-
**Function.Semiconj.mapsTo_image_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semic
onj`。
形式化陈述：mapsTo_image_right {t : Set β} (h : Semiconj f fa fb) (hst : MapsTo f s t)
 : MapsTo f (fa '' s) (fb '' t)
参数：h : Semiconj f fa fb；hst : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_image_iff`：mapsTo_image_iff {f : α -> β} {g : γ -> α} {s : Se
t γ} {t : Set β} : MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mapsTo_image_right {t : Set β} (h : Semiconj f fa fb) (hst : MapsTo f s t) :
    MapsTo f (fa '' s) (fb '' t) :=
  mapsTo_image_iff.2 fun x hx ↦ ⟨f x, hst hx, (h x).symm⟩
/-
**Function.Semiconj.mapsTo_range** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：mapsTo_range (h : Semiconj f fa fb) : MapsTo fb (range f) (range f)
参数：h : Semiconj f fa fb。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapsTo_range (h : Semiconj f fa fb) : MapsTo fb (range f) (range f) := fun _y ⟨x, hy⟩ =>
  hy ▸ ⟨fa x, h x⟩
/-
**Function.Semiconj.surjOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：surjOn_image (h : Semiconj f fa fb) (ha : SurjOn fa s t) : SurjOn fb (f ''
 s) (f '' t)
参数：h : Semiconj f fa fb；ha : SurjOn fa s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem surjOn_image (h : Semiconj f fa fb) (ha : SurjOn fa s t) : SurjOn fb (f '' s) (f '' t) := by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)
/-
**Function.Semiconj.surjOn_range** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：surjOn_range (h : Semiconj f fa fb) (ha : Surjective fa) : SurjOn fb (rang
e f) (range f)
参数：h : Semiconj f fa fb；ha : Surjective fa。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Semiconj.surjOn_image`：surjOn_image (h : Semiconj f fa fb) (ha 
: SurjOn fa s t) : SurjOn fb (f '' s) (f '' t)
· 使用定理 `Function.Surjective.surjOn`：∀ {α : Type u_1} {β : Type u_2} {t : Set β} 
{f : α → β}, Function.Surjective f → Set.SurjOn f Set.univ t
-/
theorem surjOn_range (h : Semiconj f fa fb) (ha : Surjective fa) :
    SurjOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.surjOn_image ha.surjOn
/-
**Function.Semiconj.injOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：injOn_image (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' 
s)) : InjOn fb (f '' s)
参数：h : Semiconj f fa fb；ha : InjOn fa s；hf : InjOn f (fa '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
-/
theorem injOn_image (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s)) :
    InjOn fb (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_arg f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)
/-
**Function.Semiconj.injOn_range** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：injOn_range (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (rang
e fa)) : InjOn fb (range f)
参数：h : Semiconj f fa fb；ha : Injective fa；hf : InjOn f (range fa)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Semiconj.injOn_image`：injOn_image (h : Semiconj f fa fb) (ha : 
InjOn fa s) (hf : InjOn f (fa '' s)) : InjOn fb (f '' s)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem injOn_range (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (range fa)) :
    InjOn fb (range f) := by
  rw [← image_univ] at *
  exact h.injOn_image ha.injOn hf
/-
**Function.Semiconj.bijOn_image** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：bijOn_image (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t) : 
BijOn fb (f '' s) (f '' t)
参数：h : Semiconj f fa fb；ha : BijOn fa s t；hf : InjOn f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.mapsTo_image`：mapsTo_image (h : Semiconj f fa fb) (ha 
: MapsTo fa s t) : MapsTo fb (f '' s) (f '' t)
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Function.Semiconj.injOn_image`：injOn_image (h : Semiconj f fa fb) (ha : 
InjOn fa s) (hf : InjOn f (fa '' s)) : InjOn fb (f '' s)
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Function.Semiconj.surjOn_image`：surjOn_image (h : Semiconj f fa fb) (ha 
: SurjOn fa s t) : SurjOn fb (f '' s) (f '' t)
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem bijOn_image (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t) :
    BijOn fb (f '' s) (f '' t) :=
  ⟨h.mapsTo_image ha.mapsTo, h.injOn_image ha.injOn (ha.image_eq.symm ▸ hf),
    h.surjOn_image ha.surjOn⟩
/-
**Function.Semiconj.bijOn_range** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：bijOn_range (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f) 
: BijOn fb (range f) (range f)
参数：h : Semiconj f fa fb；ha : Bijective fa；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Function.Semiconj.bijOn_image`：bijOn_image (h : Semiconj f fa fb) (ha : 
BijOn fa s t) (hf : InjOn f t) : BijOn fb (f '' s) (f '' t)
· 使用定理 `Function.Bijective.bijOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β}, Function.Bijective f → Set.BijOn f Set.univ Set.univ
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem bijOn_range (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f) :
    BijOn fb (range f) (range f) := by
  rw [← image_univ]
  exact h.bijOn_image ha.bijOn_univ hf.injOn
/-
**Function.Semiconj.mapsTo_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj
`。
形式化陈述：mapsTo_preimage (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t) 
: MapsTo fa (f ⁻¹' s) (f ⁻¹' t)
参数：h : Semiconj f fa fb；hb : MapsTo fb s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem mapsTo_preimage (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t) :
    MapsTo fa (f ⁻¹' s) (f ⁻¹' t) := fun x hx => by simp only [mem_preimage, h x, hb hx]
/-
**Function.Semiconj.injOn_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`
。
形式化陈述：injOn_preimage (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s) (hf : 
InjOn f (f ⁻¹' s)) : InjOn fa (f ⁻¹' s)
参数：h : Semiconj f fa fb；hb : InjOn fb s；hf : InjOn f (f ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
-/
theorem injOn_preimage (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s)
    (hf : InjOn f (f ⁻¹' s)) : InjOn fa (f ⁻¹' s) := by
  intro x hx y hy H
  have := congr_arg f H
  rw [h.eq, h.eq] at this
  exact hf hx hy (hb hx hy this)

end Semiconj

/-
**Function.update_comp_eq_of_notMem_range'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_comp_eq_of_notMem_range' {α : Sort*} {β : Type*} {γ : β -> Sort*} [
DecidableEq β] (g : forall b, γ b) {f : α -> β} {i : β} (a : γ i) (h : i ∉ Set.r
ange f) : (fun j => update g i a (f j)) = fun j => g (f j)
参数：g : forall b, γ b；a : γ i；h : i ∉ Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_comp_eq_of_forall_ne'`：update_comp_eq_of_forall_ne' {α'}
 (g : forall a, β a) {f : α' -> α} {i : α} (a : β i) (h : forall x, f x != i) : 
(fun j => (update g i a) (f…
-/
theorem update_comp_eq_of_notMem_range' {α : Sort*} {β : Type*} {γ : β → Sort*} [DecidableEq β]
    (g : ∀ b, γ b) {f : α → β} {i : β} (a : γ i) (h : i ∉ Set.range f) :
    (fun j => update g i a (f j)) = fun j => g (f j) :=
  (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩

/-- Non-dependent version of `Function.update_comp_eq_of_notMem_range'` -/
/-
**Function.update_comp_eq_of_notMem_range** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_comp_eq_of_notMem_range {α : Sort*} {β : Type*} {γ : Sort*} [Decida
bleEq β] (g : β -> γ) {f : α -> β} {i : β} (a : γ) (h : i ∉ Set.range f) : updat
e g i a ∘ f = g ∘ f
参数：g : β -> γ；a : γ；h : i ∉ Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_comp_eq_of_notMem_range'`：update_comp_eq_of_notMem_range
' {α : Sort*} {β : Type*} {γ : β -> Sort*} [DecidableEq β] (g : forall b, γ b) {
f : α -> β} {i : β} (a : γ i) …

--- 原说明 ---
Non-dependent version of `Function.update_comp_eq_of_notMem_range'`
-/
theorem update_comp_eq_of_notMem_range {α : Sort*} {β : Type*} {γ : Sort*} [DecidableEq β]
    (g : β → γ) {f : α → β} {i : β} (a : γ) (h : i ∉ Set.range f) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_notMem_range' g a h
/-
**Function.insert_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：insert_injOn (s : Set α) : sᶜ.InjOn fun a => insert a s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.insert_inj`：insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = 
b
-/
theorem insert_injOn (s : Set α) : sᶜ.InjOn fun a => insert a s := fun _a ha _ _ =>
  (insert_inj ha).1
/-
**Function.apply_eq_of_range_eq_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：apply_eq_of_range_eq_singleton {f : α -> β} {b : β} (h : range f = {b}) (a
 : α) : f a = b
参数：h : range f = {b}；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma apply_eq_of_range_eq_singleton {f : α → β} {b : β} (h : range f = {b}) (a : α) :
    f a = b := by
  simpa only [h, mem_singleton_iff] using mem_range_self (f := f) a

end Function

/-! ### Equivalences, permutations -/
namespace Set

variable {p : β → Prop} [DecidablePred p] {f : α ≃ Subtype p} {g g₁ g₂ : Perm α} {s t : Set α}

/-
**Set.MapsTo.extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p : β → Prop} [inst : DecidablePred p] {f
 : α ≃ Subtype p} {g : Equiv.Perm α}   {s t : Set α}, Set.MapsTo (⇑g) s t → Set.
MapsTo (⇑(g.extendDomain f)) (Subtype.val ∘ ⇑f '' s) (Subtype.val ∘ ⇑f '' t)
参数：⇑g；⇑(g.extendDomain f)；Subtype.val ∘ ⇑f '' s；Subtype.val ∘ ⇑f '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.extendDomain_apply_image`：∀ {α' : Type u_9} {β' : Type u_10} 
(e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p
)   (a : α'), (e.extendDo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma MapsTo.extendDomain (h : MapsTo g s t) :
    MapsTo (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩; exact ⟨_, h ha, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩
/-
**Set.SurjOn.extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p : β → Prop} [inst : DecidablePred p] {f
 : α ≃ Subtype p} {g : Equiv.Perm α}   {s t : Set α}, Set.SurjOn (⇑g) s t → Set.
SurjOn (⇑(g.extendDomain f)) (Subtype.val ∘ ⇑f '' s) (Subtype.val ∘ ⇑f '' t)
参数：⇑g；⇑(g.extendDomain f)；Subtype.val ∘ ⇑f '' s；Subtype.val ∘ ⇑f '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.extendDomain_apply_image`：∀ {α' : Type u_9} {β' : Type u_10} 
(e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p
)   (a : α'), (e.extendDo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma SurjOn.extendDomain (h : SurjOn g s t) :
    SurjOn (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, rfl⟩ := h ha
  exact ⟨_, ⟨_, hb, rfl⟩, by simp_rw [Function.comp_apply, extendDomain_apply_image]⟩
/-
**Set.BijOn.extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p : β → Prop} [inst : DecidablePred p] {f
 : α ≃ Subtype p} {g : Equiv.Perm α}   {s t : Set α}, Set.BijOn (⇑g) s t → Set.B
ijOn (⇑(g.extendDomain f)) (Subtype.val ∘ ⇑f '' s) (Subtype.val ∘ ⇑f '' t)
参数：⇑g；⇑(g.extendDomain f)；Subtype.val ∘ ⇑f '' s；Subtype.val ∘ ⇑f '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.extendDomain`：∀ {α : Type u_1} {β : Type u_2} {p : β → Prop} 
[inst : DecidablePred p] {f : α ≃ Subtype p} {g : Equiv.Perm α}   {s t : Set α},
 Set.MapsTo (…
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Set.SurjOn.extendDomain`：∀ {α : Type u_1} {β : Type u_2} {p : β → Prop} 
[inst : DecidablePred p] {f : α ≃ Subtype p} {g : Equiv.Perm α}   {s t : Set α},
 Set.SurjOn (…
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
protected lemma BijOn.extendDomain (h : BijOn g s t) :
    BijOn (g.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) :=
  ⟨h.mapsTo.extendDomain, (g.extendDomain f).injective.injOn, h.surjOn.extendDomain⟩
/-
**Set.LeftInvOn.extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p : β → Prop} [inst : DecidablePred p] {f
 : α ≃ Subtype p} {g₁ g₂ : Equiv.Perm α}   {s : Set α},   Set.LeftInvOn (⇑g₁) (⇑
g₂) s → Set.LeftInvOn (⇑(g₁.extendDomain f)) (⇑(g₂.extendDomain f)) (Subtype.val
 ∘ ⇑f '' s)
参数：⇑g₁；⇑g₂；⇑(g₁.extendDomain f)；⇑(g₂.extendDomain f)；Subtype.val ∘ ⇑f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.Perm.extendDomain_apply_image`：∀ {α' : Type u_9} {β' : Type u_10} 
(e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p
)   (a : α'), (e.extendDo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma LeftInvOn.extendDomain (h : LeftInvOn g₁ g₂ s) :
    LeftInvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' s) := by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]
/-
**Set.RightInvOn.extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p : β → Prop} [inst : DecidablePred p] {f
 : α ≃ Subtype p} {g₁ g₂ : Equiv.Perm α}   {t : Set α},   Set.RightInvOn (⇑g₁) (
⇑g₂) t → Set.RightInvOn (⇑(g₁.extendDomain f)) (⇑(g₂.extendDomain f)) (Subtype.v
al ∘ ⇑f '' t)
参数：⇑g₁；⇑g₂；⇑(g₁.extendDomain f)；⇑(g₂.extendDomain f)；Subtype.val ∘ ⇑f '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.Perm.extendDomain_apply_image`：∀ {α' : Type u_9} {β' : Type u_10} 
(e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p
)   (a : α'), (e.extendDo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma RightInvOn.extendDomain (h : RightInvOn g₁ g₂ t) :
    RightInvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' t) := by
  rintro _ ⟨a, ha, rfl⟩; simp_rw [Function.comp_apply, extendDomain_apply_image, h ha]
/-
**Set.InvOn.extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Set.InvOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p : β → Prop} [inst : DecidablePred p] {f
 : α ≃ Subtype p} {g₁ g₂ : Equiv.Perm α}   {s t : Set α},   Set.InvOn (⇑g₁) (⇑g₂
) s t →     Set.InvOn (⇑(g₁.extendDomain f)) (⇑(g₂.extendDomain f)) (Subtype.val
 ∘ ⇑f '' s) (Subtype.val ∘ ⇑f '' t)
参数：⇑g₁；⇑g₂；⇑(g₁.extendDomain f)；⇑(g₂.extendDomain f)；Subtype.val ∘ ⇑f '' s；Subty
pe.val ∘ ⇑f '' t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.extendDomain`：∀ {α : Type u_1} {β : Type u_2} {p : β → Pro
p} [inst : DecidablePred p] {f : α ≃ Subtype p} {g₁ g₂ : Equiv.Perm α}   {s : Se
t α},   Set.Left…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.RightInvOn.extendDomain`：∀ {α : Type u_1} {β : Type u_2} {p : β → Pr
op} [inst : DecidablePred p] {f : α ≃ Subtype p} {g₁ g₂ : Equiv.Perm α}   {t : S
et α},   Set.Righ…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma InvOn.extendDomain (h : InvOn g₁ g₂ s t) :
    InvOn (g₁.extendDomain f) (g₂.extendDomain f) ((↑) ∘ f '' s) ((↑) ∘ f '' t) :=
  ⟨h.1.extendDomain, h.2.extendDomain⟩

end Set

namespace Set

section Prod

variable {α β₁ β₂ : Type*} {s : Set α} {t₁ : Set β₁} {t₂ : Set β₂}
  {f₁ : α → β₁} {f₂ : α → β₂} {g₁ : β₁ → α} {g₂ : β₂ → α}

/-
**Set.InjOn.left_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_7} {β₁ : Type u_8} {β₂ : Type u_9} {s : Set α} {f₁ : α → β₁}
 {f₂ : α → β₂},   Set.InjOn f₁ s → Set.InjOn (fun x => (f₁ x, f₂ x)) s
参数：fun x => (f₁ x, f₂ x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
lemma InjOn.left_prodMk (h₁ : s.InjOn f₁) : s.InjOn fun x ↦ (f₁ x, f₂ x) :=
  fun _ hx _ hy h => h₁ hx hy (Prod.ext_iff.1 h).1
/-
**Set.InjOn.right_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_7} {β₁ : Type u_8} {β₂ : Type u_9} {s : Set α} {f₁ : α → β₁}
 {f₂ : α → β₂},   Set.InjOn f₂ s → Set.InjOn (fun x => (f₁ x, f₂ x)) s
参数：fun x => (f₁ x, f₂ x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
lemma InjOn.right_prodMk (h₂ : s.InjOn f₂) : s.InjOn fun x ↦ (f₁ x, f₂ x) :=
  fun _ hx _ hy h => h₂ hx hy (Prod.ext_iff.1 h).2
/-
**Set.prod_surjOn_fst** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：prod_surjOn_fst (h : t₂.Nonempty) : (t₁ ×ˢ t₂).SurjOn Prod.fst t₁
参数：h : t₂.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma prod_surjOn_fst (h : t₂.Nonempty) : (t₁ ×ˢ t₂).SurjOn Prod.fst t₁ :=
  fun _ h => by simpa [h]
/-
**Set.prod_surjOn_snd** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：prod_surjOn_snd (h : t₁.Nonempty) : (t₁ ×ˢ t₂).SurjOn Prod.snd t₂
参数：h : t₁.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma prod_surjOn_snd (h : t₁.Nonempty) : (t₁ ×ˢ t₂).SurjOn Prod.snd t₂ :=
  fun _ h => by simpa [h]
/-
**Set.prod_surjOn_fst_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：prod_surjOn_fst_iff : (t₁ ×ˢ t₂).SurjOn Prod.fst t₁ ↔ t₁ = ∅ ∨ t₂.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma prod_surjOn_fst_iff : (t₁ ×ˢ t₂).SurjOn Prod.fst t₁ ↔ t₁ = ∅ ∨ t₂.Nonempty :=
  ⟨by by_contra!; aesop, by simp +contextual [or_imp, prod_surjOn_fst]⟩
/-
**Set.prod_surjOn_snd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：prod_surjOn_snd_iff : (t₁ ×ˢ t₂).SurjOn Prod.snd t₂ ↔ t₁.Nonempty ∨ t₂ = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma prod_surjOn_snd_iff : (t₁ ×ˢ t₂).SurjOn Prod.snd t₂ ↔ t₁.Nonempty ∨ t₂ = ∅ :=
  ⟨by by_contra!; aesop, by simp +contextual [or_imp, prod_surjOn_snd]⟩
/-
**Set.MapsTo.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_7} {β₁ : Type u_8} {β₂ : Type u_9} {s : Set α} {t₁ : Set β₁}
 {t₂ : Set β₂} {f₁ : α → β₁} {f₂ : α → β₂},   Set.MapsTo f₁ s t₁ → Set.MapsTo f₂
 s t₂ → Set.MapsTo (fun x => (f₁ x, f₂ x)) s (t₁ ×ˢ t₂)
参数：fun x => (f₁ x, f₂ x)；t₁ ×ˢ t₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MapsTo.prodMk (h₁ : MapsTo f₁ s t₁) (h₂ : MapsTo f₂ s t₂) :
    MapsTo (fun x => (f₁ x, f₂ x)) s (t₁ ×ˢ t₂) :=
  fun _ hx => ⟨h₁ hx, h₂ hx⟩
/-
**Set.LeftInvOn.left_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：∀ {α : Type u_7} {β₁ : Type u_8} {β₂ : Type u_9} {s : Set α} {f₁ : α → β₁}
 {f₂ : α → β₂} {g₁ : β₁ → α},   Set.LeftInvOn g₁ f₁ s → Set.LeftInvOn (fun x => 
g₁ x.1) (fun x => (f₁ x, f₂ x)) s
参数：fun x => g₁ x.1；fun x => (f₁ x, f₂ x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LeftInvOn.left_prodMk (h₁ : LeftInvOn g₁ f₁ s) :
    LeftInvOn (fun x ↦ g₁ x.1) (fun x ↦ (f₁ x, f₂ x)) s := h₁
/-
**Set.LeftInvOn.right_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：∀ {α : Type u_7} {β₁ : Type u_8} {β₂ : Type u_9} {s : Set α} {f₁ : α → β₁}
 {f₂ : α → β₂} {g₂ : β₂ → α},   Set.LeftInvOn g₂ f₂ s → Set.LeftInvOn (fun x => 
g₂ x.2) (fun x => (f₁ x, f₂ x)) s
参数：fun x => g₂ x.2；fun x => (f₁ x, f₂ x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LeftInvOn.right_prodMk (h₂ : LeftInvOn g₂ f₂ s) :
    LeftInvOn (fun x ↦ g₂ x.2) (fun x ↦ (f₁ x, f₂ x)) s := h₂

end Prod

section ProdMap

variable {α₁ α₂ β₁ β₂ : Type*} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂}
  {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {g₁ : β₁ → α₁} {g₂ : β₂ → α₂}

/-
**Set.InjOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂ : Type u_10} {s₁ : S
et α₁} {s₂ : Set α₂} {f₁ : α₁ → β₁}   {f₂ : α₂ → β₂}, Set.InjOn f₁ s₁ → Set.InjO
n f₂ s₂ → Set.InjOn (fun x => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂)
参数：fun x => (f₁ x.1, f₂ x.2)；s₁ ×ˢ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma InjOn.prodMap (h₁ : s₁.InjOn f₁) (h₂ : s₂.InjOn f₂) :
    (s₁ ×ˢ s₂).InjOn fun x ↦ (f₁ x.1, f₂ x.2) :=
  fun x hx y hy ↦ by simp_rw [Prod.ext_iff]; exact And.imp (h₁ hx.1 hy.1) (h₂ hx.2 hy.2)
/-
**Set.SurjOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.SurjOn`。
形式化陈述：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂ : Type u_10} {s₁ : S
et α₁} {s₂ : Set α₂} {t₁ : Set β₁}   {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂}
,   Set.SurjOn f₁ s₁ t₁ → Set.SurjOn f₂ s₂ t₂ → Set.SurjOn (fun x => (f₁ x.1, f₂
 x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂)
参数：fun x => (f₁ x.1, f₂ x.2)；s₁ ×ˢ s₂；t₁ ×ˢ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
lemma SurjOn.prodMap (h₁ : SurjOn f₁ s₁ t₁) (h₂ : SurjOn f₂ s₂ t₂) :
    SurjOn (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := by
  rintro x hx
  obtain ⟨a₁, ha₁, hx₁⟩ := h₁ hx.1
  obtain ⟨a₂, ha₂, hx₂⟩ := h₂ hx.2
  exact ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, Prod.ext hx₁ hx₂⟩
/-
**Set.MapsTo.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂ : Type u_10} {s₁ : S
et α₁} {s₂ : Set α₂} {t₁ : Set β₁}   {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂}
,   Set.MapsTo f₁ s₁ t₁ → Set.MapsTo f₂ s₂ t₂ → Set.MapsTo (fun x => (f₁ x.1, f₂
 x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂)
参数：fun x => (f₁ x.1, f₂ x.2)；s₁ ×ˢ s₂；t₁ ×ˢ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma MapsTo.prodMap (h₁ : MapsTo f₁ s₁ t₁) (h₂ : MapsTo f₂ s₂ t₂) :
    MapsTo (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  fun _x hx ↦ ⟨h₁ hx.1, h₂ hx.2⟩
/-
**Set.BijOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂ : Type u_10} {s₁ : S
et α₁} {s₂ : Set α₂} {t₁ : Set β₁}   {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂}
,   Set.BijOn f₁ s₁ t₁ → Set.BijOn f₂ s₂ t₂ → Set.BijOn (fun x => (f₁ x.1, f₂ x.
2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂)
参数：fun x => (f₁ x.1, f₂ x.2)；s₁ ×ˢ s₂；t₁ ×ˢ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.prodMap`：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β
₂ : Type u_10} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁}   {t₂ : Set β₂} {f₁ : α
₁ → β₁} …
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.InjOn.prodMap`：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂
 : Type u_10} {s₁ : Set α₁} {s₂ : Set α₂} {f₁ : α₁ → β₁}   {f₂ : α₂ → β₂}, Set.I
njOn f₁…
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.SurjOn.prodMap`：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β
₂ : Type u_10} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁}   {t₂ : Set β₂} {f₁ : α
₁ → β₁} …
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
lemma BijOn.prodMap (h₁ : BijOn f₁ s₁ t₁) (h₂ : BijOn f₂ s₂ t₂) :
    BijOn (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  ⟨h₁.mapsTo.prodMap h₂.mapsTo, h₁.injOn.prodMap h₂.injOn, h₁.surjOn.prodMap h₂.surjOn⟩
/-
**Set.LeftInvOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.LeftInvOn`。
形式化陈述：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂ : Type u_10} {s₁ : S
et α₁} {s₂ : Set α₂} {f₁ : α₁ → β₁}   {f₂ : α₂ → β₂} {g₁ : β₁ → α₁} {g₂ : β₂ → α
₂},   Set.LeftInvOn g₁ f₁ s₁ →     Set.LeftInvOn g₂ f₂ s₂ → Set.LeftInvOn (fun x
 => (g₁ x.1, g₂ x.2)) (fun x => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂)
参数：fun x => (g₁ x.1, g₂ x.2)；fun x => (f₁ x.1, f₂ x.2)；s₁ ×ˢ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma LeftInvOn.prodMap (h₁ : LeftInvOn g₁ f₁ s₁) (h₂ : LeftInvOn g₂ f₂ s₂) :
    LeftInvOn (fun x ↦ (g₁ x.1, g₂ x.2)) (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) :=
  fun _x hx ↦ Prod.ext (h₁ hx.1) (h₂ hx.2)
/-
**Set.RightInvOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.RightInvOn`。
形式化陈述：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂ : Type u_10} {t₁ : S
et β₁} {t₂ : Set β₂} {f₁ : α₁ → β₁}   {f₂ : α₂ → β₂} {g₁ : β₁ → α₁} {g₂ : β₂ → α
₂},   Set.RightInvOn g₁ f₁ t₁ →     Set.RightInvOn g₂ f₂ t₂ → Set.RightInvOn (fu
n x => (g₁ x.1, g₂ x.2)) (fun x => (f₁ x.1, f₂ x.2)) (t₁ ×ˢ t₂)
参数：fun x => (g₁ x.1, g₂ x.2)；fun x => (f₁ x.1, f₂ x.2)；t₁ ×ˢ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma RightInvOn.prodMap (h₁ : RightInvOn g₁ f₁ t₁) (h₂ : RightInvOn g₂ f₂ t₂) :
    RightInvOn (fun x ↦ (g₁ x.1, g₂ x.2)) (fun x ↦ (f₁ x.1, f₂ x.2)) (t₁ ×ˢ t₂) :=
  fun _x hx ↦ Prod.ext (h₁ hx.1) (h₂ hx.2)
/-
**Set.InvOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Set.InvOn`。
形式化陈述：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂ : Type u_10} {s₁ : S
et α₁} {s₂ : Set α₂} {t₁ : Set β₁}   {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂}
 {g₁ : β₁ → α₁} {g₂ : β₂ → α₂},   Set.InvOn g₁ f₁ s₁ t₁ →     Set.InvOn g₂ f₂ s₂
 t₂ → Set.InvOn (fun x => (g₁ x.1, g₂ x.2)) (fun x => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s
₂) (t₁ ×ˢ t₂)
参数：fun x => (g₁ x.1, g₂ x.2)；fun x => (f₁ x.1, f₂ x.2)；s₁ ×ˢ s₂；t₁ ×ˢ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.prodMap`：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9}
 {β₂ : Type u_10} {s₁ : Set α₁} {s₂ : Set α₂} {f₁ : α₁ → β₁}   {f₂ : α₂ → β₂} {g
₁ : β₁ → α₁…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.RightInvOn.prodMap`：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9
} {β₂ : Type u_10} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α₁ → β₁}   {f₂ : α₂ → β₂} {
g₁ : β₁ → α₁…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma InvOn.prodMap (h₁ : InvOn g₁ f₁ s₁ t₁) (h₂ : InvOn g₂ f₂ s₂ t₂) :
    InvOn (fun x ↦ (g₁ x.1, g₂ x.2)) (fun x ↦ (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) :=
  ⟨h₁.1.prodMap h₂.1, h₁.2.prodMap h₂.2⟩

end ProdMap

end Set

namespace Equiv
open Set

variable (e : α ≃ β) {s : Set α} {t : Set β}

/-
**Equiv.bijOn'** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：bijOn' (h₁ : MapsTo e s t) (h₂ : MapsTo e.symm t s) : BijOn e s t
参数：h₁ : MapsTo e s t；h₂ : MapsTo e.symm t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma bijOn' (h₁ : MapsTo e s t) (h₂ : MapsTo e.symm t s) : BijOn e s t :=
  ⟨h₁, e.injective.injOn, fun b hb ↦ ⟨e.symm b, h₂ hb, apply_symm_apply _ _⟩⟩
/-
**Equiv.bijOn** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) {s : Set α} {t : Set β}, (∀ (a
 : α), e a ∈ t ↔ a ∈ s) → Set.BijOn (⇑e) s t
参数：e : α ≃ β；∀ (a : α), e a ∈ t ↔ a ∈ s；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.bijOn'`：bijOn' (h₁ : MapsTo e s t) (h₂ : MapsTo e.symm t s) : BijO
n e s t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
protected lemma bijOn (h : ∀ a, e a ∈ t ↔ a ∈ s) : BijOn e s t :=
  e.bijOn' (fun _ ↦ (h _).2) fun b hb ↦ (h _).1 <| by rwa [apply_symm_apply]
/-
**Equiv.invOn** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：invOn : InvOn e e.symm t s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.LeftInverse.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} {f : α →
 β} {g : β → α}, Function.LeftInverse f g → ∀ (s : Set β), Set.LeftInvOn f g s
· 使用定理 `Equiv.rightInverse_symm`：rightInverse_symm (f : α ≃ β) : Function.RightI
nverse f.symm f
· 使用定理 `Equiv.leftInverse_symm`：leftInverse_symm (f : α ≃ β) : LeftInverse f.sym
m f
-/
lemma invOn : InvOn e e.symm t s :=
  ⟨e.rightInverse_symm.leftInvOn _, e.leftInverse_symm.leftInvOn _⟩
/-
**Equiv.bijOn_image** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：bijOn_image : BijOn e s (e '' s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma bijOn_image : BijOn e s (e '' s) := e.injective.injOn.bijOn_image
/-
**Equiv.bijOn_symm_image** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：bijOn_symm_image : BijOn e.symm (e '' s) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} 
{f : α → β} {g : β → α},   Set.InvOn f g t s → Set.BijOn f s t → Set.BijOn g t s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.invOn`：invOn : InvOn e e.symm t s
· 使用引理 `Equiv.bijOn_image`：bijOn_image : BijOn e s (e '' s)
-/
lemma bijOn_symm_image : BijOn e.symm (e '' s) s := e.bijOn_image.symm e.invOn

variable {e}
/-
**Equiv.bijOn_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e : α ≃ β} {s : Set α} {t : Set β}, Set.B
ijOn (⇑e.symm) t s ↔ Set.BijOn (⇑e) s t
参数：⇑e.symm；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.bijOn_comm`：bijOn_comm {g : β -> α} (h : InvOn f g t s) : BijOn f s 
t ↔ BijOn g t s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.invOn`：invOn : InvOn e e.symm t s
-/
@[simp] lemma bijOn_symm : BijOn e.symm t s ↔ BijOn e s t := bijOn_comm e.symm.invOn

alias ⟨_root_.Set.BijOn.of_equiv_symm, _root_.Set.BijOn.equiv_symm⟩ := bijOn_symm

variable [DecidableEq α] {a b : α}
/-
**Equiv.bijOn_swap** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：bijOn_swap (ha : a in s) (hb : b in s) : BijOn (swap a b) s s
参数：ha : a in s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijOn`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) {s : Set α} {t 
: Set β}, (∀ (a : α), e a ∈ t ↔ a ∈ s) → Set.BijOn (⇑e) s t
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma bijOn_swap (ha : a ∈ s) (hb : b ∈ s) : BijOn (swap a b) s s :=
  (swap a b).bijOn fun x ↦ by
    obtain rfl | hxa := eq_or_ne x a <;>
    obtain rfl | hxb := eq_or_ne x b <;>
    simp [*, swap_apply_of_ne_of_ne]

end Equiv

