/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.Set.Prod

/-!
# N-ary images of sets

This file defines `Set.image2`, the binary image of sets.
This is mostly useful to define pointwise operations and `Set.seq`.

## Notes

This file is very similar to `Mathlib/Data/Finset/NAry.lean`, `Mathlib/Order/Filter/NAry.lean`, and
`Mathlib/Data/Option/NAry.lean`. Please keep them in sync.
-/

public section

open Function

namespace Set
variable {α α' β β' γ γ' δ δ' ε ε' ζ ζ' ν : Type*} {f f' : α → β → γ}
variable {s s' : Set α} {t t' : Set β} {u : Set γ} {v : Set δ} {a : α} {b : β}

/-
**Set.mem_image2_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_image2_iff (hf : Injective2 f) : f a b in image2 f s t ↔ a in s ∧ b in
 t
参数：hf : Injective2 f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem mem_image2_iff (hf : Injective2 f) : f a b ∈ image2 f s t ↔ a ∈ s ∧ b ∈ t :=
  ⟨by
    rintro ⟨a', ha', b', hb', h⟩
    rcases hf h with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩, fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩

/-- image2 is monotone with respect to `⊆`. -/
@[gcongr]
/-
**Set.image2_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_subset (hs : s subseteq s') (ht : t subseteq t') : image2 f s t sub
seteq image2 f s' t'
参数：hs : s subseteq s'；ht : t subseteq t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t

--- 原说明 ---
image2 is monotone with respect to `⊆`.
-/
theorem image2_subset (hs : s ⊆ s') (ht : t ⊆ t') : image2 f s t ⊆ image2 f s' t' := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mem_image2_of_mem (hs ha) (ht hb)
/-
**Set.image2_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_subset_left (ht : t subseteq t') : image2 f s t subseteq image2 f s
 t'
参数：ht : t subseteq t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem image2_subset_left (ht : t ⊆ t') : image2 f s t ⊆ image2 f s t' :=
  image2_subset Subset.rfl ht
/-
**Set.image2_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_subset_right (hs : s subseteq s') : image2 f s t subseteq image2 f 
s' t
参数：hs : s subseteq s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem image2_subset_right (hs : s ⊆ s') : image2 f s t ⊆ image2 f s' t :=
  image2_subset hs Subset.rfl
/-
**Set.image_subset_image2_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_image2_left (hb : b in t) : (fun a => f a b) '' s subseteq im
age2 f s t
参数：hb : b in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem image_subset_image2_left (hb : b ∈ t) : (fun a => f a b) '' s ⊆ image2 f s t :=
  forall_mem_image.2 fun _ ha => mem_image2_of_mem ha hb
/-
**Set.image_subset_image2_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_image2_right (ha : a in s) : f a '' t subseteq image2 f s t
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem image_subset_image2_right (ha : a ∈ s) : f a '' t ⊆ image2 f s t :=
  forall_mem_image.2 fun _ => mem_image2_of_mem ha
/-
**Set.forall_mem_image2** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：forall_mem_image2 {p : γ -> Prop} : (forall z in image2 f s t, p z) ↔ fora
ll x in s, forall y in t, p (f x y)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forall_mem_image2 {p : γ → Prop} :
    (∀ z ∈ image2 f s t, p z) ↔ ∀ x ∈ s, ∀ y ∈ t, p (f x y) := by grind
/-
**Set.exists_mem_image2** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_mem_image2 {p : γ -> Prop} : (exists z in image2 f s t, p z) ↔ exis
ts x in s, exists y in t, p (f x y)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_mem_image2 {p : γ → Prop} :
    (∃ z ∈ image2 f s t, p z) ↔ ∃ x ∈ s, ∃ y ∈ t, p (f x y) := by grind

@[simp]
/-
**Set.image2_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_subset_iff {u : Set γ} : image2 f s t subseteq u ↔ forall x in s, f
orall y in t, f x y in u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
-/
theorem image2_subset_iff {u : Set γ} : image2 f s t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, f x y ∈ u :=
  forall_mem_image2
/-
**Set.image2_subset_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_subset_iff_left : image2 f s t subseteq u ↔ forall a in s, (fun b =
> f a b) '' t subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image2_subset_iff_left : image2 f s t ⊆ u ↔ ∀ a ∈ s, (fun b => f a b) '' t ⊆ u := by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage]
/-
**Set.image2_subset_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_subset_iff_right : image2 f s t subseteq u ↔ forall b in t, (fun a 
=> f a b) '' s subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image2_subset_iff_right : image2 f s t ⊆ u ↔ ∀ b ∈ t, (fun a => f a b) '' s ⊆ u := by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage, @forall₂_comm α]

variable (f)

@[simp]
/-
**Set.image_prod** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = image2 f s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma image_prod : (fun x : α × β ↦ f x.1 x.2) '' s ×ˢ t = image2 f s t :=
  ext fun _ ↦ by simp [and_assoc]
/-
**Set.image_uncurry_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} (f : α → β → γ) (s : Set α)
 (t : Set β),   Function.uncurry f '' s ×ˢ t = Set.image2 f s t
参数：f : α → β → γ；s : Set α；t : Set β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
-/
@[simp] lemma image_uncurry_prod (s : Set α) (t : Set β) : uncurry f '' s ×ˢ t = image2 f s t :=
  image_prod _
/-
**Set.image2_mk_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} {s : Set α} {t : Set β}, Set.image2 Prod.m
k s t = s ×ˢ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma image2_mk_eq_prod : image2 Prod.mk s t = s ×ˢ t := ext <| by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Set.image2_curry** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image2_curry (f : α × β -> γ) (s : Set α) (t : Set β) : image2 (fun a b =>
 f (a, b)) s t = f '' s ×ˢ t
参数：f : α × β -> γ；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image2_curry (f : α × β → γ) (s : Set α) (t : Set β) :
    image2 (fun a b ↦ f (a, b)) s t = f '' s ×ˢ t := by
  simp [← image_uncurry_prod, uncurry]
/-
**Set.image2_swap** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_swap (s : Set α) (t : Set β) : image2 f s t = image2 (fun a b => f 
b a) t s
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image2_swap (s : Set α) (t : Set β) : image2 f s t = image2 (fun a b => f b a) t s := by
  grind

variable {f}
/-
**Set.image2_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_union_left : image2 f (s union s') t = image2 f s t union image2 f 
s' t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_prod`：union_prod : (s₁ union s₂) ×ˢ t = s₁ ×ˢ t union s₂ ×ˢ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image2_union_left : image2 f (s ∪ s') t = image2 f s t ∪ image2 f s' t := by
  simp_rw [← image_prod, union_prod, image_union]
/-
**Set.image2_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_union_right : image2 f s (t union t') = image2 f s t union image2 f
 s t'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
· 使用定理 `Set.image2_union_left`：image2_union_left : image2 f (s union s') t = ima
ge2 f s t union image2 f s' t
-/
theorem image2_union_right : image2 f s (t ∪ t') = image2 f s t ∪ image2 f s t' := by
  rw [← image2_swap, image2_union_left, image2_swap f, image2_swap f]
/-
**Set.image2_inter_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image2_inter_left (hf : Injective2 f) : image2 f (s inter s') t = image2 f
 s t inter image2 f s' t
参数：hf : Injective2 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_prod`：inter_prod : (s₁ inter s₂) ×ˢ t = s₁ ×ˢ t inter s₂ ×ˢ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `Function.Injective2.uncurry`：∀ {α : Type u_4} {β : Type u_5} {γ : Type u
_6} {f : α → β → γ},   Function.Injective2 f → Function.Injective (Function.uncu
rry f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image2_inter_left (hf : Injective2 f) :
    image2 f (s ∩ s') t = image2 f s t ∩ image2 f s' t := by
  simp_rw [← image_uncurry_prod, inter_prod, image_inter hf.uncurry]
/-
**Set.image2_inter_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image2_inter_right (hf : Injective2 f) : image2 f s (t inter t') = image2 
f s t inter image2 f s t'
参数：hf : Injective2 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.prod_inter`：prod_inter : s ×ˢ (t₁ inter t₂) = s ×ˢ t₁ inter s ×ˢ t₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `Function.Injective2.uncurry`：∀ {α : Type u_4} {β : Type u_5} {γ : Type u
_6} {f : α → β → γ},   Function.Injective2 f → Function.Injective (Function.uncu
rry f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image2_inter_right (hf : Injective2 f) :
    image2 f s (t ∩ t') = image2 f s t ∩ image2 f s t' := by
  simp_rw [← image_uncurry_prod, prod_inter, image_inter hf.uncurry]

@[simp]
/-
**Set.image2_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_empty_left : image2 f ∅ t = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem image2_empty_left : image2 f ∅ t = ∅ :=
  ext <| by simp

@[simp]
/-
**Set.image2_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_empty_right : image2 f s ∅ = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem image2_empty_right : image2 f s ∅ = ∅ :=
  ext <| by simp
/-
**Set.Nonempty.image2** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f : α → β → γ} {s : Set α}
 {t : Set β},   s.Nonempty → t.Nonempty → (Set.image2 f s t).Nonempty
参数：Set.image2 f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem Nonempty.image2 : s.Nonempty → t.Nonempty → (image2 f s t).Nonempty :=
  fun ⟨_, ha⟩ ⟨_, hb⟩ => ⟨_, mem_image2_of_mem ha hb⟩

@[simp]
/-
**Set.image2_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_nonempty_iff : (image2 f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f :
 α → β → γ} {s : Set α} {t : Set β},   s.Nonempty → t.Nonempty → (Set.image2 f s
 t).Nonem…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem image2_nonempty_iff : (image2 f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun ⟨_, a, ha, b, hb, _⟩ => ⟨⟨a, ha⟩, b, hb⟩, fun h => h.1.image2 h.2⟩
/-
**Set.Nonempty.of_image2_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f : α → β → γ} {s : Set α}
 {t : Set β},   (Set.image2 f s t).Nonempty → s.Nonempty
参数：Set.image2 f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image2_nonempty_iff`：image2_nonempty_iff : (image2 f s t).Nonempty ↔
 s.Nonempty ∧ t.Nonempty
-/
theorem Nonempty.of_image2_left (h : (Set.image2 f s t).Nonempty) : s.Nonempty :=
  (image2_nonempty_iff.1 h).1
/-
**Set.Nonempty.of_image2_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f : α → β → γ} {s : Set α}
 {t : Set β},   (Set.image2 f s t).Nonempty → t.Nonempty
参数：Set.image2 f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image2_nonempty_iff`：image2_nonempty_iff : (image2 f s t).Nonempty ↔
 s.Nonempty ∧ t.Nonempty
-/
theorem Nonempty.of_image2_right (h : (Set.image2 f s t).Nonempty) : t.Nonempty :=
  (image2_nonempty_iff.1 h).2

@[simp]
/-
**Set.image2_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Set.image2_nonempty_iff`：image2_nonempty_iff : (image2 f s t).Nonempty ↔
 s.Nonempty ∧ t.Nonempty
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  rw [← not_nonempty_iff_eq_empty, image2_nonempty_iff, not_and_or]
  simp [not_nonempty_iff_eq_empty]
/-
**Set.Subsingleton.image2** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {s : Set α} {t : Set β},   
s.Subsingleton → t.Subsingleton → ∀ (f : α → β → γ), (Set.image2 f s t).Subsingl
eton
参数：f : α → β → γ；Set.image2 f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
· 使用定理 `Set.Subsingleton.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : 
Set β}, s.Subsingleton → t.Subsingleton → (s ×ˢ t).Subsingleton
-/
theorem Subsingleton.image2 (hs : s.Subsingleton) (ht : t.Subsingleton) (f : α → β → γ) :
    (image2 f s t).Subsingleton := by
  rw [← image_prod]
  apply (hs.prod ht).image
/-
**Set.image2_inter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_inter_subset_left : image2 f (s inter s') t subseteq image2 f s t i
nter image2 f s' t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `Set.image2_subset_right`：image2_subset_right (hs : s subseteq s') : imag
e2 f s t subseteq image2 f s' t
-/
theorem image2_inter_subset_left : image2 f (s ∩ s') t ⊆ image2 f s t ∩ image2 f s' t :=
  Monotone.map_inf_le (fun _ _ ↦ image2_subset_right) s s'
/-
**Set.image2_inter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_inter_subset_right : image2 f s (t inter t') subseteq image2 f s t 
inter image2 f s t'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `Set.image2_subset_left`：image2_subset_left (ht : t subseteq t') : image2
 f s t subseteq image2 f s t'
-/
theorem image2_inter_subset_right : image2 f s (t ∩ t') ⊆ image2 f s t ∩ image2 f s t' :=
  Monotone.map_inf_le (fun _ _ ↦ image2_subset_left) t t'
/-
**Set.subset_image2_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_image2_sdiff_left : image2 f s t \ image2 f s' t subseteq image2 f 
(s \ s') t
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_image2_sdiff_left :
    image2 f s t \ image2 f s' t ⊆ image2 f (s \ s') t := by
  rintro - ⟨⟨a, ha, b, hb, rfl⟩, h⟩
  exact ⟨_, ⟨ha, fun ha' ↦ h ⟨_, ha', _, hb, rfl⟩⟩, _, hb, rfl⟩

@[deprecated (since := "2026-06-03")] alias subset_image2_diff_left := subset_image2_sdiff_left
/-
**Set.subset_image2_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_image2_sdiff_right : image2 f s t \ image2 f s t' subseteq image2 f
 s (t \ t')
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_image2_sdiff_right :
    image2 f s t \ image2 f s t' ⊆ image2 f s (t \ t') := by
  rintro - ⟨⟨a, ha, b, hb, rfl⟩, h⟩
  exact ⟨_, ha, _, ⟨hb, fun hb' ↦ h ⟨_, ha, _, hb', rfl⟩⟩, rfl⟩

@[deprecated (since := "2026-06-03")] alias subset_image2_diff_right := subset_image2_sdiff_right

@[simp]
/-
**Set.image2_singleton_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_singleton_left : image2 f {a} t = f a '' t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image2_singleton_left : image2 f {a} t = f a '' t :=
  ext fun x => by simp

@[simp]
/-
**Set.image2_singleton_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_singleton_right : image2 f s {b} = (fun a => f a b) '' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image2_singleton_right : image2 f s {b} = (fun a => f a b) '' s :=
  ext fun x => by simp
/-
**Set.image2_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_singleton : image2 f {a} {b} = {f a b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image2_singleton : image2 f {a} {b} = {f a b} := by simp

@[simp]
/-
**Set.image2_insert_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_insert_left : image2 f (insert a s) t = (fun b => f a b) '' t union
 image2 f s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.image2_union_left`：image2_union_left : image2 f (s union s') t = ima
ge2 f s t union image2 f s' t
· 使用定理 `Set.image2_singleton_left`：image2_singleton_left : image2 f {a} t = f a 
'' t
-/
theorem image2_insert_left : image2 f (insert a s) t = (fun b => f a b) '' t ∪ image2 f s t := by
  rw [insert_eq, image2_union_left, image2_singleton_left]

@[simp]
/-
**Set.image2_insert_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_insert_right : image2 f s (insert b t) = (fun a => f a b) '' s unio
n image2 f s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.image2_union_right`：image2_union_right : image2 f s (t union t') = i
mage2 f s t union image2 f s t'
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
-/
theorem image2_insert_right : image2 f s (insert b t) = (fun a => f a b) '' s ∪ image2 f s t := by
  rw [insert_eq, image2_union_right, image2_singleton_right]

@[congr]
/-
**Set.image2_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_congr (h : forall a in s, forall b in t, f a b = f' a b) : image2 f
 s t = image2 f' s t
参数：h : forall a in s, forall b in t, f a b = f' a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image2_congr (h : ∀ a ∈ s, ∀ b ∈ t, f a b = f' a b) : image2 f s t = image2 f' s t := by
  grind

/-- A common special case of `image2_congr` -/
/-
**Set.image2_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_congr' (h : forall a b, f a b = f' a b) : image2 f s t = image2 f' 
s t
参数：h : forall a b, f a b = f' a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_congr`：image2_congr (h : forall a in s, forall b in t, f a b 
= f' a b) : image2 f s t = image2 f' s t

--- 原说明 ---
A common special case of `image2_congr`
-/
theorem image2_congr' (h : ∀ a b, f a b = f' a b) : image2 f s t = image2 f' s t :=
  image2_congr fun a _ b _ => h a b
/-
**Set.image_image2** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image2 (f : α -> β -> γ) (g : γ -> δ) : g '' image2 f s t = image2 (
fun a b => g (f a b)) s t
参数：f : α -> β -> γ；g : γ -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_image2 (f : α → β → γ) (g : γ → δ) :
    g '' image2 f s t = image2 (fun a b => g (f a b)) s t := by
  simp only [← image_prod, image_image]
/-
**Set.image2_image_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_image_left (f : γ -> β -> δ) (g : α -> γ) : image2 f (g '' s) t = i
mage2 (fun a b => f (g a) b) s t
参数：f : γ -> β -> δ；g : α -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image2_image_left (f : γ → β → δ) (g : α → γ) :
    image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t := by
  ext; simp
/-
**Set.image2_image_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_image_right (f : α -> γ -> δ) (g : β -> γ) : image2 f s (g '' t) = 
image2 (fun a b => f a (g b)) s t
参数：f : α -> γ -> δ；g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image2_image_right (f : α → γ → δ) (g : β → γ) :
    image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t := by
  ext; simp

@[simp]
/-
**Set.image2_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_left (h : t.Nonempty) : image2 (fun x _ => x) s t = s
参数：h : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem image2_left (h : t.Nonempty) : image2 (fun x _ => x) s t = s := by
  simp [nonempty_def.mp h, Set.ext_iff]

@[simp]
/-
**Set.image2_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_right (h : s.Nonempty) : image2 (fun _ y => y) s t = t
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem image2_right (h : s.Nonempty) : image2 (fun _ y => y) s t = t := by
  simp [nonempty_def.mp h, Set.ext_iff]
/-
**Set.image2_range** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image2_range (f : α' -> β' -> γ) (g : α -> α') (h : β -> β') : image2 f (r
ange g) (range h) = range fun x : α × β => f (g x.1) (h x.2)
参数：f : α' -> β' -> γ；g : α -> α'；h : β -> β'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_image_right`：image2_image_right (f : α -> γ -> δ) (g : β -> γ
) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma image2_range (f : α' → β' → γ) (g : α → α') (h : β → β') :
    image2 f (range g) (range h) = range fun x : α × β ↦ f (g x.1) (h x.2) := by
  simp_rw [← image_univ, image2_image_left, image2_image_right, ← image_prod, univ_prod_univ]
/-
**Set.image2_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_assoc {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' :
 β -> γ -> ε'} (h_assoc : forall a b c, f (g a b) c = f' a (g' b c)) : image2 f 
(image2 g s t) u = image2 f' s (image2 g' t u)
参数：h_assoc : forall a b c, f (g a b) c = f' a (g' b c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.eq_of_forall_subset_iff`：eq_of_forall_subset_iff (h : forall u, s su
bseteq u ↔ t subseteq u) : s = t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image2_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    image2 f (image2 g s t) u = image2 f' s (image2 g' t u) :=
  eq_of_forall_subset_iff fun _ ↦ by simp only [image2_subset_iff, forall_mem_image2, h_assoc]
/-
**Set.image2_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_comm {g : β -> α -> γ} (h_comm : forall a b, f a b = g b a) : image
2 f s t = image2 g t s
参数：h_comm : forall a b, f a b = g b a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_congr`：image2_congr (h : forall a in s, forall b in t, f a b 
= f' a b) : image2 f s t = image2 f' s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image2_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image2 f s t = image2 g t s :=
  (image2_swap _ _ _).trans <| by simp_rw [h_comm]
/-
**Set.image2_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_left_comm {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {
g' : β -> δ' -> ε} (h_left_comm : forall a b c, f a (g b c) = g' b (f' a c)) : i
mage2 f s (image2 g t u) = image2 g' t (image2 f' s u)
参数：h_left_comm : forall a b c, f a (g b c) = g' b (f' a c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
· 使用定理 `Set.image2_assoc`：image2_assoc {f : δ -> γ -> ε} {g : α -> β -> δ} {f' :
 α -> ε' -> ε} {g' : β -> γ -> ε'} (h_assoc : forall a b c, f (g a b) c = f' a (
g' b c…
-/
theorem image2_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
    (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    image2 f s (image2 g t u) = image2 g' t (image2 f' s u) := by
  rw [image2_swap f', image2_swap f]
  exact image2_assoc fun _ _ _ => h_left_comm _ _ _
/-
**Set.image2_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_right_comm {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} 
{g' : δ' -> β -> ε} (h_right_comm : forall a b c, f (g a b) c = g' (f' a c) b) :
 image2 f (image2 g s t) u = image2 g' (image2 f' s u) t
参数：h_right_comm : forall a b c, f (g a b) c = g' (f' a c) b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
· 使用定理 `Set.image2_assoc`：image2_assoc {f : δ -> γ -> ε} {g : α -> β -> δ} {f' :
 α -> ε' -> ε} {g' : β -> γ -> ε'} (h_assoc : forall a b c, f (g a b) c = f' a (
g' b c…
-/
theorem image2_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
    (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    image2 f (image2 g s t) u = image2 g' (image2 f' s u) t := by
  rw [image2_swap g, image2_swap g']
  exact image2_assoc fun _ _ _ => h_right_comm _ _ _
/-
**Set.image2_image2_image2_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_image2_image2_comm {f : ε -> ζ -> ν} {g : α -> β -> ε} {h : γ -> δ 
-> ζ} {f' : ε' -> ζ' -> ν} {g' : α -> γ -> ε'} {h' : β -> δ -> ζ'} (h_comm : for
all a b c d, f (g a b) (h c d) = f' (g' a c) (h' b d)) : image2 f (image2 g s t)
 (image2 h u v) = image2 f' (image2 g' s u) (image2 h' t v)
参数：h_comm : forall a b c d, f (g a b) (h c d) = f' (g' a c) (h' b d)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image2_image2_image2_comm {f : ε → ζ → ν} {g : α → β → ε} {h : γ → δ → ζ} {f' : ε' → ζ' → ν}
    {g' : α → γ → ε'} {h' : β → δ → ζ'}
    (h_comm : ∀ a b c d, f (g a b) (h c d) = f' (g' a c) (h' b d)) :
    image2 f (image2 g s t) (image2 h u v) = image2 f' (image2 g' s u) (image2 h' t v) := by
  grind
/-
**Set.image_image2_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image2_distrib {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ 
: β -> β'} (h_distrib : forall a b, g (f a b) = f' (g₁ a) (g₂ b)) : (image2 f s 
t).image g = image2 f' (s.image g₁) (t.image g₂)
参数：h_distrib : forall a b, g (f a b) = f' (g₁ a) (g₂ b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image2`：image_image2 (f : α -> β -> γ) (g : γ -> δ) : g '' ima
ge2 f s t = image2 (fun a b => g (f a b)) s t
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_image_right`：image2_image_right (f : α -> γ -> δ) (g : β -> γ
) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image2_congr`：image2_congr (h : forall a in s, forall b in t, f a b 
= f' a b) : image2 f s t = image2 f' s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_image2_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (image2 f s t).image g = image2 f' (s.image g₁) (t.image g₂) := by
  simp_rw [image_image2, image2_image_left, image2_image_right, h_distrib]

/-- Symmetric statement to `Set.image2_image_left_comm`. -/
/-
**Set.image_image2_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image2_distrib_left {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'} 
(h_distrib : forall a b, g (f a b) = f' (g' a) b) : (image2 f s t).image g = ima
ge2 f' (s.image g') t
参数：h_distrib : forall a b, g (f a b) = f' (g' a) b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_image2_distrib`：image_image2_distrib {g : γ -> δ} {f' : α' -> 
β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f' (
g₁ a) (g₂ b)) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s

--- 原说明 ---
Symmetric statement to `Set.image2_image_left_comm`.
-/
theorem image_image2_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
    (image2 f s t).image g = image2 f' (s.image g') t :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']

/-- Symmetric statement to `Set.image_image2_right_comm`. -/
/-
**Set.image_image2_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image2_distrib_right {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
 (h_distrib : forall a b, g (f a b) = f' a (g' b)) : (image2 f s t).image g = im
age2 f' s (t.image g')
参数：h_distrib : forall a b, g (f a b) = f' a (g' b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_image2_distrib`：image_image2_distrib {g : γ -> δ} {f' : α' -> 
β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f' (
g₁ a) (g₂ b)) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s

--- 原说明 ---
Symmetric statement to `Set.image_image2_right_comm`.
-/
theorem image_image2_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
    (image2 f s t).image g = image2 f' s (t.image g') :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']

/-- Symmetric statement to `Set.image_image2_distrib_left`. -/
/-
**Set.image2_image_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_image_left_comm {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ}
 {g' : δ -> γ} (h_left_comm : forall a b, f (g a) b = g' (f' a b)) : image2 f (s
.image g) t = (image2 f' s t).image g'
参数：h_left_comm : forall a b, f (g a) b = g' (f' a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_image2_distrib_left`：image_image2_distrib_left {g : γ -> δ} {f
' : α' -> β -> δ} {g' : α -> α'} (h_distrib : forall a b, g (f a b) = f' (g' a) 
b) : (image2 f s t)…

--- 原说明 ---
Symmetric statement to `Set.image_image2_distrib_left`.
-/
theorem image2_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
    image2 f (s.image g) t = (image2 f' s t).image g' :=
  (image_image2_distrib_left fun a b => (h_left_comm a b).symm).symm

/-- Symmetric statement to `Set.image_image2_distrib_right`. -/
/-
**Set.image_image2_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image2_right_comm {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ
} {g' : δ -> γ} (h_right_comm : forall a b, f a (g b) = g' (f' a b)) : image2 f 
s (t.image g) = (image2 f' s t).image g'
参数：h_right_comm : forall a b, f a (g b) = g' (f' a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_image2_distrib_right`：image_image2_distrib_right {g : γ -> δ} 
{f' : α -> β' -> δ} {g' : β -> β'} (h_distrib : forall a b, g (f a b) = f' a (g'
 b)) : (image2 f s t…

--- 原说明 ---
Symmetric statement to `Set.image_image2_distrib_right`.
-/
theorem image_image2_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
    image2 f s (t.image g) = (image2 f' s t).image g' :=
  (image_image2_distrib_right fun a b => (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
/-
**Set.image2_distrib_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_distrib_subset_left {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> 
β -> β'} {f₂ : α -> γ -> γ'} {g' : β' -> γ' -> ε} (h_distrib : forall a b c, f a
 (g b c) = g' (f₁ a b) (f₂ a c)) : image2 f s (image2 g t u) subseteq image2 g' 
(image2 f₁ s t) (image2 f₂ s u)
参数：h_distrib : forall a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The other direction does not hold because of the `s`-`s` cross terms on the RHS.
-/
theorem image2_distrib_subset_left {f : α → δ → ε} {g : β → γ → δ} {f₁ : α → β → β'}
    {f₂ : α → γ → γ'} {g' : β' → γ' → ε} (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image2 f s (image2 g t u) ⊆ image2 g' (image2 f₁ s t) (image2 f₂ s u) := by
  grind

/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
/-
**Set.image2_distrib_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_distrib_subset_right {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α ->
 γ -> α'} {f₂ : β -> γ -> β'} {g' : α' -> β' -> ε} (h_distrib : forall a b c, f 
(g a b) c = g' (f₁ a c) (f₂ b c)) : image2 f (image2 g s t) u subseteq image2 g'
 (image2 f₁ s u) (image2 f₂ t u)
参数：h_distrib : forall a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The other direction does not hold because of the `u`-`u` cross terms on the RHS.
-/
theorem image2_distrib_subset_right {f : δ → γ → ε} {g : α → β → δ} {f₁ : α → γ → α'}
    {f₂ : β → γ → β'} {g' : α' → β' → ε} (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image2 f (image2 g s t) u ⊆ image2 g' (image2 f₁ s u) (image2 f₂ t u) := by
  grind
/-
**Set.image_image2_antidistrib** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image2_antidistrib {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} 
{g₂ : α -> α'} (h_antidistrib : forall a b, g (f a b) = f' (g₁ b) (g₂ a)) : (ima
ge2 f s t).image g = image2 f' (t.image g₁) (s.image g₂)
参数：h_antidistrib : forall a b, g (f a b) = f' (g₁ b) (g₂ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
· 使用定理 `Set.image_image2_distrib`：image_image2_distrib {g : γ -> δ} {f' : α' -> 
β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f' (
g₁ a) (g₂ b)) …
-/
theorem image_image2_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image2 f s t).image g = image2 f' (t.image g₁) (s.image g₂) := by
  rw [image2_swap f]
  exact image_image2_distrib fun _ _ => h_antidistrib _ _

/-- Symmetric statement to `Set.image2_image_left_anticomm`. -/
/-
**Set.image_image2_antidistrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image2_antidistrib_left {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> 
β'} (h_antidistrib : forall a b, g (f a b) = f' (g' b) a) : (image2 f s t).image
 g = image2 f' (t.image g') s
参数：h_antidistrib : forall a b, g (f a b) = f' (g' b) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_image2_antidistrib`：image_image2_antidistrib {g : γ -> δ} {f' 
: β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'} (h_antidistrib : forall a b, g (f
 a b) = f' (g₁ b) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s

--- 原说明 ---
Symmetric statement to `Set.image2_image_left_anticomm`.
-/
theorem image_image2_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
    (image2 f s t).image g = image2 f' (t.image g') s :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']

/-- Symmetric statement to `Set.image_image2_right_anticomm`. -/
/-
**Set.image_image2_antidistrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image2_antidistrib_right {g : γ -> δ} {f' : β -> α' -> δ} {g' : α ->
 α'} (h_antidistrib : forall a b, g (f a b) = f' b (g' a)) : (image2 f s t).imag
e g = image2 f' t (s.image g')
参数：h_antidistrib : forall a b, g (f a b) = f' b (g' a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_image2_antidistrib`：image_image2_antidistrib {g : γ -> δ} {f' 
: β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'} (h_antidistrib : forall a b, g (f
 a b) = f' (g₁ b) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s

--- 原说明 ---
Symmetric statement to `Set.image_image2_right_anticomm`.
-/
theorem image_image2_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
    (image2 f s t).image g = image2 f' t (s.image g') :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']

/-- Symmetric statement to `Set.image_image2_antidistrib_left`. -/
/-
**Set.image2_image_left_anticomm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_image_left_anticomm {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -
> δ} {g' : δ -> γ} (h_left_anticomm : forall a b, f (g a) b = g' (f' b a)) : ima
ge2 f (s.image g) t = (image2 f' t s).image g'
参数：h_left_anticomm : forall a b, f (g a) b = g' (f' b a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_image2_antidistrib_left`：image_image2_antidistrib_left {g : γ 
-> δ} {f' : β' -> α -> δ} {g' : β -> β'} (h_antidistrib : forall a b, g (f a b) 
= f' (g' b) a) : (image…

--- 原说明 ---
Symmetric statement to `Set.image_image2_antidistrib_left`.
-/
theorem image2_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    image2 f (s.image g) t = (image2 f' t s).image g' :=
  (image_image2_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

/-- Symmetric statement to `Set.image_image2_antidistrib_right`. -/
/-
**Set.image_image2_right_anticomm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image2_right_anticomm {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α 
-> δ} {g' : δ -> γ} (h_right_anticomm : forall a b, f a (g b) = g' (f' b a)) : i
mage2 f s (t.image g) = (image2 f' t s).image g'
参数：h_right_anticomm : forall a b, f a (g b) = g' (f' b a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_image2_antidistrib_right`：image_image2_antidistrib_right {g : 
γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'} (h_antidistrib : forall a b, g (f a b
) = f' b (g' a)) : (imag…

--- 原说明 ---
Symmetric statement to `Set.image_image2_antidistrib_right`.
-/
theorem image_image2_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    image2 f s (t.image g) = (image2 f' t s).image g' :=
  (image_image2_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

/-- If `a` is a left identity for `f : α → β → β`, then `{a}` is a left identity for
`Set.image2 f`. -/
/-
**Set.image2_left_identity** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image2_left_identity {f : α -> β -> β} {a : α} (h : forall b, f a b = b) (
t : Set β) : image2 f {a} t = t
参数：h : forall b, f a b = b；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_singleton_left`：image2_singleton_left : image2 f {a} t = f a 
'' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s

--- 原说明 ---
If `a` is a left identity for `f : α → β → β`, then `{a}` is a left identity for
`Set.image2 f`.
-/
lemma image2_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (t : Set β) :
    image2 f {a} t = t := by
  rw [image2_singleton_left, show f a = id from funext h, image_id]

/-- If `b` is a right identity for `f : α → β → α`, then `{b}` is a right identity for
`Set.image2 f`. -/
/-
**Set.image2_right_identity** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image2_right_identity {f : α -> β -> α} {b : β} (h : forall a, f a b = a) 
(s : Set α) : image2 f s {b} = s
参数：h : forall a, f a b = a；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_singleton_right`：image2_singleton_right : image2 f s {b} = (f
un a => f a b) '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s

--- 原说明 ---
If `b` is a right identity for `f : α → β → α`, then `{b}` is a right identity f
or
`Set.image2 f`.
-/
lemma image2_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (s : Set α) :
    image2 f s {b} = s := by
  rw [image2_singleton_right, funext h, image_id']
/-
**Set.image2_inter_union_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_inter_union_subset_union : image2 f (s inter s') (t union t') subse
teq image2 f s t union image2 f s' t'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_union_right`：image2_union_right : image2 f s (t union t') = i
mage2 f s t union image2 f s t'
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem image2_inter_union_subset_union :
    image2 f (s ∩ s') (t ∪ t') ⊆ image2 f s t ∪ image2 f s' t' := by
  rw [image2_union_right]
  nth_grw 1 [inter_subset_left, inter_subset_right]
/-
**Set.image2_union_inter_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_union_inter_subset_union : image2 f (s union s') (t inter t') subse
teq image2 f s t union image2 f s' t'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_union_left`：image2_union_left : image2 f (s union s') t = ima
ge2 f s t union image2 f s' t
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem image2_union_inter_subset_union :
    image2 f (s ∪ s') (t ∩ t') ⊆ image2 f s t ∪ image2 f s' t' := by
  rw [image2_union_left]
  nth_grw 1 [inter_subset_left, inter_subset_right]
/-
**Set.image2_inter_union_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_inter_union_subset {f : α -> α -> β} {s t : Set α} (hf : forall a b
, f a b = f b a) : image2 f (s inter t) (s union t) subseteq image2 f s t
参数：hf : forall a b, f a b = f b a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.image2_inter_union_subset_union`：image2_inter_union_subset_union : i
mage2 f (s inter s') (t union t') subseteq image2 f s t union image2 f s' t'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.image2_comm`：image2_comm {g : β -> α -> γ} (h_comm : forall a b, f a
 b = g b a) : image2 f s t = image2 g t s
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
-/
theorem image2_inter_union_subset {f : α → α → β} {s t : Set α} (hf : ∀ a b, f a b = f b a) :
    image2 f (s ∩ t) (s ∪ t) ⊆ image2 f s t := by
  grw [inter_comm, image2_inter_union_subset_union, image2_comm hf, union_self]
/-
**Set.image2_union_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image2_union_inter_subset {f : α -> α -> β} {s t : Set α} (hf : forall a b
, f a b = f b a) : image2 f (s union t) (s inter t) subseteq image2 f s t
参数：hf : forall a b, f a b = f b a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image2_comm`：image2_comm {g : β -> α -> γ} (h_comm : forall a b, f a
 b = g b a) : image2 f s t = image2 g t s
· 使用定理 `Set.image2_inter_union_subset`：image2_inter_union_subset {f : α -> α -> 
β} {s t : Set α} (hf : forall a b, f a b = f b a) : image2 f (s inter t) (s unio
n t) subseteq image…
-/
theorem image2_union_inter_subset {f : α → α → β} {s t : Set α} (hf : ∀ a b, f a b = f b a) :
    image2 f (s ∪ t) (s ∩ t) ⊆ image2 f s t := by
  rw [image2_comm hf]
  exact image2_inter_union_subset hf

end Set

