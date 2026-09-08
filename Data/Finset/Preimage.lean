/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Set.Finite.Basic

/-!
# Preimage of a `Finset` under an injective map.
-/

@[expose] public section

assert_not_exists Finset.sum

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Finset

section Preimage

/-- Preimage of `s : Finset β` under a map `f` injective on `f ⁻¹' s` as a `Finset`. -/
/-
**Finset.preimage** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：preimage (s : Finset β) (f : α -> β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : Finse
t α
参数：s : Finset β；f : α -> β；hf : Set.InjOn f (f ⁻¹' ↑s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preimage of `s : Finset β` under a map `f` injective on `f ⁻¹' s` as a `Finset`.
-/
noncomputable def preimage (s : Finset β) (f : α → β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : Finset α :=
  (s.finite_toSet.preimage hf).toFinset

@[simp]
/-
**Finset.mem_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_preimage {f : α -> β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' ↑s)} {x 
: α} : x in preimage s f hf ↔ f x in s
参数：f ⁻¹' ↑s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem mem_preimage {f : α → β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' ↑s)} {x : α} :
    x ∈ preimage s f hf ↔ f x ∈ s :=
  Set.Finite.mem_toFinset _

@[simp, norm_cast]
/-
**Finset.coe_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : (
↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
参数：s : Finset β；hf : Set.InjOn f (f ⁻¹' ↑s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem coe_preimage {f : α → β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' ↑s)) :
    (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s :=
  Set.Finite.coe_toFinset _

@[simp]
/-
**Finset.preimage_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_empty {f : α -> β} : preimage ∅ f (by simp [InjOn]) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_empty {f : α → β} : preimage ∅ f (by simp [InjOn]) = ∅ :=
  Finset.coe_injective (by simp)

@[simp]
/-
**Finset.preimage_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_univ {f : α -> β} [Fintype α] [Fintype β] (hf) : preimage univ f 
hf = univ
参数：hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_univ {f : α → β} [Fintype α] [Fintype β] (hf) : preimage univ f hf = univ :=
  Finset.coe_injective (by simp)

@[simp]
/-
**Finset.disjoint_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_preimage {f : α -> β} {s t : Finset β} {hs : Set.InjOn f (f ⁻¹' ↑
s)} {ht : Set.InjOn f (f ⁻¹' ↑t)} (hd : Disjoint s t) : Disjoint (s.preimage f h
s) (t.preimage f ht)
参数：f ⁻¹' ↑s；f ⁻¹' ↑t；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_preimage {f : α → β} {s t : Finset β}
    {hs : Set.InjOn f (f ⁻¹' ↑s)} {ht : Set.InjOn f (f ⁻¹' ↑t)} (hd : Disjoint s t) :
    Disjoint (s.preimage f hs) (t.preimage f ht) := by
  grind [not_disjoint_iff, mem_preimage]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Finset.preimage_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_inter [DecidableEq α] [DecidableEq β] {f : α -> β} {s t : Finset 
β} (hs : Set.InjOn f (f ⁻¹' ↑s)) (ht : Set.InjOn f (f ⁻¹' ↑t)) : (preimage (s in
ter t) f fun _ hx₁ _ hx₂ => hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_lef
t hx₂)) = preimage s f hs inter preimage t f ht
参数：hs : Set.InjOn f (f ⁻¹' ↑s)；ht : Set.InjOn f (f ⁻¹' ↑t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.mem_of_mem_inter_left`：mem_of_mem_inter_left {a : α} {s₁ s₂ : Fin
set α} (h : a in s₁ inter s₂) : a in s₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_inter [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β}
    (hs : Set.InjOn f (f ⁻¹' ↑s)) (ht : Set.InjOn f (f ⁻¹' ↑t)) :
    (preimage (s ∩ t) f fun _ hx₁ _ hx₂ =>
        hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂)) =
      preimage s f hs ∩ preimage t f ht :=
  Finset.coe_injective (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Finset.preimage_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_union [DecidableEq α] [DecidableEq β] {f : α -> β} {s t : Finset 
β} (hst) : preimage (s union t) f hst = (preimage s f fun _ hx₁ _ hx₂ => hst (me
m_union_left _ hx₁) (mem_union_left _ hx₂)) union preimage t f fun _ hx₁ _ hx₂ =
> hst (mem_union_right _ hx₁) (mem_union_right _ hx₂)
参数：hst。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_union [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β} (hst) :
    preimage (s ∪ t) f hst =
      (preimage s f fun _ hx₁ _ hx₂ => hst (mem_union_left _ hx₁) (mem_union_left _ hx₂)) ∪
        preimage t f fun _ hx₁ _ hx₂ => hst (mem_union_right _ hx₁) (mem_union_right _ hx₂) :=
  Finset.coe_injective (by simp)

@[simp]
/-
**Finset.preimage_compl'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_compl' [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f
 : α -> β} (s : Finset β) (hfc : InjOn f (f ⁻¹' ↑sᶜ)) (hf : InjOn f (f ⁻¹' ↑s)) 
: preimage sᶜ f hfc = (preimage s f hf)ᶜ
参数：s : Finset β；hfc : InjOn f (f ⁻¹' ↑sᶜ)；hf : InjOn f (f ⁻¹' ↑s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Finset.coe_compl`：coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_compl' [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α → β}
    (s : Finset β) (hfc : InjOn f (f ⁻¹' ↑sᶜ)) (hf : InjOn f (f ⁻¹' ↑s)) :
    preimage sᶜ f hfc = (preimage s f hf)ᶜ :=
  Finset.coe_injective (by simp)

-- Not `@[simp]` since `simp` can't figure out `hf`; `simp`-normal form is `preimage_compl'`.
/-
**Finset.preimage_compl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_compl [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f 
: α -> β} (s : Finset β) (hf : Function.Injective f) : preimage sᶜ f hf.injOn = 
(preimage s f hf.injOn)ᶜ
参数：s : Finset β；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.preimage_compl'`：preimage_compl' [DecidableEq α] [DecidableEq β] 
[Fintype α] [Fintype β] {f : α -> β} (s : Finset β) (hfc : InjOn f (f ⁻¹' ↑sᶜ)) 
(hf : InjOn …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem preimage_compl [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α → β}
    (s : Finset β) (hf : Function.Injective f) :
    preimage sᶜ f hf.injOn = (preimage s f hf.injOn)ᶜ :=
  preimage_compl' _ _ _

@[simp]
/-
**Finset.preimage_map** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：preimage_map (f : α ↪ β) (s : Finset α) : (s.map f).preimage f f.injective
.injOn = s
参数：f : α ↪ β；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_map (f : α ↪ β) (s : Finset α) : (s.map f).preimage f f.injective.injOn = s :=
  coe_injective <| by simp only [coe_preimage, coe_map, Set.preimage_image_eq _ f.injective]
/-
**Finset.monotone_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：monotone_preimage {f : α -> β} (h : Injective f) : Monotone fun s => preim
age s f h.injOn
参数：h : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_preimage`：mem_preimage {f : α -> β} {s : Finset β} {hf : Set.
InjOn f (f ⁻¹' ↑s)} {x : α} : x in preimage s f hf ↔ f x in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem monotone_preimage {f : α → β} (h : Injective f) :
    Monotone fun s => preimage s f h.injOn := fun _ _ H _ hx =>
  mem_preimage.2 (H <| mem_preimage.1 hx)
/-
**Finset.image_subset_iff_subset_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_subset_iff_subset_preimage [DecidableEq β] {f : α -> β} {s : Finset 
α} {t : Finset β} (hf : Set.InjOn f (f ⁻¹' ↑t)) : s.image f subseteq t ↔ s subse
teq t.preimage f hf
参数：hf : Set.InjOn f (f ⁻¹' ↑t)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.image_subset_iff`：image_subset_iff : s.image f subseteq t ↔ foral
l x in s, f x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_subset_iff_subset_preimage [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
    (hf : Set.InjOn f (f ⁻¹' ↑t)) : s.image f ⊆ t ↔ s ⊆ t.preimage f hf :=
  image_subset_iff.trans <| by simp only [subset_iff, mem_preimage]
/-
**Finset.map_subset_iff_subset_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_subset_iff_subset_preimage {f : α ↪ β} {s : Finset α} {t : Finset β} :
 s.map f subseteq t ↔ s subseteq t.preimage f f.injective.injOn
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_subset_iff_subset_preimage`：image_subset_iff_subset_preimag
e [DecidableEq β] {f : α -> β} {s : Finset α} {t : Finset β} (hf : Set.InjOn f (
f ⁻¹' ↑t)) : s.image f subset…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_subset_iff_subset_preimage {f : α ↪ β} {s : Finset α} {t : Finset β} :
    s.map f ⊆ t ↔ s ⊆ t.preimage f f.injective.injOn := by
  classical rw [map_eq_image, image_subset_iff_subset_preimage]
/-
**Finset.card_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_preimage (s : Finset β) (f : α -> β) (hf) [DecidablePred (· in Set.ra
nge f)] : (s.preimage f hf).card = {x in s | x in Set.range f}.card
参数：s : Finset β；f : α -> β；hf；· in Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_nbij`：card_nbij (i : α -> β) (hi : Set.MapsTo i s t) (i_inj 
: (s : Set α).InjOn i) (i_surj : (s : Set α).SurjOn i t) : #s = #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma card_preimage (s : Finset β) (f : α → β) (hf) [DecidablePred (· ∈ Set.range f)] :
    (s.preimage f hf).card = {x ∈ s | x ∈ Set.range f}.card :=
  card_nbij f (by simp [Set.MapsTo]) (by simpa) (fun b hb ↦ by aesop)
/-
**Finset.image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_preimage [DecidableEq β] (f : α -> β) (s : Finset β) [forall x, Deci
dable (x in Set.range f)] (hf : Set.InjOn f (f ⁻¹' ↑s)) : image f (preimage s f 
hf) = {x in s | x in Set.range f}
参数：f : α -> β；s : Finset β；x in Set.range f；hf : Set.InjOn f (f ⁻¹' ↑s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
-/
theorem image_preimage [DecidableEq β] (f : α → β) (s : Finset β) [∀ x, Decidable (x ∈ Set.range f)]
    (hf : Set.InjOn f (f ⁻¹' ↑s)) : image f (preimage s f hf) = {x ∈ s | x ∈ Set.range f} :=
  Finset.coe_inj.1 <| by
    simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range,
      ← Set.sep_mem_eq]; rfl
/-
**Finset.image_eq_preimage_of_leftInvOn_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：image_eq_preimage_of_leftInvOn_injOn {α β : Type*} [DecidableEq β] {f : α 
-> β} {g : β -> α} {s : Finset α} (hgf : Set.LeftInvOn g f s) (ginj : Set.InjOn 
g (g ⁻¹' s)) : s.image f = s.preimage g ginj
参数：hgf : Set.LeftInvOn g f s；ginj : Set.InjOn g (g ⁻¹' s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Set.image_eq_preimage_of_leftInvOn_injOn`：image_eq_preimage_of_leftInvOn
_injOn {f : α -> β} {g : β -> α} {s : Set α} (hgf : LeftInvOn g f s) (ginj : Set
.InjOn g (g ⁻¹' s)) : f '' s =…
-/
theorem image_eq_preimage_of_leftInvOn_injOn {α β : Type*} [DecidableEq β] {f : α → β}
    {g : β → α} {s : Finset α} (hgf : Set.LeftInvOn g f s) (ginj : Set.InjOn g (g ⁻¹' s)) :
    s.image f = s.preimage g ginj := by
  simp only [SetLike.ext'_iff, coe_preimage, coe_image]
  rw [Set.image_eq_preimage_of_leftInvOn_injOn hgf ginj]
/-
**Finset.image_preimage_of_bij** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_preimage_of_bij [DecidableEq β] (f : α -> β) (s : Finset β) (hf : Se
t.BijOn f (f ⁻¹' ↑s) ↑s) : image f (preimage s f hf.injOn) = s
参数：f : α -> β；s : Finset β；hf : Set.BijOn f (f ⁻¹' ↑s) ↑s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
-/
theorem image_preimage_of_bij [DecidableEq β] (f : α → β) (s : Finset β)
    (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) : image f (preimage s f hf.injOn) = s :=
  Finset.coe_inj.1 <| by simpa using hf.image_eq
/-
**Finset.image_preimage_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_preimage_of_bijective [DecidableEq β] {f : α -> β} (s : Finset β) (h
f : Bijective f) : image f (preimage s f (hf.injective.injOn)) = s
参数：s : Finset β；hf : Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_preimage_of_bij`：image_preimage_of_bij [DecidableEq β] (f :
 α -> β) (s : Finset β) (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) : image f (preimage s f
 hf.injOn) = s
· 使用定理 `Function.Bijective.bijOn_preimage`：∀ {α : Type u_1} {β : Type u_2} {t : 
Set β} {f : α → β}, Function.Bijective f → Set.BijOn f (f ⁻¹' t) t
-/
theorem image_preimage_of_bijective [DecidableEq β] {f : α → β} (s : Finset β)
    (hf : Bijective f) : image f (preimage s f (hf.injective.injOn)) = s :=
  image_preimage_of_bij f s hf.bijOn_preimage
/-
**Finset.preimage_subset_of_subset_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：preimage_subset_of_subset_image [DecidableEq β] {f : α -> β} {s : Finset β
} {t : Finset α} (hs : s subseteq t.image f) {hf} : s.preimage f hf subseteq t
参数：hs : s subseteq t.image f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用引理 `Set.preimage_subset`：preimage_subset {s t} (hs : s subseteq f '' t) (hf 
: Set.InjOn f (f ⁻¹' s)) : f ⁻¹' s subseteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
-/
lemma preimage_subset_of_subset_image [DecidableEq β] {f : α → β} {s : Finset β} {t : Finset α}
    (hs : s ⊆ t.image f) {hf} : s.preimage f hf ⊆ t := by
  rw [← coe_subset, coe_preimage]; exact Set.preimage_subset (mod_cast hs) hf
/-
**Finset.preimage_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_subset {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s subseteq
 t.map f) : s.preimage f f.injective.injOn subseteq t
参数：hs : s subseteq t.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_map'`：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map 
f ↔ a in s
· 使用定理 `Finset.mem_preimage`：mem_preimage {f : α -> β} {s : Finset β} {hf : Set.
InjOn f (f ⁻¹' ↑s)} {x : α} : x in preimage s f hf ↔ f x in s
-/
theorem preimage_subset {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s ⊆ t.map f) :
    s.preimage f f.injective.injOn ⊆ t := fun _ h => (mem_map' f).1 (hs (mem_preimage.1 h))
/-
**Finset.subset_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_map_iff {f : α ↪ β} {s : Finset β} {t : Finset α} : s subseteq t.ma
p f ↔ exists u subseteq t, s = u.map f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subset_map_iff {f : α ↪ β} {s : Finset β} {t : Finset α} :
    s ⊆ t.map f ↔ ∃ u ⊆ t, s = u.map f := by
  classical
  simp_rw [map_eq_image, subset_image_iff, eq_comm]
/-
**Finset.image_eq_iff_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_eq_iff_eq_preimage [DecidableEq β] {s : Finset α} {t : Finset β} {f 
: α -> β} (hf : Bijective f) : s.image f = t ↔ s = t.preimage f hf.injective.inj
On
参数：hf : Bijective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.image_inj`：image_inj {t : Finset α} (hf : Injective f) : s.image 
f = t.image f ↔ s = t
· 使用定理 `Finset.image_preimage_of_bijective`：image_preimage_of_bijective [Decidab
leEq β] {f : α -> β} (s : Finset β) (hf : Bijective f) : image f (preimage s f (
hf.injective.injOn)) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem image_eq_iff_eq_preimage [DecidableEq β] {s : Finset α} {t : Finset β}
    {f : α → β} (hf : Bijective f) :
    s.image f = t ↔ s = t.preimage f hf.injective.injOn := by
  rw [← image_inj hf.injective, t.image_preimage_of_bijective hf]

@[simp]
/-
**Finset.sup_preimage_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_preimage_self {α β : Type*} [Nonempty α] [SemilatticeSup β] [OrderBot 
β] {s : Finset β} {f : α -> β} (hf : Set.BijOn f (f ⁻¹' ↑s) s) : (preimage s f h
f.2.1).sup f = s.sup id
参数：hf : Set.BijOn f (f ⁻¹' ↑s) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.BijOn.invOn_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t
 : Set β} {f : α → β} [inst : Nonempty α],   Set.BijOn f s t → Set.InvOn (Functi
on.invFunOn f …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_congr`：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.sup f = s₂.sup g
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.image_eq_preimage_of_leftInvOn_injOn`：image_eq_preimage_of_leftIn
vOn_injOn {α β : Type*} [DecidableEq β] {f : α -> β} {g : β -> α} {s : Finset α}
 (hgf : Set.LeftInvOn g f s) (gin…
-/
theorem sup_preimage_self {α β : Type*} [Nonempty α] [SemilatticeSup β] [OrderBot β]
    {s : Finset β} {f : α → β} (hf : Set.BijOn f (f ⁻¹' ↑s) s) :
    (preimage s f hf.2.1).sup f = s.sup id := by
  classical
  have hfinvs : ∀ x ∈ s, (f ∘ invFunOn f (f ⁻¹' ↑s)) x = id x := hf.invOn_invFunOn.2
  rw [← sup_congr (Eq.refl s) hfinvs, ← sup_image]
  congr
  exact (image_eq_preimage_of_leftInvOn_injOn hf.invOn_invFunOn.2 hf.2.1).symm
/-
**Finset.sup_preimage_val_id** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_preimage_val_id [Lattice α] [OrderBot α] {P : α -> Prop} (Psup : foral
l ⦃s t : α⦄, P s -> P t -> P (s ⊔ t)) (Pbot : P ⊥) {t : Finset α} (ht : forall x
 in t, P x) : letI
参数：Psup : forall ⦃s t : α⦄, P s -> P t -> P (s ⊔ t)；Pbot : P ⊥；ht : forall x in 
t, P x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Finset.sup_induction`：sup_induction {p : α -> Prop} (hb : p ⊥) (hp : for
all a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂)) (hs : forall b in s, p (f b)) : 
p (s.sup f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_coe`：sup_coe {P : α -> Prop} {Pbot : P ⊥} {Psup : forall ⦃x y
⦄, P x -> P y -> P (x ⊔ y)} (t : Finset β) (f : β -> { x : α // P x }) : letI
· 使用定理 `Finset.sup_preimage_self`：sup_preimage_self {α β : Type*} [Nonempty α] [
SemilatticeSup β] [OrderBot β] {s : Finset β} {f : α -> β} (hf : Set.BijOn f (f 
⁻¹' ↑s) s) : (…
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma sup_preimage_val_id [Lattice α] [OrderBot α] {P : α → Prop}
    (Psup : ∀ ⦃s t : α⦄, P s → P t → P (s ⊔ t)) (Pbot : P ⊥) {t : Finset α}
    (ht : ∀ x ∈ t, P x) :
    letI := Subtype.semilatticeSup Psup
    letI := Subtype.orderBot Pbot
    (t.preimage Subtype.val Subtype.val_injective.injOn).sup id =
      (⟨t.sup id, sup_induction Pbot (fun _ h _ => Psup h) ht⟩ : Subtype P) := by
  let : OrderBot (Subtype P) := Subtype.orderBot Pbot
  ext
  simp only [sup_coe, id_eq]
  apply sup_preimage_self
  refine ⟨mapsTo_preimage _ _, injOn_of_injective Subtype.val_injective, ?_⟩
  intro x hx; simpa using ⟨hx, ht x hx⟩
/-
**Finset.sigma_preimage_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigma_preimage_mk {β : α -> Type*} [DecidableEq α] (s : Finset (Σ a, β a))
 (t : Finset α) : t.sigma (fun a => s.preimage (Sigma.mk a) sigma_mk_injective.i
njOn) = {a in s | a.1 in t}
参数：s : Finset (Σ a, β a)；t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sigma_preimage_mk {β : α → Type*} [DecidableEq α] (s : Finset (Σ a, β a)) (t : Finset α) :
    t.sigma (fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) = {a ∈ s | a.1 ∈ t} := by
  ext x
  simp [and_comm]
/-
**Finset.sigma_preimage_mk_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigma_preimage_mk_of_subset {β : α -> Type*} [DecidableEq α] (s : Finset (
Σ a, β a)) {t : Finset α} (ht : s.image Sigma.fst subseteq t) : (t.sigma fun a =
> s.preimage (Sigma.mk a) sigma_mk_injective.injOn) = s
参数：s : Finset (Σ a, β a)；ht : s.image Sigma.fst subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sigma_preimage_mk`：sigma_preimage_mk {β : α -> Type*} [DecidableE
q α] (s : Finset (Σ a, β a)) (t : Finset α) : t.sigma (fun a => s.preimage (Sigm
a.mk a) sigma_…
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.image_subset_iff`：image_subset_iff : s.image f subseteq t ↔ foral
l x in s, f x in t
-/
theorem sigma_preimage_mk_of_subset {β : α → Type*} [DecidableEq α] (s : Finset (Σ a, β a))
    {t : Finset α} (ht : s.image Sigma.fst ⊆ t) :
    (t.sigma fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) = s := by
  rw [sigma_preimage_mk, filter_true_of_mem <| image_subset_iff.1 ht]
/-
**Finset.sigma_image_fst_preimage_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sigma_image_fst_preimage_mk {β : α -> Type*} [DecidableEq α] (s : Finset (
Σ a, β a)) : ((s.image Sigma.fst).sigma fun a => s.preimage (Sigma.mk a) sigma_m
k_injective.injOn) = s
参数：s : Finset (Σ a, β a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sigma_preimage_mk_of_subset`：sigma_preimage_mk_of_subset {β : α -
> Type*} [DecidableEq α] (s : Finset (Σ a, β a)) {t : Finset α} (ht : s.image Si
gma.fst subseteq t) : (t…
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem sigma_image_fst_preimage_mk {β : α → Type*} [DecidableEq α] (s : Finset (Σ a, β a)) :
    ((s.image Sigma.fst).sigma fun a => s.preimage (Sigma.mk a) sigma_mk_injective.injOn) =
      s :=
  s.sigma_preimage_mk_of_subset (Subset.refl _)
/-
**Finset.preimage_inl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u} {β : Type v} (s : Finset (α ⊕ β)), s.preimage Sum.inl ⋯ = s
.toLeft
参数：s : Finset (α ⊕ β)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_inl (s : Finset (α ⊕ β)) :
    s.preimage Sum.inl Sum.inl_injective.injOn = s.toLeft := by
  ext x; simp
/-
**Finset.preimage_inr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u} {β : Type v} (s : Finset (α ⊕ β)), s.preimage Sum.inr ⋯ = s
.toRight
参数：s : Finset (α ⊕ β)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_inr (s : Finset (α ⊕ β)) :
    s.preimage Sum.inr Sum.inr_injective.injOn = s.toRight := by
  ext x; simp

end Preimage
end Finset

namespace Equiv

/-- Given an equivalence `e : α ≃ β` and `s : Finset β`, restrict `e` to an equivalence
from `e ⁻¹' s` to `s`. -/
@[simps]
/-
**Equiv.restrictPreimageFinset** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：restrictPreimageFinset (e : α ≃ β) (s : Finset β) : (s.preimage e e.inject
ive.injOn) ≃ s where toFun a
参数：e : α ≃ β；s : Finset β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given an equivalence `e : α ≃ β` and `s : Finset β`, restrict `e` to an equivale
nce
from `e ⁻¹' s` to `s`.
-/
def restrictPreimageFinset (e : α ≃ β) (s : Finset β) : (s.preimage e e.injective.injOn) ≃ s where
  toFun a := ⟨e a, Finset.mem_preimage.1 a.2⟩
  invFun b := ⟨e.symm b, by simp⟩
  left_inv _ := by simp
  right_inv _ := by simp
/-
**Equiv.image_symm_eq_preimage_of_finset** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：image_symm_eq_preimage_of_finset [DecidableEq α] (e : α ≃ β) (s : Finset β
) : s.image e.symm = s.preimage e e.injective.injOn
参数：e : α ≃ β；s : Finset β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_symm_eq_preimage_of_finset [DecidableEq α] (e : α ≃ β) (s : Finset β) :
    s.image e.symm = s.preimage e e.injective.injOn := by
  grind [Finset.mem_preimage]
/-
**Equiv.image_eq_preimage_symm_of_finset** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：image_eq_preimage_symm_of_finset [DecidableEq β] (e : α ≃ β) (s : Finset α
) : s.image e = s.preimage e.symm e.symm.injective.injOn
参数：e : α ≃ β；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_symm_eq_preimage_of_finset`：image_symm_eq_preimage_of_finset
 [DecidableEq α] (e : α ≃ β) (s : Finset β) : s.image e.symm = s.preimage e e.in
jective.injOn
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma image_eq_preimage_symm_of_finset [DecidableEq β] (e : α ≃ β) (s : Finset α) :
    s.image e = s.preimage e.symm e.symm.injective.injOn :=
  e.symm.image_symm_eq_preimage_of_finset s

end Equiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Reindexing and then restricting to a `Finset` is the same as first restricting to the preimage
of this `Finset` and then reindexing. -/
/-
**Finset.restrict_comp_piCongrLeft** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.restrict_comp_piCongrLeft {π : β -> Type*} (s : Finset β) (e : α ≃ 
β) : s.restrict ∘ ⇑(e.piCongrLeft π) = ⇑((e.restrictPreimageFinset s).piCongrLef
t (fun b : s => (π b))) ∘ (s.preimage e e.injective.injOn).restrict
参数：s : Finset β；e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.piCongrLeft_apply_eq_cast`：piCongrLeft_apply_eq_cast {P : β -> Sor
t v} {e : α ≃ β} (f : (a : α) -> P (e a)) (b : β) : piCongrLeft P e f b = cast (
congr_arg P (e.apply_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Reindexing and then restricting to a `Finset` is the same as first restricting t
o the preimage
of this `Finset` and then reindexing.
-/
lemma Finset.restrict_comp_piCongrLeft {π : β → Type*} (s : Finset β) (e : α ≃ β) :
    s.restrict ∘ ⇑(e.piCongrLeft π) =
    ⇑((e.restrictPreimageFinset s).piCongrLeft (fun b : s ↦ (π b))) ∘
    (s.preimage e e.injective.injOn).restrict := by
  ext x b
  simp only [comp_apply, restrict, Equiv.piCongrLeft_apply_eq_cast,
    Equiv.restrictPreimageFinset_symm_apply_coe]
