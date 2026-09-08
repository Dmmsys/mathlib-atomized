/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Order.Filter.Prod
public import Mathlib.Order.Filter.Ultrafilter.Defs
/-!
# Subsingleton filters

We say that a filter `l` is a *subsingleton* if there exists a subsingleton set `s ∈ l`.
Equivalently, `l` is either `⊥` or `pure a` for some `a`.
-/

@[expose] public section

open Set
variable {α β : Type*} {l : Filter α}

namespace Filter

/-- We say that a filter is a *subsingleton* if there exists a subsingleton set
that belongs to the filter. -/
/-
**Filter.Subsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → Filter α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a filter is a *subsingleton* if there exists a subsingleton set
that belongs to the filter.
-/
protected def Subsingleton (l : Filter α) : Prop := ∃ s ∈ l, Set.Subsingleton s
/-
**Filter.HasBasis.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {ι : Sort u_3} {p : ι → Prop} {s : ι → Set
 α},   l.HasBasis p s → (l.Subsingleton ↔ ∃ i, p i ∧ (s i).Subsingleton)
参数：l.Subsingleton ↔ ∃ i, p i ∧ (s i).Subsingleton。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
-/
theorem HasBasis.subsingleton_iff {ι : Sort*} {p : ι → Prop} {s : ι → Set α} (h : l.HasBasis p s) :
    l.Subsingleton ↔ ∃ i, p i ∧ (s i).Subsingleton :=
  h.exists_iff fun _ _ hsub h ↦ h.anti hsub
/-
**Filter.Subsingleton.anti** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {l l' : Filter α}, l.Subsingleton → l' ≤ l → l'.Subsingle
ton
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subsingleton.anti {l'} (hl : l.Subsingleton) (hl' : l' ≤ l) : l'.Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; ⟨s, hl' hsl, hs⟩

@[nontriviality]
/-
**Filter.Subsingleton.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Subsingl
eton`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} [Subsingleton α], l.Subsingleton
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Set.subsingleton_univ`：subsingleton_univ [Subsingleton α] : (univ : Set 
α).Subsingleton
-/
theorem Subsingleton.of_subsingleton [Subsingleton α] : l.Subsingleton :=
  ⟨univ, univ_mem, subsingleton_univ⟩
/-
**Filter.Subsingleton.map** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α}, l.Subsingleton → ∀ (f : α 
→ β), (Filter.map f l).Subsingleton
参数：f : α → β；Filter.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
-/
theorem Subsingleton.map (hl : l.Subsingleton) (f : α → β) : (map f l).Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; ⟨f '' s, image_mem_map hsl, hs.image f⟩
/-
**Filter.Subsingleton.prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α},   l.Subsingleton → ∀ {l' :
 Filter β}, l'.Subsingleton → (l ×ˢ l').Subsingleton
参数：l ×ˢ l'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `Set.Subsingleton.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : 
Set β}, s.Subsingleton → t.Subsingleton → (s ×ˢ t).Subsingleton
-/
theorem Subsingleton.prod (hl : l.Subsingleton) {l' : Filter β} (hl' : l'.Subsingleton) :
    (l ×ˢ l').Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; let ⟨t, htl', ht⟩ := hl'; ⟨s ×ˢ t, prod_mem_prod hsl htl', hs.prod ht⟩

@[simp]
/-
**Filter.subsingleton_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：subsingleton_pure {a : α} : Filter.Subsingleton (pure a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem subsingleton_pure {a : α} : Filter.Subsingleton (pure a) :=
  ⟨{a}, rfl, subsingleton_singleton⟩

@[simp]
/-
**Filter.subsingleton_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：subsingleton_bot : Filter.Subsingleton (⊥ : Filter α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
-/
theorem subsingleton_bot : Filter.Subsingleton (⊥ : Filter α) :=
  ⟨∅, trivial, subsingleton_empty⟩

/-- A nontrivial subsingleton filter is equal to `pure a` for some `a`. -/
/-
**Filter.Subsingleton.exists_eq_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Subsingle
ton`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} [l.NeBot], l.Subsingleton → ∃ a, l = pure 
a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.exists_eq_singleton_iff_nonempty_subsingleton`：exists_eq_singleton_i
ff_nonempty_subsingleton : (exists a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.NeBot.le_pure_iff`：∀ {α : Type u} {f : Filter α} {a : α}, f.NeBot
 → (f ≤ pure a ↔ f = pure a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_pure_iff`：le_pure_iff {f : Filter α} {a : α} : f <= pure a ↔ {
a} in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A nontrivial subsingleton filter is equal to `pure a` for some `a`.
-/
theorem Subsingleton.exists_eq_pure [l.NeBot] (hl : l.Subsingleton) : ∃ a, l = pure a := by
  rcases hl with ⟨s, hsl, hs⟩
  rcases exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨nonempty_of_mem hsl, hs⟩ with ⟨a, rfl⟩
  refine ⟨a, (NeBot.le_pure_iff ‹_›).1 ?_⟩
  rwa [le_pure_iff]

/-- A filter is a subsingleton iff it is equal to `⊥` or to `pure a` for some `a`. -/
/-
**Filter.subsingleton_iff_bot_or_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：subsingleton_iff_bot_or_pure : l.Subsingleton ↔ l = ⊥ ∨ exists a, l = pure
 a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Filter.Subsingleton.exists_eq_pure`：∀ {α : Type u_1} {l : Filter α} [l.N
eBot], l.Subsingleton → ∃ a, l = pure a
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A filter is a subsingleton iff it is equal to `⊥` or to `pure a` for some `a`.
-/
theorem subsingleton_iff_bot_or_pure : l.Subsingleton ↔ l = ⊥ ∨ ∃ a, l = pure a := by
  refine ⟨fun hl ↦ ?_, ?_⟩
  · exact (eq_or_neBot l).imp_right (@Subsingleton.exists_eq_pure _ _ · hl)
  · rintro (rfl | ⟨a, rfl⟩) <;> simp

/-- In a nonempty type, a filter is a subsingleton iff
it is less than or equal to a pure filter. -/
/-
**Filter.subsingleton_iff_exists_le_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：subsingleton_iff_exists_le_pure [Nonempty α] : l.Subsingleton ↔ exists a, 
l <= pure a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `Filter.NeBot.le_pure_iff`：∀ {α : Type u} {f : Filter α} {a : α}, f.NeBot
 → (f ≤ pure a ↔ f = pure a)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p

--- 原说明 ---
In a nonempty type, a filter is a subsingleton iff
it is less than or equal to a pure filter.
-/
theorem subsingleton_iff_exists_le_pure [Nonempty α] : l.Subsingleton ↔ ∃ a, l ≤ pure a := by
  rcases eq_or_neBot l with rfl | hbot
  · simp
  · simp [subsingleton_iff_bot_or_pure, ← hbot.le_pure_iff, hbot.ne]
/-
**Filter.subsingleton_iff_exists_singleton_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter
`。
形式化陈述：subsingleton_iff_exists_singleton_mem [Nonempty α] : l.Subsingleton ↔ exis
ts a, {a} in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subsingleton_iff_exists_singleton_mem [Nonempty α] : l.Subsingleton ↔ ∃ a, {a} ∈ l := by
  simp only [subsingleton_iff_exists_le_pure, le_pure_iff]

/-- A subsingleton filter on a nonempty type is less than or equal to `pure a` for some `a`. -/
alias ⟨Subsingleton.exists_le_pure, _⟩ := subsingleton_iff_exists_le_pure

/-
**Filter.Subsingleton.isCountablyGenerated** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Sub
singleton`。
形式化陈述：∀ {α : Type u_1} {l : Filter α}, l.Subsingleton → l.IsCountablyGenerated
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.subsingleton_iff_bot_or_pure`：subsingleton_iff_bot_or_pure : l.Su
bsingleton ↔ l = ⊥ ∨ exists a, l = pure a
· 使用定理 `Filter.isCountablyGenerated_bot`：isCountablyGenerated_bot : IsCountablyG
enerated (⊥ : Filter α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.isCountablyGenerated_pure`：isCountablyGenerated_pure (a : α) : Is
CountablyGenerated (pure a)
-/
lemma Subsingleton.isCountablyGenerated (hl : l.Subsingleton) : IsCountablyGenerated l := by
  rcases subsingleton_iff_bot_or_pure.1 hl with rfl | ⟨x, rfl⟩
  · exact isCountablyGenerated_bot
  · exact isCountablyGenerated_pure x

end Filter

