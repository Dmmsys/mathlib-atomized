/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Floris van Doorn
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Subsingleton
/-!
# Functions that are eventually constant along a filter

In this file we define a predicate `Filter.EventuallyConst f l` saying that a function `f : α → β`
is eventually equal to a constant along a filter `l`. We also prove some basic properties of these
functions.

## Implementation notes

A naive definition of `Filter.EventuallyConst f l` is `∃ y, ∀ᶠ x in l, f x = y`.
However, this proposition is false for empty `α`, `β`.
Instead, we say that `Filter.map f l` is supported on a subsingleton.
This allows us to drop `[Nonempty _]` assumptions here and there.
-/

@[expose] public section

open Set

variable {α β γ δ : Type*} {l : Filter α} {f : α → β}

namespace Filter

/-- The proposition that a function is eventually constant along a filter on the domain. -/
/-
**Filter.EventuallyConst** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：EventuallyConst (f : α -> β) (l : Filter α) : Prop
参数：f : α -> β；l : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a function is eventually constant along a filter on the dom
ain.
-/
def EventuallyConst (f : α → β) (l : Filter α) : Prop := (map f l).Subsingleton
/-
**Filter.HasBasis.eventuallyConst_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {f : α → β} {ι : Sort u_5} 
{p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Filter.EventuallyConst f l ↔
 ∃ i, p i ∧ ∀ x ∈ s i, ∀ y ∈ s i, f x = f y)
参数：Filter.EventuallyConst f l ↔ ∃ i, p i ∧ ∀ x ∈ s i, ∀ y ∈ s i, f x = f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.subsingleton_iff`：∀ {α : Type u_1} {l : Filter α} {ι : S
ort u_3} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l.Subsingleton ↔ ∃ 
i, p i ∧ (s i).Subsing…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem HasBasis.eventuallyConst_iff {ι : Sort*} {p : ι → Prop} {s : ι → Set α}
    (h : l.HasBasis p s) : EventuallyConst f l ↔ ∃ i, p i ∧ ∀ x ∈ s i, ∀ y ∈ s i, f x = f y :=
  (h.map f).subsingleton_iff.trans <| by simp only [Set.Subsingleton, forall_mem_image]
/-
**Filter.HasBasis.eventuallyConst_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {f : α → β} {ι : Sort u_5} 
{p : ι → Prop} {s : ι → Set α} {x : ι → α},   l.HasBasis p s → (∀ (i : ι), p i →
 x i ∈ s i) → (Filter.EventuallyConst f l ↔ ∃ i, p i ∧ ∀ y ∈ s i, f y = f (x i))
参数：∀ (i : ι), p i → x i ∈ s i；Filter.EventuallyConst f l ↔ ∃ i, p i ∧ ∀ y ∈ s i,
 f y = f (x i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.eventuallyConst_iff`：∀ {α : Type u_1} {β : Type u_2} {l 
: Filter α} {f : α → β} {ι : Sort u_5} {p : ι → Prop} {s : ι → Set α},   l.HasBa
sis p s → (Filter.Eventua…
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem HasBasis.eventuallyConst_iff' {ι : Sort*} {p : ι → Prop} {s : ι → Set α}
    {x : ι → α} (h : l.HasBasis p s) (hx : ∀ i, p i → x i ∈ s i) :
    EventuallyConst f l ↔ ∃ i, p i ∧ ∀ y ∈ s i, f y = f (x i) :=
  h.eventuallyConst_iff.trans <| exists_congr fun i ↦ and_congr_right fun hi ↦
    ⟨fun h ↦ (h · · (x i) (hx i hi)), fun h a ha b hb ↦ h a ha ▸ (h b hb).symm⟩
/-
**Filter.eventuallyConst_iff_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventuallyConst_iff_tendsto [Nonempty β] : EventuallyConst f l ↔ exists x,
 Tendsto f l (pure x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.subsingleton_iff_exists_le_pure`：subsingleton_iff_exists_le_pure 
[Nonempty α] : l.Subsingleton ↔ exists a, l <= pure a
-/
lemma eventuallyConst_iff_tendsto [Nonempty β] :
    EventuallyConst f l ↔ ∃ x, Tendsto f l (pure x) :=
  subsingleton_iff_exists_le_pure

alias ⟨EventuallyConst.exists_tendsto, _⟩ := eventuallyConst_iff_tendsto
/-
**Filter.EventuallyConst.of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventually
Const`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {f : α → β} {x : β},   Filt
er.Tendsto f l (pure x) → Filter.EventuallyConst f l
参数：pure x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventuallyConst_iff_tendsto`：eventuallyConst_iff_tendsto [Nonempt
y β] : EventuallyConst f l ↔ exists x, Tendsto f l (pure x)
-/
theorem EventuallyConst.of_tendsto {x : β} (h : Tendsto f l (pure x)) : EventuallyConst f l :=
  have : Nonempty β := ⟨x⟩; eventuallyConst_iff_tendsto.2 ⟨x, h⟩
/-
**Filter.eventuallyConst_iff_exists_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Filt
er`。
形式化陈述：eventuallyConst_iff_exists_eventuallyEq [Nonempty β] : EventuallyConst f l
 ↔ exists c, f =ᶠ[l] fun _ => c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.subsingleton_iff_exists_singleton_mem`：subsingleton_iff_exists_si
ngleton_mem [Nonempty α] : l.Subsingleton ↔ exists a, {a} in l
-/
theorem eventuallyConst_iff_exists_eventuallyEq [Nonempty β] :
    EventuallyConst f l ↔ ∃ c, f =ᶠ[l] fun _ ↦ c :=
  subsingleton_iff_exists_singleton_mem

alias ⟨EventuallyConst.eventuallyEq_const, _⟩ := eventuallyConst_iff_exists_eventuallyEq
/-
**Filter.eventuallyConst_pred'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyConst_pred' {p : α -> Prop} : EventuallyConst p l ↔ (p =ᶠ[l] fun
 _ => False) ∨ (p =ᶠ[l] fun _ => True)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventuallyConst_pred' {p : α → Prop} :
    EventuallyConst p l ↔ (p =ᶠ[l] fun _ ↦ False) ∨ (p =ᶠ[l] fun _ ↦ True) := by
  simp only [eventuallyConst_iff_exists_eventuallyEq, Prop.exists_iff]
/-
**Filter.eventuallyConst_pred** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyConst_pred {p : α -> Prop} : EventuallyConst p l ↔ (forallᶠ x in
 l, p x) ∨ (forallᶠ x in l, ¬p x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventuallyConst_pred {p : α → Prop} :
    EventuallyConst p l ↔ (∀ᶠ x in l, p x) ∨ (∀ᶠ x in l, ¬p x) := by
  simp [eventuallyConst_pred', or_comm, EventuallyEq]
/-
**Filter.eventuallyConst_set'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyConst_set' {s : Set α} : EventuallyConst s l ↔ (s =ᶠ[l] (∅ : Set
 α)) ∨ s =ᶠ[l] univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventuallyConst_pred'`：eventuallyConst_pred' {p : α -> Prop} : Ev
entuallyConst p l ↔ (p =ᶠ[l] fun _ => False) ∨ (p =ᶠ[l] fun _ => True)
-/
theorem eventuallyConst_set' {s : Set α} :
    EventuallyConst s l ↔ (s =ᶠ[l] (∅ : Set α)) ∨ s =ᶠ[l] univ :=
  eventuallyConst_pred'
/-
**Filter.eventuallyConst_set** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyConst_set {s : Set α} : EventuallyConst s l ↔ (forallᶠ x in l, x
 in s) ∨ (forallᶠ x in l, x ∉ s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventuallyConst_pred`：eventuallyConst_pred {p : α -> Prop} : Even
tuallyConst p l ↔ (forallᶠ x in l, p x) ∨ (forallᶠ x in l, ¬p x)
-/
theorem eventuallyConst_set {s : Set α} :
    EventuallyConst s l ↔ (∀ᶠ x in l, x ∈ s) ∨ (∀ᶠ x in l, x ∉ s) :=
  eventuallyConst_pred
/-
**Filter.eventuallyConst_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventuallyConst_preimage {s : Set β} {f : α -> β} : EventuallyConst (f ⁻¹'
 s) l ↔ EventuallyConst s (map f l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventuallyConst_preimage {s : Set β} {f : α → β} :
    EventuallyConst (f ⁻¹' s) l ↔ EventuallyConst s (map f l) :=
  .rfl
/-
**Filter.EventuallyEq.eventuallyConst_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Even
tuallyEq`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {f g : α → β},   f =ᶠ[l] g 
→ (Filter.EventuallyConst f l ↔ Filter.EventuallyConst g l)
参数：Filter.EventuallyConst f l ↔ Filter.EventuallyConst g l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_congr`：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f
] m₂) : map m₁ f = map m₂ f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem EventuallyEq.eventuallyConst_iff {g : α → β} (h : f =ᶠ[l] g) :
    EventuallyConst f l ↔ EventuallyConst g l := by
  simp only [EventuallyConst, map_congr h]
/-
**Filter.eventuallyConst_id** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {l : Filter α}, Filter.EventuallyConst id l ↔ l.Subsingle
ton
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem eventuallyConst_id : EventuallyConst id l ↔ l.Subsingleton := Iff.rfl

namespace EventuallyConst

/-
**Filter.EventuallyConst.bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyConst`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Filter.EventuallyConst f ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.subsingleton_bot`：subsingleton_bot : Filter.Subsingleton (⊥ : Fil
ter α)
-/
@[simp] protected lemma bot : EventuallyConst f ⊥ := subsingleton_bot

@[simp]
/-
**Filter.EventuallyConst.const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyConst
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} (c : β), Filter.EventuallyC
onst (fun x => c) l
参数：c : β；fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyConst.of_tendsto`：∀ {α : Type u_1} {β : Type u_2} {l : 
Filter α} {f : α → β} {x : β},   Filter.Tendsto f l (pure x) → Filter.Eventually
Const f l
· 使用定理 `Filter.tendsto_const_pure`：tendsto_const_pure {a : Filter α} {b : β} : T
endsto (fun _ => b) a (pure b)
-/
protected lemma const (c : β) : EventuallyConst (fun _ ↦ c) l :=
  .of_tendsto tendsto_const_pure
/-
**Filter.EventuallyConst.congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyConst
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {f g : α → β},   Filter.Eve
ntuallyConst f l → f =ᶠ[l] g → Filter.EventuallyConst g l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.EventuallyEq.eventuallyConst_iff`：∀ {α : Type u_1} {β : Type u_2}
 {l : Filter α} {f g : α → β},   f =ᶠ[l] g → (Filter.EventuallyConst f l ↔ Filte
r.EventuallyConst g l)
-/
protected lemma congr {g} (h : EventuallyConst f l) (hg : f =ᶠ[l] g) : EventuallyConst g l :=
  hg.eventuallyConst_iff.1 h

@[nontriviality]
/-
**Filter.EventuallyConst.of_subsingleton_right** 是 Mathlib 中的一个引理，位于命名空间 `Filter
.EventuallyConst`。
形式化陈述：of_subsingleton_right [Subsingleton β] : EventuallyConst f l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Subsingleton.of_subsingleton`：∀ {α : Type u_1} {l : Filter α} [Su
bsingleton α], l.Subsingleton
-/
lemma of_subsingleton_right [Subsingleton β] : EventuallyConst f l := .of_subsingleton

nonrec lemma anti {l'} (h : EventuallyConst f l) (hl' : l' ≤ l) : EventuallyConst f l' :=
  h.anti (map_mono hl')

@[nontriviality]
/-
**Filter.EventuallyConst.of_subsingleton_left** 是 Mathlib 中的一个引理，位于命名空间 `Filter.
EventuallyConst`。
形式化陈述：of_subsingleton_left [Subsingleton α] : EventuallyConst f l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Subsingleton.map`：∀ {α : Type u_1} {β : Type u_2} {l : Filter α},
 l.Subsingleton → ∀ (f : α → β), (Filter.map f l).Subsingleton
· 使用定理 `Filter.Subsingleton.of_subsingleton`：∀ {α : Type u_1} {l : Filter α} [Su
bsingleton α], l.Subsingleton
-/
lemma of_subsingleton_left [Subsingleton α] : EventuallyConst f l :=
  .map .of_subsingleton f
/-
**Filter.EventuallyConst.comp** 是 Mathlib 中的一个引理，位于命名空间 `Filter.EventuallyConst`
。
形式化陈述：comp (h : EventuallyConst f l) (g : β -> γ) : EventuallyConst (g ∘ f) l
参数：h : EventuallyConst f l；g : β -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Subsingleton.map`：∀ {α : Type u_1} {β : Type u_2} {l : Filter α},
 l.Subsingleton → ∀ (f : α → β), (Filter.map f l).Subsingleton
-/
lemma comp (h : EventuallyConst f l) (g : β → γ) : EventuallyConst (g ∘ f) l := h.map g

@[to_additive]
/-
**Filter.EventuallyConst.inv** 是 Mathlib 中的一个定理，位于命名空间 `Filter.EventuallyConst`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} {f : α → β} [inst : Inv β],
   Filter.EventuallyConst f l → Filter.EventuallyConst f⁻¹ l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyConst.comp`：comp (h : EventuallyConst f l) (g : β -> γ)
 : EventuallyConst (g ∘ f) l
-/
protected lemma inv [Inv β] (h : EventuallyConst f l) : EventuallyConst (f⁻¹) l := h.comp Inv.inv
/-
**Filter.EventuallyConst.comp_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Eventual
lyConst`。
形式化陈述：comp_tendsto {lb : Filter β} {g : β -> γ} (hg : EventuallyConst g lb) (hf 
: Tendsto f l lb) : EventuallyConst (g ∘ f) l
参数：hg : EventuallyConst g lb；hf : Tendsto f l lb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyConst.anti`：∀ {α : Type u_1} {β : Type u_2} {l : Filter
 α} {f : α → β} {l' : Filter α},   Filter.EventuallyConst f l → l' ≤ l → Filter.
EventuallyConst f…
-/
lemma comp_tendsto {lb : Filter β} {g : β → γ} (hg : EventuallyConst g lb)
    (hf : Tendsto f l lb) : EventuallyConst (g ∘ f) l :=
  hg.anti hf
/-
**Filter.EventuallyConst.apply** 是 Mathlib 中的一个引理，位于命名空间 `Filter.EventuallyConst
`。
形式化陈述：apply {ι : Type*} {p : ι -> Type*} {g : α -> forall x, p x} (h : Eventuall
yConst g l) (i : ι) : EventuallyConst (g · i) l
参数：h : EventuallyConst g l；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyConst.comp`：comp (h : EventuallyConst f l) (g : β -> γ)
 : EventuallyConst (g ∘ f) l
-/
lemma apply {ι : Type*} {p : ι → Type*} {g : α → ∀ x, p x}
    (h : EventuallyConst g l) (i : ι) : EventuallyConst (g · i) l :=
  h.comp <| Function.eval i
/-
**Filter.EventuallyConst.comp** 是 Mathlib 中的一个引理，位于命名空间 `Filter.EventuallyConst`
。
形式化陈述：comp (h : EventuallyConst f l) (g : β -> γ) : EventuallyConst (g ∘ f) l
参数：h : EventuallyConst f l；g : β -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Subsingleton.map`：∀ {α : Type u_1} {β : Type u_2} {l : Filter α},
 l.Subsingleton → ∀ (f : α → β), (Filter.map f l).Subsingleton
-/
lemma comp₂ {g : α → γ} (hf : EventuallyConst f l) (op : β → γ → δ) (hg : EventuallyConst g l) :
    EventuallyConst (fun x ↦ op (f x) (g x)) l :=
  ((hf.prod hg).map op.uncurry).anti <|
    (tendsto_map (f := op.uncurry)).comp (tendsto_map.prodMk tendsto_map)
/-
**Filter.EventuallyConst.prodMk** 是 Mathlib 中的一个引理，位于命名空间 `Filter.EventuallyCons
t`。
形式化陈述：prodMk {g : α -> γ} (hf : EventuallyConst f l) (hg : EventuallyConst g l) 
: EventuallyConst (fun x => (f x, g x)) l
参数：hf : EventuallyConst f l；hg : EventuallyConst g l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyConst.comp₂`：comp₂ {g : α -> γ} (hf : EventuallyConst f
 l) (op : β -> γ -> δ) (hg : EventuallyConst g l) : EventuallyConst (fun x => op
 (f x) (g x)) l
-/
lemma prodMk {g : α → γ} (hf : EventuallyConst f l) (hg : EventuallyConst g l) :
    EventuallyConst (fun x ↦ (f x, g x)) l :=
  hf.comp₂ Prod.mk hg

@[to_additive]
/-
**Filter.EventuallyConst.mul** 是 Mathlib 中的一个引理，位于命名空间 `Filter.EventuallyConst`。
形式化陈述：mul [Mul β] {g : α -> β} (hf : EventuallyConst f l) (hg : EventuallyConst 
g l) : EventuallyConst (f * g) l
参数：hf : EventuallyConst f l；hg : EventuallyConst g l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyConst.comp₂`：comp₂ {g : α -> γ} (hf : EventuallyConst f
 l) (op : β -> γ -> δ) (hg : EventuallyConst g l) : EventuallyConst (fun x => op
 (f x) (g x)) l
-/
lemma mul [Mul β] {g : α → β} (hf : EventuallyConst f l) (hg : EventuallyConst g l) :
    EventuallyConst (f * g) l :=
  hf.comp₂ (· * ·) hg

variable [One β] {s : Set α} {c : β}

@[to_additive]
/-
**Filter.EventuallyConst.of_mulIndicator_const** 是 Mathlib 中的一个引理，位于命名空间 `Filter
.EventuallyConst`。
形式化陈述：of_mulIndicator_const (h : EventuallyConst (s.mulIndicator fun _ => c) l) 
(hc : c != 1) : EventuallyConst s l
参数：h : EventuallyConst (s.mulIndicator fun _ => c) l；hc : c != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Filter.EventuallyConst.comp`：comp (h : EventuallyConst f l) (g : β -> γ)
 : EventuallyConst (g ∘ f) l
-/
lemma of_mulIndicator_const (h : EventuallyConst (s.mulIndicator fun _ ↦ c) l) (hc : c ≠ 1) :
    EventuallyConst s l := by
  simpa [Function.comp_def, hc, imp_false] using! h.comp (· = c)

@[to_additive]
/-
**Filter.EventuallyConst.mulIndicator_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Ev
entuallyConst`。
形式化陈述：mulIndicator_const (h : EventuallyConst s l) (c : β) : EventuallyConst (s.
mulIndicator fun _ => c) l
参数：h : EventuallyConst s l；c : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyConst.comp`：comp (h : EventuallyConst f l) (g : β -> γ)
 : EventuallyConst (g ∘ f) l
-/
theorem mulIndicator_const (h : EventuallyConst s l) (c : β) :
    EventuallyConst (s.mulIndicator fun _ ↦ c) l := by
  classical exact h.comp (if · then c else 1)

@[to_additive]
/-
**Filter.EventuallyConst.mulIndicator_const_iff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 
`Filter.EventuallyConst`。
形式化陈述：mulIndicator_const_iff_of_ne (hc : c != 1) : EventuallyConst (s.mulIndicat
or fun _ => c) l ↔ EventuallyConst s l
参数：hc : c != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.EventuallyConst.of_mulIndicator_const`：of_mulIndicator_const (h :
 EventuallyConst (s.mulIndicator fun _ => c) l) (hc : c != 1) : EventuallyConst 
s l
· 使用定理 `Filter.EventuallyConst.mulIndicator_const`：mulIndicator_const (h : Event
uallyConst s l) (c : β) : EventuallyConst (s.mulIndicator fun _ => c) l
-/
theorem mulIndicator_const_iff_of_ne (hc : c ≠ 1) :
    EventuallyConst (s.mulIndicator fun _ ↦ c) l ↔ EventuallyConst s l :=
  ⟨(of_mulIndicator_const · hc), (mulIndicator_const · c)⟩

@[to_additive (attr := simp)]
/-
**Filter.EventuallyConst.mulIndicator_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r.EventuallyConst`。
形式化陈述：mulIndicator_const_iff : EventuallyConst (s.mulIndicator fun _ => c) l ↔ c
 = 1 ∨ EventuallyConst s l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.mulIndicator_one`：mulIndicator_one (s : Set α) : (mulIndicator s fun
 _ => (1 : M)) = fun _ => (1 : M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem mulIndicator_const_iff :
    EventuallyConst (s.mulIndicator fun _ ↦ c) l ↔ c = 1 ∨ EventuallyConst s l := by
  rcases eq_or_ne c 1 with rfl | hc <;> simp [mulIndicator_const_iff_of_ne, *]

end EventuallyConst

/-
**Filter.eventuallyConst_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventuallyConst_atTop [SemilatticeSup α] [Nonempty α] : EventuallyConst f 
atTop ↔ (exists i, forall j, i <= j -> f j = f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.eventuallyConst_iff'`：∀ {α : Type u_1} {β : Type u_2} {l
 : Filter α} {f : α → β} {ι : Sort u_5} {p : ι → Prop} {s : ι → Set α} {x : ι → 
α},   l.HasBasis p s → (∀ …
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma eventuallyConst_atTop [SemilatticeSup α] [Nonempty α] :
    EventuallyConst f atTop ↔ (∃ i, ∀ j, i ≤ j → f j = f i) :=
  (atTop_basis.eventuallyConst_iff' fun _ _ ↦ self_mem_Ici).trans <| by
    simp only [true_and, mem_Ici]
/-
**Filter.eventuallyConst_atTop_nat** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：eventuallyConst_atTop_nat {f : Nat -> α} : EventuallyConst f atTop ↔ exist
s n, forall m, n <= m -> f (m + 1) = f m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventuallyConst_atTop`：eventuallyConst_atTop [SemilatticeSup α] [
Nonempty α] : EventuallyConst f atTop ↔ (exists i, forall j, i <= j -> f j = f i
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
-/
lemma eventuallyConst_atTop_nat {f : ℕ → α} :
    EventuallyConst f atTop ↔ ∃ n, ∀ m, n ≤ m → f (m + 1) = f m := by
  rw [eventuallyConst_atTop]
  refine exists_congr fun n ↦ ⟨fun h m hm ↦ ?_, fun h m hm ↦ ?_⟩
  · exact (h (m + 1) (hm.trans m.le_succ)).trans (h m hm).symm
  · induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ihm => exact (h m hm).trans ihm

end Filter

