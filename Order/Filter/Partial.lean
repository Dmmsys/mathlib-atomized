/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Data.PFun

/-!
# `Tendsto` for relations and partial functions

This file generalizes `Filter` definitions from functions to partial functions and relations.

## Considering functions and partial functions as relations

A function `f : α → β` can be considered as the relation `Rel α β` which relates `x` and `f x` for
all `x`, and nothing else. This relation is called `Function.Graph f`.

A partial function `f : α →. β` can be considered as the relation `Rel α β` which relates `x` and
`f x` for all `x` for which `f x` exists, and nothing else. This relation is called
`PFun.Graph' f`.

In this regard, a function is a relation for which every element in `α` is related to exactly one
element in `β` and a partial function is a relation for which every element in `α` is related to at
most one element in `β`.

This file leverages this analogy to generalize `Filter` definitions from functions to partial
functions and relations.

## Notes

`Set.preimage` can be generalized to relations in two ways:
* `Rel.preimage` returns the image of the set under the inverse relation.
* `Rel.core` returns the set of elements that are only related to those in the set.

Both generalizations are sensible in the context of filters, so `Filter.comap` and `Filter.Tendsto`
get two generalizations each.

We first take care of relations. Then the definitions for partial functions are taken as special
cases of the definitions for relations.
-/

@[expose] public section


universe u v w

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w}

open Filter

/-! ### Relations -/


/-- The forward map of a filter under a relation. Generalization of `Filter.map` to relations. Note
that `Rel.core` generalizes `Set.preimage`. -/
/-
**Filter.rmap** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：rmap (r : SetRel α β) (l : Filter α) : Filter β where sets
参数：r : SetRel α β；l : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward map of a filter under a relation. Generalization of `Filter.map` to 
relations. Note
that `Rel.core` generalizes `Set.preimage`.
-/
def rmap (r : SetRel α β) (l : Filter α) : Filter β where
  sets := { s | r.core s ∈ l }
  univ_sets := by simp
  sets_of_superset hs st := mem_of_superset hs (SetRel.core_mono st)
  inter_sets hs ht := by
    simp only [Set.mem_ofPred_eq]
    convert! inter_mem hs ht
    rw [← SetRel.core_inter]
/-
**Filter.rmap_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：rmap_sets (r : SetRel α β) (l : Filter α) : (l.rmap r).sets = r.core ⁻¹' l
.sets
参数：r : SetRel α β；l : Filter α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rmap_sets (r : SetRel α β) (l : Filter α) : (l.rmap r).sets = r.core ⁻¹' l.sets :=
  rfl

@[simp]
/-
**Filter.mem_rmap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_rmap (r : SetRel α β) (l : Filter α) (s : Set β) : s in l.rmap r ↔ r.c
ore s in l
参数：r : SetRel α β；l : Filter α；s : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_rmap (r : SetRel α β) (l : Filter α) (s : Set β) : s ∈ l.rmap r ↔ r.core s ∈ l :=
  Iff.rfl

@[simp]
/-
**Filter.rmap_rmap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：rmap_rmap (r : SetRel α β) (s : SetRel β γ) (l : Filter α) : rmap s (rmap 
r l) = rmap (r.comp s) l
参数：r : SetRel α β；s : SetRel β γ；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.filter_eq`：∀ {α : Type u_1} {f g : Filter α}, f.sets = g.sets → f
 = g
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
· 使用引理 `SetRel.core_comp`：core_comp : core (R ○ S) u = core R (core S u)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rmap_rmap (r : SetRel α β) (s : SetRel β γ) (l : Filter α) :
    rmap s (rmap r l) = rmap (r.comp s) l :=
  filter_eq <| by simp [rmap_sets, Set.preimage, SetRel.core_comp]

@[simp]
/-
**Filter.rmap_compose** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：rmap_compose (r : SetRel α β) (s : SetRel β γ) : rmap s ∘ rmap r = rmap (r
.comp s)
参数：r : SetRel α β；s : SetRel β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.rmap_rmap`：rmap_rmap (r : SetRel α β) (s : SetRel β γ) (l : Filte
r α) : rmap s (rmap r l) = rmap (r.comp s) l
-/
theorem rmap_compose (r : SetRel α β) (s : SetRel β γ) : rmap s ∘ rmap r = rmap (r.comp s) :=
  funext <| rmap_rmap _ _

/-- Generic "limit of a relation" predicate. `RTendsto r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `r`-core of `a` is an `l₁`-neighborhood. One generalization of
`Filter.Tendsto` to relations. -/
/-
**Filter.RTendsto** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：RTendsto (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β)
参数：r : SetRel α β；l₁ : Filter α；l₂ : Filter β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generic "limit of a relation" predicate. `RTendsto r l₁ l₂` asserts that for eve
ry
`l₂`-neighborhood `a`, the `r`-core of `a` is an `l₁`-neighborhood. One generali
zation of
`Filter.Tendsto` to relations.
-/
def RTendsto (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.rmap r ≤ l₂
/-
**Filter.rtendsto_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：rtendsto_def (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) : RTendsto r
 l₁ l₂ ↔ forall s in l₂, r.core s in l₁
参数：r : SetRel α β；l₁ : Filter α；l₂ : Filter β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rtendsto_def (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto r l₁ l₂ ↔ ∀ s ∈ l₂, r.core s ∈ l₁ :=
  Iff.rfl

/-- One way of taking the inverse map of a filter under a relation. One generalization of
`Filter.comap` to relations. Note that `Rel.core` generalizes `Set.preimage`. -/
/-
**Filter.rcomap** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：rcomap (r : SetRel α β) (f : Filter β) : Filter α where sets
参数：r : SetRel α β；f : Filter β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One way of taking the inverse map of a filter under a relation. One generalizati
on of
`Filter.comap` to relations. Note that `Rel.core` generalizes `Set.preimage`.
-/
def rcomap (r : SetRel α β) (f : Filter β) : Filter α where
  sets := SetRel.image {(s, t) : _ × _ | r.core s ⊆ t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, (r.core_inter a' b').subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩
/-
**Filter.rcomap_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：rcomap_sets (r : SetRel α β) (f : Filter β) : (rcomap r f).sets = SetRel.i
mage {(s, t) : _ × _ | r.core s subseteq t} f.sets
参数：r : SetRel α β；f : Filter β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rcomap_sets (r : SetRel α β) (f : Filter β) :
    (rcomap r f).sets = SetRel.image {(s, t) : _ × _ | r.core s ⊆ t} f.sets :=
  rfl
/-
**Filter.rcomap_rcomap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：rcomap_rcomap (r : SetRel α β) (s : SetRel β γ) (l : Filter γ) : rcomap r 
(rcomap s l) = rcomap (r.comp s) l
参数：r : SetRel α β；s : SetRel β γ；l : Filter γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.filter_eq`：∀ {α : Type u_1} {f g : Filter α}, f.sets = g.sets → f
 = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SetRel.core_comp`：core_comp : core (R ○ S) u = core R (core S u)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `SetRel.core_mono`：core_mono : Monotone R.core
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem rcomap_rcomap (r : SetRel α β) (s : SetRel β γ) (l : Filter γ) :
    rcomap r (rcomap s l) = rcomap (r.comp s) l :=
  filter_eq <| by
    ext t
    simp only [rcomap_sets, SetRel.image, Filter.mem_sets, Set.mem_ofPred_eq, SetRel.core_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, Set.Subset.trans (SetRel.core_mono hv) h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨SetRel.core s t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]
/-
**Filter.rcomap_compose** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：rcomap_compose (r : SetRel α β) (s : SetRel β γ) : rcomap r ∘ rcomap s = r
comap (r.comp s)
参数：r : SetRel α β；s : SetRel β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.rcomap_rcomap`：rcomap_rcomap (r : SetRel α β) (s : SetRel β γ) (l
 : Filter γ) : rcomap r (rcomap s l) = rcomap (r.comp s) l
-/
theorem rcomap_compose (r : SetRel α β) (s : SetRel β γ) :
    rcomap r ∘ rcomap s = rcomap (r.comp s) :=
  funext <| rcomap_rcomap _ _

set_option backward.isDefEq.respectTransparency false in
/-
**Filter.rtendsto_iff_le_rcomap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：rtendsto_iff_le_rcomap (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) : 
RTendsto r l₁ l₂ ↔ l₁ <= l₂.rcomap r
参数：r : SetRel α β；l₁ : Filter α；l₂ : Filter β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.rtendsto_def`：rtendsto_def (r : SetRel α β) (l₁ : Filter α) (l₂ :
 Filter β) : RTendsto r l₁ l₂ ↔ forall s in l₂, r.core s in l₁
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_sets`：∀ {α : Type u_1} {f : Filter α} {s : Set α}, s ∈ f.sets
 ↔ s ∈ f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem rtendsto_iff_le_rcomap (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto r l₁ l₂ ↔ l₁ ≤ l₂.rcomap r := by
  rw [rtendsto_def]
  simp_rw [← l₂.mem_sets]
  constructor
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h s t tl₂ => mem_of_superset (h t tl₂)
  · simpa [Filter.le_def, rcomap, SetRel.mem_image]
      using fun h t tl₂ => h _ t tl₂ Set.Subset.rfl

-- Interestingly, there does not seem to be a way to express this relation using a forward map.
-- Given a filter `f` on `α`, we want a filter `f'` on `β` such that `r.preimage s ∈ f` if
-- and only if `s ∈ f'`. But the intersection of two sets satisfying the lhs may be empty.
/-- One way of taking the inverse map of a filter under a relation. Generalization of `Filter.comap`
to relations. -/
/-
**Filter.rcomap'** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：rcomap' (r : SetRel α β) (f : Filter β) : Filter α where sets
参数：r : SetRel α β；f : Filter β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One way of taking the inverse map of a filter under a relation. Generalization o
f `Filter.comap`
to relations.
-/
def rcomap' (r : SetRel α β) (f : Filter β) : Filter α where
  sets := SetRel.image {(s, t) : _ × _ | r.preimage s ⊆ t} f.sets
  univ_sets := ⟨Set.univ, univ_mem, Set.subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, r.preimage_inter_subset.trans (Set.inter_subset_inter ha₂ hb₂)⟩

@[simp]
/-
**Filter.mem_rcomap'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_rcomap' (r : SetRel α β) (l : Filter β) (s : Set α) : s in l.rcomap' r
 ↔ exists t in l, r.preimage t subseteq s
参数：r : SetRel α β；l : Filter β；s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_rcomap' (r : SetRel α β) (l : Filter β) (s : Set α) :
    s ∈ l.rcomap' r ↔ ∃ t ∈ l, r.preimage t ⊆ s :=
  Iff.rfl
/-
**Filter.rcomap'_sets** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {β : Type v} (r : SetRel α β) (f : Filter β),   (Filter.rco
map' r f).sets = SetRel.image {(s, t) | r.preimage s ⊆ t} f.sets
参数：r : SetRel α β；f : Filter β；Filter.rcomap' r f；s, t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rcomap'_sets (r : SetRel α β) (f : Filter β) :
    (rcomap' r f).sets = SetRel.image {(s, t) | r.preimage s ⊆ t} f.sets :=
  rfl

@[simp]
/-
**Filter.rcomap'_rcomap'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} (r : SetRel α β) (s : SetRel β γ)
 (l : Filter γ),   Filter.rcomap' r (Filter.rcomap' s l) = Filter.rcomap' (r.com
p s) l
参数：r : SetRel α β；s : SetRel β γ；l : Filter γ；Filter.rcomap' s l；r.comp s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SetRel.preimage_comp`：preimage_comp : preimage (R ○ S) u = preimage R (p
reimage S u)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SetRel.preimage_mono`：preimage_mono : Monotone R.preimage
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem rcomap'_rcomap' (r : SetRel α β) (s : SetRel β γ) (l : Filter γ) :
    rcomap' r (rcomap' s l) = rcomap' (r.comp s) l :=
  Filter.ext fun t => by
    simp only [mem_rcomap', SetRel.preimage_comp]
    constructor
    · rintro ⟨u, ⟨v, vsets, hv⟩, h⟩
      exact ⟨v, vsets, (SetRel.preimage_mono hv).trans h⟩
    rintro ⟨t, tsets, ht⟩
    exact ⟨s.preimage t, ⟨t, tsets, Set.Subset.rfl⟩, ht⟩

@[simp]
/-
**Filter.rcomap'_compose** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} (r : SetRel α β) (s : SetRel β γ)
,   Filter.rcomap' r ∘ Filter.rcomap' s = Filter.rcomap' (r.comp s)
参数：r : SetRel α β；s : SetRel β γ；r.comp s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.rcomap'_rcomap'`：∀ {α : Type u} {β : Type v} {γ : Type w} (r : Se
tRel α β) (s : SetRel β γ) (l : Filter γ),   Filter.rcomap' r (Filter.rcomap' s 
l) = Filter.…
-/
theorem rcomap'_compose (r : SetRel α β) (s : SetRel β γ) :
    rcomap' r ∘ rcomap' s = rcomap' (r.comp s) :=
  funext <| rcomap'_rcomap' _ _

/-- Generic "limit of a relation" predicate. `RTendsto' r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `r`-preimage of `a` is an `l₁`-neighborhood. One generalization of
`Filter.Tendsto` to relations. -/
/-
**Filter.RTendsto'** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：RTendsto' (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β)
参数：r : SetRel α β；l₁ : Filter α；l₂ : Filter β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generic "limit of a relation" predicate. `RTendsto' r l₁ l₂` asserts that for ev
ery
`l₂`-neighborhood `a`, the `r`-preimage of `a` is an `l₁`-neighborhood. One gene
ralization of
`Filter.Tendsto` to relations.
-/
def RTendsto' (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ ≤ l₂.rcomap' r

set_option backward.isDefEq.respectTransparency false in
/-
**Filter.rtendsto'_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {β : Type v} (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter 
β),   Filter.RTendsto' r l₁ l₂ ↔ ∀ s ∈ l₂, r.preimage s ∈ l₁
参数：r : SetRel α β；l₁ : Filter α；l₂ : Filter β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
-/
theorem rtendsto'_def (r : SetRel α β) (l₁ : Filter α) (l₂ : Filter β) :
    RTendsto' r l₁ l₂ ↔ ∀ s ∈ l₂, r.preimage s ∈ l₁ := by
  unfold RTendsto' rcomap'; constructor
  · simpa [le_def, SetRel.mem_image] using fun h s hs => h _ _ hs Set.Subset.rfl
  · simpa [le_def, SetRel.mem_image] using fun h s t ht => mem_of_superset (h t ht)
/-
**Filter.tendsto_iff_rtendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α -> β) : Tendst
o f l₁ l₂ ↔ RTendsto (Function.graph f) l₁ l₂
参数：l₁ : Filter α；l₂ : Filter β；f : α -> β。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
    Tendsto f l₁ l₂ ↔ RTendsto (Function.graph f) l₁ l₂ := by
  simp [tendsto_def, Function.graph, rtendsto_def, SetRel.core, Set.preimage]
/-
**Filter.tendsto_iff_rtendsto'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iff_rtendsto' (l₁ : Filter α) (l₂ : Filter β) (f : α -> β) : Tends
to f l₁ l₂ ↔ RTendsto' (Function.graph f) l₁ l₂
参数：l₁ : Filter α；l₂ : Filter β；f : α -> β。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_rtendsto' (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
    Tendsto f l₁ l₂ ↔ RTendsto' (Function.graph f) l₁ l₂ := by
  simp [tendsto_def, Function.graph, rtendsto'_def, SetRel.preimage, Set.preimage]

/-! ### Partial functions -/


/-- The forward map of a filter under a partial function. Generalization of `Filter.map` to partial
functions. -/
/-
**Filter.pmap** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：pmap (f : α ->. β) (l : Filter α) : Filter β
参数：f : α ->. β；l : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward map of a filter under a partial function. Generalization of `Filter.
map` to partial
functions.
-/
def pmap (f : α →. β) (l : Filter α) : Filter β :=
  Filter.rmap f.graph' l

@[simp]
/-
**Filter.mem_pmap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_pmap (f : α ->. β) (l : Filter α) (s : Set β) : s in l.pmap f ↔ f.core
 s in l
参数：f : α ->. β；l : Filter α；s : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pmap (f : α →. β) (l : Filter α) (s : Set β) : s ∈ l.pmap f ↔ f.core s ∈ l :=
  Iff.rfl

/-- Generic "limit of a partial function" predicate. `PTendsto r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `p`-core of `a` is an `l₁`-neighborhood. One generalization of
`Filter.Tendsto` to partial function. -/
/-
**Filter.PTendsto** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：PTendsto (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β)
参数：f : α ->. β；l₁ : Filter α；l₂ : Filter β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generic "limit of a partial function" predicate. `PTendsto r l₁ l₂` asserts that
 for every
`l₂`-neighborhood `a`, the `p`-core of `a` is an `l₁`-neighborhood. One generali
zation of
`Filter.Tendsto` to partial function.
-/
def PTendsto (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.pmap f ≤ l₂
/-
**Filter.ptendsto_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：ptendsto_def (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β) : PTendsto f l₁
 l₂ ↔ forall s in l₂, f.core s in l₁
参数：f : α ->. β；l₁ : Filter α；l₂ : Filter β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ptendsto_def (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :
    PTendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f.core s ∈ l₁ :=
  Iff.rfl
/-
**Filter.ptendsto_iff_rtendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：ptendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α ->. β) : PTen
dsto f l₁ l₂ ↔ RTendsto f.graph' l₁ l₂
参数：l₁ : Filter α；l₂ : Filter β；f : α ->. β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ptendsto_iff_rtendsto (l₁ : Filter α) (l₂ : Filter β) (f : α →. β) :
    PTendsto f l₁ l₂ ↔ RTendsto f.graph' l₁ l₂ :=
  Iff.rfl
/-
**Filter.pmap_res** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pmap_res (l : Filter α) (s : Set α) (f : α -> β) : pmap (PFun.res f s) l =
 map f (l ⊓ 𝓟 s)
参数：l : Filter α；s : Set α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PFun.core_res`：core_res (f : α -> β) (s : Set α) (t : Set β) : (res f s)
.core t = sᶜ union f ⁻¹' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pmap_res (l : Filter α) (s : Set α) (f : α → β) :
    pmap (PFun.res f s) l = map f (l ⊓ 𝓟 s) := by
  ext t
  simp only [PFun.core_res, mem_pmap, mem_map, mem_inf_principal, imp_iff_not_or]
  rfl
/-
**Filter.tendsto_iff_ptendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iff_ptendsto (l₁ : Filter α) (l₂ : Filter β) (s : Set α) (f : α ->
 β) : Tendsto f (l₁ ⊓ 𝓟 s) l₂ ↔ PTendsto (PFun.res f s) l₁ l₂
参数：l₁ : Filter α；l₂ : Filter β；s : Set α；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.pmap_res`：pmap_res (l : Filter α) (s : Set α) (f : α -> β) : pmap
 (PFun.res f s) l = map f (l ⊓ 𝓟 s)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_ptendsto (l₁ : Filter α) (l₂ : Filter β) (s : Set α) (f : α → β) :
    Tendsto f (l₁ ⊓ 𝓟 s) l₂ ↔ PTendsto (PFun.res f s) l₁ l₂ := by
  simp only [Tendsto, PTendsto, pmap_res]
/-
**Filter.tendsto_iff_ptendsto_univ** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iff_ptendsto_univ (l₁ : Filter α) (l₂ : Filter β) (f : α -> β) : T
endsto f l₁ l₂ ↔ PTendsto (PFun.res f Set.univ) l₁ l₂
参数：l₁ : Filter α；l₂ : Filter β；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_iff_ptendsto`：tendsto_iff_ptendsto (l₁ : Filter α) (l₂ : 
Filter β) (s : Set α) (f : α -> β) : Tendsto f (l₁ ⊓ 𝓟 s) l₂ ↔ PTendsto (PFun.re
s f s) l₁ l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iff_ptendsto_univ (l₁ : Filter α) (l₂ : Filter β) (f : α → β) :
    Tendsto f l₁ l₂ ↔ PTendsto (PFun.res f Set.univ) l₁ l₂ := by
  rw [← tendsto_iff_ptendsto]
  simp [principal_univ]

/-- Inverse map of a filter under a partial function. One generalization of `Filter.comap` to
partial functions. -/
/-
**Filter.pcomap'** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：pcomap' (f : α ->. β) (l : Filter β) : Filter α
参数：f : α ->. β；l : Filter β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse map of a filter under a partial function. One generalization of `Filter.
comap` to
partial functions.
-/
def pcomap' (f : α →. β) (l : Filter β) : Filter α :=
  Filter.rcomap' f.graph' l

/-- Generic "limit of a partial function" predicate. `PTendsto' r l₁ l₂` asserts that for every
`l₂`-neighborhood `a`, the `p`-preimage of `a` is an `l₁`-neighborhood. One generalization of
`Filter.Tendsto` to partial functions. -/
/-
**Filter.PTendsto'** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：PTendsto' (f : α ->. β) (l₁ : Filter α) (l₂ : Filter β)
参数：f : α ->. β；l₁ : Filter α；l₂ : Filter β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generic "limit of a partial function" predicate. `PTendsto' r l₁ l₂` asserts tha
t for every
`l₂`-neighborhood `a`, the `p`-preimage of `a` is an `l₁`-neighborhood. One gene
ralization of
`Filter.Tendsto` to partial functions.
-/
def PTendsto' (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁ ≤ l₂.rcomap' f.graph'
/-
**Filter.ptendsto'_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : α →. β) (l₁ : Filter α) (l₂ : Filter β), 
  Filter.PTendsto' f l₁ l₂ ↔ ∀ s ∈ l₂, f.preimage s ∈ l₁
参数：f : α →. β；l₁ : Filter α；l₂ : Filter β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.rtendsto'_def`：∀ {α : Type u} {β : Type v} (r : SetRel α β) (l₁ :
 Filter α) (l₂ : Filter β),   Filter.RTendsto' r l₁ l₂ ↔ ∀ s ∈ l₂, r.preimage s 
∈ l₁
-/
theorem ptendsto'_def (f : α →. β) (l₁ : Filter α) (l₂ : Filter β) :
    PTendsto' f l₁ l₂ ↔ ∀ s ∈ l₂, f.preimage s ∈ l₁ :=
  rtendsto'_def _ _ _
/-
**Filter.ptendsto_of_ptendsto'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：ptendsto_of_ptendsto' {f : α ->. β} {l₁ : Filter α} {l₂ : Filter β} : PTen
dsto' f l₁ l₂ -> PTendsto f l₁ l₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.ptendsto_def`：ptendsto_def (f : α ->. β) (l₁ : Filter α) (l₂ : Fi
lter β) : PTendsto f l₁ l₂ ↔ forall s in l₂, f.core s in l₁
· 使用定理 `Filter.ptendsto'_def`：∀ {α : Type u} {β : Type v} (f : α →. β) (l₁ : Fil
ter α) (l₂ : Filter β),   Filter.PTendsto' f l₁ l₂ ↔ ∀ s ∈ l₂, f.preimage s ∈ l₁
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `PFun.preimage_subset_core`：preimage_subset_core (f : α ->. β) (s : Set β
) : f.preimage s subseteq f.core s
-/
theorem ptendsto_of_ptendsto' {f : α →. β} {l₁ : Filter α} {l₂ : Filter β} :
    PTendsto' f l₁ l₂ → PTendsto f l₁ l₂ := by
  rw [ptendsto_def, ptendsto'_def]
  exact fun h s sl₂ => mem_of_superset (h s sl₂) (PFun.preimage_subset_core _ _)
/-
**Filter.ptendsto'_of_ptendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α →. β} {l₁ : Filter α} {l₂ : Filter β}, 
  f.Dom ∈ l₁ → Filter.PTendsto f l₁ l₂ → Filter.PTendsto' f l₁ l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.ptendsto_def`：ptendsto_def (f : α ->. β) (l₁ : Filter α) (l₂ : Fi
lter β) : PTendsto f l₁ l₂ ↔ forall s in l₂, f.core s in l₁
· 使用定理 `Filter.ptendsto'_def`：∀ {α : Type u} {β : Type v} (f : α →. β) (l₁ : Fil
ter α) (l₂ : Filter β),   Filter.PTendsto' f l₁ l₂ ↔ ∀ s ∈ l₂, f.preimage s ∈ l₁
· 使用定理 `PFun.preimage_eq`：preimage_eq (f : α ->. β) (s : Set β) : f.preimage s =
 f.core s inter f.Dom
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
-/
theorem ptendsto'_of_ptendsto {f : α →. β} {l₁ : Filter α} {l₂ : Filter β} (h : f.Dom ∈ l₁) :
    PTendsto f l₁ l₂ → PTendsto' f l₁ l₂ := by
  rw [ptendsto_def, ptendsto'_def]
  intro h' s sl₂
  rw [PFun.preimage_eq]
  exact inter_mem (h' s sl₂) h

end Filter

