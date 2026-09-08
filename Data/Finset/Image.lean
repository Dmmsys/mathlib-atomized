/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Finset.Attach
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Fintype.Defs

/-! # Image and map operations on finite sets

This file provides the finite analog of `Set.image`, along with some other similar functions.

Note there are two ways to take the image over a finset; via `Finset.image` which applies the
function then removes duplicates (requiring `DecidableEq`), or via `Finset.map` which exploits
injectivity of the function to avoid needing to deduplicate. Choosing between these is similar to
choosing between `insert` and `Finset.cons`, or between `Finset.union` and `Finset.disjUnion`.

## Main definitions

* `Finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `Finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `Finset.filterMap` Given a function `f : α → Option β`, `s.filterMap f` is the
  image finset in `β`, filtering out `none`s.
* `Finset.subtype`: `s.subtype p` is the finset of `Subtype p` whose elements belong to `s`.
* `Finset.fin`:`s.fin n` is the finset of all elements of `s` less than `n`.
-/

@[expose] public section
assert_not_exists Monoid IsOrderedMonoid

variable {α β γ : Type*}

open Multiset

open Function

namespace Finset

/-! ### map -/


section Map

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
/-
**Finset.map** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：map (f : α ↪ β) (s : Finset α) : Finset β
参数：f : α ↪ β；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f
` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates i
n the image.
-/
def map (f : α ↪ β) (s : Finset α) : Finset β :=
  ⟨s.1.map f, s.2.map f.2⟩

@[simp]
/-
**Finset.map_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.map f
参数：f : α ↪ β；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.map f :=
  rfl

@[simp]
/-
**Finset.map_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅
参数：f : α ↪ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅ :=
  rfl

variable {f : α ↪ β} {s : Finset α}

@[simp, grind =]
/-
**Finset.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
  Multiset.mem_map

-- Higher priority to apply before `mem_map`.
@[simp 1100]
/-
**Finset.mem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_map_equiv {f : α ≃ β} {b : β} : b in s.map f.toEmbedding ↔ f.symm b in
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mem_map_equiv {f : α ≃ β} {b : β} : b ∈ s.map f.toEmbedding ↔ f.symm b ∈ s := by
  simp only [mem_map, Equiv.coe_toEmbedding]
  grind

@[simp 1100]
/-
**Finset.mem_map'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map f ↔ a in s
参数：f : α ↪ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_map_of_injective`：mem_map_of_injective {f : α -> β} (H : Fu
nction.Injective f) {a : α} {s : Multiset α} : f a in map f s ↔ a in s
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem mem_map' (f : α ↪ β) {a} {s : Finset α} : f a ∈ s.map f ↔ a ∈ s :=
  mem_map_of_injective f.2

@[simp 1100]
/-
**Finset.mem_map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_map_mk (f : α -> β) {a : α} {s : Finset α} (hf : Function.Injective f)
 : f a in s.map ⟨f, hf⟩ ↔ a in s
参数：f : α -> β；hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_map'`：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map 
f ↔ a in s
-/
theorem mem_map_mk (f : α → β) {a : α} {s : Finset α} (hf : Function.Injective f) :
    f a ∈ s.map ⟨f, hf⟩ ↔ a ∈ s :=
  Finset.mem_map' _
/-
**Finset.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a in s -> f a in s.map f
参数：f : α ↪ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_map'`：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map 
f ↔ a in s
-/
theorem mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a ∈ s → f a ∈ s.map f :=
  (mem_map' _).2
/-
**Finset.forall_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_mem_map {f : α ↪ β} {s : Finset α} {p : forall a, a in s.map f -> P
rop} : (forall y (H : y in s.map f), p y H) ↔ forall x (H : x in s), p (f x) (me
m_map_of_mem _ H)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_mem_map {f : α ↪ β} {s : Finset α} {p : ∀ a, a ∈ s.map f → Prop} :
    (∀ y (H : y ∈ s.map f), p y H) ↔ ∀ x (H : x ∈ s), p (f x) (mem_map_of_mem _ H) := by grind
/-
**Finset.apply_coe_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：apply_coe_mem_map (f : α ↪ β) (s : Finset α) (x : s) : f x in s.map f
参数：f : α ↪ β；s : Finset α；x : s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_map_of_mem`：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a
 in s -> f a in s.map f
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem apply_coe_mem_map (f : α ↪ β) (s : Finset α) (x : s) : f x ∈ s.map f :=
  mem_map_of_mem f x.prop

@[simp, norm_cast]
/-
**Finset.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) = f '' s
参数：f : α ↪ β；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) = f '' s := by grind
/-
**Finset.coe_map_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_map_subset_range (f : α ↪ β) (s : Finset α) : (s.map f : Set β) subset
eq Set.range f
参数：f : α ↪ β；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map_subset_range (f : α ↪ β) (s : Finset α) : (s.map f : Set β) ⊆ Set.range f := by
  grind

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
/-
**Finset.map_perm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_perm {σ : Equiv.Perm α} (hs : { a | σ a != a } subseteq s) : s.map (σ 
: α ↪ α) = s
参数：hs : { a | σ a != a } subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_perm`：image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α 
| σ a != a } subseteq s) : σ '' s = s

--- 原说明 ---
If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ
` has no effect.
-/
theorem map_perm {σ : Equiv.Perm α} (hs : { a | σ a ≠ a } ⊆ s) : s.map (σ : α ↪ α) = s :=
  coe_injective <| (coe_map _ _).trans <| Set.image_perm hs
/-
**Finset.map_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_toFinset [DecidableEq α] [DecidableEq β] {s : Multiset α} : s.toFinset
.map f = (s.map f).toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
theorem map_toFinset [DecidableEq α] [DecidableEq β] {s : Multiset α} :
    s.toFinset.map f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_map, Multiset.mem_map, Multiset.mem_toFinset]

@[simp]
/-
**Finset.map_refl** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_refl : s.map (Embedding.refl _) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_eq_right`：∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∃ a, p a ∧ a
 = a') ↔ p a'
-/
theorem map_refl : s.map (Embedding.refl _) = s :=
  ext fun _ => by simpa only [mem_map, exists_prop] using! exists_eq_right

@[simp]
/-
**Finset.map_cast_heq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_cast_heq {α β} (h : α = β) (s : Finset α) : s.map (Equiv.cast h).toEmb
edding ≍ s
参数：h : α = β；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_refl`：map_refl : s.map (Embedding.refl _) = s
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_cast_heq {α β} (h : α = β) (s : Finset α) :
    s.map (Equiv.cast h).toEmbedding ≍ s := by
  subst h
  simp
/-
**Finset.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map f).map g = s.map (
f.trans g)
参数：f : α ↪ β；g : β ↪ γ；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map f).map g = s.map (f.trans g) :=
  eq_of_veq <| by simp only [map_val, Multiset.map_map]; rfl
/-
**Finset.map_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ} (h_comm 
: forall a, f (g a) = g' (f' a)) : (s.map g).map f = (s.map f').map g'
参数：h_comm : forall a, f (g a) = g' (f' a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.map g).map f = (s.map f').map g' := by
  simp_rw [map_map, Embedding.trans, Function.comp_def, h_comm]
/-
**Finset._root_.Function.Semiconj.finset_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Semiconj.finset_map {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) := fun _ =>
  map_comm h
/-
**Finset._root_.Function.Commute.finset_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Commute.finset_map {f g : α ↪ α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  Function.Semiconj.finset_map h

@[simp, gcongr]
/-
**Finset.map_subset_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_subset_map {s₁ s₂ : Finset α} : s₁.map f subseteq s₂.map f ↔ s₁ subset
eq s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_map'`：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map 
f ↔ a in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Multiset.map_subset_map`：map_subset_map {f : α -> β} {s t : Multiset α} 
(H : s subseteq t) : map f s subseteq map f t
-/
theorem map_subset_map {s₁ s₂ : Finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
  ⟨fun h _ xs => (mem_map' _).1 <| h <| (mem_map' f).2 xs,
   fun h => by simp [subset_def, Multiset.map_subset_map h]⟩

/-- The `Finset` version of `Equiv.subset_symm_image`. -/
/-
**Finset.subset_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_map_symm {t : Finset β} {f : α ≃ β} : s subseteq t.map f.symm ↔ s.m
ap f subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
The `Finset` version of `Equiv.subset_symm_image`.
-/
theorem subset_map_symm {t : Finset β} {f : α ≃ β} : s ⊆ t.map f.symm ↔ s.map f ⊆ t := by
  constructor <;> intro h x hx
  · simp only [mem_map_equiv] at hx
    simpa using h hx
  · simp only [mem_map_equiv]
    exact h (by simp [hx])

/-- The `Finset` version of `Equiv.symm_image_subset`. -/
/-
**Finset.map_symm_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_symm_subset {t : Finset β} {f : α ≃ β} : t.map f.symm subseteq s ↔ t s
ubseteq s.map f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The `Finset` version of `Equiv.symm_image_subset`.
-/
theorem map_symm_subset {t : Finset β} {f : α ≃ β} : t.map f.symm ⊆ s ↔ t ⊆ s.map f := by
  simp only [← subset_map_symm, Equiv.symm_symm]

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a finset to its
image under `f`. -/
/-
**Finset.mapEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：mapEmbedding (f : α ↪ β) : Finset α ↪o Finset β
参数：f : α ↪ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_subset_map`：map_subset_map {s₁ s₂ : Finset α} : s₁.map f subs
eteq s₂.map f ↔ s₁ subseteq s₂

--- 原说明 ---
Associate to an embedding `f` from `α` to `β` the order embedding that maps a fi
nset to its
image under `f`.
-/
def mapEmbedding (f : α ↪ β) : Finset α ↪o Finset β :=
  OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_subset_map

@[simp]
/-
**Finset.map_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_inj {s₁ s₂ : Finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem map_inj {s₁ s₂ : Finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
  (mapEmbedding f).injective.eq_iff
/-
**Finset.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_injective (f : α ↪ β) : Injective (map f)
参数：f : α ↪ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem map_injective (f : α ↪ β) : Injective (map f) :=
  (mapEmbedding f).injective

@[simp, gcongr]
/-
**Finset.map_ssubset_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_ssubset_map {s t : Finset α} : s.map f ⊂ t.map f ↔ s ⊂ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem map_ssubset_map {s t : Finset α} : s.map f ⊂ t.map f ↔ s ⊂ t := (mapEmbedding f).lt_iff_lt

@[simp]
/-
**Finset.mapEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mapEmbedding_apply : mapEmbedding f s = map f s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEmbedding_apply : mapEmbedding f s = map f s :=
  rfl
/-
**Finset.filter_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_map {p : β -> Prop} [DecidablePred p] : (s.map f).filter p = (s.fil
ter (p ∘ f)).map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.filter_map`：filter_map (f : β -> α) (s : Multiset β) : filter p
 (map f s) = map f (filter (p ∘ f) s)
-/
theorem filter_map {p : β → Prop} [DecidablePred p] :
    (s.map f).filter p = (s.filter (p ∘ f)).map f :=
  eq_of_veq (Multiset.filter_map _ _ _)
/-
**Finset.map_filter'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_filter' (p : α -> Prop) [DecidablePred p] (f : α ↪ β) (s : Finset α) [
DecidablePred (exists a, p a ∧ f a = ·)] : (s.filter p).map f = (s.map f).filter
 fun b => exists a, p a ∧ f a = b
参数：p : α -> Prop；f : α ↪ β；s : Finset α；exists a, p a ∧ f a = ·。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_map`：filter_map {p : β -> Prop} [DecidablePred p] : (s.map
 f).filter p = (s.filter (p ∘ f)).map f
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_filter' (p : α → Prop) [DecidablePred p] (f : α ↪ β) (s : Finset α)
    [DecidablePred (∃ a, p a ∧ f a = ·)] :
    (s.filter p).map f = (s.map f).filter fun b => ∃ a, p a ∧ f a = b := by
  simp [filter_map]

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.filter_attach'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_attach' [DecidableEq α] (s : Finset α) (p : s -> Prop) [DecidablePr
ed p] : s.attach.filter p = (s.filter fun x => exists h, p ⟨x, h⟩).attach.map ⟨S
ubtype.map id filter_subset _ _, Subtype.map_injective _ injective_id⟩
参数：s : Finset α；p : s -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Subtype.map_injective`：map_injective {p : α -> Prop} {q : β -> Prop} {f 
: α -> β} (h : forall a, p a -> q (f a)) (hf : Injective f) : Injective (map f h
)
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用引理 `Multiset.filter_attach'`：filter_attach' (s : Multiset α) (p : {a // a in
 s} -> Prop) [DecidableEq α] [DecidablePred p] : s.attach.filter p = (s.filter f
un x => exist…
-/
lemma filter_attach' [DecidableEq α] (s : Finset α) (p : s → Prop) [DecidablePred p] :
    s.attach.filter p =
      (s.filter fun x => ∃ h, p ⟨x, h⟩).attach.map
        ⟨Subtype.map id <| filter_subset _ _, Subtype.map_injective _ injective_id⟩ :=
  eq_of_veq <| Multiset.filter_attach' _ _
/-
**Finset.filter_attach** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_attach (p : α -> Prop) [DecidablePred p] (s : Finset α) : s.attach.
filter (fun a : s => p a) = (s.filter p).attach.map ((Embedding.refl _).subtypeM
ap mem_of_mem_filter)
参数：p : α -> Prop；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s
· 使用引理 `Multiset.filter_attach`：filter_attach (s : Multiset α) (p : α -> Prop) [
DecidablePred p] : (s.attach.filter fun a : {a // a in s} => p ↑a) = (s.filter p
).attach.map…
-/
lemma filter_attach (p : α → Prop) [DecidablePred p] (s : Finset α) :
    s.attach.filter (fun a : s ↦ p a) =
      (s.filter p).attach.map ((Embedding.refl _).subtypeMap mem_of_mem_filter) :=
  eq_of_veq <| Multiset.filter_attach _ _
/-
**Finset.map_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_filter {f : α ≃ β} {p : α -> Prop} [DecidablePred p] : (s.filter p).ma
p f.toEmbedding = (s.map f.toEmbedding).filter (p ∘ f.symm)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_map`：filter_map {p : β -> Prop} [DecidablePred p] : (s.map
 f).filter p = (s.filter (p ∘ f)).map f
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_filter {f : α ≃ β} {p : α → Prop} [DecidablePred p] :
    (s.filter p).map f.toEmbedding = (s.map f.toEmbedding).filter (p ∘ f.symm) := by
  simp only [filter_map, Function.comp_def, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

@[simp]
/-
**Finset.disjoint_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_map {s t : Finset α} (f : α ↪ β) : Disjoint (s.map f) (t.map f) ↔
 Disjoint s t
参数：f : α ↪ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.disjoint_image_iff`：disjoint_image_iff (hf : Injective f) : Disjoint
 (f '' s) (f '' t) ↔ Disjoint s t
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem disjoint_map {s t : Finset α} (f : α ↪ β) :
    Disjoint (s.map f) (t.map f) ↔ Disjoint s t :=
  mod_cast Set.disjoint_image_iff f.injective (s := s) (t := t)
/-
**Finset.map_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_disjUnion {f : α ↪ β} (s₁ s₂ : Finset α) (h) (h'
参数：s₁ s₂ : Finset α；h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
-/
theorem map_disjUnion {f : α ↪ β} (s₁ s₂ : Finset α) (h) (h' := (disjoint_map _).mpr h) :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  eq_of_veq <| Multiset.map_add _ _ _

/-- A version of `Finset.map_disjUnion` for writing in the other direction. -/
/-
**Finset.map_disjUnion'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_disjUnion' {f : α ↪ β} (s₁ s₂ : Finset α) (h') (h
参数：s₁ s₂ : Finset α；h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_disjUnion`：map_disjUnion {f : α ↪ β} (s₁ s₂ : Finset α) (h) (
h'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_map`：disjoint_map {s t : Finset α} (f : α ↪ β) : Disjoin
t (s.map f) (t.map f) ↔ Disjoint s t

--- 原说明 ---
A version of `Finset.map_disjUnion` for writing in the other direction.
-/
theorem map_disjUnion' {f : α ↪ β} (s₁ s₂ : Finset α) (h') (h := (disjoint_map _).mp h') :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  map_disjUnion _ _ _
/-
**Finset.map_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
 (s₁ union s₂).map f = s₁.map f union s₂.map f
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
-/
theorem map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
  mod_cast Set.image_union f s₁ s₂
/-
**Finset.map_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
 (s₁ inter s₂).map f = s₁.map f inter s₂.map f
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
  mod_cast Set.image_inter f.injective (s := s₁) (t := s₂)
/-
**Finset.map_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_sdiff [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
 (s₁ \ s₂).map f = s₁.map f \ s₂.map f
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem map_sdiff [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ \ s₂).map f = s₁.map f \ s₂.map f :=
  mod_cast Set.image_sdiff f.injective (s := s₁) (t := s₂)

@[simp]
/-
**Finset.map_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a}
参数：f : α ↪ β；a : α。
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
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
  coe_injective <| by simp only [coe_map, coe_singleton, Set.image_singleton]

@[simp]
/-
**Finset.map_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset
 α) : (insert a s).map f = insert (f a) (s.map f)
参数：f : α ↪ β；a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_union`：map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} 
(s₁ s₂ : Finset α) : (s₁ union s₂).map f = s₁.map f union s₂.map f
· 使用定理 `Finset.map_singleton`：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f
 a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset α) :
    (insert a s).map f = insert (f a) (s.map f) := by
  simp only [insert_eq, map_union, map_singleton]

@[simp]
/-
**Finset.map_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_cons (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s) : (cons a s ha).m
ap f = cons (f a) (s.map f) (by simpa using ha)
参数：f : α ↪ β；a : α；s : Finset α；ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem map_cons (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s) :
    (cons a s ha).map f = cons (f a) (s.map f) (by simpa using ha) :=
  eq_of_veq <| Multiset.map_cons f a s.val

@[simp]
/-
**Finset.map_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_eq_empty : s.map f = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Finset.map_injective`：map_injective (f : α ↪ β) : Injective (map f)
· 使用定理 `Finset.map_empty`：map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅
-/
theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ := (map_injective f).eq_iff' (map_empty f)

@[simp]
/-
**Finset.empty_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_eq_map : ∅ = s.map f ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.map_eq_empty`：map_eq_empty : s.map f = ∅ ↔ s = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem empty_eq_map : ∅ = s.map f ↔ s = ∅ := by rw [eq_comm, map_eq_empty]

@[simp]
/-
**Finset.map_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_nonempty : (s.map f).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
-/
theorem map_nonempty : (s.map f).Nonempty ↔ s.Nonempty :=
  mod_cast Set.image_nonempty (f := f) (s := s)

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.map⟩ := map_nonempty

@[simp]
/-
**Finset.map_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_nontrivial : (s.map f).Nontrivial ↔ s.Nontrivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_nontrivial`：image_nontrivial (hf : f.Injective) : (f '' s).Non
trivial ↔ s.Nontrivial
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem map_nontrivial : (s.map f).Nontrivial ↔ s.Nontrivial :=
  mod_cast Set.image_nontrivial f.injective (s := s)
/-
**Finset.attach_map_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：attach_map_val {s : Finset α} : s.attach.map (Embedding.subtype _) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_val`：map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.m
ap f
· 使用定理 `Finset.attach_val`：attach_val (s : Finset α) : s.attach.1 = s.1.attach
· 使用定理 `Multiset.attach_map_val`：attach_map_val (s : Multiset α) : s.attach.map 
Subtype.val = s
-/
theorem attach_map_val {s : Finset α} : s.attach.map (Embedding.subtype _) = s :=
  eq_of_veq <| by rw [map_val, attach_val]; exact Multiset.attach_map_val _

variable (f s) in
/-- A `Finset` is in bijection with its image under an `Embedding`. -/
@[simps!]
/-
**Finset.equivMap** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：equivMap : s ≃ s.map f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Finset` is in bijection with its image under an `Embedding`.
-/
noncomputable def equivMap : s ≃ s.map f :=
  .ofBijective (fun x ↦ ⟨f x, s.mem_map_of_mem f x.2⟩) (⟨fun x y ↦ by simp, fun ⟨x, hx⟩ ↦ by
    obtain ⟨x, hxs, rfl⟩ := mem_map.mp hx
    exact ⟨⟨x, hxs⟩, rfl⟩⟩)

end Map

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.range_add_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_add_one' (n : Nat) : range (n + 1) = insert 0 ((range n).map ⟨fun i 
=> i + 1, fun i j => by simp⟩)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem range_add_one' (n : ℕ) :
    range (n + 1) = insert 0 ((range n).map ⟨fun i => i + 1, fun i j => by simp⟩) := by
  ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.zero_lt_succ n]

/-! ### image -/


section Image

variable [DecidableEq β]

/-- `image f s` is the forward image of `s` under `f`. -/
/-
**Finset.image** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：image (f : α -> β) (s : Finset α) : Finset β
参数：f : α -> β；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`image f s` is the forward image of `s` under `f`.
-/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset

@[simp]
/-
**Finset.image_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_val (f : α -> β) (s : Finset α) : (image f s).1 = (s.1.map f).dedup
参数：f : α -> β；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_val (f : α → β) (s : Finset α) : (image f s).1 = (s.1.map f).dedup :=
  rfl

@[simp]
/-
**Finset.image_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_empty (f : α -> β) : (∅ : Finset α).image f = ∅
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_empty (f : α → β) : (∅ : Finset α).image f = ∅ :=
  rfl

variable {f g : α → β} {s : Finset α} {t : Finset β} {a : α} {b c : β}

@[simp, grind =]
/-
**Finset.mem_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_image : b in s.image f ↔ exists a in s, f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem mem_image : b ∈ s.image f ↔ ∃ a ∈ s, f a = b := by
  simp only [mem_def, image_val, mem_dedup, Multiset.mem_map]
/-
**Finset.mem_image_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_image_of_mem (f : α -> β) {a} (h : a in s) : f a in s.image f
参数：f : α -> β；h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
-/
theorem mem_image_of_mem (f : α → β) {a} (h : a ∈ s) : f a ∈ s.image f :=
  mem_image.2 ⟨_, h, rfl⟩
/-
**Finset.forall_mem_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：forall_mem_image {p : β -> Prop} : (forall y in s.image f, p y) ↔ forall ⦃
x⦄, x in s -> p (f x)
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
lemma forall_mem_image {p : β → Prop} : (∀ y ∈ s.image f, p y) ↔ ∀ ⦃x⦄, x ∈ s → p (f x) := by simp
/-
**Finset.exists_mem_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_mem_image {p : β -> Prop} : (exists y in s.image f, p y) ↔ exists x
 in s, p (f x)
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
lemma exists_mem_image {p : β → Prop} : (∃ y ∈ s.image f, p y) ↔ ∃ x ∈ s, p (f x) := by simp
/-
**Finset.map_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f = s.image f
参数：f : α ↪ β；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem map_eq_image (f : α ↪ β) (s : Finset α) : s.map f = s.image f :=
  eq_of_veq (s.map f).2.dedup.symm

-- Not `@[simp]` since `mem_image` already gets most of the way there.
/-
**Finset.mem_image_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_image_const : c in s.image (const α b) ↔ s.Nonempty ∧ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_image_const : c ∈ s.image (const α b) ↔ s.Nonempty ∧ b = c := by
  grind
/-
**Finset.mem_image_const_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_image_const_self : b in s.image (const α b) ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_image_const`：mem_image_const : c in s.image (const α b) ↔ s.N
onempty ∧ b = c
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
-/
theorem mem_image_const_self : b ∈ s.image (const α b) ↔ s.Nonempty :=
  mem_image_const.trans <| and_iff_left rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.canLift** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：canLift (c) (p) [CanLift β α c p] : CanLift (Finset β) (Finset α) (image c
) fun s => forall x in s, p x where prf
参数：c；p。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
instance canLift (c) (p) [CanLift β α c p] :
    CanLift (Finset β) (Finset α) (image c) fun s => ∀ x ∈ s, p x where
  prf := by
    rintro ⟨⟨l⟩, hd : l.Nodup⟩ hl
    lift l to List α using hl
    exact ⟨⟨l, hd.of_map _⟩, ext fun a => by simp⟩
/-
**Finset.image_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_congr (h : (s : Set α).EqOn f g) : Finset.image f s = Finset.image g
 s
参数：h : (s : Set α).EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem image_congr (h : (s : Set α).EqOn f g) : Finset.image f s = Finset.image g s := by
  ext
  simp_rw [mem_image, ← bex_def]
  exact exists₂_congr fun x hx => by rw [h hx]
/-
**Finset._root_.Function.Injective.mem_finset_image** 是 Mathlib 中的一个定理，位于命名空间 `F
inset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.mem_finset_image (hf : Injective f) :
    f a ∈ s.image f ↔ a ∈ s := by
  grind


@[simp, norm_cast]
/-
**Finset.coe_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_image : ↑(s.image f) = f '' ↑s
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coe_image : ↑(s.image f) = f '' ↑s :=
  Set.ext <| by simp only [mem_coe, mem_image, Set.mem_image, implies_true]

@[simp]
/-
**Finset.image_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_nonempty : (s.image f).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
-/
lemma image_nonempty : (s.image f).Nonempty ↔ s.Nonempty :=
  mod_cast Set.image_nonempty (f := f) (s := (s : Set α))

@[aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.Nonempty.image** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] {s : Finset α},   s
.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
参数：f : α → β；Finset.image f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.image_nonempty`：image_nonempty : (s.image f).Nonempty ↔ s.Nonempt
y
-/
protected theorem Nonempty.image (h : s.Nonempty) (f : α → β) : (s.image f).Nonempty :=
  image_nonempty.2 h

alias ⟨Nonempty.of_image, _⟩ := image_nonempty

/-- If the image of a finset is nontrivial, the finset is nontrivial.
For the converse direction under an injectivity hypothesis see `Finset.Nontrivial.image_of_injOn`,
and for the combined iff see `Finset.image_nontrivial_iff_of_injOn`. -/
/-
**Finset.nontrivial_of_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nontrivial_of_image (h : (s.image f).Nontrivial) : s.Nontrivial
参数：h : (s.image f).Nontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_of_image`：nontrivial_of_image (f : α -> β) (s : Set α) (h
s : (f '' s).Nontrivial) : s.Nontrivial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s

--- 原说明 ---
If the image of a finset is nontrivial, the finset is nontrivial.
For the converse direction under an injectivity hypothesis see `Finset.Nontrivia
l.image_of_injOn`,
and for the combined iff see `Finset.image_nontrivial_iff_of_injOn`.
-/
theorem nontrivial_of_image (h : (s.image f).Nontrivial) : s.Nontrivial := by
  simp only [Finset.Nontrivial, coe_image] at h ⊢
  exact Set.nontrivial_of_image _ _ h

/-- The image of a nontrivial finset under a function injective on the finset is nontrivial.
For the version assuming `Function.Injective` see `Finset.map_nontrivial`, and for the combined
iff see `Finset.image_nontrivial_iff_of_injOn`. -/
/-
**Finset.Nontrivial.image_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nontrivial`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] {f : α → β} {s : Fi
nset α},   s.Nontrivial → Set.InjOn f ↑s → (Finset.image f s).Nontrivial
参数：Finset.image f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f

--- 原说明 ---
The image of a nontrivial finset under a function injective on the finset is non
trivial.
For the version assuming `Function.Injective` see `Finset.map_nontrivial`, and f
or the combined
iff see `Finset.image_nontrivial_iff_of_injOn`.
-/
protected theorem Nontrivial.image_of_injOn (hs : s.Nontrivial) (hf : Set.InjOn f s) :
    (s.image f).Nontrivial := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩

/-- A finset is nontrivial iff its image under a function injective on the finset is. -/
/-
**Finset.image_nontrivial_iff_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_nontrivial_iff_of_injOn (hf : Set.InjOn f s) : (s.image f).Nontrivia
l ↔ s.Nontrivial
参数：hf : Set.InjOn f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nontrivial_of_image`：nontrivial_of_image (h : (s.image f).Nontriv
ial) : s.Nontrivial
· 使用定理 `Finset.Nontrivial.image_of_injOn`：∀ {α : Type u_1} {β : Type u_2} [inst 
: DecidableEq β] {f : α → β} {s : Finset α},   s.Nontrivial → Set.InjOn f ↑s → (
Finset.image f s).Nont…

--- 原说明 ---
A finset is nontrivial iff its image under a function injective on the finset is
.
-/
theorem image_nontrivial_iff_of_injOn (hf : Set.InjOn f s) :
    (s.image f).Nontrivial ↔ s.Nontrivial :=
  ⟨nontrivial_of_image, (·.image_of_injOn hf)⟩
/-
**Finset.image_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_toFinset [DecidableEq α] {s : Multiset α} : s.toFinset.image f = (s.
map f).toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
theorem image_toFinset [DecidableEq α] {s : Multiset α} :
    s.toFinset.image f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_image, Multiset.mem_toFinset, Multiset.mem_map]
/-
**Finset.image_val_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_val_of_injOn (H : Set.InjOn f s) : (image f s).1 = s.1.map f
参数：H : Set.InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Multiset.Nodup.map_on`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {f
 : α → β},   (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → s.Nodup → (Multiset.map f s
).Nodup
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem image_val_of_injOn (H : Set.InjOn f s) : (image f s).1 = s.1.map f :=
  (s.2.map_on H).dedup

@[simp]
/-
**Finset.image_id** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_id [DecidableEq α] : s.image id = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_id [DecidableEq α] : s.image id = s :=
  ext fun _ => by simp only [mem_image, id, exists_eq_right]

@[simp]
/-
**Finset.image_id'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_id' [DecidableEq α] : (s.image fun x => x) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_id`：image_id [DecidableEq α] : s.image id = s
-/
theorem image_id' [DecidableEq α] : (s.image fun x => x) = s :=
  image_id
/-
**Finset.image_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_image [DecidableEq γ] {g : β -> γ} : (s.image f).image g = s.image (
g ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.dedup_map_dedup_eq`：dedup_map_dedup_eq [DecidableEq β] (f : α -
> β) (s : Multiset α) : dedup (map f (dedup s)) = dedup (map f s)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_image [DecidableEq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
  eq_of_veq <| by simp only [image_val, dedup_map_dedup_eq, Multiset.map_map]

/-- Reverse of `Finset.image_image`. The `Finset` analogue of `Set.image_comp`. -/
/-
**Finset.image_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_comp [DecidableEq γ] {g : β -> γ} : s.image (g ∘ f) = (s.image f).im
age g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)

--- 原说明 ---
Reverse of `Finset.image_image`. The `Finset` analogue of `Set.image_comp`.
-/
theorem image_comp [DecidableEq γ] {g : β → γ} : s.image (g ∘ f) = (s.image f).image g :=
  image_image.symm

/-- Point-free form of `Finset.image_image`: `image` distributes over `Function.comp`. -/
/-
**Finset.image_comp_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_comp_image [DecidableEq γ] {g : β -> γ} : image g ∘ image f = image 
(g ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Point-free form of `Finset.image_image`: `image` distributes over `Function.comp
`.
-/
theorem image_comp_image [DecidableEq γ] {g : β → γ} :
    image g ∘ image f = image (g ∘ f) := by ext s; simp [image_image]
/-
**Finset.image_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_comp_eq [DecidableEq γ] {g : β -> γ} : image (g ∘ f) = image g ∘ ima
ge f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_comp_image`：image_comp_image [DecidableEq γ] {g : β -> γ} :
 image g ∘ image f = image (g ∘ f)
-/
theorem image_comp_eq [DecidableEq γ] {g : β → γ} :
    image (g ∘ f) = image g ∘ image f := image_comp_image.symm
/-
**Finset.image_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f : β -> γ} {g : α -> β}
 {f' : α -> β'} {g' : β' -> γ} (h_comm : forall a, f (g a) = g' (f' a)) : (s.ima
ge g).image f = (s.image f').image g'
参数：h_comm : forall a, f (g a) = g' (f' a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f : β → γ} {g : α → β} {f' : α → β'}
    {g' : β' → γ} (h_comm : ∀ a, f (g a) = g' (f' a)) :
    (s.image g).image f = (s.image f').image g' := by simp_rw [image_image, comp_def, h_comm]
/-
**Finset._root_.Function.Semiconj.finset_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Semiconj.finset_image [DecidableEq α] {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun _ =>
  image_comm h
/-
**Finset._root_.Function.Commute.finset_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Commute.finset_image [DecidableEq α] {f g : α → α}
    (h : Function.Commute f g) : Function.Commute (image f) (image g) :=
  Function.Semiconj.finset_image h

@[gcongr]
/-
**Finset.image_subset_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_subset_image {s₁ s₂ : Finset α} (h : s₁ subseteq s₂) : s₁.image f su
bseteq s₂.image f
参数：h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Multiset.map_subset_map`：map_subset_map {f : α -> β} {s t : Multiset α} 
(H : s subseteq t) : map f s subseteq map f t
-/
theorem image_subset_image {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f := by
  simp only [subset_def, image_val, subset_dedup', dedup_subset', Multiset.map_subset_map h]
/-
**Finset.image_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_subset_iff : s.image f subseteq t ↔ forall x in s, f x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_subset_iff : s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t :=
  calc
    s.image f ⊆ t ↔ f '' ↑s ⊆ ↑t := by norm_cast
    _ ↔ _ := Set.image_subset_iff
/-
**Finset.mapsTo_iff_image_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mapsTo_iff_image_subset : Set.MapsTo f s t ↔ s.image f subseteq t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mapsTo_iff_image_subset : Set.MapsTo f s t ↔ s.image f ⊆ t := by
  simp [Set.MapsTo, image_subset_iff]

alias ⟨_root_.Set.MapsTo.finsetImage_subset, _⟩ := mapsTo_iff_image_subset
/-
**Finset.surjOn_iff_subset_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：surjOn_iff_subset_image : Set.SurjOn f s t ↔ t subseteq s.image f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma surjOn_iff_subset_image : Set.SurjOn f s t ↔ t ⊆ s.image f := by
  simp only [Set.SurjOn]
  norm_cast

alias ⟨_root_.Set.SurjOn.subset_finsetImage, _⟩ := surjOn_iff_subset_image
/-
**Finset.image_eq_iff_surjOn_mapsTo** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_eq_iff_surjOn_mapsTo : s.image f = t ↔ Set.SurjOn f s t ∧ Set.MapsTo
 f s t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_eq_iff_surjOn_mapsTo : s.image f = t ↔ Set.SurjOn f s t ∧ Set.MapsTo f s t := by
  grind [mapsTo_iff_image_subset, surjOn_iff_subset_image]

alias ⟨_root_.Set.SurjOn.finsetImage_eq_of_mapsTo, _⟩ := image_eq_iff_surjOn_mapsTo
/-
**Finset.image_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_mono (f : α -> β) : Monotone (Finset.image f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image`：image_subset_image {s₁ s₂ : Finset α} (h : s₁
 subseteq s₂) : s₁.image f subseteq s₂.image f
-/
theorem image_mono (f : α → β) : Monotone (Finset.image f) := fun _ _ => image_subset_image
/-
**Finset.image_injective** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_injective (hf : Injective f) : Injective (image f)
参数：hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.map_injective`：map_injective (f : α ↪ β) : Injective (map f)
-/
lemma image_injective (hf : Injective f) : Injective (image f) := by
  simpa only [funext (map_eq_image _)] using! map_injective ⟨f, hf⟩
/-
**Finset.image_inj** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_inj {t : Finset α} (hf : Injective f) : s.image f = t.image f ↔ s = 
t
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Finset.image_injective`：image_injective (hf : Injective f) : Injective (
image f)
-/
lemma image_inj {t : Finset α} (hf : Injective f) : s.image f = t.image f ↔ s = t :=
  (image_injective hf).eq_iff
/-
**Finset.image_subset_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_subset_image_iff {t : Finset α} (hf : Injective f) : s.image f subse
teq t.image f ↔ s subseteq t
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
-/
theorem image_subset_image_iff {t : Finset α} (hf : Injective f) :
    s.image f ⊆ t.image f ↔ s ⊆ t :=
  mod_cast Set.image_subset_image_iff hf (s := s) (t := t)

/-- Variant of `Finset.image_subset_image_iff` under an `InjOn` rather than `Injective`
hypothesis. -/
/-
**Finset.image_subset_image_iff_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_subset_image_iff_of_injOn {s₁ s₂ : Finset α} (ht : (s : Set α).InjOn
 f) (h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s) : s₁.image f subseteq s₂.image f ↔
 s₁ subseteq s₂
参数：ht : (s : Set α).InjOn f；h₁ : s₁ subseteq s；h₂ : s₂ subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.InjOn.image_subset_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ 
s₂ : Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ ⊆ f '' s₂ 
↔ s₁ ⊆ s₂)

--- 原说明 ---
Variant of `Finset.image_subset_image_iff` under an `InjOn` rather than `Injecti
ve`
hypothesis.
-/
theorem image_subset_image_iff_of_injOn {s₁ s₂ : Finset α} (ht : (s : Set α).InjOn f)
    (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) : s₁.image f ⊆ s₂.image f ↔ s₁ ⊆ s₂ := by
  exact_mod_cast ht.image_subset_image_iff (mod_cast h₁) (mod_cast h₂)

/-- Variant of `Finset.image_inj` under an `InjOn` rather than `Injective` hypothesis. -/
/-
**Finset.image_eq_image_iff_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_eq_image_iff_of_injOn {s₁ s₂ : Finset α} (ht : (s : Set α).InjOn f) 
(h₁ : s₁ subseteq s) (h₂ : s₂ subseteq s) : s₁.image f = s₂.image f ↔ s₁ = s₂
参数：ht : (s : Set α).InjOn f；h₁ : s₁ subseteq s；h₂ : s₂ subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.InjOn.image_eq_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ :
 Set α} {f : α → β},   Set.InjOn f s → s₁ ⊆ s → s₂ ⊆ s → (f '' s₁ = f '' s₂ ↔ s₁
 = s₂)

--- 原说明 ---
Variant of `Finset.image_inj` under an `InjOn` rather than `Injective` hypothesi
s.
-/
theorem image_eq_image_iff_of_injOn {s₁ s₂ : Finset α} (ht : (s : Set α).InjOn f)
    (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s) : s₁.image f = s₂.image f ↔ s₁ = s₂ := by
  exact_mod_cast ht.image_eq_image_iff (mod_cast h₁) (mod_cast h₂)
/-
**Finset.image_ssubset_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_ssubset_image {t : Finset α} (hf : Injective f) : s.image f ⊂ t.imag
e f ↔ s ⊂ t
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `Finset.image_subset_image_iff`：image_subset_image_iff {t : Finset α} (hf
 : Injective f) : s.image f subseteq t.image f ↔ s subseteq t
-/
lemma image_ssubset_image {t : Finset α} (hf : Injective f) : s.image f ⊂ t.image f ↔ s ⊂ t := by
  exact lt_iff_lt_of_le_iff_le' (image_subset_image_iff hf) (image_subset_image_iff hf)
/-
**Finset.coe_image_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_image_subset_range : ↑(s.image f) subseteq Set.range f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem coe_image_subset_range : ↑(s.image f) ⊆ Set.range f :=
  calc
    ↑(s.image f) = f '' ↑s := coe_image
    _ ⊆ Set.range f := Set.image_subset_range f ↑s
/-
**Finset.filter_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_image {p : β -> Prop} [DecidablePred p] : (s.image f).filter p = (s
.filter fun a => p (f a)).image f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_image {p : β → Prop} [DecidablePred p] :
    (s.image f).filter p = (s.filter fun a ↦ p (f a)).image f := by grind
/-
**Finset.fiber_nonempty_iff_mem_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fiber_nonempty_iff_mem_image {y : β} : (s.filter (f · = y)).Nonempty ↔ y i
n s.image f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fiber_nonempty_iff_mem_image {y : β} : (s.filter (f · = y)).Nonempty ↔ y ∈ s.image f := by
  simp [Finset.Nonempty]
/-
**Finset.image_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_union [DecidableEq α] {f : α -> β} (s₁ s₂ : Finset α) : (s₁ union s₂
).image f = s₁.image f union s₂.image f
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
-/
theorem image_union [DecidableEq α] {f : α → β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
  mod_cast Set.image_union f s₁ s₂
/-
**Finset.image_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_inter_subset [DecidableEq α] (f : α -> β) (s t : Finset α) : (s inte
r t).image f subseteq s.image f inter t.image f
参数：f : α -> β；s t : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `Finset.image_mono`：image_mono (f : α -> β) : Monotone (Finset.image f)
-/
theorem image_inter_subset [DecidableEq α] (f : α → β) (s t : Finset α) :
    (s ∩ t).image f ⊆ s.image f ∩ t.image f :=
  (image_mono f).map_inf_le s t
/-
**Finset.image_inter_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_inter_of_injOn [DecidableEq α] {f : α -> β} (s t : Finset α) (hf : S
et.InjOn f (s union t)) : (s inter t).image f = s.image f inter t.image f
参数：s t : Finset α；hf : Set.InjOn f (s union t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `Set.image_inter_on`：image_inter_on {f : α -> β} {s t : Set α} (h : foral
l x in t, forall y in s, f x = f y -> x = y) : f '' (s inter t) = f '' s inter f
 '' t
-/
theorem image_inter_of_injOn [DecidableEq α] {f : α → β} (s t : Finset α)
    (hf : Set.InjOn f (s ∪ t)) : (s ∩ t).image f = s.image f ∩ t.image f :=
  coe_injective <| by
    push_cast
    exact Set.image_inter_on fun a ha b hb => hf (Or.inr ha) <| Or.inl hb
/-
**Finset.image_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective f) : (s₁ in
ter s₂).image f = s₁.image f inter s₂.image f
参数：s₁ s₂ : Finset α；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_inter_of_injOn`：image_inter_of_injOn [DecidableEq α] {f : α
 -> β} (s t : Finset α) (hf : Set.InjOn f (s union t)) : (s inter t).image f = s
.image f inter t.…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective f) :
    (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
  image_inter_of_injOn _ _ hf.injOn

@[simp]
/-
**Finset.image_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_singleton (f : α -> β) (a : α) : image f {a} = {f a}
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} := by grind

@[simp]
/-
**Finset.image_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_insert [DecidableEq α] (f : α -> β) (a : α) (s : Finset α) : (insert
 a s).image f = insert (f a) (s.image f)
参数：f : α -> β；a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_insert [DecidableEq α] (f : α → β) (a : α) (s : Finset α) :
    (insert a s).image f = insert (f a) (s.image f) := by grind
/-
**Finset.erase_image_subset_image_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：erase_image_subset_image_erase [DecidableEq α] (f : α -> β) (s : Finset α)
 (a : α) : (s.image f).erase (f a) subseteq (s.erase a).image f
参数：f : α -> β；s : Finset α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_image_subset_image_erase [DecidableEq α] (f : α → β) (s : Finset α) (a : α) :
    (s.image f).erase (f a) ⊆ (s.erase a).image f := by grind

@[simp]
/-
**Finset.image_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_erase [DecidableEq α] {f : α -> β} (hf : Injective f) (s : Finset α)
 (a : α) : (s.erase a).image f = (s.image f).erase (f a)
参数：hf : Injective f；s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_erase [DecidableEq α] {f : α → β} (hf : Injective f) (s : Finset α) (a : α) :
    (s.erase a).image f = (s.image f).erase (f a) := by grind

@[simp]
/-
**Finset.image_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_eq_empty : s.image f = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_eq_empty`：image_eq_empty {α β} {f : α -> β} {s : Set α} : f ''
 s = ∅ ↔ s = ∅
-/
theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ := mod_cast Set.image_eq_empty (f := f) (s := s)

@[simp]
/-
**Finset.empty_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_eq_image : ∅ = s.image f ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.image_eq_empty`：image_eq_empty : s.image f = ∅ ↔ s = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem empty_eq_image : ∅ = s.image f ↔ s = ∅ := by rw [eq_comm, image_eq_empty]
/-
**Finset.image_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_sdiff [DecidableEq α] {f : α -> β} (s t : Finset α) (hf : Injective 
f) : (s \ t).image f = s.image f \ t.image f
参数：s t : Finset α；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
-/
theorem image_sdiff [DecidableEq α] {f : α → β} (s t : Finset α) (hf : Injective f) :
    (s \ t).image f = s.image f \ t.image f :=
  mod_cast Set.image_sdiff hf s t
/-
**Finset.image_sdiff_of_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_sdiff_of_injOn [DecidableEq α] {t : Finset α} (hf : Set.InjOn f s) (
hts : t subseteq s) : (s \ t).image f = s.image f \ t.image f
参数：hf : Set.InjOn f s；hts : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_sdiff_of_injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f
 : α → β} {t : Set α},   Set.InjOn f s → t ⊆ s → f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
-/
lemma image_sdiff_of_injOn [DecidableEq α] {t : Finset α} (hf : Set.InjOn f s) (hts : t ⊆ s) :
    (s \ t).image f = s.image f \ t.image f :=
  mod_cast Set.image_sdiff_of_injOn hf <| coe_subset.2 hts
/-
**Finset._root_.Disjoint.of_image_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.of_image_finset {s t : Finset α} {f : α → β}
    (h : Disjoint (s.image f) (t.image f)) : Disjoint s t :=
  disjoint_iff_ne.2 fun _ ha _ hb =>
    ne_of_apply_ne f <| h.forall_ne_finset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
/-
**Finset.mem_range_iff_mem_finset_range_of_mod_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Fi
nset`。
形式化陈述：mem_range_iff_mem_finset_range_of_mod_eq' [DecidableEq α] {f : Nat -> α} {
a : α} {n : Nat} (hn : 0 < n) (h : forall i, f (i % n) = f i) : a in Set.range f
 ↔ a in (Finset.range n).image fun i => f i
参数：hn : 0 < n；h : forall i, f (i % n) = f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.congr`：∀ {α : Sort u_1} {x₁ y₁ x₂ y₂ : α}, x₁ = y₁ → x₂ = y₂ → (x₁ = 
x₂ ↔ y₁ = y₂)
-/
theorem mem_range_iff_mem_finset_range_of_mod_eq' [DecidableEq α] {f : ℕ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image fun i => f i := by
  constructor
  · rintro ⟨i, hi⟩
    simp only [mem_image, mem_range]
    exact ⟨i % n, Nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩
  · rintro h
    simp only [mem_image, Set.mem_range, mem_range] at *
    rcases h with ⟨i, _, ha⟩
    exact ⟨i, ha⟩
/-
**Finset.mem_range_iff_mem_finset_range_of_mod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fin
set`。
形式化陈述：mem_range_iff_mem_finset_range_of_mod_eq [DecidableEq α] {f : Int -> α} {a
 : α} {n : Nat} (hn : 0 < n) (h : forall i, f (i % n) = f i) : a in Set.range f 
↔ a in (Finset.range n).image (fun (i : Nat) => f i)
参数：hn : 0 < n；h : forall i, f (i % n) = f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `Int.emod_lt_of_pos`：∀ (a : ℤ) {b : ℤ}, 0 < b → a % b < b
· 使用定理 `Int.emod_eq_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a % b = a
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Int.ofNat_lt_ofNat_of_lt`：∀ {n m : ℕ}, n < m → ↑n < ↑m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem mem_range_iff_mem_finset_range_of_mod_eq [DecidableEq α] {f : ℤ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image (fun (i : ℕ) => f i) :=
  suffices (∃ i, f (i % n) = a) ↔ ∃ i, i < n ∧ f ↑i = a by simpa [h]
  have hn' : 0 < (n : ℤ) := Int.ofNat_lt.mpr hn
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have : 0 ≤ i % ↑n := Int.emod_nonneg _ (ne_of_gt hn')
      ⟨Int.toNat (i % n), by
        rw [← Int.ofNat_lt, Int.toNat_of_nonneg this]; exact ⟨Int.emod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
    ⟨i, by rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt_ofNat_of_lt hi), ha]⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Finset.attach_image_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：attach_image_val [DecidableEq α] {s : Finset α} : s.attach.image Subtype.v
al = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_val`：image_val (f : α -> β) (s : Finset α) : (image f s).1 
= (s.1.map f).dedup
· 使用定理 `Finset.attach_val`：attach_val (s : Finset α) : s.attach.1 = s.1.attach
· 使用定理 `Multiset.attach_map_val`：attach_map_val (s : Multiset α) : s.attach.map 
Subtype.val = s
· 使用定理 `Finset.dedup_eq_self`：dedup_eq_self [DecidableEq α] (s : Finset α) : ded
up s.1 = s.1
-/
theorem attach_image_val [DecidableEq α] {s : Finset α} : s.attach.image Subtype.val = s :=
  eq_of_veq <| by rw [image_val, attach_val, Multiset.attach_map_val, dedup_eq_self]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Finset.attach_cons** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：attach_cons (a : α) (s : Finset α) (ha) : attach (cons a s ha) = cons ⟨a, 
mem_cons_self a s⟩ ((attach s).map ⟨fun x => ⟨x.1, mem_cons_of_mem x.2⟩, fun x y
 => by simp⟩) (by simpa)
参数：a : α；s : Finset α；ha。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
lemma attach_cons (a : α) (s : Finset α) (ha) :
    attach (cons a s ha) =
      cons ⟨a, mem_cons_self a s⟩
        ((attach s).map ⟨fun x ↦ ⟨x.1, mem_cons_of_mem x.2⟩, fun x y => by simp⟩)
          (by simpa) := by ext ⟨x, hx⟩; simpa using hx

@[simp]
/-
**Finset.attach_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：attach_insert [DecidableEq α] (s : Finset α) (a : α) : attach (insert a s)
 = insert (⟨a, mem_insert_self a s⟩ : { x // x in insert a s }) ((attach s).imag
e fun x => ⟨x.1, mem_insert_of_mem x.2⟩)
参数：s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
theorem attach_insert [DecidableEq α] (s : Finset α) (a : α) :
    attach (insert a s) =
      insert (⟨a, mem_insert_self a s⟩ : { x // x ∈ insert a s })
        ((attach s).image fun x => ⟨x.1, mem_insert_of_mem x.2⟩) := by ext ⟨x, hx⟩; simpa using hx

@[simp]
/-
**Finset.disjoint_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_image {s t : Finset α} {f : α -> β} (hf : Injective f) : Disjoint
 (s.image f) (t.image f) ↔ Disjoint s t
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.disjoint_image_iff`：disjoint_image_iff (hf : Injective f) : Disjoint
 (f '' s) (f '' t) ↔ Disjoint s t
-/
theorem disjoint_image {s t : Finset α} {f : α → β} (hf : Injective f) :
    Disjoint (s.image f) (t.image f) ↔ Disjoint s t :=
  mod_cast Set.disjoint_image_iff hf (s := s) (t := t)
/-
**Finset.image_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_const {s : Finset α} (h : s.Nonempty) (b : β) : (s.image fun _ => b)
 = singleton b
参数：h : s.Nonempty；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
-/
theorem image_const {s : Finset α} (h : s.Nonempty) (b : β) : (s.image fun _ => b) = singleton b :=
  mod_cast Set.Nonempty.image_const (coe_nonempty.2 h) b

@[simp]
/-
**Finset.map_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α) : (s.erase a)
.map f = (s.map f).erase (f a)
参数：f : α ↪ β；s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.image_erase`：image_erase [DecidableEq α] {f : α -> β} (hf : Injec
tive f) (s : Finset α) (a : α) : (s.erase a).image f = (s.image f).erase (f a)
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α) :
    (s.erase a).map f = (s.map f).erase (f a) := by
  simp_rw [map_eq_image]
  exact s.image_erase f.2 a
/-
**Finset.iterate_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：iterate_image [DecidableEq α] (f : α -> α) (n : Nat) : (Finset.image f)^[n
] s = s.image f^[n]
参数：f : α -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_id`：image_id [DecidableEq α] : s.image id = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
-/
theorem iterate_image [DecidableEq α] (f : α → α) (n : ℕ) :
    (Finset.image f)^[n] s = s.image f^[n] := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', iterate_succ', ih, image_image]

end Image

/-! ### filterMap -/

section FilterMap

/-- `filterMap f s` is a combination filter/map operation on `s`.
  The function `f : α → Option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is included in the result, otherwise
  `a` is excluded from the resulting finset.

  In notation, `filterMap f s` is the finset `{b : β | ∃ a ∈ s, f a = some b}`. -/
-- TODO: should there be `filterImage` too?
/-
**Finset.filterMap** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：filterMap (f : α -> Option β) (s : Finset α) (f_inj : forall a a' b, b in 
f a -> b in f a' -> a = a') : Finset β
参数：f : α -> Option β；s : Finset α；f_inj : forall a a' b, b in f a -> b in f a' -
> a = a'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def filterMap (f : α → Option β) (s : Finset α)
    (f_inj : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') : Finset β :=
  ⟨s.val.filterMap f, s.nodup.filterMap f f_inj⟩

variable (f : α → Option β) (s' : Finset α) {s t : Finset α}
  {f_inj : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a'}

@[simp]
/-
**Finset.filterMap_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filterMap_val : (filterMap f s' f_inj).1 = s'.1.filterMap f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filterMap_val : (filterMap f s' f_inj).1 = s'.1.filterMap f := rfl

@[simp]
/-
**Finset.filterMap_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filterMap_empty : (∅ : Finset α).filterMap f f_inj = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filterMap_empty : (∅ : Finset α).filterMap f f_inj = ∅ := rfl

@[simp, grind =]
/-
**Finset.mem_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_filterMap {b : β} : b in s.filterMap f f_inj ↔ exists a in s, f a = so
me b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_filterMap`：mem_filterMap (f : α -> Option β) (s : Multiset 
α) {b : β} : b in filterMap f s ↔ exists a, a in s ∧ f a = some b
-/
theorem mem_filterMap {b : β} : b ∈ s.filterMap f f_inj ↔ ∃ a ∈ s, f a = some b :=
  s.val.mem_filterMap f

@[simp, norm_cast]
/-
**Finset.coe_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_filterMap : (s.filterMap f f_inj : Set β) = {b | exists a in s, f a = 
some b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coe_filterMap : (s.filterMap f f_inj : Set β) = {b | ∃ a ∈ s, f a = some b} :=
  Set.ext (by simp only [mem_coe, mem_filterMap, Set.mem_ofPred_eq, implies_true])

@[simp]
/-
**Finset.filterMap_some** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filterMap_some : s.filterMap some (by simp) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filterMap_some : s.filterMap some (by simp) = s :=
  ext fun _ => by simp only [mem_filterMap, Option.some.injEq, exists_eq_right]
/-
**Finset.filterMap_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filterMap_mono (h : s subseteq t) : filterMap f s f_inj subseteq filterMap
 f t f_inj
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filterMap_mono (h : s ⊆ t) :
    filterMap f s f_inj ⊆ filterMap f t f_inj := by grind
/-
**Finset._root_.List.toFinset_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.List.toFinset_filterMap [DecidableEq α] [DecidableEq β]
    (f_inj : ∀ (a a' : α) (b : β), f a = some b → f a' = some b → a = a') (s : List α) :
    (s.filterMap f).toFinset = s.toFinset.filterMap f f_inj := by
  simp [← Finset.coe_inj]

end FilterMap

/-! ### Subtype -/


section Subtype

/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `Subtype p` whose
elements belong to `s`. -/
/-
**Finset.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_4} → (p : α → Prop) → [DecidablePred p] → Finset α → Finset (S
ubtype p)
参数：p : α → Prop；Subtype p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `Subtype 
p` whose
elements belong to `s`.
-/
protected def subtype {α} (p : α → Prop) [DecidablePred p] (s : Finset α) : Finset (Subtype p) :=
  (s.filter p).attach.map
    ⟨fun x => ⟨x.1, by simpa using (Finset.mem_filter.1 x.2).2⟩,
     fun _ _ H => Subtype.ext <| Subtype.mk.inj H⟩

set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
/-
**Finset.mem_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a
 : Subtype p}, a ∈ Finset.subtype p s ↔ ↑a ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_subtype {p : α → Prop} [DecidablePred p] {s : Finset α} :
    ∀ {a : Subtype p}, a ∈ s.subtype p ↔ (a : α) ∈ s
  | ⟨a, ha⟩ => by simp [Finset.subtype, ha]
/-
**Finset.subtype_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subtype_eq_empty {p : α -> Prop} [DecidablePred p] {s : Finset α} : s.subt
ype p = ∅ ↔ forall x, p x -> x ∉ s
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subtype_eq_empty {p : α → Prop} [DecidablePred p] {s : Finset α} :
    s.subtype p = ∅ ↔ ∀ x, p x → x ∉ s := by simp [Finset.ext_iff, Subtype.forall]

@[gcongr, mono]
/-
**Finset.subtype_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subtype_mono {p : α -> Prop} [DecidablePred p] : Monotone (Finset.subtype 
p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_subtype`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePre
d p] {s : Finset α} {a : Subtype p}, a ∈ Finset.subtype p s ↔ ↑a ∈ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem subtype_mono {p : α → Prop} [DecidablePred p] : Monotone (Finset.subtype p) :=
  fun _ _ h _ hx => mem_subtype.2 <| h <| mem_subtype.1 hx

/-- `s.subtype p` converts back to `s.filter p` with
`Embedding.subtype`. -/
@[simp]
/-
**Finset.subtype_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subtype_map (p : α -> Prop) [DecidablePred p] {s : Finset α} : (s.subtype 
p).map (Embedding.subtype _) = s.filter p
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`s.subtype p` converts back to `s.filter p` with
`Embedding.subtype`.
-/
theorem subtype_map (p : α → Prop) [DecidablePred p] {s : Finset α} :
    (s.subtype p).map (Embedding.subtype _) = s.filter p := by
  ext x
  simp [@and_comm _ (_ = _), @and_comm (p x) (x ∈ s)]

/-- If all elements of a `Finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `Embedding.subtype`. -/
/-
**Finset.subtype_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subtype_map_of_mem {p : α -> Prop} [DecidablePred p] {s : Finset α} (h : f
orall x in s, p x) : (s.subtype p).map (Embedding.subtype _) = s
参数：h : forall x in s, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.subtype_map`：subtype_map (p : α -> Prop) [DecidablePred p] {s : F
inset α} : (s.subtype p).map (Embedding.subtype _) = s.filter p

--- 原说明 ---
If all elements of a `Finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `Embedding.subtype`.
-/
theorem subtype_map_of_mem {p : α → Prop} [DecidablePred p] {s : Finset α} (h : ∀ x ∈ s, p x) :
    (s.subtype p).map (Embedding.subtype _) = s := ext <| by simpa [subtype_map] using h

@[simp]
/-
**Finset.subtype_mem_eq_attach** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subtype_mem_eq_attach (s : Finset α) [DecidablePred (· in s)] : s.subtype 
(· in s) = s.attach
参数：s : Finset α；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subtype_mem_eq_attach (s : Finset α) [DecidablePred (· ∈ s)] :
    s.subtype (· ∈ s) = s.attach := by
  ext; simp

/-- If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, all elements of the result have the property of
the subtype. -/
/-
**Finset.property_of_mem_map_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：property_of_mem_map_subtype {p : α -> Prop} (s : Finset { x // p x }) {a :
 α} (h : a in s.map (Embedding.subtype _)) : p a
参数：s : Finset { x // p x }；h : a in s.map (Embedding.subtype _)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, all elements of the result have the property of
the subtype.
-/
theorem property_of_mem_map_subtype {p : α → Prop} (s : Finset { x // p x }) {a : α}
    (h : a ∈ s.map (Embedding.subtype _)) : p a := by
  rcases mem_map.1 h with ⟨x, _, rfl⟩
  exact x.2

/-- If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
/-
**Finset.notMem_map_subtype_of_not_property** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_map_subtype_of_not_property {p : α -> Prop} (s : Finset { x // p x 
}) {a : α} (h : ¬p a) : a ∉ s.map (Embedding.subtype _)
参数：s : Finset { x // p x }；h : ¬p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.property_of_mem_map_subtype`：property_of_mem_map_subtype {p : α -
> Prop} (s : Finset { x // p x }) {a : α} (h : a in s.map (Embedding.subtype _))
 : p a

--- 原说明 ---
If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype.
-/
theorem notMem_map_subtype_of_not_property {p : α → Prop} (s : Finset { x // p x }) {a : α}
    (h : ¬p a) : a ∉ s.map (Embedding.subtype _) :=
  mt s.property_of_mem_map_subtype h

/-- If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, the result is a subset of the set giving the
subtype. -/
/-
**Finset.map_subtype_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_subtype_subset {t : Set α} (s : Finset t) : ↑(s.map (Embedding.subtype
 _)) subseteq t
参数：s : Finset t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.property_of_mem_map_subtype`：property_of_mem_map_subtype {p : α -
> Prop} (s : Finset { x // p x }) {a : α} (h : a in s.map (Embedding.subtype _))
 : p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)

--- 原说明 ---
If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, the result is a subset of the set giving the
subtype.
-/
theorem map_subtype_subset {t : Set α} (s : Finset t) : ↑(s.map (Embedding.subtype _)) ⊆ t := by
  intro a ha
  rw [mem_coe] at ha
  convert! property_of_mem_map_subtype s ha

end Subtype

/-- If a `Finset` is a subset of the image of a `Set` under `f`,
then it is equal to the `Finset.image` of a `Finset` subset of that `Set`. -/
/-
**Finset.subset_set_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_set_image_iff [DecidableEq β] {s : Set α} {t : Finset β} {f : α -> 
β} : ↑t subseteq f '' s ↔ exists s' : Finset α, ↑s' subseteq s ∧ s'.image f = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Finset.map_subtype_subset`：map_subtype_subset {t : Set α} (s : Finset t)
 : ↑(s.map (Embedding.subtype _)) subseteq t
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If a `Finset` is a subset of the image of a `Set` under `f`,
then it is equal to the `Finset.image` of a `Finset` subset of that `Set`.
-/
theorem subset_set_image_iff [DecidableEq β] {s : Set α} {t : Finset β} {f : α → β} :
    ↑t ⊆ f '' s ↔ ∃ s' : Finset α, ↑s' ⊆ s ∧ s'.image f = t := by
  constructor
  · intro h
    let : CanLift β s (f ∘ (↑)) fun y => y ∈ f '' s := ⟨fun y ⟨x, hxt, hy⟩ => ⟨⟨x, hxt⟩, hy⟩⟩
    lift t to Finset s using h
    refine ⟨t.map (Embedding.subtype _), map_subtype_subset _, ?_⟩
    ext y; simp
  · grind

/--
If a finset `t` is a subset of the image of another finset `s` under `f`, then it is equal to the
image of a subset of `s`.

For the version where `s` is a set, see `subset_set_image_iff`.
-/
/-
**Finset.subset_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_image_iff [DecidableEq β] {s : Finset α} {t : Finset β} {f : α -> β
} : t subseteq s.image f ↔ exists s' : Finset α, s' subseteq s ∧ s'.image f = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If a finset `t` is a subset of the image of another finset `s` under `f`, then i
t is equal to the
image of a subset of `s`.

For the version where `s` is a set, see `subset_set_image_iff`.
-/
theorem subset_image_iff [DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β} :
    t ⊆ s.image f ↔ ∃ s' : Finset α, s' ⊆ s ∧ s'.image f = t := by
  simp only [← coe_subset, coe_image, subset_set_image_iff]

/--
A special case of `subset_image_iff`,
which corresponds to `Set.subset_range_iff_exists_image_eq` for `Set`.
-/
/-
**Finset.subset_univ_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_univ_image_iff [Fintype α] [DecidableEq β] {t : Finset β} {f : α ->
 β} : t subseteq univ.image f ↔ exists s' : Finset α, s'.image f = t
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A special case of `subset_image_iff`,
which corresponds to `Set.subset_range_iff_exists_image_eq` for `Set`.
-/
theorem subset_univ_image_iff [Fintype α] [DecidableEq β] {t : Finset β} {f : α → β} :
    t ⊆ univ.image f ↔ ∃ s' : Finset α, s'.image f = t := by simp [subset_image_iff]
/-
**Finset.range_sdiff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_sdiff_zero {n : Nat} : range (n + 1) \ {0} = (range n).image Nat.suc
c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_sdiff_of_notMem`：insert_sdiff_of_notMem (s : Finset α) {t 
: Finset α} {x : α} (h : x ∉ t) : insert x s \ t = insert x (s \ t)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem range_sdiff_zero {n : ℕ} : range (n + 1) \ {0} = (range n).image Nat.succ := by
  induction n with
  | zero => simp
  | succ k hk =>
    conv_rhs => rw [range_add_one]
    rw [range_add_one, image_insert, ← hk, insert_sdiff_of_notMem]
    simp

end Finset

/-
**Multiset.toFinset_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.toFinset_map [DecidableEq α] [DecidableEq β] (f : α -> β) (m : Mu
ltiset α) : (m.map f).toFinset = m.toFinset.image f
参数：f : α -> β；m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.dedup_map_dedup_eq`：dedup_map_dedup_eq [DecidableEq β] (f : α -
> β) (s : Multiset α) : dedup (map f (dedup s)) = dedup (map f s)
-/
theorem Multiset.toFinset_map [DecidableEq α] [DecidableEq β] (f : α → β) (m : Multiset α) :
    (m.map f).toFinset = m.toFinset.image f :=
  Finset.val_inj.1 (Multiset.dedup_map_dedup_eq _ _).symm

namespace Equiv

/-- Given an equivalence `α` to `β`, produce an equivalence between `Finset α` and `Finset β`. -/
/-
**Equiv.finsetCongr** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → Finset α ≃ Finset β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given an equivalence `α` to `β`, produce an equivalence between `Finset α` and `
Finset β`.
-/
protected def finsetCongr (e : α ≃ β) : Finset α ≃ Finset β where
  toFun s := s.map e.toEmbedding
  invFun s := s.map e.symm.toEmbedding
  left_inv s := by simp [Finset.map_map]
  right_inv s := by simp [Finset.map_map]

@[simp]
/-
**Equiv.finsetCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：finsetCongr_apply (e : α ≃ β) (s : Finset α) : e.finsetCongr s = s.map e.t
oEmbedding
参数：e : α ≃ β；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finsetCongr_apply (e : α ≃ β) (s : Finset α) : e.finsetCongr s = s.map e.toEmbedding :=
  rfl

@[simp]
/-
**Equiv.finsetCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：finsetCongr_refl : (Equiv.refl α).finsetCongr = Equiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_refl`：map_refl : s.map (Embedding.refl _) = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finsetCongr_refl : (Equiv.refl α).finsetCongr = Equiv.refl _ := by
  ext
  simp

@[simp]
/-
**Equiv.finsetCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：finsetCongr_symm (e : α ≃ β) : e.finsetCongr.symm = e.symm.finsetCongr
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem finsetCongr_symm (e : α ≃ β) : e.finsetCongr.symm = e.symm.finsetCongr :=
  rfl

@[simp]
/-
**Equiv.finsetCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：finsetCongr_trans (e : α ≃ β) (e' : β ≃ γ) : e.finsetCongr.trans e'.finset
Congr = (e.trans e').finsetCongr
参数：e : α ≃ β；e' : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finsetCongr_trans (e : α ≃ β) (e' : β ≃ γ) :
    e.finsetCongr.trans e'.finsetCongr = (e.trans e').finsetCongr := by
  ext
  simp [-Finset.mem_map, -Equiv.trans_toEmbedding]
/-
**Equiv.finsetCongr_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：finsetCongr_toEmbedding (e : α ≃ β) : e.finsetCongr.toEmbedding = (Finset.
mapEmbedding e.toEmbedding).toEmbedding
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finsetCongr_toEmbedding (e : α ≃ β) :
    e.finsetCongr.toEmbedding = (Finset.mapEmbedding e.toEmbedding).toEmbedding :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a predicate `p : α → Prop`, produces an equivalence between
  `Finset {a : α // p a}` and `{s : Finset α // ∀ a ∈ s, p a}`. -/
@[simps]
/-
**Equiv.finsetSubtypeComm** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → (p : α → Prop) → Finset { a // p a } ≃ { s // ∀ a ∈ s, p 
a }
参数：p : α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate `p : α → Prop`, produces an equivalence between
  `Finset {a : α // p a}` and `{s : Finset α // ∀ a ∈ s, p a}`.
-/
protected def finsetSubtypeComm (p : α → Prop) :
    Finset {a : α // p a} ≃ {s : Finset α // ∀ a ∈ s, p a} where
  toFun s := ⟨s.map ⟨fun a ↦ a.val, Subtype.val_injective⟩, fun _ h ↦
    have ⟨v, _, h⟩ := Embedding.coeFn_mk _ _ ▸ mem_map.mp h; h ▸ v.property⟩
  invFun s := s.val.attach.map (Subtype.impEmbedding _ _ s.property)
  left_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk,
      exists_and_right, exists_eq_right, Subtype.impEmbedding] at * <;>
    grind
  right_inv s := by
    ext a; constructor <;> intro h <;>
    simp only [Finset.mem_map, Finset.mem_attach, Subtype.exists, Embedding.coeFn_mk,
      Subtype.impEmbedding] at * <;>
    grind

end Equiv

