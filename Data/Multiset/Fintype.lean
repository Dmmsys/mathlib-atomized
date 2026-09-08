/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Multiset coercion to type

This module defines a `CoeSort` instance for multisets and gives it a `Fintype` instance.
It also defines `Multiset.toEnumFinset`, which is another way to enumerate the elements of
a multiset. These coercions and definitions make it easier to sum over multisets using existing
`Finset` theory.

## Main definitions

* A coercion from `m : Multiset α` to a `Type*`. Each `x : m` has two components.
  The first, `x.1`, can be obtained via the coercion `↑x : α`,
  and it yields the underlying element of the multiset.
  The second, `x.2`, is a term of `Fin (m.count x)`,
  and its function is to ensure each term appears with the correct multiplicity.
  Note that this coercion requires `DecidableEq α` due to the definition using `Multiset.count`.
* `Multiset.toEnumFinset` is a `Finset` version of this.
* `Multiset.coeEmbedding` is the embedding `m ↪ α × ℕ`, whose first component is the coercion
  and whose second component enumerates elements with multiplicity.
* `Multiset.coeEquiv` is the equivalence `m ≃ m.toEnumFinset`.

## Tags

multiset enumeration
-/

@[expose] public section


variable {α β : Type*} [DecidableEq α] [DecidableEq β] {m : Multiset α}

namespace Multiset

/-- Auxiliary definition for the `CoeSort` instance. This prevents the `CoeOut m α`
/-
**Multiset.from** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance from inadvertently applying to other sigma types. -/
/-
**Multiset.ToType** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：ToType (m : Multiset α) : Type _
参数：m : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `CoeSort` instance. This prevents the `CoeOut m α`
instance from inadvertently applying to other sigma types.
-/
def ToType (m : Multiset α) : Type _ := (x : α) × Fin (m.count x)

/-- Create a type that has the same number of elements as the multiset.
Terms of this type are triples `⟨x, ⟨i, h⟩⟩` where `x : α`, `i : ℕ`, and `h : i < m.count x`.
This way repeated elements of a multiset appear multiple times from different values of `i`. -/
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a type that has the same number of elements as the multiset.
Terms of this type are triples `⟨x, ⟨i, h⟩⟩` where `x : α`, `i : ℕ`, and `h : i 
< m.count x`.
This way repeated elements of a multiset appear multiple times from different va
lues of `i`.
-/
instance : CoeSort (Multiset α) (Type _) := ⟨Multiset.ToType⟩
/-
**Multiset.** 是 Mathlib 中的一个示例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : DecidableEq m := inferInstanceAs <| DecidableEq ((x : α) × Fin (m.count x))

/-- Constructor for terms of the coercion of `m` to a type.
This helps Lean pick up the correct instances. -/
@[reducible, match_pattern]
/-
**Multiset.mkToType** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：mkToType (m : Multiset α) (x : α) (i : Fin (m.count x)) : m
参数：m : Multiset α；x : α；i : Fin (m.count x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for terms of the coercion of `m` to a type.
This helps Lean pick up the correct instances.
-/
def mkToType (m : Multiset α) (x : α) (i : Fin (m.count x)) : m :=
  ⟨x, i⟩

/-- As a convenience, there is a coercion from `m : Type*` to `α` by projecting onto the first
component. -/
/-
**Multiset.instCoeSortMultisetType.instCoeOutToType** 是 Mathlib 中的一个定义，位于命名空间 `M
ultiset.instCoeSortMultisetType`。
形式化陈述：{α : Type u_1} → [inst : DecidableEq α] → {m : Multiset α} → CoeOut m.ToTy
pe α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As a convenience, there is a coercion from `m : Type*` to `α` by projecting onto
 the first
component.
-/
instance instCoeSortMultisetType.instCoeOutToType : CoeOut m α :=
  ⟨fun x ↦ x.1⟩
/-
**Multiset.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_mk {x : α} {i : Fin (m.count x)} : ↑(m.mkToType x i) = x
参数：m.count x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {x : α} {i : Fin (m.count x)} : ↑(m.mkToType x i) = x :=
  rfl
/-
**Multiset.coe_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {m : Multiset α} {x : m.ToType}, x
.fst ∈ m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
@[simp] lemma coe_mem {x : m} : ↑x ∈ m := Multiset.count_pos.mp (by have := x.2.2; lia)

@[simp]
/-
**Multiset.forall_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {m : Multiset α} (p : m.ToType → P
rop),   (∀ (x : m.ToType), p x) ↔ ∀ (x : α) (i : Fin (Multiset.count x m)), p ⟨x
, i⟩
参数：p : m.ToType → Prop；∀ (x : m.ToType), p x；x : α；i : Fin (Multiset.count x m)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.forall`：∀ {α : Type u_1} {β : α → Type u_4} {p : (a : α) × β a → P
rop},   (∀ (x : (a : α) × β a), p x) ↔ ∀ (a : α) (b : β a), p ⟨a, b⟩
-/
protected theorem forall_coe (p : m → Prop) :
    (∀ x : m, p x) ↔ ∀ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.forall

@[simp]
/-
**Multiset.exists_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {m : Multiset α} (p : m.ToType → P
rop), (∃ x, p x) ↔ ∃ x i, p ⟨x, i⟩
参数：p : m.ToType → Prop；∃ x, p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.exists`：∀ {α : Type u_1} {β : α → Type u_4} {p : (a : α) × β a → P
rop}, (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩
-/
protected theorem exists_coe (p : m → Prop) :
    (∃ x : m, p x) ↔ ∃ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.exists

set_option backward.isDefEq.respectTransparency false in
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fintype { p : α × ℕ | p.2 < m.count p.1 } :=
  Fintype.ofFinset
    (m.toFinset.disjiUnion
      (fun x ↦ (Finset.range (m.count x)).map ⟨_, Prod.mk_right_injective x⟩)
      fun x hx y hy hxy => by simp [Function.onFun, Finset.disjoint_right, hxy])
    (by
      rintro ⟨x, i⟩
      simp_rw [Finset.mem_disjiUnion, Multiset.mem_toFinset, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk, Prod.mk_inj, Set.mem_ofPred_eq]
      simp only [← and_assoc, exists_eq_right, and_iff_right_iff_imp]
      exact fun h ↦ Multiset.count_pos.mp (by lia))

/-- Construct a finset whose elements enumerate the elements of the multiset `m`.
The `ℕ` component is used to differentiate between equal elements: if `x` appears `n` times
then `(x, 0)`, ..., and `(x, n-1)` appear in the `Finset`. -/
/-
**Multiset.toEnumFinset** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：toEnumFinset (m : Multiset α) : Finset (α × Nat)
参数：m : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a finset whose elements enumerate the elements of the multiset `m`.
The `ℕ` component is used to differentiate between equal elements: if `x` appear
s `n` times
then `(x, 0)`, ..., and `(x, n-1)` appear in the `Finset`.
-/
def toEnumFinset (m : Multiset α) : Finset (α × ℕ) :=
  { p : α × ℕ | p.2 < m.count p.1 }.toFinset

@[simp]
/-
**Multiset.mem_toEnumFinset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_toEnumFinset (m : Multiset α) (p : α × Nat) : p in m.toEnumFinset ↔ p.
2 < m.count p.1
参数：m : Multiset α；p : α × Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
-/
theorem mem_toEnumFinset (m : Multiset α) (p : α × ℕ) :
    p ∈ m.toEnumFinset ↔ p.2 < m.count p.1 :=
  Set.mem_toFinset
/-
**Multiset.mem_of_mem_toEnumFinset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_of_mem_toEnumFinset {p : α × Nat} (h : p in m.toEnumFinset) : p.1 in m
参数：h : p in m.toEnumFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toEnumFinset`：mem_toEnumFinset (m : Multiset α) (p : α × Na
t) : p in m.toEnumFinset ↔ p.2 < m.count p.1
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
-/
theorem mem_of_mem_toEnumFinset {p : α × ℕ} (h : p ∈ m.toEnumFinset) : p.1 ∈ m :=
  have := (m.mem_toEnumFinset p).mp h; Multiset.count_pos.mp (by lia)
/-
**Multiset.toEnumFinset_filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (m : Multiset α) (a : α),   {x ∈ m
.toEnumFinset | x.1 = a} = {a} ×ˢ Finset.range (Multiset.count a m)
参数：m : Multiset α；a : α；Multiset.count a m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.singleton_product`：singleton_product {a : α} : ({a} : Finset α) ×
ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
@[simp] lemma toEnumFinset_filter_eq (m : Multiset α) (a : α) :
    {x ∈ m.toEnumFinset | x.1 = a} = {a} ×ˢ Finset.range (m.count a) := by aesop
/-
**Multiset.map_toEnumFinset_fst** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (m : Multiset α), Multiset.map Pro
d.fst m.toEnumFinset.val = m
参数：m : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_map`：count_map {α β : Type*} (f : α -> β) (s : Multiset α
) [DecidableEq β] (b : β) : count b (map f s) = card (s.filter fun a => b = f a)
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Multiset.toEnumFinset_filter_eq`：∀ {α : Type u_1} [inst : DecidableEq α]
 (m : Multiset α) (a : α),   {x ∈ m.toEnumFinset | x.1 = a} = {a} ×ˢ Finset.rang
e (Multiset.count a m…
· 使用定理 `Finset.singleton_product`：singleton_product {a : α} : ({a} : Finset α) ×
ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.card_range`：card_range (n : Nat) : card (range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_toEnumFinset_fst (m : Multiset α) : m.toEnumFinset.val.map Prod.fst = m := by
  ext a; simp [count_map, ← Finset.filter_val, eq_comm (a := a)]
/-
**Multiset.image_toEnumFinset_fst** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (m : Multiset α), Finset.image Pro
d.fst m.toEnumFinset = m.toFinset
参数：m : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β
] (f : α → β) (s : Finset α),   Finset.image f s = (Multiset.map f s.val).toFins
et
· 使用定理 `Multiset.map_toEnumFinset_fst`：∀ {α : Type u_1} [inst : DecidableEq α] (
m : Multiset α), Multiset.map Prod.fst m.toEnumFinset.val = m
-/
@[simp] lemma image_toEnumFinset_fst (m : Multiset α) :
    m.toEnumFinset.image Prod.fst = m.toFinset := by
  rw [Finset.image, Multiset.map_toEnumFinset_fst]
/-
**Multiset.map_fst_le_of_subset_toEnumFinset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset
`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {m : Multiset α} {s : Finset (α × 
ℕ)},   s ⊆ m.toEnumFinset → Multiset.map Prod.fst s.val ≤ m
参数：α × ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_map`：count_map {α β : Type*} (f : α -> β) (s : Multiset α
) [DecidableEq β] (b : β) : count b (map f s) = card (s.filter fun a => b = f a)
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `Finset.singleton_product`：singleton_product {a : α} : ({a} : Finset α) ×
ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.card_range`：card_range (n : Nat) : card (range n) = n
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `Nat.le_of_pred_lt`：∀ {n : ℕ} {m : ℕ}, m.pred < n → m ≤ n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
@[simp] lemma map_fst_le_of_subset_toEnumFinset {s : Finset (α × ℕ)} (hsm : s ⊆ m.toEnumFinset) :
    s.1.map Prod.fst ≤ m := by
  simp_rw [le_iff_count, count_map]
  rintro a
  obtain ha | ha := (s.1.filter fun x ↦ a = x.1).card.eq_zero_or_pos
  · rw [ha]
    exact Nat.zero_le _
  obtain ⟨n, han, hn⟩ : ∃ n ≥ card (s.1.filter fun x ↦ a = x.1) - 1, (a, n) ∈ s := by
    by_contra! h
    replace h : {x ∈ s | x.1 = a} ⊆ {a} ×ˢ .range (card (s.1.filter fun x ↦ a = x.1) - 1) := by
      simpa +contextual [forall_comm (β := _ = a), Finset.subset_iff,
        imp_not_comm, not_le, Nat.lt_sub_iff_add_lt] using h
    have : card (s.1.filter fun x ↦ a = x.1) ≤ card (s.1.filter fun x ↦ a = x.1) - 1 := by
      simpa [Finset.card, eq_comm] using Finset.card_mono h
    lia
  exact Nat.le_of_pred_lt (han.trans_lt <| by simpa using hsm hn)

@[gcongr, mono]
/-
**Multiset.toEnumFinset_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toEnumFinset_mono {m₁ m₂ : Multiset α} (h : m₁ <= m₂) : m₁.toEnumFinset su
bseteq m₂.toEnumFinset
参数：h : m₁ <= m₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `lt_of_le_of_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
-/
theorem toEnumFinset_mono {m₁ m₂ : Multiset α} (h : m₁ ≤ m₂) :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset := by
  intro p
  simp only [Multiset.mem_toEnumFinset]
  exact lt_of_le_of_lt' (Multiset.le_iff_count.mp h p.1)

@[simp]
/-
**Multiset.toEnumFinset_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toEnumFinset_subset_iff {m₁ m₂ : Multiset α} : m₁.toEnumFinset subseteq m₂
.toEnumFinset ↔ m₁ <= m₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_toEnumFinset_fst`：∀ {α : Type u_1} [inst : DecidableEq α] (
m : Multiset α), Multiset.map Prod.fst m.toEnumFinset.val = m
· 使用定理 `Multiset.map_fst_le_of_subset_toEnumFinset`：∀ {α : Type u_1} [inst : Dec
idableEq α] {m : Multiset α} {s : Finset (α × ℕ)},   s ⊆ m.toEnumFinset → Multis
et.map Prod.fst s.val ≤ m
· 使用定理 `Multiset.toEnumFinset_mono`：toEnumFinset_mono {m₁ m₂ : Multiset α} (h : 
m₁ <= m₂) : m₁.toEnumFinset subseteq m₂.toEnumFinset
-/
theorem toEnumFinset_subset_iff {m₁ m₂ : Multiset α} :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset ↔ m₁ ≤ m₂ :=
  ⟨fun h ↦ by simpa using map_fst_le_of_subset_toEnumFinset h, Multiset.toEnumFinset_mono⟩

/-- The embedding from a multiset into `α × ℕ` where the second coordinate enumerates repeats.
If you are looking for the function `m → α`, that would be plain `(↑)`. -/
@[simps]
/-
**Multiset.coeEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：coeEmbedding (m : Multiset α) : m ↪ α × Nat where toFun x
参数：m : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from a multiset into `α × ℕ` where the second coordinate enumerate
s repeats.
If you are looking for the function `m → α`, that would be plain `(↑)`.
-/
def coeEmbedding (m : Multiset α) : m ↪ α × ℕ where
  toFun x := (x, x.2)
  inj' := by
    intro ⟨x, i, hi⟩ ⟨y, j, hj⟩
    rintro ⟨⟩
    rfl

/-- Another way to coerce a `Multiset` to a type is to go through `m.toEnumFinset` and coerce
that `Finset` to a type. -/
@[simps]
/-
**Multiset.coeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：coeEquiv (m : Multiset α) : m ≃ m.toEnumFinset where toFun x
参数：m : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Another way to coerce a `Multiset` to a type is to go through `m.toEnumFinset` a
nd coerce
that `Finset` to a type.
-/
def coeEquiv (m : Multiset α) : m ≃ m.toEnumFinset where
  toFun x :=
    ⟨m.coeEmbedding x, by
      rw [Multiset.mem_toEnumFinset]
      exact x.2.2⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      rw [← Multiset.mem_toEnumFinset]
      exact x.2⟩

@[simp]
/-
**Multiset.toEmbedding_coeEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toEmbedding_coeEquiv_trans (m : Multiset α) : m.coeEquiv.toEmbedding.trans
 (Function.Embedding.subtype _) = m.coeEmbedding
参数：m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem toEmbedding_coeEquiv_trans (m : Multiset α) :
    m.coeEquiv.toEmbedding.trans (Function.Embedding.subtype _) = m.coeEmbedding := by ext <;> rfl
/-
**Multiset.fintypeCoe** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：fintypeCoe : Fintype m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance fintypeCoe : Fintype m :=
  Fintype.ofEquiv m.toEnumFinset m.coeEquiv.symm

attribute [irreducible] fintypeCoe
/-
**Multiset.map_univ_coeEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_univ_coeEmbedding (m : Multiset α) : (Finset.univ : Finset m).map m.co
eEmbedding = m.toEnumFinset
参数：m : Multiset α。
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
· 使用定理 `Multiset.coeEmbedding_apply`：∀ {α : Type u_1} [inst : DecidableEq α] (m 
: Multiset α) (x : m.ToType), m.coeEmbedding x = (x.fst, ↑x.snd)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_univ_coeEmbedding (m : Multiset α) :
    (Finset.univ : Finset m).map m.coeEmbedding = m.toEnumFinset := by
  ext ⟨x, i⟩
  simp only [Fin.exists_iff, Finset.mem_map, Finset.mem_univ, Multiset.coeEmbedding_apply,
    Prod.mk_inj, Multiset.exists_coe, Multiset.coe_mk,
    exists_prop, exists_eq_right_right, exists_eq_right, Multiset.mem_toEnumFinset, true_and]

@[simp]
/-
**Multiset.map_univ_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_univ_coe (m : Multiset α) : (Finset.univ : Finset m).val.map (fun x : 
m => (x : α)) = m
参数：m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_toEnumFinset_fst`：∀ {α : Type u_1} [inst : DecidableEq α] (
m : Multiset α), Multiset.map Prod.fst m.toEnumFinset.val = m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.coeEmbedding_apply`：∀ {α : Type u_1} [inst : DecidableEq α] (m 
: Multiset α) (x : m.ToType), m.coeEmbedding x = (x.fst, ↑x.snd)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_univ_coeEmbedding`：map_univ_coeEmbedding (m : Multiset α) :
 (Finset.univ : Finset m).map m.coeEmbedding = m.toEnumFinset
-/
theorem map_univ_coe (m : Multiset α) :
    (Finset.univ : Finset m).val.map (fun x : m ↦ (x : α)) = m := by
  have := m.map_toEnumFinset_fst
  rw [← m.map_univ_coeEmbedding] at this
  simpa only [Finset.map_val, Multiset.coeEmbedding_apply, Multiset.map_map,
    Function.comp_apply] using this
/-
**Multiset.map_univ_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_univ_comp_coe {β : Type*} (m : Multiset α) (f : α -> β) : ((Finset.uni
v : Finset m).val.map (f ∘ (fun x : m => (x : α)))) = m.map f
参数：m : Multiset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_univ_coe`：map_univ_coe (m : Multiset α) : (Finset.univ : Fi
nset m).val.map (fun x : m => (x : α)) = m
-/
theorem map_univ_comp_coe {β : Type*} (m : Multiset α) (f : α → β) :
    ((Finset.univ : Finset m).val.map (f ∘ (fun x : m ↦ (x : α)))) = m.map f := by
  rw [← Multiset.map_map, Multiset.map_univ_coe]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Multiset.map_univ** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_univ {β : Type*} (m : Multiset α) (f : α -> β) : ((Finset.univ : Finse
t m).val.map fun (x : m) => f (x : α)) = m.map f
参数：m : Multiset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Multiset.map_univ_comp_coe`：map_univ_comp_coe {β : Type*} (m : Multiset 
α) (f : α -> β) : ((Finset.univ : Finset m).val.map (f ∘ (fun x : m => (x : α)))
) = m.map f
-/
theorem map_univ {β : Type*} (m : Multiset α) (f : α → β) :
    ((Finset.univ : Finset m).val.map fun (x : m) ↦ f (x : α)) = m.map f := by
  simp_rw [← Function.comp_apply (f := f)]
  exact map_univ_comp_coe m f

@[simp]
/-
**Multiset.card_toEnumFinset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_toEnumFinset (m : Multiset α) : m.toEnumFinset.card = Multiset.card m
参数：m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card.eq_1`：∀ {α : Type u_1} (s : Finset α), s.card = s.val.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.map_toEnumFinset_fst`：∀ {α : Type u_1} [inst : DecidableEq α] (
m : Multiset α), Multiset.map Prod.fst m.toEnumFinset.val = m
-/
theorem card_toEnumFinset (m : Multiset α) : m.toEnumFinset.card = Multiset.card m := by
  rw [Finset.card, ← Multiset.card_map Prod.fst m.toEnumFinset.val]
  congr
  exact m.map_toEnumFinset_fst

@[simp]
/-
**Multiset.card_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_coe (m : Multiset α) : Fintype.card m = Multiset.card m
参数：m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Multiset.card_toEnumFinset`：card_toEnumFinset (m : Multiset α) : m.toEnu
mFinset.card = Multiset.card m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_coe (m : Multiset α) : Fintype.card m = Multiset.card m := by
  rw [Fintype.card_congr m.coeEquiv]
  simp only [Fintype.card_coe, card_toEnumFinset]

@[to_additive]
/-
**Multiset.prod_eq_prod_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_eq_prod_coe [CommMonoid α] (m : Multiset α) : m.prod = ∏ x : m, (x : 
α)
参数：m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_univ_coe`：map_univ_coe (m : Multiset α) : (Finset.univ : Fi
nset m).val.map (fun x : m => (x : α)) = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_eq_prod_coe [CommMonoid α] (m : Multiset α) : m.prod = ∏ x : m, (x : α) := by
  congr
  simp

@[to_additive]
/-
**Multiset.prod_eq_prod_toEnumFinset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_eq_prod_toEnumFinset [CommMonoid α] (m : Multiset α) : m.prod = ∏ x i
n m.toEnumFinset, x.1
参数：m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_toEnumFinset_fst`：∀ {α : Type u_1} [inst : DecidableEq α] (
m : Multiset α), Multiset.map Prod.fst m.toEnumFinset.val = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_eq_prod_toEnumFinset [CommMonoid α] (m : Multiset α) :
    m.prod = ∏ x ∈ m.toEnumFinset, x.1 := by
  congr
  simp

@[to_additive]
/-
**Multiset.prod_toEnumFinset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_toEnumFinset {β : Type*} [CommMonoid β] (m : Multiset α) (f : α -> Na
t -> β) : ∏ x in m.toEnumFinset, f x.1 x.2 = ∏ x : m, f x x.2
参数：m : Multiset α；f : α -> Nat -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_coe_sort`：prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i
-/
theorem prod_toEnumFinset {β : Type*} [CommMonoid β] (m : Multiset α) (f : α → ℕ → β) :
    ∏ x ∈ m.toEnumFinset, f x.1 x.2 = ∏ x : m, f x x.2 := by
  rw [Fintype.prod_equiv m.coeEquiv (fun x ↦ f x x.2) fun x ↦ f x.1.1 x.1.2]
  · rw [← m.toEnumFinset.prod_coe_sort fun x ↦ f x.1 x.2]
  · intro x
    rfl

/--
If `s = t` then there's an equivalence between the appropriate types.
-/
@[simps]
/-
**Multiset.cast** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：cast {s t : Multiset α} (h : s = t) : s ≃ t where toFun x
参数：h : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s = t` then there's an equivalence between the appropriate types.
-/
def cast {s t : Multiset α} (h : s = t) : s ≃ t where
  toFun x := ⟨x.1, x.2.cast (by simp [h])⟩
  invFun x := ⟨x.1, x.2.cast (by simp [h])⟩
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEmpty (0 : Multiset α) := Fintype.card_eq_zero_iff.mp (by simp)
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEmpty (∅ : Multiset α) := Fintype.card_eq_zero_iff.mp (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
`v ::ₘ m` is equivalent to `Option m` by mapping one `v` to `none` and everything else to `m`.
-/
/-
**Multiset.consEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：consEquiv {v : α} : v ::ₘ m ≃ Option m where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`v ::ₘ m` is equivalent to `Option m` by mapping one `v` to `none` and everythin
g else to `m`.
-/
def consEquiv {v : α} : v ::ₘ m ≃ Option m where
  toFun x := if h : x.1 = v ∧ x.2.val = m.count v then none else some ⟨x.1, ⟨x.2, by
    by_cases hv : x.1 = v
    · simp only [hv, true_and] at h ⊢
      apply lt_of_le_of_ne (Nat.le_of_lt_add_one _) h
      convert! x.2.2 using 1
      simp [hv]
    · convert! x.2.2 using 1
      exact (count_cons_of_ne hv _).symm
    ⟩⟩
  invFun x := x.elim ⟨v, ⟨m.count v, by simp⟩⟩ (fun x ↦ ⟨x.1, x.2.castLE (count_le_count_cons ..)⟩)
  left_inv := by
    rintro ⟨x, hx⟩
    dsimp only
    split
    · rename_i h
      obtain ⟨rfl, h2⟩ := h
      simp [← h2]
    · simp
  right_inv := by
    rintro (_ | x)
    · simp
    · simp only [Option.elim_some, Fin.val_castLE, Fin.eta, Sigma.eta, dite_eq_ite,
        ite_eq_right_iff, reduceCtorEq, imp_false, not_and]
      rintro rfl
      exact x.2.2.ne

@[simp]
/-
**Multiset.consEquiv_symm_none** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：consEquiv_symm_none {v : α} : (consEquiv (m
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma consEquiv_symm_none {v : α} :
    (consEquiv (m := m) (v := v)).symm none =
      ⟨v, ⟨m.count v, (count_cons_self v m) ▸ (Nat.lt_add_one _)⟩⟩ :=
  rfl

@[simp]
/-
**Multiset.consEquiv_symm_some** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：consEquiv_symm_some {v : α} {x : m} : (consEquiv (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma consEquiv_symm_some {v : α} {x : m} :
    (consEquiv (v := v)).symm (some x) =
      ⟨x, x.2.castLE (count_le_count_cons ..)⟩ :=
  rfl
/-
**Multiset.coe_consEquiv_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：coe_consEquiv_of_ne {v : α} (x : v ::ₘ m) (hx : ↑x != v) : consEquiv x = s
ome ⟨x.1, x.2.cast (by simp [hx])⟩
参数：x : v ::ₘ m；hx : ↑x != v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
lemma coe_consEquiv_of_ne {v : α} (x : v ::ₘ m) (hx : ↑x ≠ v) :
    consEquiv x = some ⟨x.1, x.2.cast (by simp [hx])⟩ := by
  simp [consEquiv, hx]
  rfl
/-
**Multiset.coe_consEquiv_of_eq_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：coe_consEquiv_of_eq_of_eq {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 =
 m.count v) : consEquiv x = none
参数：x : v ::ₘ m；hx : ↑x = v；hx2 : x.2 = m.count v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma coe_consEquiv_of_eq_of_eq {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 = m.count v) :
    consEquiv x = none := by simp [consEquiv, hx, hx2]
/-
**Multiset.coe_consEquiv_of_eq_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：coe_consEquiv_of_eq_of_lt {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 <
 m.count v) : consEquiv x = some ⟨x.1, ⟨x.2, by simpa [hx]⟩⟩
参数：x : v ::ₘ m；hx : ↑x = v；hx2 : x.2 < m.count v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
lemma coe_consEquiv_of_eq_of_lt {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 < m.count v) :
    consEquiv x = some ⟨x.1, ⟨x.2, by simpa [hx]⟩⟩ := by simp [consEquiv, hx, hx2.ne]

set_option backward.isDefEq.respectTransparency false in
/--
There is some equivalence between `m` and `m.map f` which respects `f`.
-/
/-
**Multiset.mapEquivAux** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：mapEquivAux (m : Multiset α) (f : α -> β) : Squash { v : m ≃ m.map f // fo
rall a : m, v a = f a}
参数：m : Multiset α；f : α -> β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
There is some equivalence between `m` and `m.map f` which respects `f`.
-/
def mapEquivAux (m : Multiset α) (f : α → β) :
    Squash { v : m ≃ m.map f // ∀ a : m, v a = f a} :=
  Quotient.recOnSubsingleton m fun l ↦ .mk <|
    List.recOn l
      ⟨@Equiv.equivOfIsEmpty _ _ (by dsimp; infer_instance) (by dsimp; infer_instance), by simp⟩
      fun a s ⟨v, hv⟩ ↦ ⟨Multiset.consEquiv.trans v.optionCongr |>.trans
        Multiset.consEquiv.symm |>.trans (Multiset.cast (map_cons f a s)).symm, fun x ↦ by
        simp only [consEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.optionCongr_apply,
            Equiv.coe_fn_symm_mk]
        split <;> simp_all⟩

@[deprecated (since := "2026-06-06")] alias mapEquiv_aux := mapEquivAux

/--
One of the possible equivalences from `Multiset.mapEquivAux`, selected using choice.
-/
/-
**Multiset.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：mapEquiv (s : Multiset α) (f : α -> β) : s ≃ s.map f
参数：s : Multiset α；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One of the possible equivalences from `Multiset.mapEquivAux`, selected using cho
ice.
-/
noncomputable def mapEquiv (s : Multiset α) (f : α → β) : s ≃ s.map f :=
  (Multiset.mapEquivAux s f).out.1

@[simp]
/-
**Multiset.mapEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mapEquiv_apply (s : Multiset α) (f : α -> β) (v : s) : s.mapEquiv f v = f 
v
参数：s : Multiset α；f : α -> β；v : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mapEquiv_apply (s : Multiset α) (f : α → β) (v : s) : s.mapEquiv f v = f v :=
  (Multiset.mapEquivAux s f).out.2 v

end Multiset

