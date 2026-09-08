/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Countable.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Logic.Equiv.List
public import Mathlib.Order.Preorder.Finite

/-!
# Countable sets

In this file we define `Set.Countable s` as `Countable s`
and prove basic properties of this definition.

Note that this definition does not provide a computable encoding.
For a noncomputable conversion to `Encodable s`, use `Set.Countable.nonempty_encodable`.

## Keywords

sets, countable set
-/

@[expose] public section

assert_not_exists Monoid Multiset.sort

noncomputable section

open Function Set Encodable

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace Set

/-- A set `s` is countable if the corresponding subtype is countable,
i.e., there exists an injective map `f : s → ℕ`.

Note that this is an abbreviation, so `hs : Set.Countable s` in the proof context
is the same as an instance `Countable s`.
For a constructive version, see `Encodable`.
-/
/-
**Set.Countable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u} → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is countable if the corresponding subtype is countable,
i.e., there exists an injective map `f : s → ℕ`.

Note that this is an abbreviation, so `hs : Set.Countable s` in the proof contex
t
is the same as an instance `Countable s`.
For a constructive version, see `Encodable`.
-/
protected def Countable (s : Set α) : Prop := Countable s

@[simp]
/-
**Set.countable_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_coe_iff {s : Set α} : Countable s ↔ s.Countable
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem countable_coe_iff {s : Set α} : Countable s ↔ s.Countable := .rfl

/-- Prove `Set.Countable` from a `Countable` instance on the subtype. -/
/-
**Set.to_countable** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：to_countable (s : Set α) [Countable s] : s.Countable
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prove `Set.Countable` from a `Countable` instance on the subtype.
-/
theorem to_countable (s : Set α) [Countable s] : s.Countable := ‹_›

/-- Restate `Set.Countable` as a `Countable` instance. -/
alias ⟨_root_.Countable.to_set, Countable.to_subtype⟩ := countable_coe_iff

/-
**Set.countable_iff_exists_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Countable ↔ ∃ f, Function.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `countable_iff_exists_injective`：∀ (α : Sort u), Countable α ↔ ∃ f, Funct
ion.Injective f
-/
protected theorem countable_iff_exists_injective {s : Set α} :
    s.Countable ↔ ∃ f : s → ℕ, Injective f :=
  countable_iff_exists_injective s

/-- A set `s : Set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
/-
**Set.countable_iff_exists_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_iff_exists_injOn {s : Set α} : s.Countable ↔ exists f : α -> Nat
, InjOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.countable_iff_exists_injective`：∀ {α : Type u} {s : Set α}, s.Counta
ble ↔ ∃ f, Function.Injective f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.exists_injOn_iff_injective`：exists_injOn_iff_injective [Nonempty β] 
: (exists f : α -> β, InjOn f s) ↔ exists f : s -> β, Injective f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A set `s : Set α` is countable if and only if there exists a function `α → ℕ` in
jective
on `s`.
-/
theorem countable_iff_exists_injOn {s : Set α} : s.Countable ↔ ∃ f : α → ℕ, InjOn f s :=
  Set.countable_iff_exists_injective.trans exists_injOn_iff_injective.symm
/-
**Set.countable_iff_nonempty_encodable** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_iff_nonempty_encodable {s : Set α} : s.Countable ↔ Nonempty (Enc
odable s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Encodable.nonempty_encodable`：nonempty_encodable : Nonempty (Encodable α
) ↔ Countable α
-/
theorem countable_iff_nonempty_encodable {s : Set α} : s.Countable ↔ Nonempty (Encodable s) :=
  Encodable.nonempty_encodable.symm

alias ⟨Countable.nonempty_encodable, _⟩ := countable_iff_nonempty_encodable

/-- Convert `Set.Countable s` to `Encodable s` (noncomputable). -/
@[instance_reducible]
/-
**Set.Countable.toEncodable** 是 Mathlib 中的一个定义，位于命名空间 `Set.Countable`。
形式化陈述：{α : Type u} → {s : Set α} → s.Countable → Encodable ↑s
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.nonempty_encodable`：∀ {α : Type u} {s : Set α}, s.Countabl
e → Nonempty (Encodable ↑s)

--- 原说明 ---
Convert `Set.Countable s` to `Encodable s` (noncomputable).
-/
protected def Countable.toEncodable {s : Set α} (hs : s.Countable) : Encodable s :=
  Classical.choice hs.nonempty_encodable

section Enumerate

/-- Noncomputably enumerate elements in a set. The `default` value is used to extend the domain to
all of `ℕ`. -/
/-
**Set.enumerateCountable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：enumerateCountable {s : Set α} (h : s.Countable) (default : α) : Nat -> α
参数：h : s.Countable；default : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputably enumerate elements in a set. The `default` value is used to extend
 the domain to
all of `ℕ`.
-/
def enumerateCountable {s : Set α} (h : s.Countable) (default : α) : ℕ → α := fun n =>
  match @Encodable.decode s h.toEncodable n with
  | some y => y
  | none => default
/-
**Set.subset_range_enumerate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_range_enumerate {s : Set α} (h : s.Countable) (default : α) : s sub
seteq range (enumerateCountable h default)
参数：h : s.Countable；default : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subset_range_enumerate {s : Set α} (h : s.Countable) (default : α) :
    s ⊆ range (enumerateCountable h default) := fun x hx =>
  ⟨@Encodable.encode s h.toEncodable ⟨x, hx⟩, by
    simp [enumerateCountable, Encodable.encodek]⟩
/-
**Set.range_enumerateCountable_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：range_enumerateCountable_subset {s : Set α} (h : s.Countable) (default : α
) : range (enumerateCountable h default) subseteq insert default s
参数：h : s.Countable；default : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.enumerateCountable.eq_1`：∀ {α : Type u} {s : Set α} (h : s.Countable
) (default : α) (n : ℕ),   Set.enumerateCountable h default n =     match Encoda
ble.decode n with…
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma range_enumerateCountable_subset {s : Set α} (h : s.Countable) (default : α) :
    range (enumerateCountable h default) ⊆ insert default s := by
  refine range_subset_iff.mpr (fun n ↦ ?_)
  rw [enumerateCountable]
  match @decode s (Countable.toEncodable h) n with
  | none => exact mem_insert _ _
  | some val => simp
/-
**Set.range_enumerateCountable_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：range_enumerateCountable_of_mem {s : Set α} (h : s.Countable) {default : α
} (h_mem : default in s) : range (enumerateCountable h default) = s
参数：h : s.Countable；h_mem : default in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `Set.range_enumerateCountable_subset`：range_enumerateCountable_subset {s 
: Set α} (h : s.Countable) (default : α) : range (enumerateCountable h default) 
subseteq insert default s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `Set.subset_range_enumerate`：subset_range_enumerate {s : Set α} (h : s.Co
untable) (default : α) : s subseteq range (enumerateCountable h default)
-/
lemma range_enumerateCountable_of_mem {s : Set α} (h : s.Countable) {default : α}
    (h_mem : default ∈ s) :
    range (enumerateCountable h default) = s :=
  subset_antisymm ((range_enumerateCountable_subset h _).trans_eq (insert_eq_of_mem h_mem))
    (subset_range_enumerate h default)
/-
**Set.enumerateCountable_mem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：enumerateCountable_mem {s : Set α} (h : s.Countable) {default : α} (h_mem 
: default in s) (n : Nat) : enumerateCountable h default n in s
参数：h : s.Countable；h_mem : default in s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.range_enumerateCountable_of_mem`：range_enumerateCountable_of_mem {s 
: Set α} (h : s.Countable) {default : α} (h_mem : default in s) : range (enumera
teCountable h default) = …
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma enumerateCountable_mem {s : Set α} (h : s.Countable) {default : α} (h_mem : default ∈ s)
    (n : ℕ) :
    enumerateCountable h default n ∈ s := by
  convert! mem_range_self n
  exact (range_enumerateCountable_of_mem h h_mem).symm

end Enumerate

/-
**Set.Countable.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countable → s₁.Countable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem Countable.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) (hs : s₂.Countable) : s₁.Countable :=
  have := hs.to_subtype; (inclusion_injective h).countable
/-
**Set.countable_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_range [Countable ι] (f : ι -> β) : (range f).Countable
参数：f : ι -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.to_set`：∀ {α : Type u} {s : Set α}, Countable ↑s → s.Countable
· 使用定理 `Function.Surjective.countable`：∀ {α : Sort u} {β : Sort v} [Countable α]
 {f : α → β}, Function.Surjective f → Countable β
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
-/
theorem countable_range [Countable ι] (f : ι → β) : (range f).Countable :=
  rangeFactorization_surjective.countable.to_set
/-
**Set.countable_iff_exists_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_iff_exists_subset_range [Nonempty α] {s : Set α} : s.Countable ↔
 exists f : Nat -> α, s subseteq range f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_range_enumerate`：subset_range_enumerate {s : Set α} (h : s.Co
untable) (default : α) : s subseteq range (enumerateCountable h default)
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem countable_iff_exists_subset_range [Nonempty α] {s : Set α} :
    s.Countable ↔ ∃ f : ℕ → α, s ⊆ range f :=
  ⟨fun h => by
    inhabit α
    exact ⟨enumerateCountable h default, subset_range_enumerate _ _⟩, fun ⟨f, hsf⟩ =>
    (countable_range f).mono hsf⟩

/-- A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
/-
**Set.countable_iff_exists_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nonempty → (s.Countable ↔ ∃ f, Function.Surj
ective f)
参数：s.Countable ↔ ∃ f, Function.Surjective f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `countable_iff_exists_surjective`：countable_iff_exists_surjective [Nonemp
ty α] : Countable α ↔ exists f : Nat -> α, Surjective f
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s

--- 原说明 ---
A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
protected theorem countable_iff_exists_surjective {s : Set α} (hs : s.Nonempty) :
    s.Countable ↔ ∃ f : ℕ → s, Surjective f :=
  @countable_iff_exists_surjective s hs.to_subtype

alias ⟨Countable.exists_surjective, _⟩ := Set.countable_iff_exists_surjective
/-
**Set.countable_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_univ_iff : (univ : Set α).Countable ↔ Countable α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.countable_coe_iff`：countable_coe_iff {s : Set α} : Countable s ↔ s.C
ountable
· 使用定理 `Equiv.countable_iff`：Equiv.countable_iff (e : α ≃ β) : Countable α ↔ Cou
ntable β
-/
theorem countable_univ_iff : (univ : Set α).Countable ↔ Countable α :=
  countable_coe_iff.symm.trans (Equiv.Set.univ _).countable_iff
/-
**Set.countable_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_univ [Countable α] : (univ : Set α).Countable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
theorem countable_univ [Countable α] : (univ : Set α).Countable :=
  to_countable univ
/-
**Set.not_countable_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_countable_univ_iff : ¬ (univ : Set α).Countable ↔ Uncountable α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.countable_univ_iff`：countable_univ_iff : (univ : Set α).Countable ↔ 
Countable α
· 使用引理 `not_countable_iff`：not_countable_iff : ¬Countable α ↔ Uncountable α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_countable_univ_iff : ¬ (univ : Set α).Countable ↔ Uncountable α := by
  rw [countable_univ_iff, not_countable_iff]
/-
**Set.not_countable_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_countable_univ [Uncountable α] : ¬ (univ : Set α).Countable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.not_countable_univ_iff`：not_countable_univ_iff : ¬ (univ : Set α).Co
untable ↔ Uncountable α
-/
theorem not_countable_univ [Uncountable α] : ¬ (univ : Set α).Countable :=
  not_countable_univ_iff.2 ‹_›

/-- If `s : Set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
/-
**Set.Countable.exists_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Countable → s.Nonempty → ∃ f, s = Set.range 
f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.exists_surjective`：∀ {α : Type u} {s : Set α}, s.Nonempty 
→ s.Countable → ∃ f, Function.Surjective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s

--- 原说明 ---
If `s : Set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`.
-/
theorem Countable.exists_eq_range {s : Set α} (hc : s.Countable) (hs : s.Nonempty) :
    ∃ f : ℕ → α, s = range f := by
  rcases hc.exists_surjective hs with ⟨f, hf⟩
  refine ⟨(↑) ∘ f, ?_⟩
  rw [hf.range_comp, Subtype.range_coe]
/-
**Set.countable_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u}, ∅.Countable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
@[simp] theorem countable_empty : (∅ : Set α).Countable := to_countable _
/-
**Set.countable_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} (a : α), {a}.Countable
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
@[simp] theorem countable_singleton (a : α) : ({a} : Set α).Countable := to_countable _
/-
**Set.Countable.image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countable → ∀ (f : α → β), (f '
' s).Countable
参数：f : α → β；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
-/
theorem Countable.image {s : Set α} (hs : s.Countable) (f : α → β) : (f '' s).Countable := by
  rw [image_eq_range]
  have := hs.to_subtype
  apply countable_range
/-
**Set.Infinite.exists_subset_countable_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set.I
nfinite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Infinite → ∃ t ⊆ s, t.Countable ∧ t.Infinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Set.infinite_range_of_injective`：infinite_range_of_injective [Infinite α
] {f : α -> β} (hi : Injective f) : (range f).Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
theorem Infinite.exists_subset_countable_infinite {α : Type u} {s : Set α} (hs : s.Infinite) :
    ∃ t ⊆ s, t.Countable ∧ t.Infinite := by
  obtain ⟨f, hf⟩ := Infinite.natEmbedding s hs
  refine ⟨range (Subtype.val ∘ f), ?_, ?_, ?_⟩
  · exact fun _ ⟨y, hy⟩ ↦ hy ▸ Subtype.coe_prop (f y)
  · exact countable_range (Subtype.val ∘ f)
  · exact infinite_range_of_injective <| Injective.comp Subtype.val_injective hf
/-
**Set.MapsTo.countable_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} {t : Set β} {f : α → β},   Set.Map
sTo f s t → Set.InjOn f s → t.Countable → s.Countable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Function.Injective.codRestrict`：∀ {α : Type u_1} {ι : Sort u_5} {f : ι →
 α} {s : Set α} (h : ∀ (x : ι), f x ∈ s),   Function.Injective f → Function.Inje
ctive (Set.codRestri…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
-/
theorem MapsTo.countable_of_injOn {s : Set α} {t : Set β} {f : α → β} (hf : MapsTo f s t)
    (hf' : InjOn f s) (ht : t.Countable) : s.Countable :=
  have := ht.to_subtype
  have : Injective (hf.restrict f s t) := (injOn_iff_injective.1 hf').codRestrict _
  this.countable
/-
**Set.Countable.preimage_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set β}, s.Countable → ∀ {f : α → β}, Set.
InjOn f (f ⁻¹' s) → (f ⁻¹' s).Countable
参数：f ⁻¹' s；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.countable_of_injOn`：∀ {α : Type u} {β : Type v} {s : Set α} {
t : Set β} {f : α → β},   Set.MapsTo f s t → Set.InjOn f s → t.Countable → s.Cou
ntable
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
theorem Countable.preimage_of_injOn {s : Set β} (hs : s.Countable) {f : α → β}
    (hf : InjOn f (f ⁻¹' s)) : (f ⁻¹' s).Countable :=
  (mapsTo_preimage f s).countable_of_injOn hf hs
/-
**Set.Countable.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set β}, s.Countable → ∀ {f : α → β}, Func
tion.Injective f → (f ⁻¹' s).Countable
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.preimage_of_injOn`：∀ {α : Type u} {β : Type v} {s : Set β}
, s.Countable → ∀ {f : α → β}, Set.InjOn f (f ⁻¹' s) → (f ⁻¹' s).Countable
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
protected theorem Countable.preimage {s : Set β} (hs : s.Countable) {f : α → β} (hf : Injective f) :
    (f ⁻¹' s).Countable :=
  hs.preimage_of_injOn hf.injOn
/-
**Set.exists_seq_iSup_eq_top_iff_countable** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_seq_iSup_eq_top_iff_countable [CompleteLattice α] {p : α -> Prop} (
h : exists x, p x) : (exists s : Nat -> α, (forall n, p (s n)) ∧ ⨆ n, s n = ⊤) ↔
 exists S : Set α, S.Countable ∧ (forall s in S, p s) ∧ sSup S = ⊤
参数：h : exists x, p x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.countable_iff_exists_surjective`：∀ {α : Type u} {s : Set α}, s.Nonem
pty → (s.Countable ↔ ∃ f, Function.Surjective f)
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `Function.Surjective.iSup_comp`：Function.Surjective.iSup_comp {f : ι -> ι
'} (hf : Surjective f) (g : ι' -> α) : ⨆ x, g (f x) = ⨆ y, g y
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
-/
theorem exists_seq_iSup_eq_top_iff_countable [CompleteLattice α] {p : α → Prop} (h : ∃ x, p x) :
    (∃ s : ℕ → α, (∀ n, p (s n)) ∧ ⨆ n, s n = ⊤) ↔
      ∃ S : Set α, S.Countable ∧ (∀ s ∈ S, p s) ∧ sSup S = ⊤ := by
  constructor
  · rintro ⟨s, hps, hs⟩
    refine ⟨range s, countable_range s, forall_mem_range.2 hps, ?_⟩
    rwa [sSup_range]
  · rintro ⟨S, hSc, hps, hS⟩
    rcases eq_empty_or_nonempty S with (rfl | hne)
    · rw [sSup_empty] at hS
      have := subsingleton_of_bot_eq_top hS
      rcases h with ⟨x, hx⟩
      exact ⟨fun _ => x, fun _ => hx, Subsingleton.elim _ _⟩
    · rcases (Set.countable_iff_exists_surjective hne).1 hSc with ⟨s, hs⟩
      refine ⟨fun n => s n, fun n => hps _ (s n).coe_prop, ?_⟩
      rwa [hs.iSup_comp, ← sSup_eq_iSup']
/-
**Set.exists_seq_cover_iff_countable** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_seq_cover_iff_countable {p : Set α -> Prop} (h : exists s, p s) : (
exists s : Nat -> Set α, (forall n, p (s n)) ∧ ⋃ n, s n = univ) ↔ exists S : Set
 (Set α), S.Countable ∧ (forall s in S, p s) ∧ ⋃₀ S = univ
参数：h : exists s, p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_seq_iSup_eq_top_iff_countable`：exists_seq_iSup_eq_top_iff_cou
ntable [CompleteLattice α] {p : α -> Prop} (h : exists x, p x) : (exists s : Nat
 -> α, (forall n, p (s n)) ∧ ⨆…
-/
theorem exists_seq_cover_iff_countable {p : Set α → Prop} (h : ∃ s, p s) :
    (∃ s : ℕ → Set α, (∀ n, p (s n)) ∧ ⋃ n, s n = univ) ↔
      ∃ S : Set (Set α), S.Countable ∧ (∀ s ∈ S, p s) ∧ ⋃₀ S = univ :=
  exists_seq_iSup_eq_top_iff_countable h
/-
**Set.countable_of_injective_of_countable_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_of_injective_of_countable_image {s : Set α} {f : α -> β} (hf : I
njOn f s) (hs : (f '' s).Countable) : s.Countable
参数：hf : InjOn f s；hs : (f '' s).Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.countable_of_injOn`：∀ {α : Type u} {β : Type v} {s : Set α} {
t : Set β} {f : α → β},   Set.MapsTo f s t → Set.InjOn f s → t.Countable → s.Cou
ntable
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem countable_of_injective_of_countable_image {s : Set α} {f : α → β} (hf : InjOn f s)
    (hs : (f '' s).Countable) : s.Countable :=
  (mapsTo_image _ _).countable_of_injOn hf hs
/-
**Set.countable_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_iUnion {t : ι -> Set α} [Countable ι] (ht : forall i, (t i).Coun
table) : (⋃ i, t i).Countable
参数：ht : forall i, (t i).Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_eq_range_psigma`：iUnion_eq_range_psigma (s : ι -> Set β) : ⋃ 
i, s i = range fun a : Σ' i, s i => a.2
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountablePSigma`：∀ {α : Sort u} {π : α → Sort w} [Countable α] [∀ (a
 : α), Countable (π a)], Countable (PSigma π)
-/
theorem countable_iUnion {t : ι → Set α} [Countable ι] (ht : ∀ i, (t i).Countable) :
    (⋃ i, t i).Countable := by
  have := fun i ↦ (ht i).to_subtype
  rw [iUnion_eq_range_psigma]
  apply countable_range

@[simp]
/-
**Set.countable_iUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_iUnion_iff [Countable ι] {t : ι -> Set α} : (⋃ i, t i).Countable
 ↔ forall i, (t i).Countable
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
-/
theorem countable_iUnion_iff [Countable ι] {t : ι → Set α} :
    (⋃ i, t i).Countable ↔ ∀ i, (t i).Countable :=
  ⟨fun h _ => h.mono <| subset_iUnion _ _, countable_iUnion⟩
/-
**Set.Countable.biUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} {t : (a : α) → a ∈ s → Set β},   s
.Countable → ((⋃ a, ⋃ (h : a ∈ s), t a h).Countable ↔ ∀ (a : α) (ha : a ∈ s), (t
 a ha).Countable)
参数：a : α；(⋃ a, ⋃ (h : a ∈ s), t a h).Countable ↔ ∀ (a : α) (ha : a ∈ s), (t a ha
).Countable。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Set.countable_iUnion_iff`：countable_iUnion_iff [Countable ι] {t : ι -> S
et α} : (⋃ i, t i).Countable ↔ forall i, (t i).Countable
· 使用定理 `SetCoe.forall'`：SetCoe.forall' {s : Set α} {p : forall x, x in s -> Prop
} : (forall (x) (h : x in s), p x h) ↔ forall x : s, p x.1 x.2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Countable.biUnion_iff {s : Set α} {t : ∀ a ∈ s, Set β} (hs : s.Countable) :
    (⋃ a ∈ s, t a ‹_›).Countable ↔ ∀ a (ha : a ∈ s), (t a ha).Countable := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion, countable_iUnion_iff, SetCoe.forall']
/-
**Set.Countable.sUnion_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {s : Set (Set α)}, s.Countable → ((⋃₀ s).Countable ↔ ∀ a ∈ 
s, a.Countable)
参数：Set α；(⋃₀ s).Countable ↔ ∀ a ∈ s, a.Countable。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Set.Countable.biUnion_iff`：∀ {α : Type u} {β : Type v} {s : Set α} {t : 
(a : α) → a ∈ s → Set β},   s.Countable → ((⋃ a, ⋃ (h : a ∈ s), t a h).Countable
 ↔ ∀ (a : α) (h…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Countable.sUnion_iff {s : Set (Set α)} (hs : s.Countable) :
    (⋃₀ s).Countable ↔ ∀ a ∈ s, a.Countable := by rw [sUnion_eq_biUnion, hs.biUnion_iff]

alias ⟨_, Countable.biUnion⟩ := Countable.biUnion_iff

alias ⟨_, Countable.sUnion⟩ := Countable.sUnion_iff

@[simp]
/-
**Set.countable_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_union {s t : Set α} : (s union t).Countable ↔ s.Countable ∧ t.Co
untable
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem countable_union {s t : Set α} : (s ∪ t).Countable ↔ s.Countable ∧ t.Countable := by
  simp [union_eq_iUnion, and_comm]
/-
**Set.Countable.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s.Countable → t.Countable → (s ∪ t).Countabl
e
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.countable_union`：countable_union {s t : Set α} : (s union t).Countab
le ↔ s.Countable ∧ t.Countable
-/
theorem Countable.union {s t : Set α} (hs : s.Countable) (ht : t.Countable) : (s ∪ t).Countable :=
  countable_union.2 ⟨hs, ht⟩
/-
**Set.Countable.of_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {s t : Set α}, (s \ t).Countable → t.Countable → s.Countabl
e
参数：s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.subset_sdiff_union`：subset_sdiff_union (s t : Set α) : s subseteq s 
\ t union t
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
-/
theorem Countable.of_sdiff {s t : Set α} (h : (s \ t).Countable) (ht : t.Countable) : s.Countable :=
  (h.union ht).mono (subset_sdiff_union _ _)

@[deprecated (since := "2026-06-03")] alias Countable.of_diff := Countable.of_sdiff

@[simp]
/-
**Set.countable_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_insert {s : Set α} {a : α} : (insert a s).Countable ↔ s.Countabl
e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem countable_insert {s : Set α} {a : α} : (insert a s).Countable ↔ s.Countable := by
  simp only [insert_eq, countable_union, countable_singleton, true_and]
/-
**Set.Countable.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {s : Set α} (a : α), s.Countable → (insert a s).Countable
参数：a : α；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.countable_insert`：countable_insert {s : Set α} {a : α} : (insert a s
).Countable ↔ s.Countable
-/
protected theorem Countable.insert {s : Set α} (a : α) (h : s.Countable) : (insert a s).Countable :=
  countable_insert.2 h
/-
**Set.Finite.countable** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
-/
theorem Finite.countable {s : Set α} (hs : s.Finite) : s.Countable :=
  have := hs.to_subtype; s.to_countable

@[nontriviality]
/-
**Set.Countable.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} [Subsingleton α] (s : Set α), s.Countable
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `Set.Finite.of_subsingleton`：∀ {α : Type u} [Subsingleton α] (s : Set α),
 s.Finite
-/
theorem Countable.of_subsingleton [Subsingleton α] (s : Set α) : s.Countable :=
  (Finite.of_subsingleton s).countable
/-
**Set.Subsingleton.countable** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.Countable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
-/
theorem Subsingleton.countable {s : Set α} (hs : s.Subsingleton) : s.Countable :=
  hs.finite.countable
/-
**Set.countable_isTop** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_isTop (α : Type*) [PartialOrder α] : { x : α | IsTop x }.Countab
le
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用引理 `Set.finite_isTop`：finite_isTop : {a : α | IsTop a}.Finite
-/
theorem countable_isTop (α : Type*) [PartialOrder α] : { x : α | IsTop x }.Countable :=
  (finite_isTop α).countable
/-
**Set.countable_isBot** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_isBot (α : Type*) [PartialOrder α] : { x : α | IsBot x }.Countab
le
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `Set.finite_isBot`：∀ (α : Type u_2) [inst : PartialOrder α], {a | IsBot a
}.Finite
-/
theorem countable_isBot (α : Type*) [PartialOrder α] : { x : α | IsBot x }.Countable :=
  (finite_isBot α).countable

/-- The set of finite subsets of a countable set is countable. -/
/-
**Set.countable_ofPred_finite_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_ofPred_finite_subset {s : Set α} (hs : s.Countable) : { t | Set.
Finite t ∧ t subseteq s }.Countable
参数：hs : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)

--- 原说明 ---
The set of finite subsets of a countable set is countable.
-/
theorem countable_ofPred_finite_subset {s : Set α} (hs : s.Countable) :
    { t | Set.Finite t ∧ t ⊆ s }.Countable := by
  have := hs.to_subtype
  refine (countable_range fun t : Finset s => Subtype.val '' (t : Set s)).mono ?_
  rintro t ⟨ht, hts⟩
  lift t to Set s using hts
  lift t to Finset s using ht.of_finite_image Subtype.val_injective.injOn
  exact mem_range_self _

@[deprecated (since := "2026-07-09")]
alias countable_setOf_finite_subset := countable_ofPred_finite_subset

/-- The set of finite sets in a countable type is countable. -/
/-
**Set.Countable.ofPred_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} [Countable α], {s | s.Finite}.Countable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Set.countable_ofPred_finite_subset`：countable_ofPred_finite_subset {s : 
Set α} (hs : s.Countable) : { t | Set.Finite t ∧ t subseteq s }.Countable
· 使用定理 `Set.countable_univ`：countable_univ [Countable α] : (univ : Set α).Counta
ble

--- 原说明 ---
The set of finite sets in a countable type is countable.
-/
theorem Countable.ofPred_finite [Countable α] : {s : Set α | s.Finite}.Countable := by
  simpa using countable_ofPred_finite_subset countable_univ

@[deprecated (since := "2026-07-09")] alias Countable.setOf_finite := Countable.ofPred_finite

/-- If the codomain of a map is countable and the fibres are countable, the domain
is countable. -/
/-
**Set.Countable.of_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} [Countable β], (∀ (b : β), (f ⁻¹' 
{b}).Countable) → Countable α
参数：∀ (b : β), (f ⁻¹' {b}).Countable。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable

--- 原说明 ---
If the codomain of a map is countable and the fibres are countable, the domain
is countable.
-/
theorem Countable.of_preimage_singleton {f : α → β} [Countable β]
    (h : ∀ (b : β), (f ⁻¹' {b}).Countable) : Countable α := by
  simp_rw [← Set.countable_univ_iff, ← Set.preimage_univ (f := f), ← Set.iUnion_of_singleton,
    Set.preimage_iUnion, Set.countable_iUnion h]
/-
**Set.countable_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_univ_pi {π : α -> Type*} [Finite α] {s : forall a, Set (π a)} (h
s : forall a, (s a).Countable) : (pi univ s).Countable
参数：π a；hs : forall a, (s a).Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Countable.of_equiv`：Countable.of_equiv (α : Sort*) [Countable α] (e : α 
≃ β) : Countable β
· 使用定理 `instCountableForallOfFinite`：∀ {α : Sort u} {π : α → Sort w} [Finite α] 
[∀ (a : α), Countable (π a)], Countable ((a : α) → π a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem countable_univ_pi {π : α → Type*} [Finite α] {s : ∀ a, Set (π a)}
    (hs : ∀ a, (s a).Countable) : (pi univ s).Countable :=
  have := fun a ↦ (hs a).to_subtype; .of_equiv _ (Equiv.Set.univPi s).symm
/-
**Set.countable_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_pi {π : α -> Type*} [Finite α] {s : forall a, Set (π a)} (hs : f
orall a, (s a).Countable) : { f : forall a, π a | forall a, f a in s a }.Countab
le
参数：π a；hs : forall a, (s a).Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.countable_univ_pi`：countable_univ_pi {π : α -> Type*} [Finite α] {s 
: forall a, Set (π a)} (hs : forall a, (s a).Countable) : (pi univ s).Countable
-/
theorem countable_pi {π : α → Type*} [Finite α] {s : ∀ a, Set (π a)} (hs : ∀ a, (s a).Countable) :
    { f : ∀ a, π a | ∀ a, f a ∈ s a }.Countable := by
  simpa only [← mem_univ_pi] using! countable_univ_pi hs
/-
**Set.Countable.prod** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} {t : Set β}, s.Countable → t.Count
able → (s ×ˢ t).Countable
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Countable.of_equiv`：Countable.of_equiv (α : Sort*) [Countable α] (e : α 
≃ β) : Countable β
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
protected theorem Countable.prod {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable) :
    Set.Countable (s ×ˢ t) :=
  have := hs.to_subtype; have := ht.to_subtype; .of_equiv _ <| (Equiv.Set.prod _ _).symm
/-
**Set.Countable.image2** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} {s : Set α} {t : Set β},   s.Coun
table → t.Countable → ∀ (f : α → β → γ), (Set.image2 f s t).Countable
参数：f : α → β → γ；Set.image2 f s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Set.Countable.prod`：∀ {α : Type u} {β : Type v} {s : Set α} {t : Set β},
 s.Countable → t.Countable → (s ×ˢ t).Countable
-/
theorem Countable.image2 {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable)
    (f : α → β → γ) : (image2 f s t).Countable := by
  rw [← image_prod]
  exact (hs.prod ht).image _

/-- If a family of disjoint sets is included in a countable set, then only countably many of
them are nonempty. -/
/-
**Set.countable_ofPred_nonempty_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：countable_ofPred_nonempty_of_disjoint {f : β -> Set α} (hf : Pairwise (Dis
joint on f)) {s : Set α} (h'f : forall t, f t subseteq s) (hs : s.Countable) : S
et.Countable {t | (f t).Nonempty}
参数：hf : Pairwise (Disjoint on f)；h'f : forall t, f t subseteq s；hs : s.Countable
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.countable_coe_iff`：countable_coe_iff {s : Set α} : Countable s ↔ s.C
ountable
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If a family of disjoint sets is included in a countable set, then only countably
 many of
them are nonempty.
-/
theorem countable_ofPred_nonempty_of_disjoint {f : β → Set α}
    (hf : Pairwise (Disjoint on f)) {s : Set α} (h'f : ∀ t, f t ⊆ s) (hs : s.Countable) :
    Set.Countable {t | (f t).Nonempty} := by
  rw [← Set.countable_coe_iff] at hs ⊢
  have : ∀ t : {t // (f t).Nonempty}, ∃ x : s, x.1 ∈ f t := by
    rintro ⟨t, ⟨x, hx⟩⟩
    exact ⟨⟨x, (h'f t hx)⟩, hx⟩
  choose F hF using this
  have A : Injective F := by
    rintro ⟨t, ht⟩ ⟨t', ht'⟩ htt'
    have A : (f t ∩ f t').Nonempty := by
      refine ⟨F ⟨t, ht⟩, hF ⟨t, _⟩, ?_⟩
      rw [htt']
      exact hF ⟨t', _⟩
    simp only [Subtype.mk.injEq]
    by_contra H
    exact not_disjoint_iff_nonempty_inter.2 A (hf H)
  exact Injective.countable A

@[deprecated (since := "2026-07-09")]
alias countable_setOf_nonempty_of_disjoint := countable_ofPred_nonempty_of_disjoint

end Set

/-
**Finset.countable_toSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.countable_toSet (s : Finset α) : Set.Countable (↑s : Set α)
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem Finset.countable_toSet (s : Finset α) : Set.Countable (↑s : Set α) :=
  s.finite_toSet.countable
