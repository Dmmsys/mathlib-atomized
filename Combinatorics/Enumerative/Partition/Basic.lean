/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Tactic.ApplyFun

/-!
# Partitions

A partition of a natural number `n` is a way of writing `n` as a sum of positive integers, where the
order does not matter: two sums that differ only in the order of their summands are considered the
same partition. This notion is closely related to that of a composition of `n`, but in a composition
of `n` the order does matter.
A summand of the partition is called a part.

## Main functions

* `p : Partition n` is a structure, made of a multiset of integers which are all positive and
  add up to `n`.

## Implementation details

The main motivation for this structure and its API is to show Euler's partition theorem, and
related results.

The representation of a partition as a multiset is very handy as multisets are very flexible and
already have a well-developed API.

## TODO

Link this to Young diagrams.

## Tags

Partition

## References

<https://en.wikipedia.org/wiki/Partition_(number_theory)>
-/

@[expose] public section

assert_not_exists Field

open Multiset

namespace Nat

/-- A partition of `n` is a multiset of positive integers summing to `n`. -/
@[ext]
/-
**Nat.Partition** 是 Mathlib 中的一个归纳类型，位于命名空间 `Nat`。
形式化陈述：ℕ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partition of `n` is a multiset of positive integers summing to `n`.
-/
structure Partition (n : ℕ) where
  /-- positive integers summing to `n` -/
  parts : Multiset ℕ
  /-- proof that the `parts` are positive -/
  parts_pos : ∀ {i}, i ∈ parts → 0 < i
  /-- proof that the `parts` sum to `n` -/
  parts_sum : parts.sum = n
deriving DecidableEq

namespace Partition

attribute [grind →] parts_pos

@[grind →]
/-
**Nat.Partition.le_of_mem_parts** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：le_of_mem_parts {n : Nat} {p : Partition n} {m : Nat} (h : m in p.parts) :
 m <= n
参数：h : m in p.parts。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partition.parts_sum`：∀ {n : ℕ} (self : n.Partition), self.parts.sum 
= n
· 使用定理 `Multiset.le_sum_of_mem`：∀ {α : Type u_2} [inst : AddCommMonoid α] {m : M
ultiset α} {a : α},   a ∈ m → ∀ [inst_1 : Preorder α] [CanonicallyOrderedAdd α],
 a ≤ m.sum
-/
theorem le_of_mem_parts {n : ℕ} {p : Partition n} {m : ℕ} (h : m ∈ p.parts) : m ≤ n := by
  simpa [p.parts_sum] using Multiset.le_sum_of_mem h

/-- A composition induces a partition (just convert the list to a multiset). -/
@[simps]
/-
**Nat.Partition.ofComposition** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：ofComposition (n : Nat) (c : Composition n) : Partition n where parts
参数：n : Nat；c : Composition n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.blocks_pos`：∀ {n : ℕ} (self : Composition n) {i : ℕ}, i ∈ se
lf.blocks → 0 < i

--- 原说明 ---
A composition induces a partition (just convert the list to a multiset).
-/
def ofComposition (n : ℕ) (c : Composition n) : Partition n where
  parts := c.blocks
  parts_pos hi := c.blocks_pos hi
  parts_sum := by rw [Multiset.sum_coe, c.blocks_sum]
/-
**Nat.Partition.ofComposition_surj** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：ofComposition_surj {n : Nat} : Function.Surjective (ofComposition n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Nat.Partition.ext`：∀ {n : ℕ} {x y : n.Partition}, x.parts = y.parts → x 
= y
-/
theorem ofComposition_surj {n : ℕ} : Function.Surjective (ofComposition n) := by
  rintro ⟨b, hb₁, hb₂⟩
  induction b using Quotient.inductionOn with | _ b => ?_
  exact ⟨⟨b, hb₁, by simpa using hb₂⟩, Partition.ext rfl⟩

-- The argument `n` is kept explicit here since it is useful in tactic mode proofs to generate the
-- proof obligation `l.sum = n`.
/-- Given a multiset which sums to `n`, construct a partition of `n` with the same multiset, but
without the zeros.
-/
@[simps]
/-
**Nat.Partition.ofSums** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：ofSums (n : Nat) (l : Multiset Nat) (hl : l.sum = n) : Partition n where p
arts
参数：n : Nat；l : Multiset Nat；hl : l.sum = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multiset which sums to `n`, construct a partition of `n` with the same m
ultiset, but
without the zeros.
-/
def ofSums (n : ℕ) (l : Multiset ℕ) (hl : l.sum = n) : Partition n where
  parts := l.filter (· ≠ 0)
  parts_pos hi := (of_mem_filter hi).bot_lt
  parts_sum := by
    have lz : (l.filter (· = 0)).sum = 0 := by simp [sum_eq_zero_iff]
    rwa [← filter_add_not (· = 0) l, sum_add, lz, zero_add] at hl

/-- A `Multiset ℕ` induces a partition on its sum. -/
@[simps!]
/-
**Nat.Partition.ofMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：ofMultiset (l : Multiset Nat) : Partition l.sum
参数：l : Multiset Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Multiset ℕ` induces a partition on its sum.
-/
def ofMultiset (l : Multiset ℕ) : Partition l.sum := ofSums _ l rfl

/-- An element `s` of `Sym σ n` induces a partition given by its multiplicities. -/
/-
**Nat.Partition.ofSym** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：ofSym {n : Nat} {σ : Type*} (s : Sym σ n) [DecidableEq σ] : n.Partition wh
ere parts
参数：s : Sym σ n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `s` of `Sym σ n` induces a partition given by its multiplicities.
-/
def ofSym {n : ℕ} {σ : Type*} (s : Sym σ n) [DecidableEq σ] : n.Partition where
  parts := s.1.dedup.map s.1.count
  parts_pos := by simp [Multiset.count_pos]
  parts_sum := by
    change ∑ a ∈ s.1.toFinset, count a s.1 = n
    rw [toFinset_sum_count_eq]
    exact s.2

variable {n : ℕ} {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
/-
**Nat.Partition.ofSym_map** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：∀ {n : ℕ} {σ : Type u_1} {τ : Type u_2} [inst : DecidableEq σ] [inst_1 : D
ecidableEq τ] (e : σ ≃ τ) (s : Sym σ n),   Nat.Partition.ofSym (Sym.map (⇑e) s) 
= Nat.Partition.ofSym s
参数：e : σ ≃ τ；s : Sym σ n；Sym.map (⇑e) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partition.mk.injEq`：∀ {n : ℕ} (parts : Multiset ℕ) (parts_pos : ∀ {i
 : ℕ}, i ∈ parts → 0 < i) (parts_sum : parts.sum = n)   (parts_1 : Multiset ℕ) (
parts_pos_1 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.dedup_map_of_injective`：dedup_map_of_injective [DecidableEq β] 
{f : α -> β} (hf : Function.Injective f) (s : Multiset α) : (s.map f).dedup = s.
dedup.map f
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.count_map_eq_count'`：count_map_eq_count' [DecidableEq β] (f : α
 -> β) (s : Multiset α) (hf : Function.Injective f) (x : α) : (s.map f).count (f
 x) = s.count x
-/
@[simp] lemma ofSym_map (e : σ ≃ τ) (s : Sym σ n) :
    ofSym (s.map e) = ofSym s := by
  simp only [ofSym, Sym.val_eq_coe, Sym.coe_map, mk.injEq]
  rw [Multiset.dedup_map_of_injective e.injective]
  simp only [map_map, Function.comp_apply]
  congr; funext i
  rw [← Multiset.count_map_eq_count' e _ e.injective]

/-- An equivalence between `σ` and `τ` induces an equivalence between the subtypes of `Sym σ n` and
`Sym τ n` corresponding to a given partition. -/
/-
**Nat.Partition.ofSymShapeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：ofSymShapeEquiv (μ : Partition n) (e : σ ≃ τ) : {x : Sym σ n // ofSym x = 
μ} ≃ {x : Sym τ n // ofSym x = μ} where toFun
参数：μ : Partition n；e : σ ≃ τ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence between `σ` and `τ` induces an equivalence between the subtypes o
f `Sym σ n` and
`Sym τ n` corresponding to a given partition.
-/
def ofSymShapeEquiv (μ : Partition n) (e : σ ≃ τ) :
    {x : Sym σ n // ofSym x = μ} ≃ {x : Sym τ n // ofSym x = μ} where
  toFun := fun x => ⟨Sym.equivCongr e x, by simp [ofSym_map, x.2]⟩
  invFun := fun x => ⟨Sym.equivCongr e.symm x, by simp [ofSym_map, x.2]⟩
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- Convert a `Partition n` to a member of `(Finset.Icc 1 n).finsuppAntidiag n`
(see `Nat.Partition.toFinsuppAntidiag_mem_finsuppAntidiag` for the proof).
`p.toFinsuppAntidiag i` is defined as `i` times the number of occurrence of `i` in `p`. -/
/-
**Nat.Partition.toFinsuppAntidiag** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：toFinsuppAntidiag {n : Nat} (p : Partition n) : Nat ->₀ Nat where toFun m
参数：p : Partition n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a `Partition n` to a member of `(Finset.Icc 1 n).finsuppAntidiag n`
(see `Nat.Partition.toFinsuppAntidiag_mem_finsuppAntidiag` for the proof).
`p.toFinsuppAntidiag i` is defined as `i` times the number of occurrence of `i` 
in `p`.
-/
def toFinsuppAntidiag {n : ℕ} (p : Partition n) : ℕ →₀ ℕ where
  toFun m := p.parts.count m * m
  support := p.parts.toFinset
  mem_support_toFun m := by
    suffices m ∈ p.parts → m ≠ 0 by simpa
    grind
/-
**Nat.Partition.toFinsuppAntidiag_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Parti
tion`。
形式化陈述：toFinsuppAntidiag_injective (n : Nat) : Function.Injective (toFinsuppAntid
iag (n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mk.injEq`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero M] (supp
ort : Finset α) (toFun : α → M)   (mem_support_toFun : ∀ (a : α), a ∈ support ↔ 
toFun …
· 使用定理 `Nat.Partition.ext_iff`：∀ {n : ℕ} {x y : n.Partition}, x = y ↔ x.parts = 
y.parts
· 使用定理 `Multiset.ext`：ext {s t : Multiset α} : s = t ↔ forall a, count a s = cou
nt a t
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_of_mul_eq_mul_right`：∀ {n m k : ℕ}, 0 < m → n * m = k * m → n = k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem toFinsuppAntidiag_injective (n : ℕ) : Function.Injective (toFinsuppAntidiag (n := n)) := by
  unfold toFinsuppAntidiag
  intro p q h
  rw [Finsupp.mk.injEq] at h
  obtain ⟨hfinset, hcount⟩ := h
  rw [Nat.Partition.ext_iff, Multiset.ext]
  intro m
  obtain rfl | h0 := Nat.eq_zero_or_pos m
  · grind [Multiset.count_eq_zero]
  · exact Nat.eq_of_mul_eq_mul_right h0 <| funext_iff.mp hcount m
/-
**Nat.Partition.toFinsuppAntidiag_mem_finsuppAntidiag** 是 Mathlib 中的一个定理，位于命名空间 
`Nat.Partition`。
形式化陈述：toFinsuppAntidiag_mem_finsuppAntidiag {n : Nat} (p : Partition n) : p.toFi
nsuppAntidiag in (Finset.Icc 1 n).finsuppAntidiag n
参数：p : Partition n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_multiset_count`：∀ {M : Type u_4} [inst : AddCommMonoid M] [in
st_1 : DecidableEq M] (s : Multiset M),   s.sum = ∑ m ∈ s.toFinset, Multiset.cou
nt m s • m
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Partition.parts_sum`：∀ {n : ℕ} (self : n.Partition), self.parts.sum 
= n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem toFinsuppAntidiag_mem_finsuppAntidiag {n : ℕ} (p : Partition n) :
    p.toFinsuppAntidiag ∈ (Finset.Icc 1 n).finsuppAntidiag n := by
  have hp : p.parts.toFinset ⊆ Finset.Icc 1 n := by
    grind
  suffices ∑ m ∈ Finset.Icc 1 n, Multiset.count m p.parts * m = n by simpa [toFinsuppAntidiag, hp]
  convert! ← p.parts_sum
  rw [Finset.sum_multiset_count]
  apply Finset.sum_subset hp
  suffices ∀ (x : ℕ), 1 ≤ x → x ≤ n → x ∉ p.parts → x ∉ p.parts ∨ x = 0 by simpa
  grind

/-- The partition of exactly one part. -/
/-
**Nat.Partition.indiscrete** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：indiscrete (n : Nat) : Partition n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partition of exactly one part.
-/
def indiscrete (n : ℕ) : Partition n := ofSums n {n} rfl
/-
**Nat.Partition.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : Inhabited (Partition n) := ⟨indiscrete n⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.Partition.indiscrete_parts** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → (Nat.Partition.indiscrete n).parts = {n}
参数：Nat.Partition.indiscrete n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Partition.ofSums_parts`：∀ (n : ℕ) (l : Multiset ℕ) (hl : l.sum = n),
 (Nat.Partition.ofSums n l hl).parts = Multiset.filter (fun x => x ≠ 0) l
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma indiscrete_parts {n : ℕ} (hn : n ≠ 0) : (indiscrete n).parts = {n} := by
  simp [indiscrete, filter_eq_self, hn]
/-
**Nat.Partition.partition_zero_parts** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：∀ (p : Nat.Partition 0), p.parts = 0
参数：p : Nat.Partition 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Partition.parts_pos`：∀ {n : ℕ} (self : n.Partition) {i : ℕ}, i ∈ sel
f.parts → 0 < i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.sum_eq_zero_iff`：∀ {α : Type u_2} [inst : AddCommMonoid α] {m :
 Multiset α} [inst_1 : PartialOrder α] [CanonicallyOrderedAdd α]   [IsOrderedAdd
Monoid α], m.s…
· 使用定理 `Nat.Partition.parts_sum`：∀ {n : ℕ} (self : n.Partition), self.parts.sum 
= n
-/
@[simp] lemma partition_zero_parts (p : Partition 0) : p.parts = 0 :=
  eq_zero_of_forall_notMem fun _ h => (p.parts_pos h).ne' <| sum_eq_zero_iff.1 p.parts_sum _ h
/-
**Nat.Partition.UniquePartitionZero** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Partition`。
形式化陈述：UniquePartitionZero : Unique (Partition 0) where uniq _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance UniquePartitionZero : Unique (Partition 0) where
  uniq _ := Partition.ext <| by simp
/-
**Nat.Partition.partition_one_parts** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：∀ (p : Nat.Partition 1), p.parts = {1}
参数：p : Nat.Partition 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.eq_replicate_card`：eq_replicate_card {a : α} {s : Multiset α} :
 s = replicate (card s) a ↔ forall b in s, b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Multiset.le_sum_of_mem`：∀ {α : Type u_2} [inst : AddCommMonoid α] {m : M
ultiset α} {a : α},   a ∈ m → ∀ [inst_1 : Preorder α] [CanonicallyOrderedAdd α],
 a ≤ m.sum
· 使用定理 `Nat.Partition.parts_sum`：∀ {n : ℕ} (self : n.Partition), self.parts.sum 
= n
· 使用定理 `Nat.Partition.parts_pos`：∀ {n : ℕ} (self : n.Partition) {i : ℕ}, i ∈ sel
f.parts → 0 < i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.replicate_one`：replicate_one (a : α) : replicate 1 a = {a}
-/
@[simp] lemma partition_one_parts (p : Partition 1) : p.parts = {1} := by
  have h : p.parts = replicate (card p.parts) 1 := eq_replicate_card.2 fun x hx =>
    ((le_sum_of_mem hx).trans_eq p.parts_sum).antisymm (p.parts_pos hx)
  have h' : card p.parts = 1 := by simpa using (congrArg sum h.symm).trans p.parts_sum
  rw [h, h', replicate_one]
/-
**Nat.Partition.UniquePartitionOne** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Partition`。
形式化陈述：UniquePartitionOne : Unique (Partition 1) where uniq _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance UniquePartitionOne : Unique (Partition 1) where
  uniq _ := Partition.ext <| by simp
/-
**Nat.Partition.ofSym_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：∀ {σ : Type u_1} [inst : DecidableEq σ] (s : Sym σ 1), Nat.Partition.ofSym
 s = Nat.Partition.indiscrete 1
参数：s : Sym σ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Partition.ext`：∀ {n : ℕ} {x y : n.Partition}, x.parts = y.parts → x 
= y
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `Nat.Partition.partition_one_parts`：∀ (p : Nat.Partition 1), p.parts = {1
}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma ofSym_one (s : Sym σ 1) : ofSym s = indiscrete 1 := by
  ext; simp

/-- The number of times a positive integer `i` appears in the partition `ofSums n l hl` is the same
as the number of times it appears in the multiset `l`.
(For `i = 0`, `Partition.non_zero` combined with `Multiset.count_eq_zero_of_notMem` gives that
this is `0` instead.)
-/
/-
**Nat.Partition.count_ofSums_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition
`。
形式化陈述：count_ofSums_of_ne_zero {n : Nat} {l : Multiset Nat} (hl : l.sum = n) {i :
 Nat} (hi : i != 0) : (ofSums n l hl).parts.count i = l.count i
参数：hl : l.sum = n；hi : i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.count_filter_of_pos`：count_filter_of_pos {p} [DecidablePred p] 
{a} {s : Multiset α} (h : p a) : count a (filter p s) = count a s

--- 原说明 ---
The number of times a positive integer `i` appears in the partition `ofSums n l 
hl` is the same
as the number of times it appears in the multiset `l`.
(For `i = 0`, `Partition.non_zero` combined with `Multiset.count_eq_zero_of_notM
em` gives that
this is `0` instead.)
-/
theorem count_ofSums_of_ne_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
    (ofSums n l hl).parts.count i = l.count i :=
  count_filter_of_pos hi
/-
**Nat.Partition.count_ofSums_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：count_ofSums_zero {n : Nat} {l : Multiset Nat} (hl : l.sum = n) : (ofSums 
n l hl).parts.count 0 = 0
参数：hl : l.sum = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.count_filter_of_neg`：count_filter_of_neg {p} [DecidablePred p] 
{a} {s : Multiset α} (h : ¬p a) : count a (filter p s) = 0
-/
theorem count_ofSums_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) :
    (ofSums n l hl).parts.count 0 = 0 :=
  count_filter_of_neg fun h => h rfl

/-- Show there are finitely many partitions by considering the surjection from compositions to
partitions.
-/
/-
**Nat.Partition.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show there are finitely many partitions by considering the surjection from compo
sitions to
partitions.
-/
instance (n : ℕ) : Fintype (Partition n) :=
  Fintype.ofSurjective (ofComposition n) ofComposition_surj

/-- The finset of those partitions in which every part satisfies a certain condition. -/
/-
**Nat.Partition.restricted** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：restricted (n : Nat) (p : Nat -> Prop) [DecidablePred p] : Finset n.Partit
ion
参数：n : Nat；p : Nat -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of those partitions in which every part satisfies a certain condition
.
-/
def restricted (n : ℕ) (p : ℕ → Prop) [DecidablePred p] : Finset n.Partition :=
  Finset.univ.filter fun x ↦ ∀ i ∈ x.parts, p i

/-- The finset of those partitions in which every part is used less than `m` times. -/
/-
**Nat.Partition.countRestricted** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：countRestricted (n : Nat) (m : Nat) : Finset n.Partition
参数：n : Nat；m : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of those partitions in which every part is used less than `m` times.
-/
def countRestricted (n : ℕ) (m : ℕ) : Finset n.Partition :=
  Finset.univ.filter fun x ↦ ∀ i ∈ x.parts, x.parts.count i < m

/-- The finset of those partitions in which every part is odd. -/
/-
**Nat.Partition.odds** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：odds (n : Nat) : Finset n.Partition
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of those partitions in which every part is odd.
-/
def odds (n : ℕ) : Finset n.Partition := restricted n (¬ Even ·)

/-- The finset of those partitions in which each part is used at most once. -/
/-
**Nat.Partition.distincts** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：distincts (n : Nat) : Finset n.Partition
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of those partitions in which each part is used at most once.
-/
def distincts (n : ℕ) : Finset n.Partition :=
  Finset.univ.filter fun c => c.parts.Nodup
/-
**Nat.Partition.countRestricted_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Partition`。
形式化陈述：countRestricted_two (n : Nat) : countRestricted n 2 = distincts n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.nodup_iff_count_le_one`：nodup_iff_count_le_one [DecidableEq α] 
{s : Multiset α} : Nodup s ↔ forall a, count a s <= 1
-/
theorem countRestricted_two (n : ℕ) : countRestricted n 2 = distincts n := by
  congrm Finset.univ.filter fun x ↦ ?_
  rw [Multiset.nodup_iff_count_le_one]
  grind [Multiset.count_eq_zero]

/-- The finset of those partitions in which every part is odd and used at most once. -/
/-
**Nat.Partition.oddDistincts** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`。
形式化陈述：oddDistincts (n : Nat) : Finset n.Partition
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finset of those partitions in which every part is odd and used at most once.
-/
def oddDistincts (n : ℕ) : Finset n.Partition :=
  odds n ∩ distincts n

/-- If `1 ≤ a` and `a ≤ n`, partitions of `n` containing `a` as a part are equivalent to
partitions of `n - a`. The forward map removes one occurrence of `a`, and the inverse adds `a` as
a part. -/
/-
**Nat.Partition.partitionWithPartEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Partition`
。
形式化陈述：partitionWithPartEquiv {n a : Nat} (ha1 : 1 <= a) (ha : a <= n) : {p : n.P
artition // a in p.parts} ≃ (n - a).Partition where toFun p
参数：ha1 : 1 <= a；ha : a <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `1 ≤ a` and `a ≤ n`, partitions of `n` containing `a` as a part are equivalen
t to
partitions of `n - a`. The forward map removes one occurrence of `a`, and the in
verse adds `a` as
a part.
-/
def partitionWithPartEquiv {n a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ n) :
    {p : n.Partition // a ∈ p.parts} ≃ (n - a).Partition where
  toFun p := by
    refine ⟨p.1.parts.erase a, ?_, ?_⟩
    · intro _ hi
      exact p.1.parts_pos (p.1.parts.erase_subset a hi)
    · have hs : a + (p.1.parts.erase a).sum = n := by
        simpa [p.1.parts_sum] using congrArg Multiset.sum (Multiset.cons_erase p.2)
      lia
  invFun q := ⟨⟨a ::ₘ q.parts, by grind, by simp [q.parts_sum, ha]⟩, by simp⟩
  left_inv p := Subtype.ext <| Partition.ext <| cons_erase p.property
  right_inv q := Partition.ext <| erase_cons_head a q.parts

@[simp]
/-
**Nat.Partition.partitionWithPartEquiv_apply_parts** 是 Mathlib 中的一个定理，位于命名空间 `Na
t.Partition`。
形式化陈述：partitionWithPartEquiv_apply_parts {n a : Nat} (ha1 : 1 <= a) (ha : a <= n
) (p : {p : n.Partition // a in p.parts}) : (partitionWithPartEquiv ha1 ha p).pa
rts = p.1.parts.erase a
参数：ha1 : 1 <= a；ha : a <= n；p : {p : n.Partition // a in p.parts}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem partitionWithPartEquiv_apply_parts {n a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ n)
    (p : {p : n.Partition // a ∈ p.parts}) :
    (partitionWithPartEquiv ha1 ha p).parts = p.1.parts.erase a := by
  dsimp [partitionWithPartEquiv]

@[simp]
/-
**Nat.Partition.partitionWithPartEquiv_symm_apply_parts** 是 Mathlib 中的一个定理，位于命名空
间 `Nat.Partition`。
形式化陈述：partitionWithPartEquiv_symm_apply_parts {n a : Nat} (ha1 : 1 <= a) (ha : a
 <= n) (p : (n - a).Partition) : ((partitionWithPartEquiv ha1 ha).symm p).1.part
s = a ::ₘ p.parts
参数：ha1 : 1 <= a；ha : a <= n；p : (n - a).Partition。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem partitionWithPartEquiv_symm_apply_parts {n a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ n)
    (p : (n - a).Partition) : ((partitionWithPartEquiv ha1 ha).symm p).1.parts = a ::ₘ p.parts := by
  dsimp [partitionWithPartEquiv]

end Partition

end Nat

