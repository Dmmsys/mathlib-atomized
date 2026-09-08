/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma, Wojciech Nawrocki
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# Jacobson radical

The Jacobson radical of a ring `R` is defined to be the intersection of all maximal ideals of `R`.
This is similar to how the nilradical is equal to the intersection of all prime ideals of `R`.

We can extend the idea of the nilradical of `R` to ideals of `R`,
by letting the nilradical of an ideal `I` be the intersection of prime ideals containing `I`.
Under this extension, the original nilradical is the radical of the zero ideal `⊥`.
Here we define the Jacobson radical of an ideal `I` in a similar way,
as the intersection of maximal ideals containing `I`.

## Main definitions

Let `R` be a ring, and `I` be a left ideal of `R`

* `Ideal.jacobson I` is the Jacobson radical, i.e. the infimum of all maximal ideals containing `I`.

* `Ideal.IsLocal I` is the proposition that the Jacobson radical of `I` is itself a maximal ideal

Furthermore when `I` is a two-sided ideal of `R`

* `TwoSidedIdeal.jacobson I` is the Jacobson radical as a two-sided ideal

## Main statements

* `mem_jacobson_iff` gives a characterization of members of the Jacobson of I

* `Ideal.isLocal_of_isMaximal_radical`: if the radical of I is maximal then so is the Jacobson
  radical

## Tags

Jacobson, Jacobson radical, Local Ideal

-/

@[expose] public section


universe u v

namespace Ideal

variable {R : Type u} {S : Type v}

section Jacobson

section Ring

variable [Ring R] [Ring S] {I : Ideal R}

/-- The Jacobson radical of `I` is the infimum of all maximal (left) ideals containing `I`. -/
/-
**Ideal.jacobson** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：jacobson (I : Ideal R) : Ideal R
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Jacobson radical of `I` is the infimum of all maximal (left) ideals containi
ng `I`.
-/
def jacobson (I : Ideal R) : Ideal R :=
  sInf { J : Ideal R | I ≤ J ∧ IsMaximal J }
/-
**Ideal.le_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_jacobson : I <= jacobson I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem le_jacobson : I ≤ jacobson I := fun _ hx => mem_sInf.mpr fun _ hJ => hJ.left hx

@[simp]
/-
**Ideal.jacobson_idem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：jacobson_idem : jacobson (jacobson I) = jacobson I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.le_jacobson`：le_jacobson : I <= jacobson I
-/
theorem jacobson_idem : jacobson (jacobson I) = jacobson I :=
  le_antisymm (sInf_le_sInf fun _ hJ => ⟨sInf_le hJ, hJ.2⟩) le_jacobson

@[simp]
/-
**Ideal.jacobson_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：jacobson_top : jacobson (⊤ : Ideal R) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Ideal.le_jacobson`：le_jacobson : I <= jacobson I
-/
theorem jacobson_top : jacobson (⊤ : Ideal R) = ⊤ :=
  eq_top_iff.2 le_jacobson
/-
**Ideal.jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：jacobson_bot : jacobson (⊥ : Ideal R) = Ring.jacobson R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem jacobson_bot : jacobson (⊥ : Ideal R) = Ring.jacobson R := by
  simp_rw [jacobson, Ring.jacobson, Module.jacobson, bot_le, true_and, isMaximal_def]

@[simp]
/-
**Ideal.jacobson_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：jacobson_eq_top_iff : jacobson I = ⊤ ↔ I = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
-/
theorem jacobson_eq_top_iff : jacobson I = ⊤ ↔ I = ⊤ :=
  ⟨fun H =>
    by_contradiction fun hi => let ⟨M, hm, him⟩ := exists_le_maximal I hi
      lt_top_iff_ne_top.1
        (lt_of_le_of_lt (show jacobson I ≤ M from sInf_le ⟨him, hm⟩) <|
          lt_top_iff_ne_top.2 hm.ne_top) H,
    fun H => eq_top_iff.2 <| le_sInf fun _ ⟨hij, _⟩ => H ▸ hij⟩
/-
**Ideal.jacobson_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：jacobson_eq_bot : jacobson I = ⊥ -> I = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Ideal.le_jacobson`：le_jacobson : I <= jacobson I
-/
theorem jacobson_eq_bot : jacobson I = ⊥ → I = ⊥ := fun h => eq_bot_iff.mpr (h ▸ le_jacobson)
/-
**Ideal.jacobson_eq_self_of_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：jacobson_eq_self_of_isMaximal [H : IsMaximal I] : I.jacobson = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.le_jacobson`：le_jacobson : I <= jacobson I
-/
theorem jacobson_eq_self_of_isMaximal [H : IsMaximal I] : I.jacobson = I :=
  le_antisymm (sInf_le ⟨le_of_eq rfl, H⟩) le_jacobson
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) jacobson.isMaximal [H : IsMaximal I] : IsMaximal (jacobson I) :=
  ⟨⟨fun htop => H.1.1 (jacobson_eq_top_iff.1 htop), fun _ hJ =>
    H.1.2 _ (lt_of_le_of_lt le_jacobson hJ)⟩⟩
/-
**Ideal.mem_jacobson_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_jacobson_iff {x : R} : x in jacobson I ↔ forall y, exists z, z * y * x
 + z - 1 in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Ideal.mem_span_singleton'`：mem_span_singleton' {x y : α} : x in span ({y
} : Set α) ↔ exists a, a * y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Ideal.IsMaximal.exists_inv`：∀ {α : Type u} [inst : Semiring α] {I : Idea
l α}, I.IsMaximal → ∀ {x : α}, x ∉ I → ∃ y, ∃ i ∈ I, y * x + i = 1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
（共 32 条，此处仅展示前 30 条）
-/
theorem mem_jacobson_iff {x : R} : x ∈ jacobson I ↔ ∀ y, ∃ z, z * y * x + z - 1 ∈ I :=
  ⟨fun hx y =>
    by_cases
      (fun hxy : I ⊔ span {y * x + 1} = ⊤ =>
        let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy)
        let ⟨r, hr⟩ := mem_span_singleton'.1 hq
        ⟨r, by
          rw [mul_assoc, ← mul_add_one, hr, ← hpq, ← neg_sub, add_sub_cancel_right]
          exact I.neg_mem hpi⟩)
      fun hxy : I ⊔ span {y * x + 1} ≠ ⊤ => let ⟨M, hm1, hm2⟩ := exists_le_maximal _ hxy
      suffices x ∉ M from (this <| mem_sInf.1 hx ⟨le_trans le_sup_left hm2, hm1⟩).elim
      fun hxm => hm1.1.1 <| (eq_top_iff_one _).2 <| add_sub_cancel_left (y * x) 1 ▸
        M.sub_mem (le_sup_right.trans hm2 <| subset_span rfl) (M.mul_mem_left _ hxm),
    fun hx => mem_sInf.2 fun M ⟨him, hm⟩ => by_contradiction fun hxm =>
      let ⟨y, i, hi, df⟩ := hm.exists_inv hxm
      let ⟨z, hz⟩ := hx (-y)
      hm.1.1 <| (eq_top_iff_one _).2 <| sub_sub_cancel (z * -y * x + z) 1 ▸
        M.sub_mem (by
          rw [mul_assoc, ← mul_add_one, neg_mul, ← sub_eq_iff_eq_add.mpr df.symm, neg_sub,
            sub_add_cancel]
          exact M.mul_mem_left _ hi) <| him hz⟩
/-
**Ideal.exists_mul_add_sub_mem_of_mem_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`
。
形式化陈述：exists_mul_add_sub_mem_of_mem_jacobson {I : Ideal R} (r : R) (h : r in jac
obson I) : exists s, s * (r + 1) - 1 in I
参数：r : R；h : r in jacobson I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_jacobson_iff`：mem_jacobson_iff {x : R} : x in jacobson I ↔ for
all y, exists z, z * y * x + z - 1 in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem exists_mul_add_sub_mem_of_mem_jacobson {I : Ideal R} (r : R) (h : r ∈ jacobson I) :
    ∃ s, s * (r + 1) - 1 ∈ I := by
  obtain ⟨s, hs⟩ := mem_jacobson_iff.1 h 1
  use s
  rw [mul_add, mul_one]
  simpa using hs
/-
**Ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal`。
形式化陈述：exists_mul_sub_mem_of_sub_one_mem_jacobson {I : Ideal R} (r : R) (h : r - 
1 in jacobson I) : exists s, s * r - 1 in I
参数：r : R；h : r - 1 in jacobson I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.exists_mul_add_sub_mem_of_mem_jacobson`：exists_mul_add_sub_mem_of_
mem_jacobson {I : Ideal R} (r : R) (h : r in jacobson I) : exists s, s * (r + 1)
 - 1 in I
-/
theorem exists_mul_sub_mem_of_sub_one_mem_jacobson {I : Ideal R} (r : R) (h : r - 1 ∈ jacobson I) :
    ∃ s, s * r - 1 ∈ I := by
  convert! exists_mul_add_sub_mem_of_mem_jacobson _ h
  simp

/-- An ideal equals its Jacobson radical iff it is the intersection of a set of maximal ideals.
Allowing the set to include ⊤ is equivalent, and is included only to simplify some proofs. -/
/-
**Ideal.eq_jacobson_iff_sInf_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_jacobson_iff_sInf_maximal : I.jacobson = I ↔ exists M : Set (Ideal R), 
(forall J in M, IsMaximal J ∨ J = ⊤) ∧ I = sInf M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_sInf_iff`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set
 α} {a : α}, a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Ideal.le_jacobson`：le_jacobson : I <= jacobson I

--- 原说明 ---
An ideal equals its Jacobson radical iff it is the intersection of a set of maxi
mal ideals.
Allowing the set to include ⊤ is equivalent, and is included only to simplify so
me proofs.
-/
theorem eq_jacobson_iff_sInf_maximal :
    I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀ J ∈ M, IsMaximal J ∨ J = ⊤) ∧ I = sInf M := by
  use fun hI => ⟨{ J : Ideal R | I ≤ J ∧ J.IsMaximal }, ⟨fun _ hJ => Or.inl hJ.right, hI.symm⟩⟩
  rintro ⟨M, hM, hInf⟩
  refine le_antisymm (fun x hx => ?_) le_jacobson
  rw [hInf, mem_sInf]
  intro I hI
  rcases hM I hI with is_max | is_top
  · exact (mem_sInf.1 hx) ⟨le_sInf_iff.1 (le_of_eq hInf) I hI, is_max⟩
  · exact is_top.symm ▸ Submodule.mem_top
/-
**Ideal.eq_jacobson_iff_sInf_maximal'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_jacobson_iff_sInf_maximal' : I.jacobson = I ↔ exists M : Set (Ideal R),
 (forall J in M, forall (K : Ideal R), J < K -> K = ⊤) ∧ I = sInf M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Ideal.eq_jacobson_iff_sInf_maximal`：eq_jacobson_iff_sInf_maximal : I.jac
obson = I ↔ exists M : Set (Ideal R), (forall J in M, IsMaximal J ∨ J = ⊤) ∧ I =
 sInf M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
-/
theorem eq_jacobson_iff_sInf_maximal' :
    I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀ J ∈ M, ∀ (K : Ideal R), J < K → K = ⊤) ∧ I = sInf M :=
  eq_jacobson_iff_sInf_maximal.trans
    ⟨fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ K hK =>
          Or.recOn (hM.1 J hJ) (fun h => h.1.2 K hK) fun h => eq_top_iff.2 (le_of_lt (h ▸ hK)),
          hM.2⟩⟩,
      fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ =>
          Or.recOn (Classical.em (J = ⊤)) (fun h => Or.inr h) fun h => Or.inl ⟨⟨h, hM.1 J hJ⟩⟩,
          hM.2⟩⟩⟩

/-- An ideal `I` equals its Jacobson radical if and only if every element outside `I`
also lies outside of a maximal ideal containing `I`. -/
/-
**Ideal.eq_jacobson_iff_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_jacobson_iff_notMem : I.jacobson = I ↔ forall x ∉ I, exists M : Ideal R
, (I <= M ∧ M.IsMaximal) ∧ x ∉ M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Ideal.jacobson.eq_1`：∀ {R : Type u} [inst : Ring R] (I : Ideal R), I.jac
obson = sInf {J | I ≤ J ∧ J.IsMaximal}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Ideal.le_jacobson`：le_jacobson : I <= jacobson I

--- 原说明 ---
An ideal `I` equals its Jacobson radical if and only if every element outside `I
`
also lies outside of a maximal ideal containing `I`.
-/
theorem eq_jacobson_iff_notMem :
    I.jacobson = I ↔ ∀ x ∉ I, ∃ M : Ideal R, (I ≤ M ∧ M.IsMaximal) ∧ x ∉ M := by
  constructor
  · intro h x hx
    rw [← h, Ideal.jacobson, mem_sInf] at hx
    push Not at hx
    exact hx
  · refine fun h => le_antisymm (fun x hx => ?_) le_jacobson
    contrapose hx
    rw [Ideal.jacobson, mem_sInf]
    push Not
    exact h x hx
/-
**Ideal.map_jacobson_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_jacobson_of_surjective {f : R ->+* S} (hf : Function.Surjective f) : R
ingHom.ker f <= I -> map f I.jacobson = (map f I).jacobson
参数：hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.map_sInf`：map_sInf {A : Set (Ideal R)} {f : F} (hf : Function.Surj
ective f) : (forall J in A, RingHom.ker f <= J) -> map f (sInf A) = sInf (map f 
'' A…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Ideal.le_comap_of_map_le`：le_comap_of_map_le : I.map f <= K -> I <= K.co
map f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.comap_isMaximal_of_surjective`：comap_isMaximal_of_surjective (hf :
 Function.Surjective f) {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K)
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用定理 `sInf_le_sInf_of_subset_insert_top`：∀ {α : Type u_1} [inst : CompleteLatt
ice α] {s t : Set α}, s ⊆ insert ⊤ t → sInf t ≤ sInf s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_eq_top_or_isMaximal_of_surjective`：map_eq_top_or_isMaximal_of_
surjective (hf : Function.Surjective f) {I : Ideal R} (H : IsMaximal I) : map f 
I = ⊤ ∨ IsMaximal (map f I)
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
-/
theorem map_jacobson_of_surjective {f : R →+* S} (hf : Function.Surjective f) :
    RingHom.ker f ≤ I → map f I.jacobson = (map f I).jacobson := by
  intro h
  unfold Ideal.jacobson
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): dot notation for `RingHom.ker` does not work
  have : ∀ J ∈ { J : Ideal R | I ≤ J ∧ J.IsMaximal }, RingHom.ker f ≤ J :=
    fun J hJ => le_trans h hJ.left
  refine Trans.trans (map_sInf hf this) (le_antisymm ?_ ?_)
  · refine
      sInf_le_sInf fun J hJ =>
        ⟨comap f J, ⟨⟨le_comap_of_map_le hJ.1, ?_⟩, map_comap_of_surjective f hf J⟩⟩
    have : J.IsMaximal := hJ.right
    exact comap_isMaximal_of_surjective f hf
  · refine sInf_le_sInf_of_subset_insert_top fun j hj => hj.recOn fun J hJ => ?_
    rw [← hJ.2]
    rcases map_eq_top_or_isMaximal_of_surjective f hf hJ.left.right with htop | hmax
    · exact htop.symm ▸ Set.mem_insert ⊤ _
    · exact Set.mem_insert_of_mem ⊤ ⟨map_mono hJ.1.1, hmax⟩
/-
**Ideal.map_jacobson_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_jacobson_of_bijective {f : R ->+* S} (hf : Function.Bijective f) : map
 f I.jacobson = (map f I).jacobson
参数：hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_jacobson_of_surjective`：map_jacobson_of_surjective {f : R ->+*
 S} (hf : Function.Surjective f) : RingHom.ker f <= I -> map f I.jacobson = (map
 f I).jacobson
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem map_jacobson_of_bijective {f : R →+* S} (hf : Function.Bijective f) :
    map f I.jacobson = (map f I).jacobson :=
  map_jacobson_of_surjective hf.right
    (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot f).1 hf.left)) bot_le)
/-
**Ideal.comap_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_jacobson {f : R ->+* S} {K : Ideal S} : comap f K.jacobson = sInf (c
omap f '' { J : Ideal S | K <= J ∧ J.IsMaximal })
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_sInf'`：comap_sInf' (s : Set (Ideal S)) : (sInf s).comap f = 
⨅ I in comap f '' s, I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
-/
theorem comap_jacobson {f : R →+* S} {K : Ideal S} :
    comap f K.jacobson = sInf (comap f '' { J : Ideal S | K ≤ J ∧ J.IsMaximal }) :=
  Trans.trans (comap_sInf' f _) sInf_eq_iInf.symm
/-
**Ideal.comap_jacobson_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_jacobson_of_surjective {f : R ->+* S} (hf : Function.Surjective f) {
K : Ideal S} : comap f K.jacobson = (comap f K).jacobson
参数：hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `sInf_insert`：∀ {α : Type u_1} [inst : CompleteLattice α] {a : α} {s : Se
t α}, sInf (insert a s) = a ⊓ sInf s
· 使用定理 `Ideal.comap_sInf'`：comap_sInf' (s : Set (Ideal S)) : (sInf s).comap f = 
⨅ I in comap f '' s, I
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用定理 `iInf_le_iInf_of_subset`：∀ {α : Type u_1} {β : Type u_2} [inst : Complete
Lattice α] {f : β → α} {s t : Set β},   s ⊆ t → ⨅ x ∈ t, f x ≤ ⨅ x ∈ s, f x
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Ideal.map_eq_top_or_isMaximal_of_surjective`：map_eq_top_or_isMaximal_of_
surjective (hf : Function.Surjective f) {I : Ideal R} (H : IsMaximal I) : map f 
I = ⊤ ∨ IsMaximal (map f I)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Ideal.le_map_of_comap_le_of_surjective`：le_map_of_comap_le_of_surjective
 : comap f K <= I -> K <= map f I
· 使用定理 `Ideal.comap_sInf`：comap_sInf (s : Set (Ideal S)) : (sInf s).comap f = ⨅ 
I in s, (I : Ideal S).comap f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Ideal.comap_isMaximal_of_surjective`：comap_isMaximal_of_surjective (hf :
 Function.Surjective f) {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K)
-/
theorem comap_jacobson_of_surjective {f : R →+* S} (hf : Function.Surjective f) {K : Ideal S} :
    comap f K.jacobson = (comap f K).jacobson := by
  unfold Ideal.jacobson
  refine le_antisymm ?_ ?_
  · rw [← top_inf_eq (sInf _), ← sInf_insert, comap_sInf', sInf_eq_iInf]
    refine iInf_le_iInf_of_subset fun J hJ => ?_
    have : comap f (map f J) = J :=
      Trans.trans (comap_map_of_surjective f hf J)
        (le_antisymm (sup_le_iff.2 ⟨le_of_eq rfl, le_trans (comap_mono bot_le) hJ.left⟩)
          le_sup_left)
    rcases map_eq_top_or_isMaximal_of_surjective _ hf hJ.right with htop | hmax
    · exact ⟨⊤, Set.mem_insert ⊤ _, htop ▸ this⟩
    · exact ⟨map f J, Set.mem_insert_of_mem _ ⟨le_map_of_comap_le_of_surjective f hf hJ.1, hmax⟩,
        this⟩
  · simp_rw [comap_sInf, le_iInf_iff]
    intro J hJ
    have : J.IsMaximal := hJ.right
    exact sInf_le ⟨comap_mono hJ.left, comap_isMaximal_of_surjective _ hf⟩

@[gcongr, mono]
/-
**Ideal.jacobson_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：jacobson_mono {I J : Ideal R} : I <= J -> I.jacobson <= J.jacobson
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.jacobson.eq_1`：∀ {R : Type u} [inst : Ring R] (I : Ideal R), I.jac
obson = sInf {J | I ≤ J ∧ J.IsMaximal}
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
-/
theorem jacobson_mono {I J : Ideal R} : I ≤ J → I.jacobson ≤ J.jacobson := by
  intro h x hx
  rw [jacobson, mem_sInf] at hx ⊢
  exact fun K ⟨hK, hK_max⟩ => hx ⟨Trans.trans h hK, hK_max⟩
/-
**Ideal.ringJacobson_le_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ringJacobson_le_jacobson {I : Ideal R} : Ring.jacobson R <= I.jacobson
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.jacobson_bot`：jacobson_bot : jacobson (⊥ : Ideal R) = Ring.jacobso
n R
· 使用定理 `Ideal.jacobson_mono`：jacobson_mono {I J : Ideal R} : I <= J -> I.jacobso
n <= J.jacobson
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem ringJacobson_le_jacobson {I : Ideal R} : Ring.jacobson R ≤ I.jacobson :=
  jacobson_bot.symm.trans_le (jacobson_mono bot_le)

/-- The Jacobson radical of a two-sided ideal is two-sided. -/
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Jacobson radical of a two-sided ideal is two-sided.
-/
instance {I : Ideal R} [I.IsTwoSided] : I.jacobson.IsTwoSided where
  -- Proof generalized from
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-definition-and-basic-results/
  mul_mem_of_left {x} r xJ := by
    apply mem_sInf.mpr
    intro 𝔪 𝔪_mem
    by_cases r𝔪 : r ∈ 𝔪
    · apply 𝔪.smul_mem _ r𝔪
    -- 𝔪₀ := { a : R | a*r ∈ 𝔪 }
    let 𝔪₀ : Ideal R := Submodule.comap (DistribSMul.toLinearMap R (S := Rᵐᵒᵖ) R (.op r)) 𝔪
    suffices x ∈ 𝔪₀ by simpa [𝔪₀] using this
    have I𝔪₀ : I ≤ 𝔪₀ := fun i iI =>
      𝔪_mem.left (I.mul_mem_right _ iI)
    have 𝔪₀_maximal : IsMaximal 𝔪₀ := by
      refine isMaximal_iff.mpr ⟨
        fun h => r𝔪 (by simpa [𝔪₀] using h),
        fun J b 𝔪₀J b𝔪₀ bJ => ?_⟩
      let K : Ideal R := Ideal.span {b*r} ⊔ 𝔪
      have ⟨s, y, y𝔪, sbyr⟩ :=
        mem_span_singleton_sup.mp <|
          mul_mem_left _ r <|
            (isMaximal_iff.mp 𝔪_mem.right).right K (b * r)
            le_sup_right b𝔪₀
            (mem_sup_left <| mem_span_singleton_self _)
      have : 1 - s * b ∈ 𝔪₀ := by
        rw [mul_one, add_comm, ← eq_sub_iff_add_eq] at sbyr
        rw [sbyr, ← mul_assoc] at y𝔪
        simp [𝔪₀, sub_mul, y𝔪]
      have : 1 - s * b + s * b ∈ J := by
        apply add_mem (𝔪₀J this) (J.mul_mem_left _ bJ)
      simpa using this
    exact mem_sInf.mp xJ ⟨I𝔪₀, 𝔪₀_maximal⟩

end Ring

section CommRing

variable [CommRing R] [CommRing S] {I : Ideal R}

/-
**Ideal.radical_le_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：radical_le_jacobson : radical I <= jacobson I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
-/
theorem radical_le_jacobson : radical I ≤ jacobson I :=
  le_sInf fun _ hJ => (radical_eq_sInf I).symm ▸ sInf_le ⟨hJ.left, IsMaximal.isPrime hJ.right⟩
/-
**Ideal.isRadical_of_eq_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isRadical_of_eq_jacobson (h : jacobson I = I) : I.IsRadical
参数：h : jacobson I = I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.radical_le_jacobson`：radical_le_jacobson : radical I <= jacobson I
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem isRadical_of_eq_jacobson (h : jacobson I = I) : I.IsRadical :=
  radical_le_jacobson.trans h.le
/-
**Ideal.isRadical_jacobson** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：isRadical_jacobson (I : Ideal R) : I.jacobson.IsRadical
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isRadical_of_eq_jacobson`：isRadical_of_eq_jacobson (h : jacobson I
 = I) : I.IsRadical
· 使用定理 `Ideal.jacobson_idem`：jacobson_idem : jacobson (jacobson I) = jacobson I
-/
lemma isRadical_jacobson (I : Ideal R) : I.jacobson.IsRadical :=
  isRadical_of_eq_jacobson jacobson_idem
/-
**Ideal.isUnit_of_sub_one_mem_jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isUnit_of_sub_one_mem_jacobson_bot (r : R) (h : r - 1 in jacobson (⊥ : Ide
al R)) : IsUnit r
参数：r : R；h : r - 1 in jacobson (⊥ : Ideal R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson`：exists_mul_sub_mem_of_
sub_one_mem_jacobson {I : Ideal R} (r : R) (h : r - 1 in jacobson I) : exists s,
 s * r - 1 in I
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
-/
theorem isUnit_of_sub_one_mem_jacobson_bot (r : R) (h : r - 1 ∈ jacobson (⊥ : Ideal R)) :
    IsUnit r := by
  obtain ⟨s, hs⟩ := exists_mul_sub_mem_of_sub_one_mem_jacobson r h
  rw [mem_bot, sub_eq_zero, mul_comm] at hs
  exact .of_mul_eq_one _ hs
/-
**Ideal.mem_jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_jacobson_bot {x : R} : x in jacobson (⊥ : Ideal R) ↔ forall y, IsUnit 
(x * y + 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_jacobson_iff`：mem_jacobson_iff {x : R} : x in jacobson I ↔ for
all y, exists z, z * y * x + z - 1 in I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
（共 49 条，此处仅展示前 30 条）
-/
theorem mem_jacobson_bot {x : R} : x ∈ jacobson (⊥ : Ideal R) ↔ ∀ y, IsUnit (x * y + 1) :=
  ⟨fun hx y =>
    let ⟨z, hz⟩ := (mem_jacobson_iff.1 hx) y
    isUnit_iff_exists_inv.2
      ⟨z, by rwa [add_mul, one_mul, ← sub_eq_zero, mul_right_comm, mul_comm _ z, mul_right_comm]⟩,
    fun h =>
    mem_jacobson_iff.mpr fun y =>
      let ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (h y)
      ⟨b, (Submodule.mem_bot R).2 (hb ▸ by ring)⟩⟩

/-- An ideal `I` of `R` is equal to its Jacobson radical if and only if
the Jacobson radical of the quotient ring `R/I` is the zero ideal -/
/-
**Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Idea
l`。
形式化陈述：jacobson_eq_iff_jacobson_quotient_eq_bot : I.jacobson = I ↔ jacobson (⊥ : 
Ideal (R ⧸ I)) = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
· 使用定理 `Ideal.map_jacobson_of_surjective`：map_jacobson_of_surjective {f : R ->+*
 S} (hf : Function.Surjective f) : RingHom.ker f <= I -> map f I.jacobson = (map
 f I).jacobson
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.comap_jacobson_of_surjective`：comap_jacobson_of_surjective {f : R 
->+* S} (hf : Function.Surjective f) {K : Ideal S} : comap f K.jacobson = (comap
 f K).jacobson

--- 原说明 ---
An ideal `I` of `R` is equal to its Jacobson radical if and only if
the Jacobson radical of the quotient ring `R/I` is the zero ideal
-/
theorem jacobson_eq_iff_jacobson_quotient_eq_bot :
    I.jacobson = I ↔ jacobson (⊥ : Ideal (R ⧸ I)) = ⊥ := by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    replace h := congr_arg (Ideal.map (Ideal.Quotient.mk I)) h
    rw [map_jacobson_of_surjective hf (le_of_eq mk_ker)] at h
    simpa using h
  · intro h
    replace h := congr_arg (comap (Ideal.Quotient.mk I)) h
    rw [comap_jacobson_of_surjective hf, ← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I)] at h
    simpa using h

/-- The standard radical and Jacobson radical of an ideal `I` of `R` are equal if and only if
the nilradical and Jacobson radical of the quotient ring `R/I` coincide -/
/-
**Ideal.radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot** 是 Mathlib 中的一
个定理，位于命名空间 `Ideal`。
形式化陈述：radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot : I.radical = I.j
acobson ↔ radical (⊥ : Ideal (R ⧸ I)) = jacobson ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
· 使用定理 `Ideal.map_jacobson_of_surjective`：map_jacobson_of_surjective {f : R ->+*
 S} (hf : Function.Surjective f) : RingHom.ker f <= I -> map f I.jacobson = (map
 f I).jacobson
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.map_radical_of_surjective`：map_radical_of_surjective {f : R ->+* S
} (hf : Function.Surjective f) {I : Ideal R} (h : RingHom.ker f <= I) : map f I.
radical = (map f I).r…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Ideal.comap_jacobson_of_surjective`：comap_jacobson_of_surjective {f : R 
->+* S} (hf : Function.Surjective f) {K : Ideal S} : comap f K.jacobson = (comap
 f K).jacobson
· 使用定理 `Ideal.comap_radical`：comap_radical : comap f (radical K) = radical (coma
p f K)

--- 原说明 ---
The standard radical and Jacobson radical of an ideal `I` of `R` are equal if an
d only if
the nilradical and Jacobson radical of the quotient ring `R/I` coincide
-/
theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot :
    I.radical = I.jacobson ↔ radical (⊥ : Ideal (R ⧸ I)) = jacobson ⊥ := by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    have := congr_arg (map (Ideal.Quotient.mk I)) h
    rw [map_radical_of_surjective hf (le_of_eq mk_ker),
      map_jacobson_of_surjective hf (le_of_eq mk_ker)] at this
    simpa using this
  · intro h
    have := congr_arg (comap (Ideal.Quotient.mk I)) h
    rw [comap_radical, comap_jacobson_of_surjective hf,
      ← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I)] at this
    simpa using this
/-
**Ideal.jacobson_radical_eq_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：jacobson_radical_eq_jacobson : I.radical.jacobson = I.jacobson
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `sInf_le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s t : 
Set α}, s ⊆ t → sInf t ≤ sInf s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.jacobson_mono`：jacobson_mono {I J : Ideal R} : I <= J -> I.jacobso
n <= J.jacobson
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
-/
theorem jacobson_radical_eq_jacobson : I.radical.jacobson = I.jacobson :=
  le_antisymm
    (le_trans (le_of_eq (congr_arg jacobson (radical_eq_sInf I)))
      (sInf_le_sInf fun _ hJ => ⟨sInf_le ⟨hJ.1, hJ.2.isPrime⟩, hJ.2⟩))
    (jacobson_mono le_radical)

end CommRing

end Jacobson

section IsLocal

variable [CommRing R]

/-- An ideal `I` is local iff its Jacobson radical is maximal. -/
/-
**Ideal.IsLocal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ideal`。
形式化陈述：{R : Type u} → [inst : CommRing R] → Ideal R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal `I` is local iff its Jacobson radical is maximal.
-/
class IsLocal (I : Ideal R) : Prop where
  /-- A ring `R` is local if and only if its Jacobson radical is maximal -/
  out : IsMaximal (jacobson I)
/-
**Ideal.isLocal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isLocal_iff {I : Ideal R} : IsLocal I ↔ IsMaximal (jacobson I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsLocal.out`：∀ {R : Type u} {inst : CommRing R} {I : Ideal R} [sel
f : I.IsLocal], I.jacobson.IsMaximal
-/
theorem isLocal_iff {I : Ideal R} : IsLocal I ↔ IsMaximal (jacobson I) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
/-
**Ideal.isLocal_of_isMaximal_radical** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isLocal_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) : 
IsLocal I
参数：hi : IsMaximal (radical I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.IsPrime.radical_le_iff`：∀ {R : Type u} [inst : CommSemiring R] {I 
J : Ideal R}, J.IsPrime → (I.radical ≤ J ↔ I ≤ J)
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
-/
theorem isLocal_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) : IsLocal I :=
  ⟨have : radical I = jacobson I :=
      le_antisymm (le_sInf fun _ ⟨him, hm⟩ => hm.isPrime.radical_le_iff.2 him)
        (sInf_le ⟨le_radical, hi⟩)
    show IsMaximal (jacobson I) from this ▸ hi⟩
/-
**Ideal.IsLocal.le_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsLocal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {I J : Ideal R}, I.IsLocal → I ≤ J → J 
≠ ⊤ → J ≤ I.jacobson
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsLocal.out`：∀ {R : Type u} {inst : CommRing R} {I : Ideal R} [sel
f : I.IsLocal], I.jacobson.IsMaximal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem IsLocal.le_jacobson {I J : Ideal R} (hi : IsLocal I) (hij : I ≤ J) (hj : J ≠ ⊤) :
    J ≤ jacobson I :=
  let ⟨_, hm, hjm⟩ := exists_le_maximal J hj
  le_trans hjm <| le_of_eq <| Eq.symm <| hi.1.eq_of_le hm.1.1 <| sInf_le ⟨le_trans hij hjm, hm⟩
/-
**Ideal.IsLocal.mem_jacobson_or_exists_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsLo
cal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {I : Ideal R}, I.IsLocal → ∀ (x : R), x
 ∈ I.jacobson ∨ ∃ y, y * x - 1 ∈ I
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Ideal.IsLocal.le_jacobson`：∀ {R : Type u} [inst : CommRing R] {I J : Ide
al R}, I.IsLocal → I ≤ J → J ≠ ⊤ → J ≤ I.jacobson
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem IsLocal.mem_jacobson_or_exists_inv {I : Ideal R} (hi : IsLocal I) (x : R) :
    x ∈ jacobson I ∨ ∃ y, y * x - 1 ∈ I :=
  by_cases
    (fun h : I ⊔ span {x} = ⊤ =>
      let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
      let ⟨r, hr⟩ := mem_span_singleton.1 hq
      Or.inr ⟨r, by
        rw [← hpq, mul_comm, ← hr, ← neg_sub, add_sub_cancel_right]; exact I.neg_mem hpi⟩)
    fun h : I ⊔ span {x} ≠ ⊤ =>
    Or.inl <|
      le_trans le_sup_right (hi.le_jacobson le_sup_left h) <| mem_span_singleton.2 <| dvd_refl x

end IsLocal

end Ideal

namespace TwoSidedIdeal

variable {R : Type u} [Ring R]

/-- The Jacobson radical of `I` is the infimum of all maximal (left) ideals containing `I`. -/
/-
**TwoSidedIdeal.jacobson** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：jacobson (I : TwoSidedIdeal R) : TwoSidedIdeal R
参数：I : TwoSidedIdeal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Jacobson radical of `I` is the infimum of all maximal (left) ideals containi
ng `I`.
-/
def jacobson (I : TwoSidedIdeal R) : TwoSidedIdeal R :=
  (asIdeal I).jacobson.toTwoSided
/-
**TwoSidedIdeal.asIdeal_jacobson** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：asIdeal_jacobson (I : TwoSidedIdeal R) : asIdeal I.jacobson = (asIdeal I).
jacobson
参数：I : TwoSidedIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.asIdeal_toTwoSided`：asIdeal_toTwoSided (I : Ideal R) [I.IsTwoSided
] : I.toTwoSided.asIdeal = I
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma asIdeal_jacobson (I : TwoSidedIdeal R) : asIdeal I.jacobson = (asIdeal I).jacobson := by
  ext; simp [jacobson]
/-
**TwoSidedIdeal.mem_jacobson_iff** 是 Mathlib 中的一个定理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_jacobson_iff {x : R} {I : TwoSidedIdeal R} : x in jacobson I ↔ forall 
y, exists z, z * y * x + z - 1 in I
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_jacobson_iff {x : R} {I : TwoSidedIdeal R} :
    x ∈ jacobson I ↔ ∀ y, ∃ z, z * y * x + z - 1 ∈ I := by
  simp [jacobson, Ideal.mem_jacobson_iff]

end TwoSidedIdeal

