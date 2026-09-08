/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inna Capdeboscq, Damiano Testa
-/

module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Subnormal subgroups

In this file, we define subnormal subgroups.

We also show some basic results about the interaction of subnormality and simplicity of groups.
These should cover most of the results needed in this case.

## Main Definition

`IsSubnormal H`: A subgroup `H` of a group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is a subgroup `K` of `G` containing `H` and such that `H` is normal in `K` and
  `K` satisfies `IsSubnormal`.

## Main Statements

* `eq_bot_or_top_of_isSimpleGroup`: the only subnormal subgroups of simple groups are
  `⊥`, the trivial subgroup, and `⊤`, the whole group.
* `isSubnormal_iff`: Shows that `IsSubnormal H` holds if and only if there is
  an increasing chain of subgroups, each normal in the following, starting from `H` and
  reaching `⊤` in a finite number of steps.
* `IsSubnormal.trans`: The relation of being `IsSubnormal` is transitive.

## Implementation Notes

We deviate from the common informal definition of subnormality and use an inductive predicate.
This turns out to be more convenient to work with.
We show the equivalence of the current definition with the existence of chains in
`isSubnormal_iff`.
-/

variable {G : Type*} [Group G] {H K : Subgroup G}

public section

namespace Subgroup

/-- A subgroup `H` of a group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is a subgroup `K` of `G` containing `H` and such that `H` is normal in `K` and
  `K` satisfies `IsSubnormal`.

Equivalently, `H.IsSubnormal` means that there is a chain of subgroups
`H₀ ≤ H₁ ≤ ... ≤ Hₙ` such that
* `H = H₀`,
* `G = Hₙ`,
* for each `i ∈ {0, ..., n - 1}`, `Hᵢ` is a normal subgroup of `Hᵢ₊₁`.

See `isSubnormal_iff` for this characterisation.
-/
/-
**Subgroup.IsSubnormal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → Subgroup G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup `H` of a group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is a subgroup `K` of `G` containing `H` and such that `H` is normal i
n `K` and
  `K` satisfies `IsSubnormal`.

Equivalently, `H.IsSubnormal` means that there is a chain of subgroups
`H₀ ≤ H₁ ≤ ... ≤ Hₙ` such that
* `H = H₀`,
* `G = Hₙ`,
* for each `i ∈ {0, ..., n - 1}`, `Hᵢ` is a normal subgroup of `Hᵢ₊₁`.

See `isSubnormal_iff` for this characterisation.
-/
inductive IsSubnormal : Subgroup G → Prop where
  /-- The whole subgroup `G` is subnormal in itself. -/
  | top : IsSubnormal (⊤ : Subgroup G)
  /-- A subgroup `H` is subnormal if there is a subnormal subgroup `K` containing `H` that is
  subnormal itself and such that `H` is normal in `K`. -/
  | step : ∀ H K, (h_le : H ≤ K) → (hSubn : IsSubnormal K) → (hN : (H.subgroupOf K).Normal) →
    IsSubnormal H

/-- An additive subgroup `H` of an additive group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is an additive subgroup `K` of `G` containing `H` and such that `H` is normal in `K` and
  `K` satisfies `IsSubnormal`.

Equivalently, `H.IsSubnormal` means that there is a chain of additive subgroups
`H₀ ≤ H₁ ≤ ... ≤ Hₙ` such that
* `H = H₀`,
* `G = Hₙ`,
* for each `i ∈ {0, ..., n - 1}`, `Hᵢ` is a normal additive subgroup of `Hᵢ₊₁`.

See `isSubnormal_iff` for this characterisation.
-/
/-
**Subgroup._root_.AddSubgroup.IsSubnormal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Subgroup`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive subgroup `H` of an additive group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is an additive subgroup `K` of `G` containing `H` and such that `H` i
s normal in `K` and
  `K` satisfies `IsSubnormal`.

Equivalently, `H.IsSubnormal` means that there is a chain of additive subgroups
`H₀ ≤ H₁ ≤ ... ≤ Hₙ` such that
* `H = H₀`,
* `G = Hₙ`,
* for each `i ∈ {0, ..., n - 1}`, `Hᵢ` is a normal additive subgroup of `Hᵢ₊₁`.

See `isSubnormal_iff` for this characterisation.
-/
inductive _root_.AddSubgroup.IsSubnormal {G : Type*} [AddGroup G] : AddSubgroup G → Prop where
  /-- The whole additive subgroup `G` is subnormal in itself. -/
  | top : IsSubnormal (⊤ : AddSubgroup G)
  /-- An additive subgroup `H` is subnormal if there is a subnormal additive subgroup `K`
  containing `H` that is subnormal itself and such that `H` is normal in `K`. -/
  | step : ∀ H K, (h_le : H ≤ K) → (hSubn : IsSubnormal K) → (hN : (H.addSubgroupOf K).Normal) →
    IsSubnormal H

attribute [simp] Subgroup.IsSubnormal.top

/-- A normal subgroup is subnormal. -/
@[to_additive /-- A normal additive subgroup is subnormal. -/]
/-
**Subgroup.Normal.isSubnormal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G}, H.Normal → H.IsSubnorm
al
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Subgroup.normal_subgroupOf`：∀ {G : Type u_1} [inst : Group G] {H N : Sub
group G} [N.Normal], (N.subgroupOf H).Normal

--- 原说明 ---
A normal subgroup is subnormal.
-/
lemma Normal.isSubnormal (hn : H.Normal) : IsSubnormal H :=
  IsSubnormal.step _ ⊤ le_top IsSubnormal.top normal_subgroupOf

namespace IsSubnormal

/-- The trivial subgroup is subnormal. -/
@[to_additive (attr := simp) /-- The trivial additive subgroup is subnormal. -/]
/-
**Subgroup.IsSubnormal.bot** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsSubnormal`。
形式化陈述：bot : IsSubnormal (⊥ : Subgroup G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.isSubnormal`：∀ {G : Type u_1} [inst : Group G] {H : Subg
roup G}, H.Normal → H.IsSubnormal

--- 原说明 ---
The trivial subgroup is subnormal.
-/
lemma bot : IsSubnormal (⊥ : Subgroup G) := normal_bot.isSubnormal

/-- A subnormal subgroup of a simple group is normal. -/
@[to_additive /-- A subnormal additive subgroup of a simple additive group is normal. -/]
/-
**Subgroup.IsSubnormal.normal_of_isSimpleGroup** 是 Mathlib 中的一个引理，位于命名空间 `Subgro
up.IsSubnormal`。
形式化陈述：normal_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : H.IsSubnormal) : H.No
rmal
参数：hG : IsSimpleGroup G；hN : H.IsSubnormal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subgroup.Normal.eq_bot_or_eq_top`：Subgroup.Normal.eq_bot_or_eq_top [IsSi
mpleGroup G] {H : Subgroup G} (Hn : H.Normal) : H = ⊥ ∨ H = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A subnormal subgroup of a simple group is normal.
-/
lemma normal_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : H.IsSubnormal) :
    H.Normal := by
  induction hN with
  | top => simp
  | step H K h_le hSubn hN Knorm =>
    obtain rfl | rfl := Knorm.eq_bot_or_eq_top
    · grind
    · grind [!normal_subgroupOf_iff_le_normalizer_inf, inf_of_le_left, normalizer_eq_top_iff]

/-- A subnormal subgroup of a simple group is either trivial or the whole group. -/
@[to_additive /-- A subnormal additive subgroup of a simple additive group is either trivial or the
whole group. -/]
/-
**Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup** 是 Mathlib 中的一个引理，位于命名空间 
`Subgroup.IsSubnormal`。
形式化陈述：eq_bot_or_top_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : IsSubnormal H)
 : H = ⊥ ∨ H = ⊤
参数：hG : IsSimpleGroup G；hN : IsSubnormal H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.eq_bot_or_eq_top`：Subgroup.Normal.eq_bot_or_eq_top [IsSi
mpleGroup G] {H : Subgroup G} (Hn : H.Normal) : H = ⊥ ∨ H = ⊤
· 使用引理 `Subgroup.IsSubnormal.normal_of_isSimpleGroup`：normal_of_isSimpleGroup (h
G : IsSimpleGroup G) (hN : H.IsSubnormal) : H.Normal
-/
lemma eq_bot_or_top_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : IsSubnormal H) :
    H = ⊥ ∨ H = ⊤ :=
  (hN.normal_of_isSimpleGroup hG).eq_bot_or_eq_top

@[to_additive]
/-
**Subgroup.IsSubnormal.iff_eq_top_or_exists** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.
IsSubnormal`。
形式化陈述：iff_eq_top_or_exists : IsSubnormal H ↔ H = ⊤ ∨ exists K, H < K ∧ IsSubnorm
al K ∧ (H.subgroupOf K).Normal where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma iff_eq_top_or_exists :
    IsSubnormal H ↔ H = ⊤ ∨ ∃ K, H < K ∧ IsSubnormal K ∧ (H.subgroupOf K).Normal where
  mp h := by
    induction h with
    | top => simp
    | step H K HK hS hN ih =>
      obtain rfl | ⟨K', HK', hS', hN'⟩ := ih
      · obtain rfl | hH := eq_or_ne H ⊤
        · simp
        · exact Or.inr ⟨⊤, by simp [hH.lt_top , *]⟩
      right
      obtain rfl | hH := eq_or_ne H K
      · use K'
      · exact ⟨K, by simpa [*] using HK.lt_of_ne hH⟩
  mpr h := by
    obtain rfl | ⟨K, HK, Ksn, h⟩ := h
    · exact top
    · exact step _ _ HK.le Ksn h

/-- A proper subnormal subgroup is contained in a proper normal subgroup. -/
@[to_additive /-- A proper subnormal additive subgroup is contained in a proper normal additive
subgroup. -/]
/-
**Subgroup.IsSubnormal.exists_normal_and_le_and_lt_top_of_ne** 是 Mathlib 中的一个引理，
位于命名空间 `Subgroup.IsSubnormal`。
形式化陈述：exists_normal_and_le_and_lt_top_of_ne (hN : H.IsSubnormal) (ne_top : H != 
⊤) : exists K, K.Normal ∧ H <= K ∧ K < ⊤
参数：hN : H.IsSubnormal；ne_top : H != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer`：normal_subgroupOf_iff_le_n
ormalizer (h : H <= K) : (H.subgroupOf K).Normal ↔ K <= normalizer H
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_normal_and_le_and_lt_top_of_ne (hN : H.IsSubnormal) (ne_top : H ≠ ⊤) :
    ∃ K, K.Normal ∧ H ≤ K ∧ K < ⊤ := by
  induction hN with
  | top => contradiction
  | step H K h_le hSubn hN ih =>
    obtain rfl | K_ne := eq_or_ne K ⊤
    · rw [normal_subgroupOf_iff_le_normalizer h_le, top_le_iff, normalizer_eq_top_iff] at hN
      exact ⟨H, hN, le_rfl, ne_top.lt_top⟩
    · grind

/--
A subnormal subgroup is either the whole group or it is contained in a proper normal subgroup.
-/
@[to_additive /-- A subnormal additive subgroup is either the whole group or it is contained in a
proper normal additive subgroup. -/]
/-
**Subgroup.IsSubnormal.lt_normal** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsSubnormal
`。
形式化陈述：lt_normal (hN : H.IsSubnormal) : H = ⊤ ∨ exists K, K.Normal ∧ H <= K ∧ K <
 ⊤
参数：hN : H.IsSubnormal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma lt_normal (hN : H.IsSubnormal) : H = ⊤ ∨ ∃ K, K.Normal ∧ H ≤ K ∧ K < ⊤ := by
  obtain rfl | H_ne := eq_or_ne H ⊤
  · simp
  · grind only [iff_eq_top_or_exists, exists_normal_and_le_and_lt_top_of_ne]

/--
A characterisation of satisfying `IsSubnormal` in terms of chains of subgroups, each normal in
the following one.

The sequence stabilises once it reaches `⊤`, which is guaranteed at the asserted `n`.
-/
@[to_additive /-- A characterisation of satisfying `IsSubnormal` in terms of chains of additive
subgroups, each normal in the following one.

The sequence stabilises once it reaches `⊤`, which is guaranteed at the asserted `n`. -/]
/-
**Subgroup.IsSubnormal.isSubnormal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsSub
normal`。
形式化陈述：isSubnormal_iff : H.IsSubnormal ↔ exists n, exists f : Nat -> Subgroup G, 
(Monotone f) ∧ (forall i, ((f i).subgroupOf (f (i + 1))).Normal) ∧ f 0 = H ∧ f n
 = ⊤ where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.subgroupOf_self`：subgroupOf_self : H.subgroupOf H = ⊤
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
lemma isSubnormal_iff : H.IsSubnormal ↔
    ∃ n, ∃ f : ℕ → Subgroup G,
    (Monotone f) ∧ (∀ i, ((f i).subgroupOf (f (i + 1))).Normal) ∧
      f 0 = H ∧ f n = ⊤ where
  mp h := by
    induction h with
    | top =>
      use 0, fun _ ↦ ⊤, ?_, (by simp)
      exact monotone_nat_of_le_succ fun _ ↦ le_top
    | step H K h_le hSubn hN ih =>
      obtain ⟨n, f, hf, f0, fn⟩ := ih
      use n + 1, fun | 0 => H | n + 1 => f n, ?_, ?_
      · grind
      · refine monotone_nat_of_le_succ ?_
        grind only [monotone_iff_forall_lt]
      · grind
  mpr := by
    rintro ⟨n, hyps⟩
    revert H
    induction n with
    | zero => simp_all
    | succ n ih =>
      rintro J ⟨F, hF, H_le, rfl, ih1⟩
      refine step _ _ (hF <| Nat.le_add_right 0 1) ?_ (H_le _)
      refine ih ⟨fun n ↦ F (n + 1), ?_⟩
      grind only [Monotone, monotone_iff_forall_lt]

alias ⟨exists_chain, _⟩ := isSubnormal_iff

/--
Subnormality is transitive.

This version involves an explicit `subtype`; the version `IsSubnormal.trans` does not.
-/
@[to_additive /-- Subnormality is transitive.

This version involves an explicit `subtype`; the version `IsSubnormal.trans` does not. -/]
protected
/-
**Subgroup.IsSubnormal.trans'** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsSubnormal`。
形式化陈述：trans' {H : Subgroup K} (Hsn : IsSubnormal H) (Ksn : IsSubnormal K) : IsSu
bnormal (H.map K.subtype)
参数：Hsn : IsSubnormal H；Ksn : IsSubnormal K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `Subgroup.map_mono`：map_mono {f : G ->* N} {K K' : Subgroup G} : K <= K' 
-> map f K <= map f K'
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer`：normal_subgroupOf_iff_le_n
ormalizer (h : H <= K) : (H.subgroupOf K).Normal ↔ K <= normalizer H
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Subgroup.le_normalizer_map`：le_normalizer_map (f : G ->* N) : (normalize
r H).map f <= normalizer (H.map f)
-/
lemma trans' {H : Subgroup K} (Hsn : IsSubnormal H) (Ksn : IsSubnormal K) :
    IsSubnormal (H.map K.subtype) := by
  induction Hsn with
  | top =>
    rwa [← MonoidHom.range_eq_map, range_subtype]
  | step A B h_le hSubn hN ih =>
    refine step (A.map K.subtype) (B.map K.subtype) (map_mono h_le) ih ?_
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (map_mono h_le)]
    exact le_trans (map_mono hN) (le_normalizer_map _)

/--
If `H` is a subnormal subgroup of `K` and `K` is a subnormal subgroup of `G`,
then `H` is a subnormal subgroup of `G`.
-/
@[to_additive /-- If `H` is a subnormal additive subgroup of `K` and `K` is a subnormal
additive subgroup of `G`, then `H` is a subnormal additive subgroup of `G`. -/]
protected
/-
**Subgroup.IsSubnormal.trans** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsSubnormal`。
形式化陈述：trans (HK : H <= K) (Hsn : IsSubnormal (H.subgroupOf K)) (Ksn : IsSubnorma
l K) : IsSubnormal H
参数：HK : H <= K；Hsn : IsSubnormal (H.subgroupOf K)；Ksn : IsSubnormal K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.IsSubnormal.trans'`：trans' {H : Subgroup K} (Hsn : IsSubnormal 
H) (Ksn : IsSubnormal K) : IsSubnormal (H.map K.subtype)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_subgroupOf_eq_of_le`：map_subgroupOf_eq_of_le {H K : Subgrou
p G} (h : H <= K) : (H.subgroupOf K).map K.subtype = H
-/
lemma trans (HK : H ≤ K) (Hsn : IsSubnormal (H.subgroupOf K)) (Ksn : IsSubnormal K) :
    IsSubnormal H := by
  have key := Hsn.trans' Ksn
  rwa [map_subgroupOf_eq_of_le HK] at key

/-- The image of a subnormal subgroup under a surjective homomorphism is subnormal. -/
@[to_additive
/-- The image of a subnormal additive subgroup under a surjective homomorphism is subnormal. -/]
protected
/-
**Subgroup.IsSubnormal.map** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsSubnormal`。
形式化陈述：map {G'} [Group G'] {f : G ->* G'} (hf : Function.Surjective f) (hS : H.Is
Subnormal) : IsSubnormal (map f H)
参数：hf : Function.Surjective f；hS : H.IsSubnormal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_top_of_surjective`：map_top_of_surjective (f : G ->* N) (h :
 Function.Surjective f) : Subgroup.map f ⊤ = ⊤
· 使用定理 `Subgroup.map_mono`：map_mono {f : G ->* N} {K K' : Subgroup G} : K <= K' 
-> map f K <= map f K'
· 使用定理 `Subgroup.normal_subgroupOf_of_le_normalizer`：normal_subgroupOf_of_le_nor
malizer {H N : Subgroup G} (hLE : H <= normalizer N) : (N.subgroupOf H).Normal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer`：normal_subgroupOf_iff_le_n
ormalizer (h : H <= K) : (H.subgroupOf K).Normal ↔ K <= normalizer H
· 使用定理 `Subgroup.le_normalizer_map`：le_normalizer_map (f : G ->* N) : (normalize
r H).map f <= normalizer (H.map f)
-/
lemma map {G'} [Group G'] {f : G →* G'} (hf : Function.Surjective f) (hS : H.IsSubnormal) :
    IsSubnormal (map f H) := by
  induction hS with
  | top =>
    rw [map_top_of_surjective f hf]
    apply top
  | step H K h_le hSubn hN ih =>
    apply step _ (map f K) (map_mono h_le) ih
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    exact normal_subgroupOf_of_le_normalizer ((map_mono hN).trans (H.le_normalizer_map f))

/-- The quotient of a subnormal subgroup by a normal subgroup is subnormal. -/
@[to_additive
/-- The quotient of a subnormal additive subgroup by a normal additive subgroup is subnormal. -/]
/-
**Subgroup.IsSubnormal.quotient** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsSubnormal`
。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G} [inst_1 : K.Normal], 
  H.IsSubnormal → (Subgroup.map (QuotientGroup.mk' K) H).IsSubnormal
参数：Subgroup.map (QuotientGroup.mk' K) H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.IsSubnormal.map`：map {G'} [Group G'] {f : G ->* G'} (hf : Funct
ion.Surjective f) (hS : H.IsSubnormal) : IsSubnormal (map f H)
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
-/
protected lemma quotient [K.Normal] (hS : H.IsSubnormal) :
    IsSubnormal (map (QuotientGroup.mk' K) H) :=
  hS.map (QuotientGroup.mk'_surjective K)

/-- The inverse image of a subnormal subgroup under a group homomorphism is a subnormal subgroup. -/
@[to_additive /-- The inverse image of a subnormal additive subgroup under an additive group
homomorphism is a subnormal additive subgroup. -/]
protected
/-
**Subgroup.IsSubnormal.comap** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsSubnormal`。
形式化陈述：comap {G'} [Group G'] {H' : Subgroup G'} (f : G ->* G') (h : H'.IsSubnorma
l) : (comap f H').IsSubnormal
参数：f : G ->* G'；h : H'.IsSubnormal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.comap_top`：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f =
 ⊤
· 使用定理 `Subgroup.comap_mono`：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <=
 K' -> comap f K <= comap f K'
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer`：normal_subgroupOf_iff_le_n
ormalizer (h : H <= K) : (H.subgroupOf K).Normal ↔ K <= normalizer H
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.le_normalizer_comap`：le_normalizer_comap (f : N ->* G) : (norma
lizer H).comap f <= normalizer (H.comap f)
-/
lemma comap {G'} [Group G'] {H' : Subgroup G'} (f : G →* G') (h : H'.IsSubnormal) :
    (comap f H').IsSubnormal := by
  induction h with
  | top => simp
  | step H K h_le hSubn hN ih =>
    apply step _ (comap f K) (comap_mono h_le) ih
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (comap_mono h_le)]
    exact (comap_mono hN).trans (le_normalizer_comap f)

@[to_additive (attr := simp)]
/-
**Subgroup.IsSubnormal.subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsSubnorma
l`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsSubnormal → (H.s
ubgroupOf K).IsSubnormal
参数：H.subgroupOf K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.IsSubnormal.comap`：comap {G'} [Group G'] {H' : Subgroup G'} (f 
: G ->* G') (h : H'.IsSubnormal) : (comap f H').IsSubnormal
-/
protected lemma subgroupOf (hH : H.IsSubnormal) : (H.subgroupOf K).IsSubnormal := hH.comap _

/-- The intersection of two subnormal subgroups is subnormal. -/
@[to_additive /-- The intersection of two subnormal additive subgroups is additive subnormal. -/]
/-
**Subgroup.IsSubnormal.inf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsSubnormal`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G}, H.IsSubnormal → K.Is
Subnormal → (H ⊓ K).IsSubnormal
参数：H ⊓ K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.subgroupOf_map_subtype`：subgroupOf_map_subtype (H K : Subgroup 
G) : (H.subgroupOf K).map K.subtype = H ⊓ K
· 使用引理 `Subgroup.IsSubnormal.trans'`：trans' {H : Subgroup K} (Hsn : IsSubnormal 
H) (Ksn : IsSubnormal K) : IsSubnormal (H.map K.subtype)
· 使用定理 `Subgroup.IsSubnormal.subgroupOf`：∀ {G : Type u_1} [inst : Group G] {H K 
: Subgroup G}, H.IsSubnormal → (H.subgroupOf K).IsSubnormal

--- 原说明 ---
The intersection of two subnormal subgroups is subnormal.
-/
protected lemma inf (hH : H.IsSubnormal) (hK : K.IsSubnormal) : (H ⊓ K).IsSubnormal := by
  simpa using hH.subgroupOf.trans' hK

open scoped Pointwise

/--
If `g : Γ` is an element of a group acting on `G` and `H` is subnormal, then `g • H` is subnormal.
-/
/-
**Subgroup.IsSubnormal.smul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.IsSubnormal`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G} {Γ : Type u_2} [inst_1 
: Group Γ] [inst_2 : MulDistribMulAction Γ G],   H.IsSubnormal → ∀ (g : Γ), (g •
 H).IsSubnormal
参数：g : Γ；g • H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.IsSubnormal.map`：map {G'} [Group G'] {f : G ->* G'} (hf : Funct
ion.Surjective f) (hS : H.IsSubnormal) : IsSubnormal (map f H)
· 使用定理 `MulAction.surjective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [
inst_1 : MulAction α β] (g : α), Function.Surjective fun x => g • x

--- 原说明 ---
If `g : Γ` is an element of a group acting on `G` and `H` is subnormal, then `g 
• H` is subnormal.
-/
protected lemma smul {Γ : Type*} [Group Γ] [MulDistribMulAction Γ G] (hS : H.IsSubnormal)
    (g : Γ) : (g • H).IsSubnormal :=
  hS.map (MulAction.surjective g)

/-- If the subgroup `H` of a group `G` is trivial, then it is subnormal. -/
@[to_additive /-- If the additive subgroup `H` of a group `G` is trivial, then it is subnormal. -/]
/-
**Subgroup.IsSubnormal.of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup.IsSub
normal`。
形式化陈述：of_subsingleton [Subsingleton H] : H.IsSubnormal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton H]
 : H = ⊥

--- 原说明 ---
If the subgroup `H` of a group `G` is trivial, then it is subnormal.
-/
lemma of_subsingleton [Subsingleton H] : H.IsSubnormal := by
  simp [eq_bot_of_subsingleton H]

end Subgroup.IsSubnormal

