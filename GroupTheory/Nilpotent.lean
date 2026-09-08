/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ines Wright, Joachim Breitner
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.GroupTheory.Commutator.Finite

/-!

# Nilpotent groups

An API for nilpotent groups, that is, groups for which the upper central series
reaches `⊤`.

## Main definitions

Recall that if `H K : Subgroup G` then `⁅H, K⁆ : Subgroup G` is the subgroup of `G` generated
by the commutators `hkh⁻¹k⁻¹`. Recall also Lean's conventions that `⊤` denotes the
subgroup `G` of `G`, and `⊥` denotes the trivial subgroup `{1}`.

* `Subgroup.upperCentralSeries G : ℕ → Subgroup G` : the upper central series of a group `G`.
     This is an increasing sequence of characteristic subgroups `H n` of `G` with `H 0 = ⊥` and
     `H (n + 1) / H n` is the centre of `G / H n`.
* `Subgroup.lowerCentralSeries (S : Subgroup G) : ℕ → Subgroup G` : the lower central series of `S`,
     computed in the ambient group `G`. This is the iterated commutator
     `S, ⁅S, S⁆, ⁅⁅S, S⁆, S⁆, …`. The classical lower central series of `G` is the case
     `S = ⊤`.
* `IsNilpotent` : A group G is nilpotent if its upper central series reaches `⊤`, or
    equivalently if its lower central series reaches `⊥`.
* `Group.nilpotencyClass` : the length of the upper central series of a nilpotent group.
* `IsAscendingCentralSeries (H : ℕ → Subgroup G) : Prop` and
* `IsDescendingCentralSeries (H : ℕ → Subgroup G) : Prop` : Note that in the literature
    a "central series" for a group is usually defined to be a *finite* sequence of normal subgroups
    `H 0`, `H 1`, ..., starting at `⊤`, finishing at `⊥`, and with each `H n / H (n + 1)`
    central in `G / H (n + 1)`. In this formalisation it is convenient to have two weaker predicates
    on an infinite sequence of subgroups `H n` of `G`: we say a sequence is a *descending central
    series* if it starts at `G` and `⁅H n, ⊤⁆ ⊆ H (n + 1)` for all `n`. Note that this series
    may not terminate at `⊥`, and the `H i` need not be normal. Similarly a sequence is an
    *ascending central series* if `H 0 = ⊥` and `⁅H (n + 1), ⊤⁆ ⊆ H n` for all `n`, again with no
    requirement that the series reaches `⊤` or that the `H i` are normal.

## Main theorems

`G` is *defined* to be nilpotent if the upper central series reaches `⊤`.
* `nilpotent_iff_finite_ascending_central_series` : `G` is nilpotent iff some ascending central
    series reaches `⊤`.
* `nilpotent_iff_finite_descending_central_series` : `G` is nilpotent iff some descending central
    series reaches `⊥`.
* `nilpotent_iff_lower` : `G` is nilpotent iff the lower central series reaches `⊥`.
* The `Group.nilpotencyClass` can likewise be obtained from these equivalent
  definitions, see `least_ascending_central_series_length_eq_nilpotencyClass`,
  `least_descending_central_series_length_eq_nilpotencyClass` and
  `lowerCentralSeries_length_eq_nilpotencyClass`.
* If `G` is nilpotent, then so are its subgroups, images, quotients and preimages.
  Binary and finite products of nilpotent groups are nilpotent.
  Infinite products are nilpotent if their nilpotent class is bounded.
  Corresponding lemmas about the `Group.nilpotencyClass` are provided.
* The `Group.nilpotencyClass` of `G ⧸ center G` is given explicitly, and an induction principle
  is derived from that.
* `IsNilpotent.to_isSolvable`: If `G` is nilpotent, it is solvable.


## Warning

A "central series" is usually defined to be a finite sequence of normal subgroups going
from `⊥` to `⊤` with the property that each subquotient is contained within the centre of
the associated quotient of `G`. This means that if `G` is not nilpotent, then
none of what we have called `upperCentralSeries G`, `(⊤ : Subgroup G).lowerCentralSeries` or
the sequences satisfying `IsAscendingCentralSeries` or `IsDescendingCentralSeries`
are actually central series. Note that the fact that the upper and lower central series
are not central series if `G` is not nilpotent is a standard abuse of notation.

-/

@[expose] public section


open commutatorElement Subgroup

section WithGroup

variable {G : Type*} [Group G] (N : Subgroup G) [Normal N]

namespace Subgroup

/-- If `N` is a normal subgroup of `G`, then the set `{x : G | ∀ y : G, x*y*x⁻¹*y⁻¹ ∈ N}`
is a subgroup of `G` (because it is the preimage in `G` of the centre of the
quotient group `G/N`.)
-/
@[to_additive /-- If `N` is a normal additive subgroup of `G`, then the set
`{x : G | ∀ y : G, x + y -x - y ∈ N}` is an additive subgroup of `G`
(because it is the preimage in `G` of the centre of the additive quotient group `G/N`.) -/]
/-
**Subgroup.upperCentralSeriesStep** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：upperCentralSeriesStep : Subgroup G where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def upperCentralSeriesStep : Subgroup G where
  carrier := { x : G | ∀ y : G, ⁅x, y⁆ ∈ N }
  one_mem' y := by simp
  mul_mem' {a b} ha hb y := by
    convert! Subgroup.mul_mem _ (ha (b * y * b⁻¹)) (hb y) using 1
    group
  inv_mem' {x} hx y := by
    specialize hx y⁻¹
    rw [commutatorElement_def, mul_assoc, inv_inv] at hx ⊢
    exact Subgroup.Normal.mem_comm inferInstance hx

@[to_additive]
/-
**Subgroup.mem_upperCentralSeriesStep** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_upperCentralSeriesStep (x : G) : x in upperCentralSeriesStep N ↔ foral
l y, ⁅x, y⁆ in N
参数：x : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_upperCentralSeriesStep (x : G) :
    x ∈ upperCentralSeriesStep N ↔ ∀ y, ⁅x, y⁆ ∈ N := Iff.rfl

open QuotientGroup

/-- The proof that `upperCentralSeriesStep N` is the preimage of the centre of `G/N` under
the canonical surjection. -/
@[to_additive /-- The proof that `upperCentralSeriesStep N` is the preimage of the centre of `G/N`\
under the canonical surjection. -/]
/-
**Subgroup.upperCentralSeriesStep_eq_comap_center** 是 Mathlib 中的一个定理，位于命名空间 `Sub
group`。
形式化陈述：upperCentralSeriesStep_eq_comap_center : upperCentralSeriesStep N = Subgro
up.comap (mk' N) (center (G ⧸ N))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_comap`：mem_comap {K : Subgroup N} {f : G ->* N} {x : G} : x
 in K.comap f ↔ f x in K
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
· 使用定理 `QuotientGroup.forall_mk`：forall_mk {C : α ⧸ s -> Prop} : (forall x : α ⧸
 s, C x) ↔ forall x : α, C x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `QuotientGroup.coe_mk'`：coe_mk' : (mk' N : G -> G ⧸ N) = mk
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.mk_mul`：mk_mul (a b : G) : ((a * b : G) : Q) = a * b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `QuotientGroup.eq_iff_div_mem`：eq_iff_div_mem {N : Subgroup G} [nN : N.No
rmal] {x y : G} : (x : G ⧸ N) = y ↔ x / y in N
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `commutatorElement_def`：commutatorElement_def {G : Type*} [Group G] (g₁ g
₂ : G) : ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem upperCentralSeriesStep_eq_comap_center :
    upperCentralSeriesStep N = Subgroup.comap (mk' N) (center (G ⧸ N)) := by
  ext
  rw [mem_comap, mem_center_iff, forall_mk]
  refine forall_congr' fun y => ?_
  rw [coe_mk', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, eq_comm, eq_iff_div_mem,
    div_eq_mul_inv, mul_inv_rev, commutatorElement_def]
  simp_rw [mul_assoc]

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [N.Characteristic] : Characteristic (upperCentralSeriesStep N) :=
  (upperCentralSeriesStep_eq_comap_center N) ▸ Characteristic.comap_quotient_mk centerCharacteristic

variable (G)

/-- An auxiliary type-theoretic definition defining both the upper central series of
a group, and a proof that it is characteristic, all in one go. -/
/-
**Subgroup.upperCentralSeriesAux** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：upperCentralSeriesAux : Nat -> Σ' H : Subgroup G, Characteristic H | 0 => 
⟨⊥, inferInstance⟩ | n + 1 => let un
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary type-theoretic definition defining both the upper central series of
a group, and a proof that it is characteristic, all in one go.
-/
def upperCentralSeriesAux : ℕ → Σ' H : Subgroup G, Characteristic H
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let un := upperCentralSeriesAux n
    let _un_characteristic := un.2
    ⟨upperCentralSeriesStep un.1, inferInstance⟩

/-- An auxiliary type-theoretic definition defining both the upper central series of
an additive group, and a proof that it is characteristic, all in one go. -/
/-
**Subgroup._root_.AddSubgroup.upperCentralSeriesAux** 是 Mathlib 中的一个定义，位于命名空间 `S
ubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary type-theoretic definition defining both the upper central series of
an additive group, and a proof that it is characteristic, all in one go.
-/
def _root_.AddSubgroup.upperCentralSeriesAux (G : Type*) [AddGroup G] :
    ℕ → Σ' H : AddSubgroup G, H.Characteristic
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let un := upperCentralSeriesAux G n
    let _un_characteristic := un.2
    ⟨AddSubgroup.upperCentralSeriesStep un.1, inferInstance⟩

attribute [to_additive existing] upperCentralSeriesAux

/-- `upperCentralSeries G n` is the `n`th term in the upper central series of `G`.

This is the increasing chain of subgroups of `G` that starts with the trivial subgroup `⊥` of `G`
and then continues defining `upperCentralSeries G (n + 1)` to be all the elements of `G`
that, modulo `upperCentralSeries G n`, belong to the center of the quotient
`G ⧸ upperCentralSeries G n`.

In particular, the identities
* `upperCentralSeries G 0 = ⊥` (`upperCentralSeries_zero`);
* `upperCentralSeries G 1 = center G` (`upperCentralSeries_one`);

hold.
-/
@[to_additive
/-- `upperCentralSeries G n` is the `n`th term in the upper central series of `G`.

This is the increasing chain of additive subgroups of `G` that starts with the trivial additive
subgroup `⊥` of `G` and then continues defining `upperCentralSeries G (n + 1)` to be all the
elements of `G` that, modulo `upperCentralSeries G n`, belong to the center of the additive quotient
`G ⧸ upperCentralSeries G n`.

In particular, the identities
* `upperCentralSeries G 0 = ⊥` (`upperCentralSeries_zero`);
* `upperCentralSeries G 1 = center G` (`upperCentralSeries_one`);

hold.
-/]
/-
**Subgroup.upperCentralSeries** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：upperCentralSeries (n : Nat) : Subgroup G
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def upperCentralSeries (n : ℕ) : Subgroup G :=
  (upperCentralSeriesAux G n).1

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : Characteristic (upperCentralSeries G n) :=
  (upperCentralSeriesAux G n).2

@[to_additive (attr := simp)]
/-
**Subgroup.upperCentralSeries_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：upperCentralSeries_zero : upperCentralSeries G 0 = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem upperCentralSeries_zero : upperCentralSeries G 0 = ⊥ := rfl
/-
**Subgroup.upperCentralSeries_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：upperCentralSeries_one : upperCentralSeries G 1 = center G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.mk.congr_simp`：∀ {G : Type u_3} [inst : Group G] (toSubmonoid t
oSubmonoid_1 : Submonoid G)   (e_toSubmonoid : toSubmonoid = toSubmonoid_1)   (i
nv_mem' : ∀ …
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `commutatorElement_def`：commutatorElement_def {G : Type*} [Group G] (g₁ g
₂ : G) : ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem upperCentralSeries_one : upperCentralSeries G 1 = center G := by
  ext
  simp only [upperCentralSeries, upperCentralSeriesAux, upperCentralSeriesStep, mem_bot, mem_mk,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq, mem_center_iff]
  exact forall_congr' fun y => by
    rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, eq_comm]
/-
**Subgroup._root_.AddSubgroup.upperCentralSeries_one** 是 Mathlib 中的一个定理，位于命名空间 `
Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddSubgroup.upperCentralSeries_one (G : Type*) [AddGroup G] :
    AddSubgroup.upperCentralSeries G 1 = AddSubgroup.center G := by
  ext
  simp only [AddSubgroup.upperCentralSeries, AddSubgroup.upperCentralSeriesAux,
    AddSubgroup.upperCentralSeriesStep, AddSubgroup.mem_bot, AddSubgroup.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, AddSubgroup.mem_center_iff]
  exact forall_congr' fun y => by
    rw [addCommutatorElement_def, add_neg_eq_zero, add_neg_eq_iff_eq_add, eq_comm]

attribute [to_additive existing (attr := simp) AddSubgroup.upperCentralSeries_one]
  upperCentralSeries_one

variable {G}

/-- The `n+1`st term of the upper central series `H i` has underlying set equal to the `x` such
that `⁅x,G⁆ ⊆ H n`. -/
@[to_additive /-- The `n+1`st term of the upper central series `H i` has underlying set equal to
the `x` such that `⁅x,G⁆ ⊆ H n`. -/]
/-
**Subgroup.mem_upperCentralSeries_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_upperCentralSeries_succ_iff {n : Nat} {x : G} : x in upperCentralSerie
s G (n + 1) ↔ forall y : G, ⁅x, y⁆ in upperCentralSeries G n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_upperCentralSeries_succ_iff {n : ℕ} {x : G} :
    x ∈ upperCentralSeries G (n + 1) ↔ ∀ y : G, ⁅x, y⁆ ∈ upperCentralSeries G n :=
  Iff.rfl

variable (G) in
@[to_additive]
/-
**Subgroup.commutator_upperCentralSeries_top_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup`。
形式化陈述：commutator_upperCentralSeries_top_le (n : Nat) : ⁅upperCentralSeries G (n 
+ 1), ⊤⁆ <= upperCentralSeries G n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_upperCentralSeries_succ_iff`：mem_upperCentralSeries_succ_if
f {n : Nat} {x : G} : x in upperCentralSeries G (n + 1) ↔ forall y : G, ⁅x, y⁆ i
n upperCentralSeries G n
-/
theorem commutator_upperCentralSeries_top_le (n : ℕ) :
    ⁅upperCentralSeries G (n + 1), ⊤⁆ ≤ upperCentralSeries G n := by
  apply closure_le _ |>.mpr
  rintro _ ⟨h, hh, g, _, rfl⟩
  exact mem_upperCentralSeries_succ_iff.mp hh g

@[to_additive (attr := simp)]
/-
**Subgroup.comap_upperCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Type u_2} [inst_1 : Group H] (e : H
 ≃* G) (n : ℕ),   Subgroup.comap (↑e) (Subgroup.upperCentralSeries G n) = Subgro
up.upperCentralSeries H n
参数：e : H ≃* G；n : ℕ；↑e；Subgroup.upperCentralSeries G n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
lemma comap_upperCentralSeries {H : Type*} [Group H] (e : H ≃* G) :
    ∀ n, (upperCentralSeries G n).comap e = upperCentralSeries H n
  | 0 => by simpa [MonoidHom.ker_eq_bot_iff] using e.injective
  | n + 1 => by
    ext
    simp [mem_upperCentralSeries_succ_iff, ← comap_upperCentralSeries e n,
      ← e.toEquiv.forall_congr_right, commutatorElement_def]

end Subgroup

namespace Group

variable (G) in
-- `IsNilpotent` is already defined in the root namespace (for elements of rings).
-- TODO: Rename it to `IsNilpotentElement`?
/-- A group `G` is nilpotent if its upper central series is eventually `G`. -/
@[mk_iff, wikidata Q1755242]
/-
**Group.IsNilpotent** 是 Mathlib 中的一个归纳类型，位于命名空间 `Group`。
形式化陈述：(G : Type u_2) → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group `G` is nilpotent if its upper central series is eventually `G`.
-/
class IsNilpotent (G : Type*) [Group G] : Prop where
  nilpotent' : ∃ n : ℕ, upperCentralSeries G n = ⊤

variable (G) in
-- `IsNilpotent` is already defined in the root namespace (for elements of rings).
-- TODO: Rename it to `IsNilpotentElement`?
/-- An additive group `G` is nilpotent if its upper central series is eventually `G`. -/
@[mk_iff]
/-
**Group._root_.AddGroup.IsNilpotent** 是 Mathlib 中的一个类，位于命名空间 `Group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive group `G` is nilpotent if its upper central series is eventually `G`
.
-/
class _root_.AddGroup.IsNilpotent (G : Type*) [AddGroup G] : Prop where
  nilpotent' : ∃ n : ℕ, AddSubgroup.upperCentralSeries G n = ⊤

@[to_additive]
/-
**Group.IsNilpotent.nilpotent** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsNilpotent`。
形式化陈述：∀ (G : Type u_2) [inst : Group G] [Group.IsNilpotent G], ∃ n, Subgroup.upp
erCentralSeries G n = ⊤
参数：G : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsNilpotent.nilpotent'`：∀ {G : Type u_2} {inst : Group G} [self : 
Group.IsNilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
-/
lemma IsNilpotent.nilpotent (G : Type*) [Group G] [IsNilpotent G] :
    ∃ n : ℕ, upperCentralSeries G n = ⊤ := Group.IsNilpotent.nilpotent'

@[to_additive]
/-
**Group.isNilpotent_congr** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
形式化陈述：isNilpotent_congr {H : Type*} [Group H] (e : G ≃* H) : IsNilpotent G ↔ IsN
ilpotent H
参数：e : G ≃* H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.comap_top`：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f =
 ⊤
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.comap_upperCentralSeries`：∀ {G : Type u_1} [inst : Group G] {H 
: Type u_2} [inst_1 : Group H] (e : H ≃* G) (n : ℕ),   Subgroup.comap (↑e) (Subg
roup.upperCentralSeries…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isNilpotent_congr {H : Type*} [Group H] (e : G ≃* H) : IsNilpotent G ↔ IsNilpotent H := by
  simp_rw [isNilpotent_iff]
  refine exists_congr fun n ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [← Subgroup.comap_top e.symm.toMonoidHom, ← h]
  · simp [← Subgroup.comap_top e.toMonoidHom, ← h]

@[to_additive (attr := simp)]
/-
**Group.isNilpotent_top** 是 Mathlib 中的一个引理，位于命名空间 `Group`。
形式化陈述：isNilpotent_top : IsNilpotent (⊤ : Subgroup G) ↔ IsNilpotent G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.isNilpotent_congr`：isNilpotent_congr {H : Type*} [Group H] (e : G 
≃* H) : IsNilpotent G ↔ IsNilpotent H
-/
lemma isNilpotent_top : IsNilpotent (⊤ : Subgroup G) ↔ IsNilpotent G :=
  isNilpotent_congr Subgroup.topEquiv

variable (G) in
/-- A group `G` is virtually nilpotent if it has a nilpotent cofinite subgroup `N`. -/
@[to_additive /-- An additive group `G` is virtually nilpotent if it has a nilpotent cofinite
additive subgroup `N`. -/]
/-
**Group.IsVirtuallyNilpotent** 是 Mathlib 中的一个定义，位于命名空间 `Group`。
形式化陈述：IsVirtuallyNilpotent : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsVirtuallyNilpotent : Prop := ∃ N : Subgroup G, IsNilpotent N ∧ FiniteIndex N

@[to_additive]
/-
**Group.IsNilpotent.isVirtuallyNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsNilp
otent`。
形式化陈述：∀ {G : Type u_1} [inst : Group G], Group.IsNilpotent G → Group.IsVirtually
Nilpotent G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instFiniteIndexTop`：∀ {G : Type u_1} [inst : Group G], ⊤.Finite
Index
-/
lemma IsNilpotent.isVirtuallyNilpotent (hG : IsNilpotent G) : IsVirtuallyNilpotent G :=
  ⟨⊤, by simpa, inferInstance⟩

end Group

open Group

namespace Subgroup

/-- A sequence of subgroups of `G` is an ascending central series if `H 0` is trivial and
`⁅H (n + 1), G⁆ ⊆ H n` for all `n`. Note that we do not require that `H n = G` for some `n`. -/
@[to_additive /-- A sequence of additive subgroups of `G` is an ascending central series if `H 0` is
trivial and `⁅H (n + 1), G⁆ ⊆ H n` for all `n`. We do not require that `H n = G` for some `n`. -/]
/-
**Subgroup.IsAscendingCentralSeries** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：IsAscendingCentralSeries (H : Nat -> Subgroup G) : Prop
参数：H : Nat -> Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsAscendingCentralSeries (H : ℕ → Subgroup G) : Prop :=
  H 0 = ⊥ ∧ ∀ (x : G) (n : ℕ), x ∈ H (n + 1) → ∀ g, ⁅x, g⁆ ∈ H n

/-- A sequence of subgroups of `G` is a descending central series if `H 0` is `G` and
`⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. Note that we do not require that `H n = {1}` for some `n`. -/
@[to_additive /-- A sequence of additive subgroups of `G` is a descending central series if `H 0` is
`G` and `⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. We do not require that `H n = {1}` for some `n`. -/]
/-
**Subgroup.IsDescendingCentralSeries** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：IsDescendingCentralSeries (H : Nat -> Subgroup G)
参数：H : Nat -> Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsDescendingCentralSeries (H : ℕ → Subgroup G) :=
  H 0 = ⊤ ∧ ∀ (x : G) (n : ℕ), x ∈ H n → ∀ g, ⁅x, g⁆ ∈ H (n + 1)

/-- Any ascending central series for a group is bounded above by the upper central series. -/
@[to_additive /-- Any ascending central series for an additive group is bounded above by the upper
central series. -/]
/-
**Subgroup.ascending_central_series_le_upper** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : ℕ → Subgroup G),   Subgroup.IsAscen
dingCentralSeries H → ∀ (n : ℕ), H n ≤ Subgroup.upperCentralSeries G n
参数：H : ℕ → Subgroup G；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascending_central_series_le_upper (H : ℕ → Subgroup G) (hH : IsAscendingCentralSeries H) :
    ∀ n : ℕ, H n ≤ upperCentralSeries G n
  | 0 => hH.1.symm ▸ le_refl ⊥
  | n + 1 => by
    intro x hx
    rw [mem_upperCentralSeries_succ_iff]
    exact fun y => ascending_central_series_le_upper H hH n (hH.2 x n hx y)

variable (G)

/-- The upper central series of a group is an ascending central series. -/
@[to_additive /-- The upper central series of an additive group is an ascending central series. -/]
/-
**Subgroup.upperCentralSeries_isAscendingCentralSeries** 是 Mathlib 中的一个定理，位于命名空间
 `Subgroup`。
形式化陈述：upperCentralSeries_isAscendingCentralSeries : IsAscendingCentralSeries (up
perCentralSeries G)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The upper central series of a group is an ascending central series.
-/
theorem upperCentralSeries_isAscendingCentralSeries :
    IsAscendingCentralSeries (upperCentralSeries G) :=
  ⟨rfl, fun _x _n h => h⟩

@[to_additive]
/-
**Subgroup.upperCentralSeries_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：upperCentralSeries_mono : Monotone (upperCentralSeries G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commutatorElement_def`：commutatorElement_def {G : Type*} [Group G] (g₁ g
₂ : G) : ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `Subgroup.normal_of_characteristic`：∀ {G : Type u_1} [inst : Group G] (H 
: Subgroup G) [h : H.Characteristic], H.Normal
· 使用定理 `Subgroup.instCharacteristicUpperCentralSeries`：∀ (G : Type u_1) [inst : 
Group G] (n : ℕ), (Subgroup.upperCentralSeries G n).Characteristic
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
theorem upperCentralSeries_mono : Monotone (upperCentralSeries G) := by
  refine monotone_nat_of_le_succ ?_
  intro n x hx y
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc y x⁻¹ y⁻¹]
  exact mul_mem hx (Normal.conj_mem inferInstance x⁻¹ (inv_mem hx) y)

/-- A group `G` is nilpotent iff there exists an ascending central series which reaches `G` in
finitely many steps. -/
@[to_additive /-- An additive group `G` is nilpotent iff there exists an ascending central series
which reaches `G` in finitely many steps. -/]
/-
**Subgroup.nilpotent_iff_finite_ascending_central_series** 是 Mathlib 中的一个定理，位于命名
空间 `Subgroup`。
形式化陈述：nilpotent_iff_finite_ascending_central_series : IsNilpotent G ↔ exists n :
 Nat, exists H : Nat -> Subgroup G, IsAscendingCentralSeries H ∧ H n = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.upperCentralSeries_isAscendingCentralSeries`：upperCentralSeries
_isAscendingCentralSeries : IsAscendingCentralSeries (upperCentralSeries G)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.ascending_central_series_le_upper`：∀ {G : Type u_1} [inst : Gro
up G] (H : ℕ → Subgroup G),   Subgroup.IsAscendingCentralSeries H → ∀ (n : ℕ), H
 n ≤ Subgroup.upperCentralSeries…
-/
theorem nilpotent_iff_finite_ascending_central_series :
    IsNilpotent G ↔ ∃ n : ℕ, ∃ H : ℕ → Subgroup G, IsAscendingCentralSeries H ∧ H n = ⊤ := by
  constructor
  · rintro ⟨n, nH⟩
    exact ⟨_, _, upperCentralSeries_isAscendingCentralSeries G, nH⟩
  · rintro ⟨n, H, hH, hn⟩
    use n
    rw [eq_top_iff, ← hn]
    exact ascending_central_series_le_upper H hH n

@[to_additive]
/-
**Subgroup.is_descending_rev_series_of_is_ascending** 是 Mathlib 中的一个定理，位于命名空间 `S
ubgroup`。
形式化陈述：is_descending_rev_series_of_is_ascending {H : Nat -> Subgroup G} {n : Nat}
 (hn : H n = ⊤) (hasc : IsAscendingCentralSeries H) : IsDescendingCentralSeries 
fun m : Nat => H (n - m)
参数：hn : H n = ⊤；hasc : IsAscendingCentralSeries H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commutatorElement_one_left`：commutatorElement_one_left : ⁅(1 : G), g⁆ = 
1
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.mem_bot`：mem_bot {x : G} : x in (⊥ : Subgroup G) ↔ x = 1
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Nat.add_sub_add_right`：∀ (n k m : ℕ), n + k - (m + k) = n - m
-/
theorem is_descending_rev_series_of_is_ascending {H : ℕ → Subgroup G} {n : ℕ} (hn : H n = ⊤)
    (hasc : IsAscendingCentralSeries H) : IsDescendingCentralSeries fun m : ℕ => H (n - m) := by
  obtain ⟨h0, hH⟩ := hasc
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp at hx
  by_cases! hm : n ≤ m
  · rw [tsub_eq_zero_of_le hm, h0, Subgroup.mem_bot] at hx
    subst hx
    rw [commutatorElement_one_left]
    exact Subgroup.one_mem _
  · apply hH
    convert! hx using 1
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_lt hm), Nat.succ_eq_add_one, Nat.add_sub_add_right]

@[to_additive]
/-
**Subgroup.is_ascending_rev_series_of_is_descending** 是 Mathlib 中的一个定理，位于命名空间 `S
ubgroup`。
形式化陈述：is_ascending_rev_series_of_is_descending {H : Nat -> Subgroup G} {n : Nat}
 (hn : H n = ⊥) (hdesc : IsDescendingCentralSeries H) : IsAscendingCentralSeries
 fun m : Nat => H (n - m)
参数：hn : H n = ⊥；hdesc : IsDescendingCentralSeries H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Nat.add_sub_add_right`：∀ (n k m : ℕ), n + k - (m + k) = n - m
-/
theorem is_ascending_rev_series_of_is_descending {H : ℕ → Subgroup G} {n : ℕ} (hn : H n = ⊥)
    (hdesc : IsDescendingCentralSeries H) : IsAscendingCentralSeries fun m : ℕ => H (n - m) := by
  obtain ⟨h0, hH⟩ := hdesc
  refine ⟨hn, fun x m hx g => ?_⟩
  dsimp only at hx ⊢
  by_cases! hm : n ≤ m
  · have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm
    rw [hnm, h0]
    exact mem_top _
  · convert! hH x _ hx g using 1
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_lt hm), Nat.succ_eq_add_one, Nat.add_sub_add_right]

/-- A group `G` is nilpotent iff there exists a descending central series which reaches the
trivial group in a finite time. -/
@[to_additive /-- An additive group `G` is nilpotent iff there exists a descending central series
which reaches the trivial group in a finite time. -/]
/-
**Subgroup.nilpotent_iff_finite_descending_central_series** 是 Mathlib 中的一个定理，位于命
名空间 `Subgroup`。
形式化陈述：nilpotent_iff_finite_descending_central_series : IsNilpotent G ↔ exists n 
: Nat, exists H : Nat -> Subgroup G, IsDescendingCentralSeries H ∧ H n = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.nilpotent_iff_finite_ascending_central_series`：nilpotent_iff_fi
nite_ascending_central_series : IsNilpotent G ↔ exists n : Nat, exists H : Nat -
> Subgroup G, IsAscendingCentralSeries H ∧ H…
· 使用定理 `Subgroup.is_descending_rev_series_of_is_ascending`：is_descending_rev_ser
ies_of_is_ascending {H : Nat -> Subgroup G} {n : Nat} (hn : H n = ⊤) (hasc : IsA
scendingCentralSeries H) : IsDescending…
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subgroup.is_ascending_rev_series_of_is_descending`：is_ascending_rev_seri
es_of_is_descending {H : Nat -> Subgroup G} {n : Nat} (hn : H n = ⊥) (hdesc : Is
DescendingCentralSeries H) : IsAscendin…
-/
theorem nilpotent_iff_finite_descending_central_series :
    IsNilpotent G ↔ ∃ n : ℕ, ∃ H : ℕ → Subgroup G, IsDescendingCentralSeries H ∧ H n = ⊥ := by
  rw [nilpotent_iff_finite_ascending_central_series]
  constructor
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_descending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, fun m => H (n - m), is_ascending_rev_series_of_is_descending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1

variable {G}

/-- The lower central series of a subgroup `S` of `G`, computed in the ambient group `G`.
This is the iterated commutator `⁅⁅⋯⁅S, S⁆, S⁆⋯, S⁆`, a subgroup of `G`. The lower central series
of `G` itself is the case `S = ⊤`. -/
/-
**Subgroup.lowerCentralSeries** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → Subgroup G → ℕ → Subgroup G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lower central series of a subgroup `S` of `G`, computed in the ambient group
 `G`.
This is the iterated commutator `⁅⁅⋯⁅S, S⁆, S⁆⋯, S⁆`, a subgroup of `G`. The low
er central series
of `G` itself is the case `S = ⊤`.
-/
def lowerCentralSeries (S : Subgroup G) : ℕ → Subgroup G
  | 0 => S
  | n + 1 => ⁅lowerCentralSeries S n, S⁆

/-- The lower central series of an additive subgroup `S` of `G`, computed in the ambient additive
group `G`. -/
/-
**Subgroup._root_.AddSubgroup.lowerCentralSeries** 是 Mathlib 中的一个定义，位于命名空间 `Subg
roup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lower central series of an additive subgroup `S` of `G`, computed in the amb
ient additive
group `G`.
-/
def _root_.AddSubgroup.lowerCentralSeries {G : Type*} [AddGroup G] (S : AddSubgroup G) :
    ℕ → AddSubgroup G
  | 0 => S
  | n + 1 => ⁅lowerCentralSeries S n, S⁆

attribute [to_additive existing] lowerCentralSeries

variable (S : Subgroup G)

@[to_additive (attr := simp)]
/-
**Subgroup.lowerCentralSeries_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_zero : S.lowerCentralSeries 0 = S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lowerCentralSeries_zero : S.lowerCentralSeries 0 = S := rfl

@[to_additive (attr := simp)]
/-
**Subgroup.lowerCentralSeries_succ** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_succ (n : Nat) : S.lowerCentralSeries (n + 1) = ⁅S.lowe
rCentralSeries n, S⁆
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lowerCentralSeries_succ (n : ℕ) :
    S.lowerCentralSeries (n + 1) = ⁅S.lowerCentralSeries n, S⁆ := rfl

@[to_additive top_lowerCentralSeries_one]
/-
**Subgroup.top_lowerCentralSeries_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：top_lowerCentralSeries_one : (⊤ : Subgroup G).lowerCentralSeries 1 = _root
_.commutator G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_lowerCentralSeries_one : (⊤ : Subgroup G).lowerCentralSeries 1 = _root_.commutator G :=
  rfl

@[deprecated (since := "2026-05-25")]
alias _root_.AddSubgroup.lowerCentralSeries_one := AddSubgroup.top_lowerCentralSeries_one

@[to_additive existing lowerCentralSeries_one, deprecated (since := "2026-05-25")]
alias lowerCentralSeries_one := top_lowerCentralSeries_one

@[to_additive]
/-
**Subgroup.mem_lowerCentralSeries_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_lowerCentralSeries_succ_iff (n : Nat) (q : G) : q in S.lowerCentralSer
ies (n + 1) ↔ q in closure { x | exists p in S.lowerCentralSeries n, exists q in
 S, ⁅p, q⁆ = x }
参数：n : Nat；q : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_lowerCentralSeries_succ_iff (n : ℕ) (q : G) :
    q ∈ S.lowerCentralSeries (n + 1) ↔
    q ∈ closure { x | ∃ p ∈ S.lowerCentralSeries n, ∃ q ∈ S, ⁅p, q⁆ = x } := Iff.rfl

@[to_additive]
/-
**Subgroup.lowerCentralSeries_characteristic** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup
`。
形式化陈述：lowerCentralSeries_characteristic [S.Characteristic] (n : Nat) : (S.lowerC
entralSeries n).Characteristic
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.lowerCentralSeries_succ`：lowerCentralSeries_succ (n : Nat) : S.
lowerCentralSeries (n + 1) = ⁅S.lowerCentralSeries n, S⁆
-/
instance lowerCentralSeries_characteristic [S.Characteristic] (n : ℕ) :
    (S.lowerCentralSeries n).Characteristic := by
  induction n with
  | zero => simpa
  | succ d _ => rw [lowerCentralSeries_succ]; infer_instance

@[to_additive]
/-
**Subgroup.self_le_normalizer_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `Subg
roup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (S : Subgroup G) (n : ℕ), S ≤ Subgroup.n
ormalizer ↑(S.lowerCentralSeries n)
参数：S : Subgroup G；n : ℕ；S.lowerCentralSeries n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.lowerCentralSeries_succ`：lowerCentralSeries_succ (n : Nat) : S.
lowerCentralSeries (n + 1) = ⁅S.lowerCentralSeries n, S⁆
· 使用定理 `Subgroup.normalizer_commutator_ge_right`：normalizer_commutator_ge_right 
: H₂ <= normalizer (⁅H₁, H₂⁆ : Subgroup G)
-/
theorem self_le_normalizer_lowerCentralSeries :
    ∀ n, S ≤ Subgroup.normalizer (S.lowerCentralSeries n : Set G)
  | 0 => Subgroup.le_normalizer
  | n + 1 => by
    rw [lowerCentralSeries_succ]
    apply normalizer_commutator_ge_right

@[to_additive]
/-
**Subgroup.lowerCentralSeries_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_antitone : Antitone S.lowerCentralSeries
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.lowerCentralSeries_succ`：lowerCentralSeries_succ (n : Nat) : S.
lowerCentralSeries (n + 1) = ⁅S.lowerCentralSeries n, S⁆
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.le_normalizer_iff_commutator_le_left`：le_normalizer_iff_commuta
tor_le_left : H <= normalizer K ↔ ⁅K, H⁆ <= K
· 使用定理 `Subgroup.self_le_normalizer_lowerCentralSeries`：∀ {G : Type u_1} [inst :
 Group G] (S : Subgroup G) (n : ℕ), S ≤ Subgroup.normalizer ↑(S.lowerCentralSeri
es n)
-/
theorem lowerCentralSeries_antitone : Antitone S.lowerCentralSeries := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [lowerCentralSeries_succ, ← le_normalizer_iff_commutator_le_left]
  exact S.self_le_normalizer_lowerCentralSeries n

/-- The lower central series of a group is a descending central series. -/
@[to_additive /-- The lower central series of an additive group is a descending central series. -/]
/-
**Subgroup.lowerCentralSeries_isDescendingCentralSeries** 是 Mathlib 中的一个定理，位于命名空
间 `Subgroup`。
形式化陈述：lowerCentralSeries_isDescendingCentralSeries : IsDescendingCentralSeries (
G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.commutator_mem_commutator`：commutator_mem_commutator (h₁ : g₁ i
n H₁) (h₂ : g₂ in H₂) : ⁅g₁, g₂⁆ in ⁅H₁, H₂⁆
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)

--- 原说明 ---
The lower central series of a group is a descending central series.
-/
theorem lowerCentralSeries_isDescendingCentralSeries :
    IsDescendingCentralSeries (G := G) (lowerCentralSeries ⊤) := by
  constructor
  · rfl
  intro x n hxn g
  exact commutator_mem_commutator hxn (mem_top g)

/-- Any descending central series for a group is bounded below by the lower central series. -/
@[to_additive /-- Any descending central series for an additive group is bounded below by the lower
central series. -/]
/-
**Subgroup.descending_central_series_ge_lower** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : ℕ → Subgroup G),   Subgroup.IsDesce
ndingCentralSeries H → ∀ (n : ℕ), ⊤.lowerCentralSeries n ≤ H n
参数：H : ℕ → Subgroup G；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem descending_central_series_ge_lower (H : ℕ → Subgroup G) (hH : IsDescendingCentralSeries H) :
    ∀ n : ℕ, lowerCentralSeries ⊤ n ≤ H n
  | 0 => hH.1.symm ▸ le_refl ⊤
  | n + 1 => commutator_le.mpr fun x hx q _ =>
      hH.2 x n (descending_central_series_ge_lower H hH n hx) q

/-- The lower central series commutes with images under a group homomorphism. -/
@[to_additive]
/-
**Subgroup.map_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_lowerCentralSeries {K : Type*} [Group K] (f : G ->* K) (n : Nat) : (S.
lowerCentralSeries n).map f = (S.map f).lowerCentralSeries n
参数：f : G ->* K；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.lowerCentralSeries_succ`：lowerCentralSeries_succ (n : Nat) : S.
lowerCentralSeries (n + 1) = ⁅S.lowerCentralSeries n, S⁆
· 使用定理 `Subgroup.map_commutator`：map_commutator (f : G ->* G') : map f ⁅H₁, H₂⁆ 
= ⁅map f H₁, map f H₂⁆

--- 原说明 ---
The lower central series commutes with images under a group homomorphism.
-/
theorem map_lowerCentralSeries {K : Type*} [Group K] (f : G →* K) (n : ℕ) :
    (S.lowerCentralSeries n).map f = (S.map f).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ d hd =>
    rw [lowerCentralSeries_succ, lowerCentralSeries_succ, Subgroup.map_commutator, hd]

/-- The lower central series of `H : Subgroup G` computed in the ambient group `G` coincides with
the lower central series of `H` viewed as its own group, mapped back to `G`. -/
@[to_additive (attr := simp)]
/-
**Subgroup.top_subtype_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：top_subtype_lowerCentralSeries (H : Subgroup G) (n : Nat) : (lowerCentralS
eries ⊤ n).map H.subtype = H.lowerCentralSeries n
参数：H : Subgroup G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_lowerCentralSeries`：map_lowerCentralSeries {K : Type*} [Gro
up K] (f : G ->* K) (n : Nat) : (S.lowerCentralSeries n).map f = (S.map f).lower
CentralSeries n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.subtype_range`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H

--- 原说明 ---
The lower central series of `H : Subgroup G` computed in the ambient group `G` c
oincides with
the lower central series of `H` viewed as its own group, mapped back to `G`.
-/
theorem top_subtype_lowerCentralSeries (H : Subgroup G) (n : ℕ) :
    (lowerCentralSeries ⊤ n).map H.subtype = H.lowerCentralSeries n := by
  rw [map_lowerCentralSeries, ← MonoidHom.range_eq_map, subtype_range]

/-- A subgroup is nilpotent iff its lower central series (computed in the ambient group) eventually
vanishes. -/
@[to_additive /-- An additive subgroup is nilpotent iff its lower central series eventually
vanishes. -/]
/-
**Subgroup.isNilpotent_iff_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：isNilpotent_iff_lowerCentralSeries : Group.IsNilpotent S ↔ exists n, S.low
erCentralSeries n = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.nilpotent_iff_finite_descending_central_series`：nilpotent_iff_f
inite_descending_central_series : IsNilpotent G ↔ exists n : Nat, exists H : Nat
 -> Subgroup G, IsDescendingCentralSeries H ∧…
· 使用定理 `Subgroup.descending_central_series_ge_lower`：∀ {G : Type u_1} [inst : Gr
oup G] (H : ℕ → Subgroup G),   Subgroup.IsDescendingCentralSeries H → ∀ (n : ℕ),
 ⊤.lowerCentralSeries n ≤ H n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.top_subtype_lowerCentralSeries`：top_subtype_lowerCentralSeries 
(H : Subgroup G) (n : Nat) : (lowerCentralSeries ⊤ n).map H.subtype = H.lowerCen
tralSeries n
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
· 使用定理 `Subgroup.lowerCentralSeries_isDescendingCentralSeries`：lowerCentralSerie
s_isDescendingCentralSeries : IsDescendingCentralSeries (G
· 使用定理 `Subgroup.map_subtype_inj`：map_subtype_inj {H : Subgroup G} {K L : Subgro
up H} : K.map H.subtype = L.map H.subtype ↔ K = L
-/
theorem isNilpotent_iff_lowerCentralSeries :
    Group.IsNilpotent S ↔ ∃ n, S.lowerCentralSeries n = ⊥ := by
  rw [nilpotent_iff_finite_descending_central_series]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, H, hH, hn⟩
    refine ⟨n, ?_⟩
    have h1 := descending_central_series_ge_lower H hH n
    rw [hn, le_bot_iff] at h1
    rw [← top_subtype_lowerCentralSeries, h1, Subgroup.map_bot]
  · rintro ⟨n, hn⟩
    refine ⟨n, lowerCentralSeries ⊤, lowerCentralSeries_isDescendingCentralSeries, ?_⟩
    rwa [← map_subtype_inj, map_bot, top_subtype_lowerCentralSeries]

/-- A group is nilpotent if and only if its lower central series eventually reaches
the trivial subgroup. -/
@[to_additive /-- An additive group is nilpotent if and only if its lower central series eventually
reaches the trivial additive subgroup. -/]
/-
**Subgroup.nilpotent_iff_lowerCentralSeries** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`
。
形式化陈述：nilpotent_iff_lowerCentralSeries : IsNilpotent G ↔ exists n, lowerCentralS
eries (⊤ : Subgroup G) n = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Group.isNilpotent_top`：isNilpotent_top : IsNilpotent (⊤ : Subgroup G) ↔ 
IsNilpotent G
· 使用定理 `Subgroup.isNilpotent_iff_lowerCentralSeries`：isNilpotent_iff_lowerCentra
lSeries : Group.IsNilpotent S ↔ exists n, S.lowerCentralSeries n = ⊥
-/
theorem nilpotent_iff_lowerCentralSeries :
    IsNilpotent G ↔ ∃ n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥ :=
  Group.isNilpotent_top.symm.trans (isNilpotent_iff_lowerCentralSeries ⊤)

end Subgroup

section Classical

variable (G) in
open scoped Classical in
/-- The nilpotency class of a nilpotent group is the smallest natural `n` such that
the `n`-th term of the upper central series is `G`. If `G` is not nilpotent then the nilpotency
/-
**takes** 是 Mathlib 中的一个类，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class takes the junk value 0. -/
@[to_additive /-- The nilpotency class of a nilpotent additive group is the smallest natural `n`
such that the `n`-th term of the upper central series is `G`. If `G` is not nilpotent then the
nilpotency class takes the junk value 0. -/]
/-
**Group.nilpotencyClass** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Group.nilpotencyClass : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsNilpotent.nilpotent`：∀ (G : Type u_2) [inst : Group G] [Group.Is
Nilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
-/
noncomputable def Group.nilpotencyClass : ℕ :=
  if hG : IsNilpotent G then Nat.find hG.nilpotent else 0

@[to_additive]
/-
**Group.nilpotencyClass_of_not_nilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.nilpotencyClass_of_not_nilpotent (hG : ¬ IsNilpotent G) : Group.nilp
otencyClass G = 0
参数：hG : ¬ IsNilpotent G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Group.IsNilpotent.nilpotent`：∀ (G : Type u_2) [inst : Group G] [Group.Is
Nilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
-/
theorem Group.nilpotencyClass_of_not_nilpotent (hG : ¬ IsNilpotent G) :
    Group.nilpotencyClass G = 0 :=
  dif_neg hG

variable [hG : IsNilpotent G]

open scoped Classical in
@[to_additive]
/-
**Group.nilpotencyClass_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.nilpotencyClass_def : Group.nilpotencyClass G = Nat.find (IsNilpoten
t.nilpotent G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Group.IsNilpotent.nilpotent`：∀ (G : Type u_2) [inst : Group G] [Group.Is
Nilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
-/
theorem Group.nilpotencyClass_def :
    Group.nilpotencyClass G = Nat.find (IsNilpotent.nilpotent G) :=
  dif_pos hG

namespace Subgroup

@[to_additive (attr := simp)]
/-
**Subgroup.upperCentralSeries_nilpotencyClass** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：upperCentralSeries_nilpotencyClass : upperCentralSeries G (Group.nilpotenc
yClass G) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsNilpotent.nilpotent`：∀ (G : Type u_2) [inst : Group G] [Group.Is
Nilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.nilpotencyClass_def`：Group.nilpotencyClass_def : Group.nilpotencyC
lass G = Nat.find (IsNilpotent.nilpotent G)
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem upperCentralSeries_nilpotencyClass :
    upperCentralSeries G (Group.nilpotencyClass G) = ⊤ := by
  classical
  rw [nilpotencyClass_def, Nat.find_spec (IsNilpotent.nilpotent G)]

@[to_additive]
/-
**Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le** 是 Mathlib 中的一个定理，位
于命名空间 `Subgroup`。
形式化陈述：upperCentralSeries_eq_top_iff_nilpotencyClass_le {n : Nat} : upperCentralS
eries G n = ⊤ ↔ Group.nilpotencyClass G <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsNilpotent.nilpotent`：∀ (G : Type u_2) [inst : Group G] [Group.Is
Nilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.nilpotencyClass_def`：Group.nilpotencyClass_def : Group.nilpotencyC
lass G = Nat.find (IsNilpotent.nilpotent G)
· 使用引理 `Nat.find_le`：find_le {h : exists n, p n} (hn : p n) : Nat.find h <= n
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.upperCentralSeries_nilpotencyClass`：upperCentralSeries_nilpoten
cyClass : upperCentralSeries G (Group.nilpotencyClass G) = ⊤
· 使用定理 `Subgroup.upperCentralSeries_mono`：upperCentralSeries_mono : Monotone (up
perCentralSeries G)
-/
theorem upperCentralSeries_eq_top_iff_nilpotencyClass_le {n : ℕ} :
    upperCentralSeries G n = ⊤ ↔ Group.nilpotencyClass G ≤ n := by
  classical
  constructor
  · intro h
    rw [nilpotencyClass_def]
    exact Nat.find_le h
  · intro h
    rw [eq_top_iff, ← upperCentralSeries_nilpotencyClass]
    exact upperCentralSeries_mono _ h

open scoped Classical in
/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which an ascending
central series reaches `G` in its `n`-th term. -/
@[to_additive /-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which an
ascending central series reaches `G` in its `n`-th term. -/]
/-
**Subgroup.least_ascending_central_series_length_eq_nilpotencyClass** 是 Mathlib 
中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：least_ascending_central_series_length_eq_nilpotencyClass : Nat.find ((nilp
otent_iff_finite_ascending_central_series G).mp hG) = Group.nilpotencyClass G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.nilpotent_iff_finite_ascending_central_series`：nilpotent_iff_fi
nite_ascending_central_series : IsNilpotent G ↔ exists n : Nat, exists H : Nat -
> Subgroup G, IsAscendingCentralSeries H ∧ H…
· 使用定理 `Group.IsNilpotent.nilpotent`：∀ (G : Type u_2) [inst : Group G] [Group.Is
Nilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.nilpotencyClass_def`：Group.nilpotencyClass_def : Group.nilpotencyC
lass G = Nat.find (IsNilpotent.nilpotent G)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Nat.find_mono`：find_mono [DecidablePred q] (h : forall n, q n -> p n) {h
p : exists n, p n} {hq : exists n, q n} : Nat.find hp <= Nat.find hq
· 使用定理 `Subgroup.upperCentralSeries_isAscendingCentralSeries`：upperCentralSeries
_isAscendingCentralSeries : IsAscendingCentralSeries (upperCentralSeries G)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Subgroup.ascending_central_series_le_upper`：∀ {G : Type u_1} [inst : Gro
up G] (H : ℕ → Subgroup G),   Subgroup.IsAscendingCentralSeries H → ∀ (n : ℕ), H
 n ≤ Subgroup.upperCentralSeries…
-/
theorem least_ascending_central_series_length_eq_nilpotencyClass :
    Nat.find ((nilpotent_iff_finite_ascending_central_series G).mp hG) =
    Group.nilpotencyClass G := by
  rw [nilpotencyClass_def]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · intro n hn
    exact ⟨upperCentralSeries G, upperCentralSeries_isAscendingCentralSeries G, hn⟩
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← top_le_iff, ← hn]
    exact ascending_central_series_le_upper H hH n

open scoped Classical in
/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which the descending
central series reaches `⊥` in its `n`-th term. -/
@[to_additive /-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which the
descending central series reaches `⊥` in its `n`-th term. -/]
/-
**Subgroup.least_descending_central_series_length_eq_nilpotencyClass** 是 Mathlib
 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：least_descending_central_series_length_eq_nilpotencyClass : Nat.find ((nil
potent_iff_finite_descending_central_series G).mp hG) = Group.nilpotencyClass G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.nilpotent_iff_finite_descending_central_series`：nilpotent_iff_f
inite_descending_central_series : IsNilpotent G ↔ exists n : Nat, exists H : Nat
 -> Subgroup G, IsDescendingCentralSeries H ∧…
· 使用定理 `Subgroup.nilpotent_iff_finite_ascending_central_series`：nilpotent_iff_fi
nite_ascending_central_series : IsNilpotent G ↔ exists n : Nat, exists H : Nat -
> Subgroup G, IsAscendingCentralSeries H ∧ H…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.least_ascending_central_series_length_eq_nilpotencyClass`：least
_ascending_central_series_length_eq_nilpotencyClass : Nat.find ((nilpotent_iff_f
inite_ascending_central_series G).mp hG) = Group.nilpot…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Nat.find_mono`：find_mono [DecidablePred q] (h : forall n, q n -> p n) {h
p : exists n, p n} {hq : exists n, q n} : Nat.find hp <= Nat.find hq
· 使用定理 `Subgroup.is_descending_rev_series_of_is_ascending`：is_descending_rev_ser
ies_of_is_ascending {H : Nat -> Subgroup G} {n : Nat} (hn : H n = ⊤) (hasc : IsA
scendingCentralSeries H) : IsDescending…
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subgroup.is_ascending_rev_series_of_is_descending`：is_ascending_rev_seri
es_of_is_descending {H : Nat -> Subgroup G} {n : Nat} (hn : H n = ⊥) (hdesc : Is
DescendingCentralSeries H) : IsAscendin…
-/
theorem least_descending_central_series_length_eq_nilpotencyClass :
    Nat.find ((nilpotent_iff_finite_descending_central_series G).mp hG) =
    Group.nilpotencyClass G := by
  rw [← least_ascending_central_series_length_eq_nilpotencyClass]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    refine ⟨fun m => H (n - m), is_descending_rev_series_of_is_ascending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    refine ⟨fun m => H (n - m), is_ascending_rev_series_of_is_descending G hn hH, ?_⟩
    dsimp only
    rw [tsub_self]
    exact hH.1

open scoped Classical in
/-- The nilpotency class of a nilpotent `G` is equal to the length of the lower central series. -/
@[to_additive /-- The nilpotency class of a nilpotent `G` is equal to the length of the lower
central series. -/]
/-
**Subgroup.lowerCentralSeries_length_eq_nilpotencyClass** 是 Mathlib 中的一个定理，位于命名空
间 `Subgroup`。
形式化陈述：lowerCentralSeries_length_eq_nilpotencyClass : Nat.find (nilpotent_iff_low
erCentralSeries.mp hG) = Group.nilpotencyClass (G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `Subgroup.nilpotent_iff_finite_descending_central_series`：nilpotent_iff_f
inite_descending_central_series : IsNilpotent G ↔ exists n : Nat, exists H : Nat
 -> Subgroup G, IsDescendingCentralSeries H ∧…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.least_descending_central_series_length_eq_nilpotencyClass`：leas
t_descending_central_series_length_eq_nilpotencyClass : Nat.find ((nilpotent_iff
_finite_descending_central_series G).mp hG) = Group.nilp…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Nat.find_mono`：find_mono [DecidablePred q] (h : forall n, q n -> p n) {h
p : exists n, p n} {hq : exists n, q n} : Nat.find hp <= Nat.find hq
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Subgroup.descending_central_series_ge_lower`：∀ {G : Type u_1} [inst : Gr
oup G] (H : ℕ → Subgroup G),   Subgroup.IsDescendingCentralSeries H → ∀ (n : ℕ),
 ⊤.lowerCentralSeries n ≤ H n
· 使用定理 `Subgroup.lowerCentralSeries_isDescendingCentralSeries`：lowerCentralSerie
s_isDescendingCentralSeries : IsDescendingCentralSeries (G
-/
theorem lowerCentralSeries_length_eq_nilpotencyClass :
    Nat.find (nilpotent_iff_lowerCentralSeries.mp hG) = Group.nilpotencyClass (G := G) := by
  rw [← least_descending_central_series_length_eq_nilpotencyClass]
  refine le_antisymm (Nat.find_mono ?_) (Nat.find_mono ?_)
  · rintro n ⟨H, ⟨hH, hn⟩⟩
    rw [← le_bot_iff, ← hn]
    exact descending_central_series_ge_lower H hH n
  · rintro n h
    exact ⟨lowerCentralSeries ⊤, ⟨lowerCentralSeries_isDescendingCentralSeries, h⟩⟩

@[to_additive (attr := simp)]
/-
**Subgroup.lowerCentralSeries_nilpotencyClass** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：lowerCentralSeries_nilpotencyClass : lowerCentralSeries (⊤ : Subgroup G) (
Group.nilpotencyClass G) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.lowerCentralSeries_length_eq_nilpotencyClass`：lowerCentralSerie
s_length_eq_nilpotencyClass : Nat.find (nilpotent_iff_lowerCentralSeries.mp hG) 
= Group.nilpotencyClass (G
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem lowerCentralSeries_nilpotencyClass :
    lowerCentralSeries (⊤ : Subgroup G) (Group.nilpotencyClass G) = ⊥ := by
  classical
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  exact Nat.find_spec (nilpotent_iff_lowerCentralSeries.mp hG)

@[to_additive]
/-
**Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le** 是 Mathlib 中的一个定理，位
于命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_eq_bot_iff_nilpotencyClass_le {n : Nat} : lowerCentralS
eries (⊤ : Subgroup G) n = ⊥ ↔ Group.nilpotencyClass G <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.lowerCentralSeries_length_eq_nilpotencyClass`：lowerCentralSerie
s_length_eq_nilpotencyClass : Nat.find (nilpotent_iff_lowerCentralSeries.mp hG) 
= Group.nilpotencyClass (G
· 使用引理 `Nat.find_le`：find_le {h : exists n, p n} (hn : p n) : Nat.find h <= n
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Subgroup.lowerCentralSeries_nilpotencyClass`：lowerCentralSeries_nilpoten
cyClass : lowerCentralSeries (⊤ : Subgroup G) (Group.nilpotencyClass G) = ⊥
· 使用定理 `Subgroup.lowerCentralSeries_antitone`：lowerCentralSeries_antitone : Anti
tone S.lowerCentralSeries
-/
theorem lowerCentralSeries_eq_bot_iff_nilpotencyClass_le {n : ℕ} :
    lowerCentralSeries (⊤ : Subgroup G) n = ⊥ ↔ Group.nilpotencyClass G ≤ n := by
  classical
  constructor
  · intro h
    rw [← lowerCentralSeries_length_eq_nilpotencyClass]
    exact Nat.find_le h
  · intro h
    rw [eq_bot_iff, ← lowerCentralSeries_nilpotencyClass]
    exact lowerCentralSeries_antitone _ h

omit [IsNilpotent G] in
@[to_additive]
/-
**Subgroup.lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top** 是 Mathlib 中
的一个定理，位于命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top {n : Nat} : lowerC
entralSeries (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le`：upperCentralS
eries_eq_top_iff_nilpotencyClass_le {n : Nat} : upperCentralSeries G n = ⊤ ↔ Gro
up.nilpotencyClass G <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le`：lowerCentralS
eries_eq_bot_iff_nilpotencyClass_le {n : Nat} : lowerCentralSeries (⊤ : Subgroup
 G) n = ⊥ ↔ Group.nilpotencyClass G <= n
-/
theorem lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top {n : ℕ} :
    lowerCentralSeries (G := G) ⊤ n = ⊥ ↔ upperCentralSeries G n = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : IsNilpotent G := nilpotent_iff_lowerCentralSeries.mpr ⟨n, h⟩
    rwa [upperCentralSeries_eq_top_iff_nilpotencyClass_le,
      ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  · have : IsNilpotent G := ⟨n, h⟩
    rwa [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
      ← upperCentralSeries_eq_top_iff_nilpotencyClass_le]

end Subgroup

end Classical

namespace Subgroup

@[to_additive]
/-
**Subgroup.lowerCentralSeries_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_le_self (S : Subgroup G) (n : Nat) : S.lowerCentralSeri
es n <= S
参数：S : Subgroup G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.lowerCentralSeries_antitone`：lowerCentralSeries_antitone : Anti
tone S.lowerCentralSeries
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem lowerCentralSeries_le_self (S : Subgroup G) (n : ℕ) :
    S.lowerCentralSeries n ≤ S := by
  simpa using S.lowerCentralSeries_antitone (Nat.zero_le n)

@[to_additive]
/-
**Subgroup.lowerCentralSeries_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_mono (n : Nat) : Monotone (fun S : Subgroup G => S.lowe
rCentralSeries n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.commutator_mono`：commutator_mono (h₁ : H₁ <= K₁) (h₂ : H₂ <= K₂
) : ⁅H₁, H₂⁆ <= ⁅K₁, K₂⁆
-/
theorem lowerCentralSeries_mono (n : ℕ) :
    Monotone (fun S : Subgroup G => S.lowerCentralSeries n) := by
  induction n with
  | zero => intro S T h; simpa
  | succ d hd => intro S T h; simp only [lowerCentralSeries_succ]; exact commutator_mono (hd h) h

@[to_additive (attr := deprecated "Use `top_subtype_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-27"))]
/-
**Subgroup.lowerCentralSeries_map_subtype_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
`。
形式化陈述：lowerCentralSeries_map_subtype_le (H : Subgroup G) (n : Nat) : ((⊤ : Subgr
oup H).lowerCentralSeries n).map H.subtype <= lowerCentralSeries ⊤ n
参数：H : Subgroup G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.top_subtype_lowerCentralSeries`：top_subtype_lowerCentralSeries 
(H : Subgroup G) (n : Nat) : (lowerCentralSeries ⊤ n).map H.subtype = H.lowerCen
tralSeries n
· 使用定理 `Subgroup.lowerCentralSeries_mono`：lowerCentralSeries_mono (n : Nat) : Mo
notone (fun S : Subgroup G => S.lowerCentralSeries n)
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem lowerCentralSeries_map_subtype_le (H : Subgroup G) (n : ℕ) :
    ((⊤ : Subgroup H).lowerCentralSeries n).map H.subtype ≤ lowerCentralSeries ⊤ n := by
  rw [top_subtype_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive (attr := deprecated "Use `map_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-28"))]
/-
**Subgroup.lowerCentralSeries.map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.lowerCentr
alSeries`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {K : Type u_2} [inst_1 : Group K] (f : G
 →* K) (n : ℕ),   Subgroup.map f (⊤.lowerCentralSeries n) ≤ ⊤.lowerCentralSeries
 n
参数：f : G →* K；n : ℕ；⊤.lowerCentralSeries n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_lowerCentralSeries`：map_lowerCentralSeries {K : Type*} [Gro
up K] (f : G ->* K) (n : Nat) : (S.lowerCentralSeries n).map f = (S.map f).lower
CentralSeries n
· 使用定理 `Subgroup.lowerCentralSeries_mono`：lowerCentralSeries_mono (n : Nat) : Mo
notone (fun S : Subgroup G => S.lowerCentralSeries n)
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem lowerCentralSeries.map {K : Type*} [Group K] (f : G →* K) (n : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries n).map f ≤ (⊤ : Subgroup K).lowerCentralSeries n := by
  rw [map_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive]
/-
**Subgroup.lowerCentralSeries_normal** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_normal (S : Subgroup G) [S.Normal] (n : Nat) : (S.lower
CentralSeries n).Normal
参数：S : Subgroup G；n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.lowerCentralSeries_succ`：lowerCentralSeries_succ (n : Nat) : S.
lowerCentralSeries (n + 1) = ⁅S.lowerCentralSeries n, S⁆
-/
instance lowerCentralSeries_normal (S : Subgroup G) [S.Normal] (n : ℕ) :
    (S.lowerCentralSeries n).Normal := by
  induction n with
  | zero => simpa
  | succ n _ => rw [lowerCentralSeries_succ]; infer_instance

/-- A subgroup of a nilpotent group is nilpotent. -/
@[to_additive /-- An additive subgroup of a nilpotent group is nilpotent. -/]
/-
**Subgroup.isNilpotent** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：isNilpotent (H : Subgroup G) [hG : IsNilpotent G] : IsNilpotent H
参数：H : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_subtype_inj`：map_subtype_inj {H : Subgroup G} {K L : Subgro
up H} : K.map H.subtype = L.map H.subtype ↔ K = L
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
· 使用定理 `Subgroup.top_subtype_lowerCentralSeries`：top_subtype_lowerCentralSeries 
(H : Subgroup G) (n : Nat) : (lowerCentralSeries ⊤ n).map H.subtype = H.lowerCen
tralSeries n
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Subgroup.lowerCentralSeries_mono`：lowerCentralSeries_mono (n : Nat) : Mo
notone (fun S : Subgroup G => S.lowerCentralSeries n)
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
A subgroup of a nilpotent group is nilpotent.
-/
instance isNilpotent (H : Subgroup G) [hG : IsNilpotent G] : IsNilpotent H := by
  rw [nilpotent_iff_lowerCentralSeries] at *
  rcases hG with ⟨n, hG⟩
  refine ⟨n, ?_⟩
  rw [← map_subtype_inj, map_bot, top_subtype_lowerCentralSeries, eq_bot_iff, ← hG]
  exact H.lowerCentralSeries_mono n le_top

/-- The nilpotency class of a subgroup is less or equal to the nilpotency class of the group. -/
@[to_additive /-- The nilpotency class of an additive subgroup is less or equal to the nilpotency
/-
**Subgroup.of** 是 Mathlib 中的一个类，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nilpotency class of a subgroup is less or equal to the nilpotency class of t
he group.
-/
class of the additive group. -/]
/-
**Subgroup.nilpotencyClass_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：nilpotencyClass_le (H : Subgroup G) [hG : IsNilpotent G] : Group.nilpotenc
yClass H <= Group.nilpotencyClass G
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.lowerCentralSeries_length_eq_nilpotencyClass`：lowerCentralSerie
s_length_eq_nilpotencyClass : Nat.find (nilpotent_iff_lowerCentralSeries.mp hG) 
= Group.nilpotencyClass (G
· 使用引理 `Nat.find_mono`：find_mono [DecidablePred q] (h : forall n, q n -> p n) {h
p : exists n, p n} {hq : exists n, q n} : Nat.find hp <= Nat.find hq
· 使用定理 `Subgroup.map_subtype_inj`：map_subtype_inj {H : Subgroup G} {K L : Subgro
up H} : K.map H.subtype = L.map H.subtype ↔ K = L
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
· 使用定理 `Subgroup.top_subtype_lowerCentralSeries`：top_subtype_lowerCentralSeries 
(H : Subgroup G) (n : Nat) : (lowerCentralSeries ⊤ n).map H.subtype = H.lowerCen
tralSeries n
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Subgroup.lowerCentralSeries_mono`：lowerCentralSeries_mono (n : Nat) : Mo
notone (fun S : Subgroup G => S.lowerCentralSeries n)
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem nilpotencyClass_le (H : Subgroup G) [hG : IsNilpotent G] :
    Group.nilpotencyClass H ≤ Group.nilpotencyClass G := by
  repeat rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  classical apply Nat.find_mono
  intro n hG
  rw [← map_subtype_inj, map_bot, top_subtype_lowerCentralSeries, eq_bot_iff, ← hG]
  exact H.lowerCentralSeries_mono n le_top

@[to_additive]
/-
**Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `S
ubgroup`。
形式化陈述：isNilpotent_of_lowerCentralSeries_eq_bot {S : Subgroup G} {n : Nat} (h : S
.lowerCentralSeries n = ⊥) : Group.IsNilpotent S
参数：h : S.lowerCentralSeries n = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.isNilpotent_iff_lowerCentralSeries`：isNilpotent_iff_lowerCentra
lSeries : Group.IsNilpotent S ↔ exists n, S.lowerCentralSeries n = ⊥
-/
theorem isNilpotent_of_lowerCentralSeries_eq_bot {S : Subgroup G} {n : ℕ}
    (h : S.lowerCentralSeries n = ⊥) : Group.IsNilpotent S :=
  (isNilpotent_iff_lowerCentralSeries S).mpr ⟨n, h⟩

@[to_additive]
/-
**Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le** 是 Mathlib 中的一个定理，位于
命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_eq_bot_of_nilpotencyClass_le {S : Subgroup G} [Group.Is
Nilpotent S] {n : Nat} (hn : Group.nilpotencyClass S <= n) : S.lowerCentralSerie
s n = ⊥
参数：hn : Group.nilpotencyClass S <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.top_subtype_lowerCentralSeries`：top_subtype_lowerCentralSeries 
(H : Subgroup G) (n : Nat) : (lowerCentralSeries ⊤ n).map H.subtype = H.lowerCen
tralSeries n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le`：lowerCentralS
eries_eq_bot_iff_nilpotencyClass_le {n : Nat} : lowerCentralSeries (⊤ : Subgroup
 G) n = ⊥ ↔ Group.nilpotencyClass G <= n
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
-/
theorem lowerCentralSeries_eq_bot_of_nilpotencyClass_le {S : Subgroup G}
    [Group.IsNilpotent S] {n : ℕ} (hn : Group.nilpotencyClass S ≤ n) :
    S.lowerCentralSeries n = ⊥ := by
  rw [← top_subtype_lowerCentralSeries,
    lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hn, map_bot]

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) _root_.Group.isNilpotent_of_subsingleton [Subsingleton G] :
    IsNilpotent G :=
  nilpotent_iff_lowerCentralSeries.2 ⟨0, Subsingleton.elim ⊤ ⊥⟩

@[to_additive]
/-
**Subgroup.upperCentralSeries.map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.upperCentr
alSeries`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Type u_2} [inst_1 : Group H] {f : G
 →* H},   Function.Surjective ⇑f → ∀ (n : ℕ), Subgroup.map f (Subgroup.upperCent
ralSeries G n) ≤ Subgroup.upperCentralSeries H n
参数：n : ℕ；Subgroup.upperCentralSeries G n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_bot`：map_bot (f : G ->* N) : (⊥ : Subgroup G).map f = ⊥
· 使用定理 `map_commutatorElement`：map_commutatorElement : (f ⁅g₁, g₂⁆ : G') = ⁅f g₁
, f g₂⁆
· 使用定理 `Subgroup.mem_map_of_mem`：mem_map_of_mem (f : G ->* N) {K : Subgroup G} {
x : G} (hx : x in K) : f x in K.map f
-/
theorem upperCentralSeries.map {H : Type*} [Group H] {f : G →* H} (h : Function.Surjective f)
    (n : ℕ) : Subgroup.map f (upperCentralSeries G n) ≤ upperCentralSeries H n := by
  induction n with
  | zero => simp
  | succ d hd =>
    rintro _ ⟨x, hx : x ∈ upperCentralSeries G d.succ, rfl⟩ y'
    rcases h y' with ⟨y, rfl⟩
    simpa using! hd (mem_map_of_mem f (hx y))

@[to_additive]
/-
**Subgroup.lowerCentralSeries_succ_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：lowerCentralSeries_succ_eq_bot (S : Subgroup G) {n : Nat} (h : S.lowerCent
ralSeries n <= center G) : S.lowerCentralSeries (n + 1) = ⊥
参数：S : Subgroup G；h : S.lowerCentralSeries n <= center G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.lowerCentralSeries_succ`：lowerCentralSeries_succ (n : Nat) : S.
lowerCentralSeries (n + 1) = ⁅S.lowerCentralSeries n, S⁆
· 使用定理 `Subgroup.commutator_def`：commutator_def (H₁ H₂ : Subgroup G) : ⁅H₁, H₂⁆ 
= closure { g | exists g₁ in H₁, exists g₂ in H₂, ⁅g₁, g₂⁆ = g }
· 使用定理 `Subgroup.closure_eq_bot_iff`：closure_eq_bot_iff : closure k = ⊥ ↔ k subs
eteq {1}
· 使用定理 `Set.subset_singleton_iff`：subset_singleton_iff {α : Type*} {s : Set α} {
x : α} : s subseteq {x} ↔ forall y in s, y = x
· 使用定理 `commutatorElement_def`：commutatorElement_def {G : Type*} [Group G] (g₁ g
₂ : G) : ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
-/
theorem lowerCentralSeries_succ_eq_bot (S : Subgroup G) {n : ℕ}
    (h : S.lowerCentralSeries n ≤ center G) :
    S.lowerCentralSeries (n + 1) = ⊥ := by
  rw [lowerCentralSeries_succ, commutator_def, closure_eq_bot_iff, Set.subset_singleton_iff]
  rintro x ⟨y, hy1, z, _, rfl⟩
  rw [commutatorElement_def, mul_assoc, ← mul_inv_rev, mul_inv_eq_one, eq_comm]
  exact mem_center_iff.mp (h hy1) z

/-- The preimage of a nilpotent group is nilpotent if the kernel of the homomorphism is contained
in the center. -/
@[to_additive /-- The preimage of a nilpotent additive group is nilpotent if the kernel of the
homomorphism is contained in the center. -/]
/-
**Subgroup.isNilpotent_of_ker_le_center** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isNilpotent_of_ker_le_center {H : Type*} [Group H] (f : G ->* H) (hf1 : f.
ker <= center G) [IsNilpotent H] : IsNilpotent G
参数：f : G ->* H；hf1 : f.ker <= center G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.lowerCentralSeries_succ_eq_bot`：lowerCentralSeries_succ_eq_bot 
(S : Subgroup G) {n : Nat} (h : S.lowerCentralSeries n <= center G) : S.lowerCen
tralSeries (n + 1) = ⊥
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Subgroup.map_eq_bot_iff`：map_eq_bot_iff {f : G ->* N} : H.map f = ⊥ ↔ H 
<= f.ker
· 使用定理 `Subgroup.map_lowerCentralSeries`：map_lowerCentralSeries {K : Type*} [Gro
up K] (f : G ->* K) (n : Nat) : (S.lowerCentralSeries n).map f = (S.map f).lower
CentralSeries n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Subgroup.lowerCentralSeries_mono`：lowerCentralSeries_mono (n : Nat) : Mo
notone (fun S : Subgroup G => S.lowerCentralSeries n)
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isNilpotent_of_ker_le_center {H : Type*} [Group H] (f : G →* H) (hf1 : f.ker ≤ center G)
    [IsNilpotent H] : IsNilpotent G := by
  rw [nilpotent_iff_lowerCentralSeries]
  rcases nilpotent_iff_lowerCentralSeries.mp ‹_› with ⟨n, hn⟩
  refine ⟨n + 1, lowerCentralSeries_succ_eq_bot ⊤
    (le_trans ((Subgroup.map_eq_bot_iff _).mp ?_) hf1)⟩
  rw [map_lowerCentralSeries, ← le_bot_iff]
  exact hn ▸ Subgroup.lowerCentralSeries_mono n le_top

end Subgroup

namespace Group

@[to_additive]
/-
**Group.nilpotencyClass_le_of_ker_le_center** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：nilpotencyClass_le_of_ker_le_center {H : Type*} [Group H] (f : G ->* H) (h
f1 : f.ker <= center G) [IsNilpotent H] : Group.nilpotencyClass G <= Group.nilpo
tencyClass H + 1
参数：f : G ->* H；hf1 : f.ker <= center G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isNilpotent_of_ker_le_center`：isNilpotent_of_ker_le_center {H :
 Type*} [Group H] (f : G ->* H) (hf1 : f.ker <= center G) [IsNilpotent H] : IsNi
lpotent G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.lowerCentralSeries_length_eq_nilpotencyClass`：lowerCentralSerie
s_length_eq_nilpotencyClass : Nat.find (nilpotent_iff_lowerCentralSeries.mp hG) 
= Group.nilpotencyClass (G
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `Subgroup.lowerCentralSeries_succ_eq_bot`：lowerCentralSeries_succ_eq_bot 
(S : Subgroup G) {n : Nat} (h : S.lowerCentralSeries n <= center G) : S.lowerCen
tralSeries (n + 1) = ⊥
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Subgroup.map_eq_bot_iff`：map_eq_bot_iff {f : G ->* N} : H.map f = ⊥ ↔ H 
<= f.ker
· 使用定理 `Subgroup.map_lowerCentralSeries`：map_lowerCentralSeries {K : Type*} [Gro
up K] (f : G ->* K) (n : Nat) : (S.lowerCentralSeries n).map f = (S.map f).lower
CentralSeries n
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Subgroup.lowerCentralSeries_nilpotencyClass`：lowerCentralSeries_nilpoten
cyClass : lowerCentralSeries (⊤ : Subgroup G) (Group.nilpotencyClass G) = ⊥
· 使用定理 `Subgroup.lowerCentralSeries_mono`：lowerCentralSeries_mono (n : Nat) : Mo
notone (fun S : Subgroup G => S.lowerCentralSeries n)
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem nilpotencyClass_le_of_ker_le_center {H : Type*} [Group H] (f : G →* H)
    (hf1 : f.ker ≤ center G) [IsNilpotent H] :
    Group.nilpotencyClass G ≤ Group.nilpotencyClass H + 1 := by
  have : IsNilpotent G := isNilpotent_of_ker_le_center f hf1
  rw [← lowerCentralSeries_length_eq_nilpotencyClass]
  classical apply Nat.find_min'
  refine lowerCentralSeries_succ_eq_bot ⊤
    (le_trans ((Subgroup.map_eq_bot_iff _).mp ?_) hf1)
  rw [map_lowerCentralSeries, ← le_bot_iff,
    ← lowerCentralSeries_nilpotencyClass (G := H)]
  exact Subgroup.lowerCentralSeries_mono _ le_top

/-- The range of a surjective homomorphism from a nilpotent group is nilpotent. -/
@[to_additive /-- The range of a surjective homomorphism from a nilpotent additive group is
nilpotent. -/]
/-
**Group.nilpotent_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：nilpotent_of_surjective {G' : Type*} [Group G'] [h : IsNilpotent G] (f : G
 ->* G') (hf : Function.Surjective f) : IsNilpotent G'
参数：f : G ->* G'；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `MonoidHom.range_eq_top_of_surjective`：range_eq_top_of_surjective {N} [Gr
oup N] (f : G ->* N) (hf : Function.Surjective f) : f.range = (⊤ : Subgroup N)
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.upperCentralSeries.map`：∀ {G : Type u_1} [inst : Group G] {H : 
Type u_2} [inst_1 : Group H] {f : G →* H},   Function.Surjective ⇑f → ∀ (n : ℕ),
 Subgroup.map f (Subg…
-/
theorem nilpotent_of_surjective {G' : Type*} [Group G'] [h : IsNilpotent G] (f : G →* G')
    (hf : Function.Surjective f) : IsNilpotent G' := by
  rcases h with ⟨n, hn⟩
  use n
  apply eq_top_iff.mpr
  calc
    ⊤ = f.range := symm (f.range_eq_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (upperCentralSeries G n) := by rw [hn]
    _ ≤ upperCentralSeries G' n := upperCentralSeries.map hf n

/-- The nilpotency class of the range of a surjective homomorphism from a
nilpotent group is less or equal the nilpotency class of the domain. -/
@[to_additive /-- The nilpotency class of the range of a surjective homomorphism from a
nilpotent additive group is less or equal the nilpotency class of the domain. -/]
/-
**Group.nilpotencyClass_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：nilpotencyClass_le_of_surjective {G' : Type*} [Group G'] (f : G ->* G') (h
f : Function.Surjective f) [h : IsNilpotent G] : Group.nilpotencyClass G' <= Gro
up.nilpotencyClass G
参数：f : G ->* G'；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.nilpotent_of_surjective`：nilpotent_of_surjective {G' : Type*} [Gro
up G'] [h : IsNilpotent G] (f : G ->* G') (hf : Function.Surjective f) : IsNilpo
tent G'
· 使用定理 `Group.IsNilpotent.nilpotent`：∀ (G : Type u_2) [inst : Group G] [Group.Is
Nilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.nilpotencyClass_def`：Group.nilpotencyClass_def : Group.nilpotencyC
lass G = Nat.find (IsNilpotent.nilpotent G)
· 使用引理 `Nat.find_mono`：find_mono [DecidablePred q] (h : forall n, q n -> p n) {h
p : exists n, p n} {hq : exists n, q n} : Nat.find hp <= Nat.find hq
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `MonoidHom.range_eq_top_of_surjective`：range_eq_top_of_surjective {N} [Gr
oup N] (f : G ->* N) (hf : Function.Surjective f) : f.range = (⊤ : Subgroup N)
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.upperCentralSeries.map`：∀ {G : Type u_1} [inst : Group G] {H : 
Type u_2} [inst_1 : Group H] {f : G →* H},   Function.Surjective ⇑f → ∀ (n : ℕ),
 Subgroup.map f (Subg…
-/
theorem nilpotencyClass_le_of_surjective {G' : Type*} [Group G'] (f : G →* G')
    (hf : Function.Surjective f) [h : IsNilpotent G] :
    Group.nilpotencyClass G' ≤ Group.nilpotencyClass G := by
  have := nilpotent_of_surjective _ hf
  rw [nilpotencyClass_def, nilpotencyClass_def]
  classical apply Nat.find_mono
  intro n hn
  rw [eq_top_iff]
  calc
    ⊤ = f.range := symm (f.range_eq_top_of_surjective hf)
    _ = Subgroup.map f ⊤ := MonoidHom.range_eq_map _
    _ = Subgroup.map f (upperCentralSeries G n) := by rw [hn]
    _ ≤ upperCentralSeries G' n := upperCentralSeries.map hf n

/-- Nilpotency respects isomorphisms. -/
@[to_additive /-- Nilpotency respects isomorphisms. -/]
/-
**Group.nilpotent_of_mulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：nilpotent_of_mulEquiv {G' : Type*} [Group G'] [_h : IsNilpotent G] (f : G 
≃* G') : IsNilpotent G'
参数：f : G ≃* G'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.nilpotent_of_surjective`：nilpotent_of_surjective {G' : Type*} [Gro
up G'] [h : IsNilpotent G] (f : G ->* G') (hf : Function.Surjective f) : IsNilpo
tent G'
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e

--- 原说明 ---
Nilpotency respects isomorphisms.
-/
theorem nilpotent_of_mulEquiv {G' : Type*} [Group G'] [_h : IsNilpotent G] (f : G ≃* G') :
    IsNilpotent G' :=
  nilpotent_of_surjective f.toMonoidHom (MulEquiv.surjective f)

/-- A quotient of a nilpotent group is nilpotent. -/
@[to_additive /-- A quotient of a nilpotent group is nilpotent. -/]
/-
**Group.nilpotent_quotient_of_nilpotent** 是 Mathlib 中的一个实例，位于命名空间 `Group`。
形式化陈述：nilpotent_quotient_of_nilpotent (H : Subgroup G) [H.Normal] [_h : IsNilpot
ent G] : IsNilpotent (G ⧸ H)
参数：H : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.nilpotent_of_surjective`：nilpotent_of_surjective {G' : Type*} [Gro
up G'] [h : IsNilpotent G] (f : G ->* G') (hf : Function.Surjective f) : IsNilpo
tent G'
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s

--- 原说明 ---
A quotient of a nilpotent group is nilpotent.
-/
instance nilpotent_quotient_of_nilpotent (H : Subgroup G) [H.Normal] [_h : IsNilpotent G] :
    IsNilpotent (G ⧸ H) :=
  nilpotent_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective

/-- The nilpotency class of a quotient of `G` is less or equal the nilpotency class of `G`. -/
@[to_additive /-- The nilpotency class of a quotient of `G` is less or equal the nilpotency class
of `G`. -/]
/-
**Group.nilpotencyClass_quotient_le** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：nilpotencyClass_quotient_le (H : Subgroup G) [H.Normal] [_h : IsNilpotent 
G] : Group.nilpotencyClass (G ⧸ H) <= Group.nilpotencyClass G
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.nilpotencyClass_le_of_surjective`：nilpotencyClass_le_of_surjective
 {G' : Type*} [Group G'] (f : G ->* G') (hf : Function.Surjective f) [h : IsNilp
otent G] : Group.nilpotencyC…
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
theorem nilpotencyClass_quotient_le (H : Subgroup G) [H.Normal] [_h : IsNilpotent G] :
    Group.nilpotencyClass (G ⧸ H) ≤ Group.nilpotencyClass G :=
  nilpotencyClass_le_of_surjective (QuotientGroup.mk' H) QuotientGroup.mk_surjective

end Group

open QuotientGroup

namespace Subgroup

-- This technical lemma helps with rewriting the subgroup, which occurs in indices
@[to_additive]
/-
**Subgroup.comap_center_subst** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem comap_center_subst {H₁ H₂ : Subgroup G} [Normal H₁] [Normal H₂] (h : H₁ = H₂) :
    comap (mk' H₁) (center (G ⧸ H₁)) = comap (mk' H₂) (center (G ⧸ H₂)) := by subst h; rfl

@[to_additive]
/-
**Subgroup.comap_upperCentralSeries_quotient_center** 是 Mathlib 中的一个定理，位于命名空间 `S
ubgroup`。
形式化陈述：comap_upperCentralSeries_quotient_center (n : Nat) : comap (mk' (center G)
) (upperCentralSeries (G ⧸ center G) n) = upperCentralSeries G n.succ
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.upperCentralSeries_one`：upperCentralSeries_one : upperCentralSe
ries G 1 = center G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subgroup.normal_of_characteristic`：∀ {G : Type u_1} [inst : Group G] (H 
: Subgroup G) [h : H.Characteristic], H.Normal
· 使用定理 `Subgroup.instCharacteristicUpperCentralSeries`：∀ (G : Type u_1) [inst : 
Group G] (n : ℕ), (Subgroup.upperCentralSeries G n).Characteristic
· 使用定理 `Subgroup.normal_comap`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} 
[inst_1 : Group N] {H : Subgroup N} [nH : H.Normal] (f : G →* N),   (Subgroup.co
map f H).No…
· 使用定理 `Subgroup.upperCentralSeriesStep_eq_comap_center`：upperCentralSeriesStep_
eq_comap_center : upperCentralSeriesStep N = Subgroup.comap (mk' N) (center (G ⧸
 N))
· 使用定理 `QuotientGroup.comap_comap_center`：comap_comap_center {H₁ : Subgroup G} [
H₁.Normal] {H₂ : Subgroup (G ⧸ H₁)} [H₂.Normal] : ((Subgroup.center ((G ⧸ H₁) ⧸ 
H₂)).comap (mk' H₂)).c…
· 使用定理 `_private.Mathlib.GroupTheory.Nilpotent.0.Subgroup.comap_center_subst`：∀ 
{G : Type u_1} [inst : Group G] {H₁ H₂ : Subgroup G} [inst_1 : H₁.Normal] [inst_
2 : H₂.Normal],   H₁ = H₂ →     Subgroup.comap (QuotientGr…
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
-/
theorem comap_upperCentralSeries_quotient_center (n : ℕ) :
    comap (mk' (center G)) (upperCentralSeries (G ⧸ center G) n) = upperCentralSeries G n.succ := by
  induction n with
  | zero =>
    simp only [upperCentralSeries_zero, MonoidHom.comap_bot, ker_mk',
      (upperCentralSeries_one G).symm]
  | succ n ih =>
    let Hn := upperCentralSeries (G ⧸ center G) n
    calc
      comap (mk' (center G)) (upperCentralSeriesStep Hn) =
          comap (mk' (center G)) (comap (mk' Hn) (center ((G ⧸ center G) ⧸ Hn))) := by
        rw [upperCentralSeriesStep_eq_comap_center]
      _ = comap (mk' (comap (mk' (center G)) Hn)) (center (G ⧸ comap (mk' (center G)) Hn)) :=
        QuotientGroup.comap_comap_center
      _ = comap (mk' (upperCentralSeries G n.succ)) (center (G ⧸ upperCentralSeries G n.succ)) :=
        (comap_center_subst ih)
      _ = upperCentralSeriesStep (upperCentralSeries G n.succ) :=
        symm (upperCentralSeriesStep_eq_comap_center _)

end Subgroup

namespace Group

@[to_additive]
/-
**Group.nilpotencyClass_zero_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：nilpotencyClass_zero_iff_subsingleton [IsNilpotent G] : Group.nilpotencyCl
ass G = 0 ↔ Subsingleton G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsNilpotent.nilpotent`：∀ (G : Type u_2) [inst : Group G] [Group.Is
Nilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.nilpotencyClass_def`：Group.nilpotencyClass_def : Group.nilpotencyC
lass G = Nat.find (IsNilpotent.nilpotent G)
· 使用定理 `Nat.find_eq_zero`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p 
n), Nat.find h = 0 ↔ p 0
· 使用定理 `Subgroup.upperCentralSeries_zero`：upperCentralSeries_zero : upperCentral
Series G 0 = ⊥
· 使用定理 `subsingleton_iff_bot_eq_top`：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ 
: α) ↔ Subsingleton α
· 使用定理 `Subgroup.subsingleton_iff`：subsingleton_iff : Subsingleton (Subgroup G) 
↔ Subsingleton G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nilpotencyClass_zero_iff_subsingleton [IsNilpotent G] :
    Group.nilpotencyClass G = 0 ↔ Subsingleton G := by
  classical
  rw [Group.nilpotencyClass_def, Nat.find_eq_zero, upperCentralSeries_zero,
    subsingleton_iff_bot_eq_top, Subgroup.subsingleton_iff]

/-- If the quotient by `center G` is nilpotent, then so is G. -/
@[to_additive /-- If the quotient by `center G` is nilpotent, then so is G. -/]
/-
**Group.of_quotient_center_nilpotent** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：of_quotient_center_nilpotent (h : IsNilpotent (G ⧸ center G)) : IsNilpoten
t G
参数：h : IsNilpotent (G ⧸ center G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsNilpotent.nilpotent`：∀ (G : Type u_2) [inst : Group G] [Group.Is
Nilpotent G], ∃ n, Subgroup.upperCentralSeries G n = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.comap_top`：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f =
 ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the quotient by `center G` is nilpotent, then so is G.
-/
theorem of_quotient_center_nilpotent (h : IsNilpotent (G ⧸ center G)) : IsNilpotent G := by
  obtain ⟨n, hn⟩ := h.nilpotent
  use n.succ
  simp [← comap_upperCentralSeries_quotient_center, hn]

/-- Quotienting the `center G` reduces the nilpotency class by 1. -/
@[to_additive /-- Quotienting the `center G` reduces the nilpotency class by 1. -/]
/-
**Group.nilpotencyClass_quotient_center** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：nilpotencyClass_quotient_center : Group.nilpotencyClass (G ⧸ center G) = G
roup.nilpotencyClass G - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le`：upperCentralS
eries_eq_top_iff_nilpotencyClass_le {n : Nat} : upperCentralSeries G n = ⊤ ↔ Gro
up.nilpotencyClass G <= n
· 使用定理 `Subgroup.comap_injective`：comap_injective {f : G ->* N} (h : Function.Su
rjective f) : Function.Injective (comap f)
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
· 使用定理 `Subgroup.comap_upperCentralSeries_quotient_center`：comap_upperCentralSer
ies_quotient_center (n : Nat) : comap (mk' (center G)) (upperCentralSeries (G ⧸ 
center G) n) = upperCentralSeries G n.s…
· 使用定理 `Subgroup.comap_top`：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f =
 ⊤
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.upperCentralSeries_nilpotencyClass`：upperCentralSeries_nilpoten
cyClass : upperCentralSeries G (Group.nilpotencyClass G) = ⊤
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Group.nilpotencyClass_le_of_ker_le_center`：nilpotencyClass_le_of_ker_le_
center {H : Type*} [Group H] (f : G ->* H) (hf1 : f.ker <= center G) [IsNilpoten
t H] : Group.nilpotencyClass G …
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Group.nilpotencyClass_of_not_nilpotent`：Group.nilpotencyClass_of_not_nil
potent (hG : ¬ IsNilpotent G) : Group.nilpotencyClass G = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Group.of_quotient_center_nilpotent`：of_quotient_center_nilpotent (h : Is
Nilpotent (G ⧸ center G)) : IsNilpotent G

--- 原说明 ---
Quotienting the `center G` reduces the nilpotency class by 1.
-/
theorem nilpotencyClass_quotient_center :
    Group.nilpotencyClass (G ⧸ center G) = Group.nilpotencyClass G - 1 := by
  by_cases hH : IsNilpotent G; swap
  · rw [nilpotencyClass_of_not_nilpotent hH, zero_tsub, nilpotencyClass_of_not_nilpotent]
    exact mt of_quotient_center_nilpotent hH
  generalize hn : Group.nilpotencyClass G = n
  rcases n with (rfl | n)
  · simp only [nilpotencyClass_zero_iff_subsingleton, zero_tsub] at *
    exact Quotient.instSubsingletonQuotient (leftRel (center G))
  · suffices Group.nilpotencyClass (G ⧸ center G) = n by simpa
    apply le_antisymm
    · apply upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp
      apply comap_injective (f := (mk' (center G))) Quot.mk_surjective
      rw [comap_upperCentralSeries_quotient_center, comap_top, Nat.succ_eq_add_one, ← hn]
      exact upperCentralSeries_nilpotencyClass
    · apply le_of_add_le_add_right
      calc
        n + 1 = Group.nilpotencyClass G := hn.symm
        _ ≤ Group.nilpotencyClass (G ⧸ center G) + 1 :=
          nilpotencyClass_le_of_ker_le_center _ (le_of_eq (ker_mk' _))

/-- The nilpotency class of a non-trivial group is one more than its quotient by the center -/
@[to_additive /-- The nilpotency class of a non-trivial additive group is one more than its quotient
by the center -/]
/-
**Group.nilpotencyClass_eq_quotient_center_plus_one** 是 Mathlib 中的一个定理，位于命名空间 `G
roup`。
形式化陈述：nilpotencyClass_eq_quotient_center_plus_one [hH : IsNilpotent G] [Nontrivi
al G] : Group.nilpotencyClass G = Group.nilpotencyClass (G ⧸ center G) + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.nilpotencyClass_quotient_center`：nilpotencyClass_quotient_center :
 Group.nilpotencyClass (G ⧸ center G) = Group.nilpotencyClass G - 1
· 使用定理 `false_of_nontrivial_of_subsingleton`：false_of_nontrivial_of_subsingleton
 (α : Type*) [Nontrivial α] [Subsingleton α] : False
· 使用定理 `Group.nilpotencyClass_zero_iff_subsingleton`：nilpotencyClass_zero_iff_su
bsingleton [IsNilpotent G] : Group.nilpotencyClass G = 0 ↔ Subsingleton G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nilpotencyClass_eq_quotient_center_plus_one [hH : IsNilpotent G] [Nontrivial G] :
    Group.nilpotencyClass G = Group.nilpotencyClass (G ⧸ center G) + 1 := by
  rw [nilpotencyClass_quotient_center]
  rcases h : Group.nilpotencyClass G with ⟨⟩
  · exfalso
    rw [nilpotencyClass_zero_iff_subsingleton] at h
    apply false_of_nontrivial_of_subsingleton G
  · simp

/-- A custom induction principle for nilpotent groups. The base case is a trivial group
(`subsingleton G`), and in the induction step, one can assume the hypothesis for
the group quotiented by its center. -/
@[to_additive (attr := elab_as_elim) /-- A custom induction principle for nilpotent additive groups.
The base case is a trivial group (`subsingleton G`), and in the induction step, one can assume the
hypothesis for the additive group quotiented by its center. -/]
/-
**Group.nilpotent_center_quotient_ind** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：nilpotent_center_quotient_ind {P : forall (G) [Group G] [IsNilpotent G], P
rop} (G : Type*) [Group G] [IsNilpotent G] (hbase : forall (G) [Group G] [Subsin
gleton G], P G) (hstep : forall (G) [Group G] [IsNilpotent G], P (G ⧸ center G) 
-> P G) : P G
参数：G；G : Type*；hbase : forall (G) [Group G] [Subsingleton G], P G；hstep : forall
 (G) [Group G] [IsNilpotent G], P (G ⧸ center G) -> P G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.isNilpotent_of_subsingleton`：∀ {G : Type u_1} [inst : Group G] [Su
bsingleton G], Group.IsNilpotent G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.nilpotencyClass_zero_iff_subsingleton`：nilpotencyClass_zero_iff_su
bsingleton [IsNilpotent G] : Group.nilpotencyClass G = 0 ↔ Subsingleton G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.nilpotencyClass_quotient_center`：nilpotencyClass_quotient_center :
 Group.nilpotencyClass (G ⧸ center G) = Group.nilpotencyClass G - 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nilpotent_center_quotient_ind {P : ∀ (G) [Group G] [IsNilpotent G], Prop}
    (G : Type*) [Group G] [IsNilpotent G]
    (hbase : ∀ (G) [Group G] [Subsingleton G], P G)
    (hstep : ∀ (G) [Group G] [IsNilpotent G], P (G ⧸ center G) → P G) : P G := by
  obtain ⟨n, h⟩ : ∃ n, Group.nilpotencyClass G = n := ⟨_, rfl⟩
  induction n generalizing G with
  | zero =>
    have := nilpotencyClass_zero_iff_subsingleton.mp h
    exact hbase _
  | succ n ih =>
    have hn : Group.nilpotencyClass (G ⧸ center G) = n := by
      simp [nilpotencyClass_quotient_center, h]
    exact hstep _ (ih _ hn)

end Group

-- todo: namespace `derivedSeries` and to_additivize.
/-
**Subgroup.derived_le_lower_central** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.derived_le_lower_central (n : Nat) : derivedSeries G n <= lowerCe
ntralSeries ⊤ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subgroup.commutator_mono`：commutator_mono (h₁ : H₁ <= K₁) (h₂ : H₂ <= K₂
) : ⁅H₁, H₂⁆ <= ⁅K₁, K₂⁆
-/
theorem Subgroup.derived_le_lower_central (n : ℕ) :
    derivedSeries G n ≤ lowerCentralSeries ⊤ n := by
  induction n with
  | zero => simp
  | succ i ih => apply commutator_mono ih; simp

@[to_additive]
/-
**Subgroup.upperCentralSeries_one_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.upperCentralSeries_one_eq_top_iff : upperCentralSeries G 1 = ⊤ ↔ 
IsMulCommutative G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.upperCentralSeries_one`：upperCentralSeries_one : upperCentralSe
ries G 1 = center G
· 使用定理 `Subgroup.center_eq_top_iff`：center_eq_top_iff : center G = ⊤ ↔ IsMulComm
utative G
-/
theorem Subgroup.upperCentralSeries_one_eq_top_iff :
    upperCentralSeries G 1 = ⊤ ↔ IsMulCommutative G := by
  rw [upperCentralSeries_one]
  exact Subgroup.center_eq_top_iff

@[to_additive]
/-
**Subgroup.lowerCentralSeries_one_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.lowerCentralSeries_one_eq_bot_iff : lowerCentralSeries (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top`：lowerC
entralSeries_eq_bot_iff_upperCentralSeries_eq_top {n : Nat} : lowerCentralSeries
 (G
· 使用定理 `Subgroup.upperCentralSeries_one_eq_top_iff`：Subgroup.upperCentralSeries_
one_eq_top_iff : upperCentralSeries G 1 = ⊤ ↔ IsMulCommutative G
-/
theorem Subgroup.lowerCentralSeries_one_eq_bot_iff :
    lowerCentralSeries (G := G) ⊤ 1 = ⊥ ↔ IsMulCommutative G := by
  rw [lowerCentralSeries_eq_bot_iff_upperCentralSeries_eq_top]
  exact upperCentralSeries_one_eq_top_iff

@[to_additive]
/-
**Group.IsNilpotent.nilpotencyClass_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.IsNilpotent.nilpotencyClass_le_one_iff [IsNilpotent G] : Group.nilpo
tencyClass G <= 1 ↔ IsMulCommutative G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le`：upperCentralS
eries_eq_top_iff_nilpotencyClass_le {n : Nat} : upperCentralSeries G n = ⊤ ↔ Gro
up.nilpotencyClass G <= n
· 使用定理 `Subgroup.upperCentralSeries_one_eq_top_iff`：Subgroup.upperCentralSeries_
one_eq_top_iff : upperCentralSeries G 1 = ⊤ ↔ IsMulCommutative G
-/
theorem Group.IsNilpotent.nilpotencyClass_le_one_iff [IsNilpotent G] :
    Group.nilpotencyClass G ≤ 1 ↔ IsMulCommutative G := by
  rw [← upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  exact upperCentralSeries_one_eq_top_iff

/-- Abelian groups are nilpotent. -/
@[to_additive /-- Abelian groups are nilpotent. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abelian groups are nilpotent.
-/
instance (priority := 100) CommGroup.isNilpotent {G : Type*} [CommGroup G] : IsNilpotent G := by
  use 1
  rw [upperCentralSeries_one]
  apply CommGroup.center_eq_top

/-- Abelian groups have nilpotency class at most one. -/
@[to_additive /-- Abelian groups have nilpotency class at most one. -/]
/-
**CommGroup.nilpotencyClass_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommGroup.nilpotencyClass_le_one {G : Type*} [CommGroup G] : Group.nilpote
ncyClass G <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le`：upperCentralS
eries_eq_top_iff_nilpotencyClass_le {n : Nat} : upperCentralSeries G n = ⊤ ↔ Gro
up.nilpotencyClass G <= n
· 使用定理 `CommGroup.isNilpotent`：∀ {G : Type u_2} [inst : CommGroup G], Group.IsNi
lpotent G
· 使用定理 `Subgroup.upperCentralSeries_one`：upperCentralSeries_one : upperCentralSe
ries G 1 = center G
· 使用定理 `CommGroup.center_eq_top`：∀ {G : Type u_2} [inst : CommGroup G], Subgroup
.center G = ⊤

--- 原说明 ---
Abelian groups have nilpotency class at most one.
-/
theorem CommGroup.nilpotencyClass_le_one {G : Type*} [CommGroup G] :
    Group.nilpotencyClass G ≤ 1 := by
  rw [← upperCentralSeries_eq_top_iff_nilpotencyClass_le, upperCentralSeries_one]
  apply CommGroup.center_eq_top

/-- Groups with nilpotency class at most one are abelian. -/
@[to_additive /-- Additive groups with nilpotency class at most one are abelian. -/,
  instance_reducible]
/-
**commGroupOfNilpotencyClass** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commGroupOfNilpotencyClass [IsNilpotent G] (h : Group.nilpotencyClass G <=
 1) : CommGroup G
参数：h : Group.nilpotencyClass G <= 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def commGroupOfNilpotencyClass [IsNilpotent G] (h : Group.nilpotencyClass G ≤ 1) : CommGroup G :=
  Group.commGroupOfCenterEqTop <| by
    rw [← upperCentralSeries_one]
    exact upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr h

namespace Subgroup

@[to_additive]
/-
**Subgroup.upperCentralSeries.eq_ge_of_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up.upperCentralSeries`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a b : ℕ},   a ≤ b →     Subgroup.upperC
entralSeries G a = Subgroup.upperCentralSeries G (a + 1) →       Subgroup.upperC
entralSeries G a = Subgroup.upperCentralSeries G b
参数：a + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
-/
lemma upperCentralSeries.eq_ge_of_eq_succ {a b : ℕ} (ab : a ≤ b)
    (hn : upperCentralSeries G a = upperCentralSeries G (a + 1)) :
    upperCentralSeries G a = upperCentralSeries G b := by
  refine Nat.le_induction rfl ?_ b ab
  grind only [eq_def, upperCentralSeriesAux.eq_def]

/-- If two different elements of the `upperCentralSeries` of a group `G` are equal, then
they are all equal, starting from the smaller index. -/
@[to_additive /-- If two different elements of the `upperCentralSeries` of an additive group `G`
are equal, then they are all equal, starting from the smaller index. -/]
/-
**Subgroup.upperCentralSeries.eq_ge_of_eq_gt** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
.upperCentralSeries`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a b c : ℕ},   a ≠ b →     a ≤ c →      
 Subgroup.upperCentralSeries G a = Subgroup.upperCentralSeries G b →         Sub
group.upperCentralSeries G a = Subgroup.upperCentralSeries G c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Subgroup.upperCentralSeries.eq_ge_of_eq_succ`：∀ {G : Type u_1} [inst : G
roup G] {a b : ℕ},   a ≤ b →     Subgroup.upperCentralSeries G a = Subgroup.uppe
rCentralSeries G (a + 1) →       S…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.upperCentralSeries_mono`：upperCentralSeries_mono : Monotone (up
perCentralSeries G)
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma upperCentralSeries.eq_ge_of_eq_gt {a b c : ℕ} (ab : a ≠ b) (ac : a ≤ c)
    (hn : upperCentralSeries G a = upperCentralSeries G b) :
    upperCentralSeries G a = upperCentralSeries G c := by
  wlog ab : a < b
  · grind
  refine eq_ge_of_eq_succ ac (le_antisymm ?_ ?_)
  · exact upperCentralSeries_mono _ <| Nat.le_succ ..
  · rw [hn]
    exact upperCentralSeries_mono _ (by grind)

@[to_additive]
/-
**Subgroup.upperCentralSeries.eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.upperCe
ntralSeries`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] [Group.IsNilpotent G] {a b : ℕ},   a ≠ b
 → Subgroup.upperCentralSeries G a = Subgroup.upperCentralSeries G b → Subgroup.
upperCentralSeries G a = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma upperCentralSeries.eq_top [IsNilpotent G] {a b : ℕ} (ab : a ≠ b)
    (hn : upperCentralSeries G a = upperCentralSeries G b) :
    upperCentralSeries G a = ⊤ := by
  grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent,
    upperCentralSeries_eq_top_iff_nilpotencyClass_le, eq_ge_of_eq_gt]

@[to_additive]
/-
**Subgroup.nilpotencyClass_le_of_upperCentralSeries_eq** 是 Mathlib 中的一个引理，位于命名空间
 `Subgroup`。
形式化陈述：nilpotencyClass_le_of_upperCentralSeries_eq {a b : Nat} (ab : a < b) (hn :
 upperCentralSeries G a = upperCentralSeries G b) : nilpotencyClass G <= a
参数：ab : a < b；hn : upperCentralSeries G a = upperCentralSeries G b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.nilpotencyClass_of_not_nilpotent`：Group.nilpotencyClass_of_not_nil
potent (hG : ¬ IsNilpotent G) : Group.nilpotencyClass G = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
lemma nilpotencyClass_le_of_upperCentralSeries_eq {a b : ℕ} (ab : a < b)
    (hn : upperCentralSeries G a = upperCentralSeries G b) :
    nilpotencyClass G ≤ a := by
  by_cases hG : IsNilpotent G
  · grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent, upperCentralSeries.eq_top,
      upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  · rw [nilpotencyClass_of_not_nilpotent hG]
    apply Nat.zero_le

variable (G) in
@[to_additive]
/-
**Subgroup.upperCentralSeries.StrictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.u
pperCentralSeries`。
形式化陈述：∀ (G : Type u_1) [inst : Group G], StrictMonoOn (Subgroup.upperCentralSeri
es G) (Set.Iic (Group.nilpotencyClass G))
参数：G : Type u_1；Subgroup.upperCentralSeries G；Set.Iic (Group.nilpotencyClass G)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Subgroup.upperCentralSeries_mono`：upperCentralSeries_mono : Monotone (up
perCentralSeries G)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.nilpotencyClass_of_not_nilpotent`：Group.nilpotencyClass_of_not_nil
potent (hG : ¬ IsNilpotent G) : Group.nilpotencyClass G = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bot_eq_zero`：⊥ = 0
· 使用定理 `Set.Iic_bot`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : OrderBot
 α], Set.Iic ⊥ = {⊥}
· 使用定理 `Set.strictMonoOn_singleton`：strictMonoOn_singleton : StrictMonoOn f {a}
-/
lemma upperCentralSeries.StrictMonoOn :
    StrictMonoOn (upperCentralSeries G) (Set.Iic (nilpotencyClass G)) := by
  by_cases hG : IsNilpotent G
  · intros a ha b hb ab
    simp only [Set.mem_Iic] at ha hb
    apply lt_of_le_of_ne
    · exact upperCentralSeries_mono _ ab.le
    · grind only [IsNilpotent.nilpotent', IsNilpotent.nilpotent, eq_top,
        upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  · rw [nilpotencyClass_of_not_nilpotent hG, ← Nat.bot_eq_zero, Set.Iic_bot]
    apply Set.strictMonoOn_singleton

@[to_additive]
/-
**Subgroup.upperCentralSeries.card_image_eq_of_le_nilpotencyClass** 是 Mathlib 中的
一个定理，位于命名空间 `Subgroup.upperCentralSeries`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {a : ℕ},   a ≤ Group.nilpotencyClass G →
 (Subgroup.upperCentralSeries G '' Set.Iic a).ncard = a + 1
参数：Subgroup.upperCentralSeries G '' Set.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ncard_eq_of_bijective`：ncard_eq_of_bijective {n : Nat} (f : forall i
, i < n -> α) (hf : forall a in s, exists i, exists h : i < n, f i h = a) (hf' :
 forall (i) (h …
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `Subgroup.upperCentralSeries.StrictMonoOn`：∀ (G : Type u_1) [inst : Group
 G], StrictMonoOn (Subgroup.upperCentralSeries G) (Set.Iic (Group.nilpotencyClas
s G))
-/
lemma upperCentralSeries.card_image_eq_of_le_nilpotencyClass {a : ℕ}
    (h2 : a ≤ nilpotencyClass G) :
    (upperCentralSeries G '' (Set.Iic a)).ncard = a + 1 := by
  refine Set.ncard_eq_of_bijective (fun _ => upperCentralSeries G ·) ?_ ?_ ?_
  · grind
  · grind
  · intros i j hi hj
    refine (upperCentralSeries.StrictMonoOn G).injOn ?_ ?_ <;> grind

end Subgroup

variable (G) in
@[to_additive]
/-
**Group.IsNilpotent.center_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.IsNilpotent.center_ne_bot [Nontrivial G] [IsNilpotent G] : center G 
!= ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.upperCentralSeries_one`：upperCentralSeries_one : upperCentralSe
ries G 1 = center G
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Subgroup.upperCentralSeries.eq_top`：∀ {G : Type u_1} [inst : Group G] [G
roup.IsNilpotent G] {a b : ℕ},   a ≠ b → Subgroup.upperCentralSeries G a = Subgr
oup.upperCentralSeries G…
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.instNontrivial`：∀ {G : Type u_1} [inst : Group G] [Nontrivial G
], Nontrivial (Subgroup G)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Group.IsNilpotent.center_ne_bot [Nontrivial G] [IsNilpotent G] : center G ≠ ⊥ :=
  .symm <| by simpa using mt (upperCentralSeries.eq_top zero_ne_one) <| by simp

section Prod

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

@[to_additive]
/-
**Subgroup.lowerCentralSeries_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.lowerCentralSeries_prod (S₁ : Subgroup G₁) (S₂ : Subgroup G₂) (n 
: Nat) : (S₁.prod S₂).lowerCentralSeries n = (S₁.lowerCentralSeries n).prod (S₂.
lowerCentralSeries n)
参数：S₁ : Subgroup G₁；S₂ : Subgroup G₂；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.commutator_prod_prod`：commutator_prod_prod (K₁ K₂ : Subgroup G'
) : ⁅H₁.prod K₁, H₂.prod K₂⁆ = ⁅H₁, H₂⁆.prod ⁅K₁, K₂⁆
-/
theorem Subgroup.lowerCentralSeries_prod (S₁ : Subgroup G₁) (S₂ : Subgroup G₂) (n : ℕ) :
    (S₁.prod S₂).lowerCentralSeries n =
      (S₁.lowerCentralSeries n).prod (S₂.lowerCentralSeries n) := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_prod_prod]

/-- The ⊤-specialization of `lowerCentralSeries_prod`. -/
@[to_additive]
/-
**Subgroup.top_lowerCentralSeries_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.top_lowerCentralSeries_prod (n : Nat) : (⊤ : Subgroup (G₁ × G₂)).
lowerCentralSeries n = ((⊤ : Subgroup G₁).lowerCentralSeries n).prod ((⊤ : Subgr
oup G₂).lowerCentralSeries n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.lowerCentralSeries_prod`：Subgroup.lowerCentralSeries_prod (S₁ :
 Subgroup G₁) (S₂ : Subgroup G₂) (n : Nat) : (S₁.prod S₂).lowerCentralSeries n =
 (S₁.lowerCentralSerie…
· 使用定理 `Subgroup.top_prod_top`：top_prod_top : (⊤ : Subgroup G).prod (⊤ : Subgrou
p N) = ⊤

--- 原说明 ---
The ⊤-specialization of `lowerCentralSeries_prod`.
-/
theorem Subgroup.top_lowerCentralSeries_prod (n : ℕ) :
    (⊤ : Subgroup (G₁ × G₂)).lowerCentralSeries n =
      ((⊤ : Subgroup G₁).lowerCentralSeries n).prod ((⊤ : Subgroup G₂).lowerCentralSeries n) := by
  rw [← lowerCentralSeries_prod, top_prod_top]

/-- Products of nilpotent groups are nilpotent. -/
@[to_additive /-- Products of nilpotent groups are nilpotent. -/]
/-
**Group.isNilpotent_prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Group.isNilpotent_prod [IsNilpotent G₁] [IsNilpotent G₂] : IsNilpotent (G₁
 × G₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `Subgroup.top_lowerCentralSeries_prod`：Subgroup.top_lowerCentralSeries_pr
od (n : Nat) : (⊤ : Subgroup (G₁ × G₂)).lowerCentralSeries n = ((⊤ : Subgroup G₁
).lowerCentralSeries n).pr…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le`：lowerCentralS
eries_eq_bot_iff_nilpotencyClass_le {n : Nat} : lowerCentralSeries (⊤ : Subgroup
 G) n = ⊥ ↔ Group.nilpotencyClass G <= n
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Subgroup.bot_prod_bot`：bot_prod_bot : (⊥ : Subgroup G).prod (⊥ : Subgrou
p N) = ⊥

--- 原说明 ---
Products of nilpotent groups are nilpotent.
-/
instance Group.isNilpotent_prod [IsNilpotent G₁] [IsNilpotent G₂] : IsNilpotent (G₁ × G₂) := by
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨max (Group.nilpotencyClass G₁) (Group.nilpotencyClass G₂), ?_⟩
  rw [top_lowerCentralSeries_prod,
    lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_left _ _),
    lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (le_max_right _ _), bot_prod_bot]

/-- The nilpotency class of a product is the max of the nilpotency classes of the factors. -/
@[to_additive /-- The nilpotency class of a product is the max of the nilpotency classes of the
factors. -/]
/-
**Group.nilpotencyClass_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.nilpotencyClass_prod [IsNilpotent G₁] [IsNilpotent G₂] : Group.nilpo
tencyClass (G₁ × G₂) = max (Group.nilpotencyClass G₁) (Group.nilpotencyClass G₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.top_lowerCentralSeries_prod`：Subgroup.top_lowerCentralSeries_pr
od (n : Nat) : (⊤ : Subgroup (G₁ × G₂)).lowerCentralSeries n = ((⊤ : Subgroup G₁
).lowerCentralSeries n).pr…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Group.nilpotencyClass_prod [IsNilpotent G₁] [IsNilpotent G₂] :
    Group.nilpotencyClass (G₁ × G₂) =
    max (Group.nilpotencyClass G₁) (Group.nilpotencyClass G₂) := by
  refine eq_of_forall_ge_iff fun k => ?_
  simp only [max_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    top_lowerCentralSeries_prod, prod_eq_bot_iff]

end Prod

section BoundedPi

-- First the case of infinite products with bounded nilpotency class
variable {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]

@[to_additive]
/-
**Subgroup.lowerCentralSeries_pi_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.lowerCentralSeries_pi_le (Ss : forall i, Subgroup (Gs i)) (n : Na
t) : (Subgroup.pi Set.univ Ss).lowerCentralSeries n <= Subgroup.pi Set.univ fun 
i => (Ss i).lowerCentralSeries n
参数：Ss : forall i, Subgroup (Gs i)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Subgroup.commutator_mono`：commutator_mono (h₁ : H₁ <= K₁) (h₂ : H₂ <= K₂
) : ⁅H₁, H₂⁆ <= ⁅K₁, K₂⁆
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subgroup.commutator_pi_pi_le`：commutator_pi_pi_le {η : Type*} {Gs : η ->
 Type*} [forall i, Group (Gs i)] (H K : forall i, Subgroup (Gs i)) : ⁅Subgroup.p
i Set.univ H, Subg…
-/
theorem Subgroup.lowerCentralSeries_pi_le (Ss : ∀ i, Subgroup (Gs i)) (n : ℕ) :
    (Subgroup.pi Set.univ Ss).lowerCentralSeries n ≤ Subgroup.pi Set.univ
      fun i => (Ss i).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [lowerCentralSeries_succ]
    grw [commutator_mono ih le_rfl, commutator_pi_pi_le]

/-- The ⊤-specialization of `lowerCentralSeries_pi_le`. -/
@[to_additive]
/-
**Subgroup.top_lowerCentralSeries_pi_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.top_lowerCentralSeries_pi_le (n : Nat) : (⊤ : Subgroup (forall i,
 Gs i)).lowerCentralSeries n <= Subgroup.pi Set.univ fun i => (⊤ : Subgroup (Gs 
i)).lowerCentralSeries n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.pi_top`：pi_top (I : Set η) : (pi I fun i => (⊤ : Subgroup (f i)
)) = ⊤
· 使用定理 `Subgroup.lowerCentralSeries_pi_le`：Subgroup.lowerCentralSeries_pi_le (Ss
 : forall i, Subgroup (Gs i)) (n : Nat) : (Subgroup.pi Set.univ Ss).lowerCentral
Series n <= Subgroup.pi…

--- 原说明 ---
The ⊤-specialization of `lowerCentralSeries_pi_le`.
-/
theorem Subgroup.top_lowerCentralSeries_pi_le (n : ℕ) :
    (⊤ : Subgroup (∀ i, Gs i)).lowerCentralSeries n ≤ Subgroup.pi Set.univ
      fun i => (⊤ : Subgroup (Gs i)).lowerCentralSeries n := by
  rw [← pi_top (I := Set.univ)]
  exact lowerCentralSeries_pi_le _ _

/-- Products of nilpotent groups are nilpotent if their nilpotency class is bounded. -/
@[to_additive /-- Products of nilpotent additive groups are nilpotent if their nilpotency class is
bounded. -/]
/-
**Group.isNilpotent_pi_of_bounded_class** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.isNilpotent_pi_of_bounded_class [forall i, IsNilpotent (Gs i)] (n : 
Nat) (h : forall i, Group.nilpotencyClass (Gs i) <= n) : IsNilpotent (forall i, 
Gs i)
参数：Gs i；n : Nat；h : forall i, Group.nilpotencyClass (Gs i) <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.top_lowerCentralSeries_pi_le`：Subgroup.top_lowerCentralSeries_p
i_le (n : Nat) : (⊤ : Subgroup (forall i, Gs i)).lowerCentralSeries n <= Subgrou
p.pi Set.univ fun i => (⊤ :…
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Subgroup.pi_eq_bot_iff`：pi_eq_bot_iff (H : forall i, Subgroup (f i)) : p
i Set.univ H = ⊥ ↔ forall i, H i = ⊥
· 使用定理 `Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le`：lowerCentralS
eries_eq_bot_iff_nilpotencyClass_le {n : Nat} : lowerCentralSeries (⊤ : Subgroup
 G) n = ⊥ ↔ Group.nilpotencyClass G <= n
-/
theorem Group.isNilpotent_pi_of_bounded_class [∀ i, IsNilpotent (Gs i)] (n : ℕ)
    (h : ∀ i, Group.nilpotencyClass (Gs i) ≤ n) : IsNilpotent (∀ i, Gs i) := by
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨n, eq_bot_iff.mpr <| (top_lowerCentralSeries_pi_le _).trans ?_⟩
  rw [le_bot_iff, pi_eq_bot_iff]
  exact fun i => lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr (h i)

end BoundedPi

section FinitePi

-- Now for finite products
variable {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]

@[to_additive]
/-
**Subgroup.lowerCentralSeries_pi_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.lowerCentralSeries_pi_of_finite [Finite η] (Ss : forall i, Subgro
up (Gs i)) (n : Nat) : (Subgroup.pi Set.univ Ss).lowerCentralSeries n = Subgroup
.pi Set.univ fun i => (Ss i).lowerCentralSeries n
参数：Ss : forall i, Subgroup (Gs i)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.commutator_pi_pi_of_finite`：commutator_pi_pi_of_finite {η : Typ
e*} [Finite η] {Gs : η -> Type*} [forall i, Group (Gs i)] (H K : forall i, Subgr
oup (Gs i)) : ⁅Subgroup.p…
-/
theorem Subgroup.lowerCentralSeries_pi_of_finite [Finite η] (Ss : ∀ i, Subgroup (Gs i)) (n : ℕ) :
    (Subgroup.pi Set.univ Ss).lowerCentralSeries n = Subgroup.pi Set.univ
      fun i => (Ss i).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_pi_pi_of_finite]

/-- The ⊤-specialization of `lowerCentralSeries_pi_of_finite`. -/
@[to_additive]
/-
**Subgroup.top_lowerCentralSeries_pi_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subgroup.top_lowerCentralSeries_pi_of_finite [Finite η] (n : Nat) : (⊤ : S
ubgroup (forall i, Gs i)).lowerCentralSeries n = Subgroup.pi Set.univ fun i => (
⊤ : Subgroup (Gs i)).lowerCentralSeries n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.pi_top`：pi_top (I : Set η) : (pi I fun i => (⊤ : Subgroup (f i)
)) = ⊤
· 使用定理 `Subgroup.lowerCentralSeries_pi_of_finite`：Subgroup.lowerCentralSeries_pi
_of_finite [Finite η] (Ss : forall i, Subgroup (Gs i)) (n : Nat) : (Subgroup.pi 
Set.univ Ss).lowerCentralSerie…

--- 原说明 ---
The ⊤-specialization of `lowerCentralSeries_pi_of_finite`.
-/
theorem Subgroup.top_lowerCentralSeries_pi_of_finite [Finite η] (n : ℕ) :
    (⊤ : Subgroup (∀ i, Gs i)).lowerCentralSeries n = Subgroup.pi Set.univ
      fun i => (⊤ : Subgroup (Gs i)).lowerCentralSeries n := by
  rw [← pi_top (I := Set.univ), lowerCentralSeries_pi_of_finite]

/-- n-ary products of nilpotent groups are nilpotent. -/
@[to_additive /-- n-ary products of nilpotent groups are nilpotent. -/]
/-
**Group.isNilpotent_pi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Group.isNilpotent_pi [Finite η] [forall i, IsNilpotent (Gs i)] : IsNilpote
nt (forall i, Gs i)
参数：Gs i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.nilpotent_iff_lowerCentralSeries`：nilpotent_iff_lowerCentralSer
ies : IsNilpotent G ↔ exists n, lowerCentralSeries (⊤ : Subgroup G) n = ⊥
· 使用定理 `Subgroup.top_lowerCentralSeries_pi_of_finite`：Subgroup.top_lowerCentralS
eries_pi_of_finite [Finite η] (n : Nat) : (⊤ : Subgroup (forall i, Gs i)).lowerC
entralSeries n = Subgroup.pi Set.u…
· 使用定理 `Subgroup.pi_eq_bot_iff`：pi_eq_bot_iff (H : forall i, Subgroup (f i)) : p
i Set.univ H = ⊥ ↔ forall i, H i = ⊥
· 使用定理 `Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le`：lowerCentralS
eries_eq_bot_iff_nilpotencyClass_le {n : Nat} : lowerCentralSeries (⊤ : Subgroup
 G) n = ⊥ ↔ Group.nilpotencyClass G <= n
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
n-ary products of nilpotent groups are nilpotent.
-/
instance Group.isNilpotent_pi [Finite η] [∀ i, IsNilpotent (Gs i)] : IsNilpotent (∀ i, Gs i) := by
  cases nonempty_fintype η
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨Finset.univ.sup fun i => Group.nilpotencyClass (Gs i), ?_⟩
  rw [top_lowerCentralSeries_pi_of_finite, pi_eq_bot_iff]
  intro i
  rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  exact Finset.le_sup (f := fun i => Group.nilpotencyClass (Gs i)) (Finset.mem_univ i)

/-- The nilpotency class of an n-ary product is the sup of the nilpotency classes of the factors. -/
@[to_additive /-- The nilpotency class of an n-ary product is the sup of the nilpotency classes of
the factors. -/]
/-
**Group.nilpotencyClass_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.nilpotencyClass_pi [Fintype η] [forall i, IsNilpotent (Gs i)] : Grou
p.nilpotencyClass (forall i, Gs i) = Finset.univ.sup fun i => Group.nilpotencyCl
ass (Gs i)
参数：Gs i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.top_lowerCentralSeries_pi_of_finite`：Subgroup.top_lowerCentralS
eries_pi_of_finite [Finite η] (n : Nat) : (⊤ : Subgroup (forall i, Gs i)).lowerC
entralSeries n = Subgroup.pi Set.u…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Group.nilpotencyClass_pi [Fintype η] [∀ i, IsNilpotent (Gs i)] :
    Group.nilpotencyClass (∀ i, Gs i) = Finset.univ.sup fun i => Group.nilpotencyClass (Gs i) := by
  apply eq_of_forall_ge_iff
  intro k
  simp only [Finset.sup_le_iff, ← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    top_lowerCentralSeries_pi_of_finite, pi_eq_bot_iff, Finset.mem_univ, true_imp_iff]

end FinitePi

/-- A nilpotent subgroup is solvable -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nilpotent subgroup is solvable
-/
instance (priority := 100) IsNilpotent.to_isSolvable [h : IsNilpotent G] : Group.IsSolvable G := by
  obtain ⟨n, hn⟩ := nilpotent_iff_lowerCentralSeries.1 h
  use n
  rw [eq_bot_iff, ← hn]
  exact derived_le_lower_central n
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSimpleGroup G] [IsNilpotent G] : CommGroup G :=
  ⟨IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSimpleGroup G] [IsNilpotent G] : IsCyclic G :=
  inferInstance

namespace Group

/-
**Group.nilpotencyClass_le_one_of_isSimple_of_isNilpotent** 是 Mathlib 中的一个引理，位于命
名空间 `Group`。
形式化陈述：nilpotencyClass_le_one_of_isSimple_of_isNilpotent [IsSimpleGroup G] [IsNil
potent G] : nilpotencyClass G <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommGroup.nilpotencyClass_le_one`：CommGroup.nilpotencyClass_le_one {G : 
Type*} [CommGroup G] : Group.nilpotencyClass G <= 1
-/
lemma nilpotencyClass_le_one_of_isSimple_of_isNilpotent [IsSimpleGroup G] [IsNilpotent G] :
    nilpotencyClass G ≤ 1 :=
  CommGroup.nilpotencyClass_le_one
/-
**Group.normalizerCondition_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：normalizerCondition_of_isNilpotent [h : IsNilpotent G] : NormalizerConditi
on G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `normalizerCondition_iff_only_full_group_self_normalizing`：∀ {G : Type u_
1} [inst : Group G], NormalizerCondition G ↔ ∀ (H : Subgroup G), Subgroup.normal
izer ↑H = H → H = ⊤
· 使用定理 `Group.nilpotent_center_quotient_ind`：nilpotent_center_quotient_ind {P : 
forall (G) [Group G] [IsNilpotent G], Prop} (G : Type*) [Group G] [IsNilpotent G
] (hbase : forall (G) [Gr…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.center_le_normalizer`：center_le_normalizer (s : Set G) : center
 G <= normalizer s
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
· 使用定理 `Subgroup.comap_injective`：comap_injective {f : G ->* N} (h : Function.Su
rjective f) : Function.Injective (comap f)
· 使用定理 `Subgroup.comap_normalizer_eq_of_surjective`：comap_normalizer_eq_of_surje
ctive (H : Subgroup G) {f : N ->* G} (hf : Function.Surjective f) : (normalizer 
H).comap f = normalizer (H.comap…
· 使用定理 `Subgroup.comap_map_eq_self`：comap_map_eq_self {f : G ->* N} {H : Subgrou
p G} (h : f.ker <= H) : comap f (map f H) = H
· 使用定理 `Subgroup.map_injective_of_ker_le`：map_injective_of_ker_le {H K : Subgrou
p G} (hH : f.ker <= H) (hK : f.ker <= K) (hf : map f H = map f K) : H = K
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Subgroup.map_top_of_surjective`：map_top_of_surjective (f : G ->* N) (h :
 Function.Surjective f) : Subgroup.map f ⊤ = ⊤
-/
theorem normalizerCondition_of_isNilpotent [h : IsNilpotent G] : NormalizerCondition G := by
  -- roughly based on https://groupprops.subwiki.org/wiki/Nilpotent_implies_normalizer_condition
  rw [normalizerCondition_iff_only_full_group_self_normalizing]
  apply @nilpotent_center_quotient_ind _ G _ _ <;> clear! G
  · intro G _ _ H _
    exact @Subsingleton.elim _ Unique.instSubsingleton _ _
  · intro G _ _ ih H hH
    have hch : center G ≤ H := Subgroup.center_le_normalizer H |>.trans (le_of_eq hH)
    have hkh : (mk' (center G)).ker ≤ H := by simpa using hch
    have hsur : Function.Surjective (mk' (center G)) := Quot.mk_surjective
    let H' := H.map (mk' (center G))
    have hH' : normalizer H' = H' := by
      apply comap_injective hsur
      rw [comap_normalizer_eq_of_surjective _ hsur, comap_map_eq_self hkh]
      exact hH
    apply map_injective_of_ker_le (mk' (center G)) hkh le_top
    exact (ih H' hH').trans (symm (map_top_of_surjective _ hsur))

end Group

end WithGroup

section WithFiniteGroup

open Group Fintype

variable {G : Type*} [hG : Group G]

/-- A p-group is nilpotent -/
/-
**IsPGroup.isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPGroup.isNilpotent [Finite G] {p : Nat} [hp : Fact (Nat.Prime p)] (h : I
sPGroup p G) : IsNilpotent G
参数：Nat.Prime p；h : IsPGroup p G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_subsingleton_or_nontrivial`：induction_subsingleton_or_n
ontrivial {P : Type* -> Prop} (α) [Finite α] (hbase : forall (α) [Finite α] [Sub
singleton α], P α) (hstep : foral…
· 使用定理 `Group.isNilpotent_of_subsingleton`：∀ {G : Type u_1} [inst : Group G] [Su
bsingleton G], Group.IsNilpotent G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.card_eq_card_quotient_mul_card_subgroup`：card_eq_card_quotient_
mul_card_subgroup (s : Subgroup α) : Nat.card α = Nat.card (α ⧸ s) * Nat.card s
· 使用定理 `lt_mul_of_one_lt_right`：lt_mul_of_one_lt_right [PosMulStrictMono α] (ha 
: 0 < a) (h : 1 < b) : a < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Group.fg_of_finite`：∀ {G : Type u_3} [inst : Group G] [Finite G], Group.
FG G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.one_lt_card_iff_ne_bot`：one_lt_card_iff_ne_bot [Finite H] : 1 <
 Nat.card H ↔ H != ⊥
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `IsPGroup.bot_lt_center`：bot_lt_center [Nontrivial G] [Finite G] : ⊥ < Su
bgroup.center G
· 使用定理 `IsPGroup.to_quotient`：to_quotient (H : Subgroup G) [H.Normal] : IsPGroup
 p (G ⧸ H)
· 使用定理 `Group.of_quotient_center_nilpotent`：of_quotient_center_nilpotent (h : Is
Nilpotent (G ⧸ center G)) : IsNilpotent G

--- 原说明 ---
A p-group is nilpotent
-/
theorem IsPGroup.isNilpotent [Finite G] {p : ℕ} [hp : Fact (Nat.Prime p)] (h : IsPGroup p G) :
    IsNilpotent G := by
  induction G using Finite.induction_subsingleton_or_nontrivial generalizing hG with
  | hbase => infer_instance
  | hstep G ih =>
    have hcq : Nat.card (G ⧸ center G) < Nat.card G := by
      rw [card_eq_card_quotient_mul_card_subgroup (center G)]
      apply lt_mul_of_one_lt_right Nat.card_pos
      exact (Subgroup.one_lt_card_iff_ne_bot _).mpr (ne_of_gt h.bot_lt_center)
    have hnq : IsNilpotent (G ⧸ center G) := ih _ hcq (h.to_quotient (center G))
    exact of_quotient_center_nilpotent hnq

variable [Finite G]

/-- If a finite group is the direct product of its Sylow groups, it is nilpotent -/
/-
**Group.isNilpotent_of_product_of_sylow_group** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.isNilpotent_of_product_of_sylow_group (e : (forall p : (Nat.card G).
primeFactors, forall P : Sylow p G, (↑P : Subgroup G)) ≃* G) : IsNilpotent G
参数：e : (forall p : (Nat.card G).primeFactors, forall P : Sylow p G, (↑P : Subgro
up G)) ≃* G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsPGroup.isNilpotent`：IsPGroup.isNilpotent [Finite G] {p : Nat} [hp : Fa
ct (Nat.Prime p)] (h : IsPGroup p G) : IsNilpotent G
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Sylow.isPGroup'`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] (self : Sylow
 p G), IsPGroup p ↥↑self
· 使用定理 `Group.nilpotent_of_mulEquiv`：nilpotent_of_mulEquiv {G' : Type*} [Group G
'] [_h : IsNilpotent G] (f : G ≃* G') : IsNilpotent G'
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A

--- 原说明 ---
If a finite group is the direct product of its Sylow groups, it is nilpotent
-/
theorem Group.isNilpotent_of_product_of_sylow_group
    (e : (∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G, (↑P : Subgroup G)) ≃* G) :
    IsNilpotent G := by
  let ps := (Nat.card G).primeFactors
  have : ∀ (p : ps) (P : Sylow p G), IsNilpotent (↑P : Subgroup G) := by
    intro p P
    have : Fact (Nat.Prime ↑p) := Fact.mk <| Nat.prime_of_mem_primeFactors p.2
    exact P.isPGroup'.isNilpotent
  exact nilpotent_of_mulEquiv e

/-- A finite group is nilpotent iff the normalizer condition holds, and iff all maximal groups are
normal and iff all Sylow groups are normal and iff the group is the direct product of its Sylow
groups. -/
/-
**Group.isNilpotent_of_finite_tfae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Group.isNilpotent_of_finite_tfae : List.TFAE [IsNilpotent G, NormalizerCon
dition G, forall H : Subgroup G, IsCoatom H -> H.Normal, forall (p : Nat) (_hp :
 Fact p.Prime) (P : Sylow p G), (↑P : Subgroup G).Normal, Nonempty ((forall p : 
(Nat.card G).primeFactors, forall P : Sylow p G, (↑P : Subgroup G)) ≃* G)]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.normalizerCondition_of_isNilpotent`：normalizerCondition_of_isNilpo
tent [h : IsNilpotent G] : NormalizerCondition G
· 使用定理 `Subgroup.NormalizerCondition.normal_of_coatom`：∀ {G : Type u_1} [inst : 
Group G] (H : Subgroup G), NormalizerCondition G → IsCoatom H → H.Normal
· 使用定理 `Sylow.normal_of_all_max_subgroups_normal`：normal_of_all_max_subgroups_no
rmal [Finite G] (hnc : forall H : Subgroup G, IsCoatom H -> H.Normal) {p : Nat} 
[Fact p.Prime] [Finite (Sylow …
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A
· 使用定理 `Group.isNilpotent_of_product_of_sylow_group`：Group.isNilpotent_of_produc
t_of_sylow_group (e : (forall p : (Nat.card G).primeFactors, forall P : Sylow p 
G, (↑P : Subgroup G)) ≃* G) : IsN…
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)

--- 原说明 ---
A finite group is nilpotent iff the normalizer condition holds, and iff all maxi
mal groups are
normal and iff all Sylow groups are normal and iff the group is the direct produ
ct of its Sylow
groups.
-/
theorem Group.isNilpotent_of_finite_tfae :
    List.TFAE
      [IsNilpotent G, NormalizerCondition G, ∀ H : Subgroup G, IsCoatom H → H.Normal,
        ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G), (↑P : Subgroup G).Normal,
        Nonempty
          ((∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G, (↑P : Subgroup G)) ≃* G)] := by
  tfae_have 1 → 2 := @normalizerCondition_of_isNilpotent _ _
  tfae_have 2 → 3
  | h, H => NormalizerCondition.normal_of_coatom H h
  tfae_have 3 → 4
  | h, p, _, P => Sylow.normal_of_all_max_subgroups_normal h _
  tfae_have 4 → 5
  | h => Nonempty.intro (Sylow.directProductOfNormal fun {p hp hP} => h p hp hP)
  tfae_have 5 → 1
  | ⟨e⟩ => isNilpotent_of_product_of_sylow_group e
  tfae_finish
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNilpotent G] {p : ℕ} [Fact p.Prime] {P : Sylow p G} : P.Normal :=
  isNilpotent_of_finite_tfae.out 0 3 rfl rfl |>.mp ‹_› p ‹_› P

end WithFiniteGroup

open Group

@[deprecated (since := "2026-03-25")] alias upperCentralSeriesStep := upperCentralSeriesStep
@[deprecated (since := "2026-03-25")] alias mem_upperCentralSeriesStep := mem_upperCentralSeriesStep
@[deprecated (since := "2026-03-25")] alias upperCentralSeriesStep_eq_comap_center :=
  upperCentralSeriesStep_eq_comap_center
@[deprecated (since := "2026-03-25")] alias upperCentralSeriesAux := upperCentralSeriesAux
@[deprecated (since := "2026-03-25")] alias upperCentralSeries := upperCentralSeries
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_zero := upperCentralSeries_zero
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_one := upperCentralSeries_one
@[deprecated (since := "2026-03-25")] alias mem_upperCentralSeries_succ_iff :=
  mem_upperCentralSeries_succ_iff
@[deprecated (since := "2026-03-25")] alias comap_upperCentralSeries := comap_upperCentralSeries
@[deprecated (since := "2026-03-25")] alias IsAscendingCentralSeries := IsAscendingCentralSeries
@[deprecated (since := "2026-03-25")] alias IsDescendingCentralSeries := IsDescendingCentralSeries
@[deprecated (since := "2026-03-25")] alias ascending_central_series_le_upper :=
  ascending_central_series_le_upper
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_isAscendingCentralSeries :=
  upperCentralSeries_isAscendingCentralSeries
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_mono := upperCentralSeries_mono
@[deprecated (since := "2026-03-25")] alias nilpotent_iff_finite_ascending_central_series :=
  nilpotent_iff_finite_ascending_central_series
@[deprecated (since := "2026-03-25")] alias is_descending_rev_series_of_is_ascending :=
  is_descending_rev_series_of_is_ascending
@[deprecated (since := "2026-03-25")] alias is_ascending_rev_series_of_is_descending :=
  is_ascending_rev_series_of_is_descending
@[deprecated (since := "2026-03-25")] alias nilpotent_iff_finite_descending_central_series :=
  nilpotent_iff_finite_descending_central_series
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries := lowerCentralSeries
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_zero := lowerCentralSeries_zero
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_one := top_lowerCentralSeries_one
@[deprecated (since := "2026-03-25")] alias mem_lowerCentralSeries_succ_iff :=
  mem_lowerCentralSeries_succ_iff
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_succ := lowerCentralSeries_succ
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_antitone :=
  lowerCentralSeries_antitone
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_isDescendingCentralSeries :=
  lowerCentralSeries_isDescendingCentralSeries
@[deprecated (since := "2026-03-25")] alias descending_central_series_ge_lower :=
  descending_central_series_ge_lower
@[deprecated (since := "2026-03-25")] alias nilpotent_iff_lowerCentralSeries :=
  nilpotent_iff_lowerCentralSeries
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_nilpotencyClass :=
  upperCentralSeries_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias upperCentralSeries_eq_top_iff_nilpotencyClass_le :=
  upperCentralSeries_eq_top_iff_nilpotencyClass_le
@[deprecated (since := "2026-03-25")]
alias least_ascending_central_series_length_eq_nilpotencyClass :=
  least_ascending_central_series_length_eq_nilpotencyClass
@[deprecated (since := "2026-03-25")]
alias least_descending_central_series_length_eq_nilpotencyClass :=
  least_descending_central_series_length_eq_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_length_eq_nilpotencyClass :=
  lowerCentralSeries_length_eq_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_nilpotencyClass :=
  lowerCentralSeries_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_eq_bot_iff_nilpotencyClass_le :=
  lowerCentralSeries_eq_bot_iff_nilpotencyClass_le
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_map_subtype_le :=
  lowerCentralSeries_map_subtype_le
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.map := upperCentralSeries.map
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries.map := lowerCentralSeries.map
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_succ_eq_bot :=
  lowerCentralSeries_succ_eq_bot
@[deprecated (since := "2026-03-25")] alias isNilpotent_of_ker_le_center :=
  isNilpotent_of_ker_le_center
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_le_of_ker_le_center :=
  nilpotencyClass_le_of_ker_le_center
@[deprecated (since := "2026-03-25")] alias nilpotent_of_surjective := nilpotent_of_surjective
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_le_of_surjective :=
  nilpotencyClass_le_of_surjective
@[deprecated (since := "2026-03-25")] alias nilpotent_of_mulEquiv := nilpotent_of_mulEquiv
@[deprecated (since := "2026-03-25")] alias nilpotent_quotient_of_nilpotent :=
  nilpotent_quotient_of_nilpotent
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_quotient_le :=
  nilpotencyClass_quotient_le
@[deprecated (since := "2026-03-25")] alias comap_upperCentralSeries_quotient_center :=
  comap_upperCentralSeries_quotient_center
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_zero_iff_subsingleton :=
  nilpotencyClass_zero_iff_subsingleton
@[deprecated (since := "2026-03-25")] alias of_quotient_center_nilpotent :=
  of_quotient_center_nilpotent
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_quotient_center :=
  nilpotencyClass_quotient_center
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_eq_quotient_center_plus_one :=
  nilpotencyClass_eq_quotient_center_plus_one
@[deprecated (since := "2026-03-25")] alias nilpotent_center_quotient_ind :=
  nilpotent_center_quotient_ind
@[deprecated (since := "2026-03-25")] alias derived_le_lower_central := derived_le_lower_central
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.eq_ge_of_eq_succ :=
  upperCentralSeries.eq_ge_of_eq_succ
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.eq_ge_of_eq_gt :=
  upperCentralSeries.eq_ge_of_eq_gt
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.eq_top := upperCentralSeries.eq_top
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_le_of_upperCentralSeries_eq :=
  nilpotencyClass_le_of_upperCentralSeries_eq
@[deprecated (since := "2026-03-25")] alias upperCentralSeries.StrictMonoOn :=
  upperCentralSeries.StrictMonoOn
@[deprecated (since := "2026-03-25")]
alias upperCentralSeries.card_image_eq_of_le_nilpotencyClass :=
  upperCentralSeries.card_image_eq_of_le_nilpotencyClass
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_prod := lowerCentralSeries_prod
@[deprecated (since := "2026-03-25")] alias isNilpotent_prod := isNilpotent_prod
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_prod := nilpotencyClass_prod
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_pi_le := lowerCentralSeries_pi_le
@[deprecated (since := "2026-03-25")] alias isNilpotent_pi_of_bounded_class :=
  isNilpotent_pi_of_bounded_class
@[deprecated (since := "2026-03-25")] alias lowerCentralSeries_pi_of_finite :=
  lowerCentralSeries_pi_of_finite
@[deprecated (since := "2026-03-25")] alias isNilpotent_pi := isNilpotent_pi
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_pi := nilpotencyClass_pi
@[deprecated (since := "2026-03-25")] alias nilpotencyClass_le_one_of_isSimple_of_isNilpotent :=
  nilpotencyClass_le_one_of_isSimple_of_isNilpotent
@[deprecated (since := "2026-03-25")] alias normalizerCondition_of_isNilpotent :=
  normalizerCondition_of_isNilpotent
@[deprecated (since := "2026-03-25")] alias isNilpotent_of_product_of_sylow_group :=
  isNilpotent_of_product_of_sylow_group
@[deprecated (since := "2026-03-25")] alias isNilpotent_of_finite_tfae := isNilpotent_of_finite_tfae

