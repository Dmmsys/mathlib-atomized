/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Data.Set.Inclusion
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.FastInstance

/-!
# Subgroups

This file defines multiplicative and additive subgroups as an extension of submonoids, in a bundled
form.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `A` is an `AddGroup`

- `H K` are `Subgroup`s of `G` or `AddSubgroup`s of `A`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `Subgroup G` : the type of subgroups of a group `G`

* `AddSubgroup A` : the type of subgroups of an additive group `A`

* `Subgroup.subtype` : the natural group homomorphism from a subgroup of group `G` to `G`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

@[expose] public section

assert_not_exists RelIso IsOrderedMonoid Multiset MonoidWithZero

open Function
open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

section SubgroupClass

/-- `InvMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under inverses. -/
/-
**InvMemClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_3) → (G : outParam (Type u_4)) → [Inv G] → [SetLike S G] → Pro
p
参数：Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`InvMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under inverses.
-/
class InvMemClass (S : Type*) (G : outParam Type*) [Inv G] [SetLike S G] : Prop where
  /-- `s` is closed under inverses -/
  inv_mem : ∀ {s : S} {x}, x ∈ s → x⁻¹ ∈ s

export InvMemClass (inv_mem)

/-- `NegMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under negation. -/
/-
**NegMemClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_3) → (G : outParam (Type u_4)) → [Neg G] → [SetLike S G] → Pro
p
参数：Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NegMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under negation.
-/
class NegMemClass (S : Type*) (G : outParam Type*) [Neg G] [SetLike S G] : Prop where
  /-- `s` is closed under negation -/
  neg_mem : ∀ {s : S} {x}, x ∈ s → -x ∈ s

export NegMemClass (neg_mem)

/-- Typeclass for substructures `s` such that `s ∪ -s = G`. -/
/-
**HasMemOrNegMem** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{S : Type u_3} → {G : Type u_4} → [Neg G] → [SetLike S G] → S → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for substructures `s` such that `s ∪ -s = G`.
-/
class HasMemOrNegMem {S G : Type*} [Neg G] [SetLike S G] (s : S) : Prop where
  mem_or_neg_mem (s) (a : G) : a ∈ s ∨ -a ∈ s

/-- Typeclass for substructures `s` such that `s ∪ s⁻¹ = G`. -/
@[to_additive]
/-
**HasMemOrInvMem** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{S : Type u_3} → {G : Type u_4} → [Inv G] → [SetLike S G] → S → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for substructures `s` such that `s ∪ s⁻¹ = G`.
-/
class HasMemOrInvMem {S G : Type*} [Inv G] [SetLike S G] (s : S) : Prop where
  mem_or_inv_mem (s) (a : G) : a ∈ s ∨ a⁻¹ ∈ s

export HasMemOrNegMem (mem_or_neg_mem)
export HasMemOrInvMem (mem_or_inv_mem)

namespace HasMemOrInvMem

variable {S G : Type*} [Inv G] [SetLike S G] (s : S) [HasMemOrInvMem s]

@[to_additive (attr := aesop unsafe 70% apply)]
/-
**HasMemOrInvMem.inv_mem_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `HasMemOrInvMem`。
形式化陈述：inv_mem_of_notMem (x : G) (h : x ∉ s) : x⁻¹ in s
参数：x : G；h : x ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMemOrInvMem.mem_or_inv_mem`：∀ {S : Type u_3} {G : Type u_4} {inst : I
nv G} {inst_1 : SetLike S G} (s : S) [self : HasMemOrInvMem s] (a : G),   a ∈ s 
∨ a⁻¹ ∈ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem inv_mem_of_notMem (x : G) (h : x ∉ s) : x⁻¹ ∈ s := by
  have := mem_or_inv_mem s x
  simp_all

@[to_additive (attr := aesop unsafe 70% apply)]
/-
**HasMemOrInvMem.mem_of_inv_notMem** 是 Mathlib 中的一个定理，位于命名空间 `HasMemOrInvMem`。
形式化陈述：mem_of_inv_notMem (x : G) (h : x⁻¹ ∉ s) : x in s
参数：x : G；h : x⁻¹ ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMemOrInvMem.mem_or_inv_mem`：∀ {S : Type u_3} {G : Type u_4} {inst : I
nv G} {inst_1 : SetLike S G} (s : S) [self : HasMemOrInvMem s] (a : G),   a ∈ s 
∨ a⁻¹ ∈ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem mem_of_inv_notMem (x : G) (h : x⁻¹ ∉ s) : x ∈ s := by
  have := mem_or_inv_mem s x
  simp_all

end HasMemOrInvMem

/-- `SubgroupClass S G` states `S` is a type of subsets `s ⊆ G` that are subgroups of `G`. -/
/-
**SubgroupClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(S : Type u_3) → (G : outParam (Type u_4)) → [DivInvMonoid G] → [SetLike S
 G] → Prop
参数：Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SubgroupClass S G` states `S` is a type of subsets `s ⊆ G` that are subgroups o
f `G`.
-/
class SubgroupClass (S : Type*) (G : outParam Type*) [DivInvMonoid G] [SetLike S G] : Prop
    extends SubmonoidClass S G, InvMemClass S G

/-- `AddSubgroupClass S G` states `S` is a type of subsets `s ⊆ G` that are
additive subgroups of `G`. -/
/-
**AddSubgroupClass** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：AddSubgroupClass (S : Type*) (G : outParam Type*) [SubNegMonoid G] [SetLik
e S G] : Prop extends AddSubmonoidClass S G, NegMemClass S G  attribute [to_addi
tive] InvMemClass SubgroupClass  attribute [aesop 90% (rule_sets
参数：S : Type*；G : outParam Type*。
继承自：AddSubmonoidClass S G, NegMemClass S G  attribute [to_additive] InvMemClass 
SubgroupClass  attribute [aesop 90% (rule_sets。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddSubgroupClass S G` states `S` is a type of subsets `s ⊆ G` that are
additive subgroups of `G`.
-/
class AddSubgroupClass (S : Type*) (G : outParam Type*) [SubNegMonoid G] [SetLike S G] : Prop
    extends AddSubmonoidClass S G, NegMemClass S G

attribute [to_additive] InvMemClass SubgroupClass

attribute [aesop 90% (rule_sets := [SetLike])] inv_mem neg_mem

@[to_additive (attr := simp)]
/-
**inv_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvMemClass S G] {H
 : S} {x : G} : x⁻¹ in H ↔ x in H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvMemClass S G] {H : S}
    {x : G} : x⁻¹ ∈ H ↔ x ∈ H :=
  ⟨fun h => inv_inv x ▸ inv_mem h, inv_mem⟩

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

/-- A subgroup is closed under division. -/
@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))
  /-- An additive subgroup is closed under subtraction. -/]
/-
**div_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H
参数：hx : x in H；hy : y in H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
theorem div_mem {x y : M} (hx : x ∈ H) (hy : y ∈ H) : x / y ∈ H := by
  rw [div_eq_mul_inv]; exact mul_mem hx (inv_mem hy)

@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))]
/-
**zpow_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_3} {S : Type u_4} [inst : DivInvMonoid M] [inst_1 : SetLike 
S M] [hSM : SubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n : ℤ), x ^ n ∈ K
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
theorem zpow_mem {x : M} (hx : x ∈ K) : ∀ n : ℤ, x ^ n ∈ K
  | (n : ℕ) => by
    rw [zpow_natCast]
    exact pow_mem hx n
  | -[n+1] => by
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hx n.succ)

variable [SetLike S G] [SubgroupClass S G]

@[to_additive]
/-
**exists_inv_mem_iff_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_inv_mem_iff_exists_mem {P : G -> Prop} : (exists x : G, x in H ∧ P 
x⁻¹) ↔ exists x in H, P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem exists_inv_mem_iff_exists_mem {P : G → Prop} :
    (∃ x : G, x ∈ H ∧ P x⁻¹) ↔ ∃ x ∈ H, P x := by
  constructor <;>
    · rintro ⟨x, x_in, hx⟩
      exact ⟨x⁻¹, inv_mem x_in, by simp [hx]⟩

@[to_additive]
/-
**mul_mem_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mem_cancel_right {x y : G} (h : x in H) : y * x in H ↔ y in H
参数：h : x in H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
theorem mul_mem_cancel_right {x y : G} (h : x ∈ H) : y * x ∈ H ↔ y ∈ H :=
  ⟨fun hba => by simpa using mul_mem hba (inv_mem h), fun hb => mul_mem hb h⟩

@[to_additive]
/-
**mul_mem_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_mem_cancel_left {x y : G} (h : x in H) : x * y in H ↔ y in H
参数：h : x in H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
theorem mul_mem_cancel_left {x y : G} (h : x ∈ H) : x * y ∈ H ↔ y ∈ H :=
  ⟨fun hab => by simpa using mul_mem (inv_mem h) hab, mul_mem h⟩

namespace InvMemClass

/-- A subgroup of a group inherits an inverse. -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits an inverse. -/]
/-
**InvMemClass.inv** 是 Mathlib 中的一个实例，位于命名空间 `InvMemClass`。
形式化陈述：inv {G S : Type*} [Inv G] [SetLike S G] [InvMemClass S G] {H : S} : Inv H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits an inverse.
-/
instance inv {G S : Type*} [Inv G] [SetLike S G] [InvMemClass S G] {H : S} : Inv H :=
  ⟨fun a => ⟨a⁻¹, inv_mem a.2⟩⟩

@[to_additive (attr := simp, norm_cast)]
/-
**InvMemClass.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `InvMemClass`。
形式化陈述：coe_inv (x : H) : (x⁻¹).1 = x.1⁻¹
参数：x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
theorem coe_inv (x : H) : (x⁻¹).1 = x.1⁻¹ :=
  rfl

end InvMemClass

namespace SubgroupClass

-- Here we assume H, K, and L are subgroups, but in fact any one of them
-- could be allowed to be a subsemigroup.
-- Counterexample where K and L are submonoids: H = ℤ, K = ℕ, L = -ℕ
-- Counterexample where H and K are submonoids: H = {n | n = 0 ∨ 3 ≤ n}, K = 3ℕ + 4ℕ, L = 5ℤ
@[to_additive]
/-
**SubgroupClass.subset_union** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：subset_union [LE S] [IsConcreteLE S G] {H K L : S} : (H : Set G) subseteq 
K union L ↔ H <= K ∨ H <= L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `SetLike.not_le_iff_exists`：not_le_iff_exists : ¬p <= q ↔ exists x in p, 
x ∉ q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_mem_cancel_right`：mul_mem_cancel_right {x y : G} (h : x in H) : y * 
x in H ↔ y in H
· 使用定理 `mul_mem_cancel_left`：mul_mem_cancel_left {x y : G} (h : x in H) : x * y 
in H ↔ y in H
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `mem_of_le_of_mem`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike A B] [
inst_1 : LE A] [IsConcreteLE A B] {S T : A},   S ≤ T → ∀ ⦃x : B⦄, x ∈ S → x ∈ T
-/
theorem subset_union [LE S] [IsConcreteLE S G] {H K L : S} :
    (H : Set G) ⊆ K ∪ L ↔ H ≤ K ∨ H ≤ L := by
  refine ⟨fun h ↦ ?_, fun h x xH ↦ h.imp (mem_of_le_of_mem · xH) (mem_of_le_of_mem · xH)⟩
  rw [or_iff_not_imp_left, SetLike.not_le_iff_exists, ← SetLike.coe_subset_coe]
  exact fun ⟨x, xH, xK⟩ y yH ↦ (h <| mul_mem xH yH).elim
    ((h yH).resolve_left fun yK ↦ xK <| (mul_mem_cancel_right yK).mp ·)
    (mul_mem_cancel_left <| (h xH).resolve_left xK).mp

/-- A subgroup of a group inherits a division -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits a subtraction. -/]
/-
**SubgroupClass.div** 是 Mathlib 中的一个实例，位于命名空间 `SubgroupClass`。
形式化陈述：div {G S : Type*} [DivInvMonoid G] [SetLike S G] [SubgroupClass S G] {H : 
S} : Div H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits a division
-/
instance div {G S : Type*} [DivInvMonoid G] [SetLike S G] [SubgroupClass S G] {H : S} : Div H :=
  ⟨fun a b => ⟨a / b, div_mem a.2 b.2⟩⟩

/-- A subgroup of a group inherits an integer power. -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits an integer scaling. -/]
/-
**SubgroupClass.instZPow** 是 Mathlib 中的一个实例，位于命名空间 `SubgroupClass`。
形式化陈述：instZPow {M S} [DivInvMonoid M] [SetLike S M] [SubgroupClass S M] {H : S} 
: Pow H Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits an integer power.
-/
instance instZPow {M S} [DivInvMonoid M] [SetLike S M] [SubgroupClass S M] {H : S} : Pow H ℤ :=
  ⟨fun a n => ⟨a.1 ^ n, zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]
/-
**SubgroupClass.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：coe_div (x y : H) : (x / y).1 = x.1 / y.1
参数：x y : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div (x y : H) : (x / y).1 = x.1 / y.1 :=
  rfl

variable (H)

-- Prefer subclasses of `Group` over subclasses of `SubgroupClass`.
/-- A subgroup of a group inherits a group structure. -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits an `AddGroup` structure. -/]
/-
**SubgroupClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubgroupClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits a group structure.
-/
instance (priority := 75) toGroup : Group H := fast_instance%
  Subtype.coe_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `CommGroup` over subclasses of `SubgroupClass`.
/-- A subgroup of a `CommGroup` is a `CommGroup`. -/
@[to_additive /-- An additive subgroup of an `AddCommGroup` is an `AddCommGroup`. -/]
/-
**SubgroupClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubgroupClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a `CommGroup` is a `CommGroup`.
-/
instance (priority := 75) toCommGroup {G : Type*} [CommGroup G] [SetLike S G] [SubgroupClass S G] :
    CommGroup H := fast_instance%
  Subtype.coe_injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-- The natural group hom from a subgroup of group `G` to `G`. -/
@[to_additive (attr := coe)
  /-- The natural group hom from an additive subgroup of `AddGroup` `G` to `G`. -/]
/-
**SubgroupClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `SubgroupClass`。
形式化陈述：{G : Type u_1} →   [inst : Group G] → {S : Type u_4} → (H : S) → [inst_1 :
 SetLike S G] → [inst_2 : SubgroupClass S G] → ↥H →* G
参数：H : S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def subtype : H →* G where
  toFun := ((↑) : H → G); map_one' := rfl; map_mul' := fun _ _ => rfl

variable {H} in
@[to_additive (attr := simp)]
/-
**SubgroupClass.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `SubgroupClass`。
形式化陈述：subtype_apply (x : H) : SubgroupClass.subtype H x = x
参数：x : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (x : H) :
    SubgroupClass.subtype H x = x := rfl

@[to_additive]
/-
**SubgroupClass.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `SubgroupClass`。
形式化陈述：subtype_injective : Function.Injective (SubgroupClass.subtype H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective :
    Function.Injective (SubgroupClass.subtype H) :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/-
**SubgroupClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：coe_subtype : (SubgroupClass.subtype H : H -> G) = ((↑) : H -> G)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : (SubgroupClass.subtype H : H → G) = ((↑) : H → G) := by
  rfl

variable {H}

@[to_additive (attr := simp, norm_cast)]
/-
**SubgroupClass.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G) ^ n
参数：x : H；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
-/
theorem coe_pow (x : H) (n : ℕ) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**SubgroupClass.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：coe_zpow (x : H) (n : Int) : ((x ^ n : H) : G) = (x : G) ^ n
参数：x : H；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zpow (x : H) (n : ℤ) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl

/-- The inclusion homomorphism from a subgroup `H` contained in `K` to `K`. -/
@[to_additive
/-- The inclusion homomorphism from an additive subgroup `H` contained in `K` to `K`. -/]
/-
**SubgroupClass.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `SubgroupClass`。
形式化陈述：inclusion [LE S] [IsConcreteLE S G] {H K : S} (h : H <= K) : H ->* K
参数：h : H <= K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inclusion [LE S] [IsConcreteLE S G] {H K : S} (h : H ≤ K) : H →* K :=
  MonoidHom.mk' (fun x => ⟨x, mem_of_le_of_mem h x.prop⟩) fun _ _ => rfl

@[to_additive (attr := simp)]
/-
**SubgroupClass.inclusion_self** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：inclusion_self [Preorder S] [IsConcreteLE S G] (x : H) : inclusion le_rfl 
x = x
参数：x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inclusion_self [Preorder S] [IsConcreteLE S G] (x : H) : inclusion le_rfl x = x := by
  cases x
  rfl

@[to_additive (attr := simp)]
/-
**SubgroupClass.inclusion_mk** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：inclusion_mk [LE S] [IsConcreteLE S G] {h : H <= K} (x : G) (hx : x in H) 
: inclusion h ⟨x, hx⟩ = ⟨x, mem_of_le_of_mem h hx⟩
参数：x : G；hx : x in H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_mk [LE S] [IsConcreteLE S G] {h : H ≤ K} (x : G) (hx : x ∈ H) :
    inclusion h ⟨x, hx⟩ = ⟨x, mem_of_le_of_mem h hx⟩ :=
  rfl

@[to_additive]
/-
**SubgroupClass.inclusion_right** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：inclusion_right [LE S] [IsConcreteLE S G] (h : H <= K) (x : K) (hx : (x : 
G) in H) : inclusion h ⟨x, hx⟩ = x
参数：h : H <= K；x : K；hx : (x : G) in H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inclusion_right [LE S] [IsConcreteLE S G] (h : H ≤ K) (x : K) (hx : (x : G) ∈ H) :
    inclusion h ⟨x, hx⟩ = x := by
  cases x
  rfl

@[simp]
/-
**SubgroupClass.inclusion_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：inclusion_inclusion [Preorder S] [IsConcreteLE S G] {L : S} (hHK : H <= K)
 (hKL : K <= L) (x : H) : inclusion hKL (inclusion hHK x) = inclusion (hHK.trans
 hKL) x
参数：hHK : H <= K；hKL : K <= L；x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inclusion_inclusion [Preorder S] [IsConcreteLE S G]
    {L : S} (hHK : H ≤ K) (hKL : K ≤ L) (x : H) :
    inclusion hKL (inclusion hHK x) = inclusion (hHK.trans hKL) x := by
  cases x
  rfl

@[to_additive (attr := simp)]
/-
**SubgroupClass.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：coe_inclusion [LE S] [IsConcreteLE S G] {H K : S} (h : H <= K) (a : H) : (
inclusion h a : G) = a
参数：h : H <= K；a : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.coe_inclusion`：coe_inclusion (h : s subseteq t) (x : s) : (inclusion
 h x : α) = (x : α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
-/
theorem coe_inclusion [LE S] [IsConcreteLE S G]
    {H K : S} (h : H ≤ K) (a : H) : (inclusion h a : G) = a :=
  Set.coe_inclusion (SetLike.coe_subset_coe.mpr h) a

@[to_additive (attr := simp)]
/-
**SubgroupClass.subtype_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`
。
形式化陈述：subtype_comp_inclusion [LE S] [IsConcreteLE S G] {H K : S} (h : H <= K) : 
(SubgroupClass.subtype K).comp (inclusion h) = SubgroupClass.subtype H
参数：h : H <= K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_comp_inclusion [LE S] [IsConcreteLE S G]
    {H K : S} (h : H ≤ K) :
    (SubgroupClass.subtype K).comp (inclusion h) = SubgroupClass.subtype H :=
  rfl

end SubgroupClass

end SubgroupClass

/-- A subgroup of a group `G` is a subset containing 1, closed under multiplication
and closed under multiplicative inverse. -/
/-
**Subgroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_3) → [Group G] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group `G` is a subset containing 1, closed under multiplication
and closed under multiplicative inverse.
-/
structure Subgroup (G : Type*) [Group G] extends Submonoid G where
  /-- `G` is closed under inverses -/
  inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier

/-- An additive subgroup of an additive group `G` is a subset containing 0, closed
under addition and additive inverse. -/
/-
**AddSubgroup** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：AddSubgroup (G : Type*) [AddGroup G] extends AddSubmonoid G where /-- `G` 
is closed under negation -/ neg_mem' {x} : x in carrier -> -x in carrier  attrib
ute [to_additive (attr
参数：G : Type*。
继承自：AddSubmonoid G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive subgroup of an additive group `G` is a subset containing 0, closed
under addition and additive inverse.
-/
structure AddSubgroup (G : Type*) [AddGroup G] extends AddSubmonoid G where
  /-- `G` is closed under negation -/
  neg_mem' {x} : x ∈ carrier → -x ∈ carrier

attribute [to_additive (attr := wikidata Q466109)] Subgroup

/-- Reinterpret a `Subgroup` as a `Submonoid`. -/
add_decl_doc Subgroup.toSubmonoid

/-- Reinterpret an `AddSubgroup` as an `AddSubmonoid`. -/
add_decl_doc AddSubgroup.toAddSubmonoid

namespace Subgroup

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Subgroup G) G where
  coe s := s.carrier
  coe_injective p q h := by
    obtain ⟨⟨⟨hp, _⟩, _⟩, _⟩ := p
    obtain ⟨⟨⟨hq, _⟩, _⟩, _⟩ := q
    congr
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : PartialOrder (Subgroup G) := .ofSetLike (Subgroup G) G

initialize_simps_projections Subgroup (carrier → coe, as_prefix coe)
initialize_simps_projections AddSubgroup (carrier → coe, as_prefix coe)

/-- The actual `Subgroup` obtained from an element of a `SubgroupClass` -/
@[to_additive (attr := simps) /-- The actual `AddSubgroup` obtained from an element of a
`AddSubgroupClass` -/]
/-
**Subgroup.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：ofClass {S G : Type*} [Group G] [SetLike S G] [SubgroupClass S G] (s : S) 
: Subgroup G
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofClass {S G : Type*} [Group G] [SetLike S G] [SubgroupClass S G]
    (s : S) : Subgroup G :=
  ⟨⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩, InvMemClass.inv_mem⟩

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CanLift (Set G) (Subgroup G) (↑)
    (fun s ↦ 1 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ ∀ {x}, x ∈ s → x⁻¹ ∈ s) where
  prf s h := ⟨{ carrier := s, one_mem' := h.1, mul_mem' := h.2.1, inv_mem' := h.2.2}, rfl⟩

-- TODO: Below can probably be written more uniformly
@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubgroupClass (Subgroup G) G where
  inv_mem := Subgroup.inv_mem' _
  one_mem _ := (Subgroup.toSubmonoid _).one_mem'
  mul_mem := (Subgroup.toSubmonoid _).mul_mem'

-- This is not a simp lemma,
-- because the simp normal form left-hand side is given by `mem_toSubmonoid` below.
@[to_additive]
/-
**Subgroup.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_carrier {s : Subgroup G} {x : G} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : Subgroup G} {x : G} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
/-
**Subgroup.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_mk {s : Submonoid G} {x : G} (h_inv) : x in mk s h_inv ↔ x in s
参数：h_inv。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {s : Submonoid G} {x : G} (h_inv) :
    x ∈ mk s h_inv ↔ x ∈ s :=
  Iff.rfl

@[to_additive (attr := simp)]
/-
**Subgroup.coe_set_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_set_mk {s : Submonoid G} (h_inv) : (mk s h_inv : Set G) = s
参数：h_inv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_set_mk {s : Submonoid G} (h_inv) :
    (mk s h_inv : Set G) = s :=
  rfl

@[to_additive (attr := simp)]
/-
**Subgroup.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mk_le_mk {s t : Submonoid G} (h_inv) (h_inv') : mk s h_inv <= mk t h_inv' 
↔ s <= t
参数：h_inv；h_inv'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {s t : Submonoid G} (h_inv) (h_inv') :
    mk s h_inv ≤ mk t h_inv' ↔ s ≤ t :=
  Iff.rfl

@[to_additive (attr := simp)]
/-
**Subgroup.coe_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_toSubmonoid (K : Subgroup G) : (K.toSubmonoid : Set G) = K
参数：K : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubmonoid (K : Subgroup G) : (K.toSubmonoid : Set G) = K :=
  rfl

@[to_additive (attr := simp)]
/-
**Subgroup.mem_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_toSubmonoid (K : Subgroup G) (x : G) : x in K.toSubmonoid ↔ x in K
参数：K : Subgroup G；x : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubmonoid (K : Subgroup G) (x : G) : x ∈ K.toSubmonoid ↔ x ∈ K :=
  Iff.rfl

@[to_additive]
/-
**Subgroup.toSubmonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：toSubmonoid_injective : Function.Injective (toSubmonoid : Subgroup G -> Su
bmonoid G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.coe_toSubmonoid`：coe_toSubmonoid (K : Subgroup G) : (K.toSubmon
oid : Set G) = K
-/
theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subgroup G → Submonoid G) :=
  fun p q h => by
    have := SetLike.ext'_iff.1 h
    rw [coe_toSubmonoid, coe_toSubmonoid] at this
    exact SetLike.ext'_iff.2 this

@[to_additive (attr := simp)]
/-
**Subgroup.toSubmonoid_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：toSubmonoid_inj {p q : Subgroup G} : p.toSubmonoid = q.toSubmonoid ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subgroup.toSubmonoid_injective`：toSubmonoid_injective : Function.Injecti
ve (toSubmonoid : Subgroup G -> Submonoid G)
-/
theorem toSubmonoid_inj {p q : Subgroup G} : p.toSubmonoid = q.toSubmonoid ↔ p = q :=
  toSubmonoid_injective.eq_iff

@[to_additive (attr := mono)]
/-
**Subgroup.toSubmonoid_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：toSubmonoid_strictMono : StrictMono (toSubmonoid : Subgroup G -> Submonoid
 G)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubmonoid_strictMono : StrictMono (toSubmonoid : Subgroup G → Submonoid G) := fun _ _ =>
  id

@[to_additive (attr := mono)]
/-
**Subgroup.toSubmonoid_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：toSubmonoid_mono : Monotone (toSubmonoid : Subgroup G -> Submonoid G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Subgroup.toSubmonoid_strictMono`：toSubmonoid_strictMono : StrictMono (to
Submonoid : Subgroup G -> Submonoid G)
-/
theorem toSubmonoid_mono : Monotone (toSubmonoid : Subgroup G → Submonoid G) :=
  toSubmonoid_strictMono.monotone

@[to_additive (attr := simp)]
/-
**Subgroup.toSubmonoid_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：toSubmonoid_le {p q : Subgroup G} : p.toSubmonoid <= q.toSubmonoid ↔ p <= 
q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubmonoid_le {p q : Subgroup G} : p.toSubmonoid ≤ q.toSubmonoid ↔ p ≤ q :=
  Iff.rfl

@[to_additive]
/-
**Subgroup.coe_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：coe_nonempty (s : Subgroup G) : (s : Set G).Nonempty
参数：s : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
lemma coe_nonempty (s : Subgroup G) : (s : Set G).Nonempty := ⟨1, one_mem _⟩

attribute [deprecated OneMemClass.coe_nonempty (since := "2026-04-20")] Subgroup.coe_nonempty
attribute [deprecated ZeroMemClass.coe_nonempty (since := "2026-04-20")] AddSubgroup.coe_nonempty

end Subgroup

namespace Subgroup

variable (H K : Subgroup G)

/-- Copy of a subgroup with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive (attr := simps)
      /-- Copy of an additive subgroup with a new `carrier` equal to the old one.
      Useful to fix definitional equalities -/]
/-
**Subgroup.copy** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → (K : Subgroup G) → (s : Set G) → s = ↑
K → Subgroup G
参数：K : Subgroup G；s : Set G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def copy (K : Subgroup G) (s : Set G) (hs : s = K) : Subgroup G where
  carrier := s
  one_mem' := hs.symm ▸ K.one_mem'
  mul_mem' := hs.symm ▸ K.mul_mem'
  inv_mem' hx := by simpa [hs] using hx

@[to_additive]
/-
**Subgroup.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：copy_eq (K : Subgroup G) (s : Set G) (hs : s = ↑K) : K.copy s hs = K
参数：K : Subgroup G；s : Set G；hs : s = ↑K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (K : Subgroup G) (s : Set G) (hs : s = ↑K) : K.copy s hs = K :=
  SetLike.coe_injective hs

/-- Two subgroups are equal if they have the same elements. -/
@[to_additive (attr := ext) /-- Two `AddSubgroup`s are equal if they have the same elements. -/]
/-
**Subgroup.ext** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H = K
参数：h : forall x, x in H ↔ x in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two subgroups are equal if they have the same elements.
-/
theorem ext {H K : Subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K :=
  SetLike.ext h

/-- A subgroup contains the group's 1. -/
@[to_additive /-- An `AddSubgroup` contains the group's 0. -/]
/-
**Subgroup.one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 ∈ H
参数：H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G

--- 原说明 ---
A subgroup contains the group's 1.
-/
protected theorem one_mem : (1 : G) ∈ H :=
  one_mem _

/-- A subgroup is closed under multiplication. -/
@[to_additive /-- An `AddSubgroup` is closed under addition. -/]
/-
**Subgroup.mul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x y : G}, x ∈ H → y ∈ 
H → x * y ∈ H
参数：H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
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

--- 原说明 ---
A subgroup is closed under multiplication.
-/
protected theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H :=
  mul_mem

/-- A subgroup is closed under inverse. -/
@[to_additive /-- An `AddSubgroup` is closed under inverse. -/]
/-
**Subgroup.inv_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x : G}, x ∈ H → x⁻¹ ∈ 
H
参数：H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G

--- 原说明 ---
A subgroup is closed under inverse.
-/
protected theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H :=
  inv_mem

/-- A subgroup is closed under division. -/
@[to_additive /-- An `AddSubgroup` is closed under subtraction. -/]
/-
**Subgroup.div_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x y : G}, x ∈ H → y ∈ 
H → x / y ∈ H
参数：H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_mem`：div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G

--- 原说明 ---
A subgroup is closed under division.
-/
protected theorem div_mem {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x / y ∈ H :=
  div_mem hx hy

@[to_additive]
/-
**Subgroup.inv_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x : G}, x⁻¹ ∈ H ↔ x ∈ 
H
参数：H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
protected theorem inv_mem_iff {x : G} : x⁻¹ ∈ H ↔ x ∈ H :=
  inv_mem_iff

@[to_additive]
/-
**Subgroup.exists_inv_mem_iff_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (K : Subgroup G) {P : G → Prop}, (∃ x ∈ 
K, P x⁻¹) ↔ ∃ x ∈ K, P x
参数：K : Subgroup G；∃ x ∈ K, P x⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_inv_mem_iff_exists_mem`：exists_inv_mem_iff_exists_mem {P : G -> P
rop} : (exists x : G, x in H ∧ P x⁻¹) ↔ exists x in H, P x
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
protected theorem exists_inv_mem_iff_exists_mem (K : Subgroup G) {P : G → Prop} :
    (∃ x : G, x ∈ K ∧ P x⁻¹) ↔ ∃ x ∈ K, P x :=
  exists_inv_mem_iff_exists_mem

@[to_additive]
/-
**Subgroup.mul_mem_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x y : G}, x ∈ H → (y *
 x ∈ H ↔ y ∈ H)
参数：H : Subgroup G；y * x ∈ H ↔ y ∈ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_mem_cancel_right`：mul_mem_cancel_right {x y : G} (h : x in H) : y * 
x in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
protected theorem mul_mem_cancel_right {x y : G} (h : x ∈ H) : y * x ∈ H ↔ y ∈ H :=
  mul_mem_cancel_right h

@[to_additive]
/-
**Subgroup.mul_mem_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x y : G}, x ∈ H → (x *
 y ∈ H ↔ y ∈ H)
参数：H : Subgroup G；x * y ∈ H ↔ y ∈ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_mem_cancel_left`：mul_mem_cancel_left {x y : G} (h : x in H) : x * y 
in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
protected theorem mul_mem_cancel_left {x y : G} (h : x ∈ H) : x * y ∈ H ↔ y ∈ H :=
  mul_mem_cancel_left h

@[to_additive]
/-
**Subgroup.pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (K : Subgroup G) {x : G}, x ∈ K → ∀ (n :
 ℕ), x ^ n ∈ K
参数：K : Subgroup G；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
protected theorem pow_mem {x : G} (hx : x ∈ K) : ∀ n : ℕ, x ^ n ∈ K :=
  pow_mem hx

@[to_additive]
/-
**Subgroup.zpow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (K : Subgroup G) {x : G}, x ∈ K → ∀ (n :
 ℤ), x ^ n ∈ K
参数：K : Subgroup G；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zpow_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : DivInvMonoid M] [inst_
1 : SetLike S M] [hSM : SubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n : ℤ…
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
protected theorem zpow_mem {x : G} (hx : x ∈ K) : ∀ n : ℤ, x ^ n ∈ K :=
  zpow_mem hx

/-- Construct a subgroup from a nonempty set that is closed under division. -/
@[to_additive /-- Construct a subgroup from a nonempty set that is closed under subtraction -/]
/-
**Subgroup.ofDiv** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：ofDiv (s : Set G) (hsn : s.Nonempty) (hs : forallᵉ (x in s) (y in s), x * 
y⁻¹ in s) : Subgroup G
参数：s : Set G；hsn : s.Nonempty；hs : forallᵉ (x in s) (y in s), x * y⁻¹ in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a subgroup from a nonempty set that is closed under division.
-/
def ofDiv (s : Set G) (hsn : s.Nonempty) (hs : ∀ᵉ (x ∈ s) (y ∈ s), x * y⁻¹ ∈ s) :
    Subgroup G :=
  have one_mem : (1 : G) ∈ s := by
    let ⟨x, hx⟩ := hsn
    simpa using hs x hx x hx
  have inv_mem : ∀ x, x ∈ s → x⁻¹ ∈ s := fun x hx => by simpa using hs 1 one_mem x hx
  { carrier := s
    one_mem' := one_mem
    inv_mem' := inv_mem _
    mul_mem' := fun hx hy => by simpa using hs _ hx _ (inv_mem _ hy) }

/-- A subgroup of a group inherits a multiplication. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an addition. -/]
/-
**Subgroup.mul** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：mul : Mul H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits a multiplication.
-/
instance mul : Mul H :=
  H.toSubmonoid.mul

/-- A subgroup of a group inherits a 1. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits a zero. -/]
/-
**Subgroup.one** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：one : One H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits a 1.
-/
instance one : One H :=
  H.toSubmonoid.one

/-- A subgroup of a group inherits an inverse. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an inverse. -/]
/-
**Subgroup.inv** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：inv : Inv H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits an inverse.
-/
instance inv : Inv H :=
  ⟨fun a => ⟨a⁻¹, H.inv_mem a.2⟩⟩

/-- A subgroup of a group inherits a division -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits a subtraction. -/]
/-
**Subgroup.div** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：div : Div H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits a division
-/
instance div : Div H :=
  ⟨fun a b => ⟨a / b, H.div_mem a.2 b.2⟩⟩

/-- A subgroup of a group inherits a natural power -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits a natural scaling. -/]
/-
**Subgroup.npow** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → (H : Subgroup G) → Pow ↥H ℕ
参数：H : Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits a natural power
-/
protected instance npow : Pow H ℕ :=
  ⟨fun a n => ⟨a ^ n, H.pow_mem a.2 n⟩⟩

/-- A subgroup of a group inherits an integer power -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an integer scaling. -/]
/-
**Subgroup.zpow** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：zpow : Pow H Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a group inherits an integer power
-/
instance zpow : Pow H ℤ :=
  ⟨fun a n => ⟨a ^ n, H.zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Subgroup.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y
参数：x y : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Subgroup.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_one : ((1 : H) : G) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : H) : G) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Subgroup.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_inv (x : H) : ↑(x⁻¹ : H) = (x⁻¹ : G)
参数：x : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (x : H) : ↑(x⁻¹ : H) = (x⁻¹ : G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Subgroup.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_div (x y : H) : (↑(x / y) : G) = ↑x / ↑y
参数：x y : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div (x y : H) : (↑(x / y) : G) = ↑x / ↑y :=
  rfl

@[to_additive (attr := norm_cast)]
/-
**Subgroup.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_mk (x : G) (hx : x in H) : ((⟨x, hx⟩ : H) : G) = x
参数：x : G；hx : x in H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (x : G) (hx : x ∈ H) : ((⟨x, hx⟩ : H) : G) = x :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Subgroup.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G) ^ n
参数：x : H；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (x : H) (n : ℕ) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl

@[to_additive (attr := norm_cast)]
/-
**Subgroup.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_zpow (x : H) (n : Int) : ((x ^ n : H) : G) = (x : G) ^ n
参数：x : H；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zpow (x : H) (n : ℤ) : ((x ^ n : H) : G) = (x : G) ^ n := by
  dsimp

@[to_additive (attr := simp)]
/-
**Subgroup.mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mk_eq_one {g : G} {h} : (⟨g, h⟩ : H) = 1 ↔ g = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submonoid.mk_eq_one`：mk_eq_one {a : M} {ha} : (⟨a, ha⟩ : S) = 1 ↔ a = 1
-/
theorem mk_eq_one {g : G} {h} : (⟨g, h⟩ : H) = 1 ↔ g = 1 := Submonoid.mk_eq_one ..

/-- A subgroup of a group inherits a group structure. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an `AddGroup` structure. -/]
/-
**Subgroup.toGroup** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：toGroup {G : Type*} [Group G] (H : Subgroup G) : Group H
参数：H : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G

--- 原说明 ---
A subgroup of a group inherits a group structure.
-/
instance toGroup {G : Type*} [Group G] (H : Subgroup G) : Group H :=
  SubgroupClass.toGroup H

/-- A subgroup of a `CommGroup` is a `CommGroup`. -/
@[to_additive /-- An `AddSubgroup` of an `AddCommGroup` is an `AddCommGroup`. -/]
/-
**Subgroup.toCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：toCommGroup {G : Type*} [CommGroup G] (H : Subgroup G) : CommGroup H
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup of a `CommGroup` is a `CommGroup`.
-/
instance toCommGroup {G : Type*} [CommGroup G] (H : Subgroup G) : CommGroup H :=
  SubgroupClass.toCommGroup H

/-- The natural group hom from a subgroup of group `G` to `G`. -/
@[to_additive /-- The natural group hom from an `AddSubgroup` of `AddGroup` `G` to `G`. -/]
/-
**Subgroup.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → (H : Subgroup G) → ↥H →* G
参数：H : Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural group hom from a subgroup of group `G` to `G`.
-/
protected def subtype : H →* G where
  toFun := ((↑) : H → G); map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/-
**Subgroup.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：subtype_apply {s : Subgroup G} (x : s) : s.subtype x = x
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply {s : Subgroup G} (x : s) :
    s.subtype x = x := rfl

@[to_additive]
/-
**Subgroup.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：subtype_injective (s : Subgroup G) : Function.Injective s.subtype
参数：s : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective (s : Subgroup G) :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/-
**Subgroup.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_subtype : ⇑H.subtype = ((↑) : H -> G)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : ⇑H.subtype = ((↑) : H → G) :=
  rfl

/-- The inclusion homomorphism from a subgroup `H` contained in `K` to `K`. -/
@[to_additive
/-- The inclusion homomorphism from an additive subgroup `H` contained in `K` to `K`. -/]
/-
**Subgroup.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：inclusion {H K : Subgroup G} (h : H <= K) : H ->* K
参数：h : H <= K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inclusion {H K : Subgroup G} (h : H ≤ K) : H →* K :=
  MonoidHom.mk' (fun x => ⟨x, h x.2⟩) fun _ _ => rfl

@[to_additive (attr := simp)]
/-
**Subgroup.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_inclusion {H K : Subgroup G} (h : H <= K) (a : H) : (inclusion h a : G
) = a
参数：h : H <= K；a : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.coe_inclusion`：coe_inclusion (h : s subseteq t) (x : s) : (inclusion
 h x : α) = (x : α)
-/
theorem coe_inclusion {H K : Subgroup G} (h : H ≤ K) (a : H) : (inclusion h a : G) = a :=
  Set.coe_inclusion h a

@[to_additive]
/-
**Subgroup.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：inclusion_injective {H K : Subgroup G} (h : H <= K) : Function.Injective i
nclusion h
参数：h : H <= K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem inclusion_injective {H K : Subgroup G} (h : H ≤ K) : Function.Injective <| inclusion h :=
  Set.inclusion_injective h

@[to_additive (attr := simp)]
/-
**Subgroup.inclusion_inj** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：inclusion_inj {H K : Subgroup G} (h : H <= K) {x y : H} : inclusion h x = 
inclusion h y ↔ x = y
参数：h : H <= K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subgroup.inclusion_injective`：inclusion_injective {H K : Subgroup G} (h 
: H <= K) : Function.Injective inclusion h
-/
lemma inclusion_inj {H K : Subgroup G} (h : H ≤ K) {x y : H} :
    inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff

@[to_additive (attr := simp)]
/-
**Subgroup.subtype_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subtype_comp_inclusion {H K : Subgroup G} (hH : H <= K) : K.subtype.comp (
inclusion hH) = H.subtype
参数：hH : H <= K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_comp_inclusion {H K : Subgroup G} (hH : H ≤ K) :
    K.subtype.comp (inclusion hH) = H.subtype :=
  rfl

open Set

/-- A subgroup `H` is normal if whenever `n ∈ H`, then `g * n * g⁻¹ ∈ H` for every `g : G` -/
/-
**Subgroup.Normal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → Subgroup G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup `H` is normal if whenever `n ∈ H`, then `g * n * g⁻¹ ∈ H` for every `
g : G`
-/
structure Normal : Prop where
  /-- `H` is closed under conjugation -/
  conj_mem : ∀ n, n ∈ H → ∀ g : G, g * n * g⁻¹ ∈ H

attribute [class] Normal

end Subgroup

namespace AddSubgroup

/-- An AddSubgroup `H` is normal if whenever `n ∈ H`, then `g + n - g ∈ H` for every `g : A` -/
/-
**AddSubgroup.Normal** 是 Mathlib 中的一个结构，位于命名空间 `AddSubgroup`。
形式化陈述：Normal (H : AddSubgroup A) : Prop where /-- `H` is closed under additive c
onjugation -/ conj_mem : forall n, n in H -> forall g : A, g + n + -g in H  attr
ibute [to_additive (attr
参数：H : AddSubgroup A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An AddSubgroup `H` is normal if whenever `n ∈ H`, then `g + n - g ∈ H` for every
 `g : A`
-/
structure Normal (H : AddSubgroup A) : Prop where
  /-- `H` is closed under additive conjugation -/
  conj_mem : ∀ n, n ∈ H → ∀ g : A, g + n + -g ∈ H

attribute [to_additive (attr := wikidata Q743179)] Subgroup.Normal

attribute [class] Normal

end AddSubgroup

namespace Subgroup

variable {H : Subgroup G}

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) normal_of_isMulCommutative [IsMulCommutative G] (H : Subgroup G) :
    H.Normal := ⟨by simp [mul_comm']⟩

@[deprecated (since := "2026-04-10")] alias normal_of_comm := normal_of_isMulCommutative

namespace Normal

@[to_additive]
/-
**Subgroup.Normal.conj_mem'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：conj_mem' (nH : H.Normal) (n : G) (hn : n in H) (g : G) : g⁻¹ * n * g in H
参数：nH : H.Normal；n : G；hn : n in H；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
-/
theorem conj_mem' (nH : H.Normal) (n : G) (hn : n ∈ H) (g : G) :
    g⁻¹ * n * g ∈ H := by
  convert! nH.conj_mem n hn g⁻¹
  rw [inv_inv]

@[to_additive]
/-
**Subgroup.Normal.mem_comm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：mem_comm (nH : H.Normal) {a b : G} (h : a * b in H) : b * a in H
参数：nH : H.Normal；h : a * b in H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem mem_comm (nH : H.Normal) {a b : G} (h : a * b ∈ H) : b * a ∈ H := by
  have : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ H := nH.conj_mem (a * b) h a⁻¹
  simpa

@[to_additive]
/-
**Subgroup.Normal.mem_comm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：mem_comm_iff (nH : H.Normal) {a b : G} : a * b in H ↔ b * a in H
参数：nH : H.Normal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.mem_comm`：mem_comm (nH : H.Normal) {a b : G} (h : a * b 
in H) : b * a in H
-/
theorem mem_comm_iff (nH : H.Normal) {a b : G} : a * b ∈ H ↔ b * a ∈ H :=
  ⟨nH.mem_comm, nH.mem_comm⟩

end Normal

end Subgroup

namespace Subgroup

variable (H : Subgroup G)

section Normalizer

/-- The `normalizer` of `S` is the subgroup of `G` whose elements satisfy `g * S * g⁻¹ = S`.
When `S` is a subgroup, this is the largest subgroup of `G` inside which `S` is normal. -/
@[to_additive
/-- The `normalizer` of `S` is the subgroup of `G` whose elements satisfy `g + S - g = S`.
When `S` is a subgroup, this is the largest subgroup of `G` inside which `S` is normal. -/]
/-
**Subgroup.normalizer** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：normalizer (S : Set G) : Subgroup G where carrier
参数：S : Set G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def normalizer (S : Set G) : Subgroup G where
  carrier := { g : G | ∀ n, n ∈ S ↔ g * n * g⁻¹ ∈ S }
  one_mem' := by simp
  mul_mem' {a b} (ha : ∀ n, n ∈ S ↔ a * n * a⁻¹ ∈ S) (hb : ∀ n, n ∈ S ↔ b * n * b⁻¹ ∈ S) n := by
    rw [hb, ha]
    simp only [mul_assoc, mul_inv_rev]
  inv_mem' {a} (ha : ∀ n, n ∈ S ↔ a * n * a⁻¹ ∈ S) n := by
    rw [ha (a⁻¹ * n * a⁻¹⁻¹)]
    simp only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

@[deprecated (since := "2026-03-19")]
alias setNormalizer := normalizer
@[deprecated (since := "2026-03-19")]
alias _root_.AddSubgroup.setNormalizer := AddSubgroup.normalizer

variable {H} {S : Set G} {g : G}

@[to_additive]
/-
**Subgroup.mem_set_normalizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_set_normalizer_iff : g in normalizer S ↔ forall h, h in S ↔ g * h * g⁻
¹ in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_set_normalizer_iff : g ∈ normalizer S ↔ ∀ h, h ∈ S ↔ g * h * g⁻¹ ∈ S :=
  .rfl

@[to_additive]
/-
**Subgroup.mem_set_normalizer_iff''** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_set_normalizer_iff'' : g in normalizer S ↔ forall h, h in S ↔ g⁻¹ * h 
* g in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.mem_set_normalizer_iff`：mem_set_normalizer_iff : g in normalize
r S ↔ forall h, h in S ↔ g * h * g⁻¹ in S
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_set_normalizer_iff'' : g ∈ normalizer S ↔ ∀ h, h ∈ S ↔ g⁻¹ * h * g ∈ S := by
  rw [← inv_mem_iff, mem_set_normalizer_iff, inv_inv]

@[to_additive]
/-
**Subgroup.mem_set_normalizer_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_set_normalizer_iff' : g in normalizer S ↔ forall h, h * g in S ↔ g * h
 in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem mem_set_normalizer_iff' : g ∈ normalizer S ↔ ∀ h, h * g ∈ S ↔ g * h ∈ S :=
  ⟨fun h n ↦ by rw [h, mul_assoc, mul_inv_cancel_right],
    fun h n ↦ by rw [mul_assoc, ← h, inv_mul_cancel_right]⟩

@[to_additive]
/-
**Subgroup.mem_normalizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_normalizer_iff : g in normalizer H ↔ forall h, h in H ↔ g * h * g⁻¹ in
 H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mem_set_normalizer_iff`：mem_set_normalizer_iff : g in normalize
r S ↔ forall h, h in S ↔ g * h * g⁻¹ in S
-/
theorem mem_normalizer_iff : g ∈ normalizer H ↔ ∀ h, h ∈ H ↔ g * h * g⁻¹ ∈ H :=
  mem_set_normalizer_iff

@[to_additive]
/-
**Subgroup.mem_normalizer_iff''** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_normalizer_iff'' : g in normalizer H ↔ forall h : G, h in H ↔ g⁻¹ * h 
* g in H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mem_set_normalizer_iff''`：mem_set_normalizer_iff'' : g in norma
lizer S ↔ forall h, h in S ↔ g⁻¹ * h * g in S
-/
theorem mem_normalizer_iff'' : g ∈ normalizer H ↔ ∀ h : G, h ∈ H ↔ g⁻¹ * h * g ∈ H :=
  mem_set_normalizer_iff''

@[to_additive]
/-
**Subgroup.mem_normalizer_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_normalizer_iff' : g in normalizer H ↔ forall n, n * g in H ↔ g * n in 
H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mem_set_normalizer_iff'`：mem_set_normalizer_iff' : g in normali
zer S ↔ forall h, h * g in S ↔ g * h in S
-/
theorem mem_normalizer_iff' : g ∈ normalizer H ↔ ∀ n, n * g ∈ H ↔ g * n ∈ H :=
  mem_set_normalizer_iff'

@[to_additive]
/-
**Subgroup.le_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_normalizer : H <= normalizer H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subgroup.mul_mem_cancel_right`：∀ {G : Type u_1} [inst : Group G] (H : Su
bgroup G) {x y : G}, x ∈ H → (y * x ∈ H ↔ y ∈ H)
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `Subgroup.mul_mem_cancel_left`：∀ {G : Type u_1} [inst : Group G] (H : Sub
group G) {x y : G}, x ∈ H → (x * y ∈ H ↔ y ∈ H)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_normalizer : H ≤ normalizer H := fun x xH n => by
  rw [SetLike.mem_coe, SetLike.mem_coe, H.mul_mem_cancel_right <| H.inv_mem xH,
    H.mul_mem_cancel_left xH]

end Normalizer

@[to_additive (attr := deprecated inferInstance (since := "2026-04-09"))]
/-
**Subgroup.commGroup_isMulCommutative** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：commGroup_isMulCommutative {G : Type*} [CommGroup G] (H : Subgroup G) : Is
MulCommutative H
参数：H : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem commGroup_isMulCommutative {G : Type*} [CommGroup G] (H : Subgroup G) :
    IsMulCommutative H := inferInstance

@[to_additive (attr := deprecated setLike_mul_comm (since := "2026-03-09"))]
/-
**Subgroup.mul_comm_of_mem_isMulCommutative** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`
。
形式化陈述：mul_comm_of_mem_isMulCommutative [IsMulCommutative H] {a b : G} (ha : a in
 H) (hb : b in H) : a * b = b * a
参数：ha : a in H；hb : b in H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
lemma mul_comm_of_mem_isMulCommutative [IsMulCommutative H] {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    a * b = b * a :=
  setLike_mul_comm ha hb

end Subgroup

@[to_additive]
/-
**Set.injOn_iff_map_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.injOn_iff_map_eq_one {F G H S : Type*} [Group G] [Group H] [FunLike F 
G H] [MonoidHomClass F G H] (f : F) [SetLike S G] [OneMemClass S G] [MulMemClass
 S G] [InvMemClass S G] (s : S) : Set.InjOn f s ↔ forall a in s, f a = 1 -> a = 
1 where mp h a ha ha'
参数：f : F；s : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Set.injOn_iff_map_eq_one {F G H S : Type*} [Group G] [Group H]
    [FunLike F G H] [MonoidHomClass F G H] (f : F)
    [SetLike S G] [OneMemClass S G] [MulMemClass S G] [InvMemClass S G] (s : S) :
    Set.InjOn f s ↔ ∀ a ∈ s, f a = 1 → a = 1 where
  mp h a ha ha' := by
    refine h ha (one_mem s) ?_
    rwa [map_one]
  mpr h x hx y hy hxy := by
    refine mul_inv_eq_one.1 <| h _ (mul_mem ?_ (inv_mem ?_)) ?_ <;> simp_all
