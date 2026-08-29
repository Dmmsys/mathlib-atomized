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

/--
Definition of `InvMemClass` / `InvMemClass` 的定义

English:
class InvMemClass
  parameters: (S : Type*) (G : outParam Type*) [Inv G] [SetLike S G]
  axioms and operations (1):
    - inv_mem : forall {s : S} {x}, x in s -> x⁻¹ in s

中文:
类 InvMemClass
  参数: (S : 类型) (G : outParam 类型) [Inv G] [SetLike S G]
  公理与运算 (1 个):
    - inv_mem : 对任意 {s : S} {x}, x in s -> x⁻¹ in s
-/
class InvMemClass (S : Type*) (G : outParam Type*) [Inv G] [SetLike S G] : Prop where
  /-- `s` is closed under inverses -/
  inv_mem : forall {s : S} {x}, x in s -> x⁻¹ in s

export InvMemClass (inv_mem)

/--
Definition of `NegMemClass` / `NegMemClass` 的定义

English:
class NegMemClass
  parameters: (S : Type*) (G : outParam Type*) [Neg G] [SetLike S G]
  axioms and operations (1):
    - neg_mem : forall {s : S} {x}, x in s -> -x in s

中文:
类 NegMemClass
  参数: (S : 类型) (G : outParam 类型) [Neg G] [SetLike S G]
  公理与运算 (1 个):
    - neg_mem : 对任意 {s : S} {x}, x in s -> -x in s
-/
class NegMemClass (S : Type*) (G : outParam Type*) [Neg G] [SetLike S G] : Prop where
  /-- `s` is closed under negation -/
  neg_mem : forall {s : S} {x}, x in s -> -x in s

export NegMemClass (neg_mem)

/--
Definition of `HasMemOrNegMem` / `HasMemOrNegMem` 的定义

English:
class HasMemOrNegMem
  parameters: {S G : Type*} [Neg G] [SetLike S G] (s : S)
  axioms and operations (1):
    - mem_or_neg_mem((s) (a : G)) : a in s ∨ -a in s

中文:
类 HasMemOrNegMem
  参数: {S G : 类型} [Neg G] [SetLike S G] (s : S)
  公理与运算 (1 个):
    - mem_or_neg_mem((s) (a : G)) : a in s ∨ -a in s
-/
class HasMemOrNegMem {S G : Type*} [Neg G] [SetLike S G] (s : S) : Prop where
  mem_or_neg_mem (s) (a : G) : a in s ∨ -a in s

/-- Typeclass for substructures `s` such that `s ∪ s⁻¹ = G`. -/
@[to_additive]
/--
Definition of `HasMemOrInvMem` / `HasMemOrInvMem` 的定义

English:
class HasMemOrInvMem
  parameters: {S G : Type*} [Inv G] [SetLike S G] (s : S)
  axioms and operations (1):
    - mem_or_inv_mem((s) (a : G)) : a in s ∨ a⁻¹ in s

中文:
类 HasMemOrInvMem
  参数: {S G : 类型} [Inv G] [SetLike S G] (s : S)
  公理与运算 (1 个):
    - mem_or_inv_mem((s) (a : G)) : a in s ∨ a⁻¹ in s
-/
class HasMemOrInvMem {S G : Type*} [Inv G] [SetLike S G] (s : S) : Prop where
  mem_or_inv_mem (s) (a : G) : a in s ∨ a⁻¹ in s

export HasMemOrNegMem (mem_or_neg_mem)
export HasMemOrInvMem (mem_or_inv_mem)

namespace HasMemOrInvMem

variable {S G : Type*} [Inv G] [SetLike S G] (s : S) [HasMemOrInvMem s]

@[to_additive (attr := aesop unsafe 70% apply)]
/--
theorem `inv_mem_of_notMem` / 定理 `inv_mem_of_notMem`

English:
theorem inv_mem_of_notMem
  given: (x : G) (h : x ∉ s)
  statement: x⁻¹ in s
  proof: by
  have := mem_or_inv_mem s x
  simp_all

@[to_additive (attr := aesop unsafe 70% apply)]

中文:
定理 inv_mem_of_notMem
  条件: (x : G) (h : x ∉ s)
  结论: x⁻¹ in s
  证明: by
  have := mem_or_inv_mem s x
  simp_all

@[to_additive (attr := aesop unsafe 70% apply)]

Depends on / 依赖: mem_or_inv_mem
-/
theorem inv_mem_of_notMem (x : G) (h : x ∉ s) : x⁻¹ in s := by
  have := mem_or_inv_mem s x
  simp_all

@[to_additive (attr := aesop unsafe 70% apply)]
/--
theorem `mem_of_inv_notMem` / 定理 `mem_of_inv_notMem`

English:
theorem mem_of_inv_notMem
  given: (x : G) (h : x⁻¹ ∉ s)
  statement: x in s
  proof: by
  have := mem_or_inv_mem s x
  simp_all

中文:
定理 mem_of_inv_notMem
  条件: (x : G) (h : x⁻¹ ∉ s)
  结论: x in s
  证明: by
  have := mem_or_inv_mem s x
  simp_all

Depends on / 依赖: mem_or_inv_mem
-/
theorem mem_of_inv_notMem (x : G) (h : x⁻¹ ∉ s) : x in s := by
  have := mem_or_inv_mem s x
  simp_all

end HasMemOrInvMem

/--
Definition of `SubgroupClass` / `SubgroupClass` 的定义

English:
class SubgroupClass
  parameters: (S : Type*) (G : outParam Type*) [DivInvMonoid G] [SetLike S G]
  extends: SubmonoidClass S G, InvMemClass S G
  (no additional axioms)

中文:
类 SubgroupClass
  参数: (S : 类型) (G : outParam 类型) [DivInvMonoid G] [SetLike S G]
  继承: SubmonoidClass S G, InvMemClass S G
  (无附加公理)
-/
class SubgroupClass (S : Type*) (G : outParam Type*) [DivInvMonoid G] [SetLike S G] : Prop
    extends SubmonoidClass S G, InvMemClass S G

/--
Definition of `AddSubgroupClass` / `AddSubgroupClass` 的定义

English:
class AddSubgroupClass
  parameters: (S : Type*) (G : outParam Type*) [SubNegMonoid G] [SetLike S G]
  extends: AddSubmonoidClass S G, NegMemClass S G
  (no additional axioms)

中文:
类 AddSubgroupClass
  参数: (S : 类型) (G : outParam 类型) [SubNegMonoid G] [SetLike S G]
  继承: AddSubmonoidClass S G, NegMemClass S G
  (无附加公理)

Depends on / 依赖: SetLike, inv_mem, neg_mem
-/
class AddSubgroupClass (S : Type*) (G : outParam Type*) [SubNegMonoid G] [SetLike S G] : Prop
    extends AddSubmonoidClass S G, NegMemClass S G

attribute [to_additive] InvMemClass SubgroupClass

attribute [aesop 90% (rule_sets := [SetLike])] inv_mem neg_mem

@[to_additive (attr := simp)]
/--
theorem `inv_mem_iff` / 定理 `inv_mem_iff`

English:
theorem inv_mem_iff
  statement: {S G} [InvolutiveInv G] {_ : SetLike S G} [InvMemClass S G] {H : S}
  proof: ⟨fun h => inv_inv x ▸ inv_mem h, inv_mem⟩

中文:
定理 inv_mem_iff
  结论: {S G} [InvolutiveInv G] {_ : SetLike S G} [InvMemClass S G] {H : S}
  证明: ⟨fun h => inv_inv x ▸ inv_mem h, inv_mem⟩

Depends on / 依赖: inv_inv, inv_mem
-/
theorem inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvMemClass S G] {H : S}
    {x : G} : x⁻¹ in H ↔ x in H :=
  ⟨fun h => inv_inv x ▸ inv_mem h, inv_mem⟩

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

/-- A subgroup is closed under division. -/
@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))
  /-- An additive subgroup is closed under subtraction. -/]
/--
theorem `div_mem` / 定理 `div_mem`

English:
theorem div_mem
  given: {x y : M} (hx : x in H) (hy : y in H)
  statement: x / y in H
  proof: by
  rw [div_eq_mul_inv]; exact mul_mem hx (inv_mem hy)

@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))]

中文:
定理 div_mem
  条件: {x y : M} (hx : x in H) (hy : y in H)
  结论: x / y in H
  证明: by
  rw [div_eq_mul_inv]; exact mul_mem hx (inv_mem hy)

@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))]

Depends on / 依赖: div_eq_mul_inv, inv_mem, mul_mem
-/
theorem div_mem {x y : M} (hx : x in H) (hy : y in H) : x / y in H := by
  rw [div_eq_mul_inv]; exact mul_mem hx (inv_mem hy)

@[to_additive (attr := aesop 90% (rule_sets := [SetLike]))]
/--
theorem `zpow_mem` / 定理 `zpow_mem`

English:
theorem zpow_mem
  given: {x : M} (hx : x in K)
  statement: forall n : Int, x ^ n in K

中文:
定理 zpow_mem
  条件: {x : M} (hx : x in K)
  结论: 对任意 n : 整数, x ^ n in K
-/
theorem zpow_mem {x : M} (hx : x in K) : forall n : Int, x ^ n in K
  | (n : Nat) => by
    rw [zpow_natCast]
    exact pow_mem hx n
  | -[n+1] => by
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hx n.succ)

variable [SetLike S G] [SubgroupClass S G]

@[to_additive]
/--
theorem `exists_inv_mem_iff_exists_mem` / 定理 `exists_inv_mem_iff_exists_mem`

English:
theorem exists_inv_mem_iff_exists_mem
  given: {P : G -> Prop}
  proof: by
  constructor <;>
    · rintro ⟨x, x_in, hx⟩
      exact ⟨x⁻¹, inv_mem x_in, by simp [hx]⟩

@[to_additive]

中文:
定理 exists_inv_mem_iff_exists_mem
  条件: {P : G -> 命题}
  证明: by
  constructor <;>
    · rintro ⟨x, x_in, hx⟩
      exact ⟨x⁻¹, inv_mem x_in, by simp [hx]⟩

@[to_additive]

Depends on / 依赖: inv_mem, x_in
-/
theorem exists_inv_mem_iff_exists_mem {P : G -> Prop} :
    (exists x : G, x in H ∧ P x⁻¹) ↔ exists x in H, P x := by
  constructor <;>
    · rintro ⟨x, x_in, hx⟩
      exact ⟨x⁻¹, inv_mem x_in, by simp [hx]⟩

@[to_additive]
/--
theorem `mul_mem_cancel_right` / 定理 `mul_mem_cancel_right`

English:
theorem mul_mem_cancel_right
  given: {x y : G} (h : x in H)
  statement: y * x in H ↔ y in H
  proof: ⟨fun hba => by simpa using mul_mem hba (inv_mem h), fun hb => mul_mem hb h⟩

@[to_additive]

中文:
定理 mul_mem_cancel_right
  条件: {x y : G} (h : x in H)
  结论: y * x in H ↔ y in H
  证明: ⟨fun hba => by simpa using mul_mem hba (inv_mem h), fun hb => mul_mem hb h⟩

@[to_additive]

Depends on / 依赖: inv_mem, mul_mem
-/
theorem mul_mem_cancel_right {x y : G} (h : x in H) : y * x in H ↔ y in H :=
  ⟨fun hba => by simpa using mul_mem hba (inv_mem h), fun hb => mul_mem hb h⟩

@[to_additive]
/--
theorem `mul_mem_cancel_left` / 定理 `mul_mem_cancel_left`

English:
theorem mul_mem_cancel_left
  given: {x y : G} (h : x in H)
  statement: x * y in H ↔ y in H
  proof: ⟨fun hab => by simpa using mul_mem (inv_mem h) hab, mul_mem h⟩

中文:
定理 mul_mem_cancel_left
  条件: {x y : G} (h : x in H)
  结论: x * y in H ↔ y in H
  证明: ⟨fun hab => by simpa using mul_mem (inv_mem h) hab, mul_mem h⟩

Depends on / 依赖: inv_mem, mul_mem
-/
theorem mul_mem_cancel_left {x y : G} (h : x in H) : x * y in H ↔ y in H :=
  ⟨fun hab => by simpa using mul_mem (inv_mem h) hab, mul_mem h⟩

namespace InvMemClass

/-- A subgroup of a group inherits an inverse. -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits an inverse. -/]
/--
Instance `inv` / 实例 `inv`

English:
instance inv
  signature: {G S : Type*} [Inv G] [SetLike S G] [InvMemClass S G] {H : S}
  body: ⟨fun a => ⟨a⁻¹, inv_mem a.2⟩⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 inv
  签名: {G S : 类型} [Inv G] [SetLike S G] [InvMemClass S G] {H : S}
  定义体: ⟨fun a => ⟨a⁻¹, inv_mem a.2⟩⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: inv_mem
-/
instance inv {G S : Type*} [Inv G] [SetLike S G] [InvMemClass S G] {H : S} : Inv H :=
  ⟨fun a => ⟨a⁻¹, inv_mem a.2⟩⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (x : H)
  statement: (x⁻¹).1 = x.1⁻¹
  proof: rfl

中文:
定理 coe_inv
  条件: (x : H)
  结论: (x⁻¹).1 = x.1⁻¹
  证明: rfl
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
/--
theorem `subset_union` / 定理 `subset_union`

English:
theorem subset_union
  given: [LE S] [IsConcreteLE S G] {H K L : S}
  proof: by
  refine ⟨fun h => ?_, fun h x xH => h.imp (mem_of_le_of_mem · xH) (mem_of_le_of_mem · xH)⟩
  rw [or_iff_not_imp_left]; rw [SetLike.not_le_iff_exists]; rw [← SetLike.coe_subset_coe]
  exact fun ⟨x, xH, xK⟩ y yH => (h <| mul_mem xH yH).elim
    ((h yH).resolve_left fun yK => xK <| (mul_mem_cancel_

中文:
定理 subset_union
  条件: [LE S] [IsConcreteLE S G] {H K L : S}
  证明: by
  refine ⟨fun h => ?_, fun h x xH => h.imp (mem_of_le_of_mem · xH) (mem_of_le_of_mem · xH)⟩
  rw [or_iff_not_imp_left]; rw [SetLike.not_le_iff_exists]; rw [← SetLike.coe_subset_coe]
  exact fun ⟨x, xH, xK⟩ y yH => (h <| mul_mem xH yH).elim
    ((h yH).resolve_left fun yK => xK <| (mul_mem_cancel_

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, SetLike.not_le_iff_exists, coe_subset_coe, h.imp, mem_of_le_of_mem, mul_mem, mul_mem_cancel_left, mul_mem_cancel_right, not_le_iff_exists, or_iff_not_imp_left, resolve_left
-/
theorem subset_union [LE S] [IsConcreteLE S G] {H K L : S} :
    (H : Set G) subseteq K union L ↔ H <= K ∨ H <= L := by
  refine ⟨fun h => ?_, fun h x xH => h.imp (mem_of_le_of_mem · xH) (mem_of_le_of_mem · xH)⟩
  rw [or_iff_not_imp_left]; rw [SetLike.not_le_iff_exists]; rw [← SetLike.coe_subset_coe]
  exact fun ⟨x, xH, xK⟩ y yH => (h <| mul_mem xH yH).elim
    ((h yH).resolve_left fun yK => xK <| (mul_mem_cancel_right yK).mp ·)
    (mul_mem_cancel_left <| (h xH).resolve_left xK).mp

/-- A subgroup of a group inherits a division -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits a subtraction. -/]
/--
Instance `div` / 实例 `div`

English:
instance div
  signature: {G S : Type*} [DivInvMonoid G] [SetLike S G] [SubgroupClass S G] {H : S}
  body: ⟨fun a b => ⟨a / b, div_mem a.2 b.2⟩⟩

中文:
实例 div
  签名: {G S : 类型} [DivInvMonoid G] [SetLike S G] [SubgroupClass S G] {H : S}
  定义体: ⟨fun a b => ⟨a / b, div_mem a.2 b.2⟩⟩

Depends on / 依赖: div_mem
-/
instance div {G S : Type*} [DivInvMonoid G] [SetLike S G] [SubgroupClass S G] {H : S} : Div H :=
  ⟨fun a b => ⟨a / b, div_mem a.2 b.2⟩⟩

/-- A subgroup of a group inherits an integer power. -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits an integer scaling. -/]
/--
Instance `instZPow` / 实例 `instZPow`

English:
instance instZPow
  signature: {M S} [DivInvMonoid M] [SetLike S M] [SubgroupClass S M] {H : S}
  body: ⟨fun a n => ⟨a.1 ^ n, zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instZPow
  签名: {M S} [DivInvMonoid M] [SetLike S M] [SubgroupClass S M] {H : S}
  定义体: ⟨fun a n => ⟨a.1 ^ n, zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: zpow_mem
-/
instance instZPow {M S} [DivInvMonoid M] [SetLike S M] [SubgroupClass S M] {H : S} : Pow H Int :=
  ⟨fun a n => ⟨a.1 ^ n, zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (x y : H)
  statement: (x / y).1 = x.1 / y.1
  proof: rfl

中文:
定理 coe_div
  条件: (x y : H)
  结论: (x / y).1 = x.1 / y.1
  证明: rfl
-/
theorem coe_div (x y : H) : (x / y).1 = x.1 / y.1 :=
  rfl

variable (H)

-- Prefer subclasses of `Group` over subclasses of `SubgroupClass`.
/-- A subgroup of a group inherits a group structure. -/
@[to_additive /-- An additive subgroup of an `AddGroup` inherits an `AddGroup` structure. -/]
instance (priority := 75) toGroup : Group H := fast_instance%
  Subtype.coe_injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

-- Prefer subclasses of `CommGroup` over subclasses of `SubgroupClass`.
/-- A subgroup of a `CommGroup` is a `CommGroup`. -/
@[to_additive /-- An additive subgroup of an `AddCommGroup` is an `AddCommGroup`. -/]
instance (priority := 75) toCommGroup {G : Type*} [CommGroup G] [SetLike S G] [SubgroupClass S G] :
    CommGroup H := fast_instance%
  Subtype.coe_injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-- The natural group hom from a subgroup of group `G` to `G`. -/
@[to_additive (attr := coe)
  /-- The natural group hom from an additive subgroup of `AddGroup` `G` to `G`. -/]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : H ->* G where
  body: ((↑) : H -> G); map_one' := rfl; map_mul' := fun _ _ => rfl

中文:
定义 subtype
  签名: : H ->* G where
  定义体: ((↑) : H -> G); map_one' := rfl; map_mul' := fun _ _ => rfl
-/
protected def subtype : H ->* G where
  toFun := ((↑) : H -> G); map_one' := rfl; map_mul' := fun _ _ => rfl

variable {H} in
@[to_additive (attr := simp)]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: (x : H)
  proof: rfl

@[to_additive]

中文:
引理 subtype_apply
  条件: (x : H)
  证明: rfl

@[to_additive]
-/
lemma subtype_apply (x : H) :
    SubgroupClass.subtype H x = x := rfl

@[to_additive]
/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  proof: Subtype.coe_injective

@[to_additive (attr := simp)]

中文:
引理 subtype_injective
  证明: Subtype.coe_injective

@[to_additive (attr := simp)]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective :
    Function.Injective (SubgroupClass.subtype H) :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: (SubgroupClass.subtype H : H -> G) = ((↑) : H -> G)
  proof: by
  rfl

中文:
定理 coe_subtype
  结论: (SubgroupClass.subtype H : H -> G) = ((↑) : H -> G)
  证明: by
  rfl
-/
theorem coe_subtype : (SubgroupClass.subtype H : H -> G) = ((↑) : H -> G) := by
  rfl

variable {H}

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : H) (n : Nat)
  statement: ((x ^ n : H) : G) = (x : G) ^ n
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_pow
  条件: (x : H) (n : 自然数)
  结论: ((x ^ n : H) : G) = (x : G) ^ n
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (x : H) (n : Int)
  statement: ((x ^ n : H) : G) = (x : G) ^ n
  proof: rfl

中文:
定理 coe_zpow
  条件: (x : H) (n : 整数)
  结论: ((x ^ n : H) : G) = (x : G) ^ n
  证明: rfl
-/
theorem coe_zpow (x : H) (n : Int) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl

/-- The inclusion homomorphism from a subgroup `H` contained in `K` to `K`. -/
@[to_additive
/-- The inclusion homomorphism from an additive subgroup `H` contained in `K` to `K`. -/]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: [LE S] [IsConcreteLE S G] {H K : S} (h : H <= K)
  body: MonoidHom.mk' (fun x => ⟨x, mem_of_le_of_mem h x.prop⟩) fun _ _ => rfl

@[to_additive (attr := simp)]

中文:
定义 inclusion
  签名: [LE S] [IsConcreteLE S G] {H K : S} (h : H <= K)
  定义体: MonoidHom.mk' (fun x => ⟨x, mem_of_le_of_mem h x.prop⟩) fun _ _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.mk, mem_of_le_of_mem, x.prop
-/
def inclusion [LE S] [IsConcreteLE S G] {H K : S} (h : H <= K) : H ->* K :=
  MonoidHom.mk' (fun x => ⟨x, mem_of_le_of_mem h x.prop⟩) fun _ _ => rfl

@[to_additive (attr := simp)]
/--
theorem `inclusion_self` / 定理 `inclusion_self`

English:
theorem inclusion_self
  given: [Preorder S] [IsConcreteLE S G] (x : H)
  statement: inclusion le_rfl x = x
  proof: by
  cases x
  rfl

@[to_additive (attr := simp)]

中文:
定理 inclusion_self
  条件: [Preorder S] [IsConcreteLE S G] (x : H)
  结论: inclusion le_rfl x = x
  证明: by
  cases x
  rfl

@[to_additive (attr := simp)]
-/
theorem inclusion_self [Preorder S] [IsConcreteLE S G] (x : H) : inclusion le_rfl x = x := by
  cases x
  rfl

@[to_additive (attr := simp)]
/--
theorem `inclusion_mk` / 定理 `inclusion_mk`

English:
theorem inclusion_mk
  given: [LE S] [IsConcreteLE S G] {h : H <= K} (x : G) (hx : x in H)
  proof: rfl

@[to_additive]

中文:
定理 inclusion_mk
  条件: [LE S] [IsConcreteLE S G] {h : H <= K} (x : G) (hx : x in H)
  证明: rfl

@[to_additive]
-/
theorem inclusion_mk [LE S] [IsConcreteLE S G] {h : H <= K} (x : G) (hx : x in H) :
    inclusion h ⟨x, hx⟩ = ⟨x, mem_of_le_of_mem h hx⟩ :=
  rfl

@[to_additive]
/--
theorem `inclusion_right` / 定理 `inclusion_right`

English:
theorem inclusion_right
  given: [LE S] [IsConcreteLE S G] (h : H <= K) (x : K) (hx : (x : G) in H)
  proof: by
  cases x
  rfl

@[simp]

中文:
定理 inclusion_right
  条件: [LE S] [IsConcreteLE S G] (h : H <= K) (x : K) (hx : (x : G) in H)
  证明: by
  cases x
  rfl

@[simp]
-/
theorem inclusion_right [LE S] [IsConcreteLE S G] (h : H <= K) (x : K) (hx : (x : G) in H) :
    inclusion h ⟨x, hx⟩ = x := by
  cases x
  rfl

@[simp]
/--
theorem `inclusion_inclusion` / 定理 `inclusion_inclusion`

English:
theorem inclusion_inclusion
  statement: [Preorder S] [IsConcreteLE S G]
  proof: by
  cases x
  rfl

@[to_additive (attr := simp)]

中文:
定理 inclusion_inclusion
  结论: [Preorder S] [IsConcreteLE S G]
  证明: by
  cases x
  rfl

@[to_additive (attr := simp)]
-/
theorem inclusion_inclusion [Preorder S] [IsConcreteLE S G]
    {L : S} (hHK : H <= K) (hKL : K <= L) (x : H) :
    inclusion hKL (inclusion hHK x) = inclusion (hHK.trans hKL) x := by
  cases x
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  statement: [LE S] [IsConcreteLE S G]
  proof: Set.coe_inclusion (SetLike.coe_subset_coe.mpr h) a

@[to_additive (attr := simp)]

中文:
定理 coe_inclusion
  结论: [LE S] [IsConcreteLE S G]
  证明: Set.coe_inclusion (SetLike.coe_subset_coe.mpr h) a

@[to_additive (attr := simp)]

Depends on / 依赖: Set.coe_inclusion, SetLike, SetLike.coe_subset_coe.mpr, coe_inclusion, coe_subset_coe
-/
theorem coe_inclusion [LE S] [IsConcreteLE S G]
    {H K : S} (h : H <= K) (a : H) : (inclusion h a : G) = a :=
  Set.coe_inclusion (SetLike.coe_subset_coe.mpr h) a

@[to_additive (attr := simp)]
/--
theorem `subtype_comp_inclusion` / 定理 `subtype_comp_inclusion`

English:
theorem subtype_comp_inclusion
  statement: [LE S] [IsConcreteLE S G]
  proof: rfl

中文:
定理 subtype_comp_inclusion
  结论: [LE S] [IsConcreteLE S G]
  证明: rfl
-/
theorem subtype_comp_inclusion [LE S] [IsConcreteLE S G]
    {H K : S} (h : H <= K) :
    (SubgroupClass.subtype K).comp (inclusion h) = SubgroupClass.subtype H :=
  rfl

end SubgroupClass

end SubgroupClass

/--
Definition of `Subgroup` / `Subgroup` 的定义

English:
structure Subgroup
  parameters: (G : Type*) [Group G]
  extends: Submonoid G
  axioms and operations (1):
    - inv_mem'({x}) : x in carrier -> x⁻¹ in carrier

中文:
结构 Subgroup
  参数: (G : 类型) [Group G]
  继承: Submonoid G
  公理与运算 (1 个):
    - inv_mem'({x}) : x in carrier -> x⁻¹ in carrier
-/
structure Subgroup (G : Type*) [Group G] extends Submonoid G where
  /-- `G` is closed under inverses -/
  inv_mem' {x} : x in carrier -> x⁻¹ in carrier

/--
Definition of `AddSubgroup` / `AddSubgroup` 的定义

English:
structure AddSubgroup
  parameters: (G : Type*) [AddGroup G]
  extends: AddSubmonoid G
  axioms and operations (1):
    - neg_mem'({x}) : x in carrier -> -x in carrier

中文:
结构 AddSubgroup
  参数: (G : 类型) [AddGroup G]
  继承: AddSubmonoid G
  公理与运算 (1 个):
    - neg_mem'({x}) : x in carrier -> -x in carrier

Depends on / 依赖: Q466109, Subgroup, wikidata
-/
structure AddSubgroup (G : Type*) [AddGroup G] extends AddSubmonoid G where
  /-- `G` is closed under negation -/
  neg_mem' {x} : x in carrier -> -x in carrier

attribute [to_additive (attr := wikidata Q466109)] Subgroup

/-- Reinterpret a `Subgroup` as a `Submonoid`. -/
add_decl_doc Subgroup.toSubmonoid

/-- Reinterpret an `AddSubgroup` as an `AddSubmonoid`. -/
add_decl_doc AddSubgroup.toAddSubmonoid

namespace Subgroup

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subgroup G) G
  body: s.carrier
  coe_injective p q h := by
    obtain ⟨⟨⟨hp, _⟩, _⟩, _⟩ := p
    obtain ⟨⟨⟨hq, _⟩, _⟩, _⟩ := q
    congr

中文:
实例 :
  签名: SetLike (Subgroup G) G
  定义体: s.carrier
  coe_injective p q h := by
    obtain ⟨⟨⟨hp, _⟩, _⟩, _⟩ := p
    obtain ⟨⟨⟨hq, _⟩, _⟩, _⟩ := q
    congr

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (Subgroup G) G where
  coe s := s.carrier
  coe_injective p q h := by
    obtain ⟨⟨⟨hp, _⟩, _⟩, _⟩ := p
    obtain ⟨⟨⟨hq, _⟩, _⟩, _⟩ := q
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subgroup G)
  body: .ofSetLike (Subgroup G) G

initialize_simps_projections Subgroup (carrier -> coe, as_prefix coe)
initialize_simps_projections AddSubgroup (carrier -> coe, as_prefix coe)

中文:
实例 :
  签名: PartialOrder (Subgroup G)
  定义体: .ofSetLike (Subgroup G) G

initialize_simps_projections Subgroup (carrier -> coe, as_prefix coe)
initialize_simps_projections AddSubgroup (carrier -> coe, as_prefix coe)
-/
@[to_additive] instance : PartialOrder (Subgroup G) := .ofSetLike (Subgroup G) G

initialize_simps_projections Subgroup (carrier -> coe, as_prefix coe)
initialize_simps_projections AddSubgroup (carrier -> coe, as_prefix coe)

/-- The actual `Subgroup` obtained from an element of a `SubgroupClass` -/
@[to_additive (attr := simps) /-- The actual `AddSubgroup` obtained from an element of a
`AddSubgroupClass` -/]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S G : Type*} [Group G] [SetLike S G] [SubgroupClass S G]
  body: ⟨⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩, InvMemClass.inv_mem⟩

@[to_additive]

中文:
定义 ofClass
  签名: {S G : 类型} [Group G] [SetLike S G] [SubgroupClass S G]
  定义体: ⟨⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩, InvMemClass.inv_mem⟩

@[to_additive]

Depends on / 依赖: InvMemClass, InvMemClass.inv_mem, MulMemClass, MulMemClass.mul_mem, OneMemClass, OneMemClass.one_mem, inv_mem, mul_mem, one_mem
-/
def ofClass {S G : Type*} [Group G] [SetLike S G] [SubgroupClass S G]
    (s : S) : Subgroup G :=
  ⟨⟨⟨s, MulMemClass.mul_mem⟩, OneMemClass.one_mem s⟩, InvMemClass.inv_mem⟩

@[to_additive]
instance (priority := 100) : CanLift (Set G) (Subgroup G) (↑)
    (fun s => 1 in s ∧ (forall {x y}, x in s -> y in s -> x * y in s) ∧ forall {x}, x in s -> x⁻¹ in s) where
  prf s h := ⟨{ carrier := s, one_mem' := h.1, mul_mem' := h.2.1, inv_mem' := h.2.2}, rfl⟩

-- TODO: Below can probably be written more uniformly
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubgroupClass (Subgroup G) G
  body: Subgroup.inv_mem' _
  one_mem _ := (Subgroup.toSubmonoid _).one_mem'
  mul_mem := (Subgroup.toSubmonoid _).mul_mem'

中文:
实例 :
  签名: SubgroupClass (Subgroup G) G
  定义体: Subgroup.inv_mem' _
  one_mem _ := (Subgroup.toSubmonoid _).one_mem'
  mul_mem := (Subgroup.toSubmonoid _).mul_mem'

Depends on / 依赖: Subgroup, Subgroup.inv_mem, inv_mem
-/
instance : SubgroupClass (Subgroup G) G where
  inv_mem := Subgroup.inv_mem' _
  one_mem _ := (Subgroup.toSubmonoid _).one_mem'
  mul_mem := (Subgroup.toSubmonoid _).mul_mem'

-- This is not a simp lemma,
-- because the simp normal form left-hand side is given by `mem_toSubmonoid` below.
@[to_additive]
/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : Subgroup G} {x : G}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_carrier
  条件: {s : Subgroup G} {x : G}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : Subgroup G} {x : G} : x in s.carrier ↔ x in s :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {s : Submonoid G} {x : G} (h_inv)
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mem_mk
  条件: {s : Submonoid G} {x : G} (h_inv)
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {s : Submonoid G} {x : G} (h_inv) :
    x in mk s h_inv ↔ x in s :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `coe_set_mk` / 定理 `coe_set_mk`

English:
theorem coe_set_mk
  given: {s : Submonoid G} (h_inv)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_set_mk
  条件: {s : Submonoid G} (h_inv)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_set_mk {s : Submonoid G} (h_inv) :
    (mk s h_inv : Set G) = s :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {s t : Submonoid G} (h_inv) (h_inv')
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 mk_le_mk
  条件: {s t : Submonoid G} (h_inv) (h_inv')
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk {s t : Submonoid G} (h_inv) (h_inv') :
    mk s h_inv <= mk t h_inv' ↔ s <= t :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `coe_toSubmonoid` / 定理 `coe_toSubmonoid`

English:
theorem coe_toSubmonoid
  given: (K : Subgroup G)
  statement: (K.toSubmonoid : Set G) = K
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_toSubmonoid
  条件: (K : Subgroup G)
  结论: (K.toSubmonoid : Set G) = K
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_toSubmonoid (K : Subgroup G) : (K.toSubmonoid : Set G) = K :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_toSubmonoid` / 定理 `mem_toSubmonoid`

English:
theorem mem_toSubmonoid
  given: (K : Subgroup G) (x : G)
  statement: x in K.toSubmonoid ↔ x in K
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_toSubmonoid
  条件: (K : Subgroup G) (x : G)
  结论: x in K.toSubmonoid ↔ x in K
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubmonoid (K : Subgroup G) (x : G) : x in K.toSubmonoid ↔ x in K :=
  Iff.rfl

@[to_additive]
/--
theorem `toSubmonoid_injective` / 定理 `toSubmonoid_injective`

English:
theorem toSubmonoid_injective
  statement: Function.Injective (toSubmonoid : Subgroup G -> Submonoid G)
  proof: fun p q h => by
    have := SetLike.ext'_iff.1 h
    rw [coe_toSubmonoid]; rw [coe_toSubmonoid] at this
    exact SetLike.ext'_iff.2 this

@[to_additive (attr := simp)]

中文:
定理 toSubmonoid_injective
  结论: Function.Injective (toSubmonoid : Subgroup G -> Submonoid G)
  证明: fun p q h => by
    have := SetLike.ext'_iff.1 h
    rw [coe_toSubmonoid]; rw [coe_toSubmonoid] at this
    exact SetLike.ext'_iff.2 this

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext, _iff, coe_toSubmonoid
-/
theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subgroup G -> Submonoid G) :=
  fun p q h => by
    have := SetLike.ext'_iff.1 h
    rw [coe_toSubmonoid]; rw [coe_toSubmonoid] at this
    exact SetLike.ext'_iff.2 this

@[to_additive (attr := simp)]
/--
theorem `toSubmonoid_inj` / 定理 `toSubmonoid_inj`

English:
theorem toSubmonoid_inj
  given: {p q : Subgroup G}
  statement: p.toSubmonoid = q.toSubmonoid ↔ p = q
  proof: toSubmonoid_injective.eq_iff

@[to_additive (attr := mono)]

中文:
定理 toSubmonoid_inj
  条件: {p q : Subgroup G}
  结论: p.toSubmonoid = q.toSubmonoid ↔ p = q
  证明: toSubmonoid_injective.eq_iff

@[to_additive (attr := mono)]

Depends on / 依赖: eq_iff, toSubmonoid_injective, toSubmonoid_injective.eq_iff
-/
theorem toSubmonoid_inj {p q : Subgroup G} : p.toSubmonoid = q.toSubmonoid ↔ p = q :=
  toSubmonoid_injective.eq_iff

@[to_additive (attr := mono)]
/--
theorem `toSubmonoid_strictMono` / 定理 `toSubmonoid_strictMono`

English:
theorem toSubmonoid_strictMono
  statement: StrictMono (toSubmonoid : Subgroup G -> Submonoid G)
  proof: fun _ _ =>
  id

@[to_additive (attr := mono)]

中文:
定理 toSubmonoid_strictMono
  结论: StrictMono (toSubmonoid : Subgroup G -> Submonoid G)
  证明: fun _ _ =>
  id

@[to_additive (attr := mono)]
-/
theorem toSubmonoid_strictMono : StrictMono (toSubmonoid : Subgroup G -> Submonoid G) := fun _ _ =>
  id

@[to_additive (attr := mono)]
/--
theorem `toSubmonoid_mono` / 定理 `toSubmonoid_mono`

English:
theorem toSubmonoid_mono
  statement: Monotone (toSubmonoid : Subgroup G -> Submonoid G)
  proof: toSubmonoid_strictMono.monotone

@[to_additive (attr := simp)]

中文:
定理 toSubmonoid_mono
  结论: Monotone (toSubmonoid : Subgroup G -> Submonoid G)
  证明: toSubmonoid_strictMono.monotone

@[to_additive (attr := simp)]

Depends on / 依赖: monotone, toSubmonoid_strictMono, toSubmonoid_strictMono.monotone
-/
theorem toSubmonoid_mono : Monotone (toSubmonoid : Subgroup G -> Submonoid G) :=
  toSubmonoid_strictMono.monotone

@[to_additive (attr := simp)]
/--
theorem `toSubmonoid_le` / 定理 `toSubmonoid_le`

English:
theorem toSubmonoid_le
  given: {p q : Subgroup G}
  statement: p.toSubmonoid <= q.toSubmonoid ↔ p <= q
  proof: Iff.rfl

@[to_additive]

中文:
定理 toSubmonoid_le
  条件: {p q : Subgroup G}
  结论: p.toSubmonoid <= q.toSubmonoid ↔ p <= q
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem toSubmonoid_le {p q : Subgroup G} : p.toSubmonoid <= q.toSubmonoid ↔ p <= q :=
  Iff.rfl

@[to_additive]
/--
lemma `coe_nonempty` / 引理 `coe_nonempty`

English:
lemma coe_nonempty
  given: (s : Subgroup G)
  statement: (s : Set G).Nonempty
  proof: ⟨1, one_mem _⟩

中文:
引理 coe_nonempty
  条件: (s : Subgroup G)
  结论: (s : Set G).Nonempty
  证明: ⟨1, one_mem _⟩

Depends on / 依赖: one_mem
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
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (K : Subgroup G) (s : Set G) (hs : s = K)
  body: s
  one_mem' := hs.symm ▸ K.one_mem'
  mul_mem' := hs.symm ▸ K.mul_mem'
  inv_mem' hx := by simpa [hs] using hx

@[to_additive]

中文:
定义 copy
  签名: (K : Subgroup G) (s : Set G) (hs : s = K)
  定义体: s
  one_mem' := hs.symm ▸ K.one_mem'
  mul_mem' := hs.symm ▸ K.mul_mem'
  inv_mem' hx := by simpa [hs] using hx

@[to_additive]
-/
protected def copy (K : Subgroup G) (s : Set G) (hs : s = K) : Subgroup G where
  carrier := s
  one_mem' := hs.symm ▸ K.one_mem'
  mul_mem' := hs.symm ▸ K.mul_mem'
  inv_mem' hx := by simpa [hs] using hx

@[to_additive]
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (K : Subgroup G) (s : Set G) (hs : s = ↑K)
  statement: K.copy s hs = K
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (K : Subgroup G) (s : Set G) (hs : s = ↑K)
  结论: K.copy s hs = K
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (K : Subgroup G) (s : Set G) (hs : s = ↑K) : K.copy s hs = K :=
  SetLike.coe_injective hs

/-- Two subgroups are equal if they have the same elements. -/
@[to_additive (attr := ext) /-- Two `AddSubgroup`s are equal if they have the same elements. -/]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {H K : Subgroup G} (h : forall x, x in H ↔ x in K)
  statement: H = K
  proof: SetLike.ext h

中文:
定理 ext
  条件: {H K : Subgroup G} (h : 对任意 x, x in H ↔ x in K)
  结论: H = K
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H = K :=
  SetLike.ext h

/-- A subgroup contains the group's 1. -/
@[to_additive /-- An `AddSubgroup` contains the group's 0. -/]
/--
theorem `one_mem` / 定理 `one_mem`

English:
theorem one_mem
  statement: (1 : G) in H
  proof: one_mem _

中文:
定理 one_mem
  结论: (1 : G) in H
  证明: one_mem _
-/
protected theorem one_mem : (1 : G) in H :=
  one_mem _

/-- A subgroup is closed under multiplication. -/
@[to_additive /-- An `AddSubgroup` is closed under addition. -/]
/--
theorem `mul_mem` / 定理 `mul_mem`

English:
theorem mul_mem
  given: {x y : G}
  statement: x in H -> y in H -> x * y in H
  proof: mul_mem

中文:
定理 mul_mem
  条件: {x y : G}
  结论: x in H -> y in H -> x * y in H
  证明: mul_mem
-/
protected theorem mul_mem {x y : G} : x in H -> y in H -> x * y in H :=
  mul_mem

/-- A subgroup is closed under inverse. -/
@[to_additive /-- An `AddSubgroup` is closed under inverse. -/]
/--
theorem `inv_mem` / 定理 `inv_mem`

English:
theorem inv_mem
  given: {x : G}
  statement: x in H -> x⁻¹ in H
  proof: inv_mem

中文:
定理 inv_mem
  条件: {x : G}
  结论: x in H -> x⁻¹ in H
  证明: inv_mem
-/
protected theorem inv_mem {x : G} : x in H -> x⁻¹ in H :=
  inv_mem

/-- A subgroup is closed under division. -/
@[to_additive /-- An `AddSubgroup` is closed under subtraction. -/]
/--
theorem `div_mem` / 定理 `div_mem`

English:
theorem div_mem
  given: {x y : G} (hx : x in H) (hy : y in H)
  statement: x / y in H
  proof: div_mem hx hy

@[to_additive]

中文:
定理 div_mem
  条件: {x y : G} (hx : x in H) (hy : y in H)
  结论: x / y in H
  证明: div_mem hx hy

@[to_additive]
-/
protected theorem div_mem {x y : G} (hx : x in H) (hy : y in H) : x / y in H :=
  div_mem hx hy

@[to_additive]
/--
theorem `inv_mem_iff` / 定理 `inv_mem_iff`

English:
theorem inv_mem_iff
  given: {x : G}
  statement: x⁻¹ in H ↔ x in H
  proof: inv_mem_iff

@[to_additive]

中文:
定理 inv_mem_iff
  条件: {x : G}
  结论: x⁻¹ in H ↔ x in H
  证明: inv_mem_iff

@[to_additive]
-/
protected theorem inv_mem_iff {x : G} : x⁻¹ in H ↔ x in H :=
  inv_mem_iff

@[to_additive]
/--
theorem `exists_inv_mem_iff_exists_mem` / 定理 `exists_inv_mem_iff_exists_mem`

English:
theorem exists_inv_mem_iff_exists_mem
  given: (K : Subgroup G) {P : G -> Prop}
  proof: exists_inv_mem_iff_exists_mem

@[to_additive]

中文:
定理 exists_inv_mem_iff_exists_mem
  条件: (K : Subgroup G) {P : G -> 命题}
  证明: exists_inv_mem_iff_exists_mem

@[to_additive]
-/
protected theorem exists_inv_mem_iff_exists_mem (K : Subgroup G) {P : G -> Prop} :
    (exists x : G, x in K ∧ P x⁻¹) ↔ exists x in K, P x :=
  exists_inv_mem_iff_exists_mem

@[to_additive]
/--
theorem `mul_mem_cancel_right` / 定理 `mul_mem_cancel_right`

English:
theorem mul_mem_cancel_right
  given: {x y : G} (h : x in H)
  statement: y * x in H ↔ y in H
  proof: mul_mem_cancel_right h

@[to_additive]

中文:
定理 mul_mem_cancel_right
  条件: {x y : G} (h : x in H)
  结论: y * x in H ↔ y in H
  证明: mul_mem_cancel_right h

@[to_additive]
-/
protected theorem mul_mem_cancel_right {x y : G} (h : x in H) : y * x in H ↔ y in H :=
  mul_mem_cancel_right h

@[to_additive]
/--
theorem `mul_mem_cancel_left` / 定理 `mul_mem_cancel_left`

English:
theorem mul_mem_cancel_left
  given: {x y : G} (h : x in H)
  statement: x * y in H ↔ y in H
  proof: mul_mem_cancel_left h

@[to_additive]

中文:
定理 mul_mem_cancel_left
  条件: {x y : G} (h : x in H)
  结论: x * y in H ↔ y in H
  证明: mul_mem_cancel_left h

@[to_additive]
-/
protected theorem mul_mem_cancel_left {x y : G} (h : x in H) : x * y in H ↔ y in H :=
  mul_mem_cancel_left h

@[to_additive]
/--
theorem `pow_mem` / 定理 `pow_mem`

English:
theorem pow_mem
  given: {x : G} (hx : x in K)
  statement: forall n : Nat, x ^ n in K
  proof: pow_mem hx

@[to_additive]

中文:
定理 pow_mem
  条件: {x : G} (hx : x in K)
  结论: 对任意 n : 自然数, x ^ n in K
  证明: pow_mem hx

@[to_additive]
-/
protected theorem pow_mem {x : G} (hx : x in K) : forall n : Nat, x ^ n in K :=
  pow_mem hx

@[to_additive]
/--
theorem `zpow_mem` / 定理 `zpow_mem`

English:
theorem zpow_mem
  given: {x : G} (hx : x in K)
  statement: forall n : Int, x ^ n in K
  proof: zpow_mem hx

中文:
定理 zpow_mem
  条件: {x : G} (hx : x in K)
  结论: 对任意 n : 整数, x ^ n in K
  证明: zpow_mem hx

Depends on / 依赖: IsLeftCancelSMul
-/
protected theorem zpow_mem {x : G} (hx : x in K) : forall n : Int, x ^ n in K :=
  zpow_mem hx

/-- Construct a subgroup from a nonempty set that is closed under division. -/
@[to_additive /-- Construct a subgroup from a nonempty set that is closed under subtraction -/]
/--
Definition of `ofDiv` / `ofDiv` 的定义

English:
definition ofDiv
  signature: (s : Set G) (hsn : s.Nonempty) (hs : forallᵉ (x in s) (y in s), x * y⁻¹ in s)
  body: have one_mem : (1 : G) in s := by
    let ⟨x, hx⟩ := hsn
    simpa using hs x hx x hx
  have inv_mem : forall x, x in s -> x⁻¹ in s := fun x hx => by simpa using hs 1 one_mem x hx
  { carrier := s
    one_mem' := one_mem
    inv_mem' := inv_mem _
    mul_mem' := fun hx hy => by simpa using hs _ hx _

中文:
定义 ofDiv
  签名: (s : Set G) (hsn : s.Nonempty) (hs : 对任意ᵉ (x in s) (y in s), x * y⁻¹ in s)
  定义体: have one_mem : (1 : G) in s := by
    let ⟨x, hx⟩ := hsn
    simpa using hs x hx x hx
  have inv_mem : forall x, x in s -> x⁻¹ in s := fun x hx => by simpa using hs 1 one_mem x hx
  { carrier := s
    one_mem' := one_mem
    inv_mem' := inv_mem _
    mul_mem' := fun hx hy => by simpa using hs _ hx _

Depends on / 依赖: IsCancelSMul, carrier, inv_mem, mul_mem, one_mem
-/
def ofDiv (s : Set G) (hsn : s.Nonempty) (hs : forallᵉ (x in s) (y in s), x * y⁻¹ in s) :
    Subgroup G :=
  have one_mem : (1 : G) in s := by
    let ⟨x, hx⟩ := hsn
    simpa using hs x hx x hx
  have inv_mem : forall x, x in s -> x⁻¹ in s := fun x hx => by simpa using hs 1 one_mem x hx
  { carrier := s
    one_mem' := one_mem
    inv_mem' := inv_mem _
    mul_mem' := fun hx hy => by simpa using hs _ hx _ (inv_mem _ hy) }

/-- A subgroup of a group inherits a multiplication. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an addition. -/]
/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : Mul H
  body: H.toSubmonoid.mul

中文:
实例 mul
  签名: : Mul H
  定义体: H.toSubmonoid.mul

Depends on / 依赖: H.toSubmonoid.mul, SMulCommClass, toSubmonoid
-/
instance mul : Mul H :=
  H.toSubmonoid.mul

/-- A subgroup of a group inherits a 1. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits a zero. -/]
/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One H
  body: H.toSubmonoid.one

中文:
实例 one
  签名: : One H
  定义体: H.toSubmonoid.one

Depends on / 依赖: H.toSubmonoid.one, SMulCommClass, toSubmonoid
-/
instance one : One H :=
  H.toSubmonoid.one

/-- A subgroup of a group inherits an inverse. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an inverse. -/]
/--
Instance `inv` / 实例 `inv`

English:
instance inv
  signature: : Inv H
  body: ⟨fun a => ⟨a⁻¹, H.inv_mem a.2⟩⟩

中文:
实例 inv
  签名: : Inv H
  定义体: ⟨fun a => ⟨a⁻¹, H.inv_mem a.2⟩⟩

Depends on / 依赖: H.inv_mem, IsScalarTower, inv_mem
-/
instance inv : Inv H :=
  ⟨fun a => ⟨a⁻¹, H.inv_mem a.2⟩⟩

/-- A subgroup of a group inherits a division -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits a subtraction. -/]
/--
Instance `div` / 实例 `div`

English:
instance div
  signature: : Div H
  body: ⟨fun a b => ⟨a / b, H.div_mem a.2 b.2⟩⟩

中文:
实例 div
  签名: : Div H
  定义体: ⟨fun a b => ⟨a / b, H.div_mem a.2 b.2⟩⟩

Depends on / 依赖: H.div_mem, MulAction, div_mem
-/
instance div : Div H :=
  ⟨fun a b => ⟨a / b, H.div_mem a.2 b.2⟩⟩

/-- A subgroup of a group inherits a natural power -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits a natural scaling. -/]
/--
Instance `npow` / 实例 `npow`

English:
instance npow
  signature: : Pow H Nat
  body: ⟨fun a n => ⟨a ^ n, H.pow_mem a.2 n⟩⟩

中文:
实例 npow
  签名: : Pow H 自然数
  定义体: ⟨fun a n => ⟨a ^ n, H.pow_mem a.2 n⟩⟩
-/
protected instance npow : Pow H Nat :=
  ⟨fun a n => ⟨a ^ n, H.pow_mem a.2 n⟩⟩

/-- A subgroup of a group inherits an integer power -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an integer scaling. -/]
/--
Instance `zpow` / 实例 `zpow`

English:
instance zpow
  signature: : Pow H Int
  body: ⟨fun a n => ⟨a ^ n, H.zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 zpow
  签名: : Pow H 整数
  定义体: ⟨fun a n => ⟨a ^ n, H.zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: H.zpow_mem, zpow_mem
-/
instance zpow : Pow H Int :=
  ⟨fun a n => ⟨a ^ n, H.zpow_mem a.2 n⟩⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : H)
  statement: (↑(x * y) : G) = ↑x * ↑y
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_mul
  条件: (x y : H)
  结论: (↑(x * y) : G) = ↑x * ↑y
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : H) : G) = 1
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_one
  结论: ((1 : H) : G) = 1
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_one : ((1 : H) : G) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (x : H)
  statement: ↑(x⁻¹ : H) = (x⁻¹ : G)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_inv
  条件: (x : H)
  结论: ↑(x⁻¹ : H) = (x⁻¹ : G)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_inv (x : H) : ↑(x⁻¹ : H) = (x⁻¹ : G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (x y : H)
  statement: (↑(x / y) : G) = ↑x / ↑y
  proof: rfl

@[to_additive (attr := norm_cast)]

中文:
定理 coe_div
  条件: (x y : H)
  结论: (↑(x / y) : G) = ↑x / ↑y
  证明: rfl

@[to_additive (attr := norm_cast)]
-/
theorem coe_div (x y : H) : (↑(x / y) : G) = ↑x / ↑y :=
  rfl

@[to_additive (attr := norm_cast)]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (x : G) (hx : x in H)
  statement: ((⟨x, hx⟩ : H) : G) = x
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_mk
  条件: (x : G) (hx : x in H)
  结论: ((⟨x, hx⟩ : H) : G) = x
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_mk (x : G) (hx : x in H) : ((⟨x, hx⟩ : H) : G) = x :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : H) (n : Nat)
  statement: ((x ^ n : H) : G) = (x : G) ^ n
  proof: rfl

@[to_additive (attr := norm_cast)]

中文:
定理 coe_pow
  条件: (x : H) (n : 自然数)
  结论: ((x ^ n : H) : G) = (x : G) ^ n
  证明: rfl

@[to_additive (attr := norm_cast)]
-/
theorem coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G) ^ n :=
  rfl

@[to_additive (attr := norm_cast)]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: (x : H) (n : Int)
  statement: ((x ^ n : H) : G) = (x : G) ^ n
  proof: by
  dsimp

@[to_additive (attr := simp)]

中文:
定理 coe_zpow
  条件: (x : H) (n : 整数)
  结论: ((x ^ n : H) : G) = (x : G) ^ n
  证明: by
  dsimp

@[to_additive (attr := simp)]
-/
theorem coe_zpow (x : H) (n : Int) : ((x ^ n : H) : G) = (x : G) ^ n := by
  dsimp

@[to_additive (attr := simp)]
/--
theorem `mk_eq_one` / 定理 `mk_eq_one`

English:
theorem mk_eq_one
  given: {g : G} {h}
  statement: (⟨g, h⟩ : H) = 1 ↔ g = 1
  proof: Submonoid.mk_eq_one ..

中文:
定理 mk_eq_one
  条件: {g : G} {h}
  结论: (⟨g, h⟩ : H) = 1 ↔ g = 1
  证明: Submonoid.mk_eq_one ..

Depends on / 依赖: Submonoid, Submonoid.mk_eq_one, mk_eq_one
-/
theorem mk_eq_one {g : G} {h} : (⟨g, h⟩ : H) = 1 ↔ g = 1 := Submonoid.mk_eq_one ..

/-- A subgroup of a group inherits a group structure. -/
@[to_additive /-- An `AddSubgroup` of an `AddGroup` inherits an `AddGroup` structure. -/]
/--
Instance `toGroup` / 实例 `toGroup`

English:
instance toGroup
  signature: {G : Type*} [Group G] (H : Subgroup G)
  body: SubgroupClass.toGroup H

中文:
实例 toGroup
  签名: {G : 类型} [Group G] (H : Subgroup G)
  定义体: SubgroupClass.toGroup H

Depends on / 依赖: SubgroupClass, SubgroupClass.toGroup, toGroup
-/
instance toGroup {G : Type*} [Group G] (H : Subgroup G) : Group H :=
  SubgroupClass.toGroup H

/-- A subgroup of a `CommGroup` is a `CommGroup`. -/
@[to_additive /-- An `AddSubgroup` of an `AddCommGroup` is an `AddCommGroup`. -/]
/--
Instance `toCommGroup` / 实例 `toCommGroup`

English:
instance toCommGroup
  signature: {G : Type*} [CommGroup G] (H : Subgroup G)
  body: SubgroupClass.toCommGroup H

中文:
实例 toCommGroup
  签名: {G : 类型} [CommGroup G] (H : Subgroup G)
  定义体: SubgroupClass.toCommGroup H

Depends on / 依赖: SubgroupClass, SubgroupClass.toCommGroup, toCommGroup
-/
instance toCommGroup {G : Type*} [CommGroup G] (H : Subgroup G) : CommGroup H :=
  SubgroupClass.toCommGroup H

/-- The natural group hom from a subgroup of group `G` to `G`. -/
@[to_additive /-- The natural group hom from an `AddSubgroup` of `AddGroup` `G` to `G`. -/]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : H ->* G where
  body: ((↑) : H -> G); map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]

中文:
定义 subtype
  签名: : H ->* G where
  定义体: ((↑) : H -> G); map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]
-/
protected def subtype : H ->* G where
  toFun := ((↑) : H -> G); map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: {s : Subgroup G} (x : s)
  proof: rfl

@[to_additive]

中文:
引理 subtype_apply
  条件: {s : Subgroup G} (x : s)
  证明: rfl

@[to_additive]
-/
lemma subtype_apply {s : Subgroup G} (x : s) :
    s.subtype x = x := rfl

@[to_additive]
/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  given: (s : Subgroup G)
  proof: Subtype.coe_injective

@[to_additive (attr := simp)]

中文:
引理 subtype_injective
  条件: (s : Subgroup G)
  证明: Subtype.coe_injective

@[to_additive (attr := simp)]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective (s : Subgroup G) :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[to_additive (attr := simp)]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: ⇑H.subtype = ((↑) : H -> G)
  proof: rfl

中文:
定理 coe_subtype
  结论: ⇑H.subtype = ((↑) : H -> G)
  证明: rfl
-/
theorem coe_subtype : ⇑H.subtype = ((↑) : H -> G) :=
  rfl

/-- The inclusion homomorphism from a subgroup `H` contained in `K` to `K`. -/
@[to_additive
/-- The inclusion homomorphism from an additive subgroup `H` contained in `K` to `K`. -/]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {H K : Subgroup G} (h : H <= K)
  body: MonoidHom.mk' (fun x => ⟨x, h x.2⟩) fun _ _ => rfl

@[to_additive (attr := simp)]

中文:
定义 inclusion
  签名: {H K : Subgroup G} (h : H <= K)
  定义体: MonoidHom.mk' (fun x => ⟨x, h x.2⟩) fun _ _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.mk
-/
def inclusion {H K : Subgroup G} (h : H <= K) : H ->* K :=
  MonoidHom.mk' (fun x => ⟨x, h x.2⟩) fun _ _ => rfl

@[to_additive (attr := simp)]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: {H K : Subgroup G} (h : H <= K) (a : H)
  statement: (inclusion h a : G) = a
  proof: Set.coe_inclusion h a

@[to_additive]

中文:
定理 coe_inclusion
  条件: {H K : Subgroup G} (h : H <= K) (a : H)
  结论: (inclusion h a : G) = a
  证明: Set.coe_inclusion h a

@[to_additive]

Depends on / 依赖: Set.coe_inclusion, coe_inclusion
-/
theorem coe_inclusion {H K : Subgroup G} (h : H <= K) (a : H) : (inclusion h a : G) = a :=
  Set.coe_inclusion h a

@[to_additive]
/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: {H K : Subgroup G} (h : H <= K)
  statement: Function.Injective inclusion h
  proof: Set.inclusion_injective h

@[to_additive (attr := simp)]

中文:
定理 inclusion_injective
  条件: {H K : Subgroup G} (h : H <= K)
  结论: Function.Injective inclusion h
  证明: Set.inclusion_injective h

@[to_additive (attr := simp)]

Depends on / 依赖: Set.inclusion_injective, inclusion_injective
-/
theorem inclusion_injective {H K : Subgroup G} (h : H <= K) : Function.Injective inclusion h :=
  Set.inclusion_injective h

@[to_additive (attr := simp)]
/--
lemma `inclusion_inj` / 引理 `inclusion_inj`

English:
lemma inclusion_inj
  given: {H K : Subgroup G} (h : H <= K) {x y : H}
  proof: (inclusion_injective h).eq_iff

@[to_additive (attr := simp)]

中文:
引理 inclusion_inj
  条件: {H K : Subgroup G} (h : H <= K) {x y : H}
  证明: (inclusion_injective h).eq_iff

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, inclusion_injective
-/
lemma inclusion_inj {H K : Subgroup G} (h : H <= K) {x y : H} :
    inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff

@[to_additive (attr := simp)]
/--
theorem `subtype_comp_inclusion` / 定理 `subtype_comp_inclusion`

English:
theorem subtype_comp_inclusion
  given: {H K : Subgroup G} (hH : H <= K)
  proof: rfl

中文:
定理 subtype_comp_inclusion
  条件: {H K : Subgroup G} (hH : H <= K)
  证明: rfl
-/
theorem subtype_comp_inclusion {H K : Subgroup G} (hH : H <= K) :
    K.subtype.comp (inclusion hH) = H.subtype :=
  rfl

open Set

/--
Definition of `Normal` / `Normal` 的定义

English:
structure Normal
  parameters: : Prop where
  axioms and operations (1):
    - conj_mem : forall n, n in H -> forall g : G, g * n * g⁻¹ in H

中文:
结构 Normal
  参数: : 命题 where
  公理与运算 (1 个):
    - conj_mem : 对任意 n, n in H -> 对任意 g : G, g * n * g⁻¹ in H
-/
structure Normal : Prop where
  /-- `H` is closed under conjugation -/
  conj_mem : forall n, n in H -> forall g : G, g * n * g⁻¹ in H

attribute [class] Normal

end Subgroup

namespace AddSubgroup

/--
Definition of `Normal` / `Normal` 的定义

English:
structure Normal
  parameters: (H : AddSubgroup A)
  axioms and operations (1):
    - conj_mem : forall n, n in H -> forall g : A, g + n + -g in H

中文:
结构 Normal
  参数: (H : AddSubgroup A)
  公理与运算 (1 个):
    - conj_mem : 对任意 n, n in H -> 对任意 g : A, g + n + -g in H

Depends on / 依赖: Normal, Q743179, Subgroup, Subgroup.Normal, wikidata
-/
structure Normal (H : AddSubgroup A) : Prop where
  /-- `H` is closed under additive conjugation -/
  conj_mem : forall n, n in H -> forall g : A, g + n + -g in H

attribute [to_additive (attr := wikidata Q743179)] Subgroup.Normal

attribute [class] Normal

end AddSubgroup

namespace Subgroup

variable {H : Subgroup G}

@[to_additive]
instance (priority := 100) normal_of_isMulCommutative [IsMulCommutative G] (H : Subgroup G) :
    H.Normal := ⟨by simp [mul_comm']⟩

@[deprecated (since := "2026-04-10")] alias normal_of_comm := normal_of_isMulCommutative

namespace Normal

@[to_additive]
/--
theorem `conj_mem'` / 定理 `conj_mem'`

English:
theorem conj_mem'
  given: (nH : H.Normal) (n : G) (hn : n in H) (g : G)
  proof: by
  convert! nH.conj_mem n hn g⁻¹
  rw [inv_inv]

@[to_additive]

中文:
定理 conj_mem'
  条件: (nH : H.Normal) (n : G) (hn : n in H) (g : G)
  证明: by
  convert! nH.conj_mem n hn g⁻¹
  rw [inv_inv]

@[to_additive]

Depends on / 依赖: conj_mem, convert, inv_inv, nH.conj_mem
-/
theorem conj_mem' (nH : H.Normal) (n : G) (hn : n in H) (g : G) :
    g⁻¹ * n * g in H := by
  convert! nH.conj_mem n hn g⁻¹
  rw [inv_inv]

@[to_additive]
/--
theorem `mem_comm` / 定理 `mem_comm`

English:
theorem mem_comm
  given: (nH : H.Normal) {a b : G} (h : a * b in H)
  statement: b * a in H
  proof: by
  have : a⁻¹ * (a * b) * a⁻¹⁻¹ in H := nH.conj_mem (a * b) h a⁻¹
  simpa

@[to_additive]

中文:
定理 mem_comm
  条件: (nH : H.Normal) {a b : G} (h : a * b in H)
  结论: b * a in H
  证明: by
  have : a⁻¹ * (a * b) * a⁻¹⁻¹ in H := nH.conj_mem (a * b) h a⁻¹
  simpa

@[to_additive]

Depends on / 依赖: conj_mem, nH.conj_mem
-/
theorem mem_comm (nH : H.Normal) {a b : G} (h : a * b in H) : b * a in H := by
  have : a⁻¹ * (a * b) * a⁻¹⁻¹ in H := nH.conj_mem (a * b) h a⁻¹
  simpa

@[to_additive]
/--
theorem `mem_comm_iff` / 定理 `mem_comm_iff`

English:
theorem mem_comm_iff
  given: (nH : H.Normal) {a b : G}
  statement: a * b in H ↔ b * a in H
  proof: ⟨nH.mem_comm, nH.mem_comm⟩

中文:
定理 mem_comm_iff
  条件: (nH : H.Normal) {a b : G}
  结论: a * b in H ↔ b * a in H
  证明: ⟨nH.mem_comm, nH.mem_comm⟩

Depends on / 依赖: mem_comm, nH.mem_comm
-/
theorem mem_comm_iff (nH : H.Normal) {a b : G} : a * b in H ↔ b * a in H :=
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
/--
Definition of `normalizer` / `normalizer` 的定义

English:
definition normalizer
  signature: (S : Set G)
  body: { g : G | forall n, n in S ↔ g * n * g⁻¹ in S }
  one_mem' := by simp
  mul_mem' {a b} (ha : forall n, n in S ↔ a * n * a⁻¹ in S) (hb : forall n, n in S ↔ b * n * b⁻¹ in S) n := by
    rw [hb]; rw [ha]
    simp only [mul_assoc, mul_inv_rev]
  inv_mem' {a} (ha : forall n, n in S ↔ a * n * a⁻¹ in S) n

中文:
定义 normalizer
  签名: (S : Set G)
  定义体: { g : G | forall n, n in S ↔ g * n * g⁻¹ in S }
  one_mem' := by simp
  mul_mem' {a b} (ha : forall n, n in S ↔ a * n * a⁻¹ in S) (hb : forall n, n in S ↔ b * n * b⁻¹ in S) n := by
    rw [hb]; rw [ha]
    simp only [mul_assoc, mul_inv_rev]
  inv_mem' {a} (ha : forall n, n in S ↔ a * n * a⁻¹ in S) n
-/
def normalizer (S : Set G) : Subgroup G where
  carrier := { g : G | forall n, n in S ↔ g * n * g⁻¹ in S }
  one_mem' := by simp
  mul_mem' {a b} (ha : forall n, n in S ↔ a * n * a⁻¹ in S) (hb : forall n, n in S ↔ b * n * b⁻¹ in S) n := by
    rw [hb]; rw [ha]
    simp only [mul_assoc, mul_inv_rev]
  inv_mem' {a} (ha : forall n, n in S ↔ a * n * a⁻¹ in S) n := by
    rw [ha (a⁻¹ * n * a⁻¹⁻¹)]
    simp only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

@[deprecated (since := "2026-03-19")]
alias setNormalizer := normalizer
@[deprecated (since := "2026-03-19")]
alias _root_.AddSubgroup.setNormalizer := AddSubgroup.normalizer

variable {H} {S : Set G} {g : G}

@[to_additive]
/--
theorem `mem_set_normalizer_iff` / 定理 `mem_set_normalizer_iff`

English:
theorem mem_set_normalizer_iff
  statement: g in normalizer S ↔ forall h, h in S ↔ g * h * g⁻¹ in S
  proof: .rfl

@[to_additive]

中文:
定理 mem_set_normalizer_iff
  结论: g in normalizer S ↔ 对任意 h, h in S ↔ g * h * g⁻¹ in S
  证明: .rfl

@[to_additive]
-/
theorem mem_set_normalizer_iff : g in normalizer S ↔ forall h, h in S ↔ g * h * g⁻¹ in S :=
  .rfl

@[to_additive]
/--
theorem `mem_set_normalizer_iff''` / 定理 `mem_set_normalizer_iff''`

English:
theorem mem_set_normalizer_iff''
  statement: g in normalizer S ↔ forall h, h in S ↔ g⁻¹ * h * g in S
  proof: by
  rw [← inv_mem_iff]; rw [mem_set_normalizer_iff]; rw [inv_inv]

@[to_additive]

中文:
定理 mem_set_normalizer_iff''
  结论: g in normalizer S ↔ 对任意 h, h in S ↔ g⁻¹ * h * g in S
  证明: by
  rw [← inv_mem_iff]; rw [mem_set_normalizer_iff]; rw [inv_inv]

@[to_additive]

Depends on / 依赖: inv_inv, inv_mem_iff, mem_set_normalizer_iff
-/
theorem mem_set_normalizer_iff'' : g in normalizer S ↔ forall h, h in S ↔ g⁻¹ * h * g in S := by
  rw [← inv_mem_iff]; rw [mem_set_normalizer_iff]; rw [inv_inv]

@[to_additive]
/--
theorem `mem_set_normalizer_iff'` / 定理 `mem_set_normalizer_iff'`

English:
theorem mem_set_normalizer_iff'
  statement: g in normalizer S ↔ forall h, h * g in S ↔ g * h in S
  proof: ⟨fun h n => by rw [h, mul_assoc, mul_inv_cancel_right],
    fun h n => by rw [mul_assoc, ← h, inv_mul_cancel_right]⟩

@[to_additive]

中文:
定理 mem_set_normalizer_iff'
  结论: g in normalizer S ↔ 对任意 h, h * g in S ↔ g * h in S
  证明: ⟨fun h n => by rw [h, mul_assoc, mul_inv_cancel_right],
    fun h n => by rw [mul_assoc, ← h, inv_mul_cancel_right]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_right, mul_assoc, mul_inv_cancel_right
-/
theorem mem_set_normalizer_iff' : g in normalizer S ↔ forall h, h * g in S ↔ g * h in S :=
  ⟨fun h n => by rw [h, mul_assoc, mul_inv_cancel_right],
    fun h n => by rw [mul_assoc, ← h, inv_mul_cancel_right]⟩

@[to_additive]
/--
theorem `mem_normalizer_iff` / 定理 `mem_normalizer_iff`

English:
theorem mem_normalizer_iff
  statement: g in normalizer H ↔ forall h, h in H ↔ g * h * g⁻¹ in H
  proof: mem_set_normalizer_iff

@[to_additive]

中文:
定理 mem_normalizer_iff
  结论: g in normalizer H ↔ 对任意 h, h in H ↔ g * h * g⁻¹ in H
  证明: mem_set_normalizer_iff

@[to_additive]

Depends on / 依赖: mem_set_normalizer_iff
-/
theorem mem_normalizer_iff : g in normalizer H ↔ forall h, h in H ↔ g * h * g⁻¹ in H :=
  mem_set_normalizer_iff

@[to_additive]
/--
theorem `mem_normalizer_iff''` / 定理 `mem_normalizer_iff''`

English:
theorem mem_normalizer_iff''
  statement: g in normalizer H ↔ forall h : G, h in H ↔ g⁻¹ * h * g in H
  proof: mem_set_normalizer_iff''

@[to_additive]

中文:
定理 mem_normalizer_iff''
  结论: g in normalizer H ↔ 对任意 h : G, h in H ↔ g⁻¹ * h * g in H
  证明: mem_set_normalizer_iff''

@[to_additive]

Depends on / 依赖: mem_set_normalizer_iff
-/
theorem mem_normalizer_iff'' : g in normalizer H ↔ forall h : G, h in H ↔ g⁻¹ * h * g in H :=
  mem_set_normalizer_iff''

@[to_additive]
/--
theorem `mem_normalizer_iff'` / 定理 `mem_normalizer_iff'`

English:
theorem mem_normalizer_iff'
  statement: g in normalizer H ↔ forall n, n * g in H ↔ g * n in H
  proof: mem_set_normalizer_iff'

@[to_additive]

中文:
定理 mem_normalizer_iff'
  结论: g in normalizer H ↔ 对任意 n, n * g in H ↔ g * n in H
  证明: mem_set_normalizer_iff'

@[to_additive]

Depends on / 依赖: mem_set_normalizer_iff
-/
theorem mem_normalizer_iff' : g in normalizer H ↔ forall n, n * g in H ↔ g * n in H :=
  mem_set_normalizer_iff'

@[to_additive]
/--
theorem `le_normalizer` / 定理 `le_normalizer`

English:
theorem le_normalizer
  statement: H <= normalizer H
  proof: fun x xH n => by
  rw [SetLike.mem_coe]; rw [SetLike.mem_coe]; rw [H.mul_mem_cancel_right <| H.inv_mem xH]; rw [H.mul_mem_cancel_left xH]

中文:
定理 le_normalizer
  结论: H <= normalizer H
  证明: fun x xH n => by
  rw [SetLike.mem_coe]; rw [SetLike.mem_coe]; rw [H.mul_mem_cancel_right <| H.inv_mem xH]; rw [H.mul_mem_cancel_left xH]

Depends on / 依赖: H.inv_mem, H.mul_mem_cancel_left, H.mul_mem_cancel_right, SetLike, SetLike.mem_coe, inv_mem, mem_coe, mul_mem_cancel_left, mul_mem_cancel_right
-/
theorem le_normalizer : H <= normalizer H := fun x xH n => by
  rw [SetLike.mem_coe]; rw [SetLike.mem_coe]; rw [H.mul_mem_cancel_right <| H.inv_mem xH]; rw [H.mul_mem_cancel_left xH]

end Normalizer

@[to_additive (attr := deprecated inferInstance (since := "2026-04-09"))]
/--
theorem `commGroup_isMulCommutative` / 定理 `commGroup_isMulCommutative`

English:
theorem commGroup_isMulCommutative
  given: {G : Type*} [CommGroup G] (H : Subgroup G)
  proof: inferInstance

@[to_additive (attr := deprecated setLike_mul_comm (since := "2026-03-09"))]

中文:
定理 commGroup_isMulCommutative
  条件: {G : 类型} [CommGroup G] (H : Subgroup G)
  证明: inferInstance

@[to_additive (attr := deprecated setLike_mul_comm (since := "2026-03-09"))]
-/
theorem commGroup_isMulCommutative {G : Type*} [CommGroup G] (H : Subgroup G) :
    IsMulCommutative H := inferInstance

@[to_additive (attr := deprecated setLike_mul_comm (since := "2026-03-09"))]
/--
lemma `mul_comm_of_mem_isMulCommutative` / 引理 `mul_comm_of_mem_isMulCommutative`

English:
lemma mul_comm_of_mem_isMulCommutative
  given: [IsMulCommutative H] {a b : G} (ha : a in H) (hb : b in H)
  proof: setLike_mul_comm ha hb

中文:
引理 mul_comm_of_mem_isMulCommutative
  条件: [IsMulCommutative H] {a b : G} (ha : a in H) (hb : b in H)
  证明: setLike_mul_comm ha hb

Depends on / 依赖: setLike_mul_comm
-/
lemma mul_comm_of_mem_isMulCommutative [IsMulCommutative H] {a b : G} (ha : a in H) (hb : b in H) :
    a * b = b * a :=
  setLike_mul_comm ha hb

end Subgroup

@[to_additive]
/--
theorem `Set.injOn_iff_map_eq_one` / 定理 `Set.injOn_iff_map_eq_one`

English:
theorem Set.injOn_iff_map_eq_one
  statement: {F G H S : Type*} [Group G] [Group H]
  proof: by
    refine h ha (one_mem s) ?_
    rwa [map_one]
  mpr h x hx y hy hxy := by
refine mul_inv_eq_one.1 h _ (mul_mem ?_ (inv_mem ?_)) ?_ <;> simp_all

中文:
定理 Set.injOn_iff_map_eq_one
  结论: {F G H S : 类型} [Group G] [Group H]
  证明: by
    refine h ha (one_mem s) ?_
    rwa [map_one]
  mpr h x hx y hy hxy := by
refine mul_inv_eq_one.1 h _ (mul_mem ?_ (inv_mem ?_)) ?_ <;> simp_all

Depends on / 依赖: inv_mem, map_one, mul_inv_eq_one, mul_mem, one_mem
-/
theorem Set.injOn_iff_map_eq_one {F G H S : Type*} [Group G] [Group H]
    [FunLike F G H] [MonoidHomClass F G H] (f : F)
    [SetLike S G] [OneMemClass S G] [MulMemClass S G] [InvMemClass S G] (s : S) :
    Set.InjOn f s ↔ forall a in s, f a = 1 -> a = 1 where
  mp h a ha ha' := by
    refine h ha (one_mem s) ?_
    rwa [map_one]
  mpr h x hx y hy hxy := by
refine mul_inv_eq_one.1 h _ (mul_mem ?_ (inv_mem ?_)) ?_ <;> simp_all
