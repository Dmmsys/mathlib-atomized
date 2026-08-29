/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Order.WellFoundedSet

/-!
# Pointwise instances on `Submonoid`s and `AddSubmonoid`s

This file provides:

* `Submonoid.inv`
* `AddSubmonoid.neg`

and the actions

* `Submonoid.pointwiseMulAction`
* `AddSubmonoid.pointwiseAddAction`

which matches the action of `Set.mulActionSet`.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from
`Mathlib/Algebra/Group/Pointwise/Set/Basic.lean` and
`Mathlib/Algebra/Group/Action/Pointwise/Set/Basic.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `Set`s.
-/

@[expose] public section

assert_not_exists GroupWithZero

open Set Pointwise

variable {α G M R A S : Type*}
variable [Monoid M] [AddMonoid A]

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_mul_coe` / 引理 `coe_mul_coe`

English:
lemma coe_mul_coe
  given: [SetLike S M] [SubmonoidClass S M] (H : S)
  statement: H * H = (H : Set M)
  proof: by
  aesop (add simp mem_mul)

@[to_additive]

中文:
引理 coe_mul_coe
  条件: [集合状 S M] [子幺半群类 S M] (H : S)
  结论: H * H = (H : 集合 M)
  证明: by
  aesop (add simp mem_mul)

@[to_additive]

Depends on / 依赖: mem_mul
-/
lemma coe_mul_coe [SetLike S M] [SubmonoidClass S M] (H : S) : H * H = (H : Set M) := by
  aesop (add simp mem_mul)

@[to_additive]
/--
lemma `Set.subtype_smul_set` / 引理 `Set.subtype_smul_set`

English:
lemma Set.subtype_smul_set
  given: {S α β : Type*} [SMul α β] [SetLike S α] {s : S} (x : s) (t : Set β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 集合.subtype_smul_set
  条件: {S α β : 类型} [标量乘法 α β] [集合状 S α] {s : S} (x : s) (t : 集合 β)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma Set.subtype_smul_set {S α β : Type*} [SMul α β] [SetLike S α] {s : S} (x : s) (t : Set β) :
    (x • t : Set β) = (x : α) • t :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `coe_set_pow` / 引理 `coe_set_pow`

English:
lemma coe_set_pow
  given: [SetLike S M] [SubmonoidClass S M]

中文:
引理 coe_set_pow
  条件: [集合状 S M] [子幺半群类 S M]
-/
lemma coe_set_pow [SetLike S M] [SubmonoidClass S M] :
    forall {n} (_ : n != 0) (H : S), (H ^ n : Set M) = H
  | 1, _, H => by simp
  | n + 2, _, H => by rw [pow_succ, coe_set_pow n.succ_ne_zero, coe_mul_coe]

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `GroupTheory.Submonoid.Basic`, but currently we cannot because that file is imported by this. -/

namespace Submonoid

variable {s t u : Set M}

@[to_additive (attr := simp)]
/--
theorem `mul_subset` / 定理 `mul_subset`

English:
theorem mul_subset
  given: {S : Submonoid M} (hs : s subseteq S) (ht : t subseteq S)
  statement: s * t subseteq S
  proof: mul_subset_iff.2 fun _x hx _y hy => mul_mem (hs hx) (ht hy)

@[to_additive (attr := simp)]

中文:
定理 mul_subset
  条件: {S : 子幺半群 M} (hs : s subseteq S) (ht : t subseteq S)
  结论: s * t subseteq S
  证明: mul_subset_iff.2 fun _x hx _y hy => mul_mem (hs hx) (ht hy)

@[to_additive (attr := simp)]

Depends on / 依赖: mul_mem, mul_subset_iff
-/
theorem mul_subset {S : Submonoid M} (hs : s subseteq S) (ht : t subseteq S) : s * t subseteq S :=
  mul_subset_iff.2 fun _x hx _y hy => mul_mem (hs hx) (ht hy)

@[to_additive (attr := simp)]
/--
lemma `pow_subset` / 引理 `pow_subset`

English:
lemma pow_subset
  given: {S : Submonoid M} {n : Nat} (hs : s subseteq S)
  statement: s ^ n subseteq S
  proof: by
  induction n <;> simp [pow_succ, *]

@[to_additive]

中文:
引理 pow_subset
  条件: {S : 子幺半群 M} {n : 自然数} (hs : s subseteq S)
  结论: s ^ n subseteq S
  证明: by
  induction n <;> simp [pow_succ, *]

@[to_additive]

Depends on / 依赖: pow_succ
-/
lemma pow_subset {S : Submonoid M} {n : Nat} (hs : s subseteq S) : s ^ n subseteq S := by
  induction n <;> simp [pow_succ, *]

@[to_additive]
/--
theorem `mul_subset_closure` / 定理 `mul_subset_closure`

English:
theorem mul_subset_closure
  given: (hs : s subseteq u) (ht : t subseteq u)
  statement: s * t subseteq Submonoid.closure u
  proof: mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)

@[to_additive]

中文:
定理 mul_subset_closure
  条件: (hs : s subseteq u) (ht : t subseteq u)
  结论: s * t subseteq 子幺半群.closure u
  证明: mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.subset_closure, Subset, Subset.trans, mul_subset, subset_closure
-/
theorem mul_subset_closure (hs : s subseteq u) (ht : t subseteq u) : s * t subseteq Submonoid.closure u :=
  mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)

@[to_additive]
/--
theorem `coe_mul_self_eq` / 定理 `coe_mul_self_eq`

English:
theorem coe_mul_self_eq
  given: (s : Submonoid M)
  statement: (s : Set M) * s = s
  proof: by
  simp

@[to_additive]

中文:
定理 coe_mul_self_eq
  条件: (s : 子幺半群 M)
  结论: (s : 集合 M) * s = s
  证明: by
  simp

@[to_additive]
-/
theorem coe_mul_self_eq (s : Submonoid M) : (s : Set M) * s = s := by
  simp

@[to_additive]
/--
theorem `closure_mul_le` / 定理 `closure_mul_le`

English:
theorem closure_mul_le
  given: (S T : Set M)
  statement: closure (S * T) <= closure S ⊔ closure T
  proof: sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

中文:
定理 closure_mul_le
  条件: (S T : 集合 M)
  结论: closure (S * T) <= closure S ⊔ closure T
  证明: sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

Depends on / 依赖: SetLike, SetLike.le_def.mp, closure, le_def, le_sup_left, le_sup_right, mul_mem, sInf_le, subset_closure
-/
theorem closure_mul_le (S T : Set M) : closure (S * T) <= closure S ⊔ closure T :=
  sInf_le fun _x ⟨_s, hs, _t, ht, hx⟩ => hx ▸
    (closure S ⊔ closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
      (SetLike.le_def.mp le_sup_right <| subset_closure ht)

/--
lemma `closure_pow_le` / 引理 `closure_pow_le`

English:
lemma closure_pow_le
  given: {n : Nat}
  statement: closure (s ^ n) <= closure s
  proof: by simp

@[to_additive]

中文:
引理 closure_pow_le
  条件: {n : 自然数}
  结论: closure (s ^ n) <= closure s
  证明: by simp

@[to_additive]
-/
@[to_additive] lemma closure_pow_le {n : Nat} : closure (s ^ n) <= closure s := by simp

@[to_additive]
/--
lemma `closure_pow_anti` / 引理 `closure_pow_anti`

English:
lemma closure_pow_anti
  given: {m n : Nat} (hmn : m ∣ n)
  statement: closure (s ^ n) <= closure (s ^ m)
  proof: by
  obtain ⟨k, rfl⟩ := hmn
  simp [pow_mul]

@[to_additive]

中文:
引理 closure_pow_anti
  条件: {m n : 自然数} (hmn : m ∣ n)
  结论: closure (s ^ n) <= closure (s ^ m)
  证明: by
  obtain ⟨k, rfl⟩ := hmn
  simp [pow_mul]

@[to_additive]

Depends on / 依赖: pow_mul
-/
lemma closure_pow_anti {m n : Nat} (hmn : m ∣ n) : closure (s ^ n) <= closure (s ^ m) := by
  obtain ⟨k, rfl⟩ := hmn
  simp [pow_mul]

@[to_additive]
/--
lemma `closure_pow` / 引理 `closure_pow`

English:
lemma closure_pow
  given: {n : Nat} (hs : 1 in s) (hn : n != 0)
  statement: closure (s ^ n) = closure s
  proof: closure_pow_le.antisymm by grw [← subset_pow hs hn]

@[to_additive]

中文:
引理 closure_pow
  条件: {n : 自然数} (hs : 1 in s) (hn : n != 0)
  结论: closure (s ^ n) = closure s
  证明: closure_pow_le.antisymm by grw [← subset_pow hs hn]

@[to_additive]

Depends on / 依赖: antisymm, closure_pow_le, closure_pow_le.antisymm, subset_pow
-/
lemma closure_pow {n : Nat} (hs : 1 in s) (hn : n != 0) : closure (s ^ n) = closure s :=
closure_pow_le.antisymm by grw [← subset_pow hs hn]

@[to_additive]
/--
theorem `sup_eq_closure_mul` / 定理 `sup_eq_closure_mul`

English:
theorem sup_eq_closure_mul
  given: (H K : Submonoid M)
  statement: H ⊔ K = closure ((H : Set M) * (K : Set M))
  proof: le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[to_additive]

中文:
定理 sup_eq_closure_mul
  条件: (H K : 子幺半群 M)
  结论: H ⊔ K = closure ((H : 集合 M) * (K : 集合 M))
  证明: le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[to_additive]

Depends on / 依赖: H.one_mem, K.one_mem, closure_eq, closure_mul_le, le_antisymm, mul_one, one_mem, one_mul, subset_closure, sup_le
-/
theorem sup_eq_closure_mul (H K : Submonoid M) : H ⊔ K = closure ((H : Set M) * (K : Set M)) :=
  le_antisymm
    (sup_le (fun h hh => subset_closure ⟨h, hh, 1, K.one_mem, mul_one h⟩) fun k hk =>
      subset_closure ⟨1, H.one_mem, k, hk, one_mul k⟩)
    ((closure_mul_le _ _).trans <| by rw [closure_eq, closure_eq])

@[to_additive]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: {N : Type*} [CommMonoid N] (H K : Submonoid N)
  proof: by
  ext x
  simp [mem_sup, Set.mem_mul]

@[to_additive]

中文:
定理 coe_sup
  条件: {N : 类型} [交换幺半群 N] (H K : 子幺半群 N)
  证明: by
  ext x
  simp [mem_sup, Set.mem_mul]

@[to_additive]

Depends on / 依赖: Set.mem_mul, mem_mul, mem_sup
-/
theorem coe_sup {N : Type*} [CommMonoid N] (H K : Submonoid N) :
    ↑(H ⊔ K) = (H * K : Set N) := by
  ext x
  simp [mem_sup, Set.mem_mul]

@[to_additive]
/--
theorem `pow_smul_mem_closure_smul` / 定理 `pow_smul_mem_closure_smul`

English:
theorem pow_smul_mem_closure_smul
  statement: {N : Type*} [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
  proof: by
  induction hx using closure_induction with
  | mem x hx => exact ⟨1, subset_closure ⟨_, hx, by rw [pow_one]⟩⟩
  | one => exact ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨⟨nx, hx⟩, ⟨ny, hy⟩⟩ := And.intro hx hy
    use ny + nx
    rw [pow_add]; rw [mul_smul]; rw [← smul_mul_assoc]; rw [mul_comm]; rw [← smul_mul_assoc]
    exact mul_mem hy hx

中文:
定理 pow_smul_mem_closure_smul
  结论: {N : 类型} [交换幺半群 N] [乘法作用 M N] [标量塔 M N N]
  证明: by
  induction hx using closure_induction with
  | mem x hx => exact ⟨1, subset_closure ⟨_, hx, by rw [pow_one]⟩⟩
  | one => exact ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨⟨nx, hx⟩, ⟨ny, hy⟩⟩ := And.intro hx hy
    use ny + nx
    rw [pow_add]; rw [mul_smul]; rw [← smul_mul_assoc]; rw [mul_comm]; rw [← smul_mul_assoc]
    exact mul_mem hy hx

Depends on / 依赖: And.intro, closure_induction, mul_comm, mul_mem, mul_smul, pow_add, pow_one, smul_mul_assoc, subset_closure
-/
theorem pow_smul_mem_closure_smul {N : Type*} [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    (r : M) (s : Set N) {x : N} (hx : x in closure s) : exists n : Nat, r ^ n • x in closure (r • s) := by
  induction hx using closure_induction with
  | mem x hx => exact ⟨1, subset_closure ⟨_, hx, by rw [pow_one]⟩⟩
  | one => exact ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨⟨nx, hx⟩, ⟨ny, hy⟩⟩ := And.intro hx hy
    use ny + nx
    rw [pow_add]; rw [mul_smul]; rw [← smul_mul_assoc]; rw [mul_comm]; rw [← smul_mul_assoc]
    exact mul_mem hy hx

variable [Group G]

/-- The submonoid with every element inverted. -/
@[to_additive (attr := instance_reducible)
  /-- The additive submonoid with every element negated. -/]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : Inv (Submonoid G) where
  body: { carrier := (S : Set G)⁻¹
      mul_mem' := fun ha hb => by rw [mem_inv, mul_inv_rev]; exact mul_mem hb ha
one_mem' := mem_inv.2 by rw [inv_one]; exact S.one_mem' }

scoped[Pointwise] attribute [instance] Submonoid.inv AddSubmonoid.neg

@[to_additive (attr := simp)]

中文:
定义 inv
  签名: : 取逆 (子幺半群 G) where
  定义体: { carrier := (S : Set G)⁻¹
      mul_mem' := fun ha hb => by rw [mem_inv, mul_inv_rev]; exact mul_mem hb ha
one_mem' := mem_inv.2 by rw [inv_one]; exact S.one_mem' }

scoped[Pointwise] attribute [instance] Submonoid.inv AddSubmonoid.neg

@[to_additive (attr := simp)]
-/
protected def inv : Inv (Submonoid G) where
  inv S :=
    { carrier := (S : Set G)⁻¹
      mul_mem' := fun ha hb => by rw [mem_inv, mul_inv_rev]; exact mul_mem hb ha
one_mem' := mem_inv.2 by rw [inv_one]; exact S.one_mem' }

scoped[Pointwise] attribute [instance] Submonoid.inv AddSubmonoid.neg

@[to_additive (attr := simp)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (S : Submonoid G)
  statement: ↑S⁻¹ = (S : Set G)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_inv
  条件: (S : 子幺半群 G)
  结论: ↑S⁻¹ = (S : 集合 G)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_inv (S : Submonoid G) : ↑S⁻¹ = (S : Set G)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_inv` / 定理 `mem_inv`

English:
theorem mem_inv
  given: {g : G} {S : Submonoid G}
  statement: g in S⁻¹ ↔ g⁻¹ in S
  proof: Iff.rfl

中文:
定理 mem_inv
  条件: {g : G} {S : 子幺半群 G}
  结论: g in S⁻¹ ↔ g⁻¹ in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inv {g : G} {S : Submonoid G} : g in S⁻¹ ↔ g⁻¹ in S :=
  Iff.rfl

/-- Inversion is involutive on submonoids. -/
@[to_additive (attr := instance_reducible) /-- Inversion is involutive on additive submonoids. -/]
/--
Definition of `involutiveInv` / `involutiveInv` 的定义

English:
definition involutiveInv
  signature: : InvolutiveInv (Submonoid G)
  body: SetLike.coe_injective.involutiveInv _ fun _ => rfl

scoped[Pointwise] attribute [instance] Submonoid.involutiveInv AddSubmonoid.involutiveNeg

@[to_additive (attr := simp)]

中文:
定义 involutiveInv
  签名: : InvolutiveInv (子幺半群 G)
  定义体: SetLike.coe_injective.involutiveInv _ fun _ => rfl

scoped[Pointwise] attribute [instance] Submonoid.involutiveInv AddSubmonoid.involutiveNeg

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.coe_injective.involutiveInv, coe_injective, involutiveInv
-/
def involutiveInv : InvolutiveInv (Submonoid G) :=
  SetLike.coe_injective.involutiveInv _ fun _ => rfl

scoped[Pointwise] attribute [instance] Submonoid.involutiveInv AddSubmonoid.involutiveNeg

@[to_additive (attr := simp)]
/--
theorem `inv_le_inv` / 定理 `inv_le_inv`

English:
theorem inv_le_inv
  given: (S T : Submonoid G)
  statement: S⁻¹ <= T⁻¹ ↔ S <= T
  proof: SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv

@[to_additive]

中文:
定理 inv_le_inv
  条件: (S T : 子幺半群 G)
  结论: S⁻¹ <= T⁻¹ ↔ S <= T
  证明: SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv

@[to_additive]

Depends on / 依赖: Set.inv_subset_inv, SetLike, SetLike.coe_subset_coe.symm.trans, coe_subset_coe, inv_subset_inv
-/
theorem inv_le_inv (S T : Submonoid G) : S⁻¹ <= T⁻¹ ↔ S <= T :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv

@[to_additive]
/--
theorem `inv_le` / 定理 `inv_le`

English:
theorem inv_le
  given: (S T : Submonoid G)
  statement: S⁻¹ <= T ↔ S <= T⁻¹
  proof: SetLike.coe_subset_coe.symm.trans Set.inv_subset

中文:
定理 inv_le
  条件: (S T : 子幺半群 G)
  结论: S⁻¹ <= T ↔ S <= T⁻¹
  证明: SetLike.coe_subset_coe.symm.trans Set.inv_subset

Depends on / 依赖: Set.inv_subset, SetLike, SetLike.coe_subset_coe.symm.trans, coe_subset_coe, inv_subset
-/
theorem inv_le (S T : Submonoid G) : S⁻¹ <= T ↔ S <= T⁻¹ :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset

/-- Pointwise inversion of submonoids as an order isomorphism. -/
@[to_additive (attr := simps!)
/-- Pointwise negation of additive submonoids as an order isomorphism -/]
/--
Definition of `invOrderIso` / `invOrderIso` 的定义

English:
definition invOrderIso
  signature: : Submonoid G ≃o Submonoid G where
  body: Equiv.inv _
  map_rel_iff' := inv_le_inv _ _

@[to_additive]

中文:
定义 invOrderIso
  签名: : 子幺半群 G ≃o 子幺半群 G where
  定义体: Equiv.inv _
  map_rel_iff' := inv_le_inv _ _

@[to_additive]

Depends on / 依赖: Equiv.inv
-/
def invOrderIso : Submonoid G ≃o Submonoid G where
  toEquiv := Equiv.inv _
  map_rel_iff' := inv_le_inv _ _

@[to_additive]
/--
theorem `closure_inv` / 定理 `closure_inv`

English:
theorem closure_inv
  given: (s : Set G)
  statement: closure s⁻¹ = (closure s)⁻¹
  proof: by
  apply le_antisymm
  · rw [closure_le, coe_inv, ← Set.inv_subset, inv_inv]
    exact subset_closure
  · rw [inv_le, closure_le, coe_inv, ← Set.inv_subset]
    exact subset_closure

@[to_additive]

中文:
定理 closure_inv
  条件: (s : 集合 G)
  结论: closure s⁻¹ = (closure s)⁻¹
  证明: by
  apply le_antisymm
  · rw [closure_le, coe_inv, ← Set.inv_subset, inv_inv]
    exact subset_closure
  · rw [inv_le, closure_le, coe_inv, ← Set.inv_subset]
    exact subset_closure

@[to_additive]

Depends on / 依赖: Set.inv_subset, closure_le, coe_inv, inv_inv, inv_le, inv_subset, le_antisymm, subset_closure
-/
theorem closure_inv (s : Set G) : closure s⁻¹ = (closure s)⁻¹ := by
  apply le_antisymm
  · rw [closure_le, coe_inv, ← Set.inv_subset, inv_inv]
    exact subset_closure
  · rw [inv_le, closure_le, coe_inv, ← Set.inv_subset]
    exact subset_closure

@[to_additive]
/--
lemma `mem_closure_inv` / 引理 `mem_closure_inv`

English:
lemma mem_closure_inv
  given: (s : Set G) (x : G)
  statement: x in closure s⁻¹ ↔ x⁻¹ in closure s
  proof: by
  rw [closure_inv]; rw [mem_inv]

@[to_additive (attr := simp)]

中文:
引理 mem_closure_inv
  条件: (s : 集合 G) (x : G)
  结论: x in closure s⁻¹ ↔ x⁻¹ in closure s
  证明: by
  rw [closure_inv]; rw [mem_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: closure_inv, mem_inv
-/
lemma mem_closure_inv (s : Set G) (x : G) : x in closure s⁻¹ ↔ x⁻¹ in closure s := by
  rw [closure_inv]; rw [mem_inv]

@[to_additive (attr := simp)]
/--
theorem `inv_inf` / 定理 `inv_inf`

English:
theorem inv_inf
  given: (S T : Submonoid G)
  statement: (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹
  proof: SetLike.coe_injective Set.inter_inv

@[to_additive (attr := simp)]

中文:
定理 inv_inf
  条件: (S T : 子幺半群 G)
  结论: (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹
  证明: SetLike.coe_injective Set.inter_inv

@[to_additive (attr := simp)]

Depends on / 依赖: Set.inter_inv, SetLike, SetLike.coe_injective, coe_injective, inter_inv
-/
theorem inv_inf (S T : Submonoid G) : (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹ :=
  SetLike.coe_injective Set.inter_inv

@[to_additive (attr := simp)]
/--
theorem `inv_sup` / 定理 `inv_sup`

English:
theorem inv_sup
  given: (S T : Submonoid G)
  statement: (S ⊔ T)⁻¹ = S⁻¹ ⊔ T⁻¹
  proof: (invOrderIso : Submonoid G ≃o Submonoid G).map_sup S T

@[to_additive (attr := simp)]

中文:
定理 inv_sup
  条件: (S T : 子幺半群 G)
  结论: (S ⊔ T)⁻¹ = S⁻¹ ⊔ T⁻¹
  证明: (invOrderIso : Submonoid G ≃o Submonoid G).map_sup S T

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, invOrderIso, map_sup
-/
theorem inv_sup (S T : Submonoid G) : (S ⊔ T)⁻¹ = S⁻¹ ⊔ T⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_sup S T

@[to_additive (attr := simp)]
/--
theorem `inv_bot` / 定理 `inv_bot`

English:
theorem inv_bot
  statement: (⊥ : Submonoid G)⁻¹ = ⊥
  proof: SetLike.coe_injective (Set.inv_singleton 1).trans congr_arg _ inv_one

@[to_additive (attr := simp)]

中文:
定理 inv_bot
  结论: (⊥ : 子幺半群 G)⁻¹ = ⊥
  证明: SetLike.coe_injective (Set.inv_singleton 1).trans congr_arg _ inv_one

@[to_additive (attr := simp)]

Depends on / 依赖: Set.inv_singleton, SetLike, SetLike.coe_injective, coe_injective, congr_arg, inv_one, inv_singleton
-/
theorem inv_bot : (⊥ : Submonoid G)⁻¹ = ⊥ :=
SetLike.coe_injective (Set.inv_singleton 1).trans congr_arg _ inv_one

@[to_additive (attr := simp)]
/--
theorem `inv_top` / 定理 `inv_top`

English:
theorem inv_top
  statement: (⊤ : Submonoid G)⁻¹ = ⊤
  proof: SetLike.coe_injective Set.inv_univ

@[to_additive (attr := simp)]

中文:
定理 inv_top
  结论: (⊤ : 子幺半群 G)⁻¹ = ⊤
  证明: SetLike.coe_injective Set.inv_univ

@[to_additive (attr := simp)]

Depends on / 依赖: Set.inv_univ, SetLike, SetLike.coe_injective, coe_injective, inv_univ
-/
theorem inv_top : (⊤ : Submonoid G)⁻¹ = ⊤ :=
SetLike.coe_injective Set.inv_univ

@[to_additive (attr := simp)]
/--
theorem `inv_iInf` / 定理 `inv_iInf`

English:
theorem inv_iInf
  given: {ι : Sort*} (S : ι -> Submonoid G)
  statement: (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹
  proof: (invOrderIso : Submonoid G ≃o Submonoid G).map_iInf _

@[to_additive (attr := simp)]

中文:
定理 inv_iInf
  条件: {ι : 类型层*} (S : ι -> 子幺半群 G)
  结论: (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹
  证明: (invOrderIso : Submonoid G ≃o Submonoid G).map_iInf _

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, invOrderIso, map_iInf
-/
theorem inv_iInf {ι : Sort*} (S : ι -> Submonoid G) : (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_iInf _

@[to_additive (attr := simp)]
/--
theorem `inv_iSup` / 定理 `inv_iSup`

English:
theorem inv_iSup
  given: {ι : Sort*} (S : ι -> Submonoid G)
  statement: (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹
  proof: (invOrderIso : Submonoid G ≃o Submonoid G).map_iSup _

中文:
定理 inv_iSup
  条件: {ι : 类型层*} (S : ι -> 子幺半群 G)
  结论: (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹
  证明: (invOrderIso : Submonoid G ≃o Submonoid G).map_iSup _

Depends on / 依赖: Submonoid, invOrderIso, map_iSup
-/
theorem inv_iSup {ι : Sort*} (S : ι -> Submonoid G) : (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_iSup _

end Submonoid

namespace Submonoid

section Monoid

variable [Monoid α] [MulDistribMulAction α M]

-- todo: add `to_additive`?
/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseMulAction` / `pointwiseMulAction` 的定义

English:
definition pointwiseMulAction
  signature: : MulAction α (Submonoid M) where
  body: S.map (MulDistribMulAction.toMonoidEnd _ M a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using! S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : Monoid.End M => S.map f) (map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Submonoid.pointwiseMulAction

@[simp, norm_cast]

中文:
定义 pointwiseMulAction
  签名: : 乘法作用 α (子幺半群 M) where
  定义体: S.map (MulDistribMulAction.toMonoidEnd _ M a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using! S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : Monoid.End M => S.map f) (map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Submonoid.pointwiseMulAction

@[simp, norm_cast]
-/
protected def pointwiseMulAction : MulAction α (Submonoid M) where
  smul a S := S.map (MulDistribMulAction.toMonoidEnd _ M a)
  one_smul S := by
    change S.map _ = S
    simpa only [map_one] using! S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : Monoid.End M => S.map f) (map_mul _ _ _)).trans
      (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Submonoid.pointwiseMulAction

@[simp, norm_cast]
/--
theorem `coe_pointwise_smul` / 定理 `coe_pointwise_smul`

English:
theorem coe_pointwise_smul
  given: (a : α) (S : Submonoid M)
  statement: ↑(a • S) = a • (S : Set M)
  proof: rfl

中文:
定理 coe_pointwise_smul
  条件: (a : α) (S : 子幺半群 M)
  结论: ↑(a • S) = a • (S : 集合 M)
  证明: rfl
-/
theorem coe_pointwise_smul (a : α) (S : Submonoid M) : ↑(a • S) = a • (S : Set M) :=
  rfl

/--
theorem `smul_mem_pointwise_smul` / 定理 `smul_mem_pointwise_smul`

English:
theorem smul_mem_pointwise_smul
  given: (m : M) (a : α) (S : Submonoid M)
  statement: m in S -> a • m in a • S
  proof: (Set.smul_mem_smul_set : _ -> _ in a • (S : Set M))

中文:
定理 smul_mem_pointwise_smul
  条件: (m : M) (a : α) (S : 子幺半群 M)
  结论: m in S -> a • m in a • S
  证明: (Set.smul_mem_smul_set : _ -> _ in a • (S : Set M))

Depends on / 依赖: Set.smul_mem_smul_set, smul_mem_smul_set
-/
theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m in S -> a • m in a • S :=
  (Set.smul_mem_smul_set : _ -> _ in a • (S : Set M))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CovariantClass α (Submonoid M) HSMul.hSMul LE.le
  body: ⟨fun _ _ => image_mono⟩

中文:
实例 :
  签名: 协变类 α (子幺半群 M) 异质标量乘法.hSMul LE.le
  定义体: ⟨fun _ _ => image_mono⟩

Depends on / 依赖: image_mono
-/
instance : CovariantClass α (Submonoid M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_mono⟩

/--
theorem `mem_smul_pointwise_iff_exists` / 定理 `mem_smul_pointwise_iff_exists`

English:
theorem mem_smul_pointwise_iff_exists
  given: (m : M) (a : α) (S : Submonoid M)
  proof: (Set.mem_smul_set : m in a • (S : Set M) ↔ _)

@[simp]

中文:
定理 mem_smul_pointwise_iff_存在
  条件: (m : M) (a : α) (S : 子幺半群 M)
  证明: (Set.mem_smul_set : m in a • (S : Set M) ↔ _)

@[simp]

Depends on / 依赖: Set.mem_smul_set, mem_smul_set
-/
theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submonoid M) :
    m in a • S ↔ exists s : M, s in S ∧ a • s = m :=
  (Set.mem_smul_set : m in a • (S : Set M) ↔ _)

@[simp]
/--
theorem `smul_bot` / 定理 `smul_bot`

English:
theorem smul_bot
  given: (a : α)
  statement: a • (⊥ : Submonoid M) = ⊥
  proof: map_bot _

中文:
定理 smul_bot
  条件: (a : α)
  结论: a • (⊥ : 子幺半群 M) = ⊥
  证明: map_bot _

Depends on / 依赖: map_bot
-/
theorem smul_bot (a : α) : a • (⊥ : Submonoid M) = ⊥ :=
  map_bot _

/--
theorem `smul_sup` / 定理 `smul_sup`

English:
theorem smul_sup
  given: (a : α) (S T : Submonoid M)
  statement: a • (S ⊔ T) = a • S ⊔ a • T
  proof: map_sup _ _ _

中文:
定理 smul_sup
  条件: (a : α) (S T : 子幺半群 M)
  结论: a • (S ⊔ T) = a • S ⊔ a • T
  证明: map_sup _ _ _

Depends on / 依赖: map_sup
-/
theorem smul_sup (a : α) (S T : Submonoid M) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

/--
theorem `smul_closure` / 定理 `smul_closure`

English:
theorem smul_closure
  given: (a : α) (s : Set M)
  statement: a • closure s = closure (a • s)
  proof: MonoidHom.map_mclosure _ _

中文:
定理 smul_closure
  条件: (a : α) (s : 集合 M)
  结论: a • closure s = closure (a • s)
  证明: MonoidHom.map_mclosure _ _

Depends on / 依赖: MonoidHom, MonoidHom.map_mclosure, map_mclosure
-/
theorem smul_closure (a : α) (s : Set M) : a • closure s = closure (a • s) :=
  MonoidHom.map_mclosure _ _

/--
lemma `pointwise_isCentralScalar` / 引理 `pointwise_isCentralScalar`

English:
lemma pointwise_isCentralScalar
  given: [MulDistribMulAction αᵐᵒᵖ M] [IsCentralScalar α M]
  proof: ⟨fun _ S => (congr_arg fun f : Monoid.End M => S.map f) MonoidHom.ext op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] Submonoid.pointwise_isCentralScalar

中文:
引理 pointwise_isCentralScalar
  条件: [MulDistribMul作用 αᵐᵒᵖ M] [中心标量 α M]
  证明: ⟨fun _ S => (congr_arg fun f : Monoid.End M => S.map f) MonoidHom.ext op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] Submonoid.pointwise_isCentralScalar

Depends on / 依赖: Monoid, Monoid.End, MonoidHom, MonoidHom.ext, S.map, congr_arg, op_smul_eq_smul
-/
lemma pointwise_isCentralScalar [MulDistribMulAction αᵐᵒᵖ M] [IsCentralScalar α M] :
    IsCentralScalar α (Submonoid M) :=
⟨fun _ S => (congr_arg fun f : Monoid.End M => S.map f) MonoidHom.ext op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] Submonoid.pointwise_isCentralScalar

end Monoid

section Group

variable [Group α] [MulDistribMulAction α M]

@[simp]
/--
theorem `smul_mem_pointwise_smul_iff` / 定理 `smul_mem_pointwise_smul_iff`

English:
theorem smul_mem_pointwise_smul_iff
  given: {a : α} {S : Submonoid M} {x : M}
  statement: a • x in a • S ↔ x in S
  proof: smul_mem_smul_set_iff

中文:
定理 smul_mem_pointwise_smul_iff
  条件: {a : α} {S : 子幺半群 M} {x : M}
  结论: a • x in a • S ↔ x in S
  证明: smul_mem_smul_set_iff

Depends on / 依赖: smul_mem_smul_set_iff
-/
theorem smul_mem_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : a • x in a • S ↔ x in S :=
  smul_mem_smul_set_iff

/--
theorem `mem_pointwise_smul_iff_inv_smul_mem` / 定理 `mem_pointwise_smul_iff_inv_smul_mem`

English:
theorem mem_pointwise_smul_iff_inv_smul_mem
  given: {a : α} {S : Submonoid M} {x : M}
  proof: mem_smul_set_iff_inv_smul_mem

中文:
定理 mem_pointwise_smul_iff_inv_smul_mem
  条件: {a : α} {S : 子幺半群 M} {x : M}
  证明: mem_smul_set_iff_inv_smul_mem

Depends on / 依赖: mem_smul_set_iff_inv_smul_mem
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Submonoid M} {x : M} :
    x in a • S ↔ a⁻¹ • x in S :=
  mem_smul_set_iff_inv_smul_mem

/--
theorem `mem_inv_pointwise_smul_iff` / 定理 `mem_inv_pointwise_smul_iff`

English:
theorem mem_inv_pointwise_smul_iff
  given: {a : α} {S : Submonoid M} {x : M}
  statement: x in a⁻¹ • S ↔ a • x in S
  proof: mem_inv_smul_set_iff

@[simp]

中文:
定理 mem_inv_pointwise_smul_iff
  条件: {a : α} {S : 子幺半群 M} {x : M}
  结论: x in a⁻¹ • S ↔ a • x in S
  证明: mem_inv_smul_set_iff

@[simp]

Depends on / 依赖: mem_inv_smul_set_iff
-/
theorem mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x in a⁻¹ • S ↔ a • x in S :=
  mem_inv_smul_set_iff

@[simp]
/--
theorem `pointwise_smul_le_pointwise_smul_iff` / 定理 `pointwise_smul_le_pointwise_smul_iff`

English:
theorem pointwise_smul_le_pointwise_smul_iff
  given: {a : α} {S T : Submonoid M}
  statement: a • S <= a • T ↔ S <= T
  proof: smul_set_subset_smul_set_iff

中文:
定理 pointwise_smul_le_pointwise_smul_iff
  条件: {a : α} {S T : 子幺半群 M}
  结论: a • S <= a • T ↔ S <= T
  证明: smul_set_subset_smul_set_iff

Depends on / 依赖: smul_set_subset_smul_set_iff
-/
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Submonoid M} : a • S <= a • T ↔ S <= T :=
  smul_set_subset_smul_set_iff

/--
theorem `pointwise_smul_subset_iff` / 定理 `pointwise_smul_subset_iff`

English:
theorem pointwise_smul_subset_iff
  given: {a : α} {S T : Submonoid M}
  statement: a • S <= T ↔ S <= a⁻¹ • T
  proof: smul_set_subset_iff_subset_inv_smul_set

中文:
定理 pointwise_smul_subset_iff
  条件: {a : α} {S T : 子幺半群 M}
  结论: a • S <= T ↔ S <= a⁻¹ • T
  证明: smul_set_subset_iff_subset_inv_smul_set

Depends on / 依赖: smul_set_subset_iff_subset_inv_smul_set
-/
theorem pointwise_smul_subset_iff {a : α} {S T : Submonoid M} : a • S <= T ↔ S <= a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set

/--
theorem `subset_pointwise_smul_iff` / 定理 `subset_pointwise_smul_iff`

English:
theorem subset_pointwise_smul_iff
  given: {a : α} {S T : Submonoid M}
  statement: S <= a • T ↔ a⁻¹ • S <= T
  proof: subset_smul_set_iff

中文:
定理 subset_pointwise_smul_iff
  条件: {a : α} {S T : 子幺半群 M}
  结论: S <= a • T ↔ a⁻¹ • S <= T
  证明: subset_smul_set_iff

Depends on / 依赖: subset_smul_set_iff
-/
theorem subset_pointwise_smul_iff {a : α} {S T : Submonoid M} : S <= a • T ↔ a⁻¹ • S <= T :=
  subset_smul_set_iff

end Group
end Submonoid

namespace Set.IsPWO

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Set α}

@[to_additive]
/--
theorem `submonoid_closure` / 定理 `submonoid_closure`

English:
theorem submonoid_closure
  given: (hpos : forall x : α, x in s -> 1 <= x) (h : s.IsPWO)
  proof: by
  rw [Submonoid.closure_eq_image_prod]
  refine (h.partiallyWellOrderedOn_sublistForall₂ (· <= ·)).image_of_monotone_on ?_
exact fun l1 _ l2 hl2 h12 => h12.prod_le_prod' fun x hx => hpos x hl2 x hx

中文:
定理 submonoid_closure
  条件: (hpos : 对任意 x : α, x in s -> 1 <= x) (h : s.IsPWO)
  证明: by
  rw [Submonoid.closure_eq_image_prod]
  refine (h.partiallyWellOrderedOn_sublistForall₂ (· <= ·)).image_of_monotone_on ?_
exact fun l1 _ l2 hl2 h12 => h12.prod_le_prod' fun x hx => hpos x hl2 x hx

Depends on / 依赖: Submonoid, Submonoid.closure_eq_image_prod, closure_eq_image_prod, h.partiallyWellOrderedOn_sublistForall, h12.prod_le_prod, image_of_monotone_on, prod_le_prod
-/
theorem submonoid_closure (hpos : forall x : α, x in s -> 1 <= x) (h : s.IsPWO) :
    IsPWO (Submonoid.closure s : Set α) := by
  rw [Submonoid.closure_eq_image_prod]
  refine (h.partiallyWellOrderedOn_sublistForall₂ (· <= ·)).image_of_monotone_on ?_
exact fun l1 _ l2 hl2 h12 => h12.prod_le_prod' fun x hx => hpos x hl2 x hx

end Set.IsPWO
