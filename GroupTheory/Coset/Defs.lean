/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
module

public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Cosets

This file develops the basic theory of left and right cosets.

When `G` is a group and `a : G`, `s : Set G`, with `open scoped Pointwise` we can write:
* the left coset of `s` by `a` as `a • s`
* the right coset of `s` by `a` as `MulOpposite.op a • s` (or `op a • s` with `open MulOpposite`,
  or `s <• a` with `open scoped Pointwise RightActions`)

If instead `G` is an additive group, we can write (with `open scoped Pointwise` still)
* the left coset of `s` by `a` as `a +ᵥ s`
* the right coset of `s` by `a` as `AddOpposite.op a +ᵥ s` (or `op a +ᵥ s` with `open AddOpposite`,
  or `s <+ᵥ a` with `open scoped Pointwise RightActions`)

## Main definitions

* `QuotientGroup.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `AddGroup` this is `QuotientAddGroup.quotient s`.
* `QuotientGroup.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `AddGroup` this is `QuotientAddGroup.mk`.

## Notation

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`

## TODO

Properly merge with pointwise actions on sets, by renaming and deduplicating lemmas as appropriate.
-/

@[expose] public section

assert_not_exists Cardinal

open Function Set
open scoped Pointwise

variable {α : Type*}

/- Ensure that `@[to_additive]` uses the right namespace. -/
insert_to_additive_translation QuotientGroup QuotientAddGroup

namespace QuotientGroup

variable [Group α] (s : Subgroup α)

/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup. -/
@[to_additive (attr := instance_reducible)
  /-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup. -/]
/--
Definition of `leftRel` / `leftRel` 的定义

English:
definition leftRel
  signature: : Setoid α
  body: MulAction.orbitRel s.op α

中文:
定义 leftRel
  签名: : 集合等价关系 α
  定义体: MulAction.orbitRel s.op α

Depends on / 依赖: MulAction, MulAction.orbitRel, orbitRel, s.op
-/
def leftRel : Setoid α :=
  MulAction.orbitRel s.op α

variable {s} in
@[to_additive]
/--
theorem `leftRel_apply` / 定理 `leftRel_apply`

English:
theorem leftRel_apply
  given: {x y : α}
  statement: leftRel s x y ↔ x⁻¹ * y in s
  proof: calc
    (exists a : s.op, y * MulOpposite.unop a = x) ↔ exists a : s, y * a = x :=
      s.equivOp.symm.exists_congr_left
    _ ↔ exists a : s, x⁻¹ * y = a⁻¹ := by
      simp only [inv_mul_eq_iff_eq_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq]
    _ ↔ x⁻¹ * y in s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]

中文:
定理 leftRel_apply
  条件: {x y : α}
  结论: leftRel s x y ↔ x⁻¹ * y in s
  证明: calc
    (exists a : s.op, y * MulOpposite.unop a = x) ↔ exists a : s, y * a = x :=
      s.equivOp.symm.exists_congr_left
    _ ↔ exists a : s, x⁻¹ * y = a⁻¹ := by
      simp only [inv_mul_eq_iff_eq_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq]
    _ ↔ x⁻¹ * y in s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]

Depends on / 依赖: MulOpposite, MulOpposite.unop, Subgroup, Subgroup.coe_inv, coe_inv, eq_mul_inv_iff_mul_eq, equivOp, exists_congr_left, exists_inv_mem_iff_exists_mem, inv_mul_eq_iff_eq_mul, s.equivOp.symm.exists_congr_left, s.op
-/
theorem leftRel_apply {x y : α} : leftRel s x y ↔ x⁻¹ * y in s :=
  calc
    (exists a : s.op, y * MulOpposite.unop a = x) ↔ exists a : s, y * a = x :=
      s.equivOp.symm.exists_congr_left
    _ ↔ exists a : s, x⁻¹ * y = a⁻¹ := by
      simp only [inv_mul_eq_iff_eq_mul, Subgroup.coe_inv, eq_mul_inv_iff_mul_eq]
    _ ↔ x⁻¹ * y in s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]
/--
theorem `leftRel_eq` / 定理 `leftRel_eq`

English:
theorem leftRel_eq
  statement: ⇑(leftRel s) = fun x y => x⁻¹ * y in s
  proof: funext₂ by
    simp only [eq_iff_iff]
    apply leftRel_apply

@[to_additive]

中文:
定理 leftRel_eq
  结论: ⇑(leftRel s) = fun x y => x⁻¹ * y in s
  证明: funext₂ by
    simp only [eq_iff_iff]
    apply leftRel_apply

@[to_additive]

Depends on / 依赖: LinearMap, LinearMap.ext, eq_iff_iff, leftRel_apply, vecMul_vecMul
-/
theorem leftRel_eq : ⇑(leftRel s) = fun x y => x⁻¹ * y in s :=
funext₂ by
    simp only [eq_iff_iff]
    apply leftRel_apply

@[to_additive]
/--
Instance `leftRelDecidable` / 实例 `leftRelDecidable`

English:
instance leftRelDecidable
  signature: [DecidablePred (· in s)]
  body: fun x y => by
  rw [leftRel_eq]
  exact ‹DecidablePred (· in s)› _

中文:
实例 leftRelDecidable
  签名: [DecidablePred (· in s)]
  定义体: fun x y => by
  rw [leftRel_eq]
  exact ‹DecidablePred (· in s)› _

Depends on / 依赖: DecidablePred, leftRel_eq, vecMul_vecMul
-/
instance leftRelDecidable [DecidablePred (· in s)] : DecidableRel (leftRel s).r := fun x y => by
  rw [leftRel_eq]
  exact ‹DecidablePred (· in s)› _

/-- `α ⧸ s` is the quotient type representing the left cosets of `s`. If `s` is a normal subgroup,
`α ⧸ s` is a group -/
@[to_additive /-- `α ⧸ s` is the quotient type representing the left cosets of `s`. If `s` is a
normal subgroup, `α ⧸ s` is a group -/]
/--
Instance `instHasQuotientSubgroup` / 实例 `instHasQuotientSubgroup`

English:
instance instHasQuotientSubgroup
  signature: : HasQuotient α (Subgroup α)
  body: ⟨fun s => Quotient (leftRel s)⟩

@[to_additive]

中文:
实例 instHasQuotientSubgroup
  签名: : 有商 α (子群 α)
  定义体: ⟨fun s => Quotient (leftRel s)⟩

@[to_additive]

Depends on / 依赖: Matrix, Matrix.toLinearMapRight, Quotient, injective, leftRel, toLinearMapRight
-/
instance instHasQuotientSubgroup : HasQuotient α (Subgroup α) :=
  ⟨fun s => Quotient (leftRel s)⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidablePred
  signature: (· in s)] : DecidableEq (α ⧸ s)
  body: @Quotient.decidableEq _ _ (leftRelDecidable _)

中文:
实例 [DecidablePred
  签名: (· in s)] : DecidableEq (α ⧸ s)
  定义体: @Quotient.decidableEq _ _ (leftRelDecidable _)

Depends on / 依赖: Quotient, Quotient.decidableEq, decidableEq, leftRelDecidable
-/
instance [DecidablePred (· in s)] : DecidableEq (α ⧸ s) :=
  @Quotient.decidableEq _ _ (leftRelDecidable _)

/-- The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[to_additive (attr := instance_reducible)
  /-- The equivalence relation corresponding to the partition of a group by right cosets
  of a subgroup. -/]
/--
Definition of `rightRel` / `rightRel` 的定义

English:
definition rightRel
  signature: : Setoid α
  body: MulAction.orbitRel s α

中文:
定义 rightRel
  签名: : 集合等价关系 α
  定义体: MulAction.orbitRel s α

Depends on / 依赖: MulAction, MulAction.orbitRel, orbitRel
-/
def rightRel : Setoid α :=
  MulAction.orbitRel s α

variable {s} in
@[to_additive]
/--
theorem `rightRel_apply` / 定理 `rightRel_apply`

English:
theorem rightRel_apply
  given: {x y : α}
  statement: rightRel s x y ↔ y * x⁻¹ in s
  proof: calc
    (exists a : s, (a : α) * y = x) ↔ exists a : s, y * x⁻¹ = a⁻¹ := by
      simp only [mul_inv_eq_iff_eq_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
    _ ↔ y * x⁻¹ in s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]

中文:
定理 rightRel_apply
  条件: {x y : α}
  结论: rightRel s x y ↔ y * x⁻¹ in s
  证明: calc
    (exists a : s, (a : α) * y = x) ↔ exists a : s, y * x⁻¹ = a⁻¹ := by
      simp only [mul_inv_eq_iff_eq_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
    _ ↔ y * x⁻¹ in s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.coe_inv, coe_inv, eq_inv_mul_iff_mul_eq, exists_inv_mem_iff_exists_mem, mul_inv_eq_iff_eq_mul
-/
theorem rightRel_apply {x y : α} : rightRel s x y ↔ y * x⁻¹ in s :=
  calc
    (exists a : s, (a : α) * y = x) ↔ exists a : s, y * x⁻¹ = a⁻¹ := by
      simp only [mul_inv_eq_iff_eq_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
    _ ↔ y * x⁻¹ in s := by simp [exists_inv_mem_iff_exists_mem]

@[to_additive]
/--
theorem `rightRel_eq` / 定理 `rightRel_eq`

English:
theorem rightRel_eq
  statement: ⇑(rightRel s) = fun x y => y * x⁻¹ in s
  proof: funext₂ by
    simp only [eq_iff_iff]
    apply rightRel_apply

@[to_additive]

中文:
定理 rightRel_eq
  结论: ⇑(rightRel s) = fun x y => y * x⁻¹ in s
  证明: funext₂ by
    simp only [eq_iff_iff]
    apply rightRel_apply

@[to_additive]

Depends on / 依赖: eq_iff_iff, rightRel_apply
-/
theorem rightRel_eq : ⇑(rightRel s) = fun x y => y * x⁻¹ in s :=
funext₂ by
    simp only [eq_iff_iff]
    apply rightRel_apply

@[to_additive]
/--
Instance `rightRelDecidable` / 实例 `rightRelDecidable`

English:
instance rightRelDecidable
  signature: [DecidablePred (· in s)]
  body: fun x y => by
  rw [rightRel_eq]
  exact ‹DecidablePred (· in s)› _

中文:
实例 rightRelDecidable
  签名: [DecidablePred (· in s)]
  定义体: fun x y => by
  rw [rightRel_eq]
  exact ‹DecidablePred (· in s)› _

Depends on / 依赖: DecidablePred, rightRel_eq
-/
instance rightRelDecidable [DecidablePred (· in s)] : DecidableRel (rightRel s).r := fun x y => by
  rw [rightRel_eq]
  exact ‹DecidablePred (· in s)› _

/-- Right cosets are in bijection with left cosets. -/
@[to_additive /-- Right cosets are in bijection with left cosets. -/]
/--
Definition of `quotientRightRelEquivQuotientLeftRel` / `quotientRightRelEquivQuotientLeftRel` 的定义

English:
definition quotientRightRelEquivQuotientLeftRel
  signature: : Quotient (QuotientGroup.rightRel s) ≃ α ⧸ s where
  body: Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply]; rw [rightRel_apply]
      exact fun h => (congr_arg (· in s) (by simp)).mp (s.inv_mem h)
  invFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply]; rw [rightRel_apply]
      exact fun h => (congr_arg (· in s) (by simp)).mp (s.inv_mem h)
  left_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)
  right_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)

中文:
定义 quotientRightRelEquivQuotientLeftRel
  签名: : 商 (商群.rightRel s) ≃ α ⧸ s where
  定义体: Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply]; rw [rightRel_apply]
      exact fun h => (congr_arg (· in s) (by simp)).mp (s.inv_mem h)
  invFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply]; rw [rightRel_apply]
      exact fun h => (congr_arg (· in s) (by simp)).mp (s.inv_mem h)
  left_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)
  right_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)

Depends on / 依赖: Quotient, Quotient.exact, Quotient.inductionOn, Quotient.map, Quotient.sound, congr_arg, inductionOn, invFun, inv_i, inv_inv, inv_mem, leftRel_apply, left_inv, rightRel_apply, right_inv, s.inv_mem
-/
def quotientRightRelEquivQuotientLeftRel : Quotient (QuotientGroup.rightRel s) ≃ α ⧸ s where
  toFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply]; rw [rightRel_apply]
      exact fun h => (congr_arg (· in s) (by simp)).mp (s.inv_mem h)
  invFun :=
    Quotient.map' (fun g => g⁻¹) fun a b => by
      rw [leftRel_apply]; rw [rightRel_apply]
      exact fun h => (congr_arg (· in s) (by simp)).mp (s.inv_mem h)
  left_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)
  right_inv g :=
    Quotient.inductionOn' g fun g =>
      Quotient.sound'
        (by
          simp only [inv_inv]
          exact Quotient.exact' rfl)

end QuotientGroup

namespace QuotientGroup

variable [Group α] {s : Subgroup α}

/-- The canonical map from a group `α` to the quotient `α ⧸ s`. -/
@[to_additive (attr := coe)
/-- The canonical map from an `AddGroup` `α` to the quotient `α ⧸ s`. -/]
/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (a : α)
  body: Quotient.mk'' a

@[to_additive]

中文:
缩写 mk
  签名: (a : α)
  定义体: Quotient.mk'' a

@[to_additive]

Depends on / 依赖: Quotient, Quotient.mk
-/
abbrev mk (a : α) : α ⧸ s :=
  Quotient.mk'' a

@[to_additive]
/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective @mk _ _ s
  proof: Quotient.mk''_surjective

@[to_additive (attr := simp)]

中文:
定理 mk_surjective
  结论: 函数.满射 @mk _ _ s
  证明: Quotient.mk''_surjective

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.mk, _surjective
-/
theorem mk_surjective : Function.Surjective @mk _ _ s :=
  Quotient.mk''_surjective

@[to_additive (attr := simp)]
/--
lemma `range_mk` / 引理 `range_mk`

English:
lemma range_mk
  statement: range (QuotientGroup.mk (s := s)) = univ
  proof: range_eq_univ.mpr mk_surjective

@[to_additive (attr := elab_as_elim)]

中文:
引理 range_mk
  结论: range (商群.mk (s := s)) = univ
  证明: range_eq_univ.mpr mk_surjective

@[to_additive (attr := elab_as_elim)]

Depends on / 依赖: mk_surjective, range_eq_univ, range_eq_univ.mpr
-/
lemma range_mk : range (QuotientGroup.mk (s := s)) = univ := range_eq_univ.mpr mk_surjective

@[to_additive (attr := elab_as_elim)]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: {C : α ⧸ s -> Prop} (x : α ⧸ s) (H : forall z, C (QuotientGroup.mk z))
  statement: C x
  proof: Quotient.inductionOn' x H

@[to_additive]

中文:
定理 induction_on
  条件: {C : α ⧸ s -> 命题} (x : α ⧸ s) (H : 对任意 z, C (商群.mk z))
  结论: C x
  证明: Quotient.inductionOn' x H

@[to_additive]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s) (H : forall z, C (QuotientGroup.mk z)) : C x :=
  Quotient.inductionOn' x H

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe α (α ⧸ s)
  body: ⟨mk⟩

@[to_additive] alias induction_on' := induction_on

@[to_additive (attr := simp)]

中文:
实例 :
  签名: Coe α (α ⧸ s)
  定义体: ⟨mk⟩

@[to_additive] alias induction_on' := induction_on

@[to_additive (attr := simp)]
-/
instance : Coe α (α ⧸ s) :=
  ⟨mk⟩

@[to_additive] alias induction_on' := induction_on

@[to_additive (attr := simp)]
/--
theorem `quotient_liftOn_mk` / 定理 `quotient_liftOn_mk`

English:
theorem quotient_liftOn_mk
  given: {β} (f : α -> β) (h) (x : α)
  statement: Quotient.liftOn' (x : α ⧸ s) f h = f x
  proof: rfl

@[to_additive]

中文:
定理 quotient_liftOn_mk
  条件: {β} (f : α -> β) (h) (x : α)
  结论: 商.liftOn' (x : α ⧸ s) f h = f x
  证明: rfl

@[to_additive]
-/
theorem quotient_liftOn_mk {β} (f : α -> β) (h) (x : α) : Quotient.liftOn' (x : α ⧸ s) f h = f x :=
  rfl

@[to_additive]
/--
theorem `forall_mk` / 定理 `forall_mk`

English:
theorem forall_mk
  given: {C : α ⧸ s -> Prop}
  statement: (forall x : α ⧸ s, C x) ↔ forall x : α, C x
  proof: mk_surjective.forall

@[to_additive]

中文:
定理 对任意_mk
  条件: {C : α ⧸ s -> 命题}
  结论: (对任意 x : α ⧸ s, C x) ↔ 对任意 x : α, C x
  证明: mk_surjective.forall

@[to_additive]

Depends on / 依赖: mk_surjective, mk_surjective.forall
-/
theorem forall_mk {C : α ⧸ s -> Prop} : (forall x : α ⧸ s, C x) ↔ forall x : α, C x :=
  mk_surjective.forall

@[to_additive]
/--
theorem `exists_mk` / 定理 `exists_mk`

English:
theorem exists_mk
  given: {C : α ⧸ s -> Prop}
  statement: (exists x : α ⧸ s, C x) ↔ exists x : α, C x
  proof: mk_surjective.exists

@[to_additive]

中文:
定理 存在_mk
  条件: {C : α ⧸ s -> 命题}
  结论: (存在 x : α ⧸ s, C x) ↔ 存在 x : α, C x
  证明: mk_surjective.exists

@[to_additive]

Depends on / 依赖: mk_surjective, mk_surjective.exists
-/
theorem exists_mk {C : α ⧸ s -> Prop} : (exists x : α ⧸ s, C x) ↔ exists x : α, C x :=
  mk_surjective.exists

@[to_additive]
instance (s : Subgroup α) : Inhabited (α ⧸ s) :=
  ⟨((1 : α) : α ⧸ s)⟩

@[to_additive]
/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {a b : α}
  statement: (a : α ⧸ s) = b ↔ a⁻¹ * b in s
  proof: calc
    _ ↔ leftRel s a b := Quotient.eq''
    _ ↔ _ := by rw [leftRel_apply]

@[to_additive]

中文:
定理 eq
  条件: {a b : α}
  结论: (a : α ⧸ s) = b ↔ a⁻¹ * b in s
  证明: calc
    _ ↔ leftRel s a b := Quotient.eq''
    _ ↔ _ := by rw [leftRel_apply]

@[to_additive]
-/
protected theorem eq {a b : α} : (a : α ⧸ s) = b ↔ a⁻¹ * b in s :=
  calc
    _ ↔ leftRel s a b := Quotient.eq''
    _ ↔ _ := by rw [leftRel_apply]

@[to_additive]
/--
theorem `out_eq'` / 定理 `out_eq'`

English:
theorem out_eq'
  given: (a : α ⧸ s)
  statement: mk a.out = a
  proof: Quotient.out_eq' a

中文:
定理 out_eq'
  条件: (a : α ⧸ s)
  结论: mk a.out = a
  证明: Quotient.out_eq' a

Depends on / 依赖: Pi.single, Quotient, Quotient.out_eq, out_eq, single
-/
theorem out_eq' (a : α ⧸ s) : mk a.out = a :=
  Quotient.out_eq' a

variable (s)

/-- It can be useful to write `obtain ⟨h, H⟩ := mk_out_eq_mul ...`, and then `rw [H]` or
`simp_rw [H]` or `simp only [H]`. In order for `simp_rw` and `simp only` to work, this lemma is
stated in terms of an arbitrary `h : s`, rather than the specific `h = g⁻¹ * (mk g).out`. -/
@[to_additive]
/--
theorem `mk_out_eq_mul` / 定理 `mk_out_eq_mul`

English:
theorem mk_out_eq_mul
  given: (g : α)
  statement: exists h : s, (mk g : α ⧸ s).out = g * h
  proof: ⟨⟨g⁻¹ * (mk g).out, QuotientGroup.eq.mp (mk g).out_eq'.symm⟩, by rw [mul_inv_cancel_left]⟩

中文:
定理 mk_out_eq_mul
  条件: (g : α)
  结论: 存在 h : s, (mk g : α ⧸ s).out = g * h
  证明: ⟨⟨g⁻¹ * (mk g).out, QuotientGroup.eq.mp (mk g).out_eq'.symm⟩, by rw [mul_inv_cancel_left]⟩

Depends on / 依赖: QuotientGroup, QuotientGroup.eq.mp, mul_inv_cancel_left, out_eq
-/
theorem mk_out_eq_mul (g : α) : exists h : s, (mk g : α ⧸ s).out = g * h :=
  ⟨⟨g⁻¹ * (mk g).out, QuotientGroup.eq.mp (mk g).out_eq'.symm⟩, by rw [mul_inv_cancel_left]⟩

variable {s} {a b : α}

@[to_additive (attr := simp)]
/--
theorem `mk_mul_of_mem` / 定理 `mk_mul_of_mem`

English:
theorem mk_mul_of_mem
  given: (a : α) (hb : b in s)
  statement: (mk (a * b) : α ⧸ s) = mk a
  proof: by
  rwa [QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]

@[to_additive]

中文:
定理 mk_mul_of_mem
  条件: (a : α) (hb : b in s)
  结论: (mk (a * b) : α ⧸ s) = mk a
  证明: by
  rwa [QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]

@[to_additive]

Depends on / 依赖: QuotientGroup, QuotientGroup.eq, inv_mem_iff, inv_mul_cancel_right, mul_inv_rev, s.inv_mem_iff
-/
theorem mk_mul_of_mem (a : α) (hb : b in s) : (mk (a * b) : α ⧸ s) = mk a := by
  rwa [QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]

@[to_additive]
/--
theorem `preimage_image_mk` / 定理 `preimage_image_mk`

English:
theorem preimage_image_mk
  given: (N : Subgroup α) (s : Set α)
  proof: by
  ext x
  simp only [QuotientGroup.eq, SetLike.exists, exists_prop, Set.mem_preimage, Set.mem_iUnion,
    Set.mem_image]
  exact
    ⟨fun ⟨y, hs, hN⟩ => ⟨_, N.inv_mem hN, by simpa using hs⟩, fun ⟨z, hz, hxz⟩ =>
      ⟨x * z, hxz, by simpa using hz⟩⟩

@[to_additive]

中文:
定理 preimage_image_mk
  条件: (N : 子群 α) (s : 集合 α)
  证明: by
  ext x
  simp only [QuotientGroup.eq, SetLike.exists, exists_prop, Set.mem_preimage, Set.mem_iUnion,
    Set.mem_image]
  exact
    ⟨fun ⟨y, hs, hN⟩ => ⟨_, N.inv_mem hN, by simpa using hs⟩, fun ⟨z, hz, hxz⟩ =>
      ⟨x * z, hxz, by simpa using hz⟩⟩

@[to_additive]

Depends on / 依赖: N.inv_mem, QuotientGroup, QuotientGroup.eq, Set.mem_iUnion, Set.mem_image, Set.mem_preimage, SetLike, SetLike.exists, exists_prop, inv_mem, mem_iUnion, mem_image, mem_preimage
-/
theorem preimage_image_mk (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α -> α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) ⁻¹' s := by
  ext x
  simp only [QuotientGroup.eq, SetLike.exists, exists_prop, Set.mem_preimage, Set.mem_iUnion,
    Set.mem_image]
  exact
    ⟨fun ⟨y, hs, hN⟩ => ⟨_, N.inv_mem hN, by simpa using hs⟩, fun ⟨z, hz, hxz⟩ =>
      ⟨x * z, hxz, by simpa using hz⟩⟩

@[to_additive]
/--
theorem `preimage_image_mk_eq_iUnion_image` / 定理 `preimage_image_mk_eq_iUnion_image`

English:
theorem preimage_image_mk_eq_iUnion_image
  given: (N : Subgroup α) (s : Set α)
  proof: by
  rw [preimage_image_mk]; rw [iUnion_congr_of_surjective (·⁻¹) inv_surjective]
  exact fun x => image_mul_right'

@[to_additive]

中文:
定理 preimage_image_mk_eq_iUnion_image
  条件: (N : 子群 α) (s : 集合 α)
  证明: by
  rw [preimage_image_mk]; rw [iUnion_congr_of_surjective (·⁻¹) inv_surjective]
  exact fun x => image_mul_right'

@[to_additive]

Depends on / 依赖: iUnion_congr_of_surjective, image_mul_right, inv_surjective, preimage_image_mk
-/
theorem preimage_image_mk_eq_iUnion_image (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α -> α ⧸ N) '' s) = ⋃ x : N, (· * (x : α)) '' s := by
  rw [preimage_image_mk]; rw [iUnion_congr_of_surjective (·⁻¹) inv_surjective]
  exact fun x => image_mul_right'

@[to_additive]
/--
theorem `preimage_image_mk_eq_mul` / 定理 `preimage_image_mk_eq_mul`

English:
theorem preimage_image_mk_eq_mul
  given: (N : Subgroup α) (s : Set α)
  proof: by
  rw [preimage_image_mk_eq_iUnion_image]; rw [iUnion_subtype]; rw [← image2_mul]; rw [← iUnion_image_right]
  simp only [SetLike.mem_coe]

@[to_additive]

中文:
定理 preimage_image_mk_eq_mul
  条件: (N : 子群 α) (s : 集合 α)
  证明: by
  rw [preimage_image_mk_eq_iUnion_image]; rw [iUnion_subtype]; rw [← image2_mul]; rw [← iUnion_image_right]
  simp only [SetLike.mem_coe]

@[to_additive]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, SetLike, SetLike.mem_coe, apply_symm_apply, iUnion_image_right, iUnion_subtype, image2_mul, mem_coe, preimage_image_mk_eq_iUnion_image, toMatrix
-/
theorem preimage_image_mk_eq_mul (N : Subgroup α) (s : Set α) :
    mk ⁻¹' ((mk : α -> α ⧸ N) '' s) = s * N := by
  rw [preimage_image_mk_eq_iUnion_image]; rw [iUnion_subtype]; rw [← image2_mul]; rw [← iUnion_image_right]
  simp only [SetLike.mem_coe]

@[to_additive]
/--
theorem `preimage_mk_one` / 定理 `preimage_mk_one`

English:
theorem preimage_mk_one
  given: (N : Subgroup α)
  proof: by
  rw [← image_singleton]; rw [preimage_image_mk_eq_mul]
  simp

中文:
定理 preimage_mk_one
  条件: (N : 子群 α)
  证明: by
  rw [← image_singleton]; rw [preimage_image_mk_eq_mul]
  simp

Depends on / 依赖: Matrix, Matrix.toLin, apply_symm_apply, image_singleton, preimage_image_mk_eq_mul
-/
theorem preimage_mk_one (N : Subgroup α) :
    mk ⁻¹' {(mk : α -> α ⧸ N) 1} = N := by
  rw [← image_singleton]; rw [preimage_image_mk_eq_mul]
  simp

end QuotientGroup

@[deprecated (since := "2026-07-12")]
alias QuotientAddGroup.mk_out_eq_mul := QuotientAddGroup.mk_out_eq_add

namespace Subgroup

open QuotientGroup

variable [Group α] {s : Subgroup α}

variable {t : Subgroup α}

/-- If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection. -/
@[to_additive
/-- If two subgroups `M` and `N` of `G` are equal, their quotients are in bijection. -/]
/--
Definition of `quotientEquivOfEq` / `quotientEquivOfEq` 的定义

English:
definition quotientEquivOfEq
  signature: (h : s = t)
  body: Quotient.map' id fun _a _b h' => h ▸ h'
  invFun := Quotient.map' id fun _a _b h' => h.symm ▸ h'
  left_inv q := induction_on q fun _g => rfl
  right_inv q := induction_on q fun _g => rfl

中文:
定义 quotientEquivOfEq
  签名: (h : s = t)
  定义体: Quotient.map' id fun _a _b h' => h ▸ h'
  invFun := Quotient.map' id fun _a _b h' => h.symm ▸ h'
  left_inv q := induction_on q fun _g => rfl
  right_inv q := induction_on q fun _g => rfl

Depends on / 依赖: Quotient, Quotient.map
-/
def quotientEquivOfEq (h : s = t) : α ⧸ s ≃ α ⧸ t where
  toFun := Quotient.map' id fun _a _b h' => h ▸ h'
  invFun := Quotient.map' id fun _a _b h' => h.symm ▸ h'
  left_inv q := induction_on q fun _g => rfl
  right_inv q := induction_on q fun _g => rfl

/--
theorem `quotientEquivOfEq_mk` / 定理 `quotientEquivOfEq_mk`

English:
theorem quotientEquivOfEq_mk
  given: (h : s = t) (a : α)
  proof: rfl

中文:
定理 quotientEquivOfEq_mk
  条件: (h : s = t) (a : α)
  证明: rfl
-/
theorem quotientEquivOfEq_mk (h : s = t) (a : α) :
    quotientEquivOfEq h (QuotientGroup.mk a) = QuotientGroup.mk a :=
  rfl

end Subgroup
