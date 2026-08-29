/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise actions on sets

This file proves that several kinds of actions of a type `α` on another type `β` transfer to actions
of `α`/`Set α` on `Set β`.

## Implementation notes

* We put all instances in the scope `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the scope to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).
-/

@[expose] public section

assert_not_exists MonoidWithZero IsOrderedMonoid

open Function MulOpposite
open scoped Pointwise

variable {F α β γ : Type*}

namespace Set

/-! ### Translation/scaling of sets -/

@[to_additive vadd_set_prod]
/--
lemma `smul_set_prod` / 引理 `smul_set_prod`

English:
lemma smul_set_prod
  given: {M α : Type*} [SMul M α] [SMul M β] (c : M) (s : Set α) (t : Set β)
  proof: prodMap_image_prod (c • ·) (c • ·) s t

@[to_additive]

中文:
引理 smul_set_prod
  条件: {M α : 类型} [标量乘法 M α] [标量乘法 M β] (c : M) (s : 集合 α) (t : 集合 β)
  证明: prodMap_image_prod (c • ·) (c • ·) s t

@[to_additive]

Depends on / 依赖: prodMap_image_prod
-/
lemma smul_set_prod {M α : Type*} [SMul M α] [SMul M β] (c : M) (s : Set α) (t : Set β) :
    c • (s ×ˢ t) = (c • s) ×ˢ (c • t) :=
  prodMap_image_prod (c • ·) (c • ·) s t

@[to_additive]
/--
lemma `smul_set_pi` / 引理 `smul_set_pi`

English:
lemma smul_set_pi
  statement: {G ι : Type*} {α : ι -> Type*} [Group G] [forall i, MulAction G (α i)]
  proof: smul_set_pi_of_surjective c I s fun _ _ => (MulAction.bijective c).surjective

@[to_additive]

中文:
引理 smul_set_pi
  结论: {G ι : 类型} {α : ι -> 类型} [群 G] [对任意 i, 乘法作用 G (α i)]
  证明: smul_set_pi_of_surjective c I s fun _ _ => (MulAction.bijective c).surjective

@[to_additive]

Depends on / 依赖: MulAction, MulAction.bijective, bijective, smul_set_pi_of_surjective, surjective
-/
lemma smul_set_pi {G ι : Type*} {α : ι -> Type*} [Group G] [forall i, MulAction G (α i)]
    (c : G) (I : Set ι) (s : forall i, Set (α i)) : c • I.pi s = I.pi (c • s) :=
  smul_set_pi_of_surjective c I s fun _ _ => (MulAction.bijective c).surjective

@[to_additive]
/--
lemma `smul_set_pi_of_isUnit` / 引理 `smul_set_pi_of_isUnit`

English:
lemma smul_set_pi_of_isUnit
  statement: {M ι : Type*} {α : ι -> Type*} [Monoid M] [forall i, MulAction M (α i)]
  proof: by
  lift c to Mˣ using hc
  exact smul_set_pi c I s

中文:
引理 smul_set_pi_of_isUnit
  结论: {M ι : 类型} {α : ι -> 类型} [幺半群 M] [对任意 i, 乘法作用 M (α i)]
  证明: by
  lift c to Mˣ using hc
  exact smul_set_pi c I s

Depends on / 依赖: smul_set_pi
-/
lemma smul_set_pi_of_isUnit {M ι : Type*} {α : ι -> Type*} [Monoid M] [forall i, MulAction M (α i)]
    {c : M} (hc : IsUnit c) (I : Set ι) (s : forall i, Set (α i)) : c • I.pi s = I.pi (c • s) := by
  lift c to Mˣ using hc
  exact smul_set_pi c I s

section Mul
variable {ι : Sort*} {κ : ι -> Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/--
lemma `smul_set_subset_mul` / 引理 `smul_set_subset_mul`

English:
lemma smul_set_subset_mul
  statement: a in s -> a • t subseteq s * t
  proof: image_subset_image2_right

中文:
引理 smul_set_subset_mul
  结论: a in s -> a • t subseteq s * t
  证明: image_subset_image2_right
-/
@[to_additive] lemma smul_set_subset_mul : a in s -> a • t subseteq s * t := image_subset_image2_right

open scoped RightActions in
/--
lemma `op_smul_set_subset_mul` / 引理 `op_smul_set_subset_mul`

English:
lemma op_smul_set_subset_mul
  statement: a in t -> s <• a subseteq s * t
  proof: image_subset_image2_left

@[to_additive]

中文:
引理 op_smul_set_subset_mul
  结论: a in t -> s <• a subseteq s * t
  证明: image_subset_image2_left

@[to_additive]
-/
@[to_additive] lemma op_smul_set_subset_mul : a in t -> s <• a subseteq s * t := image_subset_image2_left

@[to_additive]
/--
theorem `image_op_smul` / 定理 `image_op_smul`

English:
theorem image_op_smul
  statement: (op '' s) • t = t * s
  proof: by
  rw [← image2_smul]; rw [← image2_mul]; rw [image2_image_left]; rw [image2_swap]
  rfl

@[to_additive (attr := simp)]

中文:
定理 image_op_smul
  结论: (op '' s) • t = t * s
  证明: by
  rw [← image2_smul]; rw [← image2_mul]; rw [image2_image_left]; rw [image2_swap]
  rfl

@[to_additive (attr := simp)]

Depends on / 依赖: image2_image_left, image2_mul, image2_smul, image2_swap
-/
theorem image_op_smul : (op '' s) • t = t * s := by
  rw [← image2_smul]; rw [← image2_mul]; rw [image2_image_left]; rw [image2_swap]
  rfl

@[to_additive (attr := simp)]
/--
theorem `iUnion_op_smul_set` / 定理 `iUnion_op_smul_set`

English:
theorem iUnion_op_smul_set
  given: (s t : Set α)
  statement: ⋃ a in t, MulOpposite.op a • s = s * t
  proof: iUnion_image_right _

@[to_additive]

中文:
定理 iUnion_op_smul_set
  条件: (s t : 集合 α)
  结论: ⋃ a in t, MulOpposite.op a • s = s * t
  证明: iUnion_image_right _

@[to_additive]

Depends on / 依赖: iUnion_image_right
-/
theorem iUnion_op_smul_set (s t : Set α) : ⋃ a in t, MulOpposite.op a • s = s * t :=
  iUnion_image_right _

@[to_additive]
/--
theorem `mul_subset_iff_left` / 定理 `mul_subset_iff_left`

English:
theorem mul_subset_iff_left
  statement: s * t subseteq u ↔ forall a in s, a • t subseteq u
  proof: image2_subset_iff_left

@[to_additive]

中文:
定理 mul_subset_iff_left
  结论: s * t subseteq u ↔ 对任意 a in s, a • t subseteq u
  证明: image2_subset_iff_left

@[to_additive]

Depends on / 依赖: image2_subset_iff_left
-/
theorem mul_subset_iff_left : s * t subseteq u ↔ forall a in s, a • t subseteq u :=
  image2_subset_iff_left

@[to_additive]
/--
theorem `mul_subset_iff_right` / 定理 `mul_subset_iff_right`

English:
theorem mul_subset_iff_right
  statement: s * t subseteq u ↔ forall b in t, op b • s subseteq u
  proof: image2_subset_iff_right

中文:
定理 mul_subset_iff_right
  结论: s * t subseteq u ↔ 对任意 b in t, op b • s subseteq u
  证明: image2_subset_iff_right

Depends on / 依赖: image2_subset_iff_right
-/
theorem mul_subset_iff_right : s * t subseteq u ↔ forall b in t, op b • s subseteq u :=
  image2_subset_iff_right

/--
lemma `pair_mul` / 引理 `pair_mul`

English:
lemma pair_mul
  given: (a b : α) (s : Set α)
  statement: {a, b} * s = a • s union b • s
  proof: by
  rw [insert_eq]; rw [union_mul]; rw [singleton_mul]; rw [singleton_mul]; rfl

中文:
引理 pair_mul
  条件: (a b : α) (s : 集合 α)
  结论: {a, b} * s = a • s union b • s
  证明: by
  rw [insert_eq]; rw [union_mul]; rw [singleton_mul]; rw [singleton_mul]; rfl
-/
@[to_additive] lemma pair_mul (a b : α) (s : Set α) : {a, b} * s = a • s union b • s := by
  rw [insert_eq]; rw [union_mul]; rw [singleton_mul]; rw [singleton_mul]; rfl

open scoped RightActions
/--
lemma `mul_pair` / 引理 `mul_pair`

English:
lemma mul_pair
  given: (s : Set α) (a b : α)
  statement: s * {a, b} = s <• a union s <• b
  proof: by
  rw [insert_eq]; rw [mul_union]; rw [mul_singleton]; rw [mul_singleton]; rfl

中文:
引理 mul_pair
  条件: (s : 集合 α) (a b : α)
  结论: s * {a, b} = s <• a union s <• b
  证明: by
  rw [insert_eq]; rw [mul_union]; rw [mul_singleton]; rw [mul_singleton]; rfl
-/
@[to_additive] lemma mul_pair (s : Set α) (a b : α) : s * {a, b} = s <• a union s <• b := by
  rw [insert_eq]; rw [mul_union]; rw [mul_singleton]; rw [mul_singleton]; rfl

/--
lemma `range_mul` / 引理 `range_mul`

English:
lemma range_mul
  given: {ι : Sort*} (a : α) (f : ι -> α)
  proof: range_smul a f

中文:
引理 range_mul
  条件: {ι : 类型层*} (a : α) (f : ι -> α)
  证明: range_smul a f
-/
@[to_additive] lemma range_mul {ι : Sort*} (a : α) (f : ι -> α) :
    range (fun i => a * f i) = a • range f := range_smul a f

end Mul

@[to_additive]
/--
lemma `image_smul_distrib` / 引理 `image_smul_distrib`

English:
lemma image_smul_distrib
  statement: [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  proof: image_comm map_mul _ _

中文:
引理 image_smul_distrib
  结论: [乘法 α] [乘法 β] [函数状 F α β] [乘法态射类 F α β]
  证明: image_comm map_mul _ _

Depends on / 依赖: image_comm, map_mul
-/
lemma image_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
    (f : F) (a : α) (s : Set α) :
    f '' (a • s) = f a • f '' s :=
image_comm map_mul _ _

open scoped RightActions in
@[to_additive]
/--
lemma `image_op_smul_distrib` / 引理 `image_op_smul_distrib`

English:
lemma image_op_smul_distrib
  statement: [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  proof: image_comm fun _ => map_mul ..

中文:
引理 image_op_smul_distrib
  结论: [乘法 α] [乘法 β] [函数状 F α β] [乘法态射类 F α β]
  证明: image_comm fun _ => map_mul ..

Depends on / 依赖: image_comm, map_mul
-/
lemma image_op_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
    (f : F) (a : α) (s : Set α) : f '' (s <• a) = f '' s <• f a := image_comm fun _ => map_mul ..

section Semigroup
variable [Semigroup α]

@[to_additive]
/--
lemma `op_smul_set_mul_eq_mul_smul_set` / 引理 `op_smul_set_mul_eq_mul_smul_set`

English:
lemma op_smul_set_mul_eq_mul_smul_set
  given: (a : α) (s : Set α) (t : Set α)
  proof: op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _

中文:
引理 op_smul_set_mul_eq_mul_smul_set
  条件: (a : α) (s : 集合 α) (t : 集合 α)
  证明: op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _

Depends on / 依赖: mul_assoc, op_smul_set_smul_eq_smul_smul_set
-/
lemma op_smul_set_mul_eq_mul_smul_set (a : α) (s : Set α) (t : Set α) :
    op a • s * t = s * a • t :=
  op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _

end Semigroup

section IsLeftCancelSMul

variable [SMul α β] [IsLeftCancelSMul α β] {s : Set α} {t : Set β}

@[to_additive]
/--
theorem `pairwiseDisjoint_smul_iff` / 定理 `pairwiseDisjoint_smul_iff`

English:
theorem pairwiseDisjoint_smul_iff
  proof: pairwiseDisjoint_image_right_iff fun a _ _ _ h => IsLeftCancelSMul.left_cancel a _ _ h

中文:
定理 pairwiseDisjoint_smul_iff
  证明: pairwiseDisjoint_image_right_iff fun a _ _ _ h => IsLeftCancelSMul.left_cancel a _ _ h

Depends on / 依赖: IsLeftCancelSMul, IsLeftCancelSMul.left_cancel, left_cancel, pairwiseDisjoint_image_right_iff
-/
theorem pairwiseDisjoint_smul_iff :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p => p.1 • p.2 :=
  pairwiseDisjoint_image_right_iff fun a _ _ _ h => IsLeftCancelSMul.left_cancel a _ _ h

end IsLeftCancelSMul

@[to_additive]
/--
Instance `smulCommClass_set` / 实例 `smulCommClass_set`

English:
instance smulCommClass_set
  signature: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  body: ⟨fun _ _ => Commute.set_image smul_comm _ _⟩

@[to_additive]

中文:
实例 smulCommClass_set
  签名: [标量乘法 α γ] [标量乘法 β γ] [标量交换类 α β γ]
  定义体: ⟨fun _ _ => Commute.set_image smul_comm _ _⟩

@[to_additive]

Depends on / 依赖: Commute, Commute.set_image, set_image, smul_comm
-/
instance smulCommClass_set [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Set γ) :=
⟨fun _ _ => Commute.set_image smul_comm _ _⟩

@[to_additive]
/--
Instance `smulCommClass_set'` / 实例 `smulCommClass_set'`

English:
instance smulCommClass_set'
  signature: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  body: ⟨fun _ _ _ => image_image2_distrib_right smul_comm _⟩

@[to_additive]

中文:
实例 smulCommClass_set'
  签名: [标量乘法 α γ] [标量乘法 β γ] [标量交换类 α β γ]
  定义体: ⟨fun _ _ _ => image_image2_distrib_right smul_comm _⟩

@[to_additive]

Depends on / 依赖: image_image2_distrib_right, smul_comm
-/
instance smulCommClass_set' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Set β) (Set γ) :=
⟨fun _ _ _ => image_image2_distrib_right smul_comm _⟩

@[to_additive]
/--
Instance `smulCommClass_set''` / 实例 `smulCommClass_set''`

English:
instance smulCommClass_set''
  signature: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  body: haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]

中文:
实例 smulCommClass_set''
  签名: [标量乘法 α γ] [标量乘法 β γ] [标量交换类 α β γ]
  定义体: haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance smulCommClass_set'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) β (Set γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]
/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  body: ⟨fun _ _ _ => image2_left_comm smul_comm⟩

@[to_additive]

中文:
实例 smulCommClass
  签名: [标量乘法 α γ] [标量乘法 β γ] [标量交换类 α β γ]
  定义体: ⟨fun _ _ _ => image2_left_comm smul_comm⟩

@[to_additive]

Depends on / 依赖: image2_left_comm, smul_comm
-/
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) (Set β) (Set γ) :=
  ⟨fun _ _ _ => image2_left_comm smul_comm⟩

@[to_additive]
/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ]
  body: by simp only [← image_smul, image_image, smul_assoc]

@[to_additive]

中文:
实例 isScalarTower
  签名: [标量乘法 α β] [标量乘法 α γ] [标量乘法 β γ] [标量塔 α β γ]
  定义体: by simp only [← image_smul, image_image, smul_assoc]

@[to_additive]

Depends on / 依赖: image_image, image_smul, smul_assoc
-/
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ) where
  smul_assoc a b T := by simp only [← image_smul, image_image, smul_assoc]

@[to_additive]
/--
Instance `isScalarTower'` / 实例 `isScalarTower'`

English:
instance isScalarTower'
  signature: [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ]
  body: ⟨fun _ _ _ => image2_image_left_comm smul_assoc _⟩

@[to_additive]

中文:
实例 isScalarTower'
  签名: [标量乘法 α β] [标量乘法 α γ] [标量乘法 β γ] [标量塔 α β γ]
  定义体: ⟨fun _ _ _ => image2_image_left_comm smul_assoc _⟩

@[to_additive]

Depends on / 依赖: image2_image_left_comm, smul_assoc
-/
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) :=
⟨fun _ _ _ => image2_image_left_comm smul_assoc _⟩

@[to_additive]
/--
Instance `isScalarTower''` / 实例 `isScalarTower''`

English:
instance isScalarTower''
  signature: [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ]
  body: image2_assoc smul_assoc

@[to_additive]

中文:
实例 isScalarTower''
  签名: [标量乘法 α β] [标量乘法 α γ] [标量乘法 β γ] [标量塔 α β γ]
  定义体: image2_assoc smul_assoc

@[to_additive]

Depends on / 依赖: image2_assoc, smul_assoc
-/
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where
  smul_assoc _ _ _ := image2_assoc smul_assoc

@[to_additive]
/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β]
  body: ⟨fun _ S => (congr_arg fun f => f '' S) funext fun _ => op_smul_eq_smul _ _⟩

中文:
实例 isCentralScalar
  签名: [标量乘法 α β] [标量乘法 αᵐᵒᵖ β] [中心标量 α β]
  定义体: ⟨fun _ S => (congr_arg fun f => f '' S) funext fun _ => op_smul_eq_smul _ _⟩

Depends on / 依赖: congr_arg, op_smul_eq_smul
-/
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Set β) :=
⟨fun _ S => (congr_arg fun f => f '' S) funext fun _ => op_smul_eq_smul _ _⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `Set α`
on `Set β`. -/
@[to_additive (attr := instance_reducible)
/-- An additive action of an additive monoid `α` on a type `β` gives an additive action of `Set α`
on `Set β` -/]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mulAction [Monoid α] [MulAction α β]
  body: image2_assoc mul_smul
one_smul s := image2_singleton_left.trans by simp_rw [one_smul, image_id']

中文:
定义 noncomputable
  签名: def mulAction [幺半群 α] [乘法作用 α β]
  定义体: image2_assoc mul_smul
one_smul s := image2_singleton_left.trans by simp_rw [one_smul, image_id']
-/
protected noncomputable def mulAction [Monoid α] [MulAction α β] : MulAction (Set α) (Set β) where
  mul_smul _ _ _ := image2_assoc mul_smul
one_smul s := image2_singleton_left.trans by simp_rw [one_smul, image_id']

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `Set β`. -/
@[to_additive (attr := instance_reducible)
/-- An additive action of an additive monoid on a type `β` gives an additive action on `Set β`. -/]
/--
Definition of `mulActionSet` / `mulActionSet` 的定义

English:
definition mulActionSet
  signature: [Monoid α] [MulAction α β]
  body: by simp only [← image_smul, image_image, ← mul_smul]
  one_smul _ := by simp only [← image_smul, one_smul, image_id']

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

中文:
定义 mulActionSet
  签名: [幺半群 α] [乘法作用 α β]
  定义体: by simp only [← image_smul, image_image, ← mul_smul]
  one_smul _ := by simp only [← image_smul, one_smul, image_id']

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction
-/
protected def mulActionSet [Monoid α] [MulAction α β] : MulAction α (Set β) where
  mul_smul _ _ _ := by simp only [← image_smul, image_image, ← mul_smul]
  one_smul _ := by simp only [← image_smul, one_smul, image_id']

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

@[to_additive (attr := simp)]
/--
theorem `smul_mem_smul_set_iff` / 定理 `smul_mem_smul_set_iff`

English:
theorem smul_mem_smul_set_iff
  statement: a • x in a • s ↔ x in s
  proof: (MulAction.injective _).mem_set_image

@[to_additive]

中文:
定理 smul_mem_smul_set_iff
  结论: a • x in a • s ↔ x in s
  证明: (MulAction.injective _).mem_set_image

@[to_additive]

Depends on / 依赖: MulAction, MulAction.injective, injective, mem_set_image
-/
theorem smul_mem_smul_set_iff : a • x in a • s ↔ x in s :=
  (MulAction.injective _).mem_set_image

@[to_additive]
/--
theorem `mem_smul_set_iff_inv_smul_mem` / 定理 `mem_smul_set_iff_inv_smul_mem`

English:
theorem mem_smul_set_iff_inv_smul_mem
  statement: x in a • A ↔ a⁻¹ • x in A
  proof: show x in MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[to_additive]

中文:
定理 mem_smul_set_iff_inv_smul_mem
  结论: x in a • A ↔ a⁻¹ • x in A
  证明: show x in MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[to_additive]

Depends on / 依赖: MulAction, MulAction.toPerm, mem_image_equiv, toPerm
-/
theorem mem_smul_set_iff_inv_smul_mem : x in a • A ↔ a⁻¹ • x in A :=
  show x in MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[to_additive]
/--
theorem `mem_inv_smul_set_iff` / 定理 `mem_inv_smul_set_iff`

English:
theorem mem_inv_smul_set_iff
  statement: x in a⁻¹ • A ↔ a • x in A
  proof: by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive (attr := simp)]

中文:
定理 mem_inv_smul_set_iff
  结论: x in a⁻¹ • A ↔ a • x in A
  证明: by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive (attr := simp)]

Depends on / 依赖: exists_eq_right, image_smul, inv_smul_eq_iff, mem_image
-/
theorem mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive (attr := simp)]
/--
lemma `mem_smul_set_inv` / 引理 `mem_smul_set_inv`

English:
lemma mem_smul_set_inv
  given: {s : Set α}
  statement: a in b • s⁻¹ ↔ b in a • s
  proof: by
  simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive]

中文:
引理 mem_smul_set_inv
  条件: {s : 集合 α}
  结论: a in b • s⁻¹ ↔ b in a • s
  证明: by
  simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive]

Depends on / 依赖: mem_smul_set_iff_inv_smul_mem
-/
lemma mem_smul_set_inv {s : Set α} : a in b • s⁻¹ ↔ b in a • s := by
  simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive]
/--
theorem `preimage_smul` / 定理 `preimage_smul`

English:
theorem preimage_smul
  given: (a : α) (t : Set β)
  statement: (fun x => a • x) ⁻¹' t = a⁻¹ • t
  proof: ((MulAction.toPerm a).image_symm_eq_preimage _).symm

@[to_additive]

中文:
定理 preimage_smul
  条件: (a : α) (t : 集合 β)
  结论: (fun x => a • x) ⁻¹' t = a⁻¹ • t
  证明: ((MulAction.toPerm a).image_symm_eq_preimage _).symm

@[to_additive]

Depends on / 依赖: MulAction, MulAction.toPerm, image_symm_eq_preimage, toPerm
-/
theorem preimage_smul (a : α) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).image_symm_eq_preimage _).symm

@[to_additive]
/--
theorem `preimage_smul_inv` / 定理 `preimage_smul_inv`

English:
theorem preimage_smul_inv
  given: (a : α) (t : Set β)
  statement: (fun x => a⁻¹ • x) ⁻¹' t = a • t
  proof: preimage_smul (toUnits a)⁻¹ t

@[to_additive (attr := simp)]

中文:
定理 preimage_smul_inv
  条件: (a : α) (t : 集合 β)
  结论: (fun x => a⁻¹ • x) ⁻¹' t = a • t
  证明: preimage_smul (toUnits a)⁻¹ t

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_smul, toUnits
-/
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t

@[to_additive (attr := simp)]
/--
theorem `smul_set_subset_smul_set_iff` / 定理 `smul_set_subset_smul_set_iff`

English:
theorem smul_set_subset_smul_set_iff
  statement: a • A subseteq a • B ↔ A subseteq B
  proof: image_subset_image_iff MulAction.injective _

@[to_additive]

中文:
定理 smul_set_subset_smul_set_iff
  结论: a • A subseteq a • B ↔ A subseteq B
  证明: image_subset_image_iff MulAction.injective _

@[to_additive]

Depends on / 依赖: MulAction, MulAction.injective, image_subset_image_iff, injective
-/
theorem smul_set_subset_smul_set_iff : a • A subseteq a • B ↔ A subseteq B :=
image_subset_image_iff MulAction.injective _

@[to_additive]
/--
theorem `smul_set_subset_iff_subset_inv_smul_set` / 定理 `smul_set_subset_iff_subset_inv_smul_set`

English:
theorem smul_set_subset_iff_subset_inv_smul_set
  statement: a • A subseteq B ↔ A subseteq a⁻¹ • B
  proof: by
  refine image_subset_iff.trans ?_
  congr! 1
  exact ((MulAction.toPerm _).image_symm_eq_preimage _).symm

@[to_additive]

中文:
定理 smul_set_subset_iff_subset_inv_smul_set
  结论: a • A subseteq B ↔ A subseteq a⁻¹ • B
  证明: by
  refine image_subset_iff.trans ?_
  congr! 1
  exact ((MulAction.toPerm _).image_symm_eq_preimage _).symm

@[to_additive]

Depends on / 依赖: MulAction, MulAction.toPerm, image_subset_iff, image_subset_iff.trans, image_symm_eq_preimage, toPerm
-/
theorem smul_set_subset_iff_subset_inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B := by
  refine image_subset_iff.trans ?_
  congr! 1
  exact ((MulAction.toPerm _).image_symm_eq_preimage _).symm

@[to_additive]
/--
theorem `subset_smul_set_iff` / 定理 `subset_smul_set_iff`

English:
theorem subset_smul_set_iff
  statement: A subseteq a • B ↔ a⁻¹ • A subseteq B
  proof: by
  refine (image_subset_iff.trans ?_).symm; congr! 1;
  exact ((MulAction.toPerm _).image_eq_preimage_symm _).symm

@[to_additive]

中文:
定理 subset_smul_set_iff
  结论: A subseteq a • B ↔ a⁻¹ • A subseteq B
  证明: by
  refine (image_subset_iff.trans ?_).symm; congr! 1;
  exact ((MulAction.toPerm _).image_eq_preimage_symm _).symm

@[to_additive]

Depends on / 依赖: MulAction, MulAction.toPerm, image_eq_preimage_symm, image_subset_iff, image_subset_iff.trans, toPerm
-/
theorem subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • A subseteq B := by
  refine (image_subset_iff.trans ?_).symm; congr! 1;
  exact ((MulAction.toPerm _).image_eq_preimage_symm _).symm

@[to_additive]
/--
theorem `smul_set_inter` / 定理 `smul_set_inter`

English:
theorem smul_set_inter
  statement: a • (s inter t) = a • s inter a • t
  proof: image_inter MulAction.injective a

@[to_additive]

中文:
定理 smul_set_inter
  结论: a • (s inter t) = a • s inter a • t
  证明: image_inter MulAction.injective a

@[to_additive]

Depends on / 依赖: MulAction, MulAction.injective, image_inter, injective
-/
theorem smul_set_inter : a • (s inter t) = a • s inter a • t :=
image_inter MulAction.injective a

@[to_additive]
/--
theorem `smul_set_iInter` / 定理 `smul_set_iInter`

English:
theorem smul_set_iInter
  statement: {ι : Sort*}
  proof: image_iInter (MulAction.bijective a) t

@[to_additive]

中文:
定理 smul_set_i整数er
  结论: {ι : 类型层*}
  证明: image_iInter (MulAction.bijective a) t

@[to_additive]

Depends on / 依赖: MulAction, MulAction.bijective, bijective, image_iInter
-/
theorem smul_set_iInter {ι : Sort*}
    (a : α) (t : ι -> Set β) : (a • ⋂ i, t i) = ⋂ i, a • t i :=
  image_iInter (MulAction.bijective a) t

@[to_additive]
/--
theorem `smul_set_sdiff` / 定理 `smul_set_sdiff`

English:
theorem smul_set_sdiff
  statement: a • (s \ t) = a • s \ a • t
  proof: image_sdiff (MulAction.injective a) _ _

中文:
定理 smul_set_sdiff
  结论: a • (s \ t) = a • s \ a • t
  证明: image_sdiff (MulAction.injective a) _ _

Depends on / 依赖: MulAction, MulAction.injective, image_sdiff, injective
-/
theorem smul_set_sdiff : a • (s \ t) = a • s \ a • t :=
  image_sdiff (MulAction.injective a) _ _

open scoped symmDiff in
@[to_additive]
/--
theorem `smul_set_symmDiff` / 定理 `smul_set_symmDiff`

English:
theorem smul_set_symmDiff
  statement: a • s ∆ t = (a • s) ∆ (a • t)
  proof: image_symmDiff (MulAction.injective a) _ _

@[to_additive (attr := simp)]

中文:
定理 smul_set_symmDiff
  结论: a • s ∆ t = (a • s) ∆ (a • t)
  证明: image_symmDiff (MulAction.injective a) _ _

@[to_additive (attr := simp)]

Depends on / 依赖: MulAction, MulAction.injective, image_symmDiff, injective
-/
theorem smul_set_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective a) _ _

@[to_additive (attr := simp)]
/--
theorem `smul_set_univ` / 定理 `smul_set_univ`

English:
theorem smul_set_univ
  statement: a • (univ : Set β) = univ
  proof: image_univ_of_surjective MulAction.surjective a

@[to_additive (attr := simp)]

中文:
定理 smul_set_univ
  结论: a • (univ : 集合 β) = univ
  证明: image_univ_of_surjective MulAction.surjective a

@[to_additive (attr := simp)]

Depends on / 依赖: MulAction, MulAction.surjective, image_univ_of_surjective, surjective
-/
theorem smul_set_univ : a • (univ : Set β) = univ :=
image_univ_of_surjective MulAction.surjective a

@[to_additive (attr := simp)]
/--
theorem `smul_set_eq_univ` / 定理 `smul_set_eq_univ`

English:
theorem smul_set_eq_univ
  statement: a • s = univ ↔ s = univ
  proof: by
  rw [smul_eq_iff_eq_inv_smul]; rw [smul_set_univ]

@[to_additive (attr := simp)]

中文:
定理 smul_set_eq_univ
  结论: a • s = univ ↔ s = univ
  证明: by
  rw [smul_eq_iff_eq_inv_smul]; rw [smul_set_univ]

@[to_additive (attr := simp)]

Depends on / 依赖: smul_eq_iff_eq_inv_smul, smul_set_univ
-/
theorem smul_set_eq_univ : a • s = univ ↔ s = univ := by
  rw [smul_eq_iff_eq_inv_smul]; rw [smul_set_univ]

@[to_additive (attr := simp)]
/--
theorem `smul_univ` / 定理 `smul_univ`

English:
theorem smul_univ
  given: {s : Set α} (hs : s.Nonempty)
  statement: s • (univ : Set β) = univ
  proof: let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[to_additive]

中文:
定理 smul_univ
  条件: {s : 集合 α} (hs : s.非空)
  结论: s • (univ : 集合 β) = univ
  证明: let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[to_additive]

Depends on / 依赖: eq_univ_of_forall, smul_inv_smul
-/
theorem smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[to_additive]
/--
theorem `smul_set_compl` / 定理 `smul_set_compl`

English:
theorem smul_set_compl
  statement: a • sᶜ = (a • s)ᶜ
  proof: by
  simp_rw [Set.compl_eq_univ_sdiff, smul_set_sdiff, smul_set_univ]

@[to_additive]

中文:
定理 smul_set_compl
  结论: a • sᶜ = (a • s)ᶜ
  证明: by
  simp_rw [Set.compl_eq_univ_sdiff, smul_set_sdiff, smul_set_univ]

@[to_additive]

Depends on / 依赖: Set.compl_eq_univ_sdiff, compl_eq_univ_sdiff, simp_rw, smul_set_sdiff, smul_set_univ
-/
theorem smul_set_compl : a • sᶜ = (a • s)ᶜ := by
  simp_rw [Set.compl_eq_univ_sdiff, smul_set_sdiff, smul_set_univ]

@[to_additive]
/--
theorem `smul_inter_nonempty_iff` / 定理 `smul_inter_nonempty_iff`

English:
theorem smul_inter_nonempty_iff
  given: {s t : Set α} {x : α}
  proof: by
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩

@[to_additive]

中文:
定理 smul_inter_nonempty_iff
  条件: {s t : 集合 α} {x : α}
  证明: by
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩

@[to_additive]

Depends on / 依赖: mem_inter, mem_smul_set, mem_smul_set.mp, mem_smul_set.mpr
-/
theorem smul_inter_nonempty_iff {s t : Set α} {x : α} :
    (x • s inter t).Nonempty ↔ exists a b, (a in t ∧ b in s) ∧ a * b⁻¹ = x := by
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩

@[to_additive]
/--
theorem `smul_inter_nonempty_iff'` / 定理 `smul_inter_nonempty_iff'`

English:
theorem smul_inter_nonempty_iff'
  given: {s t : Set α} {x : α}
  proof: by
  simp_rw [smul_inter_nonempty_iff, div_eq_mul_inv]

@[to_additive]

中文:
定理 smul_inter_nonempty_iff'
  条件: {s t : 集合 α} {x : α}
  证明: by
  simp_rw [smul_inter_nonempty_iff, div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, simp_rw, smul_inter_nonempty_iff
-/
theorem smul_inter_nonempty_iff' {s t : Set α} {x : α} :
    (x • s inter t).Nonempty ↔ exists a b, (a in t ∧ b in s) ∧ a / b = x := by
  simp_rw [smul_inter_nonempty_iff, div_eq_mul_inv]

@[to_additive]
/--
theorem `op_smul_inter_nonempty_iff` / 定理 `op_smul_inter_nonempty_iff`

English:
theorem op_smul_inter_nonempty_iff
  given: {s t : Set α} {x : αᵐᵒᵖ}
  proof: by
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩

@[to_additive (attr := simp)]

中文:
定理 op_smul_inter_nonempty_iff
  条件: {s t : 集合 α} {x : αᵐᵒᵖ}
  证明: by
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op, congr_arg, mem_inter, mem_smul_set, mem_smul_set.mp, mem_smul_set.mpr
-/
theorem op_smul_inter_nonempty_iff {s t : Set α} {x : αᵐᵒᵖ} :
    (x • s inter t).Nonempty ↔ exists a b, (a in s ∧ b in t) ∧ a⁻¹ * b = MulOpposite.unop x := by
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩

@[to_additive (attr := simp)]
/--
theorem `iUnion_inv_smul` / 定理 `iUnion_inv_smul`

English:
theorem iUnion_inv_smul
  statement: ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s
  proof: (Function.Surjective.iSup_congr _ inv_surjective) fun _ => rfl

@[to_additive]

中文:
定理 iUnion_inv_smul
  结论: ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s
  证明: (Function.Surjective.iSup_congr _ inv_surjective) fun _ => rfl

@[to_additive]

Depends on / 依赖: Function, Function.Surjective.iSup_congr, Surjective, iSup_congr, inv_surjective
-/
theorem iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s :=
  (Function.Surjective.iSup_congr _ inv_surjective) fun _ => rfl

@[to_additive]
/--
theorem `iUnion_smul_eq_ofPred_exists` / 定理 `iUnion_smul_eq_ofPred_exists`

English:
theorem iUnion_smul_eq_ofPred_exists
  given: {s : Set β}
  statement: ⋃ g : α, g • s = { a | exists g : α, g • a in s }
  proof: by
  simp_rw [← iUnion_ofPred, ← iUnion_inv_smul, ← preimage_smul, preimage]

@[deprecated (since := "2026-07-09")]
alias iUnion_smul_eq_setOf_exists := iUnion_smul_eq_ofPred_exists

@[deprecated (since := "2026-07-09")]
alias iUnion_vadd_eq_setOf_exists := iUnion_vadd_eq_ofPred_exists

@[to_additive (attr := simp)]

中文:
定理 iUnion_smul_eq_ofPred_存在
  条件: {s : 集合 β}
  结论: ⋃ g : α, g • s = { a | 存在 g : α, g • a in s }
  证明: by
  simp_rw [← iUnion_ofPred, ← iUnion_inv_smul, ← preimage_smul, preimage]

@[deprecated (since := "2026-07-09")]
alias iUnion_smul_eq_setOf_exists := iUnion_smul_eq_ofPred_exists

@[deprecated (since := "2026-07-09")]
alias iUnion_vadd_eq_setOf_exists := iUnion_vadd_eq_ofPred_exists

@[to_additive (attr := simp)]

Depends on / 依赖: iUnion_inv_smul, iUnion_ofPred, preimage, preimage_smul, simp_rw
-/
theorem iUnion_smul_eq_ofPred_exists {s : Set β} : ⋃ g : α, g • s = { a | exists g : α, g • a in s } := by
  simp_rw [← iUnion_ofPred, ← iUnion_inv_smul, ← preimage_smul, preimage]

@[deprecated (since := "2026-07-09")]
alias iUnion_smul_eq_setOf_exists := iUnion_smul_eq_ofPred_exists

@[deprecated (since := "2026-07-09")]
alias iUnion_vadd_eq_setOf_exists := iUnion_vadd_eq_ofPred_exists

@[to_additive (attr := simp)]
/--
lemma `inv_smul_set_distrib` / 引理 `inv_smul_set_distrib`

English:
lemma inv_smul_set_distrib
  given: (a : α) (s : Set α)
  statement: (a • s)⁻¹ = op a⁻¹ • s⁻¹
  proof: by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]

中文:
引理 inv_smul_set_distrib
  条件: (a : α) (s : 集合 α)
  结论: (a • s)⁻¹ = op a⁻¹ • s⁻¹
  证明: by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]

Depends on / 依赖: mem_smul_set_iff_inv_smul_mem
-/
lemma inv_smul_set_distrib (a : α) (s : Set α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]
/--
lemma `inv_op_smul_set_distrib` / 引理 `inv_op_smul_set_distrib`

English:
lemma inv_op_smul_set_distrib
  given: (a : α) (s : Set α)
  statement: (op a • s)⁻¹ = a⁻¹ • s⁻¹
  proof: by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]

中文:
引理 inv_op_smul_set_distrib
  条件: (a : α) (s : 集合 α)
  结论: (op a • s)⁻¹ = a⁻¹ • s⁻¹
  证明: by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]

Depends on / 依赖: mem_smul_set_iff_inv_smul_mem
-/
lemma inv_op_smul_set_distrib (a : α) (s : Set α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]
/--
lemma `disjoint_smul_set` / 引理 `disjoint_smul_set`

English:
lemma disjoint_smul_set
  statement: Disjoint (a • s) (a • t) ↔ Disjoint s t
  proof: disjoint_image_iff MulAction.injective _

@[to_additive]

中文:
引理 disjoint_smul_set
  结论: Disjoint (a • s) (a • t) ↔ Disjoint s t
  证明: disjoint_image_iff MulAction.injective _

@[to_additive]

Depends on / 依赖: MulAction, MulAction.injective, disjoint_image_iff, injective
-/
lemma disjoint_smul_set : Disjoint (a • s) (a • t) ↔ Disjoint s t :=
disjoint_image_iff MulAction.injective _

@[to_additive]
/--
lemma `disjoint_smul_set_left` / 引理 `disjoint_smul_set_left`

English:
lemma disjoint_smul_set_left
  statement: Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t)
  proof: by
  simpa using disjoint_smul_set (a := a) (t := a⁻¹ • t)

@[to_additive]

中文:
引理 disjoint_smul_set_left
  结论: Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t)
  证明: by
  simpa using disjoint_smul_set (a := a) (t := a⁻¹ • t)

@[to_additive]

Depends on / 依赖: disjoint_smul_set
-/
lemma disjoint_smul_set_left : Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t) := by
  simpa using disjoint_smul_set (a := a) (t := a⁻¹ • t)

@[to_additive]
/--
lemma `disjoint_smul_set_right` / 引理 `disjoint_smul_set_right`

English:
lemma disjoint_smul_set_right
  statement: Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t
  proof: by
  simpa using disjoint_smul_set (a := a) (s := a⁻¹ • s)

中文:
引理 disjoint_smul_set_right
  结论: Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t
  证明: by
  simpa using disjoint_smul_set (a := a) (s := a⁻¹ • s)

Depends on / 依赖: disjoint_smul_set
-/
lemma disjoint_smul_set_right : Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t := by
  simpa using disjoint_smul_set (a := a) (s := a⁻¹ • s)

/--
lemma `pairwise_disjoint_smul_iff` / 引理 `pairwise_disjoint_smul_iff`

English:
lemma pairwise_disjoint_smul_iff
  proof: by
  simp_rw [Pairwise, disjoint_smul_set_right, ← mul_smul,
    ← not_imp_not (b := _ != _), not_ne_iff, not_disjoint_iff_nonempty_inter]
  exact ⟨fun h a => by simpa using @h a 1,
    fun h i j ne => by simpa [inv_mul_eq_one, eq_comm] using h _ ne⟩

中文:
引理 pairwise_disjoint_smul_iff
  证明: by
  simp_rw [Pairwise, disjoint_smul_set_right, ← mul_smul,
    ← not_imp_not (b := _ != _), not_ne_iff, not_disjoint_iff_nonempty_inter]
  exact ⟨fun h a => by simpa using @h a 1,
    fun h i j ne => by simpa [inv_mul_eq_one, eq_comm] using h _ ne⟩
-/
@[to_additive] lemma pairwise_disjoint_smul_iff :
    Pairwise (Disjoint on fun a : α => a • s) ↔ forall a : α, (a • s inter s).Nonempty -> a = 1 := by
  simp_rw [Pairwise, disjoint_smul_set_right, ← mul_smul,
    ← not_imp_not (b := _ != _), not_ne_iff, not_disjoint_iff_nonempty_inter]
  exact ⟨fun h a => by simpa using @h a 1,
    fun h i j ne => by simpa [inv_mul_eq_one, eq_comm] using h _ ne⟩

/-- Any intersection of translates of two sets `s` and `t` can be covered by a single translate of
`(s⁻¹ * s) ∩ (t⁻¹ * t)`.

This is useful to show that the intersection of approximate subgroups is an approximate subgroup. -/
@[to_additive
/-- Any intersection of translates of two sets `s` and `t` can be covered by a single translate of
`(-s + s) ∩ (-t + t)`.

This is useful to show that the intersection of approximate subgroups is an approximate subgroup.
-/]
/--
lemma `exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul` / 引理 `exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul`

English:
lemma exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul
  given: (s t : Set α) (a b : α)
  proof: by
  obtain hAB | ⟨z, hzA, hzB⟩ := (a • s inter b • t).eq_empty_or_nonempty
  · exact ⟨1, by simp [hAB]⟩
  refine ⟨z, ?_⟩
  calc
    a • s inter b • t subseteq (z • s⁻¹) * s inter ((z • t⁻¹) * t) := by
      gcongr <;> apply smul_set_subset_mul <;> simpa
    _ = z • ((s⁻¹ * s) inter (t⁻¹ * t)) := by simp_rw [Set.smul_set_inter, smul_mul_assoc]

中文:
引理 存在_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul
  条件: (s t : 集合 α) (a b : α)
  证明: by
  obtain hAB | ⟨z, hzA, hzB⟩ := (a • s inter b • t).eq_empty_or_nonempty
  · exact ⟨1, by simp [hAB]⟩
  refine ⟨z, ?_⟩
  calc
    a • s inter b • t subseteq (z • s⁻¹) * s inter ((z • t⁻¹) * t) := by
      gcongr <;> apply smul_set_subset_mul <;> simpa
    _ = z • ((s⁻¹ * s) inter (t⁻¹ * t)) := by simp_rw [Set.smul_set_inter, smul_mul_assoc]

Depends on / 依赖: Set.smul_set_inter, eq_empty_or_nonempty, simp_rw, smul_mul_assoc, smul_set_inter, smul_set_subset_mul, subseteq
-/
lemma exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul (s t : Set α) (a b : α) :
    exists z : α, a • s inter b • t subseteq z • ((s⁻¹ * s) inter (t⁻¹ * t)) := by
  obtain hAB | ⟨z, hzA, hzB⟩ := (a • s inter b • t).eq_empty_or_nonempty
  · exact ⟨1, by simp [hAB]⟩
  refine ⟨z, ?_⟩
  calc
    a • s inter b • t subseteq (z • s⁻¹) * s inter ((z • t⁻¹) * t) := by
      gcongr <;> apply smul_set_subset_mul <;> simpa
    _ = z • ((s⁻¹ * s) inter (t⁻¹ * t)) := by simp_rw [Set.smul_set_inter, smul_mul_assoc]

end Group

section Monoid
variable [Monoid α] [MulAction α β] {s : Set β} {a : α} {b : β}

/--
lemma `mem_invOf_smul_set` / 引理 `mem_invOf_smul_set`

English:
lemma mem_invOf_smul_set
  given: [Invertible a]
  statement: b in ⅟a • s ↔ a • b in s
  proof: mem_inv_smul_set_iff (a := unitOfInvertible a)

中文:
引理 mem_invOf_smul_set
  条件: [可逆 a]
  结论: b in ⅟a • s ↔ a • b in s
  证明: mem_inv_smul_set_iff (a := unitOfInvertible a)
-/
@[simp] lemma mem_invOf_smul_set [Invertible a] : b in ⅟a • s ↔ a • b in s :=
  mem_inv_smul_set_iff (a := unitOfInvertible a)

end Monoid

section Group
variable [Group α] [CommGroup β] [FunLike F α β] [MonoidHomClass F α β]

@[to_additive]
/--
lemma `smul_graphOn` / 引理 `smul_graphOn`

English:
lemma smul_graphOn
  given: (x : α × β) (s : Set α) (f : F)
  proof: by
  ext ⟨a, b⟩
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_iff_eq_mul, mul_left_comm _ _⁻¹,
    eq_inv_mul_iff_mul_eq, ← mul_div_right_comm, div_eq_iff_eq_mul, mul_comm b]

@[to_additive]

中文:
引理 smul_graphOn
  条件: (x : α × β) (s : 集合 α) (f : F)
  证明: by
  ext ⟨a, b⟩
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_iff_eq_mul, mul_left_comm _ _⁻¹,
    eq_inv_mul_iff_mul_eq, ← mul_div_right_comm, div_eq_iff_eq_mul, mul_comm b]

@[to_additive]

Depends on / 依赖: div_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq, inv_mul_eq_iff_eq_mul, mem_smul_set_iff_inv_smul_mem, mul_comm, mul_div_right_comm, mul_left_comm
-/
lemma smul_graphOn (x : α × β) (s : Set α) (f : F) :
    x • s.graphOn f = (x.1 • s).graphOn fun a => x.2 / f x.1 * f a := by
  ext ⟨a, b⟩
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_iff_eq_mul, mul_left_comm _ _⁻¹,
    eq_inv_mul_iff_mul_eq, ← mul_div_right_comm, div_eq_iff_eq_mul, mul_comm b]

@[to_additive]
/--
lemma `smul_graphOn_univ` / 引理 `smul_graphOn_univ`

English:
lemma smul_graphOn_univ
  given: (x : α × β) (f : F)
  proof: by simp [smul_graphOn]

中文:
引理 smul_graphOn_univ
  条件: (x : α × β) (f : F)
  证明: by simp [smul_graphOn]

Depends on / 依赖: smul_graphOn
-/
lemma smul_graphOn_univ (x : α × β) (f : F) :
    x • univ.graphOn f = univ.graphOn fun a => x.2 / f x.1 * f a := by simp [smul_graphOn]

end Group

section CommGroup
variable [CommGroup α]

/--
lemma `smul_div_smul_comm` / 引理 `smul_div_smul_comm`

English:
lemma smul_div_smul_comm
  given: (a : α) (s : Set α) (b : α) (t : Set α)
  proof: by
  simp_rw [← image_smul, smul_eq_mul, ← singleton_mul, mul_div_mul_comm _ s,
    singleton_div_singleton]

中文:
引理 smul_div_smul_comm
  条件: (a : α) (s : 集合 α) (b : α) (t : 集合 α)
  证明: by
  simp_rw [← image_smul, smul_eq_mul, ← singleton_mul, mul_div_mul_comm _ s,
    singleton_div_singleton]
-/
@[to_additive] lemma smul_div_smul_comm (a : α) (s : Set α) (b : α) (t : Set α) :
    a • s / b • t = (a / b) • (s / t) := by
  simp_rw [← image_smul, smul_eq_mul, ← singleton_mul, mul_div_mul_comm _ s,
    singleton_div_singleton]

end CommGroup
end Set
