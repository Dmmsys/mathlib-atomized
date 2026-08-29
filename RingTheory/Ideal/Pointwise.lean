/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.RingTheory.Ideal.Maps

/-! # Pointwise instances on `Ideal`s

This file provides the action `Ideal.pointwiseMulAction` which morally matches the action of
`mulActionSet` (though here an extra `Ideal.span` is inserted).

This action is available in the `Pointwise` locale.

## Implementation notes

This file is similar (but not identical) to `Mathlib/Algebra/Ring/Subsemiring/Pointwise.lean`.
Where possible, try to keep them in sync.

-/

@[expose] public section


open Set

variable {M N R : Type*}

namespace Ideal

section Monoid

variable [Monoid M] [Monoid N] [Semiring R] [MulSemiringAction M R] [MulSemiringAction N R]

/-- The action on an ideal corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseDistribMulAction` / `pointwiseDistribMulAction` 的定义

English:
definition pointwiseDistribMulAction
  signature: : DistribMulAction M (Ideal R) where
  body: Ideal.map (MulSemiringAction.toRingHom _ _ a)
  one_smul I :=
.trans I.map_id congr_arg (I.map ·) (RingHom.ext <| one_smul M)
  mul_smul _ _ I :=
.trans (I.map_map _ _).symm congr_arg (I.map ·) (RingHom.ext <| mul_smul _ _)
  smul_zero _ := Ideal.map_bot
  smul_add _ I J := Ideal.map_sup _ I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseDistribMulAction

中文:
定义 pointwiseDistribMulAction
  签名: : 分配乘法作用 M (理想 R) where
  定义体: Ideal.map (MulSemiringAction.toRingHom _ _ a)
  one_smul I :=
.trans I.map_id congr_arg (I.map ·) (RingHom.ext <| one_smul M)
  mul_smul _ _ I :=
.trans (I.map_map _ _).symm congr_arg (I.map ·) (RingHom.ext <| mul_smul _ _)
  smul_zero _ := Ideal.map_bot
  smul_add _ I J := Ideal.map_sup _ I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseDistribMulAction
-/
protected def pointwiseDistribMulAction : DistribMulAction M (Ideal R) where
  smul a := Ideal.map (MulSemiringAction.toRingHom _ _ a)
  one_smul I :=
.trans I.map_id congr_arg (I.map ·) (RingHom.ext <| one_smul M)
  mul_smul _ _ I :=
.trans (I.map_map _ _).symm congr_arg (I.map ·) (RingHom.ext <| mul_smul _ _)
  smul_zero _ := Ideal.map_bot
  smul_add _ I J := Ideal.map_sup _ I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseDistribMulAction

open scoped Pointwise

/-- The action on an ideal corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `pointwiseMulSemiringAction` / `pointwiseMulSemiringAction` 的定义

English:
definition pointwiseMulSemiringAction
  signature: {R : Type*} [CommRing R] [MulSemiringAction M R]
  body: by simp only [Ideal.one_eq_top]; exact Ideal.map_top _
  smul_mul a I J := Ideal.map_mul (MulSemiringAction.toRingHom _ _ a) I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseMulSemiringAction

中文:
定义 pointwiseMulSemiringAction
  签名: {R : 类型} [交换环 R] [MulSemiring作用 M R]
  定义体: by simp only [Ideal.one_eq_top]; exact Ideal.map_top _
  smul_mul a I J := Ideal.map_mul (MulSemiringAction.toRingHom _ _ a) I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseMulSemiringAction
-/
protected def pointwiseMulSemiringAction {R : Type*} [CommRing R] [MulSemiringAction M R] :
    MulSemiringAction M (Ideal R) where
  smul_one a := by simp only [Ideal.one_eq_top]; exact Ideal.map_top _
  smul_mul a I J := Ideal.map_mul (MulSemiringAction.toRingHom _ _ a) I J

scoped[Pointwise] attribute [instance] Ideal.pointwiseMulSemiringAction

/--
theorem `pointwise_smul_def` / 定理 `pointwise_smul_def`

English:
theorem pointwise_smul_def
  given: {a : M} (S : Ideal R)
  proof: rfl

中文:
定理 pointwise_smul_def
  条件: {a : M} (S : 理想 R)
  证明: rfl
-/
theorem pointwise_smul_def {a : M} (S : Ideal R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M N] [IsScalarTower M N R] : IsScalarTower M N (Ideal R) where
  body: by
    simp_rw [pointwise_smul_def, map_map]
    congr
    ext
    simp

中文:
实例 [标量乘法
  签名: M N] [标量塔 M N R] : 标量塔 M N (理想 R) where
  定义体: by
    simp_rw [pointwise_smul_def, map_map]
    congr
    ext
    simp

Depends on / 依赖: map_map, pointwise_smul_def, simp_rw
-/
instance [SMul M N] [IsScalarTower M N R] : IsScalarTower M N (Ideal R) where
  smul_assoc x y z := by
    simp_rw [pointwise_smul_def, map_map]
    congr
    ext
    simp

-- note: unlike with `Subring`, `pointwise_smul_toAddSubgroup` wouldn't be true

/--
theorem `smul_mem_pointwise_smul` / 定理 `smul_mem_pointwise_smul`

English:
theorem smul_mem_pointwise_smul
  given: (m : M) (r : R) (S : Ideal R)
  statement: r in S -> m • r in m • S
  proof: fun h => subset_span Set.smul_mem_smul_set h

中文:
定理 smul_mem_pointwise_smul
  条件: (m : M) (r : R) (S : 理想 R)
  结论: r in S -> m • r in m • S
  证明: fun h => subset_span Set.smul_mem_smul_set h

Depends on / 依赖: Set.smul_mem_smul_set, smul_mem_smul_set, subset_span
-/
theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Ideal R) : r in S -> m • r in m • S :=
fun h => subset_span Set.smul_mem_smul_set h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CovariantClass M (Ideal R) HSMul.hSMul LE.le
  body: ⟨fun _ _ => map_mono⟩

中文:
实例 :
  签名: 协变类 M (理想 R) 异质标量乘法.hSMul LE.le
  定义体: ⟨fun _ _ => map_mono⟩

Depends on / 依赖: map_mono
-/
instance : CovariantClass M (Ideal R) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

-- note: unlike with `Subring`, `mem_smul_pointwise_iff_exists` wouldn't be true

@[simp]
/--
theorem `smul_bot` / 定理 `smul_bot`

English:
theorem smul_bot
  given: (a : M)
  statement: a • (⊥ : Ideal R) = ⊥
  proof: map_bot

中文:
定理 smul_bot
  条件: (a : M)
  结论: a • (⊥ : 理想 R) = ⊥
  证明: map_bot

Depends on / 依赖: map_bot
-/
theorem smul_bot (a : M) : a • (⊥ : Ideal R) = ⊥ :=
  map_bot

/--
theorem `smul_sup` / 定理 `smul_sup`

English:
theorem smul_sup
  given: (a : M) (S T : Ideal R)
  statement: a • (S ⊔ T) = a • S ⊔ a • T
  proof: map_sup _ _ _

中文:
定理 smul_sup
  条件: (a : M) (S T : 理想 R)
  结论: a • (S ⊔ T) = a • S ⊔ a • T
  证明: map_sup _ _ _

Depends on / 依赖: map_sup
-/
theorem smul_sup (a : M) (S T : Ideal R) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

/--
theorem `smul_closure` / 定理 `smul_closure`

English:
theorem smul_closure
  given: (a : M) (s : Set R)
  statement: a • span s = span (a • s)
  proof: Ideal.map_span _ _

中文:
定理 smul_closure
  条件: (a : M) (s : 集合 R)
  结论: a • span s = span (a • s)
  证明: Ideal.map_span _ _

Depends on / 依赖: Ideal.map_span, map_span
-/
theorem smul_closure (a : M) (s : Set R) : a • span s = span (a • s) :=
  Ideal.map_span _ _

/--
Instance `pointwise_central_scalar` / 实例 `pointwise_central_scalar`

English:
instance pointwise_central_scalar
  signature: [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R]
  body: ⟨fun _ S => (congr_arg fun f => S.map f) RingHom.ext op_smul_eq_smul _⟩

@[simp]

中文:
实例 pointwise_central_scalar
  签名: [MulSemiring作用 Mᵐᵒᵖ R] [中心标量 M R]
  定义体: ⟨fun _ S => (congr_arg fun f => S.map f) RingHom.ext op_smul_eq_smul _⟩

@[simp]

Depends on / 依赖: RingHom, RingHom.ext, S.map, congr_arg, op_smul_eq_smul
-/
instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] :
    IsCentralScalar M (Ideal R) :=
⟨fun _ S => (congr_arg fun f => S.map f) RingHom.ext op_smul_eq_smul _⟩

@[simp]
/--
theorem `pointwise_smul_toAddSubmonoid` / 定理 `pointwise_smul_toAddSubmonoid`

English:
theorem pointwise_smul_toAddSubmonoid
  statement: (a : M) (S : Ideal R)
  proof: by
  ext
exact Ideal.mem_map_iff_of_surjective _ by exact ha

@[simp]

中文:
定理 pointwise_smul_toAddSubmonoid
  结论: (a : M) (S : 理想 R)
  证明: by
  ext
exact Ideal.mem_map_iff_of_surjective _ by exact ha

@[simp]

Depends on / 依赖: Ideal.mem_map_iff_of_surjective, mem_map_iff_of_surjective
-/
theorem pointwise_smul_toAddSubmonoid (a : M) (S : Ideal R)
    (ha : Function.Surjective fun r : R => a • r) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid := by
  ext
exact Ideal.mem_map_iff_of_surjective _ by exact ha

@[simp]
/--
theorem `pointwise_smul_toAddSubgroup` / 定理 `pointwise_smul_toAddSubgroup`

English:
theorem pointwise_smul_toAddSubgroup
  statement: {R : Type*} [Ring R] [MulSemiringAction M R]
  proof: by
  ext
exact Ideal.mem_map_iff_of_surjective _ by exact ha

中文:
定理 pointwise_smul_toAddSubgroup
  结论: {R : 类型} [环 R] [MulSemiring作用 M R]
  证明: by
  ext
exact Ideal.mem_map_iff_of_surjective _ by exact ha

Depends on / 依赖: Ideal.mem_map_iff_of_surjective, mem_map_iff_of_surjective
-/
theorem pointwise_smul_toAddSubgroup {R : Type*} [Ring R] [MulSemiringAction M R]
    (a : M) (S : Ideal R) (ha : Function.Surjective fun r : R => a • r) :
    (a • S).toAddSubgroup = a • S.toAddSubgroup := by
  ext
exact Ideal.mem_map_iff_of_surjective _ by exact ha

end Monoid

section Group

variable [Group M] [Semiring R] [MulSemiringAction M R]

open scoped Pointwise

/--
theorem `pointwise_smul_eq_comap` / 定理 `pointwise_smul_eq_comap`

English:
theorem pointwise_smul_eq_comap
  given: {a : M} (S : Ideal R)
  proof: by
  ext
  simp [pointwise_smul_def]
  rfl

@[simp]

中文:
定理 pointwise_smul_eq_comap
  条件: {a : M} (S : 理想 R)
  证明: by
  ext
  simp [pointwise_smul_def]
  rfl

@[simp]

Depends on / 依赖: pointwise_smul_def
-/
theorem pointwise_smul_eq_comap {a : M} (S : Ideal R) :
    a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm := by
  ext
  simp [pointwise_smul_def]
  rfl

@[simp]
/--
theorem `smul_mem_pointwise_smul_iff` / 定理 `smul_mem_pointwise_smul_iff`

English:
theorem smul_mem_pointwise_smul_iff
  given: {a : M} {S : Ideal R} {x : R}
  statement: a • x in a • S ↔ x in S
  proof: ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h, smul_mem_pointwise_smul _ _ _⟩

中文:
定理 smul_mem_pointwise_smul_iff
  条件: {a : M} {S : 理想 R} {x : R}
  结论: a • x in a • S ↔ x in S
  证明: ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h, smul_mem_pointwise_smul _ _ _⟩

Depends on / 依赖: smul_mem_pointwise_smul
-/
theorem smul_mem_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : a • x in a • S ↔ x in S :=
  ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h, smul_mem_pointwise_smul _ _ _⟩

/--
theorem `mem_pointwise_smul_iff_inv_smul_mem` / 定理 `mem_pointwise_smul_iff_inv_smul_mem`

English:
theorem mem_pointwise_smul_iff_inv_smul_mem
  given: {a : M} {S : Ideal R} {x : R}
  proof: ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h,
    fun h => by simpa using smul_mem_pointwise_smul a _ _ h⟩

中文:
定理 mem_pointwise_smul_iff_inv_smul_mem
  条件: {a : M} {S : 理想 R} {x : R}
  证明: ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h,
    fun h => by simpa using smul_mem_pointwise_smul a _ _ h⟩

Depends on / 依赖: smul_mem_pointwise_smul
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Ideal R} {x : R} :
    x in a • S ↔ a⁻¹ • x in S :=
  ⟨fun h => by simpa using smul_mem_pointwise_smul a⁻¹ _ _ h,
    fun h => by simpa using smul_mem_pointwise_smul a _ _ h⟩

/--
theorem `mem_inv_pointwise_smul_iff` / 定理 `mem_inv_pointwise_smul_iff`

English:
theorem mem_inv_pointwise_smul_iff
  given: {a : M} {S : Ideal R} {x : R}
  statement: x in a⁻¹ • S ↔ a • x in S
  proof: by
  rw [mem_pointwise_smul_iff_inv_smul_mem]; rw [inv_inv]

@[simp]

中文:
定理 mem_inv_pointwise_smul_iff
  条件: {a : M} {S : 理想 R} {x : R}
  结论: x in a⁻¹ • S ↔ a • x in S
  证明: by
  rw [mem_pointwise_smul_iff_inv_smul_mem]; rw [inv_inv]

@[simp]

Depends on / 依赖: inv_inv, mem_pointwise_smul_iff_inv_smul_mem
-/
theorem mem_inv_pointwise_smul_iff {a : M} {S : Ideal R} {x : R} : x in a⁻¹ • S ↔ a • x in S := by
  rw [mem_pointwise_smul_iff_inv_smul_mem]; rw [inv_inv]

@[simp]
/--
theorem `pointwise_smul_le_pointwise_smul_iff` / 定理 `pointwise_smul_le_pointwise_smul_iff`

English:
theorem pointwise_smul_le_pointwise_smul_iff
  given: {a : M} {S T : Ideal R}
  statement: a • S <= a • T ↔ S <= T
  proof: ⟨fun h => by simpa using smul_mono_right a⁻¹ h, fun h => smul_mono_right a h⟩

中文:
定理 pointwise_smul_le_pointwise_smul_iff
  条件: {a : M} {S T : 理想 R}
  结论: a • S <= a • T ↔ S <= T
  证明: ⟨fun h => by simpa using smul_mono_right a⁻¹ h, fun h => smul_mono_right a h⟩

Depends on / 依赖: smul_mono_right
-/
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Ideal R} : a • S <= a • T ↔ S <= T :=
  ⟨fun h => by simpa using smul_mono_right a⁻¹ h, fun h => smul_mono_right a h⟩

/--
theorem `pointwise_smul_subset_iff` / 定理 `pointwise_smul_subset_iff`

English:
theorem pointwise_smul_subset_iff
  given: {a : M} {S T : Ideal R}
  statement: a • S <= T ↔ S <= a⁻¹ • T
  proof: by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹)]; rw [inv_smul_smul]

中文:
定理 pointwise_smul_subset_iff
  条件: {a : M} {S T : 理想 R}
  结论: a • S <= T ↔ S <= a⁻¹ • T
  证明: by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹)]; rw [inv_smul_smul]

Depends on / 依赖: inv_smul_smul, pointwise_smul_le_pointwise_smul_iff
-/
theorem pointwise_smul_subset_iff {a : M} {S T : Ideal R} : a • S <= T ↔ S <= a⁻¹ • T := by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹)]; rw [inv_smul_smul]

/--
theorem `subset_pointwise_smul_iff` / 定理 `subset_pointwise_smul_iff`

English:
theorem subset_pointwise_smul_iff
  given: {a : M} {S T : Ideal R}
  statement: S <= a • T ↔ a⁻¹ • S <= T
  proof: by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹)]; rw [inv_smul_smul]

中文:
定理 subset_pointwise_smul_iff
  条件: {a : M} {S T : 理想 R}
  结论: S <= a • T ↔ a⁻¹ • S <= T
  证明: by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹)]; rw [inv_smul_smul]

Depends on / 依赖: inv_smul_smul, pointwise_smul_le_pointwise_smul_iff
-/
theorem subset_pointwise_smul_iff {a : M} {S T : Ideal R} : S <= a • T ↔ a⁻¹ • S <= T := by
  rw [← pointwise_smul_le_pointwise_smul_iff (a := a⁻¹)]; rw [inv_smul_smul]

/--
Instance `IsPrime.smul` / 实例 `IsPrime.smul`

English:
instance IsPrime.smul
  signature: {I : Ideal R} [H : I.IsPrime] (g : M)
  body: by
  rw [I.pointwise_smul_eq_comap]
  apply H.comap

@[simp]

中文:
实例 是素.smul
  签名: {I : 理想 R} [H : I.是素] (g : M)
  定义体: by
  rw [I.pointwise_smul_eq_comap]
  apply H.comap

@[simp]

Depends on / 依赖: H.comap, I.pointwise_smul_eq_comap, pointwise_smul_eq_comap
-/
instance IsPrime.smul {I : Ideal R} [H : I.IsPrime] (g : M) : (g • I).IsPrime := by
  rw [I.pointwise_smul_eq_comap]
  apply H.comap

@[simp]
/--
theorem `IsPrime.smul_iff` / 定理 `IsPrime.smul_iff`

English:
theorem IsPrime.smul_iff
  given: {I : Ideal R} (g : M)
  statement: (g • I).IsPrime ↔ I.IsPrime
  proof: ⟨fun H => inv_smul_smul g I ▸ H.smul g⁻¹, fun H => H.smul g⟩

中文:
定理 是素.smul_iff
  条件: {I : 理想 R} (g : M)
  结论: (g • I).是素 ↔ I.是素
  证明: ⟨fun H => inv_smul_smul g I ▸ H.smul g⁻¹, fun H => H.smul g⟩

Depends on / 依赖: H.smul, inv_smul_smul
-/
theorem IsPrime.smul_iff {I : Ideal R} (g : M) : (g • I).IsPrime ↔ I.IsPrime :=
  ⟨fun H => inv_smul_smul g I ▸ H.smul g⁻¹, fun H => H.smul g⟩

/--
theorem `inertia_le_stabilizer` / 定理 `inertia_le_stabilizer`

English:
theorem inertia_le_stabilizer
  given: {R : Type*} [Ring R] (P : Ideal R) [MulSemiringAction M R]
  proof: by
  refine fun σ hσ => SetLike.ext fun x => ?_
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]; rw [← P.add_mem_iff_left (a := x) ((inv_mem hσ) x)]; rw [add_sub_cancel]

中文:
定理 inertia_le_stabilizer
  条件: {R : 类型} [环 R] (P : 理想 R) [MulSemiring作用 M R]
  证明: by
  refine fun σ hσ => SetLike.ext fun x => ?_
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]; rw [← P.add_mem_iff_left (a := x) ((inv_mem hσ) x)]; rw [add_sub_cancel]

Depends on / 依赖: Ideal.mem_pointwise_smul_iff_inv_smul_mem, P.add_mem_iff_left, SetLike, SetLike.ext, add_mem_iff_left, add_sub_cancel, inv_mem, mem_pointwise_smul_iff_inv_smul_mem
-/
theorem inertia_le_stabilizer {R : Type*} [Ring R] (P : Ideal R) [MulSemiringAction M R] :
    inertia M P <= MulAction.stabilizer M P := by
  refine fun σ hσ => SetLike.ext fun x => ?_
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]; rw [← P.add_mem_iff_left (a := x) ((inv_mem hσ) x)]; rw [add_sub_cancel]

instance {R : Type*} [Ring R] (P : Ideal R) [MulSemiringAction M R] :
  (P.inertia (MulAction.stabilizer M P)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff (inertia_le_stabilizer P)).mpr fun g s hg hs x => ?_
  rw [Submodule.mem_toAddSubgroup]; rw [← Ideal.smul_mem_pointwise_smul_iff (a := s⁻¹)]; rw [smul_sub]; rw [smul_smul]; rw [← mul_assoc]; rw [inv_mul_cancel_left]; rw [mul_smul]; rw [Subgroup.inv_mem _ hs]
  exact hg (s⁻¹ • x)

variable {N : Type*} [Group N] [MulSemiringAction N R]

/--
Definition of `stabilizerEquiv` / `stabilizerEquiv` 的定义

English:
definition stabilizerEquiv
  signature: (I : Ideal R) (e : M ≃* N) (he : forall (m : M) (x : R), (e m) • x = m • x)
  body: Equiv.subtypeEquiv e fun _ => by
    simp [Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, he]
  map_mul' _ _ := by simp

@[simp]

中文:
定义 stabilizerEquiv
  签名: (I : 理想 R) (e : M ≃* N) (he : 对任意 (m : M) (x : R), (e m) • x = m • x)
  定义体: Equiv.subtypeEquiv e fun _ => by
    simp [Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, he]
  map_mul' _ _ := by simp

@[simp]

Depends on / 依赖: Equiv.subtypeEquiv, Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ext_iff, map_inv, map_mul, mem_pointwise_smul_iff_inv_smul_mem, subtypeEquiv
-/
def stabilizerEquiv (I : Ideal R) (e : M ≃* N) (he : forall (m : M) (x : R), (e m) • x = m • x) :
    MulAction.stabilizer M I ≃* MulAction.stabilizer N I where
  toEquiv := Equiv.subtypeEquiv e fun _ => by
    simp [Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, he]
  map_mul' _ _ := by simp

@[simp]
/--
theorem `stabilizerEquiv_apply_smul` / 定理 `stabilizerEquiv_apply_smul`

English:
theorem stabilizerEquiv_apply_smul
  statement: (I : Ideal R) (e : M ≃* N)
  proof: by
  simp [stabilizerEquiv, MulAction.subgroup_smul_def, ← he m x]

@[simp]

中文:
定理 stabilizerEquiv_apply_smul
  结论: (I : 理想 R) (e : M ≃* N)
  证明: by
  simp [stabilizerEquiv, MulAction.subgroup_smul_def, ← he m x]

@[simp]

Depends on / 依赖: MulAction, MulAction.subgroup_smul_def, stabilizerEquiv, subgroup_smul_def
-/
theorem stabilizerEquiv_apply_smul (I : Ideal R) (e : M ≃* N)
    (he : forall (m : M) (x : R), (e m) • x = m • x) (m : MulAction.stabilizer M I) (x : R) :
    stabilizerEquiv I e he m • x = m • x := by
  simp [stabilizerEquiv, MulAction.subgroup_smul_def, ← he m x]

@[simp]
/--
theorem `stabilizerEquiv_symm_apply_smul` / 定理 `stabilizerEquiv_symm_apply_smul`

English:
theorem stabilizerEquiv_symm_apply_smul
  statement: (I : Ideal R) (e : M ≃* N)
  proof: by
  rw [← (stabilizerEquiv I e he).apply_symm_apply n]; rw [stabilizerEquiv_apply_smul]; rw [(stabilizerEquiv I e he).apply_symm_apply]

中文:
定理 stabilizerEquiv_symm_apply_smul
  结论: (I : 理想 R) (e : M ≃* N)
  证明: by
  rw [← (stabilizerEquiv I e he).apply_symm_apply n]; rw [stabilizerEquiv_apply_smul]; rw [(stabilizerEquiv I e he).apply_symm_apply]

Depends on / 依赖: apply_symm_apply, stabilizerEquiv, stabilizerEquiv_apply_smul
-/
theorem stabilizerEquiv_symm_apply_smul (I : Ideal R) (e : M ≃* N)
    (he : forall (m : M) (x : R), (e m) • x = m • x) (n : MulAction.stabilizer N I) (x : R) :
    (stabilizerEquiv I e he).symm n • x = n • x := by
  rw [← (stabilizerEquiv I e he).apply_symm_apply n]; rw [stabilizerEquiv_apply_smul]; rw [(stabilizerEquiv I e he).apply_symm_apply]

/--
Definition of `inertiaEquiv` / `inertiaEquiv` 的定义

English:
definition inertiaEquiv
  signature: {R : Type*} [Ring R] [MulSemiringAction M R] [MulSemiringAction N R] (I : Ideal R)
  body: Equiv.subtypeEquiv e fun _ => by simp [he]
  map_mul' := by simp

@[simp]

中文:
定义 inertiaEquiv
  签名: {R : 类型} [环 R] [MulSemiring作用 M R] [MulSemiring作用 N R] (I : 理想 R)
  定义体: Equiv.subtypeEquiv e fun _ => by simp [he]
  map_mul' := by simp

@[simp]

Depends on / 依赖: Equiv.subtypeEquiv, subtypeEquiv
-/
def inertiaEquiv {R : Type*} [Ring R] [MulSemiringAction M R] [MulSemiringAction N R] (I : Ideal R)
    (e : M ≃* N) (he : forall (m : M) (x : R), (e m) • x = m • x) :
    inertia M I ≃* inertia N I where
  toEquiv := Equiv.subtypeEquiv e fun _ => by simp [he]
  map_mul' := by simp

@[simp]
/--
theorem `inertiaEquiv_apply_smul` / 定理 `inertiaEquiv_apply_smul`

English:
theorem inertiaEquiv_apply_smul
  statement: {R : Type*} [Ring R] [MulSemiringAction M R] [MulSemiringAction N R]
  proof: by
  simp [inertiaEquiv, MulAction.subgroup_smul_def, ← he m x]

@[simp]

中文:
定理 inertiaEquiv_apply_smul
  结论: {R : 类型} [环 R] [MulSemiring作用 M R] [MulSemiring作用 N R]
  证明: by
  simp [inertiaEquiv, MulAction.subgroup_smul_def, ← he m x]

@[simp]

Depends on / 依赖: MulAction, MulAction.subgroup_smul_def, inertiaEquiv, subgroup_smul_def
-/
theorem inertiaEquiv_apply_smul {R : Type*} [Ring R] [MulSemiringAction M R] [MulSemiringAction N R]
    (I : Ideal R) (e : M ≃* N) (he : forall (m : M) (x : R), (e m) • x = m • x) (m : inertia M I)
    (x : R) :
    inertiaEquiv I e he m • x = m • x := by
  simp [inertiaEquiv, MulAction.subgroup_smul_def, ← he m x]

@[simp]
/--
theorem `inertiaEquiv_symm_apply_smul` / 定理 `inertiaEquiv_symm_apply_smul`

English:
theorem inertiaEquiv_symm_apply_smul
  statement: {R : Type*} [Ring R] [MulSemiringAction M R]
  proof: by
  rw [← (inertiaEquiv I e he).apply_symm_apply n]; rw [inertiaEquiv_apply_smul]; rw [(inertiaEquiv I e he).apply_symm_apply]

中文:
定理 inertiaEquiv_symm_apply_smul
  结论: {R : 类型} [环 R] [MulSemiring作用 M R]
  证明: by
  rw [← (inertiaEquiv I e he).apply_symm_apply n]; rw [inertiaEquiv_apply_smul]; rw [(inertiaEquiv I e he).apply_symm_apply]

Depends on / 依赖: apply_symm_apply, inertiaEquiv, inertiaEquiv_apply_smul
-/
theorem inertiaEquiv_symm_apply_smul {R : Type*} [Ring R] [MulSemiringAction M R]
    [MulSemiringAction N R] (I : Ideal R) (e : M ≃* N) (he : forall (m : M) (x : R), (e m) • x = m • x)
    (n : inertia N I) (x : R) :
    (inertiaEquiv I e he).symm n • x = n • x := by
  rw [← (inertiaEquiv I e he).apply_symm_apply n]; rw [inertiaEquiv_apply_smul]; rw [(inertiaEquiv I e he).apply_symm_apply]

/-! TODO: add `equivSMul` like we have for subgroup. -/

end Group

end Ideal
