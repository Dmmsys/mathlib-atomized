/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous subsemirings of a graded semiring

This file defines homogeneous subsemirings of a graded semiring, as well as operations on them.

## Main definitions

* `HomogeneousSubsemiring 𝒜`: The type of subsemirings which satisfy `SetLike.IsHomogeneous`.
-/

@[expose] public section

open DirectSum Set SetLike

variable {ι σ A : Type*} [AddMonoid ι] [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι -> σ) [DecidableEq ι] [GradedRing 𝒜]
variable (R : Subsemiring A)

section HomogeneousDef

variable {R} in
/--
theorem `DirectSum.SetLike.IsHomogeneous.mem_iff` / 定理 `DirectSum.SetLike.IsHomogeneous.mem_iff`

English:
theorem DirectSum.SetLike.IsHomogeneous.mem_iff
  given: (hR : IsHomogeneous 𝒜 R) {a}
  proof: AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hR

中文:
定理 直和.集合状.IsHomogeneous.mem_iff
  条件: (hR : IsHomogeneous 𝒜 R) {a}
  证明: AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hR

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.IsHomogeneous.mem_iff, IsHomogeneous, mem_iff
-/
theorem DirectSum.SetLike.IsHomogeneous.mem_iff (hR : IsHomogeneous 𝒜 R) {a} :
    a in R ↔ forall i, (decompose 𝒜 a i : A) in R :=
  AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hR

/--
Definition of `HomogeneousSubsemiring` / `HomogeneousSubsemiring` 的定义

English:
structure HomogeneousSubsemiring
  parameters: extends Subsemiring A
  extends: Subsemiring A
  axioms and operations (1):
    - is_homogeneous' : IsHomogeneous 𝒜 toSubsemiring

中文:
结构 齐次子半环
  参数: extends 子半环 A
  继承: 子半环 A
  公理与运算 (1 个):
    - is_homogeneous' : IsHomogeneous 𝒜 toSubsemiring
-/
structure HomogeneousSubsemiring extends Subsemiring A where
  is_homogeneous' : IsHomogeneous 𝒜 toSubsemiring

variable {𝒜}

namespace HomogeneousSubsemiring

/--
theorem `toSubsemiring_injective` / 定理 `toSubsemiring_injective`

English:
theorem toSubsemiring_injective
  proof: fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]

中文:
定理 toSubsemiring_injective
  证明: fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]
-/
theorem toSubsemiring_injective :
    (toSubsemiring : HomogeneousSubsemiring 𝒜 -> Subsemiring A).Injective :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]

/--
Instance `setLike` / 实例 `setLike`

English:
instance setLike
  signature: : SetLike (HomogeneousSubsemiring 𝒜) A where
  body: x.carrier
coe_injective _ _ h := toSubsemiring_injective SetLike.coe_injective h

中文:
实例 setLike
  签名: : 集合状 (齐次子半环 𝒜) A where
  定义体: x.carrier
coe_injective _ _ h := toSubsemiring_injective SetLike.coe_injective h

Depends on / 依赖: carrier, x.carrier
-/
instance setLike : SetLike (HomogeneousSubsemiring 𝒜) A where
  coe x := x.carrier
coe_injective _ _ h := toSubsemiring_injective SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (HomogeneousSubsemiring 𝒜)
  body: .ofSetLike (HomogeneousSubsemiring 𝒜) A

中文:
实例 :
  签名: 偏序 (齐次子半环 𝒜)
  定义体: .ofSetLike (HomogeneousSubsemiring 𝒜) A

Depends on / 依赖: HomogeneousSubsemiring, ofSetLike
-/
instance : PartialOrder (HomogeneousSubsemiring 𝒜) := .ofSetLike (HomogeneousSubsemiring 𝒜) A

/--
theorem `isHomogeneous` / 定理 `isHomogeneous`

English:
theorem isHomogeneous
  given: (R : HomogeneousSubsemiring 𝒜)
  proof: R.is_homogeneous'

中文:
定理 isHomogeneous
  条件: (R : 齐次子半环 𝒜)
  证明: R.is_homogeneous'

Depends on / 依赖: R.is_homogeneous, is_homogeneous
-/
theorem isHomogeneous (R : HomogeneousSubsemiring 𝒜) :
    IsHomogeneous 𝒜 R := R.is_homogeneous'

/--
Instance `subsemiringClass` / 实例 `subsemiringClass`

English:
instance subsemiringClass
  signature: : SubsemiringClass (HomogeneousSubsemiring 𝒜) A where
  body: a.toSubsemiring.mul_mem
  one_mem {a} := a.toSubsemiring.one_mem
  add_mem {a} := a.toSubsemiring.add_mem
  zero_mem {a} := a.toSubsemiring.zero_mem

@[ext]

中文:
实例 subsemiringClass
  签名: : 子半环类 (齐次子半环 𝒜) A where
  定义体: a.toSubsemiring.mul_mem
  one_mem {a} := a.toSubsemiring.one_mem
  add_mem {a} := a.toSubsemiring.add_mem
  zero_mem {a} := a.toSubsemiring.zero_mem

@[ext]

Depends on / 依赖: a.toSubsemiring.mul_mem, mul_mem, toSubsemiring
-/
instance subsemiringClass : SubsemiringClass (HomogeneousSubsemiring 𝒜) A where
  mul_mem {a} := a.toSubsemiring.mul_mem
  one_mem {a} := a.toSubsemiring.one_mem
  add_mem {a} := a.toSubsemiring.add_mem
  zero_mem {a} := a.toSubsemiring.zero_mem

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {R S : HomogeneousSubsemiring 𝒜}
  proof: HomogeneousSubsemiring.toSubsemiring_injective h

中文:
定理 ext
  结论: {R S : 齐次子半环 𝒜}
  证明: HomogeneousSubsemiring.toSubsemiring_injective h

Depends on / 依赖: HomogeneousSubsemiring, HomogeneousSubsemiring.toSubsemiring_injective, toSubsemiring_injective
-/
theorem ext {R S : HomogeneousSubsemiring 𝒜}
    (h : R.toSubsemiring = S.toSubsemiring) : R = S :=
  HomogeneousSubsemiring.toSubsemiring_injective h

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  statement: {R S : HomogeneousSubsemiring 𝒜}
  proof: AddSubmonoidClass.IsHomogeneous.ext R.2 S.2 h

@[simp high]

中文:
定理 ext'
  结论: {R S : 齐次子半环 𝒜}
  证明: AddSubmonoidClass.IsHomogeneous.ext R.2 S.2 h

@[simp high]

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.IsHomogeneous.ext, IsHomogeneous
-/
theorem ext' {R S : HomogeneousSubsemiring 𝒜}
    (h : forall i, forall a in 𝒜 i, a in R ↔ a in S) : R = S :=
  AddSubmonoidClass.IsHomogeneous.ext R.2 S.2 h

@[simp high]
/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {R : HomogeneousSubsemiring 𝒜} {a}
  proof: Iff.rfl

中文:
定理 mem_iff
  条件: {R : 齐次子半环 𝒜} {a}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_iff {R : HomogeneousSubsemiring 𝒜} {a} :
    a in R.toSubsemiring ↔ a in R :=
  Iff.rfl

end HomogeneousSubsemiring

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsHomogeneous.subsemiringClosure` / 定理 `IsHomogeneous.subsemiringClosure`

English:
theorem IsHomogeneous.subsemiringClosure
  statement: {s : Set A}
  proof: fun i x hx => by
  induction hx using Subsemiring.closure_induction generalizing i with
| mem _ hx => exact Subsemiring.subset_closure h i hx
  | zero => simp
  | one =>
    rw [decompose_one]; rw [one_def]
    obtain rfl | h := eq_or_ne i 0 <;> simp [of_eq_of_ne, *]
  | add _ _ _ _ h₁ h₂ => simpa using add_mem (h₁ i) (h₂ i)
  | mul x y _ _ h₁ h₂ =>
    classical
    rw [decompose_mul]; rw [DirectSum.mul_eq_dfinsuppSum]
    rw [DFinsupp.sum_apply]; rw [DFinsupp.sum]; rw [AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun j _ => ?_
    rw [DFinsupp.sum_apply]; rw [DFinsupp.sum]; rw [AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun k _ => ?_
    obtain rfl | h := eq_or_ne i (j + k) <;> simp [of_eq_of_ne, mul_mem, *]

中文:
定理 IsHomogeneous.subsemiringClosure
  结论: {s : 集合 A}
  证明: fun i x hx => by
  induction hx using Subsemiring.closure_induction generalizing i with
| mem _ hx => exact Subsemiring.subset_closure h i hx
  | zero => simp
  | one =>
    rw [decompose_one]; rw [one_def]
    obtain rfl | h := eq_or_ne i 0 <;> simp [of_eq_of_ne, *]
  | add _ _ _ _ h₁ h₂ => simpa using add_mem (h₁ i) (h₂ i)
  | mul x y _ _ h₁ h₂ =>
    classical
    rw [decompose_mul]; rw [DirectSum.mul_eq_dfinsuppSum]
    rw [DFinsupp.sum_apply]; rw [DFinsupp.sum]; rw [AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun j _ => ?_
    rw [DFinsupp.sum_apply]; rw [DFinsupp.sum]; rw [AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun k _ => ?_
    obtain rfl | h := eq_or_ne i (j + k) <;> simp [of_eq_of_ne, mul_mem, *]

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.coe_finsetSum, DFinsupp, DFinsupp.sum, DFinsupp.sum_apply, DirectSum, DirectSum.mul_eq_dfinsuppSum, Subsemiring, Subsemiring.closure_induction, Subsemiring.subset_closure, add_mem, classical, closure_induction, coe_finsetSum, decompose_mul, decompose_one, eq_or_ne, generalizing, mul_eq_dfinsuppSum, of_eq_of_ne
-/
theorem IsHomogeneous.subsemiringClosure {s : Set A}
    (h : forall (i : ι) ⦃x : A⦄, x in s -> (decompose 𝒜 x i : A) in s) :
    IsHomogeneous 𝒜 (Subsemiring.closure s) := fun i x hx => by
  induction hx using Subsemiring.closure_induction generalizing i with
| mem _ hx => exact Subsemiring.subset_closure h i hx
  | zero => simp
  | one =>
    rw [decompose_one]; rw [one_def]
    obtain rfl | h := eq_or_ne i 0 <;> simp [of_eq_of_ne, *]
  | add _ _ _ _ h₁ h₂ => simpa using add_mem (h₁ i) (h₂ i)
  | mul x y _ _ h₁ h₂ =>
    classical
    rw [decompose_mul]; rw [DirectSum.mul_eq_dfinsuppSum]
    rw [DFinsupp.sum_apply]; rw [DFinsupp.sum]; rw [AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun j _ => ?_
    rw [DFinsupp.sum_apply]; rw [DFinsupp.sum]; rw [AddSubmonoidClass.coe_finsetSum]
    refine sum_mem fun k _ => ?_
    obtain rfl | h := eq_or_ne i (j + k) <;> simp [of_eq_of_ne, mul_mem, *]

/--
theorem `IsHomogeneous.subsemiringClosure_of_isHomogeneousElem` / 定理 `IsHomogeneous.subsemiringClosure_of_isHomogeneousElem`

English:
theorem IsHomogeneous.subsemiringClosure_of_isHomogeneousElem
  statement: {s : Set A}
  proof: by
  rw [← Subsemiring.closure_insert_zero s]
  refine IsHomogeneous.subsemiringClosure fun i x hx => ?_
  obtain rfl | hx := mem_insert_iff.mp hx
  · simp
  · obtain ⟨j, hj⟩ := h x hx
    obtain rfl | h := eq_or_ne i j <;> simp [decompose_of_mem _ hj, of_eq_of_ne, *]

中文:
定理 IsHomogeneous.subsemiringClosure_of_isHomogeneousElem
  结论: {s : 集合 A}
  证明: by
  rw [← Subsemiring.closure_insert_zero s]
  refine IsHomogeneous.subsemiringClosure fun i x hx => ?_
  obtain rfl | hx := mem_insert_iff.mp hx
  · simp
  · obtain ⟨j, hj⟩ := h x hx
    obtain rfl | h := eq_or_ne i j <;> simp [decompose_of_mem _ hj, of_eq_of_ne, *]

Depends on / 依赖: IsHomogeneous, IsHomogeneous.subsemiringClosure, Subsemiring, Subsemiring.closure_insert_zero, closure_insert_zero, decompose_of_mem, eq_or_ne, mem_insert_iff, mem_insert_iff.mp, of_eq_of_ne, subsemiringClosure
-/
theorem IsHomogeneous.subsemiringClosure_of_isHomogeneousElem {s : Set A}
    (h : forall x in s, IsHomogeneousElem 𝒜 x) :
    IsHomogeneous 𝒜 (Subsemiring.closure s) := by
  rw [← Subsemiring.closure_insert_zero s]
  refine IsHomogeneous.subsemiringClosure fun i x hx => ?_
  obtain rfl | hx := mem_insert_iff.mp hx
  · simp
  · obtain ⟨j, hj⟩ := h x hx
    obtain rfl | h := eq_or_ne i j <;> simp [decompose_of_mem _ hj, of_eq_of_ne, *]

end HomogeneousDef

section HomogeneousCore

/--
Definition of `Subsemiring.homogeneousCore` / `Subsemiring.homogeneousCore` 的定义

English:
definition Subsemiring.homogeneousCore
  signature: : HomogeneousSubsemiring 𝒜 where
  body: Subsemiring.closure ((↑) '' (((↑) : Subtype (IsHomogeneousElem 𝒜) -> A) ⁻¹' R))
  is_homogeneous' := IsHomogeneous.subsemiringClosure_of_isHomogeneousElem fun x => by
    rintro ⟨x, _, rfl⟩; exact x.2

中文:
定义 子半环.homogeneousCore
  签名: : 齐次子半环 𝒜 where
  定义体: Subsemiring.closure ((↑) '' (((↑) : Subtype (IsHomogeneousElem 𝒜) -> A) ⁻¹' R))
  is_homogeneous' := IsHomogeneous.subsemiringClosure_of_isHomogeneousElem fun x => by
    rintro ⟨x, _, rfl⟩; exact x.2

Depends on / 依赖: IsHomogeneousElem, Subsemiring, Subsemiring.closure, Subtype, closure
-/
def Subsemiring.homogeneousCore : HomogeneousSubsemiring 𝒜 where
  __ := Subsemiring.closure ((↑) '' (((↑) : Subtype (IsHomogeneousElem 𝒜) -> A) ⁻¹' R))
  is_homogeneous' := IsHomogeneous.subsemiringClosure_of_isHomogeneousElem fun x => by
    rintro ⟨x, _, rfl⟩; exact x.2

/--
theorem `Subsemiring.homogeneousCore_mono` / 定理 `Subsemiring.homogeneousCore_mono`

English:
theorem Subsemiring.homogeneousCore_mono
  statement: Monotone (Subsemiring.homogeneousCore 𝒜)
  proof: fun _ _ h => Subsemiring.closure_mono Set.image_mono fun _ => @h _

中文:
定理 子半环.homogeneousCore_mono
  结论: 递增 (子半环.homogeneousCore 𝒜)
  证明: fun _ _ h => Subsemiring.closure_mono Set.image_mono fun _ => @h _

Depends on / 依赖: CharZero, Set.image_mono, Subsemiring, Subsemiring.closure_mono, closure_mono, image_mono, return, toOption, trySynthInstanceQ, with_reducible
-/
theorem Subsemiring.homogeneousCore_mono : Monotone (Subsemiring.homogeneousCore 𝒜) :=
fun _ _ h => Subsemiring.closure_mono Set.image_mono fun _ => @h _

/--
theorem `Subsemiring.toSubsemiring_homogeneousCore_le` / 定理 `Subsemiring.toSubsemiring_homogeneousCore_le`

English:
theorem Subsemiring.toSubsemiring_homogeneousCore_le
  statement: (R.homogeneousCore 𝒜).toSubsemiring <= R
  proof: Subsemiring.closure_le.2 image_preimage_subset _ _

中文:
定理 子半环.toSubsemiring_homogeneousCore_le
  结论: (R.homogeneousCore 𝒜).toSubsemiring <= R
  证明: Subsemiring.closure_le.2 image_preimage_subset _ _

Depends on / 依赖: Subsemiring, Subsemiring.closure_le, closure_le, image_preimage_subset
-/
theorem Subsemiring.toSubsemiring_homogeneousCore_le : (R.homogeneousCore 𝒜).toSubsemiring <= R :=
Subsemiring.closure_le.2 image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousSubsemiringDefs

/--
theorem `Subsemiring.isHomogeneous_iff_forall_subset` / 定理 `Subsemiring.isHomogeneous_iff_forall_subset`

English:
theorem Subsemiring.isHomogeneous_iff_forall_subset
  proof: Iff.rfl

中文:
定理 子半环.isHomogeneous_iff_对任意_subset
  证明: Iff.rfl

Depends on / 依赖: CharZero, Iff.rfl, return, toOption, trySynthInstanceQ, with_reducible
-/
theorem Subsemiring.isHomogeneous_iff_forall_subset :
    SetLike.IsHomogeneous 𝒜 R ↔ forall i, (R : Set A) subseteq GradedRing.proj 𝒜 i ⁻¹' (R : Set A) :=
  Iff.rfl

/--
theorem `Subsemiring.isHomogeneous_iff_subset_iInter` / 定理 `Subsemiring.isHomogeneous_iff_subset_iInter`

English:
theorem Subsemiring.isHomogeneous_iff_subset_iInter
  proof: subset_iInter_iff.symm

中文:
定理 子半环.isHomogeneous_iff_subset_i整数er
  证明: subset_iInter_iff.symm

Depends on / 依赖: subset_iInter_iff, subset_iInter_iff.symm
-/
theorem Subsemiring.isHomogeneous_iff_subset_iInter :
    SetLike.IsHomogeneous 𝒜 R ↔ (R : Set A) subseteq ⋂ i, GradedRing.proj 𝒜 i ⁻¹' R :=
  subset_iInter_iff.symm

end IsHomogeneousSubsemiringDefs
