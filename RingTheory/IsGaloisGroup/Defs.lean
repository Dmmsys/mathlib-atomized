/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Invariant.Defs

/-!
# Predicate for Galois Groups

Given an action of a group `G` on an extension of fields `L/K`, we introduce a predicate
`IsGaloisGroup G K L` saying that `G` acts faithfully on `L` with fixed field `K`. In particular,
we do not assume that `L` is an algebraic extension of `K`.

## Implementation notes

We actually define `IsGaloisGroup G A B` for extensions of rings `B/A`, with the same definition
(faithful action on `B` with fixed ring `A`). This definition turns out to axiomatize a common
setup in algebraic number theory where a Galois group `Gal(L/K)` acts on an extension of subrings
`B/A` (e.g., rings of integers). In particular, there are theorems in algebraic number theory that
naturally assume `[IsGaloisGroup G A B]` and whose statements would otherwise require assuming
`(K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]` (along with predicates relating
`K` and `L` to the rings `A` and `B`) despite `K` and `L` not appearing in the conclusion.

Unfortunately, this definition of `IsGaloisGroup G A B` for extensions of rings `B/A` is
nonstandard and clashes with other notions such as the étale fundamental group. In particular, if
`G` is finite and `A` is integrally closed, then `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`
(see `IsGaloisGroup.iff_isFractionRing`), rather than `B/A` being étale for instance.

But in the absence of a more suitable name, the utility of the predicate `IsGaloisGroup G A B` for
extensions of rings `B/A` seems to outweigh these terminological issues.
-/

@[expose] public section

assert_not_exists IsFractionRing

variable (G A A' B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

/--
Definition of `IsGaloisGroup` / `IsGaloisGroup` 的定义

English:
class IsGaloisGroup
  parameters: where
  axioms and operations (3):
    - faithful : FaithfulSMul G B
    - commutes : SMulCommClass G A B
    - isInvariant : Algebra.IsInvariant A B G

中文:
类 是Galois群
  参数: where
  公理与运算 (3 个):
    - faithful : 忠实标量乘法 G B
    - commutes : 标量交换类 G A B
    - isInvariant : 代数.是不变 A B G
-/
class IsGaloisGroup where
  faithful : FaithfulSMul G B
  commutes : SMulCommClass G A B
  isInvariant : Algebra.IsInvariant A B G

namespace IsGaloisGroup

variable {G A B} in
/--
theorem `of_mulEquiv` / 定理 `of_mulEquiv`

English:
theorem of_mulEquiv
  statement: [hG : IsGaloisGroup G A B] {H : Type*} [Group H]
  proof: ⟨fun h => e.injective hG.faithful.eq_of_smul_eq_smul by simpa only [he]⟩
  commutes := ⟨fun x a b => by simpa [he] using hG.commutes.smul_comm (e x) a b⟩
  isInvariant := ⟨fun b h =>
    have he' : forall (g : G) (x : B), e.symm g • x = g • x := fun g x => by simp [← he]
    hG.isInvariant.isInvariant b (fun g => by simpa [he'] using h (e.symm g))⟩

中文:
定理 of_mulEquiv
  结论: [hG : 是Galois群 G A B] {H : 类型} [群 H]
  证明: ⟨fun h => e.injective hG.faithful.eq_of_smul_eq_smul by simpa only [he]⟩
  commutes := ⟨fun x a b => by simpa [he] using hG.commutes.smul_comm (e x) a b⟩
  isInvariant := ⟨fun b h =>
    have he' : forall (g : G) (x : B), e.symm g • x = g • x := fun g x => by simp [← he]
    hG.isInvariant.isInvariant b (fun g => by simpa [he'] using h (e.symm g))⟩

Depends on / 依赖: e.injective, eq_of_smul_eq_smul, faithful, hG.faithful.eq_of_smul_eq_smul, injective
-/
theorem of_mulEquiv [hG : IsGaloisGroup G A B] {H : Type*} [Group H]
    [MulSemiringAction H B] (e : H ≃* G) (he : forall h (x : B), (e h) • x = h • x) :
    IsGaloisGroup H A B where
faithful := ⟨fun h => e.injective hG.faithful.eq_of_smul_eq_smul by simpa only [he]⟩
  commutes := ⟨fun x a b => by simpa [he] using hG.commutes.smul_comm (e x) a b⟩
  isInvariant := ⟨fun b h =>
    have he' : forall (g : G) (x : B), e.symm g • x = g • x := fun g x => by simp [← he]
    hG.isInvariant.isInvariant b (fun g => by simpa [he'] using h (e.symm g))⟩

variable {G A B} in
/--
theorem `iff_of_mulEquiv` / 定理 `iff_of_mulEquiv`

English:
theorem iff_of_mulEquiv
  statement: {H : Type*} [Group H] [MulSemiringAction H B]
  proof: by
  refine ⟨fun h => h.of_mulEquiv e.symm fun g x => ?_, fun h => h.of_mulEquiv e he⟩
  rw [← he]; rw [e.apply_symm_apply]

中文:
定理 iff_of_mulEquiv
  结论: {H : 类型} [群 H] [MulSemiring作用 H B]
  证明: by
  refine ⟨fun h => h.of_mulEquiv e.symm fun g x => ?_, fun h => h.of_mulEquiv e he⟩
  rw [← he]; rw [e.apply_symm_apply]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply, e.symm, h.of_mulEquiv, of_mulEquiv
-/
theorem iff_of_mulEquiv {H : Type*} [Group H] [MulSemiringAction H B]
    (e : H ≃* G) (he : forall h (x : B), e h • x = h • x) :
    IsGaloisGroup H A B ↔ IsGaloisGroup G A B := by
  refine ⟨fun h => h.of_mulEquiv e.symm fun g x => ?_, fun h => h.of_mulEquiv e he⟩
  rw [← he]; rw [e.apply_symm_apply]

variable {G A B} in
@[simp]
/--
theorem `top_iff` / 定理 `top_iff`

English:
theorem top_iff
  statement: IsGaloisGroup (⊤ : Subgroup G) A B ↔ IsGaloisGroup G A B
  proof: iff_of_mulEquiv Subgroup.topEquiv fun _ _ => rfl

中文:
定理 top_iff
  结论: 是Galois群 (⊤ : 子群 G) A B ↔ 是Galois群 G A B
  证明: iff_of_mulEquiv Subgroup.topEquiv fun _ _ => rfl

Depends on / 依赖: Subgroup, Subgroup.topEquiv, iff_of_mulEquiv, topEquiv
-/
theorem top_iff : IsGaloisGroup (⊤ : Subgroup G) A B ↔ IsGaloisGroup G A B :=
  iff_of_mulEquiv Subgroup.topEquiv fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsGaloisGroup
  signature: G A B] : IsGaloisGroup (⊤
  body: IsGaloisGroup.top_iff.mpr ‹_›

中文:
实例 [是Galois群
  签名: G A B] : 是Galois群 (⊤
  定义体: IsGaloisGroup.top_iff.mpr ‹_›

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.top_iff.mpr, top_iff
-/
instance [IsGaloisGroup G A B] : IsGaloisGroup (⊤ : Subgroup G) A B :=
  IsGaloisGroup.top_iff.mpr ‹_›

/--
theorem `of_algEquiv` / 定理 `of_algEquiv`

English:
theorem of_algEquiv
  statement: [hG : IsGaloisGroup G A B] (B' : Type*) [Semiring B']
  proof: ⟨fun h => hG.faithful.eq_of_smul_eq_smul fun b => by simpa [← he] using h (e b)⟩
  commutes := ⟨fun g a b' => by
    have h' {x'} : e.symm (g • x') = g • e.symm x' := by
      apply e.injective
      simp [he]
    apply e.symm.injective
    simpa [h', map_smul] using hG.commutes.smul_comm g a (e.symm b')⟩
  isInvariant := ⟨fun x' hx' => by
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant (e.symm x') (fun g => by
      apply e.injective
      simp [he, hx'])
    exact ⟨a, by rw [← e.commutes, ha, AlgEquiv.apply_symm_apply]⟩⟩

中文:
定理 of_algEquiv
  结论: [hG : 是Galois群 G A B] (B' : 类型) [半环 B']
  证明: ⟨fun h => hG.faithful.eq_of_smul_eq_smul fun b => by simpa [← he] using h (e b)⟩
  commutes := ⟨fun g a b' => by
    have h' {x'} : e.symm (g • x') = g • e.symm x' := by
      apply e.injective
      simp [he]
    apply e.symm.injective
    simpa [h', map_smul] using hG.commutes.smul_comm g a (e.symm b')⟩
  isInvariant := ⟨fun x' hx' => by
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant (e.symm x') (fun g => by
      apply e.injective
      simp [he, hx'])
    exact ⟨a, by rw [← e.commutes, ha, AlgEquiv.apply_symm_apply]⟩⟩

Depends on / 依赖: eq_of_smul_eq_smul, faithful, hG.faithful.eq_of_smul_eq_smul
-/
theorem of_algEquiv [hG : IsGaloisGroup G A B] (B' : Type*) [Semiring B']
    [Algebra A B'] [MulSemiringAction G B'] (e : B ≃ₐ[A] B')
    (he : forall (g : G) (x : B), e (g • x) = g • (e x)) :
    IsGaloisGroup G A B' where
  faithful := ⟨fun h => hG.faithful.eq_of_smul_eq_smul fun b => by simpa [← he] using h (e b)⟩
  commutes := ⟨fun g a b' => by
    have h' {x'} : e.symm (g • x') = g • e.symm x' := by
      apply e.injective
      simp [he]
    apply e.symm.injective
    simpa [h', map_smul] using hG.commutes.smul_comm g a (e.symm b')⟩
  isInvariant := ⟨fun x' hx' => by
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant (e.symm x') (fun g => by
      apply e.injective
      simp [he, hx'])
    exact ⟨a, by rw [← e.commutes, ha, AlgEquiv.apply_symm_apply]⟩⟩

/--
theorem `of_ringHom_surjective` / 定理 `of_ringHom_surjective`

English:
theorem of_ringHom_surjective
  statement: [hG : IsGaloisGroup G A B] [CommSemiring A']
  proof: hG.faithful
  commutes := ⟨by
    intro g a' b
    obtain ⟨a, rfl⟩ : exists a, e a = a' := he' a'
    rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [he]; rw [← Algebra.smul_def]; rw [← Algebra.smul_def]
    exact hG.commutes.smul_comm g a b⟩
  isInvariant := ⟨by
    intro b h
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant b h
    exact ⟨e a, by rw [he, ha]⟩⟩

中文:
定理 of_ringHom_surjective
  结论: [hG : 是Galois群 G A B] [交换半环 A']
  证明: hG.faithful
  commutes := ⟨by
    intro g a' b
    obtain ⟨a, rfl⟩ : exists a, e a = a' := he' a'
    rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [he]; rw [← Algebra.smul_def]; rw [← Algebra.smul_def]
    exact hG.commutes.smul_comm g a b⟩
  isInvariant := ⟨by
    intro b h
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant b h
    exact ⟨e a, by rw [he, ha]⟩⟩

Depends on / 依赖: faithful, hG.faithful
-/
theorem of_ringHom_surjective [hG : IsGaloisGroup G A B] [CommSemiring A']
    [Algebra A' B] (e : A ->+* A') (he : forall a, algebraMap A' B (e a) = algebraMap A B a)
    (he' : Function.Surjective e) : IsGaloisGroup G A' B where
  faithful := hG.faithful
  commutes := ⟨by
    intro g a' b
    obtain ⟨a, rfl⟩ : exists a, e a = a' := he' a'
    rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [he]; rw [← Algebra.smul_def]; rw [← Algebra.smul_def]
    exact hG.commutes.smul_comm g a b⟩
  isInvariant := ⟨by
    intro b h
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant b h
    exact ⟨e a, by rw [he, ha]⟩⟩

/--
theorem `of_ringEquiv` / 定理 `of_ringEquiv`

English:
theorem of_ringEquiv
  statement: [hG : IsGaloisGroup G A B] [CommSemiring A'] [Algebra A' B]
  proof: .of_ringHom_surjective G A A' B e he e.surjective

中文:
定理 of_ringEquiv
  结论: [hG : 是Galois群 G A B] [交换半环 A'] [代数 A' B]
  证明: .of_ringHom_surjective G A A' B e he e.surjective

Depends on / 依赖: e.surjective, of_ringHom_surjective, surjective
-/
theorem of_ringEquiv [hG : IsGaloisGroup G A B] [CommSemiring A'] [Algebra A' B]
    (e : A ≃+* A') (he : forall a, algebraMap A' B (e a) = algebraMap A B a) :
    IsGaloisGroup G A' B :=
  .of_ringHom_surjective G A A' B e he e.surjective

attribute [instance low] IsGaloisGroup.commutes IsGaloisGroup.isInvariant

variable [hA : IsGaloisGroup G A B] [FaithfulSMul A B]

/-- If `B/A` is Galois with Galois group `G`, then `A` is isomorphic to the subring of elements of
`B` fixed by `G`. -/
@[simps apply_coe]
/--
Definition of `ringEquivFixedPoints` / `ringEquivFixedPoints` 的定义

English:
definition ringEquivFixedPoints
  signature: :
  body: ⟨algebraMap A B x, fun _ => by rw [smul_algebraMap]⟩
  invFun x := (hA.isInvariant.isInvariant x x.prop).choose
  map_mul' _ _ := by simp [Subtype.ext_iff]
  map_add' _ _ := by simp [Subtype.ext_iff]
  left_inv _ := by simp
  right_inv x := by simpa [Subtype.ext_iff] using (hA.isInvariant.isInvariant x x.prop).choose_spec

@[simp]

中文:
定义 ringEquivFixedPoints
  签名: :
  定义体: ⟨algebraMap A B x, fun _ => by rw [smul_algebraMap]⟩
  invFun x := (hA.isInvariant.isInvariant x x.prop).choose
  map_mul' _ _ := by simp [Subtype.ext_iff]
  map_add' _ _ := by simp [Subtype.ext_iff]
  left_inv _ := by simp
  right_inv x := by simpa [Subtype.ext_iff] using (hA.isInvariant.isInvariant x x.prop).choose_spec

@[simp]

Depends on / 依赖: algebraMap, smul_algebraMap
-/
noncomputable def ringEquivFixedPoints :
    A ≃+* FixedPoints.subsemiring B G where
  toFun x := ⟨algebraMap A B x, fun _ => by rw [smul_algebraMap]⟩
  invFun x := (hA.isInvariant.isInvariant x x.prop).choose
  map_mul' _ _ := by simp [Subtype.ext_iff]
  map_add' _ _ := by simp [Subtype.ext_iff]
  left_inv _ := by simp
  right_inv x := by simpa [Subtype.ext_iff] using (hA.isInvariant.isInvariant x x.prop).choose_spec

@[simp]
/--
theorem `algebraMap_ringEquivFixedPoints_symm_apply` / 定理 `algebraMap_ringEquivFixedPoints_symm_apply`

English:
theorem algebraMap_ringEquivFixedPoints_symm_apply
  given: (x : FixedPoints.subsemiring B G)
  proof: (hA.isInvariant.isInvariant x x.prop).choose_spec

中文:
定理 algebraMap_ringEquivFixedPoints_symm_apply
  条件: (x : FixedPoints.subsemiring B G)
  证明: (hA.isInvariant.isInvariant x x.prop).choose_spec

Depends on / 依赖: choose_spec, hA.isInvariant.isInvariant, isInvariant, x.prop
-/
theorem algebraMap_ringEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) :
    algebraMap A B ((ringEquivFixedPoints G A B).symm x) = x :=
 (hA.isInvariant.isInvariant x x.prop).choose_spec

variable [CommSemiring A'] [Algebra A' B] [FaithfulSMul A' B] [hA' : IsGaloisGroup G A' B]

/--
Definition of `ringEquiv` / `ringEquiv` 的定义

English:
definition ringEquiv
  signature: : A ≃+* A'
  body: (ringEquivFixedPoints G A B).trans (ringEquivFixedPoints G A' B).symm

@[simp]

中文:
定义 ringEquiv
  签名: : A ≃+* A'
  定义体: (ringEquivFixedPoints G A B).trans (ringEquivFixedPoints G A' B).symm

@[simp]

Depends on / 依赖: ringEquivFixedPoints
-/
noncomputable def ringEquiv : A ≃+* A' :=
  (ringEquivFixedPoints G A B).trans (ringEquivFixedPoints G A' B).symm

@[simp]
/--
theorem `algebraMap_ringEquiv_apply` / 定理 `algebraMap_ringEquiv_apply`

English:
theorem algebraMap_ringEquiv_apply
  given: (x : A)
  proof: by
  simp [ringEquiv]

@[simp]

中文:
定理 algebraMap_ringEquiv_apply
  条件: (x : A)
  证明: by
  simp [ringEquiv]

@[simp]

Depends on / 依赖: ringEquiv
-/
theorem algebraMap_ringEquiv_apply (x : A) :
    algebraMap A' B (IsGaloisGroup.ringEquiv G A A' B x) = algebraMap A B x := by
  simp [ringEquiv]

@[simp]
/--
theorem `algebraMap_ringEquiv_symm_apply` / 定理 `algebraMap_ringEquiv_symm_apply`

English:
theorem algebraMap_ringEquiv_symm_apply
  given: (x : A')
  proof: by
  simp [ringEquiv]

中文:
定理 algebraMap_ringEquiv_symm_apply
  条件: (x : A')
  证明: by
  simp [ringEquiv]

Depends on / 依赖: ringEquiv
-/
theorem algebraMap_ringEquiv_symm_apply (x : A') :
    algebraMap A B ((IsGaloisGroup.ringEquiv G A A' B).symm x) = algebraMap A' B x := by
  simp [ringEquiv]

end IsGaloisGroup
