/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Internal grading of an `AddMonoidAlgebra`

In this file, we show that an `AddMonoidAlgebra` has an internal direct sum structure.

## Main results

* `AddMonoidAlgebra.gradeBy R f i`: the `i`th grade of an `R[M]` given by the
  degree function `f`.
* `AddMonoidAlgebra.grade R i`: the `i`th grade of an `R[M]` when the degree
  function is the identity.
* `AddMonoidAlgebra.gradeBy.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.gradeBy`.
* `AddMonoidAlgebra.grade.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.grade`.
* `AddMonoidAlgebra.gradeBy.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.gradeBy` defines an internal graded structure.
* `AddMonoidAlgebra.grade.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.grade` defines an internal graded structure when the degree function
  is the identity.
-/

@[expose] public section


noncomputable section

namespace AddMonoidAlgebra

variable {M : Type*} {ι : Type*} {R : Type*}

section

variable (R) [CommSemiring R]

/--
Definition of `gradeBy` / `gradeBy` 的定义

English:
abbreviation gradeBy
  signature: (f : M -> ι) (i : ι)
  body: { a | forall m, m in a.coeff.support -> f m = i }
  zero_mem' m h := by cases h
  add_mem' {a b} ha hb m h := by
    classical exact (Finset.mem_union.mp (Finsupp.support_add h)).elim (ha m) (hb m)
  smul_mem' _ _ h := Set.Subset.trans Finsupp.support_smul h

中文:
缩写 gradeBy
  签名: (f : M -> ι) (i : ι)
  定义体: { a | forall m, m in a.coeff.support -> f m = i }
  zero_mem' m h := by cases h
  add_mem' {a b} ha hb m h := by
    classical exact (Finset.mem_union.mp (Finsupp.support_add h)).elim (ha m) (hb m)
  smul_mem' _ _ h := Set.Subset.trans Finsupp.support_smul h

Depends on / 依赖: a.coeff.support, support
-/
abbrev gradeBy (f : M -> ι) (i : ι) : Submodule R R[M] where
  carrier := { a | forall m, m in a.coeff.support -> f m = i }
  zero_mem' m h := by cases h
  add_mem' {a b} ha hb m h := by
    classical exact (Finset.mem_union.mp (Finsupp.support_add h)).elim (ha m) (hb m)
  smul_mem' _ _ h := Set.Subset.trans Finsupp.support_smul h

/--
Definition of `grade` / `grade` 的定义

English:
abbreviation grade
  signature: (m : M)
  body: gradeBy R id m

中文:
缩写 grade
  签名: (m : M)
  定义体: gradeBy R id m

Depends on / 依赖: gradeBy
-/
abbrev grade (m : M) : Submodule R R[M] :=
  gradeBy R id m

/--
theorem `gradeBy_id` / 定理 `gradeBy_id`

English:
theorem gradeBy_id
  statement: gradeBy R (id : M -> M) = grade R
  proof: rfl

中文:
定理 gradeBy_id
  结论: gradeBy R (id : M -> M) = grade R
  证明: rfl
-/
theorem gradeBy_id : gradeBy R (id : M -> M) = grade R := rfl

/--
theorem `mem_gradeBy_iff` / 定理 `mem_gradeBy_iff`

English:
theorem mem_gradeBy_iff
  given: (f : M -> ι) (i : ι) (a : R[M])
  proof: by rfl

中文:
定理 mem_gradeBy_iff
  条件: (f : M -> ι) (i : ι) (a : R[M])
  证明: by rfl
-/
theorem mem_gradeBy_iff (f : M -> ι) (i : ι) (a : R[M]) :
    a in gradeBy R f i ↔ (a.coeff.support : Set M) subseteq f ⁻¹' {i} := by rfl

/--
theorem `mem_grade_iff` / 定理 `mem_grade_iff`

English:
theorem mem_grade_iff
  given: (m : M) (a : R[M])
  statement: a in grade R m ↔ a.coeff.support subseteq {m}
  proof: by
  rw [← Finset.coe_subset]; rw [Finset.coe_singleton]
  rfl

中文:
定理 mem_grade_iff
  条件: (m : M) (a : R[M])
  结论: a in grade R m ↔ a.coeff.support subseteq {m}
  证明: by
  rw [← Finset.coe_subset]; rw [Finset.coe_singleton]
  rfl

Depends on / 依赖: Finset, Finset.coe_singleton, Finset.coe_subset, coe_singleton, coe_subset
-/
theorem mem_grade_iff (m : M) (a : R[M]) : a in grade R m ↔ a.coeff.support subseteq {m} := by
  rw [← Finset.coe_subset]; rw [Finset.coe_singleton]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mem_grade_iff'` / 定理 `mem_grade_iff'`

English:
theorem mem_grade_iff'
  given: (m : M) (a : R[M])
  proof: by
  rw [mem_grade_iff]; rw [Finsupp.support_subset_singleton']; simp [← coeff_inj, eq_comm]

中文:
定理 mem_grade_iff'
  条件: (m : M) (a : R[M])
  证明: by
  rw [mem_grade_iff]; rw [Finsupp.support_subset_singleton']; simp [← coeff_inj, eq_comm]

Depends on / 依赖: Finsupp, Finsupp.support_subset_singleton, coeff_inj, eq_comm, mem_grade_iff, support_subset_singleton
-/
theorem mem_grade_iff' (m : M) (a : R[M]) :
    a in grade R m ↔ a in LinearMap.range (lsingle (R := R) m) := by
  rw [mem_grade_iff]; rw [Finsupp.support_subset_singleton']; simp [← coeff_inj, eq_comm]

/--
theorem `grade_eq_lsingle_range` / 定理 `grade_eq_lsingle_range`

English:
theorem grade_eq_lsingle_range
  given: (m : M)
  statement: grade R m = LinearMap.range (lsingle m)
  proof: Submodule.ext (mem_grade_iff' R m)

中文:
定理 grade_eq_lsingle_range
  条件: (m : M)
  结论: grade R m = 线性映射.range (lsingle m)
  证明: Submodule.ext (mem_grade_iff' R m)

Depends on / 依赖: Submodule, Submodule.ext, mem_grade_iff
-/
theorem grade_eq_lsingle_range (m : M) : grade R m = LinearMap.range (lsingle m) :=
  Submodule.ext (mem_grade_iff' R m)

/--
theorem `single_mem_gradeBy` / 定理 `single_mem_gradeBy`

English:
theorem single_mem_gradeBy
  given: {R} [CommSemiring R] (f : M -> ι) (m : M) (r : R)
  proof: by
  intro x hx
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]

中文:
定理 single_mem_gradeBy
  条件: {R} [交换半环 R] (f : M -> ι) (m : M) (r : R)
  证明: by
  intro x hx
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]

Depends on / 依赖: Finset, Finset.mem_singleton.mp, Finsupp, Finsupp.support_single_subset, mem_singleton, support_single_subset
-/
theorem single_mem_gradeBy {R} [CommSemiring R] (f : M -> ι) (m : M) (r : R) :
    single m r in gradeBy R f (f m) := by
  intro x hx
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]

/--
theorem `single_mem_grade` / 定理 `single_mem_grade`

English:
theorem single_mem_grade
  given: {R} [CommSemiring R] (i : M) (r : R)
  proof: single_mem_gradeBy _ _ _

中文:
定理 single_mem_grade
  条件: {R} [交换半环 R] (i : M) (r : R)
  证明: single_mem_gradeBy _ _ _

Depends on / 依赖: single_mem_gradeBy
-/
theorem single_mem_grade {R} [CommSemiring R] (i : M) (r : R) :
    single i r in grade R i :=
  single_mem_gradeBy _ _ _

end

open DirectSum

/--
Instance `gradeBy.gradedMonoid` / 实例 `gradeBy.gradedMonoid`

English:
instance gradeBy.gradedMonoid
  signature: [AddMonoid M] [AddMonoid ι] [CommSemiring R] (f : M ->+ ι)
  body: by
    rw [one_def] at h
obtain rfl : m = 0 := Finset.mem_singleton.1 Finsupp.support_single_subset h
    apply map_zero
  mul_mem i j a b ha hb c hc := by
    classical
    obtain ⟨ma, hma, mb, hmb, rfl⟩ : exists y in a.coeff.support, exists z in b.coeff.support, y + z = c :=
Finset.mem_add.1 support_coeff_mul_subset a b hc
    rw [map_add]; rw [ha ma hma]; rw [hb mb hmb]

中文:
实例 gradeBy.gradedMonoid
  签名: [加法幺半群 M] [加法幺半群 ι] [交换半环 R] (f : M ->+ ι)
  定义体: by
    rw [one_def] at h
obtain rfl : m = 0 := Finset.mem_singleton.1 Finsupp.support_single_subset h
    apply map_zero
  mul_mem i j a b ha hb c hc := by
    classical
    obtain ⟨ma, hma, mb, hmb, rfl⟩ : exists y in a.coeff.support, exists z in b.coeff.support, y + z = c :=
Finset.mem_add.1 support_coeff_mul_subset a b hc
    rw [map_add]; rw [ha ma hma]; rw [hb mb hmb]

Depends on / 依赖: Finset, Finset.mem_add, Finset.mem_singleton, Finsupp, Finsupp.support_single_subset, a.coeff.support, b.coeff.support, classical, map_add, map_zero, mem_add, mem_singleton, mul_mem, one_def, support, support_coeff_mul_subset, support_single_subset
-/
instance gradeBy.gradedMonoid [AddMonoid M] [AddMonoid ι] [CommSemiring R] (f : M ->+ ι) :
    SetLike.GradedMonoid (gradeBy R f : ι -> Submodule R R[M]) where
  one_mem m h := by
    rw [one_def] at h
obtain rfl : m = 0 := Finset.mem_singleton.1 Finsupp.support_single_subset h
    apply map_zero
  mul_mem i j a b ha hb c hc := by
    classical
    obtain ⟨ma, hma, mb, hmb, rfl⟩ : exists y in a.coeff.support, exists z in b.coeff.support, y + z = c :=
Finset.mem_add.1 support_coeff_mul_subset a b hc
    rw [map_add]; rw [ha ma hma]; rw [hb mb hmb]

/--
Instance `grade.gradedMonoid` / 实例 `grade.gradedMonoid`

English:
instance grade.gradedMonoid
  signature: [AddMonoid M] [CommSemiring R]
  body: by
  apply gradeBy.gradedMonoid (AddMonoidHom.id _)

中文:
实例 grade.gradedMonoid
  签名: [加法幺半群 M] [交换半环 R]
  定义体: by
  apply gradeBy.gradedMonoid (AddMonoidHom.id _)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, gradeBy, gradeBy.gradedMonoid, gradedMonoid
-/
instance grade.gradedMonoid [AddMonoid M] [CommSemiring R] :
    SetLike.GradedMonoid (grade R : M -> Submodule R R[M]) := by
  apply gradeBy.gradedMonoid (AddMonoidHom.id _)

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M ->+ ι)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `decomposeAux` / `decomposeAux` 的定义

English:
definition decomposeAux
  signature: : R[M] ->ₐ[R] ⨁ i : ι, gradeBy R f i
  body: lift R _ M {
    toFun m := .of (fun i => gradeBy R f i) (f m.toAdd) ⟨single m.toAdd 1, single_mem_gradeBy _ _ _⟩
    map_one' := of_eq_of_gradedMonoid_eq (by congr 2 <;> simp)
    map_mul' i j := by
      simpa [toAdd_mul, of_mul_of, GradedMonoid.GMul.mul, single_mul_single, mul_one] using
DirectSum.of_eq_of_gradedMonoid_eq Sigma.subtype_ext (f.map_add _ _) rfl
  }

中文:
定义 decomposeAux
  签名: : R[M] ->ₐ[R] ⨁ i : ι, gradeBy R f i
  定义体: lift R _ M {
    toFun m := .of (fun i => gradeBy R f i) (f m.toAdd) ⟨single m.toAdd 1, single_mem_gradeBy _ _ _⟩
    map_one' := of_eq_of_gradedMonoid_eq (by congr 2 <;> simp)
    map_mul' i j := by
      simpa [toAdd_mul, of_mul_of, GradedMonoid.GMul.mul, single_mul_single, mul_one] using
DirectSum.of_eq_of_gradedMonoid_eq Sigma.subtype_ext (f.map_add _ _) rfl
  }

Depends on / 依赖: DirectSum, DirectSum.of_eq_of_gradedMonoid_eq, GradedMonoid, GradedMonoid.GMul.mul, Sigma.subtype_ext, f.map_add, gradeBy, m.toAdd, map_add, map_mul, map_one, mul_one, of_eq_of_gradedMonoid_eq, of_mul_of, single, single_mem_gradeBy, single_mul_single, subtype_ext, toAdd_mul
-/
def decomposeAux : R[M] ->ₐ[R] ⨁ i : ι, gradeBy R f i :=
  lift R _ M {
    toFun m := .of (fun i => gradeBy R f i) (f m.toAdd) ⟨single m.toAdd 1, single_mem_gradeBy _ _ _⟩
    map_one' := of_eq_of_gradedMonoid_eq (by congr 2 <;> simp)
    map_mul' i j := by
      simpa [toAdd_mul, of_mul_of, GradedMonoid.GMul.mul, single_mul_single, mul_one] using
DirectSum.of_eq_of_gradedMonoid_eq Sigma.subtype_ext (f.map_add _ _) rfl
  }

/--
theorem `decomposeAux_single` / 定理 `decomposeAux_single`

English:
theorem decomposeAux_single
  given: (m : M) (r : R)
  proof: by
  refine (lift_single _ _ _).trans ?_
  refine (DirectSum.of_smul R _ _ _).symm.trans ?_
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine Sigma.subtype_ext rfl ?_
  refine (smul_single' _ _ _).trans ?_
  rw [mul_one]
  rfl

中文:
定理 decomposeAux_single
  条件: (m : M) (r : R)
  证明: by
  refine (lift_single _ _ _).trans ?_
  refine (DirectSum.of_smul R _ _ _).symm.trans ?_
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine Sigma.subtype_ext rfl ?_
  refine (smul_single' _ _ _).trans ?_
  rw [mul_one]
  rfl

Depends on / 依赖: DirectSum, DirectSum.of_eq_of_gradedMonoid_eq, DirectSum.of_smul, Sigma.subtype_ext, lift_single, mul_one, of_eq_of_gradedMonoid_eq, of_smul, smul_single, subtype_ext, symm.trans
-/
theorem decomposeAux_single (m : M) (r : R) :
    decomposeAux f (single m r) =
      .of (fun i => gradeBy R f i) (f m) ⟨single m r, single_mem_gradeBy _ _ _⟩ := by
  refine (lift_single _ _ _).trans ?_
  refine (DirectSum.of_smul R _ _ _).symm.trans ?_
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine Sigma.subtype_ext rfl ?_
  refine (smul_single' _ _ _).trans ?_
  rw [mul_one]
  rfl

/--
theorem `decomposeAux_coe` / 定理 `decomposeAux_coe`

English:
theorem decomposeAux_coe
  given: {i : ι} (x : gradeBy R f i)
  proof: by
  classical
  obtain ⟨x, hx⟩ := x
  revert hx
  refine induction x ?_ ?_
  · intro hx
    symm
    exact map_zero _
  · intro m b y hmy hb ih hmby
    have : Disjoint (Finsupp.single m b).support y.coeff.support := by
      simpa only [Finsupp.support_single _ hb, Finset.disjoint_singleton_left]
    rw [mem_gradeBy_iff]; rw [coeff_add]; rw [coeff_single]; rw [Finsupp.support_add_eq this]; rw [Finset.coe_union]; rw [Set.union_subset_iff] at hmby
    obtain ⟨h1, h2⟩ := hmby
    have : f m = i := by
      rwa [Finsupp.support_single _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    simp only [map_add, decomposeAux_single f m]
    let ih' := ih h2
    dsimp at ih'
    rw [ih']; rw [← map_add]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    congr 2

中文:
定理 decomposeAux_coe
  条件: {i : ι} (x : gradeBy R f i)
  证明: by
  classical
  obtain ⟨x, hx⟩ := x
  revert hx
  refine induction x ?_ ?_
  · intro hx
    symm
    exact map_zero _
  · intro m b y hmy hb ih hmby
    have : Disjoint (Finsupp.single m b).support y.coeff.support := by
      simpa only [Finsupp.support_single _ hb, Finset.disjoint_singleton_left]
    rw [mem_gradeBy_iff]; rw [coeff_add]; rw [coeff_single]; rw [Finsupp.support_add_eq this]; rw [Finset.coe_union]; rw [Set.union_subset_iff] at hmby
    obtain ⟨h1, h2⟩ := hmby
    have : f m = i := by
      rwa [Finsupp.support_single _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    simp only [map_add, decomposeAux_single f m]
    let ih' := ih h2
    dsimp at ih'
    rw [ih']; rw [← map_add]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    congr 2

Depends on / 依赖: Disjoint, Finset, Finset.coe_union, Finset.disjoint_singleton_left, Finsupp, Finsupp.single, Finsupp.support_add_eq, Finsupp.support_single, Set.union_subset_iff, classical, coe_union, coeff_add, coeff_single, disjoint_singleton_left, map_zero, mem_gradeBy_iff, revert, single, support, support_add_eq
-/
theorem decomposeAux_coe {i : ι} (x : gradeBy R f i) :
    decomposeAux f ↑x = DirectSum.of (fun i => gradeBy R f i) i x := by
  classical
  obtain ⟨x, hx⟩ := x
  revert hx
  refine induction x ?_ ?_
  · intro hx
    symm
    exact map_zero _
  · intro m b y hmy hb ih hmby
    have : Disjoint (Finsupp.single m b).support y.coeff.support := by
      simpa only [Finsupp.support_single _ hb, Finset.disjoint_singleton_left]
    rw [mem_gradeBy_iff]; rw [coeff_add]; rw [coeff_single]; rw [Finsupp.support_add_eq this]; rw [Finset.coe_union]; rw [Set.union_subset_iff] at hmby
    obtain ⟨h1, h2⟩ := hmby
    have : f m = i := by
      rwa [Finsupp.support_single _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    simp only [map_add, decomposeAux_single f m]
    let ih' := ih h2
    dsimp at ih'
    rw [ih']; rw [← map_add]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    congr 2

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `gradeBy.gradedAlgebra` / 实例 `gradeBy.gradedAlgebra`

English:
instance gradeBy.gradedAlgebra
  signature: : GradedAlgebra (gradeBy R f)
  body: .ofAlgHom _ (decomposeAux f) (by ext; simp [decomposeAux_single]) by simp [decomposeAux_coe]

@[simp]

中文:
实例 gradeBy.gradedAlgebra
  签名: : 分次代数 (gradeBy R f)
  定义体: .ofAlgHom _ (decomposeAux f) (by ext; simp [decomposeAux_single]) by simp [decomposeAux_coe]

@[simp]

Depends on / 依赖: decomposeAux, decomposeAux_coe, decomposeAux_single, ofAlgHom
-/
instance gradeBy.gradedAlgebra : GradedAlgebra (gradeBy R f) :=
.ofAlgHom _ (decomposeAux f) (by ext; simp [decomposeAux_single]) by simp [decomposeAux_coe]

@[simp]
/--
theorem `decomposeAux_eq_decompose` / 定理 `decomposeAux_eq_decompose`

English:
theorem decomposeAux_eq_decompose
  proof: rfl

中文:
定理 decomposeAux_eq_decompose
  证明: rfl
-/
theorem decomposeAux_eq_decompose :
    ⇑(decomposeAux f : R[M] ->ₐ[R] ⨁ i : ι, gradeBy R f i) =
      DirectSum.decompose (gradeBy R f) :=
  rfl

/--
theorem `GradesBy.decompose_single` / 定理 `GradesBy.decompose_single`

English:
theorem GradesBy.decompose_single
  given: (m : M) (r : R)
  proof: decomposeAux_single _ _ _

中文:
定理 GradesBy.decompose_single
  条件: (m : M) (r : R)
  证明: decomposeAux_single _ _ _

Depends on / 依赖: decomposeAux_single
-/
theorem GradesBy.decompose_single (m : M) (r : R) :
    DirectSum.decompose (gradeBy R f) (single m r : R[M]) =
      .of (fun i => gradeBy R f i) (f m) ⟨single m r, single_mem_gradeBy _ _ _⟩ :=
  decomposeAux_single _ _ _

/--
Instance `grade.gradedAlgebra` / 实例 `grade.gradedAlgebra`

English:
instance grade.gradedAlgebra
  signature: : GradedAlgebra (grade R : ι -> Submodule _ _)
  body: inferInstanceAs GradedAlgebra (gradeBy R (AddMonoidHom.id ι))

中文:
实例 grade.gradedAlgebra
  签名: : 分次代数 (grade R : ι -> 子模 _ _)
  定义体: inferInstanceAs GradedAlgebra (gradeBy R (AddMonoidHom.id ι))

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, GradedAlgebra, gradeBy
-/
instance grade.gradedAlgebra : GradedAlgebra (grade R : ι -> Submodule _ _) :=
inferInstanceAs GradedAlgebra (gradeBy R (AddMonoidHom.id ι))

/--
theorem `grade.decompose_single` / 定理 `grade.decompose_single`

English:
theorem grade.decompose_single
  given: (i : ι) (r : R)
  proof: decomposeAux_single _ _ _

中文:
定理 grade.decompose_single
  条件: (i : ι) (r : R)
  证明: decomposeAux_single _ _ _

Depends on / 依赖: decomposeAux_single
-/
theorem grade.decompose_single (i : ι) (r : R) :
    DirectSum.decompose (grade R : ι -> Submodule _ _) (single i r) =
      .of (fun i => grade R i) i ⟨single i r, single_mem_grade _ _⟩ :=
  decomposeAux_single _ _ _

/--
theorem `gradeBy.isInternal` / 定理 `gradeBy.isInternal`

English:
theorem gradeBy.isInternal
  statement: DirectSum.IsInternal (gradeBy R f)
  proof: DirectSum.Decomposition.isInternal _

中文:
定理 gradeBy.is整数ernal
  结论: 直和.Is整数ernal (gradeBy R f)
  证明: DirectSum.Decomposition.isInternal _

Depends on / 依赖: Decomposition, DirectSum, DirectSum.Decomposition.isInternal, isInternal
-/
theorem gradeBy.isInternal : DirectSum.IsInternal (gradeBy R f) :=
  DirectSum.Decomposition.isInternal _

/--
theorem `grade.isInternal` / 定理 `grade.isInternal`

English:
theorem grade.isInternal
  statement: DirectSum.IsInternal (grade R : ι -> Submodule R _)
  proof: DirectSum.Decomposition.isInternal _

中文:
定理 grade.is整数ernal
  结论: 直和.Is整数ernal (grade R : ι -> 子模 R _)
  证明: DirectSum.Decomposition.isInternal _

Depends on / 依赖: Decomposition, DirectSum, DirectSum.Decomposition.isInternal, isInternal
-/
theorem grade.isInternal : DirectSum.IsInternal (grade R : ι -> Submodule R _) :=
  DirectSum.Decomposition.isInternal _

end AddMonoidAlgebra
