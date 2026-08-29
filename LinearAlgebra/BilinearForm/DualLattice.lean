/-
Copyright (c) 2018 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!

# Dual submodule with respect to a bilinear form.

## Main definitions and results
- `BilinForm.dualSubmodule`: The dual submodule with respect to a bilinear form.
- `BilinForm.dualSubmodule_span_of_basis`: The dual of a lattice is spanned by the dual basis.

## TODO
Properly develop the material in the context of lattices.
-/

@[expose] public section

open LinearMap (BilinForm)
open Module

variable {R S M} [CommRing R] [Field S] [AddCommGroup M]
variable [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

namespace LinearMap

namespace BilinForm

variable (B : BilinForm S M)

/--
Definition of `dualSubmodule` / `dualSubmodule` 的定义

English:
definition dualSubmodule
  signature: (N : Submodule R M)
  body: { x | forall y in N, B x y in (1 : Submodule R S) }
  add_mem' {a b} ha hb y hy := by simpa using add_mem (ha y hy) (hb y hy)
  zero_mem' y _ := by rw [B.zero_left]; exact zero_mem _
  smul_mem' r a ha y hy := by
    convert! (1 : Submodule R S).smul_mem r (ha y hy)
    rw [← IsScalarTower.algebraMa

中文:
定义 dualSubmodule
  签名: (N : Submodule R M)
  定义体: { x | forall y in N, B x y in (1 : Submodule R S) }
  add_mem' {a b} ha hb y hy := by simpa using add_mem (ha y hy) (hb y hy)
  zero_mem' y _ := by rw [B.zero_left]; exact zero_mem _
  smul_mem' r a ha y hy := by
    convert! (1 : Submodule R S).smul_mem r (ha y hy)
    rw [← IsScalarTower.algebraMa

Depends on / 依赖: Submodule
-/
def dualSubmodule (N : Submodule R M) : Submodule R M where
  carrier := { x | forall y in N, B x y in (1 : Submodule R S) }
  add_mem' {a b} ha hb y hy := by simpa using add_mem (ha y hy) (hb y hy)
  zero_mem' y _ := by rw [B.zero_left]; exact zero_mem _
  smul_mem' r a ha y hy := by
    convert! (1 : Submodule R S).smul_mem r (ha y hy)
    rw [← IsScalarTower.algebraMap_smul S r a]
    simp only [algebraMap_smul, map_smul_of_tower, LinearMap.smul_apply]

/--
lemma `mem_dualSubmodule` / 引理 `mem_dualSubmodule`

English:
lemma mem_dualSubmodule
  given: {N : Submodule R M} {x}
  proof: Iff.rfl

中文:
引理 mem_dualSubmodule
  条件: {N : Submodule R M} {x}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_dualSubmodule {N : Submodule R M} {x} :
    x in B.dualSubmodule N ↔ forall y in N, B x y in (1 : Submodule R S) := Iff.rfl

/--
lemma `le_flip_dualSubmodule` / 引理 `le_flip_dualSubmodule`

English:
lemma le_flip_dualSubmodule
  given: {N₁ N₂ : Submodule R M}
  proof: by
  change (forall (x : M), x in N₁ -> _) ↔ forall (x : M), x in N₂ -> _
  simp only [mem_dualSubmodule, Submodule.mem_one, flip_apply]
  exact forall₂_comm

中文:
引理 le_flip_dualSubmodule
  条件: {N₁ N₂ : Submodule R M}
  证明: by
  change (forall (x : M), x in N₁ -> _) ↔ forall (x : M), x in N₂ -> _
  simp only [mem_dualSubmodule, Submodule.mem_one, flip_apply]
  exact forall₂_comm

Depends on / 依赖: Submodule, Submodule.mem_one, flip_apply, mem_dualSubmodule, mem_one
-/
lemma le_flip_dualSubmodule {N₁ N₂ : Submodule R M} :
    N₁ <= B.flip.dualSubmodule N₂ ↔ N₂ <= B.dualSubmodule N₁ := by
  change (forall (x : M), x in N₁ -> _) ↔ forall (x : M), x in N₂ -> _
  simp only [mem_dualSubmodule, Submodule.mem_one, flip_apply]
  exact forall₂_comm

/-- The natural paring of `B.dualSubmodule N` and `N`.
This is bundled as a bilinear map in `BilinForm.dualSubmoduleToDual`. -/
noncomputable
/--
Definition of `dualSubmoduleParing` / `dualSubmoduleParing` 的定义

English:
definition dualSubmoduleParing
  signature: {N : Submodule R M} (x : B.dualSubmodule N) (y : N)
  body: (Submodule.mem_one.mp <| x.prop y y.prop).choose

@[simp]

中文:
定义 dualSubmoduleParing
  签名: {N : Submodule R M} (x : B.dualSubmodule N) (y : N)
  定义体: (Submodule.mem_one.mp <| x.prop y y.prop).choose

@[simp]

Depends on / 依赖: Submodule, Submodule.mem_one.mp, mem_one, x.prop, y.prop
-/
def dualSubmoduleParing {N : Submodule R M} (x : B.dualSubmodule N) (y : N) : R :=
  (Submodule.mem_one.mp <| x.prop y y.prop).choose

@[simp]
/--
lemma `dualSubmoduleParing_spec` / 引理 `dualSubmoduleParing_spec`

English:
lemma dualSubmoduleParing_spec
  given: {N : Submodule R M} (x : B.dualSubmodule N) (y : N)
  proof: (Submodule.mem_one.mp <| x.prop y y.prop).choose_spec

中文:
引理 dualSubmoduleParing_spec
  条件: {N : Submodule R M} (x : B.dualSubmodule N) (y : N)
  证明: (Submodule.mem_one.mp <| x.prop y y.prop).choose_spec

Depends on / 依赖: Submodule, Submodule.mem_one.mp, choose_spec, mem_one, x.prop, y.prop
-/
lemma dualSubmoduleParing_spec {N : Submodule R M} (x : B.dualSubmodule N) (y : N) :
    algebraMap R S (B.dualSubmoduleParing x y) = B x y :=
  (Submodule.mem_one.mp <| x.prop y y.prop).choose_spec

/-- The natural paring of `B.dualSubmodule N` and `N`. -/
-- TODO: Show that this is perfect when `N` is a lattice and `B` is nondegenerate.
@[simps]
noncomputable
/--
Definition of `dualSubmoduleToDual` / `dualSubmoduleToDual` 的定义

English:
definition dualSubmoduleToDual
  signature: [IsDomain R] [IsTorsionFree R S] (N : Submodule R M)
  body: { toFun := fun x =>
    { toFun := B.dualSubmoduleParing x
      map_add' := fun x y => FaithfulSMul.algebraMap_injective R S (by simp)
      map_smul' := fun r m => FaithfulSMul.algebraMap_injective R S
        (by simp [← Algebra.smul_def]) }
    map_add' := fun x y => LinearMap.ext fun z => Faith

中文:
定义 dualSubmoduleToDual
  签名: [IsDomain R] [IsTorsionFree R S] (N : Submodule R M)
  定义体: { toFun := fun x =>
    { toFun := B.dualSubmoduleParing x
      map_add' := fun x y => FaithfulSMul.algebraMap_injective R S (by simp)
      map_smul' := fun r m => FaithfulSMul.algebraMap_injective R S
        (by simp [← Algebra.smul_def]) }
    map_add' := fun x y => LinearMap.ext fun z => Faith

Depends on / 依赖: Algebra, Algebra.smul_def, B.dualSubmoduleParing, FaithfulSMul, FaithfulSMul.algebraMap_injective, LinearMap, LinearMap.ext, algebraMap_injective, dualSubmoduleParing, map_add, map_smul, smul_def
-/
def dualSubmoduleToDual [IsDomain R] [IsTorsionFree R S] (N : Submodule R M) :
    B.dualSubmodule N ->ₗ[R] Module.Dual R N :=
  { toFun := fun x =>
    { toFun := B.dualSubmoduleParing x
      map_add' := fun x y => FaithfulSMul.algebraMap_injective R S (by simp)
      map_smul' := fun r m => FaithfulSMul.algebraMap_injective R S
        (by simp [← Algebra.smul_def]) }
    map_add' := fun x y => LinearMap.ext fun z => FaithfulSMul.algebraMap_injective R S
      (by simp)
    map_smul' := fun r x => LinearMap.ext fun y => FaithfulSMul.algebraMap_injective R S
      (by simp [← Algebra.smul_def]) }

/--
lemma `dualSubmoduleToDual_injective` / 引理 `dualSubmoduleToDual_injective`

English:
lemma dualSubmoduleToDual_injective
  statement: [IsDomain R] (hB : B.Nondegenerate) [IsTorsionFree R S]
  proof: by
  intro x y e
  ext
  apply LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  apply LinearMap.ext_on hN
  intro z hz
  simpa using congr_arg (algebraMap R S) (LinearMap.congr_fun e ⟨z, hz⟩)

中文:
引理 dualSubmoduleToDual_injective
  结论: [IsDomain R] (hB : B.Nondegenerate) [IsTorsionFree R S]
  证明: by
  intro x y e
  ext
  apply LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  apply LinearMap.ext_on hN
  intro z hz
  simpa using congr_arg (algebraMap R S) (LinearMap.congr_fun e ⟨z, hz⟩)

Depends on / 依赖: LinearMap, LinearMap.congr_fun, LinearMap.ext_on, LinearMap.ker_eq_bot.mp, algebraMap, congr_arg, congr_fun, ext_on, hB.ker_eq_bot, ker_eq_bot
-/
lemma dualSubmoduleToDual_injective [IsDomain R] (hB : B.Nondegenerate) [IsTorsionFree R S]
    (N : Submodule R M) (hN : Submodule.span S (N : Set M) = ⊤) :
    Function.Injective (B.dualSubmoduleToDual N) := by
  intro x y e
  ext
  apply LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  apply LinearMap.ext_on hN
  intro z hz
  simpa using congr_arg (algebraMap R S) (LinearMap.congr_fun e ⟨z, hz⟩)

/--
lemma `dualSubmodule_span_of_basis` / 引理 `dualSubmodule_span_of_basis`

English:
lemma dualSubmodule_span_of_basis
  statement: {ι} [Finite ι] [DecidableEq ι]
  proof: by
  cases nonempty_fintype ι
  apply le_antisymm
  · intro x hx
    rw [← (B.dualBasis hB b).sum_repr x]
    apply sum_mem
    rintro i -
obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx (b i) (Submodule.subset_span ⟨_, rfl⟩)
    simp only [dualBasis_repr_apply, ← hr, algebraMap_smul]
    apply Submodule.

中文:
引理 dualSubmodule_span_of_basis
  结论: {ι} [Finite ι] [DecidableEq ι]
  证明: by
  cases nonempty_fintype ι
  apply le_antisymm
  · intro x hx
    rw [← (B.dualBasis hB b).sum_repr x]
    apply sum_mem
    rintro i -
obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx (b i) (Submodule.subset_span ⟨_, rfl⟩)
    simp only [dualBasis_repr_apply, ← hr, algebraMap_smul]
    apply Submodule.

Depends on / 依赖: B.dualBasis, IsScalarTowe, Submodule, Submodule.mem_one.mp, Submodule.mem_span_range_iff_exists_fun, Submodule.smul_mem, Submodule.span_le, Submodule.subset_span, algebraMap_smul, dualBasis, dualBasis_repr_apply, le_antisymm, map_sum, mem_one, mem_span_range_iff_exists_fun, nonempty_fintype, smul_mem, span_le, subset_span, sum_mem
-/
lemma dualSubmodule_span_of_basis {ι} [Finite ι] [DecidableEq ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.dualSubmodule (Submodule.span R (Set.range b)) =
      Submodule.span R (Set.range <| B.dualBasis hB b) := by
  cases nonempty_fintype ι
  apply le_antisymm
  · intro x hx
    rw [← (B.dualBasis hB b).sum_repr x]
    apply sum_mem
    rintro i -
obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx (b i) (Submodule.subset_span ⟨_, rfl⟩)
    simp only [dualBasis_repr_apply, ← hr, algebraMap_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ y hy
    obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
    simp only [map_sum]
    apply sum_mem
    rintro j -
    rw [← IsScalarTower.algebraMap_smul S (f j)]; rw [map_smul]
    simp_rw [apply_dualBasis_left]
    rw [smul_eq_mul]; rw [mul_ite]; rw [mul_one]; rw [mul_zero]; rw [← (algebraMap R S).map_zero]; rw [← apply_ite]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩

/--
lemma `dualSubmodule_dualSubmodule_flip_of_basis` / 引理 `dualSubmodule_dualSubmodule_flip_of_basis`

English:
lemma dualSubmodule_dualSubmodule_flip_of_basis
  statement: {ι : Type*} [Finite ι]
  proof: by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis _ hB.flip]; rw [dualSubmodule_span_of_basis B hB]; rw [dualBasis_dualBasis_flip hB]

中文:
引理 dualSubmodule_dualSubmodule_flip_of_basis
  结论: {ι : 类型} [Finite ι]
  证明: by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis _ hB.flip]; rw [dualSubmodule_span_of_basis B hB]; rw [dualBasis_dualBasis_flip hB]

Depends on / 依赖: b.finiteDimensional_of_finite, classical, dualBasis_dualBasis_flip, dualSubmodule_span_of_basis, finiteDimensional_of_finite, hB.flip
-/
lemma dualSubmodule_dualSubmodule_flip_of_basis {ι : Type*} [Finite ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.dualSubmodule (B.flip.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) := by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis _ hB.flip]; rw [dualSubmodule_span_of_basis B hB]; rw [dualBasis_dualBasis_flip hB]

/--
lemma `dualSubmodule_flip_dualSubmodule_of_basis` / 引理 `dualSubmodule_flip_dualSubmodule_of_basis`

English:
lemma dualSubmodule_flip_dualSubmodule_of_basis
  statement: {ι : Type*} [Finite ι]
  proof: by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis B hB]; rw [dualSubmodule_span_of_basis _ hB.flip]; rw [dualBasis_flip_dualBasis hB]

中文:
引理 dualSubmodule_flip_dualSubmodule_of_basis
  结论: {ι : 类型} [Finite ι]
  证明: by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis B hB]; rw [dualSubmodule_span_of_basis _ hB.flip]; rw [dualBasis_flip_dualBasis hB]

Depends on / 依赖: b.finiteDimensional_of_finite, classical, dualBasis_flip_dualBasis, dualSubmodule_span_of_basis, finiteDimensional_of_finite, hB.flip
-/
lemma dualSubmodule_flip_dualSubmodule_of_basis {ι : Type*} [Finite ι]
    (hB : B.Nondegenerate) (b : Basis ι S M) :
    B.flip.dualSubmodule (B.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) := by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis B hB]; rw [dualSubmodule_span_of_basis _ hB.flip]; rw [dualBasis_flip_dualBasis hB]

/--
lemma `dualSubmodule_dualSubmodule_of_basis` / 引理 `dualSubmodule_dualSubmodule_of_basis`

English:
lemma dualSubmodule_dualSubmodule_of_basis
  proof: by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis B hB]; rw [dualSubmodule_span_of_basis B hB]; rw [dualBasis_dualBasis hB hB']

中文:
引理 dualSubmodule_dualSubmodule_of_basis
  证明: by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis B hB]; rw [dualSubmodule_span_of_basis B hB]; rw [dualBasis_dualBasis hB hB']

Depends on / 依赖: b.finiteDimensional_of_finite, classical, dualBasis_dualBasis, dualSubmodule_span_of_basis, finiteDimensional_of_finite
-/
lemma dualSubmodule_dualSubmodule_of_basis
    {ι} [Finite ι] (hB : B.Nondegenerate) (hB' : B.IsSymm) (b : Basis ι S M) :
    B.dualSubmodule (B.dualSubmodule (Submodule.span R (Set.range b))) =
      Submodule.span R (Set.range b) := by
  classical
  let := b.finiteDimensional_of_finite
  rw [dualSubmodule_span_of_basis B hB]; rw [dualSubmodule_span_of_basis B hB]; rw [dualBasis_dualBasis hB hB']

end BilinForm

end LinearMap
