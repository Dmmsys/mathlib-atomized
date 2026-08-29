/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Linear independence

This file collects basic consequences of linear (in)dependence and includes specialized tests for
specific families of vectors.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `linearIndependent_empty_type`: a family indexed by an empty type is linearly independent;
* `linearIndependent_unique_iff`: if `ι` is a singleton, then `LinearIndependent K v` is
  equivalent to `v default ≠ 0`;
* `linearIndependent_sum`: type-specific test for linear independence of families of vector
  fields;
* `linearIndependent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

## TODO

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

public section

assert_not_exists Cardinal

noncomputable section

open Function Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι -> M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)

variable {R v}

/--
theorem `LinearIndependent.restrict_scalars` / 定理 `LinearIndependent.restrict_scalars`

English:
theorem LinearIndependent.restrict_scalars
  statement: [Semiring K] [SMulWithZero R K] [Module K M]
  proof: by
  intro x y hxy
  let f := fun r : R => r • (1 : K)
  have := @li (x.mapRange f (by simp [f])) (y.mapRange f (by simp [f])) ?_
  · ext i
    exact hinj congr($this i)
  simpa [Finsupp.linearCombination, f, Finsupp.sum_mapRange_index]

中文:
定理 LinearIndependent.restrict_scalars
  结论: [半环 K] [带零标量乘法 R K] [模 K M]
  证明: by
  intro x y hxy
  let f := fun r : R => r • (1 : K)
  have := @li (x.mapRange f (by simp [f])) (y.mapRange f (by simp [f])) ?_
  · ext i
    exact hinj congr($this i)
  simpa [Finsupp.linearCombination, f, Finsupp.sum_mapRange_index]

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.sum_mapRange_index, linearCombination, mapRange, sum_mapRange_index, x.mapRange, y.mapRange
-/
theorem LinearIndependent.restrict_scalars [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] (hinj : Injective fun r : R => r • (1 : K))
    (li : LinearIndependent K v) : LinearIndependent R v := by
  intro x y hxy
  let f := fun r : R => r • (1 : K)
  have := @li (x.mapRange f (by simp [f])) (y.mapRange f (by simp [f])) ?_
  · ext i
    exact hinj congr($this i)
  simpa [Finsupp.linearCombination, f, Finsupp.sum_mapRange_index]

variable (R) in
/--
theorem `LinearIndependent.restrict_scalars'` / 定理 `LinearIndependent.restrict_scalars'`

English:
theorem LinearIndependent.restrict_scalars'
  statement: [Semiring K] [SMulWithZero R K] [Module K M]
  proof: restrict_scalars ((faithfulSMul_iff_injective_smul_one R K).mp inferInstance) li

中文:
定理 LinearIndependent.restrict_scalars'
  结论: [半环 K] [带零标量乘法 R K] [模 K M]
  证明: restrict_scalars ((faithfulSMul_iff_injective_smul_one R K).mp inferInstance) li

Depends on / 依赖: faithfulSMul_iff_injective_smul_one, restrict_scalars
-/
theorem LinearIndependent.restrict_scalars' [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] [FaithfulSMul R K] [IsScalarTower R K K] {v : ι -> M}
    (li : LinearIndependent K v) : LinearIndependent R v :=
  restrict_scalars ((faithfulSMul_iff_injective_smul_one R K).mp inferInstance) li

/--
theorem `Submodule.range_ker_disjoint` / 定理 `Submodule.range_ker_disjoint`

English:
theorem Submodule.range_ker_disjoint
  statement: {f : M ->ₗ[R] M'}
  proof: by
  rw [LinearIndependent]; rw [Finsupp.linearCombination_linear_comp] at hv
  rw [disjoint_iff_inf_le]; rw [← Set.image_univ]; rw [Finsupp.span_image_eq_map_linearCombination]; rw [map_inf_eq_map_inf_comap]; rw [(LinearMap.ker_comp _ _).symm.trans
      (LinearMap.ker_eq_bot_of_injective hv)]; rw [inf_bot_eq]; rw [map_bot]

中文:
定理 子模.range_ker_disjoint
  结论: {f : M ->ₗ[R] M'}
  证明: by
  rw [LinearIndependent]; rw [Finsupp.linearCombination_linear_comp] at hv
  rw [disjoint_iff_inf_le]; rw [← Set.image_univ]; rw [Finsupp.span_image_eq_map_linearCombination]; rw [map_inf_eq_map_inf_comap]; rw [(LinearMap.ker_comp _ _).symm.trans
      (LinearMap.ker_eq_bot_of_injective hv)]; rw [inf_bot_eq]; rw [map_bot]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_linear_comp, Finsupp.span_image_eq_map_linearCombination, LinearIndependent, LinearMap, LinearMap.ker_comp, LinearMap.ker_eq_bot_of_injective, Set.image_univ, disjoint_iff_inf_le, image_univ, inf_bot_eq, ker_comp, ker_eq_bot_of_injective, linearCombination_linear_comp, map_bot, map_inf_eq_map_inf_comap, span_image_eq_map_linearCombination, symm.trans
-/
theorem Submodule.range_ker_disjoint {f : M ->ₗ[R] M'}
    (hv : LinearIndependent R (f ∘ v)) :
    Disjoint (span R (range v)) (LinearMap.ker f) := by
  rw [LinearIndependent]; rw [Finsupp.linearCombination_linear_comp] at hv
  rw [disjoint_iff_inf_le]; rw [← Set.image_univ]; rw [Finsupp.span_image_eq_map_linearCombination]; rw [map_inf_eq_map_inf_comap]; rw [(LinearMap.ker_comp _ _).symm.trans
      (LinearMap.ker_eq_bot_of_injective hv)]; rw [inf_bot_eq]; rw [map_bot]

/--
theorem `LinearIndependent.map_of_injective_injectiveₛ` / 定理 `LinearIndependent.map_of_injective_injectiveₛ`

English:
theorem LinearIndependent.map_of_injective_injectiveₛ
  statement: {R' M' : Type*}
  proof: by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro S r₁ r₂ H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
exact hi hv _ _ _ (hj H) s hs

中文:
定理 LinearIndependent.map_of_injective_injectiveₛ
  结论: {R' M' : 类型}
  证明: by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro S r₁ r₂ H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
exact hi hv _ _ _ (hj H) s hs

Depends on / 依赖: comp_apply, linearIndependent_iff, map_sum, simp_rw
-/
theorem LinearIndependent.map_of_injective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R' -> R) (j : M ->+ M') (hi : Injective i) (hj : Injective j)
    (hc : forall (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v) := by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro S r₁ r₂ H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
exact hi hv _ _ _ (hj H) s hs

/--
theorem `LinearIndependent.map_of_surjective_injectiveₛ` / 定理 `LinearIndependent.map_of_surjective_injectiveₛ`

English:
theorem LinearIndependent.map_of_surjective_injectiveₛ
  statement: {R' M' : Type*}
  proof: by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine hv.map_of_injective_injectiveₛ i' j (fun _ _ h => ?_) hj fun r m => ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m]; rw [hi']

中文:
定理 LinearIndependent.map_of_surjective_injectiveₛ
  结论: {R' M' : 类型}
  证明: by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine hv.map_of_injective_injectiveₛ i' j (fun _ _ h => ?_) hj fun r m => ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m]; rw [hi']

Depends on / 依赖: apply_fun, hasRightInverse, hi.hasRightInverse, hv.map_of_injective_injective
-/
theorem LinearIndependent.map_of_surjective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R -> R') (j : M ->+ M') (hi : Surjective i) (hj : Injective j)
    (hc : forall (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v) := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine hv.map_of_injective_injectiveₛ i' j (fun _ _ h => ?_) hj fun r m => ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m]; rw [hi']

/--
theorem `LinearIndependent.map_injOn` / 定理 `LinearIndependent.map_injOn`

English:
theorem LinearIndependent.map_injOn
  statement: (hv : LinearIndependent R v) (f : M ->ₗ[R] M')
  proof: (f.linearIndependent_iff_of_injOn hf_inj).mpr hv

中文:
定理 LinearIndependent.map_injOn
  结论: (hv : LinearIndependent R v) (f : M ->ₗ[R] M')
  证明: (f.linearIndependent_iff_of_injOn hf_inj).mpr hv

Depends on / 依赖: f.linearIndependent_iff_of_injOn, hf_inj, linearIndependent_iff_of_injOn
-/
theorem LinearIndependent.map_injOn (hv : LinearIndependent R v) (f : M ->ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (Set.range v))) : LinearIndependent R (f ∘ v) :=
  (f.linearIndependent_iff_of_injOn hf_inj).mpr hv

/--
theorem `LinearIndepOn.map_injOn` / 定理 `LinearIndepOn.map_injOn`

English:
theorem LinearIndepOn.map_injOn
  statement: (hv : LinearIndepOn R v s) (f : M ->ₗ[R] M')
  proof: (f.linearIndepOn_iff_of_injOn hf_inj).mpr hv

中文:
定理 LinearIndepOn.map_injOn
  结论: (hv : LinearIndepOn R v s) (f : M ->ₗ[R] M')
  证明: (f.linearIndepOn_iff_of_injOn hf_inj).mpr hv

Depends on / 依赖: f.linearIndepOn_iff_of_injOn, hf_inj, linearIndepOn_iff_of_injOn
-/
theorem LinearIndepOn.map_injOn (hv : LinearIndepOn R v s) (f : M ->ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) : LinearIndepOn R (f ∘ v) s :=
  (f.linearIndepOn_iff_of_injOn hf_inj).mpr hv

/--
theorem `LinearIndepOn.comp_of_image` / 定理 `LinearIndepOn.comp_of_image`

English:
theorem LinearIndepOn.comp_of_image
  statement: {s : Set ι'} {f : ι' -> ι} (h : LinearIndepOn R v (f '' s))
  proof: LinearIndependent.comp h _ (Equiv.Set.imageOfInjOn _ _ hf).injective

中文:
定理 LinearIndepOn.comp_of_image
  结论: {s : 集合 ι'} {f : ι' -> ι} (h : LinearIndepOn R v (f '' s))
  证明: LinearIndependent.comp h _ (Equiv.Set.imageOfInjOn _ _ hf).injective

Depends on / 依赖: Equiv.Set.imageOfInjOn, LinearIndependent, LinearIndependent.comp, imageOfInjOn, injective
-/
theorem LinearIndepOn.comp_of_image {s : Set ι'} {f : ι' -> ι} (h : LinearIndepOn R v (f '' s))
    (hf : InjOn f s) : LinearIndepOn R (v ∘ f) s :=
  LinearIndependent.comp h _ (Equiv.Set.imageOfInjOn _ _ hf).injective

/--
theorem `LinearIndepOn.image_of_comp` / 定理 `LinearIndepOn.image_of_comp`

English:
theorem LinearIndepOn.image_of_comp
  given: (f : ι -> ι') (g : ι' -> M) (hs : LinearIndepOn R (g ∘ f) s)
  proof: by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

中文:
定理 LinearIndepOn.image_of_comp
  条件: (f : ι -> ι') (g : ι' -> M) (hs : LinearIndepOn R (g ∘ f) s)
  证明: by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

Depends on / 依赖: Equiv.Set.imageOfInjOn, hs.injective.of_comp, imageOfInjOn, injOn_iff_injective, injective, linearIndependent_equiv, nontriviality, of_comp
-/
theorem LinearIndepOn.image_of_comp (f : ι -> ι') (g : ι' -> M) (hs : LinearIndepOn R (g ∘ f) s) :
    LinearIndepOn R g (f '' s) := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

/--
theorem `LinearIndepOn.id_image` / 定理 `LinearIndepOn.id_image`

English:
theorem LinearIndepOn.id_image
  given: (hs : LinearIndepOn R v s)
  statement: LinearIndepOn R id (v '' s)
  proof: LinearIndepOn.image_of_comp v id hs

中文:
定理 LinearIndepOn.id_image
  条件: (hs : LinearIndepOn R v s)
  结论: LinearIndepOn R id (v '' s)
  证明: LinearIndepOn.image_of_comp v id hs

Depends on / 依赖: LinearIndepOn, LinearIndepOn.image_of_comp, image_of_comp
-/
theorem LinearIndepOn.id_image (hs : LinearIndepOn R v s) : LinearIndepOn R id (v '' s) :=
  LinearIndepOn.image_of_comp v id hs

/--
theorem `LinearIndepOn_iff_linearIndepOn_image_injOn` / 定理 `LinearIndepOn_iff_linearIndepOn_image_injOn`

English:
theorem LinearIndepOn_iff_linearIndepOn_image_injOn
  given: [Nontrivial R]
  proof: ⟨fun h => ⟨h.id_image, h.injOn⟩, fun h => (linearIndepOn_iff_image h.2).2 h.1⟩

中文:
定理 LinearIndepOn_iff_linearIndepOn_image_injOn
  条件: [非平凡 R]
  证明: ⟨fun h => ⟨h.id_image, h.injOn⟩, fun h => (linearIndepOn_iff_image h.2).2 h.1⟩

Depends on / 依赖: h.id_image, h.injOn, id_image, linearIndepOn_iff_image
-/
theorem LinearIndepOn_iff_linearIndepOn_image_injOn [Nontrivial R] :
    LinearIndepOn R v s ↔ LinearIndepOn R id (v '' s) ∧ InjOn v s :=
  ⟨fun h => ⟨h.id_image, h.injOn⟩, fun h => (linearIndepOn_iff_image h.2).2 h.1⟩

/--
theorem `linearIndepOn_congr` / 定理 `linearIndepOn_congr`

English:
theorem linearIndepOn_congr
  given: {w : ι -> M} (h : EqOn v w s)
  proof: by
  rw [LinearIndepOn]; rw [LinearIndepOn]
  convert! Iff.rfl using 2
  ext x
  exact h.symm x.2

中文:
定理 linearIndepOn_congr
  条件: {w : ι -> M} (h : EqOn v w s)
  证明: by
  rw [LinearIndepOn]; rw [LinearIndepOn]
  convert! Iff.rfl using 2
  ext x
  exact h.symm x.2

Depends on / 依赖: Iff.rfl, LinearIndepOn, convert, h.symm
-/
theorem linearIndepOn_congr {w : ι -> M} (h : EqOn v w s) :
    LinearIndepOn R v s ↔ LinearIndepOn R w s := by
  rw [LinearIndepOn]; rw [LinearIndepOn]
  convert! Iff.rfl using 2
  ext x
  exact h.symm x.2

/--
theorem `LinearIndepOn.congr` / 定理 `LinearIndepOn.congr`

English:
theorem LinearIndepOn.congr
  given: {w : ι -> M} (hli : LinearIndepOn R v s) (h : EqOn v w s)
  proof: (linearIndepOn_congr h).1 hli

中文:
定理 LinearIndepOn.congr
  条件: {w : ι -> M} (hli : LinearIndepOn R v s) (h : EqOn v w s)
  证明: (linearIndepOn_congr h).1 hli

Depends on / 依赖: linearIndepOn_congr
-/
theorem LinearIndepOn.congr {w : ι -> M} (hli : LinearIndepOn R v s) (h : EqOn v w s) :
    LinearIndepOn R w s :=
  (linearIndepOn_congr h).1 hli

/--
theorem `LinearIndependent.group_smul` / 定理 `LinearIndependent.group_smul`

English:
theorem LinearIndependent.group_smul
  statement: {G : Type*} [hG : Group G] [MulAction G R]
  proof: by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  refine (Group.isUnit (w i)).smul_left_cancel.mp ?_
  refine hv s (fun i => w i • g₁ i) (fun i => w i • g₂ i) (fun i hi => ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_assoc, smul_comm] using! hsum

@[simp]

中文:
定理 LinearIndependent.group_smul
  结论: {G : 类型} [hG : 群 G] [乘法作用 G R]
  证明: by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  refine (Group.isUnit (w i)).smul_left_cancel.mp ?_
  refine hv s (fun i => w i • g₁ i) (fun i => w i • g₂ i) (fun i hi => ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_assoc, smul_comm] using! hsum

@[simp]

Depends on / 依赖: Group.isUnit, isUnit, linearIndependent_iff, simp_rw, smul_assoc, smul_comm, smul_left_cancel, smul_left_cancel.mp
-/
theorem LinearIndependent.group_smul {G : Type*} [hG : Group G] [MulAction G R]
    [SMul G M] [IsScalarTower G R M] [SMulCommClass G R M] {v : ι -> M}
    (hv : LinearIndependent R v) (w : ι -> G) : LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  refine (Group.isUnit (w i)).smul_left_cancel.mp ?_
  refine hv s (fun i => w i • g₁ i) (fun i => w i • g₂ i) (fun i hi => ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_assoc, smul_comm] using! hsum

@[simp]
/--
theorem `LinearIndependent.group_smul_iff` / 定理 `LinearIndependent.group_smul_iff`

English:
theorem LinearIndependent.group_smul_iff
  statement: {G : Type*} [hG : Group G] [MulAction G R]
  proof: by
  refine ⟨fun h => ?_, fun h => h.group_smul w⟩
  convert! h.group_smul (fun i => (w i)⁻¹)
  simp [funext_iff]

中文:
定理 LinearIndependent.group_smul_iff
  结论: {G : 类型} [hG : 群 G] [乘法作用 G R]
  证明: by
  refine ⟨fun h => ?_, fun h => h.group_smul w⟩
  convert! h.group_smul (fun i => (w i)⁻¹)
  simp [funext_iff]

Depends on / 依赖: convert, funext_iff, group_smul, h.group_smul
-/
theorem LinearIndependent.group_smul_iff {G : Type*} [hG : Group G] [MulAction G R]
    [MulAction G M] [IsScalarTower G R M] [SMulCommClass G R M] (v : ι -> M) (w : ι -> G) :
    LinearIndependent R (w • v) ↔ LinearIndependent R v := by
  refine ⟨fun h => ?_, fun h => h.group_smul w⟩
  convert! h.group_smul (fun i => (w i)⁻¹)
  simp [funext_iff]

-- This lemma cannot be proved with `LinearIndependent.group_smul` since the action of
-- `Rˣ` on `R` is not commutative.
/--
theorem `LinearIndependent.units_smul` / 定理 `LinearIndependent.units_smul`

English:
theorem LinearIndependent.units_smul
  given: {v : ι -> M} (hv : LinearIndependent R v) (w : ι -> Rˣ)
  proof: by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  rw [← (w i).mul_left_inj]
  refine hv s (fun i => g₁ i • w i) (fun i => g₂ i • w i) (fun i hi => ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_eq_mul, mul_smul, Pi.smul_apply'] using! hsum

@[simp]

中文:
定理 LinearIndependent.units_smul
  条件: {v : ι -> M} (hv : LinearIndependent R v) (w : ι -> Rˣ)
  证明: by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  rw [← (w i).mul_left_inj]
  refine hv s (fun i => g₁ i • w i) (fun i => g₂ i • w i) (fun i hi => ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_eq_mul, mul_smul, Pi.smul_apply'] using! hsum

@[simp]

Depends on / 依赖: Pi.smul_apply, linearIndependent_iff, mul_left_inj, mul_smul, simp_rw, smul_apply, smul_eq_mul
-/
theorem LinearIndependent.units_smul {v : ι -> M} (hv : LinearIndependent R v) (w : ι -> Rˣ) :
    LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  rw [← (w i).mul_left_inj]
  refine hv s (fun i => g₁ i • w i) (fun i => g₂ i • w i) (fun i hi => ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_eq_mul, mul_smul, Pi.smul_apply'] using! hsum

@[simp]
/--
theorem `LinearIndependent.units_smul_iff` / 定理 `LinearIndependent.units_smul_iff`

English:
theorem LinearIndependent.units_smul_iff
  given: (v : ι -> M) (w : ι -> Rˣ)
  proof: by
  refine ⟨fun h => ?_, fun h => h.units_smul w⟩
  convert! h.units_smul (fun i => (w i)⁻¹)
  simp [funext_iff]

中文:
定理 LinearIndependent.units_smul_iff
  条件: (v : ι -> M) (w : ι -> Rˣ)
  证明: by
  refine ⟨fun h => ?_, fun h => h.units_smul w⟩
  convert! h.units_smul (fun i => (w i)⁻¹)
  simp [funext_iff]

Depends on / 依赖: convert, funext_iff, h.units_smul, units_smul
-/
theorem LinearIndependent.units_smul_iff (v : ι -> M) (w : ι -> Rˣ) :
    LinearIndependent R (w • v) ↔ LinearIndependent R v := by
  refine ⟨fun h => ?_, fun h => h.units_smul w⟩
  convert! h.units_smul (fun i => (w i)⁻¹)
  simp [funext_iff]

/--
theorem `linearIndependent_span` / 定理 `linearIndependent_span`

English:
theorem linearIndependent_span
  given: (hs : LinearIndependent R v)
  proof: LinearIndependent.of_comp (span R (range v)).subtype hs

中文:
定理 linearIndependent_span
  条件: (hs : LinearIndependent R v)
  证明: LinearIndependent.of_comp (span R (range v)).subtype hs
-/
theorem linearIndependent_span (hs : LinearIndependent R v) :
    LinearIndependent R (M := span R (range v))
      (fun i : ι => ⟨v i, subset_span (mem_range_self i)⟩) :=
  LinearIndependent.of_comp (span R (range v)).subtype hs

/--
theorem `linearIndependent_finset_map_embedding_subtype` / 定理 `linearIndependent_finset_map_embedding_subtype`

English:
theorem linearIndependent_finset_map_embedding_subtype
  statement: (s : Set M)
  proof: li.comp (fun _ => ⟨_, by aesop⟩) by intro; simp

中文:
定理 linearIndependent_finset_map_embedding_subtype
  结论: (s : 集合 M)
  证明: li.comp (fun _ => ⟨_, by aesop⟩) by intro; simp

Depends on / 依赖: li.comp
-/
theorem linearIndependent_finset_map_embedding_subtype (s : Set M)
    (li : LinearIndependent R ((↑) : s -> M)) (t : Finset s) :
    LinearIndependent R ((↑) : Finset.map (Embedding.subtype (· in s)) t -> M) :=
li.comp (fun _ => ⟨_, by aesop⟩) by intro; simp

section Indexed

/--
theorem `linearIndepOn_of_finite` / 定理 `linearIndepOn_of_finite`

English:
theorem linearIndepOn_of_finite
  given: (s : Set ι) (H : forall t subseteq s, Set.Finite t -> LinearIndepOn R v t)
  proof: linearIndepOn_iffₛ.2 fun f hf g hg eq =>
    linearIndepOn_iffₛ.1 (H _ (union_subset hf hg) <| (Finset.finite_toSet _).union <|
      Finset.finite_toSet _) f Set.subset_union_left g Set.subset_union_right eq

中文:
定理 linearIndepOn_of_finite
  条件: (s : 集合 ι) (H : 对任意 t subseteq s, 集合.有限 t -> LinearIndepOn R v t)
  证明: linearIndepOn_iffₛ.2 fun f hf g hg eq =>
    linearIndepOn_iffₛ.1 (H _ (union_subset hf hg) <| (Finset.finite_toSet _).union <|
      Finset.finite_toSet _) f Set.subset_union_left g Set.subset_union_right eq

Depends on / 依赖: Finset, Finset.finite_toSet, Set.subset_union_left, Set.subset_union_right, finite_toSet, subset_union_left, subset_union_right, union_subset
-/
theorem linearIndepOn_of_finite (s : Set ι) (H : forall t subseteq s, Set.Finite t -> LinearIndepOn R v t) :
    LinearIndepOn R v s :=
  linearIndepOn_iffₛ.2 fun f hf g hg eq =>
    linearIndepOn_iffₛ.1 (H _ (union_subset hf hg) <| (Finset.finite_toSet _).union <|
      Finset.finite_toSet _) f Set.subset_union_left g Set.subset_union_right eq

end Indexed

/--
theorem `LinearIndependent.eq_of_smul_apply_eq_smul_apply` / 定理 `LinearIndependent.eq_of_smul_apply_eq_smul_apply`

English:
theorem LinearIndependent.eq_of_smul_apply_eq_smul_apply
  statement: {M : Type*} [AddCommMonoid M] [Module R M]
  proof: by
  have h_single_eq : Finsupp.single i c = Finsupp.single j d :=
li by simpa [Finsupp.linearCombination_apply] using h
  rcases (Finsupp.single_eq_single_iff ..).mp h_single_eq with (⟨H, _⟩ | ⟨hc, _⟩)
  · exact H
  · contradiction

中文:
定理 LinearIndependent.eq_of_smul_apply_eq_smul_apply
  结论: {M : 类型} [加法交换幺半群 M] [模 R M]
  证明: by
  have h_single_eq : Finsupp.single i c = Finsupp.single j d :=
li by simpa [Finsupp.linearCombination_apply] using h
  rcases (Finsupp.single_eq_single_iff ..).mp h_single_eq with (⟨H, _⟩ | ⟨hc, _⟩)
  · exact H
  · contradiction

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.single, Finsupp.single_eq_single_iff, h_single_eq, linearCombination_apply, single, single_eq_single_iff
-/
theorem LinearIndependent.eq_of_smul_apply_eq_smul_apply {M : Type*} [AddCommMonoid M] [Module R M]
    {v : ι -> M} (li : LinearIndependent R v) (c d : R) (i j : ι) (hc : c != 0)
    (h : c • v i = d • v j) : i = j := by
  have h_single_eq : Finsupp.single i c = Finsupp.single j d :=
li by simpa [Finsupp.linearCombination_apply] using h
  rcases (Finsupp.single_eq_single_iff ..).mp h_single_eq with (⟨H, _⟩ | ⟨hc, _⟩)
  · exact H
  · contradiction

section Subtype


/--
theorem `LinearIndependent.disjoint_span_image` / 定理 `LinearIndependent.disjoint_span_image`

English:
theorem LinearIndependent.disjoint_span_image
  statement: (hv : LinearIndependent R v) {s t : Set ι}
  proof: by
  simp only [disjoint_def, Finsupp.mem_span_image_iff_linearCombination]
  rintro _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, H⟩
  rw [hv.finsuppLinearCombination_injective.eq_iff] at H; subst l₂
  have : l₁ = 0 := Submodule.disjoint_def.mp (Finsupp.disjoint_supported_supported hs) _ hl₁ hl₂
  simp [this]

中文:
定理 LinearIndependent.disjoint_span_image
  结论: (hv : LinearIndependent R v) {s t : 集合 ι}
  证明: by
  simp only [disjoint_def, Finsupp.mem_span_image_iff_linearCombination]
  rintro _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, H⟩
  rw [hv.finsuppLinearCombination_injective.eq_iff] at H; subst l₂
  have : l₁ = 0 := Submodule.disjoint_def.mp (Finsupp.disjoint_supported_supported hs) _ hl₁ hl₂
  simp [this]

Depends on / 依赖: Finsupp, Finsupp.disjoint_supported_supported, Finsupp.mem_span_image_iff_linearCombination, Submodule, Submodule.disjoint_def.mp, disjoint_def, disjoint_supported_supported, eq_iff, finsuppLinearCombination_injective, hv.finsuppLinearCombination_injective.eq_iff, mem_span_image_iff_linearCombination
-/
theorem LinearIndependent.disjoint_span_image (hv : LinearIndependent R v) {s t : Set ι}
    (hs : Disjoint s t) : Disjoint (Submodule.span R <| v '' s) (Submodule.span R <| v '' t) := by
  simp only [disjoint_def, Finsupp.mem_span_image_iff_linearCombination]
  rintro _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, H⟩
  rw [hv.finsuppLinearCombination_injective.eq_iff] at H; subst l₂
  have : l₁ = 0 := Submodule.disjoint_def.mp (Finsupp.disjoint_supported_supported hs) _ hl₁ hl₂
  simp [this]

/--
theorem `LinearIndependent.notMem_span_image` / 定理 `LinearIndependent.notMem_span_image`

English:
theorem LinearIndependent.notMem_span_image
  statement: [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι}
  proof: by
  have h' : v x in Submodule.span R (v '' {x}) := by
    rw [Set.image_singleton]
    exact mem_span_singleton_self (v x)
  intro w
  apply LinearIndependent.ne_zero x hv
  refine disjoint_def.1 (hv.disjoint_span_image ?_) (v x) h' w
  simpa using h

中文:
定理 LinearIndependent.notMem_span_image
  结论: [非平凡 R] (hv : LinearIndependent R v) {s : 集合 ι}
  证明: by
  have h' : v x in Submodule.span R (v '' {x}) := by
    rw [Set.image_singleton]
    exact mem_span_singleton_self (v x)
  intro w
  apply LinearIndependent.ne_zero x hv
  refine disjoint_def.1 (hv.disjoint_span_image ?_) (v x) h' w
  simpa using h

Depends on / 依赖: LinearIndependent, LinearIndependent.ne_zero, Set.image_singleton, Submodule, Submodule.span, disjoint_def, disjoint_span_image, hv.disjoint_span_image, image_singleton, mem_span_singleton_self, ne_zero
-/
theorem LinearIndependent.notMem_span_image [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι}
    {x : ι} (h : x ∉ s) : v x ∉ Submodule.span R (v '' s) := by
  have h' : v x in Submodule.span R (v '' {x}) := by
    rw [Set.image_singleton]
    exact mem_span_singleton_self (v x)
  intro w
  apply LinearIndependent.ne_zero x hv
  refine disjoint_def.1 (hv.disjoint_span_image ?_) (v x) h' w
  simpa using h

/--
theorem `LinearIndependent.linearCombination_ne_of_notMem_support` / 定理 `LinearIndependent.linearCombination_ne_of_notMem_support`

English:
theorem LinearIndependent.linearCombination_ne_of_notMem_support
  statement: [Nontrivial R]
  proof: by
  replace h : x ∉ (f.support : Set ι) := h
  intro w
  have p : forall x in Finsupp.supported R R f.support,
    Finsupp.linearCombination R v x != f.linearCombination R v := by
    simpa [← w, Finsupp.span_image_eq_map_linearCombination] using hv.notMem_span_image h
  exact p f (f.mem_supported_support R) rfl

中文:
定理 LinearIndependent.linearCombination_ne_of_notMem_support
  结论: [非平凡 R]
  证明: by
  replace h : x ∉ (f.support : Set ι) := h
  intro w
  have p : forall x in Finsupp.supported R R f.support,
    Finsupp.linearCombination R v x != f.linearCombination R v := by
    simpa [← w, Finsupp.span_image_eq_map_linearCombination] using hv.notMem_span_image h
  exact p f (f.mem_supported_support R) rfl

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.span_image_eq_map_linearCombination, Finsupp.supported, f.linearCombination, f.mem_supported_support, f.support, hv.notMem_span_image, linearCombination, mem_supported_support, notMem_span_image, replace, span_image_eq_map_linearCombination, support, supported
-/
theorem LinearIndependent.linearCombination_ne_of_notMem_support [Nontrivial R]
    (hv : LinearIndependent R v) {x : ι} (f : ι ->₀ R) (h : x ∉ f.support) :
    f.linearCombination R v != v x := by
  replace h : x ∉ (f.support : Set ι) := h
  intro w
  have p : forall x in Finsupp.supported R R f.support,
    Finsupp.linearCombination R v x != f.linearCombination R v := by
    simpa [← w, Finsupp.span_image_eq_map_linearCombination] using hv.notMem_span_image h
  exact p f (f.mem_supported_support R) rfl

end Subtype

/--
theorem `LinearIndepOn.id_imageₛ` / 定理 `LinearIndepOn.id_imageₛ`

English:
theorem LinearIndepOn.id_imageₛ
  statement: {s : Set M} {f : M ->ₗ[R] M'} (hs : LinearIndepOn R id s)
  proof: id_image hs.map_injOn f (by simpa using hf_inj)

中文:
定理 LinearIndepOn.id_imageₛ
  结论: {s : 集合 M} {f : M ->ₗ[R] M'} (hs : LinearIndepOn R id s)
  证明: id_image hs.map_injOn f (by simpa using hf_inj)

Depends on / 依赖: hf_inj, hs.map_injOn, id_image, map_injOn
-/
theorem LinearIndepOn.id_imageₛ {s : Set M} {f : M ->ₗ[R] M'} (hs : LinearIndepOn R id s)
    (hf_inj : Set.InjOn f (span R s)) : LinearIndepOn R id (f '' s) :=
id_image hs.map_injOn f (by simpa using hf_inj)

/--
theorem `surjective_of_linearIndependent_of_span` / 定理 `surjective_of_linearIndependent_of_span`

English:
theorem surjective_of_linearIndependent_of_span
  statement: [Nontrivial R] (hv : LinearIndependent R v)
  proof: by
  intro i
  let repr : (span R (range (v ∘ f)) : Type _) -> ι' ->₀ R := (hv.comp f f.injective).repr
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).mapDomain f
  have h_total_l : Finsupp.linearCombination R v l = v i := by
    dsimp only [l]
    rw [Finsupp.linearCombination_mapDomain]
    rw [(hv.comp f f.injective).linearCombination_repr]
  have h_total_eq : Finsupp.linearCombination R v l = Finsupp.linearCombination R v
       (Finsupp.single i 1) := by
    rw [h_total_l]; rw [Finsupp.linearCombination_single]; rw [one_smul]
  have l_eq : l = _ := hv h_total_eq
  dsimp only [l] at l_eq
  rw [← Finsupp.embDomain_eq_mapDomain] at l_eq
  rcases Finsupp.single_of_embDomain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq with
    ⟨i', hi'⟩
  use i'
  exact hi'.2

中文:
定理 surjective_of_linearIndependent_of_span
  结论: [非平凡 R] (hv : LinearIndependent R v)
  证明: by
  intro i
  let repr : (span R (range (v ∘ f)) : Type _) -> ι' ->₀ R := (hv.comp f f.injective).repr
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).mapDomain f
  have h_total_l : Finsupp.linearCombination R v l = v i := by
    dsimp only [l]
    rw [Finsupp.linearCombination_mapDomain]
    rw [(hv.comp f f.injective).linearCombination_repr]
  have h_total_eq : Finsupp.linearCombination R v l = Finsupp.linearCombination R v
       (Finsupp.single i 1) := by
    rw [h_total_l]; rw [Finsupp.linearCombination_single]; rw [one_smul]
  have l_eq : l = _ := hv h_total_eq
  dsimp only [l] at l_eq
  rw [← Finsupp.embDomain_eq_mapDomain] at l_eq
  rcases Finsupp.single_of_embDomain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq with
    ⟨i', hi'⟩
  use i'
  exact hi'.2

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_single, Finsupp.single, f.injective, h_total_eq, h_total_l, hv.comp, injective, linearCombination, linearCombination_mapDomain, linearCombination_repr, linearCombination_single, mapDomain, mem_range_self, one_s, single
-/
theorem surjective_of_linearIndependent_of_span [Nontrivial R] (hv : LinearIndependent R v)
    (f : ι' ↪ ι) (hss : range v subseteq span R (range (v ∘ f))) : Surjective f := by
  intro i
  let repr : (span R (range (v ∘ f)) : Type _) -> ι' ->₀ R := (hv.comp f f.injective).repr
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).mapDomain f
  have h_total_l : Finsupp.linearCombination R v l = v i := by
    dsimp only [l]
    rw [Finsupp.linearCombination_mapDomain]
    rw [(hv.comp f f.injective).linearCombination_repr]
  have h_total_eq : Finsupp.linearCombination R v l = Finsupp.linearCombination R v
       (Finsupp.single i 1) := by
    rw [h_total_l]; rw [Finsupp.linearCombination_single]; rw [one_smul]
  have l_eq : l = _ := hv h_total_eq
  dsimp only [l] at l_eq
  rw [← Finsupp.embDomain_eq_mapDomain] at l_eq
  rcases Finsupp.single_of_embDomain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq with
    ⟨i', hi'⟩
  use i'
  exact hi'.2

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_of_linearIndepOn_id_of_span_subtype` / 定理 `eq_of_linearIndepOn_id_of_span_subtype`

English:
theorem eq_of_linearIndepOn_id_of_span_subtype
  statement: [Nontrivial R] {s t : Set M}
  proof: by
  let f : t ↪ s :=
    ⟨fun x => ⟨x.1, h x.2⟩, fun a b hab => Subtype.coe_injective (Subtype.mk.inj hab)⟩
  have h_surj : Surjective f := by
    apply surjective_of_linearIndependent_of_span hs f _
    convert! hst <;> simp [f, comp_def]
  change s = t
  apply Subset.antisymm _ h
  intro x hx
  rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩
  convert! y.mem
  rw [← Subtype.mk.inj hy]

中文:
定理 eq_of_linearIndepOn_id_of_span_subtype
  结论: [非平凡 R] {s t : 集合 M}
  证明: by
  let f : t ↪ s :=
    ⟨fun x => ⟨x.1, h x.2⟩, fun a b hab => Subtype.coe_injective (Subtype.mk.inj hab)⟩
  have h_surj : Surjective f := by
    apply surjective_of_linearIndependent_of_span hs f _
    convert! hst <;> simp [f, comp_def]
  change s = t
  apply Subset.antisymm _ h
  intro x hx
  rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩
  convert! y.mem
  rw [← Subtype.mk.inj hy]

Depends on / 依赖: Subset, Subset.antisymm, Subtype, Subtype.coe_injective, Subtype.mk.inj, Surjective, antisymm, coe_injective, comp_def, convert, h_surj, surjective_of_linearIndependent_of_span, y.mem
-/
theorem eq_of_linearIndepOn_id_of_span_subtype [Nontrivial R] {s t : Set M}
    (hs : LinearIndepOn R id s) (h : t subseteq s) (hst : s subseteq span R t) : s = t := by
  let f : t ↪ s :=
    ⟨fun x => ⟨x.1, h x.2⟩, fun a b hab => Subtype.coe_injective (Subtype.mk.inj hab)⟩
  have h_surj : Surjective f := by
    apply surjective_of_linearIndependent_of_span hs f _
    convert! hst <;> simp [f, comp_def]
  change s = t
  apply Subset.antisymm _ h
  intro x hx
  rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩
  convert! y.mem
  rw [← Subtype.mk.inj hy]

/--
theorem `le_of_span_le_span` / 定理 `le_of_span_le_span`

English:
theorem le_of_span_le_span
  statement: [Nontrivial R] {s t u : Set M} (hl : LinearIndepOn R id u)
  proof: by
  have :=
    eq_of_linearIndepOn_id_of_span_subtype (hl.mono (Set.union_subset hsu htu))
      Set.subset_union_right (Set.union_subset (Set.Subset.trans subset_span hst) subset_span)
  rw [← this]; apply Set.subset_union_left

中文:
定理 le_of_span_le_span
  结论: [非平凡 R] {s t u : 集合 M} (hl : LinearIndepOn R id u)
  证明: by
  have :=
    eq_of_linearIndepOn_id_of_span_subtype (hl.mono (Set.union_subset hsu htu))
      Set.subset_union_right (Set.union_subset (Set.Subset.trans subset_span hst) subset_span)
  rw [← this]; apply Set.subset_union_left

Depends on / 依赖: Set.Subset.trans, Set.subset_union_left, Set.subset_union_right, Set.union_subset, Subset, eq_of_linearIndepOn_id_of_span_subtype, hl.mono, subset_span, subset_union_left, subset_union_right, union_subset
-/
theorem le_of_span_le_span [Nontrivial R] {s t u : Set M} (hl : LinearIndepOn R id u)
    (hsu : s subseteq u) (htu : t subseteq u) (hst : span R s <= span R t) : s subseteq t := by
  have :=
    eq_of_linearIndepOn_id_of_span_subtype (hl.mono (Set.union_subset hsu htu))
      Set.subset_union_right (Set.union_subset (Set.Subset.trans subset_span hst) subset_span)
  rw [← this]; apply Set.subset_union_left

/--
theorem `span_le_span_iff` / 定理 `span_le_span_iff`

English:
theorem span_le_span_iff
  statement: [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R ((↑) : u -> M))
  proof: ⟨le_of_span_le_span hl hsu htu, span_mono⟩

中文:
定理 span_le_span_iff
  结论: [非平凡 R] {s t u : 集合 M} (hl : LinearIndependent R ((↑) : u -> M))
  证明: ⟨le_of_span_le_span hl hsu htu, span_mono⟩

Depends on / 依赖: le_of_span_le_span, span_mono
-/
theorem span_le_span_iff [Nontrivial R] {s t u : Set M} (hl : LinearIndependent R ((↑) : u -> M))
    (hsu : s subseteq u) (htu : t subseteq u) : span R s <= span R t ↔ s subseteq t :=
  ⟨le_of_span_le_span hl hsu htu, span_mono⟩

end Semiring

section Module

variable {v : ι -> M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

open Finset in
/--
theorem `LinearIndependent.eq_coords_of_eq` / 定理 `LinearIndependent.eq_coords_of_eq`

English:
theorem LinearIndependent.eq_coords_of_eq
  statement: [Fintype ι] {v : ι -> M} (hv : LinearIndependent R v)
  proof: by
  rw [← sub_eq_zero]; rw [← sum_sub_distrib] at heq
  simp_rw [← sub_smul] at heq
  exact sub_eq_zero.mp ((linearIndependent_iff'.mp hv) univ (fun i => f i - g i) heq i (mem_univ i))

中文:
定理 LinearIndependent.eq_coords_of_eq
  结论: [有限类型 ι] {v : ι -> M} (hv : LinearIndependent R v)
  证明: by
  rw [← sub_eq_zero]; rw [← sum_sub_distrib] at heq
  simp_rw [← sub_smul] at heq
  exact sub_eq_zero.mp ((linearIndependent_iff'.mp hv) univ (fun i => f i - g i) heq i (mem_univ i))

Depends on / 依赖: A.unique, Box.Icc, Box.coe_ae_eq_Icc, Box.coe_subset_Icc, CompleteSpace, Hi.mono_set, Sub.sub, coe_ae_eq_Icc, coe_subset_Icc, continuousOn_pi, generalizing, hasBoxIntegral, hasIntegral_GP_divergence_of_forall_hasDerivWithinAt, hs.mono, integral, inter_subset_left, linearIndependent_iff, mem_univ, mono_set, setIntegral_congr_set
-/
theorem LinearIndependent.eq_coords_of_eq [Fintype ι] {v : ι -> M} (hv : LinearIndependent R v)
    {f : ι -> R} {g : ι -> R} (heq : ∑ i, f i • v i = ∑ i, g i • v i) (i : ι) : f i = g i := by
  rw [← sub_eq_zero]; rw [← sum_sub_distrib] at heq
  simp_rw [← sub_smul] at heq
  exact sub_eq_zero.mp ((linearIndependent_iff'.mp hv) univ (fun i => f i - g i) heq i (mem_univ i))

/--
theorem `LinearIndependent.map` / 定理 `LinearIndependent.map`

English:
theorem LinearIndependent.map
  statement: (hv : LinearIndependent R v) {f : M ->ₗ[R] M'}
  proof: (f.linearIndependent_iff_of_disjoint hf_inj).mpr hv

中文:
定理 LinearIndependent.map
  结论: (hv : LinearIndependent R v) {f : M ->ₗ[R] M'}
  证明: (f.linearIndependent_iff_of_disjoint hf_inj).mpr hv

Depends on / 依赖: f.linearIndependent_iff_of_disjoint, hf_inj, linearIndependent_iff_of_disjoint
-/
theorem LinearIndependent.map (hv : LinearIndependent R v) {f : M ->ₗ[R] M'}
    (hf_inj : Disjoint (span R (range v)) (LinearMap.ker f)) : LinearIndependent R (f ∘ v) :=
  (f.linearIndependent_iff_of_disjoint hf_inj).mpr hv

/--
theorem `LinearIndependent.map'` / 定理 `LinearIndependent.map'`

English:
theorem LinearIndependent.map'
  statement: (hv : LinearIndependent R v) (f : M ->ₗ[R] M')
  proof: hv.map by simp_rw [hf_inj, disjoint_bot_right]

中文:
定理 LinearIndependent.map'
  结论: (hv : LinearIndependent R v) (f : M ->ₗ[R] M')
  证明: hv.map by simp_rw [hf_inj, disjoint_bot_right]

Depends on / 依赖: disjoint_bot_right, hf_inj, hv.map, simp_rw
-/
theorem LinearIndependent.map' (hv : LinearIndependent R v) (f : M ->ₗ[R] M')
    (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ v) :=
hv.map by simp_rw [hf_inj, disjoint_bot_right]

/--
theorem `LinearIndependent.map_of_injective_injective` / 定理 `LinearIndependent.map_of_injective_injective`

English:
theorem LinearIndependent.map_of_injective_injective
  statement: {R' M' : Type*}
  proof: by
  rw [linearIndependent_iff'] at hv ⊢
  intro S r' H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
exact hi _ hv _ _ (hj _ H) s hs

中文:
定理 LinearIndependent.map_of_injective_injective
  结论: {R' M' : 类型}
  证明: by
  rw [linearIndependent_iff'] at hv ⊢
  intro S r' H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
exact hi _ hv _ _ (hj _ H) s hs

Depends on / 依赖: comp_apply, linearIndependent_iff, map_sum, simp_rw
-/
theorem LinearIndependent.map_of_injective_injective {R' M' : Type*}
    [Ring R'] [AddCommGroup M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R' -> R) (j : M ->+ M') (hi : forall r, i r = 0 -> r = 0) (hj : forall m, j m = 0 -> m = 0)
    (hc : forall (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro S r' H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
exact hi _ hv _ _ (hj _ H) s hs

/--
theorem `LinearIndependent.map_of_surjective_injective` / 定理 `LinearIndependent.map_of_surjective_injective`

English:
theorem LinearIndependent.map_of_surjective_injective
  statement: {R' M' : Type*}
  proof: hv.map_of_surjective_injectiveₛ i _ hi ((injective_iff_map_eq_zero _).mpr hj) hc

中文:
定理 LinearIndependent.map_of_surjective_injective
  结论: {R' M' : 类型}
  证明: hv.map_of_surjective_injectiveₛ i _ hi ((injective_iff_map_eq_zero _).mpr hj) hc

Depends on / 依赖: hv.map_of_surjective_injective, injective_iff_map_eq_zero
-/
theorem LinearIndependent.map_of_surjective_injective {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R -> R') (j : M ->+ M') (hi : Surjective i) (hj : forall m, j m = 0 -> m = 0)
    (hc : forall (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v) :=
  hv.map_of_surjective_injectiveₛ i _ hi ((injective_iff_map_eq_zero _).mpr hj) hc

/--
theorem `LinearMap.linearIndependent_iff` / 定理 `LinearMap.linearIndependent_iff`

English:
theorem LinearMap.linearIndependent_iff
  given: (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥)
  proof: f.linearIndependent_iff_of_disjoint by simp_rw [hf_inj, disjoint_bot_right]

中文:
定理 线性映射.linearIndependent_iff
  条件: (f : M ->ₗ[R] M') (hf_inj : 线性映射.ker f = ⊥)
  证明: f.linearIndependent_iff_of_disjoint by simp_rw [hf_inj, disjoint_bot_right]
-/
protected theorem LinearMap.linearIndependent_iff (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
f.linearIndependent_iff_of_disjoint by simp_rw [hf_inj, disjoint_bot_right]

/--
theorem `LinearIndependent.finCons'` / 定理 `LinearIndependent.finCons'`

English:
theorem LinearIndependent.finCons'
  statement: {m : Nat} (x : M) (v : Fin m -> M) (hli : LinearIndependent R v)
  proof: by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  rintro g total_eq j
  simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at total_eq
  have : g 0 = 0 := by
    refine x_ortho (g 0) (∑ i : Fin m, g i.succ • v i) ?_ total_eq
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [this]; rw [zero_smul]; rw [zero_add] at total_eq
  exact Fin.cases this (hli _ total_eq) j

@[deprecated (since := "2026-04-07")]
alias LinearIndependent.fin_cons' := LinearIndependent.finCons'

中文:
定理 LinearIndependent.finCons'
  结论: {m : 自然数} (x : M) (v : 有限集 m -> M) (hli : LinearIndependent R v)
  证明: by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  rintro g total_eq j
  simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at total_eq
  have : g 0 = 0 := by
    refine x_ortho (g 0) (∑ i : Fin m, g i.succ • v i) ?_ total_eq
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [this]; rw [zero_smul]; rw [zero_add] at total_eq
  exact Fin.cases this (hli _ total_eq) j

@[deprecated (since := "2026-04-07")]
alias LinearIndependent.fin_cons' := LinearIndependent.finCons'

Depends on / 依赖: Fin.cases, Fin.cons_succ, Fin.cons_zero, Fin.sum_univ_succ, Fintype, Fintype.linearIndependent_iff, cons_succ, cons_zero, i.succ, linearIndependent_iff, simp_rw, smul_mem, subset_span, sum_mem, sum_univ_succ, total_eq, x_ortho, zero_add, zero_smul
-/
theorem LinearIndependent.finCons' {m : Nat} (x : M) (v : Fin m -> M) (hli : LinearIndependent R v)
    (x_ortho : forall (c : R) (y : M), y in Submodule.span R (Set.range v) -> c • x + y = 0 -> c = 0) :
    LinearIndependent R (Fin.cons x v : Fin m.succ -> M) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  rintro g total_eq j
  simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at total_eq
  have : g 0 = 0 := by
    refine x_ortho (g 0) (∑ i : Fin m, g i.succ • v i) ?_ total_eq
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [this]; rw [zero_smul]; rw [zero_add] at total_eq
  exact Fin.cases this (hli _ total_eq) j

@[deprecated (since := "2026-04-07")]
alias LinearIndependent.fin_cons' := LinearIndependent.finCons'

/--
theorem `LinearIndependent.finSnoc'` / 定理 `LinearIndependent.finSnoc'`

English:
theorem LinearIndependent.finSnoc'
  statement: {m : Nat} (v : Fin m -> M) (x : M) (hli : LinearIndependent R v)
  proof: by
  rw [Fin.snoc_eq_cons_rotate v x]; rw [← Function.comp_def]
  exact (linearIndependent_equiv _).mpr (.finCons' x v hli x_ortho)

中文:
定理 LinearIndependent.finSnoc'
  结论: {m : 自然数} (v : 有限集 m -> M) (x : M) (hli : LinearIndependent R v)
  证明: by
  rw [Fin.snoc_eq_cons_rotate v x]; rw [← Function.comp_def]
  exact (linearIndependent_equiv _).mpr (.finCons' x v hli x_ortho)

Depends on / 依赖: Fin.snoc_eq_cons_rotate, Function, Function.comp_def, comp_def, finCons, linearIndependent_equiv, snoc_eq_cons_rotate, x_ortho
-/
theorem LinearIndependent.finSnoc' {m : Nat} (v : Fin m -> M) (x : M) (hli : LinearIndependent R v)
    (x_ortho : forall (c : R) (y : M), y in Submodule.span R (Set.range v) -> c • x + y = 0 -> c = 0) :
    LinearIndependent R (Fin.snoc v x : Fin m.succ -> M) := by
  rw [Fin.snoc_eq_cons_rotate v x]; rw [← Function.comp_def]
  exact (linearIndependent_equiv _).mpr (.finCons' x v hli x_ortho)

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι -> M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

/--
theorem `linearIndependent_sum` / 定理 `linearIndependent_sum`

English:
theorem linearIndependent_sum
  given: {v : ι oplus ι' -> M}
  proof: by
  classical
  rw [range_comp v]; rw [range_comp v]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨h.comp _ Sum.inl_injective, h.comp _ Sum.inr_injective, ?_⟩
exact h.disjoint_span_image isCompl_range_inl_range_inr.disjoint
  rintro ⟨hl, hr, hlr⟩
  rw [linearIndependent_iff'] at *
  intro s g hg i hi
  have :
    ((∑ i in s.preimage Sum.inl Sum.inl_injective.injOn, (fun x => g x • v x) (Sum.inl i)) +
        ∑ i in s.preimage Sum.inr Sum.inr_injective.injOn, (fun x => g x • v x) (Sum.inr i)) =
      0 := by
    -- Porting note: `g` must be specified.
    rw [Finset.sum_preimage' (g := fun x => g x • v x)]; rw [Finset.sum_preimage' (g := fun x => g x • v x)]; rw [← Finset.sum_union]; rw [← Finset.filter_or]
    · simpa only [← mem_union, range_inl_union_range_inr, mem_univ, Finset.filter_true]
    · exact Finset.disjoint_filter.2 fun x _ hx =>
        disjoint_left.1 isCompl_range_inl_range_inr.disjoint hx
  rw [← eq_neg_iff_add_eq_zero] at this
  rw [disjoint_def'] at hlr
  have A := by
    refine hlr _ (sum_mem fun i _ => ?_) _ (neg_mem <| sum_mem fun i _ => ?_) this
    · exact smul_mem _ _ (subset_span ⟨Sum.inl i, mem_range_self _, rfl⟩)
    · exact smul_mem _ _ (subset_span ⟨Sum.inr i, mem_range_self _, rfl⟩)
  rcases i with i | i
  · exact hl _ _ A i (Finset.mem_preimage.2 hi)
  · rw [this, neg_eq_zero] at A
    exact hr _ _ A i (Finset.mem_preimage.2 hi)

中文:
定理 linearIndependent_sum
  条件: {v : ι oplus ι' -> M}
  证明: by
  classical
  rw [range_comp v]; rw [range_comp v]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨h.comp _ Sum.inl_injective, h.comp _ Sum.inr_injective, ?_⟩
exact h.disjoint_span_image isCompl_range_inl_range_inr.disjoint
  rintro ⟨hl, hr, hlr⟩
  rw [linearIndependent_iff'] at *
  intro s g hg i hi
  have :
    ((∑ i in s.preimage Sum.inl Sum.inl_injective.injOn, (fun x => g x • v x) (Sum.inl i)) +
        ∑ i in s.preimage Sum.inr Sum.inr_injective.injOn, (fun x => g x • v x) (Sum.inr i)) =
      0 := by
    -- Porting note: `g` must be specified.
    rw [Finset.sum_preimage' (g := fun x => g x • v x)]; rw [Finset.sum_preimage' (g := fun x => g x • v x)]; rw [← Finset.sum_union]; rw [← Finset.filter_or]
    · simpa only [← mem_union, range_inl_union_range_inr, mem_univ, Finset.filter_true]
    · exact Finset.disjoint_filter.2 fun x _ hx =>
        disjoint_left.1 isCompl_range_inl_range_inr.disjoint hx
  rw [← eq_neg_iff_add_eq_zero] at this
  rw [disjoint_def'] at hlr
  have A := by
    refine hlr _ (sum_mem fun i _ => ?_) _ (neg_mem <| sum_mem fun i _ => ?_) this
    · exact smul_mem _ _ (subset_span ⟨Sum.inl i, mem_range_self _, rfl⟩)
    · exact smul_mem _ _ (subset_span ⟨Sum.inr i, mem_range_self _, rfl⟩)
  rcases i with i | i
  · exact hl _ _ A i (Finset.mem_preimage.2 hi)
  · rw [this, neg_eq_zero] at A
    exact hr _ _ A i (Finset.mem_preimage.2 hi)

Depends on / 依赖: Sum.inl, Sum.inl_injective, Sum.inl_injective.injOn, Sum.inr, Sum.inr_injective, Sum.inr_injective.injOn, classical, disjoint, disjoint_span_image, h.comp, h.disjoint_span_image, inl_injective, inr_injective, isCompl_range_inl_range_inr, isCompl_range_inl_range_inr.disjoint, linearIndependent_iff, preimage, range_comp, s.preimage
-/
theorem linearIndependent_sum {v : ι oplus ι' -> M} :
    LinearIndependent R v ↔
      LinearIndependent R (v ∘ Sum.inl) ∧
        LinearIndependent R (v ∘ Sum.inr) ∧
          Disjoint (Submodule.span R (range (v ∘ Sum.inl)))
            (Submodule.span R (range (v ∘ Sum.inr))) := by
  classical
  rw [range_comp v]; rw [range_comp v]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨h.comp _ Sum.inl_injective, h.comp _ Sum.inr_injective, ?_⟩
exact h.disjoint_span_image isCompl_range_inl_range_inr.disjoint
  rintro ⟨hl, hr, hlr⟩
  rw [linearIndependent_iff'] at *
  intro s g hg i hi
  have :
    ((∑ i in s.preimage Sum.inl Sum.inl_injective.injOn, (fun x => g x • v x) (Sum.inl i)) +
        ∑ i in s.preimage Sum.inr Sum.inr_injective.injOn, (fun x => g x • v x) (Sum.inr i)) =
      0 := by
    -- Porting note: `g` must be specified.
    rw [Finset.sum_preimage' (g := fun x => g x • v x)]; rw [Finset.sum_preimage' (g := fun x => g x • v x)]; rw [← Finset.sum_union]; rw [← Finset.filter_or]
    · simpa only [← mem_union, range_inl_union_range_inr, mem_univ, Finset.filter_true]
    · exact Finset.disjoint_filter.2 fun x _ hx =>
        disjoint_left.1 isCompl_range_inl_range_inr.disjoint hx
  rw [← eq_neg_iff_add_eq_zero] at this
  rw [disjoint_def'] at hlr
  have A := by
    refine hlr _ (sum_mem fun i _ => ?_) _ (neg_mem <| sum_mem fun i _ => ?_) this
    · exact smul_mem _ _ (subset_span ⟨Sum.inl i, mem_range_self _, rfl⟩)
    · exact smul_mem _ _ (subset_span ⟨Sum.inr i, mem_range_self _, rfl⟩)
  rcases i with i | i
  · exact hl _ _ A i (Finset.mem_preimage.2 hi)
  · rw [this, neg_eq_zero] at A
    exact hr _ _ A i (Finset.mem_preimage.2 hi)

/--
theorem `LinearIndependent.sum_type` / 定理 `LinearIndependent.sum_type`

English:
theorem LinearIndependent.sum_type
  statement: {v' : ι' -> M} (hv : LinearIndependent R v)
  proof: linearIndependent_sum.2 ⟨hv, hv', h⟩

中文:
定理 LinearIndependent.sum_type
  结论: {v' : ι' -> M} (hv : LinearIndependent R v)
  证明: linearIndependent_sum.2 ⟨hv, hv', h⟩

Depends on / 依赖: linearIndependent_sum
-/
theorem LinearIndependent.sum_type {v' : ι' -> M} (hv : LinearIndependent R v)
    (hv' : LinearIndependent R v')
    (h : Disjoint (Submodule.span R (range v)) (Submodule.span R (range v'))) :
    LinearIndependent R (Sum.elim v v') :=
  linearIndependent_sum.2 ⟨hv, hv', h⟩

/--
theorem `LinearIndepOn.union` / 定理 `LinearIndepOn.union`

English:
theorem LinearIndepOn.union
  statement: {t : Set ι} (hs : LinearIndepOn R v s) (ht : LinearIndepOn R v t)
  proof: by
  nontriviality R
  classical
  have hli := LinearIndependent.sum_type hs ht (by rwa [← image_eq_range, ← image_eq_range])
  have hdj := (hdj.of_span₀ hs.zero_notMem_image).of_image
  rw [LinearIndepOn]
  convert! (hli.comp _ (Equiv.Set.union hdj).injective) with ⟨x, hx | hx⟩
  · rw [comp_apply, Equiv.Set.union_apply_left _ hx, Sum.elim_inl]
  rw [comp_apply]; rw [Equiv.Set.union_apply_right _ hx]; rw [Sum.elim_inr]

中文:
定理 LinearIndepOn.union
  结论: {t : 集合 ι} (hs : LinearIndepOn R v s) (ht : LinearIndepOn R v t)
  证明: by
  nontriviality R
  classical
  have hli := LinearIndependent.sum_type hs ht (by rwa [← image_eq_range, ← image_eq_range])
  have hdj := (hdj.of_span₀ hs.zero_notMem_image).of_image
  rw [LinearIndepOn]
  convert! (hli.comp _ (Equiv.Set.union hdj).injective) with ⟨x, hx | hx⟩
  · rw [comp_apply, Equiv.Set.union_apply_left _ hx, Sum.elim_inl]
  rw [comp_apply]; rw [Equiv.Set.union_apply_right _ hx]; rw [Sum.elim_inr]

Depends on / 依赖: Equiv.Set.union, Equiv.Set.union_apply_left, Equiv.Set.union_apply_right, LinearIndepOn, LinearIndependent, LinearIndependent.sum_type, Sum.elim_inl, Sum.elim_inr, classical, comp_apply, convert, elim_inl, elim_inr, hdj.of_span, hli.comp, hs.zero_notMem_image, image_eq_range, injective, nontriviality, of_image
-/
theorem LinearIndepOn.union {t : Set ι} (hs : LinearIndepOn R v s) (ht : LinearIndepOn R v t)
    (hdj : Disjoint (span R (v '' s)) (span R (v '' t))) : LinearIndepOn R v (s union t) := by
  nontriviality R
  classical
  have hli := LinearIndependent.sum_type hs ht (by rwa [← image_eq_range, ← image_eq_range])
  have hdj := (hdj.of_span₀ hs.zero_notMem_image).of_image
  rw [LinearIndepOn]
  convert! (hli.comp _ (Equiv.Set.union hdj).injective) with ⟨x, hx | hx⟩
  · rw [comp_apply, Equiv.Set.union_apply_left _ hx, Sum.elim_inl]
  rw [comp_apply]; rw [Equiv.Set.union_apply_right _ hx]; rw [Sum.elim_inr]

/--
theorem `LinearIndepOn.id_union` / 定理 `LinearIndepOn.id_union`

English:
theorem LinearIndepOn.id_union
  statement: {s t : Set M} (hs : LinearIndepOn R id s) (ht : LinearIndepOn R id t)
  proof: hs.union ht (by simpa)

中文:
定理 LinearIndepOn.id_union
  结论: {s t : 集合 M} (hs : LinearIndepOn R id s) (ht : LinearIndepOn R id t)
  证明: hs.union ht (by simpa)

Depends on / 依赖: hs.union
-/
theorem LinearIndepOn.id_union {s t : Set M} (hs : LinearIndepOn R id s) (ht : LinearIndepOn R id t)
    (hdj : Disjoint (span R s) (span R t)) : LinearIndepOn R id (s union t) :=
  hs.union ht (by simpa)

/--
theorem `linearIndepOn_union_iff` / 定理 `linearIndepOn_union_iff`

English:
theorem linearIndepOn_union_iff
  given: {t : Set ι} (hdj : Disjoint s t)
  proof: by
  refine ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right, ?_⟩,
    fun h => h.1.union h.2.1 h.2.2⟩
  convert! h.disjoint_span_image (s := (↑) ⁻¹' s) (t := (↑) ⁻¹' t) (hdj.preimage _) <;>
  aesop

中文:
定理 linearIndepOn_union_iff
  条件: {t : 集合 ι} (hdj : Disjoint s t)
  证明: by
  refine ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right, ?_⟩,
    fun h => h.1.union h.2.1 h.2.2⟩
  convert! h.disjoint_span_image (s := (↑) ⁻¹' s) (t := (↑) ⁻¹' t) (hdj.preimage _) <;>
  aesop

Depends on / 依赖: convert, disjoint_span_image, h.disjoint_span_image, h.mono, hdj.preimage, preimage, subset_union_left, subset_union_right
-/
theorem linearIndepOn_union_iff {t : Set ι} (hdj : Disjoint s t) :
    LinearIndepOn R v (s union t) ↔
    LinearIndepOn R v s ∧ LinearIndepOn R v t ∧ Disjoint (span R (v '' s)) (span R (v '' t)) := by
  refine ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right, ?_⟩,
    fun h => h.1.union h.2.1 h.2.2⟩
  convert! h.disjoint_span_image (s := (↑) ⁻¹' s) (t := (↑) ⁻¹' t) (hdj.preimage _) <;>
  aesop

/--
theorem `linearIndepOn_id_union_iff` / 定理 `linearIndepOn_id_union_iff`

English:
theorem linearIndepOn_id_union_iff
  given: {s t : Set M} (hdj : Disjoint s t)
  proof: by
  rw [linearIndepOn_union_iff hdj]; rw [image_id]; rw [image_id]

中文:
定理 linearIndepOn_id_union_iff
  条件: {s t : 集合 M} (hdj : Disjoint s t)
  证明: by
  rw [linearIndepOn_union_iff hdj]; rw [image_id]; rw [image_id]

Depends on / 依赖: image_id, linearIndepOn_union_iff
-/
theorem linearIndepOn_id_union_iff {s t : Set M} (hdj : Disjoint s t) :
    LinearIndepOn R id (s union t) ↔
    LinearIndepOn R id s ∧ LinearIndepOn R id t ∧ Disjoint (span R s) (span R t) := by
  rw [linearIndepOn_union_iff hdj]; rw [image_id]; rw [image_id]

open LinearMap

/--
theorem `LinearIndepOn.image` / 定理 `LinearIndepOn.image`

English:
theorem LinearIndepOn.image
  statement: {s : Set M} {f : M ->ₗ[R] M'}
  proof: hs.id_imageₛ LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

中文:
定理 LinearIndepOn.像
  结论: {s : 集合 M} {f : M ->ₗ[R] M'}
  证明: hs.id_imageₛ LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

Depends on / 依赖: LinearMap, LinearMap.injOn_of_disjoint_ker, hf_inj, hs.id_image, injOn_of_disjoint_ker, le_rfl
-/
theorem LinearIndepOn.image {s : Set M} {f : M ->ₗ[R] M'}
    (hs : LinearIndepOn R id s) (hf_inj : Disjoint (span R s) (LinearMap.ker f)) :
    LinearIndepOn R id (f '' s) :=
hs.id_imageₛ LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

-- See, for example, Keith Conrad's note [ConradLinearChar]
-- <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>
/-- Dedekind's linear independence of characters -/
@[stacks 0CKL]
/--
theorem `linearIndependent_monoidHom` / 定理 `linearIndependent_monoidHom`

English:
theorem linearIndependent_monoidHom
  statement: (G : Type*) [MulOneClass G] (L : Type*) [CommRing L]
  proof: by
  let := Classical.decEq (G ->* L)
  let : MulAction L L := DistribMulAction.toMulAction
  -- We prove linear independence by showing that only the trivial linear combination vanishes.
  apply linearIndependent_iff'.2
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
  intro g hg
  -- Here
  -- * `a` is a new character we will insert into the `Finset` of characters `s`,
  -- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
  -- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
  -- and it remains to prove that `g` vanishes on `insert a s`.
  -- We now make the key calculation:
  -- For any character `i` in the original `Finset`, we have `g i • i = g i • a` as functions
  -- on the monoid `G`.
  have h1 (i) (his : i in s) : (g i • i : G -> L) = g i • a := by
    ext x
    rw [← sub_eq_zero]
    apply ih (fun j => g j * j x - g j * a x) _ i his
    ext y
    -- After that, it's just a chase scene.
    calc
      (∑ i in s, (g i * i x - g i * a x) • i : G -> L) y =
          (∑ i in s, g i * i x * i y) - ∑ i in s, g i * a x * i y := by simp [sub_mul]
      _ = (∑ i in insert a s, g i * i x * i y) -
            ∑ i in insert a s, g i * a x * i y := by simp [Finset.sum_insert has]
      _ = (∑ i in insert a s, g i * (i x * i y)) -
            ∑ i in insert a s, a x * (g i * i y) := by
        congrm ∑ i in insert a s, ?_ - ∑ i in insert a s, ?_
        · rw [mul_assoc]
        · rw [mul_assoc, mul_left_comm]
      _ = (∑ i in insert a s, g i • i : G -> L) (x * y) -
            a x * (∑ i in insert a s, (g i • (i : G -> L))) y := by simp [Finset.mul_sum]
      _ = 0 := by rw [hg]; simp
  -- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
  -- there is some element of the monoid on which it differs from `a`.
  have h2 (i) (his : i in s) : exists y, i y != a y := by
    by_contra! hia
    obtain rfl : i = a := MonoidHom.ext hia
    contradiction
  -- From these two facts we deduce that `g` actually vanishes on `s`,
  have h3 (i) (his : i in s) : g i = 0 := by
    let ⟨y, hy⟩ := h2 i his
    have h : g i • i y = g i • a y := congr_fun (h1 i his) y
    rw [← sub_eq_zero]; rw [← smul_sub]; rw [smul_eq_zero] at h
    exact h.resolve_right (sub_ne_zero_of_ne hy)
  -- And so, using the fact that the linear combination over `s` and over `insert a s` both
  -- vanish, we deduce that `g a = 0`.
  have h4 : g a = 0 :=
    calc
      g a = g a * 1 := (mul_one _).symm
      _ = (g a • a : G -> L) 1 := by rw [← a.map_one]; rfl
      _ = (∑ i in insert a s, g i • i : G -> L) 1 := by
        rw [Finset.sum_insert has]; rw [Finset.sum_eq_zero]; rw [add_zero]
        simp +contextual [h3]
      _ = 0 := by rw [hg]; rfl
  -- Now we're done; the last two facts together imply that `g` vanishes on every element
  -- of `insert a s`.
  exact (Finset.forall_mem_insert ..).2 ⟨h4, h3⟩

中文:
定理 linearIndependent_monoidHom
  结论: (G : 类型) [MulOne类 G] (L : 类型) [交换环 L]
  证明: by
  let := Classical.decEq (G ->* L)
  let : MulAction L L := DistribMulAction.toMulAction
  -- We prove linear independence by showing that only the trivial linear combination vanishes.
  apply linearIndependent_iff'.2
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
  intro g hg
  -- Here
  -- * `a` is a new character we will insert into the `Finset` of characters `s`,
  -- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
  -- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
  -- and it remains to prove that `g` vanishes on `insert a s`.
  -- We now make the key calculation:
  -- For any character `i` in the original `Finset`, we have `g i • i = g i • a` as functions
  -- on the monoid `G`.
  have h1 (i) (his : i in s) : (g i • i : G -> L) = g i • a := by
    ext x
    rw [← sub_eq_zero]
    apply ih (fun j => g j * j x - g j * a x) _ i his
    ext y
    -- After that, it's just a chase scene.
    calc
      (∑ i in s, (g i * i x - g i * a x) • i : G -> L) y =
          (∑ i in s, g i * i x * i y) - ∑ i in s, g i * a x * i y := by simp [sub_mul]
      _ = (∑ i in insert a s, g i * i x * i y) -
            ∑ i in insert a s, g i * a x * i y := by simp [Finset.sum_insert has]
      _ = (∑ i in insert a s, g i * (i x * i y)) -
            ∑ i in insert a s, a x * (g i * i y) := by
        congrm ∑ i in insert a s, ?_ - ∑ i in insert a s, ?_
        · rw [mul_assoc]
        · rw [mul_assoc, mul_left_comm]
      _ = (∑ i in insert a s, g i • i : G -> L) (x * y) -
            a x * (∑ i in insert a s, (g i • (i : G -> L))) y := by simp [Finset.mul_sum]
      _ = 0 := by rw [hg]; simp
  -- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
  -- there is some element of the monoid on which it differs from `a`.
  have h2 (i) (his : i in s) : exists y, i y != a y := by
    by_contra! hia
    obtain rfl : i = a := MonoidHom.ext hia
    contradiction
  -- From these two facts we deduce that `g` actually vanishes on `s`,
  have h3 (i) (his : i in s) : g i = 0 := by
    let ⟨y, hy⟩ := h2 i his
    have h : g i • i y = g i • a y := congr_fun (h1 i his) y
    rw [← sub_eq_zero]; rw [← smul_sub]; rw [smul_eq_zero] at h
    exact h.resolve_right (sub_ne_zero_of_ne hy)
  -- And so, using the fact that the linear combination over `s` and over `insert a s` both
  -- vanish, we deduce that `g a = 0`.
  have h4 : g a = 0 :=
    calc
      g a = g a * 1 := (mul_one _).symm
      _ = (g a • a : G -> L) 1 := by rw [← a.map_one]; rfl
      _ = (∑ i in insert a s, g i • i : G -> L) 1 := by
        rw [Finset.sum_insert has]; rw [Finset.sum_eq_zero]; rw [add_zero]
        simp +contextual [h3]
      _ = 0 := by rw [hg]; rfl
  -- Now we're done; the last two facts together imply that `g` vanishes on every element
  -- of `insert a s`.
  exact (Finset.forall_mem_insert ..).2 ⟨h4, h3⟩

Depends on / 依赖: Classical, Classical.decEq, DistribMulAction, DistribMulAction.toMulAction, MulAction, toMulAction
-/
theorem linearIndependent_monoidHom (G : Type*) [MulOneClass G] (L : Type*) [CommRing L]
    [IsDomain L] : LinearIndependent L (M := G -> L) (fun f => f : (G ->* L) -> G -> L) := by
  let := Classical.decEq (G ->* L)
  let : MulAction L L := DistribMulAction.toMulAction
  -- We prove linear independence by showing that only the trivial linear combination vanishes.
  apply linearIndependent_iff'.2
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
  intro g hg
  -- Here
  -- * `a` is a new character we will insert into the `Finset` of characters `s`,
  -- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
  -- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
  -- and it remains to prove that `g` vanishes on `insert a s`.
  -- We now make the key calculation:
  -- For any character `i` in the original `Finset`, we have `g i • i = g i • a` as functions
  -- on the monoid `G`.
  have h1 (i) (his : i in s) : (g i • i : G -> L) = g i • a := by
    ext x
    rw [← sub_eq_zero]
    apply ih (fun j => g j * j x - g j * a x) _ i his
    ext y
    -- After that, it's just a chase scene.
    calc
      (∑ i in s, (g i * i x - g i * a x) • i : G -> L) y =
          (∑ i in s, g i * i x * i y) - ∑ i in s, g i * a x * i y := by simp [sub_mul]
      _ = (∑ i in insert a s, g i * i x * i y) -
            ∑ i in insert a s, g i * a x * i y := by simp [Finset.sum_insert has]
      _ = (∑ i in insert a s, g i * (i x * i y)) -
            ∑ i in insert a s, a x * (g i * i y) := by
        congrm ∑ i in insert a s, ?_ - ∑ i in insert a s, ?_
        · rw [mul_assoc]
        · rw [mul_assoc, mul_left_comm]
      _ = (∑ i in insert a s, g i • i : G -> L) (x * y) -
            a x * (∑ i in insert a s, (g i • (i : G -> L))) y := by simp [Finset.mul_sum]
      _ = 0 := by rw [hg]; simp
  -- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
  -- there is some element of the monoid on which it differs from `a`.
  have h2 (i) (his : i in s) : exists y, i y != a y := by
    by_contra! hia
    obtain rfl : i = a := MonoidHom.ext hia
    contradiction
  -- From these two facts we deduce that `g` actually vanishes on `s`,
  have h3 (i) (his : i in s) : g i = 0 := by
    let ⟨y, hy⟩ := h2 i his
    have h : g i • i y = g i • a y := congr_fun (h1 i his) y
    rw [← sub_eq_zero]; rw [← smul_sub]; rw [smul_eq_zero] at h
    exact h.resolve_right (sub_ne_zero_of_ne hy)
  -- And so, using the fact that the linear combination over `s` and over `insert a s` both
  -- vanish, we deduce that `g a = 0`.
  have h4 : g a = 0 :=
    calc
      g a = g a * 1 := (mul_one _).symm
      _ = (g a • a : G -> L) 1 := by rw [← a.map_one]; rfl
      _ = (∑ i in insert a s, g i • i : G -> L) 1 := by
        rw [Finset.sum_insert has]; rw [Finset.sum_eq_zero]; rw [add_zero]
        simp +contextual [h3]
      _ = 0 := by rw [hg]; rfl
  -- Now we're done; the last two facts together imply that `g` vanishes on every element
  -- of `insert a s`.
  exact (Finset.forall_mem_insert ..).2 ⟨h4, h3⟩

end Module

section IsDomain
variable [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
  {v : ι -> M} {i : ι}

/--
lemma `linearIndependent_unique_iff` / 引理 `linearIndependent_unique_iff`

English:
lemma linearIndependent_unique_iff
  given: [Unique ι]
  statement: LinearIndependent R v ↔ v default != 0
  proof: by
  refine ⟨?_, .of_subsingleton _⟩
  simpa [linearIndependent_iff, Finsupp.linearCombination_unique, Finsupp.ext_iff,
    Unique.forall_iff, or_imp] using fun h hv => by simpa using h (.single default 1) hv

中文:
引理 linearIndependent_unique_iff
  条件: [唯一 ι]
  结论: LinearIndependent R v ↔ v default != 0
  证明: by
  refine ⟨?_, .of_subsingleton _⟩
  simpa [linearIndependent_iff, Finsupp.linearCombination_unique, Finsupp.ext_iff,
    Unique.forall_iff, or_imp] using fun h hv => by simpa using h (.single default 1) hv

Depends on / 依赖: Finsupp, Finsupp.ext_iff, Finsupp.linearCombination_unique, Unique, Unique.forall_iff, ext_iff, forall_iff, linearCombination_unique, linearIndependent_iff, of_subsingleton, or_imp, single
-/
lemma linearIndependent_unique_iff [Unique ι] : LinearIndependent R v ↔ v default != 0 := by
  refine ⟨?_, .of_subsingleton _⟩
  simpa [linearIndependent_iff, Finsupp.linearCombination_unique, Finsupp.ext_iff,
    Unique.forall_iff, or_imp] using fun h hv => by simpa using h (.single default 1) hv

variable (R) in
@[simp]
/--
theorem `linearIndepOn_singleton_iff` / 定理 `linearIndepOn_singleton_iff`

English:
theorem linearIndepOn_singleton_iff
  statement: LinearIndepOn R v {i} ↔ v i != 0
  proof: ⟨fun h => h.ne_zero rfl, .singleton⟩

@[simp]

中文:
定理 linearIndepOn_singleton_iff
  结论: LinearIndepOn R v {i} ↔ v i != 0
  证明: ⟨fun h => h.ne_zero rfl, .singleton⟩

@[simp]

Depends on / 依赖: h.ne_zero, ne_zero, singleton
-/
theorem linearIndepOn_singleton_iff : LinearIndepOn R v {i} ↔ v i != 0 :=
  ⟨fun h => h.ne_zero rfl, .singleton⟩

@[simp]
/--
theorem `linearIndependent_subsingleton_index_iff` / 定理 `linearIndependent_subsingleton_index_iff`

English:
theorem linearIndependent_subsingleton_index_iff
  given: [Subsingleton ι] (f : ι -> M)
  proof: by
  obtain (he | he) := isEmpty_or_nonempty ι
  · simp [linearIndependent_empty_type]
  obtain ⟨_⟩ := (unique_iff_subsingleton_and_nonempty (α := ι)).2 ⟨by assumption, he⟩
  rw [linearIndependent_unique_iff]
  exact ⟨fun h i => by rwa [Unique.eq_default i], fun h => h _⟩

中文:
定理 linearIndependent_subsingleton_index_iff
  条件: [子单例 ι] (f : ι -> M)
  证明: by
  obtain (he | he) := isEmpty_or_nonempty ι
  · simp [linearIndependent_empty_type]
  obtain ⟨_⟩ := (unique_iff_subsingleton_and_nonempty (α := ι)).2 ⟨by assumption, he⟩
  rw [linearIndependent_unique_iff]
  exact ⟨fun h i => by rwa [Unique.eq_default i], fun h => h _⟩

Depends on / 依赖: Unique, Unique.eq_default, eq_default, isEmpty_or_nonempty, linearIndependent_empty_type, linearIndependent_unique_iff, unique_iff_subsingleton_and_nonempty
-/
theorem linearIndependent_subsingleton_index_iff [Subsingleton ι] (f : ι -> M) :
    LinearIndependent R f ↔ forall i, f i != 0 := by
  obtain (he | he) := isEmpty_or_nonempty ι
  · simp [linearIndependent_empty_type]
  obtain ⟨_⟩ := (unique_iff_subsingleton_and_nonempty (α := ι)).2 ⟨by assumption, he⟩
  rw [linearIndependent_unique_iff]
  exact ⟨fun h i => by rwa [Unique.eq_default i], fun h => h _⟩

end IsDomain
