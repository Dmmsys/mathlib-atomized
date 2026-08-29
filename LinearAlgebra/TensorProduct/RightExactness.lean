/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Right-exactness properties of tensor product

## Modules

* `LinearMap.rTensor_surjective` asserts that when one tensors
  a surjective map on the right, one still gets a surjective linear map.
  More generally, `LinearMap.rTensor_range` computes the range of
  `LinearMap.rTensor`

* `LinearMap.lTensor_surjective` asserts that when one tensors
  a surjective map on the left, one still gets a surjective linear map.
  More generally, `LinearMap.lTensor_range` computes the range of
  `LinearMap.lTensor`

* `TensorProduct.rTensor_exact` says that when one tensors a short exact
  sequence on the right, one still gets a short exact sequence
  (right-exactness of `TensorProduct.rTensor`),
  and `rTensor.equiv` gives the LinearEquiv that follows from this
  combined with `LinearMap.rTensor_surjective`.

* `TensorProduct.lTensor_exact` says that when one tensors a short exact
  sequence on the left, one still gets a short exact sequence
  (right-exactness of `TensorProduct.rTensor`)
  and `lTensor.equiv` gives the LinearEquiv that follows from this
  combined with `LinearMap.lTensor_surjective`.

* For `N : Submodule R M`, `LinearMap.exact_subtype_mkQ N` says that
  the inclusion of the submodule and the quotient map form an exact pair,
  and `lTensor_mkQ` compute `ker (lTensor Q (N.mkQ))` and similarly for `rTensor_mkQ`

* `TensorProduct.map_ker` computes the kernel of `TensorProduct.map f g'`
  in the presence of two short exact sequences.

The proofs are those of [bourbaki1989] (chap. 2, §3, n°6)

## Algebras

In the case of a tensor product of algebras, these results can be particularized
to compute some kernels.

* `Algebra.TensorProduct.ker_map` computes the kernel of `Algebra.TensorProduct.map f g`

* `Algebra.TensorProduct.lTensor_ker` and `Algebra.TensorProduct.rTensor_ker`
  compute the kernels of `Algebra.TensorProduct.map f id` and `Algebra.TensorProduct.map id g`

## Note on implementation

* All kernels are computed by applying the first isomorphism theorem and
  establishing some isomorphisms.

* The proofs are essentially done twice,
  once for `lTensor` and then for `rTensor`.
  It is possible to apply `TensorProduct.flip` to deduce one of them
  from the other.
  However, this approach will lead to different isomorphisms,
  and it is not quicker.

* The proofs of `Ideal.map_includeLeft_eq` and `Ideal.map_includeRight_eq`
  could be easier if `I ⊗[R] B` was naturally an `A ⊗[R] B` module,
  and the map to `A ⊗[R] B` was known to be linear.
  This depends on the B-module structure on a tensor product
  whose use rapidly conflicts with everything…

## TODO

* Treat the noncommutative case

* Treat the case of modules over semirings
  (For a possible definition of an exact sequence of commutative semigroups, see
  [Grillet-1969b], Pierre-Antoine Grillet,
  *The tensor product of commutative semigroups*,
  Trans. Amer. Math. Soc. 138 (1969), 281-293, doi:10.1090/S0002-9947-1969-0237688-1 .)

-/

@[expose] public section

assert_not_exists Cardinal

section Modules

open TensorProduct LinearMap

section Semiring

variable {R : Type*} [CommSemiring R] {M N P Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    {f : M ->ₗ[R] N} (g : N ->ₗ[R] P)

/--
lemma `le_comap_range_lTensor` / 引理 `le_comap_range_lTensor`

English:
lemma le_comap_range_lTensor
  given: (q : Q)
  proof: by
  rintro x ⟨n, rfl⟩
  exact ⟨q otimesₜ[R] n, rfl⟩

中文:
引理 le_comap_range_lTensor
  条件: (q : Q)
  证明: by
  rintro x ⟨n, rfl⟩
  exact ⟨q otimesₜ[R] n, rfl⟩
-/
lemma le_comap_range_lTensor (q : Q) :
    LinearMap.range g <= (LinearMap.range (lTensor Q g)).comap (TensorProduct.mk R Q P q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨q otimesₜ[R] n, rfl⟩

/--
lemma `le_comap_range_rTensor` / 引理 `le_comap_range_rTensor`

English:
lemma le_comap_range_rTensor
  given: (q : Q)
  proof: by
  rintro x ⟨n, rfl⟩
  exact ⟨n otimesₜ[R] q, rfl⟩

中文:
引理 le_comap_range_rTensor
  条件: (q : Q)
  证明: by
  rintro x ⟨n, rfl⟩
  exact ⟨n otimesₜ[R] q, rfl⟩
-/
lemma le_comap_range_rTensor (q : Q) :
    LinearMap.range g <= (LinearMap.range (rTensor Q g)).comap
      ((TensorProduct.mk R P Q).flip q) := by
  rintro x ⟨n, rfl⟩
  exact ⟨n otimesₜ[R] q, rfl⟩

variable (Q) {g}

/--
theorem `LinearMap.lTensor_surjective` / 定理 `LinearMap.lTensor_surjective`

English:
theorem LinearMap.lTensor_surjective
  given: (hg : Function.Surjective g)
  proof: by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul q p =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨q otimesₜ[R] n, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

中文:
定理 线性映射.lTensor_surjective
  条件: (hg : 函数.满射 g)
  证明: by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul q p =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨q otimesₜ[R] n, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

Depends on / 依赖: map_add, map_zero
-/
theorem LinearMap.lTensor_surjective (hg : Function.Surjective g) :
    Function.Surjective (lTensor Q g) := by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul q p =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨q otimesₜ[R] n, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

/--
theorem `LinearMap.lTensor_range` / 定理 `LinearMap.lTensor_range`

English:
theorem LinearMap.lTensor_range
  proof: by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [lTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply lTensor_surjective
  rw [← range_eq_top]; rw [range_rangeRestrict]

中文:
定理 线性映射.lTensor_range
  证明: by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [lTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply lTensor_surjective
  rw [← range_eq_top]; rw [range_rangeRestrict]

Depends on / 依赖: Submodule, Submodule.subtype, g.rangeRestrict, lTensor_comp, lTensor_surjective, nth_rewrite, rangeRestrict, range_comp_of_range_eq_top, range_eq_top, range_rangeRestrict, subtype
-/
theorem LinearMap.lTensor_range :
    range (lTensor Q g) =
      range (lTensor Q (Submodule.subtype (range g))) := by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [lTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply lTensor_surjective
  rw [← range_eq_top]; rw [range_rangeRestrict]

/--
theorem `LinearMap.baseChange_surjective` / 定理 `LinearMap.baseChange_surjective`

English:
theorem LinearMap.baseChange_surjective
  statement: (A : Type*) [Semiring A] [Algebra R A]
  proof: by
  rw [LinearMap.baseChange_eq_ltensor]
  exact lTensor_surjective _ hg

中文:
定理 线性映射.baseChange_surjective
  结论: (A : 类型) [半环 A] [代数 R A]
  证明: by
  rw [LinearMap.baseChange_eq_ltensor]
  exact lTensor_surjective _ hg

Depends on / 依赖: LinearMap, LinearMap.baseChange_eq_ltensor, baseChange_eq_ltensor, lTensor_surjective
-/
theorem LinearMap.baseChange_surjective (A : Type*) [Semiring A] [Algebra R A]
    (hg : Function.Surjective g) : Function.Surjective (g.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact lTensor_surjective _ hg

/--
theorem `LinearMap.rTensor_surjective` / 定理 `LinearMap.rTensor_surjective`

English:
theorem LinearMap.rTensor_surjective
  given: (hg : Function.Surjective g)
  proof: by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul p q =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨n otimesₜ[R] q, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

中文:
定理 线性映射.rTensor_surjective
  条件: (hg : 函数.满射 g)
  证明: by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul p q =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨n otimesₜ[R] q, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

Depends on / 依赖: map_add, map_zero
-/
theorem LinearMap.rTensor_surjective (hg : Function.Surjective g) :
    Function.Surjective (rTensor Q g) := by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul p q =>
    obtain ⟨n, rfl⟩ := hg p
    exact ⟨n otimesₜ[R] q, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

/--
theorem `LinearMap.rTensor_range` / 定理 `LinearMap.rTensor_range`

English:
theorem LinearMap.rTensor_range
  proof: by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [rTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply rTensor_surjective
  rw [← range_eq_top]; rw [range_rangeRestrict]

中文:
定理 线性映射.rTensor_range
  证明: by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [rTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply rTensor_surjective
  rw [← range_eq_top]; rw [range_rangeRestrict]

Depends on / 依赖: Submodule, Submodule.subtype, g.rangeRestrict, nth_rewrite, rTensor_comp, rTensor_surjective, rangeRestrict, range_comp_of_range_eq_top, range_eq_top, range_rangeRestrict, subtype
-/
theorem LinearMap.rTensor_range :
    range (rTensor Q g) =
      range (rTensor Q (Submodule.subtype (range g))) := by
  have : g = (Submodule.subtype _).comp g.rangeRestrict := rfl
  nth_rewrite 1 [this]
  rw [rTensor_comp]
  apply range_comp_of_range_eq_top
  rw [range_eq_top]
  apply rTensor_surjective
  rw [← range_eq_top]; rw [range_rangeRestrict]

/--
lemma `LinearMap.rTensor_exact_iff_lTensor_exact` / 引理 `LinearMap.rTensor_exact_iff_lTensor_exact`

English:
lemma LinearMap.rTensor_exact_iff_lTensor_exact
  proof: Function.Exact.iff_of_ladder_linearEquiv (e₁ := TensorProduct.comm _ _ _)
    (e₂ := TensorProduct.comm _ _ _) (e₃ := TensorProduct.comm _ _ _)
    (by ext; simp) (by ext; simp)

中文:
引理 线性映射.rTensor_exact_iff_lTensor_exact
  证明: Function.Exact.iff_of_ladder_linearEquiv (e₁ := TensorProduct.comm _ _ _)
    (e₂ := TensorProduct.comm _ _ _) (e₃ := TensorProduct.comm _ _ _)
    (by ext; simp) (by ext; simp)

Depends on / 依赖: Function, Function.Exact.iff_of_ladder_linearEquiv, TensorProduct, TensorProduct.comm, iff_of_ladder_linearEquiv
-/
lemma LinearMap.rTensor_exact_iff_lTensor_exact :
    Function.Exact (f.rTensor Q) (g.rTensor Q) ↔
    Function.Exact (f.lTensor Q) (g.lTensor Q) :=
  Function.Exact.iff_of_ladder_linearEquiv (e₁ := TensorProduct.comm _ _ _)
    (e₂ := TensorProduct.comm _ _ _) (e₃ := TensorProduct.comm _ _ _)
    (by ext; simp) (by ext; simp)

variable (hg : Function.Surjective g)
    {N' P' : Type*} [AddCommMonoid N'] [AddCommMonoid P'] [Module R N'] [Module R P']
    {g' : N' ->ₗ[R] P'} (hg' : Function.Surjective g')

include hg hg' in
/--
theorem `TensorProduct.map_surjective` / 定理 `TensorProduct.map_surjective`

English:
theorem TensorProduct.map_surjective
  statement: Function.Surjective (TensorProduct.map g g')
  proof: by
  rw [← lTensor_comp_rTensor]; rw [coe_comp]
  exact Function.Surjective.comp (lTensor_surjective _ hg') (rTensor_surjective _ hg)

中文:
定理 张量积.map_surjective
  结论: 函数.满射 (张量积.map g g')
  证明: by
  rw [← lTensor_comp_rTensor]; rw [coe_comp]
  exact Function.Surjective.comp (lTensor_surjective _ hg') (rTensor_surjective _ hg)

Depends on / 依赖: Function, Function.Surjective.comp, Surjective, coe_comp, lTensor_comp_rTensor, lTensor_surjective, rTensor_surjective
-/
theorem TensorProduct.map_surjective : Function.Surjective (TensorProduct.map g g') := by
  rw [← lTensor_comp_rTensor]; rw [coe_comp]
  exact Function.Surjective.comp (lTensor_surjective _ hg') (rTensor_surjective _ hg)

end Semiring

variable {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]

open Function

variable {f : M ->ₗ[R] N} {g : N ->ₗ[R] P}
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    (hfg : Exact f g) (hg : Function.Surjective g)

/--
Definition of `lTensor.toFun` / `lTensor.toFun` 的定义

English:
definition lTensor.toFun
  signature: (hfg : Exact f g)
  body: Submodule.liftQ _ (lTensor Q g) by
    rw [LinearMap.range_le_iff_comap]; rw [← LinearMap.ker_comp]; rw [← lTensor_comp]; rw [hfg.linearMap_comp_eq_zero]; rw [lTensor_zero]; rw [ker_zero]

中文:
定义 lTensor.toFun
  签名: (hfg : 正合 f g)
  定义体: Submodule.liftQ _ (lTensor Q g) by
    rw [LinearMap.range_le_iff_comap]; rw [← LinearMap.ker_comp]; rw [← lTensor_comp]; rw [hfg.linearMap_comp_eq_zero]; rw [lTensor_zero]; rw [ker_zero]

Depends on / 依赖: LinearMap, LinearMap.ker_comp, LinearMap.range_le_iff_comap, Submodule, Submodule.liftQ, hfg.linearMap_comp_eq_zero, ker_comp, ker_zero, lTensor, lTensor_comp, lTensor_zero, linearMap_comp_eq_zero, range_le_iff_comap
-/
noncomputable def lTensor.toFun (hfg : Exact f g) :
    Q otimes[R] N ⧸ LinearMap.range (lTensor Q f) ->ₗ[R] Q otimes[R] P :=
Submodule.liftQ _ (lTensor Q g) by
    rw [LinearMap.range_le_iff_comap]; rw [← LinearMap.ker_comp]; rw [← lTensor_comp]; rw [hfg.linearMap_comp_eq_zero]; rw [lTensor_zero]; rw [ker_zero]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lTensor.inverse_of_rightInverse` / `lTensor.inverse_of_rightInverse` 的定义

English:
definition lTensor.inverse_of_rightInverse
  signature: {h : P -> N} (hfg : Exact f g)
  body: TensorProduct.lift LinearMap.flip {
    toFun := fun p => Submodule.mkQ _ ∘ₗ ((TensorProduct.mk R _ _).flip (h p))
map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change q otimesₜ[R] (h (p + p')) - (q otimesₜ[R] (h p) + q otimesₜ[R] (h p')) in range (lTensor Q f)
      rw [← TensorProduct.tmul_add]; rw [← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change q otimesₜ[R] (h (r • p)) - r • q otimesₜ[R] (h p) in range (lTensor Q f)
      rw [← TensorProduct.tmul_smul]; rw [← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }

中文:
定义 lTensor.inverse_of_rightInverse
  签名: {h : P -> N} (hfg : 正合 f g)
  定义体: TensorProduct.lift LinearMap.flip {
    toFun := fun p => Submodule.mkQ _ ∘ₗ ((TensorProduct.mk R _ _).flip (h p))
map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change q otimesₜ[R] (h (p + p')) - (q otimesₜ[R] (h p) + q otimesₜ[R] (h p')) in range (lTensor Q f)
      rw [← TensorProduct.tmul_add]; rw [← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change q otimesₜ[R] (h (r • p)) - r • q otimesₜ[R] (h p) in range (lTensor Q f)
      rw [← TensorProduct.tmul_smul]; rw [← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }

Depends on / 依赖: LinearMa, LinearMap, LinearMap.ext, LinearMap.flip, Quotient, Submodule, Submodule.Quotient.eq, Submodule.mkQ, TensorProduct, TensorProduct.lift, TensorProduct.mk, TensorProduct.tmul_add, TensorProduct.tmul_sub, exact_iff, lTensor, le_comap_range_lTensor, map_add, map_smul, map_sub, mem_ker
-/
noncomputable def lTensor.inverse_of_rightInverse {h : P -> N} (hfg : Exact f g)
    (hgh : Function.RightInverse h g) :
    Q otimes[R] P ->ₗ[R] Q otimes[R] N ⧸ LinearMap.range (lTensor Q f) :=
TensorProduct.lift LinearMap.flip {
    toFun := fun p => Submodule.mkQ _ ∘ₗ ((TensorProduct.mk R _ _).flip (h p))
map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change q otimesₜ[R] (h (p + p')) - (q otimesₜ[R] (h p) + q otimesₜ[R] (h p')) in range (lTensor Q f)
      rw [← TensorProduct.tmul_add]; rw [← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change q otimesₜ[R] (h (r • p)) - r • q otimesₜ[R] (h p) in range (lTensor Q f)
      rw [← TensorProduct.tmul_smul]; rw [← TensorProduct.tmul_sub]
      apply le_comap_range_lTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }

/--
lemma `lTensor.inverse_of_rightInverse_apply` / 引理 `lTensor.inverse_of_rightInverse_apply`

English:
lemma lTensor.inverse_of_rightInverse_apply
  proof: by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  suffices Submodule.Quotient.mk (n otimesₜ[R] h (g q)) = Submodule.Quotient.mk (n otimesₜ[R] q) by
    simpa
  rw [Submodule.Quotient.eq]; rw [← TensorProduct.tmul_sub]
  apply le_comap_range_lTensor f n
  rw [← hfg]; rw [mem_ker]; rw [map_sub]; rw [sub_eq_zero]; rw [hgh]

中文:
引理 lTensor.inverse_of_rightInverse_apply
  证明: by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  suffices Submodule.Quotient.mk (n otimesₜ[R] h (g q)) = Submodule.Quotient.mk (n otimesₜ[R] q) by
    simpa
  rw [Submodule.Quotient.eq]; rw [← TensorProduct.tmul_sub]
  apply le_comap_range_lTensor f n
  rw [← hfg]; rw [mem_ker]; rw [map_sub]; rw [sub_eq_zero]; rw [hgh]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, LinearMap.congr_fun, LinearMap.range, Quotient, Submodule, Submodule.Quotient.eq, Submodule.Quotient.mk, Submodule.mkQ_apply, TensorProduct, TensorProduct.ext, TensorProduct.tmul_sub, comp_apply, congr_fun, exact_iff, lTensor, le_comap_range_lTensor, map_sub, mem_ker, mkQ_apply
-/
lemma lTensor.inverse_of_rightInverse_apply
    {h : P -> N} (hgh : Function.RightInverse h g) (y : Q otimes[R] N) :
    (lTensor.inverse_of_rightInverse Q hfg hgh) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  suffices Submodule.Quotient.mk (n otimesₜ[R] h (g q)) = Submodule.Quotient.mk (n otimesₜ[R] q) by
    simpa
  rw [Submodule.Quotient.eq]; rw [← TensorProduct.tmul_sub]
  apply le_comap_range_lTensor f n
  rw [← hfg]; rw [mem_ker]; rw [map_sub]; rw [sub_eq_zero]; rw [hgh]

/--
lemma `lTensor.inverse_of_rightInverse_comp_lTensor` / 引理 `lTensor.inverse_of_rightInverse_comp_lTensor`

English:
lemma lTensor.inverse_of_rightInverse_comp_lTensor
  proof: by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    lTensor.inverse_of_rightInverse_apply]

中文:
引理 lTensor.inverse_of_rightInverse_comp_lTensor
  证明: by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    lTensor.inverse_of_rightInverse_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.ext_iff, LinearMap.range, Submodule, Submodule.mkQ_apply, coe_comp, comp_apply, ext_iff, inverse_of_rightInverse_apply, lTensor, lTensor.inverse_of_rightInverse_apply, mkQ_apply
-/
lemma lTensor.inverse_of_rightInverse_comp_lTensor
    {h : P -> N} (hgh : Function.RightInverse h g) :
    (lTensor.inverse_of_rightInverse Q hfg hgh).comp (lTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (lTensor Q f)) := by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    lTensor.inverse_of_rightInverse_apply]

/-- The inverse map in `lTensor.equiv` -/
noncomputable
/--
Definition of `lTensor.inverse` / `lTensor.inverse` 的定义

English:
definition lTensor.inverse
  signature: :
  body: lTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

中文:
定义 lTensor.inverse
  签名: :
  定义体: lTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

Depends on / 依赖: Function, Function.rightInverse_surjInv, inverse_of_rightInverse, lTensor, lTensor.inverse_of_rightInverse, rightInverse_surjInv
-/
def lTensor.inverse :
    Q otimes[R] P ->ₗ[R] Q otimes[R] N ⧸ LinearMap.range (lTensor Q f) :=
  lTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

/--
lemma `lTensor.inverse_apply` / 引理 `lTensor.inverse_apply`

English:
lemma lTensor.inverse_apply
  given: (y : Q otimes[R] N)
  proof: by
  rw [lTensor.inverse]; rw [lTensor.inverse_of_rightInverse_apply]

中文:
引理 lTensor.inverse_apply
  条件: (y : Q otimes[R] N)
  证明: by
  rw [lTensor.inverse]; rw [lTensor.inverse_of_rightInverse_apply]

Depends on / 依赖: LinearMap, LinearMap.range, inverse, inverse_of_rightInverse_apply, lTensor, lTensor.inverse, lTensor.inverse_of_rightInverse_apply
-/
lemma lTensor.inverse_apply (y : Q otimes[R] N) :
    (lTensor.inverse Q hfg hg) ((lTensor Q g) y) =
      Submodule.Quotient.mk (p := (LinearMap.range (lTensor Q f))) y := by
  rw [lTensor.inverse]; rw [lTensor.inverse_of_rightInverse_apply]

/--
lemma `lTensor.inverse_comp_lTensor` / 引理 `lTensor.inverse_comp_lTensor`

English:
lemma lTensor.inverse_comp_lTensor
  proof: by
  rw [lTensor.inverse]; rw [lTensor.inverse_of_rightInverse_comp_lTensor]

中文:
引理 lTensor.inverse_comp_lTensor
  证明: by
  rw [lTensor.inverse]; rw [lTensor.inverse_of_rightInverse_comp_lTensor]

Depends on / 依赖: LinearMap, LinearMap.range, inverse, inverse_of_rightInverse_comp_lTensor, lTensor, lTensor.inverse, lTensor.inverse_of_rightInverse_comp_lTensor
-/
lemma lTensor.inverse_comp_lTensor :
    (lTensor.inverse Q hfg hg).comp (lTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (lTensor Q f)) := by
  rw [lTensor.inverse]; rw [lTensor.inverse_of_rightInverse_comp_lTensor]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `Q ⊗ N ⧸ (image of ker f)` to `Q ⊗ P`
  (computably, given a right inverse) -/
noncomputable
/--
Definition of `lTensor.linearEquiv_of_rightInverse` / `lTensor.linearEquiv_of_rightInverse` 的定义

English:
definition lTensor.linearEquiv_of_rightInverse
  signature: {h : P -> N} (hgh : Function.RightInverse h g)
  body: {
  toLinearMap := lTensor.toFun Q hfg
  invFun := lTensor.inverse_of_rightInverse Q hfg hgh
  left_inv := fun y => by
    simp only [lTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, lTensor.inverse_of_rightInverse_apply]
  right_inv := fun z => by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := lTensor_surjective Q (hgh.surjective) z
    rw [lTensor.inverse_of_rightInverse_apply]
    simp only [lTensor.toFun, Submodule.liftQ_apply] }

中文:
定义 lTensor.linearEquiv_of_rightInverse
  签名: {h : P -> N} (hgh : 函数.右逆 h g)
  定义体: {
  toLinearMap := lTensor.toFun Q hfg
  invFun := lTensor.inverse_of_rightInverse Q hfg hgh
  left_inv := fun y => by
    simp only [lTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, lTensor.inverse_of_rightInverse_apply]
  right_inv := fun z => by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := lTensor_surjective Q (hgh.surjective) z
    rw [lTensor.inverse_of_rightInverse_apply]
    simp only [lTensor.toFun, Submodule.liftQ_apply] }
-/
def lTensor.linearEquiv_of_rightInverse {h : P -> N} (hgh : Function.RightInverse h g) :
    ((Q otimes[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q otimes[R] P) := {
  toLinearMap := lTensor.toFun Q hfg
  invFun := lTensor.inverse_of_rightInverse Q hfg hgh
  left_inv := fun y => by
    simp only [lTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, lTensor.inverse_of_rightInverse_apply]
  right_inv := fun z => by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := lTensor_surjective Q (hgh.surjective) z
    rw [lTensor.inverse_of_rightInverse_apply]
    simp only [lTensor.toFun, Submodule.liftQ_apply] }

/--
Definition of `lTensor.equiv` / `lTensor.equiv` 的定义

English:
definition lTensor.equiv
  signature: :
  body: lTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

include hfg hg in

中文:
定义 lTensor.equiv
  签名: :
  定义体: lTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

include hfg hg in

Depends on / 依赖: Function, Function.rightInverse_surjInv, lTensor, lTensor.linearEquiv_of_rightInverse, linearEquiv_of_rightInverse, rightInverse_surjInv
-/
noncomputable def lTensor.equiv :
    ((Q otimes[R] N) ⧸ (LinearMap.range (lTensor Q f))) ≃ₗ[R] (Q otimes[R] P) :=
  lTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

include hfg hg in
/--
theorem `lTensor_exact` / 定理 `lTensor_exact`

English:
theorem lTensor_exact
  statement: Exact (lTensor Q f) (lTensor Q g)
  proof: by
  rw [exact_iff]; rw [← Submodule.ker_mkQ (p := range (lTensor Q f))]; rw [← lTensor.inverse_comp_lTensor Q hfg hg]
  apply symm
  apply LinearMap.ker_comp_of_ker_eq_bot
  rw [LinearMap.ker_eq_bot]
  exact (lTensor.equiv Q hfg hg).symm.injective

中文:
定理 lTensor_exact
  结论: 正合 (lTensor Q f) (lTensor Q g)
  证明: by
  rw [exact_iff]; rw [← Submodule.ker_mkQ (p := range (lTensor Q f))]; rw [← lTensor.inverse_comp_lTensor Q hfg hg]
  apply symm
  apply LinearMap.ker_comp_of_ker_eq_bot
  rw [LinearMap.ker_eq_bot]
  exact (lTensor.equiv Q hfg hg).symm.injective

Depends on / 依赖: LinearMap, LinearMap.ker_comp_of_ker_eq_bot, LinearMap.ker_eq_bot, Submodule, Submodule.ker_mkQ, exact_iff, injective, inverse_comp_lTensor, ker_comp_of_ker_eq_bot, ker_eq_bot, ker_mkQ, lTensor, lTensor.equiv, lTensor.inverse_comp_lTensor, symm.injective
-/
theorem lTensor_exact : Exact (lTensor Q f) (lTensor Q g) := by
  rw [exact_iff]; rw [← Submodule.ker_mkQ (p := range (lTensor Q f))]; rw [← lTensor.inverse_comp_lTensor Q hfg hg]
  apply symm
  apply LinearMap.ker_comp_of_ker_eq_bot
  rw [LinearMap.ker_eq_bot]
  exact (lTensor.equiv Q hfg hg).symm.injective

/--
lemma `lTensor_mkQ` / 引理 `lTensor_mkQ`

English:
lemma lTensor_mkQ
  given: (N : Submodule R M)
  proof: by
  rw [← exact_iff]
  exact lTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

中文:
引理 lTensor_mkQ
  条件: (N : 子模 R M)
  证明: by
  rw [← exact_iff]
  exact lTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

Depends on / 依赖: LinearMap, LinearMap.exact_subtype_mkQ, Submodule, Submodule.mkQ_surjective, exact_iff, exact_subtype_mkQ, lTensor_exact, mkQ_surjective
-/
lemma lTensor_mkQ (N : Submodule R M) :
    ker (lTensor Q N.mkQ) = range (lTensor Q N.subtype) := by
  rw [← exact_iff]
  exact lTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

/--
Definition of `rTensor.toFun` / `rTensor.toFun` 的定义

English:
definition rTensor.toFun
  signature: (hfg : Exact f g)
  body: Submodule.liftQ _ (rTensor Q g) by
    rw [range_le_iff_comap]; rw [← ker_comp]; rw [← rTensor_comp]; rw [hfg.linearMap_comp_eq_zero]; rw [rTensor_zero]; rw [ker_zero]

中文:
定义 rTensor.toFun
  签名: (hfg : 正合 f g)
  定义体: Submodule.liftQ _ (rTensor Q g) by
    rw [range_le_iff_comap]; rw [← ker_comp]; rw [← rTensor_comp]; rw [hfg.linearMap_comp_eq_zero]; rw [rTensor_zero]; rw [ker_zero]

Depends on / 依赖: Submodule, Submodule.liftQ, hfg.linearMap_comp_eq_zero, ker_comp, ker_zero, linearMap_comp_eq_zero, rTensor, rTensor_comp, rTensor_zero, range_le_iff_comap
-/
noncomputable def rTensor.toFun (hfg : Exact f g) :
    N otimes[R] Q ⧸ range (rTensor Q f) ->ₗ[R] P otimes[R] Q :=
Submodule.liftQ _ (rTensor Q g) by
    rw [range_le_iff_comap]; rw [← ker_comp]; rw [← rTensor_comp]; rw [hfg.linearMap_comp_eq_zero]; rw [rTensor_zero]; rw [ker_zero]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `rTensor.inverse_of_rightInverse` / `rTensor.inverse_of_rightInverse` 的定义

English:
definition rTensor.inverse_of_rightInverse
  signature: {h : P -> N} (hfg : Exact f g)
  body: TensorProduct.lift {
    toFun := fun p => Submodule.mkQ _ ∘ₗ TensorProduct.mk R _ _ (h p)
map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change h (p + p') otimesₜ[R] q - (h p otimesₜ[R] q + h p' otimesₜ[R] q) in range (rTensor Q f)
      rw [← TensorProduct.add_tmul]; rw [← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change h (r • p) otimesₜ[R] q - r • h p otimesₜ[R] q in range (rTensor Q f)
      rw [TensorProduct.smul_tmul']; rw [← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }

中文:
定义 rTensor.inverse_of_rightInverse
  签名: {h : P -> N} (hfg : 正合 f g)
  定义体: TensorProduct.lift {
    toFun := fun p => Submodule.mkQ _ ∘ₗ TensorProduct.mk R _ _ (h p)
map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change h (p + p') otimesₜ[R] q - (h p otimesₜ[R] q + h p' otimesₜ[R] q) in range (rTensor Q f)
      rw [← TensorProduct.add_tmul]; rw [← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change h (r • p) otimesₜ[R] q - r • h p otimesₜ[R] q in range (rTensor Q f)
      rw [TensorProduct.smul_tmul']; rw [← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }

Depends on / 依赖: LinearMap, LinearMap.ext, Quotient, Submodule, Submodule.Quot, Submodule.Quotient.eq, Submodule.mkQ, TensorProduct, TensorProduct.add_tmul, TensorProduct.lift, TensorProduct.mk, TensorProduct.sub_tmul, add_tmul, exact_iff, le_comap_range_rTensor, map_add, map_smul, map_sub, mem_ker, rTensor
-/
noncomputable def rTensor.inverse_of_rightInverse {h : P -> N} (hfg : Exact f g)
    (hgh : Function.RightInverse h g) :
    P otimes[R] Q ->ₗ[R] N otimes[R] Q ⧸ LinearMap.range (rTensor Q f) :=
  TensorProduct.lift {
    toFun := fun p => Submodule.mkQ _ ∘ₗ TensorProduct.mk R _ _ (h p)
map_add' := fun p p' => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change h (p + p') otimesₜ[R] q - (h p otimesₜ[R] q + h p' otimesₜ[R] q) in range (rTensor Q f)
      rw [← TensorProduct.add_tmul]; rw [← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_add, hgh _, sub_self]
map_smul' := fun r p => LinearMap.ext fun q => (Submodule.Quotient.eq _).mpr by
      change h (r • p) otimesₜ[R] q - r • h p otimesₜ[R] q in range (rTensor Q f)
      rw [TensorProduct.smul_tmul']; rw [← TensorProduct.sub_tmul]
      apply le_comap_range_rTensor f
      rw [exact_iff] at hfg
      simp only [← hfg, mem_ker, map_sub, map_smul, hgh _, sub_self] }

/--
lemma `rTensor.inverse_of_rightInverse_apply` / 引理 `rTensor.inverse_of_rightInverse_apply`

English:
lemma rTensor.inverse_of_rightInverse_apply
  proof: by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  suffices Submodule.Quotient.mk (h (g n) otimesₜ[R] q) = Submodule.Quotient.mk (n otimesₜ[R] q) by simpa
  rw [Submodule.Quotient.eq]; rw [← TensorProduct.sub_tmul]
  apply le_comap_range_rTensor f
  rw [← hfg]; rw [mem_ker]; rw [map_sub]; rw [sub_eq_zero]; rw [hgh]

中文:
引理 rTensor.inverse_of_rightInverse_apply
  证明: by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  suffices Submodule.Quotient.mk (h (g n) otimesₜ[R] q) = Submodule.Quotient.mk (n otimesₜ[R] q) by simpa
  rw [Submodule.Quotient.eq]; rw [← TensorProduct.sub_tmul]
  apply le_comap_range_rTensor f
  rw [← hfg]; rw [mem_ker]; rw [map_sub]; rw [sub_eq_zero]; rw [hgh]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, LinearMap.congr_fun, LinearMap.range, Quotient, Submodule, Submodule.Quotient.eq, Submodule.Quotient.mk, Submodule.mkQ_apply, TensorProduct, TensorProduct.ext, TensorProduct.sub_tmul, comp_apply, congr_fun, exact_iff, le_comap_range_rTensor, map_sub, mem_ker, mkQ_apply, rTensor
-/
lemma rTensor.inverse_of_rightInverse_apply
    {h : P -> N} (hgh : Function.RightInverse h g) (y : N otimes[R] Q) :
    (rTensor.inverse_of_rightInverse Q hfg hgh) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  simp only [← LinearMap.comp_apply, ← Submodule.mkQ_apply]
  rw [exact_iff] at hfg
  apply LinearMap.congr_fun
  apply TensorProduct.ext'
  intro n q
  suffices Submodule.Quotient.mk (h (g n) otimesₜ[R] q) = Submodule.Quotient.mk (n otimesₜ[R] q) by simpa
  rw [Submodule.Quotient.eq]; rw [← TensorProduct.sub_tmul]
  apply le_comap_range_rTensor f
  rw [← hfg]; rw [mem_ker]; rw [map_sub]; rw [sub_eq_zero]; rw [hgh]

/--
lemma `rTensor.inverse_of_rightInverse_comp_rTensor` / 引理 `rTensor.inverse_of_rightInverse_comp_rTensor`

English:
lemma rTensor.inverse_of_rightInverse_comp_rTensor
  proof: by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    rTensor.inverse_of_rightInverse_apply]

中文:
引理 rTensor.inverse_of_rightInverse_comp_rTensor
  证明: by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    rTensor.inverse_of_rightInverse_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.ext_iff, LinearMap.range, Submodule, Submodule.mkQ_apply, coe_comp, comp_apply, ext_iff, inverse_of_rightInverse_apply, mkQ_apply, rTensor, rTensor.inverse_of_rightInverse_apply
-/
lemma rTensor.inverse_of_rightInverse_comp_rTensor
    {h : P -> N} (hgh : Function.RightInverse h g) :
    (rTensor.inverse_of_rightInverse Q hfg hgh).comp (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  rw [LinearMap.ext_iff]
  intro y
  simp only [coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    rTensor.inverse_of_rightInverse_apply]

/-- The inverse map in `rTensor.equiv` -/
noncomputable
/--
Definition of `rTensor.inverse` / `rTensor.inverse` 的定义

English:
definition rTensor.inverse
  signature: :
  body: rTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

中文:
定义 rTensor.inverse
  签名: :
  定义体: rTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

Depends on / 依赖: Function, Function.rightInverse_surjInv, inverse_of_rightInverse, rTensor, rTensor.inverse_of_rightInverse, rightInverse_surjInv
-/
def rTensor.inverse :
    P otimes[R] Q ->ₗ[R] N otimes[R] Q ⧸ LinearMap.range (rTensor Q f) :=
  rTensor.inverse_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

/--
lemma `rTensor.inverse_apply` / 引理 `rTensor.inverse_apply`

English:
lemma rTensor.inverse_apply
  given: (y : N otimes[R] Q)
  proof: by
  rw [rTensor.inverse]; rw [rTensor.inverse_of_rightInverse_apply]

中文:
引理 rTensor.inverse_apply
  条件: (y : N otimes[R] Q)
  证明: by
  rw [rTensor.inverse]; rw [rTensor.inverse_of_rightInverse_apply]

Depends on / 依赖: LinearMap, LinearMap.range, inverse, inverse_of_rightInverse_apply, rTensor, rTensor.inverse, rTensor.inverse_of_rightInverse_apply
-/
lemma rTensor.inverse_apply (y : N otimes[R] Q) :
    (rTensor.inverse Q hfg hg) ((rTensor Q g) y) =
      Submodule.Quotient.mk (p := LinearMap.range (rTensor Q f)) y := by
  rw [rTensor.inverse]; rw [rTensor.inverse_of_rightInverse_apply]

/--
lemma `rTensor.inverse_comp_rTensor` / 引理 `rTensor.inverse_comp_rTensor`

English:
lemma rTensor.inverse_comp_rTensor
  proof: by
  rw [rTensor.inverse]; rw [rTensor.inverse_of_rightInverse_comp_rTensor]

中文:
引理 rTensor.inverse_comp_rTensor
  证明: by
  rw [rTensor.inverse]; rw [rTensor.inverse_of_rightInverse_comp_rTensor]

Depends on / 依赖: LinearMap, LinearMap.range, inverse, inverse_of_rightInverse_comp_rTensor, rTensor, rTensor.inverse, rTensor.inverse_of_rightInverse_comp_rTensor
-/
lemma rTensor.inverse_comp_rTensor :
    (rTensor.inverse Q hfg hg).comp (rTensor Q g) =
      Submodule.mkQ (p := LinearMap.range (rTensor Q f)) := by
  rw [rTensor.inverse]; rw [rTensor.inverse_of_rightInverse_comp_rTensor]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- For a surjective `f : N →ₗ[R] P`,
  the natural equivalence between `N ⊗[R] Q ⧸ (range (rTensor Q f))` and `P ⊗[R] Q`
  (computably, given a right inverse) -/
noncomputable
/--
Definition of `rTensor.linearEquiv_of_rightInverse` / `rTensor.linearEquiv_of_rightInverse` 的定义

English:
definition rTensor.linearEquiv_of_rightInverse
  signature: {h : P -> N} (hgh : Function.RightInverse h g)
  body: {
  toLinearMap := rTensor.toFun Q hfg
  invFun := rTensor.inverse_of_rightInverse Q hfg hgh
  left_inv := fun y => by
    simp only [rTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, rTensor.inverse_of_rightInverse_apply]
  right_inv := fun z => by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := rTensor_surjective Q hgh.surjective z
    rw [rTensor.inverse_of_rightInverse_apply]
    simp only [rTensor.toFun, Submodule.liftQ_apply] }

中文:
定义 rTensor.linearEquiv_of_rightInverse
  签名: {h : P -> N} (hgh : 函数.右逆 h g)
  定义体: {
  toLinearMap := rTensor.toFun Q hfg
  invFun := rTensor.inverse_of_rightInverse Q hfg hgh
  left_inv := fun y => by
    simp only [rTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, rTensor.inverse_of_rightInverse_apply]
  right_inv := fun z => by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := rTensor_surjective Q hgh.surjective z
    rw [rTensor.inverse_of_rightInverse_apply]
    simp only [rTensor.toFun, Submodule.liftQ_apply] }
-/
def rTensor.linearEquiv_of_rightInverse {h : P -> N} (hgh : Function.RightInverse h g) :
    ((N otimes[R] Q) ⧸ (range (rTensor Q f))) ≃ₗ[R] (P otimes[R] Q) := {
  toLinearMap := rTensor.toFun Q hfg
  invFun := rTensor.inverse_of_rightInverse Q hfg hgh
  left_inv := fun y => by
    simp only [rTensor.toFun, AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, rTensor.inverse_of_rightInverse_apply]
  right_inv := fun z => by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom]
    obtain ⟨y, rfl⟩ := rTensor_surjective Q hgh.surjective z
    rw [rTensor.inverse_of_rightInverse_apply]
    simp only [rTensor.toFun, Submodule.liftQ_apply] }

/--
Definition of `rTensor.equiv` / `rTensor.equiv` 的定义

English:
definition rTensor.equiv
  signature: :
  body: rTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

include hfg hg in

中文:
定义 rTensor.equiv
  签名: :
  定义体: rTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

include hfg hg in

Depends on / 依赖: Function, Function.rightInverse_surjInv, linearEquiv_of_rightInverse, rTensor, rTensor.linearEquiv_of_rightInverse, rightInverse_surjInv
-/
noncomputable def rTensor.equiv :
    ((N otimes[R] Q) ⧸ (LinearMap.range (rTensor Q f))) ≃ₗ[R] (P otimes[R] Q) :=
  rTensor.linearEquiv_of_rightInverse Q hfg (Function.rightInverse_surjInv hg)

include hfg hg in
/--
theorem `rTensor_exact` / 定理 `rTensor_exact`

English:
theorem rTensor_exact
  statement: Exact (rTensor Q f) (rTensor Q g)
  proof: by
  rw [rTensor_exact_iff_lTensor_exact]
  exact lTensor_exact Q hfg hg

中文:
定理 rTensor_exact
  结论: 正合 (rTensor Q f) (rTensor Q g)
  证明: by
  rw [rTensor_exact_iff_lTensor_exact]
  exact lTensor_exact Q hfg hg

Depends on / 依赖: lTensor_exact, rTensor_exact_iff_lTensor_exact
-/
theorem rTensor_exact : Exact (rTensor Q f) (rTensor Q g) := by
  rw [rTensor_exact_iff_lTensor_exact]
  exact lTensor_exact Q hfg hg

/--
lemma `rTensor_mkQ` / 引理 `rTensor_mkQ`

English:
lemma rTensor_mkQ
  given: (N : Submodule R M)
  proof: by
  rw [← exact_iff]
  exact rTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

中文:
引理 rTensor_mkQ
  条件: (N : 子模 R M)
  证明: by
  rw [← exact_iff]
  exact rTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

Depends on / 依赖: LinearMap, LinearMap.exact_subtype_mkQ, Submodule, Submodule.mkQ_surjective, exact_iff, exact_subtype_mkQ, mkQ_surjective, rTensor_exact
-/
lemma rTensor_mkQ (N : Submodule R M) :
    ker (rTensor Q N.mkQ) = range (rTensor Q N.subtype) := by
  rw [← exact_iff]
  exact rTensor_exact Q (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)

open Submodule LinearEquiv in
/--
lemma `LinearMap.ker_tensorProductMk` / 引理 `LinearMap.ker_tensorProductMk`

English:
lemma LinearMap.ker_tensorProductMk
  given: {I : Ideal R}
  proof: by
  apply comap_injective_of_surjective (TensorProduct.lid R Q).surjective
  rw [← ker_comp]
  convert! rTensor_mkQ Q I
  · ext; simp
  rw [comap_equiv_eq_map_symm]; rw [map_symm_eq_iff]; rw [map_range_rTensor_subtype_lid]

中文:
引理 线性映射.ker_tensorProductMk
  条件: {I : 理想 R}
  证明: by
  apply comap_injective_of_surjective (TensorProduct.lid R Q).surjective
  rw [← ker_comp]
  convert! rTensor_mkQ Q I
  · ext; simp
  rw [comap_equiv_eq_map_symm]; rw [map_symm_eq_iff]; rw [map_range_rTensor_subtype_lid]

Depends on / 依赖: TensorProduct, TensorProduct.lid, comap_equiv_eq_map_symm, comap_injective_of_surjective, convert, ker_comp, map_range_rTensor_subtype_lid, map_symm_eq_iff, rTensor_mkQ, surjective
-/
lemma LinearMap.ker_tensorProductMk {I : Ideal R} :
    ker (TensorProduct.mk R (R ⧸ I) Q 1) = I • ⊤ := by
  apply comap_injective_of_surjective (TensorProduct.lid R Q).surjective
  rw [← ker_comp]
  convert! rTensor_mkQ Q I
  · ext; simp
  rw [comap_equiv_eq_map_symm]; rw [map_symm_eq_iff]; rw [map_range_rTensor_subtype_lid]

variable {M' N' P' : Type*}
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [Module R M'] [Module R N'] [Module R P']
    {f' : M' ->ₗ[R] N'} {g' : N' ->ₗ[R] P'}
    (hfg' : Exact f' g') (hg' : Function.Surjective g')

include hg hg' hfg hfg' in
/--
theorem `TensorProduct.map_ker` / 定理 `TensorProduct.map_ker`

English:
theorem TensorProduct.map_ker
  proof: by
  rw [← lTensor_comp_rTensor]
  rw [ker_comp]
  rw [← Exact.linearMap_ker_eq (rTensor_exact N' hfg hg)]
  rw [← Submodule.comap_map_eq]
  apply congr_arg₂ _ rfl
  rw [range_eq_map]; rw [← Submodule.map_comp]; rw [rTensor_comp_lTensor]; rw [Submodule.map_top]
  rw [← lTensor_comp_rTensor]; rw [range_eq_map]; rw [Submodule.map_comp]; rw [Submodule.map_top]
  rw [range_eq_top.mpr (rTensor_surjective M' hg)]; rw [Submodule.map_top]
  rw [Exact.linearMap_ker_eq (lTensor_exact P hfg' hg')]

中文:
定理 张量积.map_ker
  证明: by
  rw [← lTensor_comp_rTensor]
  rw [ker_comp]
  rw [← Exact.linearMap_ker_eq (rTensor_exact N' hfg hg)]
  rw [← Submodule.comap_map_eq]
  apply congr_arg₂ _ rfl
  rw [range_eq_map]; rw [← Submodule.map_comp]; rw [rTensor_comp_lTensor]; rw [Submodule.map_top]
  rw [← lTensor_comp_rTensor]; rw [range_eq_map]; rw [Submodule.map_comp]; rw [Submodule.map_top]
  rw [range_eq_top.mpr (rTensor_surjective M' hg)]; rw [Submodule.map_top]
  rw [Exact.linearMap_ker_eq (lTensor_exact P hfg' hg')]

Depends on / 依赖: Exact.linearMap_ker_eq, Submodule, Submodule.comap_map_eq, Submodule.map_comp, Submodule.map_top, comap_map_eq, ker_comp, lTensor_comp_rTensor, lTensor_exact, linearMap_ker_eq, map_comp, map_top, rTensor_comp_lTensor, rTensor_exact, rTensor_surjective, range_eq_map, range_eq_top, range_eq_top.mpr
-/
theorem TensorProduct.map_ker :
    ker (TensorProduct.map g g') = range (lTensor N f') ⊔ range (rTensor N' f) := by
  rw [← lTensor_comp_rTensor]
  rw [ker_comp]
  rw [← Exact.linearMap_ker_eq (rTensor_exact N' hfg hg)]
  rw [← Submodule.comap_map_eq]
  apply congr_arg₂ _ rfl
  rw [range_eq_map]; rw [← Submodule.map_comp]; rw [rTensor_comp_lTensor]; rw [Submodule.map_top]
  rw [← lTensor_comp_rTensor]; rw [range_eq_map]; rw [Submodule.map_comp]; rw [Submodule.map_top]
  rw [range_eq_top.mpr (rTensor_surjective M' hg)]; rw [Submodule.map_top]
  rw [Exact.linearMap_ker_eq (lTensor_exact P hfg' hg')]

end Modules

section Algebras

open Algebra.TensorProduct

open scoped TensorProduct

variable
    {R : Type*} [CommSemiring R]
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/--
lemma `Ideal.map_includeLeft_eq` / 引理 `Ideal.map_includeLeft_eq`

English:
lemma Ideal.map_includeLeft_eq
  given: (I : Ideal A)
  proof: by
  rw [← SetLike.coe_set_eq]
  apply le_antisymm
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    rw [Ideal.map]; rw [← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeLeft_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use ⟨y, hy⟩ otimesₜ[R] 1
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a • x) otimesₜ[R] (b * y)
          simp only [smul_eq_mul]
          with_unfolding_all rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype]
        suffices (a : A) otimesₜ[R] b = ((1 : A) otimesₜ[R] b) * ((a : A) otimesₜ[R] (1 : B)) by
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe]
          rw [this]
          apply Ideal.mul_mem_left
          -- Note: adding `includeLeft` as a hint fixes a timeout https://github.com/leanprover-community/mathlib4/pull/8386
          apply Ideal.mem_map_of_mem includeLeft
          exact Submodule.coe_mem a
        simp only [Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

中文:
引理 理想.map_includeLeft_eq
  条件: (I : 理想 A)
  证明: by
  rw [← SetLike.coe_set_eq]
  apply le_antisymm
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    rw [Ideal.map]; rw [← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeLeft_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use ⟨y, hy⟩ otimesₜ[R] 1
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a • x) otimesₜ[R] (b * y)
          simp only [smul_eq_mul]
          with_unfolding_all rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype]
        suffices (a : A) otimesₜ[R] b = ((1 : A) otimesₜ[R] b) * ((a : A) otimesₜ[R] (1 : B)) by
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe]
          rw [this]
          apply Ideal.mul_mem_left
          -- Note: adding `includeLeft` as a hint fixes a timeout https://github.com/leanprover-community/mathlib4/pull/8386
          apply Ideal.mem_map_of_mem includeLeft
          exact Submodule.coe_mem a
        simp only [Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

Depends on / 依赖: Ideal.map, LinearMap, LinearMap.mem_range, Set.mem_image, SetLike, SetLike.coe_set_eq, SetLike.mem_coe, Submodule, Submodule.span_induction, coe_set_eq, includeLeft_apply, le_antisymm, map_add, map_zero, mem_coe, mem_image, mem_range, span_induction, submodule_span_eq
-/
lemma Ideal.map_includeLeft_eq (I : Ideal A) :
    (I.map (Algebra.TensorProduct.includeLeft : A ->ₐ[R] A otimes[R] B)).restrictScalars R
      = LinearMap.range (LinearMap.rTensor B (Submodule.subtype (I.restrictScalars R))) := by
  rw [← SetLike.coe_set_eq]
  apply le_antisymm
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    rw [Ideal.map]; rw [← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeLeft_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use ⟨y, hy⟩ otimesₜ[R] 1
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a • x) otimesₜ[R] (b * y)
          simp only [smul_eq_mul]
          with_unfolding_all rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype]
        suffices (a : A) otimesₜ[R] b = ((1 : A) otimesₜ[R] b) * ((a : A) otimesₜ[R] (1 : B)) by
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe]
          rw [this]
          apply Ideal.mul_mem_left
          -- Note: adding `includeLeft` as a hint fixes a timeout https://github.com/leanprover-community/mathlib4/pull/8386
          apply Ideal.mem_map_of_mem includeLeft
          exact Submodule.coe_mem a
        simp only [Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

/--
lemma `Ideal.map_includeRight_eq` / 引理 `Ideal.map_includeRight_eq`

English:
lemma Ideal.map_includeRight_eq
  given: (I : Ideal B)
  proof: by
  rw [← SetLike.coe_set_eq]
  apply le_antisymm
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    rw [Ideal.map]; rw [← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeRight_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use 1 otimesₜ[R] ⟨y, hy⟩
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a * x) otimesₜ[R] (b • y)
          simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, smul_eq_mul, tmul_mul_tmul]
          rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype]
        suffices a otimesₜ[R] (b : B) = (a otimesₜ[R] (1 : B)) * ((1 : A) otimesₜ[R] (b : B)) by
          rw [this]
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe]
          apply Ideal.mul_mem_left
          -- Note: adding `includeRight` as a hint fixes a timeout https://github.com/leanprover-community/mathlib4/pull/8386
          apply Ideal.mem_map_of_mem includeRight
          exact Submodule.coe_mem b
        simp only [Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

中文:
引理 理想.map_includeRight_eq
  条件: (I : 理想 B)
  证明: by
  rw [← SetLike.coe_set_eq]
  apply le_antisymm
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    rw [Ideal.map]; rw [← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeRight_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use 1 otimesₜ[R] ⟨y, hy⟩
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a * x) otimesₜ[R] (b • y)
          simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, smul_eq_mul, tmul_mul_tmul]
          rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype]
        suffices a otimesₜ[R] (b : B) = (a otimesₜ[R] (1 : B)) * ((1 : A) otimesₜ[R] (b : B)) by
          rw [this]
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe]
          apply Ideal.mul_mem_left
          -- Note: adding `includeRight` as a hint fixes a timeout https://github.com/leanprover-community/mathlib4/pull/8386
          apply Ideal.mem_map_of_mem includeRight
          exact Submodule.coe_mem b
        simp only [Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

Depends on / 依赖: Ideal.map, LinearMap, LinearMap.mem_range, Set.mem_image, SetLike, SetLike.coe_set_eq, SetLike.mem_coe, Submodule, Submodule.span_induction, coe_set_eq, includeRight_apply, le_antisymm, map_add, map_zero, mem_coe, mem_image, mem_range, span_induction, submodule_span_eq
-/
lemma Ideal.map_includeRight_eq (I : Ideal B) :
    (I.map (Algebra.TensorProduct.includeRight : B ->ₐ[R] A otimes[R] B)).restrictScalars R
      = LinearMap.range (LinearMap.lTensor A (Submodule.subtype (I.restrictScalars R))) := by
  rw [← SetLike.coe_set_eq]
  apply le_antisymm
  · intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_range]
    rw [Ideal.map]; rw [← submodule_span_eq] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x
      simp only [includeRight_apply, Set.mem_image, SetLike.mem_coe]
      rintro ⟨y, hy, rfl⟩
      use 1 otimesₜ[R] ⟨y, hy⟩
      rfl
    · use 0
      simp only [map_zero]
    · rintro x y - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      use x + y
      simp only [map_add]
    · rintro a x - ⟨x, hx, rfl⟩
      induction a with
      | zero =>
        use 0
        simp only [map_zero, smul_eq_mul, zero_mul]
      | tmul a b =>
        induction x with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul x y =>
          use (a * x) otimesₜ[R] (b • y)
          simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, smul_eq_mul, tmul_mul_tmul]
          rfl
        | add x y hx hy =>
          obtain ⟨x', hx'⟩ := hx
          obtain ⟨y', hy'⟩ := hy
          use x' + y'
          simp only [map_add, hx', smul_add, hy']
      | add a b ha hb =>
        obtain ⟨x', ha'⟩ := ha
        obtain ⟨y', hb'⟩ := hb
        use x' + y'
        simp only [map_add, ha', add_smul, hb']
  · rintro x ⟨y, rfl⟩
    induction y with
    | zero =>
        rw [map_zero]
        apply zero_mem
    | tmul a b =>
        simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype]
        suffices a otimesₜ[R] (b : B) = (a otimesₜ[R] (1 : B)) * ((1 : A) otimesₜ[R] (b : B)) by
          rw [this]
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe]
          apply Ideal.mul_mem_left
          -- Note: adding `includeRight` as a hint fixes a timeout https://github.com/leanprover-community/mathlib4/pull/8386
          apply Ideal.mem_map_of_mem includeRight
          exact Submodule.coe_mem b
        simp only [Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add x y hx hy =>
        rw [map_add]
        apply Submodule.add_mem _ hx hy

variable (A) in
/--
lemma `TensorProduct.AlgebraTensorModule.range_lTensor_idealMap` / 引理 `TensorProduct.AlgebraTensorModule.range_lTensor_idealMap`

English:
lemma TensorProduct.AlgebraTensorModule.range_lTensor_idealMap
  statement: (S : Type*) [CommSemiring S]
  proof: by
  rw [← (Submodule.restrictScalars_injective R _ _).eq_iff]
  exact (I.map_includeRight_eq (R := R) (A := A)).symm

中文:
引理 张量积.AlgebraTensorModule.range_lTensor_idealMap
  结论: (S : 类型) [交换半环 S]
  证明: by
  rw [← (Submodule.restrictScalars_injective R _ _).eq_iff]
  exact (I.map_includeRight_eq (R := R) (A := A)).symm

Depends on / 依赖: I.map_includeRight_eq, Submodule, Submodule.restrictScalars_injective, eq_iff, map_includeRight_eq, restrictScalars, restrictScalars_injective
-/
lemma TensorProduct.AlgebraTensorModule.range_lTensor_idealMap (S : Type*) [CommSemiring S]
    [Algebra R S] [Algebra S A] [IsScalarTower R S A] (I : Ideal B) :
    LinearMap.range (lTensor S A (I.subtype.restrictScalars R)) =
      (I.map (includeRight (A := A) (R := R))).restrictScalars S := by
  rw [← (Submodule.restrictScalars_injective R _ _).eq_iff]
  exact (I.map_includeRight_eq (R := R) (A := A)).symm

-- Now, we can prove the right exactness properties of the tensor product,
-- in its versions for algebras

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {A B C D : Type*} [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra S A] [Algebra S B]
  [IsScalarTower R S A] [IsScalarTower R S B]
  (f : A ->ₐ[S] B) (g : C ->ₐ[R] D)

/--
lemma `Algebra.TensorProduct.lTensor_ker` / 引理 `Algebra.TensorProduct.lTensor_ker`

English:
lemma Algebra.TensorProduct.lTensor_ker
  given: (hg : Function.Surjective g)
  proof: by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map (AlgHom.id R A) g)).restrictScalars R =
    LinearMap.ker (LinearMap.lTensor A (AlgHom.toLinearMap g)) := rfl
  rw [this]; rw [Ideal.map_includeRight_eq]
  rw [(lTensor_exact A g.toLinearMap.exact_subtype_ker_map hg).linearMap_ker_eq]
  rfl

中文:
引理 代数.张量积.lTensor_ker
  条件: (hg : 函数.满射 g)
  证明: by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map (AlgHom.id R A) g)).restrictScalars R =
    LinearMap.ker (LinearMap.lTensor A (AlgHom.toLinearMap g)) := rfl
  rw [this]; rw [Ideal.map_includeRight_eq]
  rw [(lTensor_exact A g.toLinearMap.exact_subtype_ker_map hg).linearMap_ker_eq]
  rfl

Depends on / 依赖: AlgHom, AlgHom.id, AlgHom.toLinearMap, Ideal.map_includeRight_eq, LinearMap, LinearMap.ker, LinearMap.lTensor, RingHom, RingHom.ker, Submodule, Submodule.restrictScalars_inj, exact_subtype_ker_map, g.toLinearMap.exact_subtype_ker_map, lTensor, lTensor_exact, linearMap_ker_eq, map_includeRight_eq, restrictScalars, restrictScalars_inj, toLinearMap
-/
lemma Algebra.TensorProduct.lTensor_ker (hg : Function.Surjective g) :
    RingHom.ker (map (AlgHom.id R A) g) =
      (RingHom.ker g).map (Algebra.TensorProduct.includeRight : C ->ₐ[R] A otimes[R] C) := by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map (AlgHom.id R A) g)).restrictScalars R =
    LinearMap.ker (LinearMap.lTensor A (AlgHom.toLinearMap g)) := rfl
  rw [this]; rw [Ideal.map_includeRight_eq]
  rw [(lTensor_exact A g.toLinearMap.exact_subtype_ker_map hg).linearMap_ker_eq]
  rfl

/--
lemma `Algebra.TensorProduct.rTensor_ker` / 引理 `Algebra.TensorProduct.rTensor_ker`

English:
lemma Algebra.TensorProduct.rTensor_ker
  given: (hf : Function.Surjective f)
  proof: by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map f (AlgHom.id R C))).restrictScalars R =
    LinearMap.ker (LinearMap.rTensor C (f.restrictScalars R).toLinearMap) := rfl
  rw [this]; rw [Ideal.map_includeLeft_eq]
  rw [(rTensor_exact C (f.restrictScalars R).toLinearMap.exact_subtype_ker_map hf).linearMap_ker_eq]
  rfl

中文:
引理 代数.张量积.rTensor_ker
  条件: (hf : 函数.满射 f)
  证明: by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map f (AlgHom.id R C))).restrictScalars R =
    LinearMap.ker (LinearMap.rTensor C (f.restrictScalars R).toLinearMap) := rfl
  rw [this]; rw [Ideal.map_includeLeft_eq]
  rw [(rTensor_exact C (f.restrictScalars R).toLinearMap.exact_subtype_ker_map hf).linearMap_ker_eq]
  rfl

Depends on / 依赖: AlgHom, AlgHom.id, Ideal.map_includeLeft_eq, LinearMap, LinearMap.ker, LinearMap.rTensor, RingHom, RingHom.ker, Submodule, Submodule.restrictScalars_inj, exact_subtype_ker_map, f.restrictScalars, linearMap_ker_eq, map_includeLeft_eq, rTensor, rTensor_exact, restrictScalars, restrictScalars_inj, toLinearMap, toLinearMap.exact_subtype_ker_map
-/
lemma Algebra.TensorProduct.rTensor_ker (hf : Function.Surjective f) :
    RingHom.ker (map f (AlgHom.id R C)) =
      (RingHom.ker f).map (Algebra.TensorProduct.includeLeft : A ->ₐ[R] A otimes[R] C) := by
  rw [← Submodule.restrictScalars_inj R]
  have : (RingHom.ker (map f (AlgHom.id R C))).restrictScalars R =
    LinearMap.ker (LinearMap.rTensor C (f.restrictScalars R).toLinearMap) := rfl
  rw [this]; rw [Ideal.map_includeLeft_eq]
  rw [(rTensor_exact C (f.restrictScalars R).toLinearMap.exact_subtype_ker_map hf).linearMap_ker_eq]
  rfl

/--
theorem `Algebra.TensorProduct.map_surjective` / 定理 `Algebra.TensorProduct.map_surjective`

English:
theorem Algebra.TensorProduct.map_surjective
  proof: _root_.TensorProduct.map_surjective (g := f.toLinearMap.restrictScalars R) hf hg

中文:
定理 代数.张量积.map_surjective
  证明: _root_.TensorProduct.map_surjective (g := f.toLinearMap.restrictScalars R) hf hg

Depends on / 依赖: TensorProduct, _root_, _root_.TensorProduct.map_surjective, f.toLinearMap.restrictScalars, map_surjective, restrictScalars, toLinearMap
-/
theorem Algebra.TensorProduct.map_surjective
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (map f g) :=
  _root_.TensorProduct.map_surjective (g := f.toLinearMap.restrictScalars R) hf hg

/--
theorem `Algebra.TensorProduct.map_ker` / 定理 `Algebra.TensorProduct.map_ker`

English:
theorem Algebra.TensorProduct.map_ker
  given: (hf : Function.Surjective f) (hg : Function.Surjective g)
  proof: by
  -- rewrite map f g as the composition of two maps
  have : map f g = (map f (AlgHom.id R D)).comp (map (AlgHom.id S A) g) := ext rfl rfl
  rw [this]
  -- this needs some rewriting to RingHom
  -- TODO: can `RingHom.comap_ker` take an arbitrary `RingHomClass`, rather than just `RingHom`?
  simp only [AlgHom.ker_coe, AlgHom.comp_toRingHom]
  rw [← RingHom.comap_ker]
  simp only [← AlgHom.ker_coe]
  -- apply one step of exactness
  rw [← Algebra.TensorProduct.lTensor_ker _ hg]; rw [RingHom.ker_eq_comap_bot (map (AlgHom.id R A) g)]
  rw [← Ideal.comap_map_of_surjective (map (AlgHom.id R A) g) (LinearMap.lTensor_surjective A hg)]
  -- apply the other step of exactness
  rw [Algebra.TensorProduct.rTensor_ker _ hf]
  apply congr_arg₂ _ rfl
  simp only [AlgHom.coe_ideal_map, Ideal.map_map]
  rw [← AlgHom.comp_toRingHom]; rw [Algebra.TensorProduct.map_comp_includeLeft]
  rfl

中文:
定理 代数.张量积.map_ker
  条件: (hf : 函数.满射 f) (hg : 函数.满射 g)
  证明: by
  -- rewrite map f g as the composition of two maps
  have : map f g = (map f (AlgHom.id R D)).comp (map (AlgHom.id S A) g) := ext rfl rfl
  rw [this]
  -- this needs some rewriting to RingHom
  -- TODO: can `RingHom.comap_ker` take an arbitrary `RingHomClass`, rather than just `RingHom`?
  simp only [AlgHom.ker_coe, AlgHom.comp_toRingHom]
  rw [← RingHom.comap_ker]
  simp only [← AlgHom.ker_coe]
  -- apply one step of exactness
  rw [← Algebra.TensorProduct.lTensor_ker _ hg]; rw [RingHom.ker_eq_comap_bot (map (AlgHom.id R A) g)]
  rw [← Ideal.comap_map_of_surjective (map (AlgHom.id R A) g) (LinearMap.lTensor_surjective A hg)]
  -- apply the other step of exactness
  rw [Algebra.TensorProduct.rTensor_ker _ hf]
  apply congr_arg₂ _ rfl
  simp only [AlgHom.coe_ideal_map, Ideal.map_map]
  rw [← AlgHom.comp_toRingHom]; rw [Algebra.TensorProduct.map_comp_includeLeft]
  rfl
-/
theorem Algebra.TensorProduct.map_ker (hf : Function.Surjective f) (hg : Function.Surjective g) :
    RingHom.ker (map f g) =
      (RingHom.ker f).map (Algebra.TensorProduct.includeLeft : A ->ₐ[R] A otimes[R] C) ⊔
        (RingHom.ker g).map (Algebra.TensorProduct.includeRight : C ->ₐ[R] A otimes[R] C) := by
  -- rewrite map f g as the composition of two maps
  have : map f g = (map f (AlgHom.id R D)).comp (map (AlgHom.id S A) g) := ext rfl rfl
  rw [this]
  -- this needs some rewriting to RingHom
  -- TODO: can `RingHom.comap_ker` take an arbitrary `RingHomClass`, rather than just `RingHom`?
  simp only [AlgHom.ker_coe, AlgHom.comp_toRingHom]
  rw [← RingHom.comap_ker]
  simp only [← AlgHom.ker_coe]
  -- apply one step of exactness
  rw [← Algebra.TensorProduct.lTensor_ker _ hg]; rw [RingHom.ker_eq_comap_bot (map (AlgHom.id R A) g)]
  rw [← Ideal.comap_map_of_surjective (map (AlgHom.id R A) g) (LinearMap.lTensor_surjective A hg)]
  -- apply the other step of exactness
  rw [Algebra.TensorProduct.rTensor_ker _ hf]
  apply congr_arg₂ _ rfl
  simp only [AlgHom.coe_ideal_map, Ideal.map_map]
  rw [← AlgHom.comp_toRingHom]; rw [Algebra.TensorProduct.map_comp_includeLeft]
  rfl

end Algebras
