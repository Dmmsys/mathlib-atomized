/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
`Analysis.Complex.UpperHalfPlane`). We then define the standard fundamental domain
(`ModularGroup.fd`, `𝒟`) for this action and show (`ModularGroup.exists_smul_mem_fd`)
that any point in `ℍ` can be moved inside `𝒟`.

## Main definitions

The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟`:
`fd := {z | 1 ≤ (z : ℂ).normSq ∧ |z.re| ≤ (1 : ℝ) / 2}`

The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟ᵒ`:
`fdo := {z | 1 < (z : ℂ).normSq ∧ |z.re| < (1 : ℝ) / 2}`

These notations are localized in the `Modular` scope and can be enabled via `open scoped Modular`.

## Main results

* `ModularGroup.exists_smul_mem_fd`: Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`.
* `ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd`:
  The open fundamental domain `𝒟ᵒ` is disjoint from `g • 𝒟` for any `g ≠ ±1`.
* `ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`:
  If both `z` and `γ • z` are in the open domain `𝒟ᵒ` then `z = γ • z`.
* `ModularGroup.fdo_eq_interior_fd` and `ModularGroup.fd_eq_closure_fdo`: topological relations
  between `fd` and `fdo`.

## Discussion

Standard proofs make use of the identity

`g • z = a / c - 1 / (c (cz + d))`

for `g = [[a, b], [c, d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
Instead, our proof makes use of the following perhaps novel identity (see
`ModularGroup.smul_eq_lcRow0_add`):

`g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

where there is no issue of division by zero.

Another feature is that we delay until the very end the consideration of special matrices
`T=[[1,1],[0,1]]` (see `ModularGroup.T`) and `S=[[0,-1],[1,0]]` (see `ModularGroup.S`), by
instead using abstract theory on the properness of certain maps (phrased in terms of the filters
`Filter.cocompact`, `Filter.cofinite`, etc) to deduce existence theorems, first to prove the
existence of `g` maximizing `(g•z).im` (see `ModularGroup.exists_max_im`), and then among
those, to minimize `|(g•z).re|` (see `ModularGroup.exists_row_one_eq_and_min_re`).

The characterization of cases with `z ∈ 𝒟` and `g • z ∈ 𝒟` follows Theorem VII.1 [serre1973].
-/

@[expose] public section

open Complex hiding I

open Matrix hiding mul_smul

open Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup Topology

noncomputable section

open scoped ComplexConjugate MatrixGroups

namespace ModularGroup

variable {g : SL(2, Int)} (z : ℍ)

section BottomRow

/--
theorem `bottom_row_coprime` / 定理 `bottom_row_coprime`

English:
theorem bottom_row_coprime
  given: {R : Type*} [CommRing R] (g : SL(2, R))
  proof: isCoprime_row g 1

中文:
定理 bottom_row_coprime
  条件: {R : 类型} [CommRing R] (g : SL(2, R))
  证明: isCoprime_row g 1

Depends on / 依赖: isCoprime_row
-/
theorem bottom_row_coprime {R : Type*} [CommRing R] (g : SL(2, R)) :
    IsCoprime ((↑g : Matrix (Fin 2) (Fin 2) R) 1 0) ((↑g : Matrix (Fin 2) (Fin 2) R) 1 1) :=
  isCoprime_row g 1

/--
theorem `bottom_row_surj` / 定理 `bottom_row_surj`

English:
theorem bottom_row_surj
  given: {R : Type*} [CommRing R]
  proof: by
  rintro cd ⟨b₀, a, gcd_eqn⟩
  let A := of ![![a, -b₀], cd]
  have det_A_1 : det A = 1 := by
    convert! gcd_eqn
    rw [det_fin_two]
    simp [A, (by ring : a * cd 1 + b₀ * cd 0 = b₀ * cd 0 + a * cd 1)]
  refine ⟨⟨A, det_A_1⟩, Set.mem_univ _, ?_⟩
  ext; simp [A]

中文:
定理 bottom_row_surj
  条件: {R : 类型} [CommRing R]
  证明: by
  rintro cd ⟨b₀, a, gcd_eqn⟩
  let A := of ![![a, -b₀], cd]
  have det_A_1 : det A = 1 := by
    convert! gcd_eqn
    rw [det_fin_two]
    simp [A, (by ring : a * cd 1 + b₀ * cd 0 = b₀ * cd 0 + a * cd 1)]
  refine ⟨⟨A, det_A_1⟩, Set.mem_univ _, ?_⟩
  ext; simp [A]

Depends on / 依赖: Set.mem_univ, convert, det_A_1, det_fin_two, gcd_eqn, mem_univ
-/
theorem bottom_row_surj {R : Type*} [CommRing R] :
    Set.SurjOn (fun g : SL(2, R) => (↑g : Matrix (Fin 2) (Fin 2) R) 1) Set.univ
      {cd | IsCoprime (cd 0) (cd 1)} := by
  rintro cd ⟨b₀, a, gcd_eqn⟩
  let A := of ![![a, -b₀], cd]
  have det_A_1 : det A = 1 := by
    convert! gcd_eqn
    rw [det_fin_two]
    simp [A, (by ring : a * cd 1 + b₀ * cd 0 = b₀ * cd 0 + a * cd 1)]
  refine ⟨⟨A, det_A_1⟩, Set.mem_univ _, ?_⟩
  ext; simp [A]

end BottomRow

section TendstoLemmas

open Filter ContinuousLinearMap

attribute [local simp] FunLike.coe_smul

/--
theorem `tendsto_normSq_coprime_pair` / 定理 `tendsto_normSq_coprime_pair`

English:
theorem tendsto_normSq_coprime_pair
  proof: by
  -- using this instance rather than the automatic `Function.module` makes unification issues in
  -- `LinearEquiv.isClosedEmbedding_of_injective` less bad later in the proof.
  let : Module Real (Fin 2 -> Real) := NormedSpace.toModule
  let π₀ : (Fin 2 -> Real) ->ₗ[Real] Real := LinearMap.proj 0

中文:
定理 tendsto_normSq_coprime_pair
  证明: by
  -- using this instance rather than the automatic `Function.module` makes unification issues in
  -- `LinearEquiv.isClosedEmbedding_of_injective` less bad later in the proof.
  let : Module Real (Fin 2 -> Real) := NormedSpace.toModule
  let π₀ : (Fin 2 -> Real) ->ₗ[Real] Real := LinearMap.proj 0
-/
theorem tendsto_normSq_coprime_pair :
    Filter.Tendsto (fun p : Fin 2 -> Int => normSq ((p 0 : Complex) * z + p 1)) cofinite atTop := by
  -- using this instance rather than the automatic `Function.module` makes unification issues in
  -- `LinearEquiv.isClosedEmbedding_of_injective` less bad later in the proof.
  let : Module Real (Fin 2 -> Real) := NormedSpace.toModule
  let π₀ : (Fin 2 -> Real) ->ₗ[Real] Real := LinearMap.proj 0
  let π₁ : (Fin 2 -> Real) ->ₗ[Real] Real := LinearMap.proj 1
  let f : (Fin 2 -> Real) ->ₗ[Real] Complex := π₀.smulRight (z : Complex) + π₁.smulRight 1
  have f_def : ⇑f = fun p : Fin 2 -> Real => (p 0 : Complex) * ↑z + p 1 := by
    ext1
    dsimp only [π₀, π₁, f, LinearMap.coe_proj, real_smul, LinearMap.coe_smulRight,
      LinearMap.add_apply]
    rw [mul_one]
  have :
    (fun p : Fin 2 -> Int => normSq ((p 0 : Complex) * ↑z + ↑(p 1))) =
      normSq ∘ f ∘ fun p : Fin 2 -> Int => ((↑) : Int -> Real) ∘ p := by
    ext1
    rw [f_def]
    dsimp only [Function.comp_def]
    rw [ofReal_intCast]; rw [ofReal_intCast]
  rw [this]
  have hf : LinearMap.ker f = ⊥ := by
    let g : Complex ->ₗ[Real] Fin 2 -> Real :=
      LinearMap.pi ![imLm, imLm.comp ((z : Complex) • ((conjAe : Complex ->ₐ[Real] Complex) : Complex ->ₗ[Real] Complex))]
    suffices ((z : Complex).im⁻¹ • g).comp f = LinearMap.id by exact LinearMap.ker_eq_bot_of_inverse this
    apply LinearMap.ext
    intro c
    have hz : (z : Complex).im != 0 := z.2.ne'
    rw [LinearMap.comp_apply]; rw [LinearMap.smul_apply]; rw [LinearMap.id_apply]
    ext i
    dsimp only [Pi.smul_apply, LinearMap.pi_apply, smul_eq_mul]
    fin_cases i
    · change (z : Complex).im⁻¹ * (f c).im = c 0
      rw [f_def]; rw [add_im]; rw [im_ofReal_mul]; rw [ofReal_im]; rw [add_zero]; rw [mul_left_comm]; rw [inv_mul_cancel₀ hz]; rw [mul_one]
    · change (z : Complex).im⁻¹ * ((z : Complex) * conj (f c)).im = c 1
      rw [f_def]; rw [map_add]; rw [map_mul]; rw [mul_add]; rw [mul_left_comm]; rw [mul_conj]; rw [conj_ofReal]; rw [conj_ofReal]; rw [← ofReal_mul]; rw [add_im]; rw [ofReal_im]; rw [zero_add]; rw [inv_mul_eq_iff_eq_mul₀ hz]
      simp only [ofReal_im, ofReal_re, mul_im, zero_add, mul_zero]
  have hf' : IsClosedEmbedding f := f.isClosedEmbedding_of_injective hf
  have h₂ : Tendsto (fun p : Fin 2 -> Int => ((↑) : Int -> Real) ∘ p) cofinite (cocompact _) := by
    convert! Tendsto.pi_map_coprodᵢ fun _ => Int.tendsto_coe_cofinite
    · rw [coprodᵢ_cofinite]
    · rw [coprodᵢ_cocompact]
  exact tendsto_normSq_cocompact_atTop.comp (hf'.tendsto_cocompact.comp h₂)

/--
Definition of `lcRow0` / `lcRow0` 的定义

English:
definition lcRow0
  signature: (p : Fin 2 -> Int)
  body: ((p 0 : Real) • LinearMap.proj (0 : Fin 2) +
      (p 1 : Real) • LinearMap.proj (1 : Fin 2) : (Fin 2 -> Real) ->ₗ[Real] Real).comp
    (LinearMap.proj 0)

@[simp]

中文:
定义 lcRow0
  签名: (p : Fin 2 -> 整数)
  定义体: ((p 0 : Real) • LinearMap.proj (0 : Fin 2) +
      (p 1 : Real) • LinearMap.proj (1 : Fin 2) : (Fin 2 -> Real) ->ₗ[Real] Real).comp
    (LinearMap.proj 0)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.proj
-/
def lcRow0 (p : Fin 2 -> Int) : Matrix (Fin 2) (Fin 2) Real ->ₗ[Real] Real :=
  ((p 0 : Real) • LinearMap.proj (0 : Fin 2) +
      (p 1 : Real) • LinearMap.proj (1 : Fin 2) : (Fin 2 -> Real) ->ₗ[Real] Real).comp
    (LinearMap.proj 0)

@[simp]
/--
theorem `lcRow0_apply` / 定理 `lcRow0_apply`

English:
theorem lcRow0_apply
  given: (p : Fin 2 -> Int) (g : Matrix (Fin 2) (Fin 2) Real)
  proof: rfl

中文:
定理 lcRow0_apply
  条件: (p : Fin 2 -> 整数) (g : Matrix (Fin 2) (Fin 2) 实数)
  证明: rfl
-/
theorem lcRow0_apply (p : Fin 2 -> Int) (g : Matrix (Fin 2) (Fin 2) Real) :
    lcRow0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
  rfl

/-- Linear map sending the matrix [a, b; c, d] to the matrix [ac₀ + bd₀, - ad₀ + bc₀; c, d], for
some fixed `(c₀, d₀)`. -/
@[simps!]
/--
Definition of `lcRow0Extend` / `lcRow0Extend` 的定义

English:
definition lcRow0Extend
  signature: {cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (cd 1))
  body: LinearEquiv.piCongrRight
    ![by
      refine
        LinearMap.GeneralLinearGroup.generalLinearEquiv Real (Fin 2 -> Real)
          (GeneralLinearGroup.toLin (planeConformalMatrix (cd 0 : Real) (-(cd 1 : Real)) ?_))
      norm_cast
      rw [neg_sq]
      exact hcd.sq_add_sq_ne_zero, LinearEquiv.r

中文:
定义 lcRow0Extend
  签名: {cd : Fin 2 -> 整数} (hcd : IsCoprime (cd 0) (cd 1))
  定义体: LinearEquiv.piCongrRight
    ![by
      refine
        LinearMap.GeneralLinearGroup.generalLinearEquiv Real (Fin 2 -> Real)
          (GeneralLinearGroup.toLin (planeConformalMatrix (cd 0 : Real) (-(cd 1 : Real)) ?_))
      norm_cast
      rw [neg_sq]
      exact hcd.sq_add_sq_ne_zero, LinearEquiv.r

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.toLin, LinearEquiv, LinearEquiv.piCongrRight, LinearEquiv.refl, LinearMap, LinearMap.GeneralLinearGroup.generalLinearEquiv, generalLinearEquiv, hcd.sq_add_sq_ne_zero, neg_sq, piCongrRight, planeConformalMatrix, sq_add_sq_ne_zero
-/
def lcRow0Extend {cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (cd 1)) :
    Matrix (Fin 2) (Fin 2) Real ≃ₗ[Real] Matrix (Fin 2) (Fin 2) Real :=
  LinearEquiv.piCongrRight
    ![by
      refine
        LinearMap.GeneralLinearGroup.generalLinearEquiv Real (Fin 2 -> Real)
          (GeneralLinearGroup.toLin (planeConformalMatrix (cd 0 : Real) (-(cd 1 : Real)) ?_))
      norm_cast
      rw [neg_sq]
      exact hcd.sq_add_sq_ne_zero, LinearEquiv.refl Real (Fin 2 -> Real)]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tendsto_lcRow0` / 定理 `tendsto_lcRow0`

English:
theorem tendsto_lcRow0
  given: {cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (cd 1))
  proof: by
  let mB : Real -> Matrix (Fin 2) (Fin 2) Real := fun t => of ![![t, (-(1 : Int) : Real)], (↑) ∘ cd]
  have hmB : Continuous mB := by
    refine continuous_matrix ?_
    simp only [mB, Fin.forall_fin_two, continuous_const, continuous_id', of_apply, cons_val_zero,
      cons_val_one, and_self_iff]

中文:
定理 tendsto_lcRow0
  条件: {cd : Fin 2 -> 整数} (hcd : IsCoprime (cd 0) (cd 1))
  证明: by
  let mB : Real -> Matrix (Fin 2) (Fin 2) Real := fun t => of ![![t, (-(1 : Int) : Real)], (↑) ∘ cd]
  have hmB : Continuous mB := by
    refine continuous_matrix ?_
    simp only [mB, Fin.forall_fin_two, continuous_const, continuous_id', of_apply, cons_val_zero,
      cons_val_one, and_self_iff]

Depends on / 依赖: Continuous, Filter, Filter.Tendsto.of_tendsto_comp, Fin.forall_fin_two, Matrix, Matrix.map, Tendsto, and_self_iff, cocompact_Real_to_cofinite_Int, comap_cocompact_le, cons_val_one, cons_val_zero, continuous_const, continuous_id, continuous_matrix, forall_fin_two, of_apply, of_tendsto_comp
-/
theorem tendsto_lcRow0 {cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (cd 1)) :
    Tendsto (fun g : { g : SL(2, Int) // g 1 = cd } => lcRow0 cd ↑(↑g : SL(2, Real))) cofinite
      (cocompact Real) := by
  let mB : Real -> Matrix (Fin 2) (Fin 2) Real := fun t => of ![![t, (-(1 : Int) : Real)], (↑) ∘ cd]
  have hmB : Continuous mB := by
    refine continuous_matrix ?_
    simp only [mB, Fin.forall_fin_two, continuous_const, continuous_id', of_apply, cons_val_zero,
      cons_val_one, and_self_iff]
  refine Filter.Tendsto.of_tendsto_comp ?_ (comap_cocompact_le hmB)
  let f₁ : SL(2, Int) -> Matrix (Fin 2) (Fin 2) Real := fun g =>
    Matrix.map (↑g : Matrix _ _ Int) ((↑) : Int -> Real)
  have cocompact_Real_to_cofinite_Int_matrix :
    Tendsto (fun m : Matrix (Fin 2) (Fin 2) Int => Matrix.map m ((↑) : Int -> Real)) cofinite
      (cocompact _) := by
    simpa only [coprodᵢ_cofinite, coprodᵢ_cocompact] using!
      Tendsto.pi_map_coprodᵢ fun _ : Fin 2 =>
        Tendsto.pi_map_coprodᵢ fun _ : Fin 2 => Int.tendsto_coe_cofinite
  have hf₁ : Tendsto f₁ cofinite (cocompact _) :=
    cocompact_Real_to_cofinite_Int_matrix.comp Subtype.coe_injective.tendsto_cofinite
  have hf₂ : IsClosedEmbedding (lcRow0Extend hcd) :=
    (lcRow0Extend hcd).toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding
  convert! hf₂.tendsto_cocompact.comp (hf₁.comp Subtype.coe_injective.tendsto_cofinite) using 1
  ext ⟨g, rfl⟩ i j : 3
  fin_cases i <;> [fin_cases j; skip]
  -- the following are proved by `simp`, but it is replaced by `simp only` to avoid timeouts.
  · simp only [Fin.isValue, Int.cast_one, map_apply_coe, RingHom.mapMatrix_apply,
      Int.coe_castRingHom, lcRow0_apply, map_apply, Fin.zero_eta, Function.comp_apply,
      of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one, lcRow0Extend_apply,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, GeneralLinearGroup.coe_toLin,
      val_planeConformalMatrix, neg_neg, mulVecLin_apply, mulVec, dotProduct, Fin.sum_univ_two,
      cons_val_one, mB, f₁]
  · convert! congr_arg (fun n : Int => (-n : Real)) g.det_coe.symm using 1
    simp only [Fin.zero_eta, Function.comp_apply, lcRow0Extend_apply, cons_val_zero,
      LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, GeneralLinearGroup.coe_toLin,
      mulVecLin_apply, mulVec, dotProduct, det_fin_two, f₁]
    simp only [Fin.isValue, Fin.mk_one, val_planeConformalMatrix, neg_neg, of_apply, cons_val',
      empty_val', cons_val_fin_one, cons_val_one, map_apply, Fin.sum_univ_two,
      cons_val_zero, neg_mul, Int.cast_sub, Int.cast_mul, neg_sub]
    ring
  · rfl

/--
theorem `smul_eq_lcRow0_add` / 定理 `smul_eq_lcRow0_add`

English:
theorem smul_eq_lcRow0_add
  given: {p : Fin 2 -> Int} (hp : IsCoprime (p 0) (p 1)) (hg : g 1 = p)
  proof: by
  have nonZ1 : (p 0 : Complex) ^ 2 + (p 1 : Complex) ^ 2 != 0 := mod_cast hp.sq_add_sq_ne_zero
  have : ((↑) : Int -> Real) ∘ p != 0 := fun h => hp.ne_zero (by ext i; simpa using congr_fun h i)
  have nonZ2 : (p 0 : Complex) * z + p 1 != 0 := by simpa using linear_ne_zero z this
  subst hg
  rw [

中文:
定理 smul_eq_lcRow0_add
  条件: {p : Fin 2 -> 整数} (hp : IsCoprime (p 0) (p 1)) (hg : g 1 = p)
  证明: by
  have nonZ1 : (p 0 : Complex) ^ 2 + (p 1 : Complex) ^ 2 != 0 := mod_cast hp.sq_add_sq_ne_zero
  have : ((↑) : Int -> Real) ∘ p != 0 := fun h => hp.ne_zero (by ext i; simpa using congr_fun h i)
  have nonZ2 : (p 0 : Complex) * z + p 1 != 0 := by simpa using linear_ne_zero z this
  subst hg
  rw [

Depends on / 依赖: Int.cast, coe_specialLinearGroup_apply, congr_fun, convert, det_fin_two, hp.ne_zero, hp.sq_add_sq_ne_zero, linear_combin, linear_ne_zero, mod_cast, ne_zero, replace, sq_add_sq_ne_zero
-/
theorem smul_eq_lcRow0_add {p : Fin 2 -> Int} (hp : IsCoprime (p 0) (p 1)) (hg : g 1 = p) :
    ↑(g • z) =
      (lcRow0 p ↑(g : SL(2, Real)) : Complex) / ((p 0 : Complex) ^ 2 + (p 1 : Complex) ^ 2) +
        ((p 1 : Complex) * z - p 0) / (((p 0 : Complex) ^ 2 + (p 1 : Complex) ^ 2) * (p 0 * z + p 1)) := by
  have nonZ1 : (p 0 : Complex) ^ 2 + (p 1 : Complex) ^ 2 != 0 := mod_cast hp.sq_add_sq_ne_zero
  have : ((↑) : Int -> Real) ∘ p != 0 := fun h => hp.ne_zero (by ext i; simpa using congr_fun h i)
  have nonZ2 : (p 0 : Complex) * z + p 1 != 0 := by simpa using linear_ne_zero z this
  subst hg
  rw [coe_specialLinearGroup_apply]
  replace nonZ2 : z * (g 1 0 : Complex) + g 1 1 != 0 := by convert! nonZ2 using 1; ring
  have H := congr(Int.cast (R := Complex) $(det_fin_two g))
  simp at H
  simp [field]
  linear_combination -((z : Complex) * (g 1 1 : Complex) - g 1 0) * H

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tendsto_abs_re_smul` / 定理 `tendsto_abs_re_smul`

English:
theorem tendsto_abs_re_smul
  given: {p : Fin 2 -> Int} (hp : IsCoprime (p 0) (p 1))
  proof: by
  suffices
    Tendsto (fun g : (fun g : SL(2, Int) => g 1) ⁻¹' {p} => ((g : SL(2, Int)) • z).re) cofinite
      (cocompact Real)
    tendsto_norm_cocompact_atTop.comp this
  have : ((p 0 : Real) ^ 2 + (p 1 : Real) ^ 2)⁻¹ != 0 := by
    apply inv_ne_zero
    exact mod_cast hp.sq_add_sq_ne_zero
  

中文:
定理 tendsto_abs_re_smul
  条件: {p : Fin 2 -> 整数} (hp : IsCoprime (p 0) (p 1))
  证明: by
  suffices
    Tendsto (fun g : (fun g : SL(2, Int) => g 1) ⁻¹' {p} => ((g : SL(2, Int)) • z).re) cofinite
      (cocompact Real)
    tendsto_norm_cocompact_atTop.comp this
  have : ((p 0 : Real) ^ 2 + (p 1 : Real) ^ 2)⁻¹ != 0 := by
    apply inv_ne_zero
    exact mod_cast hp.sq_add_sq_ne_zero
  

Depends on / 依赖: Homeomorph, Homeomorph.addRight, Homeomorph.mulRight, Tendsto, addRight, cocompact, cofinite, convert, f.trans, hp.sq_add_sq_ne_zero, inv_ne_zero, isClosedEmbedding, isClosedEmbedding.tendsto_cocompact.comp, mod_cast, sq_add_sq_ne_zero, tendsto_cocompact, tendsto_norm_cocompact_atTop, tendsto_norm_cocompact_atTop.comp
-/
theorem tendsto_abs_re_smul {p : Fin 2 -> Int} (hp : IsCoprime (p 0) (p 1)) :
    Tendsto
      (fun g : { g : SL(2, Int) // g 1 = p } => |((g : SL(2, Int)) • z).re|) cofinite atTop := by
  suffices
    Tendsto (fun g : (fun g : SL(2, Int) => g 1) ⁻¹' {p} => ((g : SL(2, Int)) • z).re) cofinite
      (cocompact Real)
    tendsto_norm_cocompact_atTop.comp this
  have : ((p 0 : Real) ^ 2 + (p 1 : Real) ^ 2)⁻¹ != 0 := by
    apply inv_ne_zero
    exact mod_cast hp.sq_add_sq_ne_zero
  let f := Homeomorph.mulRight₀ _ this
  let ff := Homeomorph.addRight
    (((p 1 : Complex) * z - p 0) / (((p 0 : Complex) ^ 2 + (p 1 : Complex) ^ 2) * (p 0 * z + p 1))).re
  convert! (f.trans ff).isClosedEmbedding.tendsto_cocompact.comp (tendsto_lcRow0 hp) with _ _ g
  change
    ((g : SL(2, Int)) • z).re =
      lcRow0 p ↑(↑g : SL(2, Real)) / ((p 0 : Real) ^ 2 + (p 1 : Real) ^ 2) +
        Complex.re (((p 1 : Complex) * z - p 0) / (((p 0 : Complex) ^ 2 + (p 1 : Complex) ^ 2) * (p 0 * z + p 1)))
  exact mod_cast congr_arg Complex.re (smul_eq_lcRow0_add z hp g.2)

end TendstoLemmas

section FundamentalDomain


attribute [local simp] UpperHalfPlane.coe_specialLinearGroup_apply

/--
theorem `exists_max_im` / 定理 `exists_max_im`

English:
theorem exists_max_im
  statement: exists g : SL(2, Int), forall g' : SL(2, Int), (g' • z).im <= (g • z).im
  proof: by
  let s : Set (Fin 2 -> Int) := {cd | IsCoprime (cd 0) (cd 1)}
  have hs : s.Nonempty := ⟨![1, 1], isCoprime_one_left⟩
  obtain ⟨p, hp_coprime, hp⟩ :=
    Filter.Tendsto.exists_within_forall_le hs (tendsto_normSq_coprime_pair z)
  obtain ⟨g, -, hg⟩ := bottom_row_surj hp_coprime
  refine ⟨g, fun g

中文:
定理 exists_max_im
  结论: 存在 g : SL(2, 整数), 对任意 g' : SL(2, 整数), (g' • z).im <= (g • z).im
  证明: by
  let s : Set (Fin 2 -> Int) := {cd | IsCoprime (cd 0) (cd 1)}
  have hs : s.Nonempty := ⟨![1, 1], isCoprime_one_left⟩
  obtain ⟨p, hp_coprime, hp⟩ :=
    Filter.Tendsto.exists_within_forall_le hs (tendsto_normSq_coprime_pair z)
  obtain ⟨g, -, hg⟩ := bottom_row_surj hp_coprime
  refine ⟨g, fun g

Depends on / 依赖: Filter, Filter.Tendsto.exists_within_forall_le, IsCoprime, ModularGroup, ModularGroup.im_smul_eq_div_normSq, Nonempty, Tendsto, bottom_row_coprime, bottom_row_surj, div_le_div_iff_of_pos_left, exists_within_forall_le, hp_coprime, im_pos, im_smul_eq_div_normSq, isCoprime_one_left, normSq_den, s.Nonempty, tendsto_normSq_coprime_pair, z.im_pos
-/
theorem exists_max_im : exists g : SL(2, Int), forall g' : SL(2, Int), (g' • z).im <= (g • z).im := by
  let s : Set (Fin 2 -> Int) := {cd | IsCoprime (cd 0) (cd 1)}
  have hs : s.Nonempty := ⟨![1, 1], isCoprime_one_left⟩
  obtain ⟨p, hp_coprime, hp⟩ :=
    Filter.Tendsto.exists_within_forall_le hs (tendsto_normSq_coprime_pair z)
  obtain ⟨g, -, hg⟩ := bottom_row_surj hp_coprime
  refine ⟨g, fun g' => ?_⟩
  rw [ModularGroup.im_smul_eq_div_normSq]; rw [ModularGroup.im_smul_eq_div_normSq]; rw [div_le_div_iff_of_pos_left]
  · simpa [← hg] using! hp (g' 1) (bottom_row_coprime g')
  · exact z.im_pos
  · exact normSq_denom_pos g' z.im_ne_zero
  · exact normSq_denom_pos g z.im_ne_zero

/--
theorem `exists_row_one_eq_and_min_re` / 定理 `exists_row_one_eq_and_min_re`

English:
theorem exists_row_one_eq_and_min_re
  given: {cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (cd 1))
  proof: by
  have : Nonempty { g : SL(2, Int) // g 1 = cd } :=
    let ⟨x, hx⟩ := bottom_row_surj hcd
    ⟨⟨x, hx.2⟩⟩
  obtain ⟨g, hg⟩ := Filter.Tendsto.exists_forall_le (tendsto_abs_re_smul z hcd)
  refine ⟨g, g.2, ?_⟩
  intro g1 hg1
  have : g1 in (fun g : SL(2, Int) => g 1) ⁻¹' {cd} := by
    rw [Set.mem

中文:
定理 exists_row_one_eq_and_min_re
  条件: {cd : Fin 2 -> 整数} (hcd : IsCoprime (cd 0) (cd 1))
  证明: by
  have : Nonempty { g : SL(2, Int) // g 1 = cd } :=
    let ⟨x, hx⟩ := bottom_row_surj hcd
    ⟨⟨x, hx.2⟩⟩
  obtain ⟨g, hg⟩ := Filter.Tendsto.exists_forall_le (tendsto_abs_re_smul z hcd)
  refine ⟨g, g.2, ?_⟩
  intro g1 hg1
  have : g1 in (fun g : SL(2, Int) => g 1) ⁻¹' {cd} := by
    rw [Set.mem

Depends on / 依赖: Eq.trans, Filter, Filter.Tendsto.exists_forall_le, Nonempty, Set.mem_preimage, Set.mem_preimage.mp, Set.mem_singleton_iff, Set.mem_singleton_iff.mp, Tendsto, bottom_row_surj, exists_forall_le, hg1.symm, mem_preimage, mem_singleton_iff, tendsto_abs_re_smul
-/
theorem exists_row_one_eq_and_min_re {cd : Fin 2 -> Int} (hcd : IsCoprime (cd 0) (cd 1)) :
    exists g : SL(2, Int), g 1 = cd ∧ forall g' : SL(2, Int), g 1 = g' 1 ->
      |(g • z).re| <= |(g' • z).re| := by
  have : Nonempty { g : SL(2, Int) // g 1 = cd } :=
    let ⟨x, hx⟩ := bottom_row_surj hcd
    ⟨⟨x, hx.2⟩⟩
  obtain ⟨g, hg⟩ := Filter.Tendsto.exists_forall_le (tendsto_abs_re_smul z hcd)
  refine ⟨g, g.2, ?_⟩
  intro g1 hg1
  have : g1 in (fun g : SL(2, Int) => g 1) ⁻¹' {cd} := by
    rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]
    exact Eq.trans hg1.symm (Set.mem_singleton_iff.mp (Set.mem_preimage.mp g.2))
  exact hg ⟨g1, this⟩

/--
theorem `coe_T_zpow_smul_eq` / 定理 `coe_T_zpow_smul_eq`

English:
theorem coe_T_zpow_smul_eq
  given: {n : Int}
  statement: (↑(T ^ n • z) : Complex) = z + n
  proof: by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [coe_T_zpow, -map_zpow]

中文:
定理 coe_T_zpow_smul_eq
  条件: {n : 整数}
  结论: (↑(T ^ n • z) : Complex) = z + n
  证明: by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [coe_T_zpow, -map_zpow]

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.coe_specialLinearGroup_apply, coe_T_zpow, coe_specialLinearGroup_apply, map_zpow
-/
theorem coe_T_zpow_smul_eq {n : Int} : (↑(T ^ n • z) : Complex) = z + n := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [coe_T_zpow, -map_zpow]

/--
theorem `re_T_zpow_smul` / 定理 `re_T_zpow_smul`

English:
theorem re_T_zpow_smul
  given: (n : Int)
  statement: (T ^ n • z).re = z.re + n
  proof: by
  rw [← coe_re]; rw [coe_T_zpow_smul_eq]; rw [add_re]; rw [intCast_re]; rw [coe_re]

中文:
定理 re_T_zpow_smul
  条件: (n : 整数)
  结论: (T ^ n • z).re = z.re + n
  证明: by
  rw [← coe_re]; rw [coe_T_zpow_smul_eq]; rw [add_re]; rw [intCast_re]; rw [coe_re]

Depends on / 依赖: add_re, coe_T_zpow_smul_eq, coe_re, intCast_re
-/
theorem re_T_zpow_smul (n : Int) : (T ^ n • z).re = z.re + n := by
  rw [← coe_re]; rw [coe_T_zpow_smul_eq]; rw [add_re]; rw [intCast_re]; rw [coe_re]

/--
theorem `im_T_zpow_smul` / 定理 `im_T_zpow_smul`

English:
theorem im_T_zpow_smul
  given: (n : Int)
  statement: (T ^ n • z).im = z.im
  proof: by
  rw [← coe_im]; rw [coe_T_zpow_smul_eq]; rw [add_im]; rw [intCast_im]; rw [add_zero]; rw [coe_im]

中文:
定理 im_T_zpow_smul
  条件: (n : 整数)
  结论: (T ^ n • z).im = z.im
  证明: by
  rw [← coe_im]; rw [coe_T_zpow_smul_eq]; rw [add_im]; rw [intCast_im]; rw [add_zero]; rw [coe_im]

Depends on / 依赖: add_im, add_zero, coe_T_zpow_smul_eq, coe_im, intCast_im
-/
theorem im_T_zpow_smul (n : Int) : (T ^ n • z).im = z.im := by
  rw [← coe_im]; rw [coe_T_zpow_smul_eq]; rw [add_im]; rw [intCast_im]; rw [add_zero]; rw [coe_im]

/--
theorem `re_T_smul` / 定理 `re_T_smul`

English:
theorem re_T_smul
  statement: (T • z).re = z.re + 1
  proof: by simpa using re_T_zpow_smul z 1

中文:
定理 re_T_smul
  结论: (T • z).re = z.re + 1
  证明: by simpa using re_T_zpow_smul z 1

Depends on / 依赖: re_T_zpow_smul
-/
theorem re_T_smul : (T • z).re = z.re + 1 := by simpa using re_T_zpow_smul z 1

/--
theorem `im_T_smul` / 定理 `im_T_smul`

English:
theorem im_T_smul
  statement: (T • z).im = z.im
  proof: by simpa using im_T_zpow_smul z 1

中文:
定理 im_T_smul
  结论: (T • z).im = z.im
  证明: by simpa using im_T_zpow_smul z 1

Depends on / 依赖: im_T_zpow_smul
-/
theorem im_T_smul : (T • z).im = z.im := by simpa using im_T_zpow_smul z 1

/--
theorem `re_T_inv_smul` / 定理 `re_T_inv_smul`

English:
theorem re_T_inv_smul
  statement: (T⁻¹ • z).re = z.re - 1
  proof: by simpa using! re_T_zpow_smul z (-1)

中文:
定理 re_T_inv_smul
  结论: (T⁻¹ • z).re = z.re - 1
  证明: by simpa using! re_T_zpow_smul z (-1)

Depends on / 依赖: re_T_zpow_smul
-/
theorem re_T_inv_smul : (T⁻¹ • z).re = z.re - 1 := by simpa using! re_T_zpow_smul z (-1)

/--
theorem `im_T_inv_smul` / 定理 `im_T_inv_smul`

English:
theorem im_T_inv_smul
  statement: (T⁻¹ • z).im = z.im
  proof: by simpa using im_T_zpow_smul z (-1)

中文:
定理 im_T_inv_smul
  结论: (T⁻¹ • z).im = z.im
  证明: by simpa using im_T_zpow_smul z (-1)

Depends on / 依赖: im_T_zpow_smul
-/
theorem im_T_inv_smul : (T⁻¹ • z).im = z.im := by simpa using im_T_zpow_smul z (-1)

variable {z}

-- If instead we had `g` and `T` of type `PSL(2, ℤ)`, then we could simply state `g = T^n`.
/--
theorem `exists_eq_T_zpow_of_c_eq_zero` / 定理 `exists_eq_T_zpow_of_c_eq_zero`

English:
theorem exists_eq_T_zpow_of_c_eq_zero
  given: (hc : g 1 0 = 0)
  proof: by
  have had := g.det_coe
  replace had : g 0 0 * g 1 1 = 1 := by rw [det_fin_two, hc] at had; lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · use g 0 1
    suffices g = T ^ g 0 1 by intro z; conv_lhs => rw [this]
    ext i j; fin_cases i <;> fin_cases j <;>
   

中文:
定理 exists_eq_T_zpow_of_c_eq_zero
  条件: (hc : g 1 0 = 0)
  证明: by
  have had := g.det_coe
  replace had : g 0 0 * g 1 1 = 1 := by rw [det_fin_two, hc] at had; lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · use g 0 1
    suffices g = T ^ g 0 1 by intro z; conv_lhs => rw [this]
    ext i j; fin_cases i <;> fin_cases j <;>
   

Depends on / 依赖: Int.eq_one_or_neg_one_of_mul_eq_one, SL_neg_smul, coe_T_zpow, conv_lhs, det_coe, det_fin_two, eq_one_or_neg_one_of_mul_eq_one, fin_cases, g.det_coe, replace
-/
theorem exists_eq_T_zpow_of_c_eq_zero (hc : g 1 0 = 0) :
    exists n : Int, forall z : ℍ, g • z = T ^ n • z := by
  have had := g.det_coe
  replace had : g 0 0 * g 1 1 = 1 := by rw [det_fin_two, hc] at had; lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · use g 0 1
    suffices g = T ^ g 0 1 by intro z; conv_lhs => rw [this]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · use -(g 0 1)
    suffices g = -T ^ (-(g 0 1)) by intro z; conv_lhs => rw [this, SL_neg_smul]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]

-- If `c = 1`, then `g` factorises into a product terms involving only `T` and `S`.
/--
theorem `g_eq_of_c_eq_one` / 定理 `g_eq_of_c_eq_one`

English:
theorem g_eq_of_c_eq_one
  given: (hc : g 1 0 = 1)
  statement: g = T ^ g 0 0 * S * T ^ g 1 1
  proof: by
  have hg := g.det_coe.symm
  replace hg : g 0 1 = g 0 0 * g 1 1 - 1 := by rw [det_fin_two, hc] at hg; lia
  refine Subtype.ext ?_
  conv_lhs => rw [(g : Matrix _ _ Int).eta_fin_two]
  simp only [hg, sub_eq_add_neg, hc, coe_mul, coe_T_zpow, coe_S, mul_fin_two, mul_zero, mul_one,
    zero_add, one

中文:
定理 g_eq_of_c_eq_one
  条件: (hc : g 1 0 = 1)
  结论: g = T ^ g 0 0 * S * T ^ g 1 1
  证明: by
  have hg := g.det_coe.symm
  replace hg : g 0 1 = g 0 0 * g 1 1 - 1 := by rw [det_fin_two, hc] at hg; lia
  refine Subtype.ext ?_
  conv_lhs => rw [(g : Matrix _ _ Int).eta_fin_two]
  simp only [hg, sub_eq_add_neg, hc, coe_mul, coe_T_zpow, coe_S, mul_fin_two, mul_zero, mul_one,
    zero_add, one

Depends on / 依赖: Matrix, Subtype, Subtype.ext, add_zero, coe_S, coe_T_zpow, coe_mul, conv_lhs, det_coe, det_fin_two, eta_fin_two, g.det_coe.symm, mul_fin_two, mul_one, mul_zero, one_mul, replace, sub_eq_add_neg, zero_add, zero_mul
-/
theorem g_eq_of_c_eq_one (hc : g 1 0 = 1) : g = T ^ g 0 0 * S * T ^ g 1 1 := by
  have hg := g.det_coe.symm
  replace hg : g 0 1 = g 0 0 * g 1 1 - 1 := by rw [det_fin_two, hc] at hg; lia
  refine Subtype.ext ?_
  conv_lhs => rw [(g : Matrix _ _ Int).eta_fin_two]
  simp only [hg, sub_eq_add_neg, hc, coe_mul, coe_T_zpow, coe_S, mul_fin_two, mul_zero, mul_one,
    zero_add, one_mul, add_zero, zero_mul]

/--
theorem `normSq_S_smul_lt_one` / 定理 `normSq_S_smul_lt_one`

English:
theorem normSq_S_smul_lt_one
  given: (h : 1 < normSq z)
  statement: normSq ↑(S • z) < 1
  proof: by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simpa [coe_S, num, denom] using (inv_lt_inv₀ z.normSq_pos zero_lt_one).mpr h

中文:
定理 normSq_S_smul_lt_one
  条件: (h : 1 < normSq z)
  结论: normSq ↑(S • z) < 1
  证明: by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simpa [coe_S, num, denom] using (inv_lt_inv₀ z.normSq_pos zero_lt_one).mpr h

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.coe_specialLinearGroup_apply, coe_S, coe_specialLinearGroup_apply, normSq_pos, z.normSq_pos, zero_lt_one
-/
theorem normSq_S_smul_lt_one (h : 1 < normSq z) : normSq ↑(S • z) < 1 := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simpa [coe_S, num, denom] using (inv_lt_inv₀ z.normSq_pos zero_lt_one).mpr h

/--
theorem `im_lt_im_S_smul` / 定理 `im_lt_im_S_smul`

English:
theorem im_lt_im_S_smul
  given: (h : normSq z < 1)
  statement: z.im < (S • z).im
  proof: by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have : z.im < z.im / normSq (z : Complex) := by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff₀ z.normSq_pos).mpr
    nlinarith
  simpa [denom, coe_S, SpecialLinearGroup.toGL]

中文:
定理 im_lt_im_S_smul
  条件: (h : normSq z < 1)
  结论: z.im < (S • z).im
  证明: by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have : z.im < z.im / normSq (z : Complex) := by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff₀ z.normSq_pos).mpr
    nlinarith
  simpa [denom, coe_S, SpecialLinearGroup.toGL]

Depends on / 依赖: ModularGroup, ModularGroup.im_smul_eq_div_normSq, SpecialLinearGroup, SpecialLinearGroup.toGL, coe_S, im_pos, im_smul_eq_div_normSq, normSq, normSq_pos, z.im, z.normSq_pos
-/
theorem im_lt_im_S_smul (h : normSq z < 1) : z.im < (S • z).im := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have : z.im < z.im / normSq (z : Complex) := by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff₀ z.normSq_pos).mpr
    nlinarith
  simpa [denom, coe_S, SpecialLinearGroup.toGL]

/--
Definition of `fd` / `fd` 的定义

English:
definition fd
  signature: : Set ℍ
  body: {z | 1 <= normSq (z : Complex) ∧ |z.re| <= (1 : Real) / 2}

中文:
定义 fd
  签名: : Set ℍ
  定义体: {z | 1 <= normSq (z : Complex) ∧ |z.re| <= (1 : Real) / 2}

Depends on / 依赖: normSq, z.re
-/
def fd : Set ℍ :=
  {z | 1 <= normSq (z : Complex) ∧ |z.re| <= (1 : Real) / 2}

/--
Definition of `fdo` / `fdo` 的定义

English:
definition fdo
  signature: : Set ℍ
  body: {z | 1 < normSq (z : Complex) ∧ |z.re| < (1 : Real) / 2}

@[inherit_doc ModularGroup.fd]
scoped[Modular] notation "𝒟" => ModularGroup.fd

@[inherit_doc ModularGroup.fdo]
scoped[Modular] notation "𝒟ᵒ" => ModularGroup.fdo

中文:
定义 fdo
  签名: : Set ℍ
  定义体: {z | 1 < normSq (z : Complex) ∧ |z.re| < (1 : Real) / 2}

@[inherit_doc ModularGroup.fd]
scoped[Modular] notation "𝒟" => ModularGroup.fd

@[inherit_doc ModularGroup.fdo]
scoped[Modular] notation "𝒟ᵒ" => ModularGroup.fdo

Depends on / 依赖: normSq, z.re
-/
def fdo : Set ℍ :=
  {z | 1 < normSq (z : Complex) ∧ |z.re| < (1 : Real) / 2}

@[inherit_doc ModularGroup.fd]
scoped[Modular] notation "𝒟" => ModularGroup.fd

@[inherit_doc ModularGroup.fdo]
scoped[Modular] notation "𝒟ᵒ" => ModularGroup.fdo

open scoped Modular

/--
lemma `fdo_subset_fd` / 引理 `fdo_subset_fd`

English:
lemma fdo_subset_fd
  statement: 𝒟ᵒ subseteq 𝒟
  proof: fun _ ⟨hx, hx'⟩ => ⟨hx.le, hx'.le⟩

中文:
引理 fdo_subset_fd
  结论: 𝒟ᵒ subseteq 𝒟
  证明: fun _ ⟨hx, hx'⟩ => ⟨hx.le, hx'.le⟩

Depends on / 依赖: hx.le
-/
lemma fdo_subset_fd : 𝒟ᵒ subseteq 𝒟 := fun _ ⟨hx, hx'⟩ => ⟨hx.le, hx'.le⟩

/--
lemma `ρ_mem_fd` / 引理 `ρ_mem_fd`

English:
lemma ρ_mem_fd
  statement: ρ in 𝒟
  proof: by
  constructor <;> norm_num [ρ, ← pow_two, div_pow]

中文:
引理 ρ_mem_fd
  结论: ρ in 𝒟
  证明: by
  constructor <;> norm_num [ρ, ← pow_two, div_pow]

Depends on / 依赖: div_pow, pow_two
-/
lemma ρ_mem_fd : ρ in 𝒟 := by
  constructor <;> norm_num [ρ, ← pow_two, div_pow]

/--
lemma `I_mem_fd` / 引理 `I_mem_fd`

English:
lemma I_mem_fd
  statement: I in 𝒟
  proof: by
  constructor <;> norm_num

中文:
引理 I_mem_fd
  结论: I in 𝒟
  证明: by
  constructor <;> norm_num
-/
lemma I_mem_fd : I in 𝒟 := by
  constructor <;> norm_num

/--
theorem `abs_two_mul_re_lt_one_of_mem_fdo` / 定理 `abs_two_mul_re_lt_one_of_mem_fdo`

English:
theorem abs_two_mul_re_lt_one_of_mem_fdo
  given: (h : z in 𝒟ᵒ)
  statement: |2 * z.re| < 1
  proof: by
  rw [abs_mul]; rw [abs_two]; rw [← lt_div_iff₀' (zero_lt_two' Real)]
  exact h.2

中文:
定理 abs_two_mul_re_lt_one_of_mem_fdo
  条件: (h : z in 𝒟ᵒ)
  结论: |2 * z.re| < 1
  证明: by
  rw [abs_mul]; rw [abs_two]; rw [← lt_div_iff₀' (zero_lt_two' Real)]
  exact h.2

Depends on / 依赖: abs_mul, abs_two, zero_lt_two
-/
theorem abs_two_mul_re_lt_one_of_mem_fdo (h : z in 𝒟ᵒ) : |2 * z.re| < 1 := by
  rw [abs_mul]; rw [abs_two]; rw [← lt_div_iff₀' (zero_lt_two' Real)]
  exact h.2

/--
theorem `three_lt_four_mul_im_sq_of_mem_fdo` / 定理 `three_lt_four_mul_im_sq_of_mem_fdo`

English:
theorem three_lt_four_mul_im_sq_of_mem_fdo
  given: (h : z in 𝒟ᵒ)
  statement: 3 < 4 * z.im ^ 2
  proof: by
  have : 1 < z.re * z.re + z.im * z.im := by simpa [Complex.normSq_apply] using h.1
  have := h.2
  cases abs_cases z.re <;> nlinarith

中文:
定理 three_lt_four_mul_im_sq_of_mem_fdo
  条件: (h : z in 𝒟ᵒ)
  结论: 3 < 4 * z.im ^ 2
  证明: by
  have : 1 < z.re * z.re + z.im * z.im := by simpa [Complex.normSq_apply] using h.1
  have := h.2
  cases abs_cases z.re <;> nlinarith

Depends on / 依赖: Complex.normSq_apply, abs_cases, normSq_apply, z.im, z.re
-/
theorem three_lt_four_mul_im_sq_of_mem_fdo (h : z in 𝒟ᵒ) : 3 < 4 * z.im ^ 2 := by
  have : 1 < z.re * z.re + z.im * z.im := by simpa [Complex.normSq_apply] using h.1
  have := h.2
  cases abs_cases z.re <;> nlinarith

/--
theorem `three_le_four_mul_im_sq_of_mem_fd` / 定理 `three_le_four_mul_im_sq_of_mem_fd`

English:
theorem three_le_four_mul_im_sq_of_mem_fd
  given: {τ : ℍ} (h : τ in 𝒟)
  statement: 3 <= 4 * τ.im ^ 2
  proof: by
  have : 1 <= τ.re * τ.re + τ.im * τ.im := by simpa [Complex.normSq_apply] using h.1
  cases abs_cases τ.re <;> nlinarith [h.2]

中文:
定理 three_le_four_mul_im_sq_of_mem_fd
  条件: {τ : ℍ} (h : τ in 𝒟)
  结论: 3 <= 4 * τ.im ^ 2
  证明: by
  have : 1 <= τ.re * τ.re + τ.im * τ.im := by simpa [Complex.normSq_apply] using h.1
  cases abs_cases τ.re <;> nlinarith [h.2]

Depends on / 依赖: Complex.normSq_apply, abs_cases, normSq_apply
-/
theorem three_le_four_mul_im_sq_of_mem_fd {τ : ℍ} (h : τ in 𝒟) : 3 <= 4 * τ.im ^ 2 := by
  have : 1 <= τ.re * τ.re + τ.im * τ.im := by simpa [Complex.normSq_apply] using h.1
  cases abs_cases τ.re <;> nlinarith [h.2]

/--
theorem `one_lt_normSq_T_zpow_smul` / 定理 `one_lt_normSq_T_zpow_smul`

English:
theorem one_lt_normSq_T_zpow_smul
  given: (hz : z in 𝒟ᵒ) (n : Int)
  statement: 1 < normSq (T ^ n • z : ℍ)
  proof: by
  rw [coe_T_zpow_smul_eq]
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1
  have hzn := Int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le
  have : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im := by linarith
  simpa [normSq, num, denom]

中文:
定理 one_lt_normSq_T_zpow_smul
  条件: (hz : z in 𝒟ᵒ) (n : 整数)
  结论: 1 < normSq (T ^ n • z : ℍ)
  证明: by
  rw [coe_T_zpow_smul_eq]
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1
  have hzn := Int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le
  have : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im := by linarith
  simpa [normSq, num, denom]

Depends on / 依赖: Int.nneg_mul_add_sq_of_abs_le_one, abs_two_mul_re_lt_one_of_mem_fdo, coe_T_zpow_smul_eq, nneg_mul_add_sq_of_abs_le_one, normSq, z.im, z.re
-/
theorem one_lt_normSq_T_zpow_smul (hz : z in 𝒟ᵒ) (n : Int) : 1 < normSq (T ^ n • z : ℍ) := by
  rw [coe_T_zpow_smul_eq]
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1
  have hzn := Int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le
  have : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im := by linarith
  simpa [normSq, num, denom]

/--
theorem `eq_zero_of_mem_fdo_of_T_zpow_mem_fdo` / 定理 `eq_zero_of_mem_fdo_of_T_zpow_mem_fdo`

English:
theorem eq_zero_of_mem_fdo_of_T_zpow_mem_fdo
  given: {n : Int} (hz : z in 𝒟ᵒ) (hg : T ^ n • z in 𝒟ᵒ)
  proof: by
  suffices |(n : Real)| < 1 by
    rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this
  have h₁ := hz.2
  have h₂ := hg.2
  rw [re_T_zpow_smul] at h₂
  calc
    |(n : Real)| <= |z.re| + |z.re + (n : Real)| := abs_add' (n : Real) z.re
    _ < 1 / 2 + 1 / 2 := add_lt_add 

中文:
定理 eq_zero_of_mem_fdo_of_T_zpow_mem_fdo
  条件: {n : 整数} (hz : z in 𝒟ᵒ) (hg : T ^ n • z in 𝒟ᵒ)
  证明: by
  suffices |(n : Real)| < 1 by
    rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this
  have h₁ := hz.2
  have h₂ := hg.2
  rw [re_T_zpow_smul] at h₂
  calc
    |(n : Real)| <= |z.re| + |z.re + (n : Real)| := abs_add' (n : Real) z.re
    _ < 1 / 2 + 1 / 2 := add_lt_add 

Depends on / 依赖: Int.abs_lt_one_iff, Int.cast_abs, Int.cast_lt, Int.cast_one, abs_add, abs_lt_one_iff, add_halves, add_lt_add, cast_abs, cast_lt, cast_one, re_T_zpow_smul, z.re
-/
theorem eq_zero_of_mem_fdo_of_T_zpow_mem_fdo {n : Int} (hz : z in 𝒟ᵒ) (hg : T ^ n • z in 𝒟ᵒ) :
    n = 0 := by
  suffices |(n : Real)| < 1 by
    rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this
  have h₁ := hz.2
  have h₂ := hg.2
  rw [re_T_zpow_smul] at h₂
  calc
    |(n : Real)| <= |z.re| + |z.re + (n : Real)| := abs_add' (n : Real) z.re
    _ < 1 / 2 + 1 / 2 := add_lt_add h₁ h₂
    _ = 1 := add_halves 1

/--
theorem `exists_smul_mem_fd` / 定理 `exists_smul_mem_fd`

English:
theorem exists_smul_mem_fd
  given: (z : ℍ)
  statement: exists g : SL(2, Int), g • z in 𝒟
  proof: by
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_max_im z
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_row_one_eq_and_min_re z (bottom_row_coprime g₀)
  refine ⟨g, ?_⟩
  -- `g` has same max im property as `g₀`
  have hg₀' : forall g' : SL(2, Int), (g

中文:
定理 exists_smul_mem_fd
  条件: (z : ℍ)
  结论: 存在 g : SL(2, 整数), g • z in 𝒟
  证明: by
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_max_im z
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_row_one_eq_and_min_re z (bottom_row_coprime g₀)
  refine ⟨g, ?_⟩
  -- `g` has same max im property as `g₀`
  have hg₀' : forall g' : SL(2, Int), (g
-/
theorem exists_smul_mem_fd (z : ℍ) : exists g : SL(2, Int), g • z in 𝒟 := by
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_max_im z
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_row_one_eq_and_min_re z (bottom_row_coprime g₀)
  refine ⟨g, ?_⟩
  -- `g` has same max im property as `g₀`
  have hg₀' : forall g' : SL(2, Int), (g' • z).im <= (g • z).im := by
    have hg'' : (g • z).im = (g₀ • z).im := by
      rw [ModularGroup.im_smul_eq_div_normSq]; rw [ModularGroup.im_smul_eq_div_normSq]; rw [denom_apply]; rw [denom_apply]; rw [hg]
    simpa only [hg''] using hg₀
  constructor
  · -- Claim: `1 ≤ ⇑norm_sq ↑(g • z)`. If not, then `S•g•z` has larger imaginary part
    contrapose! hg₀'
    refine ⟨S * g, ?_⟩
    rw [mul_smul]
    exact im_lt_im_S_smul hg₀'
  · change |(g • z).re| <= 1 / 2
    -- if not, then either `T` or `T'` decrease |Re|.
    rw [abs_le]
    constructor
    · contrapose! hg'
      refine ⟨T * g, (T_mul_apply_one _).symm, ?_⟩
      rw [mul_smul]; rw [re_T_smul]
      cases abs_cases ((g • z).re + 1) <;> cases abs_cases (g • z).re <;> linarith
    · contrapose! hg'
      refine ⟨T⁻¹ * g, (T_inv_mul_apply_one _).symm, ?_⟩
      rw [mul_smul]; rw [re_T_inv_smul]
      cases abs_cases ((g • z).re - 1) <;> cases abs_cases (g • z).re <;> linarith

section UniqueRepresentative

/--
theorem `abs_c_le_one` / 定理 `abs_c_le_one`

English:
theorem abs_c_le_one
  given: (hz : z in 𝒟) (hg : g • z in 𝒟)
  statement: |g 1 0| <= 1
  proof: by
  let c' : Int := g 1 0
  let c := (c' : Real)
  suffices 3 * c ^ 2 <= 4 by
    rw [← Int.cast_pow]; rw [← Int.cast_three]; rw [← Int.cast_four]; rw [← Int.cast_mul]; rw [Int.cast_le] at this
    replace this : c' ^ 2 <= 1 ^ 2 := by lia
    rwa [sq_le_sq, abs_one] at this
  suffices c != 0 -> 9 *

中文:
定理 abs_c_le_one
  条件: (hz : z in 𝒟) (hg : g • z in 𝒟)
  结论: |g 1 0| <= 1
  证明: by
  let c' : Int := g 1 0
  let c := (c' : Real)
  suffices 3 * c ^ 2 <= 4 by
    rw [← Int.cast_pow]; rw [← Int.cast_three]; rw [← Int.cast_four]; rw [← Int.cast_mul]; rw [Int.cast_le] at this
    replace this : c' ^ 2 <= 1 ^ 2 := by lia
    rwa [sq_le_sq, abs_one] at this
  suffices c != 0 -> 9 *

Depends on / 依赖: Int.cast_four, Int.cast_le, Int.cast_mul, Int.cast_pow, Int.cast_three, abs_one, cast_four, cast_le, cast_mul, cast_pow, cast_three, eq_or_ne, le_of_sq_le_sq, replace, sq_le_sq, three_le_four_mul_im_, z.im
-/
theorem abs_c_le_one (hz : z in 𝒟) (hg : g • z in 𝒟) : |g 1 0| <= 1 := by
  let c' : Int := g 1 0
  let c := (c' : Real)
  suffices 3 * c ^ 2 <= 4 by
    rw [← Int.cast_pow]; rw [← Int.cast_three]; rw [← Int.cast_four]; rw [← Int.cast_mul]; rw [Int.cast_le] at this
    replace this : c' ^ 2 <= 1 ^ 2 := by lia
    rwa [sq_le_sq, abs_one] at this
  suffices c != 0 -> 9 * c ^ 4 <= 16 by
    rcases eq_or_ne c 0 with (hc | hc)
    · simp [hc]
    · apply le_of_sq_le_sq <;> grind
  intro hc
  have h₁ : 3 * 3 * c ^ 4 <= 4 * (g • z).im ^ 2 * (4 * z.im ^ 2) * c ^ 4 := by
    gcongr <;> exact three_le_four_mul_im_sq_of_mem_fd (by assumption)
  have h₂ : (c * z.im) ^ 4 / normSq (denom (↑g) z) ^ 2 <= 1 :=
    div_le_one_of_le₀
      (pow_four_le_pow_two_of_pow_two_le (z.c_mul_im_sq_le_normSq_denom g)) (sq_nonneg _)
  calc
    9 * c ^ 4 <= c ^ 4 * z.im ^ 2 * (g • z).im ^ 2 * 16 := by linarith
    _ = c ^ 4 * z.im ^ 4 / normSq (denom g z) ^ 2 * 16 := by grind [im_smul_eq_div_normSq]
    _ <= 16 := by rw [← mul_pow]; linarith

/--
lemma `cases_c_zero` / 引理 `cases_c_zero`

English:
lemma cases_c_zero
  given: (hz : z in 𝒟) (hg : g • z in 𝒟) (hc : g 1 0 = 0)
  proof: by
  wlog hd : 0 <= g 1 1
  · specialize this hz (g := -g) (SL_neg_smul g z ▸ hg) (by simpa using hc) ?_
    · simpa using (not_le.mp hd).le
    convert! this using 2 <;> simp [neg_eq_iff_eq_neg, or_comm]
  have hd' : g 1 1 = 1 ∨ g 1 1 = -1 := by
    simpa [hc, isCoprime_zero_left, Int.isUnit_iff] u

中文:
引理 cases_c_zero
  条件: (hz : z in 𝒟) (hg : g • z in 𝒟) (hc : g 1 0 = 0)
  证明: by
  wlog hd : 0 <= g 1 1
  · specialize this hz (g := -g) (SL_neg_smul g z ▸ hg) (by simpa using hc) ?_
    · simpa using (not_le.mp hd).le
    convert! this using 2 <;> simp [neg_eq_iff_eq_neg, or_comm]
  have hd' : g 1 1 = 1 ∨ g 1 1 = -1 := by
    simpa [hc, isCoprime_zero_left, Int.isUnit_iff] u
-/
private lemma cases_c_zero (hz : z in 𝒟) (hg : g • z in 𝒟) (hc : g 1 0 = 0) :
    ((g = T ∨ g = -T) ∧ z.re = -1 / 2) ∨
    ((g = T⁻¹ ∨ g = -T⁻¹) ∧ z.re = 1 / 2) ∨
    (g = 1 ∨ g = -1) := by
  wlog hd : 0 <= g 1 1
  · specialize this hz (g := -g) (SL_neg_smul g z ▸ hg) (by simpa using hc) ?_
    · simpa using (not_le.mp hd).le
    convert! this using 2 <;> simp [neg_eq_iff_eq_neg, or_comm]
  have hd' : g 1 1 = 1 ∨ g 1 1 = -1 := by
    simpa [hc, isCoprime_zero_left, Int.isUnit_iff] using bottom_row_coprime g
  replace hd : g 1 1 = 1 := by grind
  have ha : g 0 0 = 1 := by grind [det_fin_two, g.property]
  let b := g 0 1
  have hgz : g = T ^ b := by
    ext i j
    rw [coe_T_zpow]
    fin_cases i <;> fin_cases j <;> tauto
  have hre : (g • z).re = b + z.re := by
    rw [hgz]; rw [← coe_re]; rw [coe_T_zpow_smul_eq]; rw [add_re]; rw [coe_re]; rw [intCast_re]; rw [add_comm]
  have := (abs_sub_abs_le_abs_add ..).trans (hre ▸ hg.2)
  grw [sub_le_iff_le_add, hz.2, add_halves, ← Int.cast_abs, ← Int.cast_one, Int.cast_le,
    Int.abs_le_one_iff] at this
  rcases this with hb | hb | hb <;> rw [hb] at hgz
  · rw [hgz]
    simp
  · left
    rw [hgz]; rw [zpow_one]; rw [eq_self_iff_true]; rw [true_or]; rw [true_and]
    rw [hb]; rw [Int.cast_one] at hre
    linarith [(le_abs_self _).trans (abs_neg z.re ▸ hz.2), (le_abs_self _).trans hg.2]
  · right
    left
    rw [hgz]; rw [zpow_neg_one]; rw [eq_self_iff_true]; rw [true_or]; rw [true_and]
    rw [hb]; rw [Int.cast_neg]; rw [Int.cast_one] at hre
    linarith [(le_abs_self _).trans hz.2, (le_abs_self _).trans (abs_neg (g • z).re ▸ hg.2)]

/--
lemma `cases_d_of_c_eq_one` / 引理 `cases_d_of_c_eq_one`

English:
lemma cases_d_of_c_eq_one
  given: (hz : z in 𝒟) (hg' : ‖denom g z‖ <= 1) (hc : g 1 0 = 1)
  proof: by
  have : ‖(z : Complex) + g 1 1‖ <= 1 := by simpa [denom, hc] using hg'
  have := (abs_re_le_norm _).trans this
  rw [add_re]; rw [intCast_re]; rw [add_comm]; rw [coe_re] at this
  have := (abs_sub_abs_le_abs_add ..).trans this
  grw [sub_le_iff_le_add, hz.2, ← Int.cast_abs, ← Int.le_floor] at th

中文:
引理 cases_d_of_c_eq_one
  条件: (hz : z in 𝒟) (hg' : ‖denom g z‖ <= 1) (hc : g 1 0 = 1)
  证明: by
  have : ‖(z : Complex) + g 1 1‖ <= 1 := by simpa [denom, hc] using hg'
  have := (abs_re_le_norm _).trans this
  rw [add_re]; rw [intCast_re]; rw [add_comm]; rw [coe_re] at this
  have := (abs_sub_abs_le_abs_add ..).trans this
  grw [sub_le_iff_le_add, hz.2, ← Int.cast_abs, ← Int.le_floor] at th
-/
private lemma cases_d_of_c_eq_one (hz : z in 𝒟) (hg' : ‖denom g z‖ <= 1) (hc : g 1 0 = 1) :
    |g 1 1| <= 1 := by
  have : ‖(z : Complex) + g 1 1‖ <= 1 := by simpa [denom, hc] using hg'
  have := (abs_re_le_norm _).trans this
  rw [add_re]; rw [intCast_re]; rw [add_comm]; rw [coe_re] at this
  have := (abs_sub_abs_le_abs_add ..).trans this
  grw [sub_le_iff_le_add, hz.2, ← Int.cast_abs, ← Int.le_floor] at this
  convert! this
  rw [eq_comm]; rw [Int.floor_eq_iff]
  norm_num

/--
lemma `cases_c_one_d_zero` / 引理 `cases_c_one_d_zero`

English:
lemma cases_c_one_d_zero
  statement: (hz : z in 𝒟) (hg : g • z in 𝒟) (hg' : ‖denom g z‖ <= 1)
  proof: by
  have hb : g 0 1 = -1 := by
    simpa [-SpecialLinearGroup.det_coe, det_fin_two, hd, hc, neg_eq_iff_eq_neg] using g.property
  have hz' : ‖(z : Complex)‖ = 1 :=
    le_antisymm (by simpa [denom, hc, hd] using hg') (one_le_normSq_iff.mp hz.1)
  have hg' : g = T ^ g 0 0 * S := by
    ext i j
    s

中文:
引理 cases_c_one_d_zero
  结论: (hz : z in 𝒟) (hg : g • z in 𝒟) (hg' : ‖denom g z‖ <= 1)
  证明: by
  have hb : g 0 1 = -1 := by
    simpa [-SpecialLinearGroup.det_coe, det_fin_two, hd, hc, neg_eq_iff_eq_neg] using g.property
  have hz' : ‖(z : Complex)‖ = 1 :=
    le_antisymm (by simpa [denom, hc, hd] using hg') (one_le_normSq_iff.mp hz.1)
  have hg' : g = T ^ g 0 0 * S := by
    ext i j
    s
-/
private lemma cases_c_one_d_zero (hz : z in 𝒟) (hg : g • z in 𝒟) (hg' : ‖denom g z‖ <= 1)
    (hc : g 1 0 = 1) (hd : g 1 1 = 0) :
    (g = S ∧ ‖(z : Complex)‖ = 1) ∨ (g = T⁻¹ * S ∧ z = ρ) ∨ (g = T * S ∧ z = (1 : Real) +ᵥ ρ) := by
  have hb : g 0 1 = -1 := by
    simpa [-SpecialLinearGroup.det_coe, det_fin_two, hd, hc, neg_eq_iff_eq_neg] using g.property
  have hz' : ‖(z : Complex)‖ = 1 :=
    le_antisymm (by simpa [denom, hc, hd] using hg') (one_le_normSq_iff.mp hz.1)
  have hg' : g = T ^ g 0 0 * S := by
    ext i j
    simp only [coe_mul, coe_S, coe_T_zpow, Matrix.mul_fin_two, mul_zero, mul_one, zero_add,
      one_mul, add_zero, zero_mul]
    fin_cases i <;> fin_cases j <;> tauto
  rw [hg']; rw [mul_smul] at hg
  have hSre : re (S • z) = -z.re := by
    rw [modular_S_smul]; rw [← coe_re]; rw [coe_mk]; rw [inv_re]; rw [normSq_eq_norm_sq]; rw [norm_neg]; rw [hz']; rw [one_pow]; rw [div_one]; rw [neg_re]; rw [coe_re]
  have := hg.2
  rw [← coe_re]; rw [coe_T_zpow_smul_eq]; rw [add_re]; rw [intCast_re]; rw [add_comm]; rw [coe_re]; rw [hSre] at this
  have := (abs_sub_abs_le_abs_add _ _).trans this
  rw [abs_neg]; rw [sub_le_iff_le_add] at this
  rcases lt_or_eq_of_le hz.2 with hzre | hzre
  · have := this.trans_lt ((add_lt_add_iff_left _).mpr hzre)
    rw [add_halves]; rw [← Int.cast_abs]; rw [← Int.cast_one (R := Real)]; rw [Int.cast_lt] at this
    grind [Int.abs_lt_one_iff, zpow_zero]
  · rw [hzre, add_halves, ← Int.cast_abs, ← Int.cast_one (R := Real), Int.cast_le,
      Int.abs_le_one_iff] at this
    rcases this with h | h | h <;> simp only [h, Int.cast_zero, zero_add, Int.cast_one] at this
    · grind [zpow_zero]
    · rcases (abs_eq one_half_pos.le).mp hzre with hzre | hzre <;> [skip; norm_num [hzre] at this]
      rw [h]; rw [zpow_one] at hg'
refine .inr .inr ⟨hg', eq_of_re_of_norm (by norm_num [hzre, ρ]) ?_⟩
      simp [hz', show 1 + (ρ : Complex) = -ρ ^ 2 by grind [ρ_sq], norm_ρ]
    · rw [abs_eq (by norm_num)] at hzre
      rcases hzre with hzre | hzre <;> [norm_num [hzre] at this; skip]
      rw [h]; rw [zpow_neg_one] at hg'
exact .inr .inl ⟨hg', eq_of_re_of_norm (by norm_num [hzre, ρ]) (by rw [hz', norm_ρ])⟩

/--
lemma `case_c_one_d_one` / 引理 `case_c_one_d_one`

English:
lemma case_c_one_d_one
  statement: (hz : z in 𝒟) (hg : g • z in 𝒟) (hg' : ‖denom g z‖ <= 1)
  proof: by
  have hgeq : g = T ^ g 0 0 * S * T := by
    refine Subtype.ext ?_
    rw [coe_mul]; rw [coe_mul]; rw [coe_T_zpow]; rw [coe_S]; rw [coe_T]; rw [mul_fin_two]; rw [mul_fin_two]
    ring_nf
    ext i j
    fin_cases i <;> fin_cases j <;> [tauto; simp; tauto; tauto]
    grind [g.property, det_fin_tw

中文:
引理 case_c_one_d_one
  结论: (hz : z in 𝒟) (hg : g • z in 𝒟) (hg' : ‖denom g z‖ <= 1)
  证明: by
  have hgeq : g = T ^ g 0 0 * S * T := by
    refine Subtype.ext ?_
    rw [coe_mul]; rw [coe_mul]; rw [coe_T_zpow]; rw [coe_S]; rw [coe_T]; rw [mul_fin_two]; rw [mul_fin_two]
    ring_nf
    ext i j
    fin_cases i <;> fin_cases j <;> [tauto; simp; tauto; tauto]
    grind [g.property, det_fin_tw
-/
private lemma case_c_one_d_one (hz : z in 𝒟) (hg : g • z in 𝒟) (hg' : ‖denom g z‖ <= 1)
    (hc : g 1 0 = 1) (hd : g 1 1 = 1) :
    (g = S * T ∨ g = T * S * T) ∧ z = ρ := by
  have hgeq : g = T ^ g 0 0 * S * T := by
    refine Subtype.ext ?_
    rw [coe_mul]; rw [coe_mul]; rw [coe_T_zpow]; rw [coe_S]; rw [coe_T]; rw [mul_fin_two]; rw [mul_fin_two]
    ring_nf
    ext i j
    fin_cases i <;> fin_cases j <;> [tauto; simp; tauto; tauto]
    grind [g.property, det_fin_two]
  rw [hgeq]
  obtain ⟨hnorm, hre⟩ : normSq z = 1 ∧ z.re = -1 / 2 := by
    have hnorm : normSq ((z : Complex) + 1) <= 1 := by simpa [denom, hc, hd, norm_def] using hg'
    have : normSq (z + 1) = normSq z + (2 * z.re + 1) := by simp [normSq]; ring
    rw [this] at hnorm
    constructor <;> linarith [hz.1, show 0 <= 2 * z.re + 1 by linarith [(neg_le_abs _).trans hz.2]]
  have hρ : z = ρ := by
    apply eq_of_re_of_norm
    · simp [hre, ρ]
    · rw [norm_def, hnorm, norm_ρ, Real.sqrt_one]
  refine ⟨?_, hρ⟩
  have hSTρ : (S * T) • ρ = ρ := by
    rw [mul_smul]; rw [← SL_neg_smul S]; rw [← S_inv]; rw [inv_smul_eq_iff]; rw [eq_comm]; rw [UpperHalfPlane.ext_iff]; rw [modular_S_smul]; rw [modular_T_smul]; rw [UpperHalfPlane.coe_mk]; rw [coe_vadd]; rw [← mul_one (_ : Complex)⁻¹]; rw [inv_mul_eq_iff_eq_mul₀ (neg_ne_zero.mpr ρ.ne_zero)]
    grind [ρ_sq, ofReal_one]
  rw [hgeq]; rw [hρ]; rw [mul_assoc]; rw [mul_smul]; rw [hSTρ] at hg
  suffices g 0 0 = 0 ∨ g 0 0 = 1 by rcases this with h | h <;> simp [h]
  have hgzre := hg.2
  simp only [Fin.isValue, ρ, neg_div, one_div, ← coe_re, coe_T_zpow_smul_eq, add_re, intCast_re,
    abs_le, le_add_iff_nonneg_right, Int.cast_nonneg_iff, neg_add_le_iff_le_add,
    show (2⁻¹ : Real) + 2⁻¹ = 1 by norm_num] at hgzre
  rw [← Int.cast_one (R := Real)]; rw [Int.cast_le] at hgzre
  grind

/--
lemma `case_c_one_d_neg_one` / 引理 `case_c_one_d_neg_one`

English:
lemma case_c_one_d_neg_one
  statement: (hz : z in 𝒟) (hg : g • z in 𝒟) (hg' : ‖denom g z‖ <= 1)
  proof: by
  have : g 0 1 = -g 0 0 - 1 := by
    have := g.property
    simp_rw [det_fin_two] at this
    grind
  have hgeq : g = T ^ g 0 0 * S * T⁻¹ := by
    refine Subtype.ext ?_
    rw [coe_mul]; rw [coe_mul]; rw [coe_T_zpow]; rw [coe_S]; rw [← zpow_neg_one]; rw [coe_T_zpow]; rw [mul_fin_two]; rw [mul_f

中文:
引理 case_c_one_d_neg_one
  结论: (hz : z in 𝒟) (hg : g • z in 𝒟) (hg' : ‖denom g z‖ <= 1)
  证明: by
  have : g 0 1 = -g 0 0 - 1 := by
    have := g.property
    simp_rw [det_fin_two] at this
    grind
  have hgeq : g = T ^ g 0 0 * S * T⁻¹ := by
    refine Subtype.ext ?_
    rw [coe_mul]; rw [coe_mul]; rw [coe_T_zpow]; rw [coe_S]; rw [← zpow_neg_one]; rw [coe_T_zpow]; rw [mul_fin_two]; rw [mul_f
-/
private lemma case_c_one_d_neg_one (hz : z in 𝒟) (hg : g • z in 𝒟) (hg' : ‖denom g z‖ <= 1)
    (hc : g 1 0 = 1) (hd : g 1 1 = -1) :
    (g = S * T⁻¹ ∨ g = T⁻¹ * S * T⁻¹) ∧ z = (1 : Real) +ᵥ ρ := by
  have : g 0 1 = -g 0 0 - 1 := by
    have := g.property
    simp_rw [det_fin_two] at this
    grind
  have hgeq : g = T ^ g 0 0 * S * T⁻¹ := by
    refine Subtype.ext ?_
    rw [coe_mul]; rw [coe_mul]; rw [coe_T_zpow]; rw [coe_S]; rw [← zpow_neg_one]; rw [coe_T_zpow]; rw [mul_fin_two]; rw [mul_fin_two]
    ring_nf
    ext i j
    fin_cases i <;> fin_cases j <;> [tauto; skip; tauto; tauto]
    simp [this]
    ring_nf
  have hnorm : ‖(z : Complex) - 1‖ <= 1 := by
    convert! hg' using 2
    simp [denom, hc, hd, sub_eq_add_neg]
  rw [norm_def]; rw [Real.sqrt_le_one] at hnorm
  have : normSq (z - 1) = normSq z + (-2 * z.re + 1) := by
    simp [normSq]
    ring
  rw [this] at hnorm
  obtain ⟨h, h'⟩ : normSq z = 1 ∧ z.re = 1 / 2 := by
    have : 1 <= normSq z := hz.1
    have : 0 <= -2 * z.re + 1 := by linarith [(le_abs_self _).trans hz.2]
    constructor <;> linarith
  have hρ : z = (1 : Real) +ᵥ ρ := by
    apply eq_of_re_of_norm
    · norm_num [h', ρ]
    · rw [norm_def, h, coe_vadd, ofReal_one,
        show 1 + (ρ : Complex) = -ρ ^ 2 by grind [ρ_sq], norm_neg, norm_pow, norm_ρ, Real.sqrt_one,
        one_pow]
  refine ⟨?_, hρ⟩
  rw [hgeq]; rw [hρ]; rw [mul_assoc]; rw [mul_smul] at hg
  have : S • ρ = T • ρ := by
    rw [UpperHalfPlane.ext_iff]; rw [modular_S_smul]; rw [modular_T_smul]; rw [UpperHalfPlane.coe_mk]; rw [coe_vadd]; rw [← mul_one (_ : Complex)⁻¹]; rw [inv_mul_eq_iff_eq_mul₀ (neg_ne_zero.mpr ρ.ne_zero)]
    grind [ρ_sq, ofReal_one]
  have : (S * T⁻¹) • ((1 : Real) +ᵥ ρ) = (1 : Real) +ᵥ ρ := by
    rw [mul_smul]; rw [← SL_neg_smul S]; rw [← S_inv]; rw [inv_smul_eq_iff]; rw [← zpow_neg_one]; rw [modular_T_zpow_smul]; rw [Int.cast_neg]; rw [Int.cast_one]; rw [neg_vadd_vadd]; rw [← inv_smul_eq_iff]; rw [S_inv]; rw [SL_neg_smul]; rw [this]; rw [modular_T_smul]
  rw [this] at hg
  rw [hgeq]
  suffices g 0 0 = 0 ∨ g 0 0 = -1 by rcases this with h | h <;> simp [h]
  have : (-1 : Real) <= g 0 0 ∧ g 0 0 <= 0 := by
    simpa only [ρ, neg_div, one_div, ← coe_re, coe_T_zpow_smul_eq, coe_vadd, add_re, ofReal_re,
      show 1 + (-2⁻¹ : Real) = 2⁻¹ by norm_num, intCast_re, abs_le, ← sub_le_iff_le_add',
      show (-2⁻¹ : Real) - (2⁻¹ : Real) = -1 by norm_num, add_le_iff_nonpos_right, Int.cast_nonpos] using
      hg.2
  rw [← Int.cast_one]; rw [← Int.cast_neg]; rw [Int.cast_le] at this
  grind

set_option backward.isDefEq.respectTransparency false in
/--
lemma `serreTheorem_im_eq` / 引理 `serreTheorem_im_eq`

English:
lemma serreTheorem_im_eq
  given: (hz : z in 𝒟) (hg : g • z in 𝒟)
  statement: (g • z).im = z.im
  proof: by
  wlog hden : z.im <= (g • z).im
  · rw [← this (g := g⁻¹) hg (by simpa using hz) (by simpa using le_of_not_ge hden)]
    simp
  wlog hc : 0 <= g 1 0
  · -- TODO: `wlog` leaves junk copies of variables in scope
    simpa using @this (-g) z (-g) z hz (by simpa using hg)
      (by simpa using hden)

中文:
引理 serreTheorem_im_eq
  条件: (hz : z in 𝒟) (hg : g • z in 𝒟)
  结论: (g • z).im = z.im
  证明: by
  wlog hden : z.im <= (g • z).im
  · rw [← this (g := g⁻¹) hg (by simpa using hz) (by simpa using le_of_not_ge hden)]
    simp
  wlog hc : 0 <= g 1 0
  · -- TODO: `wlog` leaves junk copies of variables in scope
    simpa using @this (-g) z (-g) z hz (by simpa using hg)
      (by simpa using hden)
-/
private lemma serreTheorem_im_eq (hz : z in 𝒟) (hg : g • z in 𝒟) : (g • z).im = z.im := by
  wlog hden : z.im <= (g • z).im
  · rw [← this (g := g⁻¹) hg (by simpa using hz) (by simpa using le_of_not_ge hden)]
    simp
  wlog hc : 0 <= g 1 0
  · -- TODO: `wlog` leaves junk copies of variables in scope
    simpa using @this (-g) z (-g) z hz (by simpa using hg)
      (by simpa using hden) (by simpa using (not_le.mp hc).le)
  rw [im_smul_eq_div_normSq]; rw [le_div_iff₀ (normSq_denom_pos _ z.im_ne_zero)]; rw [mul_le_iff_le_one_right z.im_pos]; rw [normSq_eq_norm_sq]; rw [sq_le_one_iff₀ (norm_nonneg _)] at hden
  have hc : g 1 0 = 0 ∨ g 1 0 = 1 := by grind [abs_c_le_one hz hg]
  rcases hc with hc | hc
  · rcases cases_c_zero hz hg hc with h | h | h | h <;>
    rcases h with ⟨(rfl | rfl), -⟩ <;>
    simp only [← zpow_neg_one, im_T_zpow_smul, im_T_smul, one_smul, SL_neg_smul]
  · rw [im_smul_eq_div_normSq, div_eq_iff (normSq_denom_pos _ z.im_ne_zero).ne',
    eq_comm, mul_eq_left₀ z.im_ne_zero]
    rcases Int.abs_le_one_iff.mp (cases_d_of_c_eq_one hz hden hc) with hd | hd | hd
    · rcases cases_c_one_d_zero hz hg hden hc hd with
        ⟨rfl, hnm⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [normSq_eq_norm_sq, denom, coe_S, hnm]
      · rw [show T⁻¹ * S = ⟨!![-1, -1; 1, 0], by simp⟩ by decide]
        norm_num [ρ, denom, ← pow_two, div_pow]
      · rw [show T * S = ⟨!![1, -1; 1, 0], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]
    · rcases case_c_one_d_one hz hg hden hc hd with ⟨(rfl | rfl), rfl⟩
      · rw [show S * T = ⟨!![0, -1; 1, 1], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]
      · rw [show T * S * T = ⟨!![1, 0; 1, 1], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]
    · rcases case_c_one_d_neg_one hz hg hden hc hd with ⟨(rfl | rfl), rfl⟩
      · rw [show S * T⁻¹ = ⟨!![0, -1; 1, -1], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]
      · rw [show T⁻¹ * S * T⁻¹ = ⟨!![-1, 0; 1, -1], by simp⟩ by decide]
        norm_num [ρ, denom, normSq, ← pow_two, div_pow]

/--
lemma `cases_of_mem_fd_smul_mem_fd` / 引理 `cases_of_mem_fd_smul_mem_fd`

English:
lemma cases_of_mem_fd_smul_mem_fd
  given: (hz : z in 𝒟) (hg : g • z in 𝒟)
  proof: by
  have him : (g • z).im = z.im := serreTheorem_im_eq hz hg
  wlog hc : 0 <= g 1 0
  · simpa [neg_eq_iff_eq_neg, or_comm] using @this (-g) z hz (by simpa using hg)
      (by simpa using him) (by simpa using (not_le.mp hc).le)
  rw [im_smul_eq_div_normSq]; rw [div_eq_iff (normSq_denom_pos _ z.im_ne

中文:
引理 cases_of_mem_fd_smul_mem_fd
  条件: (hz : z in 𝒟) (hg : g • z in 𝒟)
  证明: by
  have him : (g • z).im = z.im := serreTheorem_im_eq hz hg
  wlog hc : 0 <= g 1 0
  · simpa [neg_eq_iff_eq_neg, or_comm] using @this (-g) z hz (by simpa using hg)
      (by simpa using him) (by simpa using (not_le.mp hc).le)
  rw [im_smul_eq_div_normSq]; rw [div_eq_iff (normSq_denom_pos _ z.im_ne

Depends on / 依赖: abs_c_le_one, div_eq_iff, eq_comm, im_ne_zero, im_smul_eq_div_normSq, neg_eq_iff_eq_neg, normSq_denom_pos, normSq_eq_norm_sq, norm_nonneg, not_le, not_le.mp, or_comm, pow_eq_one_iff_of_nonneg, serreTheorem_im_eq, two_ne_zero, z.im, z.im_ne_zero
-/
lemma cases_of_mem_fd_smul_mem_fd (hz : z in 𝒟) (hg : g • z in 𝒟) :
    (g = 1 ∨ g = -1) ∨
    ((g = T ∨ g = -T) ∧ z.re = -1 / 2) ∨
    ((g = T⁻¹ ∨ g = -T⁻¹) ∧ z.re = 1 / 2) ∨
    ((g = S ∨ g = -S) ∧ ‖(z : Complex)‖ = 1) ∨
    ((g = T * S ∨ g = -(T * S)) ∧ z = (1 : Real) +ᵥ ρ) ∨
    ((g = T⁻¹ * S * T⁻¹ ∨ g = -(T⁻¹ * S * T⁻¹)) ∧ z = (1 : Real) +ᵥ ρ) ∨
    ((g = S * T⁻¹ ∨ g = -(S * T⁻¹)) ∧ z = (1 : Real) +ᵥ ρ) ∨
    ((g = S * T ∨ g = -(S * T)) ∧ z = ρ) ∨
    ((g = T * S * T ∨ g = -(T * S * T)) ∧ z = ρ) ∨
    ((g = T⁻¹ * S ∨ g = -(T⁻¹ * S)) ∧ z = ρ) := by
  have him : (g • z).im = z.im := serreTheorem_im_eq hz hg
  wlog hc : 0 <= g 1 0
  · simpa [neg_eq_iff_eq_neg, or_comm] using @this (-g) z hz (by simpa using hg)
      (by simpa using him) (by simpa using (not_le.mp hc).le)
  rw [im_smul_eq_div_normSq]; rw [div_eq_iff (normSq_denom_pos _ z.im_ne_zero).ne']; rw [eq_comm]; rw [mul_eq_left₀ z.im_ne_zero]; rw [normSq_eq_norm_sq]; rw [pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at him
  have hc : g 1 0 = 0 ∨ g 1 0 = 1 := by grind [abs_c_le_one hz hg]
  rcases hc with hc | hc
  · grind [cases_c_zero hz hg hc] -- ± T, T⁻¹
  · rcases Int.abs_le_one_iff.mp (cases_d_of_c_eq_one hz him.le hc) with hd | hd | hd
    · grind [cases_c_one_d_zero hz hg him.le hc hd] -- ± S, T⁻¹S, TS
    · grind [case_c_one_d_one hz hg him.le hc hd] -- ± ST, TST
    · grind [case_c_one_d_neg_one hz hg him.le hc hd] -- ± ST⁻¹, T⁻¹ST⁻¹

/--
lemma `stabilizer_of_ne` / 引理 `stabilizer_of_ne`

English:
lemma stabilizer_of_ne
  statement: (hz : z in 𝒟) (hg : g • z = z)
  proof: by
  have : T • z != z := by
    apply_fun UpperHalfPlane.re
    simp [-sl_moeb, re_T_smul]
  have : T⁻¹ • z != z := by rwa [ne_eq, inv_smul_eq_iff, eq_comm]
  have : (z : Complex) != -I := by grind [neg_im, coe_I, Complex.I_im, z.coe_im_pos]
  have : S • z != z := by
    contrapose hzI
    rw [Uppe

中文:
引理 stabilizer_of_ne
  结论: (hz : z in 𝒟) (hg : g • z = z)
  证明: by
  have : T • z != z := by
    apply_fun UpperHalfPlane.re
    simp [-sl_moeb, re_T_smul]
  have : T⁻¹ • z != z := by rwa [ne_eq, inv_smul_eq_iff, eq_comm]
  have : (z : Complex) != -I := by grind [neg_im, coe_I, Complex.I_im, z.coe_im_pos]
  have : S • z != z := by
    contrapose hzI
    rw [Uppe

Depends on / 依赖: Complex.I_im, I_im, I_sq, UpperHalfPlane, UpperHalfPlane.ext_iff, UpperHalfPlane.re, apply_fun, coe_I, coe_im_pos, coe_mk, contrapose, eq_comm, ext_iff, inv_smul_eq_iff, modular_S_smul, mul_one, ne_eq, ne_zero, neg_eq_iff_eq_neg, neg_im
-/
lemma stabilizer_of_ne (hz : z in 𝒟) (hg : g • z = z)
    (hzI : z != I) (hzρ : z != ρ) (hzρ' : z != (1 : Real) +ᵥ ρ) :
    g = 1 ∨ g = -1 := by
  have : T • z != z := by
    apply_fun UpperHalfPlane.re
    simp [-sl_moeb, re_T_smul]
  have : T⁻¹ • z != z := by rwa [ne_eq, inv_smul_eq_iff, eq_comm]
  have : (z : Complex) != -I := by grind [neg_im, coe_I, Complex.I_im, z.coe_im_pos]
  have : S • z != z := by
    contrapose hzI
    rw [UpperHalfPlane.ext_iff]; rw [modular_S_smul]; rw [coe_mk]; rw [← mul_one (_ : Complex)⁻¹]; rw [inv_mul_eq_iff_eq_mul₀ (neg_ne_zero.mpr z.ne_zero)]; rw [neg_mul]; rw [← neg_eq_iff_eq_neg]; rw [← I_sq]; rw [← sq]; rw [sq_eq_sq_iff_eq_or_eq_neg]; rw [← coe_I]; rw [← UpperHalfPlane.ext_iff] at hzI
    grind
  all_goals grind [cases_of_mem_fd_smul_mem_fd hz (hg ▸ hz), SL_neg_smul]

/--
lemma `stabilizer_I` / 引理 `stabilizer_I`

English:
lemma stabilizer_I
  statement: g • I = I ↔ g in ({1, -1, S, -S} : Finset SL(2, Int))
  proof: by
  constructor
  · intro hg
    have := cases_of_mem_fd_smul_mem_fd I_mem_fd (hg.symm ▸ I_mem_fd)
    norm_num [UpperHalfPlane.ext_iff, Complex.ext_iff, ρ] at this
    grind
  · suffices S • I = I by simp +contextual [-sl_moeb, or_imp, this]
    rw [modular_S_smul]; rw [UpperHalfPlane.ext_iff]
   

中文:
引理 stabilizer_I
  结论: g • I = I ↔ g in ({1, -1, S, -S} : Finset SL(2, 整数))
  证明: by
  constructor
  · intro hg
    have := cases_of_mem_fd_smul_mem_fd I_mem_fd (hg.symm ▸ I_mem_fd)
    norm_num [UpperHalfPlane.ext_iff, Complex.ext_iff, ρ] at this
    grind
  · suffices S • I = I by simp +contextual [-sl_moeb, or_imp, this]
    rw [modular_S_smul]; rw [UpperHalfPlane.ext_iff]
   

Depends on / 依赖: Complex.ext_iff, I_mem_fd, UpperHalfPlane, UpperHalfPlane.ext_iff, cases_of_mem_fd_smul_mem_fd, contextual, ext_iff, hg.symm, modular_S_smul, or_imp, sl_moeb
-/
lemma stabilizer_I : g • I = I ↔ g in ({1, -1, S, -S} : Finset SL(2, Int)) := by
  constructor
  · intro hg
    have := cases_of_mem_fd_smul_mem_fd I_mem_fd (hg.symm ▸ I_mem_fd)
    norm_num [UpperHalfPlane.ext_iff, Complex.ext_iff, ρ] at this
    grind
  · suffices S • I = I by simp +contextual [-sl_moeb, or_imp, this]
    rw [modular_S_smul]; rw [UpperHalfPlane.ext_iff]
    norm_num

/--
lemma `stabilizer_ρ` / 引理 `stabilizer_ρ`

English:
lemma stabilizer_ρ
  proof: by
  constructor
  · intro hg
    have neS : g != S ∧ g != -S := by
      have : S • ρ != ρ := by
        rw [ne_eq]; rw [UpperHalfPlane.ext_iff]; rw [modular_S_smul]; rw [coe_mk]; rw [Complex.ext_iff]
        norm_num [ρ, ← pow_two, div_pow]
      grind [SL_neg_smul]
    have neT : g != T ∧ g != -T

中文:
引理 stabilizer_ρ
  证明: by
  constructor
  · intro hg
    have neS : g != S ∧ g != -S := by
      have : S • ρ != ρ := by
        rw [ne_eq]; rw [UpperHalfPlane.ext_iff]; rw [modular_S_smul]; rw [coe_mk]; rw [Complex.ext_iff]
        norm_num [ρ, ← pow_two, div_pow]
      grind [SL_neg_smul]
    have neT : g != T ∧ g != -T

Depends on / 依赖: Complex.ext_iff, SL_neg_smul, UpperHalfPlane, UpperHalfPlane.ext_iff, coe_mk, coe_vadd, div_pow, eq_comm, ext_iff, inv_smul_eq_iff, modular_S_smul, modular_T_smul, ne_eq, pow_two
-/
lemma stabilizer_ρ :
    g • ρ = ρ ↔ g in ({1, -1, S * T, -(S * T), T⁻¹ * S, -(T⁻¹ * S)} : Finset SL(2, Int)) := by
  constructor
  · intro hg
    have neS : g != S ∧ g != -S := by
      have : S • ρ != ρ := by
        rw [ne_eq]; rw [UpperHalfPlane.ext_iff]; rw [modular_S_smul]; rw [coe_mk]; rw [Complex.ext_iff]
        norm_num [ρ, ← pow_two, div_pow]
      grind [SL_neg_smul]
    have neT : g != T ∧ g != -T ∧ g != T⁻¹ ∧ g != -T⁻¹ := by
      have : T • ρ != ρ := by
        rw [ne_eq]; rw [UpperHalfPlane.ext_iff]; rw [modular_T_smul]; rw [coe_vadd]
        norm_num
      have : T⁻¹ • ρ != ρ := by rwa [ne_eq, inv_smul_eq_iff, eq_comm]
      grind [SL_neg_smul]
    have neTST : g != T * S * T ∧ g != -(T * S * T) := by
      have : (T * S * T) • ρ != ρ := by
        simp only [mul_smul, modular_T_smul, modular_S_smul,
          ne_eq, UpperHalfPlane.ext_iff, Complex.ext_iff]
        norm_num [ρ, ← pow_two, div_pow, normSq]
      grind [SL_neg_smul]
    have := cases_of_mem_fd_smul_mem_fd ρ_mem_fd (hg ▸ ρ_mem_fd)
    norm_num [UpperHalfPlane.ext_iff, Complex.ext_iff, norm_ρ, ρ, neS, neT, neTST] at this
    grind
  · suffices (S * T) • ρ = ρ ∧ (T⁻¹ * S) • ρ = ρ by simp +contextual [-sl_moeb, or_imp, this]
    rw [mul_smul T⁻¹]; rw [inv_smul_eq_iff]; rw [← eq_inv_smul_iff (g := S)]; rw [S_inv]; rw [SL_neg_smul]; rw [mul_smul]; rw [eq_comm]; rw [and_self]; rw [modular_T_smul]; rw [modular_S_smul]; rw [UpperHalfPlane.ext_iff]
    norm_num [ρ, Complex.ext_iff, normSq, ← pow_two, div_pow]

/--
theorem `eq_one_or_neg_one_of_mem_fdo_mem_fd` / 定理 `eq_one_or_neg_one_of_mem_fdo_mem_fd`

English:
theorem eq_one_or_neg_one_of_mem_fdo_mem_fd
  given: (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟)
  statement: g = 1 ∨ g = -1
  proof: by
  have : ρ ∉ 𝒟ᵒ := by
    intro h
    grind [norm_ρ, one_lt_normSq_iff.mp h.1]
  have : (1 : Real) +ᵥ ρ ∉ 𝒟ᵒ := by
    intro h
    have : ((1 : Real) +ᵥ ρ).re = 1 / 2 := by norm_num [← coe_re, coe_vadd, ρ]
    grind [h.2]
  grind [one_lt_normSq_iff, hz.1, hz.2, cases_of_mem_fd_smul_mem_fd (fdo_su

中文:
定理 eq_one_or_neg_one_of_mem_fdo_mem_fd
  条件: (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟)
  结论: g = 1 ∨ g = -1
  证明: by
  have : ρ ∉ 𝒟ᵒ := by
    intro h
    grind [norm_ρ, one_lt_normSq_iff.mp h.1]
  have : (1 : Real) +ᵥ ρ ∉ 𝒟ᵒ := by
    intro h
    have : ((1 : Real) +ᵥ ρ).re = 1 / 2 := by norm_num [← coe_re, coe_vadd, ρ]
    grind [h.2]
  grind [one_lt_normSq_iff, hz.1, hz.2, cases_of_mem_fd_smul_mem_fd (fdo_su

Depends on / 依赖: cases_of_mem_fd_smul_mem_fd, coe_re, coe_vadd, fdo_subset_fd, one_lt_normSq_iff, one_lt_normSq_iff.mp
-/
theorem eq_one_or_neg_one_of_mem_fdo_mem_fd (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟) : g = 1 ∨ g = -1 := by
  have : ρ ∉ 𝒟ᵒ := by
    intro h
    grind [norm_ρ, one_lt_normSq_iff.mp h.1]
  have : (1 : Real) +ᵥ ρ ∉ 𝒟ᵒ := by
    intro h
    have : ((1 : Real) +ᵥ ρ).re = 1 / 2 := by norm_num [← coe_re, coe_vadd, ρ]
    grind [h.2]
  grind [one_lt_normSq_iff, hz.1, hz.2, cases_of_mem_fd_smul_mem_fd (fdo_subset_fd hz) hg]

/--
theorem `eq_one_or_neg_one_of_mem_fdo_mem_fdo` / 定理 `eq_one_or_neg_one_of_mem_fdo_mem_fdo`

English:
theorem eq_one_or_neg_one_of_mem_fdo_mem_fdo
  given: (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ)
  statement: g = 1 ∨ g = -1
  proof: eq_one_or_neg_one_of_mem_fdo_mem_fd hz (fdo_subset_fd hg)

中文:
定理 eq_one_or_neg_one_of_mem_fdo_mem_fdo
  条件: (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ)
  结论: g = 1 ∨ g = -1
  证明: eq_one_or_neg_one_of_mem_fdo_mem_fd hz (fdo_subset_fd hg)

Depends on / 依赖: eq_one_or_neg_one_of_mem_fdo_mem_fd, fdo_subset_fd
-/
theorem eq_one_or_neg_one_of_mem_fdo_mem_fdo (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ) : g = 1 ∨ g = -1 :=
  eq_one_or_neg_one_of_mem_fdo_mem_fd hz (fdo_subset_fd hg)

/-- This was previously an auxiliary result en route to
`ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo`. It is now deprecated, since the proof has been
refactored so this step is no longer needed. -/
@[deprecated eq_one_or_neg_one_of_mem_fdo_mem_fdo (since := "2026-03-19")]
/--
theorem `c_eq_zero` / 定理 `c_eq_zero`

English:
theorem c_eq_zero
  given: (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ)
  statement: g 1 0 = 0
  proof: by
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hg with rfl | rfl <;> rfl

中文:
定理 c_eq_zero
  条件: (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ)
  结论: g 1 0 = 0
  证明: by
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hg with rfl | rfl <;> rfl

Depends on / 依赖: eq_one_or_neg_one_of_mem_fdo_mem_fdo
-/
theorem c_eq_zero (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ) : g 1 0 = 0 := by
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hg with rfl | rfl <;> rfl

/--
theorem `eq_smul_self_of_mem_fdo_mem_fdo` / 定理 `eq_smul_self_of_mem_fdo_mem_fdo`

English:
theorem eq_smul_self_of_mem_fdo_mem_fdo
  given: (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ)
  statement: z = g • z
  proof: by
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hg with rfl | rfl <;> simp

中文:
定理 eq_smul_self_of_mem_fdo_mem_fdo
  条件: (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ)
  结论: z = g • z
  证明: by
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hg with rfl | rfl <;> simp

Depends on / 依赖: eq_one_or_neg_one_of_mem_fdo_mem_fdo
-/
theorem eq_smul_self_of_mem_fdo_mem_fdo (hz : z in 𝒟ᵒ) (hg : g • z in 𝒟ᵒ) : z = g • z := by
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hz hg with rfl | rfl <;> simp

end UniqueRepresentative

section Topology

/--
lemma `isClosed_fd` / 引理 `isClosed_fd`

English:
lemma isClosed_fd
  statement: IsClosed 𝒟
  proof: by
  refine .inter (.preimage (by fun_prop) isClosed_Ici) ?_
  exact isClosed_le (f := fun z : ℍ => |z.re|) (by fun_prop) continuous_const

中文:
引理 isClosed_fd
  结论: IsClosed 𝒟
  证明: by
  refine .inter (.preimage (by fun_prop) isClosed_Ici) ?_
  exact isClosed_le (f := fun z : ℍ => |z.re|) (by fun_prop) continuous_const

Depends on / 依赖: continuous_const, fun_prop, isClosed_Ici, isClosed_le, preimage, z.re
-/
lemma isClosed_fd : IsClosed 𝒟 := by
  refine .inter (.preimage (by fun_prop) isClosed_Ici) ?_
  exact isClosed_le (f := fun z : ℍ => |z.re|) (by fun_prop) continuous_const

/--
lemma `isOpen_fdo` / 引理 `isOpen_fdo`

English:
lemma isOpen_fdo
  statement: IsOpen 𝒟ᵒ
  proof: by
  refine .inter (.preimage (by fun_prop) isOpen_Ioi) ?_
  exact isOpen_lt (f := fun z : ℍ => |z.re|) (by fun_prop) continuous_const

中文:
引理 isOpen_fdo
  结论: IsOpen 𝒟ᵒ
  证明: by
  refine .inter (.preimage (by fun_prop) isOpen_Ioi) ?_
  exact isOpen_lt (f := fun z : ℍ => |z.re|) (by fun_prop) continuous_const

Depends on / 依赖: continuous_const, fun_prop, isOpen_Ioi, isOpen_lt, preimage, z.re
-/
lemma isOpen_fdo : IsOpen 𝒟ᵒ := by
  refine .inter (.preimage (by fun_prop) isOpen_Ioi) ?_
  exact isOpen_lt (f := fun z : ℍ => |z.re|) (by fun_prop) continuous_const

/--
lemma `coe_fdo` / 引理 `coe_fdo`

English:
lemma coe_fdo
  statement: (↑) '' 𝒟ᵒ = {z : Complex | 0 < z.im ∧ 1 < ‖z‖ ∧ |z.re| < 1/2}
  proof: by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ => ⟨⟨x, hxim⟩, ⟨one_lt_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_lt_normSq_iff.mp hτ.1, hτ.2⟩

中文:
引理 coe_fdo
  结论: (↑) '' 𝒟ᵒ = {z : Complex | 0 < z.im ∧ 1 < ‖z‖ ∧ |z.re| < 1/2}
  证明: by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ => ⟨⟨x, hxim⟩, ⟨one_lt_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_lt_normSq_iff.mp hτ.1, hτ.2⟩

Depends on / 依赖: hxnorm, im_pos, one_lt_normSq_iff, one_lt_normSq_iff.mp, one_lt_normSq_iff.mpr
-/
lemma coe_fdo : (↑) '' 𝒟ᵒ = {z : Complex | 0 < z.im ∧ 1 < ‖z‖ ∧ |z.re| < 1/2} := by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ => ⟨⟨x, hxim⟩, ⟨one_lt_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_lt_normSq_iff.mp hτ.1, hτ.2⟩

/--
lemma `coe_fd` / 引理 `coe_fd`

English:
lemma coe_fd
  statement: (↑) '' 𝒟 = {z : Complex | 0 < z.im ∧ 1 <= ‖z‖ ∧ |z.re| <= 1/2}
  proof: by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ => ⟨⟨x, hxim⟩, ⟨one_le_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_le_normSq_iff.mp hτ.1, hτ.2⟩

中文:
引理 coe_fd
  结论: (↑) '' 𝒟 = {z : Complex | 0 < z.im ∧ 1 <= ‖z‖ ∧ |z.re| <= 1/2}
  证明: by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ => ⟨⟨x, hxim⟩, ⟨one_le_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_le_normSq_iff.mp hτ.1, hτ.2⟩

Depends on / 依赖: hxnorm, im_pos, one_le_normSq_iff, one_le_normSq_iff.mp, one_le_normSq_iff.mpr
-/
lemma coe_fd : (↑) '' 𝒟 = {z : Complex | 0 < z.im ∧ 1 <= ‖z‖ ∧ |z.re| <= 1/2} := by
  ext x
  refine ⟨?_, fun ⟨hxim, hxnorm, hxre⟩ => ⟨⟨x, hxim⟩, ⟨one_le_normSq_iff.mpr hxnorm, hxre⟩, rfl⟩⟩
  rintro ⟨τ, hτ, rfl⟩
  exact ⟨τ.im_pos, one_le_normSq_iff.mp hτ.1, hτ.2⟩

/--
lemma `isClosed_coe_fd` / 引理 `isClosed_coe_fd`

English:
lemma isClosed_coe_fd
  statement: IsClosed ((↑) '' 𝒟 : Set Complex)
  proof: by
  rw [coe_fd]
  have : IsClosed {z : Complex | 0 <= z.im ∧ 1 <= ‖z‖ ∧ |z.re| <= 1/2} := by
    refine .inter ?_ (.inter ?_ ?_)
    · exact isClosed_le continuous_const Complex.continuous_im
    · exact isClosed_le continuous_const continuous_norm
    · exact isClosed_le (continuous_abs.comp Compl

中文:
引理 isClosed_coe_fd
  结论: IsClosed ((↑) '' 𝒟 : Set Complex)
  证明: by
  rw [coe_fd]
  have : IsClosed {z : Complex | 0 <= z.im ∧ 1 <= ‖z‖ ∧ |z.re| <= 1/2} := by
    refine .inter ?_ (.inter ?_ ?_)
    · exact isClosed_le continuous_const Complex.continuous_im
    · exact isClosed_le continuous_const continuous_norm
    · exact isClosed_le (continuous_abs.comp Compl

Depends on / 依赖: Complex.continuous_im, Complex.continuous_re, IsClosed, abs_re_eq_norm, coe_fd, continuous_abs, continuous_abs.comp, continuous_const, continuous_im, continuous_norm, continuous_re, convert, him.le, him.lt_of_ne, isClosed_le, lt_of_ne, z.im, z.re
-/
lemma isClosed_coe_fd : IsClosed ((↑) '' 𝒟 : Set Complex) := by
  rw [coe_fd]
  have : IsClosed {z : Complex | 0 <= z.im ∧ 1 <= ‖z‖ ∧ |z.re| <= 1/2} := by
    refine .inter ?_ (.inter ?_ ?_)
    · exact isClosed_le continuous_const Complex.continuous_im
    · exact isClosed_le continuous_const continuous_norm
    · exact isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
  convert! this using 1
  ext x
  refine ⟨fun ⟨him, hre, hnorm⟩ => ⟨him.le, hre, hnorm⟩, fun ⟨him, hre, hnorm⟩ => ⟨?_, hre, hnorm⟩⟩
exact him.lt_of_ne' by grind [abs_re_eq_norm]

/--
lemma `mem_closure_of_one_lt_norm` / 引理 `mem_closure_of_one_lt_norm`

English:
lemma mem_closure_of_one_lt_norm
  given: {x : ℍ} (hxnorm : 1 < ‖(x : Complex)‖) (hxre : |x.re| <= 1 / 2)
  proof: by
  -- Need to show that any `x` in this set is a limit of points in `𝒟ᵒ`.
  -- Idea is to use a line segment through the origin and `x`, and show that points
  -- a little below `x` are in `𝒟ᵒ`. There are some annoyances due
  -- to subtypes, etc.
  apply mem_closure_of_frequently_of_tendsto (α :=

中文:
引理 mem_closure_of_one_lt_norm
  条件: {x : ℍ} (hxnorm : 1 < ‖(x : Complex)‖) (hxre : |x.re| <= 1 / 2)
  证明: by
  -- Need to show that any `x` in this set is a limit of points in `𝒟ᵒ`.
  -- Idea is to use a line segment through the origin and `x`, and show that points
  -- a little below `x` are in `𝒟ᵒ`. There are some annoyances due
  -- to subtypes, etc.
  apply mem_closure_of_frequently_of_tendsto (α :=
-/
private lemma mem_closure_of_one_lt_norm {x : ℍ} (hxnorm : 1 < ‖(x : Complex)‖) (hxre : |x.re| <= 1 / 2) :
    x in closure 𝒟ᵒ := by
  -- Need to show that any `x` in this set is a limit of points in `𝒟ᵒ`.
  -- Idea is to use a line segment through the origin and `x`, and show that points
  -- a little below `x` are in `𝒟ᵒ`. There are some annoyances due
  -- to subtypes, etc.
  apply mem_closure_of_frequently_of_tendsto (α := Real)
      (b := 𝓝[<] 1) (f := fun t => ofComplex (t * x))
  · apply Filter.Eventually.frequently
    simp only [fdo, Set.mem_ofPred, Filter.eventually_and, one_lt_normSq_iff]
    refine ⟨Filter.Tendsto.eventually_const_lt hxnorm (.mono_left ?_ nhdsWithin_le_nhds), ?_⟩
    · have : ContinuousAt (fun a : Real => (ofComplex (a * x : Complex) : Complex)) 1 := by
        refine .comp (by fun_prop) ((OpenPartialHomeomorph.continuousAt _ ?_).comp (by fun_prop))
        simpa [ofComplex] using x.coe_im_pos
      simpa [ofComplex_apply_of_im_pos x.coe_im_pos] using this.tendsto.norm
    · simp only [eventually_nhdsWithin_iff]
      filter_upwards [eventually_gt_nhds zero_lt_one] with a ha ha'
      rw [← coe_re]; rw [ofComplex_apply_of_im_pos (by simpa using mul_pos ha x.coe_im_pos)]
      suffices a * |x.re| < 1 / 2 by simpa [abs_of_pos ha]
      nlinarith [Set.mem_Iio.mp ha']
  · refine .mono_left ?_ nhdsWithin_le_nhds
    rw [isOpenEmbedding_coe.tendsto_nhds_iff]; rw [Function.comp_def]
    have : Filter.Tendsto (fun t : Real => t * (x : Complex)) (𝓝 1) (𝓝 (x : Complex)) := by
      rw [show 𝓝 (x : Complex) = 𝓝 ((1 : Real) * (x : Complex)) by simp]
      exact Continuous.tendsto (by fun_prop) _
    refine this.congr' ?_
    filter_upwards [eventually_gt_nhds zero_lt_one] with a ha
    rw [ofComplex_apply_of_im_pos (by simpa using mul_pos ha x.coe_im_pos)]

open scoped NNReal in
/--
lemma `mem_closure_of_arc` / 引理 `mem_closure_of_arc`

English:
lemma mem_closure_of_arc
  given: {x : ℍ} (hxnorm : ‖(x : Complex)‖ = 1) (hxre : |x.re| <= 1 / 2)
  proof: by
  -- We show that `x` is a limit of points known to be in the closure.
  rw [← closure_closure]
  -- Consider a vertical line going upwards from `x` (parametrized by `ℝ≥0`)
  apply mem_closure_of_frequently_of_tendsto (b := 𝓝[>] 0)
    (f := fun t : Real>=0 => ⟨x + t * Complex.I, by
      simpa u

中文:
引理 mem_closure_of_arc
  条件: {x : ℍ} (hxnorm : ‖(x : Complex)‖ = 1) (hxre : |x.re| <= 1 / 2)
  证明: by
  -- We show that `x` is a limit of points known to be in the closure.
  rw [← closure_closure]
  -- Consider a vertical line going upwards from `x` (parametrized by `ℝ≥0`)
  apply mem_closure_of_frequently_of_tendsto (b := 𝓝[>] 0)
    (f := fun t : Real>=0 => ⟨x + t * Complex.I, by
      simpa u
-/
private lemma mem_closure_of_arc {x : ℍ} (hxnorm : ‖(x : Complex)‖ = 1) (hxre : |x.re| <= 1 / 2) :
    x in closure 𝒟ᵒ := by
  -- We show that `x` is a limit of points known to be in the closure.
  rw [← closure_closure]
  -- Consider a vertical line going upwards from `x` (parametrized by `ℝ≥0`)
  apply mem_closure_of_frequently_of_tendsto (b := 𝓝[>] 0)
    (f := fun t : Real>=0 => ⟨x + t * Complex.I, by
      simpa using! add_pos_of_pos_of_nonneg x.coe_im_pos t.property⟩)
  · apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    refine mem_closure_of_one_lt_norm ?_ (by simpa using! hxre)
    suffices 1 < ‖(x : Complex)‖ ^ 2 + a ^ 2 + 2 * a * x.im by
      rw [← one_lt_normSq_iff]
      convert! this
      simp [← normSq_eq_norm_sq, normSq_apply]
      ring
    rw [hxnorm]; rw [one_pow]; rw [add_assoc]; rw [lt_add_iff_pos_right]
    positivity
  · refine .mono_left ?_ nhdsWithin_le_nhds
    simpa [show 𝓝 (x : Complex) = 𝓝 (x + (((0 : Real>=0) : Real) : Complex) * Complex.I) by simp,
      isOpenEmbedding_coe.tendsto_nhds_iff] using! Continuous.tendsto (by fun_prop) _

/--
lemma `fd_eq_closure_fdo` / 引理 `fd_eq_closure_fdo`

English:
lemma fd_eq_closure_fdo
  statement: 𝒟 = closure 𝒟ᵒ
  proof: by
  refine subset_antisymm ?_ (isClosed_fd.closure_subset_iff.mpr fdo_subset_fd)
  intro x ⟨hx, hx'⟩
  rw [one_le_normSq_iff] at hx
  rcases lt_or_eq_of_le hx with hx | hx
  · exact mem_closure_of_one_lt_norm hx hx'
  · exact mem_closure_of_arc hx.symm hx'

中文:
引理 fd_eq_closure_fdo
  结论: 𝒟 = closure 𝒟ᵒ
  证明: by
  refine subset_antisymm ?_ (isClosed_fd.closure_subset_iff.mpr fdo_subset_fd)
  intro x ⟨hx, hx'⟩
  rw [one_le_normSq_iff] at hx
  rcases lt_or_eq_of_le hx with hx | hx
  · exact mem_closure_of_one_lt_norm hx hx'
  · exact mem_closure_of_arc hx.symm hx'

Depends on / 依赖: closure_subset_iff, fdo_subset_fd, hx.symm, isClosed_fd, isClosed_fd.closure_subset_iff.mpr, lt_or_eq_of_le, mem_closure_of_arc, mem_closure_of_one_lt_norm, one_le_normSq_iff, subset_antisymm
-/
lemma fd_eq_closure_fdo : 𝒟 = closure 𝒟ᵒ := by
  refine subset_antisymm ?_ (isClosed_fd.closure_subset_iff.mpr fdo_subset_fd)
  intro x ⟨hx, hx'⟩
  rw [one_le_normSq_iff] at hx
  rcases lt_or_eq_of_le hx with hx | hx
  · exact mem_closure_of_one_lt_norm hx hx'
  · exact mem_closure_of_arc hx.symm hx'

/--
lemma `fdo_eq_interior_fd` / 引理 `fdo_eq_interior_fd`

English:
lemma fdo_eq_interior_fd
  statement: 𝒟ᵒ = interior 𝒟
  proof: by
  refine subset_antisymm (isOpen_fdo.subset_interior_iff.mpr fdo_subset_fd) ?_
  have ho1 := isOpenMap_re.image_interior_subset 𝒟
  have ho2 := isOpenMap_norm.image_interior_subset 𝒟
  intro x hx
  rw [Set.image_subset_iff] at *
  constructor
  · rw [one_lt_normSq_iff, ← Set.mem_Ioi, ← interior_I

中文:
引理 fdo_eq_interior_fd
  结论: 𝒟ᵒ = interior 𝒟
  证明: by
  refine subset_antisymm (isOpen_fdo.subset_interior_iff.mpr fdo_subset_fd) ?_
  have ho1 := isOpenMap_re.image_interior_subset 𝒟
  have ho2 := isOpenMap_norm.image_interior_subset 𝒟
  intro x hx
  rw [Set.image_subset_iff] at *
  constructor
  · rw [one_lt_normSq_iff, ← Set.mem_Ioi, ← interior_I

Depends on / 依赖: Set.image_subset_iff, Set.mem_, Set.mem_Ici, Set.mem_Ioi, Set.mem_of_mem_of_subset, Set.mem_preimage, Set.mem_preimage.mp, abs_lt, fdo_subset_fd, image_interior_subset, image_subset_iff, interior_Ici, interior_mono, isOpenMap_norm, isOpenMap_norm.image_interior_subset, isOpenMap_re, isOpenMap_re.image_interior_subset, isOpen_fdo, isOpen_fdo.subset_interior_iff.mpr, mem_
-/
lemma fdo_eq_interior_fd : 𝒟ᵒ = interior 𝒟 := by
  refine subset_antisymm (isOpen_fdo.subset_interior_iff.mpr fdo_subset_fd) ?_
  have ho1 := isOpenMap_re.image_interior_subset 𝒟
  have ho2 := isOpenMap_norm.image_interior_subset 𝒟
  intro x hx
  rw [Set.image_subset_iff] at *
  constructor
  · rw [one_lt_normSq_iff, ← Set.mem_Ioi, ← interior_Ici]
    apply Set.mem_of_mem_of_subset (Set.mem_preimage.mp (ho2 hx)) (interior_mono ?_)
    rw [Set.image_subset_iff]
    intro ξ hξ
    simpa [Set.mem_preimage, Set.mem_Ici, one_le_normSq_iff] using hξ.1
  · rw [abs_lt, ← Set.mem_Ioo, ← interior_Icc]
    apply Set.mem_of_mem_of_subset ((Set.mem_preimage.mp (ho1 hx))) (interior_mono ?_)
    rw [Set.image_subset_iff]
    intro ξ hξ
    simpa [Set.mem_preimage, Set.mem_Icc, abs_le] using hξ.2

end Topology

section Truncated

/--
Definition of `truncatedFundamentalDomain` / `truncatedFundamentalDomain` 的定义

English:
definition truncatedFundamentalDomain
  signature: (y : Real)
  body: { τ | τ in 𝒟 ∧ τ.im <= y }

中文:
定义 truncatedFundamentalDomain
  签名: (y : 实数)
  定义体: { τ | τ in 𝒟 ∧ τ.im <= y }
-/
def truncatedFundamentalDomain (y : Real) : Set ℍ := { τ | τ in 𝒟 ∧ τ.im <= y }

/--
lemma `coe_truncatedFundamentalDomain` / 引理 `coe_truncatedFundamentalDomain`

English:
lemma coe_truncatedFundamentalDomain
  given: (y : Real)
  proof: by
  ext z
  constructor
  · rintro ⟨⟨z, hz⟩, h, rfl⟩
    exact ⟨hz.le, h.2, h.1.2, by simpa [Complex.normSq_eq_norm_sq] using h.1.1⟩
  · rintro ⟨hz, h1, h2, h3⟩
    have hz' : 0 < z.im := by
      apply hz.lt_of_ne
      contrapose! h3
      simpa [← sq_lt_one_iff₀ (norm_nonneg _), ← Complex.normSq

中文:
引理 coe_truncatedFundamentalDomain
  条件: (y : 实数)
  证明: by
  ext z
  constructor
  · rintro ⟨⟨z, hz⟩, h, rfl⟩
    exact ⟨hz.le, h.2, h.1.2, by simpa [Complex.normSq_eq_norm_sq] using h.1.1⟩
  · rintro ⟨hz, h1, h2, h3⟩
    have hz' : 0 < z.im := by
      apply hz.lt_of_ne
      contrapose! h3
      simpa [← sq_lt_one_iff₀ (norm_nonneg _), ← Complex.normSq

Depends on / 依赖: Complex.normSq, Complex.normSq_eq_norm_sq, contrapose, h2.trans_lt, hz.le, hz.lt_of_ne, lt_of_ne, normSq, normSq_eq_norm_sq, norm_nonneg, trans_lt, z.im
-/
lemma coe_truncatedFundamentalDomain (y : Real) :
    UpperHalfPlane.coe '' truncatedFundamentalDomain y =
    {z | 0 <= z.im ∧ z.im <= y ∧ |z.re| <= 1 / 2 ∧ 1 <= ‖z‖} := by
  ext z
  constructor
  · rintro ⟨⟨z, hz⟩, h, rfl⟩
    exact ⟨hz.le, h.2, h.1.2, by simpa [Complex.normSq_eq_norm_sq] using h.1.1⟩
  · rintro ⟨hz, h1, h2, h3⟩
    have hz' : 0 < z.im := by
      apply hz.lt_of_ne
      contrapose! h3
      simpa [← sq_lt_one_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq, Complex.normSq,
        ← h3, ← sq] using h2.trans_lt (by norm_num)
    exact ⟨⟨z, hz'⟩, ⟨⟨by simpa [Complex.normSq_eq_norm_sq], h2⟩, h1⟩, rfl⟩

/--
lemma `isCompact_truncatedFundamentalDomain` / 引理 `isCompact_truncatedFundamentalDomain`

English:
lemma isCompact_truncatedFundamentalDomain
  given: (y : Real)
  proof: by
  rw [isEmbedding_coe.isCompact_iff]; rw [coe_truncatedFundamentalDomain]; rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · -- show closed
    apply (isClosed_le continuous_const Complex.continuous_im).inter
    apply (isClosed_le Complex.continuous_im continuous_const).inter
    appl

中文:
引理 isCompact_truncatedFundamentalDomain
  条件: (y : 实数)
  证明: by
  rw [isEmbedding_coe.isCompact_iff]; rw [coe_truncatedFundamentalDomain]; rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · -- show closed
    apply (isClosed_le continuous_const Complex.continuous_im).inter
    apply (isClosed_le Complex.continuous_im continuous_const).inter
    appl

Depends on / 依赖: Complex.continuous_im, Complex.continuous_re, Metric, Metric.isBounded_iff_subset_closedBall, Metric.isCompact_iff_isClosed_bounded, bounded, closed, coe_truncatedFundamentalDomain, continuous_abs, continuous_abs.comp, continuous_const, continuous_im, continuous_norm, continuous_re, isBounded_iff_subset_closedBall, isClosed_le, isCompact_iff, isCompact_iff_isClosed_bounded, isEmbedding_coe, isEmbedding_coe.isCompact_iff
-/
lemma isCompact_truncatedFundamentalDomain (y : Real) :
    IsCompact (truncatedFundamentalDomain y) := by
  rw [isEmbedding_coe.isCompact_iff]; rw [coe_truncatedFundamentalDomain]; rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · -- show closed
    apply (isClosed_le continuous_const Complex.continuous_im).inter
    apply (isClosed_le Complex.continuous_im continuous_const).inter
    apply (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    exact isClosed_le continuous_const continuous_norm
  · -- show bounded
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨√((1 / 2) ^ 2 + y ^ 2), fun z hz => ?_⟩
    simp only [mem_closedBall_zero_iff]
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [Real.sq_sqrt (by positivity)]; rw [Complex.norm_eq_sqrt_sq_add_sq]; rw [Real.sq_sqrt (by positivity)]
    apply add_le_add
    · rw [sq_le_sq, abs_of_pos <| one_half_pos (α := Real)]
      exact hz.2.2.1
    · rw [sq_le_sq₀ hz.1 (hz.1.trans hz.2.1)]
      exact hz.2.1


end Truncated

end FundamentalDomain

/--
lemma `exists_one_half_le_im_smul` / 引理 `exists_one_half_le_im_smul`

English:
lemma exists_one_half_le_im_smul
  given: (τ : ℍ)
  statement: exists γ : SL(2, Int), 1 / 2 <= im (γ • τ)
  proof: by
  obtain ⟨γ, hγ⟩ := exists_smul_mem_fd τ
  use γ
  nlinarith [three_le_four_mul_im_sq_of_mem_fd hγ, im_pos (γ • τ)]

中文:
引理 exists_one_half_le_im_smul
  条件: (τ : ℍ)
  结论: 存在 γ : SL(2, 整数), 1 / 2 <= im (γ • τ)
  证明: by
  obtain ⟨γ, hγ⟩ := exists_smul_mem_fd τ
  use γ
  nlinarith [three_le_four_mul_im_sq_of_mem_fd hγ, im_pos (γ • τ)]

Depends on / 依赖: exists_smul_mem_fd, im_pos, three_le_four_mul_im_sq_of_mem_fd
-/
lemma exists_one_half_le_im_smul (τ : ℍ) : exists γ : SL(2, Int), 1 / 2 <= im (γ • τ) := by
  obtain ⟨γ, hγ⟩ := exists_smul_mem_fd τ
  use γ
  nlinarith [three_le_four_mul_im_sq_of_mem_fd hγ, im_pos (γ • τ)]

/--
lemma `exists_one_half_le_im_smul_and_norm_denom_le` / 引理 `exists_one_half_le_im_smul_and_norm_denom_le`

English:
lemma exists_one_half_le_im_smul_and_norm_denom_le
  given: (τ : ℍ)
  proof: by
  rcases le_total (1 / 2) τ.im with h | h
  · exact ⟨1, (one_smul SL(2, Int) τ).symm ▸ h, by
      simp only [map_one, denom_one, norm_one, le_refl]⟩
  · refine (exists_one_half_le_im_smul τ).imp (fun γ hγ => ⟨hγ, ?_⟩)
    have h1 : τ.im <= (γ • τ).im := h.trans hγ
    rw [im_smul_eq_div_normSq];

中文:
引理 exists_one_half_le_im_smul_and_norm_denom_le
  条件: (τ : ℍ)
  证明: by
  rcases le_total (1 / 2) τ.im with h | h
  · exact ⟨1, (one_smul SL(2, Int) τ).symm ▸ h, by
      simp only [map_one, denom_one, norm_one, le_refl]⟩
  · refine (exists_one_half_le_im_smul τ).imp (fun γ hγ => ⟨hγ, ?_⟩)
    have h1 : τ.im <= (γ • τ).im := h.trans hγ
    rw [im_smul_eq_div_normSq];

Depends on / 依赖: abs_norm, denom_one, exists_one_half_le_im_smul, h.trans, im_ne_zero, im_smul_eq_div_normSq, le_refl, le_total, map_one, mul_le_iff_le_one_right, normSq_denom_pos, normSq_eq_norm_sq, norm_one, one_smul, sq_le_one_iff_abs_le_one
-/
lemma exists_one_half_le_im_smul_and_norm_denom_le (τ : ℍ) :
    exists γ : SL(2, Int), 1 / 2 <= im (γ • τ) ∧ ‖denom γ τ‖ <= 1 := by
  rcases le_total (1 / 2) τ.im with h | h
  · exact ⟨1, (one_smul SL(2, Int) τ).symm ▸ h, by
      simp only [map_one, denom_one, norm_one, le_refl]⟩
  · refine (exists_one_half_le_im_smul τ).imp (fun γ hγ => ⟨hγ, ?_⟩)
    have h1 : τ.im <= (γ • τ).im := h.trans hγ
    rw [im_smul_eq_div_normSq]; rw [le_div_iff₀ (normSq_denom_pos γ τ.im_ne_zero)]; rw [normSq_eq_norm_sq] at h1
    simpa only [sq_le_one_iff_abs_le_one, abs_norm] using
      (mul_le_iff_le_one_right τ.2).mp h1

end ModularGroup
