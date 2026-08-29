/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# Fourier theory on `ZMod N`

Basic definitions and properties of the discrete Fourier transform for functions on `ZMod N`
(taking values in an arbitrary `ℂ`-vector space).

### Main definitions and results

* `ZMod.dft`: the Fourier transform, with respect to the standard additive character
  `ZMod.stdAddChar` (mapping `j mod N` to `exp (2 * π * I * j / N)`). The notation `𝓕`, scoped in
  namespace `ZMod`, is available for this.
* `ZMod.dft_dft`: the Fourier inversion formula.
* `DirichletCharacter.fourierTransform_eq_inv_mul_gaussSum`: the discrete Fourier transform of a
  primitive Dirichlet character `χ` is a Gauss sum times `χ⁻¹`.
-/

@[expose] public section

open MeasureTheory Finset AddChar ZMod

namespace ZMod

variable {N : Nat} [NeZero N] {E : Type*} [AddCommGroup E] [Module Complex E]

section private_defs
/-
It doesn't _quite_ work to define the Fourier transform as a `LinearEquiv` in one go, because that
leads to annoying repetition between the proof fields. So we set up a private definition first,
prove a minimal set of lemmas about it, and then define the `LinearEquiv` using that.

**Do not add more lemmas about `auxDFT`**: it should be invisible to end-users.
-/

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def auxDFT (Φ : ZMod N -> E) (k : ZMod N)
  body: ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j

中文:
定义 noncomputable
  签名: def auxDFT (Φ : ZMod N -> E) (k : ZMod N)
  定义体: ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j
-/
private noncomputable def auxDFT (Φ : ZMod N -> E) (k : ZMod N) : E :=
  ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j

/--
lemma `auxDFT_neg` / 引理 `auxDFT_neg`

English:
lemma auxDFT_neg
  given: (Φ : ZMod N -> E)
  statement: auxDFT (fun j => Φ (-j)) = fun k => auxDFT Φ (-k)
  proof: by
  ext1 k; simpa only [auxDFT] using
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by rw [Equiv.neg_apply, neg_mul_neg])

中文:
引理 auxDFT_neg
  条件: (Φ : ZMod N -> E)
  结论: auxDFT (fun j => Φ (-j)) = fun k => auxDFT Φ (-k)
  证明: by
  ext1 k; simpa only [auxDFT] using
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by rw [Equiv.neg_apply, neg_mul_neg])
-/
private lemma auxDFT_neg (Φ : ZMod N -> E) : auxDFT (fun j => Φ (-j)) = fun k => auxDFT Φ (-k) := by
  ext1 k; simpa only [auxDFT] using
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun j => by rw [Equiv.neg_apply, neg_mul_neg])

/--
lemma `auxDFT_auxDFT` / 引理 `auxDFT_auxDFT`

English:
lemma auxDFT_auxDFT
  given: (Φ : ZMod N -> E)
  statement: auxDFT (auxDFT Φ) = fun j => (N : Complex) • Φ (-j)
  proof: by
  ext1 j
  simp only [auxDFT, mul_comm _ j, smul_sum, ← smul_assoc, smul_eq_mul, ← map_add_eq_mul, ←
    neg_add, ← add_mul]
  rw [sum_comm]
  simp only [← sum_smul, ← neg_mul]
  have h1 (t : ZMod N) : ∑ i, stdAddChar (t * i) = if t = 0 then ↑N else 0 := by
    split_ifs with h
    · simp only [h, zero_mul, map_zero_eq_one, sum_const, card_univ, card,
        nsmul_eq_mul, mul_one]
    · exact sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)
  have h2 (x j : ZMod N) : -(j + x) = 0 ↔ x = -j := by
    rw [neg_add]; rw [add_comm]; rw [add_eq_zero_iff_neg_eq]; rw [neg_neg]
  simp only [h1, h2, ite_smul, zero_smul, sum_ite_eq', mem_univ, ite_true]

中文:
引理 auxDFT_auxDFT
  条件: (Φ : ZMod N -> E)
  结论: auxDFT (auxDFT Φ) = fun j => (N : 复形) • Φ (-j)
  证明: by
  ext1 j
  simp only [auxDFT, mul_comm _ j, smul_sum, ← smul_assoc, smul_eq_mul, ← map_add_eq_mul, ←
    neg_add, ← add_mul]
  rw [sum_comm]
  simp only [← sum_smul, ← neg_mul]
  have h1 (t : ZMod N) : ∑ i, stdAddChar (t * i) = if t = 0 then ↑N else 0 := by
    split_ifs with h
    · simp only [h, zero_mul, map_zero_eq_one, sum_const, card_univ, card,
        nsmul_eq_mul, mul_one]
    · exact sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)
  have h2 (x j : ZMod N) : -(j + x) = 0 ↔ x = -j := by
    rw [neg_add]; rw [add_comm]; rw [add_eq_zero_iff_neg_eq]; rw [neg_neg]
  simp only [h1, h2, ite_smul, zero_smul, sum_ite_eq', mem_univ, ite_true]
-/
private lemma auxDFT_auxDFT (Φ : ZMod N -> E) : auxDFT (auxDFT Φ) = fun j => (N : Complex) • Φ (-j) := by
  ext1 j
  simp only [auxDFT, mul_comm _ j, smul_sum, ← smul_assoc, smul_eq_mul, ← map_add_eq_mul, ←
    neg_add, ← add_mul]
  rw [sum_comm]
  simp only [← sum_smul, ← neg_mul]
  have h1 (t : ZMod N) : ∑ i, stdAddChar (t * i) = if t = 0 then ↑N else 0 := by
    split_ifs with h
    · simp only [h, zero_mul, map_zero_eq_one, sum_const, card_univ, card,
        nsmul_eq_mul, mul_one]
    · exact sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)
  have h2 (x j : ZMod N) : -(j + x) = 0 ↔ x = -j := by
    rw [neg_add]; rw [add_comm]; rw [add_eq_zero_iff_neg_eq]; rw [neg_neg]
  simp only [h1, h2, ite_smul, zero_smul, sum_ite_eq', mem_univ, ite_true]

/--
lemma `auxDFT_smul` / 引理 `auxDFT_smul`

English:
lemma auxDFT_smul
  given: (c : Complex) (Φ : ZMod N -> E)
  proof: by
  ext; simp only [Pi.smul_def, auxDFT, smul_sum, smul_comm c]

中文:
引理 auxDFT_smul
  条件: (c : 复形) (Φ : ZMod N -> E)
  证明: by
  ext; simp only [Pi.smul_def, auxDFT, smul_sum, smul_comm c]
-/
private lemma auxDFT_smul (c : Complex) (Φ : ZMod N -> E) :
    auxDFT (c • Φ) = c • auxDFT Φ := by
  ext; simp only [Pi.smul_def, auxDFT, smul_sum, smul_comm c]

end private_defs

section defs

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `dft` / `dft` 的定义

English:
definition dft
  signature: : (ZMod N -> E) ≃ₗ[Complex] (ZMod N -> E) where
  body: auxDFT
  map_add' Φ₁ Φ₂ := by
    ext; simp only [auxDFT, Pi.add_def, smul_add, sum_add_distrib]
  map_smul' c Φ := by
    ext; simp only [auxDFT, Pi.smul_apply, RingHom.id_apply, smul_sum, smul_comm c]
  invFun Φ k := (N : Complex)⁻¹ • auxDFT Φ (-k)
  left_inv Φ := by
    simp only [auxDFT_auxDFT, neg_neg, ← mul_smul, inv_mul_cancel₀ (NeZero.ne _), one_smul]
  right_inv Φ := by
    ext1 j
    simp only [← Pi.smul_def, auxDFT_smul, auxDFT_neg, auxDFT_auxDFT, neg_neg, ← mul_smul,
      inv_mul_cancel₀ (NeZero.ne _), one_smul]

@[inherit_doc] scoped notation "𝓕" => dft

中文:
定义 dft
  签名: : (ZMod N -> E) ≃ₗ[复形] (ZMod N -> E) where
  定义体: auxDFT
  map_add' Φ₁ Φ₂ := by
    ext; simp only [auxDFT, Pi.add_def, smul_add, sum_add_distrib]
  map_smul' c Φ := by
    ext; simp only [auxDFT, Pi.smul_apply, RingHom.id_apply, smul_sum, smul_comm c]
  invFun Φ k := (N : Complex)⁻¹ • auxDFT Φ (-k)
  left_inv Φ := by
    simp only [auxDFT_auxDFT, neg_neg, ← mul_smul, inv_mul_cancel₀ (NeZero.ne _), one_smul]
  right_inv Φ := by
    ext1 j
    simp only [← Pi.smul_def, auxDFT_smul, auxDFT_neg, auxDFT_auxDFT, neg_neg, ← mul_smul,
      inv_mul_cancel₀ (NeZero.ne _), one_smul]

@[inherit_doc] scoped notation "𝓕" => dft

Depends on / 依赖: auxDFT
-/
noncomputable def dft : (ZMod N -> E) ≃ₗ[Complex] (ZMod N -> E) where
  toFun := auxDFT
  map_add' Φ₁ Φ₂ := by
    ext; simp only [auxDFT, Pi.add_def, smul_add, sum_add_distrib]
  map_smul' c Φ := by
    ext; simp only [auxDFT, Pi.smul_apply, RingHom.id_apply, smul_sum, smul_comm c]
  invFun Φ k := (N : Complex)⁻¹ • auxDFT Φ (-k)
  left_inv Φ := by
    simp only [auxDFT_auxDFT, neg_neg, ← mul_smul, inv_mul_cancel₀ (NeZero.ne _), one_smul]
  right_inv Φ := by
    ext1 j
    simp only [← Pi.smul_def, auxDFT_smul, auxDFT_neg, auxDFT_auxDFT, neg_neg, ← mul_smul,
      inv_mul_cancel₀ (NeZero.ne _), one_smul]

@[inherit_doc] scoped notation "𝓕" => dft

/-- The inverse Fourier transform on `ZMod N`. -/
scoped notation "𝓕⁻" => LinearEquiv.symm dft

/--
lemma `dft_apply` / 引理 `dft_apply`

English:
lemma dft_apply
  given: (Φ : ZMod N -> E) (k : ZMod N)
  proof: rfl

中文:
引理 dft_apply
  条件: (Φ : ZMod N -> E) (k : ZMod N)
  证明: rfl
-/
lemma dft_apply (Φ : ZMod N -> E) (k : ZMod N) :
    𝓕 Φ k = ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j :=
  rfl

/--
lemma `dft_def` / 引理 `dft_def`

English:
lemma dft_def
  given: (Φ : ZMod N -> E)
  proof: rfl

中文:
引理 dft_def
  条件: (Φ : ZMod N -> E)
  证明: rfl
-/
lemma dft_def (Φ : ZMod N -> E) :
    𝓕 Φ = fun k => ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j :=
  rfl

/--
lemma `invDFT_apply` / 引理 `invDFT_apply`

English:
lemma invDFT_apply
  given: (Ψ : ZMod N -> E) (k : ZMod N)
  proof: by
  simp only [dft, LinearEquiv.coe_symm_mk, auxDFT, mul_neg, neg_neg]

中文:
引理 invDFT_apply
  条件: (Ψ : ZMod N -> E) (k : ZMod N)
  证明: by
  simp only [dft, LinearEquiv.coe_symm_mk, auxDFT, mul_neg, neg_neg]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_symm_mk, auxDFT, coe_symm_mk, mul_neg, neg_neg
-/
lemma invDFT_apply (Ψ : ZMod N -> E) (k : ZMod N) :
    𝓕⁻ Ψ k = (N : Complex)⁻¹ • ∑ j : ZMod N, stdAddChar (j * k) • Ψ j := by
  simp only [dft, LinearEquiv.coe_symm_mk, auxDFT, mul_neg, neg_neg]

/--
lemma `invDFT_def` / 引理 `invDFT_def`

English:
lemma invDFT_def
  given: (Ψ : ZMod N -> E)
  proof: funext invDFT_apply Ψ

中文:
引理 invDFT_def
  条件: (Ψ : ZMod N -> E)
  证明: funext invDFT_apply Ψ

Depends on / 依赖: invDFT_apply
-/
lemma invDFT_def (Ψ : ZMod N -> E) :
    𝓕⁻ Ψ = fun k => (N : Complex)⁻¹ • ∑ j : ZMod N, stdAddChar (j * k) • Ψ j :=
funext invDFT_apply Ψ

/--
lemma `invDFT_apply'` / 引理 `invDFT_apply'`

English:
lemma invDFT_apply'
  given: (Ψ : ZMod N -> E) (k : ZMod N)
  statement: 𝓕⁻ Ψ k = (N : Complex)⁻¹ • 𝓕 Ψ (-k)
  proof: rfl

中文:
引理 invDFT_apply'
  条件: (Ψ : ZMod N -> E) (k : ZMod N)
  结论: 𝓕⁻ Ψ k = (N : 复形)⁻¹ • 𝓕 Ψ (-k)
  证明: rfl
-/
lemma invDFT_apply' (Ψ : ZMod N -> E) (k : ZMod N) : 𝓕⁻ Ψ k = (N : Complex)⁻¹ • 𝓕 Ψ (-k) :=
  rfl

/--
lemma `invDFT_def'` / 引理 `invDFT_def'`

English:
lemma invDFT_def'
  given: (Ψ : ZMod N -> E)
  statement: 𝓕⁻ Ψ = fun k => (N : Complex)⁻¹ • 𝓕 Ψ (-k)
  proof: rfl

中文:
引理 invDFT_def'
  条件: (Ψ : ZMod N -> E)
  结论: 𝓕⁻ Ψ = fun k => (N : 复形)⁻¹ • 𝓕 Ψ (-k)
  证明: rfl
-/
lemma invDFT_def' (Ψ : ZMod N -> E) : 𝓕⁻ Ψ = fun k => (N : Complex)⁻¹ • 𝓕 Ψ (-k) :=
  rfl

/--
lemma `dft_apply_zero` / 引理 `dft_apply_zero`

English:
lemma dft_apply_zero
  given: (Φ : ZMod N -> E)
  statement: 𝓕 Φ 0 = ∑ j, Φ j
  proof: by
  simp only [dft_apply, mul_zero, neg_zero, map_zero_eq_one, one_smul]

中文:
引理 dft_apply_zero
  条件: (Φ : ZMod N -> E)
  结论: 𝓕 Φ 0 = ∑ j, Φ j
  证明: by
  simp only [dft_apply, mul_zero, neg_zero, map_zero_eq_one, one_smul]

Depends on / 依赖: dft_apply, map_zero_eq_one, mul_zero, neg_zero, one_smul
-/
lemma dft_apply_zero (Φ : ZMod N -> E) : 𝓕 Φ 0 = ∑ j, Φ j := by
  simp only [dft_apply, mul_zero, neg_zero, map_zero_eq_one, one_smul]

/--
lemma `dft_eq_fourier` / 引理 `dft_eq_fourier`

English:
lemma dft_eq_fourier
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] [CompleteSpace E]
  proof: by
  simp only [dft_apply, stdAddChar_apply, Fourier.fourierIntegral_def, Circle.smul_def,
integral_countable .of_finite .., count_real_singleton, one_smul, tsum_fintype]

中文:
引理 dft_eq_fourier
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 复形 E] [完备空间 E]
  证明: by
  simp only [dft_apply, stdAddChar_apply, Fourier.fourierIntegral_def, Circle.smul_def,
integral_countable .of_finite .., count_real_singleton, one_smul, tsum_fintype]

Depends on / 依赖: Circle, Circle.smul_def, Fourier, Fourier.fourierIntegral_def, count_real_singleton, dft_apply, fourierIntegral_def, integral_countable, of_finite, one_smul, smul_def, stdAddChar_apply, tsum_fintype
-/
lemma dft_eq_fourier {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] [CompleteSpace E]
    (Φ : ZMod N -> E) (k : ZMod N) :
    𝓕 Φ k = Fourier.fourierIntegral toCircle Measure.count Φ k := by
  simp only [dft_apply, stdAddChar_apply, Fourier.fourierIntegral_def, Circle.smul_def,
integral_countable .of_finite .., count_real_singleton, one_smul, tsum_fintype]

end defs

section arith

/--
lemma `dft_const_smul` / 引理 `dft_const_smul`

English:
lemma dft_const_smul
  given: {R : Type*} [DistribSMul R E] [SMulCommClass R Complex E] (r : R) (Φ : ZMod N -> E)
  proof: by
  simp only [Pi.smul_def, dft_def, smul_sum, smul_comm]

中文:
引理 dft_const_smul
  条件: {R : 类型} [分配标量乘法 R E] [标量交换类 R 复形 E] (r : R) (Φ : ZMod N -> E)
  证明: by
  simp only [Pi.smul_def, dft_def, smul_sum, smul_comm]

Depends on / 依赖: Pi.smul_def, dft_def, smul_comm, smul_def, smul_sum
-/
lemma dft_const_smul {R : Type*} [DistribSMul R E] [SMulCommClass R Complex E] (r : R) (Φ : ZMod N -> E) :
    𝓕 (r • Φ) = r • 𝓕 Φ := by
  simp only [Pi.smul_def, dft_def, smul_sum, smul_comm]

/--
lemma `dft_smul_const` / 引理 `dft_smul_const`

English:
lemma dft_smul_const
  statement: {R : Type*} [Ring R] [Module Complex R] [Module R E] [IsScalarTower Complex R E]
  proof: by
  simp only [dft_def, sum_smul, smul_assoc]

中文:
引理 dft_smul_const
  结论: {R : 类型} [环 R] [模 复形 R] [模 R E] [标量塔 复形 R E]
  证明: by
  simp only [dft_def, sum_smul, smul_assoc]

Depends on / 依赖: dft_def, smul_assoc, sum_smul
-/
lemma dft_smul_const {R : Type*} [Ring R] [Module Complex R] [Module R E] [IsScalarTower Complex R E]
    (Φ : ZMod N -> R) (e : E) :
    𝓕 (fun j => Φ j • e) = fun k => 𝓕 Φ k • e := by
  simp only [dft_def, sum_smul, smul_assoc]

/--
lemma `dft_const_mul` / 引理 `dft_const_mul`

English:
lemma dft_const_mul
  given: {R : Type*} [Ring R] [Algebra Complex R] (r : R) (Φ : ZMod N -> R)
  proof: dft_const_smul r Φ

中文:
引理 dft_const_mul
  条件: {R : 类型} [环 R] [代数 复形 R] (r : R) (Φ : ZMod N -> R)
  证明: dft_const_smul r Φ

Depends on / 依赖: dft_const_smul
-/
lemma dft_const_mul {R : Type*} [Ring R] [Algebra Complex R] (r : R) (Φ : ZMod N -> R) :
    𝓕 (fun j => r * Φ j) = fun k => r * 𝓕 Φ k :=
  dft_const_smul r Φ

/--
lemma `dft_mul_const` / 引理 `dft_mul_const`

English:
lemma dft_mul_const
  given: {R : Type*} [Ring R] [Algebra Complex R] (Φ : ZMod N -> R) (r : R)
  proof: dft_smul_const Φ r

中文:
引理 dft_mul_const
  条件: {R : 类型} [环 R] [代数 复形 R] (Φ : ZMod N -> R) (r : R)
  证明: dft_smul_const Φ r

Depends on / 依赖: dft_smul_const
-/
lemma dft_mul_const {R : Type*} [Ring R] [Algebra Complex R] (Φ : ZMod N -> R) (r : R) :
    𝓕 (fun j => Φ j * r) = fun k => 𝓕 Φ k * r :=
  dft_smul_const Φ r

end arith

section inversion

/--
lemma `dft_comp_neg` / 引理 `dft_comp_neg`

English:
lemma dft_comp_neg
  given: (Φ : ZMod N -> E)
  statement: 𝓕 (fun j => Φ (-j)) = fun k => 𝓕 Φ (-k)
  proof: auxDFT_neg ..

中文:
引理 dft_comp_neg
  条件: (Φ : ZMod N -> E)
  结论: 𝓕 (fun j => Φ (-j)) = fun k => 𝓕 Φ (-k)
  证明: auxDFT_neg ..

Depends on / 依赖: auxDFT_neg
-/
lemma dft_comp_neg (Φ : ZMod N -> E) : 𝓕 (fun j => Φ (-j)) = fun k => 𝓕 Φ (-k) :=
  auxDFT_neg ..

/--
lemma `dft_dft` / 引理 `dft_dft`

English:
lemma dft_dft
  given: (Φ : ZMod N -> E)
  statement: 𝓕 (𝓕 Φ) = fun j => (N : Complex) • Φ (-j)
  proof: auxDFT_auxDFT ..

中文:
引理 dft_dft
  条件: (Φ : ZMod N -> E)
  结论: 𝓕 (𝓕 Φ) = fun j => (N : 复形) • Φ (-j)
  证明: auxDFT_auxDFT ..

Depends on / 依赖: auxDFT_auxDFT
-/
lemma dft_dft (Φ : ZMod N -> E) : 𝓕 (𝓕 Φ) = fun j => (N : Complex) • Φ (-j) :=
  auxDFT_auxDFT ..

end inversion

/--
lemma `dft_comp_unitMul` / 引理 `dft_comp_unitMul`

English:
lemma dft_comp_unitMul
  given: (Φ : ZMod N -> E) (u : (ZMod N)ˣ) (k : ZMod N)
  proof: by
  refine Fintype.sum_equiv u.mulLeft _ _ fun x => ?_
  simp only [mul_comm u.val, u.mulLeft_apply, ← mul_assoc, u.mul_inv_cancel_right]

中文:
引理 dft_comp_unitMul
  条件: (Φ : ZMod N -> E) (u : (ZMod N)ˣ) (k : ZMod N)
  证明: by
  refine Fintype.sum_equiv u.mulLeft _ _ fun x => ?_
  simp only [mul_comm u.val, u.mulLeft_apply, ← mul_assoc, u.mul_inv_cancel_right]

Depends on / 依赖: Fintype, Fintype.sum_equiv, mulLeft, mulLeft_apply, mul_assoc, mul_comm, mul_inv_cancel_right, sum_equiv, u.mulLeft, u.mulLeft_apply, u.mul_inv_cancel_right, u.val
-/
lemma dft_comp_unitMul (Φ : ZMod N -> E) (u : (ZMod N)ˣ) (k : ZMod N) :
    𝓕 (fun j => Φ (u.val * j)) k = 𝓕 Φ (u⁻¹.val * k) := by
  refine Fintype.sum_equiv u.mulLeft _ _ fun x => ?_
  simp only [mul_comm u.val, u.mulLeft_apply, ← mul_assoc, u.mul_inv_cancel_right]

section signs

/--
lemma `dft_even_iff` / 引理 `dft_even_iff`

English:
lemma dft_even_iff
  given: {Φ : ZMod N -> Complex}
  statement: (𝓕 Φ).Even ↔ Φ.Even
  proof: by
  have h {f : ZMod N -> Complex} (hf : f.Even) : (𝓕 f).Even := by
    simp only [Function.Even, ← congr_fun (dft_comp_neg f), funext hf, implies_true]
  refine ⟨fun hΦ x => ?_, h⟩
  simpa only [neg_neg, smul_right_inj (NeZero.ne (N : Complex)), dft_dft] using h hΦ (-x)

中文:
引理 dft_even_iff
  条件: {Φ : ZMod N -> 复形}
  结论: (𝓕 Φ).Even ↔ Φ.Even
  证明: by
  have h {f : ZMod N -> Complex} (hf : f.Even) : (𝓕 f).Even := by
    simp only [Function.Even, ← congr_fun (dft_comp_neg f), funext hf, implies_true]
  refine ⟨fun hΦ x => ?_, h⟩
  simpa only [neg_neg, smul_right_inj (NeZero.ne (N : Complex)), dft_dft] using h hΦ (-x)

Depends on / 依赖: Function, Function.Even, NeZero, NeZero.ne, congr_fun, dft_comp_neg, dft_dft, f.Even, implies_true, neg_neg, smul_right_inj
-/
lemma dft_even_iff {Φ : ZMod N -> Complex} : (𝓕 Φ).Even ↔ Φ.Even := by
  have h {f : ZMod N -> Complex} (hf : f.Even) : (𝓕 f).Even := by
    simp only [Function.Even, ← congr_fun (dft_comp_neg f), funext hf, implies_true]
  refine ⟨fun hΦ x => ?_, h⟩
  simpa only [neg_neg, smul_right_inj (NeZero.ne (N : Complex)), dft_dft] using h hΦ (-x)

/--
lemma `dft_odd_iff` / 引理 `dft_odd_iff`

English:
lemma dft_odd_iff
  given: {Φ : ZMod N -> Complex}
  statement: (𝓕 Φ).Odd ↔ Φ.Odd
  proof: by
  have h {f : ZMod N -> Complex} (hf : f.Odd) : (𝓕 f).Odd := by
    simp only [Function.Odd, ← congr_fun (dft_comp_neg f), funext hf, ← Pi.neg_apply, map_neg,
      implies_true]
  refine ⟨fun hΦ x => ?_, h⟩
  simpa only [neg_neg, dft_dft, ← smul_neg, smul_right_inj (NeZero.ne (N : Complex))] using h hΦ (-x)

中文:
引理 dft_odd_iff
  条件: {Φ : ZMod N -> 复形}
  结论: (𝓕 Φ).Odd ↔ Φ.Odd
  证明: by
  have h {f : ZMod N -> Complex} (hf : f.Odd) : (𝓕 f).Odd := by
    simp only [Function.Odd, ← congr_fun (dft_comp_neg f), funext hf, ← Pi.neg_apply, map_neg,
      implies_true]
  refine ⟨fun hΦ x => ?_, h⟩
  simpa only [neg_neg, dft_dft, ← smul_neg, smul_right_inj (NeZero.ne (N : Complex))] using h hΦ (-x)

Depends on / 依赖: Function, Function.Odd, NeZero, NeZero.ne, Pi.neg_apply, congr_fun, dft_comp_neg, dft_dft, f.Odd, implies_true, map_neg, neg_apply, neg_neg, smul_neg, smul_right_inj
-/
lemma dft_odd_iff {Φ : ZMod N -> Complex} : (𝓕 Φ).Odd ↔ Φ.Odd := by
  have h {f : ZMod N -> Complex} (hf : f.Odd) : (𝓕 f).Odd := by
    simp only [Function.Odd, ← congr_fun (dft_comp_neg f), funext hf, ← Pi.neg_apply, map_neg,
      implies_true]
  refine ⟨fun hΦ x => ?_, h⟩
  simpa only [neg_neg, dft_dft, ← smul_neg, smul_right_inj (NeZero.ne (N : Complex))] using h hΦ (-x)

end signs

end ZMod

namespace DirichletCharacter

variable {N : Nat} [NeZero N]

/--
lemma `fourierTransform_eq_gaussSum_mulShift` / 引理 `fourierTransform_eq_gaussSum_mulShift`

English:
lemma fourierTransform_eq_gaussSum_mulShift
  given: (χ : DirichletCharacter Complex N) (k : ZMod N)
  proof: by
  simp only [dft_apply, smul_eq_mul]
  congr 1 with j
  rw [mulShift_apply]; rw [mul_comm j]; rw [neg_mul]; rw [stdAddChar_apply]; rw [mul_comm (χ _)]

中文:
引理 fourierTransform_eq_gaussSum_mulShift
  条件: (χ : DirichletCharacter 复形 N) (k : ZMod N)
  证明: by
  simp only [dft_apply, smul_eq_mul]
  congr 1 with j
  rw [mulShift_apply]; rw [mul_comm j]; rw [neg_mul]; rw [stdAddChar_apply]; rw [mul_comm (χ _)]

Depends on / 依赖: dft_apply, mulShift_apply, mul_comm, neg_mul, smul_eq_mul, stdAddChar_apply
-/
lemma fourierTransform_eq_gaussSum_mulShift (χ : DirichletCharacter Complex N) (k : ZMod N) :
    𝓕 χ k = gaussSum χ (stdAddChar.mulShift (-k)) := by
  simp only [dft_apply, smul_eq_mul]
  congr 1 with j
  rw [mulShift_apply]; rw [mul_comm j]; rw [neg_mul]; rw [stdAddChar_apply]; rw [mul_comm (χ _)]

/--
lemma `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum` / 引理 `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`

English:
lemma IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
  statement: {χ : DirichletCharacter Complex N}
  proof: by
  rw [fourierTransform_eq_gaussSum_mulShift]; rw [gaussSum_mulShift_of_isPrimitive _ hχ]

中文:
引理 是Primitive.fourierTransform_eq_inv_mul_gaussSum
  结论: {χ : DirichletCharacter 复形 N}
  证明: by
  rw [fourierTransform_eq_gaussSum_mulShift]; rw [gaussSum_mulShift_of_isPrimitive _ hχ]

Depends on / 依赖: fourierTransform_eq_gaussSum_mulShift, gaussSum_mulShift_of_isPrimitive
-/
lemma IsPrimitive.fourierTransform_eq_inv_mul_gaussSum {χ : DirichletCharacter Complex N}
    (hχ : IsPrimitive χ) (k : ZMod N) :
    𝓕 χ k = χ⁻¹ (-k) * gaussSum χ stdAddChar := by
  rw [fourierTransform_eq_gaussSum_mulShift]; rw [gaussSum_mulShift_of_isPrimitive _ hχ]

end DirichletCharacter
