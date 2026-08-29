/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.FieldTheory.Relrank

/-!
# Lüroth's theorem

This file proves Lüroth's theorem, which says that for every field `K`, every
intermediate field between `K` and the rational function field `K⟮X⟯` is either
`K` or isomorphic to `K(X)` as an K-algebra, see `Luroth.algEquiv`. The proof
depends on the following lemma on degrees of rational functions:

Let `f` be a rational function, i.e. an element in the field `K⟮X⟯`.
Let `p` be its numerator and `q` its denominator. Then the degree of the
field extension `K⟮X⟯/K⟮f⟯` equals the maximum of the degrees of `p` and `q`,
see `finrank_eq_max_natDegree`. Since `finrank` is defined to be zero when the
extension is infinite, this holds even when `f` is constant.

References:

- https://github.com/leanprover-community/mathlib4/pull/7788#issuecomment-1788132019
- [P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*][cohn_2003], Theorem 11.3.4
- [N. Jacobson, *Basic Algebra II: Second Edition*][jacobson1989], Theorem 8.38

-/

variable {K : Type*} [Field K]

open IntermediateField

namespace RatFunc.Luroth

noncomputable section

open algebraAdjoinAdjoin Polynomial

open scoped Polynomial.Bivariate

variable {E : IntermediateField K K⟮X⟯}

-- The proof of Lüroth's theorem begins here. We follow the approach from
-- [Cohn, Basic Algebra: Groups, Rings and Fields][cohn_2003].

variable (E) in
/--
Definition of `φ` / `φ` 的定义

English:
abbreviation φ
  signature: : E[X]
  body: minpoly E (X : K⟮X⟯)

中文:
缩写 φ
  签名: : E[X]
  定义体: minpoly E (X : K⟮X⟯)

Depends on / 依赖: minpoly
-/
abbrev φ : E[X] := minpoly E (X : K⟮X⟯)

/--
lemma `φ_ne_zero` / 引理 `φ_ne_zero`

English:
lemma φ_ne_zero
  given: (h : E != ⊥)
  statement: φ E != 0
  proof: minpoly.ne_zero (IntermediateField.isAlgebraic_X h).isIntegral

中文:
引理 φ_ne_zero
  条件: (h : E != ⊥)
  结论: φ E != 0
  证明: minpoly.ne_zero (IntermediateField.isAlgebraic_X h).isIntegral

Depends on / 依赖: IntermediateField, IntermediateField.isAlgebraic_X, isAlgebraic_X, isIntegral, minpoly, minpoly.ne_zero, ne_zero
-/
lemma φ_ne_zero (h : E != ⊥) : φ E != 0 :=
  minpoly.ne_zero (IntermediateField.isAlgebraic_X h).isIntegral

/--
lemma `φ_monic` / 引理 `φ_monic`

English:
lemma φ_monic
  given: (h : E != ⊥)
  statement: (φ E).Monic
  proof: minpoly.monic (IntermediateField.isAlgebraic_X h).isIntegral

中文:
引理 φ_monic
  条件: (h : E != ⊥)
  结论: (φ E).Monic
  证明: minpoly.monic (IntermediateField.isAlgebraic_X h).isIntegral

Depends on / 依赖: IntermediateField, IntermediateField.isAlgebraic_X, isAlgebraic_X, isIntegral, minpoly, minpoly.monic
-/
lemma φ_monic (h : E != ⊥) : (φ E).Monic :=
  minpoly.monic (IntermediateField.isAlgebraic_X h).isIntegral

/--
lemma `φ_natDegree` / 引理 `φ_natDegree`

English:
lemma φ_natDegree
  given: (h : E != ⊥)
  statement: (φ E).natDegree = Module.finrank E K⟮X⟯
  proof: by
  rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq]; rw [adjoin.finrank (IntermediateField.isAlgebraic_X h).isIntegral]

中文:
引理 φ_natDegree
  条件: (h : E != ⊥)
  结论: (φ E).natDegree = 模.finrank E K⟮X⟯
  证明: by
  rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq]; rw [adjoin.finrank (IntermediateField.isAlgebraic_X h).isIntegral]

Depends on / 依赖: IntermediateField, IntermediateField.adjoinXEquiv, IntermediateField.isAlgebraic_X, adjoin, adjoin.finrank, adjoinXEquiv, finrank, finrank_eq, isAlgebraic_X, isIntegral, toLinearEquiv, toLinearEquiv.finrank_eq
-/
lemma φ_natDegree (h : E != ⊥) : (φ E).natDegree = Module.finrank E K⟮X⟯ := by
  rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq]; rw [adjoin.finrank (IntermediateField.isAlgebraic_X h).isIntegral]

/--
lemma `exists_φ_coeff_not_mem` / 引理 `exists_φ_coeff_not_mem`

English:
lemma exists_φ_coeff_not_mem
  given: (h : E != ⊥)
  proof: by
  rw [← notMem_map_range]
  intro ⟨f, hf⟩
  rw [coe_mapRingHom] at hf
  refine transcendental_X ⟨f, ?_, ?_⟩
  · apply (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K E)).mp
    exact hf ▸ φ_ne_zero h
  · simpa using congr(aeval (X : K⟮X⟯) $(hf))

中文:
引理 存在_φ_coeff_not_mem
  条件: (h : E != ⊥)
  证明: by
  rw [← notMem_map_range]
  intro ⟨f, hf⟩
  rw [coe_mapRingHom] at hf
  refine transcendental_X ⟨f, ?_, ?_⟩
  · apply (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K E)).mp
    exact hf ▸ φ_ne_zero h
  · simpa using congr(aeval (X : K⟮X⟯) $(hf))

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Polynomial, Polynomial.map_ne_zero_iff, algebraMap_injective, coe_mapRingHom, map_ne_zero_iff, notMem_map_range, transcendental_X
-/
lemma exists_φ_coeff_not_mem (h : E != ⊥) :
    exists i, (φ E).coeff i ∉ (algebraMap K E).range := by
  rw [← notMem_map_range]
  intro ⟨f, hf⟩
  rw [coe_mapRingHom] at hf
  refine transcendental_X ⟨f, ?_, ?_⟩
  · apply (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K E)).mp
    exact hf ▸ φ_ne_zero h
  · simpa using congr(aeval (X : K⟮X⟯) $(hf))

/--
Definition of `generatorIndex` / `generatorIndex` 的定义

English:
definition generatorIndex
  signature: (h : E != ⊥)
  body: (exists_φ_coeff_not_mem h).choose

中文:
定义 generatorIndex
  签名: (h : E != ⊥)
  定义体: (exists_φ_coeff_not_mem h).choose
-/
def generatorIndex (h : E != ⊥) : Nat :=
  (exists_φ_coeff_not_mem h).choose

variable (E) in
open scoped Classical in
/-- A choice of a generator for Lüroth's theorem, see `Luroth.eq_adjoin_generator`. -/
public def generator : K⟮X⟯ :=
  if h : E = ⊥ then 0 else (φ E).coeff (generatorIndex h)

public lemma generator_eq_zero (h : E = ⊥) : generator E = 0 :=
  dif_pos h

/--
lemma `generator_eq_coeff` / 引理 `generator_eq_coeff`

English:
lemma generator_eq_coeff
  given: (h : E != ⊥)
  statement: generator E = (φ E).coeff (generatorIndex h)
  proof: dif_neg h

public lemma generator_mem : generator E in E := by
  by_cases h : E = ⊥
  · rw [generator_eq_zero h]
    exact E.zero_mem
  · rw [generator_eq_coeff h]
    exact SetLike.coe_mem _

public lemma generator_spec (h : E != ⊥) : generator E ∉ (algebraMap K K⟮X⟯).range := by
  rw [generator_eq_coeff h]
  intro ⟨f, hf⟩
  exact (exists_φ_coeff_not_mem h).choose_spec ⟨f, by ext; exact hf⟩

public lemma generator_ne_C (h : E != ⊥) : ¬ exists c, generator E = C c :=
  fun ⟨c, hc⟩ => generator_spec h ⟨c, (by simpa using hc.symm)⟩

public lemma transcendental_generator (h : E != ⊥) : Transcendental K (generator E) :=
  (generator E).transcendental_of_ne_C (generator_ne_C h)

public lemma generator_ne_zero (h : E != ⊥) : generator E != 0 :=
  fun H => generator_ne_C h ⟨0, by simp [H]⟩

public lemma adjoin_generator_le : K⟮generator E⟯ <= E :=
  adjoin_simple_le_iff.mpr generator_mem

中文:
引理 generator_eq_coeff
  条件: (h : E != ⊥)
  结论: generator E = (φ E).coeff (generatorIndex h)
  证明: dif_neg h

public lemma generator_mem : generator E in E := by
  by_cases h : E = ⊥
  · rw [generator_eq_zero h]
    exact E.zero_mem
  · rw [generator_eq_coeff h]
    exact SetLike.coe_mem _

public lemma generator_spec (h : E != ⊥) : generator E ∉ (algebraMap K K⟮X⟯).range := by
  rw [generator_eq_coeff h]
  intro ⟨f, hf⟩
  exact (exists_φ_coeff_not_mem h).choose_spec ⟨f, by ext; exact hf⟩

public lemma generator_ne_C (h : E != ⊥) : ¬ exists c, generator E = C c :=
  fun ⟨c, hc⟩ => generator_spec h ⟨c, (by simpa using hc.symm)⟩

public lemma transcendental_generator (h : E != ⊥) : Transcendental K (generator E) :=
  (generator E).transcendental_of_ne_C (generator_ne_C h)

public lemma generator_ne_zero (h : E != ⊥) : generator E != 0 :=
  fun H => generator_ne_C h ⟨0, by simp [H]⟩

public lemma adjoin_generator_le : K⟮generator E⟯ <= E :=
  adjoin_simple_le_iff.mpr generator_mem

Depends on / 依赖: dif_neg
-/
lemma generator_eq_coeff (h : E != ⊥) : generator E = (φ E).coeff (generatorIndex h) :=
  dif_neg h

public lemma generator_mem : generator E in E := by
  by_cases h : E = ⊥
  · rw [generator_eq_zero h]
    exact E.zero_mem
  · rw [generator_eq_coeff h]
    exact SetLike.coe_mem _

public lemma generator_spec (h : E != ⊥) : generator E ∉ (algebraMap K K⟮X⟯).range := by
  rw [generator_eq_coeff h]
  intro ⟨f, hf⟩
  exact (exists_φ_coeff_not_mem h).choose_spec ⟨f, by ext; exact hf⟩

public lemma generator_ne_C (h : E != ⊥) : ¬ exists c, generator E = C c :=
  fun ⟨c, hc⟩ => generator_spec h ⟨c, (by simpa using hc.symm)⟩

public lemma transcendental_generator (h : E != ⊥) : Transcendental K (generator E) :=
  (generator E).transcendental_of_ne_C (generator_ne_C h)

public lemma generator_ne_zero (h : E != ⊥) : generator E != 0 :=
  fun H => generator_ne_C h ⟨0, by simp [H]⟩

public lemma adjoin_generator_le : K⟮generator E⟯ <= E :=
  adjoin_simple_le_iff.mpr generator_mem

variable (E) in
/--
Definition of `f` / `f` 的定义

English:
abbreviation f
  signature: : K[X]
  body: (generator E).num

中文:
缩写 f
  签名: : K[X]
  定义体: (generator E).num

Depends on / 依赖: generator
-/
abbrev f : K[X] := (generator E).num

variable (E) in
/-- The denominator of the generator. -/
.denom abbrev g : K[X] := generator E

-- The next step is to define a bivariate polynomial `Φ`, which is a multiple of `φ`.
-- Cohn does this my "multiplying with the lowest common denominator". In this formalisation,
-- we first define `Φ'` as any integer multiple of `φ`, and then set `Φ` to be its
-- primitive part.

variable (E) in
/--
Definition of `Φ'` / `Φ'` 的定义

English:
abbreviation Φ'
  signature: : K[X][Y]
  body: IsLocalization.integerNormalization (nonZeroDivisors K[X]) ((φ E).map (algebraMap E K⟮X⟯))

中文:
缩写 Φ'
  签名: : K[X][Y]
  定义体: IsLocalization.integerNormalization (nonZeroDivisors K[X]) ((φ E).map (algebraMap E K⟮X⟯))

Depends on / 依赖: IsLocalization, IsLocalization.integerNormalization, algebraMap, integerNormalization, nonZeroDivisors
-/
abbrev Φ' : K[X][Y] :=
  IsLocalization.integerNormalization (nonZeroDivisors K[X]) ((φ E).map (algebraMap E K⟮X⟯))

/--
lemma `Φ'_ne_zero` / 引理 `Φ'_ne_zero`

English:
lemma Φ'_ne_zero
  given: (h : E != ⊥)
  statement: Φ' E != 0
  proof: IsFractionRing.integerNormalization_eq_zero_iff.not.mpr (map_ne_zero (φ_ne_zero h))

中文:
引理 Φ'_ne_zero
  条件: (h : E != ⊥)
  结论: Φ' E != 0
  证明: IsFractionRing.integerNormalization_eq_zero_iff.not.mpr (map_ne_zero (φ_ne_zero h))
-/
lemma Φ'_ne_zero (h : E != ⊥) : Φ' E != 0 :=
  IsFractionRing.integerNormalization_eq_zero_iff.not.mpr (map_ne_zero (φ_ne_zero h))

variable (E) in
/--
Definition of `b` / `b` 的定义

English:
definition b
  signature: : K[X]
  body: (IsLocalization.integerNormalization_spec (nonZeroDivisors K[X])
    ((φ E).map (algebraMap E K⟮X⟯))).choose

中文:
定义 b
  签名: : K[X]
  定义体: (IsLocalization.integerNormalization_spec (nonZeroDivisors K[X])
    ((φ E).map (algebraMap E K⟮X⟯))).choose

Depends on / 依赖: IsLocalization, IsLocalization.integerNormalization_spec, algebraMap, integerNormalization_spec, nonZeroDivisors
-/
def b : K[X] :=
  (IsLocalization.integerNormalization_spec (nonZeroDivisors K[X])
    ((φ E).map (algebraMap E K⟮X⟯))).choose

/--
lemma `b_ne_zero` / 引理 `b_ne_zero`

English:
lemma b_ne_zero
  statement: b E != 0
  proof: nonZeroDivisors.ne_zero (IsLocalization.integerNormalization_spec _
    ((φ E).map (algebraMap ..))).choose_spec.1

中文:
引理 b_ne_zero
  结论: b E != 0
  证明: nonZeroDivisors.ne_zero (IsLocalization.integerNormalization_spec _
    ((φ E).map (algebraMap ..))).choose_spec.1

Depends on / 依赖: IsLocalization, IsLocalization.integerNormalization_spec, algebraMap, choose_spec, integerNormalization_spec, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
lemma b_ne_zero : b E != 0 :=
nonZeroDivisors.ne_zero (IsLocalization.integerNormalization_spec _
    ((φ E).map (algebraMap ..))).choose_spec.1

/--
lemma `Φ'_map` / 引理 `Φ'_map`

English:
lemma Φ'_map
  proof: (IsLocalization.integerNormalization_spec _ ((φ E).map (algebraMap ..))).choose_spec.2

中文:
引理 Φ'_map
  证明: (IsLocalization.integerNormalization_spec _ ((φ E).map (algebraMap ..))).choose_spec.2
-/
lemma Φ'_map :
    (Φ' E).map (algebraMap K[X] K⟮X⟯) = (b E) • (φ E).map (algebraMap ..) :=
  (IsLocalization.integerNormalization_spec _ ((φ E).map (algebraMap ..))).choose_spec.2

variable (E) in
open scoped Classical in
/--
Definition of `c` / `c` 的定义

English:
abbreviation c
  signature: : K⟮X⟯
  body: (algebraMap K[X] K⟮X⟯ (Φ' E).content)⁻¹ * (algebraMap K[X] K⟮X⟯ (b E))

中文:
缩写 c
  签名: : K⟮X⟯
  定义体: (algebraMap K[X] K⟮X⟯ (Φ' E).content)⁻¹ * (algebraMap K[X] K⟮X⟯ (b E))

Depends on / 依赖: algebraMap, content
-/
abbrev c : K⟮X⟯ :=
  (algebraMap K[X] K⟮X⟯ (Φ' E).content)⁻¹ * (algebraMap K[X] K⟮X⟯ (b E))

open scoped Classical in
/--
lemma `c_ne_zero` / 引理 `c_ne_zero`

English:
lemma c_ne_zero
  given: (h : E != ⊥)
  statement: c E != 0
  proof: mul_ne_zero_iff.mpr ⟨inv_ne_zero (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr
    content_eq_zero_iff.not.mpr (Φ'_ne_zero h),
  (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr b_ne_zero⟩

中文:
引理 c_ne_zero
  条件: (h : E != ⊥)
  结论: c E != 0
  证明: mul_ne_zero_iff.mpr ⟨inv_ne_zero (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr
    content_eq_zero_iff.not.mpr (Φ'_ne_zero h),
  (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr b_ne_zero⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, _ne_zero, algebraMap_eq_zero_iff, b_ne_zero, content_eq_zero_iff, content_eq_zero_iff.not.mpr, inv_ne_zero, mul_ne_zero_iff, mul_ne_zero_iff.mpr, not.mpr
-/
lemma c_ne_zero (h : E != ⊥) : c E != 0 :=
mul_ne_zero_iff.mpr ⟨inv_ne_zero (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr
    content_eq_zero_iff.not.mpr (Φ'_ne_zero h),
  (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr b_ne_zero⟩

variable (E) in
open scoped Classical in
/--
Definition of `Φ` / `Φ` 的定义

English:
abbreviation Φ
  signature: : K[X][Y]
  body: (Φ' E).primPart

中文:
缩写 Φ
  签名: : K[X][Y]
  定义体: (Φ' E).primPart

Depends on / 依赖: primPart
-/
abbrev Φ : K[X][Y] := (Φ' E).primPart

/--
lemma `C_c_mul_φ` / 引理 `C_c_mul_φ`

English:
lemma C_c_mul_φ
  given: (h : E != ⊥)
  proof: by
  classical
  rw [map_mul]; rw [mul_assoc]
  conv =>
    enter [1, 2]
    rw [← Polynomial.smul_eq_C_mul]; rw [algebraMap_smul]; rw [← Φ'_map]; rw [eq_C_content_mul_primPart (Φ' E)]
  rw [Polynomial.map_mul]; rw [map_C]; rw [← mul_assoc]; rw [← C_mul]; rw [inv_mul_cancel₀]; rw [map_one]; rw [one_mul]
  · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff]
    exact Φ'_ne_zero h

中文:
引理 C_c_mul_φ
  条件: (h : E != ⊥)
  证明: by
  classical
  rw [map_mul]; rw [mul_assoc]
  conv =>
    enter [1, 2]
    rw [← Polynomial.smul_eq_C_mul]; rw [algebraMap_smul]; rw [← Φ'_map]; rw [eq_C_content_mul_primPart (Φ' E)]
  rw [Polynomial.map_mul]; rw [map_C]; rw [← mul_assoc]; rw [← C_mul]; rw [inv_mul_cancel₀]; rw [map_one]; rw [one_mul]
  · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff]
    exact Φ'_ne_zero h

Depends on / 依赖: C_mul, FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, Polynomial, Polynomial.map_mul, Polynomial.smul_eq_C_mul, _map, _ne_zero, algebraMap_eq_zero_iff, algebraMap_smul, classical, content_eq_zero_iff, eq_C_content_mul_primPart, map_C, map_mul, map_one, mul_assoc, ne_eq, one_mul, smul_eq_C_mul
-/
lemma C_c_mul_φ (h : E != ⊥) :
    Polynomial.C (c E) * (φ E).map (algebraMap E K⟮X⟯) = (Φ E).map (algebraMap ..) := by
  classical
  rw [map_mul]; rw [mul_assoc]
  conv =>
    enter [1, 2]
    rw [← Polynomial.smul_eq_C_mul]; rw [algebraMap_smul]; rw [← Φ'_map]; rw [eq_C_content_mul_primPart (Φ' E)]
  rw [Polynomial.map_mul]; rw [map_C]; rw [← mul_assoc]; rw [← C_mul]; rw [inv_mul_cancel₀]; rw [map_one]; rw [one_mul]
  · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff]
    exact Φ'_ne_zero h

/--
lemma `Φ_natDegree_eq_φ_natDegree` / 引理 `Φ_natDegree_eq_φ_natDegree`

English:
lemma Φ_natDegree_eq_φ_natDegree
  given: (h : E != ⊥)
  statement: (Φ E).natDegree = (φ E).natDegree
  proof: by
  rw [← natDegree_map_eq_of_injective (algebraMap_injective K)]; rw [← C_c_mul_φ h]; rw [natDegree_mul (C_ne_zero.mpr (c_ne_zero h)) (map_ne_zero (φ_ne_zero h))]; rw [natDegree_C]; rw [natDegree_map]; rw [zero_add]

中文:
引理 Φ_natDegree_eq_φ_natDegree
  条件: (h : E != ⊥)
  结论: (Φ E).natDegree = (φ E).natDegree
  证明: by
  rw [← natDegree_map_eq_of_injective (algebraMap_injective K)]; rw [← C_c_mul_φ h]; rw [natDegree_mul (C_ne_zero.mpr (c_ne_zero h)) (map_ne_zero (φ_ne_zero h))]; rw [natDegree_C]; rw [natDegree_map]; rw [zero_add]

Depends on / 依赖: C_ne_zero, C_ne_zero.mpr, algebraMap_injective, c_ne_zero, map_ne_zero, natDegree_C, natDegree_map, natDegree_map_eq_of_injective, natDegree_mul, zero_add
-/
lemma Φ_natDegree_eq_φ_natDegree (h : E != ⊥) : (Φ E).natDegree = (φ E).natDegree := by
  rw [← natDegree_map_eq_of_injective (algebraMap_injective K)]; rw [← C_c_mul_φ h]; rw [natDegree_mul (C_ne_zero.mpr (c_ne_zero h)) (map_ne_zero (φ_ne_zero h))]; rw [natDegree_C]; rw [natDegree_map]; rw [zero_add]

/--
lemma `Φ_coeff_φ_natDegree` / 引理 `Φ_coeff_φ_natDegree`

English:
lemma Φ_coeff_φ_natDegree
  given: (h : E != ⊥)
  proof: by
  have := congr($(C_c_mul_φ h).coeff (φ E).natDegree)
  rw [coeff_C_mul]; rw [coeff_map]; rw [coeff_map]; rw [coeff_natDegree]; rw [IntermediateField.algebraMap_apply]; rw [φ_monic h]; rw [OneMemClass.coe_one]; rw [mul_one] at this
  exact this.symm

中文:
引理 Φ_coeff_φ_natDegree
  条件: (h : E != ⊥)
  证明: by
  have := congr($(C_c_mul_φ h).coeff (φ E).natDegree)
  rw [coeff_C_mul]; rw [coeff_map]; rw [coeff_map]; rw [coeff_natDegree]; rw [IntermediateField.algebraMap_apply]; rw [φ_monic h]; rw [OneMemClass.coe_one]; rw [mul_one] at this
  exact this.symm

Depends on / 依赖: IntermediateField, IntermediateField.algebraMap_apply, OneMemClass, OneMemClass.coe_one, algebraMap_apply, coe_one, coeff_C_mul, coeff_map, coeff_natDegree, mul_one, natDegree, this.symm
-/
lemma Φ_coeff_φ_natDegree (h : E != ⊥) :
    algebraMap K[X] K⟮X⟯ ((Φ E).coeff (φ E).natDegree) = c E := by
  have := congr($(C_c_mul_φ h).coeff (φ E).natDegree)
  rw [coeff_C_mul]; rw [coeff_map]; rw [coeff_map]; rw [coeff_natDegree]; rw [IntermediateField.algebraMap_apply]; rw [φ_monic h]; rw [OneMemClass.coe_one]; rw [mul_one] at this
  exact this.symm

/--
lemma `c_denom` / 引理 `c_denom`

English:
lemma c_denom
  given: (h : E != ⊥)
  statement: (c E).denom = 1
  proof: by
  rw [← Φ_coeff_φ_natDegree h]
  exact denom_algebraMap _

中文:
引理 c_denom
  条件: (h : E != ⊥)
  结论: (c E).denom = 1
  证明: by
  rw [← Φ_coeff_φ_natDegree h]
  exact denom_algebraMap _

Depends on / 依赖: denom_algebraMap
-/
lemma c_denom (h : E != ⊥) : (c E).denom = 1 := by
  rw [← Φ_coeff_φ_natDegree h]
  exact denom_algebraMap _

/--
lemma `Φ_coeff_φ_natDegree'` / 引理 `Φ_coeff_φ_natDegree'`

English:
lemma Φ_coeff_φ_natDegree'
  given: (h : E != ⊥)
  proof: by
  apply algebraMap_injective
  rw [Φ_coeff_φ_natDegree h]
  conv_lhs => rw [← num_div_denom (c E), c_denom h, map_one, div_one]

中文:
引理 Φ_coeff_φ_natDegree'
  条件: (h : E != ⊥)
  证明: by
  apply algebraMap_injective
  rw [Φ_coeff_φ_natDegree h]
  conv_lhs => rw [← num_div_denom (c E), c_denom h, map_one, div_one]

Depends on / 依赖: algebraMap_injective, c_denom, conv_lhs, div_one, map_one, num_div_denom
-/
lemma Φ_coeff_φ_natDegree' (h : E != ⊥) :
    (Φ E).coeff (φ E).natDegree = (c E).num := by
  apply algebraMap_injective
  rw [Φ_coeff_φ_natDegree h]
  conv_lhs => rw [← num_div_denom (c E), c_denom h, map_one, div_one]

/--
lemma `Φ_coeff_φ_natDegree_ne_zero` / 引理 `Φ_coeff_φ_natDegree_ne_zero`

English:
lemma Φ_coeff_φ_natDegree_ne_zero
  given: (h : E != ⊥)
  proof: by
  rw [Φ_coeff_φ_natDegree' h]
  exact num_ne_zero (c_ne_zero h)

中文:
引理 Φ_coeff_φ_natDegree_ne_zero
  条件: (h : E != ⊥)
  证明: by
  rw [Φ_coeff_φ_natDegree' h]
  exact num_ne_zero (c_ne_zero h)

Depends on / 依赖: c_ne_zero, num_ne_zero
-/
lemma Φ_coeff_φ_natDegree_ne_zero (h : E != ⊥) :
    (Φ E).coeff (φ E).natDegree != 0 := by
  rw [Φ_coeff_φ_natDegree' h]
  exact num_ne_zero (c_ne_zero h)

/--
lemma `Φ_coeff_generatorIndex` / 引理 `Φ_coeff_generatorIndex`

English:
lemma Φ_coeff_generatorIndex
  given: (h : E != ⊥)
  proof: by
  have := congr($(C_c_mul_φ h).coeff (generatorIndex h))
  rw [coeff_map]; rw [coeff_C_mul]; rw [coeff_map]; rw [IntermediateField.algebraMap_apply]; rw [← num_div_denom (c E)]; rw [c_denom h]; rw [map_one]; rw [div_one] at this
  rw [generator_eq_coeff h]
  exact this.symm

中文:
引理 Φ_coeff_generatorIndex
  条件: (h : E != ⊥)
  证明: by
  have := congr($(C_c_mul_φ h).coeff (generatorIndex h))
  rw [coeff_map]; rw [coeff_C_mul]; rw [coeff_map]; rw [IntermediateField.algebraMap_apply]; rw [← num_div_denom (c E)]; rw [c_denom h]; rw [map_one]; rw [div_one] at this
  rw [generator_eq_coeff h]
  exact this.symm

Depends on / 依赖: IntermediateField, IntermediateField.algebraMap_apply, algebraMap_apply, c_denom, coeff_C_mul, coeff_map, div_one, generatorIndex, generator_eq_coeff, map_one, num_div_denom, this.symm
-/
lemma Φ_coeff_generatorIndex (h : E != ⊥) :
    algebraMap K[X] K⟮X⟯ ((Φ E).coeff (generatorIndex h)) =
    algebraMap K[X] K⟮X⟯ (c E).num * generator E := by
  have := congr($(C_c_mul_φ h).coeff (generatorIndex h))
  rw [coeff_map]; rw [coeff_C_mul]; rw [coeff_map]; rw [IntermediateField.algebraMap_apply]; rw [← num_div_denom (c E)]; rw [c_denom h]; rw [map_one]; rw [div_one] at this
  rw [generator_eq_coeff h]
  exact this.symm

/--
lemma `Φ_coeff_generatorIndex_ne_zero` / 引理 `Φ_coeff_generatorIndex_ne_zero`

English:
lemma Φ_coeff_generatorIndex_ne_zero
  given: (h : E != ⊥)
  proof: by
  apply_fun algebraMap K[X] K⟮X⟯
  rw [map_zero]; rw [Φ_coeff_generatorIndex h]
  exact mul_ne_zero_iff.mpr ⟨algebraMap_ne_zero (num_ne_zero (c_ne_zero h)), generator_ne_zero h⟩

中文:
引理 Φ_coeff_generatorIndex_ne_zero
  条件: (h : E != ⊥)
  证明: by
  apply_fun algebraMap K[X] K⟮X⟯
  rw [map_zero]; rw [Φ_coeff_generatorIndex h]
  exact mul_ne_zero_iff.mpr ⟨algebraMap_ne_zero (num_ne_zero (c_ne_zero h)), generator_ne_zero h⟩

Depends on / 依赖: algebraMap, algebraMap_ne_zero, apply_fun, c_ne_zero, generator_ne_zero, map_zero, mul_ne_zero_iff, mul_ne_zero_iff.mpr, num_ne_zero
-/
lemma Φ_coeff_generatorIndex_ne_zero (h : E != ⊥) :
    (Φ E).coeff (generatorIndex h) != 0 := by
  apply_fun algebraMap K[X] K⟮X⟯
  rw [map_zero]; rw [Φ_coeff_generatorIndex h]
  exact mul_ne_zero_iff.mpr ⟨algebraMap_ne_zero (num_ne_zero (c_ne_zero h)), generator_ne_zero h⟩

/--
lemma `generator_denom_dvd_c_num` / 引理 `generator_denom_dvd_c_num`

English:
lemma generator_denom_dvd_c_num
  given: (h : E != ⊥)
  statement: (g E) ∣ (c E).num
  proof: by
  rw [denom_dvd (num_ne_zero (c_ne_zero h))]
  use (Φ E).coeff (generatorIndex h)
  rw [Φ_coeff_generatorIndex h]; rw [mul_div_cancel_left₀ _ (algebraMap_ne_zero (num_ne_zero (c_ne_zero h)))]

中文:
引理 generator_denom_dvd_c_num
  条件: (h : E != ⊥)
  结论: (g E) ∣ (c E).num
  证明: by
  rw [denom_dvd (num_ne_zero (c_ne_zero h))]
  use (Φ E).coeff (generatorIndex h)
  rw [Φ_coeff_generatorIndex h]; rw [mul_div_cancel_left₀ _ (algebraMap_ne_zero (num_ne_zero (c_ne_zero h)))]

Depends on / 依赖: algebraMap_ne_zero, c_ne_zero, denom_dvd, generatorIndex, num_ne_zero
-/
lemma generator_denom_dvd_c_num (h : E != ⊥) : (g E) ∣ (c E).num := by
  rw [denom_dvd (num_ne_zero (c_ne_zero h))]
  use (Φ E).coeff (generatorIndex h)
  rw [Φ_coeff_generatorIndex h]; rw [mul_div_cancel_left₀ _ (algebraMap_ne_zero (num_ne_zero (c_ne_zero h)))]

/--
lemma `Φ_ne_zero` / 引理 `Φ_ne_zero`

English:
lemma Φ_ne_zero
  given: (h : E != ⊥)
  statement: Φ E != 0
  proof: by
  intro H
  have := Φ_coeff_φ_natDegree' h ▸ congr($(H).coeff (φ E).natDegree)
  rw [coeff_zero] at this
  exact num_ne_zero (c_ne_zero h) this

中文:
引理 Φ_ne_zero
  条件: (h : E != ⊥)
  结论: Φ E != 0
  证明: by
  intro H
  have := Φ_coeff_φ_natDegree' h ▸ congr($(H).coeff (φ E).natDegree)
  rw [coeff_zero] at this
  exact num_ne_zero (c_ne_zero h) this

Depends on / 依赖: c_ne_zero, coeff_zero, natDegree, num_ne_zero
-/
lemma Φ_ne_zero (h : E != ⊥) : Φ E != 0 := by
  intro H
  have := Φ_coeff_φ_natDegree' h ▸ congr($(H).coeff (φ E).natDegree)
  rw [coeff_zero] at this
  exact num_ne_zero (c_ne_zero h) this

-- Next, we show that `Φ` has degree at least `m := max(deg(f), deg(g))` in `x`, where
-- `f` and `g` are the numerator and denominator of the `generator`. Cohn mentions
-- this right after Equation (11.3.8). To prove it, we show that the leading coefficient
-- `ν₀(x)` has degree at least `deg(f)`, while `νᵢ(x)` (our chosen coefficient index) has
-- degree at least `deg(g)`. The claim then follows from the fact that the monomials `X ^ i`
-- are linearly independent, see `le_swap_Φ_natDegree`.

/--
lemma `le_Φ_coeff_generatorIndex_natDegree` / 引理 `le_Φ_coeff_generatorIndex_natDegree`

English:
lemma le_Φ_coeff_generatorIndex_natDegree
  given: (h : E != ⊥)
  proof: by
  have := congr($(Φ_coeff_generatorIndex h) * algebraMap K[X] K⟮X⟯ (g E))
  conv at this => enter [2, 1, 2]; rw [← num_div_denom (generator E)]
  rw [mul_assoc]; rw [div_mul_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero)]; rw [← map_mul]; rw [← map_mul] at this
  replace this := congr($(algebraMap_injective K this).natDegree)
  rw [natDegree_mul (Φ_coeff_generatorIndex_ne_zero h) (generator E).denom_ne_zero]; rw [natDegree_mul (num_ne_zero (c_ne_zero h)) (num_ne_zero (generator_ne_zero h))] at this
  grind [natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))]

中文:
引理 le_Φ_coeff_generatorIndex_natDegree
  条件: (h : E != ⊥)
  证明: by
  have := congr($(Φ_coeff_generatorIndex h) * algebraMap K[X] K⟮X⟯ (g E))
  conv at this => enter [2, 1, 2]; rw [← num_div_denom (generator E)]
  rw [mul_assoc]; rw [div_mul_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero)]; rw [← map_mul]; rw [← map_mul] at this
  replace this := congr($(algebraMap_injective K this).natDegree)
  rw [natDegree_mul (Φ_coeff_generatorIndex_ne_zero h) (generator E).denom_ne_zero]; rw [natDegree_mul (num_ne_zero (c_ne_zero h)) (num_ne_zero (generator_ne_zero h))] at this
  grind [natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))]

Depends on / 依赖: algebraMap, algebraMap_injective, algebraMap_ne_zero, c_ne_zero, denom_ne_zero, generator, generator_ne_zero, map_mul, mul_assoc, natDegree, natDegree_mul, num_div_denom, num_ne_zero, replace
-/
lemma le_Φ_coeff_generatorIndex_natDegree (h : E != ⊥) :
    (f E).natDegree <= ((Φ E).coeff (generatorIndex h)).natDegree := by
  have := congr($(Φ_coeff_generatorIndex h) * algebraMap K[X] K⟮X⟯ (g E))
  conv at this => enter [2, 1, 2]; rw [← num_div_denom (generator E)]
  rw [mul_assoc]; rw [div_mul_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero)]; rw [← map_mul]; rw [← map_mul] at this
  replace this := congr($(algebraMap_injective K this).natDegree)
  rw [natDegree_mul (Φ_coeff_generatorIndex_ne_zero h) (generator E).denom_ne_zero]; rw [natDegree_mul (num_ne_zero (c_ne_zero h)) (num_ne_zero (generator_ne_zero h))] at this
  grind [natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))]

/--
lemma `le_Φ_coeff_natDegree_natDegree` / 引理 `le_Φ_coeff_natDegree_natDegree`

English:
lemma le_Φ_coeff_natDegree_natDegree
  given: (h : E != ⊥)
  proof: by
  rw [Φ_coeff_φ_natDegree' h]
  exact natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))

中文:
引理 le_Φ_coeff_natDegree_natDegree
  条件: (h : E != ⊥)
  证明: by
  rw [Φ_coeff_φ_natDegree' h]
  exact natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))

Depends on / 依赖: c_ne_zero, generator_denom_dvd_c_num, natDegree_le_of_dvd, num_ne_zero
-/
lemma le_Φ_coeff_natDegree_natDegree (h : E != ⊥) :
    (g E).natDegree <= ((Φ E).coeff (φ E).natDegree).natDegree := by
  rw [Φ_coeff_φ_natDegree' h]
  exact natDegree_le_of_dvd (generator_denom_dvd_c_num h) (num_ne_zero (c_ne_zero h))

variable (E) in
/--
Definition of `m` / `m` 的定义

English:
abbreviation m
  signature: : Nat
  body: max (f E).natDegree (g E).natDegree

中文:
缩写 m
  签名: : 自然数
  定义体: max (f E).natDegree (g E).natDegree

Depends on / 依赖: natDegree
-/
abbrev m : Nat := max (f E).natDegree (g E).natDegree

/--
lemma `m_le_swap_Φ_natDegree` / 引理 `m_le_swap_Φ_natDegree`

English:
lemma m_le_swap_Φ_natDegree
  given: (h : E != ⊥)
  proof: by
  rw [← sum_monomial_eq (Φ E)]; rw [sum_def]; rw [map_sum]
  conv in (fun _ => _) =>
    ext
    rw [Bivariate.swap_monomial]; rw [mul_comm]; rw [← Polynomial.smul_eq_C_mul]; rw [← monomial_one_right_eq_X_pow]; rw [← Polynomial.algebraMap_eq]
  rw [natDegree_sum_eq_of_linearIndepOn _
    (coe_basisMonomials K ▸ (basisMonomials K).linearIndepOn (Φ E).support)]
  apply max_le
· exact (le_Φ_coeff_generatorIndex_natDegree h).trans
Finset.le_sup (f := fun i => ((Φ E).coeff i).natDegree)
      mem_support_iff.mpr (Φ_coeff_generatorIndex_ne_zero h)
· exact (le_Φ_coeff_natDegree_natDegree h).trans
Finset.le_sup (f := fun i => ((Φ E).coeff i).natDegree)
      mem_support_iff.mpr (Φ_coeff_φ_natDegree_ne_zero h)

中文:
引理 m_le_swap_Φ_natDegree
  条件: (h : E != ⊥)
  证明: by
  rw [← sum_monomial_eq (Φ E)]; rw [sum_def]; rw [map_sum]
  conv in (fun _ => _) =>
    ext
    rw [Bivariate.swap_monomial]; rw [mul_comm]; rw [← Polynomial.smul_eq_C_mul]; rw [← monomial_one_right_eq_X_pow]; rw [← Polynomial.algebraMap_eq]
  rw [natDegree_sum_eq_of_linearIndepOn _
    (coe_basisMonomials K ▸ (basisMonomials K).linearIndepOn (Φ E).support)]
  apply max_le
· exact (le_Φ_coeff_generatorIndex_natDegree h).trans
Finset.le_sup (f := fun i => ((Φ E).coeff i).natDegree)
      mem_support_iff.mpr (Φ_coeff_generatorIndex_ne_zero h)
· exact (le_Φ_coeff_natDegree_natDegree h).trans
Finset.le_sup (f := fun i => ((Φ E).coeff i).natDegree)
      mem_support_iff.mpr (Φ_coeff_φ_natDegree_ne_zero h)

Depends on / 依赖: Bivariate, Bivariate.swap_monomial, Finset, Finset.le_sup, Polynomial, Polynomial.algebraMap_eq, Polynomial.smul_eq_C_mul, algebraMap_eq, basisMonomials, coe_basisMonomials, le_sup, linearIndepOn, map_sum, max_le, mem_support_iff, mem_support_iff.mpr, monomial_one_right_eq_X_pow, mul_comm, natDegree, natDegree_sum_eq_of_linearIndepOn
-/
lemma m_le_swap_Φ_natDegree (h : E != ⊥) :
    m E <= (Bivariate.swap (Φ E)).natDegree := by
  rw [← sum_monomial_eq (Φ E)]; rw [sum_def]; rw [map_sum]
  conv in (fun _ => _) =>
    ext
    rw [Bivariate.swap_monomial]; rw [mul_comm]; rw [← Polynomial.smul_eq_C_mul]; rw [← monomial_one_right_eq_X_pow]; rw [← Polynomial.algebraMap_eq]
  rw [natDegree_sum_eq_of_linearIndepOn _
    (coe_basisMonomials K ▸ (basisMonomials K).linearIndepOn (Φ E).support)]
  apply max_le
· exact (le_Φ_coeff_generatorIndex_natDegree h).trans
Finset.le_sup (f := fun i => ((Φ E).coeff i).natDegree)
      mem_support_iff.mpr (Φ_coeff_generatorIndex_ne_zero h)
· exact (le_Φ_coeff_natDegree_natDegree h).trans
Finset.le_sup (f := fun i => ((Φ E).coeff i).natDegree)
      mem_support_iff.mpr (Φ_coeff_φ_natDegree_ne_zero h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra K⟮generator E⟯ E
  body: (IntermediateField.inclusion adjoin_generator_le).toAlgebra

中文:
实例 :
  签名: 代数 K⟮generator E⟯ E
  定义体: (IntermediateField.inclusion adjoin_generator_le).toAlgebra

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, adjoin_generator_le, inclusion, toAlgebra
-/
instance : Algebra K⟮generator E⟯ E :=
  (IntermediateField.inclusion adjoin_generator_le).toAlgebra

/--
lemma `φ_dvd_generator_minpolyX` / 引理 `φ_dvd_generator_minpolyX`

English:
lemma φ_dvd_generator_minpolyX
  proof: by
  apply minpoly.dvd
  rw [← aeval_eq_aeval_map rfl]
  exact (generator E).minpolyX_aeval_X

中文:
引理 φ_dvd_generator_minpolyX
  证明: by
  apply minpoly.dvd
  rw [← aeval_eq_aeval_map rfl]
  exact (generator E).minpolyX_aeval_X

Depends on / 依赖: aeval_eq_aeval_map, generator, minpoly, minpoly.dvd, minpolyX_aeval_X
-/
lemma φ_dvd_generator_minpolyX :
    φ E ∣ ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) := by
  apply minpoly.dvd
  rw [← aeval_eq_aeval_map rfl]
  exact (generator E).minpolyX_aeval_X

variable (E) in
/--
Definition of `q` / `q` 的定义

English:
abbreviation q
  signature: : E[X]
  body: φ_dvd_generator_minpolyX.choose

中文:
缩写 q
  签名: : E[X]
  定义体: φ_dvd_generator_minpolyX.choose

Depends on / 依赖: _dvd_generator_minpolyX.choose
-/
abbrev q : E[X] := φ_dvd_generator_minpolyX.choose

/--
lemma `φ_mul_q` / 引理 `φ_mul_q`

English:
lemma φ_mul_q
  proof: φ_dvd_generator_minpolyX.choose_spec.symm

中文:
引理 φ_mul_q
  证明: φ_dvd_generator_minpolyX.choose_spec.symm

Depends on / 依赖: _dvd_generator_minpolyX.choose_spec.symm, choose_spec
-/
lemma φ_mul_q :
    φ E * q E = ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) :=
  φ_dvd_generator_minpolyX.choose_spec.symm

/--
lemma `q_ne_zero` / 引理 `q_ne_zero`

English:
lemma q_ne_zero
  given: (h : E != ⊥)
  statement: q E != 0
  proof: right_ne_zero_of_mul
φ_mul_q (E := E) ▸ Polynomial.map_ne_zero
    (generator E).minpolyX_eq_zero_iff.not.mpr (generator_ne_C h)

中文:
引理 q_ne_zero
  条件: (h : E != ⊥)
  结论: q E != 0
  证明: right_ne_zero_of_mul
φ_mul_q (E := E) ▸ Polynomial.map_ne_zero
    (generator E).minpolyX_eq_zero_iff.not.mpr (generator_ne_C h)

Depends on / 依赖: right_ne_zero_of_mul
-/
lemma q_ne_zero (h : E != ⊥) : q E != 0 := right_ne_zero_of_mul
φ_mul_q (E := E) ▸ Polynomial.map_ne_zero
    (generator E).minpolyX_eq_zero_iff.not.mpr (generator_ne_C h)

-- The next series of definitions concerns the polynomial `Q` in Cohn's proof.
-- A priori, it will be a polynomial with coefficients in `K⟮X⟯`, which we call `Q₀`.
-- We then show that `Q₀` is also a polynomial in the other variable, hence we get
-- a bivariate polynomial `Q₁`. Then we show that it is independent of `X`, hence we may
-- replace it by a univariate polynomial `Q₂`. Finally, we prove that it is also independent
-- of `x`, hence we replace it by a constant `Q₃`.

variable (E) in
/--
Definition of `Q₀` / `Q₀` 的定义

English:
abbreviation Q₀
  signature: : K⟮X⟯[X]
  body: Polynomial.C ((algebraMap K[X] K⟮X⟯ (g E)) / c E) * (q E).map (algebraMap E K⟮X⟯)

中文:
缩写 Q₀
  签名: : K⟮X⟯[X]
  定义体: Polynomial.C ((algebraMap K[X] K⟮X⟯ (g E)) / c E) * (q E).map (algebraMap E K⟮X⟯)

Depends on / 依赖: Polynomial, Polynomial.C, algebraMap
-/
abbrev Q₀ : K⟮X⟯[X] :=
  Polynomial.C ((algebraMap K[X] K⟮X⟯ (g E)) / c E) * (q E).map (algebraMap E K⟮X⟯)

/--
lemma `Q₀_ne_zero` / 引理 `Q₀_ne_zero`

English:
lemma Q₀_ne_zero
  given: (h : E != ⊥)
  statement: Q₀ E != 0
  proof: by
  apply mul_ne_zero
  · exact C_ne_zero.mpr (div_ne_zero (algebraMap_ne_zero (generator E).denom_ne_zero) (c_ne_zero h))
  · exact Polynomial.map_ne_zero (q_ne_zero h)

中文:
引理 Q₀_ne_zero
  条件: (h : E != ⊥)
  结论: Q₀ E != 0
  证明: by
  apply mul_ne_zero
  · exact C_ne_zero.mpr (div_ne_zero (algebraMap_ne_zero (generator E).denom_ne_zero) (c_ne_zero h))
  · exact Polynomial.map_ne_zero (q_ne_zero h)

Depends on / 依赖: C_ne_zero, C_ne_zero.mpr, Polynomial, Polynomial.map_ne_zero, algebraMap_ne_zero, c_ne_zero, denom_ne_zero, div_ne_zero, generator, map_ne_zero, mul_ne_zero, q_ne_zero
-/
lemma Q₀_ne_zero (h : E != ⊥) : Q₀ E != 0 := by
  apply mul_ne_zero
  · exact C_ne_zero.mpr (div_ne_zero (algebraMap_ne_zero (generator E).denom_ne_zero) (c_ne_zero h))
  · exact Polynomial.map_ne_zero (q_ne_zero h)

variable (E) in
/--
Definition of `θ` / `θ` 的定义

English:
abbreviation θ
  signature: : K[X][Y]
  body: Polynomial.C (g E) * (f E).map Polynomial.C - Polynomial.C (f E) * (g E).map Polynomial.C

中文:
缩写 θ
  签名: : K[X][Y]
  定义体: Polynomial.C (g E) * (f E).map Polynomial.C - Polynomial.C (f E) * (g E).map Polynomial.C

Depends on / 依赖: Polynomial, Polynomial.C
-/
abbrev θ : K[X][Y] :=
  Polynomial.C (g E) * (f E).map Polynomial.C - Polynomial.C (f E) * (g E).map Polynomial.C

/--
lemma `swap_θ` / 引理 `swap_θ`

English:
lemma swap_θ
  statement: Bivariate.swap (θ E) = -(θ E)
  proof: by
  rw [map_sub]; rw [map_mul]; rw [map_mul]; rw [Bivariate.swap_C]; rw [Bivariate.swap_map_C]; rw [Bivariate.swap_C]; rw [Bivariate.swap_map_C]
  ring

中文:
引理 swap_θ
  结论: Bivariate.swap (θ E) = -(θ E)
  证明: by
  rw [map_sub]; rw [map_mul]; rw [map_mul]; rw [Bivariate.swap_C]; rw [Bivariate.swap_map_C]; rw [Bivariate.swap_C]; rw [Bivariate.swap_map_C]
  ring

Depends on / 依赖: Bivariate, Bivariate.swap_C, Bivariate.swap_map_C, map_mul, map_sub, swap_C, swap_map_C
-/
lemma swap_θ : Bivariate.swap (θ E) = -(θ E) := by
  rw [map_sub]; rw [map_mul]; rw [map_mul]; rw [Bivariate.swap_C]; rw [Bivariate.swap_map_C]; rw [Bivariate.swap_C]; rw [Bivariate.swap_map_C]
  ring

/--
lemma `θ_natDegree_le` / 引理 `θ_natDegree_le`

English:
lemma θ_natDegree_le
  given: (h : E != ⊥)
  statement: (θ E).natDegree <= m E
  proof: by
  convert! natDegree_sub_le _ _ using 3
  · rw [natDegree_mul (C_ne_zero.mpr (generator E).denom_ne_zero)
      (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))), natDegree_C, zero_add,
      natDegree_map]
  · rw [natDegree_mul (C_ne_zero.mpr (num_ne_zero (generator_ne_zero h)))
      (Polynomial.map_ne_zero (generator E).denom_ne_zero), natDegree_C, zero_add, natDegree_map]

中文:
引理 θ_natDegree_le
  条件: (h : E != ⊥)
  结论: (θ E).natDegree <= m E
  证明: by
  convert! natDegree_sub_le _ _ using 3
  · rw [natDegree_mul (C_ne_zero.mpr (generator E).denom_ne_zero)
      (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))), natDegree_C, zero_add,
      natDegree_map]
  · rw [natDegree_mul (C_ne_zero.mpr (num_ne_zero (generator_ne_zero h)))
      (Polynomial.map_ne_zero (generator E).denom_ne_zero), natDegree_C, zero_add, natDegree_map]

Depends on / 依赖: C_ne_zero, C_ne_zero.mpr, IsEmpty, IsEmpty.oriented, Module, Module.Oriented, Oriented, Polynomial, Polynomial.map_ne_zero, convert, denom_ne_zero, generator, generator_ne_zero, map_ne_zero, natDegree_C, natDegree_map, natDegree_mul, natDegree_sub_le, num_ne_zero, oriented
-/
lemma θ_natDegree_le (h : E != ⊥) : (θ E).natDegree <= m E := by
  convert! natDegree_sub_le _ _ using 3
  · rw [natDegree_mul (C_ne_zero.mpr (generator E).denom_ne_zero)
      (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h))), natDegree_C, zero_add,
      natDegree_map]
  · rw [natDegree_mul (C_ne_zero.mpr (num_ne_zero (generator_ne_zero h)))
      (Polynomial.map_ne_zero (generator E).denom_ne_zero), natDegree_C, zero_add, natDegree_map]

/--
lemma `Q₀_mul_Φ` / 引理 `Q₀_mul_Φ`

English:
lemma Q₀_mul_Φ
  given: (h : E != ⊥)
  proof: by
  suffices
    Polynomial.C ((algebraMap K[X] K⟮X⟯) (g E)) * (q E).map (algebraMap (↥E) K⟮X⟯) *
       (φ E).map (algebraMap (↥E) K⟮X⟯) = (θ E).map (algebraMap K[X] K⟮X⟯) by
    rw [← C_c_mul_φ h]; rw [mul_assoc]; rw [← mul_assoc _ (Polynomial.C (c E)) _]; rw [mul_comm _ (Polynomial.C (c E))]
    simpa only [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (c_ne_zero h)] using this
  rw [mul_assoc]; rw [← Polynomial.map_mul]; rw [mul_comm (q E) (φ E)]; rw [φ_mul_q]; rw [Polynomial.map_map]; rw [Polynomial.map_sub]; rw [Polynomial.map_mul]; rw [map_C]; rw [RingHom.coe_comp]; rw [Function.comp_apply]; rw [IntermediateField.algebraMap_apply]; rw [Polynomial.map_map]; rw [Polynomial.map_map]; rw [mul_sub]; rw [← mul_assoc]; rw [← map_mul]; rw [(inclusion adjoin_generator_le).algebraMap_toAlgebra]; rw [AlgHom.toRingHom_eq_coe]; rw [RingHom.coe_coe]; rw [coe_inclusion]; rw [coe_algebraMap]
  conv => enter [1, 2, 1, 2, 2]; rw [← num_div_denom (generator E)]
  rw [mul_div_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero)]; rw [Polynomial.map_sub]; rw [Polynomial.map_mul]; rw [Polynomial.map_mul]; rw [map_C]; rw [map_C]; rw [Polynomial.map_map]; rw [Polynomial.map_map]
  rfl

中文:
引理 Q₀_mul_Φ
  条件: (h : E != ⊥)
  证明: by
  suffices
    Polynomial.C ((algebraMap K[X] K⟮X⟯) (g E)) * (q E).map (algebraMap (↥E) K⟮X⟯) *
       (φ E).map (algebraMap (↥E) K⟮X⟯) = (θ E).map (algebraMap K[X] K⟮X⟯) by
    rw [← C_c_mul_φ h]; rw [mul_assoc]; rw [← mul_assoc _ (Polynomial.C (c E)) _]; rw [mul_comm _ (Polynomial.C (c E))]
    simpa only [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (c_ne_zero h)] using this
  rw [mul_assoc]; rw [← Polynomial.map_mul]; rw [mul_comm (q E) (φ E)]; rw [φ_mul_q]; rw [Polynomial.map_map]; rw [Polynomial.map_sub]; rw [Polynomial.map_mul]; rw [map_C]; rw [RingHom.coe_comp]; rw [Function.comp_apply]; rw [IntermediateField.algebraMap_apply]; rw [Polynomial.map_map]; rw [Polynomial.map_map]; rw [mul_sub]; rw [← mul_assoc]; rw [← map_mul]; rw [(inclusion adjoin_generator_le).algebraMap_toAlgebra]; rw [AlgHom.toRingHom_eq_coe]; rw [RingHom.coe_coe]; rw [coe_inclusion]; rw [coe_algebraMap]
  conv => enter [1, 2, 1, 2, 2]; rw [← num_div_denom (generator E)]
  rw [mul_div_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero)]; rw [Polynomial.map_sub]; rw [Polynomial.map_mul]; rw [Polynomial.map_mul]; rw [map_C]; rw [map_C]; rw [Polynomial.map_map]; rw [Polynomial.map_map]
  rfl

Depends on / 依赖: C_mul, Polynomial, Polynomial.C, Polynomial.map_map, Polynomial.map_mul, Polynomial.map_sub, algebraMap, c_ne_zero, map_map, map_mul, map_sub, mul_assoc, mul_comm
-/
lemma Q₀_mul_Φ (h : E != ⊥) :
    Q₀ E * (Φ E).map (algebraMap K[X] K⟮X⟯) = (θ E).map (algebraMap K[X] K⟮X⟯) := by
  suffices
    Polynomial.C ((algebraMap K[X] K⟮X⟯) (g E)) * (q E).map (algebraMap (↥E) K⟮X⟯) *
       (φ E).map (algebraMap (↥E) K⟮X⟯) = (θ E).map (algebraMap K[X] K⟮X⟯) by
    rw [← C_c_mul_φ h]; rw [mul_assoc]; rw [← mul_assoc _ (Polynomial.C (c E)) _]; rw [mul_comm _ (Polynomial.C (c E))]
    simpa only [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (c_ne_zero h)] using this
  rw [mul_assoc]; rw [← Polynomial.map_mul]; rw [mul_comm (q E) (φ E)]; rw [φ_mul_q]; rw [Polynomial.map_map]; rw [Polynomial.map_sub]; rw [Polynomial.map_mul]; rw [map_C]; rw [RingHom.coe_comp]; rw [Function.comp_apply]; rw [IntermediateField.algebraMap_apply]; rw [Polynomial.map_map]; rw [Polynomial.map_map]; rw [mul_sub]; rw [← mul_assoc]; rw [← map_mul]; rw [(inclusion adjoin_generator_le).algebraMap_toAlgebra]; rw [AlgHom.toRingHom_eq_coe]; rw [RingHom.coe_coe]; rw [coe_inclusion]; rw [coe_algebraMap]
  conv => enter [1, 2, 1, 2, 2]; rw [← num_div_denom (generator E)]
  rw [mul_div_cancel₀ _ (algebraMap_ne_zero (generator E).denom_ne_zero)]; rw [Polynomial.map_sub]; rw [Polynomial.map_mul]; rw [Polynomial.map_mul]; rw [map_C]; rw [map_C]; rw [Polynomial.map_map]; rw [Polynomial.map_map]
  rfl

/--
lemma `Q₀_mem_lifts` / 引理 `Q₀_mem_lifts`

English:
lemma Q₀_mem_lifts
  given: (h : E != ⊥)
  statement: Q₀ E in lifts (algebraMap K[X] K⟮X⟯)
  proof: by
  classical
  apply (Φ' E).isPrimitive_primPart.mul_map_mem_lifts_iff.mp
  rw [Q₀_mul_Φ h]
  exact ⟨_, rfl⟩

中文:
引理 Q₀_mem_lifts
  条件: (h : E != ⊥)
  结论: Q₀ E in lifts (algebraMap K[X] K⟮X⟯)
  证明: by
  classical
  apply (Φ' E).isPrimitive_primPart.mul_map_mem_lifts_iff.mp
  rw [Q₀_mul_Φ h]
  exact ⟨_, rfl⟩

Depends on / 依赖: classical, isPrimitive_primPart, isPrimitive_primPart.mul_map_mem_lifts_iff.mp, mul_map_mem_lifts_iff
-/
lemma Q₀_mem_lifts (h : E != ⊥) : Q₀ E in lifts (algebraMap K[X] K⟮X⟯) := by
  classical
  apply (Φ' E).isPrimitive_primPart.mul_map_mem_lifts_iff.mp
  rw [Q₀_mul_Φ h]
  exact ⟨_, rfl⟩

/--
Definition of `Q₁` / `Q₁` 的定义

English:
abbreviation Q₁
  signature: (h : E != ⊥)
  body: (Q₀_mem_lifts h).choose

中文:
缩写 Q₁
  签名: (h : E != ⊥)
  定义体: (Q₀_mem_lifts h).choose
-/
abbrev Q₁ (h : E != ⊥) : K[X][Y] := (Q₀_mem_lifts h).choose

/--
lemma `map_Q₁` / 引理 `map_Q₁`

English:
lemma map_Q₁
  given: (h : E != ⊥)
  statement: (Q₁ h).map (algebraMap K[X] K⟮X⟯) = Q₀ E
  proof: (Q₀_mem_lifts h).choose_spec

中文:
引理 map_Q₁
  条件: (h : E != ⊥)
  结论: (Q₁ h).map (algebraMap K[X] K⟮X⟯) = Q₀ E
  证明: (Q₀_mem_lifts h).choose_spec

Depends on / 依赖: choose_spec
-/
lemma map_Q₁ (h : E != ⊥) : (Q₁ h).map (algebraMap K[X] K⟮X⟯) = Q₀ E :=
  (Q₀_mem_lifts h).choose_spec

/--
lemma `Q₁_ne_zero` / 引理 `Q₁_ne_zero`

English:
lemma Q₁_ne_zero
  given: (h : E != ⊥)
  statement: Q₁ h != 0
  proof: by
  apply_fun Polynomial.map (algebraMap K[X] K⟮X⟯)
  rw [map_Q₁]; rw [Polynomial.map_zero]
  exact Q₀_ne_zero h

中文:
引理 Q₁_ne_zero
  条件: (h : E != ⊥)
  结论: Q₁ h != 0
  证明: by
  apply_fun Polynomial.map (algebraMap K[X] K⟮X⟯)
  rw [map_Q₁]; rw [Polynomial.map_zero]
  exact Q₀_ne_zero h

Depends on / 依赖: Polynomial, Polynomial.map, Polynomial.map_zero, algebraMap, apply_fun, map_zero
-/
lemma Q₁_ne_zero (h : E != ⊥) : Q₁ h != 0 := by
  apply_fun Polynomial.map (algebraMap K[X] K⟮X⟯)
  rw [map_Q₁]; rw [Polynomial.map_zero]
  exact Q₀_ne_zero h

/--
lemma `Q₁_mul_Φ` / 引理 `Q₁_mul_Φ`

English:
lemma Q₁_mul_Φ
  given: (h : E != ⊥)
  statement: Q₁ h * Φ E = θ E
  proof: by
  apply_fun Polynomial.map (algebraMap K[X] K⟮X⟯) using
    Polynomial.map_injective _ (algebraMap_injective K)
  rw [Polynomial.map_mul]; rw [map_Q₁]; rw [Q₀_mul_Φ h]

中文:
引理 Q₁_mul_Φ
  条件: (h : E != ⊥)
  结论: Q₁ h * Φ E = θ E
  证明: by
  apply_fun Polynomial.map (algebraMap K[X] K⟮X⟯) using
    Polynomial.map_injective _ (algebraMap_injective K)
  rw [Polynomial.map_mul]; rw [map_Q₁]; rw [Q₀_mul_Φ h]

Depends on / 依赖: Polynomial, Polynomial.map, Polynomial.map_injective, Polynomial.map_mul, algebraMap, algebraMap_injective, apply_fun, map_injective, map_mul
-/
lemma Q₁_mul_Φ (h : E != ⊥) : Q₁ h * Φ E = θ E := by
  apply_fun Polynomial.map (algebraMap K[X] K⟮X⟯) using
    Polynomial.map_injective _ (algebraMap_injective K)
  rw [Polynomial.map_mul]; rw [map_Q₁]; rw [Q₀_mul_Φ h]

/--
lemma `swap_Q₁_natDegree` / 引理 `swap_Q₁_natDegree`

English:
lemma swap_Q₁_natDegree
  given: (h : E != ⊥)
  statement: (Bivariate.swap (Q₁ h)).natDegree = 0
  proof: by
  have : Q₁ h * Φ E = θ E := Q₁_mul_Φ h
  apply_fun Bivariate.swap at this
  rw [map_mul] at this
  apply_fun natDegree at this
  rw [natDegree_mul
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Q₁_ne_zero h))
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h))] at this
  have h₁ : (Bivariate.swap (θ E)).natDegree <= m E := by
    rw [swap_θ]; rw [natDegree_neg]
    exact θ_natDegree_le h
  grind [m_le_swap_Φ_natDegree h]

中文:
引理 swap_Q₁_natDegree
  条件: (h : E != ⊥)
  结论: (Bivariate.swap (Q₁ h)).natDegree = 0
  证明: by
  have : Q₁ h * Φ E = θ E := Q₁_mul_Φ h
  apply_fun Bivariate.swap at this
  rw [map_mul] at this
  apply_fun natDegree at this
  rw [natDegree_mul
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Q₁_ne_zero h))
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h))] at this
  have h₁ : (Bivariate.swap (θ E)).natDegree <= m E := by
    rw [swap_θ]; rw [natDegree_neg]
    exact θ_natDegree_le h
  grind [m_le_swap_Φ_natDegree h]

Depends on / 依赖: Bivariate, Bivariate.swap, Bivariate.swap.injective, apply_fun, injective, map_mul, map_ne_zero_iff, natDegree, natDegree_mul, natDegree_neg
-/
lemma swap_Q₁_natDegree (h : E != ⊥) : (Bivariate.swap (Q₁ h)).natDegree = 0 := by
  have : Q₁ h * Φ E = θ E := Q₁_mul_Φ h
  apply_fun Bivariate.swap at this
  rw [map_mul] at this
  apply_fun natDegree at this
  rw [natDegree_mul
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Q₁_ne_zero h))
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h))] at this
  have h₁ : (Bivariate.swap (θ E)).natDegree <= m E := by
    rw [swap_θ]; rw [natDegree_neg]
    exact θ_natDegree_le h
  grind [m_le_swap_Φ_natDegree h]

/--
Definition of `Q₂` / `Q₂` 的定义

English:
abbreviation Q₂
  signature: (h : E != ⊥)
  body: (Bivariate.swap (Q₁ h)).coeff 0

中文:
缩写 Q₂
  签名: (h : E != ⊥)
  定义体: (Bivariate.swap (Q₁ h)).coeff 0

Depends on / 依赖: Bivariate, Bivariate.swap
-/
abbrev Q₂ (h : E != ⊥) : K[X] := (Bivariate.swap (Q₁ h)).coeff 0

/--
lemma `Q₂_map` / 引理 `Q₂_map`

English:
lemma Q₂_map
  given: (h : E != ⊥)
  statement: (Q₂ h).map Polynomial.C = Q₁ h
  proof: by
  have := eq_C_of_natDegree_eq_zero (swap_Q₁_natDegree h)
  apply_fun Bivariate.swap at this
  rw [Bivariate.swap_swap_apply]; rw [Bivariate.swap_C] at this
  exact this.symm

中文:
引理 Q₂_map
  条件: (h : E != ⊥)
  结论: (Q₂ h).map 多项式.C = Q₁ h
  证明: by
  have := eq_C_of_natDegree_eq_zero (swap_Q₁_natDegree h)
  apply_fun Bivariate.swap at this
  rw [Bivariate.swap_swap_apply]; rw [Bivariate.swap_C] at this
  exact this.symm

Depends on / 依赖: Bivariate, Bivariate.swap, Bivariate.swap_C, Bivariate.swap_swap_apply, apply_fun, eq_C_of_natDegree_eq_zero, swap_C, swap_swap_apply, this.symm
-/
lemma Q₂_map (h : E != ⊥) : (Q₂ h).map Polynomial.C = Q₁ h := by
  have := eq_C_of_natDegree_eq_zero (swap_Q₁_natDegree h)
  apply_fun Bivariate.swap at this
  rw [Bivariate.swap_swap_apply]; rw [Bivariate.swap_C] at this
  exact this.symm

/--
lemma `Q₂_ne_zero` / 引理 `Q₂_ne_zero`

English:
lemma Q₂_ne_zero
  given: (h : E != ⊥)
  statement: Q₂ h != 0
  proof: by
  apply_fun Polynomial.map Polynomial.C
  rw [Polynomial.map_zero]; rw [Q₂_map]
  exact Q₁_ne_zero h

中文:
引理 Q₂_ne_zero
  条件: (h : E != ⊥)
  结论: Q₂ h != 0
  证明: by
  apply_fun Polynomial.map Polynomial.C
  rw [Polynomial.map_zero]; rw [Q₂_map]
  exact Q₁_ne_zero h

Depends on / 依赖: Polynomial, Polynomial.C, Polynomial.map, Polynomial.map_zero, apply_fun, map_zero
-/
lemma Q₂_ne_zero (h : E != ⊥) : Q₂ h != 0 := by
  apply_fun Polynomial.map Polynomial.C
  rw [Polynomial.map_zero]; rw [Q₂_map]
  exact Q₁_ne_zero h

/--
lemma `Q₂_mul_Φ` / 引理 `Q₂_mul_Φ`

English:
lemma Q₂_mul_Φ
  given: (h : E != ⊥)
  statement: (Q₂ h).map Polynomial.C * Φ E = θ E
  proof: by
  rw [Q₂_map h]; rw [Q₁_mul_Φ h]

中文:
引理 Q₂_mul_Φ
  条件: (h : E != ⊥)
  结论: (Q₂ h).map 多项式.C * Φ E = θ E
  证明: by
  rw [Q₂_map h]; rw [Q₁_mul_Φ h]
-/
lemma Q₂_mul_Φ (h : E != ⊥) : (Q₂ h).map Polynomial.C * Φ E = θ E := by
  rw [Q₂_map h]; rw [Q₁_mul_Φ h]

attribute [local instance] Polynomial.algebra in
/--
lemma `Q₂_natDegree` / 引理 `Q₂_natDegree`

English:
lemma Q₂_natDegree
  given: (h : E != ⊥)
  statement: (Q₂ h).natDegree = 0
  proof: by
  -- We have f(X)*g(Y) - g(X)*f(Y) = Q₂(X) * Φ
  -- Assume Q₂ has positive degree, take a root in an algebraic extension
  by_contra H
  apply (generator E).eq_C_iff.not.mp (generator_ne_C h)
  let F := AlgebraicClosure K
  rw [natDegree_eq_zero_iff_degree_le_zero.not]; rw [← degree_map _ (algebraMap K F)] at H
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root ((Q₂ h).map (algebraMap K F)) (ne_of_not_ge H).symm
  -- Evaluate at the root, get that f(α)*g(Y) = g(α)*f(Y)
  rw [IsRoot.def]; rw [eval_map_algebraMap] at hα
  have eq :
      (Polynomial.mapRingHom (algebraMap K F)) (g E) * Polynomial.C ((aeval α) (f E)) =
      (Polynomial.mapRingHom (algebraMap K F)) (f E) * Polynomial.C ((aeval α) (g E)) := by
    have := congr(aeval (Polynomial.C α) $(Q₂_mul_Φ h)).symm
    rwa [aeval_mul, ← map_aeval_eq_aeval_map (by ext; simp), hα, map_zero, zero_mul, aeval_sub,
      aeval_mul, aeval_mul, aeval_C, aeval_C, ← map_aeval_eq_aeval_map (by ext; simp),
      ← map_aeval_eq_aeval_map (by ext; simp), algebraMap_def, coe_mapRingHom, sub_eq_zero,
      ← Polynomial.coe_mapRingHom] at this
  obtain ⟨isUnit₁, isUnit₂⟩ :
      IsUnit (Polynomial.C <| aeval α (f E)) ∧ IsUnit (Polynomial.C <| aeval α (g E)) := by
    rw [Polynomial.isUnit_C]; rw [isUnit_iff_ne_zero]; rw [Polynomial.isUnit_C]; rw [isUnit_iff_ne_zero]
    obtain (H | H) := aeval_ne_zero_of_isCoprime (generator E).isCoprime_num_denom α
    · refine ⟨H, Polynomial.C_injective.ne_iff.mp ?_⟩
      rw [map_zero]; rw [← mul_ne_zero_iff_left <| Polynomial.map_ne_zero <|
        num_ne_zero (generator_ne_zero h)]
exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (generator E).denom_ne_zero)
        Polynomial.C_ne_zero.mpr H
    · refine ⟨Polynomial.C_injective.ne_iff.mp ?_, H⟩
      rw [map_zero]; rw [← mul_ne_zero_iff_left <| Polynomial.map_ne_zero (generator E).denom_ne_zero]
exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h)))
        Polynomial.C_ne_zero.mpr H
  -- obtain contradiction because f and g are coprime
have isCoprime := IsCoprime.map (generator E).isCoprime_num_denom
    Polynomial.mapRingHom (algebraMap K F)
  have : Associated ((f E).mapRingHom (algebraMap K F)) ((g E).mapRingHom (algebraMap K F)) := by
    rw [← associated_mul_isUnit_left_iff isUnit₂]; rw [Associated.comm]
    exact ⟨isUnit₁.unit, by simpa⟩
  have := isCoprime.isUnit_of_associated this
  exact ⟨by simpa using (natDegree_eq_zero_of_isUnit this.1),
    by simpa using (natDegree_eq_zero_of_isUnit this.2)⟩

中文:
引理 Q₂_natDegree
  条件: (h : E != ⊥)
  结论: (Q₂ h).natDegree = 0
  证明: by
  -- We have f(X)*g(Y) - g(X)*f(Y) = Q₂(X) * Φ
  -- Assume Q₂ has positive degree, take a root in an algebraic extension
  by_contra H
  apply (generator E).eq_C_iff.not.mp (generator_ne_C h)
  let F := AlgebraicClosure K
  rw [natDegree_eq_zero_iff_degree_le_zero.not]; rw [← degree_map _ (algebraMap K F)] at H
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root ((Q₂ h).map (algebraMap K F)) (ne_of_not_ge H).symm
  -- Evaluate at the root, get that f(α)*g(Y) = g(α)*f(Y)
  rw [IsRoot.def]; rw [eval_map_algebraMap] at hα
  have eq :
      (Polynomial.mapRingHom (algebraMap K F)) (g E) * Polynomial.C ((aeval α) (f E)) =
      (Polynomial.mapRingHom (algebraMap K F)) (f E) * Polynomial.C ((aeval α) (g E)) := by
    have := congr(aeval (Polynomial.C α) $(Q₂_mul_Φ h)).symm
    rwa [aeval_mul, ← map_aeval_eq_aeval_map (by ext; simp), hα, map_zero, zero_mul, aeval_sub,
      aeval_mul, aeval_mul, aeval_C, aeval_C, ← map_aeval_eq_aeval_map (by ext; simp),
      ← map_aeval_eq_aeval_map (by ext; simp), algebraMap_def, coe_mapRingHom, sub_eq_zero,
      ← Polynomial.coe_mapRingHom] at this
  obtain ⟨isUnit₁, isUnit₂⟩ :
      IsUnit (Polynomial.C <| aeval α (f E)) ∧ IsUnit (Polynomial.C <| aeval α (g E)) := by
    rw [Polynomial.isUnit_C]; rw [isUnit_iff_ne_zero]; rw [Polynomial.isUnit_C]; rw [isUnit_iff_ne_zero]
    obtain (H | H) := aeval_ne_zero_of_isCoprime (generator E).isCoprime_num_denom α
    · refine ⟨H, Polynomial.C_injective.ne_iff.mp ?_⟩
      rw [map_zero]; rw [← mul_ne_zero_iff_left <| Polynomial.map_ne_zero <|
        num_ne_zero (generator_ne_zero h)]
exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (generator E).denom_ne_zero)
        Polynomial.C_ne_zero.mpr H
    · refine ⟨Polynomial.C_injective.ne_iff.mp ?_, H⟩
      rw [map_zero]; rw [← mul_ne_zero_iff_left <| Polynomial.map_ne_zero (generator E).denom_ne_zero]
exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h)))
        Polynomial.C_ne_zero.mpr H
  -- obtain contradiction because f and g are coprime
have isCoprime := IsCoprime.map (generator E).isCoprime_num_denom
    Polynomial.mapRingHom (algebraMap K F)
  have : Associated ((f E).mapRingHom (algebraMap K F)) ((g E).mapRingHom (algebraMap K F)) := by
    rw [← associated_mul_isUnit_left_iff isUnit₂]; rw [Associated.comm]
    exact ⟨isUnit₁.unit, by simpa⟩
  have := isCoprime.isUnit_of_associated this
  exact ⟨by simpa using (natDegree_eq_zero_of_isUnit this.1),
    by simpa using (natDegree_eq_zero_of_isUnit this.2)⟩
-/
lemma Q₂_natDegree (h : E != ⊥) : (Q₂ h).natDegree = 0 := by
  -- We have f(X)*g(Y) - g(X)*f(Y) = Q₂(X) * Φ
  -- Assume Q₂ has positive degree, take a root in an algebraic extension
  by_contra H
  apply (generator E).eq_C_iff.not.mp (generator_ne_C h)
  let F := AlgebraicClosure K
  rw [natDegree_eq_zero_iff_degree_le_zero.not]; rw [← degree_map _ (algebraMap K F)] at H
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root ((Q₂ h).map (algebraMap K F)) (ne_of_not_ge H).symm
  -- Evaluate at the root, get that f(α)*g(Y) = g(α)*f(Y)
  rw [IsRoot.def]; rw [eval_map_algebraMap] at hα
  have eq :
      (Polynomial.mapRingHom (algebraMap K F)) (g E) * Polynomial.C ((aeval α) (f E)) =
      (Polynomial.mapRingHom (algebraMap K F)) (f E) * Polynomial.C ((aeval α) (g E)) := by
    have := congr(aeval (Polynomial.C α) $(Q₂_mul_Φ h)).symm
    rwa [aeval_mul, ← map_aeval_eq_aeval_map (by ext; simp), hα, map_zero, zero_mul, aeval_sub,
      aeval_mul, aeval_mul, aeval_C, aeval_C, ← map_aeval_eq_aeval_map (by ext; simp),
      ← map_aeval_eq_aeval_map (by ext; simp), algebraMap_def, coe_mapRingHom, sub_eq_zero,
      ← Polynomial.coe_mapRingHom] at this
  obtain ⟨isUnit₁, isUnit₂⟩ :
      IsUnit (Polynomial.C <| aeval α (f E)) ∧ IsUnit (Polynomial.C <| aeval α (g E)) := by
    rw [Polynomial.isUnit_C]; rw [isUnit_iff_ne_zero]; rw [Polynomial.isUnit_C]; rw [isUnit_iff_ne_zero]
    obtain (H | H) := aeval_ne_zero_of_isCoprime (generator E).isCoprime_num_denom α
    · refine ⟨H, Polynomial.C_injective.ne_iff.mp ?_⟩
      rw [map_zero]; rw [← mul_ne_zero_iff_left <| Polynomial.map_ne_zero <|
        num_ne_zero (generator_ne_zero h)]
exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (generator E).denom_ne_zero)
        Polynomial.C_ne_zero.mpr H
    · refine ⟨Polynomial.C_injective.ne_iff.mp ?_, H⟩
      rw [map_zero]; rw [← mul_ne_zero_iff_left <| Polynomial.map_ne_zero (generator E).denom_ne_zero]
exact eq ▸ mul_ne_zero (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero h)))
        Polynomial.C_ne_zero.mpr H
  -- obtain contradiction because f and g are coprime
have isCoprime := IsCoprime.map (generator E).isCoprime_num_denom
    Polynomial.mapRingHom (algebraMap K F)
  have : Associated ((f E).mapRingHom (algebraMap K F)) ((g E).mapRingHom (algebraMap K F)) := by
    rw [← associated_mul_isUnit_left_iff isUnit₂]; rw [Associated.comm]
    exact ⟨isUnit₁.unit, by simpa⟩
  have := isCoprime.isUnit_of_associated this
  exact ⟨by simpa using (natDegree_eq_zero_of_isUnit this.1),
    by simpa using (natDegree_eq_zero_of_isUnit this.2)⟩

/--
Definition of `Q₃` / `Q₃` 的定义

English:
abbreviation Q₃
  signature: (h : E != ⊥)
  body: (Q₂ h).coeff 0

中文:
缩写 Q₃
  签名: (h : E != ⊥)
  定义体: (Q₂ h).coeff 0
-/
abbrev Q₃ (h : E != ⊥) : K := (Q₂ h).coeff 0

/--
lemma `Q₃_map` / 引理 `Q₃_map`

English:
lemma Q₃_map
  given: (h : E != ⊥)
  statement: Polynomial.C (Q₃ h) = Q₂ h
  proof: (eq_C_of_natDegree_eq_zero (Q₂_natDegree h)).symm

中文:
引理 Q₃_map
  条件: (h : E != ⊥)
  结论: 多项式.C (Q₃ h) = Q₂ h
  证明: (eq_C_of_natDegree_eq_zero (Q₂_natDegree h)).symm

Depends on / 依赖: eq_C_of_natDegree_eq_zero
-/
lemma Q₃_map (h : E != ⊥) : Polynomial.C (Q₃ h) = Q₂ h :=
  (eq_C_of_natDegree_eq_zero (Q₂_natDegree h)).symm

/--
lemma `Q₃_mul_Φ` / 引理 `Q₃_mul_Φ`

English:
lemma Q₃_mul_Φ
  given: (h : E != ⊥)
  statement: (Polynomial.C (Q₃ h)).map Polynomial.C * Φ E = θ E
  proof: by
  rw [Q₃_map h]; rw [Q₂_mul_Φ h]

中文:
引理 Q₃_mul_Φ
  条件: (h : E != ⊥)
  结论: (多项式.C (Q₃ h)).map 多项式.C * Φ E = θ E
  证明: by
  rw [Q₃_map h]; rw [Q₂_mul_Φ h]
-/
lemma Q₃_mul_Φ (h : E != ⊥) : (Polynomial.C (Q₃ h)).map Polynomial.C * Φ E = θ E := by
  rw [Q₃_map h]; rw [Q₂_mul_Φ h]

/--
lemma `Φ_natDegree_eq_θ_natDegree` / 引理 `Φ_natDegree_eq_θ_natDegree`

English:
lemma Φ_natDegree_eq_θ_natDegree
  given: (h : E != ⊥)
  proof: by
  have := congr($(Q₂_mul_Φ h).natDegree)
  rwa [natDegree_mul (Polynomial.map_ne_zero (Q₂_ne_zero h)) (Φ_ne_zero h), natDegree_map,
    Q₂_natDegree h, zero_add] at this

中文:
引理 Φ_natDegree_eq_θ_natDegree
  条件: (h : E != ⊥)
  证明: by
  have := congr($(Q₂_mul_Φ h).natDegree)
  rwa [natDegree_mul (Polynomial.map_ne_zero (Q₂_ne_zero h)) (Φ_ne_zero h), natDegree_map,
    Q₂_natDegree h, zero_add] at this

Depends on / 依赖: Polynomial, Polynomial.map_ne_zero, map_ne_zero, natDegree, natDegree_map, natDegree_mul, zero_add
-/
lemma Φ_natDegree_eq_θ_natDegree (h : E != ⊥) :
    (Φ E).natDegree = (θ E).natDegree := by
  have := congr($(Q₂_mul_Φ h).natDegree)
  rwa [natDegree_mul (Polynomial.map_ne_zero (Q₂_ne_zero h)) (Φ_ne_zero h), natDegree_map,
    Q₂_natDegree h, zero_add] at this

/--
lemma `swap_Φ_natDegree_eq_θ_natDegree` / 引理 `swap_Φ_natDegree_eq_θ_natDegree`

English:
lemma swap_Φ_natDegree_eq_θ_natDegree
  given: (h : E != ⊥)
  proof: by
  have := congr((Bivariate.swap $(Q₃_mul_Φ h)).natDegree)
  rwa [map_mul, Polynomial.map_C, Bivariate.swap_C_C,
    natDegree_mul (C_ne_zero.mpr (Q₃_map h ▸ Q₂_ne_zero h))
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h)),
    natDegree_C, zero_add, swap_θ, natDegree_neg] at this

中文:
引理 swap_Φ_natDegree_eq_θ_natDegree
  条件: (h : E != ⊥)
  证明: by
  have := congr((Bivariate.swap $(Q₃_mul_Φ h)).natDegree)
  rwa [map_mul, Polynomial.map_C, Bivariate.swap_C_C,
    natDegree_mul (C_ne_zero.mpr (Q₃_map h ▸ Q₂_ne_zero h))
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h)),
    natDegree_C, zero_add, swap_θ, natDegree_neg] at this

Depends on / 依赖: Bivariate, Bivariate.swap, Bivariate.swap.injective, Bivariate.swap_C_C, C_ne_zero, C_ne_zero.mpr, Polynomial, Polynomial.map_C, injective, map_C, map_mul, map_ne_zero_iff, natDegree, natDegree_C, natDegree_mul, natDegree_neg, swap_C_C, zero_add
-/
lemma swap_Φ_natDegree_eq_θ_natDegree (h : E != ⊥) :
    (Bivariate.swap (Φ E)).natDegree = (θ E).natDegree := by
  have := congr((Bivariate.swap $(Q₃_mul_Φ h)).natDegree)
  rwa [map_mul, Polynomial.map_C, Bivariate.swap_C_C,
    natDegree_mul (C_ne_zero.mpr (Q₃_map h ▸ Q₂_ne_zero h))
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr (Φ_ne_zero h)),
    natDegree_C, zero_add, swap_θ, natDegree_neg] at this

/-- Lüroth's theorem. Any intermediate field between `K` and `K⟮X⟯` is
generated by a single element `generator E`. See also `transcendental_generator`
for the statement that the generator is transcendental if `E ≠ ⊥`. -/
public theorem eq_adjoin_generator : E = K⟮generator E⟯ := by
  by_cases h : E = ⊥
  · rwa [generator_eq_zero h, adjoin_zero]
  refine le_antisymm (relfinrank_eq_one_iff.mp ?_) adjoin_generator_le
  suffices (φ E).natDegree = m E by
refine (mul_eq_right₀ ?_).mp this ▸ (generator E).finrank_eq_max_natDegree ▸
      φ_natDegree h ▸ relfinrank_mul_finrank_top (adjoin_generator_le (E := E))
    intro H
    exact generator_ne_C h ((eq_C_iff _).mpr (Nat.max_eq_zero_iff.mp H))
  rw [← Φ_natDegree_eq_φ_natDegree h]; rw [Φ_natDegree_eq_θ_natDegree h]
  exact le_antisymm (θ_natDegree_le h) (swap_Φ_natDegree_eq_θ_natDegree h ▸ m_le_swap_Φ_natDegree h)

/-- The `K`-algebra equivalence between `K⟮X⟯` and an intermediate field `E` given
by sending `X` to `generator E`. See also `Luroth.eq_adjoin_generator`. -/
public def algEquiv (h : E != ⊥) : K⟮X⟯ ≃ₐ[K] E :=
(algEquivOfTranscendental (generator E) (transcendental_of_ne_C _ (generator_ne_C h))).trans
    IntermediateField.equivOfEq eq_adjoin_generator.symm

@[simp]
public lemma algEquiv_algebraMap (h : E != ⊥) (g : K[X]) :
    algEquiv h (algebraMap K[X] K⟮X⟯ g) = aeval (generator E) g := by
  simp [algEquiv]

@[simp]
public lemma algEquiv_X (h : E != ⊥) : algEquiv h (X : K⟮X⟯) = generator E := by
  simp [algEquiv]

public lemma algEquiv_apply (h : E != ⊥) (u : K⟮X⟯) :
    algEquiv h u = aeval (generator E) u.num / aeval (generator E) u.denom := by
  simp [algEquiv, algEquivOfTranscendental_apply]

end

end RatFunc.Luroth
