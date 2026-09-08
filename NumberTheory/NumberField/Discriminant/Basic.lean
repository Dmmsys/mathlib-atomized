/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.EquivReindex
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Number field discriminant

This file defines the discriminant of a number field.

## Main result

* `NumberField.abs_discr_gt_two`: **Hermite-Minkowski Theorem**. A nontrivial number field has
  discriminant greater than `2`.

* `NumberField.finite_of_discr_bdd`: **Hermite Theorem**. Let `N` be an integer. There are only
  finitely many number fields (in some fixed extension of `ℚ`) of discriminant bounded by `N`.

## Tags
number field, discriminant
-/

public section

-- TODO. Rewrite some of the FLT results on the discriminant using the definitions and results of
-- this file

namespace NumberField

open Module NumberField NumberField.InfinitePlace Matrix

open scoped Real nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

open MeasureTheory MeasureTheory.Measure ZSpan NumberField.mixedEmbedding
  NumberField.InfinitePlace ENNReal NNReal Complex

/-
**NumberField.discr_eq_basisMatrix_det_sq** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
`。
形式化陈述：discr_eq_basisMatrix_det_sq [DecidableEq (K ->+* Complex)] : discr K = (ba
sisMatrix K).det ^ 2
参数：K ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.coe_discr`：coe_discr : (discr K : Rat) = Algebra.discr Rat (
integralBasis K)
· 使用定理 `NumberField.basisMatrix_eq_embeddingsMatrixReindex`：basisMatrix_eq_embed
dingsMatrixReindex : basisMatrix K = Algebra.embeddingsMatrixReindex Rat Complex
 (integralBasis K ∘ (equivReindex K)) (R…
· 使用定理 `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two`：discr_eq_det_embed
dingsMatrixReindex_pow_two [Algebra.IsSeparable K L] (e : ι ≃ (L ->ₐ[K] E)) : al
gebraMap K E (discr K b) = (embeddingsMatr…
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
· 使用定理 `Algebra.discr_reindex`：discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : di
scr A (b ∘ ⇑f.symm) = discr A b
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
-/
theorem discr_eq_basisMatrix_det_sq [DecidableEq (K →+* ℂ)] :
    discr K = (basisMatrix K).det ^ 2 := by
  rw [← Rat.cast_intCast, coe_discr, basisMatrix_eq_embeddingsMatrixReindex,
    ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, ← (equivReindex K).symm_symm,
    Algebra.discr_reindex, eq_ratCast]

set_option backward.isDefEq.respectTransparency false in
open scoped ComplexConjugate ComplexOrder in
/-
**NumberField.sign_discr** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：sign_discr : (discr K).sign = (-1) ^ nrComplexPlaces K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.discr_eq_basisMatrix_det_sq`：discr_eq_basisMatrix_det_sq [De
cidableEq (K ->+* Complex)] : discr K = (basisMatrix K).det ^ 2
· 使用定理 `Complex.sq_nonneg_iff`：sq_nonneg_iff {z : Complex} : 0 <= z ^ 2 ↔ z.im =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.conj_eq_iff_im`：conj_eq_iff_im {z : Complex} : conj z = z ↔ z.im
 = 0
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `NumberField.ComplexEmbedding.involutive_conjugate`：involutive_conjugate 
: Function.Involutive (conjugate : (K ->+* Complex) -> (K ->+* Complex))
· 使用定理 `NumberField.conj_basisMatrix`：conj_basisMatrix : (basisMatrix K).map con
j = (basisMatrix K).reindex (Equiv.refl _) (ComplexEmbedding.involutive_conjugat
e K).toPerm
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.reindex_apply`：reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matri
x m n α) : reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm
· 使用定理 `Equiv.refl_symm`：∀ {α : Sort u}, (Equiv.refl α).symm = Equiv.refl α
· 使用定理 `Equiv.coe_refl`：∀ {α : Sort u}, ⇑(Equiv.refl α) = id
· 使用定理 `Function.Involutive.toPerm_symm`：toPerm_symm {f : α -> α} (h : Involutiv
e f) : (h.toPerm f).symm = h.toPerm f
· 使用定理 `Matrix.det_permute'`：det_permute' (σ : Perm n) (M : Matrix n n R) : (M.s
ubmatrix id σ).det = Perm.sign σ * M.det
· 使用定理 `mul_eq_right₀`：mul_eq_right₀ [IsRightCancelMulZero M₀] (hb : b != 0) : a
 * b = b ↔ a = 1
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NumberField.det_of_basisMatrix_non_zero`：det_of_basisMatrix_non_zero [De
cidableEq (K ->+* Complex)] : (basisMatrix K).det != 0
· 使用定理 `NumberField.InfinitePlace.ComplexEmbedding.conjugate_sign`：∀ (K : Type u
_1) [inst : Field K] [inst_1 : NumberField K],   Equiv.Perm.sign (Function.Invol
utive.toPerm NumberField.ComplexEmbedding.conju…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `neg_one_pow_eq_one_iff_even`：neg_one_pow_eq_one_iff_even (h : (-1 : R) !
= 1) : (-1 : R) ^ n = 1 ↔ Even n
· 使用定理 `Mathlib.Meta.NormNum.isInt_eq_false`：∀ {α : Type u_1} [inst : Ring α] [C
harZero α] {a b : α} {a' b' : ℤ},   Mathlib.Meta.NormNum.IsInt a a' → Mathlib.Me
ta.NormNum.IsInt b b' → d…
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 48 条，此处仅展示前 30 条）
-/
theorem sign_discr :
    (discr K).sign = (-1) ^ nrComplexPlaces K := by
  classical
  have : 0 ≤ (discr K : ℂ) ↔ Even (nrComplexPlaces K) := by
    rw [discr_eq_basisMatrix_det_sq, Complex.sq_nonneg_iff, ← conj_eq_iff_im, RingHom.map_det,
      RingHom.mapMatrix_apply, conj_basisMatrix, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
      Function.Involutive.toPerm_symm, det_permute', mul_eq_right₀,
      ComplexEmbedding.conjugate_sign]
    · simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.reduceNeg,
        Int.cast_pow, Int.cast_neg, Int.cast_one]
      rw [neg_one_pow_eq_one_iff_even (by norm_num)]
    · exact det_of_basisMatrix_non_zero K
  obtain h | h | h := Int.lt_trichotomy 0 (discr K)
  · rw [Int.sign_eq_one_of_pos h, Even.neg_one_pow (this.mp <| Int.cast_nonneg h.le)]
  · grind [discr_ne_zero]
  · rw [Int.sign_eq_neg_one_of_neg h, Odd.neg_one_pow]
    rwa [← Nat.not_even_iff_odd, ← this, Int.cast_nonneg_iff, not_le]

section rootDiscr

/-- The root discriminant of a number field `K`. -/
/-
**NumberField.rootDiscr** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：rootDiscr : Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K

--- 原说明 ---
The root discriminant of a number field `K`.
-/
noncomputable def rootDiscr : ℝ :=
  |discr K| ^ (finrank ℚ K : ℝ)⁻¹
/-
**NumberField.rootDiscr_def** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：rootDiscr_def : rootDiscr K = |discr K| ^ (finrank Rat K : Real)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.Discriminant.Basic.0.NumberFie
ld.rootDiscr.eq_1`：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],  
 NumberField.rootDiscr K = ↑|NumberField.discr K| ^ (↑(Module.finrank ℚ K))⁻¹
-/
theorem rootDiscr_def : rootDiscr K = |discr K| ^ (finrank ℚ K : ℝ)⁻¹ := by
  rw [rootDiscr]
/-
**NumberField.rootDiscr_rat** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：rootDiscr_rat : rootDiscr Rat = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.rootDiscr_def`：rootDiscr_def : rootDiscr K = |discr K| ^ (fi
nrank Rat K : Real)⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.numberField_discr`：numberField_discr : discr Rat = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rootDiscr_rat : rootDiscr ℚ = 1 := by
  simp [rootDiscr_def]

end rootDiscr

open scoped Classical in
/-
**NumberField._root_.NumberField.mixedEmbedding.volume_fundamentalDomain_lattice
Basis** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis :
    volume (fundamentalDomain (latticeBasis K)) =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * sqrt ‖discr K‖₊ := by
  let f : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ) :=
    (canonicalEmbedding.latticeBasis K).indexEquiv (Pi.basisFun ℂ _)
  let e : (index K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K) := (indexEquiv K).trans f.symm
  let M := (mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)
  let N := Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K ∘ f.symm)
    (RingHom.equivRatAlgHom K ℂ)
  suffices M.map ofRealHom = matrixToStdBasis K *
      (Matrix.reindex (indexEquiv K).symm (indexEquiv K).symm N).transpose by
    calc volume (fundamentalDomain (latticeBasis K))
      _ = ‖((mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)).det‖₊ := by
        rw [← fundamentalDomain_reindex _ e.symm, ← norm_toNNReal, measure_fundamentalDomain
          ((latticeBasis K).reindex e.symm), volume_fundamentalDomain_stdBasis, mul_one]
        rfl
      _ = ‖(matrixToStdBasis K).det * N.det‖₊ := by
        rw [← nnnorm_real, ← ofRealHom_eq_coe, RingHom.map_det, RingHom.mapMatrix_apply, this,
          det_mul, det_transpose, det_reindex_self]
      _ = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card {w : InfinitePlace K // IsComplex w} * sqrt ‖N.det ^ 2‖₊ := by
        have : ‖Complex.I‖₊ = 1 := by rw [← norm_toNNReal, norm_I, Real.toNNReal_one]
        rw [det_matrixToStdBasis, nnnorm_mul, nnnorm_pow, nnnorm_mul, this, mul_one, nnnorm_inv,
          coe_mul, ENNReal.coe_pow, ← norm_toNNReal, RCLike.norm_two, Real.toNNReal_ofNat,
          coe_inv two_ne_zero, coe_ofNat, nnnorm_pow, NNReal.sqrt_sq]
      _ = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card { w // IsComplex w } * NNReal.sqrt ‖discr K‖₊ := by
        rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, Algebra.discr_reindex,
          ← coe_discr, map_intCast, ← Complex.nnnorm_intCast]
  ext : 2
  dsimp only [M]
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.coe_reindex, Function.comp_apply,
    Equiv.symm_symm, latticeBasis_apply, ← commMap_canonical_eq_mixed, Complex.ofRealHom_eq_coe,
    stdBasis_repr_eq_matrixToStdBasis_mul K _ (fun _ => rfl)]
  rfl

open scoped Classical in
/-
**NumberField._root_.NumberField.mixedEmbedding.covolume_integerLattice** 是 Math
lib 中的一个定理，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NumberField.mixedEmbedding.covolume_integerLattice :
    ZLattice.covolume (mixedEmbedding.integerLattice K) =
      (2⁻¹) ^ nrComplexPlaces K * √|discr K| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_integerLattice K),
    measureReal_def,
    volume_fundamentalDomain_latticeBasis, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_inv, toReal_ofNat, ENNReal.coe_toReal, Real.coe_sqrt, coe_nnnorm,
    Int.norm_eq_abs]

open scoped Classical in
/-
**NumberField._root_.NumberField.mixedEmbedding.covolume_idealLattice** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NumberField.mixedEmbedding.covolume_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (mixedEmbedding.idealLattice K I) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)) *
        (2⁻¹) ^ nrComplexPlaces K * √|discr K| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I),
    measureReal_def,
    volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_latticeBasis,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, toReal_ofNat,
    ENNReal.coe_toReal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs,
    ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.val)), mul_assoc]
/-
**NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField`。
形式化陈述：exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr (I : (FractionalIdeal (
𝓞 K)⁰ K)ˣ) : exists a in (I : FractionalIdeal (𝓞 K)⁰ K), a != 0 ∧ |Algebra.norm 
Rat (a : K)| <= FractionalIdeal.absNorm I.1 * (4 / π) ^ nrComplexPlaces K * (fin
rank Rat K).factorial / (finrank Rat K) ^ (finrank Rat K) * Real.sqrt |discr K|
参数：I : (FractionalIdeal (𝓞 K)⁰ K)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.convexBodySum_volume`：convexBodySum_volume : 
volume (convexBodySum K B) = (convexBodySumFactor K) * (.ofReal B) ^ (finrank Ra
t K)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_pow`：ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) : ENNR
eal.ofReal (p ^ n) = ENNReal.ofReal p ^ n
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `NumberField.mixedEmbedding.minkowskiBound_lt_top`：minkowskiBound_lt_top 
: minkowskiBound K I < ⊤
（共 137 条，此处仅展示前 30 条）
-/
theorem exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧
      |Algebra.norm ℚ (a : K)| ≤ FractionalIdeal.absNorm I.1 * (4 / π) ^ nrComplexPlaces K *
        (finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K| := by
  classical
  -- The smallest possible value for `exists_ne_zero_mem_ideal_of_norm_le`
  let B := (minkowskiBound K I * (convexBodySumFactor K)⁻¹).toReal ^ (1 / (finrank ℚ K : ℝ))
  have h_le : (minkowskiBound K I) ≤ volume (convexBodySum K B) := by
    refine le_of_eq ?_
    rw [convexBodySum_volume, ← ENNReal.ofReal_pow (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul toReal_nonneg, div_mul_cancel₀, Real.rpow_one, ofReal_toReal, mul_comm,
      mul_assoc, ← coe_mul, inv_mul_cancel₀ (convexBodySumFactor_ne_zero K), ENNReal.coe_one,
      mul_one]
    · exact mul_ne_top (ne_of_lt (minkowskiBound_lt_top K I)) coe_ne_top
    · exact (Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos))
  convert! exists_ne_zero_mem_ideal_of_norm_le K I h_le
  rw [div_pow B, ← Real.rpow_natCast B, ← Real.rpow_mul (by positivity), div_mul_cancel₀ _
    (Nat.cast_ne_zero.mpr <| ne_of_gt finrank_pos), Real.rpow_one, mul_comm_div, mul_div_assoc']
  congr 1
  rw [eq_comm]
  calc
    _ = FractionalIdeal.absNorm I.1 * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * sqrt ‖discr K‖₊ *
          (2 : ℝ) ^ finrank ℚ K * ((2 : ℝ) ^ nrRealPlaces K * (π / 2) ^ nrComplexPlaces K /
            (Nat.factorial (finrank ℚ K)))⁻¹ := by
      simp_rw [minkowskiBound, convexBodySumFactor,
        volume_fundamentalDomain_fractionalIdealLatticeBasis,
        volume_fundamentalDomain_latticeBasis, toReal_mul, toReal_pow, toReal_inv, coe_toReal,
        toReal_ofNat, mixedEmbedding.finrank, mul_assoc]
      rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1))]
      simp_rw [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
        coe_real_pi, NNReal.coe_ofNat, NNReal.coe_natCast]
    _ = FractionalIdeal.absNorm I.1 * (2 : ℝ) ^ (finrank ℚ K - nrComplexPlaces K - nrRealPlaces K +
          nrComplexPlaces K : ℤ) * Real.sqrt ‖discr K‖ * Nat.factorial (finrank ℚ K) *
            π⁻¹ ^ (nrComplexPlaces K) := by
      simp_rw [inv_div, div_eq_mul_inv, mul_inv, ← zpow_neg_one, ← zpow_natCast, mul_zpow,
        ← zpow_mul, neg_one_mul, mul_neg_one, neg_neg, Real.coe_sqrt, coe_nnnorm, sub_eq_add_neg,
        zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
      ring
    _ = FractionalIdeal.absNorm I.1 * (2 : ℝ) ^ (2 * nrComplexPlaces K : ℤ) * Real.sqrt ‖discr K‖ *
          Nat.factorial (finrank ℚ K) * π⁻¹ ^ (nrComplexPlaces K) := by
      congr
      rw [← card_add_two_mul_card_eq_rank, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ = FractionalIdeal.absNorm I.1 * (4 / π) ^ nrComplexPlaces K * (finrank ℚ K).factorial *
          Real.sqrt |discr K| := by
      rw [Int.norm_eq_abs, zpow_mul, show (2 : ℝ) ^ (2 : ℤ) = 4 by norm_cast, div_pow,
        inv_eq_one_div, div_pow, one_pow, zpow_natCast]
      ring
/-
**NumberField.exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr** 是 Ma
thlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr : exists (a : 
𝓞 K), a != 0 ∧ |Algebra.norm Rat (a : K)| <= (4 / π) ^ nrComplexPlaces K * (finr
ank Rat K).factorial / (finrank Rat K) ^ (finrank Rat K) * Real.sqrt |discr K|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr`：exists_n
e_zero_mem_ideal_of_norm_le_mul_sqrt_discr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : e
xists a in (I : FractionalIdeal (𝓞 K)⁰ K), a != 0 ∧ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
· 使用定理 `ne_zero_of_map`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst 
: Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] {f :
 F} …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `FractionalIdeal.absNorm_one`：absNorm_one : absNorm (1 : FractionalIdeal 
R⁰ K) = 1
-/
theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr :
    ∃ (a : 𝓞 K), a ≠ 0 ∧
      |Algebra.norm ℚ (a : K)| ≤ (4 / π) ^ nrComplexPlaces K *
        (finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K| := by
  obtain ⟨_, h_mem, h_nz, h_nm⟩ := exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K ↑1
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  refine ⟨a, ne_zero_of_map h_nz, ?_⟩
  simp_rw [Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one, one_mul] at h_nm
  exact h_nm

/--
The Minkowski lower bound `n^{2n}/((4/pi)^{2r_2}*n!^2)` for the absolute value of the discriminant
of a number field of degree n.
-/
/-
**NumberField.abs_discr_ge'** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：abs_discr_ge' : (finrank Rat K) ^ (2 * finrank Rat K) / ((4 / π) ^ (2 * nr
ComplexPlaces K) * (finrank Rat K).factorial ^ 2) <= |discr K|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr`
：exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr : exists (a : 𝓞 K),
 a != 0 ∧ |Algebra.norm Rat (a : K)| <= (4 / π) ^ nrComplexPl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.coe_norm_int`：Algebra.coe_norm_int : (Algebra.norm Int x : Rat) 
= Algebra.norm Rat (x : K)
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.one_le_abs`：one_le_abs {z : Int} (h₀ : z != 0) : 1 <= |z|
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.norm_ne_zero_iff`：norm_ne_zero_iff [IsDomain R] [IsDomain S] [Mo
dule.Free R S] [Module.Finite R S] {x : S} : norm R x != 0 ↔ x != 0
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `Real.le_sqrt`：le_sqrt (hx : 0 <= x) (hy : 0 <= y) : x <= √y ↔ x ^ 2 <= y
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
The Minkowski lower bound `n^{2n}/((4/pi)^{2r_2}*n!^2)` for the absolute value o
f the discriminant
of a number field of degree n.
-/
theorem abs_discr_ge' :
    (finrank ℚ K) ^ (2 * finrank ℚ K) / ((4 / π) ^ (2 * nrComplexPlaces K) *
      (finrank ℚ K).factorial ^ 2) ≤ |discr K| := by
  -- We use `exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr` to get a nonzero
  -- algebraic integer `x` of small norm and the fact that `1 ≤ |Norm x|` to get a lower bound
  -- on `sqrt |discr K|`.
  obtain ⟨x, h_nz, h_bd⟩ := exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr K
  have h_nm : (1 : ℝ) ≤ |Algebra.norm ℚ (x : K)| := by
    rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_intCast, Int.cast_le]
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr h_nz)
  replace h_bd := le_trans h_nm h_bd
  rwa [← inv_mul_le_iff₀, inv_div, mul_one, Real.le_sqrt (by positivity) (by positivity),
    ← Int.cast_abs, div_pow, mul_pow, ← pow_mul, mul_comm _ 2, ← pow_mul, mul_comm _ 2] at h_bd
  exact div_pos (by positivity) <| pow_pos (Nat.cast_pos.mpr finrank_pos) (finrank ℚ K)
/-
**NumberField.abs_discr_ge_of_isTotallyComplex** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field`。
形式化陈述：abs_discr_ge_of_isTotallyComplex [IsTotallyComplex K] : (finrank Rat K) ^ 
(2 * finrank Rat K) / ((4 / π) ^ (finrank Rat K) * (finrank Rat K).factorial ^ 2
) <= |discr K|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.abs_discr_ge'`：abs_discr_ge' : (finrank Rat K) ^ (2 * finran
k Rat K) / ((4 / π) ^ (2 * nrComplexPlaces K) * (finrank Rat K).factorial ^ 2) <
= |discr K|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.IsTotallyComplex.finrank`：∀ (K : Type u_2) [inst : Field K] 
[inst_1 : NumberField K] [h : NumberField.IsTotallyComplex K],   Module.finrank 
ℚ K = 2 * NumberField.Infi…
-/
theorem abs_discr_ge_of_isTotallyComplex [IsTotallyComplex K] :
    (finrank ℚ K) ^ (2 * finrank ℚ K) / ((4 / π) ^ (finrank ℚ K) *
      (finrank ℚ K).factorial ^ 2) ≤ |discr K| := by
  have := abs_discr_ge' K
  rwa [← IsTotallyComplex.finrank] at this
/-
**NumberField.abs_discr_rpow_ge_of_isTotallyComplex** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField`。
形式化陈述：abs_discr_rpow_ge_of_isTotallyComplex [IsTotallyComplex K] : (finrank Rat 
K) ^ 2 / ((4 / π) * (finrank Rat K).factorial ^ (2 * (finrank Rat K : Real)⁻¹)) 
<= |discr K| ^ (finrank Rat K : Real)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 49 条，此处仅展示前 30 条）
-/
theorem abs_discr_rpow_ge_of_isTotallyComplex [IsTotallyComplex K] :
    (finrank ℚ K) ^ 2 / ((4 / π) * (finrank ℚ K).factorial ^ (2 * (finrank ℚ K : ℝ)⁻¹)) ≤
        |discr K| ^ (finrank ℚ K : ℝ)⁻¹ := by
  have h : 0 < (finrank ℚ K : ℝ) := Nat.cast_pos.mpr finrank_pos
  rw [← Real.rpow_le_rpow_iff (z := finrank ℚ K) (by positivity) (by positivity) h, Real.div_rpow
    (by positivity) (by positivity), ← Real.rpow_mul (by positivity), inv_mul_cancel₀ h.ne',
    Real.rpow_one, Real.mul_rpow (by positivity) (by positivity), Real.rpow_natCast,
    Real.rpow_natCast, ← pow_mul, ← Real.rpow_mul (by positivity),
    inv_mul_cancel_right₀ h.ne', Real.rpow_two]
  exact abs_discr_ge_of_isTotallyComplex K

variable {K}
/-
**NumberField.abs_discr_ge** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：abs_discr_ge (h : 1 < finrank Rat K) : (4 / 9 : Real) * (3 * π / 4) ^ finr
ank Rat K <= |discr K|
参数：h : 1 < finrank Rat K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 143 条，此处仅展示前 30 条）
-/
theorem abs_discr_ge (h : 1 < finrank ℚ K) :
    (4 / 9 : ℝ) * (3 * π / 4) ^ finrank ℚ K ≤ |discr K| := by
  refine le_trans ?_ (abs_discr_ge' K)
  -- The sequence `a n` is a lower bound for `|discr K|`. We prove below by induction a uniform
  -- lower bound for this sequence from which we deduce the result.
  rw [mul_comm 2 _]
  let a : ℕ → ℝ := fun n => (n : ℝ) ^ (n * 2) / ((4 / π) ^ n * (n.factorial : ℝ) ^ 2)
  suffices ∀ n, 2 ≤ n → (4 / 9 : ℝ) * (3 * π / 4) ^ n ≤ a n by
    refine le_trans (this (finrank ℚ K) h) ?_
    simp only [a]
    gcongr
    · exact (one_le_div Real.pi_pos).2 Real.pi_le_four
    · rw [← card_add_two_mul_card_eq_rank, mul_comm]
      exact Nat.le_add_left _ _
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact le_of_eq <| by simp [a, Nat.factorial_two]; field
  | succ m _ h_m =>
      suffices (3 : ℝ) ≤ (1 + 1 / m : ℝ) ^ (2 * m) by
        convert_to _ ≤ (a m) * (1 + 1 / m : ℝ) ^ (2 * m) / (4 / π)
        · simp_rw [a, add_mul, one_mul, pow_succ, Nat.factorial_succ]
          field_simp
          simp [field, div_pow]
          ring
        · rw [_root_.le_div_iff₀ (by positivity), pow_succ]
          convert! (mul_le_mul h_m this (by positivity) (by positivity)) using 1
          field
      refine le_trans (le_of_eq (by simp [field]; norm_num)) (one_add_mul_le_pow ?_ (2 * m))
      exact le_trans (by norm_num : (-2 : ℝ) ≤ 0) (by positivity)

/-- **Hermite-Minkowski Theorem**. A nontrivial number field has discriminant greater than `2`. -/
/-
**NumberField.abs_discr_gt_two** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：abs_discr_gt_two (h : 1 < finrank Rat K) : 2 < |discr K|
参数：h : 1 < finrank Rat K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Rat.cast_abs`：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K]
 [IsStrictOrderedRing K] (q : ℚ), ↑|q| = |↑q|
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 112 条，此处仅展示前 30 条）

--- 原说明 ---
**Hermite-Minkowski Theorem**. A nontrivial number field has discriminant greate
r than `2`.
-/
theorem abs_discr_gt_two (h : 1 < finrank ℚ K) : 2 < |discr K| := by
  rw [← Nat.succ_le_iff] at h
  rify
  calc
    (2 : ℝ) < (4 / 9) * (3 * π / 4) ^ 2 := by
      nlinarith [Real.pi_gt_three]
    _ ≤ (4 / 9 : ℝ) * (3 * π / 4) ^ finrank ℚ K := by
      gcongr
      linarith [Real.pi_gt_three]
    _ ≤ |(discr K : ℝ)| := mod_cast abs_discr_ge h

/-!
### Hermite Theorem
This section is devoted to the proof of Hermite theorem.

Let `N` be an integer . We prove that the set `S` of finite extensions `K` of `ℚ`
(in some fixed extension `A` of `ℚ`) such that `|discr K| ≤ N` is finite by proving, using
`finite_of_finite_generating_set`, that there exists a finite set `T ⊆ A` such that
`∀ K ∈ S, ∃ x ∈ T, K = ℚ⟮x⟯` .

To find the set `T`, we construct a finite set `T₀` of polynomials in `ℤ[X]` containing, for each
`K ∈ S`, the minimal polynomial of a primitive element of `K`. The set `T` is then the union of
roots in `A` of the polynomials in `T₀`. More precisely, the set `T₀` is the set of all polynomials
in `ℤ[X]` of degrees and coefficients bounded by some explicit constants depending only on `N`.

Indeed, we prove that, for any field `K` in `S`, its degree is bounded, see
`rank_le_rankOfDiscrBdd`, and also its Minkowski bound, see `minkowskiBound_lt_boundOfDiscBdd`.
Thus it follows from `mixedEmbedding.exists_primitive_element_lt_of_isComplex` and
`mixedEmbedding.exists_primitive_element_lt_of_isReal` that there exists an algebraic integer
`x` of `K` such that `K = ℚ(x)` and the conjugates of `x` are all bounded by some quantity
depending only on `N`.

Since the primitive element `x` is constructed differently depending on whether `K` has an infinite
real place or not, the theorem is proved in two parts.
-/

namespace hermiteTheorem

open Polynomial

open scoped IntermediateField

variable (A : Type*) [Field A] [CharZero A]

/-
**NumberField.hermiteTheorem.finite_of_finite_generating_set** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.hermiteTheorem`。
形式化陈述：finite_of_finite_generating_set {p : IntermediateField Rat A -> Prop} (S :
 Set {F : IntermediateField Rat A // p F}) {T : Set A} (hT : T.Finite) (h : fora
ll F in S, exists x in T, F = Rat⟮x⟯) : S.Finite
参数：S : Set {F : IntermediateField Rat A // p F}；hT : T.Finite；h : forall F in S,
 exists x in T, F = Rat⟮x⟯。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
-/
theorem finite_of_finite_generating_set {p : IntermediateField ℚ A → Prop}
    (S : Set {F : IntermediateField ℚ A // p F}) {T : Set A}
    (hT : T.Finite) (h : ∀ F ∈ S, ∃ x ∈ T, F = ℚ⟮x⟯) :
    S.Finite := by
  rw [← Set.finite_coe_iff] at hT
  refine Set.finite_coe_iff.mp <| Finite.of_injective
    (fun ⟨F, hF⟩ ↦ (⟨(h F hF).choose, (h F hF).choose_spec.1⟩ : T)) (fun _ _ h_eq ↦ ?_)
  rw [Subtype.ext_iff, Subtype.ext_iff]
  convert! congr_arg (ℚ⟮·⟯) (Subtype.mk_eq_mk.mp h_eq)
  all_goals exact (h _ (Subtype.mem _)).choose_spec.2

variable (N : ℕ)

/-- An upper bound on the degree of a number field `K` with `|discr K| ≤ N`,
see `rank_le_rankOfDiscrBdd`. -/
/-
**NumberField.hermiteTheorem.rankOfDiscrBdd** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberF
ield.hermiteTheorem`。
形式化陈述：rankOfDiscrBdd : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An upper bound on the degree of a number field `K` with `|discr K| ≤ N`,
see `rank_le_rankOfDiscrBdd`.
-/
noncomputable abbrev rankOfDiscrBdd : ℕ :=
  max 1 (Nat.floor ((Real.log ((9 / 4 : ℝ) * N) / Real.log (3 * π / 4))))

/-- An upper bound on the Minkowski bound of a number field `K` with `|discr K| ≤ N`;
see `minkowskiBound_lt_boundOfDiscBdd`. -/
/-
**NumberField.hermiteTheorem.boundOfDiscBdd** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberF
ield.hermiteTheorem`。
形式化陈述：boundOfDiscBdd : Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An upper bound on the Minkowski bound of a number field `K` with `|discr K| ≤ N`
;
see `minkowskiBound_lt_boundOfDiscBdd`.
-/
noncomputable abbrev boundOfDiscBdd : ℝ≥0 := sqrt N * (2 : ℝ≥0) ^ rankOfDiscrBdd N + 1

variable {N} (hK : |discr K| ≤ N)

include hK in
/-- If `|discr K| ≤ N` then the degree of `K` is at most `rankOfDiscrBdd`. -/
/-
**NumberField.hermiteTheorem.rank_le_rankOfDiscrBdd** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.hermiteTheorem`。
形式化陈述：rank_le_rankOfDiscrBdd : finrank Rat K <= rankOfDiscrBdd N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.discr_ne_zero`：discr_ne_zero : discr K != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_nonpos_iff`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrd
er α] [AddLeftMono α] {a : α} [AddRightMono α], |a| ≤ 0 ↔ a = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_lt_iff₀'`：div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 127 条，此处仅展示前 30 条）

--- 原说明 ---
If `|discr K| ≤ N` then the degree of `K` is at most `rankOfDiscrBdd`.
-/
theorem rank_le_rankOfDiscrBdd :
    finrank ℚ K ≤ rankOfDiscrBdd N := by
  have h_nz : N ≠ 0 := by
    refine fun h ↦ discr_ne_zero K ?_
    rwa [h, Nat.cast_zero, abs_nonpos_iff] at hK
  have h₂ : 1 < 3 * π / 4 := by
    rw [_root_.lt_div_iff₀ (by positivity), ← _root_.div_lt_iff₀' (by positivity), one_mul]
    linarith [Real.pi_gt_three]
  obtain h | h := lt_or_ge 1 (finrank ℚ K)
  · apply le_max_of_le_right
    rw [Nat.le_floor_iff]
    · have h := le_trans (abs_discr_ge h) (Int.cast_le.mpr hK)
      contrapose! h
      rw [← Real.rpow_natCast]
      rw [Real.log_div_log] at h
      refine lt_of_le_of_lt ?_ (mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow_of_exponent_lt h₂ h) (by positivity : (0 : ℝ) < 4 / 9))
      rw [Real.rpow_logb (lt_trans zero_lt_one h₂) (ne_of_gt h₂) (by positivity), ← mul_assoc,
            ← inv_div, inv_mul_cancel₀ (by simp), one_mul, Int.cast_natCast]
    · refine div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (le_of_lt h₂))
      rw [mul_comm, ← mul_div_assoc, _root_.le_div_iff₀ (by positivity), one_mul,
        ← _root_.div_le_iff₀ (by positivity)]
      exact le_trans (by norm_num) (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h_nz))
  · exact le_max_of_le_left h

include hK in
/-- If `|discr K| ≤ N` then the Minkowski bound of `K` is less than `boundOfDiscrBdd`. -/
/-
**NumberField.hermiteTheorem.minkowskiBound_lt_boundOfDiscBdd** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.hermiteTheorem`。
形式化陈述：minkowskiBound_lt_boundOfDiscBdd : minkowskiBound K ↑1 < boundOfDiscBdd N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `NumberField.mixedEmbedding.minkowskiBound.eq_1`：∀ (K : Type u_1) [inst :
 Field K] [inst_1 : NumberField K]   (I : (FractionalIdeal (nonZeroDivisors (Num
berField.RingOfIntegers K)) K)ˣ),   …
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatti
ceBasis`：volume_fundamentalDomain_fractionalIdealLatticeBasis : volume (fundamen
talDomain (fractionalIdealLatticeBasis K I)) = .ofReal (FractionalIde…
· 使用定理 `NumberField.hermiteTheorem.boundOfDiscBdd.eq_1`：∀ (N : ℕ),   NumberField
.hermiteTheorem.boundOfDiscBdd N = NNReal.sqrt ↑N * 2 ^ NumberField.hermiteTheor
em.rankOfDiscrBdd N + 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `FractionalIdeal.absNorm_one`：absNorm_one : absNorm (1 : FractionalIdeal 
R⁰ K) = 1
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 67 条，此处仅展示前 30 条）

--- 原说明 ---
If `|discr K| ≤ N` then the Minkowski bound of `K` is less than `boundOfDiscrBdd
`.
-/
theorem minkowskiBound_lt_boundOfDiscBdd : minkowskiBound K ↑1 < boundOfDiscBdd N := by
  have : boundOfDiscBdd N - 1 < boundOfDiscBdd N := by
    simp_rw [boundOfDiscBdd, add_tsub_cancel_right, lt_add_iff_pos_right, zero_lt_one]
  refine lt_of_le_of_lt ?_ (coe_lt_coe.mpr this)
  rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis, boundOfDiscBdd,
    add_tsub_cancel_right, Units.val_one, FractionalIdeal.absNorm_one, Rat.cast_one,
    ENNReal.ofReal_one, one_mul, mixedEmbedding.finrank, volume_fundamentalDomain_latticeBasis,
    coe_mul, ENNReal.coe_pow, coe_ofNat, show sqrt N = (1 : ℝ≥0∞) * sqrt N by rw [one_mul]]
  gcongr
  · exact pow_le_one₀ (by positivity) (by simp)
  · rwa [← NNReal.coe_le_coe, coe_nnnorm, Int.norm_eq_abs, ← Int.cast_abs,
      NNReal.coe_natCast, ← Int.cast_natCast, Int.cast_le]
  · exact one_le_two
  · exact rank_le_rankOfDiscrBdd hK

include hK in
/-
**NumberField.hermiteTheorem.natDegree_le_rankOfDiscrBdd** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.hermiteTheorem`。
形式化陈述：natDegree_le_rankOfDiscrBdd (a : 𝓞 K) (h : Rat⟮(a : K)⟯ = ⊤) : natDegree (
minpoly Int (a : K)) <= rankOfDiscrBdd N
参数：a : 𝓞 K；h : Rat⟮(a : K)⟯ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.hermiteTheorem.rank_le_rankOfDiscrBdd`：rank_le_rankOfDiscrBd
d : finrank Rat K <= rankOfDiscrBdd N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `NumberField.RingOfIntegers.isIntegral_coe`：isIntegral_coe (x : 𝓞 K) : Is
Integral Int (algebraMap _ K x)
· 使用定理 `minpoly.isIntegrallyClosed_eq_field_fractions'`：isIntegrallyClosed_eq_fi
eld_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S] {s : S} (hs : Is
Integral R s) : minpoly K s = (minpo…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Field.primitive_element_iff_minpoly_natDegree_eq`：primitive_element_iff_
minpoly_natDegree_eq (α : E) : F⟮α⟯ = ⊤ ↔ (minpoly F α).natDegree = finrank F E
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
-/
theorem natDegree_le_rankOfDiscrBdd (a : 𝓞 K) (h : ℚ⟮(a : K)⟯ = ⊤) :
    natDegree (minpoly ℤ (a : K)) ≤ rankOfDiscrBdd N := by
  rw [Field.primitive_element_iff_minpoly_natDegree_eq,
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ a.isIntegral_coe,
    (minpoly.monic a.isIntegral_coe).natDegree_map] at h
  exact h.symm ▸ rank_le_rankOfDiscrBdd hK

variable (N)

set_option backward.isDefEq.respectTransparency false in
/-
**NumberField.hermiteTheorem.finite_of_discr_bdd_of_isReal** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.hermiteTheorem`。
形式化陈述：finite_of_discr_bdd_of_isReal : {K : { F : IntermediateField Rat A // Fini
teDimensional Rat F} | haveI : NumberField K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.hermiteTheorem.finite_of_finite_generating_set`：finite_of_fi
nite_generating_set {p : IntermediateField Rat A -> Prop} (S : Set {F : Intermed
iateField Rat A // p F}) {T : Set A} (hT : T.Fin…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.bUnion_roots_finite`：bUnion_roots_finite {R S : Type*} [Semir
ing R] [CommRing S] [IsDomain S] [DecidableEq S] (m : R ->+* S) (d : Nat) {U : S
et R} (h : U.Finite)…
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.hermiteTheorem.minkowskiBound_lt_boundOfDiscBdd`：minkowskiBo
und_lt_boundOfDiscBdd : minkowskiBound K ↑1 < boundOfDiscBdd N
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NumberField.mixedEmbedding.one_le_convexBodyLTFactor`：one_le_convexBodyL
TFactor : 1 <= convexBodyLTFactor K
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.exists_primitive_element_lt_of_isReal`：exists
_primitive_element_lt_of_isReal {w₀ : InfinitePlace K} (hw₀ : IsReal w₀) {B : Re
al>=0} (hB : minkowskiBound K ↑1 < convexBodyLTFactor …
· 使用定理 `NumberField.RingOfIntegers.isIntegral_coe`：isIntegral_coe (x : 𝓞 K) : Is
Integral Int (algebraMap _ K x)
· 使用定理 `NumberField.hermiteTheorem.natDegree_le_rankOfDiscrBdd`：natDegree_le_ran
kOfDiscrBdd (a : 𝓞 K) (h : Rat⟮(a : K)⟯ = ⊤) : natDegree (minpoly Int (a : K)) <
= rankOfDiscrBdd N
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
（共 104 条，此处仅展示前 30 条）
-/
theorem finite_of_discr_bdd_of_isReal :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI :  NumberField K := @NumberField.mk _ _ inferInstance K.prop
      {w : InfinitePlace K | IsReal w}.Nonempty ∧ |discr K| ≤ N }.Finite := by
  classical
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max B 1) ^ D * Nat.choose D (D / 2))
  refine finite_of_finite_generating_set A _ (bUnion_roots_finite (algebraMap ℤ A) D
      (Set.finite_Icc (-C : ℤ) C)) (fun ⟨K, hK₀⟩ ⟨hK₁, hK₂⟩ ↦ ?_)
  -- We now need to prove that each field is generated by an element of the union of the root set
  simp_rw [Set.mem_iUnion]
  -- this is purely an optimization
  have : CharZero K := SubsemiringClass.instCharZero K
  have : NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨w₀, hw₀⟩ := hK₁
  suffices minkowskiBound K ↑1 < (convexBodyLTFactor K) * B by
    obtain ⟨x, hx₁, hx₂⟩ := exists_primitive_element_lt_of_isReal K hw₀ this
    have hx := x.isIntegral_coe
    refine ⟨x, ⟨⟨minpoly ℤ (x : K), ⟨?_, fun i ↦ ?_⟩, ?_⟩, ?_⟩⟩
    · exact natDegree_le_rankOfDiscrBdd hK₂ x hx₁
    · rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
      refine (Eq.trans_le ?_ <| Embeddings.coeff_bdd_of_norm_le
          ((le_iff_le (x : K) _).mp (fun w ↦ le_of_lt (hx₂ w))) i).trans ?_
      · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map, eq_intCast,
          Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
      · refine le_trans ?_ (Nat.le_ceil _)
        rw [show max ↑(max (B : ℝ≥0) 1) (1 : ℝ) = max (B : ℝ) 1 by simp, val_eq_coe, NNReal.coe_mul,
          NNReal.coe_pow, NNReal.coe_max, NNReal.coe_one, NNReal.coe_natCast]
        gcongr
        · exact le_max_right _ 1
        · exact rank_le_rankOfDiscrBdd hK₂
        · exact (Nat.choose_le_choose _ (rank_le_rankOfDiscrBdd hK₂)).trans
            (Nat.choose_le_middle _ _)
    · refine mem_rootSet.mpr ⟨minpoly.ne_zero hx, ?_⟩
      exact (aeval_algebraMap_eq_zero_iff A (x : K) _).mpr (minpoly.aeval ℤ (x : K))
    · rw [← (IntermediateField.lift_injective _).eq_iff, eq_comm] at hx₁
      convert! hx₁
      · simp only [IntermediateField.lift_top]
      · simp only [IntermediateField.lift_adjoin, Set.image_singleton]
  calc
    minkowskiBound K 1 < B := minkowskiBound_lt_boundOfDiscBdd hK₂
    _ = 1 * B := by rw [one_mul]
    _ ≤ convexBodyLTFactor K * B := by gcongr; exact mod_cast one_le_convexBodyLTFactor K

set_option backward.isDefEq.respectTransparency false in
/-
**NumberField.hermiteTheorem.finite_of_discr_bdd_of_isComplex** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.hermiteTheorem`。
形式化陈述：finite_of_discr_bdd_of_isComplex : {K : { F : IntermediateField Rat A // F
initeDimensional Rat F} | haveI : NumberField K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.hermiteTheorem.finite_of_finite_generating_set`：finite_of_fi
nite_generating_set {p : IntermediateField Rat A -> Prop} (S : Set {F : Intermed
iateField Rat A // p F}) {T : Set A} (hT : T.Fin…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.bUnion_roots_finite`：bUnion_roots_finite {R S : Type*} [Semir
ing R] [CommRing S] [IsDomain S] [DecidableEq S] (m : R ->+* S) (d : Nat) {U : S
et R} (h : U.Finite)…
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.hermiteTheorem.minkowskiBound_lt_boundOfDiscBdd`：minkowskiBo
und_lt_boundOfDiscBdd : minkowskiBound K ↑1 < boundOfDiscBdd N
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NumberField.mixedEmbedding.one_le_convexBodyLT'Factor`：∀ (K : Type u_1) 
[inst : Field K] [inst_1 : NumberField K], 1 ≤ NumberField.mixedEmbedding.convex
BodyLT'Factor K
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.exists_primitive_element_lt_of_isComplex`：exi
sts_primitive_element_lt_of_isComplex {w₀ : InfinitePlace K} (hw₀ : IsComplex w₀
) {B : Real>=0} (hB : minkowskiBound K ↑1 < convexBodyLT'…
· 使用定理 `NumberField.RingOfIntegers.isIntegral_coe`：isIntegral_coe (x : 𝓞 K) : Is
Integral Int (algebraMap _ K x)
· 使用定理 `NumberField.hermiteTheorem.natDegree_le_rankOfDiscrBdd`：natDegree_le_ran
kOfDiscrBdd (a : 𝓞 K) (h : Rat⟮(a : K)⟯ = ⊤) : natDegree (minpoly Int (a : K)) <
= rankOfDiscrBdd N
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
（共 107 条，此处仅展示前 30 条）
-/
theorem finite_of_discr_bdd_of_isComplex :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI :  NumberField K := @NumberField.mk _ _ inferInstance K.prop
      {w : InfinitePlace K | IsComplex w}.Nonempty ∧ |discr K| ≤ N }.Finite := by
  classical
  -- The bound on the degree of the generating polynomials
  let D := rankOfDiscrBdd N
  -- The bound on the Minkowski bound
  let B := boundOfDiscBdd N
  -- The bound on the coefficients of the generating polynomials
  let C := Nat.ceil ((max (sqrt (1 + B ^ 2)) 1) ^ D * Nat.choose D (D / 2))
  refine finite_of_finite_generating_set A _ (bUnion_roots_finite (algebraMap ℤ A) D
      (Set.finite_Icc (-C : ℤ) C)) (fun ⟨K, hK₀⟩ ⟨hK₁, hK₂⟩ ↦ ?_)
  -- We now need to prove that each field is generated by an element of the union of the root set
  simp_rw [Set.mem_iUnion]
  -- this is purely an optimization
  have : CharZero K := SubsemiringClass.instCharZero K
  have : NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨w₀, hw₀⟩ := hK₁
  suffices minkowskiBound K ↑1 < (convexBodyLT'Factor K) * boundOfDiscBdd N by
    obtain ⟨x, hx₁, hx₂⟩ := exists_primitive_element_lt_of_isComplex K hw₀ this
    have hx := x.isIntegral_coe
    refine ⟨x, ⟨⟨minpoly ℤ (x : K), ⟨?_, fun i ↦ ?_⟩, ?_⟩, ?_⟩⟩
    · exact natDegree_le_rankOfDiscrBdd hK₂ x hx₁
    · rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
      refine (Eq.trans_le ?_ <| Embeddings.coeff_bdd_of_norm_le
          ((le_iff_le (x : K) _).mp (fun w ↦ le_of_lt (hx₂ w))) i).trans ?_
      · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map, eq_intCast,
          Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
      · refine le_trans ?_ (Nat.le_ceil _)
        rw [val_eq_coe, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_max, NNReal.coe_one,
          Real.coe_sqrt, NNReal.coe_add 1, NNReal.coe_one, NNReal.coe_pow]
        gcongr
        · exact le_max_right _ 1
        · exact rank_le_rankOfDiscrBdd hK₂
        · rw [NNReal.coe_natCast, Nat.cast_le]
          exact (Nat.choose_le_choose _ (rank_le_rankOfDiscrBdd hK₂)).trans
            (Nat.choose_le_middle _ _)
    · refine mem_rootSet.mpr ⟨minpoly.ne_zero hx, ?_⟩
      exact (aeval_algebraMap_eq_zero_iff A (x : K) _).mpr (minpoly.aeval ℤ (x : K))
    · rw [← (IntermediateField.lift_injective _).eq_iff, eq_comm] at hx₁
      convert! hx₁
      · simp only [IntermediateField.lift_top]
      · simp only [IntermediateField.lift_adjoin, Set.image_singleton]
  calc
    minkowskiBound K 1 < B := minkowskiBound_lt_boundOfDiscBdd hK₂
    _ = 1 * B := by rw [one_mul]
    _ ≤ convexBodyLT'Factor K * B := by gcongr; exact mod_cast one_le_convexBodyLT'Factor K

/-- **Hermite Theorem**. Let `N` be an integer. There are only finitely many number fields
(in some fixed extension of `ℚ`) of discriminant bounded by `N`. -/
/-
**NumberField.hermiteTheorem._root_.NumberField.finite_of_discr_bdd** 是 Mathlib 
中的一个定理，位于命名空间 `NumberField.hermiteTheorem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Hermite Theorem**. Let `N` be an integer. There are only finitely many number 
fields
(in some fixed extension of `ℚ`) of discriminant bounded by `N`.
-/
theorem _root_.NumberField.finite_of_discr_bdd :
    {K : { F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
      haveI :  NumberField K := @NumberField.mk _ _ inferInstance K.prop
      |discr K| ≤ N }.Finite := by
  refine Set.Finite.subset (Set.Finite.union (finite_of_discr_bdd_of_isReal A N)
    (finite_of_discr_bdd_of_isComplex A N)) ?_
  rintro ⟨K, hK₀⟩ hK₁
  -- this is purely an optimization
  have : CharZero K := SubsemiringClass.instCharZero K
  have : NumberField K := @NumberField.mk _ _ inferInstance hK₀
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  by_cases hw₀ : IsReal w₀
  · apply Set.mem_union_left
    exact ⟨⟨w₀, hw₀⟩, hK₁⟩
  · apply Set.mem_union_right
    exact ⟨⟨w₀, not_isReal_iff_isComplex.mp hw₀⟩, hK₁⟩

end hermiteTheorem

end NumberField

