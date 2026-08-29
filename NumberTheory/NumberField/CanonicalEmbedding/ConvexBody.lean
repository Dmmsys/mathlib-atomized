/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Convex Bodies

The file contains the definitions of several convex bodies lying in the mixed space `ℝ^r₁ × ℂ^r₂`
associated to a number field of signature `K` and proves several existence theorems by applying
*Minkowski Convex Body Theorem* to those.

## Main definitions and results

* `NumberField.mixedEmbedding.convexBodyLT`: The set of points `x` such that `‖x w‖ < f w` for all
  infinite places `w` with `f : InfinitePlace K → ℝ≥0`.

* `NumberField.mixedEmbedding.convexBodySum`: The set of points `x` such that
  `∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B`

* `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt`: Let `I` be a fractional ideal of `K`.
  Assume that `f` is such that `minkowskiBound K I < volume (convexBodyLT K f)`, then there exists a
  nonzero algebraic number `a` in `I` such that `w a < f w` for all infinite places `w`.

* `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le`: Let `I` be a fractional ideal
  of `K`. Assume that `B` is such that `minkowskiBound K I < volume (convexBodySum K B)` (see
  `convexBodySum_volume` for the computation of this volume), then there exists a nonzero algebraic
  number `a` in `I` such that `|Norm a| < (B / d) ^ d` where `d` is the degree of `K`.

## Tags

number field, infinite places
-/

@[expose] public section

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace Module

section convexBodyLT

open Metric NNReal

variable (f : InfinitePlace K -> Real>=0)

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `convexBodyLT` / `convexBodyLT` 的定义

English:
abbreviation convexBodyLT
  signature: : Set (mixedSpace K)
  body: (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => ball 0 (f w)))

中文:
缩写 convexBodyLT
  签名: : Set (mixedSpace K)
  定义体: (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => ball 0 (f w)))

Depends on / 依赖: InfinitePlace, IsComplex, IsReal, Set.univ.pi
-/
noncomputable abbrev convexBodyLT : Set (mixedSpace K) :=
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => ball 0 (f w)))

/--
theorem `convexBodyLT_mem` / 定理 `convexBodyLT_mem`

English:
theorem convexBodyLT_mem
  given: {x : K}
  proof: by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, mem_ball_zero_iff, RingHom.pi_apply, ← Complex.norm_real,
    embedding_of_isReal_apply, Subtype.forall, ← forall₂_or_left, ← not_isReal_iff_isComplex, em,
    forall_true_left, norm_embed

中文:
定理 convexBodyLT_mem
  条件: {x : K}
  证明: by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, mem_ball_zero_iff, RingHom.pi_apply, ← Complex.norm_real,
    embedding_of_isReal_apply, Subtype.forall, ← forall₂_or_left, ← not_isReal_iff_isComplex, em,
    forall_true_left, norm_embed

Depends on / 依赖: Complex.norm_real, RingHom, RingHom.pi_apply, RingHom.prod_apply, Set.mem_pi, Set.mem_prod, Set.mem_univ, Subtype, Subtype.forall, embedding_of_isReal_apply, forall_true_left, mem_ball_zero_iff, mem_pi, mem_prod, mem_univ, mixedEmbedding, norm_embedding_eq, norm_real, not_isReal_iff_isComplex, pi_apply
-/
theorem convexBodyLT_mem {x : K} :
    mixedEmbedding K x in (convexBodyLT K f) ↔ forall w : InfinitePlace K, w x < f w := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, mem_ball_zero_iff, RingHom.pi_apply, ← Complex.norm_real,
    embedding_of_isReal_apply, Subtype.forall, ← forall₂_or_left, ← not_isReal_iff_isComplex, em,
    forall_true_left, norm_embedding_eq]

/--
theorem `convexBodyLT_neg_mem` / 定理 `convexBodyLT_neg_mem`

English:
theorem convexBodyLT_neg_mem
  given: (x : mixedSpace K) (hx : x in (convexBodyLT K f))
  proof: by
  simp only [Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
    mem_ball_zero_iff, norm_neg, Real.norm_eq_abs, forall_true_left, Subtype.forall,
    Prod.snd_neg] at hx ⊢
  exact hx

中文:
定理 convexBodyLT_neg_mem
  条件: (x : mixedSpace K) (hx : x in (convexBodyLT K f))
  证明: by
  simp only [Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
    mem_ball_zero_iff, norm_neg, Real.norm_eq_abs, forall_true_left, Subtype.forall,
    Prod.snd_neg] at hx ⊢
  exact hx

Depends on / 依赖: Pi.neg_apply, Prod.fst_neg, Prod.snd_neg, Real.norm_eq_abs, Set.mem_pi, Set.mem_prod, Set.mem_univ, Subtype, Subtype.forall, forall_true_left, fst_neg, mem_ball_zero_iff, mem_pi, mem_prod, mem_univ, neg_apply, norm_eq_abs, norm_neg, snd_neg
-/
theorem convexBodyLT_neg_mem (x : mixedSpace K) (hx : x in (convexBodyLT K f)) :
    -x in (convexBodyLT K f) := by
  simp only [Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
    mem_ball_zero_iff, norm_neg, Real.norm_eq_abs, forall_true_left, Subtype.forall,
    Prod.snd_neg] at hx ⊢
  exact hx

/--
theorem `convexBodyLT_convex` / 定理 `convexBodyLT_convex`

English:
theorem convexBodyLT_convex
  statement: Convex Real (convexBodyLT K f)
  proof: Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => convex_ball _ _))

中文:
定理 convexBodyLT_convex
  结论: Convex 实数 (convexBodyLT K f)
  证明: Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => convex_ball _ _))

Depends on / 依赖: Convex, Convex.prod, convex_ball, convex_pi
-/
theorem convexBodyLT_convex : Convex Real (convexBodyLT K f) :=
  Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => convex_ball _ _))

open Fintype MeasureTheory MeasureTheory.Measure ENNReal

variable [NumberField K]

/--
Definition of `convexBodyLTFactor` / `convexBodyLTFactor` 的定义

English:
abbreviation convexBodyLTFactor
  signature: : Real>=0
  body: (2 : Real>=0) ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K

中文:
缩写 convexBodyLTFactor
  签名: : 实数>=0
  定义体: (2 : Real>=0) ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K

Depends on / 依赖: NNReal, NNReal.pi, nrComplexPlaces, nrRealPlaces
-/
noncomputable abbrev convexBodyLTFactor : Real>=0 :=
  (2 : Real>=0) ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K

/--
theorem `convexBodyLTFactor_ne_zero` / 定理 `convexBodyLTFactor_ne_zero`

English:
theorem convexBodyLTFactor_ne_zero
  statement: convexBodyLTFactor K != 0
  proof: mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)

中文:
定理 convexBodyLTFactor_ne_zero
  结论: convexBodyLTFactor K != 0
  证明: mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)

Depends on / 依赖: mul_ne_zero, pi_ne_zero, pow_ne_zero, two_ne_zero
-/
theorem convexBodyLTFactor_ne_zero : convexBodyLTFactor K != 0 :=
  mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)

/--
theorem `one_le_convexBodyLTFactor` / 定理 `one_le_convexBodyLTFactor`

English:
theorem one_le_convexBodyLTFactor
  statement: 1 <= convexBodyLTFactor K
  proof: one_le_mul (one_le_pow₀ one_le_two) (one_le_pow₀ (one_le_two.trans Real.two_le_pi))

中文:
定理 one_le_convexBodyLTFactor
  结论: 1 <= convexBodyLTFactor K
  证明: one_le_mul (one_le_pow₀ one_le_two) (one_le_pow₀ (one_le_two.trans Real.two_le_pi))

Depends on / 依赖: Real.two_le_pi, one_le_mul, one_le_two, one_le_two.trans, two_le_pi
-/
theorem one_le_convexBodyLTFactor : 1 <= convexBodyLTFactor K :=
  one_le_mul (one_le_pow₀ one_le_two) (one_le_pow₀ (one_le_two.trans Real.two_le_pi))

open scoped Classical in
/--
theorem `convexBodyLT_volume` / 定理 `convexBodyLT_volume`

English:
theorem convexBodyLT_volume
  proof: by
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ∏ x : {w // InfinitePlace.IsComplex w}, ENNReal.ofReal (f x.val) ^ 2 * NNReal.pi := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball, Complex.volume_ball]
    _ = ((2 : 

中文:
定理 convexBodyLT_volume
  证明: by
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ∏ x : {w // InfinitePlace.IsComplex w}, ENNReal.ofReal (f x.val) ^ 2 * NNReal.pi := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball, Complex.volume_ball]
    _ = ((2 : 

Depends on / 依赖: Complex.volume_ball, ENNReal, ENNReal.ofReal, InfinitePlace, InfinitePlace.IsComplex, InfinitePlace.IsReal, IsComplex, IsReal, NNReal, NNReal.pi, Real.volume_ball, nrComplexPlaces, nrRealPlaces, ofReal, ofReal_mul, pi_pi, prod_prod, simp_rw, volume_ball, volume_eq_prod
-/
theorem convexBodyLT_volume :
    volume (convexBodyLT K f) = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w) := by
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ∏ x : {w // InfinitePlace.IsComplex w}, ENNReal.ofReal (f x.val) ^ 2 * NNReal.pi := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball, Complex.volume_ball]
    _ = ((2 : Real>=0) ^ nrRealPlaces K
          * (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val)))
          * ((∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) *
            NNReal.pi ^ nrComplexPlaces K) := by
      simp_rw [ofReal_mul (by simp : 0 <= (2 : Real)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, ofReal_ofNat, ofReal_coe_nnreal, coe_ofNat]
    _ = (convexBodyLTFactor K) * ((∏ x : {w // InfinitePlace.IsReal w}, .ofReal (f x.val)) *
        (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2)) := by
      simp_rw [convexBodyLTFactor, coe_mul, ENNReal.coe_pow]
      ring
    _ = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w) := by
      simp_rw [prod_eq_prod_mul_prod, coe_mul, ofNNReal_finsetProd, mult_isReal, mult_isComplex,
        pow_one, ENNReal.coe_pow, ofReal_coe_nnreal]

variable {f}

/--
theorem `adjust_f` / 定理 `adjust_f`

English:
theorem adjust_f
  given: {w₁ : InfinitePlace K} (B : Real>=0) (hf : forall w, w != w₁ -> f w != 0)
  proof: by
  classical
  let S := ∏ w in Finset.univ.erase w₁, (f w) ^ mult w
  refine ⟨Function.update f w₁ ((B * S⁻¹) ^ (mult w₁ : Real)⁻¹), ?_, ?_⟩
  · exact fun w hw => Function.update_of_ne hw _ f
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₁), Function.update_self,
      Finset.pro

中文:
定理 adjust_f
  条件: {w₁ : InfinitePlace K} (B : 实数>=0) (hf : 对任意 w, w != w₁ -> f w != 0)
  证明: by
  classical
  let S := ∏ w in Finset.univ.erase w₁, (f w) ^ mult w
  refine ⟨Function.update f w₁ ((B * S⁻¹) ^ (mult w₁ : Real)⁻¹), ?_, ?_⟩
  · exact fun w hw => Function.update_of_ne hw _ f
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₁), Function.update_self,
      Finset.pro

Depends on / 依赖: Finset, Finset.mem_univ, Finset.mul_prod_erase, Finset.ne_of_mem_erase, Finset.prod_congr, Finset.prod_ne, Finset.univ, Finset.univ.erase, Function, Function.update, Function.update_of_ne, Function.update_self, NNReal, NNReal.rpow_mul, NNReal.rpow_natCast, NNReal.rpow_one, classical, mem_univ, mul_assoc, mul_one
-/
theorem adjust_f {w₁ : InfinitePlace K} (B : Real>=0) (hf : forall w, w != w₁ -> f w != 0) :
    exists g : InfinitePlace K -> Real>=0, (forall w, w != w₁ -> g w = f w) ∧ ∏ w, (g w) ^ mult w = B := by
  classical
  let S := ∏ w in Finset.univ.erase w₁, (f w) ^ mult w
  refine ⟨Function.update f w₁ ((B * S⁻¹) ^ (mult w₁ : Real)⁻¹), ?_, ?_⟩
  · exact fun w hw => Function.update_of_ne hw _ f
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₁), Function.update_self,
      Finset.prod_congr rfl fun w hw => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)],
      ← NNReal.rpow_natCast, ← NNReal.rpow_mul, inv_mul_cancel₀, NNReal.rpow_one, mul_assoc,
      inv_mul_cancel₀, mul_one]
    · rw [Finset.prod_ne_zero_iff]
      exact fun w hw => pow_ne_zero _ (hf w (Finset.ne_of_mem_erase hw))
    · rw [mult]; split_ifs <;> norm_num

end convexBodyLT

section convexBodyLT'

open Metric ENNReal NNReal

variable (f : InfinitePlace K -> Real>=0) (w₀ : {w : InfinitePlace K // IsComplex w})

open scoped Classical in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `convexBodyLT'` / `convexBodyLT'` 的定义

English:
abbreviation convexBodyLT'
  signature: : Set (mixedSpace K)
  body: (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } =>
    if w = w₀ then {x | |x.re| < 1 ∧ |x.im| < (f w : Real) ^ 2} else ball 0 (f w)))

中文:
缩写 convexBodyLT'
  签名: : Set (mixedSpace K)
  定义体: (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } =>
    if w = w₀ then {x | |x.re| < 1 ∧ |x.im| < (f w : Real) ^ 2} else ball 0 (f w)))

Depends on / 依赖: InfinitePlace, IsComplex, IsReal, Set.univ.pi, x.im, x.re
-/
noncomputable abbrev convexBodyLT' : Set (mixedSpace K) :=
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } =>
    if w = w₀ then {x | |x.re| < 1 ∧ |x.im| < (f w : Real) ^ 2} else ball 0 (f w)))

/--
theorem `convexBodyLT'_mem` / 定理 `convexBodyLT'_mem`

English:
theorem convexBodyLT'_mem
  given: {x : K}
  proof: by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, RingHom.pi_apply, mem_ball_zero_iff, ← Complex.norm_real,
    embedding_of_isReal_apply, norm_embedding_eq, Subtype.forall]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨fun w h_ne => ?_, ?_⟩, fun ⟨h₁, h₂⟩ =

中文:
定理 convexBodyLT'_mem
  条件: {x : K}
  证明: by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, RingHom.pi_apply, mem_ball_zero_iff, ← Complex.norm_real,
    embedding_of_isReal_apply, norm_embedding_eq, Subtype.forall]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨fun w h_ne => ?_, ?_⟩, fun ⟨h₁, h₂⟩ =
-/
theorem convexBodyLT'_mem {x : K} :
    mixedEmbedding K x in convexBodyLT' K f w₀ ↔
      (forall w : InfinitePlace K, w != w₀ -> w x < f w) ∧
      |(w₀.val.embedding x).re| < 1 ∧ |(w₀.val.embedding x).im| < (f w₀ : Real) ^ 2 := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, RingHom.pi_apply, mem_ball_zero_iff, ← Complex.norm_real,
    embedding_of_isReal_apply, norm_embedding_eq, Subtype.forall]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨fun w h_ne => ?_, ?_⟩, fun ⟨h₁, h₂⟩ => ⟨fun w hw => ?_, fun w hw => ?_⟩⟩
  · by_cases hw : IsReal w
    · exact norm_embedding_eq w _ ▸ h₁ w hw
    · specialize h₂ w (not_isReal_iff_isComplex.mp hw)
      rw [apply_ite (w.embedding x in ·)]; rw [Set.mem_ofPred_eq]; rw [mem_ball_zero_iff]; rw [norm_embedding_eq] at h₂
      rwa [if_neg (by exact Subtype.coe_ne_coe.1 h_ne)] at h₂
  · simpa [if_true] using h₂ w₀.val w₀.prop
  · exact h₁ w (ne_of_isReal_isComplex hw w₀.prop)
  · by_cases h_ne : w = w₀
    · simpa [h_ne]
    · rw [if_neg (by exact Subtype.coe_ne_coe.1 h_ne)]
      rw [mem_ball_zero_iff]; rw [norm_embedding_eq]
      exact h₁ w h_ne

/--
theorem `convexBodyLT'_neg_mem` / 定理 `convexBodyLT'_neg_mem`

English:
theorem convexBodyLT'_neg_mem
  given: (x : mixedSpace K) (hx : x in convexBodyLT' K f w₀)
  proof: by
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, mem_ball, dist_zero_right, Real.norm_eq_abs,
    true_implies, Subtype.forall, Prod.fst_neg, Pi.neg_apply, norm_neg, Prod.snd_neg] at hx ⊢
  convert! hx using 3
  split_ifs <;> simp

中文:
定理 convexBodyLT'_neg_mem
  条件: (x : mixedSpace K) (hx : x in convexBodyLT' K f w₀)
  证明: by
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, mem_ball, dist_zero_right, Real.norm_eq_abs,
    true_implies, Subtype.forall, Prod.fst_neg, Pi.neg_apply, norm_neg, Prod.snd_neg] at hx ⊢
  convert! hx using 3
  split_ifs <;> simp
-/
theorem convexBodyLT'_neg_mem (x : mixedSpace K) (hx : x in convexBodyLT' K f w₀) :
    -x in convexBodyLT' K f w₀ := by
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, mem_ball, dist_zero_right, Real.norm_eq_abs,
    true_implies, Subtype.forall, Prod.fst_neg, Pi.neg_apply, norm_neg, Prod.snd_neg] at hx ⊢
  convert! hx using 3
  split_ifs <;> simp

/--
theorem `convexBodyLT'_convex` / 定理 `convexBodyLT'_convex`

English:
theorem convexBodyLT'_convex
  statement: Convex Real (convexBodyLT' K f w₀)
  proof: by
  refine Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => ?_))
  split_ifs
  · simp_rw [abs_lt]
    refine Convex.inter ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _))
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  · exact convex_bal

中文:
定理 convexBodyLT'_convex
  结论: Convex 实数 (convexBodyLT' K f w₀)
  证明: by
  refine Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => ?_))
  split_ifs
  · simp_rw [abs_lt]
    refine Convex.inter ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _))
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  · exact convex_bal
-/
theorem convexBodyLT'_convex : Convex Real (convexBodyLT' K f w₀) := by
  refine Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => ?_))
  split_ifs
  · simp_rw [abs_lt]
    refine Convex.inter ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _))
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  · exact convex_ball _ _

open MeasureTheory MeasureTheory.Measure

variable [NumberField K]

/--
Definition of `convexBodyLT'Factor` / `convexBodyLT'Factor` 的定义

English:
abbreviation convexBodyLT'Factor
  signature: : Real>=0
  body: (2 : Real>=0) ^ (nrRealPlaces K + 2) * NNReal.pi ^ (nrComplexPlaces K - 1)

中文:
缩写 convexBodyLT'Factor
  签名: : 实数>=0
  定义体: (2 : Real>=0) ^ (nrRealPlaces K + 2) * NNReal.pi ^ (nrComplexPlaces K - 1)
-/
noncomputable abbrev convexBodyLT'Factor : Real>=0 :=
  (2 : Real>=0) ^ (nrRealPlaces K + 2) * NNReal.pi ^ (nrComplexPlaces K - 1)

/--
theorem `convexBodyLT'Factor_ne_zero` / 定理 `convexBodyLT'Factor_ne_zero`

English:
theorem convexBodyLT'Factor_ne_zero
  statement: convexBodyLT'Factor K != 0
  proof: mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)

中文:
定理 convexBodyLT'Factor_ne_zero
  结论: convexBodyLT'Factor K != 0
  证明: mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)
-/
theorem convexBodyLT'Factor_ne_zero : convexBodyLT'Factor K != 0 :=
  mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)

/--
theorem `one_le_convexBodyLT'Factor` / 定理 `one_le_convexBodyLT'Factor`

English:
theorem one_le_convexBodyLT'Factor
  statement: 1 <= convexBodyLT'Factor K
  proof: one_le_mul (one_le_pow₀ one_le_two) (one_le_pow₀ (one_le_two.trans Real.two_le_pi))

中文:
定理 one_le_convexBodyLT'Factor
  结论: 1 <= convexBodyLT'Factor K
  证明: one_le_mul (one_le_pow₀ one_le_two) (one_le_pow₀ (one_le_two.trans Real.two_le_pi))

Depends on / 依赖: Real.two_le_pi, one_le_mul, one_le_two, one_le_two.trans, two_le_pi
-/
theorem one_le_convexBodyLT'Factor : 1 <= convexBodyLT'Factor K :=
  one_le_mul (one_le_pow₀ one_le_two) (one_le_pow₀ (one_le_two.trans Real.two_le_pi))

open scoped Classical in
/--
theorem `convexBodyLT'_volume` / 定理 `convexBodyLT'_volume`

English:
theorem convexBodyLT'_volume
  proof: by
  have vol_box : forall B : Real>=0, volume {x : Complex | |x.re| < 1 ∧ |x.im| < B ^ 2} = 4 * B ^ 2 := by
    intro B
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage]
    · simp_rw [Set.preimage_ofPred_eq, Complex.measurableEquivRealProd_symm_apply]
      rw [show {a :

中文:
定理 convexBodyLT'_volume
  证明: by
  have vol_box : forall B : Real>=0, volume {x : Complex | |x.re| < 1 ∧ |x.im| < B ^ 2} = 4 * B ^ 2 := by
    intro B
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage]
    · simp_rw [Set.preimage_ofPred_eq, Complex.measurableEquivRealProd_symm_apply]
      rw [show {a :
-/
theorem convexBodyLT'_volume :
    volume (convexBodyLT' K f w₀) = convexBodyLT'Factor K * ∏ w, (f w) ^ (mult w) := by
  have vol_box : forall B : Real>=0, volume {x : Complex | |x.re| < 1 ∧ |x.im| < B ^ 2} = 4 * B ^ 2 := by
    intro B
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage]
    · simp_rw [Set.preimage_ofPred_eq, Complex.measurableEquivRealProd_symm_apply]
      rw [show {a : Real × Real | |a.1| < 1 ∧ |a.2| < B ^ 2} =
        Set.Ioo (-1 : Real) (1 : Real) ×ˢ Set.Ioo (-(B : Real) ^ 2) ((B : Real) ^ 2) by
          ext; simp_rw [Set.mem_ofPred_eq]; rw [Set.mem_prod]; rw [Set.mem_Ioo]; rw [abs_lt]]
      simp_rw [volume_eq_prod, prod_prod, Real.volume_Ioo, sub_neg_eq_add, one_add_one_eq_two,
        ← two_mul, ofReal_mul zero_le_two, ofReal_pow (coe_nonneg B), ofReal_ofNat,
        ofReal_coe_nnreal, ← mul_assoc, show (2 : Real>=0∞) * 2 = 4 by norm_num]
    · refine (MeasurableSet.inter ?_ ?_).nullMeasurableSet
      · exact measurableSet_lt (measurable_norm.comp Complex.measurable_re) measurable_const
      · exact measurableSet_lt (measurable_norm.comp Complex.measurable_im) measurable_const
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ((∏ x in Finset.univ.erase w₀, ENNReal.ofReal (f x.val) ^ 2 * pi) *
          (4 * (f w₀) ^ 2)) := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
      congr 2
      · refine Finset.prod_congr rfl (fun w' hw' => ?_)
        rw [if_neg (Finset.ne_of_mem_erase hw')]; rw [Complex.volume_ball]
      · simpa only [ite_true] using vol_box (f w₀)
    _ = ((2 : Real>=0) ^ nrRealPlaces K *
          (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val))) *
            ((∏ x in Finset.univ.erase w₀, ENNReal.ofReal (f x.val) ^ 2) *
              ↑pi ^ (nrComplexPlaces K - 1) * (4 * (f w₀) ^ 2)) := by
      simp_rw [ofReal_mul (by simp : 0 <= (2 : Real)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ofReal_ofNat,
        ofReal_coe_nnreal, coe_ofNat]
    _ = convexBodyLT'Factor K * (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val))
        * (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) := by
      rw [show (4 : Real>=0∞) = (2 : Real>=0) ^ 2 by norm_num]; rw [convexBodyLT'Factor]; rw [pow_add]; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]; rw [ofReal_coe_nnreal]
      simp_rw [coe_mul, ENNReal.coe_pow]
      ring
    _ = convexBodyLT'Factor K * ∏ w, (f w) ^ (mult w) := by
      simp_rw [prod_eq_prod_mul_prod, coe_mul, ofNNReal_finsetProd, mult_isReal, mult_isComplex,
        pow_one, ENNReal.coe_pow, ofReal_coe_nnreal, mul_assoc]

end convexBodyLT'

section convexBodySum

open ENNReal MeasureTheory Fintype

open scoped Real NNReal

variable [NumberField K] (B : Real)
variable {K}

/--
Definition of `convexBodySumFun` / `convexBodySumFun` 的定义

English:
abbreviation convexBodySumFun
  signature: (x : mixedSpace K)
  body: ∑ w, mult w * normAtPlace w x

中文:
缩写 convexBodySumFun
  签名: (x : mixedSpace K)
  定义体: ∑ w, mult w * normAtPlace w x

Depends on / 依赖: normAtPlace
-/
noncomputable abbrev convexBodySumFun (x : mixedSpace K) : Real := ∑ w, mult w * normAtPlace w x

/--
theorem `convexBodySumFun_apply` / 定理 `convexBodySumFun_apply`

English:
theorem convexBodySumFun_apply
  given: (x : mixedSpace K)
  proof: rfl

中文:
定理 convexBodySumFun_apply
  条件: (x : mixedSpace K)
  证明: rfl
-/
theorem convexBodySumFun_apply (x : mixedSpace K) :
    convexBodySumFun x = ∑ w, mult w * normAtPlace w x := rfl

open scoped Classical in
/--
theorem `convexBodySumFun_apply'` / 定理 `convexBodySumFun_apply'`

English:
theorem convexBodySumFun_apply'
  given: (x : mixedSpace K)
  proof: by
  simp_rw [convexBodySumFun_apply, sum_eq_sum_add_sum, mult_isReal, mult_isComplex,
    Nat.cast_one, one_mul, Nat.cast_ofNat, normAtPlace_apply_of_isReal (Subtype.prop _),
    normAtPlace_apply_of_isComplex (Subtype.prop _), Finset.mul_sum]

中文:
定理 convexBodySumFun_apply'
  条件: (x : mixedSpace K)
  证明: by
  simp_rw [convexBodySumFun_apply, sum_eq_sum_add_sum, mult_isReal, mult_isComplex,
    Nat.cast_one, one_mul, Nat.cast_ofNat, normAtPlace_apply_of_isReal (Subtype.prop _),
    normAtPlace_apply_of_isComplex (Subtype.prop _), Finset.mul_sum]

Depends on / 依赖: Finset, Finset.mul_sum, Nat.cast_ofNat, Nat.cast_one, Subtype, Subtype.prop, cast_ofNat, cast_one, convexBodySumFun_apply, mul_sum, mult_isComplex, mult_isReal, normAtPlace_apply_of_isComplex, normAtPlace_apply_of_isReal, one_mul, simp_rw, sum_eq_sum_add_sum
-/
theorem convexBodySumFun_apply' (x : mixedSpace K) :
    convexBodySumFun x = ∑ w, ‖x.1 w‖ + 2 * ∑ w, ‖x.2 w‖ := by
  simp_rw [convexBodySumFun_apply, sum_eq_sum_add_sum, mult_isReal, mult_isComplex,
    Nat.cast_one, one_mul, Nat.cast_ofNat, normAtPlace_apply_of_isReal (Subtype.prop _),
    normAtPlace_apply_of_isComplex (Subtype.prop _), Finset.mul_sum]

/--
theorem `convexBodySumFun_nonneg` / 定理 `convexBodySumFun_nonneg`

English:
theorem convexBodySumFun_nonneg
  given: (x : mixedSpace K)
  proof: Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _))

中文:
定理 convexBodySumFun_nonneg
  条件: (x : mixedSpace K)
  证明: Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _))

Depends on / 依赖: Finset, Finset.sum_nonneg, Nat.cast_pos.mpr, cast_pos, mul_nonneg, mult_pos, normAtPlace_nonneg, sum_nonneg
-/
theorem convexBodySumFun_nonneg (x : mixedSpace K) :
    0 <= convexBodySumFun x :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _))

/--
theorem `convexBodySumFun_neg` / 定理 `convexBodySumFun_neg`

English:
theorem convexBodySumFun_neg
  given: (x : mixedSpace K)
  proof: by
  simp_rw [convexBodySumFun, normAtPlace_neg]

中文:
定理 convexBodySumFun_neg
  条件: (x : mixedSpace K)
  证明: by
  simp_rw [convexBodySumFun, normAtPlace_neg]

Depends on / 依赖: convexBodySumFun, normAtPlace_neg, simp_rw
-/
theorem convexBodySumFun_neg (x : mixedSpace K) :
    convexBodySumFun (-x) = convexBodySumFun x := by
  simp_rw [convexBodySumFun, normAtPlace_neg]

/--
theorem `convexBodySumFun_add_le` / 定理 `convexBodySumFun_add_le`

English:
theorem convexBodySumFun_add_le
  given: (x y : mixedSpace K)
  proof: by
  simp_rw [convexBodySumFun, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum
    fun _ _ => mul_le_mul_of_nonneg_left (normAtPlace_add_le _ x y) (Nat.cast_pos.mpr mult_pos).le

中文:
定理 convexBodySumFun_add_le
  条件: (x y : mixedSpace K)
  证明: by
  simp_rw [convexBodySumFun, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum
    fun _ _ => mul_le_mul_of_nonneg_left (normAtPlace_add_le _ x y) (Nat.cast_pos.mpr mult_pos).le

Depends on / 依赖: Finset, Finset.sum_add_distrib, Finset.sum_le_sum, Nat.cast_pos.mpr, cast_pos, convexBodySumFun, mul_add, mul_le_mul_of_nonneg_left, mult_pos, normAtPlace_add_le, simp_rw, sum_add_distrib, sum_le_sum
-/
theorem convexBodySumFun_add_le (x y : mixedSpace K) :
    convexBodySumFun (x + y) <= convexBodySumFun x + convexBodySumFun y := by
  simp_rw [convexBodySumFun, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum
    fun _ _ => mul_le_mul_of_nonneg_left (normAtPlace_add_le _ x y) (Nat.cast_pos.mpr mult_pos).le

/--
theorem `convexBodySumFun_smul` / 定理 `convexBodySumFun_smul`

English:
theorem convexBodySumFun_smul
  given: (c : Real) (x : mixedSpace K)
  proof: by
  simp_rw [convexBodySumFun, normAtPlace_smul, ← mul_assoc, mul_comm, Finset.mul_sum, mul_assoc]

中文:
定理 convexBodySumFun_smul
  条件: (c : 实数) (x : mixedSpace K)
  证明: by
  simp_rw [convexBodySumFun, normAtPlace_smul, ← mul_assoc, mul_comm, Finset.mul_sum, mul_assoc]

Depends on / 依赖: Finset, Finset.mul_sum, convexBodySumFun, mul_assoc, mul_comm, mul_sum, normAtPlace_smul, simp_rw
-/
theorem convexBodySumFun_smul (c : Real) (x : mixedSpace K) :
    convexBodySumFun (c • x) = |c| * convexBodySumFun x := by
  simp_rw [convexBodySumFun, normAtPlace_smul, ← mul_assoc, mul_comm, Finset.mul_sum, mul_assoc]

/--
theorem `convexBodySumFun_eq_zero_iff` / 定理 `convexBodySumFun_eq_zero_iff`

English:
theorem convexBodySumFun_eq_zero_iff
  given: (x : mixedSpace K)
  proof: by
  rw [← forall_normAtPlace_eq_zero_iff]; rw [convexBodySumFun]; rw [Finset.sum_eq_zero_iff_of_nonneg
    fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _)]
  simp

中文:
定理 convexBodySumFun_eq_zero_iff
  条件: (x : mixedSpace K)
  证明: by
  rw [← forall_normAtPlace_eq_zero_iff]; rw [convexBodySumFun]; rw [Finset.sum_eq_zero_iff_of_nonneg
    fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _)]
  simp

Depends on / 依赖: Finset, Finset.sum_eq_zero_iff_of_nonneg, Nat.cast_pos.mpr, cast_pos, convexBodySumFun, forall_normAtPlace_eq_zero_iff, mul_nonneg, mult_pos, normAtPlace_nonneg, sum_eq_zero_iff_of_nonneg
-/
theorem convexBodySumFun_eq_zero_iff (x : mixedSpace K) :
    convexBodySumFun x = 0 ↔ x = 0 := by
  rw [← forall_normAtPlace_eq_zero_iff]; rw [convexBodySumFun]; rw [Finset.sum_eq_zero_iff_of_nonneg
    fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _)]
  simp

open scoped Classical in
/--
theorem `norm_le_convexBodySumFun` / 定理 `norm_le_convexBodySumFun`

English:
theorem norm_le_convexBodySumFun
  given: (x : mixedSpace K)
  statement: ‖x‖ <= convexBodySumFun x
  proof: by
  rw [norm_eq_sup'_normAtPlace]
  refine (Finset.sup'_le_iff _ _).mpr fun w _ => ?_
  rw [convexBodySumFun_apply]; rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ w)]
  refine le_add_of_le_of_nonneg ?_ ?_
  · exact le_mul_of_one_le_left (normAtPlace_nonneg w x) one_le_mult
  · exact Finset.sum

中文:
定理 norm_le_convexBodySumFun
  条件: (x : mixedSpace K)
  结论: ‖x‖ <= convexBodySumFun x
  证明: by
  rw [norm_eq_sup'_normAtPlace]
  refine (Finset.sup'_le_iff _ _).mpr fun w _ => ?_
  rw [convexBodySumFun_apply]; rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ w)]
  refine le_add_of_le_of_nonneg ?_ ?_
  · exact le_mul_of_one_le_left (normAtPlace_nonneg w x) one_le_mult
  · exact Finset.sum

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_nonneg, Finset.sup, Finset.univ.add_sum_erase, Nat.cast_pos.mpr, _le_iff, _normAtPlace, add_sum_erase, cast_pos, convexBodySumFun_apply, le_add_of_le_of_nonneg, le_mul_of_one_le_left, mem_univ, mul_nonneg, mult_pos, normAtPlace_nonneg, norm_eq_sup, one_le_mult, sum_nonneg
-/
theorem norm_le_convexBodySumFun (x : mixedSpace K) : ‖x‖ <= convexBodySumFun x := by
  rw [norm_eq_sup'_normAtPlace]
  refine (Finset.sup'_le_iff _ _).mpr fun w _ => ?_
  rw [convexBodySumFun_apply]; rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ w)]
  refine le_add_of_le_of_nonneg ?_ ?_
  · exact le_mul_of_one_le_left (normAtPlace_nonneg w x) one_le_mult
  · exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le
      (normAtPlace_nonneg _ _))

variable (K)

/--
theorem `convexBodySumFun_continuous` / 定理 `convexBodySumFun_continuous`

English:
theorem convexBodySumFun_continuous
  proof: by
  fun_prop

中文:
定理 convexBodySumFun_continuous
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem convexBodySumFun_continuous :
    Continuous (convexBodySumFun : mixedSpace K -> Real) := by
  fun_prop

/--
Definition of `convexBodySum` / `convexBodySum` 的定义

English:
abbreviation convexBodySum
  signature: : Set (mixedSpace K)
  body: { x | convexBodySumFun x <= B }

中文:
缩写 convexBodySum
  签名: : Set (mixedSpace K)
  定义体: { x | convexBodySumFun x <= B }

Depends on / 依赖: Std.Refl.refl, convexBodySumFun
-/
abbrev convexBodySum : Set (mixedSpace K) := { x | convexBodySumFun x <= B }

open scoped Classical in
/--
theorem `convexBodySum_volume_eq_zero_of_le_zero` / 定理 `convexBodySum_volume_eq_zero_of_le_zero`

English:
theorem convexBodySum_volume_eq_zero_of_le_zero
  given: {B} (hB : B <= 0)
  proof: by
  obtain hB | hB := lt_or_eq_of_le hB
  · suffices convexBodySum K B = ∅ by rw [this, measure_empty]
    ext x
    refine ⟨fun hx => ?_, fun h => h.elim⟩
    rw [Set.mem_ofPred] at hx
    linarith [convexBodySumFun_nonneg x]
  · suffices convexBodySum K B = { 0 } by rw [this, measure_singleton]
 

中文:
定理 convexBodySum_volume_eq_zero_of_le_zero
  条件: {B} (hB : B <= 0)
  证明: by
  obtain hB | hB := lt_or_eq_of_le hB
  · suffices convexBodySum K B = ∅ by rw [this, measure_empty]
    ext x
    refine ⟨fun hx => ?_, fun h => h.elim⟩
    rw [Set.mem_ofPred] at hx
    linarith [convexBodySumFun_nonneg x]
  · suffices convexBodySum K B = { 0 } by rw [this, measure_singleton]
 

Depends on / 依赖: Set.mem_ofPred, Set.mem_ofPred_eq, Set.mem_singleton_iff, Std.Symm.symm, convexBodySum, convexBodySumFun_eq_zero_iff, convexBodySumFun_nonneg, ge_iff_eq, h.elim, lt_or_eq_of_le, measure_empty, measure_singleton, mem_ofPred, mem_ofPred_eq, mem_singleton_iff
-/
theorem convexBodySum_volume_eq_zero_of_le_zero {B} (hB : B <= 0) :
    volume (convexBodySum K B) = 0 := by
  obtain hB | hB := lt_or_eq_of_le hB
  · suffices convexBodySum K B = ∅ by rw [this, measure_empty]
    ext x
    refine ⟨fun hx => ?_, fun h => h.elim⟩
    rw [Set.mem_ofPred] at hx
    linarith [convexBodySumFun_nonneg x]
  · suffices convexBodySum K B = { 0 } by rw [this, measure_singleton]
    ext
    rw [convexBodySum]; rw [Set.mem_ofPred_eq]; rw [Set.mem_singleton_iff]; rw [hB]; rw [← convexBodySumFun_eq_zero_iff]
    exact (convexBodySumFun_nonneg _).ge_iff_eq'

/--
theorem `convexBodySum_mem` / 定理 `convexBodySum_mem`

English:
theorem convexBodySum_mem
  given: {x : K}
  proof: by
  simp_rw [Set.mem_ofPred_eq, convexBodySumFun, normAtPlace_apply]
  rfl

中文:
定理 convexBodySum_mem
  条件: {x : K}
  证明: by
  simp_rw [Set.mem_ofPred_eq, convexBodySumFun, normAtPlace_apply]
  rfl

Depends on / 依赖: Set.mem_ofPred_eq, Std.Asymm.asymm, convexBodySumFun, mem_ofPred_eq, normAtPlace_apply, simp_rw
-/
theorem convexBodySum_mem {x : K} :
    mixedEmbedding K x in (convexBodySum K B) ↔
      ∑ w : InfinitePlace K, (mult w) * w.val x <= B := by
  simp_rw [Set.mem_ofPred_eq, convexBodySumFun, normAtPlace_apply]
  rfl

/--
theorem `convexBodySum_neg_mem` / 定理 `convexBodySum_neg_mem`

English:
theorem convexBodySum_neg_mem
  given: {x : mixedSpace K} (hx : x in (convexBodySum K B))
  proof: by
  rw [Set.mem_ofPred]; rw [convexBodySumFun_neg]
  exact hx

中文:
定理 convexBodySum_neg_mem
  条件: {x : mixedSpace K} (hx : x in (convexBodySum K B))
  证明: by
  rw [Set.mem_ofPred]; rw [convexBodySumFun_neg]
  exact hx

Depends on / 依赖: IsTrans, IsTrans.trans, Set.mem_ofPred, convexBodySumFun_neg, mem_ofPred
-/
theorem convexBodySum_neg_mem {x : mixedSpace K} (hx : x in (convexBodySum K B)) :
    -x in (convexBodySum K B) := by
  rw [Set.mem_ofPred]; rw [convexBodySumFun_neg]
  exact hx

/--
theorem `convexBodySum_convex` / 定理 `convexBodySum_convex`

English:
theorem convexBodySum_convex
  statement: Convex Real (convexBodySum K B)
  proof: by
  refine Convex_subadditive_le (fun _ _ => convexBodySumFun_add_le _ _) (fun c x h => ?_) B
  convert! le_of_eq (convexBodySumFun_smul c x)
  exact (abs_eq_self.mpr h).symm

中文:
定理 convexBodySum_convex
  结论: Convex 实数 (convexBodySum K B)
  证明: by
  refine Convex_subadditive_le (fun _ _ => convexBodySumFun_add_le _ _) (fun c x h => ?_) B
  convert! le_of_eq (convexBodySumFun_smul c x)
  exact (abs_eq_self.mpr h).symm

Depends on / 依赖: Convex_subadditive_le, Irrefl, Std.Irrefl.irrefl, abs_eq_self, abs_eq_self.mpr, convert, convexBodySumFun_add_le, convexBodySumFun_smul, irrefl, le_of_eq
-/
theorem convexBodySum_convex : Convex Real (convexBodySum K B) := by
  refine Convex_subadditive_le (fun _ _ => convexBodySumFun_add_le _ _) (fun c x h => ?_) B
  convert! le_of_eq (convexBodySumFun_smul c x)
  exact (abs_eq_self.mpr h).symm

/--
theorem `convexBodySum_isBounded` / 定理 `convexBodySum_isBounded`

English:
theorem convexBodySum_isBounded
  statement: Bornology.IsBounded (convexBodySum K B)
  proof: by
  classical
  refine Metric.isBounded_iff.mpr ⟨B + B, fun x hx y hy => ?_⟩
  simp_rw [dist_eq_norm]
  refine le_trans (norm_sub_le x y) (add_le_add ?_ ?_)
  · exact le_trans (norm_le_convexBodySumFun x) hx
  · exact le_trans (norm_le_convexBodySumFun y) hy

中文:
定理 convexBodySum_isBounded
  结论: Bornology.IsBounded (convexBodySum K B)
  证明: by
  classical
  refine Metric.isBounded_iff.mpr ⟨B + B, fun x hx y hy => ?_⟩
  simp_rw [dist_eq_norm]
  refine le_trans (norm_sub_le x y) (add_le_add ?_ ?_)
  · exact le_trans (norm_le_convexBodySumFun x) hx
  · exact le_trans (norm_le_convexBodySumFun y) hy

Depends on / 依赖: Metric, Metric.isBounded_iff.mpr, Std.Trichotomous.trichotomous, Subtype, Subtype.ext_iff, Trichotomous, add_le_add, classical, dist_eq_norm, ext_iff, isBounded_iff, le_trans, norm_le_convexBodySumFun, norm_sub_le, simp_rw, trichotomous
-/
theorem convexBodySum_isBounded : Bornology.IsBounded (convexBodySum K B) := by
  classical
  refine Metric.isBounded_iff.mpr ⟨B + B, fun x hx y hy => ?_⟩
  simp_rw [dist_eq_norm]
  refine le_trans (norm_sub_le x y) (add_le_add ?_ ?_)
  · exact le_trans (norm_le_convexBodySumFun x) hx
  · exact le_trans (norm_le_convexBodySumFun y) hy

/--
theorem `convexBodySum_compact` / 定理 `convexBodySum_compact`

English:
theorem convexBodySum_compact
  statement: IsCompact (convexBodySum K B)
  proof: by
  classical
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, convexBodySum_isBounded K B⟩
  convert! IsClosed.preimage (convexBodySumFun_continuous K) (isClosed_Icc : IsClosed (Set.Icc 0 B))
  ext
  simp [convexBodySumFun_nonneg]

中文:
定理 convexBodySum_compact
  结论: IsCompact (convexBodySum K B)
  证明: by
  classical
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, convexBodySum_isBounded K B⟩
  convert! IsClosed.preimage (convexBodySumFun_continuous K) (isClosed_Icc : IsClosed (Set.Icc 0 B))
  ext
  simp [convexBodySumFun_nonneg]

Depends on / 依赖: IsClosed, IsClosed.preimage, Metric, Metric.isCompact_iff_isClosed_bounded, Set.Icc, Subrel, Subrel.relEmbedding, classical, convert, convexBodySumFun_continuous, convexBodySumFun_nonneg, convexBodySum_isBounded, isClosed_Icc, isCompact_iff_isClosed_bounded, isWellFounded, preimage, relEmbedding
-/
theorem convexBodySum_compact : IsCompact (convexBodySum K B) := by
  classical
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, convexBodySum_isBounded K B⟩
  convert! IsClosed.preimage (convexBodySumFun_continuous K) (isClosed_Icc : IsClosed (Set.Icc 0 B))
  ext
  simp [convexBodySumFun_nonneg]

/--
Definition of `convexBodySumFactor` / `convexBodySumFactor` 的定义

English:
abbreviation convexBodySumFactor
  signature: : Real>=0
  body: (2 : Real>=0) ^ nrRealPlaces K * (NNReal.pi / 2) ^ nrComplexPlaces K / (finrank Rat K).factorial

中文:
缩写 convexBodySumFactor
  签名: : 实数>=0
  定义体: (2 : Real>=0) ^ nrRealPlaces K * (NNReal.pi / 2) ^ nrComplexPlaces K / (finrank Rat K).factorial

Depends on / 依赖: NNReal, NNReal.pi, factorial, finrank, nrComplexPlaces, nrRealPlaces
-/
noncomputable abbrev convexBodySumFactor : Real>=0 :=
  (2 : Real>=0) ^ nrRealPlaces K * (NNReal.pi / 2) ^ nrComplexPlaces K / (finrank Rat K).factorial

/--
theorem `convexBodySumFactor_ne_zero` / 定理 `convexBodySumFactor_ne_zero`

English:
theorem convexBodySumFactor_ne_zero
  statement: convexBodySumFactor K != 0
  proof: by
refine div_ne_zero ?_ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
    (pow_ne_zero _ (div_ne_zero NNReal.pi_ne_zero two_ne_zero))

中文:
定理 convexBodySumFactor_ne_zero
  结论: convexBodySumFactor K != 0
  证明: by
refine div_ne_zero ?_ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
    (pow_ne_zero _ (div_ne_zero NNReal.pi_ne_zero two_ne_zero))

Depends on / 依赖: NNReal, NNReal.pi_ne_zero, Nat.cast_ne_zero.mpr, Nat.factorial_ne_zero, cast_ne_zero, div_ne_zero, factorial_ne_zero, mul_ne_zero, pi_ne_zero, pow_ne_zero, two_ne_zero
-/
theorem convexBodySumFactor_ne_zero : convexBodySumFactor K != 0 := by
refine div_ne_zero ?_ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
    (pow_ne_zero _ (div_ne_zero NNReal.pi_ne_zero two_ne_zero))

open MeasureTheory MeasureTheory.Measure Real in
open scoped Classical in
/--
theorem `convexBodySum_volume` / 定理 `convexBodySum_volume`

English:
theorem convexBodySum_volume
  proof: by
  obtain hB | hB := le_or_gt B 0
  · rw [convexBodySum_volume_eq_zero_of_le_zero K hB, ofReal_eq_zero.mpr hB, zero_pow, mul_zero]
    exact finrank_pos.ne'
  · suffices volume (convexBodySum K 1) = (convexBodySumFactor K) by
      rw [mul_comm]
      convert! addHaar_smul volume B (convexBodySum 

中文:
定理 convexBodySum_volume
  证明: by
  obtain hB | hB := le_or_gt B 0
  · rw [convexBodySum_volume_eq_zero_of_le_zero K hB, ofReal_eq_zero.mpr hB, zero_pow, mul_zero]
    exact finrank_pos.ne'
  · suffices volume (convexBodySum K 1) = (convexBodySumFactor K) by
      rw [mul_comm]
      convert! addHaar_smul volume B (convexBodySum 

Depends on / 依赖: Finset, Finset.mul_sum, Set.preimage_ofPred_eq, Set.preimage_smul_inv, abs_eq_self, abs_eq_self.mpr, abs_inv, addHaar_smul, convert, convexBodySum, convexBodySumFactor, convexBodySumFun, convexBodySum_volume_eq_zero_of_le_zero, finrank_pos, finrank_pos.ne, inv_mul_le_iff, le_of_lt, le_or_gt, mul_assoc, mul_comm
-/
theorem convexBodySum_volume :
    volume (convexBodySum K B) = (convexBodySumFactor K) * (.ofReal B) ^ (finrank Rat K) := by
  obtain hB | hB := le_or_gt B 0
  · rw [convexBodySum_volume_eq_zero_of_le_zero K hB, ofReal_eq_zero.mpr hB, zero_pow, mul_zero]
    exact finrank_pos.ne'
  · suffices volume (convexBodySum K 1) = (convexBodySumFactor K) by
      rw [mul_comm]
      convert! addHaar_smul volume B (convexBodySum K 1)
      · simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hB), Set.preimage_ofPred_eq, convexBodySumFun,
        normAtPlace_smul, abs_inv, abs_eq_self.mpr (le_of_lt hB), ← mul_assoc, mul_comm, mul_assoc,
        ← Finset.mul_sum, inv_mul_le_iff₀ hB, mul_one]
      · rw [abs_pow, ofReal_pow (abs_nonneg _), abs_eq_self.mpr (le_of_lt hB),
          mixedEmbedding.finrank]
      · exact this.symm
    rw [MeasureTheory.measure_le_eq_lt _ ((convexBodySumFun_eq_zero_iff 0).mpr rfl)
      convexBodySumFun_neg convexBodySumFun_add_le
      (fun hx => (convexBodySumFun_eq_zero_iff _).mp hx)
      (fun r x => le_of_eq (convexBodySumFun_smul r x))]
    rw [measure_lt_one_eq_integral_div_gamma (g := fun x : (mixedSpace K) => convexBodySumFun x)
      volume ((convexBodySumFun_eq_zero_iff 0).mpr rfl) convexBodySumFun_neg convexBodySumFun_add_le
      (fun hx => (convexBodySumFun_eq_zero_iff _).mp hx)
      (fun r x => le_of_eq (convexBodySumFun_smul r x)) zero_lt_one]
    simp_rw [mixedEmbedding.finrank, div_one, Gamma_nat_eq_factorial, ofReal_div_of_pos
      (Nat.cast_pos.mpr (Nat.factorial_pos _)), Real.rpow_one, ofReal_natCast]
    suffices ∫ x : mixedSpace K, exp (-convexBodySumFun x) =
        (2 : Real) ^ nrRealPlaces K * (π / 2) ^ nrComplexPlaces K by
      rw [this]; rw [convexBodySumFactor]; rw [ofReal_mul (by positivity)]; rw [ofReal_pow zero_le_two]; rw [ofReal_pow (by positivity)]; rw [ofReal_div_of_pos zero_lt_two]; rw [ofReal_ofNat]; rw [← NNReal.coe_real_pi]; rw [ofReal_coe_nnreal]; rw [coe_div (Nat.cast_ne_zero.mpr
        (Nat.factorial_ne_zero _))]; rw [coe_mul]; rw [coe_pow]; rw [coe_pow]; rw [coe_ofNat]; rw [coe_div two_ne_zero]; rw [coe_ofNat]; rw [coe_natCast]
    calc
      _ = (∫ x : {w : InfinitePlace K // IsReal w} -> Real, ∏ w, exp (-‖x w‖)) *
              (∫ x : {w : InfinitePlace K // IsComplex w} -> Complex, ∏ w, exp (-2 * ‖x w‖)) := by
        simp_rw [convexBodySumFun_apply', neg_add, ← neg_mul, Finset.mul_sum,
          ← Finset.sum_neg_distrib, exp_add, exp_sum, ← integral_prod_mul, volume_eq_prod]
      _ = (∫ x : Real, exp (-|x|)) ^ nrRealPlaces K *
              (∫ x : Complex, Real.exp (-2 * ‖x‖)) ^ nrComplexPlaces K := by
        rw [integral_fintype_prod_volume_eq_pow (fun x => exp (-‖x‖))]; rw [integral_fintype_prod_volume_eq_pow (fun x => exp (-2 * ‖x‖))]
        simp_rw [norm_eq_abs]
      _ = (2 * Gamma (1 / 1 + 1)) ^ nrRealPlaces K *
              (π * (2 : Real) ^ (-(2 : Real) / 1) * Gamma (2 / 1 + 1)) ^ nrComplexPlaces K := by
        rw [integral_comp_abs (f := fun x => exp (-x))]; rw [← integral_exp_neg_rpow zero_lt_one]; rw [← Complex.integral_exp_neg_mul_rpow le_rfl zero_lt_two]
        simp_rw [Real.rpow_one]
      _ = (2 : Real) ^ nrRealPlaces K * (π / 2) ^ nrComplexPlaces K := by
        simp_rw [div_one, one_add_one_eq_two, Gamma_add_one two_ne_zero, Gamma_two, mul_one,
          mul_assoc, ← Real.rpow_add_one two_ne_zero, show (-2 : Real) + 1 = -1 by norm_num,
          Real.rpow_neg_one, div_eq_mul_inv]

end convexBodySum

section minkowski

open MeasureTheory MeasureTheory.Measure Module ZSpan Real Submodule

open scoped ENNReal NNReal nonZeroDivisors IntermediateField

variable [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

open scoped Classical in
/--
Definition of `minkowskiBound` / `minkowskiBound` 的定义

English:
definition minkowskiBound
  signature: : Real>=0∞
  body: volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) *
    (2 : Real>=0∞) ^ (finrank Real (mixedSpace K))

中文:
定义 minkowskiBound
  签名: : 实数>=0∞
  定义体: volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) *
    (2 : Real>=0∞) ^ (finrank Real (mixedSpace K))

Depends on / 依赖: finrank, fractionalIdealLatticeBasis, fundamentalDomain, mixedSpace, volume
-/
noncomputable def minkowskiBound : Real>=0∞ :=
  volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) *
    (2 : Real>=0∞) ^ (finrank Real (mixedSpace K))

open scoped Classical in
/--
theorem `volume_fundamentalDomain_fractionalIdealLatticeBasis` / 定理 `volume_fundamentalDomain_fractionalIdealLatticeBasis`

English:
theorem volume_fundamentalDomain_fractionalIdealLatticeBasis
  proof: by
  let e : (Module.Free.ChooseBasisIndex Int I) ≃ (Module.Free.ChooseBasisIndex Int (𝓞 K)) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [← finrank_eq_card_chooseBasisIndex]; rw [fractionalIdeal_rank]
  rw [← fundamentalDomain_reindex (fractionalIdealLat

中文:
定理 volume_fundamentalDomain_fractionalIdealLatticeBasis
  证明: by
  let e : (Module.Free.ChooseBasisIndex Int I) ≃ (Module.Free.ChooseBasisIndex Int (𝓞 K)) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [← finrank_eq_card_chooseBasisIndex]; rw [fractionalIdeal_rank]
  rw [← fundamentalDomain_reindex (fractionalIdealLat

Depends on / 依赖: ChooseBasisIndex, Fintype, Fintype.equivOfCardEq, Module, Module.Free.ChooseBasisIndex, basisOfFractionalIdeal, e.symm, equivOfCardEq, finrank_eq_card_chooseBasisIndex, fractionalIdealLatticeBasis, fractionalIdeal_rank, fundamentalDomain_reindex, measure_fundamentalDomain, mixedEmbedding, reindex
-/
theorem volume_fundamentalDomain_fractionalIdealLatticeBasis :
    volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) =
      .ofReal (FractionalIdeal.absNorm I.1) * volume (fundamentalDomain (latticeBasis K)) := by
  let e : (Module.Free.ChooseBasisIndex Int I) ≃ (Module.Free.ChooseBasisIndex Int (𝓞 K)) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex]; rw [← finrank_eq_card_chooseBasisIndex]; rw [fractionalIdeal_rank]
  rw [← fundamentalDomain_reindex (fractionalIdealLatticeBasis K I) e]; rw [measure_fundamentalDomain ((fractionalIdealLatticeBasis K I).reindex e)]
  · rw [show (fractionalIdealLatticeBasis K I).reindex e = (mixedEmbedding K) ∘
        (basisOfFractionalIdeal K I) ∘ e.symm by
      ext1; simp only [Basis.coe_reindex, Function.comp_apply, fractionalIdealLatticeBasis_apply]]
    rw [mixedEmbedding.det_basisOfFractionalIdeal_eq_norm]

/--
theorem `minkowskiBound_lt_top` / 定理 `minkowskiBound_lt_top`

English:
theorem minkowskiBound_lt_top
  statement: minkowskiBound K I < ⊤
  proof: by
  classical
  -- FIXME: Make `finiteness` work here
exact ENNReal.mul_lt_top (fundamentalDomain_isBounded _).measure_lt_top
    ENNReal.pow_lt_top ENNReal.ofNat_lt_top

中文:
定理 minkowskiBound_lt_top
  结论: minkowskiBound K I < ⊤
  证明: by
  classical
  -- FIXME: Make `finiteness` work here
exact ENNReal.mul_lt_top (fundamentalDomain_isBounded _).measure_lt_top
    ENNReal.pow_lt_top ENNReal.ofNat_lt_top

Depends on / 依赖: classical
-/
theorem minkowskiBound_lt_top : minkowskiBound K I < ⊤ := by
  classical
  -- FIXME: Make `finiteness` work here
exact ENNReal.mul_lt_top (fundamentalDomain_isBounded _).measure_lt_top
    ENNReal.pow_lt_top ENNReal.ofNat_lt_top

/--
theorem `minkowskiBound_pos` / 定理 `minkowskiBound_pos`

English:
theorem minkowskiBound_pos
  statement: 0 < minkowskiBound K I
  proof: -- TODO: The `NormedAddCommGroup (mixedSpace K)` instance should not need any decidability.
ENNReal.mul_pos (by classical exact ZSpan.measure_fundamentalDomain_ne_zero _)
    ENNReal.pow_ne_zero two_ne_zero _

中文:
定理 minkowskiBound_pos
  结论: 0 < minkowskiBound K I
  证明: -- TODO: The `NormedAddCommGroup (mixedSpace K)` instance should not need any decidability.
ENNReal.mul_pos (by classical exact ZSpan.measure_fundamentalDomain_ne_zero _)
    ENNReal.pow_ne_zero two_ne_zero _
-/
theorem minkowskiBound_pos : 0 < minkowskiBound K I :=
  -- TODO: The `NormedAddCommGroup (mixedSpace K)` instance should not need any decidability.
ENNReal.mul_pos (by classical exact ZSpan.measure_fundamentalDomain_ne_zero _)
    ENNReal.pow_ne_zero two_ne_zero _

variable {f : InfinitePlace K -> Real>=0} (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

open scoped Classical in
/--
theorem `exists_ne_zero_mem_ideal_lt` / 定理 `exists_ne_zero_mem_ideal_lt`

English:
theorem exists_ne_zero_mem_ideal_lt
  given: (h : minkowskiBound K I < volume (convexBodyLT K f))
  proof: by
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span Int (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span Int (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx

中文:
定理 exists_ne_zero_mem_ideal_lt
  条件: (h : minkowskiBound K I < volume (convexBodyLT K f))
  证明: by
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span Int (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span Int (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx

Depends on / 依赖: Countable, Set.range, ZSpan.isAddFundamentalDomain, convexBodyLT_convex, convexBodyLT_neg_mem, exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure, fractionalIdealLatticeBasis, h_fund, h_mem, h_nz, infer_instance, isAddFundamentalDomain, mem_span_fractionalIdealLatticeBasis, mem_toAddSubgroup, toAddSubgroup, volume
-/
theorem exists_ne_zero_mem_ideal_lt (h : minkowskiBound K I < volume (convexBodyLT K f)) :
    exists a in (I : FractionalIdeal (𝓞 K)⁰ K), a != 0 ∧ forall w : InfinitePlace K, w a < f w := by
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span Int (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span Int (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_fund (convexBodyLT_neg_mem K f) (convexBodyLT_convex K f) h
  rw [mem_toAddSubgroup]; rw [mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, by simpa using h_nz, (convexBodyLT_mem K f).mp h_mem⟩

open scoped Classical in
/--
theorem `exists_ne_zero_mem_ideal_lt'` / 定理 `exists_ne_zero_mem_ideal_lt'`

English:
theorem exists_ne_zero_mem_ideal_lt'
  statement: (w₀ : {w : InfinitePlace K // IsComplex w})
  proof: by
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span Int (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span Int (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx

中文:
定理 exists_ne_zero_mem_ideal_lt'
  结论: (w₀ : {w : InfinitePlace K // IsComplex w})
  证明: by
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span Int (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span Int (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx

Depends on / 依赖: Countable, Set.range, ZSpan.isAddFundamentalDomain, _convex, _neg_mem, convexBodyLT, exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure, fractionalIdealLatticeBasis, h_fund, h_mem, h_nz, infer_instance, isAddFundamentalDomain, mem_span_fractionalIdealLatticeBasis, mem_toAddSubgroup, toAddSubgroup, volume
-/
theorem exists_ne_zero_mem_ideal_lt' (w₀ : {w : InfinitePlace K // IsComplex w})
    (h : minkowskiBound K I < volume (convexBodyLT' K f w₀)) :
    exists a in (I : FractionalIdeal (𝓞 K)⁰ K), a != 0 ∧ (forall w : InfinitePlace K, w != w₀ -> w a < f w) ∧
      |(w₀.val.embedding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : Real) ^ 2 := by
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span Int (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span Int (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_fund (convexBodyLT'_neg_mem K f w₀) (convexBodyLT'_convex K f w₀) h
  rw [mem_toAddSubgroup]; rw [mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, by simpa using h_nz, (convexBodyLT'_mem K f w₀).mp h_mem⟩

open scoped Classical in
/--
theorem `exists_ne_zero_mem_ringOfIntegers_lt` / 定理 `exists_ne_zero_mem_ringOfIntegers_lt`

English:
theorem exists_ne_zero_mem_ringOfIntegers_lt
  given: (h : minkowskiBound K ↑1 < volume (convexBodyLT K f))
  proof: by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

中文:
定理 exists_ne_zero_mem_ringOfIntegers_lt
  条件: (h : minkowskiBound K ↑1 < volume (convexBodyLT K f))
  证明: by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

Depends on / 依赖: FractionalIdeal, FractionalIdeal.mem_one_iff, RingOfIntegers, RingOfIntegers.coe_ne_zero_iff.mp, coe_ne_zero_iff, exists_ne_zero_mem_ideal_lt, h_bd, h_mem, h_nz, mem_one_iff
-/
theorem exists_ne_zero_mem_ringOfIntegers_lt (h : minkowskiBound K ↑1 < volume (convexBodyLT K f)) :
    exists a : 𝓞 K, a != 0 ∧ forall w : InfinitePlace K, w a < f w := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

open scoped Classical in
/--
theorem `exists_ne_zero_mem_ringOfIntegers_lt'` / 定理 `exists_ne_zero_mem_ringOfIntegers_lt'`

English:
theorem exists_ne_zero_mem_ringOfIntegers_lt'
  statement: (w₀ : {w : InfinitePlace K // IsComplex w})
  proof: by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt' K ↑1 w₀ h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

中文:
定理 exists_ne_zero_mem_ringOfIntegers_lt'
  结论: (w₀ : {w : InfinitePlace K // IsComplex w})
  证明: by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt' K ↑1 w₀ h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

Depends on / 依赖: FractionalIdeal, FractionalIdeal.mem_one_iff, RingOfIntegers, RingOfIntegers.coe_ne_zero_iff.mp, coe_ne_zero_iff, exists_ne_zero_mem_ideal_lt, h_bd, h_mem, h_nz, mem_one_iff
-/
theorem exists_ne_zero_mem_ringOfIntegers_lt' (w₀ : {w : InfinitePlace K // IsComplex w})
    (h : minkowskiBound K ↑1 < volume (convexBodyLT' K f w₀)) :
    exists a : 𝓞 K, a != 0 ∧ (forall w : InfinitePlace K, w != w₀ -> w a < f w) ∧
      |(w₀.val.embedding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : Real) ^ 2 := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt' K ↑1 w₀ h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

/--
theorem `exists_primitive_element_lt_of_isReal` / 定理 `exists_primitive_element_lt_of_isReal`

English:
theorem exists_primitive_element_lt_of_isReal
  statement: {w₀ : InfinitePlace K} (hw₀ : IsReal w₀) {B : Real>=0}
  proof: by
  classical
  have : minkowskiBound K ↑1 < volume (convexBodyLT K (fun w => if w = w₀ then B else 1)) := by
    rw [convexBodyLT_volume]; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.notMem_erase, ite_false, 

中文:
定理 exists_primitive_element_lt_of_isReal
  结论: {w₀ : InfinitePlace K} (hw₀ : Is实数 w₀) {B : 实数>=0}
  证明: by
  classical
  have : minkowskiBound K ↑1 < volume (convexBodyLT K (fun w => if w = w₀ then B else 1)) := by
    rw [convexBodyLT_volume]; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.notMem_erase, ite_false, 

Depends on / 依赖: Finset, Finset.mem_univ, Finset.notMem_erase, Finset.prod_erase_mul, Finset.prod_ite_eq, classical, convexBodyLT, convexBodyLT_volume, exists_ne_zero_mem_ringOfIntegers_lt, h_le, h_nz, is_primitive_element_of_infinitePlace_lt, ite_false, ite_pow, ite_true, lt_of_lt_of_le, mem_univ, minkowskiBound, notMem_erase, one_mul
-/
theorem exists_primitive_element_lt_of_isReal {w₀ : InfinitePlace K} (hw₀ : IsReal w₀) {B : Real>=0}
    (hB : minkowskiBound K ↑1 < convexBodyLTFactor K * B) :
    exists a : 𝓞 K, Rat⟮(a : K)⟯ = ⊤ ∧
      forall w : InfinitePlace K, w a < max B 1 := by
  classical
  have : minkowskiBound K ↑1 < volume (convexBodyLT K (fun w => if w = w₀ then B else 1)) := by
    rw [convexBodyLT_volume]; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.notMem_erase, ite_false, mult, hw₀, ite_true, one_mul, pow_one]
    exact hB
  obtain ⟨a, h_nz, h_le⟩ := exists_ne_zero_mem_ringOfIntegers_lt K this
  refine ⟨a, ?_, fun w => lt_of_lt_of_le (h_le w) ?_⟩
  · exact is_primitive_element_of_infinitePlace_lt h_nz
      (fun w h_ne => by convert! (if_neg h_ne) ▸ h_le w) (Or.inl hw₀)
  · split_ifs <;> simp

/--
theorem `exists_primitive_element_lt_of_isComplex` / 定理 `exists_primitive_element_lt_of_isComplex`

English:
theorem exists_primitive_element_lt_of_isComplex
  statement: {w₀ : InfinitePlace K} (hw₀ : IsComplex w₀)
  proof: by
  classical
  have : minkowskiBound K ↑1 <
      volume (convexBodyLT' K (fun w => if w = w₀ then NNReal.sqrt B else 1) ⟨w₀, hw₀⟩) := by
    rw [convexBodyLT'_volume]; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Fi

中文:
定理 exists_primitive_element_lt_of_isComplex
  结论: {w₀ : InfinitePlace K} (hw₀ : IsComplex w₀)
  证明: by
  classical
  have : minkowskiBound K ↑1 <
      volume (convexBodyLT' K (fun w => if w = w₀ then NNReal.sqrt B else 1) ⟨w₀, hw₀⟩) := by
    rw [convexBodyLT'_volume]; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Fi

Depends on / 依赖: Finset, Finset.mem_univ, Finset.notMem_erase, Finset.prod_erase_mul, Finset.prod_ite_eq, NNReal, NNReal.sq_sqrt, NNReal.sqrt, _volume, classical, convexBodyLT, exists_ne_zero_mem_ringOfIntegers_lt, h_le, h_nz, ite_false, ite_pow, ite_true, mem_univ, minkowskiBound, notMem_erase
-/
theorem exists_primitive_element_lt_of_isComplex {w₀ : InfinitePlace K} (hw₀ : IsComplex w₀)
    {B : Real>=0} (hB : minkowskiBound K ↑1 < convexBodyLT'Factor K * B) :
    exists a : 𝓞 K, Rat⟮(a : K)⟯ = ⊤ ∧
      forall w : InfinitePlace K, w a < Real.sqrt (1 + B ^ 2) := by
  classical
  have : minkowskiBound K ↑1 <
      volume (convexBodyLT' K (fun w => if w = w₀ then NNReal.sqrt B else 1) ⟨w₀, hw₀⟩) := by
    rw [convexBodyLT'_volume]; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.notMem_erase, ite_false, mult, not_isReal_iff_isComplex.mpr hw₀,
      ite_true, ite_false, one_mul, NNReal.sq_sqrt]
    exact hB
  obtain ⟨a, h_nz, h_le, h_le₀⟩ := exists_ne_zero_mem_ringOfIntegers_lt' K ⟨w₀, hw₀⟩ this
  refine ⟨a, ?_, fun w => ?_⟩
  · exact is_primitive_element_of_infinitePlace_lt h_nz
      (fun w h_ne => by convert! if_neg h_ne ▸ h_le w h_ne) (Or.inr h_le₀.1)
  · by_cases h_eq : w = w₀
    · rw [if_pos rfl] at h_le₀
      dsimp only at h_le₀
      rw [h_eq]; rw [← norm_embedding_eq]; rw [Real.lt_sqrt (norm_nonneg _)]; rw [← Complex.re_add_im
        (embedding w₀ _)]; rw [Complex.norm_add_mul_I]; rw [Real.sq_sqrt (by positivity)]
      refine add_lt_add ?_ ?_
      · rw [← sq_abs, sq_lt_one_iff₀ (abs_nonneg _)]
        exact h_le₀.1
      · rw [sq_lt_sq, NNReal.abs_eq, ← NNReal.sq_sqrt B]
        exact h_le₀.2
    · refine lt_of_lt_of_le (if_neg h_eq ▸ h_le w h_eq) ?_
      rw [NNReal.coe_one]; rw [Real.le_sqrt' zero_lt_one]; rw [one_pow]
      norm_num

open scoped Classical in
/--
theorem `exists_ne_zero_mem_ideal_of_norm_le` / 定理 `exists_ne_zero_mem_ideal_of_norm_le`

English:
theorem exists_ne_zero_mem_ideal_of_norm_le
  statement: {B : Real}
  proof: by
  have hB : 0 <= B := by
    contrapose! h
    rw [convexBodySum_volume_eq_zero_of_le_zero K (le_of_lt h)]
    exact minkowskiBound_pos K I
  -- Some inequalities that will be useful later on
  have h1 : 0 < (finrank Rat K : Real)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr finrank_pos)
  have h2 : 0 <= B

中文:
定理 exists_ne_zero_mem_ideal_of_norm_le
  结论: {B : 实数}
  证明: by
  have hB : 0 <= B := by
    contrapose! h
    rw [convexBodySum_volume_eq_zero_of_le_zero K (le_of_lt h)]
    exact minkowskiBound_pos K I
  -- Some inequalities that will be useful later on
  have h1 : 0 < (finrank Rat K : Real)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr finrank_pos)
  have h2 : 0 <= B

Depends on / 依赖: contrapose, convexBodySum_volume_eq_zero_of_le_zero, le_of_lt, minkowskiBound_pos
-/
theorem exists_ne_zero_mem_ideal_of_norm_le {B : Real}
    (h : (minkowskiBound K I) <= volume (convexBodySum K B)) :
    exists a in (I : FractionalIdeal (𝓞 K)⁰ K), a != 0 ∧
      |Algebra.norm Rat (a : K)| <= (B / finrank Rat K) ^ finrank Rat K := by
  have hB : 0 <= B := by
    contrapose! h
    rw [convexBodySum_volume_eq_zero_of_le_zero K (le_of_lt h)]
    exact minkowskiBound_pos K I
  -- Some inequalities that will be useful later on
  have h1 : 0 < (finrank Rat K : Real)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr finrank_pos)
  have h2 : 0 <= B / (finrank Rat K) := div_nonneg hB (Nat.cast_nonneg _)
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span Int (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span Int (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      h_fund (fun _ => convexBodySum_neg_mem K B) (convexBodySum_convex K B)
      (convexBodySum_compact K B) h
  rw [mem_toAddSubgroup]; rw [mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, by simpa using h_nz, ?_⟩
  rw [← rpow_natCast]; rw [← rpow_le_rpow_iff (by simp only [Rat.cast_abs]; rw [abs_nonneg])
      (rpow_nonneg h2 _) h1, ← rpow_mul h2, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr
      (ne_of_gt finrank_pos)), rpow_one, le_div_iff₀' (Nat.cast_pos.mpr finrank_pos)]
  refine le_trans ?_ ((convexBodySum_mem K B).mp h_mem)
  rw [← le_div_iff₀' (Nat.cast_pos.mpr finrank_pos)]; rw [← sum_mult_eq]; rw [Nat.cast_sum]
  refine le_trans ?_ (geom_mean_le_arith_mean Finset.univ _ _ (fun _ _ => Nat.cast_nonneg _)
    ?_ (fun _ _ => AbsoluteValue.nonneg _ _))
  · simp_rw [← prod_eq_abs_norm, rpow_natCast]
    exact le_of_eq rfl
  · rw [← Nat.cast_sum, sum_mult_eq, Nat.cast_pos]
    exact finrank_pos

open scoped Classical in
/--
theorem `exists_ne_zero_mem_ringOfIntegers_of_norm_le` / 定理 `exists_ne_zero_mem_ringOfIntegers_of_norm_le`

English:
theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le
  statement: {B : Real}
  proof: by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_of_norm_le K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

中文:
定理 exists_ne_zero_mem_ringOfIntegers_of_norm_le
  结论: {B : 实数}
  证明: by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_of_norm_le K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

Depends on / 依赖: FractionalIdeal, FractionalIdeal.mem_one_iff, RingOfIntegers, RingOfIntegers.coe_ne_zero_iff.mp, coe_ne_zero_iff, exists_ne_zero_mem_ideal_of_norm_le, h_bd, h_mem, h_nz, mem_one_iff
-/
theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le {B : Real}
    (h : (minkowskiBound K ↑1) <= volume (convexBodySum K B)) :
    exists a : 𝓞 K, a != 0 ∧ |Algebra.norm Rat (a : K)| <= (B / finrank Rat K) ^ finrank Rat K := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_of_norm_le K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

end minkowski

end NumberField.mixedEmbedding
