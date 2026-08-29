/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Instances.RealVectorSpace

/-! # Further lemmas about `RCLike` -/

public section

open scoped Finset

variable {K E : Type*} [RCLike K]

open ComplexOrder RCLike in
/--
lemma `convex_RCLike_iff_convex_real` / 引理 `convex_RCLike_iff_convex_real`

English:
lemma convex_RCLike_iff_convex_real
  statement: [AddCommMonoid E] [Module K E] [Module Real E]
  proof: ⟨Convex.lift Real,
  fun hs => convex_of_nonneg_surjective_algebraMap _ (fun _ => nonneg_iff_exists_ofReal.mp) hs⟩

中文:
引理 convex_RCLike_iff_convex_real
  结论: [加法交换幺半群 E] [模 K E] [模 实数 E]
  证明: ⟨Convex.lift Real,
  fun hs => convex_of_nonneg_surjective_algebraMap _ (fun _ => nonneg_iff_exists_ofReal.mp) hs⟩

Depends on / 依赖: Convex, Convex.lift, convex_of_nonneg_surjective_algebraMap, nonneg_iff_exists_ofReal, nonneg_iff_exists_ofReal.mp
-/
lemma convex_RCLike_iff_convex_real [AddCommMonoid E] [Module K E] [Module Real E]
    [IsScalarTower Real K E] {s : Set E} : Convex K s ↔ Convex Real s :=
  ⟨Convex.lift Real,
  fun hs => convex_of_nonneg_surjective_algebraMap _ (fun _ => nonneg_iff_exists_ofReal.mp) hs⟩

namespace Polynomial

/--
theorem `ofReal_eval` / 定理 `ofReal_eval`

English:
theorem ofReal_eval
  given: (p : Real[X]) (x : Real)
  statement: (↑(p.eval x) : K) = aeval (↑x) p
  proof: (@aeval_algebraMap_apply_eq_algebraMap_eval Real K _ _ _ x p).symm

中文:
定理 of实数_eval
  条件: (p : 实数[X]) (x : 实数)
  结论: (↑(p.eval x) : K) = aeval (↑x) p
  证明: (@aeval_algebraMap_apply_eq_algebraMap_eval Real K _ _ _ x p).symm

Depends on / 依赖: aeval_algebraMap_apply_eq_algebraMap_eval
-/
theorem ofReal_eval (p : Real[X]) (x : Real) : (↑(p.eval x) : K) = aeval (↑x) p :=
  (@aeval_algebraMap_apply_eq_algebraMap_eval Real K _ _ _ x p).symm

end Polynomial

variable (K) in
/--
lemma `RCLike.span_one_I` / 引理 `RCLike.span_one_I`

English:
lemma RCLike.span_one_I
  statement: Submodule.span Real (M := K) {1, I} = ⊤
  proof: by
  suffices forall x : K, exists a b : Real, a • 1 + b • I = x by
    simpa [Submodule.eq_top_iff', Submodule.mem_span_pair]
  exact fun x => ⟨re x, im x, by simp [real_smul_eq_coe_mul]⟩

中文:
引理 RCLike.span_one_I
  结论: 子模.span 实数 (M := K) {1, I} = ⊤
  证明: by
  suffices forall x : K, exists a b : Real, a • 1 + b • I = x by
    simpa [Submodule.eq_top_iff', Submodule.mem_span_pair]
  exact fun x => ⟨re x, im x, by simp [real_smul_eq_coe_mul]⟩

Depends on / 依赖: Submodule, Submodule.eq_top_iff, Submodule.mem_span_pair, eq_top_iff, mem_span_pair, real_smul_eq_coe_mul
-/
lemma RCLike.span_one_I : Submodule.span Real (M := K) {1, I} = ⊤ := by
  suffices forall x : K, exists a b : Real, a • 1 + b • I = x by
    simpa [Submodule.eq_top_iff', Submodule.mem_span_pair]
  exact fun x => ⟨re x, im x, by simp [real_smul_eq_coe_mul]⟩

variable (K) in
/--
lemma `RCLike.rank_le_two` / 引理 `RCLike.rank_le_two`

English:
lemma RCLike.rank_le_two
  statement: Module.rank Real K <= 2
  proof: calc
    _ = Module.rank Real ↥(Submodule.span Real ({1, I} : Set K)) := by rw [span_one_I]; simp
    _ <= #({1, I} : Finset K) := by
      -- TODO: `simp` doesn't rewrite inside the type argument to `Module.rank`, but `rw` does.
      -- We should introduce `Submodule.rank` to fix this.
      have := rank_span_finset_le (R := Real) (M := K) {1, I}
      rw [Finset.coe_pair] at this
      simpa [span_one_I] using this
    _ <= 2 := mod_cast Finset.card_le_two

中文:
引理 RCLike.rank_le_two
  结论: 模.rank 实数 K <= 2
  证明: calc
    _ = Module.rank Real ↥(Submodule.span Real ({1, I} : Set K)) := by rw [span_one_I]; simp
    _ <= #({1, I} : Finset K) := by
      -- TODO: `simp` doesn't rewrite inside the type argument to `Module.rank`, but `rw` does.
      -- We should introduce `Submodule.rank` to fix this.
      have := rank_span_finset_le (R := Real) (M := K) {1, I}
      rw [Finset.coe_pair] at this
      simpa [span_one_I] using this
    _ <= 2 := mod_cast Finset.card_le_two

Depends on / 依赖: Finset, Module, Module.rank, Submodule, Submodule.span, span_one_I
-/
lemma RCLike.rank_le_two : Module.rank Real K <= 2 :=
  calc
    _ = Module.rank Real ↥(Submodule.span Real ({1, I} : Set K)) := by rw [span_one_I]; simp
    _ <= #({1, I} : Finset K) := by
      -- TODO: `simp` doesn't rewrite inside the type argument to `Module.rank`, but `rw` does.
      -- We should introduce `Submodule.rank` to fix this.
      have := rank_span_finset_le (R := Real) (M := K) {1, I}
      rw [Finset.coe_pair] at this
      simpa [span_one_I] using this
    _ <= 2 := mod_cast Finset.card_le_two

variable (K) in
/--
lemma `RCLike.finrank_le_two` / 引理 `RCLike.finrank_le_two`

English:
lemma RCLike.finrank_le_two
  statement: Module.finrank Real K <= 2
  proof: Module.finrank_le_of_rank_le rank_le_two _

中文:
引理 RCLike.finrank_le_two
  结论: 模.finrank 实数 K <= 2
  证明: Module.finrank_le_of_rank_le rank_le_two _

Depends on / 依赖: Module, Module.finrank_le_of_rank_le, finrank_le_of_rank_le, rank_le_two
-/
lemma RCLike.finrank_le_two : Module.finrank Real K <= 2 :=
Module.finrank_le_of_rank_le rank_le_two _

namespace FiniteDimensional

open RCLike

library_note «RCLike instance» /--
This instance generates a type-class problem with a metavariable `?m` that should satisfy
`RCLike ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/

/--
Instance `rclike_to_real` / 实例 `rclike_to_real`

English:
instance rclike_to_real
  signature: : FiniteDimensional Real K
  body: ⟨{1, I}, by simp [span_one_I]⟩

中文:
实例 rclike_to_real
  签名: : 有限维 实数 K
  定义体: ⟨{1, I}, by simp [span_one_I]⟩

Depends on / 依赖: span_one_I
-/
instance rclike_to_real : FiniteDimensional Real K := ⟨{1, I}, by simp [span_one_I]⟩

variable (K E)
variable [NormedAddCommGroup E] [NormedSpace K E]

/--
theorem `proper_rclike` / 定理 `proper_rclike`

English:
theorem proper_rclike
  given: [FiniteDimensional K E]
  statement: ProperSpace E
  proof: by
  -- Using `have` not `let` since it is only existence of `NormedSpace` structure that we need.
  have : NormedSpace Real E := .restrictScalars Real K E
  have : FiniteDimensional Real E := FiniteDimensional.trans Real K E
  infer_instance

中文:
定理 proper_rclike
  条件: [有限维 K E]
  结论: 真空间 E
  证明: by
  -- Using `have` not `let` since it is only existence of `NormedSpace` structure that we need.
  have : NormedSpace Real E := .restrictScalars Real K E
  have : FiniteDimensional Real E := FiniteDimensional.trans Real K E
  infer_instance
-/
theorem proper_rclike [FiniteDimensional K E] : ProperSpace E := by
  -- Using `have` not `let` since it is only existence of `NormedSpace` structure that we need.
  have : NormedSpace Real E := .restrictScalars Real K E
  have : FiniteDimensional Real E := FiniteDimensional.trans Real K E
  infer_instance

variable {E}

/--
Instance `RCLike.properSpace_submodule` / 实例 `RCLike.properSpace_submodule`

English:
instance RCLike.properSpace_submodule
  signature: (S : Submodule K E) [FiniteDimensional K S]
  body: proper_rclike K S

中文:
实例 RCLike.properSpace_submodule
  签名: (S : 子模 K E) [有限维 K S]
  定义体: proper_rclike K S

Depends on / 依赖: proper_rclike
-/
instance RCLike.properSpace_submodule (S : Submodule K E) [FiniteDimensional K S] :
    ProperSpace S :=
  proper_rclike K S

end FiniteDimensional

namespace RCLike

@[simp, rclike_simps]
/--
theorem `reCLM_norm` / 定理 `reCLM_norm`

English:
theorem reCLM_norm
  statement: ‖(reCLM : StrongDual Real K)‖ = 1
  proof: by
  apply le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
  convert! ContinuousLinearMap.ratio_le_opNorm (reCLM : StrongDual Real K) (1 : K)
  simp

@[simp, rclike_simps]

中文:
定理 reCLM_norm
  结论: ‖(reCLM : StrongDual 实数 K)‖ = 1
  证明: by
  apply le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
  convert! ContinuousLinearMap.ratio_le_opNorm (reCLM : StrongDual Real K) (1 : K)
  simp

@[simp, rclike_simps]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ratio_le_opNorm, LinearMap, LinearMap.mkContinuous_norm_le, StrongDual, convert, le_antisymm, mkContinuous_norm_le, ratio_le_opNorm, zero_le_one
-/
theorem reCLM_norm : ‖(reCLM : StrongDual Real K)‖ = 1 := by
  apply le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _)
  convert! ContinuousLinearMap.ratio_le_opNorm (reCLM : StrongDual Real K) (1 : K)
  simp

@[simp, rclike_simps]
/--
theorem `conjCLE_norm` / 定理 `conjCLE_norm`

English:
theorem conjCLE_norm
  statement: ‖(@conjCLE K _ : K ->L[Real] K)‖ = 1
  proof: (@conjLIE K _).toLinearIsometry.norm_toContinuousLinearMap

@[simp, rclike_simps]

中文:
定理 conjCLE_norm
  结论: ‖(@conjCLE K _ : K ->L[实数] K)‖ = 1
  证明: (@conjLIE K _).toLinearIsometry.norm_toContinuousLinearMap

@[simp, rclike_simps]

Depends on / 依赖: conjLIE, norm_toContinuousLinearMap, toLinearIsometry, toLinearIsometry.norm_toContinuousLinearMap
-/
theorem conjCLE_norm : ‖(@conjCLE K _ : K ->L[Real] K)‖ = 1 :=
  (@conjLIE K _).toLinearIsometry.norm_toContinuousLinearMap

@[simp, rclike_simps]
/--
theorem `ofRealCLM_norm` / 定理 `ofRealCLM_norm`

English:
theorem ofRealCLM_norm
  statement: ‖(ofRealCLM : Real ->L[Real] K)‖ = 1
  proof: LinearIsometry.norm_toContinuousLinearMap _

中文:
定理 of实数CLM_norm
  结论: ‖(of实数CLM : 实数 ->L[实数] K)‖ = 1
  证明: LinearIsometry.norm_toContinuousLinearMap _

Depends on / 依赖: LinearIsometry, LinearIsometry.norm_toContinuousLinearMap, norm_toContinuousLinearMap
-/
theorem ofRealCLM_norm : ‖(ofRealCLM : Real ->L[Real] K)‖ = 1 :=
  LinearIsometry.norm_toContinuousLinearMap _

end RCLike

namespace Polynomial

open ComplexConjugate in
/--
lemma `aeval_conj` / 引理 `aeval_conj`

English:
lemma aeval_conj
  given: (p : Real[X]) (z : K)
  statement: aeval (conj z) p = conj (aeval z p)
  proof: aeval_algHom_apply (RCLike.conjAe (K := K)) z p

中文:
引理 aeval_conj
  条件: (p : 实数[X]) (z : K)
  结论: aeval (conj z) p = conj (aeval z p)
  证明: aeval_algHom_apply (RCLike.conjAe (K := K)) z p

Depends on / 依赖: RCLike, RCLike.conjAe, aeval_algHom_apply, conjAe
-/
lemma aeval_conj (p : Real[X]) (z : K) : aeval (conj z) p = conj (aeval z p) :=
  aeval_algHom_apply (RCLike.conjAe (K := K)) z p

/--
lemma `aeval_ofReal` / 引理 `aeval_ofReal`

English:
lemma aeval_ofReal
  given: (p : Real[X]) (x : Real)
  statement: aeval (RCLike.ofReal x : K) p = eval x p
  proof: aeval_algHom_apply RCLike.ofRealAm x p

中文:
引理 aeval_of实数
  条件: (p : 实数[X]) (x : 实数)
  结论: aeval (RCLike.of实数 x : K) p = eval x p
  证明: aeval_algHom_apply RCLike.ofRealAm x p

Depends on / 依赖: RCLike, RCLike.ofRealAm, aeval_algHom_apply, ofRealAm
-/
lemma aeval_ofReal (p : Real[X]) (x : Real) : aeval (RCLike.ofReal x : K) p = eval x p :=
  aeval_algHom_apply RCLike.ofRealAm x p

end Polynomial
