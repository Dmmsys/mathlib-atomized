/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
## Polynomials over finite fields
-/

@[expose] public section


namespace MvPolynomial

variable {σ : Type*}

/--
theorem `C_dvd_iff_zmod` / 定理 `C_dvd_iff_zmod`

English:
theorem C_dvd_iff_zmod
  given: (n : Nat) (φ : MvPolynomial σ Int)
  proof: C_dvd_iff_map_hom_eq_zero _ _ (CharP.intCast_eq_zero_iff (ZMod n) n) _

中文:
定理 C_dvd_iff_zmod
  条件: (n : 自然数) (φ : 多元多项式 σ 整数)
  证明: C_dvd_iff_map_hom_eq_zero _ _ (CharP.intCast_eq_zero_iff (ZMod n) n) _

Depends on / 依赖: C_dvd_iff_map_hom_eq_zero, CharP.intCast_eq_zero_iff, intCast_eq_zero_iff
-/
theorem C_dvd_iff_zmod (n : Nat) (φ : MvPolynomial σ Int) :
    C (n : Int) ∣ φ ↔ map (Int.castRingHom (ZMod n)) φ = 0 :=
  C_dvd_iff_map_hom_eq_zero _ _ (CharP.intCast_eq_zero_iff (ZMod n) n) _

section frobenius

variable {p : Nat} [Fact p.Prime]

/--
theorem `frobenius_zmod` / 定理 `frobenius_zmod`

English:
theorem frobenius_zmod
  given: (f : MvPolynomial σ (ZMod p))
  statement: frobenius _ p f = expand p f
  proof: by
  apply induction_on f
  · intro a; rw [expand_C, frobenius_def, ← C_pow, ZMod.pow_card]
  · simp only [map_add]; intro _ _ hf hg; rw [hf, hg]
  · simp only [expand_X, map_mul]
    intro _ _ hf; rw [hf, frobenius_def]

中文:
定理 frobenius_zmod
  条件: (f : 多元多项式 σ (ZMod p))
  结论: frobenius _ p f = expand p f
  证明: by
  apply induction_on f
  · intro a; rw [expand_C, frobenius_def, ← C_pow, ZMod.pow_card]
  · simp only [map_add]; intro _ _ hf hg; rw [hf, hg]
  · simp only [expand_X, map_mul]
    intro _ _ hf; rw [hf, frobenius_def]

Depends on / 依赖: C_pow, ZMod.pow_card, expand_C, expand_X, frobenius_def, induction_on, map_add, map_mul, pow_card
-/
theorem frobenius_zmod (f : MvPolynomial σ (ZMod p)) : frobenius _ p f = expand p f := by
  apply induction_on f
  · intro a; rw [expand_C, frobenius_def, ← C_pow, ZMod.pow_card]
  · simp only [map_add]; intro _ _ hf hg; rw [hf, hg]
  · simp only [expand_X, map_mul]
    intro _ _ hf; rw [hf, frobenius_def]

/--
theorem `expand_zmod` / 定理 `expand_zmod`

English:
theorem expand_zmod
  given: (f : MvPolynomial σ (ZMod p))
  statement: expand p f = f ^ p
  proof: (frobenius_zmod _).symm

中文:
定理 expand_zmod
  条件: (f : 多元多项式 σ (ZMod p))
  结论: expand p f = f ^ p
  证明: (frobenius_zmod _).symm

Depends on / 依赖: frobenius_zmod
-/
theorem expand_zmod (f : MvPolynomial σ (ZMod p)) : expand p f = f ^ p :=
  (frobenius_zmod _).symm

end frobenius

end MvPolynomial

namespace MvPolynomial

noncomputable section

open Set LinearMap Submodule

variable {K : Type*} {σ : Type*}

section Indicator

variable [Fintype K] [Fintype σ]

/--
Definition of `indicator` / `indicator` 的定义

English:
definition indicator
  signature: [CommRing K] (a : σ -> K)
  body: ∏ n, (1 - (X n - C (a n)) ^ (Fintype.card K - 1))

中文:
定义 indicator
  签名: [交换环 K] (a : σ -> K)
  定义体: ∏ n, (1 - (X n - C (a n)) ^ (Fintype.card K - 1))

Depends on / 依赖: Fintype, Fintype.card
-/
def indicator [CommRing K] (a : σ -> K) : MvPolynomial σ K :=
  ∏ n, (1 - (X n - C (a n)) ^ (Fintype.card K - 1))

section CommRing

variable [CommRing K]

/--
theorem `eval_indicator_apply_eq_one` / 定理 `eval_indicator_apply_eq_one`

English:
theorem eval_indicator_apply_eq_one
  given: (a : σ -> K)
  statement: eval a (indicator a) = 1
  proof: by
  nontriviality
  have : 0 < Fintype.card K - 1 := tsub_pos_of_lt Fintype.one_lt_card
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C, sub_self,
    zero_pow this.ne', sub_zero, Finset.prod_const_one]

中文:
定理 eval_indicator_apply_eq_one
  条件: (a : σ -> K)
  结论: eval a (indicator a) = 1
  证明: by
  nontriviality
  have : 0 < Fintype.card K - 1 := tsub_pos_of_lt Fintype.one_lt_card
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C, sub_self,
    zero_pow this.ne', sub_zero, Finset.prod_const_one]

Depends on / 依赖: Finset, Finset.prod_const_one, Fintype, Fintype.card, Fintype.one_lt_card, eval_C, eval_X, indicator, map_one, map_pow, map_prod, map_sub, nontriviality, one_lt_card, prod_const_one, sub_self, sub_zero, this.ne, tsub_pos_of_lt, zero_pow
-/
theorem eval_indicator_apply_eq_one (a : σ -> K) : eval a (indicator a) = 1 := by
  nontriviality
  have : 0 < Fintype.card K - 1 := tsub_pos_of_lt Fintype.one_lt_card
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C, sub_self,
    zero_pow this.ne', sub_zero, Finset.prod_const_one]

/--
theorem `degrees_indicator` / 定理 `degrees_indicator`

English:
theorem degrees_indicator
  given: (c : σ -> K)
  proof: by
  rw [indicator]
  classical
refine degrees_prod_le.trans Finset.sum_le_sum fun s _ => degrees_sub_le.trans ?_
  rw [degrees_one]; rw [Multiset.zero_union]
  refine le_trans degrees_pow_le (nsmul_le_nsmul_right ?_ _)
  refine degrees_sub_le.trans ?_
  rw [degrees_C]; rw [Multiset.union_zero]
  exact degrees_X' _

中文:
定理 degrees_indicator
  条件: (c : σ -> K)
  证明: by
  rw [indicator]
  classical
refine degrees_prod_le.trans Finset.sum_le_sum fun s _ => degrees_sub_le.trans ?_
  rw [degrees_one]; rw [Multiset.zero_union]
  refine le_trans degrees_pow_le (nsmul_le_nsmul_right ?_ _)
  refine degrees_sub_le.trans ?_
  rw [degrees_C]; rw [Multiset.union_zero]
  exact degrees_X' _

Depends on / 依赖: Finset, Finset.sum_le_sum, Multiset, Multiset.union_zero, Multiset.zero_union, classical, degrees_C, degrees_X, degrees_one, degrees_pow_le, degrees_prod_le, degrees_prod_le.trans, degrees_sub_le, degrees_sub_le.trans, indicator, le_trans, nsmul_le_nsmul_right, sum_le_sum, union_zero, zero_union
-/
theorem degrees_indicator (c : σ -> K) :
    degrees (indicator c) <= ∑ s : σ, (Fintype.card K - 1) • {s} := by
  rw [indicator]
  classical
refine degrees_prod_le.trans Finset.sum_le_sum fun s _ => degrees_sub_le.trans ?_
  rw [degrees_one]; rw [Multiset.zero_union]
  refine le_trans degrees_pow_le (nsmul_le_nsmul_right ?_ _)
  refine degrees_sub_le.trans ?_
  rw [degrees_C]; rw [Multiset.union_zero]
  exact degrees_X' _

/--
theorem `indicator_mem_restrictDegree` / 定理 `indicator_mem_restrictDegree`

English:
theorem indicator_mem_restrictDegree
  given: (c : σ -> K)
  proof: by
  classical
  rw [mem_restrictDegree_iff_sup]; rw [indicator]
  intro n
  refine le_trans (Multiset.count_le_of_le _ <| degrees_indicator _) (le_of_eq ?_)
  simp_rw [← Multiset.coe_countAddMonoidHom, map_sum,
    map_nsmul, Multiset.coe_countAddMonoidHom, nsmul_eq_mul, Nat.cast_id]
  trans
  · refine Finset.sum_eq_single n ?_ ?_
    · intro b _ ne
      simp [ne, eqComm]
    · intro h; exact (h <| Finset.mem_univ _).elim
  · rw [Multiset.count_singleton_self, mul_one]

中文:
定理 indicator_mem_restrictDegree
  条件: (c : σ -> K)
  证明: by
  classical
  rw [mem_restrictDegree_iff_sup]; rw [indicator]
  intro n
  refine le_trans (Multiset.count_le_of_le _ <| degrees_indicator _) (le_of_eq ?_)
  simp_rw [← Multiset.coe_countAddMonoidHom, map_sum,
    map_nsmul, Multiset.coe_countAddMonoidHom, nsmul_eq_mul, Nat.cast_id]
  trans
  · refine Finset.sum_eq_single n ?_ ?_
    · intro b _ ne
      simp [ne, eqComm]
    · intro h; exact (h <| Finset.mem_univ _).elim
  · rw [Multiset.count_singleton_self, mul_one]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_eq_single, Multiset, Multiset.coe_countAddMonoidHom, Multiset.count_le_of_le, Multiset.count_singleton_self, Nat.cast_id, cast_id, classical, coe_countAddMonoidHom, count_le_of_le, count_singleton_self, degrees_indicator, eqComm, indicator, le_of_eq, le_trans, map_nsmul, map_sum
-/
theorem indicator_mem_restrictDegree (c : σ -> K) :
    indicator c in restrictDegree σ K (Fintype.card K - 1) := by
  classical
  rw [mem_restrictDegree_iff_sup]; rw [indicator]
  intro n
  refine le_trans (Multiset.count_le_of_le _ <| degrees_indicator _) (le_of_eq ?_)
  simp_rw [← Multiset.coe_countAddMonoidHom, map_sum,
    map_nsmul, Multiset.coe_countAddMonoidHom, nsmul_eq_mul, Nat.cast_id]
  trans
  · refine Finset.sum_eq_single n ?_ ?_
    · intro b _ ne
      simp [ne, eqComm]
    · intro h; exact (h <| Finset.mem_univ _).elim
  · rw [Multiset.count_singleton_self, mul_one]

end CommRing

variable [Field K]

/--
theorem `eval_indicator_apply_eq_zero` / 定理 `eval_indicator_apply_eq_zero`

English:
theorem eval_indicator_apply_eq_zero
  given: (a b : σ -> K) (h : a != b)
  statement: eval a (indicator b) = 0
  proof: by
  obtain ⟨i, hi⟩ : exists i, a i != b i := by rwa [Ne, funext_iff, not_forall] at h
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C,
    Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [FiniteField.pow_card_sub_one_eq_one]; rw [sub_self]
  rwa [Ne, sub_eq_zero]

中文:
定理 eval_indicator_apply_eq_zero
  条件: (a b : σ -> K) (h : a != b)
  结论: eval a (indicator b) = 0
  证明: by
  obtain ⟨i, hi⟩ : exists i, a i != b i := by rwa [Ne, funext_iff, not_forall] at h
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C,
    Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [FiniteField.pow_card_sub_one_eq_one]; rw [sub_self]
  rwa [Ne, sub_eq_zero]

Depends on / 依赖: FiniteField, FiniteField.pow_card_sub_one_eq_one, Finset, Finset.mem_univ, Finset.prod_eq_zero_iff, eval_C, eval_X, funext_iff, indicator, map_one, map_pow, map_prod, map_sub, mem_univ, not_forall, pow_card_sub_one_eq_one, prod_eq_zero_iff, sub_eq_zero, sub_self
-/
theorem eval_indicator_apply_eq_zero (a b : σ -> K) (h : a != b) : eval a (indicator b) = 0 := by
  obtain ⟨i, hi⟩ : exists i, a i != b i := by rwa [Ne, funext_iff, not_forall] at h
  simp only [indicator, map_prod, map_sub, map_one, map_pow, eval_X, eval_C,
    Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [FiniteField.pow_card_sub_one_eq_one]; rw [sub_self]
  rwa [Ne, sub_eq_zero]

end Indicator

section

variable (K σ)

set_option backward.isDefEq.respectTransparency false in
/-- `MvPolynomial.eval` as a `K`-linear map. -/
@[simps]
/--
Definition of `evalₗ` / `evalₗ` 的定义

English:
definition evalₗ
  signature: [CommSemiring K]
  body: eval e p
  map_add' p q := by ext x; simp
  map_smul' a p := by ext e; simp

中文:
定义 evalₗ
  签名: [交换半环 K]
  定义体: eval e p
  map_add' p q := by ext x; simp
  map_smul' a p := by ext e; simp
-/
def evalₗ [CommSemiring K] : MvPolynomial σ K ->ₗ[K] (σ -> K) -> K where
  toFun p e := eval e p
  map_add' p q := by ext x; simp
  map_smul' a p := by ext e; simp

variable [Field K] [Fintype K] [Finite σ]

/--
theorem `map_restrict_dom_evalₗ` / 定理 `map_restrict_dom_evalₗ`

English:
theorem map_restrict_dom_evalₗ
  statement: (restrictDegree σ K (Fintype.card K - 1)).map (evalₗ K σ) = ⊤
  proof: by
  cases nonempty_fintype σ
  refine top_unique (SetLike.le_def.2 fun e _ => mem_map.2 ?_)
  classical
  refine ⟨∑ n : σ -> K, e n • indicator n, ?_, ?_⟩
  · exact sum_mem fun c _ => smul_mem _ _ (indicator_mem_restrictDegree _)
  · ext n
    simp only [evalₗ_apply, map_sum, smul_eval]
    rw [Finset.sum_eq_single n] <;>
      aesop (add simp [eval_indicator_apply_eq_zero, eval_indicator_apply_eq_one, eq_comm])

中文:
定理 map_restrict_dom_evalₗ
  结论: (restrictDegree σ K (有限类型.card K - 1)).map (evalₗ K σ) = ⊤
  证明: by
  cases nonempty_fintype σ
  refine top_unique (SetLike.le_def.2 fun e _ => mem_map.2 ?_)
  classical
  refine ⟨∑ n : σ -> K, e n • indicator n, ?_, ?_⟩
  · exact sum_mem fun c _ => smul_mem _ _ (indicator_mem_restrictDegree _)
  · ext n
    simp only [evalₗ_apply, map_sum, smul_eval]
    rw [Finset.sum_eq_single n] <;>
      aesop (add simp [eval_indicator_apply_eq_zero, eval_indicator_apply_eq_one, eq_comm])

Depends on / 依赖: Finset, Finset.sum_eq_single, SetLike, SetLike.le_def, classical, eq_comm, eval_indicator_apply_eq_one, eval_indicator_apply_eq_zero, indicator, indicator_mem_restrictDegree, le_def, map_sum, mem_map, nonempty_fintype, smul_eval, smul_mem, sum_eq_single, sum_mem, top_unique
-/
theorem map_restrict_dom_evalₗ : (restrictDegree σ K (Fintype.card K - 1)).map (evalₗ K σ) = ⊤ := by
  cases nonempty_fintype σ
  refine top_unique (SetLike.le_def.2 fun e _ => mem_map.2 ?_)
  classical
  refine ⟨∑ n : σ -> K, e n • indicator n, ?_, ?_⟩
  · exact sum_mem fun c _ => smul_mem _ _ (indicator_mem_restrictDegree _)
  · ext n
    simp only [evalₗ_apply, map_sum, smul_eval]
    rw [Finset.sum_eq_single n] <;>
      aesop (add simp [eval_indicator_apply_eq_zero, eval_indicator_apply_eq_one, eq_comm])

end

end

end MvPolynomial

namespace MvPolynomial

open scoped Cardinal
open LinearMap Submodule

universe u

variable (σ : Type u) (K : Type u) [Fintype K]

/--
Definition of `R` / `R` 的定义

English:
definition R
  signature: [CommRing K]
  body: restrictDegree σ K (Fintype.card K - 1)

中文:
定义 R
  签名: [交换环 K]
  定义体: restrictDegree σ K (Fintype.card K - 1)

Depends on / 依赖: Fintype, Fintype.card, restrictDegree
-/
def R [CommRing K] : Type u :=
  restrictDegree σ K (Fintype.card K - 1)
-- The `AddCommGroup, Module K, Inhabited` instances should be constructed by a deriving handler.

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: K] : AddCommGroup (R σ K)
  body: inferInstanceAs (AddCommGroup (restrictDegree σ K (Fintype.card K - 1)))

中文:
实例 [交换环
  签名: K] : 加法交换群 (R σ K)
  定义体: inferInstanceAs (AddCommGroup (restrictDegree σ K (Fintype.card K - 1)))

Depends on / 依赖: AddCommGroup, Fintype, Fintype.card, restrictDegree
-/
noncomputable instance [CommRing K] : AddCommGroup (R σ K) :=
  inferInstanceAs (AddCommGroup (restrictDegree σ K (Fintype.card K - 1)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: K] : Module K (R σ K)
  body: inferInstanceAs (Module K (restrictDegree σ K (Fintype.card K - 1)))

中文:
实例 [交换环
  签名: K] : 模 K (R σ K)
  定义体: inferInstanceAs (Module K (restrictDegree σ K (Fintype.card K - 1)))

Depends on / 依赖: Fintype, Fintype.card, Module, restrictDegree
-/
noncomputable instance [CommRing K] : Module K (R σ K) :=
  inferInstanceAs (Module K (restrictDegree σ K (Fintype.card K - 1)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: K] : Inhabited (R σ K)
  body: inferInstanceAs (Inhabited (restrictDegree σ K (Fintype.card K - 1)))

中文:
实例 [交换环
  签名: K] : 可居 (R σ K)
  定义体: inferInstanceAs (Inhabited (restrictDegree σ K (Fintype.card K - 1)))

Depends on / 依赖: Fintype, Fintype.card, Inhabited, restrictDegree
-/
noncomputable instance [CommRing K] : Inhabited (R σ K) :=
  inferInstanceAs (Inhabited (restrictDegree σ K (Fintype.card K - 1)))

/--
Definition of `evalᵢ` / `evalᵢ` 的定义

English:
definition evalᵢ
  signature: [CommRing K]
  body: (evalₗ K σ).comp (restrictDegree σ K (Fintype.card K - 1)).subtype

中文:
定义 evalᵢ
  签名: [交换环 K]
  定义体: (evalₗ K σ).comp (restrictDegree σ K (Fintype.card K - 1)).subtype

Depends on / 依赖: Fintype, Fintype.card, restrictDegree, subtype
-/
noncomputable def evalᵢ [CommRing K] : R σ K ->ₗ[K] (σ -> K) -> K :=
  (evalₗ K σ).comp (restrictDegree σ K (Fintype.card K - 1)).subtype

-- TODO: would be nice to replace this by suitable decidability assumptions
open scoped Classical in
/--
Instance `decidableRestrictDegree` / 实例 `decidableRestrictDegree`

English:
instance decidableRestrictDegree
  signature: (m : Nat)
  body: by
  simp only [Set.mem_ofPred_eq]; infer_instance

中文:
实例 decidableRestrictDegree
  签名: (m : 自然数)
  定义体: by
  simp only [Set.mem_ofPred_eq]; infer_instance

Depends on / 依赖: Set.mem_ofPred_eq, infer_instance, mem_ofPred_eq
-/
noncomputable instance decidableRestrictDegree (m : Nat) :
    DecidablePred (· in { n : σ ->₀ Nat | forall i, n i <= m }) := by
  simp only [Set.mem_ofPred_eq]; infer_instance

variable [Field K]

open scoped Classical in
/--
theorem `rank_R` / 定理 `rank_R`

English:
theorem rank_R
  given: [Fintype σ]
  statement: Module.rank K (R σ K) = Fintype.card (σ -> K)
  proof: calc
    Module.rank K (R σ K) =
        Module.rank K (↥{ s : σ ->₀ Nat | forall n : σ, s n <= Fintype.card K - 1 } ->₀ K) :=
      LinearEquiv.rank_eq
        (AddMonoidAlgebra.supportedEquivFinsupp { s : σ ->₀ Nat | forall n : σ, s n <= Fintype.card K - 1 })
    _ = #{ s : σ ->₀ Nat | forall n : σ, s n <= Fintype.card K - 1 } := by rw [rank_finsupp_self']
    _ = #{ s : σ -> Nat | forall n : σ, s n < Fintype.card K } := by
      refine Quotient.sound ⟨Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun f => ?_⟩
      refine forall_congr' fun n => le_tsub_iff_right ?_
      exact Fintype.card_pos_iff.2 ⟨0⟩
    _ = #(σ -> { n // n < Fintype.card K }) :=
      (@Equiv.subtypePiEquivPi σ (fun _ => Nat) fun _ n => n < Fintype.card K).cardinal_eq
    _ = #(σ -> Fin (Fintype.card K)) :=
      (Equiv.arrowCongr (Equiv.refl σ) Fin.equivSubtype.symm).cardinal_eq
    _ = #(σ -> K) := (Equiv.arrowCongr (Equiv.refl σ) (Fintype.equivFin K).symm).cardinal_eq
    _ = Fintype.card (σ -> K) := Cardinal.mk_fintype _

中文:
定理 rank_R
  条件: [有限类型 σ]
  结论: 模.rank K (R σ K) = 有限类型.card (σ -> K)
  证明: calc
    Module.rank K (R σ K) =
        Module.rank K (↥{ s : σ ->₀ Nat | forall n : σ, s n <= Fintype.card K - 1 } ->₀ K) :=
      LinearEquiv.rank_eq
        (AddMonoidAlgebra.supportedEquivFinsupp { s : σ ->₀ Nat | forall n : σ, s n <= Fintype.card K - 1 })
    _ = #{ s : σ ->₀ Nat | forall n : σ, s n <= Fintype.card K - 1 } := by rw [rank_finsupp_self']
    _ = #{ s : σ -> Nat | forall n : σ, s n < Fintype.card K } := by
      refine Quotient.sound ⟨Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun f => ?_⟩
      refine forall_congr' fun n => le_tsub_iff_right ?_
      exact Fintype.card_pos_iff.2 ⟨0⟩
    _ = #(σ -> { n // n < Fintype.card K }) :=
      (@Equiv.subtypePiEquivPi σ (fun _ => Nat) fun _ n => n < Fintype.card K).cardinal_eq
    _ = #(σ -> Fin (Fintype.card K)) :=
      (Equiv.arrowCongr (Equiv.refl σ) Fin.equivSubtype.symm).cardinal_eq
    _ = #(σ -> K) := (Equiv.arrowCongr (Equiv.refl σ) (Fintype.equivFin K).symm).cardinal_eq
    _ = Fintype.card (σ -> K) := Cardinal.mk_fintype _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supportedEquivFinsupp, Equiv.subtypeEquiv, Finsupp, Finsupp.equivFunOnFinite, Fintype, Fintype.card, LinearEquiv, LinearEquiv.rank_eq, Module, Module.rank, Quotient, Quotient.sound, equivFunOnFinite, forall_congr, rank_eq, rank_finsupp_self, subtypeEquiv, supportedEquivFinsupp
-/
theorem rank_R [Fintype σ] : Module.rank K (R σ K) = Fintype.card (σ -> K) :=
  calc
    Module.rank K (R σ K) =
        Module.rank K (↥{ s : σ ->₀ Nat | forall n : σ, s n <= Fintype.card K - 1 } ->₀ K) :=
      LinearEquiv.rank_eq
        (AddMonoidAlgebra.supportedEquivFinsupp { s : σ ->₀ Nat | forall n : σ, s n <= Fintype.card K - 1 })
    _ = #{ s : σ ->₀ Nat | forall n : σ, s n <= Fintype.card K - 1 } := by rw [rank_finsupp_self']
    _ = #{ s : σ -> Nat | forall n : σ, s n < Fintype.card K } := by
      refine Quotient.sound ⟨Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun f => ?_⟩
      refine forall_congr' fun n => le_tsub_iff_right ?_
      exact Fintype.card_pos_iff.2 ⟨0⟩
    _ = #(σ -> { n // n < Fintype.card K }) :=
      (@Equiv.subtypePiEquivPi σ (fun _ => Nat) fun _ n => n < Fintype.card K).cardinal_eq
    _ = #(σ -> Fin (Fintype.card K)) :=
      (Equiv.arrowCongr (Equiv.refl σ) Fin.equivSubtype.symm).cardinal_eq
    _ = #(σ -> K) := (Equiv.arrowCongr (Equiv.refl σ) (Fintype.equivFin K).symm).cardinal_eq
    _ = Fintype.card (σ -> K) := Cardinal.mk_fintype _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: σ] : FiniteDimensional K (R σ K)
  body: by
  cases nonempty_fintype σ
  rw [FiniteDimensional]; rw [← IsNoetherian.iff_fg]; rw [IsNoetherian.iff_rank_lt_aleph0]
  simpa only [rank_R] using Cardinal.natCast_lt_aleph0

中文:
实例 [有限
  签名: σ] : 有限维 K (R σ K)
  定义体: by
  cases nonempty_fintype σ
  rw [FiniteDimensional]; rw [← IsNoetherian.iff_fg]; rw [IsNoetherian.iff_rank_lt_aleph0]
  simpa only [rank_R] using Cardinal.natCast_lt_aleph0

Depends on / 依赖: Cardinal, Cardinal.natCast_lt_aleph0, FiniteDimensional, IsNoetherian, IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0, iff_fg, iff_rank_lt_aleph0, natCast_lt_aleph0, nonempty_fintype, rank_R
-/
instance [Finite σ] : FiniteDimensional K (R σ K) := by
  cases nonempty_fintype σ
  rw [FiniteDimensional]; rw [← IsNoetherian.iff_fg]; rw [IsNoetherian.iff_rank_lt_aleph0]
  simpa only [rank_R] using Cardinal.natCast_lt_aleph0

open scoped Classical in
/--
theorem `finrank_R` / 定理 `finrank_R`

English:
theorem finrank_R
  given: [Fintype σ]
  statement: Module.finrank K (R σ K) = Fintype.card (σ -> K)
  proof: Module.finrank_eq_of_rank_eq (rank_R σ K)

中文:
定理 finrank_R
  条件: [有限类型 σ]
  结论: 模.finrank K (R σ K) = 有限类型.card (σ -> K)
  证明: Module.finrank_eq_of_rank_eq (rank_R σ K)

Depends on / 依赖: Module, Module.finrank_eq_of_rank_eq, finrank_eq_of_rank_eq, rank_R
-/
theorem finrank_R [Fintype σ] : Module.finrank K (R σ K) = Fintype.card (σ -> K) :=
  Module.finrank_eq_of_rank_eq (rank_R σ K)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `range_evalᵢ` / 定理 `range_evalᵢ`

English:
theorem range_evalᵢ
  given: [Finite σ]
  statement: range (evalᵢ σ K) = ⊤
  proof: by
  rw [evalᵢ]; rw [LinearMap.range_comp]; rw [range_subtype]
  exact map_restrict_dom_evalₗ K σ

中文:
定理 range_evalᵢ
  条件: [有限 σ]
  结论: range (evalᵢ σ K) = ⊤
  证明: by
  rw [evalᵢ]; rw [LinearMap.range_comp]; rw [range_subtype]
  exact map_restrict_dom_evalₗ K σ

Depends on / 依赖: LinearMap, LinearMap.range_comp, range_comp, range_subtype
-/
theorem range_evalᵢ [Finite σ] : range (evalᵢ σ K) = ⊤ := by
  rw [evalᵢ]; rw [LinearMap.range_comp]; rw [range_subtype]
  exact map_restrict_dom_evalₗ K σ

/--
theorem `ker_evalₗ` / 定理 `ker_evalₗ`

English:
theorem ker_evalₗ
  given: [Finite σ]
  statement: ker (evalᵢ σ K) = ⊥
  proof: by
  cases nonempty_fintype σ
  refine (ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank ?_).mpr (range_evalᵢ σ K)
  classical
  rw [Module.finrank_fintype_fun_eq_card]; rw [finrank_R]

中文:
定理 ker_evalₗ
  条件: [有限 σ]
  结论: ker (evalᵢ σ K) = ⊥
  证明: by
  cases nonempty_fintype σ
  refine (ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank ?_).mpr (range_evalᵢ σ K)
  classical
  rw [Module.finrank_fintype_fun_eq_card]; rw [finrank_R]

Depends on / 依赖: Module, Module.finrank_fintype_fun_eq_card, classical, finrank_R, finrank_fintype_fun_eq_card, ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank, nonempty_fintype
-/
theorem ker_evalₗ [Finite σ] : ker (evalᵢ σ K) = ⊥ := by
  cases nonempty_fintype σ
  refine (ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank ?_).mpr (range_evalᵢ σ K)
  classical
  rw [Module.finrank_fintype_fun_eq_card]; rw [finrank_R]

/--
theorem `eq_zero_of_eval_eq_zero` / 定理 `eq_zero_of_eval_eq_zero`

English:
theorem eq_zero_of_eval_eq_zero
  statement: [Finite σ] (p : MvPolynomial σ K) (h : forall v : σ -> K, eval v p = 0)
  proof: let p' : R σ K := ⟨p, hp⟩
  have : p' in ker (evalᵢ σ K) := funext h
show p'.1 = (0 : R σ K).1 from congr_arg _ by rwa [ker_evalₗ, mem_bot] at this

中文:
定理 eq_zero_of_eval_eq_zero
  结论: [有限 σ] (p : 多元多项式 σ K) (h : 对任意 v : σ -> K, eval v p = 0)
  证明: let p' : R σ K := ⟨p, hp⟩
  have : p' in ker (evalᵢ σ K) := funext h
show p'.1 = (0 : R σ K).1 from congr_arg _ by rwa [ker_evalₗ, mem_bot] at this

Depends on / 依赖: congr_arg, mem_bot
-/
theorem eq_zero_of_eval_eq_zero [Finite σ] (p : MvPolynomial σ K) (h : forall v : σ -> K, eval v p = 0)
    (hp : p in restrictDegree σ K (Fintype.card K - 1)) : p = 0 :=
  let p' : R σ K := ⟨p, hp⟩
  have : p' in ker (evalᵢ σ K) := funext h
show p'.1 = (0 : R σ K).1 from congr_arg _ by rwa [ker_evalₗ, mem_bot] at this

end MvPolynomial
