/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Uncurrying continuous alternating maps

Given a continuous function `f` which is linear in the first argument
and is alternating form in the other `n` arguments,
this file defines a continuous alternating form `ContinuousAlternatingMap.alternatizeUncurryFin f`
in `n + 1` arguments.

This function is given by
```
ContinuousAlternatingMap.alternatizeUncurryFin f v =
  ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Given a continuous alternating map `f` of `n + 1` arguments,
each term in the sum above written for `f.curryLeft` equals the original map,
thus `f.curryLeft.alternatizeUncurryFin = (n + 1) • f`.

We do not multiply the result of `alternatizeUncurryFin` by `(n + 1)⁻¹`
so that the construction works for `𝕜`-multilinear maps over any normed field `𝕜`,
not only a field of characteristic zero.

## Main results

- `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft`:
  the round-trip formula for currying/uncurrying, see above.

- `ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric`:
  If `f` is a symmetric bilinear map taking values in the space of continuous alternating maps,
  then the twice uncurried `f` is zero.

The latter theorem will be used
to prove that the second exterior derivative of a differential form is zero.
-/

@[expose] public section

open Fin Function

namespace ContinuousAlternatingMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : Nat}

/--
theorem `map_insertNth` / 定理 `map_insertNth`

English:
theorem map_insertNth
  given: (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (p : Fin (n + 1)) (x : E) (v : Fin n -> E)
  proof: f.toAlternatingMap.map_insertNth p x v

中文:
定理 map_insertNth
  条件: (f : E [⋀^有限集 (n + 1)]->L[𝕜] F) (p : 有限集 (n + 1)) (x : E) (v : 有限集 n -> E)
  证明: f.toAlternatingMap.map_insertNth p x v

Depends on / 依赖: f.toAlternatingMap.map_insertNth, map_insertNth, toAlternatingMap
-/
theorem map_insertNth (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (p : Fin (n + 1)) (x : E) (v : Fin n -> E) :
    f (p.insertNth x v) = (-1) ^ (p : Nat) • f (Matrix.vecCons x v) :=
  f.toAlternatingMap.map_insertNth p x v

/--
theorem `neg_one_pow_smul_map_insertNth` / 定理 `neg_one_pow_smul_map_insertNth`

English:
theorem neg_one_pow_smul_map_insertNth
  statement: (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (p : Fin (n + 1)) (x : E)
  proof: f.toAlternatingMap.neg_one_pow_smul_map_insertNth p x v

中文:
定理 neg_one_pow_smul_map_insertNth
  结论: (f : E [⋀^有限集 (n + 1)]->L[𝕜] F) (p : 有限集 (n + 1)) (x : E)
  证明: f.toAlternatingMap.neg_one_pow_smul_map_insertNth p x v

Depends on / 依赖: f.toAlternatingMap.neg_one_pow_smul_map_insertNth, neg_one_pow_smul_map_insertNth, toAlternatingMap
-/
theorem neg_one_pow_smul_map_insertNth (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (p : Fin (n + 1)) (x : E)
    (v : Fin n -> E) : (-1) ^ (p : Nat) • f (p.insertNth x v) = f (Matrix.vecCons x v) :=
  f.toAlternatingMap.neg_one_pow_smul_map_insertNth p x v

/--
theorem `neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq` / 定理 `neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq`

English:
theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq
  statement: (f : E [⋀^Fin n]->L[𝕜] F)
  proof: f.toAlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq hvij hij

中文:
定理 neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq
  结论: (f : E [⋀^有限集 n]->L[𝕜] F)
  证明: f.toAlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq hvij hij

Depends on / 依赖: f.toAlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq, neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq, toAlternatingMap
-/
theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : E [⋀^Fin n]->L[𝕜] F)
    {v : Fin (n + 1) -> E} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i != j) :
    (-1) ^ (i : Nat) • f (i.removeNth v) + (-1) ^ (j : Nat) • f (j.removeNth v) = 0 :=
  f.toAlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq hvij hij

set_option backward.privateInPublic true in
/--
Definition of `alternatizeUncurryFinCLM.aux` / `alternatizeUncurryFinCLM.aux` 的定义

English:
definition alternatizeUncurryFinCLM.aux
  signature: :
  body: AlternatingMap.alternatizeUncurryFinLM ∘ₗ (toAlternatingMapLinear (R := 𝕜)).compRight (S := 𝕜) ∘ₗ
    ContinuousLinearMap.coeLM 𝕜

中文:
定义 alternatizeUncurryFinCLM.aux
  签名: :
  定义体: AlternatingMap.alternatizeUncurryFinLM ∘ₗ (toAlternatingMapLinear (R := 𝕜)).compRight (S := 𝕜) ∘ₗ
    ContinuousLinearMap.coeLM 𝕜
-/
private def alternatizeUncurryFinCLM.aux :
    (E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) ->ₗ[𝕜] E [⋀^Fin (n + 1)]->ₗ[𝕜] F :=
  AlternatingMap.alternatizeUncurryFinLM ∘ₗ (toAlternatingMapLinear (R := 𝕜)).compRight (S := 𝕜) ∘ₗ
    ContinuousLinearMap.coeLM 𝕜

/--
lemma `alternatizeUncurryFinCLM.aux_apply` / 引理 `alternatizeUncurryFinCLM.aux_apply`

English:
lemma alternatizeUncurryFinCLM.aux_apply
  statement: (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F)
  proof: by
  simp [aux, AlternatingMap.alternatizeUncurryFin_apply]

中文:
引理 alternatizeUncurryFinCLM.aux_apply
  结论: (f : E ->L[𝕜] E [⋀^有限集 n]->L[𝕜] F)
  证明: by
  simp [aux, AlternatingMap.alternatizeUncurryFin_apply]
-/
private lemma alternatizeUncurryFinCLM.aux_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F)
    (v : Fin (n + 1) -> E) :
    aux f v = ∑ i : Fin (n + 1), (-1) ^ (i : Nat) • f (v i) (i.removeNth v) := by
  simp [aux, AlternatingMap.alternatizeUncurryFin_apply]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (𝕜 E F) in
/-- `AlternatingMap.alternatizeUncurryFin` as a continuous linear map. -/
@[irreducible]
/--
Definition of `alternatizeUncurryFinCLM` / `alternatizeUncurryFinCLM` 的定义

English:
definition alternatizeUncurryFinCLM
  signature: :
  body: AlternatingMap.mkContinuousLinear alternatizeUncurryFinCLM.aux (n + 1) fun f v => calc
    ‖alternatizeUncurryFinCLM.aux f v‖ <= ∑ i : Fin (n + 1), ‖f‖ * ∏ i, ‖v i‖ := by
      rw [alternatizeUncurryFinCLM.aux_apply]
      refine norm_sum_le_of_le _ fun i hi => ?_
      rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg)]; rw [i.prod_univ_succAbove]; rw [← mul_assoc]
      apply (f (v i)).le_of_opNorm_le
      apply f.le_opNorm
    _ = (n + 1) * ‖f‖ * ∏ i, ‖v i‖ := by simp [mul_assoc]

中文:
定义 alternatizeUncurryFinCLM
  签名: :
  定义体: AlternatingMap.mkContinuousLinear alternatizeUncurryFinCLM.aux (n + 1) fun f v => calc
    ‖alternatizeUncurryFinCLM.aux f v‖ <= ∑ i : Fin (n + 1), ‖f‖ * ∏ i, ‖v i‖ := by
      rw [alternatizeUncurryFinCLM.aux_apply]
      refine norm_sum_le_of_le _ fun i hi => ?_
      rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg)]; rw [i.prod_univ_succAbove]; rw [← mul_assoc]
      apply (f (v i)).le_of_opNorm_le
      apply f.le_opNorm
    _ = (n + 1) * ‖f‖ * ∏ i, ‖v i‖ := by simp [mul_assoc]

Depends on / 依赖: AlternatingMap, AlternatingMap.mkContinuousLinear, alternatizeUncurryFinCLM, alternatizeUncurryFinCLM.aux, alternatizeUncurryFinCLM.aux_apply, aux_apply, f.le_opNorm, i.prod_univ_succAbove, isUnit_one, isUnit_one.neg, le_of_opNorm_le, le_opNorm, mkContinuousLinear, mul_assoc, norm_isUnit_zsmul, norm_sum_le_of_le, prod_univ_succAbove
-/
noncomputable def alternatizeUncurryFinCLM :
    (E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) ->L[𝕜] E [⋀^Fin (n + 1)]->L[𝕜] F :=
  AlternatingMap.mkContinuousLinear alternatizeUncurryFinCLM.aux (n + 1) fun f v => calc
    ‖alternatizeUncurryFinCLM.aux f v‖ <= ∑ i : Fin (n + 1), ‖f‖ * ∏ i, ‖v i‖ := by
      rw [alternatizeUncurryFinCLM.aux_apply]
      refine norm_sum_le_of_le _ fun i hi => ?_
      rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg)]; rw [i.prod_univ_succAbove]; rw [← mul_assoc]
      apply (f (v i)).le_of_opNorm_le
      apply f.le_opNorm
    _ = (n + 1) * ‖f‖ * ∏ i, ‖v i‖ := by simp [mul_assoc]

/--
lemma `norm_alternatizeUncurryFinCLM_le` / 引理 `norm_alternatizeUncurryFinCLM_le`

English:
lemma norm_alternatizeUncurryFinCLM_le
  statement: ‖alternatizeUncurryFinCLM (n := n) 𝕜 E F‖ <= n + 1
  proof: by
  rw [alternatizeUncurryFinCLM]
  apply AlternatingMap.mkContinuousLinear_norm_le
  positivity

中文:
引理 norm_alternatizeUncurryFinCLM_le
  结论: ‖alternatizeUncurryFinCLM (n := n) 𝕜 E F‖ <= n + 1
  证明: by
  rw [alternatizeUncurryFinCLM]
  apply AlternatingMap.mkContinuousLinear_norm_le
  positivity

Depends on / 依赖: AlternatingMap, AlternatingMap.mkContinuousLinear_norm_le, alternatizeUncurryFinCLM, mkContinuousLinear_norm_le
-/
lemma norm_alternatizeUncurryFinCLM_le : ‖alternatizeUncurryFinCLM (n := n) 𝕜 E F‖ <= n + 1 := by
  rw [alternatizeUncurryFinCLM]
  apply AlternatingMap.mkContinuousLinear_norm_le
  positivity

/--
Definition of `alternatizeUncurryFin` / `alternatizeUncurryFin` 的定义

English:
definition alternatizeUncurryFin
  signature: (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F)
  body: alternatizeUncurryFinCLM 𝕜 E F f

@[simp]

中文:
定义 alternatizeUncurryFin
  签名: (f : E ->L[𝕜] E [⋀^有限集 n]->L[𝕜] F)
  定义体: alternatizeUncurryFinCLM 𝕜 E F f

@[simp]

Depends on / 依赖: alternatizeUncurryFinCLM
-/
noncomputable def alternatizeUncurryFin (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) :
    E [⋀^Fin (n + 1)]->L[𝕜] F :=
  alternatizeUncurryFinCLM 𝕜 E F f

@[simp]
/--
lemma `alternatizeUncurryFinCLM_apply` / 引理 `alternatizeUncurryFinCLM_apply`

English:
lemma alternatizeUncurryFinCLM_apply
  given: (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F)
  proof: rfl

中文:
引理 alternatizeUncurryFinCLM_apply
  条件: (f : E ->L[𝕜] E [⋀^有限集 n]->L[𝕜] F)
  证明: rfl
-/
lemma alternatizeUncurryFinCLM_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) :
    alternatizeUncurryFinCLM 𝕜 E F f = alternatizeUncurryFin f :=
  rfl

/--
lemma `norm_alternatizeUncurryFin_le` / 引理 `norm_alternatizeUncurryFin_le`

English:
lemma norm_alternatizeUncurryFin_le
  given: (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F)
  proof: (alternatizeUncurryFinCLM 𝕜 E F).le_of_opNorm_le norm_alternatizeUncurryFinCLM_le f

中文:
引理 norm_alternatizeUncurryFin_le
  条件: (f : E ->L[𝕜] E [⋀^有限集 n]->L[𝕜] F)
  证明: (alternatizeUncurryFinCLM 𝕜 E F).le_of_opNorm_le norm_alternatizeUncurryFinCLM_le f

Depends on / 依赖: alternatizeUncurryFinCLM, le_of_opNorm_le, norm_alternatizeUncurryFinCLM_le
-/
lemma norm_alternatizeUncurryFin_le (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) :
    ‖alternatizeUncurryFin f‖ <= (n + 1) * ‖f‖ :=
  (alternatizeUncurryFinCLM 𝕜 E F).le_of_opNorm_le norm_alternatizeUncurryFinCLM_le f

/--
theorem `alternatizeUncurryFin_apply` / 定理 `alternatizeUncurryFin_apply`

English:
theorem alternatizeUncurryFin_apply
  given: (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 1) -> E)
  proof: by
  rw [alternatizeUncurryFin]; rw [alternatizeUncurryFinCLM]
  apply alternatizeUncurryFinCLM.aux_apply

中文:
定理 alternatizeUncurryFin_apply
  条件: (f : E ->L[𝕜] E [⋀^有限集 n]->L[𝕜] F) (v : 有限集 (n + 1) -> E)
  证明: by
  rw [alternatizeUncurryFin]; rw [alternatizeUncurryFinCLM]
  apply alternatizeUncurryFinCLM.aux_apply

Depends on / 依赖: alternatizeUncurryFin, alternatizeUncurryFinCLM, alternatizeUncurryFinCLM.aux_apply, aux_apply
-/
theorem alternatizeUncurryFin_apply (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 1) -> E) :
    alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : Nat) • f (v i) (removeNth i v) := by
  rw [alternatizeUncurryFin]; rw [alternatizeUncurryFinCLM]
  apply alternatizeUncurryFinCLM.aux_apply

/--
lemma `toAlternatingMap_alternatizeUncurryFin` / 引理 `toAlternatingMap_alternatizeUncurryFin`

English:
lemma toAlternatingMap_alternatizeUncurryFin
  given: (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F)
  proof: by
  ext
  simp [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]

@[simp]

中文:
引理 toAlternatingMap_alternatizeUncurryFin
  条件: (f : E ->L[𝕜] E [⋀^有限集 n]->L[𝕜] F)
  证明: by
  ext
  simp [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.alternatizeUncurryFin_apply, alternatizeUncurryFin_apply
-/
lemma toAlternatingMap_alternatizeUncurryFin (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) :
    (alternatizeUncurryFin f).toAlternatingMap =
      .alternatizeUncurryFin (toAlternatingMapLinear ∘ₗ (f : E ->ₗ[𝕜] E [⋀^Fin n]->L[𝕜] F)) := by
  ext
  simp [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]

@[simp]
/--
theorem `alternatizeUncurryFin_add` / 定理 `alternatizeUncurryFin_add`

English:
theorem alternatizeUncurryFin_add
  given: (f g : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F)
  proof: map_add (alternatizeUncurryFinCLM 𝕜 E F) f g

@[simp]

中文:
定理 alternatizeUncurryFin_add
  条件: (f g : E ->L[𝕜] E [⋀^有限集 n]->L[𝕜] F)
  证明: map_add (alternatizeUncurryFinCLM 𝕜 E F) f g

@[simp]

Depends on / 依赖: alternatizeUncurryFinCLM, map_add
-/
theorem alternatizeUncurryFin_add (f g : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) :
    alternatizeUncurryFin (f + g) = alternatizeUncurryFin f + alternatizeUncurryFin g :=
  map_add (alternatizeUncurryFinCLM 𝕜 E F) f g

@[simp]
/--
lemma `alternatizeUncurryFin_curryLeft` / 引理 `alternatizeUncurryFin_curryLeft`

English:
lemma alternatizeUncurryFin_curryLeft
  given: (f : E [⋀^Fin (n + 1)]->L[𝕜] F)
  proof: by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

@[simp]

中文:
引理 alternatizeUncurryFin_curryLeft
  条件: (f : E [⋀^有限集 (n + 1)]->L[𝕜] F)
  证明: by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

@[simp]

Depends on / 依赖: alternatizeUncurryFin_apply, map_insertNth
-/
lemma alternatizeUncurryFin_curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) :
    alternatizeUncurryFin (curryLeft f) = (n + 1) • f := by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

@[simp]
/--
theorem `alternatizeUncurryFin_smul` / 定理 `alternatizeUncurryFin_smul`

English:
theorem alternatizeUncurryFin_smul
  statement: {S : Type*} [Monoid S] [DistribMulAction S F]
  proof: by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]

中文:
定理 alternatizeUncurryFin_smul
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S F]
  证明: by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]

Depends on / 依赖: Finset, Finset.smul_sum, alternatizeUncurryFin_apply, smul_comm, smul_sum
-/
theorem alternatizeUncurryFin_smul {S : Type*} [Monoid S] [DistribMulAction S F]
    [ContinuousConstSMul S F] [SMulCommClass 𝕜 S F] (c : S) (f : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) :
    alternatizeUncurryFin (c • f) = c • alternatizeUncurryFin f := by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]

/--
theorem `alternatizeUncurryFin_constOfIsEmptyLIE_comp` / 定理 `alternatizeUncurryFin_constOfIsEmptyLIE_comp`

English:
theorem alternatizeUncurryFin_constOfIsEmptyLIE_comp
  given: (f : E ->L[𝕜] F)
  proof: by
  ext
  simp [alternatizeUncurryFin_apply]

中文:
定理 alternatizeUncurryFin_constOfIsEmptyLIE_comp
  条件: (f : E ->L[𝕜] F)
  证明: by
  ext
  simp [alternatizeUncurryFin_apply]

Depends on / 依赖: alternatizeUncurryFin_apply
-/
theorem alternatizeUncurryFin_constOfIsEmptyLIE_comp (f : E ->L[𝕜] F) :
    alternatizeUncurryFin (constOfIsEmptyLIE 𝕜 E F (Fin 0) ∘L f) =
      ofSubsingleton _ _ _ (0 : Fin 1) f := by
  ext
  simp [alternatizeUncurryFin_apply]

/--
theorem `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply` / 定理 `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply`

English:
theorem alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply
  proof: by
  simpa [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]
    using AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
      (R := 𝕜) (M := E) (N := F)
      (f.toLinearMap₁₂.compr₂ (toAlternatingMapLinear (R := 𝕜))) v

中文:
定理 alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply
  证明: by
  simpa [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]
    using AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
      (R := 𝕜) (M := E) (N := F)
      (f.toLinearMap₁₂.compr₂ (toAlternatingMapLinear (R := 𝕜))) v

Depends on / 依赖: AlternatingMap, AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply, AlternatingMap.alternatizeUncurryFin_apply, alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply, alternatizeUncurryFin_apply, f.toLinearMap, toAlternatingMapLinear
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply
    (f : E ->L[𝕜] E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) (v : Fin (n + 2) -> E) :
    alternatizeUncurryFin (alternatizeUncurryFinCLM 𝕜 E F ∘L f) v =
      ∑ (i : Fin (n + 1)), ∑ j >= i,
        (-1 : Int) ^ (i + j : Nat) •
          (f (v i.castSucc) (v j.succ) (j.removeNth <| i.castSucc.removeNth v) -
            f (v j.succ) (v i.castSucc) (j.removeNth <| i.castSucc.removeNth v)) := by
  simpa [alternatizeUncurryFin_apply, AlternatingMap.alternatizeUncurryFin_apply]
    using AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
      (R := 𝕜) (M := E) (N := F)
      (f.toLinearMap₁₂.compr₂ (toAlternatingMapLinear (R := 𝕜))) v

/--
theorem `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric` / 定理 `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric`

English:
theorem alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
  proof: by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply, hf]

中文:
定理 alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
  证明: by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply, hf]

Depends on / 依赖: alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
    {f : E ->L[𝕜] E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F}
    (hf : forall x y, f x y = f y x) :
    alternatizeUncurryFin (alternatizeUncurryFinCLM 𝕜 E F ∘L f) = 0 := by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_apply, hf]

/--
theorem `fderivCompContinuousLinearMap_eq_alternatizeUncurryFin` / 定理 `fderivCompContinuousLinearMap_eq_alternatizeUncurryFin`

English:
theorem fderivCompContinuousLinearMap_eq_alternatizeUncurryFin
  statement: (f : F [⋀^Fin (n + 1)]->L[𝕜] G)
  proof: by
  ext dg v
  have (i j : Fin (n + 1)) :
      i.insertNth (α := fun _ => E ->L[𝕜] F) dg (fun _ => g) j (v j) =
        i.insertNth (α := fun _ => F) (dg (v i)) (g ∘ i.removeNth v) j := by
    cases j using i.succAboveCases <;> simp [Fin.removeNth]
  simp [alternatizeUncurryFin_apply, ← Fin.insertNth_removeNth, Fin.removeNth_fun_const,
    ← map_insertNth, this]

中文:
定理 fderivCompContinuousLinearMap_eq_alternatizeUncurryFin
  结论: (f : F [⋀^有限集 (n + 1)]->L[𝕜] G)
  证明: by
  ext dg v
  have (i j : Fin (n + 1)) :
      i.insertNth (α := fun _ => E ->L[𝕜] F) dg (fun _ => g) j (v j) =
        i.insertNth (α := fun _ => F) (dg (v i)) (g ∘ i.removeNth v) j := by
    cases j using i.succAboveCases <;> simp [Fin.removeNth]
  simp [alternatizeUncurryFin_apply, ← Fin.insertNth_removeNth, Fin.removeNth_fun_const,
    ← map_insertNth, this]

Depends on / 依赖: Fin.insertNth_removeNth, Fin.removeNth, Fin.removeNth_fun_const, alternatizeUncurryFin_apply, i.insertNth, i.removeNth, i.succAboveCases, insertNth, insertNth_removeNth, map_insertNth, removeNth, removeNth_fun_const, succAboveCases
-/
theorem fderivCompContinuousLinearMap_eq_alternatizeUncurryFin (f : F [⋀^Fin (n + 1)]->L[𝕜] G)
    (g : E ->L[𝕜] F) :
    f.fderivCompContinuousLinearMap g = alternatizeUncurryFinCLM 𝕜 E G ∘L
      ((compContinuousLinearMapCLM g ∘L f.curryLeft).postcomp E) := by
  ext dg v
  have (i j : Fin (n + 1)) :
      i.insertNth (α := fun _ => E ->L[𝕜] F) dg (fun _ => g) j (v j) =
        i.insertNth (α := fun _ => F) (dg (v i)) (g ∘ i.removeNth v) j := by
    cases j using i.succAboveCases <;> simp [Fin.removeNth]
  simp [alternatizeUncurryFin_apply, ← Fin.insertNth_removeNth, Fin.removeNth_fun_const,
    ← map_insertNth, this]

/--
theorem `alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero` / 定理 `alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero`

English:
theorem alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero
  statement: (f : F [⋀^Fin n]->L[𝕜] G)
  proof: by
  cases n with
  | zero =>
    simp [fderivCompContinuousLinearMap_of_isEmpty, ← alternatizeUncurryFinCLM_apply]
  | succ n =>
    rw [fderivCompContinuousLinearMap_eq_alternatizeUncurryFin]; rw [ContinuousLinearMap.comp_assoc]; rw [alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric]
    intro x y
    ext v
    simp [hsymm]

中文:
定理 alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero
  结论: (f : F [⋀^有限集 n]->L[𝕜] G)
  证明: by
  cases n with
  | zero =>
    simp [fderivCompContinuousLinearMap_of_isEmpty, ← alternatizeUncurryFinCLM_apply]
  | succ n =>
    rw [fderivCompContinuousLinearMap_eq_alternatizeUncurryFin]; rw [ContinuousLinearMap.comp_assoc]; rw [alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric]
    intro x y
    ext v
    simp [hsymm]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_assoc, alternatizeUncurryFinCLM_apply, alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric, comp_assoc, fderivCompContinuousLinearMap_eq_alternatizeUncurryFin, fderivCompContinuousLinearMap_of_isEmpty
-/
theorem alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero (f : F [⋀^Fin n]->L[𝕜] G)
    (g : E ->L[𝕜] F) {h : E ->L[𝕜] E ->L[𝕜] F} (hsymm : forall x y, h x y = h y x) :
    alternatizeUncurryFin (f.fderivCompContinuousLinearMap g ∘L h) = 0 := by
  cases n with
  | zero =>
    simp [fderivCompContinuousLinearMap_of_isEmpty, ← alternatizeUncurryFinCLM_apply]
  | succ n =>
    rw [fderivCompContinuousLinearMap_eq_alternatizeUncurryFin]; rw [ContinuousLinearMap.comp_assoc]; rw [alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric]
    intro x y
    ext v
    simp [hsymm]

end ContinuousAlternatingMap
