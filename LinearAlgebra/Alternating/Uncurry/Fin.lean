/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fin.Parity

/-!
# Uncurrying alternating maps

Given a function `f` which is linear in the first argument
and is alternating form in the other `n` arguments,
this file defines an alternating form `AlternatingMap.alternatizeUncurryFin f` in `n + 1` arguments.

This function is given by
```
AlternatingMap.alternatizeUncurryFin f v =
  ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Given an alternating map `f` of `n + 1` arguments,
each term in the sum above written for `f.curryLeft` equals the original map,
thus `f.curryLeft.alternatizeUncurryFin = (n + 1) • f`.

We do not multiply the result of `alternatizeUncurryFin` by `(n + 1)⁻¹`
so that the construction works for `R`-multilinear maps over any commutative ring `R`,
not only a field of characteristic zero.

## Main results

- `AlternatingMap.alternatizeUncurryFin_curryLeft`:
  the round-trip formula for currying/uncurrying, see above.

- `AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric`:
  If `f` is a symmetric bilinear map taking values in the space of alternating maps,
  then the twice uncurried `f` is zero.

A version of the latter theorem for continuous alternating maps
will be used to prove that the second exterior derivative of a differential form is zero.
-/

@[expose] public section

open Fin Function

namespace AlternatingMap

variable {R : Type*} {M M₂ N N₂ : Type*} [CommRing R] [AddCommGroup M]
  [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : Nat}

/--
theorem `map_insertNth` / 定理 `map_insertNth`

English:
theorem map_insertNth
  given: (f : M [⋀^Fin (n + 1)]->ₗ[R] N) (p : Fin (n + 1)) (x : M) (v : Fin n -> M)
  proof: by
  rw [← cons_comp_cycleRange]; rw [map_perm]; rw [Matrix.vecCons]
  simp [Units.smul_def]

中文:
定理 map_insertNth
  条件: (f : M [⋀^有限集 (n + 1)]->ₗ[R] N) (p : 有限集 (n + 1)) (x : M) (v : 有限集 n -> M)
  证明: by
  rw [← cons_comp_cycleRange]; rw [map_perm]; rw [Matrix.vecCons]
  simp [Units.smul_def]

Depends on / 依赖: Matrix, Matrix.vecCons, StandardBorelSpace, Units.smul_def, cons_comp_cycleRange, map_perm, measurableSingleton_of_standardBorel, smul_def, vecCons
-/
theorem map_insertNth (f : M [⋀^Fin (n + 1)]->ₗ[R] N) (p : Fin (n + 1)) (x : M) (v : Fin n -> M) :
    f (p.insertNth x v) = (-1) ^ (p : Nat) • f (Matrix.vecCons x v) := by
  rw [← cons_comp_cycleRange]; rw [map_perm]; rw [Matrix.vecCons]
  simp [Units.smul_def]

/--
theorem `neg_one_pow_smul_map_insertNth` / 定理 `neg_one_pow_smul_map_insertNth`

English:
theorem neg_one_pow_smul_map_insertNth
  statement: (f : M [⋀^Fin (n + 1)]->ₗ[R] N) (p : Fin (n + 1)) (x : M)
  proof: by
  rw [map_insertNth]; rw [smul_smul]; rw [← pow_add]; rw [Even.neg_one_pow]; rw [one_smul]
  use p

中文:
定理 neg_one_pow_smul_map_insertNth
  结论: (f : M [⋀^有限集 (n + 1)]->ₗ[R] N) (p : 有限集 (n + 1)) (x : M)
  证明: by
  rw [map_insertNth]; rw [smul_smul]; rw [← pow_add]; rw [Even.neg_one_pow]; rw [one_smul]
  use p

Depends on / 依赖: Even.neg_one_pow, map_insertNth, neg_one_pow, one_smul, pow_add, smul_smul
-/
theorem neg_one_pow_smul_map_insertNth (f : M [⋀^Fin (n + 1)]->ₗ[R] N) (p : Fin (n + 1)) (x : M)
    (v : Fin n -> M) :
    (-1) ^ (p : Nat) • f (p.insertNth x v) = f (Matrix.vecCons x v) := by
  rw [map_insertNth]; rw [smul_smul]; rw [← pow_add]; rw [Even.neg_one_pow]; rw [one_smul]
  use p

/--
theorem `neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq` / 定理 `neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq`

English:
theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq
  statement: (f : M [⋀^Fin n]->ₗ[R] N)
  proof: by
  rcases exists_succAbove_eq hij with ⟨i, rfl⟩
  obtain ⟨m, rfl⟩ : exists m, m + 1 = n := by simp [i.pos]
  rw [← (i.predAbove j).insertNth_self_removeNth (removeNth _ _)]; rw [← removeNth_removeNth_eq_swap]; rw [removeNth]; rw [succAbove_succAbove_predAbove]; rw [map_insertNth]; rw [← neg_one_po

中文:
定理 neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq
  结论: (f : M [⋀^有限集 n]->ₗ[R] N)
  证明: by
  rcases exists_succAbove_eq hij with ⟨i, rfl⟩
  obtain ⟨m, rfl⟩ : exists m, m + 1 = n := by simp [i.pos]
  rw [← (i.predAbove j).insertNth_self_removeNth (removeNth _ _)]; rw [← removeNth_removeNth_eq_swap]; rw [removeNth]; rw [succAbove_succAbove_predAbove]; rw [map_insertNth]; rw [← neg_one_po

Depends on / 依赖: exists_succAbove_eq, i.pos, i.predAbove, insertNth_removeNth, insertNth_self_removeNth, map_insertNth, mul_smul, neg_one_pow_smul_map_insertNth, neg_one_pow_succAbove_add_predAbove, neg_smul, pow_add, predAbove, removeNth, removeNth_removeNth_eq_swap, smul_smu, smul_smul, succAbove_succAbove_predAbove, update_eq_self_iff
-/
theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : M [⋀^Fin n]->ₗ[R] N)
    {v : Fin (n + 1) -> M} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i != j) :
    (-1) ^ (i : Nat) • f (i.removeNth v) + (-1) ^ (j : Nat) • f (j.removeNth v) = 0 := by
  rcases exists_succAbove_eq hij with ⟨i, rfl⟩
  obtain ⟨m, rfl⟩ : exists m, m + 1 = n := by simp [i.pos]
  rw [← (i.predAbove j).insertNth_self_removeNth (removeNth _ _)]; rw [← removeNth_removeNth_eq_swap]; rw [removeNth]; rw [succAbove_succAbove_predAbove]; rw [map_insertNth]; rw [← neg_one_pow_smul_map_insertNth]; rw [insertNth_removeNth]; rw [update_eq_self_iff.2]; rw [smul_smul]; rw [← pow_add]; rw [neg_one_pow_succAbove_add_predAbove]; rw [neg_smul]; rw [pow_add]; rw [mul_smul]; rw [smul_smul (_ ^ i.val)]; rw [← sq]; rw [← pow_mul]; rw [pow_mul']; rw [neg_one_pow_two]; rw [one_pow]; rw [one_smul]; rw [neg_add_cancel]
  exact hvij.symm

/--
Definition of `alternatizeUncurryFin` / `alternatizeUncurryFin` 的定义

English:
definition alternatizeUncurryFin
  signature: (f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N)
  body: ∑ p : Fin (n + 1), (-1) ^ (p : Nat) • LinearMap.uncurryMid p (toMultilinearMapLM ∘ₗ f)
  map_eq_zero_of_eq' := by
    intro v i j hvij hij
    suffices ∑ k : Fin (n + 1), (-1) ^ (k : Nat) • f (v k) (k.removeNth v) = 0 by simpa
    calc
      _ = (-1) ^ (i : Nat) • f (v i) (i.removeNth v) + (-1) ^ (j

中文:
定义 alternatizeUncurryFin
  签名: (f : M ->ₗ[R] M [⋀^有限集 n]->ₗ[R] N)
  定义体: ∑ p : Fin (n + 1), (-1) ^ (p : Nat) • LinearMap.uncurryMid p (toMultilinearMapLM ∘ₗ f)
  map_eq_zero_of_eq' := by
    intro v i j hvij hij
    suffices ∑ k : Fin (n + 1), (-1) ^ (k : Nat) • f (v k) (k.removeNth v) = 0 by simpa
    calc
      _ = (-1) ^ (i : Nat) • f (v i) (i.removeNth v) + (-1) ^ (j

Depends on / 依赖: Fintype, Fintype.sum_eq_add, LinearMap, LinearMap.uncurryMid, exists_succAbove_eq, hki.symm, hkj.symm, i.removeNth, j.removeNth, k.removeNth, map_eq_ze, map_eq_zero_of_eq, removeNth, sum_eq_add, toMultilinearMapLM, uncurryMid
-/
def alternatizeUncurryFin (f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) :
    M [⋀^Fin (n + 1)]->ₗ[R] N where
  toMultilinearMap :=
    ∑ p : Fin (n + 1), (-1) ^ (p : Nat) • LinearMap.uncurryMid p (toMultilinearMapLM ∘ₗ f)
  map_eq_zero_of_eq' := by
    intro v i j hvij hij
    suffices ∑ k : Fin (n + 1), (-1) ^ (k : Nat) • f (v k) (k.removeNth v) = 0 by simpa
    calc
      _ = (-1) ^ (i : Nat) • f (v i) (i.removeNth v) + (-1) ^ (j : Nat) • f (v j) (j.removeNth v) := by
        refine Fintype.sum_eq_add _ _ hij fun k ⟨hki, hkj⟩ => ?_
        rcases exists_succAbove_eq hki.symm with ⟨i, rfl⟩
        rcases exists_succAbove_eq hkj.symm with ⟨j, rfl⟩
        rw [(f (v k)).map_eq_zero_of_eq _ hvij (ne_of_apply_ne _ hij)]; rw [smul_zero]
      _ = 0 := by
        rw [hvij]; rw [neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq] <;> assumption

/--
theorem `alternatizeUncurryFin_apply` / 定理 `alternatizeUncurryFin_apply`

English:
theorem alternatizeUncurryFin_apply
  given: (f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 1) -> M)
  proof: by
  simp [alternatizeUncurryFin]

@[simp]

中文:
定理 alternatizeUncurryFin_apply
  条件: (f : M ->ₗ[R] M [⋀^有限集 n]->ₗ[R] N) (v : 有限集 (n + 1) -> M)
  证明: by
  simp [alternatizeUncurryFin]

@[simp]

Depends on / 依赖: alternatizeUncurryFin
-/
theorem alternatizeUncurryFin_apply (f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 1) -> M) :
    alternatizeUncurryFin f v = ∑ i : Fin (n + 1), (-1) ^ (i : Nat) • f (v i) (removeNth i v) := by
  simp [alternatizeUncurryFin]

@[simp]
/--
theorem `alternatizeUncurryFin_add` / 定理 `alternatizeUncurryFin_add`

English:
theorem alternatizeUncurryFin_add
  given: (f g : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N)
  proof: by
  ext
  simp [alternatizeUncurryFin_apply, Finset.sum_add_distrib]

@[simp]

中文:
定理 alternatizeUncurryFin_add
  条件: (f g : M ->ₗ[R] M [⋀^有限集 n]->ₗ[R] N)
  证明: by
  ext
  simp [alternatizeUncurryFin_apply, Finset.sum_add_distrib]

@[simp]

Depends on / 依赖: Finset, Finset.sum_add_distrib, alternatizeUncurryFin_apply, sum_add_distrib
-/
theorem alternatizeUncurryFin_add (f g : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) :
    alternatizeUncurryFin (f + g) = alternatizeUncurryFin f + alternatizeUncurryFin g := by
  ext
  simp [alternatizeUncurryFin_apply, Finset.sum_add_distrib]

@[simp]
/--
lemma `alternatizeUncurryFin_curryLeft` / 引理 `alternatizeUncurryFin_curryLeft`

English:
lemma alternatizeUncurryFin_curryLeft
  given: (f : M [⋀^Fin (n + 1)]->ₗ[R] N)
  proof: by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

中文:
引理 alternatizeUncurryFin_curryLeft
  条件: (f : M [⋀^有限集 (n + 1)]->ₗ[R] N)
  证明: by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

Depends on / 依赖: alternatizeUncurryFin_apply, map_insertNth
-/
lemma alternatizeUncurryFin_curryLeft (f : M [⋀^Fin (n + 1)]->ₗ[R] N) :
    alternatizeUncurryFin (curryLeft f) = (n + 1) • f := by
  ext v
  simp [alternatizeUncurryFin_apply, ← map_insertNth]

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

@[simp]
/--
theorem `alternatizeUncurryFin_smul` / 定理 `alternatizeUncurryFin_smul`

English:
theorem alternatizeUncurryFin_smul
  given: (c : S) (f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N)
  proof: by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]

中文:
定理 alternatizeUncurryFin_smul
  条件: (c : S) (f : M ->ₗ[R] M [⋀^有限集 n]->ₗ[R] N)
  证明: by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]

Depends on / 依赖: Finset, Finset.smul_sum, alternatizeUncurryFin_apply, smul_comm, smul_sum
-/
theorem alternatizeUncurryFin_smul (c : S) (f : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) :
    alternatizeUncurryFin (c • f) = c • alternatizeUncurryFin f := by
  ext v
  simp [alternatizeUncurryFin_apply, smul_comm _ c, Finset.smul_sum]

/-- `AlternatingMap.alternatizeUncurryFin` as a linear map. -/
@[simps! apply]
/--
Definition of `alternatizeUncurryFinLM` / `alternatizeUncurryFinLM` 的定义

English:
definition alternatizeUncurryFinLM
  signature: : (M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) ->ₗ[R] M [⋀^Fin (n + 1)]->ₗ[R] N where
  body: alternatizeUncurryFin
  map_add' := alternatizeUncurryFin_add
  map_smul' := alternatizeUncurryFin_smul

中文:
定义 alternatizeUncurryFinLM
  签名: : (M ->ₗ[R] M [⋀^有限集 n]->ₗ[R] N) ->ₗ[R] M [⋀^有限集 (n + 1)]->ₗ[R] N where
  定义体: alternatizeUncurryFin
  map_add' := alternatizeUncurryFin_add
  map_smul' := alternatizeUncurryFin_smul

Depends on / 依赖: alternatizeUncurryFin
-/
def alternatizeUncurryFinLM : (M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) ->ₗ[R] M [⋀^Fin (n + 1)]->ₗ[R] N where
  toFun := alternatizeUncurryFin
  map_add' := alternatizeUncurryFin_add
  map_smul' := alternatizeUncurryFin_smul

/--
theorem `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply` / 定理 `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply`

English:
theorem alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
  proof: by
  simp only [alternatizeUncurryFin_apply, Int.reduceNeg, LinearMap.coe_comp, comp_apply,
    alternatizeUncurryFinLM_apply, Finset.smul_sum, sum_sum_eq_sum_triangle_add, val_castSucc,
    val_succ]
  refine Fintype.sum_congr _ _ fun i => Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ici] a

中文:
定理 alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
  证明: by
  simp only [alternatizeUncurryFin_apply, Int.reduceNeg, LinearMap.coe_comp, comp_apply,
    alternatizeUncurryFinLM_apply, Finset.smul_sum, sum_sum_eq_sum_triangle_add, val_castSucc,
    val_succ]
  refine Fintype.sum_congr _ _ fun i => Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ici] a

Depends on / 依赖: Fin.removeNth_apply, Fin.succAbove_of_, Fin.succAbove_of_le_castSucc, Finset, Finset.mem_Ici, Finset.smul_sum, Finset.sum_congr, Fintype, Fintype.sum_congr, Int.reduceNeg, LinearMap, LinearMap.coe_comp, alternatizeUncurryFinLM_apply, alternatizeUncurryFin_apply, castSucc, coe_comp, comp_apply, i.castSucc, i.castSucc.removeNth, j.succ
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply
    (f : M ->ₗ[R] M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N) (v : Fin (n + 2) -> M) :
    alternatizeUncurryFin (alternatizeUncurryFinLM ∘ₗ f) v =
      ∑ (i : Fin (n + 1)), ∑ j >= i,
        (-1 : Int) ^ (i + j : Nat) •
          (f (v i.castSucc) (v j.succ) (j.removeNth <| i.castSucc.removeNth v) -
            f (v j.succ) (v i.castSucc) (j.removeNth <| i.castSucc.removeNth v)) := by
  simp only [alternatizeUncurryFin_apply, Int.reduceNeg, LinearMap.coe_comp, comp_apply,
    alternatizeUncurryFinLM_apply, Finset.smul_sum, sum_sum_eq_sum_triangle_add, val_castSucc,
    val_succ]
  refine Fintype.sum_congr _ _ fun i => Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ici] at hj
  have H₁ : i.castSucc.removeNth v j = v j.succ := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.succ.removeNth v i = v i.castSucc := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_castSucc_lt, hj]
  simp only [pow_add, mul_smul, pow_one, neg_one_smul, smul_neg, smul_sub, ← sub_eq_add_neg,
    smul_comm ((-1 : Int) ^ (j : Nat)), H₁, H₂]
  congr 4
  rw [removeNth_removeNth_eq_swap]
  simp [Fin.predAbove, hj, Fin.succAbove]

/--
theorem `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric` / 定理 `alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric`

English:
theorem alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
  proof: by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply, hf (v <| .castSucc _)]

中文:
定理 alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
  证明: by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply, hf (v <| .castSucc _)]

Depends on / 依赖: alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply, castSucc
-/
theorem alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
    {f : M ->ₗ[R] M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N} (hf : forall x y, f x y = f y x) :
    alternatizeUncurryFin (alternatizeUncurryFinLM ∘ₗ f) = 0 := by
  ext v
  simp [alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply, hf (v <| .castSucc _)]

end AlternatingMap
