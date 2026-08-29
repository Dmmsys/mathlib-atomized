/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Currying and uncurrying continuous multilinear maps

We associate to a continuous multilinear map in `n+1` variables (i.e., based on `Fin n.succ`) two
curried functions, named `f.curryLeft` (which is a continuous linear map on `E 0` taking values
in continuous multilinear maps in `n` variables) and `f.curryRight` (which is a continuous
multilinear map in `n` variables taking values in continuous linear maps on `E (last n)`).
The inverse operations are called `uncurryLeft` and `uncurryRight`.

We also register continuous linear equiv versions of these correspondences, in
`continuousMultilinearCurryLeftEquiv` and `continuousMultilinearCurryRightEquiv`.

## Main results

* `ContinuousMultilinearMap.curryLeft`, `ContinuousLinearMap.uncurryLeft` and
  `continuousMultilinearCurryLeftEquiv`
* `ContinuousMultilinearMap.curryRight`, `ContinuousMultilinearMap.uncurryRight` and
  `continuousMultilinearCurryRightEquiv`.
* `ContinuousMultilinearMap.curryMid`, `ContinuousLinearMap.uncurryMid` and
  `ContinuousMultilinearMap.curryMidEquiv`
-/

@[expose] public section

suppress_compilation

noncomputable section

open NNReal Finset Metric ContinuousMultilinearMap Fin Function

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a `NontriviallyNormedField`;
* `ι`, `ι'` : finite index types with decidable equality;
* `E`, `E₁` : families of normed vector spaces over `𝕜` indexed by `i : ι`;
* `E'` : a family of normed vector spaces over `𝕜` indexed by `i' : ι'`;
* `Ei` : a family of normed vector spaces over `𝕜` indexed by `i : Fin (Nat.succ n)`;
* `G`, `G'` : normed vector spaces over `𝕜`.
-/


universe u v v' wE wE₁ wE' wEi wG wG'

variable {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {n : Nat} {E : ι -> Type wE}
  {Ei : Fin n.succ -> Type wEi} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [Fintype ι'] [NontriviallyNormedField 𝕜] [forall i, NormedAddCommGroup (E i)]
  [forall i, NormedSpace 𝕜 (E i)] [forall i, NormedAddCommGroup (Ei i)] [forall i, NormedSpace 𝕜 (Ei i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

/--
theorem `ContinuousLinearMap.norm_map_removeNth_le` / 定理 `ContinuousLinearMap.norm_map_removeNth_le`

English:
theorem ContinuousLinearMap.norm_map_removeNth_le
  statement: {i : Fin (n + 1)}
  proof: by
  rw [i.prod_univ_succAbove]; rw [← mul_assoc]
  exact (f (m i)).le_of_opNorm_le (f.le_opNorm _) _

中文:
定理 连续线性映射.norm_map_removeNth_le
  结论: {i : 有限集 (n + 1)}
  证明: by
  rw [i.prod_univ_succAbove]; rw [← mul_assoc]
  exact (f (m i)).le_of_opNorm_le (f.le_opNorm _) _

Depends on / 依赖: f.le_opNorm, i.prod_univ_succAbove, le_of_opNorm_le, le_opNorm, mul_assoc, prod_univ_succAbove
-/
theorem ContinuousLinearMap.norm_map_removeNth_le {i : Fin (n + 1)}
    (f : Ei i ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun j => Ei (i.succAbove j)) G) (m : forall i, Ei i) :
    ‖f (m i) (i.removeNth m)‖ <= ‖f‖ * ∏ j, ‖m j‖ := by
  rw [i.prod_univ_succAbove]; rw [← mul_assoc]
  exact (f (m i)).le_of_opNorm_le (f.le_opNorm _) _

/--
theorem `ContinuousLinearMap.norm_map_tail_le` / 定理 `ContinuousLinearMap.norm_map_tail_le`

English:
theorem ContinuousLinearMap.norm_map_tail_le
  proof: ContinuousLinearMap.norm_map_removeNth_le (i := 0) f m

中文:
定理 连续线性映射.norm_map_tail_le
  证明: ContinuousLinearMap.norm_map_removeNth_le (i := 0) f m

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_map_removeNth_le, norm_map_removeNth_le
-/
theorem ContinuousLinearMap.norm_map_tail_le
    (f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : forall i, Ei i) :
    ‖f (m 0) (tail m)‖ <= ‖f‖ * ∏ i, ‖m i‖ :=
  ContinuousLinearMap.norm_map_removeNth_le (i := 0) f m

/--
theorem `ContinuousMultilinearMap.norm_map_init_le` / 定理 `ContinuousMultilinearMap.norm_map_init_le`

English:
theorem ContinuousMultilinearMap.norm_map_init_le
  proof: by
  rw [prod_univ_castSucc]; rw [← mul_assoc]
  exact (f (init m)).le_of_opNorm_le (f.le_opNorm _) _

中文:
定理 连续多重线性映射.norm_map_init_le
  证明: by
  rw [prod_univ_castSucc]; rw [← mul_assoc]
  exact (f (init m)).le_of_opNorm_le (f.le_opNorm _) _

Depends on / 依赖: f.le_opNorm, le_of_opNorm_le, le_opNorm, mul_assoc, prod_univ_castSucc
-/
theorem ContinuousMultilinearMap.norm_map_init_le
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G))
    (m : forall i, Ei i) : ‖f (init m) (m (last n))‖ <= ‖f‖ * ∏ i, ‖m i‖ := by
  rw [prod_univ_castSucc]; rw [← mul_assoc]
  exact (f (init m)).le_of_opNorm_le (f.le_opNorm _) _

/--
theorem `ContinuousMultilinearMap.norm_map_insertNth_le` / 定理 `ContinuousMultilinearMap.norm_map_insertNth_le`

English:
theorem ContinuousMultilinearMap.norm_map_insertNth_le
  statement: (f : ContinuousMultilinearMap 𝕜 Ei G)
  proof: by
  simpa [i.prod_univ_succAbove, mul_assoc] using f.le_opNorm (i.insertNth x m)

中文:
定理 连续多重线性映射.norm_map_insertNth_le
  结论: (f : 连续多重线性映射 𝕜 Ei G)
  证明: by
  simpa [i.prod_univ_succAbove, mul_assoc] using f.le_opNorm (i.insertNth x m)

Depends on / 依赖: f.le_opNorm, i.insertNth, i.prod_univ_succAbove, insertNth, le_opNorm, mul_assoc, prod_univ_succAbove
-/
theorem ContinuousMultilinearMap.norm_map_insertNth_le (f : ContinuousMultilinearMap 𝕜 Ei G)
    {i : Fin (n + 1)} (x : Ei i) (m : forall j, Ei (i.succAbove j)) :
    ‖f (i.insertNth x m)‖ <= ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ := by
  simpa [i.prod_univ_succAbove, mul_assoc] using f.le_opNorm (i.insertNth x m)

/--
theorem `ContinuousMultilinearMap.norm_map_cons_le` / 定理 `ContinuousMultilinearMap.norm_map_cons_le`

English:
theorem ContinuousMultilinearMap.norm_map_cons_le
  statement: (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
  proof: by
  simpa [prod_univ_succ, mul_assoc] using f.le_opNorm (cons x m)

中文:
定理 连续多重线性映射.norm_map_cons_le
  结论: (f : 连续多重线性映射 𝕜 Ei G) (x : Ei 0)
  证明: by
  simpa [prod_univ_succ, mul_assoc] using f.le_opNorm (cons x m)

Depends on / 依赖: f.le_opNorm, le_opNorm, mul_assoc, prod_univ_succ
-/
theorem ContinuousMultilinearMap.norm_map_cons_le (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
    (m : forall i : Fin n, Ei i.succ) : ‖f (cons x m)‖ <= ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ := by
  simpa [prod_univ_succ, mul_assoc] using f.le_opNorm (cons x m)

/--
theorem `ContinuousMultilinearMap.norm_map_snoc_le` / 定理 `ContinuousMultilinearMap.norm_map_snoc_le`

English:
theorem ContinuousMultilinearMap.norm_map_snoc_le
  statement: (f : ContinuousMultilinearMap 𝕜 Ei G)
  proof: by
  simpa [prod_univ_castSucc, mul_assoc] using f.le_opNorm (snoc m x)

中文:
定理 连续多重线性映射.norm_map_snoc_le
  结论: (f : 连续多重线性映射 𝕜 Ei G)
  证明: by
  simpa [prod_univ_castSucc, mul_assoc] using f.le_opNorm (snoc m x)

Depends on / 依赖: f.le_opNorm, le_opNorm, mul_assoc, prod_univ_castSucc
-/
theorem ContinuousMultilinearMap.norm_map_snoc_le (f : ContinuousMultilinearMap 𝕜 Ei G)
    (m : forall i : Fin n, Ei <| castSucc i) (x : Ei (last n)) :
    ‖f (snoc m x)‖ <= (‖f‖ * ∏ i, ‖m i‖) * ‖x‖ := by
  simpa [prod_univ_castSucc, mul_assoc] using f.le_opNorm (snoc m x)

/-! #### Left currying -/


/--
Definition of `ContinuousLinearMap.uncurryLeft` / `ContinuousLinearMap.uncurryLeft` 的定义

English:
definition ContinuousLinearMap.uncurryLeft
  body: (ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ f.toLinearMap).uncurryLeft.mkContinuous
    ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_tail_le f m

@[simp]

中文:
定义 连续线性映射.uncurryLeft
  定义体: (ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ f.toLinearMap).uncurryLeft.mkContinuous
    ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_tail_le f m

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_map_tail_le, ContinuousMultilinearMap, ContinuousMultilinearMap.toMultilinearMapLinear, f.toLinearMap, mkContinuous, norm_map_tail_le, toLinearMap, toMultilinearMapLinear, uncurryLeft, uncurryLeft.mkContinuous
-/
def ContinuousLinearMap.uncurryLeft
    (f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  (ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ f.toLinearMap).uncurryLeft.mkContinuous
    ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_tail_le f m

@[simp]
/--
theorem `ContinuousLinearMap.uncurryLeft_apply` / 定理 `ContinuousLinearMap.uncurryLeft_apply`

English:
theorem ContinuousLinearMap.uncurryLeft_apply
  proof: rfl

中文:
定理 连续线性映射.uncurryLeft_apply
  证明: rfl
-/
theorem ContinuousLinearMap.uncurryLeft_apply
    (f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : forall i, Ei i) :
    f.uncurryLeft m = f (m 0) (tail m) :=
  rfl

/--
Definition of `ContinuousMultilinearMap.curryLeft` / `ContinuousMultilinearMap.curryLeft` 的定义

English:
definition ContinuousMultilinearMap.curryLeft
  signature: (f : ContinuousMultilinearMap 𝕜 Ei G)
  body: MultilinearMap.mkContinuousLinear f.toMultilinearMap.curryLeft ‖f‖ f.norm_map_cons_le

@[simp]

中文:
定义 连续多重线性映射.curryLeft
  签名: (f : 连续多重线性映射 𝕜 Ei G)
  定义体: MultilinearMap.mkContinuousLinear f.toMultilinearMap.curryLeft ‖f‖ f.norm_map_cons_le

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.mkContinuousLinear, curryLeft, f.norm_map_cons_le, f.toMultilinearMap.curryLeft, mkContinuousLinear, norm_map_cons_le, toMultilinearMap
-/
def ContinuousMultilinearMap.curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G :=
  MultilinearMap.mkContinuousLinear f.toMultilinearMap.curryLeft ‖f‖ f.norm_map_cons_le

@[simp]
/--
theorem `ContinuousMultilinearMap.curryLeft_apply` / 定理 `ContinuousMultilinearMap.curryLeft_apply`

English:
theorem ContinuousMultilinearMap.curryLeft_apply
  statement: (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
  proof: rfl

@[simp]

中文:
定理 连续多重线性映射.curryLeft_apply
  结论: (f : 连续多重线性映射 𝕜 Ei G) (x : Ei 0)
  证明: rfl

@[simp]
-/
theorem ContinuousMultilinearMap.curryLeft_apply (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
    (m : forall i : Fin n, Ei i.succ) : f.curryLeft x m = f (cons x m) :=
  rfl

@[simp]
/--
theorem `ContinuousLinearMap.curry_uncurryLeft` / 定理 `ContinuousLinearMap.curry_uncurryLeft`

English:
theorem ContinuousLinearMap.curry_uncurryLeft
  proof: by
  ext m x
  rw [ContinuousMultilinearMap.curryLeft_apply]; rw [ContinuousLinearMap.uncurryLeft_apply]; rw [tail_cons]; rw [cons_zero]

@[simp]

中文:
定理 连续线性映射.curry_uncurryLeft
  证明: by
  ext m x
  rw [ContinuousMultilinearMap.curryLeft_apply]; rw [ContinuousLinearMap.uncurryLeft_apply]; rw [tail_cons]; rw [cons_zero]

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.uncurryLeft_apply, ContinuousMultilinearMap, ContinuousMultilinearMap.curryLeft_apply, cons_zero, curryLeft_apply, tail_cons, uncurryLeft_apply
-/
theorem ContinuousLinearMap.curry_uncurryLeft
    (f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    f.uncurryLeft.curryLeft = f := by
  ext m x
  rw [ContinuousMultilinearMap.curryLeft_apply]; rw [ContinuousLinearMap.uncurryLeft_apply]; rw [tail_cons]; rw [cons_zero]

@[simp]
/--
theorem `ContinuousMultilinearMap.uncurry_curryLeft` / 定理 `ContinuousMultilinearMap.uncurry_curryLeft`

English:
theorem ContinuousMultilinearMap.uncurry_curryLeft
  given: (f : ContinuousMultilinearMap 𝕜 Ei G)
  proof: ContinuousMultilinearMap.toMultilinearMap_injective f.toMultilinearMap.uncurry_curryLeft

中文:
定理 连续多重线性映射.uncurry_curryLeft
  条件: (f : 连续多重线性映射 𝕜 Ei G)
  证明: ContinuousMultilinearMap.toMultilinearMap_injective f.toMultilinearMap.uncurry_curryLeft

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.toMultilinearMap_injective, f.toMultilinearMap.uncurry_curryLeft, toMultilinearMap, toMultilinearMap_injective, uncurry_curryLeft
-/
theorem ContinuousMultilinearMap.uncurry_curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    f.curryLeft.uncurryLeft = f :=
ContinuousMultilinearMap.toMultilinearMap_injective f.toMultilinearMap.uncurry_curryLeft

variable (𝕜 Ei G)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `continuousMultilinearCurryLeftEquiv` / `continuousMultilinearCurryLeftEquiv` 的定义

English:
definition continuousMultilinearCurryLeftEquiv
  signature: :
  body: LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryLeft
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousLinearMap.uncurryLeft
      left_inv := ContinuousMultilinearMap.uncurry_curryLeft
      right_inv := ContinuousLinearMap.curry_uncurryLeft }
    (fun f => by dsimp; exact MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

中文:
定义 continuousMultilinearCurryLeftEquiv
  签名: :
  定义体: LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryLeft
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousLinearMap.uncurryLeft
      left_inv := ContinuousMultilinearMap.uncurry_curryLeft
      right_inv := ContinuousLinearMap.curry_uncurryLeft }
    (fun f => by dsimp; exact MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.curry_uncurryLeft, ContinuousLinearMap.uncurryLeft, ContinuousMultilinearMap, ContinuousMultilinearMap.curryLeft, ContinuousMultilinearMap.uncurry_curryLeft, LinearEquiv, LinearEquiv.coe_symm_mk, LinearIsometryEquiv, LinearIsometryEquiv.ofBounds, MultilinearMap, MultilinearMap.mkContinuousLinear_norm_le, MultilinearMap.mkContinuous_norm_le, coe_symm_mk, curryLeft, curry_uncurryLeft, invFun, left_inv, map_add, map_smul
-/
def continuousMultilinearCurryLeftEquiv :
    ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[𝕜]
      Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryLeft
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousLinearMap.uncurryLeft
      left_inv := ContinuousMultilinearMap.uncurry_curryLeft
      right_inv := ContinuousLinearMap.curry_uncurryLeft }
    (fun f => by dsimp; exact MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

variable {𝕜 Ei G}

@[simp]
/--
theorem `continuousMultilinearCurryLeftEquiv_apply` / 定理 `continuousMultilinearCurryLeftEquiv_apply`

English:
theorem continuousMultilinearCurryLeftEquiv_apply
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearCurryLeftEquiv_apply
  证明: rfl

@[simp]
-/
theorem continuousMultilinearCurryLeftEquiv_apply
    (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0) (v : Π i : Fin n, Ei i.succ) :
    continuousMultilinearCurryLeftEquiv 𝕜 Ei G f x v = f (cons x v) :=
  rfl

@[simp]
/--
theorem `continuousMultilinearCurryLeftEquiv_symm_apply` / 定理 `continuousMultilinearCurryLeftEquiv_symm_apply`

English:
theorem continuousMultilinearCurryLeftEquiv_symm_apply
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearCurryLeftEquiv_symm_apply
  证明: rfl

@[simp]
-/
theorem continuousMultilinearCurryLeftEquiv_symm_apply
    (f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (v : Π i, Ei i) :
    (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm f v = f (v 0) (tail v) :=
  rfl

@[simp]
/--
theorem `ContinuousMultilinearMap.curryLeft_norm` / 定理 `ContinuousMultilinearMap.curryLeft_norm`

English:
theorem ContinuousMultilinearMap.curryLeft_norm
  given: (f : ContinuousMultilinearMap 𝕜 Ei G)
  proof: (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).norm_map f

@[simp]

中文:
定理 连续多重线性映射.curryLeft_norm
  条件: (f : 连续多重线性映射 𝕜 Ei G)
  证明: (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).norm_map f

@[simp]

Depends on / 依赖: continuousMultilinearCurryLeftEquiv, norm_map
-/
theorem ContinuousMultilinearMap.curryLeft_norm (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ‖f.curryLeft‖ = ‖f‖ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).norm_map f

@[simp]
/--
theorem `ContinuousLinearMap.uncurryLeft_norm` / 定理 `ContinuousLinearMap.uncurryLeft_norm`

English:
theorem ContinuousLinearMap.uncurryLeft_norm
  proof: (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm.norm_map f

中文:
定理 连续线性映射.uncurryLeft_norm
  证明: (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm.norm_map f

Depends on / 依赖: continuousMultilinearCurryLeftEquiv, norm_map, symm.norm_map
-/
theorem ContinuousLinearMap.uncurryLeft_norm
    (f : Ei 0 ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ‖f.uncurryLeft‖ = ‖f‖ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm.norm_map f

/-! #### Right currying -/


/--
Definition of `ContinuousMultilinearMap.uncurryRight` / `ContinuousMultilinearMap.uncurryRight` 的定义

English:
definition ContinuousMultilinearMap.uncurryRight
  body: let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->ₗ[𝕜] G) :=
    (ContinuousLinearMap.coeLM 𝕜).compMultilinearMap f.toMultilinearMap
  f'.uncurryRight.mkContinuous ‖f‖ fun m => f.norm_map_init_le m

@[simp]

中文:
定义 连续多重线性映射.uncurryRight
  定义体: let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->ₗ[𝕜] G) :=
    (ContinuousLinearMap.coeLM 𝕜).compMultilinearMap f.toMultilinearMap
  f'.uncurryRight.mkContinuous ‖f‖ fun m => f.norm_map_init_le m

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coeLM, MultilinearMap, castSucc, compMultilinearMap, f.norm_map_init_le, f.toMultilinearMap, mkContinuous, norm_map_init_le, toMultilinearMap, uncurryRight, uncurryRight.mkContinuous
-/
def ContinuousMultilinearMap.uncurryRight
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G)) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->ₗ[𝕜] G) :=
    (ContinuousLinearMap.coeLM 𝕜).compMultilinearMap f.toMultilinearMap
  f'.uncurryRight.mkContinuous ‖f‖ fun m => f.norm_map_init_le m

@[simp]
/--
theorem `ContinuousMultilinearMap.uncurryRight_apply` / 定理 `ContinuousMultilinearMap.uncurryRight_apply`

English:
theorem ContinuousMultilinearMap.uncurryRight_apply
  proof: rfl

中文:
定理 连续多重线性映射.uncurryRight_apply
  证明: rfl
-/
theorem ContinuousMultilinearMap.uncurryRight_apply
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G))
    (m : forall i, Ei i) : f.uncurryRight m = f (init m) (m (last n)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ContinuousMultilinearMap.curryRight` / `ContinuousMultilinearMap.curryRight` 的定义

English:
definition ContinuousMultilinearMap.curryRight
  signature: (f : ContinuousMultilinearMap 𝕜 Ei G)
  body: let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G) :=
    { toFun := fun m =>
        (f.toMultilinearMap.curryRight m).mkContinuous (‖f‖ * ∏ i, ‖m i‖) fun x =>
          f.norm_map_snoc_le m x
      map_update_add' := fun m i x y => by
        ext
        simp
      map_update_smul' := fun m i c x => by
        ext
        simp }
  f'.mkContinuous ‖f‖ fun m => by
    simp only [f', MultilinearMap.coe_mk]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _

@[simp]

中文:
定义 连续多重线性映射.curryRight
  签名: (f : 连续多重线性映射 𝕜 Ei G)
  定义体: let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G) :=
    { toFun := fun m =>
        (f.toMultilinearMap.curryRight m).mkContinuous (‖f‖ * ∏ i, ‖m i‖) fun x =>
          f.norm_map_snoc_le m x
      map_update_add' := fun m i x y => by
        ext
        simp
      map_update_smul' := fun m i c x => by
        ext
        simp }
  f'.mkContinuous ‖f‖ fun m => by
    simp only [f', MultilinearMap.coe_mk]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, MultilinearMap, MultilinearMap.coe_mk, castSucc, coe_mk, curryRight, f.norm_map_snoc_le, f.toMultilinearMap.curryRight, map_update_add, map_update_smul, mkContinuous, mkContinuous_norm_le, norm_map_snoc_le, toMultilinearMap
-/
def ContinuousMultilinearMap.curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G) :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G) :=
    { toFun := fun m =>
        (f.toMultilinearMap.curryRight m).mkContinuous (‖f‖ * ∏ i, ‖m i‖) fun x =>
          f.norm_map_snoc_le m x
      map_update_add' := fun m i x y => by
        ext
        simp
      map_update_smul' := fun m i c x => by
        ext
        simp }
  f'.mkContinuous ‖f‖ fun m => by
    simp only [f', MultilinearMap.coe_mk]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _

@[simp]
/--
theorem `ContinuousMultilinearMap.curryRight_apply` / 定理 `ContinuousMultilinearMap.curryRight_apply`

English:
theorem ContinuousMultilinearMap.curryRight_apply
  statement: (f : ContinuousMultilinearMap 𝕜 Ei G)
  proof: rfl

@[simp]

中文:
定理 连续多重线性映射.curryRight_apply
  结论: (f : 连续多重线性映射 𝕜 Ei G)
  证明: rfl

@[simp]
-/
theorem ContinuousMultilinearMap.curryRight_apply (f : ContinuousMultilinearMap 𝕜 Ei G)
    (m : forall i : Fin n, Ei <| castSucc i) (x : Ei (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl

@[simp]
/--
theorem `ContinuousMultilinearMap.curry_uncurryRight` / 定理 `ContinuousMultilinearMap.curry_uncurryRight`

English:
theorem ContinuousMultilinearMap.curry_uncurryRight
  proof: by
  ext m x
  rw [ContinuousMultilinearMap.curryRight_apply]; rw [ContinuousMultilinearMap.uncurryRight_apply]; rw [snoc_last]; rw [init_snoc]

@[simp]

中文:
定理 连续多重线性映射.curry_uncurryRight
  证明: by
  ext m x
  rw [ContinuousMultilinearMap.curryRight_apply]; rw [ContinuousMultilinearMap.uncurryRight_apply]; rw [snoc_last]; rw [init_snoc]

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curryRight_apply, ContinuousMultilinearMap.uncurryRight_apply, curryRight_apply, init_snoc, snoc_last, uncurryRight_apply
-/
theorem ContinuousMultilinearMap.curry_uncurryRight
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  rw [ContinuousMultilinearMap.curryRight_apply]; rw [ContinuousMultilinearMap.uncurryRight_apply]; rw [snoc_last]; rw [init_snoc]

@[simp]
/--
theorem `ContinuousMultilinearMap.uncurry_curryRight` / 定理 `ContinuousMultilinearMap.uncurry_curryRight`

English:
theorem ContinuousMultilinearMap.uncurry_curryRight
  given: (f : ContinuousMultilinearMap 𝕜 Ei G)
  proof: by
  ext m
  rw [uncurryRight_apply]; rw [curryRight_apply]; rw [snoc_init_self]

中文:
定理 连续多重线性映射.uncurry_curryRight
  条件: (f : 连续多重线性映射 𝕜 Ei G)
  证明: by
  ext m
  rw [uncurryRight_apply]; rw [curryRight_apply]; rw [snoc_init_self]

Depends on / 依赖: curryRight_apply, snoc_init_self, uncurryRight_apply
-/
theorem ContinuousMultilinearMap.uncurry_curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
    f.curryRight.uncurryRight = f := by
  ext m
  rw [uncurryRight_apply]; rw [curryRight_apply]; rw [snoc_init_self]

variable (𝕜 Ei G)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `continuousMultilinearCurryRightEquiv` / `continuousMultilinearCurryRightEquiv` 的定义

English:
definition continuousMultilinearCurryRightEquiv
  signature: :
  body: LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryRight
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousMultilinearMap.uncurryRight
      left_inv := ContinuousMultilinearMap.uncurry_curryRight
      right_inv := ContinuousMultilinearMap.curry_uncurryRight }
    (fun f => by
      simp only [curryRight, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [uncurryRight, LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

中文:
定义 continuousMultilinearCurryRightEquiv
  签名: :
  定义体: LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryRight
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousMultilinearMap.uncurryRight
      left_inv := ContinuousMultilinearMap.uncurry_curryRight
      right_inv := ContinuousMultilinearMap.curry_uncurryRight }
    (fun f => by
      simp only [curryRight, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [uncurryRight, LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

Depends on / 依赖: AddHom, AddHom.coe_mk, ContinuousMultilinearMap, ContinuousMultilinearMap.curryRight, ContinuousMultilinearMap.curry_uncurryRight, ContinuousMultilinearMap.uncurryRight, ContinuousMultilinearMap.uncurry_curryRight, LinearEquiv, LinearEquiv.coe_, LinearEquiv.coe_mk, LinearIsometryEquiv, LinearIsometryEquiv.ofBounds, LinearMap, LinearMap.coe_mk, MultilinearMap, MultilinearMap.mkContinuous_norm_le, coe_, coe_mk, curryRight, curry_uncurryRight
-/
def continuousMultilinearCurryRightEquiv :
    ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G) :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryRight
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousMultilinearMap.uncurryRight
      left_inv := ContinuousMultilinearMap.uncurry_curryRight
      right_inv := ContinuousMultilinearMap.curry_uncurryRight }
    (fun f => by
      simp only [curryRight, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [uncurryRight, LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

variable (n G')

/--
Definition of `continuousMultilinearCurryRightEquiv'` / `continuousMultilinearCurryRightEquiv'` 的定义

English:
definition continuousMultilinearCurryRightEquiv'
  signature: : (G [×n.succ]->L[𝕜] G') ≃ₗᵢ[𝕜] G [×n]->L[𝕜] G ->L[𝕜] G'
  body: continuousMultilinearCurryRightEquiv 𝕜 (fun _ => G) G'

中文:
定义 continuousMultilinearCurryRightEquiv'
  签名: : (G [×n.succ]->L[𝕜] G') ≃ₗᵢ[𝕜] G [×n]->L[𝕜] G ->L[𝕜] G'
  定义体: continuousMultilinearCurryRightEquiv 𝕜 (fun _ => G) G'

Depends on / 依赖: continuousMultilinearCurryRightEquiv
-/
def continuousMultilinearCurryRightEquiv' : (G [×n.succ]->L[𝕜] G') ≃ₗᵢ[𝕜] G [×n]->L[𝕜] G ->L[𝕜] G' :=
  continuousMultilinearCurryRightEquiv 𝕜 (fun _ => G) G'

variable {n 𝕜 G Ei G'}

@[simp]
/--
theorem `continuousMultilinearCurryRightEquiv_apply` / 定理 `continuousMultilinearCurryRightEquiv_apply`

English:
theorem continuousMultilinearCurryRightEquiv_apply
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearCurryRightEquiv_apply
  证明: rfl

@[simp]
-/
theorem continuousMultilinearCurryRightEquiv_apply
    (f : ContinuousMultilinearMap 𝕜 Ei G) (v : Π i : Fin n, Ei <| castSucc i) (x : Ei (last n)) :
    continuousMultilinearCurryRightEquiv 𝕜 Ei G f v x = f (snoc v x) :=
  rfl

@[simp]
/--
theorem `continuousMultilinearCurryRightEquiv_symm_apply` / 定理 `continuousMultilinearCurryRightEquiv_symm_apply`

English:
theorem continuousMultilinearCurryRightEquiv_symm_apply
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearCurryRightEquiv_symm_apply
  证明: rfl

@[simp]
-/
theorem continuousMultilinearCurryRightEquiv_symm_apply
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G))
    (v : Π i, Ei i) :
    (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm f v = f (init v) (v (last n)) :=
  rfl

@[simp]
/--
theorem `continuousMultilinearCurryRightEquiv_apply'` / 定理 `continuousMultilinearCurryRightEquiv_apply'`

English:
theorem continuousMultilinearCurryRightEquiv_apply'
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearCurryRightEquiv_apply'
  证明: rfl

@[simp]
-/
theorem continuousMultilinearCurryRightEquiv_apply'
    (f : G [×n.succ]->L[𝕜] G') (v : Fin n -> G) (x : G) :
    continuousMultilinearCurryRightEquiv' 𝕜 n G G' f v x = f (snoc v x) :=
  rfl

@[simp]
/--
theorem `continuousMultilinearCurryRightEquiv_symm_apply'` / 定理 `continuousMultilinearCurryRightEquiv_symm_apply'`

English:
theorem continuousMultilinearCurryRightEquiv_symm_apply'
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearCurryRightEquiv_symm_apply'
  证明: rfl

@[simp]
-/
theorem continuousMultilinearCurryRightEquiv_symm_apply'
    (f : G [×n]->L[𝕜] G ->L[𝕜] G') (v : Fin (n + 1) -> G) :
    (continuousMultilinearCurryRightEquiv' 𝕜 n G G').symm f v = f (init v) (v (last n)) :=
  rfl

@[simp]
/--
theorem `ContinuousMultilinearMap.curryRight_norm` / 定理 `ContinuousMultilinearMap.curryRight_norm`

English:
theorem ContinuousMultilinearMap.curryRight_norm
  given: (f : ContinuousMultilinearMap 𝕜 Ei G)
  proof: (continuousMultilinearCurryRightEquiv 𝕜 Ei G).norm_map f

@[simp]

中文:
定理 连续多重线性映射.curryRight_norm
  条件: (f : 连续多重线性映射 𝕜 Ei G)
  证明: (continuousMultilinearCurryRightEquiv 𝕜 Ei G).norm_map f

@[simp]

Depends on / 依赖: continuousMultilinearCurryRightEquiv, norm_map
-/
theorem ContinuousMultilinearMap.curryRight_norm (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ‖f.curryRight‖ = ‖f‖ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).norm_map f

@[simp]
/--
theorem `ContinuousMultilinearMap.uncurryRight_norm` / 定理 `ContinuousMultilinearMap.uncurryRight_norm`

English:
theorem ContinuousMultilinearMap.uncurryRight_norm
  proof: (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm.norm_map f

中文:
定理 连续多重线性映射.uncurryRight_norm
  证明: (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm.norm_map f

Depends on / 依赖: continuousMultilinearCurryRightEquiv, norm_map, symm.norm_map
-/
theorem ContinuousMultilinearMap.uncurryRight_norm
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) ->L[𝕜] G)) :
    ‖f.uncurryRight‖ = ‖f‖ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm.norm_map f

/-!
### Currying a variable in the middle
-/

/-- Given a continuous linear map from `M p` to the space of continuous multilinear maps
in `n` variables `M 0`, ..., `M n` with `M p` removed,
returns a continuous multilinear map in all `n + 1` variables. -/
@[simps! apply]
/--
Definition of `ContinuousLinearMap.uncurryMid` / `ContinuousLinearMap.uncurryMid` 的定义

English:
definition ContinuousLinearMap.uncurryMid
  signature: (p : Fin (n + 1))
  body: (ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ f.toLinearMap).uncurryMid p
.mkContinuous ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_removeNth_le f m

中文:
定义 连续线性映射.uncurryMid
  签名: (p : 有限集 (n + 1))
  定义体: (ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ f.toLinearMap).uncurryMid p
.mkContinuous ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_removeNth_le f m

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_map_removeNth_le, ContinuousMultilinearMap, ContinuousMultilinearMap.toMultilinearMapLinear, f.toLinearMap, mkContinuous, norm_map_removeNth_le, toLinearMap, toMultilinearMapLinear, uncurryMid
-/
def ContinuousLinearMap.uncurryMid (p : Fin (n + 1))
    (f : Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.succAbove i)) G) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  (ContinuousMultilinearMap.toMultilinearMapLinear ∘ₗ f.toLinearMap).uncurryMid p
.mkContinuous ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_removeNth_le f m

/--
Definition of `ContinuousMultilinearMap.curryMid` / `ContinuousMultilinearMap.curryMid` 的定义

English:
definition ContinuousMultilinearMap.curryMid
  signature: (p : Fin (n + 1)) (f : ContinuousMultilinearMap 𝕜 Ei G)
  body: MultilinearMap.mkContinuousLinear (f.toMultilinearMap.curryMid p) ‖f‖ f.norm_map_insertNth_le

@[simp]

中文:
定义 连续多重线性映射.curryMid
  签名: (p : 有限集 (n + 1)) (f : 连续多重线性映射 𝕜 Ei G)
  定义体: MultilinearMap.mkContinuousLinear (f.toMultilinearMap.curryMid p) ‖f‖ f.norm_map_insertNth_le

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.mkContinuousLinear, curryMid, f.norm_map_insertNth_le, f.toMultilinearMap.curryMid, mkContinuousLinear, norm_map_insertNth_le, toMultilinearMap
-/
def ContinuousMultilinearMap.curryMid (p : Fin (n + 1)) (f : ContinuousMultilinearMap 𝕜 Ei G) :
    Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.succAbove i)) G :=
  MultilinearMap.mkContinuousLinear (f.toMultilinearMap.curryMid p) ‖f‖ f.norm_map_insertNth_le

@[simp]
/--
theorem `ContinuousMultilinearMap.curryMid_apply` / 定理 `ContinuousMultilinearMap.curryMid_apply`

English:
theorem ContinuousMultilinearMap.curryMid_apply
  statement: (p : Fin (n + 1))
  proof: rfl

@[simp]

中文:
定理 连续多重线性映射.curryMid_apply
  结论: (p : 有限集 (n + 1))
  证明: rfl

@[simp]
-/
theorem ContinuousMultilinearMap.curryMid_apply (p : Fin (n + 1))
    (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei p) (m : forall i, Ei (p.succAbove i)) :
    f.curryMid p x m = f (p.insertNth x m) :=
  rfl

@[simp]
/--
theorem `ContinuousLinearMap.curryMid_uncurryMid` / 定理 `ContinuousLinearMap.curryMid_uncurryMid`

English:
theorem ContinuousLinearMap.curryMid_uncurryMid
  statement: (p : Fin (n + 1))
  proof: by ext; simp

@[simp]

中文:
定理 连续线性映射.curryMid_uncurryMid
  结论: (p : 有限集 (n + 1))
  证明: by ext; simp

@[simp]
-/
theorem ContinuousLinearMap.curryMid_uncurryMid (p : Fin (n + 1))
    (f : Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.succAbove i)) G) :
    (f.uncurryMid p).curryMid p = f := by ext; simp

@[simp]
/--
theorem `ContinuousMultilinearMap.uncurryMid_curryMid` / 定理 `ContinuousMultilinearMap.uncurryMid_curryMid`

English:
theorem ContinuousMultilinearMap.uncurryMid_curryMid
  statement: (p : Fin (n + 1))
  proof: ContinuousMultilinearMap.toMultilinearMap_injective f.toMultilinearMap.uncurryMid_curryMid p

中文:
定理 连续多重线性映射.uncurryMid_curryMid
  结论: (p : 有限集 (n + 1))
  证明: ContinuousMultilinearMap.toMultilinearMap_injective f.toMultilinearMap.uncurryMid_curryMid p

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.toMultilinearMap_injective, f.toMultilinearMap.uncurryMid_curryMid, toMultilinearMap, toMultilinearMap_injective, uncurryMid_curryMid
-/
theorem ContinuousMultilinearMap.uncurryMid_curryMid (p : Fin (n + 1))
    (f : ContinuousMultilinearMap 𝕜 Ei G) : (f.curryMid p).uncurryMid p = f :=
ContinuousMultilinearMap.toMultilinearMap_injective f.toMultilinearMap.uncurryMid_curryMid p

variable (𝕜 Ei G)

set_option backward.isDefEq.respectTransparency false in
/-- `ContinuousMultilinearMap.curryMid` as a linear isometry equivalence. -/
@[simps! apply symm_apply]
/--
Definition of `ContinuousMultilinearMap.curryMidEquiv` / `ContinuousMultilinearMap.curryMidEquiv` 的定义

English:
definition ContinuousMultilinearMap.curryMidEquiv
  signature: (p : Fin (n + 1))
  body: LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryMid p
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousLinearMap.uncurryMid p
      left_inv := ContinuousMultilinearMap.uncurryMid_curryMid p
      right_inv := ContinuousLinearMap.curryMid_uncurryMid p }
    (fun f => by dsimp; exact MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

中文:
定义 连续多重线性映射.curryMidEquiv
  签名: (p : 有限集 (n + 1))
  定义体: LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryMid p
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousLinearMap.uncurryMid p
      left_inv := ContinuousMultilinearMap.uncurryMid_curryMid p
      right_inv := ContinuousLinearMap.curryMid_uncurryMid p }
    (fun f => by dsimp; exact MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.curryMid_uncurryMid, ContinuousLinearMap.uncurryMid, ContinuousMultilinearMap, ContinuousMultilinearMap.curryMid, ContinuousMultilinearMap.uncurryMid_curryMid, LinearEquiv, LinearEquiv.coe_symm_mk, LinearIsometryEquiv, LinearIsometryEquiv.ofBounds, MultilinearMap, MultilinearMap.mkContinuousLinear_norm_le, MultilinearMap.mkContinuous_norm_le, coe_symm_mk, curryMid, curryMid_uncurryMid, invFun, left_inv, map_add, map_smul
-/
def ContinuousMultilinearMap.curryMidEquiv (p : Fin (n + 1)) :
    ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[𝕜]
      Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.succAbove i)) G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.curryMid p
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := ContinuousLinearMap.uncurryMid p
      left_inv := ContinuousMultilinearMap.uncurryMid_curryMid p
      right_inv := ContinuousLinearMap.curryMid_uncurryMid p }
    (fun f => by dsimp; exact MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)

variable {𝕜 Ei G}

@[simp]
/--
theorem `ContinuousMultilinearMap.norm_curryMid` / 定理 `ContinuousMultilinearMap.norm_curryMid`

English:
theorem ContinuousMultilinearMap.norm_curryMid
  statement: (p : Fin (n + 1))
  proof: (ContinuousMultilinearMap.curryMidEquiv 𝕜 Ei G p).norm_map f

@[simp]

中文:
定理 连续多重线性映射.norm_curryMid
  结论: (p : 有限集 (n + 1))
  证明: (ContinuousMultilinearMap.curryMidEquiv 𝕜 Ei G p).norm_map f

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curryMidEquiv, curryMidEquiv, norm_map
-/
theorem ContinuousMultilinearMap.norm_curryMid (p : Fin (n + 1))
    (f : ContinuousMultilinearMap 𝕜 Ei G) : ‖f.curryMid p‖ = ‖f‖ :=
  (ContinuousMultilinearMap.curryMidEquiv 𝕜 Ei G p).norm_map f

@[simp]
/--
theorem `ContinuousLinearMap.norm_uncurryMid` / 定理 `ContinuousLinearMap.norm_uncurryMid`

English:
theorem ContinuousLinearMap.norm_uncurryMid
  statement: (p : Fin (n + 1))
  proof: (ContinuousMultilinearMap.curryMidEquiv 𝕜 Ei G p).symm.norm_map f

中文:
定理 连续线性映射.norm_uncurryMid
  结论: (p : 有限集 (n + 1))
  证明: (ContinuousMultilinearMap.curryMidEquiv 𝕜 Ei G p).symm.norm_map f

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curryMidEquiv, curryMidEquiv, norm_map, symm.norm_map
-/
theorem ContinuousLinearMap.norm_uncurryMid (p : Fin (n + 1))
    (f : Ei p ->L[𝕜] ContinuousMultilinearMap 𝕜 (fun i => Ei (p.succAbove i)) G) :
    ‖f.uncurryMid p‖ = ‖f‖ :=
  (ContinuousMultilinearMap.curryMidEquiv 𝕜 Ei G p).symm.norm_map f

/-!
#### Currying with `0` variables

The space of multilinear maps with `0` variables is trivial: such a multilinear map is just an
arbitrary constant (note that multilinear maps in `0` variables need not map `0` to `0`!).
Therefore, the space of continuous multilinear maps on `(Fin 0) → G` with values in `E₂` is
isomorphic (and even isometric) to `E₂`. As this is the zeroth step in the construction of iterated
derivatives, we register this isomorphism. -/


section

/--
Definition of `ContinuousMultilinearMap.curry0` / `ContinuousMultilinearMap.curry0` 的定义

English:
definition ContinuousMultilinearMap.curry0
  signature: (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => G) G')
  body: f 0

中文:
定义 连续多重线性映射.curry0
  签名: (f : 连续多重线性映射 𝕜 (fun _ : 有限集 0 => G) G')
  定义体: f 0
-/
def ContinuousMultilinearMap.curry0 (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => G) G') :
    G' :=
  f 0

variable (𝕜 G) in
/--
Definition of `ContinuousMultilinearMap.uncurry0` / `ContinuousMultilinearMap.uncurry0` 的定义

English:
definition ContinuousMultilinearMap.uncurry0
  signature: (x : G')
  body: ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ x

中文:
定义 连续多重线性映射.uncurry0
  签名: (x : G')
  定义体: ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ x

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.constOfIsEmpty, constOfIsEmpty
-/
def ContinuousMultilinearMap.uncurry0 (x : G') : G [×0]->L[𝕜] G' :=
  ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ x

variable (𝕜) in
@[simp]
/--
theorem `ContinuousMultilinearMap.uncurry0_apply` / 定理 `ContinuousMultilinearMap.uncurry0_apply`

English:
theorem ContinuousMultilinearMap.uncurry0_apply
  given: (x : G') (m : Fin 0 -> G)
  proof: rfl

@[simp]

中文:
定理 连续多重线性映射.uncurry0_apply
  条件: (x : G') (m : 有限集 0 -> G)
  证明: rfl

@[simp]
-/
theorem ContinuousMultilinearMap.uncurry0_apply (x : G') (m : Fin 0 -> G) :
    ContinuousMultilinearMap.uncurry0 𝕜 G x m = x :=
  rfl

@[simp]
/--
theorem `ContinuousMultilinearMap.curry0_apply` / 定理 `ContinuousMultilinearMap.curry0_apply`

English:
theorem ContinuousMultilinearMap.curry0_apply
  given: (f : G [×0]->L[𝕜] G')
  statement: f.curry0 = f 0
  proof: rfl

@[simp]

中文:
定理 连续多重线性映射.curry0_apply
  条件: (f : G [×0]->L[𝕜] G')
  结论: f.curry0 = f 0
  证明: rfl

@[simp]
-/
theorem ContinuousMultilinearMap.curry0_apply (f : G [×0]->L[𝕜] G') : f.curry0 = f 0 :=
  rfl

@[simp]
/--
theorem `ContinuousMultilinearMap.apply_zero_uncurry0` / 定理 `ContinuousMultilinearMap.apply_zero_uncurry0`

English:
theorem ContinuousMultilinearMap.apply_zero_uncurry0
  given: (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G}
  proof: by
  ext m
  simp [Subsingleton.elim x m]

中文:
定理 连续多重线性映射.apply_zero_uncurry0
  条件: (f : G [×0]->L[𝕜] G') {x : 有限集 0 -> G}
  证明: by
  ext m
  simp [Subsingleton.elim x m]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem ContinuousMultilinearMap.apply_zero_uncurry0 (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G} :
    ContinuousMultilinearMap.uncurry0 𝕜 G (f x) = f := by
  ext m
  simp [Subsingleton.elim x m]

/--
theorem `ContinuousMultilinearMap.uncurry0_curry0` / 定理 `ContinuousMultilinearMap.uncurry0_curry0`

English:
theorem ContinuousMultilinearMap.uncurry0_curry0
  given: (f : G [×0]->L[𝕜] G')
  proof: by simp

中文:
定理 连续多重线性映射.uncurry0_curry0
  条件: (f : G [×0]->L[𝕜] G')
  证明: by simp
-/
theorem ContinuousMultilinearMap.uncurry0_curry0 (f : G [×0]->L[𝕜] G') :
    ContinuousMultilinearMap.uncurry0 𝕜 G f.curry0 = f := by simp

variable (𝕜 G) in
/--
theorem `ContinuousMultilinearMap.curry0_uncurry0` / 定理 `ContinuousMultilinearMap.curry0_uncurry0`

English:
theorem ContinuousMultilinearMap.curry0_uncurry0
  given: (x : G')
  proof: rfl

中文:
定理 连续多重线性映射.curry0_uncurry0
  条件: (x : G')
  证明: rfl
-/
theorem ContinuousMultilinearMap.curry0_uncurry0 (x : G') :
    (ContinuousMultilinearMap.uncurry0 𝕜 G x).curry0 = x :=
  rfl

variable (𝕜 G) in
@[simp]
/--
theorem `ContinuousMultilinearMap.uncurry0_norm` / 定理 `ContinuousMultilinearMap.uncurry0_norm`

English:
theorem ContinuousMultilinearMap.uncurry0_norm
  given: (x : G')
  proof: norm_constOfIsEmpty _ _ _

@[simp]

中文:
定理 连续多重线性映射.uncurry0_norm
  条件: (x : G')
  证明: norm_constOfIsEmpty _ _ _

@[simp]

Depends on / 依赖: norm_constOfIsEmpty
-/
theorem ContinuousMultilinearMap.uncurry0_norm (x : G') :
    ‖ContinuousMultilinearMap.uncurry0 𝕜 G x‖ = ‖x‖ :=
  norm_constOfIsEmpty _ _ _

@[simp]
/--
theorem `ContinuousMultilinearMap.fin0_apply_norm` / 定理 `ContinuousMultilinearMap.fin0_apply_norm`

English:
theorem ContinuousMultilinearMap.fin0_apply_norm
  given: (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G}
  proof: by
  obtain rfl : x = 0 := Subsingleton.elim _ _
  refine le_antisymm (by simpa using f.le_opNorm 0) ?_
  have : ‖ContinuousMultilinearMap.uncurry0 𝕜 G f.curry0‖ <= ‖f.curry0‖ :=
    ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => by
      simp [-ContinuousMultilinearMap.apply_zero_uncurry0]
  simpa [-Matrix.zero_empty] using this

@[simp]

中文:
定理 连续多重线性映射.fin0_apply_norm
  条件: (f : G [×0]->L[𝕜] G') {x : 有限集 0 -> G}
  证明: by
  obtain rfl : x = 0 := Subsingleton.elim _ _
  refine le_antisymm (by simpa using f.le_opNorm 0) ?_
  have : ‖ContinuousMultilinearMap.uncurry0 𝕜 G f.curry0‖ <= ‖f.curry0‖ :=
    ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => by
      simp [-ContinuousMultilinearMap.apply_zero_uncurry0]
  simpa [-Matrix.zero_empty] using this

@[simp]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.apply_zero_uncurry0, ContinuousMultilinearMap.opNorm_le_bound, ContinuousMultilinearMap.uncurry0, Matrix, Matrix.zero_empty, Subsingleton, Subsingleton.elim, apply_zero_uncurry0, curry0, f.curry0, f.le_opNorm, le_antisymm, le_opNorm, norm_nonneg, opNorm_le_bound, uncurry0, zero_empty
-/
theorem ContinuousMultilinearMap.fin0_apply_norm (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G} :
    ‖f x‖ = ‖f‖ := by
  obtain rfl : x = 0 := Subsingleton.elim _ _
  refine le_antisymm (by simpa using f.le_opNorm 0) ?_
  have : ‖ContinuousMultilinearMap.uncurry0 𝕜 G f.curry0‖ <= ‖f.curry0‖ :=
    ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m => by
      simp [-ContinuousMultilinearMap.apply_zero_uncurry0]
  simpa [-Matrix.zero_empty] using this

@[simp]
/--
theorem `ContinuousMultilinearMap.fin0_apply_enorm` / 定理 `ContinuousMultilinearMap.fin0_apply_enorm`

English:
theorem ContinuousMultilinearMap.fin0_apply_enorm
  given: (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G}
  proof: by
  simp_rw [← ofReal_norm, fin0_apply_norm]

中文:
定理 连续多重线性映射.fin0_apply_enorm
  条件: (f : G [×0]->L[𝕜] G') {x : 有限集 0 -> G}
  证明: by
  simp_rw [← ofReal_norm, fin0_apply_norm]

Depends on / 依赖: fin0_apply_norm, ofReal_norm, simp_rw
-/
theorem ContinuousMultilinearMap.fin0_apply_enorm (f : G [×0]->L[𝕜] G') {x : Fin 0 -> G} :
    ‖f x‖ₑ = ‖f‖ₑ := by
  simp_rw [← ofReal_norm, fin0_apply_norm]

/--
theorem `ContinuousMultilinearMap.curry0_norm` / 定理 `ContinuousMultilinearMap.curry0_norm`

English:
theorem ContinuousMultilinearMap.curry0_norm
  given: (f : G [×0]->L[𝕜] G')
  statement: ‖f.curry0‖ = ‖f‖
  proof: by simp

中文:
定理 连续多重线性映射.curry0_norm
  条件: (f : G [×0]->L[𝕜] G')
  结论: ‖f.curry0‖ = ‖f‖
  证明: by simp
-/
theorem ContinuousMultilinearMap.curry0_norm (f : G [×0]->L[𝕜] G') : ‖f.curry0‖ = ‖f‖ := by simp

variable (𝕜 G G')

/--
Definition of `continuousMultilinearCurryFin0` / `continuousMultilinearCurryFin0` 的定义

English:
definition continuousMultilinearCurryFin0
  signature: : (G [×0]->L[𝕜] G') ≃ₗᵢ[𝕜] G' where
  body: ContinuousMultilinearMap.curry0 f
  invFun f := ContinuousMultilinearMap.uncurry0 𝕜 G f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := ContinuousMultilinearMap.uncurry0_curry0
  right_inv := ContinuousMultilinearMap.curry0_uncurry0 𝕜 G
  norm_map' := ContinuousMultilinearMap.curry0_norm

中文:
定义 continuousMultilinearCurryFin0
  签名: : (G [×0]->L[𝕜] G') ≃ₗᵢ[𝕜] G' where
  定义体: ContinuousMultilinearMap.curry0 f
  invFun f := ContinuousMultilinearMap.uncurry0 𝕜 G f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := ContinuousMultilinearMap.uncurry0_curry0
  right_inv := ContinuousMultilinearMap.curry0_uncurry0 𝕜 G
  norm_map' := ContinuousMultilinearMap.curry0_norm

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curry0, curry0
-/
def continuousMultilinearCurryFin0 : (G [×0]->L[𝕜] G') ≃ₗᵢ[𝕜] G' where
  toFun f := ContinuousMultilinearMap.curry0 f
  invFun f := ContinuousMultilinearMap.uncurry0 𝕜 G f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := ContinuousMultilinearMap.uncurry0_curry0
  right_inv := ContinuousMultilinearMap.curry0_uncurry0 𝕜 G
  norm_map' := ContinuousMultilinearMap.curry0_norm

variable {𝕜 G G'}

@[simp]
/--
theorem `continuousMultilinearCurryFin0_apply` / 定理 `continuousMultilinearCurryFin0_apply`

English:
theorem continuousMultilinearCurryFin0_apply
  given: (f : G [×0]->L[𝕜] G')
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearCurryFin0_apply
  条件: (f : G [×0]->L[𝕜] G')
  证明: rfl

@[simp]
-/
theorem continuousMultilinearCurryFin0_apply (f : G [×0]->L[𝕜] G') :
    continuousMultilinearCurryFin0 𝕜 G G' f = f 0 :=
  rfl

@[simp]
/--
theorem `continuousMultilinearCurryFin0_symm_apply` / 定理 `continuousMultilinearCurryFin0_symm_apply`

English:
theorem continuousMultilinearCurryFin0_symm_apply
  given: (x : G')
  proof: rfl

中文:
定理 continuousMultilinearCurryFin0_symm_apply
  条件: (x : G')
  证明: rfl
-/
theorem continuousMultilinearCurryFin0_symm_apply (x : G') :
    (continuousMultilinearCurryFin0 𝕜 G G').symm x = ContinuousMultilinearMap.uncurry0 𝕜 G x :=
  rfl

/--
theorem `continuousMultilinearCurryFin0_symm_apply_apply` / 定理 `continuousMultilinearCurryFin0_symm_apply_apply`

English:
theorem continuousMultilinearCurryFin0_symm_apply_apply
  given: (x : G') (v : Fin 0 -> G)
  proof: rfl

中文:
定理 continuousMultilinearCurryFin0_symm_apply_apply
  条件: (x : G') (v : 有限集 0 -> G)
  证明: rfl
-/
theorem continuousMultilinearCurryFin0_symm_apply_apply (x : G') (v : Fin 0 -> G) :
    (continuousMultilinearCurryFin0 𝕜 G G').symm x v = x :=
  rfl

end

/-! #### With 1 variable -/


variable (𝕜 G G')

/--
Definition of `continuousMultilinearCurryFin1` / `continuousMultilinearCurryFin1` 的定义

English:
definition continuousMultilinearCurryFin1
  signature: : (G [×1]->L[𝕜] G') ≃ₗᵢ[𝕜] G ->L[𝕜] G'
  body: (continuousMultilinearCurryRightEquiv 𝕜 (fun _ : Fin 1 => G) G').trans
    (continuousMultilinearCurryFin0 𝕜 G (G ->L[𝕜] G'))

中文:
定义 continuousMultilinearCurryFin1
  签名: : (G [×1]->L[𝕜] G') ≃ₗᵢ[𝕜] G ->L[𝕜] G'
  定义体: (continuousMultilinearCurryRightEquiv 𝕜 (fun _ : Fin 1 => G) G').trans
    (continuousMultilinearCurryFin0 𝕜 G (G ->L[𝕜] G'))

Depends on / 依赖: continuousMultilinearCurryFin0, continuousMultilinearCurryRightEquiv
-/
def continuousMultilinearCurryFin1 : (G [×1]->L[𝕜] G') ≃ₗᵢ[𝕜] G ->L[𝕜] G' :=
  (continuousMultilinearCurryRightEquiv 𝕜 (fun _ : Fin 1 => G) G').trans
    (continuousMultilinearCurryFin0 𝕜 G (G ->L[𝕜] G'))

variable {𝕜 G G'}

@[simp]
/--
theorem `continuousMultilinearCurryFin1_apply` / 定理 `continuousMultilinearCurryFin1_apply`

English:
theorem continuousMultilinearCurryFin1_apply
  given: (f : G [×1]->L[𝕜] G') (x : G)
  proof: rfl

@[simp]

中文:
定理 continuousMultilinearCurryFin1_apply
  条件: (f : G [×1]->L[𝕜] G') (x : G)
  证明: rfl

@[simp]
-/
theorem continuousMultilinearCurryFin1_apply (f : G [×1]->L[𝕜] G') (x : G) :
    continuousMultilinearCurryFin1 𝕜 G G' f x = f (Fin.snoc 0 x) :=
  rfl

@[simp]
/--
theorem `continuousMultilinearCurryFin1_symm_apply` / 定理 `continuousMultilinearCurryFin1_symm_apply`

English:
theorem continuousMultilinearCurryFin1_symm_apply
  given: (f : G ->L[𝕜] G') (v : Fin 1 -> G)
  proof: rfl

中文:
定理 continuousMultilinearCurryFin1_symm_apply
  条件: (f : G ->L[𝕜] G') (v : 有限集 1 -> G)
  证明: rfl
-/
theorem continuousMultilinearCurryFin1_symm_apply (f : G ->L[𝕜] G') (v : Fin 1 -> G) :
    (continuousMultilinearCurryFin1 𝕜 G G').symm f v = f (v 0) :=
  rfl

namespace ContinuousMultilinearMap

variable (𝕜 G G')

@[simp]
/--
theorem `norm_domDomCongr` / 定理 `norm_domDomCongr`

English:
theorem norm_domDomCongr
  given: (σ : ι ≃ ι') (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G')
  proof: by
  simp only [norm_def, ← σ.prod_comp,
    (σ.arrowCongr (Equiv.refl G)).surjective.forall, domDomCongr_apply, Equiv.arrowCongr_apply,
    Equiv.coe_refl, comp_apply, Equiv.symm_apply_apply, id]

中文:
定理 norm_domDomCongr
  条件: (σ : ι ≃ ι') (f : 连续多重线性映射 𝕜 (fun _ : ι => G) G')
  证明: by
  simp only [norm_def, ← σ.prod_comp,
    (σ.arrowCongr (Equiv.refl G)).surjective.forall, domDomCongr_apply, Equiv.arrowCongr_apply,
    Equiv.coe_refl, comp_apply, Equiv.symm_apply_apply, id]

Depends on / 依赖: Equiv.arrowCongr_apply, Equiv.coe_refl, Equiv.refl, Equiv.symm_apply_apply, arrowCongr, arrowCongr_apply, coe_refl, comp_apply, domDomCongr_apply, norm_def, prod_comp, surjective, surjective.forall, symm_apply_apply
-/
theorem norm_domDomCongr (σ : ι ≃ ι') (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :
    ‖domDomCongr σ f‖ = ‖f‖ := by
  simp only [norm_def, ← σ.prod_comp,
    (σ.arrowCongr (Equiv.refl G)).surjective.forall, domDomCongr_apply, Equiv.arrowCongr_apply,
    Equiv.coe_refl, comp_apply, Equiv.symm_apply_apply, id]

/--
Definition of `domDomCongrₗᵢ` / `domDomCongrₗᵢ` 的定义

English:
definition domDomCongrₗᵢ
  signature: (σ : ι ≃ ι')
  body: { domDomCongrEquiv σ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_domDomCongr 𝕜 G G' σ }

中文:
定义 domDomCongrₗᵢ
  签名: (σ : ι ≃ ι')
  定义体: { domDomCongrEquiv σ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_domDomCongr 𝕜 G G' σ }

Depends on / 依赖: domDomCongrEquiv, map_add, map_smul, norm_domDomCongr, norm_map
-/
def domDomCongrₗᵢ (σ : ι ≃ ι') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G' ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G' :=
  { domDomCongrEquiv σ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_domDomCongr 𝕜 G G' σ }

variable {𝕜 G G'}

section

/--
Definition of `currySum` / `currySum` 的定义

English:
definition currySum
  signature: (f : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G')
  body: MultilinearMap.mkContinuousMultilinear (MultilinearMap.currySum f.toMultilinearMap) ‖f‖
    fun m m' => by simpa [Fintype.prod_sum_type, mul_assoc] using f.le_opNorm (Sum.elim m m')

@[simp]

中文:
定义 currySum
  签名: (f : 连续多重线性映射 𝕜 (fun _ : ι oplus ι' => G) G')
  定义体: MultilinearMap.mkContinuousMultilinear (MultilinearMap.currySum f.toMultilinearMap) ‖f‖
    fun m m' => by simpa [Fintype.prod_sum_type, mul_assoc] using f.le_opNorm (Sum.elim m m')

@[simp]

Depends on / 依赖: Fintype, Fintype.prod_sum_type, MultilinearMap, MultilinearMap.currySum, MultilinearMap.mkContinuousMultilinear, Sum.elim, currySum, f.le_opNorm, f.toMultilinearMap, le_opNorm, mkContinuousMultilinear, mul_assoc, prod_sum_type, toMultilinearMap
-/
def currySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  MultilinearMap.mkContinuousMultilinear (MultilinearMap.currySum f.toMultilinearMap) ‖f‖
    fun m m' => by simpa [Fintype.prod_sum_type, mul_assoc] using f.le_opNorm (Sum.elim m m')

@[simp]
/--
theorem `currySum_apply` / 定理 `currySum_apply`

English:
theorem currySum_apply
  statement: (f : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G') (m : ι -> G)
  proof: rfl

中文:
定理 currySum_apply
  结论: (f : 连续多重线性映射 𝕜 (fun _ : ι oplus ι' => G) G') (m : ι -> G)
  证明: rfl
-/
theorem currySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G') (m : ι -> G)
    (m' : ι' -> G) : f.currySum m m' = f (Sum.elim m m') :=
  rfl

/--
Definition of `uncurrySum` / `uncurrySum` 的定义

English:
definition uncurrySum
  signature: (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
  body: MultilinearMap.mkContinuous
    (toMultilinearMapLinear.compMultilinearMap f.toMultilinearMap).uncurrySum ‖f‖ fun m => by
    simpa [Fintype.prod_sum_type, mul_assoc] using!
      (f (m ∘ Sum.inl)).le_of_opNorm_le (f.le_opNorm _) (m ∘ Sum.inr)

@[simp]

中文:
定义 uncurrySum
  签名: (f : 连续多重线性映射 𝕜 (fun _ : ι => G)
  定义体: MultilinearMap.mkContinuous
    (toMultilinearMapLinear.compMultilinearMap f.toMultilinearMap).uncurrySum ‖f‖ fun m => by
    simpa [Fintype.prod_sum_type, mul_assoc] using!
      (f (m ∘ Sum.inl)).le_of_opNorm_le (f.le_opNorm _) (m ∘ Sum.inr)

@[simp]

Depends on / 依赖: Fintype, Fintype.prod_sum_type, MultilinearMap, MultilinearMap.mkContinuous, Sum.inl, Sum.inr, compMultilinearMap, f.le_opNorm, f.toMultilinearMap, le_of_opNorm_le, le_opNorm, mkContinuous, mul_assoc, prod_sum_type, toMultilinearMap, toMultilinearMapLinear, toMultilinearMapLinear.compMultilinearMap, uncurrySum
-/
def uncurrySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G')) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G' :=
  MultilinearMap.mkContinuous
    (toMultilinearMapLinear.compMultilinearMap f.toMultilinearMap).uncurrySum ‖f‖ fun m => by
    simpa [Fintype.prod_sum_type, mul_assoc] using!
      (f (m ∘ Sum.inl)).le_of_opNorm_le (f.le_opNorm _) (m ∘ Sum.inr)

@[simp]
/--
theorem `uncurrySum_apply` / 定理 `uncurrySum_apply`

English:
theorem uncurrySum_apply
  statement: (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
  proof: rfl

中文:
定理 uncurrySum_apply
  结论: (f : 连续多重线性映射 𝕜 (fun _ : ι => G)
  证明: rfl
-/
theorem uncurrySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G'))
    (m : ι oplus ι' -> G) : f.uncurrySum m = f (m ∘ Sum.inl) (m ∘ Sum.inr) :=
  rfl

variable (𝕜 ι ι' G G')

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `currySumEquiv` / `currySumEquiv` 的定义

English:
definition currySumEquiv
  signature: : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G' ≃ₗᵢ[𝕜]
  body: LinearIsometryEquiv.ofBounds
    { toFun := currySum
      invFun := uncurrySum
      map_add' := fun f g => by
        ext
        rfl
      map_smul' := fun c f => by
        ext
        rfl
      left_inv := fun f => by
        ext m
        exact congr_arg f (Sum.elim_comp_inl_inr m) }
    (fun f => MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg f) _) fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

中文:
定义 currySumEquiv
  签名: : 连续多重线性映射 𝕜 (fun _ : ι oplus ι' => G) G' ≃ₗᵢ[𝕜]
  定义体: LinearIsometryEquiv.ofBounds
    { toFun := currySum
      invFun := uncurrySum
      map_add' := fun f g => by
        ext
        rfl
      map_smul' := fun c f => by
        ext
        rfl
      left_inv := fun f => by
        ext m
        exact congr_arg f (Sum.elim_comp_inl_inr m) }
    (fun f => MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg f) _) fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_symm_mk, LinearIsometryEquiv, LinearIsometryEquiv.ofBounds, MultilinearMap, MultilinearMap.mkContinuousMultilinear_norm_le, MultilinearMap.mkContinuous_norm_le, Sum.elim_comp_inl_inr, coe_symm_mk, congr_arg, currySum, elim_comp_inl_inr, invFun, left_inv, map_add, map_smul, mkContinuousMultilinear_norm_le, mkContinuous_norm_le, norm_nonneg, ofBounds
-/
def currySumEquiv : ContinuousMultilinearMap 𝕜 (fun _ : ι oplus ι' => G) G' ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  LinearIsometryEquiv.ofBounds
    { toFun := currySum
      invFun := uncurrySum
      map_add' := fun f g => by
        ext
        rfl
      map_smul' := fun c f => by
        ext
        rfl
      left_inv := fun f => by
        ext m
        exact congr_arg f (Sum.elim_comp_inl_inr m) }
    (fun f => MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg f) _) fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

end

section

variable (𝕜 G G') {k l : Nat} {s : Finset (Fin n)}

/--
Definition of `curryFinFinset` / `curryFinFinset` 的定义

English:
definition curryFinFinset
  signature: {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
  body: (domDomCongrₗᵢ 𝕜 G G' (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv 𝕜 (Fin k) (Fin l) G G')

中文:
定义 curryFinFinset
  签名: {k l n : 自然数} {s : 有限集 (有限集 n)} (hk : #s = k) (hl : #sᶜ = l)
  定义体: (domDomCongrₗᵢ 𝕜 G G' (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv 𝕜 (Fin k) (Fin l) G G')

Depends on / 依赖: currySumEquiv, finSumEquivOfFinset
-/
def curryFinFinset {k l n : Nat} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l) :
    (G [×n]->L[𝕜] G') ≃ₗᵢ[𝕜] G [×k]->L[𝕜] G [×l]->L[𝕜] G' :=
  (domDomCongrₗᵢ 𝕜 G G' (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv 𝕜 (Fin k) (Fin l) G G')

variable {𝕜 G G'}

@[simp]
/--
theorem `curryFinFinset_apply` / 定理 `curryFinFinset_apply`

English:
theorem curryFinFinset_apply
  statement: (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]->L[𝕜] G')
  proof: rfl

@[simp]

中文:
定理 curryFinFinset_apply
  结论: (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]->L[𝕜] G')
  证明: rfl

@[simp]
-/
theorem curryFinFinset_apply (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]->L[𝕜] G')
    (mk : Fin k -> G) (ml : Fin l -> G) : curryFinFinset 𝕜 G G' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl

@[simp]
/--
theorem `curryFinFinset_symm_apply` / 定理 `curryFinFinset_symm_apply`

English:
theorem curryFinFinset_symm_apply
  statement: (hk : #s = k) (hl : #sᶜ = l)
  proof: rfl

中文:
定理 curryFinFinset_symm_apply
  结论: (hk : #s = k) (hl : #sᶜ = l)
  证明: rfl
-/
theorem curryFinFinset_symm_apply (hk : #s = k) (hl : #sᶜ = l)
    (f : G [×k]->L[𝕜] G [×l]->L[𝕜] G') (m : Fin n -> G) : (curryFinFinset 𝕜 G G' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
m finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl

/--
theorem `curryFinFinset_symm_apply_piecewise_const` / 定理 `curryFinFinset_symm_apply_piecewise_const`

English:
theorem curryFinFinset_symm_apply_piecewise_const
  statement: (hk : #s = k) (hl : #sᶜ = l)
  proof: MultilinearMap.curryFinFinset_symm_apply_piecewise_const hk hl _ x y

@[simp]

中文:
定理 curryFinFinset_symm_apply_piecewise_const
  结论: (hk : #s = k) (hl : #sᶜ = l)
  证明: MultilinearMap.curryFinFinset_symm_apply_piecewise_const hk hl _ x y

@[simp]

Depends on / 依赖: MultilinearMap, MultilinearMap.curryFinFinset_symm_apply_piecewise_const, curryFinFinset_symm_apply_piecewise_const
-/
theorem curryFinFinset_symm_apply_piecewise_const (hk : #s = k) (hl : #sᶜ = l)
    (f : G [×k]->L[𝕜] G [×l]->L[𝕜] G') (x y : G) :
    (curryFinFinset 𝕜 G G' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y :=
  MultilinearMap.curryFinFinset_symm_apply_piecewise_const hk hl _ x y

@[simp]
/--
theorem `curryFinFinset_symm_apply_const` / 定理 `curryFinFinset_symm_apply_const`

English:
theorem curryFinFinset_symm_apply_const
  statement: (hk : #s = k) (hl : #sᶜ = l)
  proof: rfl

中文:
定理 curryFinFinset_symm_apply_const
  结论: (hk : #s = k) (hl : #sᶜ = l)
  证明: rfl
-/
theorem curryFinFinset_symm_apply_const (hk : #s = k) (hl : #sᶜ = l)
    (f : G [×k]->L[𝕜] G [×l]->L[𝕜] G') (x : G) :
    ((curryFinFinset 𝕜 G G' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl

/--
theorem `curryFinFinset_apply_const` / 定理 `curryFinFinset_apply_const`

English:
theorem curryFinFinset_apply_const
  statement: (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]->L[𝕜] G')
  proof: by
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  rw [LinearIsometryEquiv.symm_apply_apply]

中文:
定理 curryFinFinset_apply_const
  结论: (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]->L[𝕜] G')
  证明: by
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  rw [LinearIsometryEquiv.symm_apply_apply]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.symm_apply_apply, curryFinFinset_symm_apply_piecewise_const, symm.trans, symm_apply_apply
-/
theorem curryFinFinset_apply_const (hk : #s = k) (hl : #sᶜ = l) (f : G [×n]->L[𝕜] G')
    (x y : G) : (curryFinFinset 𝕜 G G' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  rw [LinearIsometryEquiv.symm_apply_apply]

end

end ContinuousMultilinearMap

namespace ContinuousLinearMap

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/--
Definition of `continuousMultilinearMapOption` / `continuousMultilinearMapOption` 的定义

English:
definition continuousMultilinearMapOption
  signature: (B : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F)
  body: MultilinearMap.mkContinuous
  { toFun := fun p => B (p none).1 (fun i => (p i).2 i)
    map_update_add' := by
      intro inst v j x y
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i => (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) => (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B]
    map_update_smul' := by
      intro inst v j c x
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i => (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) => (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B] } (‖B‖) <| by
  intro b
  simp only [MultilinearMap.coe_mk, Fintype.prod_option]
  apply (ContinuousMultilinearMap.le_opNorm _ _).trans
  rw [← mul_assoc]
  gcongr with i _
  · apply (B.le_opNorm _).trans
    gcongr
    exact norm_fst_le _
  · exact (norm_le_pi_norm _ _).trans (norm_snd_le _)

中文:
定义 continuousMultilinearMapOption
  签名: (B : G ->L[𝕜] 连续多重线性映射 𝕜 E F)
  定义体: MultilinearMap.mkContinuous
  { toFun := fun p => B (p none).1 (fun i => (p i).2 i)
    map_update_add' := by
      intro inst v j x y
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i => (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) => (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B]
    map_update_smul' := by
      intro inst v j c x
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i => (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) => (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B] } (‖B‖) <| by
  intro b
  simp only [MultilinearMap.coe_mk, Fintype.prod_option]
  apply (ContinuousMultilinearMap.le_opNorm _ _).trans
  rw [← mul_assoc]
  gcongr with i _
  · apply (B.le_opNorm _).trans
    gcongr
    exact norm_fst_le _
  · exact (norm_le_pi_norm _ _).trans (norm_snd_le _)

Depends on / 依赖: Function, Function.update, MultilinearMap, MultilinearMap.mkContinuous, classical, eq_or_ne, map_update_add, map_update_smul, mkContinuous, update
-/
noncomputable def continuousMultilinearMapOption (B : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F) :
    ContinuousMultilinearMap 𝕜 (fun (_ : Option ι) => (G × (Π i, E i))) F :=
  MultilinearMap.mkContinuous
  { toFun := fun p => B (p none).1 (fun i => (p i).2 i)
    map_update_add' := by
      intro inst v j x y
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i => (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) => (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B]
    map_update_smul' := by
      intro inst v j c x
      match j with
      | none => simp
      | some j =>
        classical
        have B z : (fun i => (Function.update v (some j) z (some i)).2 i) =
            Function.update (fun (i : ι) => (v i).2 i) j (z.2 j) := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp
          · simp [hij]
        simp [B] } (‖B‖) <| by
  intro b
  simp only [MultilinearMap.coe_mk, Fintype.prod_option]
  apply (ContinuousMultilinearMap.le_opNorm _ _).trans
  rw [← mul_assoc]
  gcongr with i _
  · apply (B.le_opNorm _).trans
    gcongr
    exact norm_fst_le _
  · exact (norm_le_pi_norm _ _).trans (norm_snd_le _)

/--
lemma `continuousMultilinearMapOption_apply_eq_self` / 引理 `continuousMultilinearMapOption_apply_eq_self`

English:
lemma continuousMultilinearMapOption_apply_eq_self
  statement: (B : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F)
  proof: rfl

中文:
引理 continuousMultilinearMapOption_apply_eq_self
  结论: (B : G ->L[𝕜] 连续多重线性映射 𝕜 E F)
  证明: rfl
-/
lemma continuousMultilinearMapOption_apply_eq_self (B : G ->L[𝕜] ContinuousMultilinearMap 𝕜 E F)
    (a : G) (v : Π i, E i) : B.continuousMultilinearMapOption (fun _ => (a, v)) = B a v := rfl

end ContinuousLinearMap
