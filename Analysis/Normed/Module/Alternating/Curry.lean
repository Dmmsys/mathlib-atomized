/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Currying continuous alternating forms

In this file we define `ContinuousAlternatingMap.curryLeft`
which interprets a continuous alternating map in `n + 1` variables
as a continuous linear map in the 0th variable
taking values in the continuous alternating maps in `n` variables.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : Nat}

namespace ContinuousAlternatingMap

/--
Definition of `curryLeft` / `curryLeft` 的定义

English:
definition curryLeft
  signature: (f : E [⋀^Fin (n + 1)]->L[𝕜] F)
  body: AlternatingMap.mkContinuousLinear f.toAlternatingMap.curryLeft ‖f‖
    f.toContinuousMultilinearMap.norm_map_cons_le

@[simp]

中文:
定义 curryLeft
  签名: (f : E [⋀^有限集 (n + 1)]->L[𝕜] F)
  定义体: AlternatingMap.mkContinuousLinear f.toAlternatingMap.curryLeft ‖f‖
    f.toContinuousMultilinearMap.norm_map_cons_le

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.mkContinuousLinear, curryLeft, f.toAlternatingMap.curryLeft, f.toContinuousMultilinearMap.norm_map_cons_le, mkContinuousLinear, norm_map_cons_le, toAlternatingMap, toContinuousMultilinearMap
-/
noncomputable def curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) : E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F :=
  AlternatingMap.mkContinuousLinear f.toAlternatingMap.curryLeft ‖f‖
    f.toContinuousMultilinearMap.norm_map_cons_le

@[simp]
/--
lemma `toContinuousMultilinearMap_curryLeft` / 引理 `toContinuousMultilinearMap_curryLeft`

English:
lemma toContinuousMultilinearMap_curryLeft
  given: (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (x : E)
  proof: rfl

@[simp]

中文:
引理 toContinuousMultilinearMap_curryLeft
  条件: (f : E [⋀^有限集 (n + 1)]->L[𝕜] F) (x : E)
  证明: rfl

@[simp]
-/
lemma toContinuousMultilinearMap_curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (x : E) :
    (f.curryLeft x).toContinuousMultilinearMap = f.toContinuousMultilinearMap.curryLeft x :=
  rfl

@[simp]
/--
lemma `toAlternatingMap_curryLeft` / 引理 `toAlternatingMap_curryLeft`

English:
lemma toAlternatingMap_curryLeft
  given: (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (x : E)
  proof: rfl

@[simp]

中文:
引理 toAlternatingMap_curryLeft
  条件: (f : E [⋀^有限集 (n + 1)]->L[𝕜] F) (x : E)
  证明: rfl

@[simp]
-/
lemma toAlternatingMap_curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (x : E) :
    (f.curryLeft x).toAlternatingMap = f.toAlternatingMap.curryLeft x :=
  rfl

@[simp]
/--
lemma `norm_curryLeft` / 引理 `norm_curryLeft`

English:
lemma norm_curryLeft
  given: (f : E [⋀^Fin (n + 1)]->L[𝕜] F)
  statement: ‖f.curryLeft‖ = ‖f‖
  proof: f.toContinuousMultilinearMap.curryLeft_norm

@[simp]

中文:
引理 norm_curryLeft
  条件: (f : E [⋀^有限集 (n + 1)]->L[𝕜] F)
  结论: ‖f.curryLeft‖ = ‖f‖
  证明: f.toContinuousMultilinearMap.curryLeft_norm

@[simp]

Depends on / 依赖: curryLeft_norm, f.toContinuousMultilinearMap.curryLeft_norm, toContinuousMultilinearMap
-/
lemma norm_curryLeft (f : E [⋀^Fin (n + 1)]->L[𝕜] F) : ‖f.curryLeft‖ = ‖f‖ :=
  f.toContinuousMultilinearMap.curryLeft_norm

@[simp]
/--
theorem `curryLeft_apply_apply` / 定理 `curryLeft_apply_apply`

English:
theorem curryLeft_apply_apply
  given: (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (x : E) (v : Fin n -> E)
  proof: rfl

@[simp]

中文:
定理 curryLeft_apply_apply
  条件: (f : E [⋀^有限集 (n + 1)]->L[𝕜] F) (x : E) (v : 有限集 n -> E)
  证明: rfl

@[simp]
-/
theorem curryLeft_apply_apply (f : E [⋀^Fin (n + 1)]->L[𝕜] F) (x : E) (v : Fin n -> E) :
    curryLeft f x v = f (Matrix.vecCons x v) :=
  rfl

@[simp]
/--
theorem `curryLeft_zero` / 定理 `curryLeft_zero`

English:
theorem curryLeft_zero
  statement: curryLeft (0 : E [⋀^Fin (n + 1)]->L[𝕜] F) = 0
  proof: rfl

@[simp]

中文:
定理 curryLeft_zero
  结论: curryLeft (0 : E [⋀^有限集 (n + 1)]->L[𝕜] F) = 0
  证明: rfl

@[simp]
-/
theorem curryLeft_zero : curryLeft (0 : E [⋀^Fin (n + 1)]->L[𝕜] F) = 0 :=
  rfl

@[simp]
/--
theorem `curryLeft_add` / 定理 `curryLeft_add`

English:
theorem curryLeft_add
  given: (f g : E [⋀^Fin (n + 1)]->L[𝕜] F)
  proof: rfl

@[simp]

中文:
定理 curryLeft_add
  条件: (f g : E [⋀^有限集 (n + 1)]->L[𝕜] F)
  证明: rfl

@[simp]
-/
theorem curryLeft_add (f g : E [⋀^Fin (n + 1)]->L[𝕜] F) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

@[simp]
/--
theorem `curryLeft_smul` / 定理 `curryLeft_smul`

English:
theorem curryLeft_smul
  given: (r : 𝕜) (f : E [⋀^Fin (n + 1)]->L[𝕜] F)
  proof: rfl

中文:
定理 curryLeft_smul
  条件: (r : 𝕜) (f : E [⋀^有限集 (n + 1)]->L[𝕜] F)
  证明: rfl
-/
theorem curryLeft_smul (r : 𝕜) (f : E [⋀^Fin (n + 1)]->L[𝕜] F) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `ContinuousAlternatingMap.curryLeft` as a `LinearIsometry`. -/
@[simps]
/--
Definition of `curryLeftLI` / `curryLeftLI` 的定义

English:
definition curryLeftLI
  signature: :
  body: f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul
  norm_map' := norm_curryLeft

中文:
定义 curryLeftLI
  签名: :
  定义体: f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul
  norm_map' := norm_curryLeft

Depends on / 依赖: curryLeft, f.curryLeft
-/
noncomputable def curryLeftLI :
    (E [⋀^Fin (n + 1)]->L[𝕜] F) ->ₗᵢ[𝕜] (E ->L[𝕜] E [⋀^Fin n]->L[𝕜] F) where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul
  norm_map' := norm_curryLeft

/-- Currying with the same element twice gives the zero map. -/
@[simp]
/--
theorem `curryLeft_same` / 定理 `curryLeft_same`

English:
theorem curryLeft_same
  given: (f : E [⋀^Fin (n + 2)]->L[𝕜] F) (x : E)
  proof: ext fun _ => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]

中文:
定理 curryLeft_same
  条件: (f : E [⋀^有限集 (n + 2)]->L[𝕜] F) (x : E)
  证明: ext fun _ => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]

Depends on / 依赖: Fin.zero_ne_one, f.map_eq_zero_of_eq, map_eq_zero_of_eq, zero_ne_one
-/
theorem curryLeft_same (f : E [⋀^Fin (n + 2)]->L[𝕜] F) (x : E) :
    (f.curryLeft x).curryLeft x = 0 :=
  ext fun _ => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]
/--
theorem `curryLeft_compContinuousAlternatingMap` / 定理 `curryLeft_compContinuousAlternatingMap`

English:
theorem curryLeft_compContinuousAlternatingMap
  statement: (g : F ->L[𝕜] G) (f : E [⋀^Fin (n + 1)]->L[𝕜] F)
  proof: rfl

@[simp]

中文:
定理 curryLeft_compContinuousAlternatingMap
  结论: (g : F ->L[𝕜] G) (f : E [⋀^有限集 (n + 1)]->L[𝕜] F)
  证明: rfl

@[simp]
-/
theorem curryLeft_compContinuousAlternatingMap (g : F ->L[𝕜] G) (f : E [⋀^Fin (n + 1)]->L[𝕜] F)
    (x : E) :
    (g.compContinuousAlternatingMap f).curryLeft x =
      g.compContinuousAlternatingMap (f.curryLeft x) :=
  rfl

@[simp]
/--
theorem `curryLeft_compContinuousLinearMap` / 定理 `curryLeft_compContinuousLinearMap`

English:
theorem curryLeft_compContinuousLinearMap
  given: (g : F [⋀^Fin (n + 1)]->L[𝕜] G) (f : E ->L[𝕜] F) (x : E)
  proof: ext fun v => congr_arg g funext fun i => by cases i using Fin.cases <;> simp

中文:
定理 curryLeft_compContinuousLinearMap
  条件: (g : F [⋀^有限集 (n + 1)]->L[𝕜] G) (f : E ->L[𝕜] F) (x : E)
  证明: ext fun v => congr_arg g funext fun i => by cases i using Fin.cases <;> simp

Depends on / 依赖: Fin.cases, congr_arg
-/
theorem curryLeft_compContinuousLinearMap (g : F [⋀^Fin (n + 1)]->L[𝕜] G) (f : E ->L[𝕜] F) (x : E) :
    (g.compContinuousLinearMap f).curryLeft x = (g.curryLeft (f x)).compContinuousLinearMap f :=
ext fun v => congr_arg g funext fun i => by cases i using Fin.cases <;> simp

end ContinuousAlternatingMap
