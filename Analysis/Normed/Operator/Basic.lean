/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Tactic.SuppressCompilation

/-!
# Operator norm on the space of continuous linear maps

Define the operator (semi)-norm on the space of continuous (semi)linear maps between (semi)-normed
spaces, and prove its basic properties. In particular, show that this space is itself a semi-normed
space.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup`. Later we will specialize to `NormedAddCommGroup` in the
file `NormedSpace.lean`.

Note that most of statements that apply to semilinear maps only hold when the ring homomorphism
is isometric, as expressed by the typeclass `[RingHomIsometric σ]`.

## Main Results
* `ball_subset_range_iff_surjective` (and its variants) shows that a semi-linear map between normed
  spaces is surjective if and only if it contains a ball.

-/

@[expose] public section

suppress_compilation

open Bornology Metric
open Filter hiding map_smul
open scoped NNReal Topology Uniformity ENNReal

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E F Fₗ G 𝓕 : Type*}

section SemiNormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup Fₗ]
  [SeminormedAddCommGroup G]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₃ : 𝕜₂ ->+* 𝕜₃} {σ₁₃ : 𝕜 ->+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [FunLike 𝓕 E F]

section

variable [SemilinearMapClass 𝓕 σ₁₂ E F]

/--
theorem `ball_zero_subset_range_iff_surjective` / 定理 `ball_zero_subset_range_iff_surjective`

English:
theorem ball_zero_subset_range_iff_surjective
  statement: [RingHomSurjective σ₁₂] {f : 𝓕} {r : Real}
  proof: .subset_range_iff_surjective (f := (f : E ->ₛₗ[σ₁₂] F)) absorbent_ball (by simpa)

中文:
定理 ball_zero_subset_range_iff_surjective
  结论: [RingHomSurjective σ₁₂] {f : 𝓕} {r : 实数}
  证明: .subset_range_iff_surjective (f := (f : E ->ₛₗ[σ₁₂] F)) absorbent_ball (by simpa)

Depends on / 依赖: absorbent_ball, subset_range_iff_surjective
-/
theorem ball_zero_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {r : Real}
    (hr : 0 < r) : ball 0 r subseteq Set.range f ↔ (⇑f).Surjective :=
.subset_range_iff_surjective (f := (f : E ->ₛₗ[σ₁₂] F)) absorbent_ball (by simpa)

/--
theorem `ball_subset_range_iff_surjective` / 定理 `ball_subset_range_iff_surjective`

English:
theorem ball_subset_range_iff_surjective
  statement: [RingHomSurjective σ₁₂] {f : 𝓕} {x : F} {r : Real}
  proof: by
  refine ⟨fun h => ?_, by simp_all⟩
  rw [← ball_zero_subset_range_iff_surjective hr]; rw [← LinearMap.coe_coe]
  simp_rw [← LinearMap.coe_range, Set.subset_def, SetLike.mem_coe] at h ⊢
  intro _ _
  rw [← Submodule.add_mem_iff_left (f : E ->ₛₗ[σ₁₂] F).range (h _ <| mem_ball_self hr)]
  apply h
  simp_all

中文:
定理 ball_subset_range_iff_surjective
  结论: [RingHomSurjective σ₁₂] {f : 𝓕} {x : F} {r : 实数}
  证明: by
  refine ⟨fun h => ?_, by simp_all⟩
  rw [← ball_zero_subset_range_iff_surjective hr]; rw [← LinearMap.coe_coe]
  simp_rw [← LinearMap.coe_range, Set.subset_def, SetLike.mem_coe] at h ⊢
  intro _ _
  rw [← Submodule.add_mem_iff_left (f : E ->ₛₗ[σ₁₂] F).range (h _ <| mem_ball_self hr)]
  apply h
  simp_all

Depends on / 依赖: LinearMap, LinearMap.coe_coe, LinearMap.coe_range, Set.subset_def, SetLike, SetLike.mem_coe, Submodule, Submodule.add_mem_iff_left, add_mem_iff_left, ball_zero_subset_range_iff_surjective, coe_coe, coe_range, mem_ball_self, mem_coe, simp_rw, subset_def
-/
theorem ball_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} {x : F} {r : Real}
    (hr : 0 < r) : ball x r subseteq Set.range f ↔ (⇑f).Surjective := by
  refine ⟨fun h => ?_, by simp_all⟩
  rw [← ball_zero_subset_range_iff_surjective hr]; rw [← LinearMap.coe_coe]
  simp_rw [← LinearMap.coe_range, Set.subset_def, SetLike.mem_coe] at h ⊢
  intro _ _
  rw [← Submodule.add_mem_iff_left (f : E ->ₛₗ[σ₁₂] F).range (h _ <| mem_ball_self hr)]
  apply h
  simp_all

/--
theorem `closedBall_subset_range_iff_surjective` / 定理 `closedBall_subset_range_iff_surjective`

English:
theorem closedBall_subset_range_iff_surjective
  statement: [RingHomSurjective σ₁₂] {f : 𝓕} (x : F) {r : Real}
  proof: ⟨fun h => (ball_subset_range_iff_surjective hr).mp subset_trans ball_subset_closedBall h,
    by simp_all⟩

中文:
定理 closedBall_subset_range_iff_surjective
  结论: [RingHomSurjective σ₁₂] {f : 𝓕} (x : F) {r : 实数}
  证明: ⟨fun h => (ball_subset_range_iff_surjective hr).mp subset_trans ball_subset_closedBall h,
    by simp_all⟩

Depends on / 依赖: ball_subset_closedBall, ball_subset_range_iff_surjective, subset_trans
-/
theorem closedBall_subset_range_iff_surjective [RingHomSurjective σ₁₂] {f : 𝓕} (x : F) {r : Real}
    (hr : 0 < r) : closedBall (x : F) r subseteq Set.range f ↔ (⇑f).Surjective :=
⟨fun h => (ball_subset_range_iff_surjective hr).mp subset_trans ball_subset_closedBall h,
    by simp_all⟩

variable {F' 𝓕' : Type*} [NormedAddCommGroup F'] [NormedSpace Real F'] [Nontrivial F']
  {τ : 𝕜 ->+* Real} [FunLike 𝓕' E F'] [SemilinearMapClass 𝓕' τ E F']

/--
theorem `sphere_subset_range_iff_surjective` / 定理 `sphere_subset_range_iff_surjective`

English:
theorem sphere_subset_range_iff_surjective
  statement: [RingHomSurjective τ] {f : 𝓕'} {x : F'} {r : Real}
  proof: by
  refine ⟨fun h => ?_, by simp_all⟩
  grw [← (closedBall_subset_range_iff_surjective x hr), ← convexHull_sphere_eq_closedBall x hr.le,
    convexHull_mono h, (convexHull_eq_self (𝕜 := Real) (s := Set.range ↑f)).mpr]
  exact Submodule.Convex.semilinear_range (E := F') (F' := E) (σ := τ) f

中文:
定理 sphere_subset_range_iff_surjective
  结论: [RingHomSurjective τ] {f : 𝓕'} {x : F'} {r : 实数}
  证明: by
  refine ⟨fun h => ?_, by simp_all⟩
  grw [← (closedBall_subset_range_iff_surjective x hr), ← convexHull_sphere_eq_closedBall x hr.le,
    convexHull_mono h, (convexHull_eq_self (𝕜 := Real) (s := Set.range ↑f)).mpr]
  exact Submodule.Convex.semilinear_range (E := F') (F' := E) (σ := τ) f

Depends on / 依赖: Convex, Set.range, Submodule, Submodule.Convex.semilinear_range, closedBall_subset_range_iff_surjective, convexHull_eq_self, convexHull_mono, convexHull_sphere_eq_closedBall, hr.le, semilinear_range
-/
theorem sphere_subset_range_iff_surjective [RingHomSurjective τ] {f : 𝓕'} {x : F'} {r : Real}
    (hr : 0 < r) : sphere x r subseteq Set.range f ↔ (⇑f).Surjective := by
  refine ⟨fun h => ?_, by simp_all⟩
  grw [← (closedBall_subset_range_iff_surjective x hr), ← convexHull_sphere_eq_closedBall x hr.le,
    convexHull_mono h, (convexHull_eq_self (𝕜 := Real) (s := Set.range ↑f)).mpr]
  exact Submodule.Convex.semilinear_range (E := F') (F' := E) (σ := τ) f

end

/--
theorem `norm_image_of_norm_eq_zero` / 定理 `norm_image_of_norm_eq_zero`

English:
theorem norm_image_of_norm_eq_zero
  statement: [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f)
  proof: by
  rw [← mem_closure_zero_iff_norm]; rw [← specializes_iff_mem_closure]; rw [← map_zero f] at *
  exact hx.map hf

中文:
定理 norm_image_of_norm_eq_zero
  结论: [半线性映射类 𝓕 σ₁₂ E F] (f : 𝓕) (hf : 连续 f)
  证明: by
  rw [← mem_closure_zero_iff_norm]; rw [← specializes_iff_mem_closure]; rw [← map_zero f] at *
  exact hx.map hf

Depends on / 依赖: hx.map, map_zero, mem_closure_zero_iff_norm, specializes_iff_mem_closure
-/
theorem norm_image_of_norm_eq_zero [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f)
    {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0 := by
  rw [← mem_closure_zero_iff_norm]; rw [← specializes_iff_mem_closure]; rw [← map_zero f] at *
  exact hx.map hf

section

variable [RingHomIsometric σ₁₂]

/--
theorem `SemilinearMapClass.bound_of_shell_semi_normed` / 定理 `SemilinearMapClass.bound_of_shell_semi_normed`

English:
theorem SemilinearMapClass.bound_of_shell_semi_normed
  statement: [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
  proof: (normSeminorm 𝕜 E).bound_of_shell ((normSeminorm 𝕜₂ F).comp ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩)
    ε_pos hc hf hx

中文:
定理 半线性映射类.bound_of_shell_semi_normed
  结论: [半线性映射类 𝓕 σ₁₂ E F] (f : 𝓕)
  证明: (normSeminorm 𝕜 E).bound_of_shell ((normSeminorm 𝕜₂ F).comp ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩)
    ε_pos hc hf hx

Depends on / 依赖: bound_of_shell, map_add, normSeminorm
-/
theorem SemilinearMapClass.bound_of_shell_semi_normed [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    {ε C : Real} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : forall x, ε / ‖c‖ <= ‖x‖ -> ‖x‖ < ε -> ‖f x‖ <= C * ‖x‖) {x : E} (hx : ‖x‖ != 0) :
    ‖f x‖ <= C * ‖x‖ :=
  (normSeminorm 𝕜 E).bound_of_shell ((normSeminorm 𝕜₂ F).comp ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩)
    ε_pos hc hf hx

/--
theorem `SemilinearMapClass.bound_of_continuous` / 定理 `SemilinearMapClass.bound_of_continuous`

English:
theorem SemilinearMapClass.bound_of_continuous
  statement: [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
  proof: let φ : E ->ₛₗ[σ₁₂] F := ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩
  ((normSeminorm 𝕜₂ F).comp φ).bound_of_continuous_normedSpace (continuous_norm.comp hf)

中文:
定理 半线性映射类.bound_of_continuous
  结论: [半线性映射类 𝓕 σ₁₂ E F] (f : 𝓕)
  证明: let φ : E ->ₛₗ[σ₁₂] F := ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩
  ((normSeminorm 𝕜₂ F).comp φ).bound_of_continuous_normedSpace (continuous_norm.comp hf)

Depends on / 依赖: bound_of_continuous_normedSpace, continuous_norm, continuous_norm.comp, map_add, normSeminorm
-/
theorem SemilinearMapClass.bound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : exists C, 0 < C ∧ forall x : E, ‖f x‖ <= C * ‖x‖ :=
  let φ : E ->ₛₗ[σ₁₂] F := ⟨⟨f, map_add f⟩, map_smulₛₗ f⟩
  ((normSeminorm 𝕜₂ F).comp φ).bound_of_continuous_normedSpace (continuous_norm.comp hf)

/--
theorem `SemilinearMapClass.nnbound_of_continuous` / 定理 `SemilinearMapClass.nnbound_of_continuous`

English:
theorem SemilinearMapClass.nnbound_of_continuous
  statement: [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
  proof: let ⟨c, hc, hcf⟩ := SemilinearMapClass.bound_of_continuous f hf; ⟨⟨c, hc.le⟩, hc, hcf⟩

中文:
定理 半线性映射类.nnbound_of_continuous
  结论: [半线性映射类 𝓕 σ₁₂ E F] (f : 𝓕)
  证明: let ⟨c, hc, hcf⟩ := SemilinearMapClass.bound_of_continuous f hf; ⟨⟨c, hc.le⟩, hc, hcf⟩

Depends on / 依赖: SemilinearMapClass, SemilinearMapClass.bound_of_continuous, bound_of_continuous, hc.le
-/
theorem SemilinearMapClass.nnbound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : exists C : Real>=0, 0 < C ∧ forall x : E, ‖f x‖₊ <= C * ‖x‖₊ :=
  let ⟨c, hc, hcf⟩ := SemilinearMapClass.bound_of_continuous f hf; ⟨⟨c, hc.le⟩, hc, hcf⟩

/--
theorem `SemilinearMapClass.ebound_of_continuous` / 定理 `SemilinearMapClass.ebound_of_continuous`

English:
theorem SemilinearMapClass.ebound_of_continuous
  statement: [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
  proof: let ⟨c, hc, hcf⟩ := SemilinearMapClass.nnbound_of_continuous f hf
⟨c, hc, fun x => ENNReal.coe_mono hcf x⟩

中文:
定理 半线性映射类.ebound_of_continuous
  结论: [半线性映射类 𝓕 σ₁₂ E F] (f : 𝓕)
  证明: let ⟨c, hc, hcf⟩ := SemilinearMapClass.nnbound_of_continuous f hf
⟨c, hc, fun x => ENNReal.coe_mono hcf x⟩

Depends on / 依赖: ENNReal, ENNReal.coe_mono, SemilinearMapClass, SemilinearMapClass.nnbound_of_continuous, coe_mono, nnbound_of_continuous
-/
theorem SemilinearMapClass.ebound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : exists C : Real>=0, 0 < C ∧ forall x : E, ‖f x‖ₑ <= C * ‖x‖ₑ :=
  let ⟨c, hc, hcf⟩ := SemilinearMapClass.nnbound_of_continuous f hf
⟨c, hc, fun x => ENNReal.coe_mono hcf x⟩

end

namespace ContinuousLinearMap

/--
theorem `bound` / 定理 `bound`

English:
theorem bound
  given: [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F)
  statement: exists C, 0 < C ∧ forall x : E, ‖f x‖ <= C * ‖x‖
  proof: SemilinearMapClass.bound_of_continuous f f.2

中文:
定理 bound
  条件: [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F)
  结论: 存在 C, 0 < C ∧ 对任意 x : E, ‖f x‖ <= C * ‖x‖
  证明: SemilinearMapClass.bound_of_continuous f f.2

Depends on / 依赖: SemilinearMapClass, SemilinearMapClass.bound_of_continuous, bound_of_continuous
-/
theorem bound [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F) : exists C, 0 < C ∧ forall x : E, ‖f x‖ <= C * ‖x‖ :=
  SemilinearMapClass.bound_of_continuous f f.2

/--
theorem `nnbound` / 定理 `nnbound`

English:
theorem nnbound
  given: [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F)
  proof: SemilinearMapClass.nnbound_of_continuous f f.2

中文:
定理 nnbound
  条件: [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F)
  证明: SemilinearMapClass.nnbound_of_continuous f f.2

Depends on / 依赖: SemilinearMapClass, SemilinearMapClass.nnbound_of_continuous, nnbound_of_continuous
-/
theorem nnbound [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F) :
    exists C : Real>=0, 0 < C ∧ forall x : E, ‖f x‖₊ <= C * ‖x‖₊ :=
  SemilinearMapClass.nnbound_of_continuous f f.2

/--
theorem `ebound` / 定理 `ebound`

English:
theorem ebound
  given: [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F)
  proof: SemilinearMapClass.ebound_of_continuous f f.2

中文:
定理 ebound
  条件: [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F)
  证明: SemilinearMapClass.ebound_of_continuous f f.2

Depends on / 依赖: SemilinearMapClass, SemilinearMapClass.ebound_of_continuous, ebound_of_continuous
-/
theorem ebound [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F) :
    exists C : Real>=0, 0 < C ∧ forall x : E, ‖f x‖ₑ <= C * ‖x‖ₑ :=
  SemilinearMapClass.ebound_of_continuous f f.2

section

open Filter

variable (𝕜 E)

/--
Definition of `_root_.LinearIsometry.toSpanSingleton` / `_root_.LinearIsometry.toSpanSingleton` 的定义

English:
definition _root_.LinearIsometry.toSpanSingleton
  signature: {v : E} (hv : ‖v‖ = 1)
  body: { LinearMap.toSpanSingleton 𝕜 E v with norm_map' := fun x => by simp [norm_smul, hv] }

中文:
定义 _root_.线性等距.toSpanSingleton
  签名: {v : E} (hv : ‖v‖ = 1)
  定义体: { LinearMap.toSpanSingleton 𝕜 E v with norm_map' := fun x => by simp [norm_smul, hv] }

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton, norm_map, norm_smul, toSpanSingleton
-/
def _root_.LinearIsometry.toSpanSingleton {v : E} (hv : ‖v‖ = 1) : 𝕜 ->ₗᵢ[𝕜] E :=
  { LinearMap.toSpanSingleton 𝕜 E v with norm_map' := fun x => by simp [norm_smul, hv] }

variable {𝕜 E}

@[simp]
/--
theorem `_root_.LinearIsometry.toSpanSingleton_apply` / 定理 `_root_.LinearIsometry.toSpanSingleton_apply`

English:
theorem _root_.LinearIsometry.toSpanSingleton_apply
  given: {v : E} (hv : ‖v‖ = 1) (a : 𝕜)
  proof: rfl

@[simp]

中文:
定理 _root_.线性等距.toSpanSingleton_apply
  条件: {v : E} (hv : ‖v‖ = 1) (a : 𝕜)
  证明: rfl

@[simp]
-/
theorem _root_.LinearIsometry.toSpanSingleton_apply {v : E} (hv : ‖v‖ = 1) (a : 𝕜) :
    LinearIsometry.toSpanSingleton 𝕜 E hv a = a • v :=
  rfl

@[simp]
/--
theorem `_root_.LinearIsometry.coe_toSpanSingleton` / 定理 `_root_.LinearIsometry.coe_toSpanSingleton`

English:
theorem _root_.LinearIsometry.coe_toSpanSingleton
  given: {v : E} (hv : ‖v‖ = 1)
  proof: rfl

中文:
定理 _root_.线性等距.coe_toSpanSingleton
  条件: {v : E} (hv : ‖v‖ = 1)
  证明: rfl
-/
theorem _root_.LinearIsometry.coe_toSpanSingleton {v : E} (hv : ‖v‖ = 1) :
    (LinearIsometry.toSpanSingleton 𝕜 E hv).toLinearMap = LinearMap.toSpanSingleton 𝕜 E v :=
  rfl

end

section OpNorm

open Set Real

/--
Definition of `opNorm` / `opNorm` 的定义

English:
definition opNorm
  signature: (f : E ->SL[σ₁₂] F)
  body: sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }

中文:
定义 opNorm
  签名: (f : E ->SL[σ₁₂] F)
  定义体: sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
-/
def opNorm (f : E ->SL[σ₁₂] F) :=
  sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }

/--
Instance `hasOpNorm` / 实例 `hasOpNorm`

English:
instance hasOpNorm
  signature: : Norm (E ->SL[σ₁₂] F)
  body: ⟨opNorm⟩

中文:
实例 hasOpNorm
  签名: : 范数 (E ->SL[σ₁₂] F)
  定义体: ⟨opNorm⟩

Depends on / 依赖: opNorm
-/
instance hasOpNorm : Norm (E ->SL[σ₁₂] F) :=
  ⟨opNorm⟩

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (f : E ->SL[σ₁₂] F)
  statement: ‖f‖ = sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
  proof: rfl

中文:
定理 norm_def
  条件: (f : E ->SL[σ₁₂] F)
  结论: ‖f‖ = sInf { c | 0 <= c ∧ 对任意 x, ‖f x‖ <= c * ‖x‖ }
  证明: rfl
-/
theorem norm_def (f : E ->SL[σ₁₂] F) : ‖f‖ = sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ } :=
  rfl

-- So that invocations of `le_csInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
/--
theorem `bounds_nonempty` / 定理 `bounds_nonempty`

English:
theorem bounds_nonempty
  given: [RingHomIsometric σ₁₂] {f : E ->SL[σ₁₂] F}
  proof: let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

中文:
定理 bounds_nonempty
  条件: [RingHomIsometric σ₁₂] {f : E ->SL[σ₁₂] F}
  证明: let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

Depends on / 依赖: f.bound, le_of_lt
-/
theorem bounds_nonempty [RingHomIsometric σ₁₂] {f : E ->SL[σ₁₂] F} :
    exists c, c in { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

/--
theorem `bounds_bddBelow` / 定理 `bounds_bddBelow`

English:
theorem bounds_bddBelow
  given: {f : E ->SL[σ₁₂] F}
  statement: BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
  proof: ⟨0, fun _ ⟨hn, _⟩ => hn⟩

中文:
定理 bounds_bddBelow
  条件: {f : E ->SL[σ₁₂] F}
  结论: BddBelow { c | 0 <= c ∧ 对任意 x, ‖f x‖ <= c * ‖x‖ }
  证明: ⟨0, fun _ ⟨hn, _⟩ => hn⟩
-/
theorem bounds_bddBelow {f : E ->SL[σ₁₂] F} : BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

/--
theorem `isLeast_opNorm` / 定理 `isLeast_opNorm`

English:
theorem isLeast_opNorm
  given: [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F)
  proof: by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [ofPred_and, ofPred_forall]
refine isClosed_Ici.inter isClosed_iInter fun _ => isClosed_le ?_ ?_ <;> fun_prop

中文:
定理 isLeast_opNorm
  条件: [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F)
  证明: by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [ofPred_and, ofPred_forall]
refine isClosed_Ici.inter isClosed_iInter fun _ => isClosed_le ?_ ?_ <;> fun_prop

Depends on / 依赖: IsClosed, IsClosed.isLeast_csInf, bounds_bddBelow, bounds_nonempty, fun_prop, isClosed_Ici, isClosed_Ici.inter, isClosed_iInter, isClosed_le, isLeast_csInf, ofPred_and, ofPred_forall
-/
theorem isLeast_opNorm [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F) :
    IsLeast {c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖} ‖f‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [ofPred_and, ofPred_forall]
refine isClosed_Ici.inter isClosed_iInter fun _ => isClosed_le ?_ ?_ <;> fun_prop

/--
theorem `opNorm_le_bound` / 定理 `opNorm_le_bound`

English:
theorem opNorm_le_bound
  given: (f : E ->SL[σ₁₂] F) {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖)
  proof: csInf_le bounds_bddBelow ⟨hMp, hM⟩

中文:
定理 opNorm_le_bound
  条件: (f : E ->SL[σ₁₂] F) {M : 实数} (hMp : 0 <= M) (hM : 对任意 x, ‖f x‖ <= M * ‖x‖)
  证明: csInf_le bounds_bddBelow ⟨hMp, hM⟩

Depends on / 依赖: bounds_bddBelow, csInf_le
-/
theorem opNorm_le_bound (f : E ->SL[σ₁₂] F) {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) :
    ‖f‖ <= M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩

/--
theorem `opNorm_le_bound'` / 定理 `opNorm_le_bound'`

English:
theorem opNorm_le_bound'
  statement: (f : E ->SL[σ₁₂] F) {M : Real} (hMp : 0 <= M)
  proof: opNorm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, mul_zero, norm_image_of_norm_eq_zero f f.2 h, le_refl]

中文:
定理 opNorm_le_bound'
  结论: (f : E ->SL[σ₁₂] F) {M : 实数} (hMp : 0 <= M)
  证明: opNorm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, mul_zero, norm_image_of_norm_eq_zero f f.2 h, le_refl]

Depends on / 依赖: le_refl, mul_zero, ne_or_eq, norm_image_of_norm_eq_zero, opNorm_le_bound
-/
theorem opNorm_le_bound' (f : E ->SL[σ₁₂] F) {M : Real} (hMp : 0 <= M)
    (hM : forall x, ‖x‖ != 0 -> ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M :=
  opNorm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, mul_zero, norm_image_of_norm_eq_zero f f.2 h, le_refl]

/--
theorem `opNorm_eq_of_bounds` / 定理 `opNorm_eq_of_bounds`

English:
theorem opNorm_eq_of_bounds
  statement: {φ : E ->SL[σ₁₂] F} {M : Real} (M_nonneg : 0 <= M)
  proof: le_antisymm (φ.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff ContinuousLinearMap.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

中文:
定理 opNorm_eq_of_bounds
  结论: {φ : E ->SL[σ₁₂] F} {M : 实数} (M_nonneg : 0 <= M)
  证明: le_antisymm (φ.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff ContinuousLinearMap.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.bounds_bddBelow, M_nonneg, N_nonneg, bounds_bddBelow, h_above, h_below, le_antisymm, le_csInf_iff, opNorm_le_bound
-/
theorem opNorm_eq_of_bounds {φ : E ->SL[σ₁₂] F} {M : Real} (M_nonneg : 0 <= M)
    (h_above : forall x, ‖φ x‖ <= M * ‖x‖) (h_below : forall N >= 0, (forall x, ‖φ x‖ <= N * ‖x‖) -> M <= N) :
    ‖φ‖ = M :=
  le_antisymm (φ.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff ContinuousLinearMap.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

/--
theorem `opNorm_neg` / 定理 `opNorm_neg`

English:
theorem opNorm_neg
  given: (f : E ->SL[σ₁₂] F)
  statement: ‖-f‖ = ‖f‖
  proof: by simp only [norm_def, neg_apply, norm_neg]

中文:
定理 opNorm_neg
  条件: (f : E ->SL[σ₁₂] F)
  结论: ‖-f‖ = ‖f‖
  证明: by simp only [norm_def, neg_apply, norm_neg]

Depends on / 依赖: neg_apply, norm_def, norm_neg
-/
theorem opNorm_neg (f : E ->SL[σ₁₂] F) : ‖-f‖ = ‖f‖ := by simp only [norm_def, neg_apply, norm_neg]

/--
theorem `opNorm_nonneg` / 定理 `opNorm_nonneg`

English:
theorem opNorm_nonneg
  given: (f : E ->SL[σ₁₂] F)
  statement: 0 <= ‖f‖
  proof: Real.sInf_nonneg fun _ => And.left

中文:
定理 opNorm_nonneg
  条件: (f : E ->SL[σ₁₂] F)
  结论: 0 <= ‖f‖
  证明: Real.sInf_nonneg fun _ => And.left

Depends on / 依赖: And.left, Real.sInf_nonneg, sInf_nonneg
-/
theorem opNorm_nonneg (f : E ->SL[σ₁₂] F) : 0 <= ‖f‖ :=
  Real.sInf_nonneg fun _ => And.left

/--
theorem `opNorm_zero` / 定理 `opNorm_zero`

English:
theorem opNorm_zero
  statement: ‖(0 : E ->SL[σ₁₂] F)‖ = 0
  proof: le_antisymm (opNorm_le_bound _ le_rfl fun _ => by simp) (opNorm_nonneg _)

中文:
定理 opNorm_zero
  结论: ‖(0 : E ->SL[σ₁₂] F)‖ = 0
  证明: le_antisymm (opNorm_le_bound _ le_rfl fun _ => by simp) (opNorm_nonneg _)

Depends on / 依赖: le_antisymm, le_rfl, opNorm_le_bound, opNorm_nonneg
-/
theorem opNorm_zero : ‖(0 : E ->SL[σ₁₂] F)‖ = 0 :=
  le_antisymm (opNorm_le_bound _ le_rfl fun _ => by simp) (opNorm_nonneg _)

/--
theorem `norm_id_le` / 定理 `norm_id_le`

English:
theorem norm_id_le
  statement: ‖ContinuousLinearMap.id 𝕜 E‖ <= 1
  proof: opNorm_le_bound _ zero_le_one fun x => by simp

中文:
定理 norm_id_le
  结论: ‖连续线性映射.id 𝕜 E‖ <= 1
  证明: opNorm_le_bound _ zero_le_one fun x => by simp

Depends on / 依赖: opNorm_le_bound, zero_le_one
-/
theorem norm_id_le : ‖ContinuousLinearMap.id 𝕜 E‖ <= 1 :=
  opNorm_le_bound _ zero_le_one fun x => by simp

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (f g : E ->SL[σ₁₂] F) (h : F ->SL[σ₂₃] G)
  (x : E)

/--
theorem `le_opNorm` / 定理 `le_opNorm`

English:
theorem le_opNorm
  statement: ‖f x‖ <= ‖f‖ * ‖x‖
  proof: (isLeast_opNorm f).1.2 x

中文:
定理 le_opNorm
  结论: ‖f x‖ <= ‖f‖ * ‖x‖
  证明: (isLeast_opNorm f).1.2 x

Depends on / 依赖: isLeast_opNorm
-/
theorem le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x

/--
theorem `dist_le_opNorm` / 定理 `dist_le_opNorm`

English:
theorem dist_le_opNorm
  given: (x y : E)
  statement: dist (f x) (f y) <= ‖f‖ * dist x y
  proof: by
  simp_rw [dist_eq_norm, ← map_sub, f.le_opNorm]

中文:
定理 dist_le_opNorm
  条件: (x y : E)
  结论: dist (f x) (f y) <= ‖f‖ * dist x y
  证明: by
  simp_rw [dist_eq_norm, ← map_sub, f.le_opNorm]

Depends on / 依赖: dist_eq_norm, f.le_opNorm, le_opNorm, map_sub, simp_rw
-/
theorem dist_le_opNorm (x y : E) : dist (f x) (f y) <= ‖f‖ * dist x y := by
  simp_rw [dist_eq_norm, ← map_sub, f.le_opNorm]

/--
theorem `le_of_opNorm_le_of_le` / 定理 `le_of_opNorm_le_of_le`

English:
theorem le_of_opNorm_le_of_le
  given: {x} {a b : Real} (hf : ‖f‖ <= a) (hx : ‖x‖ <= b)
  proof: (f.le_opNorm x).trans by gcongr; exact (opNorm_nonneg f).trans hf

中文:
定理 le_of_opNorm_le_of_le
  条件: {x} {a b : 实数} (hf : ‖f‖ <= a) (hx : ‖x‖ <= b)
  证明: (f.le_opNorm x).trans by gcongr; exact (opNorm_nonneg f).trans hf

Depends on / 依赖: f.le_opNorm, le_opNorm, opNorm_nonneg
-/
theorem le_of_opNorm_le_of_le {x} {a b : Real} (hf : ‖f‖ <= a) (hx : ‖x‖ <= b) :
    ‖f x‖ <= a * b :=
(f.le_opNorm x).trans by gcongr; exact (opNorm_nonneg f).trans hf

/--
theorem `le_opNorm_of_le` / 定理 `le_opNorm_of_le`

English:
theorem le_opNorm_of_le
  given: {c : Real} {x} (h : ‖x‖ <= c)
  statement: ‖f x‖ <= ‖f‖ * c
  proof: f.le_of_opNorm_le_of_le le_rfl h

中文:
定理 le_opNorm_of_le
  条件: {c : 实数} {x} (h : ‖x‖ <= c)
  结论: ‖f x‖ <= ‖f‖ * c
  证明: f.le_of_opNorm_le_of_le le_rfl h

Depends on / 依赖: f.le_of_opNorm_le_of_le, le_of_opNorm_le_of_le, le_rfl
-/
theorem le_opNorm_of_le {c : Real} {x} (h : ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c :=
  f.le_of_opNorm_le_of_le le_rfl h

/--
theorem `le_of_opNorm_le` / 定理 `le_of_opNorm_le`

English:
theorem le_of_opNorm_le
  given: {c : Real} (h : ‖f‖ <= c) (x : E)
  statement: ‖f x‖ <= c * ‖x‖
  proof: f.le_of_opNorm_le_of_le h le_rfl

中文:
定理 le_of_opNorm_le
  条件: {c : 实数} (h : ‖f‖ <= c) (x : E)
  结论: ‖f x‖ <= c * ‖x‖
  证明: f.le_of_opNorm_le_of_le h le_rfl

Depends on / 依赖: f.le_of_opNorm_le_of_le, le_of_opNorm_le_of_le, le_rfl
-/
theorem le_of_opNorm_le {c : Real} (h : ‖f‖ <= c) (x : E) : ‖f x‖ <= c * ‖x‖ :=
  f.le_of_opNorm_le_of_le h le_rfl

/--
theorem `opNorm_le_iff` / 定理 `opNorm_le_iff`

English:
theorem opNorm_le_iff
  given: {f : E ->SL[σ₁₂] F} {M : Real} (hMp : 0 <= M)
  proof: ⟨f.le_of_opNorm_le, opNorm_le_bound f hMp⟩

中文:
定理 opNorm_le_iff
  条件: {f : E ->SL[σ₁₂] F} {M : 实数} (hMp : 0 <= M)
  证明: ⟨f.le_of_opNorm_le, opNorm_le_bound f hMp⟩

Depends on / 依赖: f.le_of_opNorm_le, le_of_opNorm_le, opNorm_le_bound
-/
theorem opNorm_le_iff {f : E ->SL[σ₁₂] F} {M : Real} (hMp : 0 <= M) :
    ‖f‖ <= M ↔ forall x, ‖f x‖ <= M * ‖x‖ :=
  ⟨f.le_of_opNorm_le, opNorm_le_bound f hMp⟩

/--
theorem `ratio_le_opNorm` / 定理 `ratio_le_opNorm`

English:
theorem ratio_le_opNorm
  statement: ‖f x‖ / ‖x‖ <= ‖f‖
  proof: div_le_of_le_mul₀ (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)

中文:
定理 ratio_le_opNorm
  结论: ‖f x‖ / ‖x‖ <= ‖f‖
  证明: div_le_of_le_mul₀ (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)

Depends on / 依赖: f.opNorm_nonneg, le_opNorm, norm_nonneg, opNorm_nonneg
-/
theorem ratio_le_opNorm : ‖f x‖ / ‖x‖ <= ‖f‖ :=
  div_le_of_le_mul₀ (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)

/--
theorem `unit_le_opNorm` / 定理 `unit_le_opNorm`

English:
theorem unit_le_opNorm
  statement: ‖x‖ <= 1 -> ‖f x‖ <= ‖f‖
  proof: mul_one ‖f‖ ▸ f.le_opNorm_of_le

中文:
定理 unit_le_opNorm
  结论: ‖x‖ <= 1 -> ‖f x‖ <= ‖f‖
  证明: mul_one ‖f‖ ▸ f.le_opNorm_of_le

Depends on / 依赖: f.le_opNorm_of_le, le_opNorm_of_le, mul_one
-/
theorem unit_le_opNorm : ‖x‖ <= 1 -> ‖f x‖ <= ‖f‖ :=
  mul_one ‖f‖ ▸ f.le_opNorm_of_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyBoundedMapClass (E ->SL[σ₁₂] F) E F
  body: by
    intro ℓ
    rw [Bornology.comap_cobounded_le_iff]
    intro s hs
    obtain ⟨M, hM⟩ := hs.exists_norm_le
    rw [isBounded_iff_forall_norm_le]
    use ‖ℓ‖ * M
    intro y hy
    obtain ⟨σ, hσ⟩ := (mem_image _ _ _).1 hy
    calc ‖y‖
      _ <= ‖ℓ σ‖ := by rw [hσ.2]
      _ <= ‖ℓ‖ * ‖σ‖ := ContinuousLinearMap.le_opNorm ℓ σ
      _ <= ‖ℓ‖ * M := mul_le_mul (by rfl) (hM σ hσ.1) (norm_nonneg σ) (opNorm_nonneg ℓ)

中文:
实例 :
  签名: LocallyBounded映射类 (E ->SL[σ₁₂] F) E F
  定义体: by
    intro ℓ
    rw [Bornology.comap_cobounded_le_iff]
    intro s hs
    obtain ⟨M, hM⟩ := hs.exists_norm_le
    rw [isBounded_iff_forall_norm_le]
    use ‖ℓ‖ * M
    intro y hy
    obtain ⟨σ, hσ⟩ := (mem_image _ _ _).1 hy
    calc ‖y‖
      _ <= ‖ℓ σ‖ := by rw [hσ.2]
      _ <= ‖ℓ‖ * ‖σ‖ := ContinuousLinearMap.le_opNorm ℓ σ
      _ <= ‖ℓ‖ * M := mul_le_mul (by rfl) (hM σ hσ.1) (norm_nonneg σ) (opNorm_nonneg ℓ)

Depends on / 依赖: Bornology, Bornology.comap_cobounded_le_iff, ContinuousLinearMap, ContinuousLinearMap.le_opNorm, comap_cobounded_le_iff, exists_norm_le, hs.exists_norm_le, isBounded_iff_forall_norm_le, le_opNorm, mem_image, mul_le_mul, norm_nonneg, opNorm_nonneg
-/
instance : LocallyBoundedMapClass (E ->SL[σ₁₂] F) E F where
  comap_cobounded_le := by
    intro ℓ
    rw [Bornology.comap_cobounded_le_iff]
    intro s hs
    obtain ⟨M, hM⟩ := hs.exists_norm_le
    rw [isBounded_iff_forall_norm_le]
    use ‖ℓ‖ * M
    intro y hy
    obtain ⟨σ, hσ⟩ := (mem_image _ _ _).1 hy
    calc ‖y‖
      _ <= ‖ℓ σ‖ := by rw [hσ.2]
      _ <= ‖ℓ‖ * ‖σ‖ := ContinuousLinearMap.le_opNorm ℓ σ
      _ <= ‖ℓ‖ * M := mul_le_mul (by rfl) (hM σ hσ.1) (norm_nonneg σ) (opNorm_nonneg ℓ)

/--
theorem `opNorm_le_of_shell` / 定理 `opNorm_le_of_shell`

English:
theorem opNorm_le_of_shell
  statement: {f : E ->SL[σ₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜}
  proof: f.opNorm_le_bound' hC fun _ hx => SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf hx

中文:
定理 opNorm_le_of_shell
  结论: {f : E ->SL[σ₁₂] F} {ε C : 实数} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜}
  证明: f.opNorm_le_bound' hC fun _ hx => SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf hx

Depends on / 依赖: SemilinearMapClass, SemilinearMapClass.bound_of_shell_semi_normed, bound_of_shell_semi_normed, f.opNorm_le_bound, opNorm_le_bound
-/
theorem opNorm_le_of_shell {f : E ->SL[σ₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : forall x, ε / ‖c‖ <= ‖x‖ -> ‖x‖ < ε -> ‖f x‖ <= C * ‖x‖) : ‖f‖ <= C :=
  f.opNorm_le_bound' hC fun _ hx => SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf hx

/--
theorem `opNorm_le_of_ball` / 定理 `opNorm_le_of_ball`

English:
theorem opNorm_le_of_ball
  statement: {f : E ->SL[σ₁₂] F} {ε : Real} {C : Real} (ε_pos : 0 < ε) (hC : 0 <= C)
  proof: by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine opNorm_le_of_shell ε_pos hC hc fun x _ hx => hf x ?_
  rwa [ball_zero_eq]

中文:
定理 opNorm_le_of_ball
  结论: {f : E ->SL[σ₁₂] F} {ε : 实数} {C : 实数} (ε_pos : 0 < ε) (hC : 0 <= C)
  证明: by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine opNorm_le_of_shell ε_pos hC hc fun x _ hx => hf x ?_
  rwa [ball_zero_eq]

Depends on / 依赖: NormedField, NormedField.exists_one_lt_norm, ball_zero_eq, exists_one_lt_norm, opNorm_le_of_shell
-/
theorem opNorm_le_of_ball {f : E ->SL[σ₁₂] F} {ε : Real} {C : Real} (ε_pos : 0 < ε) (hC : 0 <= C)
    (hf : forall x in ball (0 : E) ε, ‖f x‖ <= C * ‖x‖) : ‖f‖ <= C := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine opNorm_le_of_shell ε_pos hC hc fun x _ hx => hf x ?_
  rwa [ball_zero_eq]

/--
theorem `opNorm_le_of_nhds_zero` / 定理 `opNorm_le_of_nhds_zero`

English:
theorem opNorm_le_of_nhds_zero
  statement: {f : E ->SL[σ₁₂] F} {C : Real} (hC : 0 <= C)
  proof: let ⟨_, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf
  opNorm_le_of_ball ε0 hC hε

中文:
定理 opNorm_le_of_nhds_zero
  结论: {f : E ->SL[σ₁₂] F} {C : 实数} (hC : 0 <= C)
  证明: let ⟨_, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf
  opNorm_le_of_ball ε0 hC hε

Depends on / 依赖: Metric, Metric.eventually_nhds_iff_ball, eventually_nhds_iff_ball, opNorm_le_of_ball
-/
theorem opNorm_le_of_nhds_zero {f : E ->SL[σ₁₂] F} {C : Real} (hC : 0 <= C)
    (hf : forallᶠ x in 𝓝 (0 : E), ‖f x‖ <= C * ‖x‖) : ‖f‖ <= C :=
  let ⟨_, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf
  opNorm_le_of_ball ε0 hC hε

/--
theorem `opNorm_le_of_shell'` / 定理 `opNorm_le_of_shell'`

English:
theorem opNorm_le_of_shell'
  statement: {f : E ->SL[σ₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜}
  proof: by
  by_cases h0 : c = 0
  · refine opNorm_le_of_ball ε_pos hC fun x hx => hf x ?_ ?_
    · simp [h0]
    · rwa [ball_zero_eq] at hx
  · rw [← inv_inv c, norm_inv, inv_lt_one₀ (norm_pos_iff.2 <| inv_ne_zero h0)] at hc
    refine opNorm_le_of_shell ε_pos hC hc ?_
    rwa [norm_inv, div_eq_mul_inv, inv_inv]

中文:
定理 opNorm_le_of_shell'
  结论: {f : E ->SL[σ₁₂] F} {ε C : 实数} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜}
  证明: by
  by_cases h0 : c = 0
  · refine opNorm_le_of_ball ε_pos hC fun x hx => hf x ?_ ?_
    · simp [h0]
    · rwa [ball_zero_eq] at hx
  · rw [← inv_inv c, norm_inv, inv_lt_one₀ (norm_pos_iff.2 <| inv_ne_zero h0)] at hc
    refine opNorm_le_of_shell ε_pos hC hc ?_
    rwa [norm_inv, div_eq_mul_inv, inv_inv]

Depends on / 依赖: ball_zero_eq, div_eq_mul_inv, inv_inv, inv_ne_zero, norm_inv, norm_pos_iff, opNorm_le_of_ball, opNorm_le_of_shell
-/
theorem opNorm_le_of_shell' {f : E ->SL[σ₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜}
    (hc : ‖c‖ < 1) (hf : forall x, ε * ‖c‖ <= ‖x‖ -> ‖x‖ < ε -> ‖f x‖ <= C * ‖x‖) : ‖f‖ <= C := by
  by_cases h0 : c = 0
  · refine opNorm_le_of_ball ε_pos hC fun x hx => hf x ?_ ?_
    · simp [h0]
    · rwa [ball_zero_eq] at hx
  · rw [← inv_inv c, norm_inv, inv_lt_one₀ (norm_pos_iff.2 <| inv_ne_zero h0)] at hc
    refine opNorm_le_of_shell ε_pos hC hc ?_
    rwa [norm_inv, div_eq_mul_inv, inv_inv]

/--
theorem `opNorm_le_of_unit_norm` / 定理 `opNorm_le_of_unit_norm`

English:
theorem opNorm_le_of_unit_norm
  statement: [NormedAlgebra Real 𝕜] {f : E ->SL[σ₁₂] F} {C : Real}
  proof: by
  refine opNorm_le_bound' f hC fun x hx => ?_
  have H₁ : ‖algebraMap _ 𝕜 ‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, inv_mul_cancel₀ hx]
  have H₂ : ‖x‖⁻¹ * ‖f x‖ <= C := by simpa [norm_smul] using hf _ H₁
  rwa [← div_eq_inv_mul, div_le_iff₀] at H₂
  exact (norm_nonneg x).lt_of_ne' hx

中文:
定理 opNorm_le_of_unit_norm
  结论: [赋范代数 实数 𝕜] {f : E ->SL[σ₁₂] F} {C : 实数}
  证明: by
  refine opNorm_le_bound' f hC fun x hx => ?_
  have H₁ : ‖algebraMap _ 𝕜 ‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, inv_mul_cancel₀ hx]
  have H₂ : ‖x‖⁻¹ * ‖f x‖ <= C := by simpa [norm_smul] using hf _ H₁
  rwa [← div_eq_inv_mul, div_le_iff₀] at H₂
  exact (norm_nonneg x).lt_of_ne' hx

Depends on / 依赖: algebraMap, div_eq_inv_mul, lt_of_ne, norm_nonneg, norm_smul, opNorm_le_bound
-/
theorem opNorm_le_of_unit_norm [NormedAlgebra Real 𝕜] {f : E ->SL[σ₁₂] F} {C : Real}
    (hC : 0 <= C) (hf : forall x, ‖x‖ = 1 -> ‖f x‖ <= C) : ‖f‖ <= C := by
  refine opNorm_le_bound' f hC fun x hx => ?_
  have H₁ : ‖algebraMap _ 𝕜 ‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, inv_mul_cancel₀ hx]
  have H₂ : ‖x‖⁻¹ * ‖f x‖ <= C := by simpa [norm_smul] using hf _ H₁
  rwa [← div_eq_inv_mul, div_le_iff₀] at H₂
  exact (norm_nonneg x).lt_of_ne' hx

/--
theorem `opNorm_add_le` / 定理 `opNorm_add_le`

English:
theorem opNorm_add_le
  statement: ‖f + g‖ <= ‖f‖ + ‖g‖
  proof: (f + g).opNorm_le_bound (add_nonneg f.opNorm_nonneg g.opNorm_nonneg) fun x =>
    (norm_add_le_of_le (f.le_opNorm x) (g.le_opNorm x)).trans_eq (add_mul _ _ _).symm

中文:
定理 opNorm_add_le
  结论: ‖f + g‖ <= ‖f‖ + ‖g‖
  证明: (f + g).opNorm_le_bound (add_nonneg f.opNorm_nonneg g.opNorm_nonneg) fun x =>
    (norm_add_le_of_le (f.le_opNorm x) (g.le_opNorm x)).trans_eq (add_mul _ _ _).symm

Depends on / 依赖: add_mul, add_nonneg, f.le_opNorm, f.opNorm_nonneg, g.le_opNorm, g.opNorm_nonneg, le_opNorm, norm_add_le_of_le, opNorm_le_bound, opNorm_nonneg, trans_eq
-/
theorem opNorm_add_le : ‖f + g‖ <= ‖f‖ + ‖g‖ :=
  (f + g).opNorm_le_bound (add_nonneg f.opNorm_nonneg g.opNorm_nonneg) fun x =>
    (norm_add_le_of_le (f.le_opNorm x) (g.le_opNorm x)).trans_eq (add_mul _ _ _).symm

/-- If a normed space is (topologically) non-trivial, then the norm of the identity equals `1`. -/
@[simp]
/--
theorem `norm_id` / 定理 `norm_id`

English:
theorem norm_id
  given: [NontrivialTopology E]
  statement: ‖ContinuousLinearMap.id 𝕜 E‖ = 1
  proof: le_antisymm norm_id_le by
    let ⟨x, hx⟩ := exists_norm_ne_zero E
    have := (ContinuousLinearMap.id 𝕜 E).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this

中文:
定理 norm_id
  条件: [非平凡拓扑 E]
  结论: ‖连续线性映射.id 𝕜 E‖ = 1
  证明: le_antisymm norm_id_le by
    let ⟨x, hx⟩ := exists_norm_ne_zero E
    have := (ContinuousLinearMap.id 𝕜 E).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, div_self, exists_norm_ne_zero, id_apply, le_antisymm, norm_id_le, ratio_le_opNorm
-/
theorem norm_id [NontrivialTopology E] : ‖ContinuousLinearMap.id 𝕜 E‖ = 1 :=
le_antisymm norm_id_le by
    let ⟨x, hx⟩ := exists_norm_ne_zero E
    have := (ContinuousLinearMap.id 𝕜 E).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this

/--
Instance `normOneClass` / 实例 `normOneClass`

English:
instance normOneClass
  signature: [NontrivialTopology E]
  body: ⟨norm_id⟩

中文:
实例 normOneClass
  签名: [非平凡拓扑 E]
  定义体: ⟨norm_id⟩

Depends on / 依赖: norm_id
-/
instance normOneClass [NontrivialTopology E] : NormOneClass (E ->L[𝕜] E) :=
  ⟨norm_id⟩

/--
theorem `opNorm_smul_le` / 定理 `opNorm_smul_le`

English:
theorem opNorm_smul_le
  statement: {𝕜' : Type*} [DistribSMul 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
  proof: (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun _ => by
    grw [smul_apply, norm_smul_le, mul_assoc, le_opNorm]

中文:
定理 opNorm_smul_le
  结论: {𝕜' : 类型} [分配标量乘法 𝕜' F] [标量交换类 𝕜₂ 𝕜' F]
  证明: (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun _ => by
    grw [smul_apply, norm_smul_le, mul_assoc, le_opNorm]

Depends on / 依赖: le_opNorm, mul_assoc, mul_nonneg, norm_nonneg, norm_smul_le, opNorm_le_bound, opNorm_nonneg, smul_apply
-/
theorem opNorm_smul_le {𝕜' : Type*} [DistribSMul 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
    [SeminormedAddCommGroup 𝕜'] [IsBoundedSMul 𝕜' F]
    (c : 𝕜') (f : E ->SL[σ₁₂] F) : ‖c • f‖ <= ‖c‖ * ‖f‖ :=
  (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun _ => by
    grw [smul_apply, norm_smul_le, mul_assoc, le_opNorm]

/--
theorem `opNorm_le_iff_lipschitz` / 定理 `opNorm_le_iff_lipschitz`

English:
theorem opNorm_le_iff_lipschitz
  given: {f : E ->SL[σ₁₂] F} {K : Real>=0}
  proof: ⟨fun h => by simpa using AddMonoidHomClass.lipschitz_of_bound f K le_of_opNorm_le f h,
fun hf => f.opNorm_le_bound K.2 hf.norm_le_mul (map_zero f)⟩

alias ⟨lipschitzWith_of_opNorm_le, opNorm_le_of_lipschitz⟩ := opNorm_le_iff_lipschitz

中文:
定理 opNorm_le_iff_lipschitz
  条件: {f : E ->SL[σ₁₂] F} {K : 实数>=0}
  证明: ⟨fun h => by simpa using AddMonoidHomClass.lipschitz_of_bound f K le_of_opNorm_le f h,
fun hf => f.opNorm_le_bound K.2 hf.norm_le_mul (map_zero f)⟩

alias ⟨lipschitzWith_of_opNorm_le, opNorm_le_of_lipschitz⟩ := opNorm_le_iff_lipschitz

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.lipschitz_of_bound, f.opNorm_le_bound, hf.norm_le_mul, le_of_opNorm_le, lipschitz_of_bound, map_zero, norm_le_mul, opNorm_le_bound
-/
theorem opNorm_le_iff_lipschitz {f : E ->SL[σ₁₂] F} {K : Real>=0} :
    ‖f‖ <= K ↔ LipschitzWith K f :=
⟨fun h => by simpa using AddMonoidHomClass.lipschitz_of_bound f K le_of_opNorm_le f h,
fun hf => f.opNorm_le_bound K.2 hf.norm_le_mul (map_zero f)⟩

alias ⟨lipschitzWith_of_opNorm_le, opNorm_le_of_lipschitz⟩ := opNorm_le_iff_lipschitz

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def seminorm
  body: .ofSMulLE norm opNorm_zero opNorm_add_le opNorm_smul_le

中文:
定义 noncomputable
  签名: def seminorm
  定义体: .ofSMulLE norm opNorm_zero opNorm_add_le opNorm_smul_le
-/
protected noncomputable def seminorm : Seminorm 𝕜₂ (E ->SL[σ₁₂] F) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le opNorm_smul_le

set_option backward.privateInPublic true in
/--
lemma `uniformity_eq_seminorm` / 引理 `uniformity_eq_seminorm`

English:
lemma uniformity_eq_seminorm
  proof: by
  have A (f : (E ->SL[σ₁₂] F) × (E ->SL[σ₁₂] F)) : ‖-f.1 + f.2‖ = ‖f.1 - f.2‖ := by
    rw [← opNorm_neg]; rw [neg_add]; rw [neg_neg]; rw [sub_eq_add_neg]
  simp only [A]
.uniformity_eq_of_hasBasis refine ContinuousLinearMap.seminorm (σ₁₂ := σ₁₂) (E := E) (F := F)
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ => ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    refine ⟨‖c‖, ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.2
      ⟨(closedBall 0 1, closedBall 0 1), ?_⟩⟩
    suffices forall f : E ->SL[σ₁₂] F, (forall x, ‖x‖ <= 1 -> ‖f x‖ <= 1) -> ‖f‖ <= ‖c‖ by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, subset_def] using! this
    intro f hf
    refine opNorm_le_of_shell (f := f) one_pos (norm_nonneg c) hc fun x hcx hx => ?_
    exact (hf x hx.le).trans ((div_le_iff₀' <| one_pos.trans hc).1 hcx)
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr ε with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx => ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    rw [mul_comm] at hδ
    exact le_trans (le_of_opNorm_le_of_le _ hf.le (hε _ hx)) hδ.le

中文:
引理 uniformity_eq_seminorm
  证明: by
  have A (f : (E ->SL[σ₁₂] F) × (E ->SL[σ₁₂] F)) : ‖-f.1 + f.2‖ = ‖f.1 - f.2‖ := by
    rw [← opNorm_neg]; rw [neg_add]; rw [neg_neg]; rw [sub_eq_add_neg]
  simp only [A]
.uniformity_eq_of_hasBasis refine ContinuousLinearMap.seminorm (σ₁₂ := σ₁₂) (E := E) (F := F)
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ => ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    refine ⟨‖c‖, ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.2
      ⟨(closedBall 0 1, closedBall 0 1), ?_⟩⟩
    suffices forall f : E ->SL[σ₁₂] F, (forall x, ‖x‖ <= 1 -> ‖f x‖ <= 1) -> ‖f‖ <= ‖c‖ by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, subset_def] using! this
    intro f hf
    refine opNorm_le_of_shell (f := f) one_pos (norm_nonneg c) hc fun x hcx hx => ?_
    exact (hf x hx.le).trans ((div_le_iff₀' <| one_pos.trans hc).1 hcx)
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr ε with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx => ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    rw [mul_comm] at hδ
    exact le_trans (le_of_opNorm_le_of_le _ hf.le (hε _ hx)) hδ.le
-/
private lemma uniformity_eq_seminorm :
    𝓤 (E ->SL[σ₁₂] F) = ⨅ r > 0, 𝓟 {f | ‖-f.1 + f.2‖ < r} := by
  have A (f : (E ->SL[σ₁₂] F) × (E ->SL[σ₁₂] F)) : ‖-f.1 + f.2‖ = ‖f.1 - f.2‖ := by
    rw [← opNorm_neg]; rw [neg_add]; rw [neg_neg]; rw [sub_eq_add_neg]
  simp only [A]
.uniformity_eq_of_hasBasis refine ContinuousLinearMap.seminorm (σ₁₂ := σ₁₂) (E := E) (F := F)
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ => ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    refine ⟨‖c‖, ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.2
      ⟨(closedBall 0 1, closedBall 0 1), ?_⟩⟩
    suffices forall f : E ->SL[σ₁₂] F, (forall x, ‖x‖ <= 1 -> ‖f x‖ <= 1) -> ‖f‖ <= ‖c‖ by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, subset_def] using! this
    intro f hf
    refine opNorm_le_of_shell (f := f) one_pos (norm_nonneg c) hc fun x hcx hx => ?_
    exact (hf x hx.le).trans ((div_le_iff₀' <| one_pos.trans hc).1 hcx)
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr ε with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx => ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    rw [mul_comm] at hδ
    exact le_trans (le_of_opNorm_le_of_le _ hf.le (hε _ hx)) hδ.le

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `toPseudoMetricSpace` / 实例 `toPseudoMetricSpace`

English:
instance toPseudoMetricSpace
  signature: : PseudoMetricSpace (E ->SL[σ₁₂] F)
  body: .replaceUniformity
  ContinuousLinearMap.seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace uniformity_eq_seminorm

中文:
实例 toPseudoMetricSpace
  签名: : 伪度量空间 (E ->SL[σ₁₂] F)
  定义体: .replaceUniformity
  ContinuousLinearMap.seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace uniformity_eq_seminorm

Depends on / 依赖: replaceUniformity
-/
instance toPseudoMetricSpace : PseudoMetricSpace (E ->SL[σ₁₂] F) := .replaceUniformity
  ContinuousLinearMap.seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace uniformity_eq_seminorm

/--
Instance `toSeminormedAddCommGroup` / 实例 `toSeminormedAddCommGroup`

English:
instance toSeminormedAddCommGroup
  signature: : SeminormedAddCommGroup (E ->SL[σ₁₂] F) where

中文:
实例 toSeminormedAddCommGroup
  签名: : SeminormedAddComm群 (E ->SL[σ₁₂] F) where
-/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (E ->SL[σ₁₂] F) where

/-- If a normed space is (topologically) non-trivial, then the norm of the identity equals `1`. -/
@[simp]
/--
theorem `nnnorm_id` / 定理 `nnnorm_id`

English:
theorem nnnorm_id
  given: [NontrivialTopology E]
  statement: ‖ContinuousLinearMap.id 𝕜 E‖₊ = 1
  proof: NNReal.eq norm_id

中文:
定理 nnnorm_id
  条件: [非平凡拓扑 E]
  结论: ‖连续线性映射.id 𝕜 E‖₊ = 1
  证明: NNReal.eq norm_id

Depends on / 依赖: NNReal, NNReal.eq, norm_id
-/
theorem nnnorm_id [NontrivialTopology E] : ‖ContinuousLinearMap.id 𝕜 E‖₊ = 1 :=
  NNReal.eq norm_id

/--
Instance `toNormedSpace` / 实例 `toNormedSpace`

English:
instance toNormedSpace
  signature: {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
  body: ⟨opNorm_smul_le⟩

中文:
实例 toNormedSpace
  签名: {𝕜' : 类型} [赋范域 𝕜'] [赋范空间 𝕜' F] [标量交换类 𝕜₂ 𝕜' F]
  定义体: ⟨opNorm_smul_le⟩

Depends on / 依赖: opNorm_smul_le
-/
instance toNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] :
    NormedSpace 𝕜' (E ->SL[σ₁₂] F) :=
  ⟨opNorm_smul_le⟩

/--
theorem `opNorm_comp_le` / 定理 `opNorm_comp_le`

English:
theorem opNorm_comp_le
  given: (f : E ->SL[σ₁₂] F)
  statement: ‖h.comp f‖ <= ‖h‖ * ‖f‖
  proof: csInf_le bounds_bddBelow ⟨by positivity, fun x => by
    rw [mul_assoc]
    exact h.le_opNorm_of_le (f.le_opNorm x)⟩

中文:
定理 opNorm_comp_le
  条件: (f : E ->SL[σ₁₂] F)
  结论: ‖h.comp f‖ <= ‖h‖ * ‖f‖
  证明: csInf_le bounds_bddBelow ⟨by positivity, fun x => by
    rw [mul_assoc]
    exact h.le_opNorm_of_le (f.le_opNorm x)⟩

Depends on / 依赖: bounds_bddBelow, csInf_le, f.le_opNorm, h.le_opNorm_of_le, le_opNorm, le_opNorm_of_le, mul_assoc
-/
theorem opNorm_comp_le (f : E ->SL[σ₁₂] F) : ‖h.comp f‖ <= ‖h‖ * ‖f‖ :=
  csInf_le bounds_bddBelow ⟨by positivity, fun x => by
    rw [mul_assoc]
    exact h.le_opNorm_of_le (f.le_opNorm x)⟩

/--
Instance `toSeminormedRing` / 实例 `toSeminormedRing`

English:
instance toSeminormedRing
  signature: : SeminormedRing (E ->L[𝕜] E)
  body: { toSeminormedAddCommGroup, ring with norm_mul_le := opNorm_comp_le }

中文:
实例 toSeminormedRing
  签名: : Seminormed环 (E ->L[𝕜] E)
  定义体: { toSeminormedAddCommGroup, ring with norm_mul_le := opNorm_comp_le }

Depends on / 依赖: norm_mul_le, opNorm_comp_le, toSeminormedAddCommGroup
-/
instance toSeminormedRing : SeminormedRing (E ->L[𝕜] E) :=
  { toSeminormedAddCommGroup, ring with norm_mul_le := opNorm_comp_le }

/--
Instance `toNormedAlgebra` / 实例 `toNormedAlgebra`

English:
instance toNormedAlgebra
  signature: : NormedAlgebra 𝕜 (E ->L[𝕜] E)
  body: { toNormedSpace, algebra with }

中文:
实例 toNormedAlgebra
  签名: : 赋范代数 𝕜 (E ->L[𝕜] E)
  定义体: { toNormedSpace, algebra with }

Depends on / 依赖: algebra, toNormedSpace
-/
instance toNormedAlgebra : NormedAlgebra 𝕜 (E ->L[𝕜] E) := { toNormedSpace, algebra with }

end

variable [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂] F)

@[simp, nontriviality]
/--
theorem `opNorm_subsingleton` / 定理 `opNorm_subsingleton`

English:
theorem opNorm_subsingleton
  given: [Subsingleton E]
  statement: ‖f‖ = 0
  proof: norm_of_subsingleton f

中文:
定理 opNorm_subsingleton
  条件: [子单例 E]
  结论: ‖f‖ = 0
  证明: norm_of_subsingleton f

Depends on / 依赖: norm_of_subsingleton
-/
theorem opNorm_subsingleton [Subsingleton E] : ‖f‖ = 0 := norm_of_subsingleton f

variable {f} in
/--
theorem `homothety_norm` / 定理 `homothety_norm`

English:
theorem homothety_norm
  statement: [NontrivialTopology E] (f : E ->SL[σ₁₂] F) {a : Real}
  proof: by
  obtain ⟨x, hx⟩ := exists_norm_ne_zero E
  replace hx : 0 < ‖x‖ := lt_of_le_of_ne' (norm_nonneg _) hx
  have ha : 0 <= a := by simpa only [hf, hx, mul_nonneg_iff_of_pos_right] using norm_nonneg (f x)
  apply le_antisymm (f.opNorm_le_bound ha fun y => le_of_eq (hf y))
  simpa only [hf, hx, mul_le_mul_iff_left₀] using f.le_opNorm x

中文:
定理 homothety_norm
  结论: [非平凡拓扑 E] (f : E ->SL[σ₁₂] F) {a : 实数}
  证明: by
  obtain ⟨x, hx⟩ := exists_norm_ne_zero E
  replace hx : 0 < ‖x‖ := lt_of_le_of_ne' (norm_nonneg _) hx
  have ha : 0 <= a := by simpa only [hf, hx, mul_nonneg_iff_of_pos_right] using norm_nonneg (f x)
  apply le_antisymm (f.opNorm_le_bound ha fun y => le_of_eq (hf y))
  simpa only [hf, hx, mul_le_mul_iff_left₀] using f.le_opNorm x

Depends on / 依赖: exists_norm_ne_zero, f.le_opNorm, f.opNorm_le_bound, le_antisymm, le_of_eq, le_opNorm, lt_of_le_of_ne, mul_nonneg_iff_of_pos_right, norm_nonneg, opNorm_le_bound, replace
-/
theorem homothety_norm [NontrivialTopology E] (f : E ->SL[σ₁₂] F) {a : Real}
    (hf : forall x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a := by
  obtain ⟨x, hx⟩ := exists_norm_ne_zero E
  replace hx : 0 < ‖x‖ := lt_of_le_of_ne' (norm_nonneg _) hx
  have ha : 0 <= a := by simpa only [hf, hx, mul_nonneg_iff_of_pos_right] using norm_nonneg (f x)
  apply le_antisymm (f.opNorm_le_bound ha fun y => le_of_eq (hf y))
  simpa only [hf, hx, mul_le_mul_iff_left₀] using f.le_opNorm x

end OpNorm

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]
variable [NormedSpace 𝕜' Fₗ] [IsScalarTower 𝕜' 𝕜 Fₗ]

@[simp]
/--
theorem `norm_restrictScalars` / 定理 `norm_restrictScalars`

English:
theorem norm_restrictScalars
  given: (f : E ->L[𝕜] Fₗ)
  statement: ‖f.restrictScalars 𝕜'‖ = ‖f‖
  proof: le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)
    (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)

中文:
定理 norm_restrictScalars
  条件: (f : E ->L[𝕜] Fₗ)
  结论: ‖f.restrictScalars 𝕜'‖ = ‖f‖
  证明: le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)
    (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)

Depends on / 依赖: f.le_opNorm, le_antisymm, le_opNorm, norm_nonneg, opNorm_le_bound
-/
theorem norm_restrictScalars (f : E ->L[𝕜] Fₗ) : ‖f.restrictScalars 𝕜'‖ = ‖f‖ :=
  le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)
    (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)

variable (𝕜 E Fₗ 𝕜') (𝕜'' : Type*) [Ring 𝕜'']
variable [Module 𝕜'' Fₗ] [ContinuousConstSMul 𝕜'' Fₗ]
  [SMulCommClass 𝕜 𝕜'' Fₗ] [SMulCommClass 𝕜' 𝕜'' Fₗ]

/--
Definition of `restrictScalarsIsometry` / `restrictScalarsIsometry` 的定义

English:
definition restrictScalarsIsometry
  signature: : (E ->L[𝕜] Fₗ) ->ₗᵢ[𝕜''] E ->L[𝕜'] Fₗ
  body: ⟨restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'', norm_restrictScalars⟩

中文:
定义 restrictScalarsIsometry
  签名: : (E ->L[𝕜] Fₗ) ->ₗᵢ[𝕜''] E ->L[𝕜'] Fₗ
  定义体: ⟨restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'', norm_restrictScalars⟩

Depends on / 依赖: norm_restrictScalars
-/
def restrictScalarsIsometry : (E ->L[𝕜] Fₗ) ->ₗᵢ[𝕜''] E ->L[𝕜'] Fₗ :=
  ⟨restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'', norm_restrictScalars⟩

variable {𝕜''}

@[simp]
/--
theorem `coe_restrictScalarsIsometry` / 定理 `coe_restrictScalarsIsometry`

English:
theorem coe_restrictScalarsIsometry
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalarsIsometry
  证明: rfl

@[simp]
-/
theorem coe_restrictScalarsIsometry :
    ⇑(restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl

@[simp]
/--
theorem `restrictScalarsIsometry_toLinearMap` / 定理 `restrictScalarsIsometry_toLinearMap`

English:
theorem restrictScalarsIsometry_toLinearMap
  proof: rfl

中文:
定理 restrictScalarsIsometry_toLinearMap
  证明: rfl
-/
theorem restrictScalarsIsometry_toLinearMap :
    (restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'').toLinearMap = restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'' :=
  rfl

end RestrictScalars

/--
lemma `norm_pi_le_of_le` / 引理 `norm_pi_le_of_le`

English:
lemma norm_pi_le_of_le
  statement: {ι : Type*} [Fintype ι]
  proof: by
  refine opNorm_le_bound _ hC (fun x => ?_)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
  exact (L i).le_of_opNorm_le (hL i) _

中文:
引理 norm_pi_le_of_le
  结论: {ι : 类型} [有限类型 ι]
  证明: by
  refine opNorm_le_bound _ hC (fun x => ?_)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
  exact (L i).le_of_opNorm_le (hL i) _

Depends on / 依赖: le_of_opNorm_le, opNorm_le_bound, pi_norm_le_iff_of_nonneg
-/
lemma norm_pi_le_of_le {ι : Type*} [Fintype ι]
    {M : ι -> Type*} [forall i, SeminormedAddCommGroup (M i)] [forall i, NormedSpace 𝕜 (M i)] {C : Real}
    {L : (i : ι) -> (E ->L[𝕜] M i)} (hL : forall i, ‖L i‖ <= C) (hC : 0 <= C) :
    ‖pi L‖ <= C := by
  refine opNorm_le_bound _ hC (fun x => ?_)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
  exact (L i).le_of_opNorm_le (hL i) _

/--
lemma `norm_postcomp_le` / 引理 `norm_postcomp_le`

English:
lemma norm_postcomp_le
  statement: [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]
  proof: .opNorm_le_bound (by positivity) opNorm_comp_le L L.postcomp (σ := σ₁₂) E

中文:
引理 norm_postcomp_le
  结论: [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]
  证明: .opNorm_le_bound (by positivity) opNorm_comp_le L L.postcomp (σ := σ₁₂) E
-/
lemma norm_postcomp_le [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]
    (L : F ->SL[σ₂₃] G) : ‖L.postcomp (σ := σ₁₂) E‖ <= ‖L‖ :=
.opNorm_le_bound (by positivity) opNorm_comp_le L L.postcomp (σ := σ₁₂) E

end ContinuousLinearMap

namespace LinearMap

/--
theorem `mkContinuous_norm_le` / 定理 `mkContinuous_norm_le`

English:
theorem mkContinuous_norm_le
  given: (f : E ->ₛₗ[σ₁₂] F) {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖)
  proof: ContinuousLinearMap.opNorm_le_bound _ hC h

中文:
定理 mkContinuous_norm_le
  条件: (f : E ->ₛₗ[σ₁₂] F) {C : 实数} (hC : 0 <= C) (h : 对任意 x, ‖f x‖ <= C * ‖x‖)
  证明: ContinuousLinearMap.opNorm_le_bound _ hC h

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, opNorm_le_bound
-/
theorem mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F) {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) :
    ‖f.mkContinuous C h‖ <= C :=
  ContinuousLinearMap.opNorm_le_bound _ hC h

/--
theorem `mkContinuous_norm_le'` / 定理 `mkContinuous_norm_le'`

English:
theorem mkContinuous_norm_le'
  given: (f : E ->ₛₗ[σ₁₂] F) {C : Real} (h : forall x, ‖f x‖ <= C * ‖x‖)
  proof: ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun x => (h x).trans by
    gcongr; apply le_max_left

中文:
定理 mkContinuous_norm_le'
  条件: (f : E ->ₛₗ[σ₁₂] F) {C : 实数} (h : 对任意 x, ‖f x‖ <= C * ‖x‖)
  证明: ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun x => (h x).trans by
    gcongr; apply le_max_left

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, le_max_left, le_max_right, opNorm_le_bound
-/
theorem mkContinuous_norm_le' (f : E ->ₛₗ[σ₁₂] F) {C : Real} (h : forall x, ‖f x‖ <= C * ‖x‖) :
    ‖f.mkContinuous C h‖ <= max C 0 :=
ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun x => (h x).trans by
    gcongr; apply le_max_left

end LinearMap

namespace LinearIsometry

/--
theorem `norm_toContinuousLinearMap_le` / 定理 `norm_toContinuousLinearMap_le`

English:
theorem norm_toContinuousLinearMap_le
  given: (f : E ->ₛₗᵢ[σ₁₂] F)
  statement: ‖f.toContinuousLinearMap‖ <= 1
  proof: f.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => by simp

中文:
定理 norm_toContinuousLinearMap_le
  条件: (f : E ->ₛₗᵢ[σ₁₂] F)
  结论: ‖f.toContinuousLinearMap‖ <= 1
  证明: f.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => by simp

Depends on / 依赖: f.toContinuousLinearMap.opNorm_le_bound, opNorm_le_bound, toContinuousLinearMap, zero_le_one
-/
theorem norm_toContinuousLinearMap_le (f : E ->ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ <= 1 :=
  f.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => by simp

end LinearIsometry

namespace Submodule

/--
theorem `norm_subtypeL_le` / 定理 `norm_subtypeL_le`

English:
theorem norm_subtypeL_le
  given: (K : Submodule 𝕜 E)
  statement: ‖K.subtypeL‖ <= 1
  proof: K.subtypeₗᵢ.norm_toContinuousLinearMap_le

中文:
定理 norm_subtypeL_le
  条件: (K : 子模 𝕜 E)
  结论: ‖K.subtypeL‖ <= 1
  证明: K.subtypeₗᵢ.norm_toContinuousLinearMap_le

Depends on / 依赖: K.subtype, norm_toContinuousLinearMap_le
-/
theorem norm_subtypeL_le (K : Submodule 𝕜 E) : ‖K.subtypeL‖ <= 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap_le

end Submodule

end SemiNormed
