/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded linear maps

This file defines a class stating that a map between normed vector spaces is (bi)linear and
continuous.
Instead of asking for continuity, the definition takes the equivalent condition (because the space
is normed) that `‖f x‖` is bounded by a multiple of `‖x‖`. Hence the "bounded" in the name refers to
`‖f x‖/‖x‖` rather than `‖f x‖` itself.

## Main definitions

* `IsBoundedLinearMap`: Class stating that a map `f : E → F` is linear and has `‖f x‖` bounded
  by a multiple of `‖x‖`.
* `IsBoundedBilinearMap`: Class stating that a map `f : E × F → G` is bilinear and continuous,
  but through the simpler to provide statement that `‖f (x, y)‖` is bounded by a multiple of
  `‖x‖ * ‖y‖`
* `IsBoundedBilinearMap.linearDeriv`: Derivative of a continuous bilinear map as a linear map.
* `IsBoundedBilinearMap.deriv`: Derivative of a continuous bilinear map as a continuous linear
  map. The proof that it is indeed the derivative is `IsBoundedBilinearMap.hasFDerivAt` in
  `Analysis.Calculus.FDeriv`.

## Main theorems

* `IsBoundedBilinearMap.continuous`: A bounded bilinear map is continuous.
* `ContinuousLinearEquiv.isOpen`: The continuous linear equivalences are an open subset of the
  set of continuous linear maps between a pair of Banach spaces. Placed in this file because its
  proof uses `IsBoundedBilinearMap.continuous`.

## Notes

The main use of this file is `IsBoundedBilinearMap`.
The file `Mathlib/Analysis/NormedSpace/Multilinear/Basic.lean`
already expounds the theory of multilinear maps,
but the `2`-variables case is sufficiently simpler to currently deserve its own treatment.

`IsBoundedLinearMap` is effectively an unbundled version of `ContinuousLinearMap` (defined
in `Topology.Algebra.Module.Basic`, theory over normed spaces developed in
`Analysis.NormedSpace.OperatorNorm`), albeit the name disparity. A bundled
`ContinuousLinearMap` is to be preferred over an `IsBoundedLinearMap` hypothesis. Historical
artifact, really.
-/

@[expose] public section


noncomputable section

open Topology

open Filter (Tendsto)

open Metric ContinuousLinearMap

section Semiring

variable {𝕜 E F G : Type*} [Semiring 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E]
    [SeminormedAddCommGroup F] [Module 𝕜 F]
    [SeminormedAddCommGroup G] [Module 𝕜 G]
    {f g : E -> F}

variable (𝕜 f) in
/-- A function `f` satisfies `IsBoundedLinearMap 𝕜 f` if it is linear and satisfies the
inequality `‖f x‖ ≤ M * ‖x‖` for some positive constant `M`.

(We put only the typeclasses strictly necessary for the definition, although the main case of
interest is when `𝕜` itself is a normed ring and `E, F` are normed modules.) -/
@[wikidata Q2342396]
/--
Definition of `IsBoundedLinearMap` / `IsBoundedLinearMap` 的定义

English:
structure IsBoundedLinearMap
  parameters: : Prop
  extends: IsLinearMap 𝕜 f
  axioms and operations (1):
    - bound : exists M, 0 < M ∧ forall x : E, ‖f x‖ <= M * ‖x‖

中文:
结构 是BoundedLinear映射
  参数: : 命题
  继承: 是线性映射 𝕜 f
  公理与运算 (1 个):
    - bound : 存在 M, 0 < M ∧ 对任意 x : E, ‖f x‖ <= M * ‖x‖
-/
structure IsBoundedLinearMap : Prop
    extends IsLinearMap 𝕜 f where
  bound : exists M, 0 < M ∧ forall x : E, ‖f x‖ <= M * ‖x‖

/--
lemma `isBoundedLinearMap_iff` / 引理 `isBoundedLinearMap_iff`

English:
lemma isBoundedLinearMap_iff
  given: {f : E -> F}
  proof: ⟨fun hf => ⟨hf.toIsLinearMap, hf.bound⟩, fun ⟨hl, hm⟩ => ⟨hl, hm⟩⟩

中文:
引理 isBoundedLinearMap_iff
  条件: {f : E -> F}
  证明: ⟨fun hf => ⟨hf.toIsLinearMap, hf.bound⟩, fun ⟨hl, hm⟩ => ⟨hl, hm⟩⟩

Depends on / 依赖: hf.bound, hf.toIsLinearMap, toIsLinearMap
-/
lemma isBoundedLinearMap_iff {f : E -> F} :
    IsBoundedLinearMap 𝕜 f ↔ IsLinearMap 𝕜 f ∧ exists M, 0 < M ∧ forall x : E, ‖f x‖ <= M * ‖x‖ :=
  ⟨fun hf => ⟨hf.toIsLinearMap, hf.bound⟩, fun ⟨hl, hm⟩ => ⟨hl, hm⟩⟩

/--
theorem `IsLinearMap.with_bound` / 定理 `IsLinearMap.with_bound`

English:
theorem IsLinearMap.with_bound
  statement: {f : E -> F} (hf : IsLinearMap 𝕜 f) (M : Real)
  proof: ⟨hf,
    by_cases
      (fun (this : M <= 0) =>
        ⟨1, zero_lt_one, fun x =>
(h x).trans mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
      fun (this : ¬M <= 0) => ⟨M, lt_of_not_ge this, h⟩⟩

中文:
定理 是线性映射.with_bound
  结论: {f : E -> F} (hf : 是线性映射 𝕜 f) (M : 实数)
  证明: ⟨hf,
    by_cases
      (fun (this : M <= 0) =>
        ⟨1, zero_lt_one, fun x =>
(h x).trans mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
      fun (this : ¬M <= 0) => ⟨M, lt_of_not_ge this, h⟩⟩

Depends on / 依赖: lt_of_not_ge, mul_le_mul_of_nonneg_right, norm_nonneg, this.trans, zero_le_one, zero_lt_one
-/
theorem IsLinearMap.with_bound {f : E -> F} (hf : IsLinearMap 𝕜 f) (M : Real)
    (h : forall x : E, ‖f x‖ <= M * ‖x‖) : IsBoundedLinearMap 𝕜 f :=
  ⟨hf,
    by_cases
      (fun (this : M <= 0) =>
        ⟨1, zero_lt_one, fun x =>
(h x).trans mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
      fun (this : ¬M <= 0) => ⟨M, lt_of_not_ge this, h⟩⟩

namespace IsBoundedLinearMap

/--
Definition of `toLinearMap` / `toLinearMap` 的定义

English:
definition toLinearMap
  signature: (f : E -> F) (h : IsBoundedLinearMap 𝕜 f)
  body: IsLinearMap.mk' _ h.toIsLinearMap

中文:
定义 toLinearMap
  签名: (f : E -> F) (h : 是BoundedLinear映射 𝕜 f)
  定义体: IsLinearMap.mk' _ h.toIsLinearMap

Depends on / 依赖: IsLinearMap, IsLinearMap.mk, h.toIsLinearMap, toIsLinearMap
-/
def toLinearMap (f : E -> F) (h : IsBoundedLinearMap 𝕜 f) : E ->ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.toIsLinearMap

/--
Definition of `toContinuousLinearMap` / `toContinuousLinearMap` 的定义

English:
definition toContinuousLinearMap
  signature: (f : E -> F) (hf : IsBoundedLinearMap 𝕜 f)
  body: { toLinearMap f hf with
    cont :=
      let ⟨C, _, hC⟩ := hf.bound
      AddMonoidHomClass.continuous_of_bound (toLinearMap f hf) C hC }

中文:
定义 toContinuousLinearMap
  签名: (f : E -> F) (hf : 是BoundedLinear映射 𝕜 f)
  定义体: { toLinearMap f hf with
    cont :=
      let ⟨C, _, hC⟩ := hf.bound
      AddMonoidHomClass.continuous_of_bound (toLinearMap f hf) C hC }

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.continuous_of_bound, continuous_of_bound, hf.bound, toLinearMap
-/
def toContinuousLinearMap (f : E -> F) (hf : IsBoundedLinearMap 𝕜 f) : E ->L[𝕜] F :=
  { toLinearMap f hf with
    cont :=
      let ⟨C, _, hC⟩ := hf.bound
      AddMonoidHomClass.continuous_of_bound (toLinearMap f hf) C hC }

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: IsBoundedLinearMap 𝕜 fun _ : E => (0 : F)
  proof: (0 : E ->ₗ[𝕜] F).isLinear.with_bound 0 by simp

中文:
定理 zero
  结论: 是BoundedLinear映射 𝕜 fun _ : E => (0 : F)
  证明: (0 : E ->ₗ[𝕜] F).isLinear.with_bound 0 by simp

Depends on / 依赖: isLinear, isLinear.with_bound, with_bound
-/
theorem zero : IsBoundedLinearMap 𝕜 fun _ : E => (0 : F) :=
(0 : E ->ₗ[𝕜] F).isLinear.with_bound 0 by simp

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: IsBoundedLinearMap 𝕜 fun x : E => x
  proof: LinearMap.id.isLinear.with_bound 1 by simp

中文:
定理 id
  结论: 是BoundedLinear映射 𝕜 fun x : E => x
  证明: LinearMap.id.isLinear.with_bound 1 by simp

Depends on / 依赖: LinearMap, LinearMap.id.isLinear.with_bound, isLinear, with_bound
-/
theorem id : IsBoundedLinearMap 𝕜 fun x : E => x :=
LinearMap.id.isLinear.with_bound 1 by simp

/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  statement: IsBoundedLinearMap 𝕜 fun x : E × F => x.1
  proof: by
  refine (LinearMap.fst 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_left _ _

中文:
定理 fst
  结论: 是BoundedLinear映射 𝕜 fun x : E × F => x.1
  证明: by
  refine (LinearMap.fst 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_left _ _

Depends on / 依赖: LinearMap, LinearMap.fst, isLinear, isLinear.with_bound, le_max_left, one_mul, with_bound
-/
theorem fst : IsBoundedLinearMap 𝕜 fun x : E × F => x.1 := by
  refine (LinearMap.fst 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_left _ _

/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  statement: IsBoundedLinearMap 𝕜 fun x : E × F => x.2
  proof: by
  refine (LinearMap.snd 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_right _ _

中文:
定理 snd
  结论: 是BoundedLinear映射 𝕜 fun x : E × F => x.2
  证明: by
  refine (LinearMap.snd 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_right _ _

Depends on / 依赖: LinearMap, LinearMap.snd, isLinear, isLinear.with_bound, le_max_right, one_mul, with_bound
-/
theorem snd : IsBoundedLinearMap 𝕜 fun x : E × F => x.2 := by
  refine (LinearMap.snd 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_right _ _

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {𝕜' : Type*} (c : 𝕜') [SeminormedRing 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  proof: let ⟨hlf, M, _, hM⟩ := hf
  (c • hlf.mk' f).isLinear.with_bound (‖c‖ * M) fun x =>
    calc
      ‖c • f x‖ <= ‖c‖ * ‖f x‖ := norm_smul_le c (f x)
      _ <= ‖c‖ * (M * ‖x‖) := by grw [hM]
      _ = ‖c‖ * M * ‖x‖ := (mul_assoc _ _ _).symm

中文:
定理 smul
  结论: {𝕜' : 类型} (c : 𝕜') [Seminormed环 𝕜'] [模 𝕜' F] [是BoundedSMul 𝕜' F]
  证明: let ⟨hlf, M, _, hM⟩ := hf
  (c • hlf.mk' f).isLinear.with_bound (‖c‖ * M) fun x =>
    calc
      ‖c • f x‖ <= ‖c‖ * ‖f x‖ := norm_smul_le c (f x)
      _ <= ‖c‖ * (M * ‖x‖) := by grw [hM]
      _ = ‖c‖ * M * ‖x‖ := (mul_assoc _ _ _).symm

Depends on / 依赖: hlf.mk, isLinear, isLinear.with_bound, mul_assoc, norm_smul_le, with_bound
-/
theorem smul {𝕜' : Type*} (c : 𝕜') [SeminormedRing 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
    [SMulCommClass 𝕜 𝕜' F] (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 (c • f) :=
  let ⟨hlf, M, _, hM⟩ := hf
  (c • hlf.mk' f).isLinear.with_bound (‖c‖ * M) fun x =>
    calc
      ‖c • f x‖ <= ‖c‖ * ‖f x‖ := norm_smul_le c (f x)
      _ <= ‖c‖ * (M * ‖x‖) := by grw [hM]
      _ = ‖c‖ * M * ‖x‖ := (mul_assoc _ _ _).symm

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hf : IsBoundedLinearMap 𝕜 f)
  statement: IsBoundedLinearMap 𝕜 fun e => -f e
  proof: ⟨(-hf.1.mk' _).isLinear, by simpa using hf.2⟩

中文:
定理 neg
  条件: (hf : 是BoundedLinear映射 𝕜 f)
  结论: 是BoundedLinear映射 𝕜 fun e => -f e
  证明: ⟨(-hf.1.mk' _).isLinear, by simpa using hf.2⟩

Depends on / 依赖: isLinear
-/
theorem neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 fun e => -f e :=
  ⟨(-hf.1.mk' _).isLinear, by simpa using hf.2⟩

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g)
  proof: let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
  (hlf.mk' _ + hlg.mk' _).isLinear.with_bound (Mf + Mg) fun x =>
    calc
      ‖f x + g x‖ <= Mf * ‖x‖ + Mg * ‖x‖ := norm_add_le_of_le (hMf x) (hMg x)
      _ <= (Mf + Mg) * ‖x‖ := by rw [add_mul]

中文:
定理 add
  条件: (hf : 是BoundedLinear映射 𝕜 f) (hg : 是BoundedLinear映射 𝕜 g)
  证明: let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
  (hlf.mk' _ + hlg.mk' _).isLinear.with_bound (Mf + Mg) fun x =>
    calc
      ‖f x + g x‖ <= Mf * ‖x‖ + Mg * ‖x‖ := norm_add_le_of_le (hMf x) (hMg x)
      _ <= (Mf + Mg) * ‖x‖ := by rw [add_mul]

Depends on / 依赖: add_mul, hlf.mk, hlg.mk, isLinear, isLinear.with_bound, norm_add_le_of_le, with_bound
-/
theorem add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e + g e :=
  let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
  (hlf.mk' _ + hlg.mk' _).isLinear.with_bound (Mf + Mg) fun x =>
    calc
      ‖f x + g x‖ <= Mf * ‖x‖ + Mg * ‖x‖ := norm_add_le_of_le (hMf x) (hMg x)
      _ <= (Mf + Mg) * ‖x‖ := by rw [add_mul]

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g)
  proof: by simpa [sub_eq_add_neg] using add hf (neg hg)

中文:
定理 sub
  条件: (hf : 是BoundedLinear映射 𝕜 f) (hg : 是BoundedLinear映射 𝕜 g)
  证明: by simpa [sub_eq_add_neg] using add hf (neg hg)

Depends on / 依赖: sub_eq_add_neg
-/
theorem sub (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e - g e := by simpa [sub_eq_add_neg] using add hf (neg hg)

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g : F -> G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f)
  proof: let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
.isLinear.with_bound (Mg * Mf) fun x => (hg.1.mk' _).comp (hf.1.mk' _)
    show ‖g (f x)‖ <= _ by grw [hMg, hMf, mul_assoc]

中文:
定理 comp
  条件: {g : F -> G} (hg : 是BoundedLinear映射 𝕜 g) (hf : 是BoundedLinear映射 𝕜 f)
  证明: let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
.isLinear.with_bound (Mg * Mf) fun x => (hg.1.mk' _).comp (hf.1.mk' _)
    show ‖g (f x)‖ <= _ by grw [hMg, hMf, mul_assoc]

Depends on / 依赖: isLinear, isLinear.with_bound, mul_assoc, with_bound
-/
theorem comp {g : F -> G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 (g ∘ f) :=
  let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
.isLinear.with_bound (Mg * Mf) fun x => (hg.1.mk' _).comp (hf.1.mk' _)
    show ‖g (f x)‖ <= _ by grw [hMg, hMf, mul_assoc]

/--
theorem `tendsto` / 定理 `tendsto`

English:
theorem tendsto
  given: (x : E) (hf : IsBoundedLinearMap 𝕜 f)
  statement: Tendsto f (𝓝 x) (𝓝 (f x))
  proof: hf.toContinuousLinearMap.continuous.tendsto x

中文:
定理 tendsto
  条件: (x : E) (hf : 是BoundedLinear映射 𝕜 f)
  结论: 收敛 f (𝓝 x) (𝓝 (f x))
  证明: hf.toContinuousLinearMap.continuous.tendsto x
-/
protected theorem tendsto (x : E) (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  hf.toContinuousLinearMap.continuous.tendsto x

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (hf : IsBoundedLinearMap 𝕜 f)
  statement: Continuous f
  proof: hf.toContinuousLinearMap.continuous

中文:
定理 continuous
  条件: (hf : 是BoundedLinear映射 𝕜 f)
  结论: 连续 f
  证明: hf.toContinuousLinearMap.continuous

Depends on / 依赖: continuous, hf.toContinuousLinearMap.continuous, toContinuousLinearMap
-/
theorem continuous (hf : IsBoundedLinearMap 𝕜 f) : Continuous f :=
  hf.toContinuousLinearMap.continuous

/--
theorem `lim_zero_bounded_linear_map` / 定理 `lim_zero_bounded_linear_map`

English:
theorem lim_zero_bounded_linear_map
  given: (hf : IsBoundedLinearMap 𝕜 f)
  statement: Tendsto f (𝓝 0) (𝓝 0)
  proof: (hf.1.mk' _).map_zero ▸ hf.tendsto 0

中文:
定理 lim_zero_bounded_linear_map
  条件: (hf : 是BoundedLinear映射 𝕜 f)
  结论: 收敛 f (𝓝 0) (𝓝 0)
  证明: (hf.1.mk' _).map_zero ▸ hf.tendsto 0

Depends on / 依赖: hf.tendsto, map_zero, tendsto
-/
theorem lim_zero_bounded_linear_map (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 0) (𝓝 0) :=
  (hf.1.mk' _).map_zero ▸ hf.tendsto 0

section

open Asymptotics Filter

/--
theorem `isBigO_id` / 定理 `isBigO_id`

English:
theorem isBigO_id
  given: (h : IsBoundedLinearMap 𝕜 f) (l : Filter E)
  statement: f =O[l] fun x => x
  proof: let ⟨_, _, hM⟩ := h.bound
  IsBigO.of_bound _ (mem_of_superset univ_mem fun x _ => hM x)

中文:
定理 isBigO_id
  条件: (h : 是BoundedLinear映射 𝕜 f) (l : 滤子 E)
  结论: f =O[l] fun x => x
  证明: let ⟨_, _, hM⟩ := h.bound
  IsBigO.of_bound _ (mem_of_superset univ_mem fun x _ => hM x)

Depends on / 依赖: IsBigO, IsBigO.of_bound, h.bound, mem_of_superset, of_bound, univ_mem
-/
theorem isBigO_id (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) : f =O[l] fun x => x :=
  let ⟨_, _, hM⟩ := h.bound
  IsBigO.of_bound _ (mem_of_superset univ_mem fun x _ => hM x)

/--
theorem `isBigO_comp` / 定理 `isBigO_comp`

English:
theorem isBigO_comp
  statement: {E : Type*} {g : F -> G} (hg : IsBoundedLinearMap 𝕜 g) {f : E -> F}
  proof: (hg.isBigO_id ⊤).comp_tendsto le_top

中文:
定理 isBigO_comp
  结论: {E : 类型} {g : F -> G} (hg : 是BoundedLinear映射 𝕜 g) {f : E -> F}
  证明: (hg.isBigO_id ⊤).comp_tendsto le_top

Depends on / 依赖: comp_tendsto, hg.isBigO_id, isBigO_id, le_top
-/
theorem isBigO_comp {E : Type*} {g : F -> G} (hg : IsBoundedLinearMap 𝕜 g) {f : E -> F}
    (l : Filter E) : (fun x' => g (f x')) =O[l] f :=
  (hg.isBigO_id ⊤).comp_tendsto le_top

/--
theorem `isBigO_sub` / 定理 `isBigO_sub`

English:
theorem isBigO_sub
  given: {f : E -> F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) (x : E)
  proof: isBigO_comp h l

中文:
定理 isBigO_sub
  条件: {f : E -> F} (h : 是BoundedLinear映射 𝕜 f) (l : 滤子 E) (x : E)
  证明: isBigO_comp h l

Depends on / 依赖: isBigO_comp
-/
theorem isBigO_sub {f : E -> F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  isBigO_comp h l

end

end IsBoundedLinearMap

variable (𝕜) in
/--
Definition of `IsBoundedBilinearMap` / `IsBoundedBilinearMap` 的定义

English:
structure IsBoundedBilinearMap
  parameters: (f : E × F -> G)
  axioms and operations (5):
    - add_left : forall (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
    - smul_left : forall (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
    - add_right : forall (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
    - smul_right : forall (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
    - bound : exists C > 0, forall (x : E) (y : F), ‖f (x, y)‖ <= C * ‖x‖ * ‖y‖

中文:
结构 是BoundedBilinear映射
  参数: (f : E × F -> G)
  公理与运算 (5 个):
    - add_left : 对任意 (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
    - smul_left : 对任意 (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
    - add_right : 对任意 (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
    - smul_right : 对任意 (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
    - bound : 存在 C > 0, 对任意 (x : E) (y : F), ‖f (x, y)‖ <= C * ‖x‖ * ‖y‖
-/
structure IsBoundedBilinearMap (f : E × F -> G) : Prop where
  add_left : forall (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
  smul_left : forall (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
  add_right : forall (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
  smul_right : forall (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
  bound : exists C > 0, forall (x : E) (y : F), ‖f (x, y)‖ <= C * ‖x‖ * ‖y‖

namespace IsBoundedBilinearMap

variable {f : E × F -> G}

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: (h : IsBoundedBilinearMap 𝕜 f)
  proof: h.add_right _ _ _
  smul_left c x y := h.smul_right _ _ _
  add_right x y₁ y₂ := h.add_left _ _ _
  smul_right c x y := h.smul_left _ _ _
  bound := by
    obtain ⟨C, hC_pos, hC⟩ := h.bound
    exact ⟨C, hC_pos, fun x y => (hC y x).trans_eq (by ring)⟩

中文:
引理 symm
  条件: (h : 是BoundedBilinear映射 𝕜 f)
  证明: h.add_right _ _ _
  smul_left c x y := h.smul_right _ _ _
  add_right x y₁ y₂ := h.add_left _ _ _
  smul_right c x y := h.smul_left _ _ _
  bound := by
    obtain ⟨C, hC_pos, hC⟩ := h.bound
    exact ⟨C, hC_pos, fun x y => (hC y x).trans_eq (by ring)⟩

Depends on / 依赖: add_right, h.add_right
-/
lemma symm (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedBilinearMap 𝕜 (fun p => f (p.2, p.1)) where
  add_left x₁ x₂ y := h.add_right _ _ _
  smul_left c x y := h.smul_right _ _ _
  add_right x y₁ y₂ := h.add_left _ _ _
  smul_right c x y := h.smul_left _ _ _
  bound := by
    obtain ⟨C, hC_pos, hC⟩ := h.bound
    exact ⟨C, hC_pos, fun x y => (hC y x).trans_eq (by ring)⟩

/--
lemma `isBoundedLinearMap_right` / 引理 `isBoundedLinearMap_right`

English:
lemma isBoundedLinearMap_right
  given: (h : IsBoundedBilinearMap 𝕜 f) (x : E)
  proof: h.add_right x
  map_smul := (h.smul_right · x ·)
  bound := by
    let ⟨C, hC_pos, hC⟩ := h.bound
    -- Using `C * ‖x‖` is tempting but `x` might be 0 and the constant must be positive!
    refine ⟨C * max ‖x‖ 1, by positivity, fun y => (hC x y).trans ?_⟩
    rcases max_cases ‖x‖ 1 with hx | hx
   

中文:
引理 isBoundedLinearMap_right
  条件: (h : 是BoundedBilinear映射 𝕜 f) (x : E)
  证明: h.add_right x
  map_smul := (h.smul_right · x ·)
  bound := by
    let ⟨C, hC_pos, hC⟩ := h.bound
    -- Using `C * ‖x‖` is tempting but `x` might be 0 and the constant must be positive!
    refine ⟨C * max ‖x‖ 1, by positivity, fun y => (hC x y).trans ?_⟩
    rcases max_cases ‖x‖ 1 with hx | hx
   

Depends on / 依赖: add_right, h.add_right
-/
lemma isBoundedLinearMap_right (h : IsBoundedBilinearMap 𝕜 f) (x : E) :
    IsBoundedLinearMap 𝕜 (fun y => f (x, y)) where
  map_add := h.add_right x
  map_smul := (h.smul_right · x ·)
  bound := by
    let ⟨C, hC_pos, hC⟩ := h.bound
    -- Using `C * ‖x‖` is tempting but `x` might be 0 and the constant must be positive!
    refine ⟨C * max ‖x‖ 1, by positivity, fun y => (hC x y).trans ?_⟩
    rcases max_cases ‖x‖ 1 with hx | hx
    · grw [hx.1]
    · grw [hx.1, hx.2.le]

/--
lemma `isBoundedLinearMap_left` / 引理 `isBoundedLinearMap_left`

English:
lemma isBoundedLinearMap_left
  given: (h : IsBoundedBilinearMap 𝕜 f) (y : F)
  proof: h.symm.isBoundedLinearMap_right y

中文:
引理 isBoundedLinearMap_left
  条件: (h : 是BoundedBilinear映射 𝕜 f) (y : F)
  证明: h.symm.isBoundedLinearMap_right y

Depends on / 依赖: h.symm.isBoundedLinearMap_right, isBoundedLinearMap_right
-/
lemma isBoundedLinearMap_left (h : IsBoundedBilinearMap 𝕜 f) (y : F) :
    IsBoundedLinearMap 𝕜 (fun x => f (x, y)) :=
  h.symm.isBoundedLinearMap_right y

/--
theorem `map_sub_left` / 定理 `map_sub_left`

English:
theorem map_sub_left
  given: (h : IsBoundedBilinearMap 𝕜 f) {x y : E} {z : F}
  proof: (h.isBoundedLinearMap_left z).map_sub x y

中文:
定理 map_sub_left
  条件: (h : 是BoundedBilinear映射 𝕜 f) {x y : E} {z : F}
  证明: (h.isBoundedLinearMap_left z).map_sub x y

Depends on / 依赖: h.isBoundedLinearMap_left, isBoundedLinearMap_left, map_sub
-/
theorem map_sub_left (h : IsBoundedBilinearMap 𝕜 f) {x y : E} {z : F} :
    f (x - y, z) = f (x, z) - f (y, z) :=
  (h.isBoundedLinearMap_left z).map_sub x y

/--
theorem `map_sub_right` / 定理 `map_sub_right`

English:
theorem map_sub_right
  given: (h : IsBoundedBilinearMap 𝕜 f) {x : E} {y z : F}
  proof: (h.isBoundedLinearMap_right x).map_sub y z

中文:
定理 map_sub_right
  条件: (h : 是BoundedBilinear映射 𝕜 f) {x : E} {y z : F}
  证明: (h.isBoundedLinearMap_right x).map_sub y z

Depends on / 依赖: h.isBoundedLinearMap_right, isBoundedLinearMap_right, map_sub
-/
theorem map_sub_right (h : IsBoundedBilinearMap 𝕜 f) {x : E} {y z : F} :
    f (x, y - z) = f (x, y) - f (x, z) :=
  (h.isBoundedLinearMap_right x).map_sub y z

/--
theorem `isBigO` / 定理 `isBigO`

English:
theorem isBigO
  given: (h : IsBoundedBilinearMap 𝕜 f)
  proof: let ⟨C, _, hC⟩ := h.bound
Asymptotics.IsBigO.of_bound C
    Filter.Eventually.of_forall fun ⟨x, y⟩ => by simpa [mul_assoc] using hC x y

中文:
定理 isBigO
  条件: (h : 是BoundedBilinear映射 𝕜 f)
  证明: let ⟨C, _, hC⟩ := h.bound
Asymptotics.IsBigO.of_bound C
    Filter.Eventually.of_forall fun ⟨x, y⟩ => by simpa [mul_assoc] using hC x y
-/
protected theorem isBigO (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p.1‖ * ‖p.2‖ :=
  let ⟨C, _, hC⟩ := h.bound
Asymptotics.IsBigO.of_bound C
    Filter.Eventually.of_forall fun ⟨x, y⟩ => by simpa [mul_assoc] using hC x y

/--
theorem `isBigO_comp` / 定理 `isBigO_comp`

English:
theorem isBigO_comp
  statement: {α : Type*} (H : IsBoundedBilinearMap 𝕜 f) {g : α -> E}
  proof: H.isBigO.comp_tendsto le_top

中文:
定理 isBigO_comp
  结论: {α : 类型} (H : 是BoundedBilinear映射 𝕜 f) {g : α -> E}
  证明: H.isBigO.comp_tendsto le_top

Depends on / 依赖: H.isBigO.comp_tendsto, comp_tendsto, isBigO, le_top
-/
theorem isBigO_comp {α : Type*} (H : IsBoundedBilinearMap 𝕜 f) {g : α -> E}
    {h : α -> F} {l : Filter α} : (fun x => f (g x, h x)) =O[l] fun x => ‖g x‖ * ‖h x‖ :=
  H.isBigO.comp_tendsto le_top

/--
theorem `isBigO'` / 定理 `isBigO'`

English:
theorem isBigO'
  given: (h : IsBoundedBilinearMap 𝕜 f)
  proof: h.isBigO.trans
    (@Asymptotics.isBigO_fst_prod' _ E F _ _ _ _).norm_norm.mul
      (@Asymptotics.isBigO_snd_prod' _ E F _ _ _ _).norm_norm

中文:
定理 isBigO'
  条件: (h : 是BoundedBilinear映射 𝕜 f)
  证明: h.isBigO.trans
    (@Asymptotics.isBigO_fst_prod' _ E F _ _ _ _).norm_norm.mul
      (@Asymptotics.isBigO_snd_prod' _ E F _ _ _ _).norm_norm
-/
protected theorem isBigO' (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p‖ * ‖p‖ :=
h.isBigO.trans
    (@Asymptotics.isBigO_fst_prod' _ E F _ _ _ _).norm_norm.mul
      (@Asymptotics.isBigO_snd_prod' _ E F _ _ _ _).norm_norm

open Asymptotics in
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (h : IsBoundedBilinearMap 𝕜 f)
  statement: Continuous f
  proof: by
  refine continuous_iff_continuousAt.2 fun x => tendsto_sub_nhds_zero_iff.1 ?_
  suffices Tendsto (fun y : E × F => f (y.1 - x.1, y.2) + f (x.1, y.2 - x.2)) (𝓝 x) (𝓝 (0 + 0)) by
    simpa only [h.map_sub_left, h.map_sub_right, sub_add_sub_cancel, zero_add] using this
  apply Tendsto.add
  · rw [←

中文:
定理 continuous
  条件: (h : 是BoundedBilinear映射 𝕜 f)
  结论: 连续 f
  证明: by
  refine continuous_iff_continuousAt.2 fun x => tendsto_sub_nhds_zero_iff.1 ?_
  suffices Tendsto (fun y : E × F => f (y.1 - x.1, y.2) + f (x.1, y.2 - x.2)) (𝓝 x) (𝓝 (0 + 0)) by
    simpa only [h.map_sub_left, h.map_sub_right, sub_add_sub_cancel, zero_add] using this
  apply Tendsto.add
  · rw [←

Depends on / 依赖: IsBigO, IsBigO.norm_left, IsLittleO, IsLittleO.norm_left, Tendsto, Tendsto.add, continu, continuous_iff_continuousAt, h.isBigO_comp.trans_isLittleO, h.map_sub_left, h.map_sub_right, isBigO_comp, isLittleO_one_iff, map_sub_left, map_sub_right, mul_isBigO, norm_left, one_mul, sub_add_sub_cancel, tendsto_sub_nhds_zero_iff
-/
theorem continuous (h : IsBoundedBilinearMap 𝕜 f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => tendsto_sub_nhds_zero_iff.1 ?_
  suffices Tendsto (fun y : E × F => f (y.1 - x.1, y.2) + f (x.1, y.2 - x.2)) (𝓝 x) (𝓝 (0 + 0)) by
    simpa only [h.map_sub_left, h.map_sub_right, sub_add_sub_cancel, zero_add] using this
  apply Tendsto.add
  · rw [← isLittleO_one_iff Real, ← one_mul 1]
    refine h.isBigO_comp.trans_isLittleO ?_
    refine (IsLittleO.norm_left ?_).mul_isBigO (IsBigO.norm_left ?_)
    · exact (isLittleO_one_iff _).2 (tendsto_sub_nhds_zero_iff.2 (continuous_fst.tendsto _))
    · exact (continuous_snd.tendsto _).isBigO_one Real
  · rw [← isLittleO_one_iff Real]
    refine h.isBigO_comp.trans_isLittleO ?_
    apply IsLittleO.const_mul_left
    rw [isLittleO_norm_left]; rw [isLittleO_one_iff]; rw [← sub_self x.2]
    exact continuous_snd.continuousAt.sub tendsto_const_nhds

/--
theorem `continuous_left` / 定理 `continuous_left`

English:
theorem continuous_left
  given: (h : IsBoundedBilinearMap 𝕜 f) {e₂ : F}
  proof: h.continuous.comp (by fun_prop)

中文:
定理 continuous_left
  条件: (h : 是BoundedBilinear映射 𝕜 f) {e₂ : F}
  证明: h.continuous.comp (by fun_prop)

Depends on / 依赖: continuous, fun_prop, h.continuous.comp
-/
theorem continuous_left (h : IsBoundedBilinearMap 𝕜 f) {e₂ : F} :
    Continuous fun e₁ => f (e₁, e₂) :=
  h.continuous.comp (by fun_prop)

/--
theorem `continuous_right` / 定理 `continuous_right`

English:
theorem continuous_right
  given: (h : IsBoundedBilinearMap 𝕜 f) {e₁ : E}
  proof: h.continuous.comp (by fun_prop)

中文:
定理 continuous_right
  条件: (h : 是BoundedBilinear映射 𝕜 f) {e₁ : E}
  证明: h.continuous.comp (by fun_prop)

Depends on / 依赖: continuous, fun_prop, h.continuous.comp
-/
theorem continuous_right (h : IsBoundedBilinearMap 𝕜 f) {e₁ : E} :
    Continuous fun e₂ => f (e₁, e₂) :=
  h.continuous.comp (by fun_prop)

end IsBoundedBilinearMap

end Semiring

section CommSemiring

variable {𝕜 A : Type*} [CommSemiring 𝕜] [SeminormedRing A] [Algebra 𝕜 A]

/--
theorem `isBoundedBilinearMap_smul` / 定理 `isBoundedBilinearMap_smul`

English:
theorem isBoundedBilinearMap_smul
  statement: {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E]
  proof: add_smul
  add_right := smul_add
  smul_left := smul_assoc
  smul_right c x := smul_comm x c
  bound := ⟨1, one_pos, fun x y => by grw [one_mul, norm_smul_le]⟩

中文:
定理 isBoundedBilinearMap_smul
  结论: {E : 类型} [SeminormedAddComm群 E] [模 𝕜 E]
  证明: add_smul
  add_right := smul_add
  smul_left := smul_assoc
  smul_right c x := smul_comm x c
  bound := ⟨1, one_pos, fun x y => by grw [one_mul, norm_smul_le]⟩

Depends on / 依赖: add_smul
-/
theorem isBoundedBilinearMap_smul {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E]
    [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] :
    IsBoundedBilinearMap 𝕜 fun p : A × E => p.1 • p.2 where
  add_left := add_smul
  add_right := smul_add
  smul_left := smul_assoc
  smul_right c x := smul_comm x c
  bound := ⟨1, one_pos, fun x y => by grw [one_mul, norm_smul_le]⟩

/--
theorem `isBoundedBilinearMap_mul` / 定理 `isBoundedBilinearMap_mul`

English:
theorem isBoundedBilinearMap_mul
  proof: isBoundedBilinearMap_smul

中文:
定理 isBoundedBilinearMap_mul
  证明: isBoundedBilinearMap_smul

Depends on / 依赖: isBoundedBilinearMap_smul
-/
theorem isBoundedBilinearMap_mul :
    IsBoundedBilinearMap 𝕜 fun p : A × A => p.1 * p.2 :=
  isBoundedBilinearMap_smul

end CommSemiring

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/--
theorem `ContinuousLinearMap.isBoundedLinearMap` / 定理 `ContinuousLinearMap.isBoundedLinearMap`

English:
theorem ContinuousLinearMap.isBoundedLinearMap
  given: (f : E ->L[𝕜] F)
  statement: IsBoundedLinearMap 𝕜 f
  proof: { f.toLinearMap.isLinear with bound := f.bound }

中文:
定理 连续线性映射.isBoundedLinearMap
  条件: (f : E ->L[𝕜] F)
  结论: 是BoundedLinear映射 𝕜 f
  证明: { f.toLinearMap.isLinear with bound := f.bound }

Depends on / 依赖: f.bound, f.toLinearMap.isLinear, isLinear, toLinearMap
-/
theorem ContinuousLinearMap.isBoundedLinearMap (f : E ->L[𝕜] F) : IsBoundedLinearMap 𝕜 f :=
  { f.toLinearMap.isLinear with bound := f.bound }

namespace IsBoundedLinearMap

variable {f g : E -> F}

/--
theorem `isLinearMap_and_continuous_iff_isBoundedLinearMap` / 定理 `isLinearMap_and_continuous_iff_isBoundedLinearMap`

English:
theorem isLinearMap_and_continuous_iff_isBoundedLinearMap
  given: (f : E -> F)
  proof: ⟨h_bdd.toIsLinearMap, h_bdd.continuous⟩

中文:
定理 isLinearMap_and_continuous_iff_isBoundedLinearMap
  条件: (f : E -> F)
  证明: ⟨h_bdd.toIsLinearMap, h_bdd.continuous⟩

Depends on / 依赖: continuous, h_bdd, h_bdd.continuous, h_bdd.toIsLinearMap, toIsLinearMap
-/
theorem isLinearMap_and_continuous_iff_isBoundedLinearMap (f : E -> F) :
    IsLinearMap 𝕜 f ∧ Continuous f ↔ IsBoundedLinearMap 𝕜 f where
  mp | ⟨hlin, hcont⟩ => ContinuousLinearMap.isBoundedLinearMap ⟨hlin.mk' _, hcont⟩
  mpr h_bdd := ⟨h_bdd.toIsLinearMap, h_bdd.continuous⟩

end IsBoundedLinearMap

section

variable {ι : Type*} [Fintype ι]

/--
theorem `isBoundedLinearMap_prod_multilinear` / 定理 `isBoundedLinearMap_prod_multilinear`

English:
theorem isBoundedLinearMap_prod_multilinear
  statement: {E : ι -> Type*} [forall i, SeminormedAddCommGroup (E i)]
  proof: (ContinuousMultilinearMap.prodL 𝕜 E F G).toContinuousLinearEquiv
.toContinuousLinearMap.isBoundedLinearMap

中文:
定理 isBoundedLinearMap_prod_multilinear
  结论: {E : ι -> 类型} [对任意 i, SeminormedAddComm群 (E i)]
  证明: (ContinuousMultilinearMap.prodL 𝕜 E F G).toContinuousLinearEquiv
.toContinuousLinearMap.isBoundedLinearMap

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.prodL, isBoundedLinearMap, toContinuousLinearEquiv, toContinuousLinearMap, toContinuousLinearMap.isBoundedLinearMap
-/
theorem isBoundedLinearMap_prod_multilinear {E : ι -> Type*} [forall i, SeminormedAddCommGroup (E i)]
    [forall i, NormedSpace 𝕜 (E i)] :
    IsBoundedLinearMap 𝕜 fun p : ContinuousMultilinearMap 𝕜 E F × ContinuousMultilinearMap 𝕜 E G =>
      p.1.prod p.2 :=
  (ContinuousMultilinearMap.prodL 𝕜 E F G).toContinuousLinearEquiv
.toContinuousLinearMap.isBoundedLinearMap

/--
theorem `isBoundedLinearMap_continuousMultilinearMap_comp_linear` / 定理 `isBoundedLinearMap_continuousMultilinearMap_comp_linear`

English:
theorem isBoundedLinearMap_continuousMultilinearMap_comp_linear
  given: (g : G ->L[𝕜] E)
  proof: (ContinuousMultilinearMap.compContinuousLinearMapL (ι := ι) (F := F) (fun _ => g))
.isBoundedLinearMap

中文:
定理 isBoundedLinearMap_continuousMultilinearMap_comp_linear
  条件: (g : G ->L[𝕜] E)
  证明: (ContinuousMultilinearMap.compContinuousLinearMapL (ι := ι) (F := F) (fun _ => g))
.isBoundedLinearMap

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapL, compContinuousLinearMapL, isBoundedLinearMap
-/
theorem isBoundedLinearMap_continuousMultilinearMap_comp_linear (g : G ->L[𝕜] E) :
    IsBoundedLinearMap 𝕜 fun f : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F =>
      f.compContinuousLinearMap fun _ => g :=
  (ContinuousMultilinearMap.compContinuousLinearMapL (ι := ι) (F := F) (fun _ => g))
.isBoundedLinearMap

end

section BilinearMap

variable {f : E × F -> G}

/--
theorem `ContinuousLinearMap.isBoundedBilinearMap` / 定理 `ContinuousLinearMap.isBoundedBilinearMap`

English:
theorem ContinuousLinearMap.isBoundedBilinearMap
  given: (f : E ->L[𝕜] F ->L[𝕜] G)
  proof: { add_left := f.map_add₂
    smul_left := f.map_smul₂
    add_right := fun x => (f x).map_add
    smul_right := fun c x => (f x).map_smul c
    bound :=
      ⟨max ‖f‖ 1, zero_lt_one.trans_le (le_max_right _ _), fun x y =>
(f.le_opNorm₂ x y).trans by
          gcongr; apply le_max_left ⟩ }

中文:
定理 连续线性映射.isBoundedBilinearMap
  条件: (f : E ->L[𝕜] F ->L[𝕜] G)
  证明: { add_left := f.map_add₂
    smul_left := f.map_smul₂
    add_right := fun x => (f x).map_add
    smul_right := fun c x => (f x).map_smul c
    bound :=
      ⟨max ‖f‖ 1, zero_lt_one.trans_le (le_max_right _ _), fun x y =>
(f.le_opNorm₂ x y).trans by
          gcongr; apply le_max_left ⟩ }

Depends on / 依赖: add_left, add_right, f.le_opNorm, f.map_add, f.map_smul, le_max_left, le_max_right, map_add, map_smul, smul_left, smul_right, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem ContinuousLinearMap.isBoundedBilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) :
    IsBoundedBilinearMap 𝕜 fun x : E × F => f x.1 x.2 :=
  { add_left := f.map_add₂
    smul_left := f.map_smul₂
    add_right := fun x => (f x).map_add
    smul_right := fun c x => (f x).map_smul c
    bound :=
      ⟨max ‖f‖ 1, zero_lt_one.trans_le (le_max_right _ _), fun x y =>
(f.le_opNorm₂ x y).trans by
          gcongr; apply le_max_left ⟩ }

/--
Definition of `IsBoundedBilinearMap.toContinuousLinearMap` / `IsBoundedBilinearMap.toContinuousLinearMap` 的定义

English:
definition IsBoundedBilinearMap.toContinuousLinearMap
  signature: (hf : IsBoundedBilinearMap 𝕜 f)
  body: LinearMap.mkContinuousOfExistsBound₂
(LinearMap.mk₂ _ f.curry hf.add_left hf.smul_left hf.add_right hf.smul_right)
    hf.bound.imp fun _ => And.right

@[simp]

中文:
定义 是BoundedBilinear映射.toContinuousLinearMap
  签名: (hf : 是BoundedBilinear映射 𝕜 f)
  定义体: LinearMap.mkContinuousOfExistsBound₂
(LinearMap.mk₂ _ f.curry hf.add_left hf.smul_left hf.add_right hf.smul_right)
    hf.bound.imp fun _ => And.right

@[simp]

Depends on / 依赖: And.right, LinearMap, LinearMap.mk, LinearMap.mkContinuousOfExistsBound, add_left, add_right, f.curry, hf.add_left, hf.add_right, hf.bound.imp, hf.smul_left, hf.smul_right, smul_left, smul_right
-/
def IsBoundedBilinearMap.toContinuousLinearMap (hf : IsBoundedBilinearMap 𝕜 f) :
    E ->L[𝕜] F ->L[𝕜] G :=
  LinearMap.mkContinuousOfExistsBound₂
(LinearMap.mk₂ _ f.curry hf.add_left hf.smul_left hf.add_right hf.smul_right)
    hf.bound.imp fun _ => And.right

@[simp]
/--
lemma `IsBoundedBilinearMap.toContinuousLinearMap_apply` / 引理 `IsBoundedBilinearMap.toContinuousLinearMap_apply`

English:
lemma IsBoundedBilinearMap.toContinuousLinearMap_apply
  statement: (hf : IsBoundedBilinearMap 𝕜 f)
  proof: rfl

中文:
引理 是BoundedBilinear映射.toContinuousLinearMap_apply
  结论: (hf : 是BoundedBilinear映射 𝕜 f)
  证明: rfl
-/
lemma IsBoundedBilinearMap.toContinuousLinearMap_apply (hf : IsBoundedBilinearMap 𝕜 f)
    (x : E) (y : F) : hf.toContinuousLinearMap x y = f (x, y) := rfl

/--
theorem `ContinuousLinearMap.continuous₂` / 定理 `ContinuousLinearMap.continuous₂`

English:
theorem ContinuousLinearMap.continuous₂
  given: (f : E ->L[𝕜] F ->L[𝕜] G)
  proof: f.isBoundedBilinearMap.continuous

中文:
定理 连续线性映射.continuous₂
  条件: (f : E ->L[𝕜] F ->L[𝕜] G)
  证明: f.isBoundedBilinearMap.continuous

Depends on / 依赖: continuous, f.isBoundedBilinearMap.continuous, isBoundedBilinearMap
-/
theorem ContinuousLinearMap.continuous₂ (f : E ->L[𝕜] F ->L[𝕜] G) :
    Continuous (Function.uncurry fun x y => f x y) :=
  f.isBoundedBilinearMap.continuous

/--
theorem `isBoundedBilinearMap_comp` / 定理 `isBoundedBilinearMap_comp`

English:
theorem isBoundedBilinearMap_comp
  proof: (compL 𝕜 E F G).isBoundedBilinearMap

中文:
定理 isBoundedBilinearMap_comp
  证明: (compL 𝕜 E F G).isBoundedBilinearMap

Depends on / 依赖: isBoundedBilinearMap
-/
theorem isBoundedBilinearMap_comp :
    IsBoundedBilinearMap 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2 :=
  (compL 𝕜 E F G).isBoundedBilinearMap

/--
theorem `ContinuousLinearMap.isBoundedLinearMap_comp_left` / 定理 `ContinuousLinearMap.isBoundedLinearMap_comp_left`

English:
theorem ContinuousLinearMap.isBoundedLinearMap_comp_left
  given: (g : F ->L[𝕜] G)
  proof: isBoundedBilinearMap_comp.isBoundedLinearMap_right g

中文:
定理 连续线性映射.isBoundedLinearMap_comp_left
  条件: (g : F ->L[𝕜] G)
  证明: isBoundedBilinearMap_comp.isBoundedLinearMap_right g

Depends on / 依赖: isBoundedBilinearMap_comp, isBoundedBilinearMap_comp.isBoundedLinearMap_right, isBoundedLinearMap_right
-/
theorem ContinuousLinearMap.isBoundedLinearMap_comp_left (g : F ->L[𝕜] G) :
    IsBoundedLinearMap 𝕜 fun f : E ->L[𝕜] F => ContinuousLinearMap.comp g f :=
  isBoundedBilinearMap_comp.isBoundedLinearMap_right g

/--
theorem `ContinuousLinearMap.isBoundedLinearMap_comp_right` / 定理 `ContinuousLinearMap.isBoundedLinearMap_comp_right`

English:
theorem ContinuousLinearMap.isBoundedLinearMap_comp_right
  given: (f : E ->L[𝕜] F)
  proof: (isBoundedBilinearMap_comp (G := G)).isBoundedLinearMap_left f

中文:
定理 连续线性映射.isBoundedLinearMap_comp_right
  条件: (f : E ->L[𝕜] F)
  证明: (isBoundedBilinearMap_comp (G := G)).isBoundedLinearMap_left f

Depends on / 依赖: isBoundedBilinearMap_comp, isBoundedLinearMap_left
-/
theorem ContinuousLinearMap.isBoundedLinearMap_comp_right (f : E ->L[𝕜] F) :
    IsBoundedLinearMap 𝕜 fun g : F ->L[𝕜] G => ContinuousLinearMap.comp g f :=
  (isBoundedBilinearMap_comp (G := G)).isBoundedLinearMap_left f

/--
theorem `isBoundedBilinearMap_apply` / 定理 `isBoundedBilinearMap_apply`

English:
theorem isBoundedBilinearMap_apply
  statement: IsBoundedBilinearMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
  proof: (ContinuousLinearMap.flip (apply 𝕜 F : E ->L[𝕜] (E ->L[𝕜] F) ->L[𝕜] F)).isBoundedBilinearMap

中文:
定理 isBoundedBilinearMap_apply
  结论: 是BoundedBilinear映射 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
  证明: (ContinuousLinearMap.flip (apply 𝕜 F : E ->L[𝕜] (E ->L[𝕜] F) ->L[𝕜] F)).isBoundedBilinearMap

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.flip, isBoundedBilinearMap
-/
theorem isBoundedBilinearMap_apply : IsBoundedBilinearMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2 :=
  (ContinuousLinearMap.flip (apply 𝕜 F : E ->L[𝕜] (E ->L[𝕜] F) ->L[𝕜] F)).isBoundedBilinearMap

/--
theorem `isBoundedBilinearMap_smulRight` / 定理 `isBoundedBilinearMap_smulRight`

English:
theorem isBoundedBilinearMap_smulRight
  proof: (smulRightL 𝕜 E F).isBoundedBilinearMap

中文:
定理 isBoundedBilinearMap_smulRight
  证明: (smulRightL 𝕜 E F).isBoundedBilinearMap

Depends on / 依赖: isBoundedBilinearMap, smulRightL
-/
theorem isBoundedBilinearMap_smulRight :
    IsBoundedBilinearMap 𝕜 fun p =>
      (ContinuousLinearMap.smulRight : StrongDual 𝕜 E -> F -> E ->L[𝕜] F) p.1 p.2 :=
  (smulRightL 𝕜 E F).isBoundedBilinearMap

/--
theorem `isBoundedBilinearMap_compMultilinear` / 定理 `isBoundedBilinearMap_compMultilinear`

English:
theorem isBoundedBilinearMap_compMultilinear
  statement: {ι : Type*} {E : ι -> Type*} [Fintype ι]
  proof: (compContinuousMultilinearMapL 𝕜 E F G).isBoundedBilinearMap

中文:
定理 isBoundedBilinearMap_compMultilinear
  结论: {ι : 类型} {E : ι -> 类型} [有限类型 ι]
  证明: (compContinuousMultilinearMapL 𝕜 E F G).isBoundedBilinearMap

Depends on / 依赖: compContinuousMultilinearMapL, isBoundedBilinearMap
-/
theorem isBoundedBilinearMap_compMultilinear {ι : Type*} {E : ι -> Type*} [Fintype ι]
    [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)] :
    IsBoundedBilinearMap 𝕜 fun p : (F ->L[𝕜] G) × ContinuousMultilinearMap 𝕜 E F =>
      p.1.compContinuousMultilinearMap p.2 :=
  (compContinuousMultilinearMapL 𝕜 E F G).isBoundedBilinearMap

/--
Definition of `IsBoundedBilinearMap.linearDeriv` / `IsBoundedBilinearMap.linearDeriv` 的定义

English:
definition IsBoundedBilinearMap.linearDeriv
  signature: (h : IsBoundedBilinearMap 𝕜 f) (p : E × F)
  body: (h.toContinuousLinearMap.deriv₂ p).toLinearMap

中文:
定义 是BoundedBilinear映射.linearDeriv
  签名: (h : 是BoundedBilinear映射 𝕜 f) (p : E × F)
  定义体: (h.toContinuousLinearMap.deriv₂ p).toLinearMap

Depends on / 依赖: h.toContinuousLinearMap.deriv, toContinuousLinearMap, toLinearMap
-/
def IsBoundedBilinearMap.linearDeriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F ->ₗ[𝕜] G :=
  (h.toContinuousLinearMap.deriv₂ p).toLinearMap

/--
Definition of `IsBoundedBilinearMap.deriv` / `IsBoundedBilinearMap.deriv` 的定义

English:
definition IsBoundedBilinearMap.deriv
  signature: (h : IsBoundedBilinearMap 𝕜 f) (p : E × F)
  body: h.toContinuousLinearMap.deriv₂ p

@[simp]

中文:
定义 是BoundedBilinear映射.deriv
  签名: (h : 是BoundedBilinear映射 𝕜 f) (p : E × F)
  定义体: h.toContinuousLinearMap.deriv₂ p

@[simp]

Depends on / 依赖: h.toContinuousLinearMap.deriv, toContinuousLinearMap
-/
def IsBoundedBilinearMap.deriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F ->L[𝕜] G :=
  h.toContinuousLinearMap.deriv₂ p

@[simp]
/--
theorem `IsBoundedBilinearMap.deriv_apply` / 定理 `IsBoundedBilinearMap.deriv_apply`

English:
theorem IsBoundedBilinearMap.deriv_apply
  given: (h : IsBoundedBilinearMap 𝕜 f) (p q : E × F)
  proof: rfl

中文:
定理 是BoundedBilinear映射.deriv_apply
  条件: (h : 是BoundedBilinear映射 𝕜 f) (p q : E × F)
  证明: rfl
-/
theorem IsBoundedBilinearMap.deriv_apply (h : IsBoundedBilinearMap 𝕜 f) (p q : E × F) :
    h.deriv p q = f (p.1, q.2) + f (q.1, p.2) :=
  rfl

variable (𝕜) in
/--
theorem `ContinuousLinearMap.mulLeftRight_isBoundedBilinear` / 定理 `ContinuousLinearMap.mulLeftRight_isBoundedBilinear`

English:
theorem ContinuousLinearMap.mulLeftRight_isBoundedBilinear
  statement: (𝕜' : Type*) [SeminormedRing 𝕜']
  proof: (ContinuousLinearMap.mulLeftRight 𝕜 𝕜').isBoundedBilinearMap

中文:
定理 连续线性映射.mulLeftRight_isBoundedBilinear
  结论: (𝕜' : 类型) [Seminormed环 𝕜']
  证明: (ContinuousLinearMap.mulLeftRight 𝕜 𝕜').isBoundedBilinearMap

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mulLeftRight, isBoundedBilinearMap, mulLeftRight
-/
theorem ContinuousLinearMap.mulLeftRight_isBoundedBilinear (𝕜' : Type*) [SeminormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] :
    IsBoundedBilinearMap 𝕜 fun p : 𝕜' × 𝕜' => ContinuousLinearMap.mulLeftRight 𝕜 𝕜' p.1 p.2 :=
  (ContinuousLinearMap.mulLeftRight 𝕜 𝕜').isBoundedBilinearMap

/--
theorem `IsBoundedBilinearMap.isBoundedLinearMap_deriv` / 定理 `IsBoundedBilinearMap.isBoundedLinearMap_deriv`

English:
theorem IsBoundedBilinearMap.isBoundedLinearMap_deriv
  given: (h : IsBoundedBilinearMap 𝕜 f)
  proof: h.toContinuousLinearMap.deriv₂.isBoundedLinearMap

中文:
定理 是BoundedBilinear映射.isBoundedLinearMap_deriv
  条件: (h : 是BoundedBilinear映射 𝕜 f)
  证明: h.toContinuousLinearMap.deriv₂.isBoundedLinearMap

Depends on / 依赖: h.toContinuousLinearMap.deriv, isBoundedLinearMap, toContinuousLinearMap
-/
theorem IsBoundedBilinearMap.isBoundedLinearMap_deriv (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 fun p : E × F => h.deriv p :=
  h.toContinuousLinearMap.deriv₂.isBoundedLinearMap

end BilinearMap

variable {X : Type*} [TopologicalSpace X]

@[continuity, fun_prop]
/--
theorem `Continuous.clm_comp` / 定理 `Continuous.clm_comp`

English:
theorem Continuous.clm_comp
  statement: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
  proof: (compL 𝕜 E F G).continuous₂.comp₂ hg hf

@[fun_prop]

中文:
定理 连续.clm_comp
  结论: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
  证明: (compL 𝕜 E F G).continuous₂.comp₂ hg hf

@[fun_prop]
-/
theorem Continuous.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
    (hg : Continuous g) (hf : Continuous f) : Continuous fun x => (g x).comp (f x) :=
  (compL 𝕜 E F G).continuous₂.comp₂ hg hf

@[fun_prop]
/--
theorem `ContinuousOn.clm_comp` / 定理 `ContinuousOn.clm_comp`

English:
theorem ContinuousOn.clm_comp
  statement: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
  proof: (compL 𝕜 E F G).continuous₂.comp_continuousOn (hg.prodMk hf)

@[fun_prop]

中文:
定理 ContinuousOn.clm_comp
  结论: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
  证明: (compL 𝕜 E F G).continuous₂.comp_continuousOn (hg.prodMk hf)

@[fun_prop]

Depends on / 依赖: comp_continuousOn, hg.prodMk, prodMk
-/
theorem ContinuousOn.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
    {s : Set X} (hg : ContinuousOn g s) (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (g x).comp (f x)) s :=
  (compL 𝕜 E F G).continuous₂.comp_continuousOn (hg.prodMk hf)

@[fun_prop]
/--
theorem `ContinuousAt.clm_comp` / 定理 `ContinuousAt.clm_comp`

English:
theorem ContinuousAt.clm_comp
  statement: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
  proof: (compL 𝕜 E F G).continuous₂.continuousAt.comp (hg.prodMk hf)

@[fun_prop]

中文:
定理 ContinuousAt.clm_comp
  结论: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
  证明: (compL 𝕜 E F G).continuous₂.continuousAt.comp (hg.prodMk hf)

@[fun_prop]

Depends on / 依赖: continuousAt, continuousAt.comp, hg.prodMk, prodMk
-/
theorem ContinuousAt.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
    {x : X} (hg : ContinuousAt g x) (hf : ContinuousAt f x) :
    ContinuousAt (fun x => (g x).comp (f x)) x :=
  (compL 𝕜 E F G).continuous₂.continuousAt.comp (hg.prodMk hf)

@[fun_prop]
/--
theorem `ContinuousWithinAt.clm_comp` / 定理 `ContinuousWithinAt.clm_comp`

English:
theorem ContinuousWithinAt.clm_comp
  statement: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
  proof: (compL 𝕜 E F G).continuous₂.continuousAt.comp_continuousWithinAt (hg.prodMk hf)

@[continuity, fun_prop]

中文:
定理 ContinuousWithinAt.clm_comp
  结论: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
  证明: (compL 𝕜 E F G).continuous₂.continuousAt.comp_continuousWithinAt (hg.prodMk hf)

@[continuity, fun_prop]

Depends on / 依赖: comp_continuousWithinAt, continuousAt, continuousAt.comp_continuousWithinAt, hg.prodMk, prodMk
-/
theorem ContinuousWithinAt.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F}
    {s : Set X} {x : X} (hg : ContinuousWithinAt g s x) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (g x).comp (f x)) s x :=
  (compL 𝕜 E F G).continuous₂.continuousAt.comp_continuousWithinAt (hg.prodMk hf)

@[continuity, fun_prop]
/--
theorem `Continuous.clm_apply` / 定理 `Continuous.clm_apply`

English:
theorem Continuous.clm_apply
  statement: {f : X -> E ->L[𝕜] F} {g : X -> E}
  proof: isBoundedBilinearMap_apply.continuous.comp₂ hf hg

@[fun_prop]

中文:
定理 连续.clm_apply
  结论: {f : X -> E ->L[𝕜] F} {g : X -> E}
  证明: isBoundedBilinearMap_apply.continuous.comp₂ hf hg

@[fun_prop]

Depends on / 依赖: continuous, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.continuous.comp
-/
theorem Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X -> E}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x)) :=
  isBoundedBilinearMap_apply.continuous.comp₂ hf hg

@[fun_prop]
/--
theorem `ContinuousOn.clm_apply` / 定理 `ContinuousOn.clm_apply`

English:
theorem ContinuousOn.clm_apply
  statement: {f : X -> E ->L[𝕜] F} {g : X -> E}
  proof: (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.comp_continuousOn (hf.prodMk hg)

@[continuity, fun_prop]

中文:
定理 ContinuousOn.clm_apply
  结论: {f : X -> E ->L[𝕜] F} {g : X -> E}
  证明: (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.comp_continuousOn (hf.prodMk hg)

@[continuity, fun_prop]

Depends on / 依赖: comp_continuousOn, continuous, continuous.comp_continuousOn, hf.prodMk, isBoundedBilinearMap_apply, prodMk
-/
theorem ContinuousOn.clm_apply {f : X -> E ->L[𝕜] F} {g : X -> E}
    {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x (g x)) s :=
  (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.comp_continuousOn (hf.prodMk hg)

@[continuity, fun_prop]
/--
theorem `ContinuousAt.clm_apply` / 定理 `ContinuousAt.clm_apply`

English:
theorem ContinuousAt.clm_apply
  statement: {X} [TopologicalSpace X] {f : X -> E ->L[𝕜] F} {g : X -> E} {x : X}
  proof: isBoundedBilinearMap_apply.continuous.continuousAt.comp₂ hf hg

@[continuity, fun_prop]

中文:
定理 ContinuousAt.clm_apply
  结论: {X} [拓扑空间 X] {f : X -> E ->L[𝕜] F} {g : X -> E} {x : X}
  证明: isBoundedBilinearMap_apply.continuous.continuousAt.comp₂ hf hg

@[continuity, fun_prop]

Depends on / 依赖: continuous, continuousAt, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.continuous.continuousAt.comp
-/
theorem ContinuousAt.clm_apply {X} [TopologicalSpace X] {f : X -> E ->L[𝕜] F} {g : X -> E} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => f x (g x)) x :=
  isBoundedBilinearMap_apply.continuous.continuousAt.comp₂ hf hg

@[continuity, fun_prop]
/--
theorem `ContinuousWithinAt.clm_apply` / 定理 `ContinuousWithinAt.clm_apply`

English:
theorem ContinuousWithinAt.clm_apply
  statement: {X} [TopologicalSpace X] {f : X -> E ->L[𝕜] F} {g : X -> E}
  proof: (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.continuousAt.comp_continuousWithinAt
    (hf.prodMk hg)

@[fun_prop]

中文:
定理 ContinuousWithinAt.clm_apply
  结论: {X} [拓扑空间 X] {f : X -> E ->L[𝕜] F} {g : X -> E}
  证明: (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.continuousAt.comp_continuousWithinAt
    (hf.prodMk hg)

@[fun_prop]

Depends on / 依赖: comp_continuousWithinAt, continuous, continuous.continuousAt.comp_continuousWithinAt, continuousAt, hf.prodMk, isBoundedBilinearMap_apply, prodMk
-/
theorem ContinuousWithinAt.clm_apply {X} [TopologicalSpace X] {f : X -> E ->L[𝕜] F} {g : X -> E}
    {s : Set X} {x : X} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => f x (g x)) s x :=
  (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.continuousAt.comp_continuousWithinAt
    (hf.prodMk hg)

@[fun_prop]
/--
theorem `ContinuousWithinAt.continuousLinearMapCoprod` / 定理 `ContinuousWithinAt.continuousLinearMapCoprod`

English:
theorem ContinuousWithinAt.continuousLinearMapCoprod
  proof: by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]

中文:
定理 ContinuousWithinAt.continuousLinearMapCoprod
  证明: by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]

Depends on / 依赖: comp_fst_add_comp_snd, fun_prop
-/
theorem ContinuousWithinAt.continuousLinearMapCoprod
    {f : X -> E ->L[𝕜] G} {g : X -> F ->L[𝕜] G} {s : Set X} {x : X}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => (f x).coprod (g x)) s x := by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]
/--
theorem `ContinuousAt.continuousLinearMapCoprod` / 定理 `ContinuousAt.continuousLinearMapCoprod`

English:
theorem ContinuousAt.continuousLinearMapCoprod
  proof: by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]

中文:
定理 ContinuousAt.continuousLinearMapCoprod
  证明: by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]

Depends on / 依赖: comp_fst_add_comp_snd, fun_prop
-/
theorem ContinuousAt.continuousLinearMapCoprod
    {f : X -> E ->L[𝕜] G} {g : X -> F ->L[𝕜] G} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => (f x).coprod (g x)) x := by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]
/--
theorem `ContinuousOn.continuousLinearMapCoprod` / 定理 `ContinuousOn.continuousLinearMapCoprod`

English:
theorem ContinuousOn.continuousLinearMapCoprod
  proof: by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]

中文:
定理 ContinuousOn.continuousLinearMapCoprod
  证明: by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]

Depends on / 依赖: comp_fst_add_comp_snd, fun_prop
-/
theorem ContinuousOn.continuousLinearMapCoprod
    {f : X -> E ->L[𝕜] G} {g : X -> F ->L[𝕜] G} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).coprod (g x)) s := by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]
/--
theorem `Continuous.continuousLinearMapCoprod` / 定理 `Continuous.continuousLinearMapCoprod`

English:
theorem Continuous.continuousLinearMapCoprod
  proof: by
  apply continuousOn_univ.mp
  fun_prop

中文:
定理 连续.continuousLinearMapCoprod
  证明: by
  apply continuousOn_univ.mp
  fun_prop

Depends on / 依赖: continuousOn_univ, continuousOn_univ.mp, fun_prop
-/
theorem Continuous.continuousLinearMapCoprod
    {f : X -> E ->L[𝕜] G} {g : X -> F ->L[𝕜] G}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (f x).coprod (g x)) := by
  apply continuousOn_univ.mp
  fun_prop

end

namespace ContinuousLinearEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open Set
open scoped Topology


/--
theorem `isOpen` / 定理 `isOpen`

English:
theorem isOpen
  given: [CompleteSpace E]
  statement: IsOpen (range ((↑) : (E ≃L[𝕜] F) -> E ->L[𝕜] F))
  proof: by
  rw [isOpen_iff_mem_nhds]; rw [forall_mem_range]
  refine fun e => IsOpen.mem_nhds ?_ (mem_range_self _)
  let O : (E ->L[𝕜] F) -> E ->L[𝕜] E := fun f => (e.symm : F ->L[𝕜] E).comp f
  have h_O : Continuous O := (isBoundedBilinearMap_comp (𝕜 := 𝕜) (F := F) (G := E)).continuous_right
  convert! s

中文:
定理 isOpen
  条件: [完备空间 E]
  结论: 是开集 (range ((↑) : (E ≃L[𝕜] F) -> E ->L[𝕜] F))
  证明: by
  rw [isOpen_iff_mem_nhds]; rw [forall_mem_range]
  refine fun e => IsOpen.mem_nhds ?_ (mem_range_self _)
  let O : (E ->L[𝕜] F) -> E ->L[𝕜] E := fun f => (e.symm : F ->L[𝕜] E).comp f
  have h_O : Continuous O := (isBoundedBilinearMap_comp (𝕜 := 𝕜) (F := F) (G := E)).continuous_right
  convert! s
-/
protected theorem isOpen [CompleteSpace E] : IsOpen (range ((↑) : (E ≃L[𝕜] F) -> E ->L[𝕜] F)) := by
  rw [isOpen_iff_mem_nhds]; rw [forall_mem_range]
  refine fun e => IsOpen.mem_nhds ?_ (mem_range_self _)
  let O : (E ->L[𝕜] F) -> E ->L[𝕜] E := fun f => (e.symm : F ->L[𝕜] E).comp f
  have h_O : Continuous O := (isBoundedBilinearMap_comp (𝕜 := 𝕜) (F := F) (G := E)).continuous_right
  convert! show IsOpen (O ⁻¹' {x | IsUnit x}) from Units.isOpen.preimage h_O using 1
  ext f'
  constructor
  · rintro ⟨e', rfl⟩
    exact ⟨(e'.trans e.symm).toUnit, rfl⟩
  · rintro ⟨w, hw⟩
    use (unitsEquiv 𝕜 E w).trans e
    ext x
    simp [O, hw]

/--
theorem `nhds` / 定理 `nhds`

English:
theorem nhds
  given: [CompleteSpace E] (e : E ≃L[𝕜] F)
  proof: IsOpen.mem_nhds ContinuousLinearEquiv.isOpen (by simp)

中文:
定理 邻域滤子
  条件: [完备空间 E] (e : E ≃L[𝕜] F)
  证明: IsOpen.mem_nhds ContinuousLinearEquiv.isOpen (by simp)
-/
protected theorem nhds [CompleteSpace E] (e : E ≃L[𝕜] F) :
    range ((↑) : (E ≃L[𝕜] F) -> E ->L[𝕜] F) in 𝓝 (e : E ->L[𝕜] F) :=
  IsOpen.mem_nhds ContinuousLinearEquiv.isOpen (by simp)

end ContinuousLinearEquiv
