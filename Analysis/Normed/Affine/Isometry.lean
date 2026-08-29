/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.AffineSpace.Restrict
public import Mathlib.Topology.Algebra.AffineSubspace
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Affine isometries

In this file we define `AffineIsometry 𝕜 P P₂` to be an affine isometric embedding of normed
add-torsors `P` into `P₂` over normed `𝕜`-spaces and `AffineIsometryEquiv` to be an affine
isometric equivalence between `P` and `P₂`.

We also prove basic lemmas and provide convenience constructors. The choice of these lemmas and
constructors is closely modelled on those for the `LinearIsometry` and `AffineMap` theories.

Since many elementary properties don't require `‖x‖ = 0 → x = 0` we initially set up the theory for
`SeminormedAddCommGroup` and specialize to `NormedAddCommGroup` only when needed.

## Notation

We introduce the notation `P →ᵃⁱ[𝕜] P₂` for `AffineIsometry 𝕜 P P₂`, and `P ≃ᵃⁱ[𝕜] P₂` for
`AffineIsometryEquiv 𝕜 P P₂`. In contrast with the notation `→ₗᵢ` for linear isometries, `≃ᵢ`
for isometric equivalences, etc., the "i" here is a superscript. This is for aesthetic reasons to
match the superscript "a" (note that in mathlib `→ᵃ` is an affine map, since `→ₐ` has been taken by
algebra-homomorphisms.)

-/

@[expose] public section

open Function Set Metric

variable (𝕜 : Type*) {V V₁ V₁' V₂ V₃ V₄ : Type*} {P₁ P₁' : Type*} (P P₂ : Type*) {P₃ P₄ : Type*}
  [NormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [SeminormedAddCommGroup V₁] [NormedSpace 𝕜 V₁] [PseudoMetricSpace P₁] [NormedAddTorsor V₁ P₁]
  [SeminormedAddCommGroup V₁'] [NormedSpace 𝕜 V₁'] [MetricSpace P₁'] [NormedAddTorsor V₁' P₁']
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]
  [SeminormedAddCommGroup V₃] [NormedSpace 𝕜 V₃] [PseudoMetricSpace P₃] [NormedAddTorsor V₃ P₃]
  [SeminormedAddCommGroup V₄] [NormedSpace 𝕜 V₄] [PseudoMetricSpace P₄] [NormedAddTorsor V₄ P₄]

/--
Definition of `AffineIsometry` / `AffineIsometry` 的定义

English:
structure AffineIsometry
  parameters: extends P ->ᵃ[𝕜] P₂
  extends: P ->ᵃ[𝕜] P₂
  axioms and operations (1):
    - norm_map : forall x : V, ‖linear x‖ = ‖x‖

中文:
结构 仿射等距
  参数: extends P ->ᵃ[𝕜] P₂
  继承: P ->ᵃ[𝕜] P₂
  公理与运算 (1 个):
    - norm_map : 对任意 x : V, ‖linear x‖ = ‖x‖
-/
structure AffineIsometry extends P ->ᵃ[𝕜] P₂ where
  norm_map : forall x : V, ‖linear x‖ = ‖x‖

variable {𝕜 P P₂}

@[inherit_doc]
notation:25 -- `→ᵃᵢ` would be more consistent with the linear isometry notation, but it is uglier
P " ->ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometry 𝕜 P P₂

namespace AffineIsometry

variable (f : P ->ᵃⁱ[𝕜] P₂)

/--
Definition of `linearIsometry` / `linearIsometry` 的定义

English:
definition linearIsometry
  signature: : V ->ₗᵢ[𝕜] V₂
  body: { f.linear with norm_map' := f.norm_map }

@[simp]

中文:
定义 linearIsometry
  签名: : V ->ₗᵢ[𝕜] V₂
  定义体: { f.linear with norm_map' := f.norm_map }

@[simp]
-/
protected def linearIsometry : V ->ₗᵢ[𝕜] V₂ :=
  { f.linear with norm_map' := f.norm_map }

@[simp]
/--
theorem `linear_eq_linearIsometry` / 定理 `linear_eq_linearIsometry`

English:
theorem linear_eq_linearIsometry
  statement: f.linear = f.linearIsometry.toLinearMap
  proof: by
  ext
  rfl

中文:
定理 linear_eq_linearIsometry
  结论: f.linear = f.linearIsometry.toLinearMap
  证明: by
  ext
  rfl
-/
theorem linear_eq_linearIsometry : f.linear = f.linearIsometry.toLinearMap := by
  ext
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (P ->ᵃⁱ[𝕜] P₂) P P₂
  body: f.toFun
  coe_injective f g := by cases f; cases g; simp

@[simp]

中文:
实例 :
  签名: 函数状 (P ->ᵃⁱ[𝕜] P₂) P P₂
  定义体: f.toFun
  coe_injective f g := by cases f; cases g; simp

@[simp]

Depends on / 依赖: f.toFun
-/
instance : FunLike (P ->ᵃⁱ[𝕜] P₂) P P₂ where
  coe f := f.toFun
  coe_injective f g := by cases f; cases g; simp

@[simp]
/--
theorem `coe_toAffineMap` / 定理 `coe_toAffineMap`

English:
theorem coe_toAffineMap
  statement: ⇑f.toAffineMap = f
  proof: by
  rfl

中文:
定理 coe_toAffineMap
  结论: ⇑f.toAffineMap = f
  证明: by
  rfl
-/
theorem coe_toAffineMap : ⇑f.toAffineMap = f := by
  rfl

/--
theorem `toAffineMap_injective` / 定理 `toAffineMap_injective`

English:
theorem toAffineMap_injective
  statement: Injective (toAffineMap : (P ->ᵃⁱ[𝕜] P₂) -> P ->ᵃ[𝕜] P₂)
  proof: by
  rintro ⟨f, _⟩ ⟨g, _⟩ rfl
  rfl

中文:
定理 toAffineMap_injective
  结论: 单射 (toAffineMap : (P ->ᵃⁱ[𝕜] P₂) -> P ->ᵃ[𝕜] P₂)
  证明: by
  rintro ⟨f, _⟩ ⟨g, _⟩ rfl
  rfl
-/
theorem toAffineMap_injective : Injective (toAffineMap : (P ->ᵃⁱ[𝕜] P₂) -> P ->ᵃ[𝕜] P₂) := by
  rintro ⟨f, _⟩ ⟨g, _⟩ rfl
  rfl

/--
theorem `coeFn_injective` / 定理 `coeFn_injective`

English:
theorem coeFn_injective
  statement: @Injective (P ->ᵃⁱ[𝕜] P₂) (P -> P₂) (↑)
  proof: AffineMap.coeFn_injective.comp toAffineMap_injective

@[ext]

中文:
定理 coeFn_injective
  结论: @单射 (P ->ᵃⁱ[𝕜] P₂) (P -> P₂) (↑)
  证明: AffineMap.coeFn_injective.comp toAffineMap_injective

@[ext]

Depends on / 依赖: AffineMap, AffineMap.coeFn_injective.comp, coeFn_injective, toAffineMap_injective
-/
theorem coeFn_injective : @Injective (P ->ᵃⁱ[𝕜] P₂) (P -> P₂) (↑) :=
  AffineMap.coeFn_injective.comp toAffineMap_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : P ->ᵃⁱ[𝕜] P₂} (h : forall x, f x = g x)
  statement: f = g
  proof: coeFn_injective funext h

中文:
定理 ext
  条件: {f g : P ->ᵃⁱ[𝕜] P₂} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: coeFn_injective funext h

Depends on / 依赖: coeFn_injective
-/
theorem ext {f g : P ->ᵃⁱ[𝕜] P₂} (h : forall x, f x = g x) : f = g :=
coeFn_injective funext h

end AffineIsometry

namespace LinearIsometry

variable (f : V ->ₗᵢ[𝕜] V₂)

/--
Definition of `toAffineIsometry` / `toAffineIsometry` 的定义

English:
definition toAffineIsometry
  signature: : V ->ᵃⁱ[𝕜] V₂
  body: { f.toLinearMap.toAffineMap with norm_map := f.norm_map }

@[simp]

中文:
定义 toAffineIsometry
  签名: : V ->ᵃⁱ[𝕜] V₂
  定义体: { f.toLinearMap.toAffineMap with norm_map := f.norm_map }

@[simp]

Depends on / 依赖: f.norm_map, f.toLinearMap.toAffineMap, norm_map, toAffineMap, toLinearMap
-/
def toAffineIsometry : V ->ᵃⁱ[𝕜] V₂ :=
  { f.toLinearMap.toAffineMap with norm_map := f.norm_map }

@[simp]
/--
theorem `coe_toAffineIsometry` / 定理 `coe_toAffineIsometry`

English:
theorem coe_toAffineIsometry
  statement: ⇑(f.toAffineIsometry : V ->ᵃⁱ[𝕜] V₂) = f
  proof: rfl

@[simp]

中文:
定理 coe_toAffineIsometry
  结论: ⇑(f.toAffineIsometry : V ->ᵃⁱ[𝕜] V₂) = f
  证明: rfl

@[simp]
-/
theorem coe_toAffineIsometry : ⇑(f.toAffineIsometry : V ->ᵃⁱ[𝕜] V₂) = f :=
  rfl

@[simp]
/--
theorem `toAffineIsometry_linearIsometry` / 定理 `toAffineIsometry_linearIsometry`

English:
theorem toAffineIsometry_linearIsometry
  statement: f.toAffineIsometry.linearIsometry = f
  proof: by
  ext
  rfl

中文:
定理 toAffineIsometry_linearIsometry
  结论: f.toAffineIsometry.linearIsometry = f
  证明: by
  ext
  rfl
-/
theorem toAffineIsometry_linearIsometry : f.toAffineIsometry.linearIsometry = f := by
  ext
  rfl

-- somewhat arbitrary choice of simp direction
@[simp]
/--
theorem `toAffineIsometry_toAffineMap` / 定理 `toAffineIsometry_toAffineMap`

English:
theorem toAffineIsometry_toAffineMap
  statement: f.toAffineIsometry.toAffineMap = f.toLinearMap.toAffineMap
  proof: rfl

中文:
定理 toAffineIsometry_toAffineMap
  结论: f.toAffineIsometry.toAffineMap = f.toLinearMap.toAffineMap
  证明: rfl
-/
theorem toAffineIsometry_toAffineMap : f.toAffineIsometry.toAffineMap = f.toLinearMap.toAffineMap :=
  rfl

end LinearIsometry

namespace AffineIsometry

variable (f : P ->ᵃⁱ[𝕜] P₂) (f₁ : P₁' ->ᵃⁱ[𝕜] P₂)

@[simp]
/--
theorem `map_vadd` / 定理 `map_vadd`

English:
theorem map_vadd
  given: (p : P) (v : V)
  statement: f (v +ᵥ p) = f.linearIsometry v +ᵥ f p
  proof: f.toAffineMap.map_vadd p v

@[simp]

中文:
定理 map_vadd
  条件: (p : P) (v : V)
  结论: f (v +ᵥ p) = f.linearIsometry v +ᵥ f p
  证明: f.toAffineMap.map_vadd p v

@[simp]

Depends on / 依赖: f.toAffineMap.map_vadd, map_vadd, toAffineMap
-/
theorem map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linearIsometry v +ᵥ f p :=
  f.toAffineMap.map_vadd p v

@[simp]
/--
theorem `map_vsub` / 定理 `map_vsub`

English:
theorem map_vsub
  given: (p1 p2 : P)
  statement: f.linearIsometry (p1 -ᵥ p2) = f p1 -ᵥ f p2
  proof: f.toAffineMap.linearMap_vsub p1 p2

@[simp]

中文:
定理 map_vsub
  条件: (p1 p2 : P)
  结论: f.linearIsometry (p1 -ᵥ p2) = f p1 -ᵥ f p2
  证明: f.toAffineMap.linearMap_vsub p1 p2

@[simp]

Depends on / 依赖: f.toAffineMap.linearMap_vsub, linearMap_vsub, toAffineMap
-/
theorem map_vsub (p1 p2 : P) : f.linearIsometry (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
  f.toAffineMap.linearMap_vsub p1 p2

@[simp]
/--
theorem `dist_map` / 定理 `dist_map`

English:
theorem dist_map
  given: (x y : P)
  statement: dist (f x) (f y) = dist x y
  proof: by
  rw [dist_eq_norm_vsub V₂]; rw [dist_eq_norm_vsub V]; rw [← map_vsub]; rw [f.linearIsometry.norm_map]

@[simp]

中文:
定理 dist_map
  条件: (x y : P)
  结论: dist (f x) (f y) = dist x y
  证明: by
  rw [dist_eq_norm_vsub V₂]; rw [dist_eq_norm_vsub V]; rw [← map_vsub]; rw [f.linearIsometry.norm_map]

@[simp]

Depends on / 依赖: dist_eq_norm_vsub, f.linearIsometry.norm_map, linearIsometry, map_vsub, norm_map
-/
theorem dist_map (x y : P) : dist (f x) (f y) = dist x y := by
  rw [dist_eq_norm_vsub V₂]; rw [dist_eq_norm_vsub V]; rw [← map_vsub]; rw [f.linearIsometry.norm_map]

@[simp]
/--
theorem `nndist_map` / 定理 `nndist_map`

English:
theorem nndist_map
  given: (x y : P)
  statement: nndist (f x) (f y) = nndist x y
  proof: by simp [nndist_dist]

@[simp]

中文:
定理 nndist_map
  条件: (x y : P)
  结论: nndist (f x) (f y) = nndist x y
  证明: by simp [nndist_dist]

@[simp]

Depends on / 依赖: nndist_dist
-/
theorem nndist_map (x y : P) : nndist (f x) (f y) = nndist x y := by simp [nndist_dist]

@[simp]
/--
theorem `edist_map` / 定理 `edist_map`

English:
theorem edist_map
  given: (x y : P)
  statement: edist (f x) (f y) = edist x y
  proof: by simp [edist_dist]

中文:
定理 edist_map
  条件: (x y : P)
  结论: edist (f x) (f y) = edist x y
  证明: by simp [edist_dist]

Depends on / 依赖: edist_dist
-/
theorem edist_map (x y : P) : edist (f x) (f y) = edist x y := by simp [edist_dist]

/--
theorem `isometry` / 定理 `isometry`

English:
theorem isometry
  statement: Isometry f
  proof: f.edist_map

中文:
定理 isometry
  结论: 等距 f
  证明: f.edist_map
-/
protected theorem isometry : Isometry f :=
  f.edist_map

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Injective f₁
  proof: f₁.isometry.injective

@[simp]

中文:
定理 injective
  结论: 单射 f₁
  证明: f₁.isometry.injective

@[simp]
-/
protected theorem injective : Injective f₁ :=
  f₁.isometry.injective

@[simp]
/--
theorem `map_eq_iff` / 定理 `map_eq_iff`

English:
theorem map_eq_iff
  given: {x y : P₁'}
  statement: f₁ x = f₁ y ↔ x = y
  proof: f₁.injective.eq_iff

中文:
定理 map_eq_iff
  条件: {x y : P₁'}
  结论: f₁ x = f₁ y ↔ x = y
  证明: f₁.injective.eq_iff

Depends on / 依赖: eq_iff, injective, injective.eq_iff
-/
theorem map_eq_iff {x y : P₁'} : f₁ x = f₁ y ↔ x = y :=
  f₁.injective.eq_iff

/--
theorem `map_ne` / 定理 `map_ne`

English:
theorem map_ne
  given: {x y : P₁'} (h : x != y)
  statement: f₁ x != f₁ y
  proof: f₁.injective.ne h

中文:
定理 map_ne
  条件: {x y : P₁'} (h : x != y)
  结论: f₁ x != f₁ y
  证明: f₁.injective.ne h

Depends on / 依赖: injective, injective.ne
-/
theorem map_ne {x y : P₁'} (h : x != y) : f₁ x != f₁ y :=
  f₁.injective.ne h

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  statement: LipschitzWith 1 f
  proof: f.isometry.lipschitz

中文:
定理 lipschitz
  结论: LipschitzWith 1 f
  证明: f.isometry.lipschitz
-/
protected theorem lipschitz : LipschitzWith 1 f :=
  f.isometry.lipschitz

/--
theorem `antilipschitz` / 定理 `antilipschitz`

English:
theorem antilipschitz
  statement: AntilipschitzWith 1 f
  proof: f.isometry.antilipschitz

@[continuity]

中文:
定理 antilipschitz
  结论: AntilipschitzWith 1 f
  证明: f.isometry.antilipschitz

@[continuity]
-/
protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.isometry.antilipschitz

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous f
  proof: f.isometry.continuous

中文:
定理 continuous
  结论: 连续 f
  证明: f.isometry.continuous
-/
protected theorem continuous : Continuous f :=
  f.isometry.continuous

/--
theorem `ediam_image` / 定理 `ediam_image`

English:
theorem ediam_image
  given: (s : Set P)
  statement: ediam (f '' s) = ediam s
  proof: f.isometry.ediam_image s

中文:
定理 ediam_image
  条件: (s : 集合 P)
  结论: ediam (f '' s) = ediam s
  证明: f.isometry.ediam_image s

Depends on / 依赖: ediam_image, f.isometry.ediam_image, isometry
-/
theorem ediam_image (s : Set P) : ediam (f '' s) = ediam s :=
  f.isometry.ediam_image s

/--
theorem `ediam_range` / 定理 `ediam_range`

English:
theorem ediam_range
  statement: ediam (range f) = ediam (univ : Set P)
  proof: f.isometry.ediam_range

中文:
定理 ediam_range
  结论: ediam (range f) = ediam (univ : 集合 P)
  证明: f.isometry.ediam_range

Depends on / 依赖: ediam_range, f.isometry.ediam_range, isometry
-/
theorem ediam_range : ediam (range f) = ediam (univ : Set P) :=
  f.isometry.ediam_range

/--
theorem `diam_image` / 定理 `diam_image`

English:
theorem diam_image
  given: (s : Set P)
  statement: Metric.diam (f '' s) = Metric.diam s
  proof: f.isometry.diam_image s

中文:
定理 diam_image
  条件: (s : 集合 P)
  结论: Metric.diam (f '' s) = Metric.diam s
  证明: f.isometry.diam_image s

Depends on / 依赖: diam_image, f.isometry.diam_image, isometry
-/
theorem diam_image (s : Set P) : Metric.diam (f '' s) = Metric.diam s :=
  f.isometry.diam_image s

/--
theorem `diam_range` / 定理 `diam_range`

English:
theorem diam_range
  statement: Metric.diam (range f) = Metric.diam (univ : Set P)
  proof: f.isometry.diam_range

中文:
定理 diam_range
  结论: Metric.diam (range f) = Metric.diam (univ : 集合 P)
  证明: f.isometry.diam_range

Depends on / 依赖: diam_range, f.isometry.diam_range, isometry
-/
theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set P) :=
  f.isometry.diam_range

/--
Definition of `toContinuousAffineMap` / `toContinuousAffineMap` 的定义

English:
definition toContinuousAffineMap
  signature: : P ->ᴬ[𝕜] P₂
  body: { f with cont := f.continuous }

中文:
定义 toContinuousAffineMap
  签名: : P ->ᴬ[𝕜] P₂
  定义体: { f with cont := f.continuous }

Depends on / 依赖: continuous, f.continuous
-/
def toContinuousAffineMap : P ->ᴬ[𝕜] P₂ := { f with cont := f.continuous }

/--
theorem `toContinuousAffineMap_injective` / 定理 `toContinuousAffineMap_injective`

English:
theorem toContinuousAffineMap_injective
  proof: fun x _ h =>
  coeFn_injective (congr_arg _ h : ⇑x.toContinuousAffineMap = _)

@[simp]

中文:
定理 toContinuousAffineMap_injective
  证明: fun x _ h =>
  coeFn_injective (congr_arg _ h : ⇑x.toContinuousAffineMap = _)

@[simp]
-/
theorem toContinuousAffineMap_injective :
    Function.Injective (toContinuousAffineMap : _ -> P ->ᴬ[𝕜] P₂) := fun x _ h =>
  coeFn_injective (congr_arg _ h : ⇑x.toContinuousAffineMap = _)

@[simp]
/--
theorem `toContinuousAffineMap_inj` / 定理 `toContinuousAffineMap_inj`

English:
theorem toContinuousAffineMap_inj
  given: {f g : P ->ᵃⁱ[𝕜] P₂}
  proof: toContinuousAffineMap_injective.eq_iff

@[simp]

中文:
定理 toContinuousAffineMap_inj
  条件: {f g : P ->ᵃⁱ[𝕜] P₂}
  证明: toContinuousAffineMap_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toContinuousAffineMap_injective, toContinuousAffineMap_injective.eq_iff
-/
theorem toContinuousAffineMap_inj {f g : P ->ᵃⁱ[𝕜] P₂} :
    f.toContinuousAffineMap = g.toContinuousAffineMap ↔ f = g :=
  toContinuousAffineMap_injective.eq_iff

@[simp]
/--
theorem `coe_toContinuousAffineMap` / 定理 `coe_toContinuousAffineMap`

English:
theorem coe_toContinuousAffineMap
  statement: ⇑f.toContinuousAffineMap = f
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousAffineMap
  结论: ⇑f.toContinuousAffineMap = f
  证明: rfl

@[simp]
-/
theorem coe_toContinuousAffineMap : ⇑f.toContinuousAffineMap = f := rfl

@[simp]
/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: {α : Type*} [TopologicalSpace α] {g : α -> P}
  proof: f.isometry.comp_continuous_iff

中文:
定理 comp_continuous_iff
  条件: {α : 类型} [拓扑空间 α] {g : α -> P}
  证明: f.isometry.comp_continuous_iff

Depends on / 依赖: comp_continuous_iff, f.isometry.comp_continuous_iff, isometry
-/
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α -> P} :
    Continuous (f ∘ g) ↔ Continuous g :=
  f.isometry.comp_continuous_iff

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : P ->ᵃⁱ[𝕜] P
  body: ⟨AffineMap.id 𝕜 P, fun _ => rfl⟩

@[simp, norm_cast]

中文:
定义 id
  签名: : P ->ᵃⁱ[𝕜] P
  定义体: ⟨AffineMap.id 𝕜 P, fun _ => rfl⟩

@[simp, norm_cast]

Depends on / 依赖: AffineMap, AffineMap.id
-/
def id : P ->ᵃⁱ[𝕜] P :=
  ⟨AffineMap.id 𝕜 P, fun _ => rfl⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(id : P ->ᵃⁱ[𝕜] P) = _root_.id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ⇑(id : P ->ᵃⁱ[𝕜] P) = _root_.id
  证明: rfl

@[simp]
-/
theorem coe_id : ⇑(id : P ->ᵃⁱ[𝕜] P) = _root_.id :=
  rfl

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : P)
  statement: (AffineIsometry.id : P ->ᵃⁱ[𝕜] P) x = x
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (x : P)
  结论: (仿射等距.id : P ->ᵃⁱ[𝕜] P) x = x
  证明: rfl

@[simp]
-/
theorem id_apply (x : P) : (AffineIsometry.id : P ->ᵃⁱ[𝕜] P) x = x :=
  rfl

@[simp]
/--
theorem `id_toAffineMap` / 定理 `id_toAffineMap`

English:
theorem id_toAffineMap
  statement: (id.toAffineMap : P ->ᵃ[𝕜] P) = AffineMap.id 𝕜 P
  proof: rfl

@[simp]

中文:
定理 id_toAffineMap
  结论: (id.toAffineMap : P ->ᵃ[𝕜] P) = 仿射映射.id 𝕜 P
  证明: rfl

@[simp]
-/
theorem id_toAffineMap : (id.toAffineMap : P ->ᵃ[𝕜] P) = AffineMap.id 𝕜 P :=
  rfl

@[simp]
/--
theorem `toContinuousAffineMap_id` / 定理 `toContinuousAffineMap_id`

English:
theorem toContinuousAffineMap_id
  statement: id.toContinuousAffineMap = ContinuousAffineMap.id 𝕜 P
  proof: rfl

中文:
定理 toContinuousAffineMap_id
  结论: id.toContinuousAffineMap = 余ntinuousAffine映射.id 𝕜 P
  证明: rfl
-/
theorem toContinuousAffineMap_id : id.toContinuousAffineMap = ContinuousAffineMap.id 𝕜 P :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (P ->ᵃⁱ[𝕜] P)
  body: ⟨id⟩

中文:
实例 :
  签名: 可居 (P ->ᵃⁱ[𝕜] P)
  定义体: ⟨id⟩
-/
instance : Inhabited (P ->ᵃⁱ[𝕜] P) :=
  ⟨id⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : P₂ ->ᵃⁱ[𝕜] P₃) (f : P ->ᵃⁱ[𝕜] P₂)
  body: ⟨g.toAffineMap.comp f.toAffineMap, fun _ => (g.norm_map _).trans (f.norm_map _)⟩

@[simp]

中文:
定义 comp
  签名: (g : P₂ ->ᵃⁱ[𝕜] P₃) (f : P ->ᵃⁱ[𝕜] P₂)
  定义体: ⟨g.toAffineMap.comp f.toAffineMap, fun _ => (g.norm_map _).trans (f.norm_map _)⟩

@[simp]

Depends on / 依赖: f.norm_map, f.toAffineMap, g.norm_map, g.toAffineMap.comp, norm_map, toAffineMap
-/
def comp (g : P₂ ->ᵃⁱ[𝕜] P₃) (f : P ->ᵃⁱ[𝕜] P₂) : P ->ᵃⁱ[𝕜] P₃ :=
  ⟨g.toAffineMap.comp f.toAffineMap, fun _ => (g.norm_map _).trans (f.norm_map _)⟩

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g : P₂ ->ᵃⁱ[𝕜] P₃) (f : P ->ᵃⁱ[𝕜] P₂)
  statement: ⇑(g.comp f) = g ∘ f
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (g : P₂ ->ᵃⁱ[𝕜] P₃) (f : P ->ᵃⁱ[𝕜] P₂)
  结论: ⇑(g.comp f) = g ∘ f
  证明: rfl

@[simp]
-/
theorem coe_comp (g : P₂ ->ᵃⁱ[𝕜] P₃) (f : P ->ᵃⁱ[𝕜] P₂) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  statement: (id : P₂ ->ᵃⁱ[𝕜] P₂).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  结论: (id : P₂ ->ᵃⁱ[𝕜] P₂).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp : (id : P₂ ->ᵃⁱ[𝕜] P₂).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  statement: f.comp id = f
  proof: ext fun _ => rfl

中文:
定理 comp_id
  结论: f.comp id = f
  证明: ext fun _ => rfl
-/
theorem comp_id : f.comp id = f :=
  ext fun _ => rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : P₃ ->ᵃⁱ[𝕜] P₄) (g : P₂ ->ᵃⁱ[𝕜] P₃) (h : P ->ᵃⁱ[𝕜] P₂)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : P₃ ->ᵃⁱ[𝕜] P₄) (g : P₂ ->ᵃⁱ[𝕜] P₃) (h : P ->ᵃⁱ[𝕜] P₂)
  证明: rfl
-/
theorem comp_assoc (f : P₃ ->ᵃⁱ[𝕜] P₄) (g : P₂ ->ᵃⁱ[𝕜] P₃) (h : P ->ᵃⁱ[𝕜] P₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (P ->ᵃⁱ[𝕜] P)
  body: id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]

中文:
实例 :
  签名: 幺半群 (P ->ᵃⁱ[𝕜] P)
  定义体: id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
-/
instance : Monoid (P ->ᵃⁱ[𝕜] P) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : P ->ᵃⁱ[𝕜] P) = _root_.id
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ⇑(1 : P ->ᵃⁱ[𝕜] P) = _root_.id
  证明: rfl

@[simp]
-/
theorem coe_one : ⇑(1 : P ->ᵃⁱ[𝕜] P) = _root_.id :=
  rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : P ->ᵃⁱ[𝕜] P)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
定理 coe_mul
  条件: (f g : P ->ᵃⁱ[𝕜] P)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
theorem coe_mul (f g : P ->ᵃⁱ[𝕜] P) : ⇑(f * g) = f ∘ g :=
  rfl

end AffineIsometry

namespace AffineSubspace

/--
Definition of `subtypeₐᵢ` / `subtypeₐᵢ` 的定义

English:
definition subtypeₐᵢ
  signature: (s : AffineSubspace 𝕜 P) [Nonempty s]
  body: { s.subtype with norm_map := s.direction.subtypeₗᵢ.norm_map }

中文:
定义 subtypeₐᵢ
  签名: (s : 仿射子空间 𝕜 P) [非空 s]
  定义体: { s.subtype with norm_map := s.direction.subtypeₗᵢ.norm_map }

Depends on / 依赖: direction, norm_map, s.direction.subtype, s.subtype, subtype
-/
def subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] : s ->ᵃⁱ[𝕜] P :=
  { s.subtype with norm_map := s.direction.subtypeₗᵢ.norm_map }

/--
theorem `subtypeₐᵢ_linear` / 定理 `subtypeₐᵢ_linear`

English:
theorem subtypeₐᵢ_linear
  given: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: rfl

@[simp]

中文:
定理 subtypeₐᵢ_linear
  条件: (s : 仿射子空间 𝕜 P) [非空 s]
  证明: rfl

@[simp]
-/
theorem subtypeₐᵢ_linear (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.linear = s.direction.subtype :=
  rfl

@[simp]
/--
theorem `subtypeₐᵢ_linearIsometry` / 定理 `subtypeₐᵢ_linearIsometry`

English:
theorem subtypeₐᵢ_linearIsometry
  given: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: rfl

@[simp]

中文:
定理 subtypeₐᵢ_linearIsometry
  条件: (s : 仿射子空间 𝕜 P) [非空 s]
  证明: rfl

@[simp]
-/
theorem subtypeₐᵢ_linearIsometry (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.linearIsometry = s.direction.subtypeₗᵢ :=
  rfl

@[simp]
/--
theorem `coe_subtypeₐᵢ` / 定理 `coe_subtypeₐᵢ`

English:
theorem coe_subtypeₐᵢ
  given: (s : AffineSubspace 𝕜 P) [Nonempty s]
  statement: ⇑s.subtypeₐᵢ = s.subtype
  proof: rfl

@[simp]

中文:
定理 coe_subtypeₐᵢ
  条件: (s : 仿射子空间 𝕜 P) [非空 s]
  结论: ⇑s.subtypeₐᵢ = s.subtype
  证明: rfl

@[simp]
-/
theorem coe_subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] : ⇑s.subtypeₐᵢ = s.subtype :=
  rfl

@[simp]
/--
theorem `subtypeₐᵢ_toAffineMap` / 定理 `subtypeₐᵢ_toAffineMap`

English:
theorem subtypeₐᵢ_toAffineMap
  given: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: rfl

@[simp]

中文:
定理 subtypeₐᵢ_toAffineMap
  条件: (s : 仿射子空间 𝕜 P) [非空 s]
  证明: rfl

@[simp]
-/
theorem subtypeₐᵢ_toAffineMap (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.toAffineMap = s.subtype :=
  rfl

@[simp]
/--
theorem `toContinuousAffineMap_subtypeₐᵢ` / 定理 `toContinuousAffineMap_subtypeₐᵢ`

English:
theorem toContinuousAffineMap_subtypeₐᵢ
  given: (s : AffineSubspace 𝕜 P) [Nonempty s]
  proof: rfl

中文:
定理 toContinuousAffineMap_subtypeₐᵢ
  条件: (s : 仿射子空间 𝕜 P) [非空 s]
  证明: rfl
-/
theorem toContinuousAffineMap_subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.toContinuousAffineMap = s.subtypeA :=
  rfl

end AffineSubspace

variable (𝕜 P P₂)

/--
Definition of `AffineIsometryEquiv` / `AffineIsometryEquiv` 的定义

English:
structure AffineIsometryEquiv
  parameters: extends P ≃ᵃ[𝕜] P₂
  extends: P ≃ᵃ[𝕜] P₂
  axioms and operations (1):
    - norm_map : forall x, ‖linear x‖ = ‖x‖

中文:
结构 仿射等距等价
  参数: extends P ≃ᵃ[𝕜] P₂
  继承: P ≃ᵃ[𝕜] P₂
  公理与运算 (1 个):
    - norm_map : 对任意 x, ‖linear x‖ = ‖x‖
-/
structure AffineIsometryEquiv extends P ≃ᵃ[𝕜] P₂ where
  norm_map : forall x, ‖linear x‖ = ‖x‖

variable {𝕜 P P₂}

-- `≃ᵃᵢ` would be more consistent with the linear isometry equiv notation, but it is uglier
@[inherit_doc] notation:25 P " ≃ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometryEquiv 𝕜 P P₂

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

/--
Definition of `linearIsometryEquiv` / `linearIsometryEquiv` 的定义

English:
definition linearIsometryEquiv
  signature: : V ≃ₗᵢ[𝕜] V₂
  body: { e.linear with norm_map' := e.norm_map }

@[simp]

中文:
定义 linearIsometryEquiv
  签名: : V ≃ₗᵢ[𝕜] V₂
  定义体: { e.linear with norm_map' := e.norm_map }

@[simp]
-/
protected def linearIsometryEquiv : V ≃ₗᵢ[𝕜] V₂ :=
  { e.linear with norm_map' := e.norm_map }

@[simp]
/--
theorem `linear_eq_linear_isometry` / 定理 `linear_eq_linear_isometry`

English:
theorem linear_eq_linear_isometry
  statement: e.linear = e.linearIsometryEquiv.toLinearEquiv
  proof: by
  ext
  rfl

中文:
定理 linear_eq_linear_isometry
  结论: e.linear = e.linearIsometryEquiv.toLinearEquiv
  证明: by
  ext
  rfl
-/
theorem linear_eq_linear_isometry : e.linear = e.linearIsometryEquiv.toLinearEquiv := by
  ext
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (P ≃ᵃⁱ[𝕜] P₂) P P₂
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h _ := by
    cases f
    cases g
    congr
    simpa [DFunLike.coe_injective.eq_iff] using h

@[simp]

中文:
实例 :
  签名: 等价状 (P ≃ᵃⁱ[𝕜] P₂) P P₂
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h _ := by
    cases f
    cases g
    congr
    simpa [DFunLike.coe_injective.eq_iff] using h

@[simp]

Depends on / 依赖: f.toFun
-/
instance : EquivLike (P ≃ᵃⁱ[𝕜] P₂) P P₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h _ := by
    cases f
    cases g
    congr
    simpa [DFunLike.coe_injective.eq_iff] using h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : P ≃ᵃ[𝕜] P₂) (he : forall x, ‖e.linear x‖ = ‖x‖)
  statement: ⇑(mk e he) = e
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (e : P ≃ᵃ[𝕜] P₂) (he : 对任意 x, ‖e.linear x‖ = ‖x‖)
  结论: ⇑(mk e he) = e
  证明: rfl

@[simp]
-/
theorem coe_mk (e : P ≃ᵃ[𝕜] P₂) (he : forall x, ‖e.linear x‖ = ‖x‖) : ⇑(mk e he) = e :=
  rfl

@[simp]
/--
theorem `coe_toAffineEquiv` / 定理 `coe_toAffineEquiv`

English:
theorem coe_toAffineEquiv
  given: (e : P ≃ᵃⁱ[𝕜] P₂)
  statement: ⇑e.toAffineEquiv = e
  proof: rfl

中文:
定理 coe_toAffineEquiv
  条件: (e : P ≃ᵃⁱ[𝕜] P₂)
  结论: ⇑e.toAffineEquiv = e
  证明: rfl
-/
theorem coe_toAffineEquiv (e : P ≃ᵃⁱ[𝕜] P₂) : ⇑e.toAffineEquiv = e :=
  rfl

/--
theorem `toAffineEquiv_injective` / 定理 `toAffineEquiv_injective`

English:
theorem toAffineEquiv_injective
  statement: Injective (toAffineEquiv : (P ≃ᵃⁱ[𝕜] P₂) -> P ≃ᵃ[𝕜] P₂)

中文:
定理 toAffineEquiv_injective
  结论: 单射 (toAffineEquiv : (P ≃ᵃⁱ[𝕜] P₂) -> P ≃ᵃ[𝕜] P₂)
-/
theorem toAffineEquiv_injective : Injective (toAffineEquiv : (P ≃ᵃⁱ[𝕜] P₂) -> P ≃ᵃ[𝕜] P₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e' x)
  statement: e = e'
  proof: toAffineEquiv_injective AffineEquiv.ext h

中文:
定理 ext
  条件: {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : 对任意 x, e x = e' x)
  结论: e = e'
  证明: toAffineEquiv_injective AffineEquiv.ext h

Depends on / 依赖: AffineEquiv, AffineEquiv.ext, toAffineEquiv_injective
-/
theorem ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e' x) : e = e' :=
toAffineEquiv_injective AffineEquiv.ext h

/--
theorem `coeFn_injective` / 定理 `coeFn_injective`

English:
theorem coeFn_injective
  statement: @Injective (P ≃ᵃⁱ[𝕜] P₂) (P -> P₂) (fun f => f)
  proof: DFunLike.coe_injective

中文:
定理 coeFn_injective
  结论: @单射 (P ≃ᵃⁱ[𝕜] P₂) (P -> P₂) (fun f => f)
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coeFn_injective : @Injective (P ≃ᵃⁱ[𝕜] P₂) (P -> P₂) (fun f => f) :=
  DFunLike.coe_injective

/--
Definition of `toAffineIsometry` / `toAffineIsometry` 的定义

English:
definition toAffineIsometry
  signature: : P ->ᵃⁱ[𝕜] P₂
  body: ⟨e.1.toAffineMap, e.2⟩

@[simp]

中文:
定义 toAffineIsometry
  签名: : P ->ᵃⁱ[𝕜] P₂
  定义体: ⟨e.1.toAffineMap, e.2⟩

@[simp]

Depends on / 依赖: toAffineMap
-/
def toAffineIsometry : P ->ᵃⁱ[𝕜] P₂ :=
  ⟨e.1.toAffineMap, e.2⟩

@[simp]
/--
theorem `coe_toAffineIsometry` / 定理 `coe_toAffineIsometry`

English:
theorem coe_toAffineIsometry
  statement: ⇑e.toAffineIsometry = e
  proof: rfl

中文:
定理 coe_toAffineIsometry
  结论: ⇑e.toAffineIsometry = e
  证明: rfl
-/
theorem coe_toAffineIsometry : ⇑e.toAffineIsometry = e :=
  rfl

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : forall p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p)
  body: { AffineEquiv.mk' e e'.toLinearEquiv p h with norm_map := e'.norm_map }

@[simp]

中文:
定义 mk'
  签名: (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : 对任意 p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p)
  定义体: { AffineEquiv.mk' e e'.toLinearEquiv p h with norm_map := e'.norm_map }

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.mk, norm_map, toLinearEquiv
-/
def mk' (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : forall p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  { AffineEquiv.mk' e e'.toLinearEquiv p h with norm_map := e'.norm_map }

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h)
  statement: ⇑(mk' e e' p h) = e
  proof: rfl

@[simp]

中文:
定理 coe_mk'
  条件: (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h)
  结论: ⇑(mk' e e' p h) = e
  证明: rfl

@[simp]
-/
theorem coe_mk' (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) : ⇑(mk' e e' p h) = e :=
  rfl

@[simp]
/--
theorem `linearIsometryEquiv_mk'` / 定理 `linearIsometryEquiv_mk'`

English:
theorem linearIsometryEquiv_mk'
  given: (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h)
  proof: by
  ext
  rfl

中文:
定理 linearIsometryEquiv_mk'
  条件: (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h)
  证明: by
  ext
  rfl
-/
theorem linearIsometryEquiv_mk' (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) :
    (mk' e e' p h).linearIsometryEquiv = e' := by
  ext
  rfl

end AffineIsometryEquiv

namespace LinearIsometryEquiv

variable (e : V ≃ₗᵢ[𝕜] V₂)

/--
Definition of `toAffineIsometryEquiv` / `toAffineIsometryEquiv` 的定义

English:
definition toAffineIsometryEquiv
  signature: : V ≃ᵃⁱ[𝕜] V₂
  body: { e.toLinearEquiv.toAffineEquiv with norm_map := e.norm_map }

@[simp]

中文:
定义 toAffineIsometryEquiv
  签名: : V ≃ᵃⁱ[𝕜] V₂
  定义体: { e.toLinearEquiv.toAffineEquiv with norm_map := e.norm_map }

@[simp]

Depends on / 依赖: e.norm_map, e.toLinearEquiv.toAffineEquiv, norm_map, toAffineEquiv, toLinearEquiv
-/
def toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂ :=
  { e.toLinearEquiv.toAffineEquiv with norm_map := e.norm_map }

@[simp]
/--
theorem `coe_toAffineIsometryEquiv` / 定理 `coe_toAffineIsometryEquiv`

English:
theorem coe_toAffineIsometryEquiv
  statement: ⇑(e.toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂) = e
  proof: by
  rfl

@[simp]

中文:
定理 coe_toAffineIsometryEquiv
  结论: ⇑(e.toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂) = e
  证明: by
  rfl

@[simp]
-/
theorem coe_toAffineIsometryEquiv : ⇑(e.toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂) = e := by
  rfl

@[simp]
/--
theorem `toAffineIsometryEquiv_linearIsometryEquiv` / 定理 `toAffineIsometryEquiv_linearIsometryEquiv`

English:
theorem toAffineIsometryEquiv_linearIsometryEquiv
  proof: by
  ext
  rfl

中文:
定理 toAffineIsometryEquiv_linearIsometryEquiv
  证明: by
  ext
  rfl
-/
theorem toAffineIsometryEquiv_linearIsometryEquiv :
    e.toAffineIsometryEquiv.linearIsometryEquiv = e := by
  ext
  rfl

-- somewhat arbitrary choice of simp direction
@[simp]
/--
theorem `toAffineIsometryEquiv_toAffineEquiv` / 定理 `toAffineIsometryEquiv_toAffineEquiv`

English:
theorem toAffineIsometryEquiv_toAffineEquiv
  proof: rfl

中文:
定理 toAffineIsometryEquiv_toAffineEquiv
  证明: rfl
-/
theorem toAffineIsometryEquiv_toAffineEquiv :
    e.toAffineIsometryEquiv.toAffineEquiv = e.toLinearEquiv.toAffineEquiv :=
  rfl

-- somewhat arbitrary choice of simp direction
@[simp]
/--
theorem `toAffineIsometryEquiv_toAffineIsometry` / 定理 `toAffineIsometryEquiv_toAffineIsometry`

English:
theorem toAffineIsometryEquiv_toAffineIsometry
  proof: rfl

中文:
定理 toAffineIsometryEquiv_toAffineIsometry
  证明: rfl
-/
theorem toAffineIsometryEquiv_toAffineIsometry :
    e.toAffineIsometryEquiv.toAffineIsometry = e.toLinearIsometry.toAffineIsometry :=
  rfl

end LinearIsometryEquiv

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

/--
theorem `isometry` / 定理 `isometry`

English:
theorem isometry
  statement: Isometry e
  proof: e.toAffineIsometry.isometry

中文:
定理 isometry
  结论: 等距 e
  证明: e.toAffineIsometry.isometry
-/
protected theorem isometry : Isometry e :=
  e.toAffineIsometry.isometry

/--
Definition of `toIsometryEquiv` / `toIsometryEquiv` 的定义

English:
definition toIsometryEquiv
  signature: : P ≃ᵢ P₂
  body: ⟨e.toAffineEquiv.toEquiv, e.isometry⟩

@[simp]

中文:
定义 toIsometryEquiv
  签名: : P ≃ᵢ P₂
  定义体: ⟨e.toAffineEquiv.toEquiv, e.isometry⟩

@[simp]

Depends on / 依赖: e.isometry, e.toAffineEquiv.toEquiv, isometry, toAffineEquiv, toEquiv
-/
def toIsometryEquiv : P ≃ᵢ P₂ :=
  ⟨e.toAffineEquiv.toEquiv, e.isometry⟩

@[simp]
/--
theorem `coe_toIsometryEquiv` / 定理 `coe_toIsometryEquiv`

English:
theorem coe_toIsometryEquiv
  statement: ⇑e.toIsometryEquiv = e
  proof: rfl

中文:
定理 coe_toIsometryEquiv
  结论: ⇑e.toIsometryEquiv = e
  证明: rfl
-/
theorem coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e :=
  rfl

/--
theorem `range_eq_univ` / 定理 `range_eq_univ`

English:
theorem range_eq_univ
  given: (e : P ≃ᵃⁱ[𝕜] P₂)
  statement: Set.range e = Set.univ
  proof: by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

中文:
定理 range_eq_univ
  条件: (e : P ≃ᵃⁱ[𝕜] P₂)
  结论: 集合.range e = 集合.univ
  证明: by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

Depends on / 依赖: IsometryEquiv, IsometryEquiv.range_eq_univ, coe_toIsometryEquiv, range_eq_univ
-/
theorem range_eq_univ (e : P ≃ᵃⁱ[𝕜] P₂) : Set.range e = Set.univ := by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: : P ≃ₜ P₂
  body: e.toIsometryEquiv.toHomeomorph

@[simp]

中文:
定义 toHomeomorph
  签名: : P ≃ₜ P₂
  定义体: e.toIsometryEquiv.toHomeomorph

@[simp]

Depends on / 依赖: e.toIsometryEquiv.toHomeomorph, toHomeomorph, toIsometryEquiv
-/
def toHomeomorph : P ≃ₜ P₂ :=
  e.toIsometryEquiv.toHomeomorph

@[simp]
/--
theorem `coe_toHomeomorph` / 定理 `coe_toHomeomorph`

English:
theorem coe_toHomeomorph
  statement: ⇑e.toHomeomorph = e
  proof: rfl

中文:
定理 coe_toHomeomorph
  结论: ⇑e.toHomeomorph = e
  证明: rfl
-/
theorem coe_toHomeomorph : ⇑e.toHomeomorph = e :=
  rfl

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous e
  proof: e.isometry.continuous

中文:
定理 continuous
  结论: 连续 e
  证明: e.isometry.continuous
-/
protected theorem continuous : Continuous e :=
  e.isometry.continuous

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: {x}
  statement: ContinuousAt e x
  proof: e.continuous.continuousAt

中文:
定理 continuousAt
  条件: {x}
  结论: ContinuousAt e x
  证明: e.continuous.continuousAt
-/
protected theorem continuousAt {x} : ContinuousAt e x :=
  e.continuous.continuousAt

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: {s}
  statement: ContinuousOn e s
  proof: e.continuous.continuousOn

中文:
定理 continuousOn
  条件: {s}
  结论: ContinuousOn e s
  证明: e.continuous.continuousOn
-/
protected theorem continuousOn {s} : ContinuousOn e s :=
  e.continuous.continuousOn

/--
theorem `continuousWithinAt` / 定理 `continuousWithinAt`

English:
theorem continuousWithinAt
  given: {s x}
  statement: ContinuousWithinAt e s x
  proof: e.continuous.continuousWithinAt

中文:
定理 continuousWithinAt
  条件: {s x}
  结论: ContinuousWithinAt e s x
  证明: e.continuous.continuousWithinAt
-/
protected theorem continuousWithinAt {s x} : ContinuousWithinAt e s x :=
  e.continuous.continuousWithinAt

/--
Definition of `toContinuousAffineEquiv` / `toContinuousAffineEquiv` 的定义

English:
definition toContinuousAffineEquiv
  signature: : P ≃ᴬ[𝕜] P₂
  body: { e.toAffineEquiv, e.toHomeomorph with }

中文:
定义 toContinuousAffineEquiv
  签名: : P ≃ᴬ[𝕜] P₂
  定义体: { e.toAffineEquiv, e.toHomeomorph with }

Depends on / 依赖: e.toAffineEquiv, e.toHomeomorph, toAffineEquiv, toHomeomorph
-/
def toContinuousAffineEquiv : P ≃ᴬ[𝕜] P₂ :=
  { e.toAffineEquiv, e.toHomeomorph with }

/--
theorem `toContinuousAffineEquiv_injective` / 定理 `toContinuousAffineEquiv_injective`

English:
theorem toContinuousAffineEquiv_injective
  proof: fun x _ h =>
  coeFn_injective (congr_arg _ h : ⇑x.toContinuousAffineEquiv = _)

@[simp]

中文:
定理 toContinuousAffineEquiv_injective
  证明: fun x _ h =>
  coeFn_injective (congr_arg _ h : ⇑x.toContinuousAffineEquiv = _)

@[simp]
-/
theorem toContinuousAffineEquiv_injective :
    Function.Injective (toContinuousAffineEquiv : _ -> P ≃ᴬ[𝕜] P₂) := fun x _ h =>
  coeFn_injective (congr_arg _ h : ⇑x.toContinuousAffineEquiv = _)

@[simp]
/--
theorem `toContinuousAffineEquiv_inj` / 定理 `toContinuousAffineEquiv_inj`

English:
theorem toContinuousAffineEquiv_inj
  given: {f g : P ≃ᵃⁱ[𝕜] P₂}
  proof: toContinuousAffineEquiv_injective.eq_iff

@[simp]

中文:
定理 toContinuousAffineEquiv_inj
  条件: {f g : P ≃ᵃⁱ[𝕜] P₂}
  证明: toContinuousAffineEquiv_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toContinuousAffineEquiv_injective, toContinuousAffineEquiv_injective.eq_iff
-/
theorem toContinuousAffineEquiv_inj {f g : P ≃ᵃⁱ[𝕜] P₂} :
    f.toContinuousAffineEquiv = g.toContinuousAffineEquiv ↔ f = g :=
  toContinuousAffineEquiv_injective.eq_iff

@[simp]
/--
theorem `coe_toContinuousAffineEquiv` / 定理 `coe_toContinuousAffineEquiv`

English:
theorem coe_toContinuousAffineEquiv
  statement: ⇑e.toContinuousAffineEquiv = e
  proof: rfl

中文:
定理 coe_toContinuousAffineEquiv
  结论: ⇑e.toContinuousAffineEquiv = e
  证明: rfl
-/
theorem coe_toContinuousAffineEquiv : ⇑e.toContinuousAffineEquiv = e :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (P ≃ᵃⁱ[𝕜] P₂) (P ≃ᴬ[𝕜] P₂)
  body: ⟨fun e => e.toContinuousAffineEquiv⟩

中文:
实例 :
  签名: Coe (P ≃ᵃⁱ[𝕜] P₂) (P ≃ᴬ[𝕜] P₂)
  定义体: ⟨fun e => e.toContinuousAffineEquiv⟩

Depends on / 依赖: e.toContinuousAffineEquiv, toContinuousAffineEquiv
-/
instance : Coe (P ≃ᵃⁱ[𝕜] P₂) (P ≃ᴬ[𝕜] P₂) :=
  ⟨fun e => e.toContinuousAffineEquiv⟩

variable (𝕜 P)

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : P ≃ᵃⁱ[𝕜] P
  body: ⟨AffineEquiv.refl 𝕜 P, fun _ => rfl⟩

中文:
定义 refl
  签名: : P ≃ᵃⁱ[𝕜] P
  定义体: ⟨AffineEquiv.refl 𝕜 P, fun _ => rfl⟩

Depends on / 依赖: AffineEquiv, AffineEquiv.refl
-/
def refl : P ≃ᵃⁱ[𝕜] P :=
  ⟨AffineEquiv.refl 𝕜 P, fun _ => rfl⟩

variable {𝕜 P}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (P ≃ᵃⁱ[𝕜] P)
  body: ⟨refl 𝕜 P⟩

@[simp]

中文:
实例 :
  签名: 可居 (P ≃ᵃⁱ[𝕜] P)
  定义体: ⟨refl 𝕜 P⟩

@[simp]
-/
instance : Inhabited (P ≃ᵃⁱ[𝕜] P) :=
  ⟨refl 𝕜 P⟩

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(refl 𝕜 P) = id
  proof: rfl

@[simp]

中文:
定理 coe_refl
  结论: ⇑(refl 𝕜 P) = id
  证明: rfl

@[simp]
-/
theorem coe_refl : ⇑(refl 𝕜 P) = id :=
  rfl

@[simp]
/--
theorem `toAffineEquiv_refl` / 定理 `toAffineEquiv_refl`

English:
theorem toAffineEquiv_refl
  statement: (refl 𝕜 P).toAffineEquiv = AffineEquiv.refl 𝕜 P
  proof: rfl

@[simp]

中文:
定理 toAffineEquiv_refl
  结论: (refl 𝕜 P).toAffineEquiv = 仿射等价.refl 𝕜 P
  证明: rfl

@[simp]
-/
theorem toAffineEquiv_refl : (refl 𝕜 P).toAffineEquiv = AffineEquiv.refl 𝕜 P :=
  rfl

@[simp]
/--
theorem `toContinuousAffineEquiv_refl` / 定理 `toContinuousAffineEquiv_refl`

English:
theorem toContinuousAffineEquiv_refl
  statement: (refl 𝕜 P).toContinuousAffineEquiv = .refl 𝕜 P
  proof: rfl

@[simp]

中文:
定理 toContinuousAffineEquiv_refl
  结论: (refl 𝕜 P).toContinuousAffineEquiv = .refl 𝕜 P
  证明: rfl

@[simp]
-/
theorem toContinuousAffineEquiv_refl : (refl 𝕜 P).toContinuousAffineEquiv = .refl 𝕜 P := rfl

@[simp]
/--
theorem `toIsometryEquiv_refl` / 定理 `toIsometryEquiv_refl`

English:
theorem toIsometryEquiv_refl
  statement: (refl 𝕜 P).toIsometryEquiv = IsometryEquiv.refl P
  proof: rfl

@[simp]

中文:
定理 toIsometryEquiv_refl
  结论: (refl 𝕜 P).toIsometryEquiv = 等距等价.refl P
  证明: rfl

@[simp]
-/
theorem toIsometryEquiv_refl : (refl 𝕜 P).toIsometryEquiv = IsometryEquiv.refl P :=
  rfl

@[simp]
/--
theorem `toHomeomorph_refl` / 定理 `toHomeomorph_refl`

English:
theorem toHomeomorph_refl
  statement: (refl 𝕜 P).toHomeomorph = Homeomorph.refl P
  proof: rfl

中文:
定理 toHomeomorph_refl
  结论: (refl 𝕜 P).toHomeomorph = 同胚.refl P
  证明: rfl
-/
theorem toHomeomorph_refl : (refl 𝕜 P).toHomeomorph = Homeomorph.refl P :=
  rfl

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : P₂ ≃ᵃⁱ[𝕜] P
  body: { e.toAffineEquiv.symm with norm_map := e.linearIsometryEquiv.symm.norm_map }

@[simp]

中文:
定义 symm
  签名: : P₂ ≃ᵃⁱ[𝕜] P
  定义体: { e.toAffineEquiv.symm with norm_map := e.linearIsometryEquiv.symm.norm_map }

@[simp]

Depends on / 依赖: e.linearIsometryEquiv.symm.norm_map, e.toAffineEquiv.symm, linearIsometryEquiv, norm_map, toAffineEquiv
-/
def symm : P₂ ≃ᵃⁱ[𝕜] P :=
  { e.toAffineEquiv.symm with norm_map := e.linearIsometryEquiv.symm.norm_map }

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (x : P₂)
  statement: e (e.symm x) = x
  proof: e.toAffineEquiv.apply_symm_apply x

@[simp]

中文:
定理 apply_symm_apply
  条件: (x : P₂)
  结论: e (e.symm x) = x
  证明: e.toAffineEquiv.apply_symm_apply x

@[simp]

Depends on / 依赖: apply_symm_apply, e.toAffineEquiv.apply_symm_apply, toAffineEquiv
-/
theorem apply_symm_apply (x : P₂) : e (e.symm x) = x :=
  e.toAffineEquiv.apply_symm_apply x

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (x : P)
  statement: e.symm (e x) = x
  proof: e.toAffineEquiv.symm_apply_apply x

@[simp]

中文:
定理 symm_apply_apply
  条件: (x : P)
  结论: e.symm (e x) = x
  证明: e.toAffineEquiv.symm_apply_apply x

@[simp]

Depends on / 依赖: e.toAffineEquiv.symm_apply_apply, symm_apply_apply, toAffineEquiv
-/
theorem symm_apply_apply (x : P) : e.symm (e x) = x :=
  e.toAffineEquiv.symm_apply_apply x

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm : e.symm.symm = e := rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toAffineEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toAffineEquiv.symm_apply_eq

Depends on / 依赖: e.toAffineEquiv.symm_apply_eq, symm_apply_eq, toAffineEquiv
-/
theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toAffineEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toAffineEquiv.eq_symm_apply

中文:
定理 eq_symm_apply
  条件: {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toAffineEquiv.eq_symm_apply

Depends on / 依赖: e.toAffineEquiv.eq_symm_apply, eq_symm_apply, toAffineEquiv
-/
theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toAffineEquiv.eq_symm_apply

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Bijective (AffineIsometryEquiv.symm : (P₂ ≃ᵃⁱ[𝕜] P) -> _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 双射 (仿射等距等价.symm : (P₂ ≃ᵃⁱ[𝕜] P) -> _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Bijective (AffineIsometryEquiv.symm : (P₂ ≃ᵃⁱ[𝕜] P) -> _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `toAffineEquiv_symm` / 定理 `toAffineEquiv_symm`

English:
theorem toAffineEquiv_symm
  statement: e.symm.toAffineEquiv = e.toAffineEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toAffineEquiv_symm
  结论: e.symm.toAffineEquiv = e.toAffineEquiv.symm
  证明: rfl

@[simp]
-/
theorem toAffineEquiv_symm : e.symm.toAffineEquiv = e.toAffineEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_symm_toAffineEquiv` / 定理 `coe_symm_toAffineEquiv`

English:
theorem coe_symm_toAffineEquiv
  statement: ⇑e.toAffineEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toAffineEquiv
  结论: ⇑e.toAffineEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toAffineEquiv : ⇑e.toAffineEquiv.symm = e.symm :=
  rfl

@[simp]
/--
theorem `toContinuousAffineEquiv_symm` / 定理 `toContinuousAffineEquiv_symm`

English:
theorem toContinuousAffineEquiv_symm
  proof: rfl

@[simp]

中文:
定理 toContinuousAffineEquiv_symm
  证明: rfl

@[simp]
-/
theorem toContinuousAffineEquiv_symm :
    e.symm.toContinuousAffineEquiv = e.toContinuousAffineEquiv.symm := rfl

@[simp]
/--
theorem `coe_symm_toContinuousAffineEquiv` / 定理 `coe_symm_toContinuousAffineEquiv`

English:
theorem coe_symm_toContinuousAffineEquiv
  statement: ⇑e.toContinuousAffineEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toContinuousAffineEquiv
  结论: ⇑e.toContinuousAffineEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toContinuousAffineEquiv : ⇑e.toContinuousAffineEquiv.symm = e.symm :=
  rfl

@[simp]
/--
theorem `toIsometryEquiv_symm` / 定理 `toIsometryEquiv_symm`

English:
theorem toIsometryEquiv_symm
  statement: e.symm.toIsometryEquiv = e.toIsometryEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toIsometryEquiv_symm
  结论: e.symm.toIsometryEquiv = e.toIsometryEquiv.symm
  证明: rfl

@[simp]
-/
theorem toIsometryEquiv_symm : e.symm.toIsometryEquiv = e.toIsometryEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_symm_toIsometryEquiv` / 定理 `coe_symm_toIsometryEquiv`

English:
theorem coe_symm_toIsometryEquiv
  statement: ⇑e.toIsometryEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toIsometryEquiv
  结论: ⇑e.toIsometryEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toIsometryEquiv : ⇑e.toIsometryEquiv.symm = e.symm :=
  rfl

@[simp]
/--
theorem `toHomeomorph_symm` / 定理 `toHomeomorph_symm`

English:
theorem toHomeomorph_symm
  statement: e.symm.toHomeomorph = e.toHomeomorph.symm
  proof: rfl

@[simp]

中文:
定理 toHomeomorph_symm
  结论: e.symm.toHomeomorph = e.toHomeomorph.symm
  证明: rfl

@[simp]
-/
theorem toHomeomorph_symm : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

@[simp]
/--
theorem `coe_symm_toHomeomorph` / 定理 `coe_symm_toHomeomorph`

English:
theorem coe_symm_toHomeomorph
  statement: ⇑e.toHomeomorph.symm = e.symm
  proof: rfl

中文:
定理 coe_symm_toHomeomorph
  结论: ⇑e.toHomeomorph.symm = e.symm
  证明: rfl
-/
theorem coe_symm_toHomeomorph : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e' : P₂ ≃ᵃⁱ[𝕜] P₃)
  body: ⟨e.toAffineEquiv.trans e'.toAffineEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]

中文:
定义 trans
  签名: (e' : P₂ ≃ᵃⁱ[𝕜] P₃)
  定义体: ⟨e.toAffineEquiv.trans e'.toAffineEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]

Depends on / 依赖: e.norm_map, e.toAffineEquiv.trans, norm_map, toAffineEquiv
-/
def trans (e' : P₂ ≃ᵃⁱ[𝕜] P₃) : P ≃ᵃⁱ[𝕜] P₃ :=
  ⟨e.toAffineEquiv.trans e'.toAffineEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃)
  statement: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃)
  结论: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  证明: rfl

@[simp]
-/
theorem coe_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  statement: e.trans (refl 𝕜 P₂) = e
  proof: ext fun _ => rfl

@[simp]

中文:
定理 trans_refl
  结论: e.trans (refl 𝕜 P₂) = e
  证明: ext fun _ => rfl

@[simp]
-/
theorem trans_refl : e.trans (refl 𝕜 P₂) = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  statement: (refl 𝕜 P).trans e = e
  proof: ext fun _ => rfl

@[simp]

中文:
定理 refl_trans
  结论: (refl 𝕜 P).trans e = e
  证明: ext fun _ => rfl

@[simp]
-/
theorem refl_trans : (refl 𝕜 P).trans e = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  statement: e.trans e.symm = refl 𝕜 P
  proof: ext e.symm_apply_apply

@[simp]

中文:
定理 self_trans_symm
  结论: e.trans e.symm = refl 𝕜 P
  证明: ext e.symm_apply_apply

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem self_trans_symm : e.trans e.symm = refl 𝕜 P :=
  ext e.symm_apply_apply

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  statement: e.symm.trans e = refl 𝕜 P₂
  proof: ext e.apply_symm_apply

@[simp]

中文:
定理 symm_trans_self
  结论: e.symm.trans e = refl 𝕜 P₂
  证明: ext e.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply
-/
theorem symm_trans_self : e.symm.trans e = refl 𝕜 P₂ :=
  ext e.apply_symm_apply

@[simp]
/--
theorem `coe_symm_trans` / 定理 `coe_symm_trans`

English:
theorem coe_symm_trans
  given: (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃)
  proof: rfl

中文:
定理 coe_symm_trans
  条件: (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃)
  证明: rfl
-/
theorem coe_symm_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) :
    ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
  rfl

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄)
  proof: rfl

中文:
定理 trans_assoc
  条件: (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄)
  证明: rfl
-/
theorem trans_assoc (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄) :
    ePP₂.trans (eP₂G.trans eGG') = (ePP₂.trans eP₂G).trans eGG' :=
  rfl

/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: : Group (P ≃ᵃⁱ[𝕜] P) where
  body: e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  inv_mul_cancel := self_trans_symm

@[simp]

中文:
实例 instGroup
  签名: : 群 (P ≃ᵃⁱ[𝕜] P) where
  定义体: e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  inv_mul_cancel := self_trans_symm

@[simp]
-/
instance instGroup : Group (P ≃ᵃⁱ[𝕜] P) where
  mul e₁ e₂ := e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  inv_mul_cancel := self_trans_symm

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : P ≃ᵃⁱ[𝕜] P) = id
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ⇑(1 : P ≃ᵃⁱ[𝕜] P) = id
  证明: rfl

@[simp]
-/
theorem coe_one : ⇑(1 : P ≃ᵃⁱ[𝕜] P) = id :=
  rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (e e' : P ≃ᵃⁱ[𝕜] P)
  statement: ⇑(e * e') = e ∘ e'
  proof: rfl

@[simp]

中文:
定理 coe_mul
  条件: (e e' : P ≃ᵃⁱ[𝕜] P)
  结论: ⇑(e * e') = e ∘ e'
  证明: rfl

@[simp]
-/
theorem coe_mul (e e' : P ≃ᵃⁱ[𝕜] P) : ⇑(e * e') = e ∘ e' :=
  rfl

@[simp]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (e : P ≃ᵃⁱ[𝕜] P)
  statement: ⇑e⁻¹ = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_inv
  条件: (e : P ≃ᵃⁱ[𝕜] P)
  结论: ⇑e⁻¹ = e.symm
  证明: rfl

@[simp]
-/
theorem coe_inv (e : P ≃ᵃⁱ[𝕜] P) : ⇑e⁻¹ = e.symm :=
  rfl

@[simp]
/--
theorem `map_vadd` / 定理 `map_vadd`

English:
theorem map_vadd
  given: (p : P) (v : V)
  statement: e (v +ᵥ p) = e.linearIsometryEquiv v +ᵥ e p
  proof: e.toAffineIsometry.map_vadd p v

@[simp]

中文:
定理 map_vadd
  条件: (p : P) (v : V)
  结论: e (v +ᵥ p) = e.linearIsometryEquiv v +ᵥ e p
  证明: e.toAffineIsometry.map_vadd p v

@[simp]

Depends on / 依赖: e.toAffineIsometry.map_vadd, map_vadd, toAffineIsometry
-/
theorem map_vadd (p : P) (v : V) : e (v +ᵥ p) = e.linearIsometryEquiv v +ᵥ e p :=
  e.toAffineIsometry.map_vadd p v

@[simp]
/--
theorem `map_vsub` / 定理 `map_vsub`

English:
theorem map_vsub
  given: (p1 p2 : P)
  statement: e.linearIsometryEquiv (p1 -ᵥ p2) = e p1 -ᵥ e p2
  proof: e.toAffineIsometry.map_vsub p1 p2

@[simp]

中文:
定理 map_vsub
  条件: (p1 p2 : P)
  结论: e.linearIsometryEquiv (p1 -ᵥ p2) = e p1 -ᵥ e p2
  证明: e.toAffineIsometry.map_vsub p1 p2

@[simp]

Depends on / 依赖: e.toAffineIsometry.map_vsub, map_vsub, toAffineIsometry
-/
theorem map_vsub (p1 p2 : P) : e.linearIsometryEquiv (p1 -ᵥ p2) = e p1 -ᵥ e p2 :=
  e.toAffineIsometry.map_vsub p1 p2

@[simp]
/--
theorem `dist_map` / 定理 `dist_map`

English:
theorem dist_map
  given: (x y : P)
  statement: dist (e x) (e y) = dist x y
  proof: e.toAffineIsometry.dist_map x y

@[simp]

中文:
定理 dist_map
  条件: (x y : P)
  结论: dist (e x) (e y) = dist x y
  证明: e.toAffineIsometry.dist_map x y

@[simp]

Depends on / 依赖: dist_map, e.toAffineIsometry.dist_map, toAffineIsometry
-/
theorem dist_map (x y : P) : dist (e x) (e y) = dist x y :=
  e.toAffineIsometry.dist_map x y

@[simp]
/--
theorem `edist_map` / 定理 `edist_map`

English:
theorem edist_map
  given: (x y : P)
  statement: edist (e x) (e y) = edist x y
  proof: e.toAffineIsometry.edist_map x y

中文:
定理 edist_map
  条件: (x y : P)
  结论: edist (e x) (e y) = edist x y
  证明: e.toAffineIsometry.edist_map x y

Depends on / 依赖: e.toAffineIsometry.edist_map, edist_map, toAffineIsometry
-/
theorem edist_map (x y : P) : edist (e x) (e y) = edist x y :=
  e.toAffineIsometry.edist_map x y

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  statement: Bijective e
  proof: e.1.bijective

中文:
定理 bijective
  结论: 双射 e
  证明: e.1.bijective
-/
protected theorem bijective : Bijective e :=
  e.1.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Injective e
  proof: e.1.injective

中文:
定理 injective
  结论: 单射 e
  证明: e.1.injective
-/
protected theorem injective : Injective e :=
  e.1.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  statement: Surjective e
  proof: e.1.surjective

中文:
定理 surjective
  结论: 满射 e
  证明: e.1.surjective
-/
protected theorem surjective : Surjective e :=
  e.1.surjective

/--
theorem `map_eq_iff` / 定理 `map_eq_iff`

English:
theorem map_eq_iff
  given: {x y : P}
  statement: e x = e y ↔ x = y
  proof: e.injective.eq_iff

中文:
定理 map_eq_iff
  条件: {x y : P}
  结论: e x = e y ↔ x = y
  证明: e.injective.eq_iff

Depends on / 依赖: e.injective.eq_iff, eq_iff, injective
-/
theorem map_eq_iff {x y : P} : e x = e y ↔ x = y :=
  e.injective.eq_iff

/--
theorem `map_ne` / 定理 `map_ne`

English:
theorem map_ne
  given: {x y : P} (h : x != y)
  statement: e x != e y
  proof: e.injective.ne h

中文:
定理 map_ne
  条件: {x y : P} (h : x != y)
  结论: e x != e y
  证明: e.injective.ne h

Depends on / 依赖: e.injective.ne, injective
-/
theorem map_ne {x y : P} (h : x != y) : e x != e y :=
  e.injective.ne h

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  statement: LipschitzWith 1 e
  proof: e.isometry.lipschitz

中文:
定理 lipschitz
  结论: LipschitzWith 1 e
  证明: e.isometry.lipschitz
-/
protected theorem lipschitz : LipschitzWith 1 e :=
  e.isometry.lipschitz

/--
theorem `antilipschitz` / 定理 `antilipschitz`

English:
theorem antilipschitz
  statement: AntilipschitzWith 1 e
  proof: e.isometry.antilipschitz

@[simp]

中文:
定理 antilipschitz
  结论: AntilipschitzWith 1 e
  证明: e.isometry.antilipschitz

@[simp]
-/
protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.isometry.antilipschitz

@[simp]
/--
theorem `ediam_image` / 定理 `ediam_image`

English:
theorem ediam_image
  given: (s : Set P)
  statement: ediam (e '' s) = ediam s
  proof: e.isometry.ediam_image s

@[simp]

中文:
定理 ediam_image
  条件: (s : 集合 P)
  结论: ediam (e '' s) = ediam s
  证明: e.isometry.ediam_image s

@[simp]

Depends on / 依赖: e.isometry.ediam_image, ediam_image, isometry
-/
theorem ediam_image (s : Set P) : ediam (e '' s) = ediam s :=
  e.isometry.ediam_image s

@[simp]
/--
theorem `diam_image` / 定理 `diam_image`

English:
theorem diam_image
  given: (s : Set P)
  statement: Metric.diam (e '' s) = Metric.diam s
  proof: e.isometry.diam_image s

中文:
定理 diam_image
  条件: (s : 集合 P)
  结论: Metric.diam (e '' s) = Metric.diam s
  证明: e.isometry.diam_image s

Depends on / 依赖: diam_image, e.isometry.diam_image, isometry
-/
theorem diam_image (s : Set P) : Metric.diam (e '' s) = Metric.diam s :=
  e.isometry.diam_image s

variable {α : Type*} [TopologicalSpace α]

@[simp]
/--
theorem `comp_continuousOn_iff` / 定理 `comp_continuousOn_iff`

English:
theorem comp_continuousOn_iff
  given: {f : α -> P} {s : Set α}
  statement: ContinuousOn (e ∘ f) s ↔ ContinuousOn f s
  proof: e.isometry.comp_continuousOn_iff

@[simp]

中文:
定理 comp_continuousOn_iff
  条件: {f : α -> P} {s : 集合 α}
  结论: ContinuousOn (e ∘ f) s ↔ ContinuousOn f s
  证明: e.isometry.comp_continuousOn_iff

@[simp]

Depends on / 依赖: comp_continuousOn_iff, e.isometry.comp_continuousOn_iff, isometry
-/
theorem comp_continuousOn_iff {f : α -> P} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.isometry.comp_continuousOn_iff

@[simp]
/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: {f : α -> P}
  statement: Continuous (e ∘ f) ↔ Continuous f
  proof: e.isometry.comp_continuous_iff

中文:
定理 comp_continuous_iff
  条件: {f : α -> P}
  结论: 连续 (e ∘ f) ↔ 连续 f
  证明: e.isometry.comp_continuous_iff

Depends on / 依赖: comp_continuous_iff, e.isometry.comp_continuous_iff, isometry
-/
theorem comp_continuous_iff {f : α -> P} : Continuous (e ∘ f) ↔ Continuous f :=
  e.isometry.comp_continuous_iff

section Constructions

variable (s₁ s₂ : AffineSubspace 𝕜 P) [Nonempty s₁] [Nonempty s₂]

/--
Definition of `ofTop` / `ofTop` 的定义

English:
definition ofTop
  signature: (h : s₁ = ⊤)
  body: { (AffineEquiv.ofEq s₁ ⊤ h).trans (AffineSubspace.topEquiv 𝕜 V P) with norm_map := fun _ => rfl }

中文:
定义 ofTop
  签名: (h : s₁ = ⊤)
  定义体: { (AffineEquiv.ofEq s₁ ⊤ h).trans (AffineSubspace.topEquiv 𝕜 V P) with norm_map := fun _ => rfl }

Depends on / 依赖: AffineEquiv, AffineEquiv.ofEq, AffineSubspace, AffineSubspace.topEquiv, norm_map, topEquiv
-/
def ofTop (h : s₁ = ⊤) : s₁ ≃ᵃⁱ[𝕜] P :=
  { (AffineEquiv.ofEq s₁ ⊤ h).trans (AffineSubspace.topEquiv 𝕜 V P) with norm_map := fun _ => rfl }

variable {s₁}

@[simp]
/--
lemma `ofTop_apply` / 引理 `ofTop_apply`

English:
lemma ofTop_apply
  given: (h : s₁ = ⊤) (x : s₁)
  statement: (ofTop s₁ h x : P) = x
  proof: rfl

@[simp]

中文:
引理 ofTop_apply
  条件: (h : s₁ = ⊤) (x : s₁)
  结论: (ofTop s₁ h x : P) = x
  证明: rfl

@[simp]
-/
lemma ofTop_apply (h : s₁ = ⊤) (x : s₁) : (ofTop s₁ h x : P) = x :=
  rfl

@[simp]
/--
lemma `ofTop_symm_apply_coe` / 引理 `ofTop_symm_apply_coe`

English:
lemma ofTop_symm_apply_coe
  given: (h : s₁ = ⊤) (x : P)
  statement: (ofTop s₁ h).symm x = x
  proof: rfl

中文:
引理 ofTop_symm_apply_coe
  条件: (h : s₁ = ⊤) (x : P)
  结论: (ofTop s₁ h).symm x = x
  证明: rfl
-/
lemma ofTop_symm_apply_coe (h : s₁ = ⊤) (x : P) : (ofTop s₁ h).symm x = x :=
  rfl

variable (s₁)

/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (h : s₁ = s₂)
  body: { AffineEquiv.ofEq s₁ s₂ h with norm_map := fun _ => rfl }

中文:
定义 ofEq
  签名: (h : s₁ = s₂)
  定义体: { AffineEquiv.ofEq s₁ s₂ h with norm_map := fun _ => rfl }

Depends on / 依赖: AffineEquiv, AffineEquiv.ofEq, norm_map
-/
def ofEq (h : s₁ = s₂) : s₁ ≃ᵃⁱ[𝕜] s₂ :=
  { AffineEquiv.ofEq s₁ s₂ h with norm_map := fun _ => rfl }

variable {s₁ s₂}

@[simp]
/--
lemma `coe_ofEq_apply` / 引理 `coe_ofEq_apply`

English:
lemma coe_ofEq_apply
  given: (h : s₁ = s₂) (x : s₁)
  statement: (ofEq s₁ s₂ h x : P) = x
  proof: rfl

@[simp]

中文:
引理 coe_ofEq_apply
  条件: (h : s₁ = s₂) (x : s₁)
  结论: (ofEq s₁ s₂ h x : P) = x
  证明: rfl

@[simp]
-/
lemma coe_ofEq_apply (h : s₁ = s₂) (x : s₁) : (ofEq s₁ s₂ h x : P) = x :=
  rfl

@[simp]
/--
lemma `ofEq_symm` / 引理 `ofEq_symm`

English:
lemma ofEq_symm
  given: (h : s₁ = s₂)
  statement: (ofEq s₁ s₂ h).symm = ofEq s₂ s₁ h.symm
  proof: rfl

@[simp]

中文:
引理 ofEq_symm
  条件: (h : s₁ = s₂)
  结论: (ofEq s₁ s₂ h).symm = ofEq s₂ s₁ h.symm
  证明: rfl

@[simp]
-/
lemma ofEq_symm (h : s₁ = s₂) : (ofEq s₁ s₂ h).symm = ofEq s₂ s₁ h.symm :=
  rfl

@[simp]
/--
lemma `ofEq_rfl` / 引理 `ofEq_rfl`

English:
lemma ofEq_rfl
  statement: ofEq s₁ s₁ rfl = refl 𝕜 s₁
  proof: rfl

中文:
引理 ofEq_rfl
  结论: ofEq s₁ s₁ rfl = refl 𝕜 s₁
  证明: rfl
-/
lemma ofEq_rfl : ofEq s₁ s₁ rfl = refl 𝕜 s₁ :=
  rfl

variable (𝕜) in
/--
Definition of `vaddConst` / `vaddConst` 的定义

English:
definition vaddConst
  signature: (p : P)
  body: { AffineEquiv.vaddConst 𝕜 p with norm_map := fun _ => rfl }

@[simp]

中文:
定义 vaddConst
  签名: (p : P)
  定义体: { AffineEquiv.vaddConst 𝕜 p with norm_map := fun _ => rfl }

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.vaddConst, norm_map, vaddConst
-/
def vaddConst (p : P) : V ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.vaddConst 𝕜 p with norm_map := fun _ => rfl }

@[simp]
/--
theorem `coe_vaddConst` / 定理 `coe_vaddConst`

English:
theorem coe_vaddConst
  given: (p : P)
  statement: ⇑(vaddConst 𝕜 p) = fun v => v +ᵥ p
  proof: rfl

@[simp]

中文:
定理 coe_vaddConst
  条件: (p : P)
  结论: ⇑(vaddConst 𝕜 p) = fun v => v +ᵥ p
  证明: rfl

@[simp]
-/
theorem coe_vaddConst (p : P) : ⇑(vaddConst 𝕜 p) = fun v => v +ᵥ p :=
  rfl

@[simp]
/--
theorem `coe_vaddConst'` / 定理 `coe_vaddConst'`

English:
theorem coe_vaddConst'
  given: (p : P)
  statement: ↑(AffineEquiv.vaddConst 𝕜 p) = fun v => v +ᵥ p
  proof: rfl

@[simp]

中文:
定理 coe_vaddConst'
  条件: (p : P)
  结论: ↑(仿射等价.vaddConst 𝕜 p) = fun v => v +ᵥ p
  证明: rfl

@[simp]
-/
theorem coe_vaddConst' (p : P) : ↑(AffineEquiv.vaddConst 𝕜 p) = fun v => v +ᵥ p :=
  rfl

@[simp]
/--
theorem `coe_vaddConst_symm` / 定理 `coe_vaddConst_symm`

English:
theorem coe_vaddConst_symm
  given: (p : P)
  statement: ⇑(vaddConst 𝕜 p).symm = fun p' => p' -ᵥ p
  proof: rfl

@[simp]

中文:
定理 coe_vaddConst_symm
  条件: (p : P)
  结论: ⇑(vaddConst 𝕜 p).symm = fun p' => p' -ᵥ p
  证明: rfl

@[simp]
-/
theorem coe_vaddConst_symm (p : P) : ⇑(vaddConst 𝕜 p).symm = fun p' => p' -ᵥ p :=
  rfl

@[simp]
/--
theorem `vaddConst_toAffineEquiv` / 定理 `vaddConst_toAffineEquiv`

English:
theorem vaddConst_toAffineEquiv
  given: (p : P)
  proof: rfl

中文:
定理 vaddConst_toAffineEquiv
  条件: (p : P)
  证明: rfl
-/
theorem vaddConst_toAffineEquiv (p : P) :
    (vaddConst 𝕜 p).toAffineEquiv = AffineEquiv.vaddConst 𝕜 p :=
  rfl

variable (𝕜) in
/--
Definition of `constVSub` / `constVSub` 的定义

English:
definition constVSub
  signature: (p : P)
  body: { AffineEquiv.constVSub 𝕜 p with norm_map := norm_neg }

@[simp]

中文:
定义 constVSub
  签名: (p : P)
  定义体: { AffineEquiv.constVSub 𝕜 p with norm_map := norm_neg }

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.constVSub, constVSub, norm_map, norm_neg
-/
def constVSub (p : P) : P ≃ᵃⁱ[𝕜] V :=
  { AffineEquiv.constVSub 𝕜 p with norm_map := norm_neg }

@[simp]
/--
theorem `coe_constVSub` / 定理 `coe_constVSub`

English:
theorem coe_constVSub
  given: (p : P)
  statement: ⇑(constVSub 𝕜 p) = (p -ᵥ ·)
  proof: rfl

@[simp]

中文:
定理 coe_constVSub
  条件: (p : P)
  结论: ⇑(constVSub 𝕜 p) = (p -ᵥ ·)
  证明: rfl

@[simp]
-/
theorem coe_constVSub (p : P) : ⇑(constVSub 𝕜 p) = (p -ᵥ ·) :=
  rfl

@[simp]
/--
theorem `symm_constVSub` / 定理 `symm_constVSub`

English:
theorem symm_constVSub
  given: (p : P)
  proof: by
  ext
  rfl

中文:
定理 symm_constVSub
  条件: (p : P)
  证明: by
  ext
  rfl
-/
theorem symm_constVSub (p : P) :
    (constVSub 𝕜 p).symm =
      (LinearIsometryEquiv.neg 𝕜).toAffineIsometryEquiv.trans (vaddConst 𝕜 p) := by
  ext
  rfl

variable (𝕜 P) in
/--
Definition of `constVAdd` / `constVAdd` 的定义

English:
definition constVAdd
  signature: (v : V)
  body: { AffineEquiv.constVAdd 𝕜 P v with norm_map := fun _ => rfl }

@[simp]

中文:
定义 constVAdd
  签名: (v : V)
  定义体: { AffineEquiv.constVAdd 𝕜 P v with norm_map := fun _ => rfl }

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.constVAdd, constVAdd, norm_map
-/
def constVAdd (v : V) : P ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.constVAdd 𝕜 P v with norm_map := fun _ => rfl }

@[simp]
/--
theorem `coe_constVAdd` / 定理 `coe_constVAdd`

English:
theorem coe_constVAdd
  given: (v : V)
  statement: ⇑(constVAdd 𝕜 P v : P ≃ᵃⁱ[𝕜] P) = (v +ᵥ ·)
  proof: rfl

@[simp]

中文:
定理 coe_constVAdd
  条件: (v : V)
  结论: ⇑(constVAdd 𝕜 P v : P ≃ᵃⁱ[𝕜] P) = (v +ᵥ ·)
  证明: rfl

@[simp]
-/
theorem coe_constVAdd (v : V) : ⇑(constVAdd 𝕜 P v : P ≃ᵃⁱ[𝕜] P) = (v +ᵥ ·) :=
  rfl

@[simp]
/--
theorem `constVAdd_zero` / 定理 `constVAdd_zero`

English:
theorem constVAdd_zero
  statement: constVAdd 𝕜 P (0 : V) = refl 𝕜 P
  proof: ext zero_vadd V

include 𝕜 in

中文:
定理 constVAdd_zero
  结论: constVAdd 𝕜 P (0 : V) = refl 𝕜 P
  证明: ext zero_vadd V

include 𝕜 in

Depends on / 依赖: zero_vadd
-/
theorem constVAdd_zero : constVAdd 𝕜 P (0 : V) = refl 𝕜 P :=
ext zero_vadd V

include 𝕜 in
/--
theorem `vadd_vsub` / 定理 `vadd_vsub`

English:
theorem vadd_vsub
  statement: {f : P -> P₂} (hf : Isometry f) {p : P} {g : V -> V₂}
  proof: by
  convert! (vaddConst 𝕜 (f p)).symm.isometry.comp (hf.comp (vaddConst 𝕜 p).isometry)
  exact funext hg

中文:
定理 vadd_vsub
  结论: {f : P -> P₂} (hf : 等距 f) {p : P} {g : V -> V₂}
  证明: by
  convert! (vaddConst 𝕜 (f p)).symm.isometry.comp (hf.comp (vaddConst 𝕜 p).isometry)
  exact funext hg

Depends on / 依赖: convert, hf.comp, isometry, symm.isometry.comp, vaddConst
-/
theorem vadd_vsub {f : P -> P₂} (hf : Isometry f) {p : P} {g : V -> V₂}
    (hg : forall v, g v = f (v +ᵥ p) -ᵥ f p) : Isometry g := by
  convert! (vaddConst 𝕜 (f p)).symm.isometry.comp (hf.comp (vaddConst 𝕜 p).isometry)
  exact funext hg

variable (𝕜) in
/--
Definition of `pointReflection` / `pointReflection` 的定义

English:
definition pointReflection
  signature: (x : P)
  body: (constVSub 𝕜 x).trans (vaddConst 𝕜 x)

中文:
定义 pointReflection
  签名: (x : P)
  定义体: (constVSub 𝕜 x).trans (vaddConst 𝕜 x)

Depends on / 依赖: constVSub, vaddConst
-/
def pointReflection (x : P) : P ≃ᵃⁱ[𝕜] P :=
  (constVSub 𝕜 x).trans (vaddConst 𝕜 x)

/--
theorem `pointReflection_apply` / 定理 `pointReflection_apply`

English:
theorem pointReflection_apply
  given: (x y : P)
  statement: (pointReflection 𝕜 x) y = (x -ᵥ y) +ᵥ x
  proof: rfl

@[simp]

中文:
定理 pointReflection_apply
  条件: (x y : P)
  结论: (pointReflection 𝕜 x) y = (x -ᵥ y) +ᵥ x
  证明: rfl

@[simp]
-/
theorem pointReflection_apply (x y : P) : (pointReflection 𝕜 x) y = (x -ᵥ y) +ᵥ x :=
  rfl

@[simp]
/--
theorem `pointReflection_toAffineEquiv` / 定理 `pointReflection_toAffineEquiv`

English:
theorem pointReflection_toAffineEquiv
  given: (x : P)
  proof: rfl

@[simp]

中文:
定理 pointReflection_toAffineEquiv
  条件: (x : P)
  证明: rfl

@[simp]
-/
theorem pointReflection_toAffineEquiv (x : P) :
    (pointReflection 𝕜 x).toAffineEquiv = AffineEquiv.pointReflection 𝕜 x :=
  rfl

@[simp]
/--
theorem `pointReflection_self` / 定理 `pointReflection_self`

English:
theorem pointReflection_self
  given: (x : P)
  statement: pointReflection 𝕜 x x = x
  proof: AffineEquiv.pointReflection_self 𝕜 x

中文:
定理 pointReflection_self
  条件: (x : P)
  结论: pointReflection 𝕜 x x = x
  证明: AffineEquiv.pointReflection_self 𝕜 x

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection_self, pointReflection_self
-/
theorem pointReflection_self (x : P) : pointReflection 𝕜 x x = x :=
  AffineEquiv.pointReflection_self 𝕜 x

/--
theorem `pointReflection_involutive` / 定理 `pointReflection_involutive`

English:
theorem pointReflection_involutive
  given: (x : P)
  statement: Function.Involutive (pointReflection 𝕜 x)
  proof: Equiv.pointReflection_involutive x

@[simp]

中文:
定理 pointReflection_involutive
  条件: (x : P)
  结论: 函数.对合 (pointReflection 𝕜 x)
  证明: Equiv.pointReflection_involutive x

@[simp]

Depends on / 依赖: Equiv.pointReflection_involutive, pointReflection_involutive
-/
theorem pointReflection_involutive (x : P) : Function.Involutive (pointReflection 𝕜 x) :=
  Equiv.pointReflection_involutive x

@[simp]
/--
theorem `pointReflection_symm` / 定理 `pointReflection_symm`

English:
theorem pointReflection_symm
  given: (x : P)
  statement: (pointReflection 𝕜 x).symm = pointReflection 𝕜 x
  proof: toAffineEquiv_injective AffineEquiv.pointReflection_symm 𝕜 x

@[simp]

中文:
定理 pointReflection_symm
  条件: (x : P)
  结论: (pointReflection 𝕜 x).symm = pointReflection 𝕜 x
  证明: toAffineEquiv_injective AffineEquiv.pointReflection_symm 𝕜 x

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection_symm, pointReflection_symm, toAffineEquiv_injective
-/
theorem pointReflection_symm (x : P) : (pointReflection 𝕜 x).symm = pointReflection 𝕜 x :=
toAffineEquiv_injective AffineEquiv.pointReflection_symm 𝕜 x

@[simp]
/--
theorem `dist_pointReflection_fixed` / 定理 `dist_pointReflection_fixed`

English:
theorem dist_pointReflection_fixed
  given: (x y : P)
  statement: dist (pointReflection 𝕜 x y) x = dist y x
  proof: by
  rw [← (pointReflection 𝕜 x).dist_map y x]; rw [pointReflection_self]

中文:
定理 dist_pointReflection_fixed
  条件: (x y : P)
  结论: dist (pointReflection 𝕜 x y) x = dist y x
  证明: by
  rw [← (pointReflection 𝕜 x).dist_map y x]; rw [pointReflection_self]

Depends on / 依赖: dist_map, pointReflection, pointReflection_self
-/
theorem dist_pointReflection_fixed (x y : P) : dist (pointReflection 𝕜 x y) x = dist y x := by
  rw [← (pointReflection 𝕜 x).dist_map y x]; rw [pointReflection_self]

/--
theorem `dist_pointReflection_self'` / 定理 `dist_pointReflection_self'`

English:
theorem dist_pointReflection_self'
  given: (x y : P)
  proof: by
  rw [pointReflection_apply]; rw [dist_eq_norm_vsub V]; rw [vadd_vsub_assoc]; rw [two_nsmul]

中文:
定理 dist_pointReflection_self'
  条件: (x y : P)
  证明: by
  rw [pointReflection_apply]; rw [dist_eq_norm_vsub V]; rw [vadd_vsub_assoc]; rw [two_nsmul]

Depends on / 依赖: dist_eq_norm_vsub, pointReflection_apply, two_nsmul, vadd_vsub_assoc
-/
theorem dist_pointReflection_self' (x y : P) :
    dist (pointReflection 𝕜 x y) y = ‖2 • (x -ᵥ y)‖ := by
  rw [pointReflection_apply]; rw [dist_eq_norm_vsub V]; rw [vadd_vsub_assoc]; rw [two_nsmul]

/--
theorem `dist_pointReflection_self` / 定理 `dist_pointReflection_self`

English:
theorem dist_pointReflection_self
  given: (x y : P)
  proof: by
  rw [dist_pointReflection_self']; rw [two_nsmul]; rw [← two_smul 𝕜]; rw [norm_smul]; rw [← dist_eq_norm_vsub V]

中文:
定理 dist_pointReflection_self
  条件: (x y : P)
  证明: by
  rw [dist_pointReflection_self']; rw [two_nsmul]; rw [← two_smul 𝕜]; rw [norm_smul]; rw [← dist_eq_norm_vsub V]

Depends on / 依赖: dist_eq_norm_vsub, dist_pointReflection_self, norm_smul, two_nsmul, two_smul
-/
theorem dist_pointReflection_self (x y : P) :
    dist (pointReflection 𝕜 x y) y = ‖(2 : 𝕜)‖ * dist x y := by
  rw [dist_pointReflection_self']; rw [two_nsmul]; rw [← two_smul 𝕜]; rw [norm_smul]; rw [← dist_eq_norm_vsub V]

/--
theorem `pointReflection_fixed_iff` / 定理 `pointReflection_fixed_iff`

English:
theorem pointReflection_fixed_iff
  given: [Invertible (2 : 𝕜)] {x y : P}
  proof: AffineEquiv.pointReflection_fixed_iff_of_module 𝕜

中文:
定理 pointReflection_fixed_iff
  条件: [可逆 (2 : 𝕜)] {x y : P}
  证明: AffineEquiv.pointReflection_fixed_iff_of_module 𝕜

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection_fixed_iff_of_module, pointReflection_fixed_iff_of_module
-/
theorem pointReflection_fixed_iff [Invertible (2 : 𝕜)] {x y : P} :
    pointReflection 𝕜 x y = y ↔ y = x :=
  AffineEquiv.pointReflection_fixed_iff_of_module 𝕜

variable [NormedSpace Real V]

/--
theorem `dist_pointReflection_self_real` / 定理 `dist_pointReflection_self_real`

English:
theorem dist_pointReflection_self_real
  given: (x y : P)
  proof: by
  rw [dist_pointReflection_self]; rw [Real.norm_two]

@[simp]

中文:
定理 dist_pointReflection_self_real
  条件: (x y : P)
  证明: by
  rw [dist_pointReflection_self]; rw [Real.norm_two]

@[simp]

Depends on / 依赖: Real.norm_two, dist_pointReflection_self, norm_two
-/
theorem dist_pointReflection_self_real (x y : P) :
    dist (pointReflection Real x y) y = 2 * dist x y := by
  rw [dist_pointReflection_self]; rw [Real.norm_two]

@[simp]
/--
theorem `pointReflection_midpoint_left` / 定理 `pointReflection_midpoint_left`

English:
theorem pointReflection_midpoint_left
  given: (x y : P)
  statement: pointReflection Real (midpoint Real x y) x = y
  proof: AffineEquiv.pointReflection_midpoint_left x y

@[simp]

中文:
定理 pointReflection_midpoint_left
  条件: (x y : P)
  结论: pointReflection 实数 (midpoint 实数 x y) x = y
  证明: AffineEquiv.pointReflection_midpoint_left x y

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection_midpoint_left, pointReflection_midpoint_left
-/
theorem pointReflection_midpoint_left (x y : P) : pointReflection Real (midpoint Real x y) x = y :=
  AffineEquiv.pointReflection_midpoint_left x y

@[simp]
/--
theorem `pointReflection_midpoint_right` / 定理 `pointReflection_midpoint_right`

English:
theorem pointReflection_midpoint_right
  given: (x y : P)
  statement: pointReflection Real (midpoint Real x y) y = x
  proof: AffineEquiv.pointReflection_midpoint_right x y

中文:
定理 pointReflection_midpoint_right
  条件: (x y : P)
  结论: pointReflection 实数 (midpoint 实数 x y) y = x
  证明: AffineEquiv.pointReflection_midpoint_right x y

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection_midpoint_right, pointReflection_midpoint_right
-/
theorem pointReflection_midpoint_right (x y : P) : pointReflection Real (midpoint Real x y) y = x :=
  AffineEquiv.pointReflection_midpoint_right x y

end Constructions

end AffineIsometryEquiv

namespace AffineSubspace

/-- An affine subspace is isomorphic to its image under an injective affine map.
This is the affine version of `Submodule.equivMapOfInjective`.
-/
@[simps linear, simps! toFun]
/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (E : AffineSubspace 𝕜 P₁) [Nonempty E] (φ : P₁ ->ᵃ[𝕜] P₂)
  body: { Equiv.Set.image _ (E : Set P₁) hφ with
    linear :=
      (E.direction.equivMapOfInjective φ.linear (φ.linear_injective_iff.mpr hφ)).trans
        (LinearEquiv.ofEq _ _ (AffineSubspace.map_direction _ _).symm)
map_vadd' := fun p v => Subtype.ext φ.map_vadd p v }

中文:
定义 equivMapOfInjective
  签名: (E : 仿射子空间 𝕜 P₁) [非空 E] (φ : P₁ ->ᵃ[𝕜] P₂)
  定义体: { Equiv.Set.image _ (E : Set P₁) hφ with
    linear :=
      (E.direction.equivMapOfInjective φ.linear (φ.linear_injective_iff.mpr hφ)).trans
        (LinearEquiv.ofEq _ _ (AffineSubspace.map_direction _ _).symm)
map_vadd' := fun p v => Subtype.ext φ.map_vadd p v }

Depends on / 依赖: AffineSubspace, AffineSubspace.map_direction, E.direction.equivMapOfInjective, Equiv.Set.image, LinearEquiv, LinearEquiv.ofEq, Subtype, Subtype.ext, direction, equivMapOfInjective, linear, linear_injective_iff, linear_injective_iff.mpr, map_direction, map_vadd
-/
noncomputable def equivMapOfInjective (E : AffineSubspace 𝕜 P₁) [Nonempty E] (φ : P₁ ->ᵃ[𝕜] P₂)
    (hφ : Function.Injective φ) : E ≃ᵃ[𝕜] E.map φ :=
  { Equiv.Set.image _ (E : Set P₁) hφ with
    linear :=
      (E.direction.equivMapOfInjective φ.linear (φ.linear_injective_iff.mpr hφ)).trans
        (LinearEquiv.ofEq _ _ (AffineSubspace.map_direction _ _).symm)
map_vadd' := fun p v => Subtype.ext φ.map_vadd p v }

/--
Definition of `isometryEquivMap` / `isometryEquivMap` 的定义

English:
definition isometryEquivMap
  signature: (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty E]
  body: ⟨E.equivMapOfInjective φ.toAffineMap φ.injective, fun _ => φ.norm_map _⟩

@[simp]

中文:
定义 isometryEquivMap
  签名: (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : 仿射子空间 𝕜 P₁') [非空 E]
  定义体: ⟨E.equivMapOfInjective φ.toAffineMap φ.injective, fun _ => φ.norm_map _⟩

@[simp]

Depends on / 依赖: E.equivMapOfInjective, equivMapOfInjective, injective, norm_map, toAffineMap
-/
noncomputable def isometryEquivMap (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty E] :
    E ≃ᵃⁱ[𝕜] E.map φ.toAffineMap :=
  ⟨E.equivMapOfInjective φ.toAffineMap φ.injective, fun _ => φ.norm_map _⟩

@[simp]
/--
theorem `isometryEquivMap.apply_symm_apply` / 定理 `isometryEquivMap.apply_symm_apply`

English:
theorem isometryEquivMap.apply_symm_apply
  statement: {E : AffineSubspace 𝕜 P₁'} [Nonempty E]
  proof: congr_arg Subtype.val (E.isometryEquivMap φ).apply_symm_apply _

@[simp]

中文:
定理 isometryEquivMap.apply_symm_apply
  结论: {E : 仿射子空间 𝕜 P₁'} [非空 E]
  证明: congr_arg Subtype.val (E.isometryEquivMap φ).apply_symm_apply _

@[simp]

Depends on / 依赖: E.isometryEquivMap, Subtype, Subtype.val, apply_symm_apply, congr_arg, isometryEquivMap
-/
theorem isometryEquivMap.apply_symm_apply {E : AffineSubspace 𝕜 P₁'} [Nonempty E]
    {φ : P₁' ->ᵃⁱ[𝕜] P₂} (x : E.map φ.toAffineMap) : φ ((E.isometryEquivMap φ).symm x) = x :=
congr_arg Subtype.val (E.isometryEquivMap φ).apply_symm_apply _

@[simp]
/--
theorem `isometryEquivMap.coe_apply` / 定理 `isometryEquivMap.coe_apply`

English:
theorem isometryEquivMap.coe_apply
  statement: (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty E]
  proof: rfl

@[simp]

中文:
定理 isometryEquivMap.coe_apply
  结论: (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : 仿射子空间 𝕜 P₁') [非空 E]
  证明: rfl

@[simp]
-/
theorem isometryEquivMap.coe_apply (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty E]
    (g : E) : ↑(E.isometryEquivMap φ g) = φ g :=
  rfl

@[simp]
/--
theorem `isometryEquivMap.toAffineMap_eq` / 定理 `isometryEquivMap.toAffineMap_eq`

English:
theorem isometryEquivMap.toAffineMap_eq
  statement: (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁')
  proof: rfl

中文:
定理 isometryEquivMap.toAffineMap_eq
  结论: (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : 仿射子空间 𝕜 P₁')
  证明: rfl
-/
theorem isometryEquivMap.toAffineMap_eq (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁')
    [Nonempty E] :
    (E.isometryEquivMap φ).toAffineMap = E.equivMapOfInjective φ.toAffineMap φ.injective :=
  rfl

end AffineSubspace
