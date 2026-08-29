/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Star.Basic -- shake: keep (used in `notation` only)
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# (Semi-)linear isometries

In this file we define `LinearIsometry σ₁₂ E E₂` (notation: `E →ₛₗᵢ[σ₁₂] E₂`) to be a semilinear
isometric embedding of `E` into `E₂` and `LinearIsometryEquiv` (notation: `E ≃ₛₗᵢ[σ₁₂] E₂`) to be
a semilinear isometric equivalence between `E` and `E₂`. The notation for the associated purely
linear concepts is `E →ₗᵢ[R] E₂`, `E ≃ₗᵢ[R] E₂`, and `E →ₗᵢ⋆[R] E₂`, `E ≃ₗᵢ⋆[R] E₂` for
the star-linear versions.

We also prove some trivial lemmas and provide convenience constructors.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup` and we specialize to `NormedAddCommGroup` when needed.
-/

@[expose] public section

open Function Set Topology

variable {R R₂ R₃ R₄ E E₂ E₃ E₄ F 𝓕 : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R} {σ₁₃ : R ->+* R₃} {σ₃₁ : R₃ ->+* R} {σ₁₄ : R ->+* R₄}
  {σ₄₁ : R₄ ->+* R} {σ₂₃ : R₂ ->+* R₃} {σ₃₂ : R₃ ->+* R₂} {σ₂₄ : R₂ ->+* R₄} {σ₄₂ : R₄ ->+* R₂}
  {σ₃₄ : R₃ ->+* R₄} {σ₄₃ : R₄ ->+* R₃} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃] [RingHomInvPair σ₂₃ σ₃₂]
  [RingHomInvPair σ₃₂ σ₂₃] [RingHomInvPair σ₁₄ σ₄₁] [RingHomInvPair σ₄₁ σ₁₄]
  [RingHomInvPair σ₂₄ σ₄₂] [RingHomInvPair σ₄₂ σ₂₄] [RingHomInvPair σ₃₄ σ₄₃]
  [RingHomInvPair σ₄₃ σ₃₄] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
  [RingHomCompTriple σ₄₂ σ₂₁ σ₄₁] [RingHomCompTriple σ₄₃ σ₃₂ σ₄₂] [RingHomCompTriple σ₄₃ σ₃₁ σ₄₁]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup E₃]
  [SeminormedAddCommGroup E₄] [Module R E] [Module R₂ E₂] [Module R₃ E₃] [Module R₄ E₄]
  [NormedAddCommGroup F] [Module R F]

/--
Definition of `LinearIsometry` / `LinearIsometry` 的定义

English:
structure LinearIsometry
  parameters: (σ₁₂ : R ->+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
  extends: E ->ₛₗ[σ₁₂] E₂
  axioms and operations (1):
    - norm_map' : forall x, ‖toLinearMap x‖ = ‖x‖

中文:
结构 LinearIsometry
  参数: (σ₁₂ : R ->+* R₂) (E E₂ : 类型) [SeminormedAddCommGroup E]
  继承: E ->ₛₗ[σ₁₂] E₂
  公理与运算 (1 个):
    - norm_map' : 对任意 x, ‖toLinearMap x‖ = ‖x‖
-/
structure LinearIsometry (σ₁₂ : R ->+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] extends E ->ₛₗ[σ₁₂] E₂ where
  norm_map' : forall x, ‖toLinearMap x‖ = ‖x‖

@[inherit_doc]
notation:25 E " ->ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometry σ₁₂ E E₂

/-- A linear isometric embedding of a normed `R`-module into another one. -/
notation:25 E " ->ₗᵢ[" R:25 "] " E₂:0 => LinearIsometry (RingHom.id R) E E₂

/-- An antilinear isometric embedding of a normed `R`-module into another one. -/
notation:25 E " ->ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometry (starRingEnd R) E E₂

/--
Definition of `SemilinearIsometryClass` / `SemilinearIsometryClass` 的定义

English:
class SemilinearIsometryClass
  parameters: (𝓕 : Type*) {R R₂ : outParam Type*} [Semiring R] [Semiring R₂]
  extends: SemilinearMapClass 𝓕 σ₁₂ E E₂
  axioms and operations (1):
    - norm_map : forall (f : 𝓕) (x : E), ‖f x‖ = ‖x‖

中文:
类 SemilinearIsometryClass
  参数: (𝓕 : 类型) {R R₂ : outParam 类型} [Semiring R] [Semiring R₂]
  继承: SemilinearMapClass 𝓕 σ₁₂ E E₂
  公理与运算 (1 个):
    - norm_map : 对任意 (f : 𝓕) (x : E), ‖f x‖ = ‖x‖
-/
class SemilinearIsometryClass (𝓕 : Type*) {R R₂ : outParam Type*} [Semiring R] [Semiring R₂]
    (σ₁₂ : outParam <| R ->+* R₂) (E E₂ : outParam Type*) [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] [FunLike 𝓕 E E₂] : Prop
    extends SemilinearMapClass 𝓕 σ₁₂ E E₂ where
  norm_map : forall (f : 𝓕) (x : E), ‖f x‖ = ‖x‖

/--
Definition of `LinearIsometryClass` / `LinearIsometryClass` 的定义

English:
abbreviation LinearIsometryClass
  signature: (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R]
  body: SemilinearIsometryClass 𝓕 (RingHom.id R) E E₂

中文:
缩写 LinearIsometryClass
  签名: (𝓕 : 类型) (R E E₂ : outParam 类型) [Semiring R]
  定义体: SemilinearIsometryClass 𝓕 (RingHom.id R) E E₂

Depends on / 依赖: RingHom, RingHom.id, SemilinearIsometryClass
-/
abbrev LinearIsometryClass (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R E₂]
    [FunLike 𝓕 E E₂] :=
  SemilinearIsometryClass 𝓕 (RingHom.id R) E E₂

namespace SemilinearIsometryClass

variable [FunLike 𝓕 E E₂]

/--
theorem `isometry` / 定理 `isometry`

English:
theorem isometry
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  statement: Isometry f
  proof: AddMonoidHomClass.isometry_of_norm _ (norm_map _)

@[continuity]

中文:
定理 isometry
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  结论: Isometry f
  证明: AddMonoidHomClass.isometry_of_norm _ (norm_map _)

@[continuity]
-/
protected theorem isometry [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Isometry f :=
  AddMonoidHomClass.isometry_of_norm _ (norm_map _)

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  statement: Continuous f
  proof: (SemilinearIsometryClass.isometry f).continuous

中文:
定理 continuous
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  结论: Continuous f
  证明: (SemilinearIsometryClass.isometry f).continuous
-/
protected theorem continuous [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Continuous f :=
  (SemilinearIsometryClass.isometry f).continuous

-- Should be `@[simp]` but it doesn't fire due to https://github.com/leanprover/lean4/issues/3107.
/--
theorem `nnnorm_map` / 定理 `nnnorm_map`

English:
theorem nnnorm_map
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (x : E)
  statement: ‖f x‖₊ = ‖x‖₊
  proof: NNReal.eq norm_map f x

中文:
定理 nnnorm_map
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (x : E)
  结论: ‖f x‖₊ = ‖x‖₊
  证明: NNReal.eq norm_map f x

Depends on / 依赖: NNReal, NNReal.eq, norm_map
-/
theorem nnnorm_map [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (x : E) : ‖f x‖₊ = ‖x‖₊ :=
NNReal.eq norm_map f x

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  statement: LipschitzWith 1 f
  proof: (SemilinearIsometryClass.isometry f).lipschitz

中文:
定理 lipschitz
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  结论: LipschitzWith 1 f
  证明: (SemilinearIsometryClass.isometry f).lipschitz
-/
protected theorem lipschitz [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : LipschitzWith 1 f :=
  (SemilinearIsometryClass.isometry f).lipschitz

/--
theorem `antilipschitz` / 定理 `antilipschitz`

English:
theorem antilipschitz
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  proof: (SemilinearIsometryClass.isometry f).antilipschitz

中文:
定理 antilipschitz
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  证明: (SemilinearIsometryClass.isometry f).antilipschitz
-/
protected theorem antilipschitz [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    AntilipschitzWith 1 f :=
  (SemilinearIsometryClass.isometry f).antilipschitz

/--
theorem `ediam_image` / 定理 `ediam_image`

English:
theorem ediam_image
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E)
  proof: (SemilinearIsometryClass.isometry f).ediam_image s

中文:
定理 ediam_image
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E)
  证明: (SemilinearIsometryClass.isometry f).ediam_image s

Depends on / 依赖: SemilinearIsometryClass, SemilinearIsometryClass.isometry, ediam_image, isometry
-/
theorem ediam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) :
    Metric.ediam (f '' s) = Metric.ediam s :=
  (SemilinearIsometryClass.isometry f).ediam_image s

/--
theorem `ediam_range` / 定理 `ediam_range`

English:
theorem ediam_range
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  proof: (SemilinearIsometryClass.isometry f).ediam_range

中文:
定理 ediam_range
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  证明: (SemilinearIsometryClass.isometry f).ediam_range

Depends on / 依赖: SemilinearIsometryClass, SemilinearIsometryClass.isometry, ediam_range, isometry
-/
theorem ediam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    Metric.ediam (range f) = Metric.ediam (univ : Set E) :=
  (SemilinearIsometryClass.isometry f).ediam_range

/--
theorem `diam_image` / 定理 `diam_image`

English:
theorem diam_image
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E)
  proof: (SemilinearIsometryClass.isometry f).diam_image s

中文:
定理 diam_image
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E)
  证明: (SemilinearIsometryClass.isometry f).diam_image s

Depends on / 依赖: SemilinearIsometryClass, SemilinearIsometryClass.isometry, diam_image, isometry
-/
theorem diam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) :
    Metric.diam (f '' s) = Metric.diam s :=
  (SemilinearIsometryClass.isometry f).diam_image s

/--
theorem `diam_range` / 定理 `diam_range`

English:
theorem diam_range
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  proof: (SemilinearIsometryClass.isometry f).diam_range

中文:
定理 diam_range
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕)
  证明: (SemilinearIsometryClass.isometry f).diam_range

Depends on / 依赖: SemilinearIsometryClass, SemilinearIsometryClass.isometry, diam_range, isometry
-/
theorem diam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    Metric.diam (range f) = Metric.diam (univ : Set E) :=
  (SemilinearIsometryClass.isometry f).diam_range

instance (priority := 100) toContinuousSemilinearMapClass
    [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] : ContinuousSemilinearMapClass 𝓕 σ₁₂ E E₂ where
  map_continuous := SemilinearIsometryClass.continuous

instance (priority := 100) toIsometryClass [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] :
    IsometryClass 𝓕 E E₂ where
  isometry := SemilinearIsometryClass.isometry

end SemilinearIsometryClass

namespace LinearIsometry

variable (f : E ->ₛₗᵢ[σ₁₂] E₂) (f₁ : F ->ₛₗᵢ[σ₁₂] E₂)

/--
theorem `toLinearMap_injective` / 定理 `toLinearMap_injective`

English:
theorem toLinearMap_injective
  statement: Injective (toLinearMap : (E ->ₛₗᵢ[σ₁₂] E₂) -> E ->ₛₗ[σ₁₂] E₂)

中文:
定理 toLinearMap_injective
  结论: Injective (toLinearMap : (E ->ₛₗᵢ[σ₁₂] E₂) -> E ->ₛₗ[σ₁₂] E₂)
-/
theorem toLinearMap_injective : Injective (toLinearMap : (E ->ₛₗᵢ[σ₁₂] E₂) -> E ->ₛₗ[σ₁₂] E₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp]
/--
theorem `toLinearMap_inj` / 定理 `toLinearMap_inj`

English:
theorem toLinearMap_inj
  given: {f g : E ->ₛₗᵢ[σ₁₂] E₂}
  statement: f.toLinearMap = g.toLinearMap ↔ f = g
  proof: toLinearMap_injective.eq_iff

中文:
定理 toLinearMap_inj
  条件: {f g : E ->ₛₗᵢ[σ₁₂] E₂}
  结论: f.toLinearMap = g.toLinearMap ↔ f = g
  证明: toLinearMap_injective.eq_iff

Depends on / 依赖: eq_iff, toLinearMap_injective, toLinearMap_injective.eq_iff
-/
theorem toLinearMap_inj {f g : E ->ₛₗᵢ[σ₁₂] E₂} : f.toLinearMap = g.toLinearMap ↔ f = g :=
  toLinearMap_injective.eq_iff

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (E ->ₛₗᵢ[σ₁₂] E₂) E E₂ where
  body: f.toFun
  coe_injective _ _ h := toLinearMap_injective (DFunLike.coe_injective h)

中文:
实例 instFunLike
  签名: : FunLike (E ->ₛₗᵢ[σ₁₂] E₂) E E₂ where
  定义体: f.toFun
  coe_injective _ _ h := toLinearMap_injective (DFunLike.coe_injective h)

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (E ->ₛₗᵢ[σ₁₂] E₂) E E₂ where
  coe f := f.toFun
  coe_injective _ _ h := toLinearMap_injective (DFunLike.coe_injective h)

/--
Instance `instSemilinearIsometryClass` / 实例 `instSemilinearIsometryClass`

English:
instance instSemilinearIsometryClass
  signature: : SemilinearIsometryClass (E ->ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  body: map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap
  norm_map f := f.norm_map'

@[simp]

中文:
实例 instSemilinearIsometryClass
  签名: : SemilinearIsometryClass (E ->ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  定义体: map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap
  norm_map f := f.norm_map'

@[simp]

Depends on / 依赖: f.toLinearMap, map_add, toLinearMap
-/
instance instSemilinearIsometryClass : SemilinearIsometryClass (E ->ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap
  norm_map f := f.norm_map'

@[simp]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  statement: ⇑f.toLinearMap = f
  proof: rfl

@[simp]

中文:
定理 coe_toLinearMap
  结论: ⇑f.toLinearMap = f
  证明: rfl

@[simp]
-/
theorem coe_toLinearMap : ⇑f.toLinearMap = f :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : E ->ₛₗ[σ₁₂] E₂) (hf)
  statement: ⇑(mk f hf) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : E ->ₛₗ[σ₁₂] E₂) (hf)
  结论: ⇑(mk f hf) = f
  证明: rfl
-/
theorem coe_mk (f : E ->ₛₗ[σ₁₂] E₂) (hf) : ⇑(mk f hf) = f :=
  rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Injective (E ->ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (fun f => f)
  proof: by
  rintro ⟨_⟩ ⟨_⟩
  simp

中文:
定理 coe_injective
  结论: @Injective (E ->ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (fun f => f)
  证明: by
  rintro ⟨_⟩ ⟨_⟩
  simp
-/
theorem coe_injective : @Injective (E ->ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (fun f => f) := by
  rintro ⟨_⟩ ⟨_⟩
  simp

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (σ₁₂ : R ->+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
  body: h

initialize_simps_projections LinearIsometry (toFun -> apply)

@[ext]

中文:
定义 Simps.apply
  签名: (σ₁₂ : R ->+* R₂) (E E₂ : 类型) [SeminormedAddCommGroup E]
  定义体: h

initialize_simps_projections LinearIsometry (toFun -> apply)

@[ext]
-/
def Simps.apply (σ₁₂ : R ->+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] (h : E ->ₛₗᵢ[σ₁₂] E₂) : E -> E₂ :=
  h

initialize_simps_projections LinearIsometry (toFun -> apply)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : E ->ₛₗᵢ[σ₁₂] E₂} (h : forall x, f x = g x)
  statement: f = g
  proof: coe_injective funext h

中文:
定理 ext
  条件: {f g : E ->ₛₗᵢ[σ₁₂] E₂} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: coe_injective funext h

Depends on / 依赖: coe_injective
-/
theorem ext {f g : E ->ₛₗᵢ[σ₁₂] E₂} (h : forall x, f x = g x) : f = g :=
coe_injective funext h

variable [FunLike 𝓕 E E₂]

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: f 0 = 0
  proof: f.toLinearMap.map_zero

中文:
定理 map_zero
  结论: f 0 = 0
  证明: f.toLinearMap.map_zero
-/
protected theorem map_zero : f 0 = 0 :=
  f.toLinearMap.map_zero

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (x y : E)
  statement: f (x + y) = f x + f y
  proof: f.toLinearMap.map_add x y

中文:
定理 map_add
  条件: (x y : E)
  结论: f (x + y) = f x + f y
  证明: f.toLinearMap.map_add x y
-/
protected theorem map_add (x y : E) : f (x + y) = f x + f y :=
  f.toLinearMap.map_add x y

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (x : E)
  statement: f (-x) = -f x
  proof: f.toLinearMap.map_neg x

中文:
定理 map_neg
  条件: (x : E)
  结论: f (-x) = -f x
  证明: f.toLinearMap.map_neg x
-/
protected theorem map_neg (x : E) : f (-x) = -f x :=
  f.toLinearMap.map_neg x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (x y : E)
  statement: f (x - y) = f x - f y
  proof: f.toLinearMap.map_sub x y

中文:
定理 map_sub
  条件: (x y : E)
  结论: f (x - y) = f x - f y
  证明: f.toLinearMap.map_sub x y
-/
protected theorem map_sub (x y : E) : f (x - y) = f x - f y :=
  f.toLinearMap.map_sub x y

/--
theorem `map_smulₛₗ` / 定理 `map_smulₛₗ`

English:
theorem map_smulₛₗ
  given: (c : R) (x : E)
  statement: f (c • x) = σ₁₂ c • f x
  proof: f.toLinearMap.map_smulₛₗ c x

中文:
定理 map_smulₛₗ
  条件: (c : R) (x : E)
  结论: f (c • x) = σ₁₂ c • f x
  证明: f.toLinearMap.map_smulₛₗ c x
-/
protected theorem map_smulₛₗ (c : R) (x : E) : f (c • x) = σ₁₂ c • f x :=
  f.toLinearMap.map_smulₛₗ c x

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: [Module R E₂] (f : E ->ₗᵢ[R] E₂) (c : R) (x : E)
  statement: f (c • x) = c • f x
  proof: f.toLinearMap.map_smul c x

中文:
定理 map_smul
  条件: [Module R E₂] (f : E ->ₗᵢ[R] E₂) (c : R) (x : E)
  结论: f (c • x) = c • f x
  证明: f.toLinearMap.map_smul c x
-/
protected theorem map_smul [Module R E₂] (f : E ->ₗᵢ[R] E₂) (c : R) (x : E) : f (c • x) = c • f x :=
  f.toLinearMap.map_smul c x

/--
lemma `norm_map` / 引理 `norm_map`

English:
lemma norm_map
  given: (x : E)
  statement: ‖f x‖ = ‖x‖
  proof: by simp

中文:
引理 norm_map
  条件: (x : E)
  结论: ‖f x‖ = ‖x‖
  证明: by simp
-/
protected lemma norm_map (x : E) : ‖f x‖ = ‖x‖ := by simp
/--
lemma `nnnorm_map` / 引理 `nnnorm_map`

English:
lemma nnnorm_map
  given: (x : E)
  statement: ‖f x‖₊ = ‖x‖₊
  proof: by simp

中文:
引理 nnnorm_map
  条件: (x : E)
  结论: ‖f x‖₊ = ‖x‖₊
  证明: by simp
-/
protected lemma nnnorm_map (x : E) : ‖f x‖₊ = ‖x‖₊ := by simp
/--
lemma `enorm_map` / 引理 `enorm_map`

English:
lemma enorm_map
  given: (x : E)
  statement: ‖f x‖ₑ = ‖x‖ₑ
  proof: by simp

中文:
引理 enorm_map
  条件: (x : E)
  结论: ‖f x‖ₑ = ‖x‖ₑ
  证明: by simp
-/
protected lemma enorm_map (x : E) : ‖f x‖ₑ = ‖x‖ₑ := by simp

/--
theorem `isometry` / 定理 `isometry`

English:
theorem isometry
  statement: Isometry f
  proof: AddMonoidHomClass.isometry_of_norm f.toLinearMap f.norm_map

中文:
定理 isometry
  结论: Isometry f
  证明: AddMonoidHomClass.isometry_of_norm f.toLinearMap f.norm_map
-/
protected theorem isometry : Isometry f :=
  AddMonoidHomClass.isometry_of_norm f.toLinearMap f.norm_map

/--
lemma `isEmbedding` / 引理 `isEmbedding`

English:
lemma isEmbedding
  given: (f : F ->ₛₗᵢ[σ₁₂] E₂)
  statement: IsEmbedding f
  proof: f.isometry.isEmbedding

@[simp]

中文:
引理 isEmbedding
  条件: (f : F ->ₛₗᵢ[σ₁₂] E₂)
  结论: IsEmbedding f
  证明: f.isometry.isEmbedding

@[simp]

Depends on / 依赖: f.isometry.isEmbedding, isEmbedding, isometry
-/
lemma isEmbedding (f : F ->ₛₗᵢ[σ₁₂] E₂) : IsEmbedding f := f.isometry.isEmbedding

@[simp]
/--
theorem `isComplete_image_iff` / 定理 `isComplete_image_iff`

English:
theorem isComplete_image_iff
  given: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) {s : Set E}
  proof: _root_.isComplete_image_iff (SemilinearIsometryClass.isometry f).isUniformInducing

中文:
定理 isComplete_image_iff
  条件: [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) {s : Set E}
  证明: _root_.isComplete_image_iff (SemilinearIsometryClass.isometry f).isUniformInducing

Depends on / 依赖: SemilinearIsometryClass, SemilinearIsometryClass.isometry, _root_, _root_.isComplete_image_iff, isComplete_image_iff, isUniformInducing, isometry
-/
theorem isComplete_image_iff [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) {s : Set E} :
    IsComplete (f '' s) ↔ IsComplete s :=
  _root_.isComplete_image_iff (SemilinearIsometryClass.isometry f).isUniformInducing

/--
theorem `isComplete_map_iff` / 定理 `isComplete_map_iff`

English:
theorem isComplete_map_iff
  given: [RingHomSurjective σ₁₂] {p : Submodule R E}
  proof: isComplete_image_iff f

中文:
定理 isComplete_map_iff
  条件: [RingHomSurjective σ₁₂] {p : Submodule R E}
  证明: isComplete_image_iff f

Depends on / 依赖: isComplete_image_iff
-/
theorem isComplete_map_iff [RingHomSurjective σ₁₂] {p : Submodule R E} :
    IsComplete (p.map f.toLinearMap : Set E₂) ↔ IsComplete (p : Set E) :=
  isComplete_image_iff f

/--
Instance `completeSpace_map` / 实例 `completeSpace_map`

English:
instance completeSpace_map
  signature: [RingHomSurjective σ₁₂] (p : Submodule R E) [CompleteSpace p]
  body: ((isComplete_map_iff f).2 <| completeSpace_coe_iff_isComplete.1 ‹_›).completeSpace_coe

@[simp]

中文:
实例 completeSpace_map
  签名: [RingHomSurjective σ₁₂] (p : Submodule R E) [CompleteSpace p]
  定义体: ((isComplete_map_iff f).2 <| completeSpace_coe_iff_isComplete.1 ‹_›).completeSpace_coe

@[simp]

Depends on / 依赖: completeSpace_coe, completeSpace_coe_iff_isComplete, isComplete_map_iff
-/
instance completeSpace_map [RingHomSurjective σ₁₂] (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map (f : E ->ₛₗ[σ₁₂] E₂)) :=
  ((isComplete_map_iff f).2 <| completeSpace_coe_iff_isComplete.1 ‹_›).completeSpace_coe

@[simp]
/--
theorem `dist_map` / 定理 `dist_map`

English:
theorem dist_map
  given: (x y : E)
  statement: dist (f x) (f y) = dist x y
  proof: f.isometry.dist_eq x y

@[simp]

中文:
定理 dist_map
  条件: (x y : E)
  结论: dist (f x) (f y) = dist x y
  证明: f.isometry.dist_eq x y

@[simp]

Depends on / 依赖: dist_eq, f.isometry.dist_eq, isometry
-/
theorem dist_map (x y : E) : dist (f x) (f y) = dist x y :=
  f.isometry.dist_eq x y

@[simp]
/--
theorem `edist_map` / 定理 `edist_map`

English:
theorem edist_map
  given: (x y : E)
  statement: edist (f x) (f y) = edist x y
  proof: f.isometry.edist_eq x y

中文:
定理 edist_map
  条件: (x y : E)
  结论: edist (f x) (f y) = edist x y
  证明: f.isometry.edist_eq x y

Depends on / 依赖: edist_eq, f.isometry.edist_eq, isometry
-/
theorem edist_map (x y : E) : edist (f x) (f y) = edist x y :=
  f.isometry.edist_eq x y

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Injective f₁
  proof: Isometry.injective (LinearIsometry.isometry f₁)

@[simp]

中文:
定理 injective
  结论: Injective f₁
  证明: Isometry.injective (LinearIsometry.isometry f₁)

@[simp]
-/
protected theorem injective : Injective f₁ :=
  Isometry.injective (LinearIsometry.isometry f₁)

@[simp]
/--
theorem `map_eq_iff` / 定理 `map_eq_iff`

English:
theorem map_eq_iff
  given: {x y : F}
  statement: f₁ x = f₁ y ↔ x = y
  proof: f₁.injective.eq_iff

中文:
定理 map_eq_iff
  条件: {x y : F}
  结论: f₁ x = f₁ y ↔ x = y
  证明: f₁.injective.eq_iff

Depends on / 依赖: eq_iff, injective, injective.eq_iff
-/
theorem map_eq_iff {x y : F} : f₁ x = f₁ y ↔ x = y :=
  f₁.injective.eq_iff

/--
theorem `map_ne` / 定理 `map_ne`

English:
theorem map_ne
  given: {x y : F} (h : x != y)
  statement: f₁ x != f₁ y
  proof: f₁.injective.ne h

中文:
定理 map_ne
  条件: {x y : F} (h : x != y)
  结论: f₁ x != f₁ y
  证明: f₁.injective.ne h

Depends on / 依赖: injective, injective.ne
-/
theorem map_ne {x y : F} (h : x != y) : f₁ x != f₁ y :=
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

@[simp]

中文:
定理 continuous
  结论: Continuous f
  证明: f.isometry.continuous

@[simp]
-/
protected theorem continuous : Continuous f :=
  f.isometry.continuous

@[simp]
/--
theorem `preimage_ball` / 定理 `preimage_ball`

English:
theorem preimage_ball
  given: (x : E) (r : Real)
  statement: f ⁻¹' Metric.ball (f x) r = Metric.ball x r
  proof: f.isometry.preimage_ball x r

@[simp]

中文:
定理 preimage_ball
  条件: (x : E) (r : 实数)
  结论: f ⁻¹' Metric.ball (f x) r = Metric.ball x r
  证明: f.isometry.preimage_ball x r

@[simp]

Depends on / 依赖: f.isometry.preimage_ball, isometry, preimage_ball
-/
theorem preimage_ball (x : E) (r : Real) : f ⁻¹' Metric.ball (f x) r = Metric.ball x r :=
  f.isometry.preimage_ball x r

@[simp]
/--
theorem `preimage_sphere` / 定理 `preimage_sphere`

English:
theorem preimage_sphere
  given: (x : E) (r : Real)
  statement: f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r
  proof: f.isometry.preimage_sphere x r

@[simp]

中文:
定理 preimage_sphere
  条件: (x : E) (r : 实数)
  结论: f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r
  证明: f.isometry.preimage_sphere x r

@[simp]

Depends on / 依赖: f.isometry.preimage_sphere, isometry, preimage_sphere
-/
theorem preimage_sphere (x : E) (r : Real) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r :=
  f.isometry.preimage_sphere x r

@[simp]
/--
theorem `preimage_closedBall` / 定理 `preimage_closedBall`

English:
theorem preimage_closedBall
  given: (x : E) (r : Real)
  proof: f.isometry.preimage_closedBall x r

中文:
定理 preimage_closedBall
  条件: (x : E) (r : 实数)
  证明: f.isometry.preimage_closedBall x r

Depends on / 依赖: f.isometry.preimage_closedBall, isometry, preimage_closedBall
-/
theorem preimage_closedBall (x : E) (r : Real) :
    f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r :=
  f.isometry.preimage_closedBall x r

/--
theorem `ediam_image` / 定理 `ediam_image`

English:
theorem ediam_image
  given: (s : Set E)
  statement: Metric.ediam (f '' s) = Metric.ediam s
  proof: f.isometry.ediam_image s

中文:
定理 ediam_image
  条件: (s : Set E)
  结论: Metric.ediam (f '' s) = Metric.ediam s
  证明: f.isometry.ediam_image s

Depends on / 依赖: ediam_image, f.isometry.ediam_image, isometry
-/
theorem ediam_image (s : Set E) : Metric.ediam (f '' s) = Metric.ediam s :=
  f.isometry.ediam_image s

/--
theorem `ediam_range` / 定理 `ediam_range`

English:
theorem ediam_range
  statement: Metric.ediam (range f) = Metric.ediam (univ : Set E)
  proof: f.isometry.ediam_range

中文:
定理 ediam_range
  结论: Metric.ediam (range f) = Metric.ediam (univ : Set E)
  证明: f.isometry.ediam_range

Depends on / 依赖: ediam_range, f.isometry.ediam_range, isometry
-/
theorem ediam_range : Metric.ediam (range f) = Metric.ediam (univ : Set E) :=
  f.isometry.ediam_range

/--
theorem `diam_image` / 定理 `diam_image`

English:
theorem diam_image
  given: (s : Set E)
  statement: Metric.diam (f '' s) = Metric.diam s
  proof: Isometry.diam_image (LinearIsometry.isometry f) s

中文:
定理 diam_image
  条件: (s : Set E)
  结论: Metric.diam (f '' s) = Metric.diam s
  证明: Isometry.diam_image (LinearIsometry.isometry f) s

Depends on / 依赖: Isometry, Isometry.diam_image, LinearIsometry, LinearIsometry.isometry, diam_image, isometry
-/
theorem diam_image (s : Set E) : Metric.diam (f '' s) = Metric.diam s :=
  Isometry.diam_image (LinearIsometry.isometry f) s

/--
theorem `diam_range` / 定理 `diam_range`

English:
theorem diam_range
  statement: Metric.diam (range f) = Metric.diam (univ : Set E)
  proof: Isometry.diam_range (LinearIsometry.isometry f)

中文:
定理 diam_range
  结论: Metric.diam (range f) = Metric.diam (univ : Set E)
  证明: Isometry.diam_range (LinearIsometry.isometry f)

Depends on / 依赖: Isometry, Isometry.diam_range, LinearIsometry, LinearIsometry.isometry, diam_range, isometry
-/
theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set E) :=
  Isometry.diam_range (LinearIsometry.isometry f)

/--
Definition of `toContinuousLinearMap` / `toContinuousLinearMap` 的定义

English:
definition toContinuousLinearMap
  signature: : E ->SL[σ₁₂] E₂
  body: ⟨f.toLinearMap, f.continuous⟩

中文:
定义 toContinuousLinearMap
  签名: : E ->SL[σ₁₂] E₂
  定义体: ⟨f.toLinearMap, f.continuous⟩

Depends on / 依赖: continuous, f.continuous, f.toLinearMap, toLinearMap
-/
def toContinuousLinearMap : E ->SL[σ₁₂] E₂ :=
  ⟨f.toLinearMap, f.continuous⟩

/--
lemma `toLinearMap_toContinuousLinearMap` / 引理 `toLinearMap_toContinuousLinearMap`

English:
lemma toLinearMap_toContinuousLinearMap
  given: (f : E ->ₛₗᵢ[σ₁₂] E₂)
  proof: rfl

中文:
引理 toLinearMap_toContinuousLinearMap
  条件: (f : E ->ₛₗᵢ[σ₁₂] E₂)
  证明: rfl
-/
@[simp] lemma toLinearMap_toContinuousLinearMap (f : E ->ₛₗᵢ[σ₁₂] E₂) :
  f.toContinuousLinearMap.toLinearMap = f.toLinearMap := rfl

/--
theorem `toContinuousLinearMap_injective` / 定理 `toContinuousLinearMap_injective`

English:
theorem toContinuousLinearMap_injective
  proof: fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearMap = _)

@[simp]

中文:
定理 toContinuousLinearMap_injective
  证明: fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearMap = _)

@[simp]
-/
theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : _ -> E ->SL[σ₁₂] E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearMap = _)

@[simp]
/--
theorem `toContinuousLinearMap_inj` / 定理 `toContinuousLinearMap_inj`

English:
theorem toContinuousLinearMap_inj
  given: {f g : E ->ₛₗᵢ[σ₁₂] E₂}
  proof: toContinuousLinearMap_injective.eq_iff

@[simp]

中文:
定理 toContinuousLinearMap_inj
  条件: {f g : E ->ₛₗᵢ[σ₁₂] E₂}
  证明: toContinuousLinearMap_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toContinuousLinearMap_injective, toContinuousLinearMap_injective.eq_iff
-/
theorem toContinuousLinearMap_inj {f g : E ->ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearMap = g.toContinuousLinearMap ↔ f = g :=
  toContinuousLinearMap_injective.eq_iff

@[simp]
/--
theorem `coe_toContinuousLinearMap` / 定理 `coe_toContinuousLinearMap`

English:
theorem coe_toContinuousLinearMap
  statement: ⇑f.toContinuousLinearMap = f
  proof: rfl

@[simp]

中文:
定理 coe_toContinuousLinearMap
  结论: ⇑f.toContinuousLinearMap = f
  证明: rfl

@[simp]
-/
theorem coe_toContinuousLinearMap : ⇑f.toContinuousLinearMap = f :=
  rfl

@[simp]
/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: {α : Type*} [TopologicalSpace α] {g : α -> E}
  proof: f.isometry.comp_continuous_iff

中文:
定理 comp_continuous_iff
  条件: {α : 类型} [TopologicalSpace α] {g : α -> E}
  证明: f.isometry.comp_continuous_iff

Depends on / 依赖: comp_continuous_iff, f.isometry.comp_continuous_iff, isometry
-/
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α -> E} :
    Continuous (f ∘ g) ↔ Continuous g :=
  f.isometry.comp_continuous_iff

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : E ->ₗᵢ[R] E
  body: ⟨LinearMap.id, fun _ => rfl⟩

@[simp, norm_cast]

中文:
定义 id
  签名: : E ->ₗᵢ[R] E
  定义体: ⟨LinearMap.id, fun _ => rfl⟩

@[simp, norm_cast]

Depends on / 依赖: LinearMap, LinearMap.id
-/
def id : E ->ₗᵢ[R] E :=
  ⟨LinearMap.id, fun _ => rfl⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ((id : E ->ₗᵢ[R] E) : E -> E) = _root_.id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ((id : E ->ₗᵢ[R] E) : E -> E) = _root_.id
  证明: rfl

@[simp]
-/
theorem coe_id : ((id : E ->ₗᵢ[R] E) : E -> E) = _root_.id :=
  rfl

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : E)
  statement: (id : E ->ₗᵢ[R] E) x = x
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (x : E)
  结论: (id : E ->ₗᵢ[R] E) x = x
  证明: rfl

@[simp]
-/
theorem id_apply (x : E) : (id : E ->ₗᵢ[R] E) x = x :=
  rfl

@[simp]
/--
theorem `id_toLinearMap` / 定理 `id_toLinearMap`

English:
theorem id_toLinearMap
  statement: (id.toLinearMap : E ->ₗ[R] E) = LinearMap.id
  proof: rfl

@[simp]

中文:
定理 id_toLinearMap
  结论: (id.toLinearMap : E ->ₗ[R] E) = LinearMap.id
  证明: rfl

@[simp]
-/
theorem id_toLinearMap : (id.toLinearMap : E ->ₗ[R] E) = LinearMap.id :=
  rfl

@[simp]
/--
theorem `id_toContinuousLinearMap` / 定理 `id_toContinuousLinearMap`

English:
theorem id_toContinuousLinearMap
  statement: id.toContinuousLinearMap = ContinuousLinearMap.id R E
  proof: rfl

中文:
定理 id_toContinuousLinearMap
  结论: id.toContinuousLinearMap = ContinuousLinearMap.id R E
  证明: rfl
-/
theorem id_toContinuousLinearMap : id.toContinuousLinearMap = ContinuousLinearMap.id R E :=
  rfl

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (E ->ₗᵢ[R] E)
  body: ⟨id⟩

中文:
实例 instInhabited
  签名: : Inhabited (E ->ₗᵢ[R] E)
  定义体: ⟨id⟩
-/
instance instInhabited : Inhabited (E ->ₗᵢ[R] E) := ⟨id⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (f : E ->ₛₗᵢ[σ₁₂] E₂)
  body: ⟨g.toLinearMap.comp f.toLinearMap, fun _ => (norm_map g _).trans (norm_map f _)⟩

@[simp]

中文:
定义 comp
  签名: (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (f : E ->ₛₗᵢ[σ₁₂] E₂)
  定义体: ⟨g.toLinearMap.comp f.toLinearMap, fun _ => (norm_map g _).trans (norm_map f _)⟩

@[simp]

Depends on / 依赖: f.toLinearMap, g.toLinearMap.comp, norm_map, toLinearMap
-/
def comp (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (f : E ->ₛₗᵢ[σ₁₂] E₂) : E ->ₛₗᵢ[σ₁₃] E₃ :=
  ⟨g.toLinearMap.comp f.toLinearMap, fun _ => (norm_map g _).trans (norm_map f _)⟩

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (f : E ->ₛₗᵢ[σ₁₂] E₂)
  statement: ⇑(g.comp f) = g ∘ f
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (f : E ->ₛₗᵢ[σ₁₂] E₂)
  结论: ⇑(g.comp f) = g ∘ f
  证明: rfl

@[simp]
-/
theorem coe_comp (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (f : E ->ₛₗᵢ[σ₁₂] E₂) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  statement: (id : E₂ ->ₗᵢ[R₂] E₂).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  结论: (id : E₂ ->ₗᵢ[R₂] E₂).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp : (id : E₂ ->ₗᵢ[R₂] E₂).comp f = f :=
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
  given: (f : E₃ ->ₛₗᵢ[σ₃₄] E₄) (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (h : E ->ₛₗᵢ[σ₁₂] E₂)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : E₃ ->ₛₗᵢ[σ₃₄] E₄) (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (h : E ->ₛₗᵢ[σ₁₂] E₂)
  证明: rfl
-/
theorem comp_assoc (f : E₃ ->ₛₗᵢ[σ₃₄] E₄) (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (h : E ->ₛₗᵢ[σ₁₂] E₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (E ->ₗᵢ[R] E) where
  body: id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]

中文:
实例 instMonoid
  签名: : Monoid (E ->ₗᵢ[R] E) where
  定义体: id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
-/
instance instMonoid : Monoid (E ->ₗᵢ[R] E) where
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
  statement: ((1 : E ->ₗᵢ[R] E) : E -> E) = _root_.id
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ((1 : E ->ₗᵢ[R] E) : E -> E) = _root_.id
  证明: rfl

@[simp]
-/
theorem coe_one : ((1 : E ->ₗᵢ[R] E) : E -> E) = _root_.id :=
  rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : E ->ₗᵢ[R] E)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
定理 coe_mul
  条件: (f g : E ->ₗᵢ[R] E)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
theorem coe_mul (f g : E ->ₗᵢ[R] E) : ⇑(f * g) = f ∘ g :=
  rfl

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : E ->ₗᵢ[R] E) = id
  proof: rfl

中文:
定理 one_def
  结论: (1 : E ->ₗᵢ[R] E) = id
  证明: rfl
-/
theorem one_def : (1 : E ->ₗᵢ[R] E) = id :=
  rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (f g : E ->ₗᵢ[R] E)
  statement: (f * g : E ->ₗᵢ[R] E) = f.comp g
  proof: rfl

中文:
定理 mul_def
  条件: (f g : E ->ₗᵢ[R] E)
  结论: (f * g : E ->ₗᵢ[R] E) = f.comp g
  证明: rfl
-/
theorem mul_def (f g : E ->ₗᵢ[R] E) : (f * g : E ->ₗᵢ[R] E) = f.comp g :=
  rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (f : E ->ₗᵢ[R] E) (n : Nat)
  statement: ⇑(f ^ n) = f^[n]
  proof: hom_coe_pow _ rfl (fun _ _ => rfl) _ _

中文:
定理 coe_pow
  条件: (f : E ->ₗᵢ[R] E) (n : 自然数)
  结论: ⇑(f ^ n) = f^[n]
  证明: hom_coe_pow _ rfl (fun _ _ => rfl) _ _

Depends on / 依赖: hom_coe_pow
-/
theorem coe_pow (f : E ->ₗᵢ[R] E) (n : Nat) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) _ _

section submoduleMap

variable {R R₁ R₂ M M₁ : Type*}
variable [Ring R] [SeminormedAddCommGroup M] [SeminormedAddCommGroup M₁]
variable [Module R M] [Module R M₁]

/-- A linear isometry between two modules restricts to a linear isometry
from any submodule `p` of the domain onto the image of that submodule.

This is a version of `LinearMap.submoduleMap` extended to linear isometries. -/
@[simps!]
/--
Definition of `submoduleMap` / `submoduleMap` 的定义

English:
definition submoduleMap
  signature: (p : Submodule R M) (e : M ->ₗᵢ[R] M₁)
  body: { e.toLinearMap.submoduleMap p with norm_map' x := e.norm_map' x }

中文:
定义 submoduleMap
  签名: (p : Submodule R M) (e : M ->ₗᵢ[R] M₁)
  定义体: { e.toLinearMap.submoduleMap p with norm_map' x := e.norm_map' x }

Depends on / 依赖: e.norm_map, e.toLinearMap.submoduleMap, norm_map, submoduleMap, toLinearMap
-/
def submoduleMap (p : Submodule R M) (e : M ->ₗᵢ[R] M₁) :
    p ->ₗᵢ[R] p.map (e : M ->ₗ[R] M₁) :=
  { e.toLinearMap.submoduleMap p with norm_map' x := e.norm_map' x }

end submoduleMap

end LinearIsometry

/--
Definition of `LinearMap.toLinearIsometry` / `LinearMap.toLinearIsometry` 的定义

English:
definition LinearMap.toLinearIsometry
  signature: (f : E ->ₛₗ[σ₁₂] E₂) (hf : Isometry f)
  body: { f with
    norm_map' := by
      simp_rw [← dist_zero_right]
      simpa using (hf.dist_eq · 0) }

中文:
定义 LinearMap.toLinearIsometry
  签名: (f : E ->ₛₗ[σ₁₂] E₂) (hf : Isometry f)
  定义体: { f with
    norm_map' := by
      simp_rw [← dist_zero_right]
      simpa using (hf.dist_eq · 0) }

Depends on / 依赖: dist_eq, dist_zero_right, hf.dist_eq, norm_map, simp_rw
-/
def LinearMap.toLinearIsometry (f : E ->ₛₗ[σ₁₂] E₂) (hf : Isometry f) : E ->ₛₗᵢ[σ₁₂] E₂ :=
  { f with
    norm_map' := by
      simp_rw [← dist_zero_right]
      simpa using (hf.dist_eq · 0) }

namespace Submodule

variable {R' : Type*} [Ring R'] [Module R' E] (p : Submodule R' E)

/--
Definition of `subtypeₗᵢ` / `subtypeₗᵢ` 的定义

English:
definition subtypeₗᵢ
  signature: : p ->ₗᵢ[R'] E
  body: ⟨p.subtype, fun _ => rfl⟩

@[simp]

中文:
定义 subtypeₗᵢ
  签名: : p ->ₗᵢ[R'] E
  定义体: ⟨p.subtype, fun _ => rfl⟩

@[simp]

Depends on / 依赖: p.subtype, subtype
-/
def subtypeₗᵢ : p ->ₗᵢ[R'] E :=
  ⟨p.subtype, fun _ => rfl⟩

@[simp]
/--
theorem `coe_subtypeₗᵢ` / 定理 `coe_subtypeₗᵢ`

English:
theorem coe_subtypeₗᵢ
  statement: ⇑p.subtypeₗᵢ = p.subtype
  proof: rfl

@[simp]

中文:
定理 coe_subtypeₗᵢ
  结论: ⇑p.subtypeₗᵢ = p.subtype
  证明: rfl

@[simp]
-/
theorem coe_subtypeₗᵢ : ⇑p.subtypeₗᵢ = p.subtype :=
  rfl

@[simp]
/--
theorem `subtypeₗᵢ_toLinearMap` / 定理 `subtypeₗᵢ_toLinearMap`

English:
theorem subtypeₗᵢ_toLinearMap
  statement: p.subtypeₗᵢ.toLinearMap = p.subtype
  proof: rfl

@[simp]

中文:
定理 subtypeₗᵢ_toLinearMap
  结论: p.subtypeₗᵢ.toLinearMap = p.subtype
  证明: rfl

@[simp]
-/
theorem subtypeₗᵢ_toLinearMap : p.subtypeₗᵢ.toLinearMap = p.subtype :=
  rfl

@[simp]
/--
theorem `subtypeₗᵢ_toContinuousLinearMap` / 定理 `subtypeₗᵢ_toContinuousLinearMap`

English:
theorem subtypeₗᵢ_toContinuousLinearMap
  statement: p.subtypeₗᵢ.toContinuousLinearMap = p.subtypeL
  proof: rfl

中文:
定理 subtypeₗᵢ_toContinuousLinearMap
  结论: p.subtypeₗᵢ.toContinuousLinearMap = p.subtypeL
  证明: rfl
-/
theorem subtypeₗᵢ_toContinuousLinearMap : p.subtypeₗᵢ.toContinuousLinearMap = p.subtypeL :=
  rfl

end Submodule

/--
Definition of `LinearIsometryEquiv` / `LinearIsometryEquiv` 的定义

English:
structure LinearIsometryEquiv
  parameters: (σ₁₂ : R ->+* R₂) {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁]
  extends: E ≃ₛₗ[σ₁₂] E₂
  axioms and operations (1):
    - norm_map' : forall x, ‖toLinearEquiv x‖ = ‖x‖

中文:
结构 LinearIsometryEquiv
  参数: (σ₁₂ : R ->+* R₂) {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁]
  继承: E ≃ₛₗ[σ₁₂] E₂
  公理与运算 (1 个):
    - norm_map' : 对任意 x, ‖toLinearEquiv x‖ = ‖x‖
-/
structure LinearIsometryEquiv (σ₁₂ : R ->+* R₂) {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
  [Module R E] [Module R₂ E₂] extends E ≃ₛₗ[σ₁₂] E₂ where
  norm_map' : forall x, ‖toLinearEquiv x‖ = ‖x‖

@[inherit_doc]
notation:25 E " ≃ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometryEquiv σ₁₂ E E₂

/-- A linear isometric equivalence between two normed vector spaces. -/
notation:25 E " ≃ₗᵢ[" R:25 "] " E₂:0 => LinearIsometryEquiv (RingHom.id R) E E₂

/-- An antilinear isometric equivalence between two normed vector spaces. -/
notation:25 E " ≃ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometryEquiv (starRingEnd R) E E₂

/--
Definition of `SemilinearIsometryEquivClass` / `SemilinearIsometryEquivClass` 的定义

English:
class SemilinearIsometryEquivClass
  parameters: (𝓕 : Type*) {R R₂ : outParam Type*} [Semiring R]
  extends: SemilinearEquivClass 𝓕 σ₁₂ E E₂
  axioms and operations (1):
    - norm_map : forall (f : 𝓕) (x : E), ‖f x‖ = ‖x‖

中文:
类 SemilinearIsometryEquivClass
  参数: (𝓕 : 类型) {R R₂ : outParam 类型} [Semiring R]
  继承: SemilinearEquivClass 𝓕 σ₁₂ E E₂
  公理与运算 (1 个):
    - norm_map : 对任意 (f : 𝓕) (x : E), ‖f x‖ = ‖x‖
-/
class SemilinearIsometryEquivClass (𝓕 : Type*) {R R₂ : outParam Type*} [Semiring R]
  [Semiring R₂] (σ₁₂ : outParam <| R ->+* R₂) {σ₂₁ : outParam <| R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : outParam Type*) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] [EquivLike 𝓕 E E₂] : Prop
  extends SemilinearEquivClass 𝓕 σ₁₂ E E₂ where
  norm_map : forall (f : 𝓕) (x : E), ‖f x‖ = ‖x‖

/--
Definition of `LinearIsometryEquivClass` / `LinearIsometryEquivClass` 的定义

English:
abbreviation LinearIsometryEquivClass
  signature: (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R]
  body: SemilinearIsometryEquivClass 𝓕 (RingHom.id R) E E₂

中文:
缩写 LinearIsometryEquivClass
  签名: (𝓕 : 类型) (R E E₂ : outParam 类型) [Semiring R]
  定义体: SemilinearIsometryEquivClass 𝓕 (RingHom.id R) E E₂

Depends on / 依赖: RingHom, RingHom.id, SemilinearIsometryEquivClass
-/
abbrev LinearIsometryEquivClass (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R E₂]
    [EquivLike 𝓕 E E₂] :=
  SemilinearIsometryEquivClass 𝓕 (RingHom.id R) E E₂

namespace SemilinearIsometryEquivClass

variable (𝓕)

-- `σ₂₁` becomes a metavariable, but it's OK since it's an outparam
instance (priority := 100) toSemilinearIsometryClass [EquivLike 𝓕 E E₂]
    [s : SemilinearIsometryEquivClass 𝓕 σ₁₂ E E₂] : SemilinearIsometryClass 𝓕 σ₁₂ E E₂ :=
  { s with }

end SemilinearIsometryEquivClass

namespace LinearIsometryEquiv

variable (e : E ≃ₛₗᵢ[σ₁₂] E₂)

/--
theorem `toLinearEquiv_injective` / 定理 `toLinearEquiv_injective`

English:
theorem toLinearEquiv_injective
  statement: Injective (toLinearEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) -> E ≃ₛₗ[σ₁₂] E₂)

中文:
定理 toLinearEquiv_injective
  结论: Injective (toLinearEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) -> E ≃ₛₗ[σ₁₂] E₂)
-/
theorem toLinearEquiv_injective : Injective (toLinearEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) -> E ≃ₛₗ[σ₁₂] E₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp]
/--
theorem `toLinearEquiv_inj` / 定理 `toLinearEquiv_inj`

English:
theorem toLinearEquiv_inj
  given: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  statement: f.toLinearEquiv = g.toLinearEquiv ↔ f = g
  proof: toLinearEquiv_injective.eq_iff

中文:
定理 toLinearEquiv_inj
  条件: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  结论: f.toLinearEquiv = g.toLinearEquiv ↔ f = g
  证明: toLinearEquiv_injective.eq_iff

Depends on / 依赖: eq_iff, toLinearEquiv_injective, toLinearEquiv_injective.eq_iff
-/
theorem toLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toLinearEquiv = g.toLinearEquiv ↔ f = g :=
  toLinearEquiv_injective.eq_iff

/--
Instance `instEquivLike` / 实例 `instEquivLike`

English:
instance instEquivLike
  signature: : EquivLike (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ where
  body: e.toFun
  inv e := e.invFun
coe_injective' _ _ h _ := toLinearEquiv_injective DFunLike.ext' h
  left_inv e := e.left_inv
  right_inv e := e.right_inv

中文:
实例 instEquivLike
  签名: : EquivLike (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ where
  定义体: e.toFun
  inv e := e.invFun
coe_injective' _ _ h _ := toLinearEquiv_injective DFunLike.ext' h
  left_inv e := e.left_inv
  right_inv e := e.right_inv

Depends on / 依赖: e.toFun
-/
instance instEquivLike : EquivLike (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ where
  coe e := e.toFun
  inv e := e.invFun
coe_injective' _ _ h _ := toLinearEquiv_injective DFunLike.ext' h
  left_inv e := e.left_inv
  right_inv e := e.right_inv

/--
Instance `instSemilinearIsometryEquivClass` / 实例 `instSemilinearIsometryEquivClass`

English:
instance instSemilinearIsometryEquivClass
  signature: :
  body: map_add f.toLinearEquiv
  map_smulₛₗ e := map_smulₛₗ e.toLinearEquiv
  norm_map e := e.norm_map'

中文:
实例 instSemilinearIsometryEquivClass
  签名: :
  定义体: map_add f.toLinearEquiv
  map_smulₛₗ e := map_smulₛₗ e.toLinearEquiv
  norm_map e := e.norm_map'

Depends on / 依赖: f.toLinearEquiv, map_add, toLinearEquiv
-/
instance instSemilinearIsometryEquivClass :
    SemilinearIsometryEquivClass (E ≃ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ e := map_smulₛₗ e.toLinearEquiv
  norm_map e := e.norm_map'

/--
Instance `instCoeFun` / 实例 `instCoeFun`

English:
instance instCoeFun
  signature: : CoeFun (E ≃ₛₗᵢ[σ₁₂] E₂) fun _ => E -> E₂
  body: ⟨DFunLike.coe⟩

中文:
实例 instCoeFun
  签名: : CoeFun (E ≃ₛₗᵢ[σ₁₂] E₂) fun _ => E -> E₂
  定义体: ⟨DFunLike.coe⟩

Depends on / 依赖: DFunLike, DFunLike.coe
-/
instance instCoeFun : CoeFun (E ≃ₛₗᵢ[σ₁₂] E₂) fun _ => E -> E₂ := ⟨DFunLike.coe⟩

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (E ≃ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (↑)
  proof: DFunLike.coe_injective

@[simp]

中文:
定理 coe_injective
  结论: @Function.Injective (E ≃ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (↑)
  证明: DFunLike.coe_injective

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : @Function.Injective (E ≃ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (↑) :=
  DFunLike.coe_injective

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : E ≃ₛₗ[σ₁₂] E₂) (he : forall x, ‖e x‖ = ‖x‖)
  statement: ⇑(mk e he) = e
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (e : E ≃ₛₗ[σ₁₂] E₂) (he : 对任意 x, ‖e x‖ = ‖x‖)
  结论: ⇑(mk e he) = e
  证明: rfl

@[simp]
-/
theorem coe_mk (e : E ≃ₛₗ[σ₁₂] E₂) (he : forall x, ‖e x‖ = ‖x‖) : ⇑(mk e he) = e :=
  rfl

@[simp]
/--
theorem `coe_toLinearEquiv` / 定理 `coe_toLinearEquiv`

English:
theorem coe_toLinearEquiv
  given: (e : E ≃ₛₗᵢ[σ₁₂] E₂)
  statement: ⇑e.toLinearEquiv = e
  proof: rfl

@[ext]

中文:
定理 coe_toLinearEquiv
  条件: (e : E ≃ₛₗᵢ[σ₁₂] E₂)
  结论: ⇑e.toLinearEquiv = e
  证明: rfl

@[ext]
-/
theorem coe_toLinearEquiv (e : E ≃ₛₗᵢ[σ₁₂] E₂) : ⇑e.toLinearEquiv = e :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x = e' x)
  statement: e = e'
  proof: toLinearEquiv_injective LinearEquiv.ext h

中文:
定理 ext
  条件: {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : 对任意 x, e x = e' x)
  结论: e = e'
  证明: toLinearEquiv_injective LinearEquiv.ext h

Depends on / 依赖: LinearEquiv, LinearEquiv.ext, toLinearEquiv_injective
-/
theorem ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x = e' x) : e = e' :=
toLinearEquiv_injective LinearEquiv.ext h

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: {f : E ≃ₛₗᵢ[σ₁₂] E₂}
  statement: forall {x x' : E}, x = x' -> f x = f x'

中文:
定理 congr_arg
  条件: {f : E ≃ₛₗᵢ[σ₁₂] E₂}
  结论: 对任意 {x x' : E}, x = x' -> f x = f x'
-/
protected theorem congr_arg {f : E ≃ₛₗᵢ[σ₁₂] E₂} : forall {x x' : E}, x = x' -> f x = f x'
  | _, _, rfl => rfl

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : E ≃ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E)
  statement: f x = g x
  proof: h ▸ rfl

中文:
定理 congr_fun
  条件: {f g : E ≃ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E)
  结论: f x = g x
  证明: h ▸ rfl
-/
protected theorem congr_fun {f g : E ≃ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E) : f x = g x :=
  h ▸ rfl

/--
Definition of `ofBounds` / `ofBounds` 的定义

English:
definition ofBounds
  signature: (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : forall x, ‖e x‖ <= ‖x‖) (h₂ : forall y, ‖e.symm y‖ <= ‖y‖)
  body: ⟨e, fun x => le_antisymm (h₁ x) by simpa only [e.symm_apply_apply] using h₂ (e x)⟩

中文:
定义 ofBounds
  签名: (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : 对任意 x, ‖e x‖ <= ‖x‖) (h₂ : 对任意 y, ‖e.symm y‖ <= ‖y‖)
  定义体: ⟨e, fun x => le_antisymm (h₁ x) by simpa only [e.symm_apply_apply] using h₂ (e x)⟩

Depends on / 依赖: e.symm_apply_apply, le_antisymm, symm_apply_apply
-/
def ofBounds (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : forall x, ‖e x‖ <= ‖x‖) (h₂ : forall y, ‖e.symm y‖ <= ‖y‖) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
⟨e, fun x => le_antisymm (h₁ x) by simpa only [e.symm_apply_apply] using h₂ (e x)⟩

/--
lemma `norm_map` / 引理 `norm_map`

English:
lemma norm_map
  given: (x : E)
  statement: ‖e x‖ = ‖x‖
  proof: by simp

中文:
引理 norm_map
  条件: (x : E)
  结论: ‖e x‖ = ‖x‖
  证明: by simp
-/
protected lemma norm_map (x : E) : ‖e x‖ = ‖x‖ := by simp
/--
lemma `nnnorm_map` / 引理 `nnnorm_map`

English:
lemma nnnorm_map
  given: (x : E)
  statement: ‖e x‖₊ = ‖x‖₊
  proof: by simp

中文:
引理 nnnorm_map
  条件: (x : E)
  结论: ‖e x‖₊ = ‖x‖₊
  证明: by simp
-/
protected lemma nnnorm_map (x : E) : ‖e x‖₊ = ‖x‖₊ := by simp
/--
lemma `enorm_map` / 引理 `enorm_map`

English:
lemma enorm_map
  given: (x : E)
  statement: ‖e x‖ₑ = ‖x‖ₑ
  proof: by simp

中文:
引理 enorm_map
  条件: (x : E)
  结论: ‖e x‖ₑ = ‖x‖ₑ
  证明: by simp
-/
protected lemma enorm_map (x : E) : ‖e x‖ₑ = ‖x‖ₑ := by simp

/--
Definition of `toLinearIsometry` / `toLinearIsometry` 的定义

English:
definition toLinearIsometry
  signature: : E ->ₛₗᵢ[σ₁₂] E₂
  body: ⟨e.1, e.2⟩

中文:
定义 toLinearIsometry
  签名: : E ->ₛₗᵢ[σ₁₂] E₂
  定义体: ⟨e.1, e.2⟩
-/
def toLinearIsometry : E ->ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e.1, e.2⟩

/--
theorem `toLinearIsometry_injective` / 定理 `toLinearIsometry_injective`

English:
theorem toLinearIsometry_injective
  statement: Function.Injective (toLinearIsometry : _ -> E ->ₛₗᵢ[σ₁₂] E₂)
  proof: fun x _ h => coe_injective (congr_arg _ h : ⇑x.toLinearIsometry = _)

@[simp]

中文:
定理 toLinearIsometry_injective
  结论: Function.Injective (toLinearIsometry : _ -> E ->ₛₗᵢ[σ₁₂] E₂)
  证明: fun x _ h => coe_injective (congr_arg _ h : ⇑x.toLinearIsometry = _)

@[simp]

Depends on / 依赖: coe_injective, congr_arg, toLinearIsometry, x.toLinearIsometry
-/
theorem toLinearIsometry_injective : Function.Injective (toLinearIsometry : _ -> E ->ₛₗᵢ[σ₁₂] E₂) :=
  fun x _ h => coe_injective (congr_arg _ h : ⇑x.toLinearIsometry = _)

@[simp]
/--
theorem `toLinearIsometry_inj` / 定理 `toLinearIsometry_inj`

English:
theorem toLinearIsometry_inj
  given: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  proof: toLinearIsometry_injective.eq_iff

@[simp]

中文:
定理 toLinearIsometry_inj
  条件: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  证明: toLinearIsometry_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toLinearIsometry_injective, toLinearIsometry_injective.eq_iff
-/
theorem toLinearIsometry_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toLinearIsometry = g.toLinearIsometry ↔ f = g :=
  toLinearIsometry_injective.eq_iff

@[simp]
/--
theorem `coe_toLinearIsometry` / 定理 `coe_toLinearIsometry`

English:
theorem coe_toLinearIsometry
  statement: ⇑e.toLinearIsometry = e
  proof: rfl

中文:
定理 coe_toLinearIsometry
  结论: ⇑e.toLinearIsometry = e
  证明: rfl
-/
theorem coe_toLinearIsometry : ⇑e.toLinearIsometry = e :=
  rfl

/--
theorem `isometry` / 定理 `isometry`

English:
theorem isometry
  statement: Isometry e
  proof: e.toLinearIsometry.isometry

中文:
定理 isometry
  结论: Isometry e
  证明: e.toLinearIsometry.isometry
-/
protected theorem isometry : Isometry e :=
  e.toLinearIsometry.isometry

/--
Definition of `toIsometryEquiv` / `toIsometryEquiv` 的定义

English:
definition toIsometryEquiv
  signature: : E ≃ᵢ E₂
  body: ⟨e.toLinearEquiv.toEquiv, e.isometry⟩

中文:
定义 toIsometryEquiv
  签名: : E ≃ᵢ E₂
  定义体: ⟨e.toLinearEquiv.toEquiv, e.isometry⟩

Depends on / 依赖: e.isometry, e.toLinearEquiv.toEquiv, isometry, toEquiv, toLinearEquiv
-/
def toIsometryEquiv : E ≃ᵢ E₂ :=
  ⟨e.toLinearEquiv.toEquiv, e.isometry⟩

/--
theorem `toIsometryEquiv_injective` / 定理 `toIsometryEquiv_injective`

English:
theorem toIsometryEquiv_injective
  proof: fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toIsometryEquiv = _)

@[simp]

中文:
定理 toIsometryEquiv_injective
  证明: fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toIsometryEquiv = _)

@[simp]
-/
theorem toIsometryEquiv_injective :
    Function.Injective (toIsometryEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) -> E ≃ᵢ E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toIsometryEquiv = _)

@[simp]
/--
theorem `toIsometryEquiv_inj` / 定理 `toIsometryEquiv_inj`

English:
theorem toIsometryEquiv_inj
  given: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  proof: toIsometryEquiv_injective.eq_iff

@[simp]

中文:
定理 toIsometryEquiv_inj
  条件: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  证明: toIsometryEquiv_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toIsometryEquiv_injective, toIsometryEquiv_injective.eq_iff
-/
theorem toIsometryEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toIsometryEquiv = g.toIsometryEquiv ↔ f = g :=
  toIsometryEquiv_injective.eq_iff

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
  given: (e : E ≃ₛₗᵢ[σ₁₂] E₂)
  statement: Set.range e = Set.univ
  proof: by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

中文:
定理 range_eq_univ
  条件: (e : E ≃ₛₗᵢ[σ₁₂] E₂)
  结论: Set.range e = Set.univ
  证明: by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

Depends on / 依赖: IsometryEquiv, IsometryEquiv.range_eq_univ, coe_toIsometryEquiv, range_eq_univ
-/
theorem range_eq_univ (e : E ≃ₛₗᵢ[σ₁₂] E₂) : Set.range e = Set.univ := by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: : E ≃ₜ E₂
  body: e.toIsometryEquiv.toHomeomorph

中文:
定义 toHomeomorph
  签名: : E ≃ₜ E₂
  定义体: e.toIsometryEquiv.toHomeomorph

Depends on / 依赖: e.toIsometryEquiv.toHomeomorph, toHomeomorph, toIsometryEquiv
-/
def toHomeomorph : E ≃ₜ E₂ :=
  e.toIsometryEquiv.toHomeomorph

/--
theorem `toHomeomorph_injective` / 定理 `toHomeomorph_injective`

English:
theorem toHomeomorph_injective
  statement: Function.Injective (toHomeomorph : (E ≃ₛₗᵢ[σ₁₂] E₂) -> E ≃ₜ E₂)
  proof: fun x _ h => coe_injective (congr_arg _ h : ⇑x.toHomeomorph = _)

@[simp]

中文:
定理 toHomeomorph_injective
  结论: Function.Injective (toHomeomorph : (E ≃ₛₗᵢ[σ₁₂] E₂) -> E ≃ₜ E₂)
  证明: fun x _ h => coe_injective (congr_arg _ h : ⇑x.toHomeomorph = _)

@[simp]

Depends on / 依赖: coe_injective, congr_arg, toHomeomorph, x.toHomeomorph
-/
theorem toHomeomorph_injective : Function.Injective (toHomeomorph : (E ≃ₛₗᵢ[σ₁₂] E₂) -> E ≃ₜ E₂) :=
  fun x _ h => coe_injective (congr_arg _ h : ⇑x.toHomeomorph = _)

@[simp]
/--
theorem `toHomeomorph_inj` / 定理 `toHomeomorph_inj`

English:
theorem toHomeomorph_inj
  given: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  statement: f.toHomeomorph = g.toHomeomorph ↔ f = g
  proof: toHomeomorph_injective.eq_iff

@[simp]

中文:
定理 toHomeomorph_inj
  条件: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  结论: f.toHomeomorph = g.toHomeomorph ↔ f = g
  证明: toHomeomorph_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toHomeomorph_injective, toHomeomorph_injective.eq_iff
-/
theorem toHomeomorph_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toHomeomorph = g.toHomeomorph ↔ f = g :=
  toHomeomorph_injective.eq_iff

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
  结论: Continuous e
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

/-- Interpret a `LinearIsometryEquiv` as a `ContinuousLinearEquiv`. -/
@[coe]
/--
Definition of `toContinuousLinearEquiv` / `toContinuousLinearEquiv` 的定义

English:
definition toContinuousLinearEquiv
  signature: : E ≃SL[σ₁₂] E₂
  body: { e.toLinearIsometry.toContinuousLinearMap, e.toHomeomorph with }

中文:
定义 toContinuousLinearEquiv
  签名: : E ≃SL[σ₁₂] E₂
  定义体: { e.toLinearIsometry.toContinuousLinearMap, e.toHomeomorph with }

Depends on / 依赖: e.toHomeomorph, e.toLinearIsometry.toContinuousLinearMap, toContinuousLinearMap, toHomeomorph, toLinearIsometry
-/
def toContinuousLinearEquiv : E ≃SL[σ₁₂] E₂ :=
  { e.toLinearIsometry.toContinuousLinearMap, e.toHomeomorph with }

/--
theorem `toContinuousLinearEquiv_injective` / 定理 `toContinuousLinearEquiv_injective`

English:
theorem toContinuousLinearEquiv_injective
  proof: fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearEquiv = _)

@[simp]

中文:
定理 toContinuousLinearEquiv_injective
  证明: fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearEquiv = _)

@[simp]
-/
theorem toContinuousLinearEquiv_injective :
    Function.Injective (toContinuousLinearEquiv : _ -> E ≃SL[σ₁₂] E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearEquiv = _)

@[simp]
/--
theorem `toContinuousLinearEquiv_inj` / 定理 `toContinuousLinearEquiv_inj`

English:
theorem toContinuousLinearEquiv_inj
  given: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  proof: toContinuousLinearEquiv_injective.eq_iff

@[simp]

中文:
定理 toContinuousLinearEquiv_inj
  条件: {f g : E ≃ₛₗᵢ[σ₁₂] E₂}
  证明: toContinuousLinearEquiv_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toContinuousLinearEquiv_injective, toContinuousLinearEquiv_injective.eq_iff
-/
theorem toContinuousLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearEquiv = g.toContinuousLinearEquiv ↔ f = g :=
  toContinuousLinearEquiv_injective.eq_iff

@[simp]
/--
theorem `coe_toContinuousLinearEquiv` / 定理 `coe_toContinuousLinearEquiv`

English:
theorem coe_toContinuousLinearEquiv
  statement: ⇑e.toContinuousLinearEquiv = e
  proof: rfl

中文:
定理 coe_toContinuousLinearEquiv
  结论: ⇑e.toContinuousLinearEquiv = e
  证明: rfl
-/
theorem coe_toContinuousLinearEquiv : ⇑e.toContinuousLinearEquiv = e :=
  rfl

variable (R E)

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : E ≃ₗᵢ[R] E
  body: ⟨LinearEquiv.refl R E, fun _ => rfl⟩

中文:
定义 refl
  签名: : E ≃ₗᵢ[R] E
  定义体: ⟨LinearEquiv.refl R E, fun _ => rfl⟩

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def refl : E ≃ₗᵢ[R] E :=
  ⟨LinearEquiv.refl R E, fun _ => rfl⟩

/--
Definition of `ulift` / `ulift` 的定义

English:
definition ulift
  signature: : ULift E ≃ₗᵢ[R] E
  body: { ContinuousLinearEquiv.ulift with norm_map' := fun _ => rfl }

中文:
定义 ulift
  签名: : ULift E ≃ₗᵢ[R] E
  定义体: { ContinuousLinearEquiv.ulift with norm_map' := fun _ => rfl }

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ulift, norm_map
-/
def ulift : ULift E ≃ₗᵢ[R] E :=
  { ContinuousLinearEquiv.ulift with norm_map' := fun _ => rfl }

variable {R E}

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (E ≃ₗᵢ[R] E)
  body: ⟨refl R E⟩

@[simp]

中文:
实例 instInhabited
  签名: : Inhabited (E ≃ₗᵢ[R] E)
  定义体: ⟨refl R E⟩

@[simp]
-/
instance instInhabited : Inhabited (E ≃ₗᵢ[R] E) := ⟨refl R E⟩

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(refl R E) = id
  proof: rfl

中文:
定理 coe_refl
  结论: ⇑(refl R E) = id
  证明: rfl
-/
theorem coe_refl : ⇑(refl R E) = id :=
  rfl

/--
theorem `toLinearEquiv_refl` / 定理 `toLinearEquiv_refl`

English:
theorem toLinearEquiv_refl
  statement: (refl R E).toLinearEquiv = .refl R E
  proof: rfl

中文:
定理 toLinearEquiv_refl
  结论: (refl R E).toLinearEquiv = .refl R E
  证明: rfl
-/
@[simp] theorem toLinearEquiv_refl : (refl R E).toLinearEquiv = .refl R E := rfl

/--
theorem `toContinuousLinearEquiv_refl` / 定理 `toContinuousLinearEquiv_refl`

English:
theorem toContinuousLinearEquiv_refl
  statement: (refl R E).toContinuousLinearEquiv = .refl R E
  proof: rfl

中文:
定理 toContinuousLinearEquiv_refl
  结论: (refl R E).toContinuousLinearEquiv = .refl R E
  证明: rfl
-/
@[simp] theorem toContinuousLinearEquiv_refl : (refl R E).toContinuousLinearEquiv = .refl R E := rfl

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : E₂ ≃ₛₗᵢ[σ₂₁] E
  body: ⟨e.toLinearEquiv.symm, fun x =>
(e.norm_map _).symm.trans congr_arg norm e.toLinearEquiv.apply_symm_apply x⟩

@[simp]

中文:
定义 symm
  签名: : E₂ ≃ₛₗᵢ[σ₂₁] E
  定义体: ⟨e.toLinearEquiv.symm, fun x =>
(e.norm_map _).symm.trans congr_arg norm e.toLinearEquiv.apply_symm_apply x⟩

@[simp]

Depends on / 依赖: apply_symm_apply, congr_arg, e.norm_map, e.toLinearEquiv.apply_symm_apply, e.toLinearEquiv.symm, norm_map, symm.trans, toLinearEquiv
-/
def symm : E₂ ≃ₛₗᵢ[σ₂₁] E :=
  ⟨e.toLinearEquiv.symm, fun x =>
(e.norm_map _).symm.trans congr_arg norm e.toLinearEquiv.apply_symm_apply x⟩

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (x : E₂)
  statement: e (e.symm x) = x
  proof: e.toLinearEquiv.apply_symm_apply x

@[simp]

中文:
定理 apply_symm_apply
  条件: (x : E₂)
  结论: e (e.symm x) = x
  证明: e.toLinearEquiv.apply_symm_apply x

@[simp]

Depends on / 依赖: apply_symm_apply, e.toLinearEquiv.apply_symm_apply, toLinearEquiv
-/
theorem apply_symm_apply (x : E₂) : e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (x : E)
  statement: e.symm (e x) = x
  proof: e.toLinearEquiv.symm_apply_apply x

中文:
定理 symm_apply_apply
  条件: (x : E)
  结论: e.symm (e x) = x
  证明: e.toLinearEquiv.symm_apply_apply x

Depends on / 依赖: e.toLinearEquiv.symm_apply_apply, symm_apply_apply, toLinearEquiv
-/
theorem symm_apply_apply (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toEquiv.eq_symm_apply

中文:
定理 eq_symm_apply
  条件: {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toEquiv.eq_symm_apply

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: {x : E}
  statement: e x = 0 ↔ x = 0
  proof: e.toLinearEquiv.map_eq_zero_iff

@[simp]

中文:
定理 map_eq_zero_iff
  条件: {x : E}
  结论: e x = 0 ↔ x = 0
  证明: e.toLinearEquiv.map_eq_zero_iff

@[simp]

Depends on / 依赖: e.toLinearEquiv.map_eq_zero_iff, map_eq_zero_iff, toLinearEquiv
-/
theorem map_eq_zero_iff {x : E} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff

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
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (E₂ ≃ₛₗᵢ[σ₂₁] E) -> _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: Function.Bijective (symm : (E₂ ≃ₛₗᵢ[σ₂₁] E) -> _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (E₂ ≃ₛₗᵢ[σ₂₁] E) -> _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `toLinearEquiv_symm` / 定理 `toLinearEquiv_symm`

English:
theorem toLinearEquiv_symm
  statement: e.symm.toLinearEquiv = e.toLinearEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_symm
  结论: e.symm.toLinearEquiv = e.toLinearEquiv.symm
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_symm : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_symm_toLinearEquiv` / 定理 `coe_symm_toLinearEquiv`

English:
theorem coe_symm_toLinearEquiv
  statement: ⇑e.toLinearEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toLinearEquiv
  结论: ⇑e.toLinearEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toLinearEquiv : ⇑e.toLinearEquiv.symm = e.symm := rfl

@[simp]
/--
theorem `toContinuousLinearEquiv_symm` / 定理 `toContinuousLinearEquiv_symm`

English:
theorem toContinuousLinearEquiv_symm
  proof: rfl

@[simp]

中文:
定理 toContinuousLinearEquiv_symm
  证明: rfl

@[simp]
-/
theorem toContinuousLinearEquiv_symm :
    e.symm.toContinuousLinearEquiv = e.toContinuousLinearEquiv.symm := rfl

@[simp]
/--
theorem `coe_symm_toContinuousLinearEquiv` / 定理 `coe_symm_toContinuousLinearEquiv`

English:
theorem coe_symm_toContinuousLinearEquiv
  statement: ⇑e.toContinuousLinearEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toContinuousLinearEquiv
  结论: ⇑e.toContinuousLinearEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toContinuousLinearEquiv : ⇑e.toContinuousLinearEquiv.symm = e.symm :=
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
theorem coe_symm_toIsometryEquiv : ⇑e.toIsometryEquiv.symm = e.symm := rfl

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
theorem coe_symm_toHomeomorph : ⇑e.toHomeomorph.symm = e.symm := rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (σ₁₂ : R ->+* R₂) {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  body: h

中文:
定义 Simps.apply
  签名: (σ₁₂ : R ->+* R₂) {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  定义体: h
-/
def Simps.apply (σ₁₂ : R ->+* R₂) {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E]
    [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E -> E₂ :=
  h

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (σ₁₂ : R ->+* R₂) {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁]
  body: h.symm

initialize_simps_projections LinearIsometryEquiv (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (σ₁₂ : R ->+* R₂) {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁]
  定义体: h.symm

initialize_simps_projections LinearIsometryEquiv (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (σ₁₂ : R ->+* R₂) {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁]
    [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
    [Module R E] [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E₂ -> E :=
  h.symm

initialize_simps_projections LinearIsometryEquiv (toFun -> apply, invFun -> symm_apply)

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  body: ⟨e.toLinearEquiv.trans e'.toLinearEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]

中文:
定义 trans
  签名: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  定义体: ⟨e.toLinearEquiv.trans e'.toLinearEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]

Depends on / 依赖: e.norm_map, e.toLinearEquiv.trans, norm_map, toLinearEquiv
-/
def trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : E ≃ₛₗᵢ[σ₁₃] E₃ :=
  ⟨e.toLinearEquiv.trans e'.toLinearEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  statement: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  结论: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  证明: rfl

@[simp]
-/
theorem coe_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E)
  证明: rfl

@[simp]
-/
theorem trans_apply (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E) :
    (e₁.trans e₂ : E ≃ₛₗᵢ[σ₁₃] E₃) c = e₂ (e₁ c) :=
  rfl

@[simp]
/--
theorem `toLinearEquiv_trans` / 定理 `toLinearEquiv_trans`

English:
theorem toLinearEquiv_trans
  given: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  proof: rfl

中文:
定理 toLinearEquiv_trans
  条件: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  证明: rfl
-/
theorem toLinearEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toLinearEquiv = e.toLinearEquiv.trans e'.toLinearEquiv :=
  rfl

/--
theorem `toContinuousLinearEquiv_trans` / 定理 `toContinuousLinearEquiv_trans`

English:
theorem toContinuousLinearEquiv_trans
  given: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  proof: rfl

@[simp]

中文:
定理 toContinuousLinearEquiv_trans
  条件: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  证明: rfl

@[simp]
-/
@[simp] theorem toContinuousLinearEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toContinuousLinearEquiv =
      e.toContinuousLinearEquiv.trans e'.toContinuousLinearEquiv :=
  rfl

@[simp]
/--
theorem `toIsometryEquiv_trans` / 定理 `toIsometryEquiv_trans`

English:
theorem toIsometryEquiv_trans
  given: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  proof: rfl

@[simp]

中文:
定理 toIsometryEquiv_trans
  条件: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  证明: rfl

@[simp]
-/
theorem toIsometryEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toIsometryEquiv = e.toIsometryEquiv.trans e'.toIsometryEquiv :=
  rfl

@[simp]
/--
theorem `toHomeomorph_trans` / 定理 `toHomeomorph_trans`

English:
theorem toHomeomorph_trans
  given: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  proof: rfl

@[simp]

中文:
定理 toHomeomorph_trans
  条件: (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  证明: rfl

@[simp]
-/
theorem toHomeomorph_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toHomeomorph = e.toHomeomorph.trans e'.toHomeomorph :=
  rfl

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  statement: e.trans (refl R₂ E₂) = e
  proof: ext fun _ => rfl

@[simp]

中文:
定理 trans_refl
  结论: e.trans (refl R₂ E₂) = e
  证明: ext fun _ => rfl

@[simp]
-/
theorem trans_refl : e.trans (refl R₂ E₂) = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  statement: (refl R E).trans e = e
  proof: ext fun _ => rfl

@[simp]

中文:
定理 refl_trans
  结论: (refl R E).trans e = e
  证明: ext fun _ => rfl

@[simp]
-/
theorem refl_trans : (refl R E).trans e = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  statement: e.trans e.symm = refl R E
  proof: ext e.symm_apply_apply

@[simp]

中文:
定理 self_trans_symm
  结论: e.trans e.symm = refl R E
  证明: ext e.symm_apply_apply

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem self_trans_symm : e.trans e.symm = refl R E :=
  ext e.symm_apply_apply

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  statement: e.symm.trans e = refl R₂ E₂
  proof: ext e.apply_symm_apply

@[simp]

中文:
定理 symm_trans_self
  结论: e.symm.trans e = refl R₂ E₂
  证明: ext e.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply
-/
theorem symm_trans_self : e.symm.trans e = refl R₂ E₂ :=
  ext e.apply_symm_apply

@[simp]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  statement: e.symm ∘ e = id
  proof: funext e.symm_apply_apply

@[simp]

中文:
定理 symm_comp_self
  结论: e.symm ∘ e = id
  证明: funext e.symm_apply_apply

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp_self : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  statement: e ∘ e.symm = id
  proof: e.symm.symm_comp_self

@[simp]

中文:
定理 self_comp_symm
  结论: e ∘ e.symm = id
  证明: e.symm.symm_comp_self

@[simp]

Depends on / 依赖: e.symm.symm_comp_self, symm_comp_self
-/
theorem self_comp_symm : e ∘ e.symm = id :=
  e.symm.symm_comp_self

@[simp]
/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  proof: rfl

中文:
定理 symm_trans
  条件: (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  证明: rfl
-/
theorem symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

/--
theorem `coe_symm_trans` / 定理 `coe_symm_trans`

English:
theorem coe_symm_trans
  given: (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  proof: rfl

中文:
定理 coe_symm_trans
  条件: (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃)
  证明: rfl
-/
theorem coe_symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
  rfl

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄)
  proof: rfl

中文:
定理 trans_assoc
  条件: (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄)
  证明: rfl
-/
theorem trans_assoc (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄) :
    eEE₂.trans (eE₂E₃.trans eE₃E₄) = (eEE₂.trans eE₂E₃).trans eE₃E₄ :=
  rfl

/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: : Group (E ≃ₗᵢ[R] E) where
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
  签名: : Group (E ≃ₗᵢ[R] E) where
  定义体: e₂.trans e₁
  one := refl _ _
  inv := symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_assoc _ _ _ := trans_assoc _ _ _
  inv_mul_cancel := self_trans_symm

@[simp]
-/
instance instGroup : Group (E ≃ₗᵢ[R] E) where
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
  statement: ⇑(1 : E ≃ₗᵢ[R] E) = id
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ⇑(1 : E ≃ₗᵢ[R] E) = id
  证明: rfl

@[simp]
-/
theorem coe_one : ⇑(1 : E ≃ₗᵢ[R] E) = id :=
  rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (e e' : E ≃ₗᵢ[R] E)
  statement: ⇑(e * e') = e ∘ e'
  proof: rfl

@[simp]

中文:
定理 coe_mul
  条件: (e e' : E ≃ₗᵢ[R] E)
  结论: ⇑(e * e') = e ∘ e'
  证明: rfl

@[simp]
-/
theorem coe_mul (e e' : E ≃ₗᵢ[R] E) : ⇑(e * e') = e ∘ e' :=
  rfl

@[simp]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (e : E ≃ₗᵢ[R] E)
  statement: ⇑e⁻¹ = e.symm
  proof: rfl

中文:
定理 coe_inv
  条件: (e : E ≃ₗᵢ[R] E)
  结论: ⇑e⁻¹ = e.symm
  证明: rfl
-/
theorem coe_inv (e : E ≃ₗᵢ[R] E) : ⇑e⁻¹ = e.symm :=
  rfl

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : E ≃ₗᵢ[R] E) = refl _ _
  proof: rfl

中文:
定理 one_def
  结论: (1 : E ≃ₗᵢ[R] E) = refl _ _
  证明: rfl
-/
theorem one_def : (1 : E ≃ₗᵢ[R] E) = refl _ _ :=
  rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (e e' : E ≃ₗᵢ[R] E)
  statement: (e * e' : E ≃ₗᵢ[R] E) = e'.trans e
  proof: rfl

中文:
定理 mul_def
  条件: (e e' : E ≃ₗᵢ[R] E)
  结论: (e * e' : E ≃ₗᵢ[R] E) = e'.trans e
  证明: rfl
-/
theorem mul_def (e e' : E ≃ₗᵢ[R] E) : (e * e' : E ≃ₗᵢ[R] E) = e'.trans e :=
  rfl

/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (e : E ≃ₗᵢ[R] E)
  statement: (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm
  proof: rfl

中文:
定理 inv_def
  条件: (e : E ≃ₗᵢ[R] E)
  结论: (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm
  证明: rfl
-/
theorem inv_def (e : E ≃ₗᵢ[R] E) : (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm :=
  rfl

/--
lemma `toContinuousLinearEquiv_one` / 引理 `toContinuousLinearEquiv_one`

English:
lemma toContinuousLinearEquiv_one
  statement: toContinuousLinearEquiv (1 : E ≃ₗᵢ[R] E) = 1
  proof: rfl

中文:
引理 toContinuousLinearEquiv_one
  结论: toContinuousLinearEquiv (1 : E ≃ₗᵢ[R] E) = 1
  证明: rfl
-/
@[simp] lemma toContinuousLinearEquiv_one : toContinuousLinearEquiv (1 : E ≃ₗᵢ[R] E) = 1 := rfl

/--
lemma `toContinuousLinearEquiv_mul` / 引理 `toContinuousLinearEquiv_mul`

English:
lemma toContinuousLinearEquiv_mul
  given: (e e' : E ≃ₗᵢ[R] E)
  proof: rfl

中文:
引理 toContinuousLinearEquiv_mul
  条件: (e e' : E ≃ₗᵢ[R] E)
  证明: rfl
-/
@[simp] lemma toContinuousLinearEquiv_mul (e e' : E ≃ₗᵢ[R] E) :
    toContinuousLinearEquiv (e * e') = e.toContinuousLinearEquiv * e'.toContinuousLinearEquiv := rfl

/--
lemma `toContinuousLinearEquiv_inv` / 引理 `toContinuousLinearEquiv_inv`

English:
lemma toContinuousLinearEquiv_inv
  given: (e : E ≃ₗᵢ[R] E)
  proof: rfl

中文:
引理 toContinuousLinearEquiv_inv
  条件: (e : E ≃ₗᵢ[R] E)
  证明: rfl
-/
@[simp] lemma toContinuousLinearEquiv_inv (e : E ≃ₗᵢ[R] E) :
    toContinuousLinearEquiv e⁻¹ = e.toContinuousLinearEquiv⁻¹ := rfl

/-! Lemmas about mixing the group structure with definitions. Because we have multiple ways to
express `LinearIsometryEquiv.refl`, `LinearIsometryEquiv.symm`, and
`LinearIsometryEquiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it
after simp.

This copies the approach used by the lemmas near `Equiv.Perm.trans_one`. -/


@[simp]
/--
theorem `trans_one` / 定理 `trans_one`

English:
theorem trans_one
  statement: e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e
  proof: trans_refl _

@[simp]

中文:
定理 trans_one
  结论: e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e
  证明: trans_refl _

@[simp]

Depends on / 依赖: trans_refl
-/
theorem trans_one : e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e :=
  trans_refl _

@[simp]
/--
theorem `one_trans` / 定理 `one_trans`

English:
theorem one_trans
  statement: (1 : E ≃ₗᵢ[R] E).trans e = e
  proof: refl_trans _

@[simp]

中文:
定理 one_trans
  结论: (1 : E ≃ₗᵢ[R] E).trans e = e
  证明: refl_trans _

@[simp]

Depends on / 依赖: refl_trans
-/
theorem one_trans : (1 : E ≃ₗᵢ[R] E).trans e = e :=
  refl_trans _

@[simp]
/--
theorem `refl_mul` / 定理 `refl_mul`

English:
theorem refl_mul
  given: (e : E ≃ₗᵢ[R] E)
  statement: refl _ _ * e = e
  proof: trans_refl _

@[simp]

中文:
定理 refl_mul
  条件: (e : E ≃ₗᵢ[R] E)
  结论: refl _ _ * e = e
  证明: trans_refl _

@[simp]

Depends on / 依赖: trans_refl
-/
theorem refl_mul (e : E ≃ₗᵢ[R] E) : refl _ _ * e = e :=
  trans_refl _

@[simp]
/--
theorem `mul_refl` / 定理 `mul_refl`

English:
theorem mul_refl
  given: (e : E ≃ₗᵢ[R] E)
  statement: e * refl _ _ = e
  proof: refl_trans _

中文:
定理 mul_refl
  条件: (e : E ≃ₗᵢ[R] E)
  结论: e * refl _ _ = e
  证明: refl_trans _

Depends on / 依赖: refl_trans
-/
theorem mul_refl (e : E ≃ₗᵢ[R] E) : e * refl _ _ = e :=
  refl_trans _

/--
Instance `instCoeTCContinuousLinearEquiv` / 实例 `instCoeTCContinuousLinearEquiv`

English:
instance instCoeTCContinuousLinearEquiv
  signature: : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ≃SL[σ₁₂] E₂)
  body: ⟨fun e => e.toContinuousLinearEquiv⟩

中文:
实例 instCoeTCContinuousLinearEquiv
  签名: : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ≃SL[σ₁₂] E₂)
  定义体: ⟨fun e => e.toContinuousLinearEquiv⟩

Depends on / 依赖: e.toContinuousLinearEquiv, toContinuousLinearEquiv
-/
instance instCoeTCContinuousLinearEquiv : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ≃SL[σ₁₂] E₂) :=
  ⟨fun e => e.toContinuousLinearEquiv⟩

/--
Instance `instCoeTCContinuousLinearMap` / 实例 `instCoeTCContinuousLinearMap`

English:
instance instCoeTCContinuousLinearMap
  signature: : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ->SL[σ₁₂] E₂)
  body: ⟨fun e => ↑(e : E ≃SL[σ₁₂] E₂)⟩

中文:
实例 instCoeTCContinuousLinearMap
  签名: : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ->SL[σ₁₂] E₂)
  定义体: ⟨fun e => ↑(e : E ≃SL[σ₁₂] E₂)⟩
-/
instance instCoeTCContinuousLinearMap : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ->SL[σ₁₂] E₂) :=
  ⟨fun e => ↑(e : E ≃SL[σ₁₂] E₂)⟩

/--
theorem `toContinuousLinearMap_toLinearIsometry` / 定理 `toContinuousLinearMap_toLinearIsometry`

English:
theorem toContinuousLinearMap_toLinearIsometry
  proof: rfl

中文:
定理 toContinuousLinearMap_toLinearIsometry
  证明: rfl
-/
theorem toContinuousLinearMap_toLinearIsometry :
    e.toLinearIsometry.toContinuousLinearMap = e := rfl

/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: ⇑(e : E ≃SL[σ₁₂] E₂) = e
  proof: rfl

中文:
定理 coe_coe
  结论: ⇑(e : E ≃SL[σ₁₂] E₂) = e
  证明: rfl
-/
theorem coe_coe : ⇑(e : E ≃SL[σ₁₂] E₂) = e := rfl

/--
theorem `coe_coe''` / 定理 `coe_coe''`

English:
theorem coe_coe''
  statement: ⇑(e : E ->SL[σ₁₂] E₂) = e
  proof: rfl

中文:
定理 coe_coe''
  结论: ⇑(e : E ->SL[σ₁₂] E₂) = e
  证明: rfl
-/
theorem coe_coe'' : ⇑(e : E ->SL[σ₁₂] E₂) = e := rfl

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: e 0 = 0
  proof: e.1.map_zero

中文:
定理 map_zero
  结论: e 0 = 0
  证明: e.1.map_zero

Depends on / 依赖: map_zero
-/
theorem map_zero : e 0 = 0 :=
  e.1.map_zero

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (x y : E)
  statement: e (x + y) = e x + e y
  proof: e.1.map_add x y

中文:
定理 map_add
  条件: (x y : E)
  结论: e (x + y) = e x + e y
  证明: e.1.map_add x y

Depends on / 依赖: map_add
-/
theorem map_add (x y : E) : e (x + y) = e x + e y :=
  e.1.map_add x y

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (x y : E)
  statement: e (x - y) = e x - e y
  proof: e.1.map_sub x y

中文:
定理 map_sub
  条件: (x y : E)
  结论: e (x - y) = e x - e y
  证明: e.1.map_sub x y

Depends on / 依赖: map_sub
-/
theorem map_sub (x y : E) : e (x - y) = e x - e y :=
  e.1.map_sub x y

/--
theorem `map_smulₛₗ` / 定理 `map_smulₛₗ`

English:
theorem map_smulₛₗ
  given: (c : R) (x : E)
  statement: e (c • x) = σ₁₂ c • e x
  proof: e.1.map_smulₛₗ c x

中文:
定理 map_smulₛₗ
  条件: (c : R) (x : E)
  结论: e (c • x) = σ₁₂ c • e x
  证明: e.1.map_smulₛₗ c x
-/
theorem map_smulₛₗ (c : R) (x : E) : e (c • x) = σ₁₂ c • e x :=
  e.1.map_smulₛₗ c x

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E)
  statement: e (c • x) = c • e x
  proof: e.1.map_smul c x


@[simp]

中文:
定理 map_smul
  条件: [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E)
  结论: e (c • x) = c • e x
  证明: e.1.map_smul c x


@[simp]

Depends on / 依赖: map_smul
-/
theorem map_smul [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E) : e (c • x) = c • e x :=
  e.1.map_smul c x


@[simp]
/--
theorem `dist_map` / 定理 `dist_map`

English:
theorem dist_map
  given: (x y : E)
  statement: dist (e x) (e y) = dist x y
  proof: e.toLinearIsometry.dist_map x y

@[simp]

中文:
定理 dist_map
  条件: (x y : E)
  结论: dist (e x) (e y) = dist x y
  证明: e.toLinearIsometry.dist_map x y

@[simp]

Depends on / 依赖: dist_map, e.toLinearIsometry.dist_map, toLinearIsometry
-/
theorem dist_map (x y : E) : dist (e x) (e y) = dist x y :=
  e.toLinearIsometry.dist_map x y

@[simp]
/--
theorem `edist_map` / 定理 `edist_map`

English:
theorem edist_map
  given: (x y : E)
  statement: edist (e x) (e y) = edist x y
  proof: e.toLinearIsometry.edist_map x y

中文:
定理 edist_map
  条件: (x y : E)
  结论: edist (e x) (e y) = edist x y
  证明: e.toLinearIsometry.edist_map x y

Depends on / 依赖: e.toLinearIsometry.edist_map, edist_map, toLinearIsometry
-/
theorem edist_map (x y : E) : edist (e x) (e y) = edist x y :=
  e.toLinearIsometry.edist_map x y

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  statement: Bijective e
  proof: e.1.bijective

中文:
定理 bijective
  结论: Bijective e
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
  结论: Injective e
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
  结论: Surjective e
  证明: e.1.surjective
-/
protected theorem surjective : Surjective e :=
  e.1.surjective

/--
theorem `map_eq_iff` / 定理 `map_eq_iff`

English:
theorem map_eq_iff
  given: {x y : E}
  statement: e x = e y ↔ x = y
  proof: e.injective.eq_iff

中文:
定理 map_eq_iff
  条件: {x y : E}
  结论: e x = e y ↔ x = y
  证明: e.injective.eq_iff

Depends on / 依赖: e.injective.eq_iff, eq_iff, injective
-/
theorem map_eq_iff {x y : E} : e x = e y ↔ x = y :=
  e.injective.eq_iff

/--
theorem `map_ne` / 定理 `map_ne`

English:
theorem map_ne
  given: {x y : E} (h : x != y)
  statement: e x != e y
  proof: e.injective.ne h

中文:
定理 map_ne
  条件: {x y : E} (h : x != y)
  结论: e x != e y
  证明: e.injective.ne h

Depends on / 依赖: e.injective.ne, injective
-/
theorem map_ne {x y : E} (h : x != y) : e x != e y :=
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

中文:
定理 antilipschitz
  结论: AntilipschitzWith 1 e
  证明: e.isometry.antilipschitz
-/
protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.isometry.antilipschitz

/--
theorem `image_eq_preimage_symm` / 定理 `image_eq_preimage_symm`

English:
theorem image_eq_preimage_symm
  given: (s : Set E)
  statement: e '' s = e.symm ⁻¹' s
  proof: e.toLinearEquiv.image_eq_preimage_symm s

@[simp]

中文:
定理 image_eq_preimage_symm
  条件: (s : Set E)
  结论: e '' s = e.symm ⁻¹' s
  证明: e.toLinearEquiv.image_eq_preimage_symm s

@[simp]

Depends on / 依赖: e.toLinearEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toLinearEquiv
-/
theorem image_eq_preimage_symm (s : Set E) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.image_eq_preimage_symm s

@[simp]
/--
theorem `ediam_image` / 定理 `ediam_image`

English:
theorem ediam_image
  given: (s : Set E)
  statement: Metric.ediam (e '' s) = Metric.ediam s
  proof: e.isometry.ediam_image s

@[simp]

中文:
定理 ediam_image
  条件: (s : Set E)
  结论: Metric.ediam (e '' s) = Metric.ediam s
  证明: e.isometry.ediam_image s

@[simp]

Depends on / 依赖: e.isometry.ediam_image, ediam_image, isometry
-/
theorem ediam_image (s : Set E) : Metric.ediam (e '' s) = Metric.ediam s :=
  e.isometry.ediam_image s

@[simp]
/--
theorem `diam_image` / 定理 `diam_image`

English:
theorem diam_image
  given: (s : Set E)
  statement: Metric.diam (e '' s) = Metric.diam s
  proof: e.isometry.diam_image s

@[simp]

中文:
定理 diam_image
  条件: (s : Set E)
  结论: Metric.diam (e '' s) = Metric.diam s
  证明: e.isometry.diam_image s

@[simp]

Depends on / 依赖: diam_image, e.isometry.diam_image, isometry
-/
theorem diam_image (s : Set E) : Metric.diam (e '' s) = Metric.diam s :=
  e.isometry.diam_image s

@[simp]
/--
theorem `preimage_ball` / 定理 `preimage_ball`

English:
theorem preimage_ball
  given: (x : E₂) (r : Real)
  statement: e ⁻¹' Metric.ball x r = Metric.ball (e.symm x) r
  proof: e.toIsometryEquiv.preimage_ball x r

@[simp]

中文:
定理 preimage_ball
  条件: (x : E₂) (r : 实数)
  结论: e ⁻¹' Metric.ball x r = Metric.ball (e.symm x) r
  证明: e.toIsometryEquiv.preimage_ball x r

@[simp]

Depends on / 依赖: e.toIsometryEquiv.preimage_ball, preimage_ball, toIsometryEquiv
-/
theorem preimage_ball (x : E₂) (r : Real) : e ⁻¹' Metric.ball x r = Metric.ball (e.symm x) r :=
  e.toIsometryEquiv.preimage_ball x r

@[simp]
/--
theorem `preimage_sphere` / 定理 `preimage_sphere`

English:
theorem preimage_sphere
  given: (x : E₂) (r : Real)
  statement: e ⁻¹' Metric.sphere x r = Metric.sphere (e.symm x) r
  proof: e.toIsometryEquiv.preimage_sphere x r

@[simp]

中文:
定理 preimage_sphere
  条件: (x : E₂) (r : 实数)
  结论: e ⁻¹' Metric.sphere x r = Metric.sphere (e.symm x) r
  证明: e.toIsometryEquiv.preimage_sphere x r

@[simp]

Depends on / 依赖: e.toIsometryEquiv.preimage_sphere, preimage_sphere, toIsometryEquiv
-/
theorem preimage_sphere (x : E₂) (r : Real) : e ⁻¹' Metric.sphere x r = Metric.sphere (e.symm x) r :=
  e.toIsometryEquiv.preimage_sphere x r

@[simp]
/--
theorem `preimage_closedBall` / 定理 `preimage_closedBall`

English:
theorem preimage_closedBall
  given: (x : E₂) (r : Real)
  proof: e.toIsometryEquiv.preimage_closedBall x r

@[simp]

中文:
定理 preimage_closedBall
  条件: (x : E₂) (r : 实数)
  证明: e.toIsometryEquiv.preimage_closedBall x r

@[simp]

Depends on / 依赖: e.toIsometryEquiv.preimage_closedBall, preimage_closedBall, toIsometryEquiv
-/
theorem preimage_closedBall (x : E₂) (r : Real) :
    e ⁻¹' Metric.closedBall x r = Metric.closedBall (e.symm x) r :=
  e.toIsometryEquiv.preimage_closedBall x r

@[simp]
/--
theorem `image_ball` / 定理 `image_ball`

English:
theorem image_ball
  given: (x : E) (r : Real)
  statement: e '' Metric.ball x r = Metric.ball (e x) r
  proof: e.toIsometryEquiv.image_ball x r

@[simp]

中文:
定理 image_ball
  条件: (x : E) (r : 实数)
  结论: e '' Metric.ball x r = Metric.ball (e x) r
  证明: e.toIsometryEquiv.image_ball x r

@[simp]

Depends on / 依赖: e.toIsometryEquiv.image_ball, image_ball, toIsometryEquiv
-/
theorem image_ball (x : E) (r : Real) : e '' Metric.ball x r = Metric.ball (e x) r :=
  e.toIsometryEquiv.image_ball x r

@[simp]
/--
theorem `image_sphere` / 定理 `image_sphere`

English:
theorem image_sphere
  given: (x : E) (r : Real)
  statement: e '' Metric.sphere x r = Metric.sphere (e x) r
  proof: e.toIsometryEquiv.image_sphere x r

@[simp]

中文:
定理 image_sphere
  条件: (x : E) (r : 实数)
  结论: e '' Metric.sphere x r = Metric.sphere (e x) r
  证明: e.toIsometryEquiv.image_sphere x r

@[simp]

Depends on / 依赖: e.toIsometryEquiv.image_sphere, image_sphere, toIsometryEquiv
-/
theorem image_sphere (x : E) (r : Real) : e '' Metric.sphere x r = Metric.sphere (e x) r :=
  e.toIsometryEquiv.image_sphere x r

@[simp]
/--
theorem `image_closedBall` / 定理 `image_closedBall`

English:
theorem image_closedBall
  given: (x : E) (r : Real)
  statement: e '' Metric.closedBall x r = Metric.closedBall (e x) r
  proof: e.toIsometryEquiv.image_closedBall x r

中文:
定理 image_closedBall
  条件: (x : E) (r : 实数)
  结论: e '' Metric.closedBall x r = Metric.closedBall (e x) r
  证明: e.toIsometryEquiv.image_closedBall x r

Depends on / 依赖: e.toIsometryEquiv.image_closedBall, image_closedBall, toIsometryEquiv
-/
theorem image_closedBall (x : E) (r : Real) : e '' Metric.closedBall x r = Metric.closedBall (e x) r :=
  e.toIsometryEquiv.image_closedBall x r

variable {α : Type*} [TopologicalSpace α]

@[simp]
/--
theorem `comp_continuousOn_iff` / 定理 `comp_continuousOn_iff`

English:
theorem comp_continuousOn_iff
  given: {f : α -> E} {s : Set α}
  statement: ContinuousOn (e ∘ f) s ↔ ContinuousOn f s
  proof: e.isometry.comp_continuousOn_iff

@[simp]

中文:
定理 comp_continuousOn_iff
  条件: {f : α -> E} {s : Set α}
  结论: ContinuousOn (e ∘ f) s ↔ ContinuousOn f s
  证明: e.isometry.comp_continuousOn_iff

@[simp]

Depends on / 依赖: comp_continuousOn_iff, e.isometry.comp_continuousOn_iff, isometry
-/
theorem comp_continuousOn_iff {f : α -> E} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.isometry.comp_continuousOn_iff

@[simp]
/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: {f : α -> E}
  statement: Continuous (e ∘ f) ↔ Continuous f
  proof: e.isometry.comp_continuous_iff

中文:
定理 comp_continuous_iff
  条件: {f : α -> E}
  结论: Continuous (e ∘ f) ↔ Continuous f
  证明: e.isometry.comp_continuous_iff

Depends on / 依赖: comp_continuous_iff, e.isometry.comp_continuous_iff, isometry
-/
theorem comp_continuous_iff {f : α -> E} : Continuous (e ∘ f) ↔ Continuous f :=
  e.isometry.comp_continuous_iff

/--
Instance `completeSpace_map` / 实例 `completeSpace_map`

English:
instance completeSpace_map
  signature: (p : Submodule R E) [CompleteSpace p]
  body: e.toLinearIsometry.completeSpace_map p

中文:
实例 completeSpace_map
  签名: (p : Submodule R E) [CompleteSpace p]
  定义体: e.toLinearIsometry.completeSpace_map p

Depends on / 依赖: completeSpace_map, e.toLinearIsometry.completeSpace_map, toLinearIsometry
-/
instance completeSpace_map (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map (e : E ->ₛₗ[σ₁₂] E₂)) :=
  e.toLinearIsometry.completeSpace_map p

/--
Definition of `ofSurjective` / `ofSurjective` 的定义

English:
definition ofSurjective
  signature: (f : F ->ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f)
  body: { LinearEquiv.ofBijective f.toLinearMap ⟨f.injective, hfr⟩ with norm_map' := f.norm_map }

@[simp]

中文:
定义 ofSurjective
  签名: (f : F ->ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f)
  定义体: { LinearEquiv.ofBijective f.toLinearMap ⟨f.injective, hfr⟩ with norm_map' := f.norm_map }

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, f.injective, f.norm_map, f.toLinearMap, injective, norm_map, ofBijective, toLinearMap
-/
noncomputable def ofSurjective (f : F ->ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    F ≃ₛₗᵢ[σ₁₂] E₂ :=
  { LinearEquiv.ofBijective f.toLinearMap ⟨f.injective, hfr⟩ with norm_map' := f.norm_map }

@[simp]
/--
theorem `coe_ofSurjective` / 定理 `coe_ofSurjective`

English:
theorem coe_ofSurjective
  given: (f : F ->ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f)
  proof: by
  ext
  rfl

中文:
定理 coe_ofSurjective
  条件: (f : F ->ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f)
  证明: by
  ext
  rfl
-/
theorem coe_ofSurjective (f : F ->ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    ⇑(LinearIsometryEquiv.ofSurjective f hfr) = f := by
  ext
  rfl

/--
Definition of `ofLinearIsometry` / `ofLinearIsometry` 的定义

English:
definition ofLinearIsometry
  signature: (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E)
  body: { toLinearEquiv := LinearEquiv.ofLinearMap f.toLinearMap g h₁ h₂
    norm_map' := fun x => f.norm_map x }

@[simp]

中文:
定义 ofLinearIsometry
  签名: (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E)
  定义体: { toLinearEquiv := LinearEquiv.ofLinearMap f.toLinearMap g h₁ h₂
    norm_map' := fun x => f.norm_map x }

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, f.norm_map, f.toLinearMap, norm_map, ofLinearMap, toLinearEquiv, toLinearMap
-/
def ofLinearIsometry (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
  { toLinearEquiv := LinearEquiv.ofLinearMap f.toLinearMap g h₁ h₂
    norm_map' := fun x => f.norm_map x }

@[simp]
/--
theorem `coe_ofLinearIsometry` / 定理 `coe_ofLinearIsometry`

English:
theorem coe_ofLinearIsometry
  statement: (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E)
  proof: rfl

@[simp]

中文:
定理 coe_ofLinearIsometry
  结论: (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E)
  证明: rfl

@[simp]
-/
theorem coe_ofLinearIsometry (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    (ofLinearIsometry f g h₁ h₂ : E -> E₂) = (f : E -> E₂) :=
  rfl

@[simp]
/--
theorem `coe_ofLinearIsometry_symm` / 定理 `coe_ofLinearIsometry_symm`

English:
theorem coe_ofLinearIsometry_symm
  statement: (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E)
  proof: rfl

中文:
定理 coe_ofLinearIsometry_symm
  结论: (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E)
  证明: rfl
-/
theorem coe_ofLinearIsometry_symm (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    ((ofLinearIsometry f g h₁ h₂).symm : E₂ -> E) = (g : E₂ -> E) :=
  rfl

variable (R) in
/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: : E ≃ₗᵢ[R] E
  body: { LinearEquiv.neg R with norm_map' := norm_neg }

@[simp]

中文:
定义 neg
  签名: : E ≃ₗᵢ[R] E
  定义体: { LinearEquiv.neg R with norm_map' := norm_neg }

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.neg, norm_map, norm_neg
-/
def neg : E ≃ₗᵢ[R] E :=
  { LinearEquiv.neg R with norm_map' := norm_neg }

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: (neg R : E -> E) = fun x => -x
  proof: rfl

@[simp]

中文:
定理 coe_neg
  结论: (neg R : E -> E) = fun x => -x
  证明: rfl

@[simp]
-/
theorem coe_neg : (neg R : E -> E) = fun x => -x :=
  rfl

@[simp]
/--
theorem `symm_neg` / 定理 `symm_neg`

English:
theorem symm_neg
  statement: (neg R : E ≃ₗᵢ[R] E).symm = neg R
  proof: rfl

中文:
定理 symm_neg
  结论: (neg R : E ≃ₗᵢ[R] E).symm = neg R
  证明: rfl
-/
theorem symm_neg : (neg R : E ≃ₗᵢ[R] E).symm = neg R :=
  rfl

variable (R E E₂)

/-- The natural equivalence `E × E₂ ≃ E₂ × E` is a linear isometry. -/
@[simps! apply]
/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: [Module R E₂]
  body: ⟨LinearEquiv.prodComm R E E₂, by intro; simp [norm, sup_comm]⟩

@[simp]

中文:
定义 prodComm
  签名: [Module R E₂]
  定义体: ⟨LinearEquiv.prodComm R E E₂, by intro; simp [norm, sup_comm]⟩

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.prodComm, prodComm, sup_comm
-/
def prodComm [Module R E₂] : E × E₂ ≃ₗᵢ[R] E₂ × E :=
  ⟨LinearEquiv.prodComm R E E₂, by intro; simp [norm, sup_comm]⟩

@[simp]
/--
theorem `symm_prodComm` / 定理 `symm_prodComm`

English:
theorem symm_prodComm
  given: [Module R E₂]
  statement: (prodComm R E E₂).symm = prodComm R E₂ E
  proof: rfl

中文:
定理 symm_prodComm
  条件: [Module R E₂]
  结论: (prodComm R E E₂).symm = prodComm R E₂ E
  证明: rfl
-/
theorem symm_prodComm [Module R E₂] : (prodComm R E E₂).symm = prodComm R E₂ E :=
  rfl

variable (E₃)

/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: [Module R E₂] [Module R E₃]
  body: { LinearEquiv.prodAssoc R E E₂ E₃ with
    norm_map' := by
      rintro ⟨⟨e, f⟩, g⟩
      simp only [LinearEquiv.prodAssoc_apply, AddEquiv.toEquiv_eq_coe,
        Equiv.toFun_as_coe, EquivLike.coe_coe, AddEquiv.coe_prodAssoc,
        Equiv.prodAssoc_apply, Prod.norm_def, max_assoc] }

@[simp]

中文:
定义 prodAssoc
  签名: [Module R E₂] [Module R E₃]
  定义体: { LinearEquiv.prodAssoc R E E₂ E₃ with
    norm_map' := by
      rintro ⟨⟨e, f⟩, g⟩
      simp only [LinearEquiv.prodAssoc_apply, AddEquiv.toEquiv_eq_coe,
        Equiv.toFun_as_coe, EquivLike.coe_coe, AddEquiv.coe_prodAssoc,
        Equiv.prodAssoc_apply, Prod.norm_def, max_assoc] }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.coe_prodAssoc, AddEquiv.toEquiv_eq_coe, Equiv.prodAssoc_apply, Equiv.toFun_as_coe, EquivLike, EquivLike.coe_coe, LinearEquiv, LinearEquiv.prodAssoc, LinearEquiv.prodAssoc_apply, Prod.norm_def, coe_coe, coe_prodAssoc, max_assoc, norm_def, norm_map, prodAssoc, prodAssoc_apply, toEquiv_eq_coe, toFun_as_coe
-/
def prodAssoc [Module R E₂] [Module R E₃] : (E × E₂) × E₃ ≃ₗᵢ[R] E × E₂ × E₃ :=
  { LinearEquiv.prodAssoc R E E₂ E₃ with
    norm_map' := by
      rintro ⟨⟨e, f⟩, g⟩
      simp only [LinearEquiv.prodAssoc_apply, AddEquiv.toEquiv_eq_coe,
        Equiv.toFun_as_coe, EquivLike.coe_coe, AddEquiv.coe_prodAssoc,
        Equiv.prodAssoc_apply, Prod.norm_def, max_assoc] }

@[simp]
/--
theorem `coe_prodAssoc` / 定理 `coe_prodAssoc`

English:
theorem coe_prodAssoc
  given: [Module R E₂] [Module R E₃]
  proof: rfl

@[simp]

中文:
定理 coe_prodAssoc
  条件: [Module R E₂] [Module R E₃]
  证明: rfl

@[simp]
-/
theorem coe_prodAssoc [Module R E₂] [Module R E₃] :
    (prodAssoc R E E₂ E₃ : (E × E₂) × E₃ -> E × E₂ × E₃) = Equiv.prodAssoc E E₂ E₃ :=
  rfl

@[simp]
/--
theorem `coe_prodAssoc_symm` / 定理 `coe_prodAssoc_symm`

English:
theorem coe_prodAssoc_symm
  given: [Module R E₂] [Module R E₃]
  proof: rfl

中文:
定理 coe_prodAssoc_symm
  条件: [Module R E₂] [Module R E₃]
  证明: rfl
-/
theorem coe_prodAssoc_symm [Module R E₂] [Module R E₃] :
    ((prodAssoc R E E₂ E₃).symm : E × E₂ × E₃ -> (E × E₂) × E₃) = (Equiv.prodAssoc E E₂ E₃).symm :=
  rfl

/-- If `p` is a submodule that is equal to `⊤`, then `LinearIsometryEquiv.ofTop p hp` is the
"identity" equivalence between `p` and `E`. -/
@[simps! toLinearEquiv apply symm_apply_coe]
/--
Definition of `ofTop` / `ofTop` 的定义

English:
definition ofTop
  signature: {R : Type*} [Ring R] [Module R E] (p : Submodule R E) (hp : p = ⊤)
  body: { p.subtypeₗᵢ with toLinearEquiv := LinearEquiv.ofTop p hp }

中文:
定义 ofTop
  签名: {R : 类型} [Ring R] [Module R E] (p : Submodule R E) (hp : p = ⊤)
  定义体: { p.subtypeₗᵢ with toLinearEquiv := LinearEquiv.ofTop p hp }

Depends on / 依赖: LinearEquiv, LinearEquiv.ofTop, p.subtype, toLinearEquiv
-/
def ofTop {R : Type*} [Ring R] [Module R E] (p : Submodule R E) (hp : p = ⊤) : p ≃ₗᵢ[R] E :=
  { p.subtypeₗᵢ with toLinearEquiv := LinearEquiv.ofTop p hp }

variable {R E E₂ E₃} {R' : Type*} [Ring R']
variable [Module R' E] (p q : Submodule R' E)

/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (hpq : p = q)
  body: { LinearEquiv.ofEq p q hpq with norm_map' := fun _ => rfl }

中文:
定义 ofEq
  签名: (hpq : p = q)
  定义体: { LinearEquiv.ofEq p q hpq with norm_map' := fun _ => rfl }

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq, norm_map
-/
def ofEq (hpq : p = q) : p ≃ₗᵢ[R'] q :=
  { LinearEquiv.ofEq p q hpq with norm_map' := fun _ => rfl }

variable {p q}

@[simp]
/--
theorem `coe_ofEq_apply` / 定理 `coe_ofEq_apply`

English:
theorem coe_ofEq_apply
  given: (h : p = q) (x : p)
  statement: (ofEq p q h x : E) = x
  proof: rfl

@[simp]

中文:
定理 coe_ofEq_apply
  条件: (h : p = q) (x : p)
  结论: (ofEq p q h x : E) = x
  证明: rfl

@[simp]
-/
theorem coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : E) = x :=
  rfl

@[simp]
/--
theorem `ofEq_symm` / 定理 `ofEq_symm`

English:
theorem ofEq_symm
  given: (h : p = q)
  statement: (ofEq p q h).symm = ofEq q p h.symm
  proof: rfl

@[simp]

中文:
定理 ofEq_symm
  条件: (h : p = q)
  结论: (ofEq p q h).symm = ofEq q p h.symm
  证明: rfl

@[simp]
-/
theorem ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm :=
  rfl

@[simp]
/--
theorem `ofEq_rfl` / 定理 `ofEq_rfl`

English:
theorem ofEq_rfl
  statement: ofEq p p rfl = LinearIsometryEquiv.refl R' p
  proof: rfl

中文:
定理 ofEq_rfl
  结论: ofEq p p rfl = LinearIsometryEquiv.refl R' p
  证明: rfl
-/
theorem ofEq_rfl : ofEq p p rfl = LinearIsometryEquiv.refl R' p := rfl

section submoduleMap

variable {R R₁ R₂ M M₂ : Type*}
variable [Ring R] [Ring R₂] [SeminormedAddCommGroup M] [SeminormedAddCommGroup M₂]
variable [Module R M] [Module R₂ M₂] {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

/-- A linear isometry equivalence between two modules restricts to a
linear isometry equivalence from any submodule `p` of the domain onto
the image of that submodule.

This is a version of `LinearEquiv.submoduleMap` extended to linear isometry equivalences. -/
@[simps!]
/--
Definition of `submoduleMap` / `submoduleMap` 的定义

English:
definition submoduleMap
  signature: (p : Submodule R M) (e : M ≃ₛₗᵢ[σ₁₂] M₂)
  body: { e.toLinearEquiv.submoduleMap p with norm_map' x := e.norm_map' x }

中文:
定义 submoduleMap
  签名: (p : Submodule R M) (e : M ≃ₛₗᵢ[σ₁₂] M₂)
  定义体: { e.toLinearEquiv.submoduleMap p with norm_map' x := e.norm_map' x }

Depends on / 依赖: e.norm_map, e.toLinearEquiv.submoduleMap, norm_map, submoduleMap, toLinearEquiv
-/
def submoduleMap (p : Submodule R M) (e : M ≃ₛₗᵢ[σ₁₂] M₂) :
    p ≃ₛₗᵢ[σ₁₂] p.map (e : M ->ₛₗ[σ₁₂] M₂) :=
  { e.toLinearEquiv.submoduleMap p with norm_map' x := e.norm_map' x }

end submoduleMap

end LinearIsometryEquiv

/--
theorem `Module.Basis.ext_linearIsometry` / 定理 `Module.Basis.ext_linearIsometry`

English:
theorem Module.Basis.ext_linearIsometry
  statement: {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ->ₛₗᵢ[σ₁₂] E₂}
  proof: LinearIsometry.toLinearMap_injective b.ext h

中文:
定理 Module.Basis.ext_linearIsometry
  结论: {ι : 类型} (b : Basis ι R E) {f₁ f₂ : E ->ₛₗᵢ[σ₁₂] E₂}
  证明: LinearIsometry.toLinearMap_injective b.ext h

Depends on / 依赖: LinearIsometry, LinearIsometry.toLinearMap_injective, b.ext, toLinearMap_injective
-/
theorem Module.Basis.ext_linearIsometry {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ->ₛₗᵢ[σ₁₂] E₂}
    (h : forall i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
LinearIsometry.toLinearMap_injective b.ext h

/--
theorem `Module.Basis.ext_linearIsometryEquiv` / 定理 `Module.Basis.ext_linearIsometryEquiv`

English:
theorem Module.Basis.ext_linearIsometryEquiv
  statement: {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂}
  proof: LinearIsometryEquiv.toLinearEquiv_injective b.ext' h

中文:
定理 Module.Basis.ext_linearIsometryEquiv
  结论: {ι : 类型} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂}
  证明: LinearIsometryEquiv.toLinearEquiv_injective b.ext' h

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.toLinearEquiv_injective, b.ext, toLinearEquiv_injective
-/
theorem Module.Basis.ext_linearIsometryEquiv {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂}
    (h : forall i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
LinearIsometryEquiv.toLinearEquiv_injective b.ext' h

/-- Reinterpret a `LinearIsometry` as a `LinearIsometryEquiv` to the range. -/
@[simps! apply_coe]
/--
Definition of `LinearIsometry.equivRange` / `LinearIsometry.equivRange` 的定义

English:
definition LinearIsometry.equivRange
  signature: {R S : Type*} [Semiring R] [Ring S] [Module S E]
  body: { f with toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap f.injective }

中文:
定义 LinearIsometry.equivRange
  签名: {R S : 类型} [Semiring R] [Ring S] [Module S E]
  定义体: { f with toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap f.injective }

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, f.injective, f.toLinearMap, injective, ofInjective, toLinearEquiv, toLinearMap
-/
noncomputable def LinearIsometry.equivRange {R S : Type*} [Semiring R] [Ring S] [Module S E]
    [Module R F] {σ₁₂ : R ->+* S} {σ₂₁ : S ->+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (f : F ->ₛₗᵢ[σ₁₂] E) : F ≃ₛₗᵢ[σ₁₂] (LinearMap.range f.toLinearMap) :=
  { f with toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap f.injective }

namespace MulOpposite
variable {R H : Type*} [Semiring R] [SeminormedAddCommGroup H] [Module R H]

/--
theorem `isometry_opLinearEquiv` / 定理 `isometry_opLinearEquiv`

English:
theorem isometry_opLinearEquiv
  statement: Isometry (opLinearEquiv R (M := H))
  proof: fun _ _ => rfl

中文:
定理 isometry_opLinearEquiv
  结论: Isometry (opLinearEquiv R (M := H))
  证明: fun _ _ => rfl
-/
theorem isometry_opLinearEquiv : Isometry (opLinearEquiv R (M := H)) := fun _ _ => rfl

variable (R H) in
/-- The linear isometry equivalence version of the function `op`. -/
@[simps!]
/--
Definition of `opLinearIsometryEquiv` / `opLinearIsometryEquiv` 的定义

English:
definition opLinearIsometryEquiv
  signature: : H ≃ₗᵢ[R] Hᵐᵒᵖ where
  body: opLinearEquiv R
  norm_map' _ := rfl

@[simp]

中文:
定义 opLinearIsometryEquiv
  签名: : H ≃ₗᵢ[R] Hᵐᵒᵖ where
  定义体: opLinearEquiv R
  norm_map' _ := rfl

@[simp]

Depends on / 依赖: opLinearEquiv
-/
def opLinearIsometryEquiv : H ≃ₗᵢ[R] Hᵐᵒᵖ where
  toLinearEquiv := opLinearEquiv R
  norm_map' _ := rfl

@[simp]
/--
theorem `toLinearEquiv_opLinearIsometryEquiv` / 定理 `toLinearEquiv_opLinearIsometryEquiv`

English:
theorem toLinearEquiv_opLinearIsometryEquiv
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_opLinearIsometryEquiv
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_opLinearIsometryEquiv :
    (opLinearIsometryEquiv R H).toLinearEquiv = opLinearEquiv R := rfl

@[simp]
/--
theorem `toContinuousLinearEquiv_opLinearIsometryEquiv` / 定理 `toContinuousLinearEquiv_opLinearIsometryEquiv`

English:
theorem toContinuousLinearEquiv_opLinearIsometryEquiv
  proof: rfl

中文:
定理 toContinuousLinearEquiv_opLinearIsometryEquiv
  证明: rfl
-/
theorem toContinuousLinearEquiv_opLinearIsometryEquiv :
    (opLinearIsometryEquiv R H).toContinuousLinearEquiv = opContinuousLinearEquiv R := rfl

end MulOpposite
