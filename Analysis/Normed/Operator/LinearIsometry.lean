/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Star.Basic  -- shake: keep (used in `notation` only)
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
a semilinear isometric equivalence between `E` and `E₂`.  The notation for the associated purely
linear concepts is `E →ₗᵢ[R] E₂`, `E ≃ₗᵢ[R] E₂`, and `E →ₗᵢ⋆[R] E₂`, `E ≃ₗᵢ⋆[R] E₂` for
the star-linear versions.

We also prove some trivial lemmas and provide convenience constructors.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup` and we specialize to `NormedAddCommGroup` when needed.
-/

@[expose] public section

open Function Set Topology

variable {R R₂ R₃ R₄ E E₂ E₃ E₄ F 𝓕 : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R} {σ₁₄ : R →+* R₄}
  {σ₄₁ : R₄ →+* R} {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₂₄ : R₂ →+* R₄} {σ₄₂ : R₄ →+* R₂}
  {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃] [RingHomInvPair σ₂₃ σ₃₂]
  [RingHomInvPair σ₃₂ σ₂₃] [RingHomInvPair σ₁₄ σ₄₁] [RingHomInvPair σ₄₁ σ₁₄]
  [RingHomInvPair σ₂₄ σ₄₂] [RingHomInvPair σ₄₂ σ₂₄] [RingHomInvPair σ₃₄ σ₄₃]
  [RingHomInvPair σ₄₃ σ₃₄] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
  [RingHomCompTriple σ₄₂ σ₂₁ σ₄₁] [RingHomCompTriple σ₄₃ σ₃₂ σ₄₂] [RingHomCompTriple σ₄₃ σ₃₁ σ₄₁]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup E₃]
  [SeminormedAddCommGroup E₄] [Module R E] [Module R₂ E₂] [Module R₃ E₃] [Module R₄ E₄]
  [NormedAddCommGroup F] [Module R F]

/-- A `σ₁₂`-semilinear isometric embedding of a normed `R`-module into an `R₂`-module,
denoted as `f : E →ₛₗᵢ[σ₁₂] E₂`. -/
/-
**LinearIsometry** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R] →       [inst
_1 : Semiring R₂] →         (R →+* R₂) →           (E : Type u_11) →            
 (E₂ : Type u_12) →               [inst_2 : SeminormedAddCommGroup E] →         
        [inst_3 : SeminormedAddCommGroup E₂] →                   [_root_.Module 
R E] → [_root_.Module R₂ E₂] → Type (max u_11 u_12)
参数：R →+* R₂；E : Type u_11；E₂ : Type u_12；max u_11 u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `σ₁₂`-semilinear isometric embedding of a normed `R`-module into an `R₂`-modul
e,
denoted as `f : E →ₛₗᵢ[σ₁₂] E₂`.
-/
structure LinearIsometry (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] extends E →ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ‖toLinearMap x‖ = ‖x‖

@[inherit_doc]
notation:25 E " →ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometry σ₁₂ E E₂

/-- A linear isometric embedding of a normed `R`-module into another one. -/
notation:25 E " →ₗᵢ[" R:25 "] " E₂:0 => LinearIsometry (RingHom.id R) E E₂

/-- An antilinear isometric embedding of a normed `R`-module into another one. -/
notation:25 E " →ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometry (starRingEnd R) E E₂

/-- `SemilinearIsometryClass F σ E E₂` asserts `F` is a type of bundled `σ`-semilinear isometries
`E → E₂`.

See also `LinearIsometryClass F R E E₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
/-
**SemilinearIsometryClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝓕 : Type u_11) →   {R : outParam (Type u_12)} →     {R₂ : outParam (Type 
u_13)} →       [inst : Semiring R] →         [inst_1 : Semiring R₂] →           
outParam (R →+* R₂) →             (E : outParam (Type u_14)) →               (E₂
 : outParam (Type u_15)) →                 [inst_2 : SeminormedAddCommGroup E] →
                   [inst_3 : SeminormedAddCommGroup E₂] →                     [_
root_.Module R E] → [_root_.Module R₂ E₂] → [FunLike 𝓕 E E₂] → Prop
参数：Type u_14；Type u_15。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SemilinearIsometryClass F σ E E₂` asserts `F` is a type of bundled `σ`-semiline
ar isometries
`E → E₂`.

See also `LinearIsometryClass F R E E₂` for the case where `σ` is the identity m
ap on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : 
R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`.
-/
class SemilinearIsometryClass (𝓕 : Type*) {R R₂ : outParam Type*} [Semiring R] [Semiring R₂]
    (σ₁₂ : outParam <| R →+* R₂) (E E₂ : outParam Type*) [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] [FunLike 𝓕 E E₂] : Prop
    extends SemilinearMapClass 𝓕 σ₁₂ E E₂ where
  norm_map : ∀ (f : 𝓕) (x : E), ‖f x‖ = ‖x‖

/-- `LinearIsometryClass F R E E₂` asserts `F` is a type of bundled `R`-linear isometries
`M → M₂`.

This is an abbreviation for `SemilinearIsometryClass F (RingHom.id R) E E₂`.
-/
/-
**LinearIsometryClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearIsometryClass (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R] [Se
minormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R E₂] [
FunLike 𝓕 E E₂]
参数：𝓕 : Type*；R E E₂ : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearIsometryClass F R E E₂` asserts `F` is a type of bundled `R`-linear isome
tries
`M → M₂`.

This is an abbreviation for `SemilinearIsometryClass F (RingHom.id R) E E₂`.
-/
abbrev LinearIsometryClass (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R E₂]
    [FunLike 𝓕 E E₂] :=
  SemilinearIsometryClass 𝓕 (RingHom.id R) E E₂

namespace SemilinearIsometryClass

variable [FunLike 𝓕 E E₂]

/-
**SemilinearIsometryClass.isometry** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearIsometry
Class`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂} [inst_2 : Se
minormedAddCommGroup E] [inst_3 : SeminormedAddCommGroup E₂]   [inst_4 : _root_.
Module R E] [inst_5 : _root_.Module R₂ E₂] [inst_6 : FunLike 𝓕 E E₂]   [Semiline
arIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕), Isometry ⇑f
参数：f : 𝓕。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryClass.norm_map`：∀ {𝓕 : Type u_11} {R : outParam (Type 
u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Semiring R₂}   
{σ₁₂ : outParam (R →+*…
-/
protected theorem isometry [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Isometry f :=
  AddMonoidHomClass.isometry_of_norm _ (norm_map _)

@[continuity]
/-
**SemilinearIsometryClass.continuous** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearIsomet
ryClass`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂} [inst_2 : Se
minormedAddCommGroup E] [inst_3 : SeminormedAddCommGroup E₂]   [inst_4 : _root_.
Module R E] [inst_5 : _root_.Module R₂ E₂] [inst_6 : FunLike 𝓕 E E₂]   [Semiline
arIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕), Continuous ⇑f
参数：f : 𝓕。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `SemilinearIsometryClass.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 : Semiri
ng R₂] {σ₁₂ : R →+* R₂…
-/
protected theorem continuous [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Continuous f :=
  (SemilinearIsometryClass.isometry f).continuous

-- Should be `@[simp]` but it doesn't fire due to https://github.com/leanprover/lean4/issues/3107.
/-
**SemilinearIsometryClass.nnnorm_map** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearIsomet
ryClass`。
形式化陈述：nnnorm_map [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (x : E) : ‖f x‖₊ =
 ‖x‖₊
参数：f : 𝓕；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `SemilinearIsometryClass.norm_map`：∀ {𝓕 : Type u_11} {R : outParam (Type 
u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Semiring R₂}   
{σ₁₂ : outParam (R →+*…
-/
theorem nnnorm_map [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (x : E) : ‖f x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_map f x
/-
**SemilinearIsometryClass.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearIsometr
yClass`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂} [inst_2 : Se
minormedAddCommGroup E] [inst_3 : SeminormedAddCommGroup E₂]   [inst_4 : _root_.
Module R E] [inst_5 : _root_.Module R₂ E₂] [inst_6 : FunLike 𝓕 E E₂]   [Semiline
arIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕), LipschitzWith 1 ⇑f
参数：f : 𝓕。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `SemilinearIsometryClass.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 : Semiri
ng R₂] {σ₁₂ : R →+* R₂…
-/
protected theorem lipschitz [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : LipschitzWith 1 f :=
  (SemilinearIsometryClass.isometry f).lipschitz
/-
**SemilinearIsometryClass.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearIso
metryClass`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂} [inst_2 : Se
minormedAddCommGroup E] [inst_3 : SeminormedAddCommGroup E₂]   [inst_4 : _root_.
Module R E] [inst_5 : _root_.Module R₂ E₂] [inst_6 : FunLike 𝓕 E E₂]   [Semiline
arIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕), AntilipschitzWith 1 ⇑f
参数：f : 𝓕。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `SemilinearIsometryClass.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 : Semiri
ng R₂] {σ₁₂ : R →+* R₂…
-/
protected theorem antilipschitz [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    AntilipschitzWith 1 f :=
  (SemilinearIsometryClass.isometry f).antilipschitz
/-
**SemilinearIsometryClass.ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearIsome
tryClass`。
形式化陈述：ediam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) : Met
ric.ediam (f '' s) = Metric.ediam s
参数：f : 𝓕；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `SemilinearIsometryClass.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 : Semiri
ng R₂] {σ₁₂ : R →+* R₂…
-/
theorem ediam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) :
    Metric.ediam (f '' s) = Metric.ediam s :=
  (SemilinearIsometryClass.isometry f).ediam_image s
/-
**SemilinearIsometryClass.ediam_range** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearIsome
tryClass`。
形式化陈述：ediam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Metric.ediam (r
ange f) = Metric.ediam (univ : Set E)
参数：f : 𝓕。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_range`：ediam_range (hf : Isometry f) : Metric.ediam (rang
e f) = Metric.ediam (univ : Set α)
· 使用定理 `SemilinearIsometryClass.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 : Semiri
ng R₂] {σ₁₂ : R →+* R₂…
-/
theorem ediam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    Metric.ediam (range f) = Metric.ediam (univ : Set E) :=
  (SemilinearIsometryClass.isometry f).ediam_range
/-
**SemilinearIsometryClass.diam_image** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearIsomet
ryClass`。
形式化陈述：diam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) : Metr
ic.diam (f '' s) = Metric.diam s
参数：f : 𝓕；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
· 使用定理 `SemilinearIsometryClass.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 : Semiri
ng R₂] {σ₁₂ : R →+* R₂…
-/
theorem diam_image [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) (s : Set E) :
    Metric.diam (f '' s) = Metric.diam s :=
  (SemilinearIsometryClass.isometry f).diam_image s
/-
**SemilinearIsometryClass.diam_range** 是 Mathlib 中的一个定理，位于命名空间 `SemilinearIsomet
ryClass`。
形式化陈述：diam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Metric.diam (ran
ge f) = Metric.diam (univ : Set E)
参数：f : 𝓕。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_range`：diam_range (hf : Isometry f) : Metric.diam (range f
) = Metric.diam (univ : Set α)
· 使用定理 `SemilinearIsometryClass.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 : Semiri
ng R₂] {σ₁₂ : R →+* R₂…
-/
theorem diam_range [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) :
    Metric.diam (range f) = Metric.diam (univ : Set E) :=
  (SemilinearIsometryClass.isometry f).diam_range
/-
**SemilinearIsometryClass.** 是 Mathlib 中的一个实例，位于命名空间 `SemilinearIsometryClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toContinuousSemilinearMapClass
    [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] : ContinuousSemilinearMapClass 𝓕 σ₁₂ E E₂ where
  map_continuous := SemilinearIsometryClass.continuous
/-
**SemilinearIsometryClass.** 是 Mathlib 中的一个实例，位于命名空间 `SemilinearIsometryClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toIsometryClass [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] :
    IsometryClass 𝓕 E E₂ where
  isometry := SemilinearIsometryClass.isometry

end SemilinearIsometryClass

namespace LinearIsometry

variable (f : E →ₛₗᵢ[σ₁₂] E₂) (f₁ : F →ₛₗᵢ[σ₁₂] E₂)

/-
**LinearIsometry.toLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂], Function.Injective LinearIsometry.toLinearMap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_injective : Injective (toLinearMap : (E →ₛₗᵢ[σ₁₂] E₂) → E →ₛₗ[σ₁₂] E₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp]
/-
**LinearIsometry.toLinearMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：toLinearMap_inj {f g : E ->ₛₗᵢ[σ₁₂] E₂} : f.toLinearMap = g.toLinearMap ↔ 
f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometry.toLinearMap_injective`：∀ {R : Type u_1} {R₂ : Type u_2} {
E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ 
: R →+* R₂} [inst_2 : Semi…
-/
theorem toLinearMap_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} : f.toLinearMap = g.toLinearMap ↔ f = g :=
  toLinearMap_injective.eq_iff
/-
**LinearIsometry.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometry`。
形式化陈述：instFunLike : FunLike (E ->ₛₗᵢ[σ₁₂] E₂) E E₂ where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (E →ₛₗᵢ[σ₁₂] E₂) E E₂ where
  coe f := f.toFun
  coe_injective _ _ h := toLinearMap_injective (DFunLike.coe_injective h)
/-
**LinearIsometry.instSemilinearIsometryClass** 是 Mathlib 中的一个实例，位于命名空间 `LinearIs
ometry`。
形式化陈述：instSemilinearIsometryClass : SemilinearIsometryClass (E ->ₛₗᵢ[σ₁₂] E₂) σ₁
₂ E E₂ where map_add f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearIsometry.norm_map'`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : Semir
ing R] [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂} {E : Type u_11}   {E₂ : Type u_12
} [inst_2 : Se…
-/
instance instSemilinearIsometryClass : SemilinearIsometryClass (E →ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap
  norm_map f := f.norm_map'

@[simp]
/-
**LinearIsometry.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：coe_toLinearMap : ⇑f.toLinearMap = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearMap : ⇑f.toLinearMap = f :=
  rfl

@[simp]
/-
**LinearIsometry.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：coe_mk (f : E ->ₛₗ[σ₁₂] E₂) (hf) : ⇑(mk f hf) = f
参数：f : E ->ₛₗ[σ₁₂] E₂；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : E →ₛₗ[σ₁₂] E₂) (hf) : ⇑(mk f hf) = f :=
  rfl
/-
**LinearIsometry.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：coe_injective : @Injective (E ->ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (fun f => f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearIsometry.mk.injEq`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂} {E : Type u_11}   {E₂ : Type u_12}
 [inst_2 : Se…
-/
theorem coe_injective : @Injective (E →ₛₗᵢ[σ₁₂] E₂) (E → E₂) (fun f => f) := by
  rintro ⟨_⟩ ⟨_⟩
  simp

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**LinearIsometry.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry.Simps`。
形式化陈述：{R : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R] →       [inst
_1 : Semiring R₂] →         (σ₁₂ : R →+* R₂) →           (E : Type u_11) →      
       (E₂ : Type u_12) →               [inst_2 : SeminormedAddCommGroup E] →   
              [inst_3 : SeminormedAddCommGroup E₂] →                   [inst_4 :
 _root_.Module R E] → [inst_5 : _root_.Module R₂ E₂] → (E →ₛₗᵢ[σ₁₂] E₂) → E → E₂
参数：σ₁₂ : R →+* R₂；E : Type u_11；E₂ : Type u_12；E →ₛₗᵢ[σ₁₂] E₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] (h : E →ₛₗᵢ[σ₁₂] E₂) : E → E₂ :=
  h

initialize_simps_projections LinearIsometry (toFun → apply)

@[ext]
/-
**LinearIsometry.ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：ext {f g : E ->ₛₗᵢ[σ₁₂] E₂} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.coe_injective`：coe_injective : @Injective (E ->ₛₗᵢ[σ₁₂] E
₂) (E -> E₂) (fun f => f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {f g : E →ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

variable [FunLike 𝓕 E E₂]
/-
**LinearIsometry.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂), f 0 = 0
参数：f : E →ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
protected theorem map_zero : f 0 = 0 :=
  f.toLinearMap.map_zero
/-
**LinearIsometry.map_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂) (x y : E), f (x + y) = f x + f y
参数：f : E →ₛₗᵢ[σ₁₂] E₂；x y : E；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
protected theorem map_add (x y : E) : f (x + y) = f x + f y :=
  f.toLinearMap.map_add x y
/-
**LinearIsometry.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂) (x : E), f (-x) = -f x
参数：f : E →ₛₗᵢ[σ₁₂] E₂；x : E；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_neg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
protected theorem map_neg (x : E) : f (-x) = -f x :=
  f.toLinearMap.map_neg x
/-
**LinearIsometry.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂) (x y : E), f (x - y) = f x - f y
参数：f : E →ₛₗᵢ[σ₁₂] E₂；x y : E；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
protected theorem map_sub (x y : E) : f (x - y) = f x - f y :=
  f.toLinearMap.map_sub x y
/-
**LinearIsometry.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_
1 : SeminormedAddCommGroup E]   [inst_2 : SeminormedAddCommGroup E₂] [inst_3 : _
root_.Module R E] [inst_4 : _root_.Module R E₂] (f : E →ₗᵢ[R] E₂)   (c : R) (x :
 E), f (c • x) = c • f x
参数：f : E →ₗᵢ[R] E₂；c : R；x : E；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
protected theorem map_smulₛₗ (c : R) (x : E) : f (c • x) = σ₁₂ c • f x :=
  f.toLinearMap.map_smulₛₗ c x
/-
**LinearIsometry.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_
1 : SeminormedAddCommGroup E]   [inst_2 : SeminormedAddCommGroup E₂] [inst_3 : _
root_.Module R E] [inst_4 : _root_.Module R E₂] (f : E →ₗᵢ[R] E₂)   (c : R) (x :
 E), f (c • x) = c • f x
参数：f : E →ₗᵢ[R] E₂；c : R；x : E；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
protected theorem map_smul [Module R E₂] (f : E →ₗᵢ[R] E₂) (c : R) (x : E) : f (c • x) = c • f x :=
  f.toLinearMap.map_smul c x
/-
**LinearIsometry.norm_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂) (x : E), ‖f x‖ = ‖x‖
参数：f : E →ₛₗᵢ[σ₁₂] E₂；x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma norm_map (x : E) : ‖f x‖ = ‖x‖ := by simp
/-
**LinearIsometry.nnnorm_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂) (x : E), ‖f x‖₊ = ‖x‖₊
参数：f : E →ₛₗᵢ[σ₁₂] E₂；x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semin
ormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso
…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma nnnorm_map (x : E) : ‖f x‖₊ = ‖x‖₊ := by simp
/-
**LinearIsometry.enorm_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂) (x : E), ‖f x‖ₑ = ‖x‖ₑ
参数：f : E →ₛₗᵢ[σ₁₂] E₂；x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `enorm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semino
rmedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma enorm_map (x : E) : ‖f x‖ₑ = ‖x‖ₑ := by simp
/-
**LinearIsometry.isometry** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂), Isometry ⇑f
参数：f : E →ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
protected theorem isometry : Isometry f :=
  AddMonoidHomClass.isometry_of_norm f.toLinearMap f.norm_map
/-
**LinearIsometry.isEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `LinearIsometry`。
形式化陈述：isEmbedding (f : F ->ₛₗᵢ[σ₁₂] E₂) : IsEmbedding f
参数：f : F ->ₛₗᵢ[σ₁₂] E₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.isEmbedding`：isEmbedding (hf : Isometry f) : IsEmbedding f
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
lemma isEmbedding (f : F →ₛₗᵢ[σ₁₂] E₂) : IsEmbedding f := f.isometry.isEmbedding

@[simp]
/-
**LinearIsometry.isComplete_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`
。
形式化陈述：isComplete_image_iff [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) {s : Set
 E} : IsComplete (f '' s) ↔ IsComplete s
参数：f : 𝓕。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isComplete_image_iff`：isComplete_image_iff {m : α -> β} {s : Set α} (hm 
: IsUniformInducing m) : IsComplete (m '' s) ↔ IsComplete s
· 使用定理 `Isometry.isUniformInducing`：isUniformInducing (hf : Isometry f) : IsUnif
ormInducing f
· 使用定理 `SemilinearIsometryClass.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : 
Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 : Semiri
ng R₂] {σ₁₂ : R →+* R₂…
-/
theorem isComplete_image_iff [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) {s : Set E} :
    IsComplete (f '' s) ↔ IsComplete s :=
  _root_.isComplete_image_iff (SemilinearIsometryClass.isometry f).isUniformInducing
/-
**LinearIsometry.isComplete_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：isComplete_map_iff [RingHomSurjective σ₁₂] {p : Submodule R E} : IsComplet
e (p.map f.toLinearMap : Set E₂) ↔ IsComplete (p : Set E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.isComplete_image_iff`：isComplete_image_iff [SemilinearIso
metryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) {s : Set E} : IsComplete (f '' s) ↔ IsComplete s
-/
theorem isComplete_map_iff [RingHomSurjective σ₁₂] {p : Submodule R E} :
    IsComplete (p.map f.toLinearMap : Set E₂) ↔ IsComplete (p : Set E) :=
  isComplete_image_iff f
/-
**LinearIsometry.completeSpace_map** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometry`。
形式化陈述：completeSpace_map [RingHomSurjective σ₁₂] (p : Submodule R E) [CompleteSpa
ce p] : CompleteSpace (p.map (f : E ->ₛₗ[σ₁₂] E₂))
参数：p : Submodule R E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.completeSpace_coe`：∀ {α : Type u} [inst : UniformSpace α] {s 
: Set α}, IsComplete s → CompleteSpace ↑s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearIsometry.isComplete_map_iff`：isComplete_map_iff [RingHomSurjective
 σ₁₂] {p : Submodule R E} : IsComplete (p.map f.toLinearMap : Set E₂) ↔ IsComple
te (p : Set E)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `completeSpace_coe_iff_isComplete`：completeSpace_coe_iff_isComplete {s : 
Set α} : CompleteSpace s ↔ IsComplete s
-/
instance completeSpace_map [RingHomSurjective σ₁₂] (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map (f : E →ₛₗ[σ₁₂] E₂)) :=
  ((isComplete_map_iff f).2 <| completeSpace_coe_iff_isComplete.1 ‹_›).completeSpace_coe

@[simp]
/-
**LinearIsometry.dist_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：dist_map (x y : E) : dist (f x) (f y) = dist x y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem dist_map (x y : E) : dist (f x) (f y) = dist x y :=
  f.isometry.dist_eq x y

@[simp]
/-
**LinearIsometry.edist_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：edist_map (x y : E) : edist (f x) (f y) = edist x y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem edist_map (x y : E) : edist (f x) (f y) = edist x y :=
  f.isometry.edist_eq x y
/-
**LinearIsometry.injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E₂ : Type u_6} {F : Type u_9} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E₂] [inst_3 : _root_.Module R₂ E₂] [inst_4 : NormedAddCommGroup F]   [inst_
5 : _root_.Module R F] (f₁ : F →ₛₗᵢ[σ₁₂] E₂), Function.Injective ⇑f₁
参数：f₁ : F →ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
protected theorem injective : Injective f₁ :=
  Isometry.injective (LinearIsometry.isometry f₁)

@[simp]
/-
**LinearIsometry.map_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：map_eq_iff {x y : F} : f₁ x = f₁ y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometry.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E₂ : Type u_
6} {F : Type u_9} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
-/
theorem map_eq_iff {x y : F} : f₁ x = f₁ y ↔ x = y :=
  f₁.injective.eq_iff
/-
**LinearIsometry.map_ne** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：map_ne {x y : F} (h : x != y) : f₁ x != f₁ y
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `LinearIsometry.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E₂ : Type u_
6} {F : Type u_9} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
-/
theorem map_ne {x y : F} (h : x ≠ y) : f₁ x ≠ f₁ y :=
  f₁.injective.ne h
/-
**LinearIsometry.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂), LipschitzWith 1 ⇑f
参数：f : E →ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
protected theorem lipschitz : LipschitzWith 1 f :=
  f.isometry.lipschitz
/-
**LinearIsometry.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂), AntilipschitzWith 1 ⇑f
参数：f : E →ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.isometry.antilipschitz

@[continuity]
/-
**LinearIsometry.continuous** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂), Continuous ⇑f
参数：f : E →ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
protected theorem continuous : Continuous f :=
  f.isometry.continuous

@[simp]
/-
**LinearIsometry.preimage_ball** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：preimage_ball (x : E) (r : Real) : f ⁻¹' Metric.ball (f x) r = Metric.ball
 x r
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.preimage_ball`：preimage_ball (hf : Isometry f) (x : α) (r : Rea
l) : f ⁻¹' Metric.ball (f x) r = Metric.ball x r
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem preimage_ball (x : E) (r : ℝ) : f ⁻¹' Metric.ball (f x) r = Metric.ball x r :=
  f.isometry.preimage_ball x r

@[simp]
/-
**LinearIsometry.preimage_sphere** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：preimage_sphere (x : E) (r : Real) : f ⁻¹' Metric.sphere (f x) r = Metric.
sphere x r
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.preimage_sphere`：preimage_sphere (hf : Isometry f) (x : α) (r :
 Real) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem preimage_sphere (x : E) (r : ℝ) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r :=
  f.isometry.preimage_sphere x r

@[simp]
/-
**LinearIsometry.preimage_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：preimage_closedBall (x : E) (r : Real) : f ⁻¹' Metric.closedBall (f x) r =
 Metric.closedBall x r
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.preimage_closedBall`：preimage_closedBall (hf : Isometry f) (x :
 α) (r : Real) : f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem preimage_closedBall (x : E) (r : ℝ) :
    f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r :=
  f.isometry.preimage_closedBall x r
/-
**LinearIsometry.ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：ediam_image (s : Set E) : Metric.ediam (f '' s) = Metric.ediam s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem ediam_image (s : Set E) : Metric.ediam (f '' s) = Metric.ediam s :=
  f.isometry.ediam_image s
/-
**LinearIsometry.ediam_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：ediam_range : Metric.ediam (range f) = Metric.ediam (univ : Set E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_range`：ediam_range (hf : Isometry f) : Metric.ediam (rang
e f) = Metric.ediam (univ : Set α)
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem ediam_range : Metric.ediam (range f) = Metric.ediam (univ : Set E) :=
  f.isometry.ediam_range
/-
**LinearIsometry.diam_image** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：diam_image (s : Set E) : Metric.diam (f '' s) = Metric.diam s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem diam_image (s : Set E) : Metric.diam (f '' s) = Metric.diam s :=
  Isometry.diam_image (LinearIsometry.isometry f) s
/-
**LinearIsometry.diam_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：diam_range : Metric.diam (range f) = Metric.diam (univ : Set E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_range`：diam_range (hf : Isometry f) : Metric.diam (range f
) = Metric.diam (univ : Set α)
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set E) :=
  Isometry.diam_range (LinearIsometry.isometry f)

/-- Interpret a linear isometry as a continuous linear map. -/
/-
**LinearIsometry.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry
`。
形式化陈述：toContinuousLinearMap : E ->SL[σ₁₂] E₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_
5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂}
 [inst_2 : Semi…

--- 原说明 ---
Interpret a linear isometry as a continuous linear map.
-/
def toContinuousLinearMap : E →SL[σ₁₂] E₂ :=
  ⟨f.toLinearMap, f.continuous⟩
/-
**LinearIsometry.toLinearMap_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearIsometry`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [inst_2 : SeminormedAddCommG
roup E] [inst_3 : SeminormedAddCommGroup E₂] [inst_4 : _root_.Module R E]   [ins
t_5 : _root_.Module R₂ E₂] (f : E →ₛₗᵢ[σ₁₂] E₂), ↑f.toContinuousLinearMap = f.to
LinearMap
参数：f : E →ₛₗᵢ[σ₁₂] E₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_toContinuousLinearMap (f : E →ₛₗᵢ[σ₁₂] E₂) :
  f.toContinuousLinearMap.toLinearMap = f.toLinearMap := rfl
/-
**LinearIsometry.toContinuousLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Line
arIsometry`。
形式化陈述：toContinuousLinearMap_injective : Function.Injective (toContinuousLinearMa
p : _ -> E ->SL[σ₁₂] E₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.coe_injective`：coe_injective : @Injective (E ->ₛₗᵢ[σ₁₂] E
₂) (E -> E₂) (fun f => f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap : _ → E →SL[σ₁₂] E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearMap = _)

@[simp]
/-
**LinearIsometry.toContinuousLinearMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etry`。
形式化陈述：toContinuousLinearMap_inj {f g : E ->ₛₗᵢ[σ₁₂] E₂} : f.toContinuousLinearMa
p = g.toContinuousLinearMap ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometry.toContinuousLinearMap_injective`：toContinuousLinearMap_in
jective : Function.Injective (toContinuousLinearMap : _ -> E ->SL[σ₁₂] E₂)
-/
theorem toContinuousLinearMap_inj {f g : E →ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearMap = g.toContinuousLinearMap ↔ f = g :=
  toContinuousLinearMap_injective.eq_iff

@[simp]
/-
**LinearIsometry.coe_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etry`。
形式化陈述：coe_toContinuousLinearMap : ⇑f.toContinuousLinearMap = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousLinearMap : ⇑f.toContinuousLinearMap = f :=
  rfl

@[simp]
/-
**LinearIsometry.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α -> E} : Contin
uous (f ∘ g) ↔ Continuous g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp_continuous_iff`：comp_continuous_iff {γ} [TopologicalSpace 
γ] (hf : Isometry f) {g : γ -> α} : Continuous (f ∘ g) ↔ Continuous g
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α → E} :
    Continuous (f ∘ g) ↔ Continuous g :=
  f.isometry.comp_continuous_iff

/-- The identity linear isometry. -/
/-
**LinearIsometry.id** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry`。
形式化陈述：id : E ->ₗᵢ[R] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity linear isometry.
-/
def id : E →ₗᵢ[R] E :=
  ⟨LinearMap.id, fun _ => rfl⟩

@[simp, norm_cast]
/-
**LinearIsometry.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：coe_id : ((id : E ->ₗᵢ[R] E) : E -> E) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ((id : E →ₗᵢ[R] E) : E → E) = _root_.id :=
  rfl

@[simp]
/-
**LinearIsometry.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：id_apply (x : E) : (id : E ->ₗᵢ[R] E) x = x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : E) : (id : E →ₗᵢ[R] E) x = x :=
  rfl

@[simp]
/-
**LinearIsometry.id_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：id_toLinearMap : (id.toLinearMap : E ->ₗ[R] E) = LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_toLinearMap : (id.toLinearMap : E →ₗ[R] E) = LinearMap.id :=
  rfl

@[simp]
/-
**LinearIsometry.id_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsome
try`。
形式化陈述：id_toContinuousLinearMap : id.toContinuousLinearMap = ContinuousLinearMap.
id R E
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_toContinuousLinearMap : id.toContinuousLinearMap = ContinuousLinearMap.id R E :=
  rfl
/-
**LinearIsometry.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometry`。
形式化陈述：instInhabited : Inhabited (E ->ₗᵢ[R] E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (E →ₗᵢ[R] E) := ⟨id⟩

/-- Composition of linear isometries. -/
/-
**LinearIsometry.comp** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry`。
形式化陈述：comp (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (f : E ->ₛₗᵢ[σ₁₂] E₂) : E ->ₛₗᵢ[σ₁₃] E₃
参数：g : E₂ ->ₛₗᵢ[σ₂₃] E₃；f : E ->ₛₗᵢ[σ₁₂] E₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of linear isometries.
-/
def comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : E →ₛₗᵢ[σ₁₃] E₃ :=
  ⟨g.toLinearMap.comp f.toLinearMap, fun _ => (norm_map g _).trans (norm_map f _)⟩

@[simp]
/-
**LinearIsometry.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：coe_comp (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (f : E ->ₛₗᵢ[σ₁₂] E₂) : ⇑(g.comp f) = g ∘ 
f
参数：g : E₂ ->ₛₗᵢ[σ₂₃] E₃；f : E ->ₛₗᵢ[σ₁₂] E₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
/-
**LinearIsometry.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：id_comp : (id : E₂ ->ₗᵢ[R₂] E₂).comp f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.ext`：ext {f g : E ->ₛₗᵢ[σ₁₂] E₂} (h : forall x, f x = g x
) : f = g
-/
theorem id_comp : (id : E₂ →ₗᵢ[R₂] E₂).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**LinearIsometry.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：comp_id : f.comp id = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.ext`：ext {f g : E ->ₛₗᵢ[σ₁₂] E₂} (h : forall x, f x = g x
) : f = g
-/
theorem comp_id : f.comp id = f :=
  ext fun _ => rfl
/-
**LinearIsometry.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：comp_assoc (f : E₃ ->ₛₗᵢ[σ₃₄] E₄) (g : E₂ ->ₛₗᵢ[σ₂₃] E₃) (h : E ->ₛₗᵢ[σ₁₂]
 E₂) : (f.comp g).comp h = f.comp (g.comp h)
参数：f : E₃ ->ₛₗᵢ[σ₃₄] E₄；g : E₂ ->ₛₗᵢ[σ₂₃] E₃；h : E ->ₛₗᵢ[σ₁₂] E₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : E₃ →ₛₗᵢ[σ₃₄] E₄) (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (h : E →ₛₗᵢ[σ₁₂] E₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
/-
**LinearIsometry.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometry`。
形式化陈述：instMonoid : Monoid (E ->ₗᵢ[R] E) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid : Monoid (E →ₗᵢ[R] E) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
/-
**LinearIsometry.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：coe_one : ((1 : E ->ₗᵢ[R] E) : E -> E) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : E →ₗᵢ[R] E) : E → E) = _root_.id :=
  rfl

@[simp]
/-
**LinearIsometry.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：coe_mul (f g : E ->ₗᵢ[R] E) : ⇑(f * g) = f ∘ g
参数：f g : E ->ₗᵢ[R] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : E →ₗᵢ[R] E) : ⇑(f * g) = f ∘ g :=
  rfl
/-
**LinearIsometry.one_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：one_def : (1 : E ->ₗᵢ[R] E) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : E →ₗᵢ[R] E) = id :=
  rfl
/-
**LinearIsometry.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：mul_def (f g : E ->ₗᵢ[R] E) : (f * g : E ->ₗᵢ[R] E) = f.comp g
参数：f g : E ->ₗᵢ[R] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (f g : E →ₗᵢ[R] E) : (f * g : E →ₗᵢ[R] E) = f.comp g :=
  rfl
/-
**LinearIsometry.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：coe_pow (f : E ->ₗᵢ[R] E) (n : Nat) : ⇑(f ^ n) = f^[n]
参数：f : E ->ₗᵢ[R] E；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hom_coe_pow`：∀ {M : Type u_4} {F : Type u_5} [inst : Monoid F] (c : F → 
M → M),   c 1 = id → (∀ (f g : F), c (f * g) = c f ∘ c g) → ∀ (f : F) (n : ℕ), c
 …
-/
theorem coe_pow (f : E →ₗᵢ[R] E) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

section submoduleMap

variable {R R₁ R₂ M M₁ : Type*}
variable [Ring R] [SeminormedAddCommGroup M] [SeminormedAddCommGroup M₁]
variable [Module R M] [Module R M₁]

/-- A linear isometry between two modules restricts to a linear isometry
from any submodule `p` of the domain onto the image of that submodule.

This is a version of `LinearMap.submoduleMap` extended to linear isometries. -/
@[simps!]
/-
**LinearIsometry.submoduleMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry`。
形式化陈述：submoduleMap (p : Submodule R M) (e : M ->ₗᵢ[R] M₁) : p ->ₗᵢ[R] p.map (e :
 M ->ₗ[R] M₁)
参数：p : Submodule R M；e : M ->ₗᵢ[R] M₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear isometry between two modules restricts to a linear isometry
from any submodule `p` of the domain onto the image of that submodule.

This is a version of `LinearMap.submoduleMap` extended to linear isometries.
-/
def submoduleMap (p : Submodule R M) (e : M →ₗᵢ[R] M₁) :
    p →ₗᵢ[R] p.map (e : M →ₗ[R] M₁) :=
  { e.toLinearMap.submoduleMap p with norm_map' x := e.norm_map' x }

end submoduleMap

end LinearIsometry

/-- Construct a `LinearIsometry` from a `LinearMap` satisfying `Isometry`. -/
/-
**LinearMap.toLinearIsometry** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.toLinearIsometry (f : E ->ₛₗ[σ₁₂] E₂) (hf : Isometry f) : E ->ₛₗ
ᵢ[σ₁₂] E₂
参数：f : E ->ₛₗ[σ₁₂] E₂；hf : Isometry f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `LinearIsometry` from a `LinearMap` satisfying `Isometry`.
-/
def LinearMap.toLinearIsometry (f : E →ₛₗ[σ₁₂] E₂) (hf : Isometry f) : E →ₛₗᵢ[σ₁₂] E₂ :=
  { f with
    norm_map' := by
      simp_rw [← dist_zero_right]
      simpa using (hf.dist_eq · 0) }

namespace Submodule

variable {R' : Type*} [Ring R'] [Module R' E] (p : Submodule R' E)

/-- `Submodule.subtype` as a `LinearIsometry`. -/
/-
**Submodule.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Semiring R] → [inst_1 : AddCom
mMonoid M] → {module_M : _root_.Module R M} → (p : Submodule R M) → ↥p →ₗ[R] M
参数：p : Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule.subtype` as a `LinearIsometry`.
-/
def subtypeₗᵢ : p →ₗᵢ[R'] E :=
  ⟨p.subtype, fun _ => rfl⟩

@[simp]
/-
**Submodule.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_subtype : (Submodule.subtype p : p -> M) = Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtypeₗᵢ : ⇑p.subtypeₗᵢ = p.subtype :=
  rfl

@[simp]
/-
**Submodule.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Semiring R] → [inst_1 : AddCom
mMonoid M] → {module_M : _root_.Module R M} → (p : Submodule R M) → ↥p →ₗ[R] M
参数：p : Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeₗᵢ_toLinearMap : p.subtypeₗᵢ.toLinearMap = p.subtype :=
  rfl

@[simp]
/-
**Submodule.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Semiring R] → [inst_1 : AddCom
mMonoid M] → {module_M : _root_.Module R M} → (p : Submodule R M) → ↥p →ₗ[R] M
参数：p : Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeₗᵢ_toContinuousLinearMap : p.subtypeₗᵢ.toContinuousLinearMap = p.subtypeL :=
  rfl

end Submodule

/-- A semilinear isometric equivalence between two normed vector spaces,
denoted as `f : E ≃ₛₗᵢ[σ₁₂] E₂`. -/
/-
**LinearIsometryEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R] →       [inst
_1 : Semiring R₂] →         (σ₁₂ : R →+* R₂) →           {σ₂₁ : R₂ →+* R} →     
        [RingHomInvPair σ₁₂ σ₂₁] →               [RingHomInvPair σ₂₁ σ₁₂] →     
            (E : Type u_11) →                   (E₂ : Type u_12) →              
       [inst_4 : SeminormedAddCommGroup E] →                       [inst_5 : Sem
inormedAddCommGroup E₂] →                         [_root_.Module R E] → [_root_.
Module R₂ E₂] → Type (max u_11 u_12)
参数：σ₁₂ : R →+* R₂；E : Type u_11；E₂ : Type u_12；max u_11 u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semilinear isometric equivalence between two normed vector spaces,
denoted as `f : E ≃ₛₗᵢ[σ₁₂] E₂`.
-/
structure LinearIsometryEquiv (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
  [Module R E] [Module R₂ E₂] extends E ≃ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ‖toLinearEquiv x‖ = ‖x‖

@[inherit_doc]
notation:25 E " ≃ₛₗᵢ[" σ₁₂:25 "] " E₂:0 => LinearIsometryEquiv σ₁₂ E E₂

/-- A linear isometric equivalence between two normed vector spaces. -/
notation:25 E " ≃ₗᵢ[" R:25 "] " E₂:0 => LinearIsometryEquiv (RingHom.id R) E E₂

/-- An antilinear isometric equivalence between two normed vector spaces. -/
notation:25 E " ≃ₗᵢ⋆[" R:25 "] " E₂:0 => LinearIsometryEquiv (starRingEnd R) E E₂

/-- `SemilinearIsometryEquivClass F σ E E₂` asserts `F` is a type of bundled `σ`-semilinear
isometric equivs `E → E₂`.

See also `LinearIsometryEquivClass F R E E₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
/-
**SemilinearIsometryEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝓕 : Type u_11) →   {R : outParam (Type u_12)} →     {R₂ : outParam (Type 
u_13)} →       [inst : Semiring R] →         [inst_1 : Semiring R₂] →           
(σ₁₂ : outParam (R →+* R₂)) →             {σ₂₁ : outParam (R₂ →+* R)} →         
      [RingHomInvPair σ₁₂ σ₂₁] →                 [RingHomInvPair σ₂₁ σ₁₂] →     
              (E : outParam (Type u_14)) →                     (E₂ : outParam (T
ype u_15)) →                       [inst_4 : SeminormedAddCommGroup E] →        
                 [inst_5 : SeminormedAddCommGroup E₂] →                         
  [_root_.Module R E] → [_root_.Module R₂ E₂] → [EquivLike 𝓕 E E₂] → Prop
参数：R →+* R₂；Type u_14；Type u_15。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SemilinearIsometryEquivClass F σ E E₂` asserts `F` is a type of bundled `σ`-sem
ilinear
isometric equivs `E → E₂`.

See also `LinearIsometryEquivClass F R E E₂` for the case where `σ` is the ident
ity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : 
R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`.
-/
class SemilinearIsometryEquivClass (𝓕 : Type*) {R R₂ : outParam Type*} [Semiring R]
  [Semiring R₂] (σ₁₂ : outParam <| R →+* R₂) {σ₂₁ : outParam <| R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : outParam Type*) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] [EquivLike 𝓕 E E₂] : Prop
  extends SemilinearEquivClass 𝓕 σ₁₂ E E₂ where
  norm_map : ∀ (f : 𝓕) (x : E), ‖f x‖ = ‖x‖

/-- `LinearIsometryEquivClass F R E E₂` asserts `F` is a type of bundled `R`-linear isometries
`M → M₂`.

This is an abbreviation for `SemilinearIsometryEquivClass F (RingHom.id R) E E₂`.
-/
/-
**LinearIsometryEquivClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearIsometryEquivClass (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R
] [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R 
E₂] [EquivLike 𝓕 E E₂]
参数：𝓕 : Type*；R E E₂ : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearIsometryEquivClass F R E E₂` asserts `F` is a type of bundled `R`-linear 
isometries
`M → M₂`.

This is an abbreviation for `SemilinearIsometryEquivClass F (RingHom.id R) E E₂`
.
-/
abbrev LinearIsometryEquivClass (𝓕 : Type*) (R E E₂ : outParam Type*) [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E] [Module R E₂]
    [EquivLike 𝓕 E E₂] :=
  SemilinearIsometryEquivClass 𝓕 (RingHom.id R) E E₂

namespace SemilinearIsometryEquivClass

variable (𝓕)

-- `σ₂₁` becomes a metavariable, but it's OK since it's an outparam
/-
**SemilinearIsometryEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `SemilinearIsometryEqu
ivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toSemilinearIsometryClass [EquivLike 𝓕 E E₂]
    [s : SemilinearIsometryEquivClass 𝓕 σ₁₂ E E₂] : SemilinearIsometryClass 𝓕 σ₁₂ E E₂ :=
  { s with }

end SemilinearIsometryEquivClass

namespace LinearIsometryEquiv

variable (e : E ≃ₛₗᵢ[σ₁₂] E₂)

/-
**LinearIsometryEquiv.toLinearEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearI
sometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂], Function.Injective LinearIsometryEquiv.toLine
arEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_injective : Injective (toLinearEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ₛₗ[σ₁₂] E₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[simp]
/-
**LinearIsometryEquiv.toLinearEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometr
yEquiv`。
形式化陈述：toLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toLinearEquiv = g.toLinearEqu
iv ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometryEquiv.toLinearEquiv_injective`：∀ {R : Type u_1} {R₂ : Type
 u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂] 
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* …
-/
theorem toLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toLinearEquiv = g.toLinearEquiv ↔ f = g :=
  toLinearEquiv_injective.eq_iff
/-
**LinearIsometryEquiv.instEquivLike** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：instEquivLike : EquivLike (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ where coe e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instEquivLike : EquivLike (E ≃ₛₗᵢ[σ₁₂] E₂) E E₂ where
  coe e := e.toFun
  inv e := e.invFun
  coe_injective' _ _ h _ := toLinearEquiv_injective <| DFunLike.ext' h
  left_inv e := e.left_inv
  right_inv e := e.right_inv
/-
**LinearIsometryEquiv.instSemilinearIsometryEquivClass** 是 Mathlib 中的一个实例，位于命名空间
 `LinearIsometryEquiv`。
形式化陈述：instSemilinearIsometryEquivClass : SemilinearIsometryEquivClass (E ≃ₛₗᵢ[σ₁
₂] E₂) σ₁₂ E E₂ where map_add f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearIsometryEquiv.norm_map'`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R] [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}   [inst_2 :
 RingHomInvPair σ₁₂…
-/
instance instSemilinearIsometryEquivClass :
    SemilinearIsometryEquivClass (E ≃ₛₗᵢ[σ₁₂] E₂) σ₁₂ E E₂ where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ e := map_smulₛₗ e.toLinearEquiv
  norm_map e := e.norm_map'

/-- Shortcut instance, saving 8.5% of compilation time in
`Mathlib/Analysis/InnerProductSpace/Adjoint.lean`.

(This instance was pinpointed by benchmarks; we didn't do an in depth investigation why it is
specifically needed.)
-/
/-
**LinearIsometryEquiv.instCoeFun** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：instCoeFun : CoeFun (E ≃ₛₗᵢ[σ₁₂] E₂) fun _ => E -> E₂
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shortcut instance, saving 8.5% of compilation time in
`Mathlib/Analysis/InnerProductSpace/Adjoint.lean`.

(This instance was pinpointed by benchmarks; we didn't do an in depth investigat
ion why it is
specifically needed.)
-/
instance instCoeFun : CoeFun (E ≃ₛₗᵢ[σ₁₂] E₂) fun _ ↦ E → E₂ := ⟨DFunLike.coe⟩
/-
**LinearIsometryEquiv.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：coe_injective : @Function.Injective (E ≃ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : @Function.Injective (E ≃ₛₗᵢ[σ₁₂] E₂) (E → E₂) (↑) :=
  DFunLike.coe_injective

@[simp]
/-
**LinearIsometryEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：coe_mk (e : E ≃ₛₗ[σ₁₂] E₂) (he : forall x, ‖e x‖ = ‖x‖) : ⇑(mk e he) = e
参数：e : E ≃ₛₗ[σ₁₂] E₂；he : forall x, ‖e x‖ = ‖x‖。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e : E ≃ₛₗ[σ₁₂] E₂) (he : ∀ x, ‖e x‖ = ‖x‖) : ⇑(mk e he) = e :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.coe_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometr
yEquiv`。
形式化陈述：coe_toLinearEquiv (e : E ≃ₛₗᵢ[σ₁₂] E₂) : ⇑e.toLinearEquiv = e
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearEquiv (e : E ≃ₛₗᵢ[σ₁₂] E₂) : ⇑e.toLinearEquiv = e :=
  rfl

@[ext]
/-
**LinearIsometryEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x = e' x) : e = e'
参数：h : forall x, e x = e' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.toLinearEquiv_injective`：∀ {R : Type u_1} {R₂ : Type
 u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂] 
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
-/
theorem ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, e x = e' x) : e = e' :=
  toLinearEquiv_injective <| LinearEquiv.ext h
/-
**LinearIsometryEquiv.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] {f : E ≃ₛₗᵢ[σ₁₂] E₂} {x x' : E}, x = x' → f x 
= f x'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem congr_arg {f : E ≃ₛₗᵢ[σ₁₂] E₂} : ∀ {x x' : E}, x = x' → f x = f x'
  | _, _, rfl => rfl
/-
**LinearIsometryEquiv.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] {f g : E ≃ₛₗᵢ[σ₁₂] E₂}, f = g → ∀ (x : E), f x
 = g x
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem congr_fun {f g : E ≃ₛₗᵢ[σ₁₂] E₂} (h : f = g) (x : E) : f x = g x :=
  h ▸ rfl

/-- Construct a `LinearIsometryEquiv` from a `LinearEquiv` and two inequalities:
`∀ x, ‖e x‖ ≤ ‖x‖` and `∀ y, ‖e.symm y‖ ≤ ‖y‖`. -/
/-
**LinearIsometryEquiv.ofBounds** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：ofBounds (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : forall x, ‖e x‖ <= ‖x‖) (h₂ : forall y,
 ‖e.symm y‖ <= ‖y‖) : E ≃ₛₗᵢ[σ₁₂] E₂
参数：e : E ≃ₛₗ[σ₁₂] E₂；h₁ : forall x, ‖e x‖ <= ‖x‖；h₂ : forall y, ‖e.symm y‖ <= ‖y
‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `LinearIsometryEquiv` from a `LinearEquiv` and two inequalities:
`∀ x, ‖e x‖ ≤ ‖x‖` and `∀ y, ‖e.symm y‖ ≤ ‖y‖`.
-/
def ofBounds (e : E ≃ₛₗ[σ₁₂] E₂) (h₁ : ∀ x, ‖e x‖ ≤ ‖x‖) (h₂ : ∀ y, ‖e.symm y‖ ≤ ‖y‖) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e, fun x => le_antisymm (h₁ x) <| by simpa only [e.symm_apply_apply] using h₂ (e x)⟩
/-
**LinearIsometryEquiv.norm_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂) (x : E), ‖e x‖ = ‖x‖
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂；x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma norm_map (x : E) : ‖e x‖ = ‖x‖ := by simp
/-
**LinearIsometryEquiv.nnnorm_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂) (x : E), ‖e x‖₊ = ‖x‖₊
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂；x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semin
ormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso
…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma nnnorm_map (x : E) : ‖e x‖₊ = ‖x‖₊ := by simp
/-
**LinearIsometryEquiv.enorm_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂) (x : E), ‖e x‖ₑ = ‖x‖ₑ
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂；x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `enorm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semino
rmedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma enorm_map (x : E) : ‖e x‖ₑ = ‖x‖ₑ := by simp

/-- Reinterpret a `LinearIsometryEquiv` as a `LinearIsometry`. -/
/-
**LinearIsometryEquiv.toLinearIsometry** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：toLinearIsometry : E ->ₛₗᵢ[σ₁₂] E₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.norm_map'`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R] [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}   [inst_2 :
 RingHomInvPair σ₁₂…

--- 原说明 ---
Reinterpret a `LinearIsometryEquiv` as a `LinearIsometry`.
-/
def toLinearIsometry : E →ₛₗᵢ[σ₁₂] E₂ :=
  ⟨e.1, e.2⟩
/-
**LinearIsometryEquiv.toLinearIsometry_injective** 是 Mathlib 中的一个定理，位于命名空间 `Line
arIsometryEquiv`。
形式化陈述：toLinearIsometry_injective : Function.Injective (toLinearIsometry : _ -> E
 ->ₛₗᵢ[σ₁₂] E₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.coe_injective`：coe_injective : @Function.Injective (
E ≃ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (↑)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toLinearIsometry_injective : Function.Injective (toLinearIsometry : _ → E →ₛₗᵢ[σ₁₂] E₂) :=
  fun x _ h => coe_injective (congr_arg _ h : ⇑x.toLinearIsometry = _)

@[simp]
/-
**LinearIsometryEquiv.toLinearIsometry_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etryEquiv`。
形式化陈述：toLinearIsometry_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toLinearIsometry = g.toLin
earIsometry ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometryEquiv.toLinearIsometry_injective`：toLinearIsometry_injecti
ve : Function.Injective (toLinearIsometry : _ -> E ->ₛₗᵢ[σ₁₂] E₂)
-/
theorem toLinearIsometry_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toLinearIsometry = g.toLinearIsometry ↔ f = g :=
  toLinearIsometry_injective.eq_iff

@[simp]
/-
**LinearIsometryEquiv.coe_toLinearIsometry** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etryEquiv`。
形式化陈述：coe_toLinearIsometry : ⇑e.toLinearIsometry = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearIsometry : ⇑e.toLinearIsometry = e :=
  rfl
/-
**LinearIsometryEquiv.isometry** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂), Isometry ⇑e
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
protected theorem isometry : Isometry e :=
  e.toLinearIsometry.isometry

/-- Reinterpret a `LinearIsometryEquiv` as an `IsometryEquiv`. -/
/-
**LinearIsometryEquiv.toIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryE
quiv`。
形式化陈述：toIsometryEquiv : E ≃ᵢ E₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …

--- 原说明 ---
Reinterpret a `LinearIsometryEquiv` as an `IsometryEquiv`.
-/
def toIsometryEquiv : E ≃ᵢ E₂ :=
  ⟨e.toLinearEquiv.toEquiv, e.isometry⟩
/-
**LinearIsometryEquiv.toIsometryEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rIsometryEquiv`。
形式化陈述：toIsometryEquiv_injective : Function.Injective (toIsometryEquiv : (E ≃ₛₗᵢ[
σ₁₂] E₂) -> E ≃ᵢ E₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.coe_injective`：coe_injective : @Function.Injective (
E ≃ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (↑)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toIsometryEquiv_injective :
    Function.Injective (toIsometryEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ᵢ E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toIsometryEquiv = _)

@[simp]
/-
**LinearIsometryEquiv.toIsometryEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsome
tryEquiv`。
形式化陈述：toIsometryEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toIsometryEquiv = g.toIsome
tryEquiv ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometryEquiv.toIsometryEquiv_injective`：toIsometryEquiv_injective
 : Function.Injective (toIsometryEquiv : (E ≃ₛₗᵢ[σ₁₂] E₂) -> E ≃ᵢ E₂)
-/
theorem toIsometryEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toIsometryEquiv = g.toIsometryEquiv ↔ f = g :=
  toIsometryEquiv_injective.eq_iff

@[simp]
/-
**LinearIsometryEquiv.coe_toIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsome
tryEquiv`。
形式化陈述：coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e :=
  rfl
/-
**LinearIsometryEquiv.range_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：range_eq_univ (e : E ≃ₛₗᵢ[σ₁₂] E₂) : Set.range e = Set.univ
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.coe_toIsometryEquiv`：coe_toIsometryEquiv : ⇑e.toIsom
etryEquiv = e
· 使用定理 `IsometryEquiv.range_eq_univ`：range_eq_univ (h : α ≃ᵢ β) : range h = univ
-/
theorem range_eq_univ (e : E ≃ₛₗᵢ[σ₁₂] E₂) : Set.range e = Set.univ := by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

/-- Reinterpret a `LinearIsometryEquiv` as a `Homeomorph`. -/
/-
**LinearIsometryEquiv.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEqui
v`。
形式化陈述：toHomeomorph : E ≃ₜ E₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `LinearIsometryEquiv` as a `Homeomorph`.
-/
def toHomeomorph : E ≃ₜ E₂ :=
  e.toIsometryEquiv.toHomeomorph
/-
**LinearIsometryEquiv.toHomeomorph_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIs
ometryEquiv`。
形式化陈述：toHomeomorph_injective : Function.Injective (toHomeomorph : (E ≃ₛₗᵢ[σ₁₂] E
₂) -> E ≃ₜ E₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.coe_injective`：coe_injective : @Function.Injective (
E ≃ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (↑)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toHomeomorph_injective : Function.Injective (toHomeomorph : (E ≃ₛₗᵢ[σ₁₂] E₂) → E ≃ₜ E₂) :=
  fun x _ h => coe_injective (congr_arg _ h : ⇑x.toHomeomorph = _)

@[simp]
/-
**LinearIsometryEquiv.toHomeomorph_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：toHomeomorph_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toHomeomorph = g.toHomeomorph 
↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometryEquiv.toHomeomorph_injective`：toHomeomorph_injective : Fun
ction.Injective (toHomeomorph : (E ≃ₛₗᵢ[σ₁₂] E₂) -> E ≃ₜ E₂)
-/
theorem toHomeomorph_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toHomeomorph = g.toHomeomorph ↔ f = g :=
  toHomeomorph_injective.eq_iff

@[simp]
/-
**LinearIsometryEquiv.coe_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：coe_toHomeomorph : ⇑e.toHomeomorph = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomeomorph : ⇑e.toHomeomorph = e :=
  rfl
/-
**LinearIsometryEquiv.continuous** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂), Continuous ⇑e
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `LinearIsometryEquiv.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
protected theorem continuous : Continuous e :=
  e.isometry.continuous
/-
**LinearIsometryEquiv.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqui
v`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂) {x : E}, ContinuousAt (⇑e
) x
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
protected theorem continuousAt {x} : ContinuousAt e x :=
  e.continuous.continuousAt
/-
**LinearIsometryEquiv.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqui
v`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂) {s : Set E}, ContinuousOn
 (⇑e) s
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
protected theorem continuousOn {s} : ContinuousOn e s :=
  e.continuous.continuousOn
/-
**LinearIsometryEquiv.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsomet
ryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂) {s : Set E} {x : E}, Cont
inuousWithinAt (⇑e) s x
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
protected theorem continuousWithinAt {s x} : ContinuousWithinAt e s x :=
  e.continuous.continuousWithinAt

/-- Interpret a `LinearIsometryEquiv` as a `ContinuousLinearEquiv`. -/
@[coe]
/-
**LinearIsometryEquiv.toContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearI
sometryEquiv`。
形式化陈述：toContinuousLinearEquiv : E ≃SL[σ₁₂] E₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `LinearIsometryEquiv` as a `ContinuousLinearEquiv`.
-/
def toContinuousLinearEquiv : E ≃SL[σ₁₂] E₂ :=
  { e.toLinearIsometry.toContinuousLinearMap, e.toHomeomorph with }
/-
**LinearIsometryEquiv.toContinuousLinearEquiv_injective** 是 Mathlib 中的一个定理，位于命名空
间 `LinearIsometryEquiv`。
形式化陈述：toContinuousLinearEquiv_injective : Function.Injective (toContinuousLinear
Equiv : _ -> E ≃SL[σ₁₂] E₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.coe_injective`：coe_injective : @Function.Injective (
E ≃ₛₗᵢ[σ₁₂] E₂) (E -> E₂) (↑)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toContinuousLinearEquiv_injective :
    Function.Injective (toContinuousLinearEquiv : _ → E ≃SL[σ₁₂] E₂) := fun x _ h =>
  coe_injective (congr_arg _ h : ⇑x.toContinuousLinearEquiv = _)

@[simp]
/-
**LinearIsometryEquiv.toContinuousLinearEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earIsometryEquiv`。
形式化陈述：toContinuousLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} : f.toContinuousLinearE
quiv = g.toContinuousLinearEquiv ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometryEquiv.toContinuousLinearEquiv_injective`：toContinuousLinea
rEquiv_injective : Function.Injective (toContinuousLinearEquiv : _ -> E ≃SL[σ₁₂]
 E₂)
-/
theorem toContinuousLinearEquiv_inj {f g : E ≃ₛₗᵢ[σ₁₂] E₂} :
    f.toContinuousLinearEquiv = g.toContinuousLinearEquiv ↔ f = g :=
  toContinuousLinearEquiv_injective.eq_iff

@[simp]
/-
**LinearIsometryEquiv.coe_toContinuousLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earIsometryEquiv`。
形式化陈述：coe_toContinuousLinearEquiv : ⇑e.toContinuousLinearEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousLinearEquiv : ⇑e.toContinuousLinearEquiv = e :=
  rfl

variable (R E)

/-- Identity map as a `LinearIsometryEquiv`. -/
/-
**LinearIsometryEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：refl : E ≃ₗᵢ[R] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity map as a `LinearIsometryEquiv`.
-/
def refl : E ≃ₗᵢ[R] E :=
  ⟨LinearEquiv.refl R E, fun _ => rfl⟩

/-- Linear isometry equiv between a space and its lift to another universe. -/
/-
**LinearIsometryEquiv.ulift** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：ulift : ULift E ≃ₗᵢ[R] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear isometry equiv between a space and its lift to another universe.
-/
def ulift : ULift E ≃ₗᵢ[R] E :=
  { ContinuousLinearEquiv.ulift with norm_map' := fun _ => rfl }

variable {R E}
/-
**LinearIsometryEquiv.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：instInhabited : Inhabited (E ≃ₗᵢ[R] E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (E ≃ₗᵢ[R] E) := ⟨refl R E⟩

@[simp]
/-
**LinearIsometryEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：coe_refl : ⇑(refl R E) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ⇑(refl R E) = id :=
  rfl
/-
**LinearIsometryEquiv.toLinearEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsomet
ryEquiv`。
形式化陈述：∀ {R : Type u_1} {E : Type u_5} [inst : Semiring R] [inst_1 : SeminormedAd
dCommGroup E] [inst_2 : _root_.Module R E],   (LinearIsometryEquiv.refl R E).toL
inearEquiv = LinearEquiv.refl R E
参数：LinearIsometryEquiv.refl R E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toLinearEquiv_refl : (refl R E).toLinearEquiv = .refl R E := rfl
/-
**LinearIsometryEquiv.toContinuousLinearEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {E : Type u_5} [inst : Semiring R] [inst_1 : SeminormedAd
dCommGroup E] [inst_2 : _root_.Module R E],   ↑(LinearIsometryEquiv.refl R E) = 
ContinuousLinearEquiv.refl R E
参数：LinearIsometryEquiv.refl R E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toContinuousLinearEquiv_refl : (refl R E).toContinuousLinearEquiv = .refl R E := rfl

/-- The inverse `LinearIsometryEquiv`. -/
/-
**LinearIsometryEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：symm : E₂ ≃ₛₗᵢ[σ₂₁] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse `LinearIsometryEquiv`.
-/
def symm : E₂ ≃ₛₗᵢ[σ₂₁] E :=
  ⟨e.toLinearEquiv.symm, fun x =>
    (e.norm_map _).symm.trans <| congr_arg norm <| e.toLinearEquiv.apply_symm_apply x⟩

@[simp]
/-
**LinearIsometryEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：apply_symm_apply (x : E₂) : e (e.symm x) = x
参数：x : E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem apply_symm_apply (x : E₂) : e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x

@[simp]
/-
**LinearIsometryEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：symm_apply_apply (x : E) : e.symm (e x) = x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem symm_apply_apply (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x
/-
**LinearIsometryEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
/-
**LinearIsometryEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply
/-
**LinearIsometryEquiv.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryE
quiv`。
形式化陈述：map_eq_zero_iff {x : E} : e x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
-/
theorem map_eq_zero_iff {x : E} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff

@[simp]
/-
**LinearIsometryEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：symm_symm : e.symm.symm = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm : e.symm.symm = e := rfl
/-
**LinearIsometryEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEq
uiv`。
形式化陈述：symm_bijective : Function.Bijective (symm : (E₂ ≃ₛₗᵢ[σ₂₁] E) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `LinearIsometryEquiv.symm_symm`：symm_symm : e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective (symm : (E₂ ≃ₛₗᵢ[σ₂₁] E) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**LinearIsometryEquiv.toLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsomet
ryEquiv`。
形式化陈述：toLinearEquiv_symm : e.symm.toLinearEquiv = e.toLinearEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_symm : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.coe_symm_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearIs
ometryEquiv`。
形式化陈述：coe_symm_toLinearEquiv : ⇑e.toLinearEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toLinearEquiv : ⇑e.toLinearEquiv.symm = e.symm := rfl

@[simp]
/-
**LinearIsometryEquiv.toContinuousLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearIsometryEquiv`。
形式化陈述：toContinuousLinearEquiv_symm : e.symm.toContinuousLinearEquiv = e.toContin
uousLinearEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearEquiv_symm :
    e.symm.toContinuousLinearEquiv = e.toContinuousLinearEquiv.symm := rfl

@[simp]
/-
**LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间
 `LinearIsometryEquiv`。
形式化陈述：coe_symm_toContinuousLinearEquiv : ⇑e.toContinuousLinearEquiv.symm = e.sym
m
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toContinuousLinearEquiv : ⇑e.toContinuousLinearEquiv.symm = e.symm :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.toIsometryEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etryEquiv`。
形式化陈述：toIsometryEquiv_symm : e.symm.toIsometryEquiv = e.toIsometryEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIsometryEquiv_symm : e.symm.toIsometryEquiv = e.toIsometryEquiv.symm :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.coe_symm_toIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Linear
IsometryEquiv`。
形式化陈述：coe_symm_toIsometryEquiv : ⇑e.toIsometryEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toIsometryEquiv : ⇑e.toIsometryEquiv.symm = e.symm := rfl

@[simp]
/-
**LinearIsometryEquiv.toHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometr
yEquiv`。
形式化陈述：toHomeomorph_symm : e.symm.toHomeomorph = e.toHomeomorph.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorph_symm : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.coe_symm_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `LinearIso
metryEquiv`。
形式化陈述：coe_symm_toHomeomorph : ⇑e.toHomeomorph.symm = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toHomeomorph : ⇑e.toHomeomorph.symm = e.symm := rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**LinearIsometryEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv
.Simps`。
形式化陈述：{R : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R] →       [inst
_1 : Semiring R₂] →         (σ₁₂ : R →+* R₂) →           {σ₂₁ : R₂ →+* R} →     
        [inst_2 : RingHomInvPair σ₁₂ σ₂₁] →               [inst_3 : RingHomInvPa
ir σ₂₁ σ₁₂] →                 (E : Type u_11) →                   (E₂ : Type u_1
2) →                     [inst_4 : SeminormedAddCommGroup E] →                  
     [inst_5 : SeminormedAddCommGroup E₂] →                         [inst_6 : _r
oot_.Module R E] → [inst_7 : _root_.Module R₂ E₂] → (E ≃ₛₗᵢ[σ₁₂] E₂) → E → E₂
参数：σ₁₂ : R →+* R₂；E : Type u_11；E₂ : Type u_12；E ≃ₛₗᵢ[σ₁₂] E₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [Module R E]
    [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E → E₂ :=
  h

/-- See Note [custom simps projection] -/
/-
**LinearIsometryEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry
Equiv.Simps`。
形式化陈述：{R : Type u_1} →   {R₂ : Type u_2} →     [inst : Semiring R] →       [inst
_1 : Semiring R₂] →         (σ₁₂ : R →+* R₂) →           {σ₂₁ : R₂ →+* R} →     
        [inst_2 : RingHomInvPair σ₁₂ σ₂₁] →               [inst_3 : RingHomInvPa
ir σ₂₁ σ₁₂] →                 (E : Type u_11) →                   (E₂ : Type u_1
2) →                     [inst_4 : SeminormedAddCommGroup E] →                  
     [inst_5 : SeminormedAddCommGroup E₂] →                         [inst_6 : _r
oot_.Module R E] → [inst_7 : _root_.Module R₂ E₂] → (E ≃ₛₗᵢ[σ₁₂] E₂) → E₂ → E
参数：σ₁₂ : R →+* R₂；E : Type u_11；E₂ : Type u_12；E ≃ₛₗᵢ[σ₁₂] E₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (σ₁₂ : R →+* R₂) {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]
    [RingHomInvPair σ₂₁ σ₁₂] (E E₂ : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂]
    [Module R E] [Module R₂ E₂] (h : E ≃ₛₗᵢ[σ₁₂] E₂) : E₂ → E :=
  h.symm

initialize_simps_projections LinearIsometryEquiv (toFun → apply, invFun → symm_apply)

/-- Composition of `LinearIsometryEquiv`s as a `LinearIsometryEquiv`. -/
/-
**LinearIsometryEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : E ≃ₛₗᵢ[σ₁₃] E₃
参数：e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `LinearIsometryEquiv`s as a `LinearIsometryEquiv`.
-/
def trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : E ≃ₛₗᵢ[σ₁₃] E₃ :=
  ⟨e.toLinearEquiv.trans e'.toLinearEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]
/-
**LinearIsometryEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：coe_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : ⇑(e₁.trans e₂) = 
e₂ ∘ e₁
参数：e₁ : E ≃ₛₗᵢ[σ₁₂] E₂；e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv
`。
形式化陈述：trans_apply (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E) : (e₁.tra
ns e₂ : E ≃ₛₗᵢ[σ₁₃] E₃) c = e₂ (e₁ c)
参数：e₁ : E ≃ₛₗᵢ[σ₁₂] E₂；e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃；c : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (c : E) :
    (e₁.trans e₂ : E ≃ₛₗᵢ[σ₁₃] E₃) c = e₂ (e₁ c) :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.toLinearEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsome
tryEquiv`。
形式化陈述：toLinearEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : (e.trans e').toLinearEquiv = 
e.toLinearEquiv.trans e'.toLinearEquiv
参数：e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toLinearEquiv = e.toLinearEquiv.trans e'.toLinearEquiv :=
  rfl
/-
**LinearIsometryEquiv.toContinuousLinearEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `L
inearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {R₃ : Type u_3} {E : Type u_5} {E₂ : Type
 u_6} {E₃ : Type u_7} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : Sem
iring R₃] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R}   
{σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [inst_3 : RingHomInvPair σ₁₂ σ₂₁] [inst_4 : 
RingHomInvPair σ₂₁ σ₁₂]   [inst_5 : RingHomInvPair σ₁₃ σ₃₁] [inst_6 : RingHomInv
Pair σ₃₁ σ₁₃] [inst_7 : RingHomInvPair σ₂₃ σ₃₂]   [inst_8 : RingHomInvPair σ₃₂ σ
₂₃] [inst_9 : RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [inst_10 : RingHomCompTriple σ₃₂ σ₂
₁ σ₃₁]   [inst_11 : SeminormedAddCommGroup E] [inst_12 : SeminormedAddCommGroup 
E₂] [inst_13 : SeminormedAddCommGroup E₃]   [inst_14 : _root_.Module R E] [inst_
15 : _root_.Module R₂ E₂] [inst_16 : _root_.Module R₃ E₃] (e : E ≃ₛₗᵢ[σ₁₂] E₂)  
 (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃), ↑(e.trans e') = (↑e).trans ↑e'
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂；e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃；e.trans e'；↑e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toContinuousLinearEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toContinuousLinearEquiv =
      e.toContinuousLinearEquiv.trans e'.toContinuousLinearEquiv :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.toIsometryEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIso
metryEquiv`。
形式化陈述：toIsometryEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : (e.trans e').toIsometryEqui
v = e.toIsometryEquiv.trans e'.toIsometryEquiv
参数：e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIsometryEquiv_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toIsometryEquiv = e.toIsometryEquiv.trans e'.toIsometryEquiv :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.toHomeomorph_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsomet
ryEquiv`。
形式化陈述：toHomeomorph_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : (e.trans e').toHomeomorph = e.
toHomeomorph.trans e'.toHomeomorph
参数：e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorph_trans (e' : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e.trans e').toHomeomorph = e.toHomeomorph.trans e'.toHomeomorph :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：trans_refl : e.trans (refl R₂ E₂) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
-/
theorem trans_refl : e.trans (refl R₂ E₂) = e :=
  ext fun _ => rfl

@[simp]
/-
**LinearIsometryEquiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：refl_trans : (refl R E).trans e = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
-/
theorem refl_trans : (refl R E).trans e = e :=
  ext fun _ => rfl

@[simp]
/-
**LinearIsometryEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryE
quiv`。
形式化陈述：self_trans_symm : e.trans e.symm = refl R E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
-/
theorem self_trans_symm : e.trans e.symm = refl R E :=
  ext e.symm_apply_apply

@[simp]
/-
**LinearIsometryEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryE
quiv`。
形式化陈述：symm_trans_self : e.symm.trans e = refl R₂ E₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
-/
theorem symm_trans_self : e.symm.trans e = refl R₂ E₂ :=
  ext e.apply_symm_apply

@[simp]
/-
**LinearIsometryEquiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEq
uiv`。
形式化陈述：symm_comp_self : e.symm ∘ e = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
-/
theorem symm_comp_self : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp]
/-
**LinearIsometryEquiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEq
uiv`。
形式化陈述：self_comp_symm : e ∘ e.symm = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.symm_comp_self`：symm_comp_self : e.symm ∘ e = id
-/
theorem self_comp_symm : e ∘ e.symm = id :=
  e.symm.symm_comp_self

@[simp]
/-
**LinearIsometryEquiv.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : (e₁.trans e₂).sy
mm = e₂.symm.trans e₁.symm
参数：e₁ : E ≃ₛₗᵢ[σ₁₂] E₂；e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
/-
**LinearIsometryEquiv.coe_symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEq
uiv`。
形式化陈述：coe_symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) : ⇑(e₁.trans e
₂).symm = e₁.symm ∘ e₂.symm
参数：e₁ : E ≃ₛₗᵢ[σ₁₂] E₂；e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_trans (e₁ : E ≃ₛₗᵢ[σ₁₂] E₂) (e₂ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) :
    ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
  rfl
/-
**LinearIsometryEquiv.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv
`。
形式化陈述：trans_assoc (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ 
≃ₛₗᵢ[σ₃₄] E₄) : eEE₂.trans (eE₂E₃.trans eE₃E₄) = (eEE₂.trans eE₂E₃).trans eE₃E₄
参数：eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂；eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃；eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_assoc (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄) :
    eEE₂.trans (eE₂E₃.trans eE₃E₄) = (eEE₂.trans eE₂E₃).trans eE₃E₄ :=
  rfl
/-
**LinearIsometryEquiv.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：instGroup : Group (E ≃ₗᵢ[R] E) where mul e₁ e₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**LinearIsometryEquiv.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：coe_one : ⇑(1 : E ≃ₗᵢ[R] E) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : E ≃ₗᵢ[R] E) = id :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：coe_mul (e e' : E ≃ₗᵢ[R] E) : ⇑(e * e') = e ∘ e'
参数：e e' : E ≃ₗᵢ[R] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (e e' : E ≃ₗᵢ[R] E) : ⇑(e * e') = e ∘ e' :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：coe_inv (e : E ≃ₗᵢ[R] E) : ⇑e⁻¹ = e.symm
参数：e : E ≃ₗᵢ[R] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (e : E ≃ₗᵢ[R] E) : ⇑e⁻¹ = e.symm :=
  rfl
/-
**LinearIsometryEquiv.one_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：one_def : (1 : E ≃ₗᵢ[R] E) = refl _ _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : E ≃ₗᵢ[R] E) = refl _ _ :=
  rfl
/-
**LinearIsometryEquiv.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：mul_def (e e' : E ≃ₗᵢ[R] E) : (e * e' : E ≃ₗᵢ[R] E) = e'.trans e
参数：e e' : E ≃ₗᵢ[R] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (e e' : E ≃ₗᵢ[R] E) : (e * e' : E ≃ₗᵢ[R] E) = e'.trans e :=
  rfl
/-
**LinearIsometryEquiv.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：inv_def (e : E ≃ₗᵢ[R] E) : (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm
参数：e : E ≃ₗᵢ[R] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (e : E ≃ₗᵢ[R] E) : (e⁻¹ : E ≃ₗᵢ[R] E) = e.symm :=
  rfl
/-
**LinearIsometryEquiv.toContinuousLinearEquiv_one** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {E : Type u_5} [inst : Semiring R] [inst_1 : SeminormedAd
dCommGroup E] [inst_2 : _root_.Module R E],   ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toContinuousLinearEquiv_one : toContinuousLinearEquiv (1 : E ≃ₗᵢ[R] E) = 1 := rfl
/-
**LinearIsometryEquiv.toContinuousLinearEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {E : Type u_5} [inst : Semiring R] [inst_1 : SeminormedAd
dCommGroup E] [inst_2 : _root_.Module R E]   (e e' : E ≃ₗᵢ[R] E), ↑(e * e') = ↑e
 * ↑e'
参数：e e' : E ≃ₗᵢ[R] E；e * e'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toContinuousLinearEquiv_mul (e e' : E ≃ₗᵢ[R] E) :
    toContinuousLinearEquiv (e * e') = e.toContinuousLinearEquiv * e'.toContinuousLinearEquiv := rfl
/-
**LinearIsometryEquiv.toContinuousLinearEquiv_inv** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {E : Type u_5} [inst : Semiring R] [inst_1 : SeminormedAd
dCommGroup E] [inst_2 : _root_.Module R E]   (e : E ≃ₗᵢ[R] E), ↑e⁻¹ = (↑e)⁻¹
参数：e : E ≃ₗᵢ[R] E；↑e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**LinearIsometryEquiv.trans_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：trans_one : e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.trans_refl`：trans_refl : e.trans (refl R₂ E₂) = e

--- 原说明 ---
Lemmas about mixing the group structure with definitions. Because we have multip
le ways to
express `LinearIsometryEquiv.refl`, `LinearIsometryEquiv.symm`, and
`LinearIsometryEquiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want t
o preserve it
after simp.

This copies the approach used by the lemmas near `Equiv.Perm.trans_one`.
-/
theorem trans_one : e.trans (1 : E₂ ≃ₗᵢ[R₂] E₂) = e :=
  trans_refl _

@[simp]
/-
**LinearIsometryEquiv.one_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：one_trans : (1 : E ≃ₗᵢ[R] E).trans e = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.refl_trans`：refl_trans : (refl R E).trans e = e
-/
theorem one_trans : (1 : E ≃ₗᵢ[R] E).trans e = e :=
  refl_trans _

@[simp]
/-
**LinearIsometryEquiv.refl_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：refl_mul (e : E ≃ₗᵢ[R] E) : refl _ _ * e = e
参数：e : E ≃ₗᵢ[R] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.trans_refl`：trans_refl : e.trans (refl R₂ E₂) = e
-/
theorem refl_mul (e : E ≃ₗᵢ[R] E) : refl _ _ * e = e :=
  trans_refl _

@[simp]
/-
**LinearIsometryEquiv.mul_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：mul_refl (e : E ≃ₗᵢ[R] E) : e * refl _ _ = e
参数：e : E ≃ₗᵢ[R] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.refl_trans`：refl_trans : (refl R E).trans e = e
-/
theorem mul_refl (e : E ≃ₗᵢ[R] E) : e * refl _ _ = e :=
  refl_trans _

/-- Reinterpret a `LinearIsometryEquiv` as a `ContinuousLinearEquiv`. -/
/-
**LinearIsometryEquiv.instCoeTCContinuousLinearEquiv** 是 Mathlib 中的一个实例，位于命名空间 `
LinearIsometryEquiv`。
形式化陈述：instCoeTCContinuousLinearEquiv : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ≃SL[σ₁₂] E₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `LinearIsometryEquiv` as a `ContinuousLinearEquiv`.
-/
instance instCoeTCContinuousLinearEquiv : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ≃SL[σ₁₂] E₂) :=
  ⟨fun e => e.toContinuousLinearEquiv⟩
/-
**LinearIsometryEquiv.instCoeTCContinuousLinearMap** 是 Mathlib 中的一个实例，位于命名空间 `Li
nearIsometryEquiv`。
形式化陈述：instCoeTCContinuousLinearMap : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E ->SL[σ₁₂] E₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeTCContinuousLinearMap : CoeTC (E ≃ₛₗᵢ[σ₁₂] E₂) (E →SL[σ₁₂] E₂) :=
  ⟨fun e => ↑(e : E ≃SL[σ₁₂] E₂)⟩
/-
**LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry** 是 Mathlib 中的一个定理，
位于命名空间 `LinearIsometryEquiv`。
形式化陈述：toContinuousLinearMap_toLinearIsometry : e.toLinearIsometry.toContinuousLi
nearMap = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearMap_toLinearIsometry :
    e.toLinearIsometry.toContinuousLinearMap = e := rfl
/-
**LinearIsometryEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：coe_coe : ⇑(e : E ≃SL[σ₁₂] E₂) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe : ⇑(e : E ≃SL[σ₁₂] E₂) = e := rfl
/-
**LinearIsometryEquiv.coe_coe''** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：coe_coe'' : ⇑(e : E ->SL[σ₁₂] E₂) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe'' : ⇑(e : E →SL[σ₁₂] E₂) = e := rfl
/-
**LinearIsometryEquiv.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：map_zero : e 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
-/
theorem map_zero : e 0 = 0 :=
  e.1.map_zero
/-
**LinearIsometryEquiv.map_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：map_add (x y : E) : e (x + y) = e x + e y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.map_add`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ 
: Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst_…
-/
theorem map_add (x y : E) : e (x + y) = e x + e y :=
  e.1.map_add x y
/-
**LinearIsometryEquiv.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：map_sub (x y : E) : e (x - y) = e x - e y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem map_sub (x y : E) : e (x - y) = e x - e y :=
  e.1.map_sub x y
/-
**LinearIsometryEquiv.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：map_smul [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E) : e (c • x) = c •
 e x
参数：c : R；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
-/
theorem map_smulₛₗ (c : R) (x : E) : e (c • x) = σ₁₂ c • e x :=
  e.1.map_smulₛₗ c x
/-
**LinearIsometryEquiv.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：map_smul [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E) : e (c • x) = c •
 e x
参数：c : R；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
-/
theorem map_smul [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (c : R) (x : E) : e (c • x) = c • e x :=
  e.1.map_smul c x


@[simp]
/-
**LinearIsometryEquiv.dist_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：dist_map (x y : E) : dist (e x) (e y) = dist x y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.dist_map`：dist_map (x y : E) : dist (f x) (f y) = dist x 
y
-/
theorem dist_map (x y : E) : dist (e x) (e y) = dist x y :=
  e.toLinearIsometry.dist_map x y

@[simp]
/-
**LinearIsometryEquiv.edist_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：edist_map (x y : E) : edist (e x) (e y) = edist x y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.edist_map`：edist_map (x y : E) : edist (f x) (f y) = edis
t x y
-/
theorem edist_map (x y : E) : edist (e x) (e y) = edist x y :=
  e.toLinearIsometry.edist_map x y
/-
**LinearIsometryEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂), Function.Bijective ⇑e
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
protected theorem bijective : Bijective e :=
  e.1.bijective
/-
**LinearIsometryEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂), Function.Injective ⇑e
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
protected theorem injective : Injective e :=
  e.1.injective
/-
**LinearIsometryEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂), Function.Surjective ⇑e
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
-/
protected theorem surjective : Surjective e :=
  e.1.surjective
/-
**LinearIsometryEquiv.map_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：map_eq_iff {x y : E} : e x = e y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearIsometryEquiv.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Typ
e u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+*
 R₂} {σ₂₁ : R₂ →+* …
-/
theorem map_eq_iff {x y : E} : e x = e y ↔ x = y :=
  e.injective.eq_iff
/-
**LinearIsometryEquiv.map_ne** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：map_ne {x y : E} (h : x != y) : e x != e y
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `LinearIsometryEquiv.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Typ
e u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+*
 R₂} {σ₂₁ : R₂ →+* …
-/
theorem map_ne {x y : E} (h : x ≠ y) : e x ≠ e y :=
  e.injective.ne h
/-
**LinearIsometryEquiv.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂), LipschitzWith 1 ⇑e
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `LinearIsometryEquiv.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
protected theorem lipschitz : LipschitzWith 1 e :=
  e.isometry.lipschitz
/-
**LinearIsometryEquiv.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_2 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_3 : RingHomInvPair σ₂₁ σ₁₂]   [inst_4 : SeminormedA
ddCommGroup E] [inst_5 : SeminormedAddCommGroup E₂] [inst_6 : _root_.Module R E]
   [inst_7 : _root_.Module R₂ E₂] (e : E ≃ₛₗᵢ[σ₁₂] E₂), AntilipschitzWith 1 ⇑e
参数：e : E ≃ₛₗᵢ[σ₁₂] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `LinearIsometryEquiv.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.isometry.antilipschitz
/-
**LinearIsometryEquiv.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIs
ometryEquiv`。
形式化陈述：image_eq_preimage_symm (s : Set E) : e '' s = e.symm ⁻¹' s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.image_eq_preimage_symm`：∀ {R : Type u_1} {S : Type u_6} {M :
 Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 :
 AddCommMonoid M] [inst_…
-/
theorem image_eq_preimage_symm (s : Set E) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.image_eq_preimage_symm s

@[simp]
/-
**LinearIsometryEquiv.ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv
`。
形式化陈述：ediam_image (s : Set E) : Metric.ediam (e '' s) = Metric.ediam s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `LinearIsometryEquiv.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
theorem ediam_image (s : Set E) : Metric.ediam (e '' s) = Metric.ediam s :=
  e.isometry.ediam_image s

@[simp]
/-
**LinearIsometryEquiv.diam_image** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：diam_image (s : Set E) : Metric.diam (e '' s) = Metric.diam s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
· 使用定理 `LinearIsometryEquiv.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
theorem diam_image (s : Set E) : Metric.diam (e '' s) = Metric.diam s :=
  e.isometry.diam_image s

@[simp]
/-
**LinearIsometryEquiv.preimage_ball** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：preimage_ball (x : E₂) (r : Real) : e ⁻¹' Metric.ball x r = Metric.ball (e
.symm x) r
参数：x : E₂；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.preimage_ball`：preimage_ball (h : α ≃ᵢ β) (x : β) (r : Rea
l) : h ⁻¹' Metric.ball x r = Metric.ball (h.symm x) r
-/
theorem preimage_ball (x : E₂) (r : ℝ) : e ⁻¹' Metric.ball x r = Metric.ball (e.symm x) r :=
  e.toIsometryEquiv.preimage_ball x r

@[simp]
/-
**LinearIsometryEquiv.preimage_sphere** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryE
quiv`。
形式化陈述：preimage_sphere (x : E₂) (r : Real) : e ⁻¹' Metric.sphere x r = Metric.sph
ere (e.symm x) r
参数：x : E₂；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.preimage_sphere`：preimage_sphere (h : α ≃ᵢ β) (x : β) (r :
 Real) : h ⁻¹' Metric.sphere x r = Metric.sphere (h.symm x) r
-/
theorem preimage_sphere (x : E₂) (r : ℝ) : e ⁻¹' Metric.sphere x r = Metric.sphere (e.symm x) r :=
  e.toIsometryEquiv.preimage_sphere x r

@[simp]
/-
**LinearIsometryEquiv.preimage_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsome
tryEquiv`。
形式化陈述：preimage_closedBall (x : E₂) (r : Real) : e ⁻¹' Metric.closedBall x r = Me
tric.closedBall (e.symm x) r
参数：x : E₂；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.preimage_closedBall`：preimage_closedBall (h : α ≃ᵢ β) (x :
 β) (r : Real) : h ⁻¹' Metric.closedBall x r = Metric.closedBall (h.symm x) r
-/
theorem preimage_closedBall (x : E₂) (r : ℝ) :
    e ⁻¹' Metric.closedBall x r = Metric.closedBall (e.symm x) r :=
  e.toIsometryEquiv.preimage_closedBall x r

@[simp]
/-
**LinearIsometryEquiv.image_ball** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`
。
形式化陈述：image_ball (x : E) (r : Real) : e '' Metric.ball x r = Metric.ball (e x) r
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.image_ball`：image_ball (h : α ≃ᵢ β) (x : α) (r : Real) : h
 '' Metric.ball x r = Metric.ball (h x) r
-/
theorem image_ball (x : E) (r : ℝ) : e '' Metric.ball x r = Metric.ball (e x) r :=
  e.toIsometryEquiv.image_ball x r

@[simp]
/-
**LinearIsometryEquiv.image_sphere** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqui
v`。
形式化陈述：image_sphere (x : E) (r : Real) : e '' Metric.sphere x r = Metric.sphere (
e x) r
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.image_sphere`：image_sphere (h : α ≃ᵢ β) (x : α) (r : Real)
 : h '' Metric.sphere x r = Metric.sphere (h x) r
-/
theorem image_sphere (x : E) (r : ℝ) : e '' Metric.sphere x r = Metric.sphere (e x) r :=
  e.toIsometryEquiv.image_sphere x r

@[simp]
/-
**LinearIsometryEquiv.image_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：image_closedBall (x : E) (r : Real) : e '' Metric.closedBall x r = Metric.
closedBall (e x) r
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.image_closedBall`：image_closedBall (h : α ≃ᵢ β) (x : α) (r
 : Real) : h '' Metric.closedBall x r = Metric.closedBall (h x) r
-/
theorem image_closedBall (x : E) (r : ℝ) : e '' Metric.closedBall x r = Metric.closedBall (e x) r :=
  e.toIsometryEquiv.image_closedBall x r

variable {α : Type*} [TopologicalSpace α]

@[simp]
/-
**LinearIsometryEquiv.comp_continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIso
metryEquiv`。
形式化陈述：comp_continuousOn_iff {f : α -> E} {s : Set α} : ContinuousOn (e ∘ f) s ↔ 
ContinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp_continuousOn_iff`：comp_continuousOn_iff {γ} [TopologicalSp
ace γ] (hf : Isometry f) {g : γ -> α} {s : Set γ} : ContinuousOn (f ∘ g) s ↔ Con
tinuousOn g s
· 使用定理 `LinearIsometryEquiv.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
theorem comp_continuousOn_iff {f : α → E} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.isometry.comp_continuousOn_iff

@[simp]
/-
**LinearIsometryEquiv.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsome
tryEquiv`。
形式化陈述：comp_continuous_iff {f : α -> E} : Continuous (e ∘ f) ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp_continuous_iff`：comp_continuous_iff {γ} [TopologicalSpace 
γ] (hf : Isometry f) {g : γ -> α} : Continuous (f ∘ g) ↔ Continuous g
· 使用定理 `LinearIsometryEquiv.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
theorem comp_continuous_iff {f : α → E} : Continuous (e ∘ f) ↔ Continuous f :=
  e.isometry.comp_continuous_iff
/-
**LinearIsometryEquiv.completeSpace_map** 是 Mathlib 中的一个实例，位于命名空间 `LinearIsometr
yEquiv`。
形式化陈述：completeSpace_map (p : Submodule R E) [CompleteSpace p] : CompleteSpace (p
.map (e : E ->ₛₗ[σ₁₂] E₂))
参数：p : Submodule R E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
instance completeSpace_map (p : Submodule R E) [CompleteSpace p] :
    CompleteSpace (p.map (e : E →ₛₗ[σ₁₂] E₂)) :=
  e.toLinearIsometry.completeSpace_map p

/-- Construct a linear isometry equiv from a surjective linear isometry. -/
/-
**LinearIsometryEquiv.ofSurjective** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEqui
v`。
形式化陈述：ofSurjective (f : F ->ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) : F ≃ₛₗᵢ[
σ₁₂] E₂
参数：f : F ->ₛₗᵢ[σ₁₂] E₂；hfr : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a linear isometry equiv from a surjective linear isometry.
-/
noncomputable def ofSurjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    F ≃ₛₗᵢ[σ₁₂] E₂ :=
  { LinearEquiv.ofBijective f.toLinearMap ⟨f.injective, hfr⟩ with norm_map' := f.norm_map }

@[simp]
/-
**LinearIsometryEquiv.coe_ofSurjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：coe_ofSurjective (f : F ->ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) : ⇑(L
inearIsometryEquiv.ofSurjective f hfr) = f
参数：f : F ->ₛₗᵢ[σ₁₂] E₂；hfr : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem coe_ofSurjective (f : F →ₛₗᵢ[σ₁₂] E₂) (hfr : Function.Surjective f) :
    ⇑(LinearIsometryEquiv.ofSurjective f hfr) = f := by
  ext
  rfl

/-- If a linear isometry has an inverse, it is a linear isometric equivalence. -/
/-
**LinearIsometryEquiv.ofLinearIsometry** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：ofLinearIsometry (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E) (h₁ : f.toLine
arMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) : E ≃ₛₗᵢ
[σ₁₂] E₂
参数：f : E ->ₛₗᵢ[σ₁₂] E₂；g : E₂ ->ₛₗ[σ₂₁] E；h₁ : f.toLinearMap.comp g = LinearMap.
id；h₂ : g.comp f.toLinearMap = LinearMap.id。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…

--- 原说明 ---
If a linear isometry has an inverse, it is a linear isometric equivalence.
-/
def ofLinearIsometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    E ≃ₛₗᵢ[σ₁₂] E₂ :=
  { toLinearEquiv := LinearEquiv.ofLinearMap f.toLinearMap g h₁ h₂
    norm_map' := fun x => f.norm_map x }

@[simp]
/-
**LinearIsometryEquiv.coe_ofLinearIsometry** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etryEquiv`。
形式化陈述：coe_ofLinearIsometry (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E) (h₁ : f.to
LinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) : (o
fLinearIsometry f g h₁ h₂ : E -> E₂) = (f : E -> E₂)
参数：f : E ->ₛₗᵢ[σ₁₂] E₂；g : E₂ ->ₛₗ[σ₂₁] E；h₁ : f.toLinearMap.comp g = LinearMap.
id；h₂ : g.comp f.toLinearMap = LinearMap.id。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofLinearIsometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    (ofLinearIsometry f g h₁ h₂ : E → E₂) = (f : E → E₂) :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.coe_ofLinearIsometry_symm** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rIsometryEquiv`。
形式化陈述：coe_ofLinearIsometry_symm (f : E ->ₛₗᵢ[σ₁₂] E₂) (g : E₂ ->ₛₗ[σ₂₁] E) (h₁ :
 f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id)
 : ((ofLinearIsometry f g h₁ h₂).symm : E₂ -> E) = (g : E₂ -> E)
参数：f : E ->ₛₗᵢ[σ₁₂] E₂；g : E₂ ->ₛₗ[σ₂₁] E；h₁ : f.toLinearMap.comp g = LinearMap.
id；h₂ : g.comp f.toLinearMap = LinearMap.id。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofLinearIsometry_symm (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
    (h₁ : f.toLinearMap.comp g = LinearMap.id) (h₂ : g.comp f.toLinearMap = LinearMap.id) :
    ((ofLinearIsometry f g h₁ h₂).symm : E₂ → E) = (g : E₂ → E) :=
  rfl

variable (R) in
/-- The negation operation on a normed space `E`, considered as a linear isometry equivalence. -/
/-
**LinearIsometryEquiv.neg** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：neg : E ≃ₗᵢ[R] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The negation operation on a normed space `E`, considered as a linear isometry eq
uivalence.
-/
def neg : E ≃ₗᵢ[R] E :=
  { LinearEquiv.neg R with norm_map' := norm_neg }

@[simp]
/-
**LinearIsometryEquiv.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：coe_neg : (neg R : E -> E) = fun x => -x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg : (neg R : E → E) = fun x => -x :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.symm_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：symm_neg : (neg R : E ≃ₗᵢ[R] E).symm = neg R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_neg : (neg R : E ≃ₗᵢ[R] E).symm = neg R :=
  rfl

variable (R E E₂)

/-- The natural equivalence `E × E₂ ≃ E₂ × E` is a linear isometry. -/
@[simps! apply]
/-
**LinearIsometryEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：prodComm [Module R E₂] : E × E₂ ≃ₗᵢ[R] E₂ × E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence `E × E₂ ≃ E₂ × E` is a linear isometry.
-/
def prodComm [Module R E₂] : E × E₂ ≃ₗᵢ[R] E₂ × E :=
  ⟨LinearEquiv.prodComm R E E₂, by intro; simp [norm, sup_comm]⟩

@[simp]
/-
**LinearIsometryEquiv.symm_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：symm_prodComm [Module R E₂] : (prodComm R E E₂).symm = prodComm R E₂ E
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_prodComm [Module R E₂] : (prodComm R E E₂).symm = prodComm R E₂ E :=
  rfl

variable (E₃)

/-- The natural equivalence `(E × E₂) × E₃ ≃ E × (E₂ × E₃)` is a linear isometry. -/
/-
**LinearIsometryEquiv.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：prodAssoc [Module R E₂] [Module R E₃] : (E × E₂) × E₃ ≃ₗᵢ[R] E × E₂ × E₃
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence `(E × E₂) × E₃ ≃ E × (E₂ × E₃)` is a linear isometry.
-/
def prodAssoc [Module R E₂] [Module R E₃] : (E × E₂) × E₃ ≃ₗᵢ[R] E × E₂ × E₃ :=
  { LinearEquiv.prodAssoc R E E₂ E₃ with
    norm_map' := by
      rintro ⟨⟨e, f⟩, g⟩
      simp only [LinearEquiv.prodAssoc_apply, AddEquiv.toEquiv_eq_coe,
        Equiv.toFun_as_coe, EquivLike.coe_coe, AddEquiv.coe_prodAssoc,
        Equiv.prodAssoc_apply, Prod.norm_def, max_assoc] }

@[simp]
/-
**LinearIsometryEquiv.coe_prodAssoc** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqu
iv`。
形式化陈述：coe_prodAssoc [Module R E₂] [Module R E₃] : (prodAssoc R E E₂ E₃ : (E × E₂
) × E₃ -> E × E₂ × E₃) = Equiv.prodAssoc E E₂ E₃
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodAssoc [Module R E₂] [Module R E₃] :
    (prodAssoc R E E₂ E₃ : (E × E₂) × E₃ → E × E₂ × E₃) = Equiv.prodAssoc E E₂ E₃ :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.coe_prodAssoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsomet
ryEquiv`。
形式化陈述：coe_prodAssoc_symm [Module R E₂] [Module R E₃] : ((prodAssoc R E E₂ E₃).sy
mm : E × E₂ × E₃ -> (E × E₂) × E₃) = (Equiv.prodAssoc E E₂ E₃).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodAssoc_symm [Module R E₂] [Module R E₃] :
    ((prodAssoc R E E₂ E₃).symm : E × E₂ × E₃ → (E × E₂) × E₃) = (Equiv.prodAssoc E E₂ E₃).symm :=
  rfl

/-- If `p` is a submodule that is equal to `⊤`, then `LinearIsometryEquiv.ofTop p hp` is the
"identity" equivalence between `p` and `E`. -/
@[simps! toLinearEquiv apply symm_apply_coe]
/-
**LinearIsometryEquiv.ofTop** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：ofTop {R : Type*} [Ring R] [Module R E] (p : Submodule R E) (hp : p = ⊤) :
 p ≃ₗᵢ[R] E
参数：p : Submodule R E；hp : p = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p` is a submodule that is equal to `⊤`, then `LinearIsometryEquiv.ofTop p hp
` is the
"identity" equivalence between `p` and `E`.
-/
def ofTop {R : Type*} [Ring R] [Module R E] (p : Submodule R E) (hp : p = ⊤) : p ≃ₗᵢ[R] E :=
  { p.subtypeₗᵢ with toLinearEquiv := LinearEquiv.ofTop p hp }

variable {R E E₂ E₃} {R' : Type*} [Ring R']
variable [Module R' E] (p q : Submodule R' E)

/-- `LinearEquiv.ofEq` as a `LinearIsometryEquiv`. -/
/-
**LinearIsometryEquiv.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：ofEq (hpq : p = q) : p ≃ₗᵢ[R'] q
参数：hpq : p = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearEquiv.ofEq` as a `LinearIsometryEquiv`.
-/
def ofEq (hpq : p = q) : p ≃ₗᵢ[R'] q :=
  { LinearEquiv.ofEq p q hpq with norm_map' := fun _ => rfl }

variable {p q}

@[simp]
/-
**LinearIsometryEquiv.coe_ofEq_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEq
uiv`。
形式化陈述：coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : E) = x
参数：h : p = q；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : E) = x :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.ofEq_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm
参数：h : p = q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm :=
  rfl

@[simp]
/-
**LinearIsometryEquiv.ofEq_rfl** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：ofEq_rfl : ofEq p p rfl = LinearIsometryEquiv.refl R' p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEq_rfl : ofEq p p rfl = LinearIsometryEquiv.refl R' p := rfl

section submoduleMap

variable {R R₁ R₂ M M₂ : Type*}
variable [Ring R] [Ring R₂] [SeminormedAddCommGroup M] [SeminormedAddCommGroup M₂]
variable [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

/-- A linear isometry equivalence between two modules restricts to a
linear isometry equivalence from any submodule `p` of the domain onto
the image of that submodule.

This is a version of `LinearEquiv.submoduleMap` extended to linear isometry equivalences. -/
@[simps!]
/-
**LinearIsometryEquiv.submoduleMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometryEqui
v`。
形式化陈述：submoduleMap (p : Submodule R M) (e : M ≃ₛₗᵢ[σ₁₂] M₂) : p ≃ₛₗᵢ[σ₁₂] p.map 
(e : M ->ₛₗ[σ₁₂] M₂)
参数：p : Submodule R M；e : M ≃ₛₗᵢ[σ₁₂] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear isometry equivalence between two modules restricts to a
linear isometry equivalence from any submodule `p` of the domain onto
the image of that submodule.

This is a version of `LinearEquiv.submoduleMap` extended to linear isometry equi
valences.
-/
def submoduleMap (p : Submodule R M) (e : M ≃ₛₗᵢ[σ₁₂] M₂) :
    p ≃ₛₗᵢ[σ₁₂] p.map (e : M →ₛₗ[σ₁₂] M₂) :=
  { e.toLinearEquiv.submoduleMap p with norm_map' x := e.norm_map' x }

end submoduleMap

end LinearIsometryEquiv

/-- Two linear isometries are equal if they are equal on basis vectors. -/
/-
**Module.Basis.ext_linearIsometry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.ext_linearIsometry {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E -
>ₛₗᵢ[σ₁₂] E₂} (h : forall i, f₁ (b i) = f₂ (b i)) : f₁ = f₂
参数：b : Basis ι R E；h : forall i, f₁ (b i) = f₂ (b i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.toLinearMap_injective`：∀ {R : Type u_1} {R₂ : Type u_2} {
E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ 
: R →+* R₂} [inst_2 : Semi…
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂

--- 原说明 ---
Two linear isometries are equal if they are equal on basis vectors.
-/
theorem Module.Basis.ext_linearIsometry {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E →ₛₗᵢ[σ₁₂] E₂}
    (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  LinearIsometry.toLinearMap_injective <| b.ext h

/-- Two linear isometric equivalences are equal if they are equal on basis vectors. -/
/-
**Module.Basis.ext_linearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.ext_linearIsometryEquiv {ι : Type*} (b : Basis ι R E) {f₁ f₂ 
: E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall i, f₁ (b i) = f₂ (b i)) : f₁ = f₂
参数：b : Basis ι R E；h : forall i, f₁ (b i) = f₂ (b i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.toLinearEquiv_injective`：∀ {R : Type u_1} {R₂ : Type
 u_2} {E : Type u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂] 
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `Module.Basis.ext'`：ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = 
f₂ (b i)) : f₁ = f₂

--- 原说明 ---
Two linear isometric equivalences are equal if they are equal on basis vectors.
-/
theorem Module.Basis.ext_linearIsometryEquiv {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂}
    (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  LinearIsometryEquiv.toLinearEquiv_injective <| b.ext' h

/-- Reinterpret a `LinearIsometry` as a `LinearIsometryEquiv` to the range. -/
@[simps! apply_coe]
/-
**LinearIsometry.equivRange** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearIsometry.equivRange {R S : Type*} [Semiring R] [Ring S] [Module S E]
 [Module R F] {σ₁₂ : R ->+* S} {σ₂₁ : S ->+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHo
mInvPair σ₂₁ σ₁₂] (f : F ->ₛₗᵢ[σ₁₂] E) : F ≃ₛₗᵢ[σ₁₂] (LinearMap.range f.toLinear
Map)
参数：f : F ->ₛₗᵢ[σ₁₂] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `LinearIsometry` as a `LinearIsometryEquiv` to the range.
-/
noncomputable def LinearIsometry.equivRange {R S : Type*} [Semiring R] [Ring S] [Module S E]
    [Module R F] {σ₁₂ : R →+* S} {σ₂₁ : S →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (f : F →ₛₗᵢ[σ₁₂] E) : F ≃ₛₗᵢ[σ₁₂] (LinearMap.range f.toLinearMap) :=
  { f with toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap f.injective }

namespace MulOpposite
variable {R H : Type*} [Semiring R] [SeminormedAddCommGroup H] [Module R H]

/-
**MulOpposite.isometry_opLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：isometry_opLinearEquiv : Isometry (opLinearEquiv R (M
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isometry_opLinearEquiv : Isometry (opLinearEquiv R (M := H)) := fun _ _ => rfl

variable (R H) in
/-- The linear isometry equivalence version of the function `op`. -/
@[simps!]
/-
**MulOpposite.opLinearIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：opLinearIsometryEquiv : H ≃ₗᵢ[R] Hᵐᵒᵖ where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear isometry equivalence version of the function `op`.
-/
def opLinearIsometryEquiv : H ≃ₗᵢ[R] Hᵐᵒᵖ where
  toLinearEquiv := opLinearEquiv R
  norm_map' _ := rfl

@[simp]
/-
**MulOpposite.toLinearEquiv_opLinearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Mul
Opposite`。
形式化陈述：toLinearEquiv_opLinearIsometryEquiv : (opLinearIsometryEquiv R H).toLinear
Equiv = opLinearEquiv R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_opLinearIsometryEquiv :
    (opLinearIsometryEquiv R H).toLinearEquiv = opLinearEquiv R := rfl

@[simp]
/-
**MulOpposite.toContinuousLinearEquiv_opLinearIsometryEquiv** 是 Mathlib 中的一个定理，位
于命名空间 `MulOpposite`。
形式化陈述：toContinuousLinearEquiv_opLinearIsometryEquiv : (opLinearIsometryEquiv R H
).toContinuousLinearEquiv = opContinuousLinearEquiv R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearEquiv_opLinearIsometryEquiv :
    (opLinearIsometryEquiv R H).toContinuousLinearEquiv = opContinuousLinearEquiv R := rfl

end MulOpposite

