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

We also prove basic lemmas and provide convenience constructors.  The choice of these lemmas and
constructors is closely modelled on those for the `LinearIsometry` and `AffineMap` theories.

Since many elementary properties don't require `‖x‖ = 0 → x = 0` we initially set up the theory for
`SeminormedAddCommGroup` and specialize to `NormedAddCommGroup` only when needed.

## Notation

We introduce the notation `P →ᵃⁱ[𝕜] P₂` for `AffineIsometry 𝕜 P P₂`, and `P ≃ᵃⁱ[𝕜] P₂` for
`AffineIsometryEquiv 𝕜 P P₂`.  In contrast with the notation `→ₗᵢ` for linear isometries, `≃ᵢ`
for isometric equivalences, etc., the "i" here is a superscript.  This is for aesthetic reasons to
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

/-- A `𝕜`-affine isometric embedding of one normed add-torsor over a normed `𝕜`-space into
another, denoted as `f : P →ᵃⁱ[𝕜] P₂`. -/
/-
**AffineIsometry** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_1) →   {V : Type u_2} →     {V₂ : Type u_5} →       (P : Type 
u_10) →         (P₂ : Type u_11) →           [inst : NormedField 𝕜] →           
  [inst_1 : SeminormedAddCommGroup V] →               [NormedSpace 𝕜 V] →       
          [inst_3 : PseudoMetricSpace P] →                   [NormedAddTorsor V 
P] →                     [inst_5 : SeminormedAddCommGroup V₂] →                 
      [NormedSpace 𝕜 V₂] →                         [inst : PseudoMetricSpace P₂]
 →                           [NormedAddTorsor V₂ P₂] → Type (max (max (max u_10 
u_11) u_2) u_5)
参数：max (max u_10 u_11) u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `𝕜`-affine isometric embedding of one normed add-torsor over a normed `𝕜`-spac
e into
another, denoted as `f : P →ᵃⁱ[𝕜] P₂`.
-/
structure AffineIsometry extends P →ᵃ[𝕜] P₂ where
  norm_map : ∀ x : V, ‖linear x‖ = ‖x‖

variable {𝕜 P P₂}

@[inherit_doc]
notation:25 -- `→ᵃᵢ` would be more consistent with the linear isometry notation, but it is uglier
P " →ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometry 𝕜 P P₂

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂)

/-- The underlying linear map of an affine isometry is in fact a linear isometry. -/
/-
**AffineIsometry.linearIsometry** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometry`。
形式化陈述：{𝕜 : Type u_1} →   {V : Type u_2} →     {V₂ : Type u_5} →       {P : Type 
u_10} →         {P₂ : Type u_11} →           [inst : NormedField 𝕜] →           
  [inst_1 : SeminormedAddCommGroup V] →               [inst_2 : NormedSpace 𝕜 V]
 →                 [inst_3 : PseudoMetricSpace P] →                   [inst_4 : 
NormedAddTorsor V P] →                     [inst_5 : SeminormedAddCommGroup V₂] 
→                       [inst_6 : NormedSpace 𝕜 V₂] →                         [i
nst_7 : PseudoMetricSpace P₂] → [inst_8 : NormedAddTorsor V₂ P₂] → (P →ᵃⁱ[𝕜] P₂)
 → V →ₗᵢ[𝕜] V₂
参数：P →ᵃⁱ[𝕜] P₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.norm_map`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…

--- 原说明 ---
The underlying linear map of an affine isometry is in fact a linear isometry.
-/
protected def linearIsometry : V →ₗᵢ[𝕜] V₂ :=
  { f.linear with norm_map' := f.norm_map }

@[simp]
/-
**AffineIsometry.linear_eq_linearIsometry** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsome
try`。
形式化陈述：linear_eq_linearIsometry : f.linear = f.linearIsometry.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem linear_eq_linearIsometry : f.linear = f.linearIsometry.toLinearMap := by
  ext
  rfl
/-
**AffineIsometry.** 是 Mathlib 中的一个实例，位于命名空间 `AffineIsometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (P →ᵃⁱ[𝕜] P₂) P P₂ where
  coe f := f.toFun
  coe_injective f g := by cases f; cases g; simp

@[simp]
/-
**AffineIsometry.coe_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：coe_toAffineMap : ⇑f.toAffineMap = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineMap : ⇑f.toAffineMap = f := by
  rfl
/-
**AffineIsometry.toAffineMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry
`。
形式化陈述：toAffineMap_injective : Injective (toAffineMap : (P ->ᵃⁱ[𝕜] P₂) -> P ->ᵃ[𝕜
] P₂)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineMap_injective : Injective (toAffineMap : (P →ᵃⁱ[𝕜] P₂) → P →ᵃ[𝕜] P₂) := by
  rintro ⟨f, _⟩ ⟨g, _⟩ rfl
  rfl
/-
**AffineIsometry.coeFn_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：coeFn_injective : @Injective (P ->ᵃⁱ[𝕜] P₂) (P -> P₂) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AffineMap.coeFn_injective`：coeFn_injective : @Function.Injective (P1 ->ᵃ
[k] P2) (P1 -> P2) (⇑)
· 使用定理 `AffineIsometry.toAffineMap_injective`：toAffineMap_injective : Injective 
(toAffineMap : (P ->ᵃⁱ[𝕜] P₂) -> P ->ᵃ[𝕜] P₂)
-/
theorem coeFn_injective : @Injective (P →ᵃⁱ[𝕜] P₂) (P → P₂) (↑) :=
  AffineMap.coeFn_injective.comp toAffineMap_injective

@[ext]
/-
**AffineIsometry.ext** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：ext {f g : P ->ᵃⁱ[𝕜] P₂} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.coeFn_injective`：coeFn_injective : @Injective (P ->ᵃⁱ[𝕜] 
P₂) (P -> P₂) (↑)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {f g : P →ᵃⁱ[𝕜] P₂} (h : ∀ x, f x = g x) : f = g :=
  coeFn_injective <| funext h

end AffineIsometry

namespace LinearIsometry

variable (f : V →ₗᵢ[𝕜] V₂)

/-- Reinterpret a linear isometry as an affine isometry. -/
/-
**LinearIsometry.toAffineIsometry** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry`。
形式化陈述：toAffineIsometry : V ->ᵃⁱ[𝕜] V₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a linear isometry as an affine isometry.
-/
def toAffineIsometry : V →ᵃⁱ[𝕜] V₂ :=
  { f.toLinearMap.toAffineMap with norm_map := f.norm_map }

@[simp]
/-
**LinearIsometry.coe_toAffineIsometry** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`
。
形式化陈述：coe_toAffineIsometry : ⇑(f.toAffineIsometry : V ->ᵃⁱ[𝕜] V₂) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineIsometry : ⇑(f.toAffineIsometry : V →ᵃⁱ[𝕜] V₂) = f :=
  rfl

@[simp]
/-
**LinearIsometry.toAffineIsometry_linearIsometry** 是 Mathlib 中的一个定理，位于命名空间 `Line
arIsometry`。
形式化陈述：toAffineIsometry_linearIsometry : f.toAffineIsometry.linearIsometry = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.ext`：ext {f g : E ->ₛₗᵢ[σ₁₂] E₂} (h : forall x, f x = g x
) : f = g
-/
theorem toAffineIsometry_linearIsometry : f.toAffineIsometry.linearIsometry = f := by
  ext
  rfl

-- somewhat arbitrary choice of simp direction
@[simp]
/-
**LinearIsometry.toAffineIsometry_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearI
sometry`。
形式化陈述：toAffineIsometry_toAffineMap : f.toAffineIsometry.toAffineMap = f.toLinear
Map.toAffineMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineIsometry_toAffineMap : f.toAffineIsometry.toAffineMap = f.toLinearMap.toAffineMap :=
  rfl

end LinearIsometry

namespace AffineIsometry

variable (f : P →ᵃⁱ[𝕜] P₂) (f₁ : P₁' →ᵃⁱ[𝕜] P₂)

@[simp]
/-
**AffineIsometry.map_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linearIsometry v +ᵥ f p
参数：p : P；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
-/
theorem map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linearIsometry v +ᵥ f p :=
  f.toAffineMap.map_vadd p v

@[simp]
/-
**AffineIsometry.map_vsub** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：map_vsub (p1 p2 : P) : f.linearIsometry (p1 -ᵥ p2) = f p1 -ᵥ f p2
参数：p1 p2 : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
-/
theorem map_vsub (p1 p2 : P) : f.linearIsometry (p1 -ᵥ p2) = f p1 -ᵥ f p2 :=
  f.toAffineMap.linearMap_vsub p1 p2

@[simp]
/-
**AffineIsometry.dist_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：dist_map (x y : P) : dist (f x) (f y) = dist x y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineIsometry.map_vsub`：map_vsub (p1 p2 : P) : f.linearIsometry (p1 -ᵥ 
p2) = f p1 -ᵥ f p2
· 使用定理 `LinearIsometry.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem dist_map (x y : P) : dist (f x) (f y) = dist x y := by
  rw [dist_eq_norm_vsub V₂, dist_eq_norm_vsub V, ← map_vsub, f.linearIsometry.norm_map]

@[simp]
/-
**AffineIsometry.nndist_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：nndist_map (x y : P) : nndist (f x) (f y) = nndist x y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_dist`：nndist_dist (x y : α) : nndist x y = Real.toNNReal (dist x 
y)
· 使用定理 `AffineIsometry.dist_map`：dist_map (x y : P) : dist (f x) (f y) = dist x 
y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nndist_map (x y : P) : nndist (f x) (f y) = nndist x y := by simp [nndist_dist]

@[simp]
/-
**AffineIsometry.edist_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：edist_map (x y : P) : edist (f x) (f y) = edist x y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `AffineIsometry.dist_map`：dist_map (x y : P) : dist (f x) (f y) = dist x 
y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edist_map (x y : P) : edist (f x) (f y) = edist x y := by simp [edist_dist]
/-
**AffineIsometry.isometry** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (f : P →ᵃⁱ[𝕜] P₂), Isometry ⇑
f
参数：f : P →ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.edist_map`：edist_map (x y : P) : edist (f x) (f y) = edis
t x y
-/
protected theorem isometry : Isometry f :=
  f.edist_map
/-
**AffineIsometry.injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u_5} {P₁' : Type u_9} {P₂ : T
ype u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V₁'] [inst_2
 : NormedSpace 𝕜 V₁'] [inst_3 : MetricSpace P₁']   [inst_4 : NormedAddTorsor V₁'
 P₁'] [inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7
 : PseudoMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (f₁ : P₁' →ᵃⁱ[𝕜] P₂), 
Function.Injective ⇑f₁
参数：f₁ : P₁' →ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
protected theorem injective : Injective f₁ :=
  f₁.isometry.injective

@[simp]
/-
**AffineIsometry.map_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：map_eq_iff {x y : P₁'} : f₁ x = f₁ y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
-/
theorem map_eq_iff {x y : P₁'} : f₁ x = f₁ y ↔ x = y :=
  f₁.injective.eq_iff
/-
**AffineIsometry.map_ne** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：map_ne {x y : P₁'} (h : x != y) : f₁ x != f₁ y
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…
-/
theorem map_ne {x y : P₁'} (h : x ≠ y) : f₁ x ≠ f₁ y :=
  f₁.injective.ne h
/-
**AffineIsometry.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (f : P →ᵃⁱ[𝕜] P₂), LipschitzW
ith 1 ⇑f
参数：f : P →ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
protected theorem lipschitz : LipschitzWith 1 f :=
  f.isometry.lipschitz
/-
**AffineIsometry.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (f : P →ᵃⁱ[𝕜] P₂), Antilipsch
itzWith 1 ⇑f
参数：f : P →ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
protected theorem antilipschitz : AntilipschitzWith 1 f :=
  f.isometry.antilipschitz

@[continuity]
/-
**AffineIsometry.continuous** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (f : P →ᵃⁱ[𝕜] P₂), Continuous
 ⇑f
参数：f : P →ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
protected theorem continuous : Continuous f :=
  f.isometry.continuous
/-
**AffineIsometry.ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：ediam_image (s : Set P) : ediam (f '' s) = ediam s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
theorem ediam_image (s : Set P) : ediam (f '' s) = ediam s :=
  f.isometry.ediam_image s
/-
**AffineIsometry.ediam_range** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：ediam_range : ediam (range f) = ediam (univ : Set P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_range`：ediam_range (hf : Isometry f) : Metric.ediam (rang
e f) = Metric.ediam (univ : Set α)
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
theorem ediam_range : ediam (range f) = ediam (univ : Set P) :=
  f.isometry.ediam_range
/-
**AffineIsometry.diam_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：diam_image (s : Set P) : Metric.diam (f '' s) = Metric.diam s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
theorem diam_image (s : Set P) : Metric.diam (f '' s) = Metric.diam s :=
  f.isometry.diam_image s
/-
**AffineIsometry.diam_range** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：diam_range : Metric.diam (range f) = Metric.diam (univ : Set P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_range`：diam_range (hf : Isometry f) : Metric.diam (range f
) = Metric.diam (univ : Set α)
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set P) :=
  f.isometry.diam_range

/-- Interpret an affine isometry as a continuous affine map. -/
/-
**AffineIsometry.toContinuousAffineMap** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometry
`。
形式化陈述：toContinuousAffineMap : P ->ᴬ[𝕜] P₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.continuous`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_
5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminorme
dAddCommGroup V…

--- 原说明 ---
Interpret an affine isometry as a continuous affine map.
-/
def toContinuousAffineMap : P →ᴬ[𝕜] P₂ := { f with cont := f.continuous }
/-
**AffineIsometry.toContinuousAffineMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neIsometry`。
形式化陈述：toContinuousAffineMap_injective : Function.Injective (toContinuousAffineMa
p : _ -> P ->ᴬ[𝕜] P₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.coeFn_injective`：coeFn_injective : @Injective (P ->ᵃⁱ[𝕜] 
P₂) (P -> P₂) (↑)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toContinuousAffineMap_injective :
    Function.Injective (toContinuousAffineMap : _ → P →ᴬ[𝕜] P₂) := fun x _ h =>
  coeFn_injective (congr_arg _ h : ⇑x.toContinuousAffineMap = _)

@[simp]
/-
**AffineIsometry.toContinuousAffineMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsom
etry`。
形式化陈述：toContinuousAffineMap_inj {f g : P ->ᵃⁱ[𝕜] P₂} : f.toContinuousAffineMap =
 g.toContinuousAffineMap ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AffineIsometry.toContinuousAffineMap_injective`：toContinuousAffineMap_in
jective : Function.Injective (toContinuousAffineMap : _ -> P ->ᴬ[𝕜] P₂)
-/
theorem toContinuousAffineMap_inj {f g : P →ᵃⁱ[𝕜] P₂} :
    f.toContinuousAffineMap = g.toContinuousAffineMap ↔ f = g :=
  toContinuousAffineMap_injective.eq_iff

@[simp]
/-
**AffineIsometry.coe_toContinuousAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsom
etry`。
形式化陈述：coe_toContinuousAffineMap : ⇑f.toContinuousAffineMap = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousAffineMap : ⇑f.toContinuousAffineMap = f := rfl

@[simp]
/-
**AffineIsometry.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α -> P} : Contin
uous (f ∘ g) ↔ Continuous g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp_continuous_iff`：comp_continuous_iff {γ} [TopologicalSpace 
γ] (hf : Isometry f) {g : γ -> α} : Continuous (f ∘ g) ↔ Continuous g
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] {g : α → P} :
    Continuous (f ∘ g) ↔ Continuous g :=
  f.isometry.comp_continuous_iff

/-- The identity affine isometry. -/
/-
**AffineIsometry.id** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometry`。
形式化陈述：id : P ->ᵃⁱ[𝕜] P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity affine isometry.
-/
def id : P →ᵃⁱ[𝕜] P :=
  ⟨AffineMap.id 𝕜 P, fun _ => rfl⟩

@[simp, norm_cast]
/-
**AffineIsometry.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：coe_id : ⇑(id : P ->ᵃⁱ[𝕜] P) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(id : P →ᵃⁱ[𝕜] P) = _root_.id :=
  rfl

@[simp]
/-
**AffineIsometry.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：id_apply (x : P) : (AffineIsometry.id : P ->ᵃⁱ[𝕜] P) x = x
参数：x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : P) : (AffineIsometry.id : P →ᵃⁱ[𝕜] P) x = x :=
  rfl

@[simp]
/-
**AffineIsometry.id_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：id_toAffineMap : (id.toAffineMap : P ->ᵃ[𝕜] P) = AffineMap.id 𝕜 P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_toAffineMap : (id.toAffineMap : P →ᵃ[𝕜] P) = AffineMap.id 𝕜 P :=
  rfl

@[simp]
/-
**AffineIsometry.toContinuousAffineMap_id** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsome
try`。
形式化陈述：toContinuousAffineMap_id : id.toContinuousAffineMap = ContinuousAffineMap.
id 𝕜 P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousAffineMap_id : id.toContinuousAffineMap = ContinuousAffineMap.id 𝕜 P :=
  rfl
/-
**AffineIsometry.** 是 Mathlib 中的一个实例，位于命名空间 `AffineIsometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (P →ᵃⁱ[𝕜] P) :=
  ⟨id⟩

/-- Composition of affine isometries. -/
/-
**AffineIsometry.comp** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometry`。
形式化陈述：comp (g : P₂ ->ᵃⁱ[𝕜] P₃) (f : P ->ᵃⁱ[𝕜] P₂) : P ->ᵃⁱ[𝕜] P₃
参数：g : P₂ ->ᵃⁱ[𝕜] P₃；f : P ->ᵃⁱ[𝕜] P₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of affine isometries.
-/
def comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : P →ᵃⁱ[𝕜] P₃ :=
  ⟨g.toAffineMap.comp f.toAffineMap, fun _ => (g.norm_map _).trans (f.norm_map _)⟩

@[simp]
/-
**AffineIsometry.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：coe_comp (g : P₂ ->ᵃⁱ[𝕜] P₃) (f : P ->ᵃⁱ[𝕜] P₂) : ⇑(g.comp f) = g ∘ f
参数：g : P₂ ->ᵃⁱ[𝕜] P₃；f : P ->ᵃⁱ[𝕜] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
/-
**AffineIsometry.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：id_comp : (id : P₂ ->ᵃⁱ[𝕜] P₂).comp f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.ext`：ext {f g : P ->ᵃⁱ[𝕜] P₂} (h : forall x, f x = g x) :
 f = g
-/
theorem id_comp : (id : P₂ →ᵃⁱ[𝕜] P₂).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**AffineIsometry.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：comp_id : f.comp id = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.ext`：ext {f g : P ->ᵃⁱ[𝕜] P₂} (h : forall x, f x = g x) :
 f = g
-/
theorem comp_id : f.comp id = f :=
  ext fun _ => rfl
/-
**AffineIsometry.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：comp_assoc (f : P₃ ->ᵃⁱ[𝕜] P₄) (g : P₂ ->ᵃⁱ[𝕜] P₃) (h : P ->ᵃⁱ[𝕜] P₂) : (f
.comp g).comp h = f.comp (g.comp h)
参数：f : P₃ ->ᵃⁱ[𝕜] P₄；g : P₂ ->ᵃⁱ[𝕜] P₃；h : P ->ᵃⁱ[𝕜] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : P₃ →ᵃⁱ[𝕜] P₄) (g : P₂ →ᵃⁱ[𝕜] P₃) (h : P →ᵃⁱ[𝕜] P₂) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
/-
**AffineIsometry.** 是 Mathlib 中的一个实例，位于命名空间 `AffineIsometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (P →ᵃⁱ[𝕜] P) where
  one := id
  mul := comp
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

@[simp]
/-
**AffineIsometry.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：coe_one : ⇑(1 : P ->ᵃⁱ[𝕜] P) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : P →ᵃⁱ[𝕜] P) = _root_.id :=
  rfl

@[simp]
/-
**AffineIsometry.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry`。
形式化陈述：coe_mul (f g : P ->ᵃⁱ[𝕜] P) : ⇑(f * g) = f ∘ g
参数：f g : P ->ᵃⁱ[𝕜] P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : P →ᵃⁱ[𝕜] P) : ⇑(f * g) = f ∘ g :=
  rfl

end AffineIsometry

namespace AffineSubspace

/-- `AffineSubspace.subtype` as an `AffineIsometry`. -/
/-
**AffineSubspace.subtype** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：{k : Type u_1} →   {V : Type u_2} →     {P : Type u_3} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] →             [inst_3 : AddTorsor V P] → (s : AffineSubspace k P) → [inst_4 : 
Nonempty ↥s] → ↥s →ᵃ[k] P
参数：s : AffineSubspace k P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AffineSubspace.subtype` as an `AffineIsometry`.
-/
def subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] : s →ᵃⁱ[𝕜] P :=
  { s.subtype with norm_map := s.direction.subtypeₗᵢ.norm_map }
/-
**AffineSubspace.subtype** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：{k : Type u_1} →   {V : Type u_2} →     {P : Type u_3} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] →             [inst_3 : AddTorsor V P] → (s : AffineSubspace k P) → [inst_4 : 
Nonempty ↥s] → ↥s →ᵃ[k] P
参数：s : AffineSubspace k P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeₐᵢ_linear (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.linear = s.direction.subtype :=
  rfl

@[simp]
/-
**AffineSubspace.subtype** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：{k : Type u_1} →   {V : Type u_2} →     {P : Type u_3} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] →             [inst_3 : AddTorsor V P] → (s : AffineSubspace k P) → [inst_4 : 
Nonempty ↥s] → ↥s →ᵃ[k] P
参数：s : AffineSubspace k P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeₐᵢ_linearIsometry (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.linearIsometry = s.direction.subtypeₗᵢ :=
  rfl

@[simp]
/-
**AffineSubspace.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：coe_subtype (s : AffineSubspace k P) [Nonempty s] : (s.subtype : s -> P) =
 ((↑) : s -> P)
参数：s : AffineSubspace k P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] : ⇑s.subtypeₐᵢ = s.subtype :=
  rfl

@[simp]
/-
**AffineSubspace.subtype** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：{k : Type u_1} →   {V : Type u_2} →     {P : Type u_3} →       [inst : Rin
g k] →         [inst_1 : AddCommGroup V] →           [inst_2 : _root_.Module k V
] →             [inst_3 : AddTorsor V P] → (s : AffineSubspace k P) → [inst_4 : 
Nonempty ↥s] → ↥s →ᵃ[k] P
参数：s : AffineSubspace k P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeₐᵢ_toAffineMap (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.toAffineMap = s.subtype :=
  rfl

@[simp]
/-
**AffineSubspace.toContinuousAffineMap_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousAffineMap_subtypeₐᵢ (s : AffineSubspace 𝕜 P) [Nonempty s] :
    s.subtypeₐᵢ.toContinuousAffineMap = s.subtypeA :=
  rfl

end AffineSubspace

variable (𝕜 P P₂)

/-- An affine isometric equivalence between two normed vector spaces,
denoted `f : P ≃ᵃⁱ[𝕜] P₂`. -/
/-
**AffineIsometryEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_1) →   {V : Type u_2} →     {V₂ : Type u_5} →       (P : Type 
u_10) →         (P₂ : Type u_11) →           [inst : NormedField 𝕜] →           
  [inst_1 : SeminormedAddCommGroup V] →               [NormedSpace 𝕜 V] →       
          [inst_3 : PseudoMetricSpace P] →                   [NormedAddTorsor V 
P] →                     [inst_5 : SeminormedAddCommGroup V₂] →                 
      [NormedSpace 𝕜 V₂] →                         [inst : PseudoMetricSpace P₂]
 →                           [NormedAddTorsor V₂ P₂] → Type (max (max (max u_10 
u_11) u_2) u_5)
参数：max (max u_10 u_11) u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine isometric equivalence between two normed vector spaces,
denoted `f : P ≃ᵃⁱ[𝕜] P₂`.
-/
structure AffineIsometryEquiv extends P ≃ᵃ[𝕜] P₂ where
  norm_map : ∀ x, ‖linear x‖ = ‖x‖

variable {𝕜 P P₂}

-- `≃ᵃᵢ` would be more consistent with the linear isometry equiv notation, but it is uglier
@[inherit_doc] notation:25 P " ≃ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometryEquiv 𝕜 P P₂

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

/-- The underlying linear equiv of an affine isometry equiv is in fact a linear isometry equiv. -/
/-
**AffineIsometryEquiv.linearIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsome
tryEquiv`。
形式化陈述：{𝕜 : Type u_1} →   {V : Type u_2} →     {V₂ : Type u_5} →       {P : Type 
u_10} →         {P₂ : Type u_11} →           [inst : NormedField 𝕜] →           
  [inst_1 : SeminormedAddCommGroup V] →               [inst_2 : NormedSpace 𝕜 V]
 →                 [inst_3 : PseudoMetricSpace P] →                   [inst_4 : 
NormedAddTorsor V P] →                     [inst_5 : SeminormedAddCommGroup V₂] 
→                       [inst_6 : NormedSpace 𝕜 V₂] →                         [i
nst_7 : PseudoMetricSpace P₂] → [inst_8 : NormedAddTorsor V₂ P₂] → (P ≃ᵃⁱ[𝕜] P₂)
 → V ≃ₗᵢ[𝕜] V₂
参数：P ≃ᵃⁱ[𝕜] P₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.norm_map`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…

--- 原说明 ---
The underlying linear equiv of an affine isometry equiv is in fact a linear isom
etry equiv.
-/
protected def linearIsometryEquiv : V ≃ₗᵢ[𝕜] V₂ :=
  { e.linear with norm_map' := e.norm_map }

@[simp]
/-
**AffineIsometryEquiv.linear_eq_linear_isometry** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eIsometryEquiv`。
形式化陈述：linear_eq_linear_isometry : e.linear = e.linearIsometryEquiv.toLinearEquiv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
-/
theorem linear_eq_linear_isometry : e.linear = e.linearIsometryEquiv.toLinearEquiv := by
  ext
  rfl
/-
**AffineIsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AffineIsometryEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**AffineIsometryEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：coe_mk (e : P ≃ᵃ[𝕜] P₂) (he : forall x, ‖e.linear x‖ = ‖x‖) : ⇑(mk e he) =
 e
参数：e : P ≃ᵃ[𝕜] P₂；he : forall x, ‖e.linear x‖ = ‖x‖。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e : P ≃ᵃ[𝕜] P₂) (he : ∀ x, ‖e.linear x‖ = ‖x‖) : ⇑(mk e he) = e :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.coe_toAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometr
yEquiv`。
形式化陈述：coe_toAffineEquiv (e : P ≃ᵃⁱ[𝕜] P₂) : ⇑e.toAffineEquiv = e
参数：e : P ≃ᵃⁱ[𝕜] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineEquiv (e : P ≃ᵃⁱ[𝕜] P₂) : ⇑e.toAffineEquiv = e :=
  rfl
/-
**AffineIsometryEquiv.toAffineEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineI
sometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂], Function.Injective AffineIso
metryEquiv.toAffineEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineEquiv_injective : Injective (toAffineEquiv : (P ≃ᵃⁱ[𝕜] P₂) → P ≃ᵃ[𝕜] P₂)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[ext]
/-
**AffineIsometryEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e' x) : e = e'
参数：h : forall x, e x = e' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.toAffineEquiv_injective`：∀ {𝕜 : Type u_1} {V : Type 
u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [
inst_1 : SeminormedAddCommGroup V…
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
-/
theorem ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  toAffineEquiv_injective <| AffineEquiv.ext h
/-
**AffineIsometryEquiv.coeFn_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryE
quiv`。
形式化陈述：coeFn_injective : @Injective (P ≃ᵃⁱ[𝕜] P₂) (P -> P₂) (fun f => f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coeFn_injective : @Injective (P ≃ᵃⁱ[𝕜] P₂) (P → P₂) (fun f => f) :=
  DFunLike.coe_injective

/-- Reinterpret an `AffineIsometryEquiv` as an `AffineIsometry`. -/
/-
**AffineIsometryEquiv.toAffineIsometry** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometry
Equiv`。
形式化陈述：toAffineIsometry : P ->ᵃⁱ[𝕜] P₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.norm_map`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…

--- 原说明 ---
Reinterpret an `AffineIsometryEquiv` as an `AffineIsometry`.
-/
def toAffineIsometry : P →ᵃⁱ[𝕜] P₂ :=
  ⟨e.1.toAffineMap, e.2⟩

@[simp]
/-
**AffineIsometryEquiv.coe_toAffineIsometry** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsom
etryEquiv`。
形式化陈述：coe_toAffineIsometry : ⇑e.toAffineIsometry = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineIsometry : ⇑e.toAffineIsometry = e :=
  rfl

/-- Construct an affine isometry equivalence by verifying the relation between the map and its
linear part at one base point. Namely, this function takes a map `e : P₁ → P₂`, a linear isometry
equivalence `e' : V₁ ≃ᵢₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
/-
**AffineIsometryEquiv.mk'** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：mk' (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : forall p' : P₁, e p' 
= e' (p' -ᵥ p) +ᵥ e p) : P₁ ≃ᵃⁱ[𝕜] P₂
参数：e : P₁ -> P₂；e' : V₁ ≃ₗᵢ[𝕜] V₂；p : P₁；h : forall p' : P₁, e p' = e' (p' -ᵥ p)
 +ᵥ e p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an affine isometry equivalence by verifying the relation between the m
ap and its
linear part at one base point. Namely, this function takes a map `e : P₁ → P₂`, 
a linear isometry
equivalence `e' : V₁ ≃ᵢₗ[k] V₂`, and a point `p` such that for any other point `
p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`.
-/
def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  { AffineEquiv.mk' e e'.toLinearEquiv p h with norm_map := e'.norm_map }

@[simp]
/-
**AffineIsometryEquiv.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：coe_mk' (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) : ⇑(mk' e e' p h) = e
参数：e : P₁ -> P₂；e' : V₁ ≃ₗᵢ[𝕜] V₂；p h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) : ⇑(mk' e e' p h) = e :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.linearIsometryEquiv_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AffineI
sometryEquiv`。
形式化陈述：linearIsometryEquiv_mk' (e : P₁ -> P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) : (mk' e 
e' p h).linearIsometryEquiv = e'
参数：e : P₁ -> P₂；e' : V₁ ≃ₗᵢ[𝕜] V₂；p h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
-/
theorem linearIsometryEquiv_mk' (e : P₁ → P₂) (e' : V₁ ≃ₗᵢ[𝕜] V₂) (p h) :
    (mk' e e' p h).linearIsometryEquiv = e' := by
  ext
  rfl

end AffineIsometryEquiv

namespace LinearIsometryEquiv

variable (e : V ≃ₗᵢ[𝕜] V₂)

/-- Reinterpret a linear isometry equiv as an affine isometry equiv. -/
/-
**LinearIsometryEquiv.toAffineIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearIso
metryEquiv`。
形式化陈述：toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a linear isometry equiv as an affine isometry equiv.
-/
def toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂ :=
  { e.toLinearEquiv.toAffineEquiv with norm_map := e.norm_map }

@[simp]
/-
**LinearIsometryEquiv.coe_toAffineIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rIsometryEquiv`。
形式化陈述：coe_toAffineIsometryEquiv : ⇑(e.toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineIsometryEquiv : ⇑(e.toAffineIsometryEquiv : V ≃ᵃⁱ[𝕜] V₂) = e := by
  rfl

@[simp]
/-
**LinearIsometryEquiv.toAffineIsometryEquiv_linearIsometryEquiv** 是 Mathlib 中的一个
定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：toAffineIsometryEquiv_linearIsometryEquiv : e.toAffineIsometryEquiv.linear
IsometryEquiv = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
-/
theorem toAffineIsometryEquiv_linearIsometryEquiv :
    e.toAffineIsometryEquiv.linearIsometryEquiv = e := by
  ext
  rfl

-- somewhat arbitrary choice of simp direction
@[simp]
/-
**LinearIsometryEquiv.toAffineIsometryEquiv_toAffineEquiv** 是 Mathlib 中的一个定理，位于命
名空间 `LinearIsometryEquiv`。
形式化陈述：toAffineIsometryEquiv_toAffineEquiv : e.toAffineIsometryEquiv.toAffineEqui
v = e.toLinearEquiv.toAffineEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineIsometryEquiv_toAffineEquiv :
    e.toAffineIsometryEquiv.toAffineEquiv = e.toLinearEquiv.toAffineEquiv :=
  rfl

-- somewhat arbitrary choice of simp direction
@[simp]
/-
**LinearIsometryEquiv.toAffineIsometryEquiv_toAffineIsometry** 是 Mathlib 中的一个定理，
位于命名空间 `LinearIsometryEquiv`。
形式化陈述：toAffineIsometryEquiv_toAffineIsometry : e.toAffineIsometryEquiv.toAffineI
sometry = e.toLinearIsometry.toAffineIsometry
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineIsometryEquiv_toAffineIsometry :
    e.toAffineIsometryEquiv.toAffineIsometry = e.toLinearIsometry.toAffineIsometry :=
  rfl

end LinearIsometryEquiv

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

/-
**AffineIsometryEquiv.isometry** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂), Isometry ⇑
e
参数：e : P ≃ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5}
 {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedA
ddCommGroup V…
-/
protected theorem isometry : Isometry e :=
  e.toAffineIsometry.isometry

/-- Reinterpret an `AffineIsometryEquiv` as an `IsometryEquiv`. -/
/-
**AffineIsometryEquiv.toIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryE
quiv`。
形式化陈述：toIsometryEquiv : P ≃ᵢ P₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…

--- 原说明 ---
Reinterpret an `AffineIsometryEquiv` as an `IsometryEquiv`.
-/
def toIsometryEquiv : P ≃ᵢ P₂ :=
  ⟨e.toAffineEquiv.toEquiv, e.isometry⟩

@[simp]
/-
**AffineIsometryEquiv.coe_toIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsome
tryEquiv`。
形式化陈述：coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toIsometryEquiv : ⇑e.toIsometryEquiv = e :=
  rfl
/-
**AffineIsometryEquiv.range_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEqu
iv`。
形式化陈述：range_eq_univ (e : P ≃ᵃⁱ[𝕜] P₂) : Set.range e = Set.univ
参数：e : P ≃ᵃⁱ[𝕜] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineIsometryEquiv.coe_toIsometryEquiv`：coe_toIsometryEquiv : ⇑e.toIsom
etryEquiv = e
· 使用定理 `IsometryEquiv.range_eq_univ`：range_eq_univ (h : α ≃ᵢ β) : range h = univ
-/
theorem range_eq_univ (e : P ≃ᵃⁱ[𝕜] P₂) : Set.range e = Set.univ := by
  rw [← coe_toIsometryEquiv]
  exact IsometryEquiv.range_eq_univ _

/-- Reinterpret an `AffineIsometryEquiv` as a `Homeomorph`. -/
/-
**AffineIsometryEquiv.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEqui
v`。
形式化陈述：toHomeomorph : P ≃ₜ P₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an `AffineIsometryEquiv` as a `Homeomorph`.
-/
def toHomeomorph : P ≃ₜ P₂ :=
  e.toIsometryEquiv.toHomeomorph

@[simp]
/-
**AffineIsometryEquiv.coe_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry
Equiv`。
形式化陈述：coe_toHomeomorph : ⇑e.toHomeomorph = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomeomorph : ⇑e.toHomeomorph = e :=
  rfl
/-
**AffineIsometryEquiv.continuous** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`
。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂), Continuous
 ⇑e
参数：e : P ≃ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…
-/
protected theorem continuous : Continuous e :=
  e.isometry.continuous
/-
**AffineIsometryEquiv.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEqui
v`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂) {x : P}, Co
ntinuousAt (⇑e) x
参数：e : P ≃ᵃⁱ[𝕜] P₂；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `AffineIsometryEquiv.continuous`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Ty
pe u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semi
normedAddCommGroup V…
-/
protected theorem continuousAt {x} : ContinuousAt e x :=
  e.continuous.continuousAt
/-
**AffineIsometryEquiv.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEqui
v`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂) {s : Set P}
, ContinuousOn (⇑e) s
参数：e : P ≃ᵃⁱ[𝕜] P₂；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `AffineIsometryEquiv.continuous`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Ty
pe u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semi
normedAddCommGroup V…
-/
protected theorem continuousOn {s} : ContinuousOn e s :=
  e.continuous.continuousOn
/-
**AffineIsometryEquiv.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsomet
ryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂) {s : Set P}
 {x : P},   ContinuousWithinAt (⇑e) s x
参数：e : P ≃ᵃⁱ[𝕜] P₂；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `AffineIsometryEquiv.continuous`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Ty
pe u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semi
normedAddCommGroup V…
-/
protected theorem continuousWithinAt {s x} : ContinuousWithinAt e s x :=
  e.continuous.continuousWithinAt

/-- Interpret a `AffineIsometryEquiv` as a `ContinuousAffineEquiv`. -/
/-
**AffineIsometryEquiv.toContinuousAffineEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AffineI
sometryEquiv`。
形式化陈述：toContinuousAffineEquiv : P ≃ᴬ[𝕜] P₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `AffineIsometryEquiv` as a `ContinuousAffineEquiv`.
-/
def toContinuousAffineEquiv : P ≃ᴬ[𝕜] P₂ :=
  { e.toAffineEquiv, e.toHomeomorph with }
/-
**AffineIsometryEquiv.toContinuousAffineEquiv_injective** 是 Mathlib 中的一个定理，位于命名空
间 `AffineIsometryEquiv`。
形式化陈述：toContinuousAffineEquiv_injective : Function.Injective (toContinuousAffine
Equiv : _ -> P ≃ᴬ[𝕜] P₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.coeFn_injective`：coeFn_injective : @Injective (P ≃ᵃⁱ
[𝕜] P₂) (P -> P₂) (fun f => f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toContinuousAffineEquiv_injective :
    Function.Injective (toContinuousAffineEquiv : _ → P ≃ᴬ[𝕜] P₂) := fun x _ h =>
  coeFn_injective (congr_arg _ h : ⇑x.toContinuousAffineEquiv = _)

@[simp]
/-
**AffineIsometryEquiv.toContinuousAffineEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ineIsometryEquiv`。
形式化陈述：toContinuousAffineEquiv_inj {f g : P ≃ᵃⁱ[𝕜] P₂} : f.toContinuousAffineEqui
v = g.toContinuousAffineEquiv ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AffineIsometryEquiv.toContinuousAffineEquiv_injective`：toContinuousAffin
eEquiv_injective : Function.Injective (toContinuousAffineEquiv : _ -> P ≃ᴬ[𝕜] P₂
)
-/
theorem toContinuousAffineEquiv_inj {f g : P ≃ᵃⁱ[𝕜] P₂} :
    f.toContinuousAffineEquiv = g.toContinuousAffineEquiv ↔ f = g :=
  toContinuousAffineEquiv_injective.eq_iff

@[simp]
/-
**AffineIsometryEquiv.coe_toContinuousAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ineIsometryEquiv`。
形式化陈述：coe_toContinuousAffineEquiv : ⇑e.toContinuousAffineEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousAffineEquiv : ⇑e.toContinuousAffineEquiv = e :=
  rfl

/-- Reinterpret a `AffineIsometryEquiv` as a `ContinuousAffineEquiv`. -/
/-
**AffineIsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AffineIsometryEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `AffineIsometryEquiv` as a `ContinuousAffineEquiv`.
-/
instance : Coe (P ≃ᵃⁱ[𝕜] P₂) (P ≃ᴬ[𝕜] P₂) :=
  ⟨fun e => e.toContinuousAffineEquiv⟩

variable (𝕜 P)

/-- Identity map as an `AffineIsometryEquiv`. -/
/-
**AffineIsometryEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：refl : P ≃ᵃⁱ[𝕜] P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity map as an `AffineIsometryEquiv`.
-/
def refl : P ≃ᵃⁱ[𝕜] P :=
  ⟨AffineEquiv.refl 𝕜 P, fun _ => rfl⟩

variable {𝕜 P}
/-
**AffineIsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AffineIsometryEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (P ≃ᵃⁱ[𝕜] P) :=
  ⟨refl 𝕜 P⟩

@[simp]
/-
**AffineIsometryEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：coe_refl : ⇑(refl 𝕜 P) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ⇑(refl 𝕜 P) = id :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.toAffineEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsomet
ryEquiv`。
形式化陈述：toAffineEquiv_refl : (refl 𝕜 P).toAffineEquiv = AffineEquiv.refl 𝕜 P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineEquiv_refl : (refl 𝕜 P).toAffineEquiv = AffineEquiv.refl 𝕜 P :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.toContinuousAffineEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Af
fineIsometryEquiv`。
形式化陈述：toContinuousAffineEquiv_refl : (refl 𝕜 P).toContinuousAffineEquiv = .refl 
𝕜 P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousAffineEquiv_refl : (refl 𝕜 P).toContinuousAffineEquiv = .refl 𝕜 P := rfl

@[simp]
/-
**AffineIsometryEquiv.toIsometryEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsom
etryEquiv`。
形式化陈述：toIsometryEquiv_refl : (refl 𝕜 P).toIsometryEquiv = IsometryEquiv.refl P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIsometryEquiv_refl : (refl 𝕜 P).toIsometryEquiv = IsometryEquiv.refl P :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.toHomeomorph_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometr
yEquiv`。
形式化陈述：toHomeomorph_refl : (refl 𝕜 P).toHomeomorph = Homeomorph.refl P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorph_refl : (refl 𝕜 P).toHomeomorph = Homeomorph.refl P :=
  rfl

/-- The inverse `AffineIsometryEquiv`. -/
/-
**AffineIsometryEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：symm : P₂ ≃ᵃⁱ[𝕜] P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse `AffineIsometryEquiv`.
-/
def symm : P₂ ≃ᵃⁱ[𝕜] P :=
  { e.toAffineEquiv.symm with norm_map := e.linearIsometryEquiv.symm.norm_map }

@[simp]
/-
**AffineIsometryEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry
Equiv`。
形式化陈述：apply_symm_apply (x : P₂) : e (e.symm x) = x
参数：x : P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.apply_symm_apply`：apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂
) : e (e.symm p) = p
-/
theorem apply_symm_apply (x : P₂) : e (e.symm x) = x :=
  e.toAffineEquiv.apply_symm_apply x

@[simp]
/-
**AffineIsometryEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometry
Equiv`。
形式化陈述：symm_apply_apply (x : P) : e.symm (e x) = x
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.symm_apply_apply`：symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁
) : e.symm (e p) = p
-/
theorem symm_apply_apply (x : P) : e.symm (e x) = x :=
  e.toAffineEquiv.symm_apply_apply x

@[simp]
/-
**AffineIsometryEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：symm_symm : e.symm.symm = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm : e.symm.symm = e := rfl
/-
**AffineIsometryEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEqu
iv`。
形式化陈述：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.symm_apply_eq`：symm_apply_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e.s
ymm p₁ = p₂ ↔ p₁ = e p₂
-/
theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toAffineEquiv.symm_apply_eq
/-
**AffineIsometryEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEqu
iv`。
形式化陈述：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.eq_symm_apply`：eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : p₂ 
= e.symm p₁ ↔ e p₂ = p₁
-/
theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toAffineEquiv.eq_symm_apply
/-
**AffineIsometryEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEq
uiv`。
形式化陈述：symm_bijective : Bijective (AffineIsometryEquiv.symm : (P₂ ≃ᵃⁱ[𝕜] P) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `AffineIsometryEquiv.symm_symm`：symm_symm : e.symm.symm = e
-/
theorem symm_bijective : Bijective (AffineIsometryEquiv.symm : (P₂ ≃ᵃⁱ[𝕜] P) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**AffineIsometryEquiv.toAffineEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsomet
ryEquiv`。
形式化陈述：toAffineEquiv_symm : e.symm.toAffineEquiv = e.toAffineEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineEquiv_symm : e.symm.toAffineEquiv = e.toAffineEquiv.symm :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.coe_symm_toAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AffineIs
ometryEquiv`。
形式化陈述：coe_symm_toAffineEquiv : ⇑e.toAffineEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toAffineEquiv : ⇑e.toAffineEquiv.symm = e.symm :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.toContinuousAffineEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Af
fineIsometryEquiv`。
形式化陈述：toContinuousAffineEquiv_symm : e.symm.toContinuousAffineEquiv = e.toContin
uousAffineEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousAffineEquiv_symm :
    e.symm.toContinuousAffineEquiv = e.toContinuousAffineEquiv.symm := rfl

@[simp]
/-
**AffineIsometryEquiv.coe_symm_toContinuousAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间
 `AffineIsometryEquiv`。
形式化陈述：coe_symm_toContinuousAffineEquiv : ⇑e.toContinuousAffineEquiv.symm = e.sym
m
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toContinuousAffineEquiv : ⇑e.toContinuousAffineEquiv.symm = e.symm :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.toIsometryEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsom
etryEquiv`。
形式化陈述：toIsometryEquiv_symm : e.symm.toIsometryEquiv = e.toIsometryEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIsometryEquiv_symm : e.symm.toIsometryEquiv = e.toIsometryEquiv.symm :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.coe_symm_toIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Affine
IsometryEquiv`。
形式化陈述：coe_symm_toIsometryEquiv : ⇑e.toIsometryEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toIsometryEquiv : ⇑e.toIsometryEquiv.symm = e.symm :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.toHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometr
yEquiv`。
形式化陈述：toHomeomorph_symm : e.symm.toHomeomorph = e.toHomeomorph.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorph_symm : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.coe_symm_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `AffineIso
metryEquiv`。
形式化陈述：coe_symm_toHomeomorph : ⇑e.toHomeomorph.symm = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toHomeomorph : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

/-- Composition of `AffineIsometryEquiv`s as an `AffineIsometryEquiv`. -/
/-
**AffineIsometryEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：trans (e' : P₂ ≃ᵃⁱ[𝕜] P₃) : P ≃ᵃⁱ[𝕜] P₃
参数：e' : P₂ ≃ᵃⁱ[𝕜] P₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `AffineIsometryEquiv`s as an `AffineIsometryEquiv`.
-/
def trans (e' : P₂ ≃ᵃⁱ[𝕜] P₃) : P ≃ᵃⁱ[𝕜] P₃ :=
  ⟨e.toAffineEquiv.trans e'.toAffineEquiv, fun _ => (e'.norm_map _).trans (e.norm_map _)⟩

@[simp]
/-
**AffineIsometryEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：coe_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) : ⇑(e₁.trans e₂) = e₂ ∘ e
₁
参数：e₁ : P ≃ᵃⁱ[𝕜] P₂；e₂ : P₂ ≃ᵃⁱ[𝕜] P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`
。
形式化陈述：trans_refl : e.trans (refl 𝕜 P₂) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.ext`：ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e
' x) : e = e'
-/
theorem trans_refl : e.trans (refl 𝕜 P₂) = e :=
  ext fun _ => rfl

@[simp]
/-
**AffineIsometryEquiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`
。
形式化陈述：refl_trans : (refl 𝕜 P).trans e = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.ext`：ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e
' x) : e = e'
-/
theorem refl_trans : (refl 𝕜 P).trans e = e :=
  ext fun _ => rfl

@[simp]
/-
**AffineIsometryEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryE
quiv`。
形式化陈述：self_trans_symm : e.trans e.symm = refl 𝕜 P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.ext`：ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e
' x) : e = e'
· 使用定理 `AffineIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : P) : e.symm 
(e x) = x
-/
theorem self_trans_symm : e.trans e.symm = refl 𝕜 P :=
  ext e.symm_apply_apply

@[simp]
/-
**AffineIsometryEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryE
quiv`。
形式化陈述：symm_trans_self : e.symm.trans e = refl 𝕜 P₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.ext`：ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e
' x) : e = e'
· 使用定理 `AffineIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : P₂) : e (e.s
ymm x) = x
-/
theorem symm_trans_self : e.symm.trans e = refl 𝕜 P₂ :=
  ext e.apply_symm_apply

@[simp]
/-
**AffineIsometryEquiv.coe_symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEq
uiv`。
形式化陈述：coe_symm_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) : ⇑(e₁.trans e₂).sym
m = e₁.symm ∘ e₂.symm
参数：e₁ : P ≃ᵃⁱ[𝕜] P₂；e₂ : P₂ ≃ᵃⁱ[𝕜] P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_trans (e₁ : P ≃ᵃⁱ[𝕜] P₂) (e₂ : P₂ ≃ᵃⁱ[𝕜] P₃) :
    ⇑(e₁.trans e₂).symm = e₁.symm ∘ e₂.symm :=
  rfl
/-
**AffineIsometryEquiv.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv
`。
形式化陈述：trans_assoc (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P
₄) : ePP₂.trans (eP₂G.trans eGG') = (ePP₂.trans eP₂G).trans eGG'
参数：ePP₂ : P ≃ᵃⁱ[𝕜] P₂；eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃；eGG' : P₃ ≃ᵃⁱ[𝕜] P₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_assoc (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G : P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄) :
    ePP₂.trans (eP₂G.trans eGG') = (ePP₂.trans eP₂G).trans eGG' :=
  rfl

/-- The group of affine isometries of a `NormedAddTorsor`, `P`. -/
/-
**AffineIsometryEquiv.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：instGroup : Group (P ≃ᵃⁱ[𝕜] P) where mul e₁ e₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.trans_assoc`：trans_assoc (ePP₂ : P ≃ᵃⁱ[𝕜] P₂) (eP₂G 
: P₂ ≃ᵃⁱ[𝕜] P₃) (eGG' : P₃ ≃ᵃⁱ[𝕜] P₄) : ePP₂.trans (eP₂G.trans eGG') = (ePP₂.tra
ns eP₂G).trans eGG'
· 使用定理 `AffineIsometryEquiv.trans_refl`：trans_refl : e.trans (refl 𝕜 P₂) = e
· 使用定理 `AffineIsometryEquiv.refl_trans`：refl_trans : (refl 𝕜 P).trans e = e
· 使用定理 `AffineIsometryEquiv.self_trans_symm`：self_trans_symm : e.trans e.symm = 
refl 𝕜 P

--- 原说明 ---
The group of affine isometries of a `NormedAddTorsor`, `P`.
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
/-
**AffineIsometryEquiv.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：coe_one : ⇑(1 : P ≃ᵃⁱ[𝕜] P) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : P ≃ᵃⁱ[𝕜] P) = id :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：coe_mul (e e' : P ≃ᵃⁱ[𝕜] P) : ⇑(e * e') = e ∘ e'
参数：e e' : P ≃ᵃⁱ[𝕜] P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (e e' : P ≃ᵃⁱ[𝕜] P) : ⇑(e * e') = e ∘ e' :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：coe_inv (e : P ≃ᵃⁱ[𝕜] P) : ⇑e⁻¹ = e.symm
参数：e : P ≃ᵃⁱ[𝕜] P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (e : P ≃ᵃⁱ[𝕜] P) : ⇑e⁻¹ = e.symm :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.map_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：map_vadd (p : P) (v : V) : e (v +ᵥ p) = e.linearIsometryEquiv v +ᵥ e p
参数：p : P；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.map_vadd`：map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linea
rIsometry v +ᵥ f p
-/
theorem map_vadd (p : P) (v : V) : e (v +ᵥ p) = e.linearIsometryEquiv v +ᵥ e p :=
  e.toAffineIsometry.map_vadd p v

@[simp]
/-
**AffineIsometryEquiv.map_vsub** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：map_vsub (p1 p2 : P) : e.linearIsometryEquiv (p1 -ᵥ p2) = e p1 -ᵥ e p2
参数：p1 p2 : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.map_vsub`：map_vsub (p1 p2 : P) : f.linearIsometry (p1 -ᵥ 
p2) = f p1 -ᵥ f p2
-/
theorem map_vsub (p1 p2 : P) : e.linearIsometryEquiv (p1 -ᵥ p2) = e p1 -ᵥ e p2 :=
  e.toAffineIsometry.map_vsub p1 p2

@[simp]
/-
**AffineIsometryEquiv.dist_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：dist_map (x y : P) : dist (e x) (e y) = dist x y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.dist_map`：dist_map (x y : P) : dist (f x) (f y) = dist x 
y
-/
theorem dist_map (x y : P) : dist (e x) (e y) = dist x y :=
  e.toAffineIsometry.dist_map x y

@[simp]
/-
**AffineIsometryEquiv.edist_map** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：edist_map (x y : P) : edist (e x) (e y) = edist x y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.edist_map`：edist_map (x y : P) : edist (f x) (f y) = edis
t x y
-/
theorem edist_map (x y : P) : edist (e x) (e y) = edist x y :=
  e.toAffineIsometry.edist_map x y
/-
**AffineIsometryEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂), Function.B
ijective ⇑e
参数：e : P ≃ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.bijective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} 
{V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [in
st_2 : AddC…
-/
protected theorem bijective : Bijective e :=
  e.1.bijective
/-
**AffineIsometryEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂), Function.I
njective ⇑e
参数：e : P ≃ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.injective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} 
{V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [in
st_2 : AddC…
-/
protected theorem injective : Injective e :=
  e.1.injective
/-
**AffineIsometryEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`
。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂), Function.S
urjective ⇑e
参数：e : P ≃ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.surjective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3}
 {V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [i
nst_2 : AddC…
-/
protected theorem surjective : Surjective e :=
  e.1.surjective
/-
**AffineIsometryEquiv.map_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`
。
形式化陈述：map_eq_iff {x y : P} : e x = e y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AffineIsometryEquiv.injective`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Typ
e u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semin
ormedAddCommGroup V…
-/
theorem map_eq_iff {x y : P} : e x = e y ↔ x = y :=
  e.injective.eq_iff
/-
**AffineIsometryEquiv.map_ne** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：map_ne {x y : P} (h : x != y) : e x != e y
参数：h : x != y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `AffineIsometryEquiv.injective`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Typ
e u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semin
ormedAddCommGroup V…
-/
theorem map_ne {x y : P} (h : x ≠ y) : e x ≠ e y :=
  e.injective.ne h
/-
**AffineIsometryEquiv.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂), LipschitzW
ith 1 ⇑e
参数：e : P ≃ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…
-/
protected theorem lipschitz : LipschitzWith 1 e :=
  e.isometry.lipschitz
/-
**AffineIsometryEquiv.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEqu
iv`。
形式化陈述：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type
 u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V] [inst_2 : No
rmedSpace 𝕜 V] [inst_3 : PseudoMetricSpace P]   [inst_4 : NormedAddTorsor V P] [
inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7 : Pseu
doMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂), Antilipsch
itzWith 1 ⇑e
参数：e : P ≃ᵃⁱ[𝕜] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…
-/
protected theorem antilipschitz : AntilipschitzWith 1 e :=
  e.isometry.antilipschitz

@[simp]
/-
**AffineIsometryEquiv.ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv
`。
形式化陈述：ediam_image (s : Set P) : ediam (e '' s) = ediam s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…
-/
theorem ediam_image (s : Set P) : ediam (e '' s) = ediam s :=
  e.isometry.ediam_image s

@[simp]
/-
**AffineIsometryEquiv.diam_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`
。
形式化陈述：diam_image (s : Set P) : Metric.diam (e '' s) = Metric.diam s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…
-/
theorem diam_image (s : Set P) : Metric.diam (e '' s) = Metric.diam s :=
  e.isometry.diam_image s

variable {α : Type*} [TopologicalSpace α]

@[simp]
/-
**AffineIsometryEquiv.comp_continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineIso
metryEquiv`。
形式化陈述：comp_continuousOn_iff {f : α -> P} {s : Set α} : ContinuousOn (e ∘ f) s ↔ 
ContinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp_continuousOn_iff`：comp_continuousOn_iff {γ} [TopologicalSp
ace γ] (hf : Isometry f) {g : γ -> α} {s : Set γ} : ContinuousOn (f ∘ g) s ↔ Con
tinuousOn g s
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…
-/
theorem comp_continuousOn_iff {f : α → P} {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.isometry.comp_continuousOn_iff

@[simp]
/-
**AffineIsometryEquiv.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsome
tryEquiv`。
形式化陈述：comp_continuous_iff {f : α -> P} : Continuous (e ∘ f) ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp_continuous_iff`：comp_continuous_iff {γ} [TopologicalSpace 
γ] (hf : Isometry f) {g : γ -> α} : Continuous (f ∘ g) ↔ Continuous g
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…
-/
theorem comp_continuous_iff {f : α → P} : Continuous (e ∘ f) ↔ Continuous f :=
  e.isometry.comp_continuous_iff

section Constructions

variable (s₁ s₂ : AffineSubspace 𝕜 P) [Nonempty s₁] [Nonempty s₂]

/-- The identity equivalence of an affine subspace equal to `⊤` to the whole space. -/
/-
**AffineIsometryEquiv.ofTop** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：ofTop (h : s₁ = ⊤) : s₁ ≃ᵃⁱ[𝕜] P
参数：h : s₁ = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity equivalence of an affine subspace equal to `⊤` to the whole space.
-/
def ofTop (h : s₁ = ⊤) : s₁ ≃ᵃⁱ[𝕜] P :=
  { (AffineEquiv.ofEq s₁ ⊤ h).trans (AffineSubspace.topEquiv 𝕜 V P) with norm_map := fun _ ↦ rfl }

variable {s₁}

@[simp]
/-
**AffineIsometryEquiv.ofTop_apply** 是 Mathlib 中的一个引理，位于命名空间 `AffineIsometryEquiv
`。
形式化陈述：ofTop_apply (h : s₁ = ⊤) (x : s₁) : (ofTop s₁ h x : P) = x
参数：h : s₁ = ⊤；x : s₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofTop_apply (h : s₁ = ⊤) (x : s₁) : (ofTop s₁ h x : P) = x :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.ofTop_symm_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `AffineIsom
etryEquiv`。
形式化陈述：ofTop_symm_apply_coe (h : s₁ = ⊤) (x : P) : (ofTop s₁ h).symm x = x
参数：h : s₁ = ⊤；x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofTop_symm_apply_coe (h : s₁ = ⊤) (x : P) : (ofTop s₁ h).symm x = x :=
  rfl

variable (s₁)

/-- `AffineEquiv.ofEq` as an `AffineIsometryEquiv`. -/
/-
**AffineIsometryEquiv.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：ofEq (h : s₁ = s₂) : s₁ ≃ᵃⁱ[𝕜] s₂
参数：h : s₁ = s₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AffineEquiv.ofEq` as an `AffineIsometryEquiv`.
-/
def ofEq (h : s₁ = s₂) : s₁ ≃ᵃⁱ[𝕜] s₂ :=
  { AffineEquiv.ofEq s₁ s₂ h with norm_map := fun _ ↦ rfl }

variable {s₁ s₂}

@[simp]
/-
**AffineIsometryEquiv.coe_ofEq_apply** 是 Mathlib 中的一个引理，位于命名空间 `AffineIsometryEq
uiv`。
形式化陈述：coe_ofEq_apply (h : s₁ = s₂) (x : s₁) : (ofEq s₁ s₂ h x : P) = x
参数：h : s₁ = s₂；x : s₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofEq_apply (h : s₁ = s₂) (x : s₁) : (ofEq s₁ s₂ h x : P) = x :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.ofEq_symm** 是 Mathlib 中的一个引理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：ofEq_symm (h : s₁ = s₂) : (ofEq s₁ s₂ h).symm = ofEq s₂ s₁ h.symm
参数：h : s₁ = s₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofEq_symm (h : s₁ = s₂) : (ofEq s₁ s₂ h).symm = ofEq s₂ s₁ h.symm :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.ofEq_rfl** 是 Mathlib 中的一个引理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：ofEq_rfl : ofEq s₁ s₁ rfl = refl 𝕜 s₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofEq_rfl : ofEq s₁ s₁ rfl = refl 𝕜 s₁ :=
  rfl

variable (𝕜) in
/-- The map `v ↦ v +ᵥ p` as an affine isometric equivalence between `V` and `P`. -/
/-
**AffineIsometryEquiv.vaddConst** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：vaddConst (p : P) : V ≃ᵃⁱ[𝕜] P
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `v ↦ v +ᵥ p` as an affine isometric equivalence between `V` and `P`.
-/
def vaddConst (p : P) : V ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.vaddConst 𝕜 p with norm_map := fun _ => rfl }

@[simp]
/-
**AffineIsometryEquiv.coe_vaddConst** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEqu
iv`。
形式化陈述：coe_vaddConst (p : P) : ⇑(vaddConst 𝕜 p) = fun v => v +ᵥ p
参数：p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_vaddConst (p : P) : ⇑(vaddConst 𝕜 p) = fun v => v +ᵥ p :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.coe_vaddConst'** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEq
uiv`。
形式化陈述：coe_vaddConst' (p : P) : ↑(AffineEquiv.vaddConst 𝕜 p) = fun v => v +ᵥ p
参数：p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_vaddConst' (p : P) : ↑(AffineEquiv.vaddConst 𝕜 p) = fun v => v +ᵥ p :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.coe_vaddConst_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsomet
ryEquiv`。
形式化陈述：coe_vaddConst_symm (p : P) : ⇑(vaddConst 𝕜 p).symm = fun p' => p' -ᵥ p
参数：p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_vaddConst_symm (p : P) : ⇑(vaddConst 𝕜 p).symm = fun p' => p' -ᵥ p :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.vaddConst_toAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AffineI
sometryEquiv`。
形式化陈述：vaddConst_toAffineEquiv (p : P) : (vaddConst 𝕜 p).toAffineEquiv = AffineEq
uiv.vaddConst 𝕜 p
参数：p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vaddConst_toAffineEquiv (p : P) :
    (vaddConst 𝕜 p).toAffineEquiv = AffineEquiv.vaddConst 𝕜 p :=
  rfl

variable (𝕜) in
/-- `p' ↦ p -ᵥ p'` as an affine isometric equivalence. -/
/-
**AffineIsometryEquiv.constVSub** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：constVSub (p : P) : P ≃ᵃⁱ[𝕜] V
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p' ↦ p -ᵥ p'` as an affine isometric equivalence.
-/
def constVSub (p : P) : P ≃ᵃⁱ[𝕜] V :=
  { AffineEquiv.constVSub 𝕜 p with norm_map := norm_neg }

@[simp]
/-
**AffineIsometryEquiv.coe_constVSub** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEqu
iv`。
形式化陈述：coe_constVSub (p : P) : ⇑(constVSub 𝕜 p) = (p -ᵥ ·)
参数：p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_constVSub (p : P) : ⇑(constVSub 𝕜 p) = (p -ᵥ ·) :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.symm_constVSub** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEq
uiv`。
形式化陈述：symm_constVSub (p : P) : (constVSub 𝕜 p).symm = (LinearIsometryEquiv.neg 𝕜
).toAffineIsometryEquiv.trans (vaddConst 𝕜 p)
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.ext`：ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e
' x) : e = e'
-/
theorem symm_constVSub (p : P) :
    (constVSub 𝕜 p).symm =
      (LinearIsometryEquiv.neg 𝕜).toAffineIsometryEquiv.trans (vaddConst 𝕜 p) := by
  ext
  rfl

variable (𝕜 P) in
/-- Translation by `v` (that is, the map `p ↦ v +ᵥ p`) as an affine isometric automorphism of `P`.
-/
/-
**AffineIsometryEquiv.constVAdd** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：constVAdd (v : V) : P ≃ᵃⁱ[𝕜] P
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Translation by `v` (that is, the map `p ↦ v +ᵥ p`) as an affine isometric automo
rphism of `P`.
-/
def constVAdd (v : V) : P ≃ᵃⁱ[𝕜] P :=
  { AffineEquiv.constVAdd 𝕜 P v with norm_map := fun _ => rfl }

@[simp]
/-
**AffineIsometryEquiv.coe_constVAdd** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEqu
iv`。
形式化陈述：coe_constVAdd (v : V) : ⇑(constVAdd 𝕜 P v : P ≃ᵃⁱ[𝕜] P) = (v +ᵥ ·)
参数：v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_constVAdd (v : V) : ⇑(constVAdd 𝕜 P v : P ≃ᵃⁱ[𝕜] P) = (v +ᵥ ·) :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.constVAdd_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEq
uiv`。
形式化陈述：constVAdd_zero : constVAdd 𝕜 P (0 : V) = refl 𝕜 P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.ext`：ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : forall x, e x = e
' x) : e = e'
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
-/
theorem constVAdd_zero : constVAdd 𝕜 P (0 : V) = refl 𝕜 P :=
  ext <| zero_vadd V

include 𝕜 in
/-- The map `g` from `V` to `V₂` corresponding to a map `f` from `P` to `P₂`, at a base point `p`,
is an isometry if `f` is one. -/
/-
**AffineIsometryEquiv.vadd_vsub** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsometryEquiv`。
形式化陈述：vadd_vsub {f : P -> P₂} (hf : Isometry f) {p : P} {g : V -> V₂} (hg : fora
ll v, g v = f (v +ᵥ p) -ᵥ f p) : Isometry g
参数：hf : Isometry f；hg : forall v, g v = f (v +ᵥ p) -ᵥ f p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `AffineIsometryEquiv.isometry`：∀ {𝕜 : Type u_1} {V : Type u_2} {V₂ : Type
 u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Semino
rmedAddCommGroup V…

--- 原说明 ---
The map `g` from `V` to `V₂` corresponding to a map `f` from `P` to `P₂`, at a b
ase point `p`,
is an isometry if `f` is one.
-/
theorem vadd_vsub {f : P → P₂} (hf : Isometry f) {p : P} {g : V → V₂}
    (hg : ∀ v, g v = f (v +ᵥ p) -ᵥ f p) : Isometry g := by
  convert! (vaddConst 𝕜 (f p)).symm.isometry.comp (hf.comp (vaddConst 𝕜 p).isometry)
  exact funext hg

variable (𝕜) in
/-- Point reflection in `x` as an affine isometric automorphism. -/
/-
**AffineIsometryEquiv.pointReflection** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometryE
quiv`。
形式化陈述：pointReflection (x : P) : P ≃ᵃⁱ[𝕜] P
参数：x : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Point reflection in `x` as an affine isometric automorphism.
-/
def pointReflection (x : P) : P ≃ᵃⁱ[𝕜] P :=
  (constVSub 𝕜 x).trans (vaddConst 𝕜 x)
/-
**AffineIsometryEquiv.pointReflection_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineIso
metryEquiv`。
形式化陈述：pointReflection_apply (x y : P) : (pointReflection 𝕜 x) y = (x -ᵥ y) +ᵥ x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointReflection_apply (x y : P) : (pointReflection 𝕜 x) y = (x -ᵥ y) +ᵥ x :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.pointReflection_toAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 `A
ffineIsometryEquiv`。
形式化陈述：pointReflection_toAffineEquiv (x : P) : (pointReflection 𝕜 x).toAffineEqui
v = AffineEquiv.pointReflection 𝕜 x
参数：x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointReflection_toAffineEquiv (x : P) :
    (pointReflection 𝕜 x).toAffineEquiv = AffineEquiv.pointReflection 𝕜 x :=
  rfl

@[simp]
/-
**AffineIsometryEquiv.pointReflection_self** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsom
etryEquiv`。
形式化陈述：pointReflection_self (x : P) : pointReflection 𝕜 x x = x
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.pointReflection_self`：pointReflection_self (x : P₁) : pointR
eflection k x x = x
-/
theorem pointReflection_self (x : P) : pointReflection 𝕜 x x = x :=
  AffineEquiv.pointReflection_self 𝕜 x
/-
**AffineIsometryEquiv.pointReflection_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neIsometryEquiv`。
形式化陈述：pointReflection_involutive (x : P) : Function.Involutive (pointReflection 
𝕜 x)
参数：x : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.pointReflection_involutive`：pointReflection_involutive (x : P) : I
nvolutive (pointReflection x : P -> P)
-/
theorem pointReflection_involutive (x : P) : Function.Involutive (pointReflection 𝕜 x) :=
  Equiv.pointReflection_involutive x

@[simp]
/-
**AffineIsometryEquiv.pointReflection_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsom
etryEquiv`。
形式化陈述：pointReflection_symm (x : P) : (pointReflection 𝕜 x).symm = pointReflectio
n 𝕜 x
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometryEquiv.toAffineEquiv_injective`：∀ {𝕜 : Type u_1} {V : Type 
u_2} {V₂ : Type u_5} {P : Type u_10} {P₂ : Type u_11} [inst : NormedField 𝕜]   [
inst_1 : SeminormedAddCommGroup V…
· 使用定理 `AffineEquiv.pointReflection_symm`：pointReflection_symm (x : P₁) : (point
Reflection k x).symm = pointReflection k x
-/
theorem pointReflection_symm (x : P) : (pointReflection 𝕜 x).symm = pointReflection 𝕜 x :=
  toAffineEquiv_injective <| AffineEquiv.pointReflection_symm 𝕜 x

@[simp]
/-
**AffineIsometryEquiv.dist_pointReflection_fixed** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neIsometryEquiv`。
形式化陈述：dist_pointReflection_fixed (x y : P) : dist (pointReflection 𝕜 x y) x = di
st y x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineIsometryEquiv.dist_map`：dist_map (x y : P) : dist (e x) (e y) = di
st x y
· 使用定理 `AffineIsometryEquiv.pointReflection_self`：pointReflection_self (x : P) :
 pointReflection 𝕜 x x = x
-/
theorem dist_pointReflection_fixed (x y : P) : dist (pointReflection 𝕜 x y) x = dist y x := by
  rw [← (pointReflection 𝕜 x).dist_map y x, pointReflection_self]
/-
**AffineIsometryEquiv.dist_pointReflection_self'** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neIsometryEquiv`。
形式化陈述：dist_pointReflection_self' (x y : P) : dist (pointReflection 𝕜 x y) y = ‖2
 • (x -ᵥ y)‖
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIsometryEquiv.pointReflection_apply`：pointReflection_apply (x y : 
P) : (pointReflection 𝕜 x) y = (x -ᵥ y) +ᵥ x
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
-/
theorem dist_pointReflection_self' (x y : P) :
    dist (pointReflection 𝕜 x y) y = ‖2 • (x -ᵥ y)‖ := by
  rw [pointReflection_apply, dist_eq_norm_vsub V, vadd_vsub_assoc, two_nsmul]
/-
**AffineIsometryEquiv.dist_pointReflection_self** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eIsometryEquiv`。
形式化陈述：dist_pointReflection_self (x y : P) : dist (pointReflection 𝕜 x y) y = ‖(2
 : 𝕜)‖ * dist x y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIsometryEquiv.dist_pointReflection_self'`：dist_pointReflection_sel
f' (x y : P) : dist (pointReflection 𝕜 x y) y = ‖2 • (x -ᵥ y)‖
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
-/
theorem dist_pointReflection_self (x y : P) :
    dist (pointReflection 𝕜 x y) y = ‖(2 : 𝕜)‖ * dist x y := by
  rw [dist_pointReflection_self', two_nsmul, ← two_smul 𝕜, norm_smul, ← dist_eq_norm_vsub V]
/-
**AffineIsometryEquiv.pointReflection_fixed_iff** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eIsometryEquiv`。
形式化陈述：pointReflection_fixed_iff [Invertible (2 : 𝕜)] {x y : P} : pointReflection
 𝕜 x y = y ↔ y = x
参数：2 : 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineEquiv.pointReflection_fixed_iff_of_module`：pointReflection_fixed_i
ff_of_module [Invertible (2 : k)] {x y : P₁} : pointReflection k x y = y ↔ y = x
-/
theorem pointReflection_fixed_iff [Invertible (2 : 𝕜)] {x y : P} :
    pointReflection 𝕜 x y = y ↔ y = x :=
  AffineEquiv.pointReflection_fixed_iff_of_module 𝕜

variable [NormedSpace ℝ V]
/-
**AffineIsometryEquiv.dist_pointReflection_self_real** 是 Mathlib 中的一个定理，位于命名空间 `
AffineIsometryEquiv`。
形式化陈述：dist_pointReflection_self_real (x y : P) : dist (pointReflection Real x y)
 y = 2 * dist x y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIsometryEquiv.dist_pointReflection_self`：dist_pointReflection_self
 (x y : P) : dist (pointReflection 𝕜 x y) y = ‖(2 : 𝕜)‖ * dist x y
· 使用引理 `Real.norm_two`：norm_two : ‖(2 : Real)‖ = 2
-/
theorem dist_pointReflection_self_real (x y : P) :
    dist (pointReflection ℝ x y) y = 2 * dist x y := by
  rw [dist_pointReflection_self, Real.norm_two]

@[simp]
/-
**AffineIsometryEquiv.pointReflection_midpoint_left** 是 Mathlib 中的一个定理，位于命名空间 `A
ffineIsometryEquiv`。
形式化陈述：pointReflection_midpoint_left (x y : P) : pointReflection Real (midpoint R
eal x y) x = y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.pointReflection_midpoint_left`：AffineEquiv.pointReflection_m
idpoint_left (x y : P) : pointReflection R (midpoint R x y) x = y
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem pointReflection_midpoint_left (x y : P) : pointReflection ℝ (midpoint ℝ x y) x = y :=
  AffineEquiv.pointReflection_midpoint_left x y

@[simp]
/-
**AffineIsometryEquiv.pointReflection_midpoint_right** 是 Mathlib 中的一个定理，位于命名空间 `
AffineIsometryEquiv`。
形式化陈述：pointReflection_midpoint_right (x y : P) : pointReflection Real (midpoint 
Real x y) y = x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.pointReflection_midpoint_right`：AffineEquiv.pointReflection_
midpoint_right (x y : P) : pointReflection R (midpoint R x y) y = x
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem pointReflection_midpoint_right (x y : P) : pointReflection ℝ (midpoint ℝ x y) y = x :=
  AffineEquiv.pointReflection_midpoint_right x y

end Constructions

end AffineIsometryEquiv

namespace AffineSubspace

/-- An affine subspace is isomorphic to its image under an injective affine map.
This is the affine version of `Submodule.equivMapOfInjective`.
-/
@[simps linear, simps! toFun]
/-
**AffineSubspace.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：equivMapOfInjective (E : AffineSubspace 𝕜 P₁) [Nonempty E] (φ : P₁ ->ᵃ[𝕜] 
P₂) (hφ : Function.Injective φ) : E ≃ᵃ[𝕜] E.map φ
参数：E : AffineSubspace 𝕜 P₁；φ : P₁ ->ᵃ[𝕜] P₂；hφ : Function.Injective φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine subspace is isomorphic to its image under an injective affine map.
This is the affine version of `Submodule.equivMapOfInjective`.
-/
noncomputable def equivMapOfInjective (E : AffineSubspace 𝕜 P₁) [Nonempty E] (φ : P₁ →ᵃ[𝕜] P₂)
    (hφ : Function.Injective φ) : E ≃ᵃ[𝕜] E.map φ :=
  { Equiv.Set.image _ (E : Set P₁) hφ with
    linear :=
      (E.direction.equivMapOfInjective φ.linear (φ.linear_injective_iff.mpr hφ)).trans
        (LinearEquiv.ofEq _ _ (AffineSubspace.map_direction _ _).symm)
    map_vadd' := fun p v => Subtype.ext <| φ.map_vadd p v }

/-- Restricts an affine isometry to an affine isometry equivalence between a nonempty affine
subspace `E` and its image.

This is an isometry version of `AffineSubspace.equivMap`, having a stronger premise and a stronger
conclusion.
-/
/-
**AffineSubspace.isometryEquivMap** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：isometryEquivMap (φ : P₁' ->ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty
 E] : E ≃ᵃⁱ[𝕜] E.map φ.toAffineMap
参数：φ : P₁' ->ᵃⁱ[𝕜] P₂；E : AffineSubspace 𝕜 P₁'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIsometry.injective`：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u
_5} {P₁' : Type u_9} {P₂ : Type u_11} [inst : NormedField 𝕜]   [inst_1 : Seminor
medAddCommGrou…

--- 原说明 ---
Restricts an affine isometry to an affine isometry equivalence between a nonempt
y affine
subspace `E` and its image.

This is an isometry version of `AffineSubspace.equivMap`, having a stronger prem
ise and a stronger
conclusion.
-/
noncomputable def isometryEquivMap (φ : P₁' →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty E] :
    E ≃ᵃⁱ[𝕜] E.map φ.toAffineMap :=
  ⟨E.equivMapOfInjective φ.toAffineMap φ.injective, fun _ => φ.norm_map _⟩

@[simp]
/-
**AffineSubspace.isometryEquivMap.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Af
fineSubspace.isometryEquivMap`。
形式化陈述：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u_5} {P₁' : Type u_9} {P₂ : T
ype u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V₁'] [inst_2
 : NormedSpace 𝕜 V₁'] [inst_3 : MetricSpace P₁']   [inst_4 : NormedAddTorsor V₁'
 P₁'] [inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7
 : PseudoMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] {E : AffineSubspace 𝕜 
P₁'} [inst_9 : Nonempty ↥E]   {φ : P₁' →ᵃⁱ[𝕜] P₂} (x : ↥(AffineSubspace.map φ.to
AffineMap E)),   φ ↑((AffineSubspace.isometryEquivMap φ E).symm x) = ↑x
参数：x : ↥(AffineSubspace.map φ.toAffineMap E)；(AffineSubspace.isometryEquivMap φ 
E).symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AffineIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : P₂) : e (e.s
ymm x) = x
-/
theorem isometryEquivMap.apply_symm_apply {E : AffineSubspace 𝕜 P₁'} [Nonempty E]
    {φ : P₁' →ᵃⁱ[𝕜] P₂} (x : E.map φ.toAffineMap) : φ ((E.isometryEquivMap φ).symm x) = x :=
  congr_arg Subtype.val <| (E.isometryEquivMap φ).apply_symm_apply _

@[simp]
/-
**AffineSubspace.isometryEquivMap.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineSub
space.isometryEquivMap`。
形式化陈述：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u_5} {P₁' : Type u_9} {P₂ : T
ype u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V₁'] [inst_2
 : NormedSpace 𝕜 V₁'] [inst_3 : MetricSpace P₁']   [inst_4 : NormedAddTorsor V₁'
 P₁'] [inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7
 : PseudoMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (φ : P₁' →ᵃⁱ[𝕜] P₂) (E
 : AffineSubspace 𝕜 P₁')   [inst_9 : Nonempty ↥E] (g : ↥E), ↑((AffineSubspace.is
ometryEquivMap φ E) g) = φ ↑g
参数：φ : P₁' →ᵃⁱ[𝕜] P₂；E : AffineSubspace 𝕜 P₁'；g : ↥E；(AffineSubspace.isometryEqu
ivMap φ E) g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isometryEquivMap.coe_apply (φ : P₁' →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁') [Nonempty E]
    (g : E) : ↑(E.isometryEquivMap φ g) = φ g :=
  rfl

@[simp]
/-
**AffineSubspace.isometryEquivMap.toAffineMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neSubspace.isometryEquivMap`。
形式化陈述：∀ {𝕜 : Type u_1} {V₁' : Type u_4} {V₂ : Type u_5} {P₁' : Type u_9} {P₂ : T
ype u_11} [inst : NormedField 𝕜]   [inst_1 : SeminormedAddCommGroup V₁'] [inst_2
 : NormedSpace 𝕜 V₁'] [inst_3 : MetricSpace P₁']   [inst_4 : NormedAddTorsor V₁'
 P₁'] [inst_5 : SeminormedAddCommGroup V₂] [inst_6 : NormedSpace 𝕜 V₂]   [inst_7
 : PseudoMetricSpace P₂] [inst_8 : NormedAddTorsor V₂ P₂] (φ : P₁' →ᵃⁱ[𝕜] P₂) (E
 : AffineSubspace 𝕜 P₁')   [inst_9 : Nonempty ↥E],   ↑(AffineSubspace.isometryEq
uivMap φ E).toAffineEquiv = ↑(E.equivMapOfInjective φ.toAffineMap ⋯)
参数：φ : P₁' →ᵃⁱ[𝕜] P₂；E : AffineSubspace 𝕜 P₁'；AffineSubspace.isometryEquivMap φ 
E；E.equivMapOfInjective φ.toAffineMap ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isometryEquivMap.toAffineMap_eq (φ : P₁' →ᵃⁱ[𝕜] P₂) (E : AffineSubspace 𝕜 P₁')
    [Nonempty E] :
    (E.isometryEquivMap φ).toAffineMap = E.equivMapOfInjective φ.toAffineMap φ.injective :=
  rfl

end AffineSubspace

