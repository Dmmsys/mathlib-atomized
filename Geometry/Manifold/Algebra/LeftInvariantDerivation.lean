/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.Geometry.Manifold.DerivationBundle

/-!

# Left invariant derivations

In this file we define the concept of left invariant derivations for a Lie group. The concept is
analogous to the more classical concept of left invariant vector fields, and it holds that the
derivation associated to a vector field is left invariant iff the field is.

Moreover we prove that `LeftInvariantDerivation I G` has the structure of a Lie algebra, hence
implementing one of the possible definitions of the Lie algebra attached to a Lie group.

Note that one can also define a Lie algebra on the space of left-invariant vector fields
(see `instLieAlgebraGroupLieAlgebra`). For finite-dimensional `C^∞` real manifolds, the space of
derivations can be canonically identified with the tangent space, and we recover the same Lie
algebra structure (TODO: prove this). In other smoothness classes or on other
fields, this identification is not always true, though, so the derivations point of view does not
work in these settings. The left-invariant vector fields should
therefore be favored to construct a theory of Lie groups in suitable generality.
-/

@[expose] public section


noncomputable section

open scoped LieGroup Manifold Derivation ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (G : Type*)
  [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [ContMDiffMul I ∞ G] (g h : G)

/--
Definition of `LeftInvariantDerivation` / `LeftInvariantDerivation` 的定义

English:
structure LeftInvariantDerivation
  parameters: extends Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯
  extends: Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯
  axioms and operations (1):
    - left_invariant'' : forall g, 𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt 1 toDerivation) = Derivation.evalAt g toDerivation

中文:
结构 左不变导子
  参数: extends 导子 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯
  继承: 导子 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯
  公理与运算 (1 个):
    - left_invariant'' : 对任意 g, 𝒅ₕ (smoothLeftMul_one I g) (导子.evalAt 1 toDerivation) = 导子.evalAt g toDerivation
-/
structure LeftInvariantDerivation extends Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  left_invariant'' :
    forall g, 𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt 1 toDerivation) =
      Derivation.evalAt g toDerivation

variable {I G}

namespace LeftInvariantDerivation

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (LeftInvariantDerivation I G) (Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯)
  body: ⟨toDerivation⟩

中文:
实例 :
  签名: Coe (左不变导子 I G) (导子 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯)
  定义体: ⟨toDerivation⟩

Depends on / 依赖: toDerivation
-/
instance : Coe (LeftInvariantDerivation I G) (Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  ⟨toDerivation⟩

attribute [coe] toDerivation

/--
theorem `toDerivation_injective` / 定理 `toDerivation_injective`

English:
theorem toDerivation_injective
  proof: fun X Y h => by cases X; cases Y; congr

中文:
定理 toDerivation_injective
  证明: fun X Y h => by cases X; cases Y; congr
-/
theorem toDerivation_injective :
    Function.Injective (toDerivation : LeftInvariantDerivation I G -> _) :=
  fun X Y h => by cases X; cases Y; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (LeftInvariantDerivation I G) C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯
  body: f.toDerivation
coe_injective _ _ h := toDerivation_injective DFunLike.ext' h

中文:
实例 :
  签名: 函数状 (左不变导子 I G) C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯
  定义体: f.toDerivation
coe_injective _ _ h := toDerivation_injective DFunLike.ext' h

Depends on / 依赖: f.toDerivation, toDerivation
-/
instance : FunLike (LeftInvariantDerivation I G) C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  coe f := f.toDerivation
coe_injective _ _ h := toDerivation_injective DFunLike.ext' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearMapClass (LeftInvariantDerivation I G) 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯
  body: map_add f.1
  map_smulₛₗ f := map_smul f.1.1

中文:
实例 :
  签名: 线性映射类 (左不变导子 I G) 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯
  定义体: map_add f.1
  map_smulₛₗ f := map_smul f.1.1

Depends on / 依赖: map_add
-/
instance : LinearMapClass (LeftInvariantDerivation I G) 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  map_add f := map_add f.1
  map_smulₛₗ f := map_smul f.1.1

variable {r : 𝕜} {X Y : LeftInvariantDerivation I G} {f f' : C^∞⟮I, G; 𝕜⟯}

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: X.toFun = ⇑X
  proof: rfl

中文:
定理 toFun_eq_coe
  结论: X.toFun = ⇑X
  证明: rfl
-/
theorem toFun_eq_coe : X.toFun = ⇑X :=
  rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_injective
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective :
    @Function.Injective (LeftInvariantDerivation I G) (_ -> C^∞⟮I, G; 𝕜⟯) DFunLike.coe :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall f, X f = Y f)
  statement: X = Y
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: (h : 对任意 f, X f = Y f)
  结论: X = Y
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (h : forall f, X f = Y f) : X = Y := DFunLike.ext _ _ h

variable (X Y f)

/--
theorem `coe_derivation` / 定理 `coe_derivation`

English:
theorem coe_derivation
  proof: rfl

中文:
定理 coe_derivation
  证明: rfl
-/
theorem coe_derivation :
    ⇑(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = (X : C^∞⟮I, G; 𝕜⟯ -> C^∞⟮I, G; 𝕜⟯) :=
  rfl

/--
theorem `left_invariant'` / 定理 `left_invariant'`

English:
theorem left_invariant'
  proof: left_invariant'' X g

中文:
定理 left_invariant'
  证明: left_invariant'' X g

Depends on / 依赖: left_invariant
-/
theorem left_invariant' :
    𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt (1 : G) ↑X) = Derivation.evalAt g ↑X :=
  left_invariant'' X g

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: X (f + f') = X f + X f'
  proof: by simp

中文:
定理 map_add
  结论: X (f + f') = X f + X f'
  证明: by simp
-/
protected theorem map_add : X (f + f') = X f + X f' := by simp

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: X 0 = 0
  proof: by simp

中文:
定理 map_zero
  结论: X 0 = 0
  证明: by simp
-/
protected theorem map_zero : X 0 = 0 := by simp

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  statement: X (-f) = -X f
  proof: by simp

中文:
定理 map_neg
  结论: X (-f) = -X f
  证明: by simp
-/
protected theorem map_neg : X (-f) = -X f := by simp

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  statement: X (f - f') = X f - X f'
  proof: by simp

中文:
定理 map_sub
  结论: X (f - f') = X f - X f'
  证明: by simp
-/
protected theorem map_sub : X (f - f') = X f - X f' := by simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  statement: X (r • f) = r • X f
  proof: by simp

@[simp]

中文:
定理 map_smul
  结论: X (r • f) = r • X f
  证明: by simp

@[simp]
-/
protected theorem map_smul : X (r • f) = r • X f := by simp

@[simp]
/--
theorem `leibniz` / 定理 `leibniz`

English:
theorem leibniz
  statement: X (f * f') = f • X f' + f' • X f
  proof: X.leibniz' _ _

中文:
定理 leibniz
  结论: X (f * f') = f • X f' + f' • X f
  证明: X.leibniz' _ _

Depends on / 依赖: X.leibniz, leibniz
-/
theorem leibniz : X (f * f') = f • X f' + f' • X f :=
  X.leibniz' _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (LeftInvariantDerivation I G)
  body: ⟨⟨0, fun g => by simp only [map_zero]⟩⟩

中文:
实例 :
  签名: 零 (左不变导子 I G)
  定义体: ⟨⟨0, fun g => by simp only [map_zero]⟩⟩

Depends on / 依赖: map_zero
-/
instance : Zero (LeftInvariantDerivation I G) :=
  ⟨⟨0, fun g => by simp only [map_zero]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LeftInvariantDerivation I G)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (左不变导子 I G)
  定义体: ⟨0⟩
-/
instance : Inhabited (LeftInvariantDerivation I G) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (LeftInvariantDerivation I G)
  body: ⟨X + Y, fun g => by
      simp only [map_add, left_invariant']⟩

中文:
实例 :
  签名: 加法 (左不变导子 I G)
  定义体: ⟨X + Y, fun g => by
      simp only [map_add, left_invariant']⟩

Depends on / 依赖: left_invariant, map_add
-/
instance : Add (LeftInvariantDerivation I G) where
  add X Y :=
    ⟨X + Y, fun g => by
      simp only [map_add, left_invariant']⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (LeftInvariantDerivation I G)
  body: ⟨-X, fun g => by simp [left_invariant']⟩

中文:
实例 :
  签名: 取负 (左不变导子 I G)
  定义体: ⟨-X, fun g => by simp [left_invariant']⟩

Depends on / 依赖: left_invariant
-/
instance : Neg (LeftInvariantDerivation I G) where
  neg X := ⟨-X, fun g => by simp [left_invariant']⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (LeftInvariantDerivation I G)
  body: ⟨X - Y, fun g => by simp [left_invariant']⟩

@[simp]

中文:
实例 :
  签名: 减法 (左不变导子 I G)
  定义体: ⟨X - Y, fun g => by simp [left_invariant']⟩

@[simp]

Depends on / 依赖: left_invariant
-/
instance : Sub (LeftInvariantDerivation I G) where
  sub X Y := ⟨X - Y, fun g => by simp [left_invariant']⟩

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  statement: ⇑(X + Y) = X + Y
  proof: rfl

@[simp]

中文:
定理 coe_add
  结论: ⇑(X + Y) = X + Y
  证明: rfl

@[simp]
-/
theorem coe_add : ⇑(X + Y) = X + Y :=
  rfl

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : LeftInvariantDerivation I G) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ⇑(0 : 左不变导子 I G) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ⇑(0 : LeftInvariantDerivation I G) = 0 :=
  rfl

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: ⇑(-X) = -X
  proof: rfl

@[simp]

中文:
定理 coe_neg
  结论: ⇑(-X) = -X
  证明: rfl

@[simp]
-/
theorem coe_neg : ⇑(-X) = -X :=
  rfl

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  statement: ⇑(X - Y) = X - Y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sub
  结论: ⇑(X - Y) = X - Y
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sub : ⇑(X - Y) = X - Y :=
  rfl

@[simp, norm_cast]
/--
theorem `lift_add` / 定理 `lift_add`

English:
theorem lift_add
  statement: (↑(X + Y) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y
  proof: rfl

@[simp, norm_cast]

中文:
定理 lift_add
  结论: (↑(X + Y) : 导子 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y
  证明: rfl

@[simp, norm_cast]
-/
theorem lift_add : (↑(X + Y) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y :=
  rfl

@[simp, norm_cast]
/--
theorem `lift_zero` / 定理 `lift_zero`

English:
theorem lift_zero
  proof: rfl

中文:
定理 lift_zero
  证明: rfl
-/
theorem lift_zero :
    (↑(0 : LeftInvariantDerivation I G) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = 0 :=
  rfl

/--
Instance `hasNatScalar` / 实例 `hasNatScalar`

English:
instance hasNatScalar
  signature: : SMul Nat (LeftInvariantDerivation I G) where
  body: ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩

中文:
实例 has自然数Scalar
  签名: : 标量乘法 自然数 (左不变导子 I G) where
  定义体: ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩

Depends on / 依赖: LinearMap, LinearMap.map_smul_of_tower, left_invariant, map_smul_of_tower, simp_rw
-/
instance hasNatScalar : SMul Nat (LeftInvariantDerivation I G) where
  smul r X := ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩

/--
Instance `hasIntScalar` / 实例 `hasIntScalar`

English:
instance hasIntScalar
  signature: : SMul Int (LeftInvariantDerivation I G) where
  body: ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩

中文:
实例 has整数Scalar
  签名: : 标量乘法 整数 (左不变导子 I G) where
  定义体: ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩

Depends on / 依赖: LinearMap, LinearMap.map_smul_of_tower, left_invariant, map_smul_of_tower, simp_rw
-/
instance hasIntScalar : SMul Int (LeftInvariantDerivation I G) where
  smul r X := ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (LeftInvariantDerivation I G)
  body: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: 加法交换群 (左不变导子 I G)
  定义体: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: addCommGroup, coe_add, coe_injective, coe_injective.addCommGroup, coe_neg, coe_sub, coe_zero
-/
instance : AddCommGroup (LeftInvariantDerivation I G) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul 𝕜 (LeftInvariantDerivation I G)
  body: ⟨r • X.1, fun g => by
    simp only [LinearMap.map_smul_of_tower, map_smul]; rw [left_invariant']⟩

中文:
实例 :
  签名: 标量乘法 𝕜 (左不变导子 I G)
  定义体: ⟨r • X.1, fun g => by
    simp only [LinearMap.map_smul_of_tower, map_smul]; rw [left_invariant']⟩

Depends on / 依赖: LinearMap, LinearMap.map_smul_of_tower, left_invariant, map_smul, map_smul_of_tower
-/
instance : SMul 𝕜 (LeftInvariantDerivation I G) where
  smul r X := ⟨r • X.1, fun g => by
    simp only [LinearMap.map_smul_of_tower, map_smul]; rw [left_invariant']⟩

variable (r)

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  statement: ⇑(r • X) = r • ⇑X
  proof: rfl

@[simp]

中文:
定理 coe_smul
  结论: ⇑(r • X) = r • ⇑X
  证明: rfl

@[simp]
-/
theorem coe_smul : ⇑(r • X) = r • ⇑X :=
  rfl

@[simp]
/--
theorem `lift_smul` / 定理 `lift_smul`

English:
theorem lift_smul
  given: (k : 𝕜)
  statement: (k • X).1 = k • X.1
  proof: rfl

中文:
定理 lift_smul
  条件: (k : 𝕜)
  结论: (k • X).1 = k • X.1
  证明: rfl
-/
theorem lift_smul (k : 𝕜) : (k • X).1 = k • X.1 :=
  rfl

variable (I G)

/-- The coercion to function is a monoid homomorphism. -/
@[simps]
/--
Definition of `coeFnAddMonoidHom` / `coeFnAddMonoidHom` 的定义

English:
definition coeFnAddMonoidHom
  signature: : LeftInvariantDerivation I G ->+ C^∞⟮I, G; 𝕜⟯ -> C^∞⟮I, G; 𝕜⟯
  body: ⟨⟨DFunLike.coe, coe_zero⟩, coe_add⟩

中文:
定义 coeFnAddMonoidHom
  签名: : 左不变导子 I G ->+ C^∞⟮I, G; 𝕜⟯ -> C^∞⟮I, G; 𝕜⟯
  定义体: ⟨⟨DFunLike.coe, coe_zero⟩, coe_add⟩

Depends on / 依赖: DFunLike, DFunLike.coe, coe_add, coe_zero
-/
def coeFnAddMonoidHom : LeftInvariantDerivation I G ->+ C^∞⟮I, G; 𝕜⟯ -> C^∞⟮I, G; 𝕜⟯ :=
  ⟨⟨DFunLike.coe, coe_zero⟩, coe_add⟩

variable {I G}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module 𝕜 (LeftInvariantDerivation I G)
  body: coe_injective.module _ (coeFnAddMonoidHom I G) coe_smul

中文:
实例 :
  签名: 模 𝕜 (左不变导子 I G)
  定义体: coe_injective.module _ (coeFnAddMonoidHom I G) coe_smul

Depends on / 依赖: coeFnAddMonoidHom, coe_injective, coe_injective.module, coe_smul, module
-/
instance : Module 𝕜 (LeftInvariantDerivation I G) :=
  coe_injective.module _ (coeFnAddMonoidHom I G) coe_smul

/--
Definition of `evalAt` / `evalAt` 的定义

English:
definition evalAt
  signature: : LeftInvariantDerivation I G ->ₗ[𝕜] PointDerivation I g where
  body: Derivation.evalAt g X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 evalAt
  签名: : 左不变导子 I G ->ₗ[𝕜] PointDerivation I g where
  定义体: Derivation.evalAt g X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: Derivation, Derivation.evalAt, evalAt
-/
def evalAt : LeftInvariantDerivation I G ->ₗ[𝕜] PointDerivation I g where
  toFun X := Derivation.evalAt g X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
theorem `evalAt_apply` / 定理 `evalAt_apply`

English:
theorem evalAt_apply
  statement: evalAt g X f = (X f) g
  proof: rfl

@[simp]

中文:
定理 evalAt_apply
  结论: evalAt g X f = (X f) g
  证明: rfl

@[simp]
-/
theorem evalAt_apply : evalAt g X f = (X f) g :=
  rfl

@[simp]
/--
theorem `evalAt_coe` / 定理 `evalAt_coe`

English:
theorem evalAt_coe
  statement: Derivation.evalAt g ↑X = evalAt g X
  proof: rfl

中文:
定理 evalAt_coe
  结论: 导子.evalAt g ↑X = evalAt g X
  证明: rfl
-/
theorem evalAt_coe : Derivation.evalAt g ↑X = evalAt g X :=
  rfl

/--
theorem `left_invariant` / 定理 `left_invariant`

English:
theorem left_invariant
  statement: 𝒅ₕ (smoothLeftMul_one I g) (evalAt (1 : G) X) = evalAt g X
  proof: X.left_invariant'' g

中文:
定理 left_invariant
  结论: 𝒅ₕ (smoothLeftMul_one I g) (evalAt (1 : G) X) = evalAt g X
  证明: X.left_invariant'' g

Depends on / 依赖: X.left_invariant, left_invariant
-/
theorem left_invariant : 𝒅ₕ (smoothLeftMul_one I g) (evalAt (1 : G) X) = evalAt g X :=
  X.left_invariant'' g

set_option backward.isDefEq.respectTransparency false in
/--
theorem `evalAt_mul` / 定理 `evalAt_mul`

English:
theorem evalAt_mul
  statement: evalAt (g * h) X = 𝒅ₕ (L_apply I g h) (evalAt h X)
  proof: by
  ext f
  rw [← left_invariant]; rw [hfdifferential_apply]; rw [hfdifferential_apply]; rw [L_mul]; rw [fdifferential_comp]; rw [fdifferential_apply]
  simp only [ContMDiffMap.comp_apply, LinearMap.comp_apply]
  rw [fdifferential_apply]; rw [← hfdifferential_apply (smoothLeftMul_one I h)]; rw [lef

中文:
定理 evalAt_mul
  结论: evalAt (g * h) X = 𝒅ₕ (L_apply I g h) (evalAt h X)
  证明: by
  ext f
  rw [← left_invariant]; rw [hfdifferential_apply]; rw [hfdifferential_apply]; rw [L_mul]; rw [fdifferential_comp]; rw [fdifferential_apply]
  simp only [ContMDiffMap.comp_apply, LinearMap.comp_apply]
  rw [fdifferential_apply]; rw [← hfdifferential_apply (smoothLeftMul_one I h)]; rw [lef

Depends on / 依赖: ContMDiffMap, ContMDiffMap.comp_apply, L_mul, LinearMap, LinearMap.comp_apply, comp_apply, fdifferential_apply, fdifferential_comp, hfdifferential_apply, left_invariant, smoothLeftMul_one
-/
theorem evalAt_mul : evalAt (g * h) X = 𝒅ₕ (L_apply I g h) (evalAt h X) := by
  ext f
  rw [← left_invariant]; rw [hfdifferential_apply]; rw [hfdifferential_apply]; rw [L_mul]; rw [fdifferential_comp]; rw [fdifferential_apply]
  simp only [ContMDiffMap.comp_apply, LinearMap.comp_apply]
  rw [fdifferential_apply]; rw [← hfdifferential_apply (smoothLeftMul_one I h)]; rw [left_invariant]

/--
theorem `comp_L` / 定理 `comp_L`

English:
theorem comp_L
  statement: (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g))
  proof: by
  ext h
  rw [ContMDiffMap.comp_apply]; rw [L_apply]; rw [← evalAt_apply]; rw [evalAt_mul]; rw [hfdifferential_apply]; rw [fdifferential_apply]; rw [evalAt_apply]

中文:
定理 comp_L
  结论: (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g))
  证明: by
  ext h
  rw [ContMDiffMap.comp_apply]; rw [L_apply]; rw [← evalAt_apply]; rw [evalAt_mul]; rw [hfdifferential_apply]; rw [fdifferential_apply]; rw [evalAt_apply]

Depends on / 依赖: ContMDiffMap, ContMDiffMap.comp_apply, L_apply, comp_apply, evalAt_apply, evalAt_mul, fdifferential_apply, hfdifferential_apply
-/
theorem comp_L : (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g)) := by
  ext h
  rw [ContMDiffMap.comp_apply]; rw [L_apply]; rw [← evalAt_apply]; rw [evalAt_mul]; rw [hfdifferential_apply]; rw [fdifferential_apply]; rw [evalAt_apply]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bracket (LeftInvariantDerivation I G) (LeftInvariantDerivation I G)
  body: ⟨⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆, fun g => by
      ext f
      have hX := Derivation.congr_fun (left_invariant' g X) (Y f)
      have hY := Derivation.congr_fun (left_invariant' g Y) (X f)
      rw [hfdifferential_apply]; rw [fdifferential_apply]; rw [Derivation.evalAt_apply] at h

中文:
实例 :
  签名: Bracket (左不变导子 I G) (左不变导子 I G)
  定义体: ⟨⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆, fun g => by
      ext f
      have hX := Derivation.congr_fun (left_invariant' g X) (Y f)
      have hY := Derivation.congr_fun (left_invariant' g Y) (X f)
      rw [hfdifferential_apply]; rw [fdifferential_apply]; rw [Derivation.evalAt_apply] at h

Depends on / 依赖: ContMDiffMap, ContMDiffMap.coe_sub, Derivation, Derivation.commutator_apply, Derivation.congr_fun, Derivation.evalAt_apply, Pi.sub_apply, coe_derivation, coe_sub, commutator_apply, comp_L, congr_fun, evalAt_apply, fdifferential_apply, hfdifferential_apply, left_invariant, sub_apply
-/
instance : Bracket (LeftInvariantDerivation I G) (LeftInvariantDerivation I G) where
  bracket X Y :=
    ⟨⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆, fun g => by
      ext f
      have hX := Derivation.congr_fun (left_invariant' g X) (Y f)
      have hY := Derivation.congr_fun (left_invariant' g Y) (X f)
      rw [hfdifferential_apply]; rw [fdifferential_apply]; rw [Derivation.evalAt_apply] at hX hY ⊢
      rw [comp_L] at hX hY
      rw [Derivation.commutator_apply]; rw [ContMDiffMap.coe_sub]; rw [Pi.sub_apply]; rw [coe_derivation]
      rw [coe_derivation] at hX hY ⊢
      rw [hX]; rw [hY]
      rfl⟩

@[simp]
/--
theorem `commutator_coe_derivation` / 定理 `commutator_coe_derivation`

English:
theorem commutator_coe_derivation
  proof: rfl

中文:
定理 commutator_coe_derivation
  证明: rfl
-/
theorem commutator_coe_derivation :
    ⇑⁅X, Y⁆ =
      (⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆ :
        Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  rfl

/--
theorem `commutator_apply` / 定理 `commutator_apply`

English:
theorem commutator_apply
  statement: ⁅X, Y⁆ f = X (Y f) - Y (X f)
  proof: rfl

中文:
定理 commutator_apply
  结论: ⁅X, Y⁆ f = X (Y f) - Y (X f)
  证明: rfl
-/
theorem commutator_apply : ⁅X, Y⁆ f = X (Y f) - Y (X f) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRing (LeftInvariantDerivation I G)
  body: by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_add X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_self X := by ext1; simp only [commutator_apply, sub_self]; rfl
  leibniz_lie X Y Z := by
    ext1
    s

中文:
实例 :
  签名: Lie环 (左不变导子 I G)
  定义体: by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_add X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_self X := by ext1; simp only [commutator_apply, sub_self]; rfl
  leibniz_lie X Y Z := by
    ext1
    s

Depends on / 依赖: Pi.add_apply, add_apply, coe_add, commutator_apply, leibniz_lie, lie_add, lie_self, map_add, map_sub, sub_self
-/
instance : LieRing (LeftInvariantDerivation I G) where
  add_lie X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_add X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_self X := by ext1; simp only [commutator_apply, sub_self]; rfl
  leibniz_lie X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, map_sub, Pi.add_apply]
    ring

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieAlgebra 𝕜 (LeftInvariantDerivation I G)
  body: by
    ext1
    simp only [commutator_apply, map_smul, smul_sub, coe_smul, Pi.smul_apply]

中文:
实例 :
  签名: Lie代数 𝕜 (左不变导子 I G)
  定义体: by
    ext1
    simp only [commutator_apply, map_smul, smul_sub, coe_smul, Pi.smul_apply]

Depends on / 依赖: Pi.smul_apply, coe_smul, commutator_apply, map_smul, smul_apply, smul_sub
-/
instance : LieAlgebra 𝕜 (LeftInvariantDerivation I G) where
  lie_smul r Y Z := by
    ext1
    simp only [commutator_apply, map_smul, smul_sub, coe_smul, Pi.smul_apply]

end LeftInvariantDerivation
