/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.GroupWithZero.Pointwise.Set.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Group actions by isometries

In this file we define two typeclasses:

- `IsIsometricSMul M X` says that `M` multiplicatively acts on a (pseudo extended) metric space
  `X` by isometries;
- `IsIsometricVAdd` is an additive version of `IsIsometricSMul`.

We also prove basic facts about isometric actions and define bundled isometries
`IsometryEquiv.constSMul`, `IsometryEquiv.mulLeft`, `IsometryEquiv.mulRight`,
`IsometryEquiv.divLeft`, `IsometryEquiv.divRight`, and `IsometryEquiv.inv`, as well as their
additive versions.

If `G` is a group, then `IsIsometricSMul G G` means that `G` has a left-invariant metric while
`IsIsometricSMul Gᵐᵒᵖ G` means that `G` has a right-invariant metric. For a commutative group,
these two notions are equivalent. A group with a right-invariant metric can be also represented as a
`NormedGroup`.
-/

@[expose] public section


open Set

open scoped ENNReal Pointwise

universe u v w

variable (M : Type u) (G : Type v) (X : Type w)

/--
Definition of `IsIsometricVAdd` / `IsIsometricVAdd` 的定义

English:
class IsIsometricVAdd
  parameters: (X : Type w) [PseudoEMetricSpace X] [VAdd M X]
  axioms and operations (1):
    - isometry_vadd((X)) : forall c : M, Isometry ((c +ᵥ ·) : X -> X)

中文:
类 是是ometricVAdd
  参数: (X : 类型 w) [PseudoEMetric空间 X] [向量加法 M X]
  公理与运算 (1 个):
    - isometry_vadd((X)) : 对任意 c : M, 等距 ((c +ᵥ ·) : X -> X)
-/
class IsIsometricVAdd (X : Type w) [PseudoEMetricSpace X] [VAdd M X] : Prop where
  isometry_vadd (X) : forall c : M, Isometry ((c +ᵥ ·) : X -> X)

/-- A multiplicative action is isometric if each map `x ↦ c • x` is an isometry. -/
@[to_additive]
/--
Definition of `IsIsometricSMul` / `IsIsometricSMul` 的定义

English:
class IsIsometricSMul
  parameters: (X : Type w) [PseudoEMetricSpace X] [SMul M X]
  axioms and operations (1):
    - isometry_smul((X)) : forall c : M, Isometry ((c • ·) : X -> X)

中文:
类 是是ometricSMul
  参数: (X : 类型 w) [PseudoEMetric空间 X] [标量乘法 M X]
  公理与运算 (1 个):
    - isometry_smul((X)) : 对任意 c : M, 等距 ((c • ·) : X -> X)
-/
class IsIsometricSMul (X : Type w) [PseudoEMetricSpace X] [SMul M X] : Prop where
  isometry_smul (X) : forall c : M, Isometry ((c • ·) : X -> X)

export IsIsometricSMul (isometry_smul)
export IsIsometricVAdd (isometry_vadd)

@[to_additive]
instance (priority := 100) IsIsometricSMul.to_continuousConstSMul [PseudoEMetricSpace X] [SMul M X]
    [IsIsometricSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (isometry_smul X c).continuous⟩

@[to_additive]
instance (priority := 100) IsIsometricSMul.opposite_of_comm [PseudoEMetricSpace X] [SMul M X]
    [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] [IsIsometricSMul M X] : IsIsometricSMul Mᵐᵒᵖ X :=
  ⟨fun c x y => by simpa only [← op_smul_eq_smul] using! isometry_smul X c.unop x y⟩

variable {M G X}

section EMetric

variable [PseudoEMetricSpace X] [Group G] [MulAction G X] [IsIsometricSMul G X]

@[to_additive (attr := simp)]
/--
theorem `edist_smul_left` / 定理 `edist_smul_left`

English:
theorem edist_smul_left
  given: [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X)
  proof: isometry_smul X c x y

@[to_additive (attr := simp)]

中文:
定理 edist_smul_left
  条件: [标量乘法 M X] [是是ometricSMul M X] (c : M) (x y : X)
  证明: isometry_smul X c x y

@[to_additive (attr := simp)]

Depends on / 依赖: isometry_smul
-/
theorem edist_smul_left [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X) :
    edist (c • x) (c • y) = edist x y :=
  isometry_smul X c x y

@[to_additive (attr := simp)]
/--
theorem `ediam_smul` / 定理 `ediam_smul`

English:
theorem ediam_smul
  given: [SMul M X] [IsIsometricSMul M X] (c : M) (s : Set X)
  proof: (isometry_smul _ _).ediam_image s

@[to_additive]

中文:
定理 ediam_smul
  条件: [标量乘法 M X] [是是ometricSMul M X] (c : M) (s : 集合 X)
  证明: (isometry_smul _ _).ediam_image s

@[to_additive]

Depends on / 依赖: ediam_image, isometry_smul
-/
theorem ediam_smul [SMul M X] [IsIsometricSMul M X] (c : M) (s : Set X) :
    Metric.ediam (c • s) = Metric.ediam s :=
  (isometry_smul _ _).ediam_image s

@[to_additive]
/--
theorem `isometry_mul_left` / 定理 `isometry_mul_left`

English:
theorem isometry_mul_left
  given: [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] (a : M)
  proof: isometry_smul M a

@[to_additive (attr := simp)]

中文:
定理 isometry_mul_left
  条件: [乘法 M] [PseudoEMetric空间 M] [是是ometricSMul M M] (a : M)
  证明: isometry_smul M a

@[to_additive (attr := simp)]

Depends on / 依赖: isometry_smul
-/
theorem isometry_mul_left [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] (a : M) :
    Isometry (a * ·) :=
  isometry_smul M a

@[to_additive (attr := simp)]
/--
theorem `edist_mul_left` / 定理 `edist_mul_left`

English:
theorem edist_mul_left
  given: [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] (a b c : M)
  proof: isometry_mul_left a b c

@[to_additive]

中文:
定理 edist_mul_left
  条件: [乘法 M] [PseudoEMetric空间 M] [是是ometricSMul M M] (a b c : M)
  证明: isometry_mul_left a b c

@[to_additive]

Depends on / 依赖: isometry_mul_left
-/
theorem edist_mul_left [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] (a b c : M) :
    edist (a * b) (a * c) = edist b c :=
  isometry_mul_left a b c

@[to_additive]
/--
theorem `isometry_mul_right` / 定理 `isometry_mul_right`

English:
theorem isometry_mul_right
  given: [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a : M)
  proof: isometry_smul M (MulOpposite.op a)

@[to_additive (attr := simp)]

中文:
定理 isometry_mul_right
  条件: [乘法 M] [PseudoEMetric空间 M] [是是ometricSMul Mᵐᵒᵖ M] (a : M)
  证明: isometry_smul M (MulOpposite.op a)

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op, isometry_smul
-/
theorem isometry_mul_right [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a : M) :
    Isometry fun x => x * a :=
  isometry_smul M (MulOpposite.op a)

@[to_additive (attr := simp)]
/--
theorem `edist_mul_right` / 定理 `edist_mul_right`

English:
theorem edist_mul_right
  given: [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a b c : M)
  proof: isometry_mul_right c a b

@[to_additive (attr := simp)]

中文:
定理 edist_mul_right
  条件: [乘法 M] [PseudoEMetric空间 M] [是是ometricSMul Mᵐᵒᵖ M] (a b c : M)
  证明: isometry_mul_right c a b

@[to_additive (attr := simp)]

Depends on / 依赖: isometry_mul_right
-/
theorem edist_mul_right [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    edist (a * c) (b * c) = edist a b :=
  isometry_mul_right c a b

@[to_additive (attr := simp)]
/--
theorem `edist_div_right` / 定理 `edist_div_right`

English:
theorem edist_div_right
  statement: [DivInvMonoid M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
  proof: by
  simp only [div_eq_mul_inv, edist_mul_right]

@[to_additive (attr := simp)]

中文:
定理 edist_div_right
  结论: [除逆幺半群 M] [PseudoEMetric空间 M] [是是ometricSMul Mᵐᵒᵖ M]
  证明: by
  simp only [div_eq_mul_inv, edist_mul_right]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, edist_mul_right
-/
theorem edist_div_right [DivInvMonoid M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : edist (a / c) (b / c) = edist a b := by
  simp only [div_eq_mul_inv, edist_mul_right]

@[to_additive (attr := simp)]
/--
theorem `edist_inv_inv` / 定理 `edist_inv_inv`

English:
theorem edist_inv_inv
  statement: [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
  proof: by
  rw [← edist_mul_left a]; rw [← edist_mul_right _ _ b]; rw [mul_inv_cancel]; rw [one_mul]; rw [inv_mul_cancel_right]; rw [edist_comm]

@[to_additive]

中文:
定理 edist_inv_inv
  结论: [PseudoEMetric空间 G] [是是ometricSMul G G] [是是ometricSMul Gᵐᵒᵖ G]
  证明: by
  rw [← edist_mul_left a]; rw [← edist_mul_right _ _ b]; rw [mul_inv_cancel]; rw [one_mul]; rw [inv_mul_cancel_right]; rw [edist_comm]

@[to_additive]

Depends on / 依赖: edist_comm, edist_mul_left, edist_mul_right, inv_mul_cancel_right, mul_inv_cancel, one_mul
-/
theorem edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
    (a b : G) : edist a⁻¹ b⁻¹ = edist a b := by
  rw [← edist_mul_left a]; rw [← edist_mul_right _ _ b]; rw [mul_inv_cancel]; rw [one_mul]; rw [inv_mul_cancel_right]; rw [edist_comm]

@[to_additive]
/--
theorem `isometry_inv` / 定理 `isometry_inv`

English:
theorem isometry_inv
  given: [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
  proof: edist_inv_inv

@[to_additive]

中文:
定理 isometry_inv
  条件: [PseudoEMetric空间 G] [是是ometricSMul G G] [是是ometricSMul Gᵐᵒᵖ G]
  证明: edist_inv_inv

@[to_additive]

Depends on / 依赖: edist_inv_inv
-/
theorem isometry_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G] :
    Isometry (Inv.inv : G -> G) :=
  edist_inv_inv

@[to_additive]
/--
theorem `edist_inv` / 定理 `edist_inv`

English:
theorem edist_inv
  statement: [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
  proof: by rw [← edist_inv_inv, inv_inv]

@[to_additive (attr := simp)]

中文:
定理 edist_inv
  结论: [PseudoEMetric空间 G] [是是ometricSMul G G] [是是ometricSMul Gᵐᵒᵖ G]
  证明: by rw [← edist_inv_inv, inv_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: edist_inv_inv, inv_inv
-/
theorem edist_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
    (x y : G) : edist x⁻¹ y = edist x y⁻¹ := by rw [← edist_inv_inv, inv_inv]

@[to_additive (attr := simp)]
/--
theorem `edist_div_left` / 定理 `edist_div_left`

English:
theorem edist_div_left
  statement: [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [edist_mul_left]; rw [edist_inv_inv]

中文:
定理 edist_div_left
  结论: [PseudoEMetric空间 G] [是是ometricSMul G G] [是是ometricSMul Gᵐᵒᵖ G]
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [edist_mul_left]; rw [edist_inv_inv]

Depends on / 依赖: div_eq_mul_inv, edist_inv_inv, edist_mul_left
-/
theorem edist_div_left [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
    (a b c : G) : edist (a / b) (a / c) = edist b c := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [edist_mul_left]; rw [edist_inv_inv]

namespace IsometryEquiv

/-- If a group `G` acts on `X` by isometries, then `IsometryEquiv.constSMul` is the isometry of
`X` given by multiplication of a constant element of the group. -/
@[to_additive (attr := simps! toEquiv apply) /-- If an additive group `G` acts on `X` by isometries,
then `IsometryEquiv.constVAdd` is the isometry of `X` given by addition of a constant element of the
group. -/]
/--
Definition of `constSMul` / `constSMul` 的定义

English:
definition constSMul
  signature: (c : G)
  body: MulAction.toPerm c
  isometry_toFun := isometry_smul X c

@[to_additive (attr := simp)]

中文:
定义 constSMul
  签名: (c : G)
  定义体: MulAction.toPerm c
  isometry_toFun := isometry_smul X c

@[to_additive (attr := simp)]

Depends on / 依赖: MulAction, MulAction.toPerm, toPerm
-/
def constSMul (c : G) : X ≃ᵢ X where
  toEquiv := MulAction.toPerm c
  isometry_toFun := isometry_smul X c

@[to_additive (attr := simp)]
/--
theorem `constSMul_symm` / 定理 `constSMul_symm`

English:
theorem constSMul_symm
  given: (c : G)
  statement: (constSMul c : X ≃ᵢ X).symm = constSMul c⁻¹
  proof: ext fun _ => rfl

中文:
定理 constSMul_symm
  条件: (c : G)
  结论: (constSMul c : X ≃ᵢ X).symm = constSMul c⁻¹
  证明: ext fun _ => rfl
-/
theorem constSMul_symm (c : G) : (constSMul c : X ≃ᵢ X).symm = constSMul c⁻¹ :=
  ext fun _ => rfl

variable [PseudoEMetricSpace G]

/-- Multiplication `y ↦ x * y` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) /-- Addition `y ↦ x + y` as an `IsometryEquiv`. -/]
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: [IsIsometricSMul G G] (c : G)
  body: Equiv.mulLeft c
  isometry_toFun := edist_mul_left c

@[to_additive (attr := simp)]

中文:
定义 mulLeft
  签名: [是是ometricSMul G G] (c : G)
  定义体: Equiv.mulLeft c
  isometry_toFun := edist_mul_left c

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.mulLeft, mulLeft
-/
def mulLeft [IsIsometricSMul G G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulLeft c
  isometry_toFun := edist_mul_left c

@[to_additive (attr := simp)]
/--
theorem `mulLeft_symm` / 定理 `mulLeft_symm`

English:
theorem mulLeft_symm
  given: [IsIsometricSMul G G] (x : G)
  proof: constSMul_symm x

中文:
定理 mulLeft_symm
  条件: [是是ometricSMul G G] (x : G)
  证明: constSMul_symm x

Depends on / 依赖: constSMul_symm
-/
theorem mulLeft_symm [IsIsometricSMul G G] (x : G) :
    (mulLeft x).symm = IsometryEquiv.mulLeft x⁻¹ :=
  constSMul_symm x

/-- Multiplication `y ↦ y * x` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) /-- Addition `y ↦ y + x` as an `IsometryEquiv`. -/]
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: [IsIsometricSMul Gᵐᵒᵖ G] (c : G)
  body: Equiv.mulRight c
  isometry_toFun a b := edist_mul_right a b c

@[to_additive (attr := simp)]

中文:
定义 mulRight
  签名: [是是ometricSMul Gᵐᵒᵖ G] (c : G)
  定义体: Equiv.mulRight c
  isometry_toFun a b := edist_mul_right a b c

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.mulRight, mulRight
-/
def mulRight [IsIsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulRight c
  isometry_toFun a b := edist_mul_right a b c

@[to_additive (attr := simp)]
/--
theorem `mulRight_symm` / 定理 `mulRight_symm`

English:
theorem mulRight_symm
  given: [IsIsometricSMul Gᵐᵒᵖ G] (x : G)
  statement: (mulRight x).symm = mulRight x⁻¹
  proof: ext fun _ => rfl

中文:
定理 mulRight_symm
  条件: [是是ometricSMul Gᵐᵒᵖ G] (x : G)
  结论: (mulRight x).symm = mulRight x⁻¹
  证明: ext fun _ => rfl
-/
theorem mulRight_symm [IsIsometricSMul Gᵐᵒᵖ G] (x : G) : (mulRight x).symm = mulRight x⁻¹ :=
  ext fun _ => rfl

/-- Division `y ↦ y / x` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) /-- Subtraction `y ↦ y - x` as an `IsometryEquiv`. -/]
/--
Definition of `divRight` / `divRight` 的定义

English:
definition divRight
  signature: [IsIsometricSMul Gᵐᵒᵖ G] (c : G)
  body: Equiv.divRight c
  isometry_toFun a b := edist_div_right a b c

@[to_additive (attr := simp)]

中文:
定义 divRight
  签名: [是是ometricSMul Gᵐᵒᵖ G] (c : G)
  定义体: Equiv.divRight c
  isometry_toFun a b := edist_div_right a b c

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.divRight, divRight
-/
def divRight [IsIsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divRight c
  isometry_toFun a b := edist_div_right a b c

@[to_additive (attr := simp)]
/--
theorem `divRight_symm` / 定理 `divRight_symm`

English:
theorem divRight_symm
  given: [IsIsometricSMul Gᵐᵒᵖ G] (c : G)
  statement: (divRight c).symm = mulRight c
  proof: ext fun _ => rfl

中文:
定理 divRight_symm
  条件: [是是ometricSMul Gᵐᵒᵖ G] (c : G)
  结论: (divRight c).symm = mulRight c
  证明: ext fun _ => rfl
-/
theorem divRight_symm [IsIsometricSMul Gᵐᵒᵖ G] (c : G) : (divRight c).symm = mulRight c :=
  ext fun _ => rfl

variable [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]

/-- Division `y ↦ x / y` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply symm_apply toEquiv)
  /-- Subtraction `y ↦ x - y` as an `IsometryEquiv`. -/]
/--
Definition of `divLeft` / `divLeft` 的定义

English:
definition divLeft
  signature: (c : G)
  body: Equiv.divLeft c
  isometry_toFun := edist_div_left c

中文:
定义 divLeft
  签名: (c : G)
  定义体: Equiv.divLeft c
  isometry_toFun := edist_div_left c

Depends on / 依赖: Equiv.divLeft, divLeft
-/
def divLeft (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divLeft c
  isometry_toFun := edist_div_left c

variable (G)

/-- Inversion `x ↦ x⁻¹` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) /-- Negation `x ↦ -x` as an `IsometryEquiv`. -/]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : G ≃ᵢ G where
  body: Equiv.inv G
  isometry_toFun := edist_inv_inv

中文:
定义 inv
  签名: : G ≃ᵢ G where
  定义体: Equiv.inv G
  isometry_toFun := edist_inv_inv

Depends on / 依赖: Equiv.inv
-/
def inv : G ≃ᵢ G where
  toEquiv := Equiv.inv G
  isometry_toFun := edist_inv_inv

/--
theorem `inv_symm` / 定理 `inv_symm`

English:
theorem inv_symm
  statement: (inv G).symm = inv G
  proof: rfl

中文:
定理 inv_symm
  结论: (inv G).symm = inv G
  证明: rfl
-/
@[to_additive (attr := simp)] theorem inv_symm : (inv G).symm = inv G := rfl

end IsometryEquiv

namespace Metric

@[to_additive (attr := simp)]
/--
theorem `smul_eball` / 定理 `smul_eball`

English:
theorem smul_eball
  given: (c : G) (x : X) (r : Real>=0∞)
  proof: (IsometryEquiv.constSMul c).image_eball _ _

@[to_additive (attr := simp)]

中文:
定理 smul_eball
  条件: (c : G) (x : X) (r : 实数>=0∞)
  证明: (IsometryEquiv.constSMul c).image_eball _ _

@[to_additive (attr := simp)]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.constSMul, constSMul, image_eball
-/
theorem smul_eball (c : G) (x : X) (r : Real>=0∞) :
    c • eball x r = eball (c • x) r :=
  (IsometryEquiv.constSMul c).image_eball _ _

@[to_additive (attr := simp)]
/--
theorem `preimage_smul_eball` / 定理 `preimage_smul_eball`

English:
theorem preimage_smul_eball
  given: (c : G) (x : X) (r : Real>=0∞)
  proof: by
  rw [preimage_smul]; rw [smul_eball]

@[to_additive (attr := simp)]

中文:
定理 preimage_smul_eball
  条件: (c : G) (x : X) (r : 实数>=0∞)
  证明: by
  rw [preimage_smul]; rw [smul_eball]

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_smul, smul_eball
-/
theorem preimage_smul_eball (c : G) (x : X) (r : Real>=0∞) :
    (c • ·) ⁻¹' eball x r = eball (c⁻¹ • x) r := by
  rw [preimage_smul]; rw [smul_eball]

@[to_additive (attr := simp)]
/--
theorem `smul_closedEBall` / 定理 `smul_closedEBall`

English:
theorem smul_closedEBall
  given: (c : G) (x : X) (r : Real>=0∞)
  proof: (IsometryEquiv.constSMul c).image_closedEBall _ _

@[to_additive (attr := simp)]

中文:
定理 smul_closedEBall
  条件: (c : G) (x : X) (r : 实数>=0∞)
  证明: (IsometryEquiv.constSMul c).image_closedEBall _ _

@[to_additive (attr := simp)]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.constSMul, constSMul, image_closedEBall
-/
theorem smul_closedEBall (c : G) (x : X) (r : Real>=0∞) :
    c • closedEBall x r = closedEBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_closedEBall _ _

@[to_additive (attr := simp)]
/--
theorem `preimage_smul_closedEBall` / 定理 `preimage_smul_closedEBall`

English:
theorem preimage_smul_closedEBall
  given: (c : G) (x : X) (r : Real>=0∞)
  proof: by
  rw [preimage_smul]; rw [smul_closedEBall]

中文:
定理 preimage_smul_closedEBall
  条件: (c : G) (x : X) (r : 实数>=0∞)
  证明: by
  rw [preimage_smul]; rw [smul_closedEBall]

Depends on / 依赖: preimage_smul, smul_closedEBall
-/
theorem preimage_smul_closedEBall (c : G) (x : X) (r : Real>=0∞) :
    (c • ·) ⁻¹' closedEBall x r = closedEBall (c⁻¹ • x) r := by
  rw [preimage_smul]; rw [smul_closedEBall]

variable [PseudoEMetricSpace G]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_left_eball` / 定理 `preimage_mul_left_eball`

English:
theorem preimage_mul_left_eball
  given: [IsIsometricSMul G G] (a b : G) (r : Real>=0∞)
  proof: preimage_smul_eball a b r

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_left_eball
  条件: [是是ometricSMul G G] (a b : G) (r : 实数>=0∞)
  证明: preimage_smul_eball a b r

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_smul_eball
-/
theorem preimage_mul_left_eball [IsIsometricSMul G G] (a b : G) (r : Real>=0∞) :
    (a * ·) ⁻¹' eball b r = eball (a⁻¹ * b) r :=
  preimage_smul_eball a b r

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_right_eball` / 定理 `preimage_mul_right_eball`

English:
theorem preimage_mul_right_eball
  given: [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real>=0∞)
  proof: by
  rw [div_eq_mul_inv]
  exact preimage_smul_eball (MulOpposite.op a) b r

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_right_eball
  条件: [是是ometricSMul Gᵐᵒᵖ G] (a b : G) (r : 实数>=0∞)
  证明: by
  rw [div_eq_mul_inv]
  exact preimage_smul_eball (MulOpposite.op a) b r

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op, div_eq_mul_inv, preimage_smul_eball
-/
theorem preimage_mul_right_eball [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real>=0∞) :
    (fun x => x * a) ⁻¹' eball b r = eball (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_eball (MulOpposite.op a) b r

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_left_closedEBall` / 定理 `preimage_mul_left_closedEBall`

English:
theorem preimage_mul_left_closedEBall
  given: [IsIsometricSMul G G] (a b : G) (r : Real>=0∞)
  proof: preimage_smul_closedEBall a b r

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_left_closedEBall
  条件: [是是ometricSMul G G] (a b : G) (r : 实数>=0∞)
  证明: preimage_smul_closedEBall a b r

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_smul_closedEBall
-/
theorem preimage_mul_left_closedEBall [IsIsometricSMul G G] (a b : G) (r : Real>=0∞) :
    (a * ·) ⁻¹' closedEBall b r = closedEBall (a⁻¹ * b) r :=
  preimage_smul_closedEBall a b r

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_right_closedEBall` / 定理 `preimage_mul_right_closedEBall`

English:
theorem preimage_mul_right_closedEBall
  given: [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real>=0∞)
  proof: by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedEBall (MulOpposite.op a) b r

中文:
定理 preimage_mul_right_closedEBall
  条件: [是是ometricSMul Gᵐᵒᵖ G] (a b : G) (r : 实数>=0∞)
  证明: by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedEBall (MulOpposite.op a) b r

Depends on / 依赖: MulOpposite, MulOpposite.op, div_eq_mul_inv, preimage_smul_closedEBall
-/
theorem preimage_mul_right_closedEBall [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real>=0∞) :
    (fun x => x * a) ⁻¹' closedEBall b r = closedEBall (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedEBall (MulOpposite.op a) b r

end Metric

end EMetric

namespace EMetric
open Metric

@[deprecated (since := "2026-01-24")]
alias vadd_ball := vadd_eball

@[to_additive existing, deprecated (since := "2026-01-24")]
alias smul_ball := smul_eball

@[deprecated (since := "2026-01-24")] alias preimage_vadd_ball := preimage_vadd_eball

@[to_additive existing, deprecated (since := "2026-01-24")]
alias preimage_smul_ball := preimage_smul_eball

@[deprecated (since := "2026-01-24")]
alias vadd_closedBall := vadd_closedEBall

@[to_additive existing, deprecated (since := "2026-01-24")]
alias smul_closedBall := smul_closedEBall

@[deprecated (since := "2026-01-24")]
alias preimage_vadd_closedBall := preimage_vadd_closedEBall

@[to_additive existing, deprecated (since := "2026-01-24")]
alias preimage_smul_closedBall := preimage_smul_closedEBall

@[deprecated (since := "2026-01-24")]
alias preimage_add_left_ball := preimage_add_left_eball

@[to_additive existing, deprecated (since := "2026-01-24")]
alias preimage_mul_left_ball := preimage_mul_left_eball

@[deprecated (since := "2026-01-24")]
alias preimage_add_right_ball := preimage_add_right_eball

@[to_additive existing, deprecated (since := "2026-01-24")]
alias preimage_mul_right_ball := preimage_mul_right_eball

@[deprecated (since := "2026-01-24")]
alias preimage_add_left_closedBall := preimage_add_left_closedEBall

@[to_additive existing, deprecated (since := "2026-01-24")]
alias preimage_mul_left_closedBall := preimage_mul_left_closedEBall

@[deprecated (since := "2026-01-24")]
alias preimage_add_right_closedBall := preimage_add_right_closedEBall

@[to_additive existing, deprecated (since := "2026-01-24")]
alias preimage_mul_right_closedBall := preimage_mul_right_closedEBall

end EMetric

@[to_additive (attr := simp)]
/--
theorem `dist_smul` / 定理 `dist_smul`

English:
theorem dist_smul
  given: [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X)
  proof: (isometry_smul X c).dist_eq x y

@[to_additive (attr := simp)]

中文:
定理 dist_smul
  条件: [伪度量空间 X] [标量乘法 M X] [是是ometricSMul M X] (c : M) (x y : X)
  证明: (isometry_smul X c).dist_eq x y

@[to_additive (attr := simp)]

Depends on / 依赖: dist_eq, isometry_smul
-/
theorem dist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X) :
    dist (c • x) (c • y) = dist x y :=
  (isometry_smul X c).dist_eq x y

@[to_additive (attr := simp)]
/--
theorem `nndist_smul` / 定理 `nndist_smul`

English:
theorem nndist_smul
  given: [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X)
  proof: (isometry_smul X c).nndist_eq x y

@[to_additive (attr := simp)]

中文:
定理 nndist_smul
  条件: [伪度量空间 X] [标量乘法 M X] [是是ometricSMul M X] (c : M) (x y : X)
  证明: (isometry_smul X c).nndist_eq x y

@[to_additive (attr := simp)]

Depends on / 依赖: isometry_smul, nndist_eq
-/
theorem nndist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X) :
    nndist (c • x) (c • y) = nndist x y :=
  (isometry_smul X c).nndist_eq x y

@[to_additive (attr := simp)]
/--
theorem `diam_smul` / 定理 `diam_smul`

English:
theorem diam_smul
  given: [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (s : Set X)
  proof: (isometry_smul _ _).diam_image s

@[to_additive (attr := simp)]

中文:
定理 diam_smul
  条件: [伪度量空间 X] [标量乘法 M X] [是是ometricSMul M X] (c : M) (s : 集合 X)
  证明: (isometry_smul _ _).diam_image s

@[to_additive (attr := simp)]

Depends on / 依赖: diam_image, isometry_smul
-/
theorem diam_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (s : Set X) :
    Metric.diam (c • s) = Metric.diam s :=
  (isometry_smul _ _).diam_image s

@[to_additive (attr := simp)]
/--
theorem `dist_mul_left` / 定理 `dist_mul_left`

English:
theorem dist_mul_left
  given: [PseudoMetricSpace M] [Mul M] [IsIsometricSMul M M] (a b c : M)
  proof: dist_smul a b c

@[to_additive (attr := simp)]

中文:
定理 dist_mul_left
  条件: [伪度量空间 M] [乘法 M] [是是ometricSMul M M] (a b c : M)
  证明: dist_smul a b c

@[to_additive (attr := simp)]

Depends on / 依赖: dist_smul
-/
theorem dist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricSMul M M] (a b c : M) :
    dist (a * b) (a * c) = dist b c :=
  dist_smul a b c

@[to_additive (attr := simp)]
/--
theorem `nndist_mul_left` / 定理 `nndist_mul_left`

English:
theorem nndist_mul_left
  given: [PseudoMetricSpace M] [Mul M] [IsIsometricSMul M M] (a b c : M)
  proof: nndist_smul a b c

@[to_additive (attr := simp)]

中文:
定理 nndist_mul_left
  条件: [伪度量空间 M] [乘法 M] [是是ometricSMul M M] (a b c : M)
  证明: nndist_smul a b c

@[to_additive (attr := simp)]

Depends on / 依赖: nndist_smul
-/
theorem nndist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricSMul M M] (a b c : M) :
    nndist (a * b) (a * c) = nndist b c :=
  nndist_smul a b c

@[to_additive (attr := simp)]
/--
theorem `dist_mul_right` / 定理 `dist_mul_right`

English:
theorem dist_mul_right
  given: [Mul M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a b c : M)
  proof: dist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]

中文:
定理 dist_mul_right
  条件: [乘法 M] [伪度量空间 M] [是是ometricSMul Mᵐᵒᵖ M] (a b c : M)
  证明: dist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op, dist_smul
-/
theorem dist_mul_right [Mul M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    dist (a * c) (b * c) = dist a b :=
  dist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]
/--
theorem `nndist_mul_right` / 定理 `nndist_mul_right`

English:
theorem nndist_mul_right
  given: [PseudoMetricSpace M] [Mul M] [IsIsometricSMul Mᵐᵒᵖ M] (a b c : M)
  proof: nndist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]

中文:
定理 nndist_mul_right
  条件: [伪度量空间 M] [乘法 M] [是是ometricSMul Mᵐᵒᵖ M] (a b c : M)
  证明: nndist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op, nndist_smul
-/
theorem nndist_mul_right [PseudoMetricSpace M] [Mul M] [IsIsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    nndist (a * c) (b * c) = nndist a b :=
  nndist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]
/--
theorem `dist_div_right` / 定理 `dist_div_right`

English:
theorem dist_div_right
  statement: [DivInvMonoid M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
  proof: by simp only [div_eq_mul_inv, dist_mul_right]

@[to_additive (attr := simp)]

中文:
定理 dist_div_right
  结论: [除逆幺半群 M] [伪度量空间 M] [是是ometricSMul Mᵐᵒᵖ M]
  证明: by simp only [div_eq_mul_inv, dist_mul_right]

@[to_additive (attr := simp)]

Depends on / 依赖: dist_mul_right, div_eq_mul_inv
-/
theorem dist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : dist (a / c) (b / c) = dist a b := by simp only [div_eq_mul_inv, dist_mul_right]

@[to_additive (attr := simp)]
/--
theorem `nndist_div_right` / 定理 `nndist_div_right`

English:
theorem nndist_div_right
  statement: [DivInvMonoid M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
  proof: by
  simp only [div_eq_mul_inv, nndist_mul_right]

@[to_additive (attr := simp)]

中文:
定理 nndist_div_right
  结论: [除逆幺半群 M] [伪度量空间 M] [是是ometricSMul Mᵐᵒᵖ M]
  证明: by
  simp only [div_eq_mul_inv, nndist_mul_right]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, nndist_mul_right
-/
theorem nndist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : nndist (a / c) (b / c) = nndist a b := by
  simp only [div_eq_mul_inv, nndist_mul_right]

@[to_additive (attr := simp)]
/--
theorem `dist_inv_inv` / 定理 `dist_inv_inv`

English:
theorem dist_inv_inv
  statement: [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  proof: (IsometryEquiv.inv G).dist_eq a b

@[to_additive (attr := simp)]

中文:
定理 dist_inv_inv
  结论: [群 G] [伪度量空间 G] [是是ometricSMul G G]
  证明: (IsometryEquiv.inv G).dist_eq a b

@[to_additive (attr := simp)]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.inv, dist_eq
-/
theorem dist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b :=
  (IsometryEquiv.inv G).dist_eq a b

@[to_additive (attr := simp)]
/--
theorem `nndist_inv_inv` / 定理 `nndist_inv_inv`

English:
theorem nndist_inv_inv
  statement: [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  proof: (IsometryEquiv.inv G).nndist_eq a b

@[to_additive (attr := simp)]

中文:
定理 nndist_inv_inv
  结论: [群 G] [伪度量空间 G] [是是ometricSMul G G]
  证明: (IsometryEquiv.inv G).nndist_eq a b

@[to_additive (attr := simp)]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.inv, nndist_eq
-/
theorem nndist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b :=
  (IsometryEquiv.inv G).nndist_eq a b

@[to_additive (attr := simp)]
/--
theorem `dist_div_left` / 定理 `dist_div_left`

English:
theorem dist_div_left
  statement: [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 dist_div_left
  结论: [群 G] [伪度量空间 G] [是是ometricSMul G G]
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem dist_div_left [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [IsIsometricSMul Gᵐᵒᵖ G] (a b c : G) : dist (a / b) (a / c) = dist b c := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `nndist_div_left` / 定理 `nndist_div_left`

English:
theorem nndist_div_left
  statement: [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  proof: by
  simp [div_eq_mul_inv]

中文:
定理 nndist_div_left
  结论: [群 G] [伪度量空间 G] [是是ometricSMul G G]
  证明: by
  simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
theorem nndist_div_left [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [IsIsometricSMul Gᵐᵒᵖ G] (a b c : G) : nndist (a / b) (a / c) = nndist b c := by
  simp [div_eq_mul_inv]

/-- If `G` acts isometrically on `X`, then the image of a bounded set in `X` under scalar
multiplication by `c : G` is bounded. See also `Bornology.IsBounded.smul₀` for a similar lemma about
normed spaces. -/
@[to_additive /-- Given an additive isometric action of `G` on `X`, the image of a bounded set in
`X` under translation by `c : G` is bounded. -/]
/--
theorem `Bornology.IsBounded.smul` / 定理 `Bornology.IsBounded.smul`

English:
theorem Bornology.IsBounded.smul
  statement: [PseudoMetricSpace X] [SMul G X] [IsIsometricSMul G X] {s : Set X}
  proof: (isometry_smul X c).lipschitz.isBounded_image hs

中文:
定理 有界结构.IsBounded.smul
  结论: [伪度量空间 X] [标量乘法 G X] [是是ometricSMul G X] {s : 集合 X}
  证明: (isometry_smul X c).lipschitz.isBounded_image hs

Depends on / 依赖: isBounded_image, isometry_smul, lipschitz, lipschitz.isBounded_image
-/
theorem Bornology.IsBounded.smul [PseudoMetricSpace X] [SMul G X] [IsIsometricSMul G X] {s : Set X}
    (hs : IsBounded s) (c : G) : IsBounded (c • s) :=
  (isometry_smul X c).lipschitz.isBounded_image hs

namespace Metric

variable [PseudoMetricSpace X] [Group G] [MulAction G X] [IsIsometricSMul G X]

@[to_additive (attr := simp)]
/--
theorem `smul_ball` / 定理 `smul_ball`

English:
theorem smul_ball
  given: (c : G) (x : X) (r : Real)
  statement: c • ball x r = ball (c • x) r
  proof: (IsometryEquiv.constSMul c).image_ball _ _

@[to_additive (attr := simp)]

中文:
定理 smul_ball
  条件: (c : G) (x : X) (r : 实数)
  结论: c • ball x r = ball (c • x) r
  证明: (IsometryEquiv.constSMul c).image_ball _ _

@[to_additive (attr := simp)]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.constSMul, constSMul, image_ball
-/
theorem smul_ball (c : G) (x : X) (r : Real) : c • ball x r = ball (c • x) r :=
  (IsometryEquiv.constSMul c).image_ball _ _

@[to_additive (attr := simp)]
/--
theorem `preimage_smul_ball` / 定理 `preimage_smul_ball`

English:
theorem preimage_smul_ball
  given: (c : G) (x : X) (r : Real)
  statement: (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r
  proof: by
  rw [preimage_smul]; rw [smul_ball]

@[to_additive (attr := simp)]

中文:
定理 preimage_smul_ball
  条件: (c : G) (x : X) (r : 实数)
  结论: (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r
  证明: by
  rw [preimage_smul]; rw [smul_ball]

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_smul, smul_ball
-/
theorem preimage_smul_ball (c : G) (x : X) (r : Real) : (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r := by
  rw [preimage_smul]; rw [smul_ball]

@[to_additive (attr := simp)]
/--
theorem `smul_closedBall` / 定理 `smul_closedBall`

English:
theorem smul_closedBall
  given: (c : G) (x : X) (r : Real)
  statement: c • closedBall x r = closedBall (c • x) r
  proof: (IsometryEquiv.constSMul c).image_closedBall _ _

@[to_additive (attr := simp)]

中文:
定理 smul_closedBall
  条件: (c : G) (x : X) (r : 实数)
  结论: c • closedBall x r = closedBall (c • x) r
  证明: (IsometryEquiv.constSMul c).image_closedBall _ _

@[to_additive (attr := simp)]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.constSMul, constSMul, image_closedBall
-/
theorem smul_closedBall (c : G) (x : X) (r : Real) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_closedBall _ _

@[to_additive (attr := simp)]
/--
theorem `preimage_smul_closedBall` / 定理 `preimage_smul_closedBall`

English:
theorem preimage_smul_closedBall
  given: (c : G) (x : X) (r : Real)
  proof: by rw [preimage_smul, smul_closedBall]

@[to_additive (attr := simp)]

中文:
定理 preimage_smul_closedBall
  条件: (c : G) (x : X) (r : 实数)
  证明: by rw [preimage_smul, smul_closedBall]

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_smul, smul_closedBall
-/
theorem preimage_smul_closedBall (c : G) (x : X) (r : Real) :
    (c • ·) ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by rw [preimage_smul, smul_closedBall]

@[to_additive (attr := simp)]
/--
theorem `smul_sphere` / 定理 `smul_sphere`

English:
theorem smul_sphere
  given: (c : G) (x : X) (r : Real)
  statement: c • sphere x r = sphere (c • x) r
  proof: (IsometryEquiv.constSMul c).image_sphere _ _

@[to_additive (attr := simp)]

中文:
定理 smul_sphere
  条件: (c : G) (x : X) (r : 实数)
  结论: c • sphere x r = sphere (c • x) r
  证明: (IsometryEquiv.constSMul c).image_sphere _ _

@[to_additive (attr := simp)]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.constSMul, constSMul, image_sphere
-/
theorem smul_sphere (c : G) (x : X) (r : Real) : c • sphere x r = sphere (c • x) r :=
  (IsometryEquiv.constSMul c).image_sphere _ _

@[to_additive (attr := simp)]
/--
theorem `preimage_smul_sphere` / 定理 `preimage_smul_sphere`

English:
theorem preimage_smul_sphere
  given: (c : G) (x : X) (r : Real)
  proof: by rw [preimage_smul, smul_sphere]

中文:
定理 preimage_smul_sphere
  条件: (c : G) (x : X) (r : 实数)
  证明: by rw [preimage_smul, smul_sphere]

Depends on / 依赖: preimage_smul, smul_sphere
-/
theorem preimage_smul_sphere (c : G) (x : X) (r : Real) :
    (c • ·) ⁻¹' sphere x r = sphere (c⁻¹ • x) r := by rw [preimage_smul, smul_sphere]

variable [PseudoMetricSpace G]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_left_ball` / 定理 `preimage_mul_left_ball`

English:
theorem preimage_mul_left_ball
  given: [IsIsometricSMul G G] (a b : G) (r : Real)
  proof: preimage_smul_ball a b r

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_left_ball
  条件: [是是ometricSMul G G] (a b : G) (r : 实数)
  证明: preimage_smul_ball a b r

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_smul_ball
-/
theorem preimage_mul_left_ball [IsIsometricSMul G G] (a b : G) (r : Real) :
    (a * ·) ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_right_ball` / 定理 `preimage_mul_right_ball`

English:
theorem preimage_mul_right_ball
  given: [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real)
  proof: by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_right_ball
  条件: [是是ometricSMul Gᵐᵒᵖ G] (a b : G) (r : 实数)
  证明: by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r

@[to_additive (attr := simp)]

Depends on / 依赖: MulOpposite, MulOpposite.op, div_eq_mul_inv, preimage_smul_ball
-/
theorem preimage_mul_right_ball [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_left_closedBall` / 定理 `preimage_mul_left_closedBall`

English:
theorem preimage_mul_left_closedBall
  given: [IsIsometricSMul G G] (a b : G) (r : Real)
  proof: preimage_smul_closedBall a b r

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_left_closedBall
  条件: [是是ometricSMul G G] (a b : G) (r : 实数)
  证明: preimage_smul_closedBall a b r

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_smul_closedBall
-/
theorem preimage_mul_left_closedBall [IsIsometricSMul G G] (a b : G) (r : Real) :
    (a * ·) ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_right_closedBall` / 定理 `preimage_mul_right_closedBall`

English:
theorem preimage_mul_right_closedBall
  given: [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real)
  proof: by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedBall (MulOpposite.op a) b r

中文:
定理 preimage_mul_right_closedBall
  条件: [是是ometricSMul Gᵐᵒᵖ G] (a b : G) (r : 实数)
  证明: by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedBall (MulOpposite.op a) b r

Depends on / 依赖: MulOpposite, MulOpposite.op, div_eq_mul_inv, preimage_smul_closedBall
-/
theorem preimage_mul_right_closedBall [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedBall (MulOpposite.op a) b r

end Metric

section Instances

variable {Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [SMul M X]
  [IsIsometricSMul M X]

@[to_additive]
/--
Instance `Prod.instIsIsometricSMul` / 实例 `Prod.instIsIsometricSMul`

English:
instance Prod.instIsIsometricSMul
  signature: [SMul M Y] [IsIsometricSMul M Y]
  body: ⟨fun c => (isometry_smul X c).prodMap (isometry_smul Y c)⟩

@[to_additive]

中文:
实例 积类型.instIsIsometricSMul
  签名: [标量乘法 M Y] [是是ometricSMul M Y]
  定义体: ⟨fun c => (isometry_smul X c).prodMap (isometry_smul Y c)⟩

@[to_additive]

Depends on / 依赖: isometry_smul, prodMap
-/
instance Prod.instIsIsometricSMul [SMul M Y] [IsIsometricSMul M Y] : IsIsometricSMul M (X × Y) :=
  ⟨fun c => (isometry_smul X c).prodMap (isometry_smul Y c)⟩

@[to_additive]
/--
Instance `Prod.isIsometricSMul'` / 实例 `Prod.isIsometricSMul'`

English:
instance Prod.isIsometricSMul'
  signature: {N} [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] [Mul N]
  body: ⟨fun c => (isometry_smul M c.1).prodMap (isometry_smul N c.2)⟩

@[to_additive]

中文:
实例 积类型.isIsometricSMul'
  签名: {N} [乘法 M] [PseudoEMetric空间 M] [是是ometricSMul M M] [乘法 N]
  定义体: ⟨fun c => (isometry_smul M c.1).prodMap (isometry_smul N c.2)⟩

@[to_additive]

Depends on / 依赖: isometry_smul, prodMap
-/
instance Prod.isIsometricSMul' {N} [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] [Mul N]
    [PseudoEMetricSpace N] [IsIsometricSMul N N] : IsIsometricSMul (M × N) (M × N) :=
  ⟨fun c => (isometry_smul M c.1).prodMap (isometry_smul N c.2)⟩

@[to_additive]
/--
Instance `Prod.isIsometricSMul''` / 实例 `Prod.isIsometricSMul''`

English:
instance Prod.isIsometricSMul''
  signature: {N} [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
  body: ⟨fun c => (isometry_mul_right c.unop.1).prodMap (isometry_mul_right c.unop.2)⟩

@[to_additive]

中文:
实例 积类型.isIsometricSMul''
  签名: {N} [乘法 M] [PseudoEMetric空间 M] [是是ometricSMul Mᵐᵒᵖ M]
  定义体: ⟨fun c => (isometry_mul_right c.unop.1).prodMap (isometry_mul_right c.unop.2)⟩

@[to_additive]

Depends on / 依赖: c.unop, isometry_mul_right, prodMap
-/
instance Prod.isIsometricSMul'' {N} [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
    [Mul N] [PseudoEMetricSpace N] [IsIsometricSMul Nᵐᵒᵖ N] :
    IsIsometricSMul (M × N)ᵐᵒᵖ (M × N) :=
  ⟨fun c => (isometry_mul_right c.unop.1).prodMap (isometry_mul_right c.unop.2)⟩

@[to_additive]
/--
Instance `Units.isIsometricSMul` / 实例 `Units.isIsometricSMul`

English:
instance Units.isIsometricSMul
  signature: [Monoid M]
  body: ⟨fun c => isometry_smul X (c : M)⟩

@[to_additive]

中文:
实例 单位群.isIsometricSMul
  签名: [幺半群 M]
  定义体: ⟨fun c => isometry_smul X (c : M)⟩

@[to_additive]

Depends on / 依赖: isometry_smul
-/
instance Units.isIsometricSMul [Monoid M] : IsIsometricSMul Mˣ X :=
  ⟨fun c => isometry_smul X (c : M)⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIsometricSMul M Xᵐᵒᵖ
  body: ⟨fun c x y => by simpa only using! edist_smul_left c x.unop y.unop⟩

@[to_additive]

中文:
实例 :
  签名: 是是ometricSMul M Xᵐᵒᵖ
  定义体: ⟨fun c x y => by simpa only using! edist_smul_left c x.unop y.unop⟩

@[to_additive]

Depends on / 依赖: edist_smul_left, x.unop, y.unop
-/
instance : IsIsometricSMul M Xᵐᵒᵖ :=
  ⟨fun c x y => by simpa only using! edist_smul_left c x.unop y.unop⟩

@[to_additive]
/--
Instance `ULift.isIsometricSMul` / 实例 `ULift.isIsometricSMul`

English:
instance ULift.isIsometricSMul
  signature: : IsIsometricSMul (ULift M) X
  body: ⟨fun c => by simpa only using! isometry_smul X c.down⟩

@[to_additive]

中文:
实例 类型层提升.isIsometricSMul
  签名: : 是是ometricSMul (类型层提升 M) X
  定义体: ⟨fun c => by simpa only using! isometry_smul X c.down⟩

@[to_additive]

Depends on / 依赖: c.down, isometry_smul
-/
instance ULift.isIsometricSMul : IsIsometricSMul (ULift M) X :=
  ⟨fun c => by simpa only using! isometry_smul X c.down⟩

@[to_additive]
/--
Instance `ULift.isIsometricSMul'` / 实例 `ULift.isIsometricSMul'`

English:
instance ULift.isIsometricSMul'
  signature: : IsIsometricSMul M (ULift X)
  body: ⟨fun c x y => by simpa only using! edist_smul_left c x.1 y.1⟩

@[to_additive]

中文:
实例 类型层提升.isIsometricSMul'
  签名: : 是是ometricSMul M (类型层提升 X)
  定义体: ⟨fun c x y => by simpa only using! edist_smul_left c x.1 y.1⟩

@[to_additive]

Depends on / 依赖: edist_smul_left
-/
instance ULift.isIsometricSMul' : IsIsometricSMul M (ULift X) :=
  ⟨fun c x y => by simpa only using! edist_smul_left c x.1 y.1⟩

@[to_additive]
instance {ι} {X : ι -> Type*} [Fintype ι] [forall i, SMul M (X i)] [forall i, PseudoEMetricSpace (X i)]
    [forall i, IsIsometricSMul M (X i)] : IsIsometricSMul M (forall i, X i) :=
  ⟨fun c => .piMap (fun _ => (c • ·)) fun i => isometry_smul (X i) c⟩

@[to_additive]
/--
Instance `Pi.isIsometricSMul'` / 实例 `Pi.isIsometricSMul'`

English:
instance Pi.isIsometricSMul'
  signature: {ι} {M X : ι -> Type*} [Fintype ι] [forall i, SMul (M i) (X i)]
  body: ⟨fun c => .piMap (fun i => (c i • ·)) fun _ => isometry_smul _ _⟩

@[to_additive]

中文:
实例 依赖函数类型.isIsometricSMul'
  签名: {ι} {M X : ι -> 类型} [有限类型 ι] [对任意 i, 标量乘法 (M i) (X i)]
  定义体: ⟨fun c => .piMap (fun i => (c i • ·)) fun _ => isometry_smul _ _⟩

@[to_additive]

Depends on / 依赖: isometry_smul
-/
instance Pi.isIsometricSMul' {ι} {M X : ι -> Type*} [Fintype ι] [forall i, SMul (M i) (X i)]
    [forall i, PseudoEMetricSpace (X i)] [forall i, IsIsometricSMul (M i) (X i)] :
    IsIsometricSMul (forall i, M i) (forall i, X i) :=
  ⟨fun c => .piMap (fun i => (c i • ·)) fun _ => isometry_smul _ _⟩

@[to_additive]
/--
Instance `Pi.isIsometricSMul''` / 实例 `Pi.isIsometricSMul''`

English:
instance Pi.isIsometricSMul''
  signature: {ι} {M : ι -> Type*} [Fintype ι] [forall i, Mul (M i)]
  body: ⟨fun c => .piMap (fun i (x : M i) => x * c.unop i) fun _ => isometry_mul_right _⟩

中文:
实例 依赖函数类型.isIsometricSMul''
  签名: {ι} {M : ι -> 类型} [有限类型 ι] [对任意 i, 乘法 (M i)]
  定义体: ⟨fun c => .piMap (fun i (x : M i) => x * c.unop i) fun _ => isometry_mul_right _⟩

Depends on / 依赖: c.unop, isometry_mul_right
-/
instance Pi.isIsometricSMul'' {ι} {M : ι -> Type*} [Fintype ι] [forall i, Mul (M i)]
    [forall i, PseudoEMetricSpace (M i)] [forall i, IsIsometricSMul (M i)ᵐᵒᵖ (M i)] :
    IsIsometricSMul (forall i, M i)ᵐᵒᵖ (forall i, M i) :=
  ⟨fun c => .piMap (fun i (x : M i) => x * c.unop i) fun _ => isometry_mul_right _⟩

/--
Instance `Additive.isIsIsometricVAdd` / 实例 `Additive.isIsIsometricVAdd`

English:
instance Additive.isIsIsometricVAdd
  signature: : IsIsometricVAdd (Additive M) X
  body: ⟨fun c => isometry_smul X c.toMul⟩

中文:
实例 加性.isIsIsometricVAdd
  签名: : 是是ometricVAdd (加性 M) X
  定义体: ⟨fun c => isometry_smul X c.toMul⟩

Depends on / 依赖: c.toMul, isometry_smul
-/
instance Additive.isIsIsometricVAdd : IsIsometricVAdd (Additive M) X :=
  ⟨fun c => isometry_smul X c.toMul⟩

/--
Instance `Additive.isIsIsometricVAdd'` / 实例 `Additive.isIsIsometricVAdd'`

English:
instance Additive.isIsIsometricVAdd'
  signature: [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M]
  body: ⟨fun c x y => edist_smul_left c.toMul x.toMul y.toMul⟩

中文:
实例 加性.isIsIsometricVAdd'
  签名: [乘法 M] [PseudoEMetric空间 M] [是是ometricSMul M M]
  定义体: ⟨fun c x y => edist_smul_left c.toMul x.toMul y.toMul⟩

Depends on / 依赖: c.toMul, edist_smul_left, x.toMul, y.toMul
-/
instance Additive.isIsIsometricVAdd' [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] :
    IsIsometricVAdd (Additive M) (Additive M) :=
  ⟨fun c x y => edist_smul_left c.toMul x.toMul y.toMul⟩

/--
Instance `Additive.isIsIsometricVAdd''` / 实例 `Additive.isIsIsometricVAdd''`

English:
instance Additive.isIsIsometricVAdd''
  signature: [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
  body: ⟨fun c x y => edist_smul_left (MulOpposite.op c.unop.toMul) x.toMul y.toMul⟩

中文:
实例 加性.isIsIsometricVAdd''
  签名: [乘法 M] [PseudoEMetric空间 M] [是是ometricSMul Mᵐᵒᵖ M]
  定义体: ⟨fun c x y => edist_smul_left (MulOpposite.op c.unop.toMul) x.toMul y.toMul⟩

Depends on / 依赖: MulOpposite, MulOpposite.op, c.unop.toMul, edist_smul_left, x.toMul, y.toMul
-/
instance Additive.isIsIsometricVAdd'' [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] :
    IsIsometricVAdd (Additive M)ᵃᵒᵖ (Additive M) :=
  ⟨fun c x y => edist_smul_left (MulOpposite.op c.unop.toMul) x.toMul y.toMul⟩

/--
Instance `Multiplicative.isIsometricSMul` / 实例 `Multiplicative.isIsometricSMul`

English:
instance Multiplicative.isIsometricSMul
  signature: {M X} [VAdd M X] [PseudoEMetricSpace X]
  body: ⟨fun c => isometry_vadd X c.toAdd⟩

中文:
实例 Multiplicative.isIsometricSMul
  签名: {M X} [向量加法 M X] [PseudoEMetric空间 X]
  定义体: ⟨fun c => isometry_vadd X c.toAdd⟩

Depends on / 依赖: c.toAdd, isometry_vadd
-/
instance Multiplicative.isIsometricSMul {M X} [VAdd M X] [PseudoEMetricSpace X]
    [IsIsometricVAdd M X] : IsIsometricSMul (Multiplicative M) X :=
  ⟨fun c => isometry_vadd X c.toAdd⟩

/--
Instance `Multiplicative.isIsometricSMul'` / 实例 `Multiplicative.isIsometricSMul'`

English:
instance Multiplicative.isIsometricSMul'
  signature: [Add M] [PseudoEMetricSpace M] [IsIsometricVAdd M M]
  body: ⟨fun c x y => edist_vadd_left c.toAdd x.toAdd y.toAdd⟩

中文:
实例 Multiplicative.isIsometricSMul'
  签名: [加法 M] [PseudoEMetric空间 M] [是是ometricVAdd M M]
  定义体: ⟨fun c x y => edist_vadd_left c.toAdd x.toAdd y.toAdd⟩

Depends on / 依赖: c.toAdd, edist_vadd_left, x.toAdd, y.toAdd
-/
instance Multiplicative.isIsometricSMul' [Add M] [PseudoEMetricSpace M] [IsIsometricVAdd M M] :
    IsIsometricSMul (Multiplicative M) (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left c.toAdd x.toAdd y.toAdd⟩

/--
Instance `Multiplicative.isIsIsometricVAdd''` / 实例 `Multiplicative.isIsIsometricVAdd''`

English:
instance Multiplicative.isIsIsometricVAdd''
  signature: [Add M] [PseudoEMetricSpace M]
  body: ⟨fun c x y => edist_vadd_left (AddOpposite.op c.unop.toAdd) x.toAdd y.toAdd⟩

中文:
实例 Multiplicative.isIsIsometricVAdd''
  签名: [加法 M] [PseudoEMetric空间 M]
  定义体: ⟨fun c x y => edist_vadd_left (AddOpposite.op c.unop.toAdd) x.toAdd y.toAdd⟩

Depends on / 依赖: AddOpposite, AddOpposite.op, c.unop.toAdd, edist_vadd_left, x.toAdd, y.toAdd
-/
instance Multiplicative.isIsIsometricVAdd'' [Add M] [PseudoEMetricSpace M]
    [IsIsometricVAdd Mᵃᵒᵖ M] : IsIsometricSMul (Multiplicative M)ᵐᵒᵖ (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left (AddOpposite.op c.unop.toAdd) x.toAdd y.toAdd⟩

end Instances
