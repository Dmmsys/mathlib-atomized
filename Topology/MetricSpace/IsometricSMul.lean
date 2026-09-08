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

/-- An additive action is isometric if each map `x ↦ c +ᵥ x` is an isometry. -/
/-
**IsIsometricVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u) → (X : Type w) → [PseudoEMetricSpace X] → [VAdd M X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive action is isometric if each map `x ↦ c +ᵥ x` is an isometry.
-/
class IsIsometricVAdd (X : Type w) [PseudoEMetricSpace X] [VAdd M X] : Prop where
  isometry_vadd (X) : ∀ c : M, Isometry ((c +ᵥ ·) : X → X)

/-- A multiplicative action is isometric if each map `x ↦ c • x` is an isometry. -/
@[to_additive]
/-
**IsIsometricSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u) → (X : Type w) → [PseudoEMetricSpace X] → [SMul M X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative action is isometric if each map `x ↦ c • x` is an isometry.
-/
class IsIsometricSMul (X : Type w) [PseudoEMetricSpace X] [SMul M X] : Prop where
  isometry_smul (X) : ∀ c : M, Isometry ((c • ·) : X → X)

export IsIsometricSMul (isometry_smul)
export IsIsometricVAdd (isometry_vadd)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsIsometricSMul.to_continuousConstSMul [PseudoEMetricSpace X] [SMul M X]
    [IsIsometricSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (isometry_smul X c).continuous⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsIsometricSMul.opposite_of_comm [PseudoEMetricSpace X] [SMul M X]
    [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] [IsIsometricSMul M X] : IsIsometricSMul Mᵐᵒᵖ X :=
  ⟨fun c x y => by simpa only [← op_smul_eq_smul] using! isometry_smul X c.unop x y⟩

variable {M G X}

section EMetric

variable [PseudoEMetricSpace X] [Group G] [MulAction G X] [IsIsometricSMul G X]

@[to_additive (attr := simp)]
/-
**edist_smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_smul_left [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X) : edist
 (c • x) (c • y) = edist x y
参数：c : M；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem edist_smul_left [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X) :
    edist (c • x) (c • y) = edist x y :=
  isometry_smul X c x y

@[to_additive (attr := simp)]
/-
**ediam_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ediam_smul [SMul M X] [IsIsometricSMul M X] (c : M) (s : Set X) : Metric.e
diam (c • s) = Metric.ediam s
参数：c : M；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem ediam_smul [SMul M X] [IsIsometricSMul M X] (c : M) (s : Set X) :
    Metric.ediam (c • s) = Metric.ediam s :=
  (isometry_smul _ _).ediam_image s

@[to_additive]
/-
**isometry_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isometry_mul_left [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] (a 
: M) : Isometry (a * ·)
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem isometry_mul_left [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] (a : M) :
    Isometry (a * ·) :=
  isometry_smul M a

@[to_additive (attr := simp)]
/-
**edist_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_mul_left [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] (a b c
 : M) : edist (a * b) (a * c) = edist b c
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isometry_mul_left`：isometry_mul_left [Mul M] [PseudoEMetricSpace M] [IsI
sometricSMul M M] (a : M) : Isometry (a * ·)
-/
theorem edist_mul_left [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] (a b c : M) :
    edist (a * b) (a * c) = edist b c :=
  isometry_mul_left a b c

@[to_additive]
/-
**isometry_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isometry_mul_right [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
 (a : M) : Isometry fun x => x * a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem isometry_mul_right [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a : M) :
    Isometry fun x => x * a :=
  isometry_smul M (MulOpposite.op a)

@[to_additive (attr := simp)]
/-
**edist_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_mul_right [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a
 b c : M) : edist (a * c) (b * c) = edist a b
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isometry_mul_right`：isometry_mul_right [Mul M] [PseudoEMetricSpace M] [I
sIsometricSMul Mᵐᵒᵖ M] (a : M) : Isometry fun x => x * a
-/
theorem edist_mul_right [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    edist (a * c) (b * c) = edist a b :=
  isometry_mul_right c a b

@[to_additive (attr := simp)]
/-
**edist_div_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_div_right [DivInvMonoid M] [PseudoEMetricSpace M] [IsIsometricSMul M
ᵐᵒᵖ M] (a b c : M) : edist (a / c) (b / c) = edist a b
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `edist_mul_right`：edist_mul_right [Mul M] [PseudoEMetricSpace M] [IsIsome
tricSMul Mᵐᵒᵖ M] (a b c : M) : edist (a * c) (b * c) = edist a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edist_div_right [DivInvMonoid M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : edist (a / c) (b / c) = edist a b := by
  simp only [div_eq_mul_inv, edist_mul_right]

@[to_additive (attr := simp)]
/-
**edist_inv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMu
l Gᵐᵒᵖ G] (a b : G) : edist a⁻¹ b⁻¹ = edist a b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `edist_mul_left`：edist_mul_left [Mul M] [PseudoEMetricSpace M] [IsIsometr
icSMul M M] (a b c : M) : edist (a * b) (a * c) = edist b c
· 使用定理 `edist_mul_right`：edist_mul_right [Mul M] [PseudoEMetricSpace M] [IsIsome
tricSMul Mᵐᵒᵖ M] (a b c : M) : edist (a * c) (b * c) = edist a b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
-/
theorem edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
    (a b : G) : edist a⁻¹ b⁻¹ = edist a b := by
  rw [← edist_mul_left a, ← edist_mul_right _ _ b, mul_inv_cancel, one_mul, inv_mul_cancel_right,
    edist_comm]

@[to_additive]
/-
**isometry_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isometry_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul
 Gᵐᵒᵖ G] : Isometry (Inv.inv : G -> G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_inv_inv`：edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G
] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : edist a⁻¹ b⁻¹ = edist a b
-/
theorem isometry_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G] :
    Isometry (Inv.inv : G → G) :=
  edist_inv_inv

@[to_additive]
/-
**edist_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐ
ᵒᵖ G] (x y : G) : edist x⁻¹ y = edist x y⁻¹
参数：x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `edist_inv_inv`：edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G
] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : edist a⁻¹ b⁻¹ = edist a b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem edist_inv [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
    (x y : G) : edist x⁻¹ y = edist x y⁻¹ := by rw [← edist_inv_inv, inv_inv]

@[to_additive (attr := simp)]
/-
**edist_div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_div_left [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSM
ul Gᵐᵒᵖ G] (a b c : G) : edist (a / b) (a / c) = edist b c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `edist_mul_left`：edist_mul_left [Mul M] [PseudoEMetricSpace M] [IsIsometr
icSMul M M] (a b c : M) : edist (a * b) (a * c) = edist b c
· 使用定理 `edist_inv_inv`：edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G
] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : edist a⁻¹ b⁻¹ = edist a b
-/
theorem edist_div_left [PseudoEMetricSpace G] [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]
    (a b c : G) : edist (a / b) (a / c) = edist b c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, edist_mul_left, edist_inv_inv]

namespace IsometryEquiv

/-- If a group `G` acts on `X` by isometries, then `IsometryEquiv.constSMul` is the isometry of
`X` given by multiplication of a constant element of the group. -/
@[to_additive (attr := simps! toEquiv apply) /-- If an additive group `G` acts on `X` by isometries,
then `IsometryEquiv.constVAdd` is the isometry of `X` given by addition of a constant element of the
group. -/]
/-
**IsometryEquiv.constSMul** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：constSMul (c : G) : X ≃ᵢ X where toEquiv
参数：c : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def constSMul (c : G) : X ≃ᵢ X where
  toEquiv := MulAction.toPerm c
  isometry_toFun := isometry_smul X c

@[to_additive (attr := simp)]
/-
**IsometryEquiv.constSMul_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：constSMul_symm (c : G) : (constSMul c : X ≃ᵢ X).symm = constSMul c⁻¹
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.ext`：ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : forall x, h₁ x = h₂ x) : h₁
 = h₂
-/
theorem constSMul_symm (c : G) : (constSMul c : X ≃ᵢ X).symm = constSMul c⁻¹ :=
  ext fun _ => rfl

variable [PseudoEMetricSpace G]

/-- Multiplication `y ↦ x * y` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) /-- Addition `y ↦ x + y` as an `IsometryEquiv`. -/]
/-
**IsometryEquiv.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：mulLeft [IsIsometricSMul G G] (c : G) : G ≃ᵢ G where toEquiv
参数：c : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication `y ↦ x * y` as an `IsometryEquiv`.
-/
def mulLeft [IsIsometricSMul G G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulLeft c
  isometry_toFun := edist_mul_left c

@[to_additive (attr := simp)]
/-
**IsometryEquiv.mulLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：mulLeft_symm [IsIsometricSMul G G] (x : G) : (mulLeft x).symm = IsometryEq
uiv.mulLeft x⁻¹
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.constSMul_symm`：constSMul_symm (c : G) : (constSMul c : X 
≃ᵢ X).symm = constSMul c⁻¹
-/
theorem mulLeft_symm [IsIsometricSMul G G] (x : G) :
    (mulLeft x).symm = IsometryEquiv.mulLeft x⁻¹ :=
  constSMul_symm x

/-- Multiplication `y ↦ y * x` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) /-- Addition `y ↦ y + x` as an `IsometryEquiv`. -/]
/-
**IsometryEquiv.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：mulRight [IsIsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where toEquiv
参数：c : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication `y ↦ y * x` as an `IsometryEquiv`.
-/
def mulRight [IsIsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.mulRight c
  isometry_toFun a b := edist_mul_right a b c

@[to_additive (attr := simp)]
/-
**IsometryEquiv.mulRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：mulRight_symm [IsIsometricSMul Gᵐᵒᵖ G] (x : G) : (mulRight x).symm = mulRi
ght x⁻¹
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.ext`：ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : forall x, h₁ x = h₂ x) : h₁
 = h₂
-/
theorem mulRight_symm [IsIsometricSMul Gᵐᵒᵖ G] (x : G) : (mulRight x).symm = mulRight x⁻¹ :=
  ext fun _ => rfl

/-- Division `y ↦ y / x` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) /-- Subtraction `y ↦ y - x` as an `IsometryEquiv`. -/]
/-
**IsometryEquiv.divRight** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：divRight [IsIsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where toEquiv
参数：c : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Division `y ↦ y / x` as an `IsometryEquiv`.
-/
def divRight [IsIsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divRight c
  isometry_toFun a b := edist_div_right a b c

@[to_additive (attr := simp)]
/-
**IsometryEquiv.divRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：divRight_symm [IsIsometricSMul Gᵐᵒᵖ G] (c : G) : (divRight c).symm = mulRi
ght c
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.ext`：ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : forall x, h₁ x = h₂ x) : h₁
 = h₂
-/
theorem divRight_symm [IsIsometricSMul Gᵐᵒᵖ G] (c : G) : (divRight c).symm = mulRight c :=
  ext fun _ => rfl

variable [IsIsometricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G]

/-- Division `y ↦ x / y` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply symm_apply toEquiv)
  /-- Subtraction `y ↦ x - y` as an `IsometryEquiv`. -/]
/-
**IsometryEquiv.divLeft** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：divLeft (c : G) : G ≃ᵢ G where toEquiv
参数：c : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `edist_div_left`：edist_div_left [PseudoEMetricSpace G] [IsIsometricSMul G
 G] [IsIsometricSMul Gᵐᵒᵖ G] (a b c : G) : edist (a / b) (a / c) = edist b c
-/
def divLeft (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divLeft c
  isometry_toFun := edist_div_left c

variable (G)

/-- Inversion `x ↦ x⁻¹` as an `IsometryEquiv`. -/
@[to_additive (attr := simps! apply toEquiv) /-- Negation `x ↦ -x` as an `IsometryEquiv`. -/]
/-
**IsometryEquiv.inv** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：inv : G ≃ᵢ G where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `edist_inv_inv`：edist_inv_inv [PseudoEMetricSpace G] [IsIsometricSMul G G
] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : edist a⁻¹ b⁻¹ = edist a b

--- 原说明 ---
Inversion `x ↦ x⁻¹` as an `IsometryEquiv`.
-/
def inv : G ≃ᵢ G where
  toEquiv := Equiv.inv G
  isometry_toFun := edist_inv_inv
/-
**IsometryEquiv.inv_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ (G : Type v) [inst : Group G] [inst_1 : PseudoEMetricSpace G] [inst_2 : 
IsIsometricSMul G G]   [inst_3 : IsIsometricSMul Gᵐᵒᵖ G], (IsometryEquiv.inv G).
symm = IsometryEquiv.inv G
参数：G : Type v；IsometryEquiv.inv G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem inv_symm : (inv G).symm = inv G := rfl

end IsometryEquiv

namespace Metric

@[to_additive (attr := simp)]
/-
**Metric.smul_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：smul_eball (c : G) (x : X) (r : Real>=0∞) : c • eball x r = eball (c • x) 
r
参数：c : G；x : X；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.image_eball`：image_eball (h : α ≃ᵢ β) (x : α) (r : Real>=0
∞) : h '' Metric.eball x r = Metric.eball (h x) r
-/
theorem smul_eball (c : G) (x : X) (r : ℝ≥0∞) :
    c • eball x r = eball (c • x) r :=
  (IsometryEquiv.constSMul c).image_eball _ _

@[to_additive (attr := simp)]
/-
**Metric.preimage_smul_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_smul_eball (c : G) (x : X) (r : Real>=0∞) : (c • ·) ⁻¹' eball x r
 = eball (c⁻¹ • x) r
参数：c : G；x : X；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `Metric.smul_eball`：smul_eball (c : G) (x : X) (r : Real>=0∞) : c • eball
 x r = eball (c • x) r
-/
theorem preimage_smul_eball (c : G) (x : X) (r : ℝ≥0∞) :
    (c • ·) ⁻¹' eball x r = eball (c⁻¹ • x) r := by
  rw [preimage_smul, smul_eball]

@[to_additive (attr := simp)]
/-
**Metric.smul_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：smul_closedEBall (c : G) (x : X) (r : Real>=0∞) : c • closedEBall x r = cl
osedEBall (c • x) r
参数：c : G；x : X；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.image_closedEBall`：image_closedEBall (h : α ≃ᵢ β) (x : α) 
(r : Real>=0∞) : h '' Metric.closedEBall x r = Metric.closedEBall (h x) r
-/
theorem smul_closedEBall (c : G) (x : X) (r : ℝ≥0∞) :
    c • closedEBall x r = closedEBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_closedEBall _ _

@[to_additive (attr := simp)]
/-
**Metric.preimage_smul_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_smul_closedEBall (c : G) (x : X) (r : Real>=0∞) : (c • ·) ⁻¹' clo
sedEBall x r = closedEBall (c⁻¹ • x) r
参数：c : G；x : X；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `Metric.smul_closedEBall`：smul_closedEBall (c : G) (x : X) (r : Real>=0∞)
 : c • closedEBall x r = closedEBall (c • x) r
-/
theorem preimage_smul_closedEBall (c : G) (x : X) (r : ℝ≥0∞) :
    (c • ·) ⁻¹' closedEBall x r = closedEBall (c⁻¹ • x) r := by
  rw [preimage_smul, smul_closedEBall]

variable [PseudoEMetricSpace G]

@[to_additive (attr := simp)]
/-
**Metric.preimage_mul_left_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_mul_left_eball [IsIsometricSMul G G] (a b : G) (r : Real>=0∞) : (
a * ·) ⁻¹' eball b r = eball (a⁻¹ * b) r
参数：a b : G；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.preimage_smul_eball`：preimage_smul_eball (c : G) (x : X) (r : Rea
l>=0∞) : (c • ·) ⁻¹' eball x r = eball (c⁻¹ • x) r
-/
theorem preimage_mul_left_eball [IsIsometricSMul G G] (a b : G) (r : ℝ≥0∞) :
    (a * ·) ⁻¹' eball b r = eball (a⁻¹ * b) r :=
  preimage_smul_eball a b r

@[to_additive (attr := simp)]
/-
**Metric.preimage_mul_right_eball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_mul_right_eball [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real>=0∞)
 : (fun x => x * a) ⁻¹' eball b r = eball (b / a) r
参数：a b : G；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Metric.preimage_smul_eball`：preimage_smul_eball (c : G) (x : X) (r : Rea
l>=0∞) : (c • ·) ⁻¹' eball x r = eball (c⁻¹ • x) r
-/
theorem preimage_mul_right_eball [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
    (fun x => x * a) ⁻¹' eball b r = eball (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_eball (MulOpposite.op a) b r

@[to_additive (attr := simp)]
/-
**Metric.preimage_mul_left_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_mul_left_closedEBall [IsIsometricSMul G G] (a b : G) (r : Real>=0
∞) : (a * ·) ⁻¹' closedEBall b r = closedEBall (a⁻¹ * b) r
参数：a b : G；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.preimage_smul_closedEBall`：preimage_smul_closedEBall (c : G) (x :
 X) (r : Real>=0∞) : (c • ·) ⁻¹' closedEBall x r = closedEBall (c⁻¹ • x) r
-/
theorem preimage_mul_left_closedEBall [IsIsometricSMul G G] (a b : G) (r : ℝ≥0∞) :
    (a * ·) ⁻¹' closedEBall b r = closedEBall (a⁻¹ * b) r :=
  preimage_smul_closedEBall a b r

@[to_additive (attr := simp)]
/-
**Metric.preimage_mul_right_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_mul_right_closedEBall [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Rea
l>=0∞) : (fun x => x * a) ⁻¹' closedEBall b r = closedEBall (b / a) r
参数：a b : G；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Metric.preimage_smul_closedEBall`：preimage_smul_closedEBall (c : G) (x :
 X) (r : Real>=0∞) : (c • ·) ⁻¹' closedEBall x r = closedEBall (c⁻¹ • x) r
-/
theorem preimage_mul_right_closedEBall [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
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
/-
**dist_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (
x y : X) : dist (c • x) (c • y) = dist x y
参数：c : M；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem dist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X) :
    dist (c • x) (c • y) = dist x y :=
  (isometry_smul X c).dist_eq x y

@[to_additive (attr := simp)]
/-
**nndist_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M)
 (x y : X) : nndist (c • x) (c • y) = nndist x y
参数：c : M；x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.nndist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpac
e α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), nnd
ist (f x…
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem nndist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (x y : X) :
    nndist (c • x) (c • y) = nndist x y :=
  (isometry_smul X c).nndist_eq x y

@[to_additive (attr := simp)]
/-
**diam_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：diam_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (
s : Set X) : Metric.diam (c • s) = Metric.diam s
参数：c : M；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem diam_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] (c : M) (s : Set X) :
    Metric.diam (c • s) = Metric.diam s :=
  (isometry_smul _ _).diam_image s

@[to_additive (attr := simp)]
/-
**dist_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricSMul M M] (a b c :
 M) : dist (a * b) (a * c) = dist b c
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_smul`：dist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M
 X] (c : M) (x y : X) : dist (c • x) (c • y) = dist x y
-/
theorem dist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricSMul M M] (a b c : M) :
    dist (a * b) (a * c) = dist b c :=
  dist_smul a b c

@[to_additive (attr := simp)]
/-
**nndist_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricSMul M M] (a b c
 : M) : nndist (a * b) (a * c) = nndist b c
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nndist_smul`：nndist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSM
ul M X] (c : M) (x y : X) : nndist (c • x) (c • y) = nndist x y
-/
theorem nndist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricSMul M M] (a b c : M) :
    nndist (a * b) (a * c) = nndist b c :=
  nndist_smul a b c

@[to_additive (attr := simp)]
/-
**dist_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_mul_right [Mul M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a b
 c : M) : dist (a * c) (b * c) = dist a b
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_smul`：dist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M
 X] (c : M) (x y : X) : dist (c • x) (c • y) = dist x y
-/
theorem dist_mul_right [Mul M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    dist (a * c) (b * c) = dist a b :=
  dist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]
/-
**nndist_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_mul_right [PseudoMetricSpace M] [Mul M] [IsIsometricSMul Mᵐᵒᵖ M] (a
 b c : M) : nndist (a * c) (b * c) = nndist a b
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nndist_smul`：nndist_smul [PseudoMetricSpace X] [SMul M X] [IsIsometricSM
ul M X] (c : M) (x y : X) : nndist (c • x) (c • y) = nndist x y
-/
theorem nndist_mul_right [PseudoMetricSpace M] [Mul M] [IsIsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    nndist (a * c) (b * c) = nndist a b :=
  nndist_smul (MulOpposite.op c) a b

@[to_additive (attr := simp)]
/-
**dist_div_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒ
ᵖ M] (a b c : M) : dist (a / c) (b / c) = dist a b
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `dist_mul_right`：dist_mul_right [Mul M] [PseudoMetricSpace M] [IsIsometri
cSMul Mᵐᵒᵖ M] (a b c : M) : dist (a * c) (b * c) = dist a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : dist (a / c) (b / c) = dist a b := by simp only [div_eq_mul_inv, dist_mul_right]

@[to_additive (attr := simp)]
/-
**nndist_div_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsIsometricSMul M
ᵐᵒᵖ M] (a b c : M) : nndist (a / c) (b / c) = nndist a b
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `nndist_mul_right`：nndist_mul_right [PseudoMetricSpace M] [Mul M] [IsIsom
etricSMul Mᵐᵒᵖ M] (a b c : M) : nndist (a * c) (b * c) = nndist a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nndist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
    (a b c : M) : nndist (a / c) (b / c) = nndist a b := by
  simp only [div_eq_mul_inv, nndist_mul_right]

@[to_additive (attr := simp)]
/-
**dist_inv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G] [IsIsom
etricSMul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.dist_eq`：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   dist (h x) 
(h y) = dis…
-/
theorem dist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b :=
  (IsometryEquiv.inv G).dist_eq a b

@[to_additive (attr := simp)]
/-
**nndist_inv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G] [IsIs
ometricSMul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.nndist_eq`：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoM
etricSpace α] [inst_1 : PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   nndist (h
 x) (h y) = n…
-/
theorem nndist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b :=
  (IsometryEquiv.inv G).nndist_eq a b

@[to_additive (attr := simp)]
/-
**dist_div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_div_left [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G] [IsIso
metricSMul Gᵐᵒᵖ G] (a b c : G) : dist (a / b) (a / c) = dist b c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `dist_mul_left`：dist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsometricS
Mul M M] (a b c : M) : dist (a * b) (a * c) = dist b c
· 使用定理 `dist_inv_inv`：dist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricS
Mul G G] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_div_left [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [IsIsometricSMul Gᵐᵒᵖ G] (a b c : G) : dist (a / b) (a / c) = dist b c := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**nndist_div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_div_left [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G] [IsI
sometricSMul Gᵐᵒᵖ G] (a b c : G) : nndist (a / b) (a / c) = nndist b c
参数：a b c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `nndist_mul_left`：nndist_mul_left [PseudoMetricSpace M] [Mul M] [IsIsomet
ricSMul M M] (a b c : M) : nndist (a * b) (a * c) = nndist b c
· 使用定理 `nndist_inv_inv`：nndist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsomet
ricSMul G G] [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nndist_div_left [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    [IsIsometricSMul Gᵐᵒᵖ G] (a b c : G) : nndist (a / b) (a / c) = nndist b c := by
  simp [div_eq_mul_inv]

/-- If `G` acts isometrically on `X`, then the image of a bounded set in `X` under scalar
multiplication by `c : G` is bounded. See also `Bornology.IsBounded.smul₀` for a similar lemma about
normed spaces. -/
@[to_additive /-- Given an additive isometric action of `G` on `X`, the image of a bounded set in
`X` under translation by `c : G` is bounded. -/]
/-
**Bornology.IsBounded.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.smul [PseudoMetricSpace X] [SMul G X] [IsIsometricSMul
 G X] {s : Set X} (hs : IsBounded s) (c : G) : IsBounded (c • s)
参数：hs : IsBounded s；c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.isBounded_image`：isBounded_image (hf : LipschitzWith K f) 
{s : Set α} (hs : IsBounded s) : IsBounded (f '' s)
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem Bornology.IsBounded.smul [PseudoMetricSpace X] [SMul G X] [IsIsometricSMul G X] {s : Set X}
    (hs : IsBounded s) (c : G) : IsBounded (c • s) :=
  (isometry_smul X c).lipschitz.isBounded_image hs

namespace Metric

variable [PseudoMetricSpace X] [Group G] [MulAction G X] [IsIsometricSMul G X]

@[to_additive (attr := simp)]
/-
**Metric.smul_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：smul_ball (c : G) (x : X) (r : Real) : c • ball x r = ball (c • x) r
参数：c : G；x : X；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.image_ball`：image_ball (h : α ≃ᵢ β) (x : α) (r : Real) : h
 '' Metric.ball x r = Metric.ball (h x) r
-/
theorem smul_ball (c : G) (x : X) (r : ℝ) : c • ball x r = ball (c • x) r :=
  (IsometryEquiv.constSMul c).image_ball _ _

@[to_additive (attr := simp)]
/-
**Metric.preimage_smul_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_smul_ball (c : G) (x : X) (r : Real) : (c • ·) ⁻¹' ball x r = bal
l (c⁻¹ • x) r
参数：c : G；x : X；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `Metric.smul_ball`：smul_ball (c : G) (x : X) (r : Real) : c • ball x r = 
ball (c • x) r
-/
theorem preimage_smul_ball (c : G) (x : X) (r : ℝ) : (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r := by
  rw [preimage_smul, smul_ball]

@[to_additive (attr := simp)]
/-
**Metric.smul_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：smul_closedBall (c : G) (x : X) (r : Real) : c • closedBall x r = closedBa
ll (c • x) r
参数：c : G；x : X；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.image_closedBall`：image_closedBall (h : α ≃ᵢ β) (x : α) (r
 : Real) : h '' Metric.closedBall x r = Metric.closedBall (h x) r
-/
theorem smul_closedBall (c : G) (x : X) (r : ℝ) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_closedBall _ _

@[to_additive (attr := simp)]
/-
**Metric.preimage_smul_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_smul_closedBall (c : G) (x : X) (r : Real) : (c • ·) ⁻¹' closedBa
ll x r = closedBall (c⁻¹ • x) r
参数：c : G；x : X；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `Metric.smul_closedBall`：smul_closedBall (c : G) (x : X) (r : Real) : c •
 closedBall x r = closedBall (c • x) r
-/
theorem preimage_smul_closedBall (c : G) (x : X) (r : ℝ) :
    (c • ·) ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by rw [preimage_smul, smul_closedBall]

@[to_additive (attr := simp)]
/-
**Metric.smul_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：smul_sphere (c : G) (x : X) (r : Real) : c • sphere x r = sphere (c • x) r
参数：c : G；x : X；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.image_sphere`：image_sphere (h : α ≃ᵢ β) (x : α) (r : Real)
 : h '' Metric.sphere x r = Metric.sphere (h x) r
-/
theorem smul_sphere (c : G) (x : X) (r : ℝ) : c • sphere x r = sphere (c • x) r :=
  (IsometryEquiv.constSMul c).image_sphere _ _

@[to_additive (attr := simp)]
/-
**Metric.preimage_smul_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_smul_sphere (c : G) (x : X) (r : Real) : (c • ·) ⁻¹' sphere x r =
 sphere (c⁻¹ • x) r
参数：c : G；x : X；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `Metric.smul_sphere`：smul_sphere (c : G) (x : X) (r : Real) : c • sphere 
x r = sphere (c • x) r
-/
theorem preimage_smul_sphere (c : G) (x : X) (r : ℝ) :
    (c • ·) ⁻¹' sphere x r = sphere (c⁻¹ • x) r := by rw [preimage_smul, smul_sphere]

variable [PseudoMetricSpace G]

@[to_additive (attr := simp)]
/-
**Metric.preimage_mul_left_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_mul_left_ball [IsIsometricSMul G G] (a b : G) (r : Real) : (a * ·
) ⁻¹' ball b r = ball (a⁻¹ * b) r
参数：a b : G；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.preimage_smul_ball`：preimage_smul_ball (c : G) (x : X) (r : Real)
 : (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r
-/
theorem preimage_mul_left_ball [IsIsometricSMul G G] (a b : G) (r : ℝ) :
    (a * ·) ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r

@[to_additive (attr := simp)]
/-
**Metric.preimage_mul_right_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_mul_right_ball [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real) : (f
un x => x * a) ⁻¹' ball b r = ball (b / a) r
参数：a b : G；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Metric.preimage_smul_ball`：preimage_smul_ball (c : G) (x : X) (r : Real)
 : (c • ·) ⁻¹' ball x r = ball (c⁻¹ • x) r
-/
theorem preimage_mul_right_ball [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r

@[to_additive (attr := simp)]
/-
**Metric.preimage_mul_left_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_mul_left_closedBall [IsIsometricSMul G G] (a b : G) (r : Real) : 
(a * ·) ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r
参数：a b : G；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.preimage_smul_closedBall`：preimage_smul_closedBall (c : G) (x : X
) (r : Real) : (c • ·) ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r
-/
theorem preimage_mul_left_closedBall [IsIsometricSMul G G] (a b : G) (r : ℝ) :
    (a * ·) ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r

@[to_additive (attr := simp)]
/-
**Metric.preimage_mul_right_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：preimage_mul_right_closedBall [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : Real
) : (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r
参数：a b : G；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Metric.preimage_smul_closedBall`：preimage_smul_closedBall (c : G) (x : X
) (r : Real) : (c • ·) ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r
-/
theorem preimage_mul_right_closedBall [IsIsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r := by
  rw [div_eq_mul_inv]
  exact preimage_smul_closedBall (MulOpposite.op a) b r

end Metric

section Instances

variable {Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [SMul M X]
  [IsIsometricSMul M X]

@[to_additive]
/-
**Prod.instIsIsometricSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instIsIsometricSMul [SMul M Y] [IsIsometricSMul M Y] : IsIsometricSMu
l M (X × Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.prodMap`：prodMap {δ} [PseudoEMetricSpace δ] {f : α -> β} {g : γ
 -> δ} (hf : Isometry f) (hg : Isometry g) : Isometry (Prod.map f g)
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
instance Prod.instIsIsometricSMul [SMul M Y] [IsIsometricSMul M Y] : IsIsometricSMul M (X × Y) :=
  ⟨fun c => (isometry_smul X c).prodMap (isometry_smul Y c)⟩

@[to_additive]
/-
**Prod.isIsometricSMul'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.isIsometricSMul' {N} [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul 
M M] [Mul N] [PseudoEMetricSpace N] [IsIsometricSMul N N] : IsIsometricSMul (M ×
 N) (M × N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.prodMap`：prodMap {δ} [PseudoEMetricSpace δ] {f : α -> β} {g : γ
 -> δ} (hf : Isometry f) (hg : Isometry g) : Isometry (Prod.map f g)
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
instance Prod.isIsometricSMul' {N} [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] [Mul N]
    [PseudoEMetricSpace N] [IsIsometricSMul N N] : IsIsometricSMul (M × N) (M × N) :=
  ⟨fun c => (isometry_smul M c.1).prodMap (isometry_smul N c.2)⟩

@[to_additive]
/-
**Prod.isIsometricSMul''** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.isIsometricSMul'' {N} [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul
 Mᵐᵒᵖ M] [Mul N] [PseudoEMetricSpace N] [IsIsometricSMul Nᵐᵒᵖ N] : IsIsometricSM
ul (M × N)ᵐᵒᵖ (M × N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.prodMap`：prodMap {δ} [PseudoEMetricSpace δ] {f : α -> β} {g : γ
 -> δ} (hf : Isometry f) (hg : Isometry g) : Isometry (Prod.map f g)
· 使用定理 `isometry_mul_right`：isometry_mul_right [Mul M] [PseudoEMetricSpace M] [I
sIsometricSMul Mᵐᵒᵖ M] (a : M) : Isometry fun x => x * a
-/
instance Prod.isIsometricSMul'' {N} [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M]
    [Mul N] [PseudoEMetricSpace N] [IsIsometricSMul Nᵐᵒᵖ N] :
    IsIsometricSMul (M × N)ᵐᵒᵖ (M × N) :=
  ⟨fun c => (isometry_mul_right c.unop.1).prodMap (isometry_mul_right c.unop.2)⟩

@[to_additive]
/-
**Units.isIsometricSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Units.isIsometricSMul [Monoid M] : IsIsometricSMul Mˣ X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
instance Units.isIsometricSMul [Monoid M] : IsIsometricSMul Mˣ X :=
  ⟨fun c => isometry_smul X (c : M)⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIsometricSMul M Xᵐᵒᵖ :=
  ⟨fun c x y => by simpa only using! edist_smul_left c x.unop y.unop⟩

@[to_additive]
/-
**ULift.isIsometricSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.isIsometricSMul : IsIsometricSMul (ULift M) X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
instance ULift.isIsometricSMul : IsIsometricSMul (ULift M) X :=
  ⟨fun c => by simpa only using! isometry_smul X c.down⟩

@[to_additive]
/-
**ULift.isIsometricSMul'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.isIsometricSMul' : IsIsometricSMul M (ULift X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_smul_left`：edist_smul_left [SMul M X] [IsIsometricSMul M X] (c : M
) (x y : X) : edist (c • x) (c • y) = edist x y
-/
instance ULift.isIsometricSMul' : IsIsometricSMul M (ULift X) :=
  ⟨fun c x y => by simpa only using! edist_smul_left c x.1 y.1⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι} {X : ι → Type*} [Fintype ι] [∀ i, SMul M (X i)] [∀ i, PseudoEMetricSpace (X i)]
    [∀ i, IsIsometricSMul M (X i)] : IsIsometricSMul M (∀ i, X i) :=
  ⟨fun c => .piMap (fun _ => (c • ·)) fun i => isometry_smul (X i) c⟩

@[to_additive]
/-
**Pi.isIsometricSMul'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.isIsometricSMul' {ι} {M X : ι -> Type*} [Fintype ι] [forall i, SMul (M 
i) (X i)] [forall i, PseudoEMetricSpace (X i)] [forall i, IsIsometricSMul (M i) 
(X i)] : IsIsometricSMul (forall i, M i) (forall i, X i)
参数：M i；X i；X i；M i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.piMap`：∀ {ι : Type u_5} [inst : Fintype ι] {α : ι → Type u_3} {
β : ι → Type u_4} [inst_1 : (i : ι) → PseudoEMetricSpace (α i)]   [inst_2 : (i :
 ι) …
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
instance Pi.isIsometricSMul' {ι} {M X : ι → Type*} [Fintype ι] [∀ i, SMul (M i) (X i)]
    [∀ i, PseudoEMetricSpace (X i)] [∀ i, IsIsometricSMul (M i) (X i)] :
    IsIsometricSMul (∀ i, M i) (∀ i, X i) :=
  ⟨fun c => .piMap (fun i => (c i • ·)) fun _ => isometry_smul _ _⟩

@[to_additive]
/-
**Pi.isIsometricSMul''** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.isIsometricSMul'' {ι} {M : ι -> Type*} [Fintype ι] [forall i, Mul (M i)
] [forall i, PseudoEMetricSpace (M i)] [forall i, IsIsometricSMul (M i)ᵐᵒᵖ (M i)
] : IsIsometricSMul (forall i, M i)ᵐᵒᵖ (forall i, M i)
参数：M i；M i；M i；M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.piMap`：∀ {ι : Type u_5} [inst : Fintype ι] {α : ι → Type u_3} {
β : ι → Type u_4} [inst_1 : (i : ι) → PseudoEMetricSpace (α i)]   [inst_2 : (i :
 ι) …
· 使用定理 `isometry_mul_right`：isometry_mul_right [Mul M] [PseudoEMetricSpace M] [I
sIsometricSMul Mᵐᵒᵖ M] (a : M) : Isometry fun x => x * a
-/
instance Pi.isIsometricSMul'' {ι} {M : ι → Type*} [Fintype ι] [∀ i, Mul (M i)]
    [∀ i, PseudoEMetricSpace (M i)] [∀ i, IsIsometricSMul (M i)ᵐᵒᵖ (M i)] :
    IsIsometricSMul (∀ i, M i)ᵐᵒᵖ (∀ i, M i) :=
  ⟨fun c => .piMap (fun i (x : M i) => x * c.unop i) fun _ => isometry_mul_right _⟩
/-
**Additive.isIsIsometricVAdd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.isIsIsometricVAdd : IsIsometricVAdd (Additive M) X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
instance Additive.isIsIsometricVAdd : IsIsometricVAdd (Additive M) X :=
  ⟨fun c => isometry_smul X c.toMul⟩
/-
**Additive.isIsIsometricVAdd'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.isIsIsometricVAdd' [Mul M] [PseudoEMetricSpace M] [IsIsometricSMu
l M M] : IsIsometricVAdd (Additive M) (Additive M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_smul_left`：edist_smul_left [SMul M X] [IsIsometricSMul M X] (c : M
) (x y : X) : edist (c • x) (c • y) = edist x y
-/
instance Additive.isIsIsometricVAdd' [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul M M] :
    IsIsometricVAdd (Additive M) (Additive M) :=
  ⟨fun c x y => edist_smul_left c.toMul x.toMul y.toMul⟩
/-
**Additive.isIsIsometricVAdd''** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.isIsIsometricVAdd'' [Mul M] [PseudoEMetricSpace M] [IsIsometricSM
ul Mᵐᵒᵖ M] : IsIsometricVAdd (Additive M)ᵃᵒᵖ (Additive M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_smul_left`：edist_smul_left [SMul M X] [IsIsometricSMul M X] (c : M
) (x y : X) : edist (c • x) (c • y) = edist x y
-/
instance Additive.isIsIsometricVAdd'' [Mul M] [PseudoEMetricSpace M] [IsIsometricSMul Mᵐᵒᵖ M] :
    IsIsometricVAdd (Additive M)ᵃᵒᵖ (Additive M) :=
  ⟨fun c x y => edist_smul_left (MulOpposite.op c.unop.toMul) x.toMul y.toMul⟩
/-
**Multiplicative.isIsometricSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.isIsometricSMul {M X} [VAdd M X] [PseudoEMetricSpace X] [Is
IsometricVAdd M X] : IsIsometricSMul (Multiplicative M) X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsometricVAdd.isometry_vadd`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : VAdd M X} [self : IsIsometricVAdd M X] (c : M),   Iso
metry fun x => c +ᵥ…
-/
instance Multiplicative.isIsometricSMul {M X} [VAdd M X] [PseudoEMetricSpace X]
    [IsIsometricVAdd M X] : IsIsometricSMul (Multiplicative M) X :=
  ⟨fun c => isometry_vadd X c.toAdd⟩
/-
**Multiplicative.isIsometricSMul'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.isIsometricSMul' [Add M] [PseudoEMetricSpace M] [IsIsometri
cVAdd M M] : IsIsometricSMul (Multiplicative M) (Multiplicative M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_vadd_left`：∀ {M : Type u} {X : Type w} [inst : PseudoEMetricSpace 
X] [inst_1 : VAdd M X] [IsIsometricVAdd M X] (c : M) (x y : X),   edist (c +ᵥ x)
 (c +…
-/
instance Multiplicative.isIsometricSMul' [Add M] [PseudoEMetricSpace M] [IsIsometricVAdd M M] :
    IsIsometricSMul (Multiplicative M) (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left c.toAdd x.toAdd y.toAdd⟩
/-
**Multiplicative.isIsIsometricVAdd''** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.isIsIsometricVAdd'' [Add M] [PseudoEMetricSpace M] [IsIsome
tricVAdd Mᵃᵒᵖ M] : IsIsometricSMul (Multiplicative M)ᵐᵒᵖ (Multiplicative M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_vadd_left`：∀ {M : Type u} {X : Type w} [inst : PseudoEMetricSpace 
X] [inst_1 : VAdd M X] [IsIsometricVAdd M X] (c : M) (x y : X),   edist (c +ᵥ x)
 (c +…
-/
instance Multiplicative.isIsIsometricVAdd'' [Add M] [PseudoEMetricSpace M]
    [IsIsometricVAdd Mᵃᵒᵖ M] : IsIsometricSMul (Multiplicative M)ᵐᵒᵖ (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left (AddOpposite.op c.unop.toAdd) x.toAdd y.toAdd⟩

end Instances

