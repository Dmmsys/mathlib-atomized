/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Joseph Myers
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.InnerProductSpace.Affine

/-!
# Perpendicular bisector of a segment

We define `AffineSubspace.perpBisector p₁ p₂` to be the perpendicular bisector of the segment
`[p₁, p₂]`, as a bundled affine subspace. We also prove that a point belongs to the perpendicular
bisector if and only if it is equidistant from `p₁` and `p₂`, as well as a few linear equations that
define this subspace.

## Keywords

euclidean geometry, perpendicular, perpendicular bisector, line segment bisector, equidistant
-/

@[expose] public section

open Set
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

noncomputable section

namespace AffineSubspace

variable {c p₁ p₂ : P}

/-- Perpendicular bisector of a segment in a Euclidean affine space. -/
/-
**AffineSubspace.perpBisector** 是 Mathlib 中的一个定义，位于命名空间 `AffineSubspace`。
形式化陈述：perpBisector (p₁ p₂ : P) : AffineSubspace Real P
参数：p₁ p₂ : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Perpendicular bisector of a segment in a Euclidean affine space.
-/
def perpBisector (p₁ p₂ : P) : AffineSubspace ℝ P :=
  mk' (midpoint ℝ p₁ p₂) (LinearMap.ker (innerₛₗ ℝ (p₂ -ᵥ p₁)))

/-- A point `c` belongs the perpendicular bisector of `[p₁, p₂]` iff `p₂ -ᵥ p₁` is orthogonal to
`c -ᵥ midpoint ℝ p₁ p₂`. -/
/-
**AffineSubspace.mem_perpBisector_iff_inner_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `
AffineSubspace`。
形式化陈述：mem_perpBisector_iff_inner_eq_zero' : c in perpBisector p₁ p₂ ↔ ⟪p₂ -ᵥ p₁,
 c -ᵥ midpoint Real p₁ p₂⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A point `c` belongs the perpendicular bisector of `[p₁, p₂]` iff `p₂ -ᵥ p₁` is o
rthogonal to
`c -ᵥ midpoint ℝ p₁ p₂`.
-/
theorem mem_perpBisector_iff_inner_eq_zero' :
    c ∈ perpBisector p₁ p₂ ↔ ⟪p₂ -ᵥ p₁, c -ᵥ midpoint ℝ p₁ p₂⟫ = 0 :=
  Iff.rfl

/-- A point `c` belongs the perpendicular bisector of `[p₁, p₂]` iff `c -ᵥ midpoint ℝ p₁ p₂` is
orthogonal to `p₂ -ᵥ p₁`. -/
/-
**AffineSubspace.mem_perpBisector_iff_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `A
ffineSubspace`。
形式化陈述：mem_perpBisector_iff_inner_eq_zero : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpo
int Real p₁ p₂, p₂ -ᵥ p₁⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0

--- 原说明 ---
A point `c` belongs the perpendicular bisector of `[p₁, p₂]` iff `c -ᵥ midpoint 
ℝ p₁ p₂` is
orthogonal to `p₂ -ᵥ p₁`.
-/
theorem mem_perpBisector_iff_inner_eq_zero :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint ℝ p₁ p₂, p₂ -ᵥ p₁⟫ = 0 :=
  inner_eq_zero_symm
/-
**AffineSubspace.mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero** 是 Mat
hlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero : c in perpBisecto
r p₁ p₂ ↔ ⟪Equiv.pointReflection c p₁ -ᵥ p₂, p₂ -ᵥ p₁⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_perpBisector_iff_inner_eq_zero`：mem_perpBisector_iff_
inner_eq_zero : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint Real p₁ p₂, p₂ -ᵥ p₁⟫ =
 0
· 使用定理 `Equiv.pointReflection_apply`：pointReflection_apply (x y : P) : pointRefl
ection x y = (x -ᵥ y) +ᵥ x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `vsub_midpoint`：vsub_midpoint (p₁ p₂ p : P) : p -ᵥ midpoint R p₁ p₂ = (⅟2
 : R) • (p -ᵥ p₁) + (⅟2 : R) • (p -ᵥ p₂)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero :
    c ∈ perpBisector p₁ p₂ ↔ ⟪Equiv.pointReflection c p₁ -ᵥ p₂, p₂ -ᵥ p₁⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero, Equiv.pointReflection_apply,
    vsub_midpoint, invOf_eq_inv, ← smul_add, real_inner_smul_left, vadd_vsub_assoc]
  simp
/-
**AffineSubspace.mem_perpBisector_pointReflection_iff_inner_eq_zero** 是 Mathlib 
中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：mem_perpBisector_pointReflection_iff_inner_eq_zero : c in perpBisector p₁ 
(Equiv.pointReflection p₂ p₁) ↔ ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_perpBisector_iff_inner_eq_zero`：mem_perpBisector_iff_
inner_eq_zero : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint Real p₁ p₂, p₂ -ᵥ p₁⟫ =
 0
· 使用定理 `midpoint_pointReflection_right`：midpoint_pointReflection_right (x y : P)
 : midpoint R y (Equiv.pointReflection x y) = x
· 使用定理 `Equiv.pointReflection_apply`：pointReflection_apply (x y : P) : pointRefl
ection x y = (x -ᵥ y) +ᵥ x
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `add_self_eq_zero`：add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_perpBisector_pointReflection_iff_inner_eq_zero :
    c ∈ perpBisector p₁ (Equiv.pointReflection p₂ p₁) ↔ ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero, midpoint_pointReflection_right,
    Equiv.pointReflection_apply, vadd_vsub_assoc, inner_add_right, add_self_eq_zero,
    ← neg_eq_zero, ← inner_neg_right, neg_vsub_eq_vsub_rev]
/-
**AffineSubspace.midpoint_mem_perpBisector** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubs
pace`。
形式化陈述：midpoint_mem_perpBisector (p₁ p₂ : P) : midpoint Real p₁ p₂ in perpBisecto
r p₁ p₂
参数：p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem midpoint_mem_perpBisector (p₁ p₂ : P) :
    midpoint ℝ p₁ p₂ ∈ perpBisector p₁ p₂ := by
  simp [mem_perpBisector_iff_inner_eq_zero]
/-
**AffineSubspace.perpBisector_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
形式化陈述：perpBisector_nonempty : (perpBisector p₁ p₂ : Set P).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `AffineSubspace.midpoint_mem_perpBisector`：midpoint_mem_perpBisector (p₁ 
p₂ : P) : midpoint Real p₁ p₂ in perpBisector p₁ p₂
-/
theorem perpBisector_nonempty : (perpBisector p₁ p₂ : Set P).Nonempty :=
  ⟨_, midpoint_mem_perpBisector _ _⟩

@[simp]
/-
**AffineSubspace.direction_perpBisector** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：direction_perpBisector (p₁ p₂ : P) : (perpBisector p₁ p₂).direction = (Rea
l ∙ (p₂ -ᵥ p₁))ᗮ
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.perpBisector.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst 
: NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P
]   [inst_3 : NormedAd…
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_right`：mem_orthogonal_singl
eton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
-/
theorem direction_perpBisector (p₁ p₂ : P) :
    (perpBisector p₁ p₂).direction = (ℝ ∙ (p₂ -ᵥ p₁))ᗮ := by
  rw [perpBisector, direction_mk']
  ext x
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm
/-
**AffineSubspace.mem_perpBisector_iff_inner_eq_inner** 是 Mathlib 中的一个定理，位于命名空间 `
AffineSubspace`。
形式化陈述：mem_perpBisector_iff_inner_eq_inner : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, 
p₂ -ᵥ p₁⟫ = ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `AffineSubspace.mem_perpBisector_iff_inner_eq_zero`：mem_perpBisector_iff_
inner_eq_zero : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint Real p₁ p₂, p₂ -ᵥ p₁⟫ =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_neg_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a + -b 
= 0 ↔ a = b
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `vsub_midpoint`：vsub_midpoint (p₁ p₂ p : P) : p -ᵥ midpoint R p₁ p₂ = (⅟2
 : R) • (p -ᵥ p₁) + (⅟2 : R) • (p -ᵥ p₂)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_perpBisector_iff_inner_eq_inner :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ := by
  rw [Iff.comm, mem_perpBisector_iff_inner_eq_zero, ← add_neg_eq_zero, ← inner_neg_right,
    neg_vsub_eq_vsub_rev, ← inner_add_left, vsub_midpoint, invOf_eq_inv, ← smul_add,
    real_inner_smul_left]; simp
/-
**AffineSubspace.mem_perpBisector_iff_inner_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：mem_perpBisector_iff_inner_eq : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, p₂ -ᵥ 
p₁⟫ = (dist p₁ p₂) ^ 2 / 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_perpBisector_iff_inner_eq_zero`：mem_perpBisector_iff_
inner_eq_zero : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint Real p₁ p₂, p₂ -ᵥ p₁⟫ =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `midpoint_vsub_left`：midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ
 p₁ = (⅟2 : R) • (p₂ -ᵥ p₁)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `real_inner_self_eq_norm_sq`：real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_
Real = ‖x‖ ^ 2
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_perpBisector_iff_inner_eq :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = (dist p₁ p₂) ^ 2 / 2 := by
  rw [mem_perpBisector_iff_inner_eq_zero, ← vsub_sub_vsub_cancel_right _ _ p₁, inner_sub_left,
    sub_eq_zero, midpoint_vsub_left, invOf_eq_inv, real_inner_smul_left, real_inner_self_eq_norm_sq,
    dist_eq_norm_vsub' V, div_eq_inv_mul]
/-
**AffineSubspace.mem_perpBisector_iff_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineS
ubspace`。
形式化陈述：mem_perpBisector_iff_dist_eq : c in perpBisector p₁ p₂ ↔ dist c p₁ = dist 
c p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `real_inner_add_sub_eq_zero_iff`：real_inner_add_sub_eq_zero_iff (x y : F)
 : ⟪x + y, x - y⟫_Real = 0 ↔ ‖x‖ = ‖y‖
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `AffineSubspace.mem_perpBisector_iff_inner_eq_inner`：mem_perpBisector_iff
_inner_eq_inner : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = ⟪c -ᵥ p₂, p₁ -
ᵥ p₂⟫
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_perpBisector_iff_dist_eq : c ∈ perpBisector p₁ p₂ ↔ dist c p₁ = dist c p₂ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← real_inner_add_sub_eq_zero_iff,
    vsub_sub_vsub_cancel_left, inner_add_left, add_eq_zero_iff_eq_neg, ← inner_neg_right,
    neg_vsub_eq_vsub_rev, mem_perpBisector_iff_inner_eq_inner]
/-
**AffineSubspace.mem_perpBisector_iff_dist_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Affine
Subspace`。
形式化陈述：mem_perpBisector_iff_dist_eq' : c in perpBisector p₁ p₂ ↔ dist p₁ c = dist
 p₂ c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_perpBisector_iff_dist_eq' : c ∈ perpBisector p₁ p₂ ↔ dist p₁ c = dist p₂ c := by
  simp only [mem_perpBisector_iff_dist_eq, dist_comm]
/-
**AffineSubspace.perpBisector_comm** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：perpBisector_comm (p₁ p₂ : P) : perpBisector p₁ p₂ = perpBisector p₂ p₁
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem perpBisector_comm (p₁ p₂ : P) : perpBisector p₁ p₂ = perpBisector p₂ p₁ := by
  ext c; simp only [mem_perpBisector_iff_dist_eq, eq_comm]
/-
**AffineSubspace.right_mem_perpBisector** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspac
e`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
p₁ p₂ : P}, p₂ ∈ AffineSubspace.perpBisector p₁ p₂ ↔ p₁ = p₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
@[simp] theorem right_mem_perpBisector : p₂ ∈ perpBisector p₁ p₂ ↔ p₁ = p₂ := by
  simpa [mem_perpBisector_iff_inner_eq_inner] using eq_comm
/-
**AffineSubspace.left_mem_perpBisector** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace
`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
p₁ p₂ : P}, p₁ ∈ AffineSubspace.perpBisector p₁ p₂ ↔ p₁ = p₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.perpBisector_comm`：perpBisector_comm (p₁ p₂ : P) : perpBi
sector p₁ p₂ = perpBisector p₂ p₁
· 使用定理 `AffineSubspace.right_mem_perpBisector`：∀ {V : Type u_1} {P : Type u_2} [
inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSp
ace P]   [inst_3 : NormedAd…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem left_mem_perpBisector : p₁ ∈ perpBisector p₁ p₂ ↔ p₁ = p₂ := by
  rw [perpBisector_comm, right_mem_perpBisector, eq_comm]
/-
**AffineSubspace.perpBisector_self** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
p : P), AffineSubspace.perpBisector p p = ⊤
参数：p : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem perpBisector_self (p : P) : perpBisector p p = ⊤ :=
  top_unique fun _ ↦ by simp [mem_perpBisector_iff_inner_eq_inner]
/-
**AffineSubspace.perpBisector_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
p₁ p₂ : P}, AffineSubspace.perpBisector p₁ p₂ = ⊤ ↔ p₁ = p₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.left_mem_perpBisector`：∀ {V : Type u_1} {P : Type u_2} [i
nst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpa
ce P]   [inst_3 : NormedAd…
· 使用定理 `AffineSubspace.perpBisector_self`：∀ {V : Type u_1} {P : Type u_2} [inst 
: NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P
]   [inst_3 : NormedAd…
-/
@[simp] theorem perpBisector_eq_top : perpBisector p₁ p₂ = ⊤ ↔ p₁ = p₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ perpBisector_self _⟩
  rw [← left_mem_perpBisector, h]
  trivial
/-
**AffineSubspace.perpBisector_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `AffineSubspace`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
p₁ p₂ : P}, AffineSubspace.perpBisector p₁ p₂ ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.nonempty_iff_ne_bot`：nonempty_iff_ne_bot (Q : AffineSubsp
ace k P) : (Q : Set P).Nonempty ↔ Q != ⊥
· 使用定理 `AffineSubspace.perpBisector_nonempty`：perpBisector_nonempty : (perpBisec
tor p₁ p₂ : Set P).Nonempty
-/
@[simp] theorem perpBisector_ne_bot : perpBisector p₁ p₂ ≠ ⊥ := by
  rw [← nonempty_iff_ne_bot]; exact perpBisector_nonempty

end AffineSubspace

open AffineSubspace

namespace EuclideanGeometry

/-- If `b` is strictly between `a` and `c`, and `p -ᵥ a` is orthogonal to `b -ᵥ a`,
then `p` is closer to `b` than to `c`. -/
/-
**EuclideanGeometry.dist_lt_of_sbtw_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：dist_lt_of_sbtw_of_inner_eq_zero {a b c p : P} (h_sbtw : Sbtw Real a b c) 
(h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) : dist p b < dist p c
参数：h_sbtw : Sbtw Real a b c；h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.mem_image_Ioo`：Sbtw.mem_image_Ioo {x y z : P} (h : Sbtw R x y z) : 
y in lineMap x z '' Set.Ioo (0 : R) 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `dist_sq_lineMap_of_inner_eq_zero`：dist_sq_lineMap_of_inner_eq_zero {a b 
p : P} (t : Real) (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) : dist p (AffineMap.lineMap a
 b t) ^ 2 = dist p a ^…
· 使用定理 `dist_sq_of_inner_eq_zero`：dist_sq_of_inner_eq_zero {a b p : P} (h_inner 
: ⟪p -ᵥ a, b -ᵥ a⟫ = 0) : dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2
· 使用引理 `sq_pos_of_pos`：sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a 
^ 2
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_pos`：dist_pos {x y : γ} : 0 < dist x y ↔ x != y
· 使用定理 `Sbtw.left_ne_right`：Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : 
x != z
· 使用引理 `sq_lt_one_iff₀`：sq_lt_one_iff₀ (ha : 0 <= a) : a ^ 2 < 1 ↔ a < 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 86 条，此处仅展示前 30 条）

--- 原说明 ---
If `b` is strictly between `a` and `c`, and `p -ᵥ a` is orthogonal to `b -ᵥ a`,
then `p` is closer to `b` than to `c`.
-/
theorem dist_lt_of_sbtw_of_inner_eq_zero {a b c p : P}
    (h_sbtw : Sbtw ℝ a b c)
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p b < dist p c := by
  obtain ⟨t, ⟨ht0, ht1⟩, hb_eq⟩ := h_sbtw.mem_image_Ioo
  have hb : b -ᵥ a = t • (c -ᵥ a) := by simp [← hb_eq, AffineMap.lineMap_apply]
  have hpc : ⟪p -ᵥ a, c -ᵥ a⟫ = 0 := by simpa [ht0.ne', hb, inner_smul_right] using h_inner
  have h_sq_ineq : dist p b ^ 2 < dist p c ^ 2 := by
    rw [← hb_eq, dist_sq_lineMap_of_inner_eq_zero t hpc, dist_sq_of_inner_eq_zero hpc]
    have hv_pos : 0 < dist a c ^ 2 := sq_pos_of_pos (dist_pos.mpr h_sbtw.left_ne_right)
    have ht_sq_lt : t ^ 2 < 1 := sq_lt_one_iff₀ ht0.le |>.mpr ht1
    nlinarith [sq_nonneg (dist p a), sq_nonneg (dist a c)]
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_ineq

/-- If `b` is weakly between `a` and `c`, and `p -ᵥ a` is orthogonal to `c -ᵥ a`,
then `p` is at least as close to `b` as to `c`. -/
/-
**EuclideanGeometry.dist_le_of_wbtw_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：dist_le_of_wbtw_of_inner_eq_zero {a b c p : P} (h_wbtw : Wbtw Real a b c) 
(h_inner : ⟪p -ᵥ a, c -ᵥ a⟫ = 0) : dist p b <= dist p c
参数：h_wbtw : Wbtw Real a b c；h_inner : ⟪p -ᵥ a, c -ᵥ a⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_sq_lineMap_of_inner_eq_zero`：dist_sq_lineMap_of_inner_eq_zero {a b 
p : P} (t : Real) (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) : dist p (AffineMap.lineMap a
 b t) ^ 2 = dist p a ^…
· 使用定理 `dist_sq_of_inner_eq_zero`：dist_sq_of_inner_eq_zero {a b p : P} (h_inner 
: ⟪p -ᵥ a, b -ᵥ a⟫ = 0) : dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `sq_le_one_iff₀`：sq_le_one_iff₀ (ha : 0 <= a) : a ^ 2 <= 1 ↔ a <= 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
If `b` is weakly between `a` and `c`, and `p -ᵥ a` is orthogonal to `c -ᵥ a`,
then `p` is at least as close to `b` as to `c`.
-/
theorem dist_le_of_wbtw_of_inner_eq_zero {a b c p : P}
    (h_wbtw : Wbtw ℝ a b c)
    (h_inner : ⟪p -ᵥ a, c -ᵥ a⟫ = 0) :
    dist p b ≤ dist p c := by
  obtain ⟨t, ⟨ht0, ht1⟩, hb_eq⟩ := h_wbtw
  have h_sq_ineq : dist p b ^ 2 ≤ dist p c ^ 2 := by
    rw [← hb_eq, dist_sq_lineMap_of_inner_eq_zero t h_inner, dist_sq_of_inner_eq_zero h_inner]
    have ht_sq_le : t ^ 2 ≤ 1 := sq_le_one_iff₀ ht0 |>.mpr ht1
    nlinarith [sq_nonneg (dist p a), sq_nonneg (dist a c)]
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_le_sqrt h_sq_ineq

/-- If `p` lies on the perpendicular bisector of `ab` and `b` is strictly between `a` and `c`,
then `p` is closer to `b` than to `c`. -/
/-
**EuclideanGeometry.dist_lt_of_sbtw_of_mem_perpBisector** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry`。
形式化陈述：dist_lt_of_sbtw_of_mem_perpBisector {a b c p : P} (h_sbtw : Sbtw Real a b 
c) (hp : p in AffineSubspace.perpBisector a b) : dist p b < dist p c
参数：h_sbtw : Sbtw Real a b c；hp : p in AffineSubspace.perpBisector a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.dist_lt_of_sbtw_of_inner_eq_zero`：dist_lt_of_sbtw_of_i
nner_eq_zero {a b c p : P} (h_sbtw : Sbtw Real a b c) (h_inner : ⟪p -ᵥ a, b -ᵥ a
⟫ = 0) : dist p b < dist p c
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Sbtw.trans_left_right`：Sbtw.trans_left_right {w x y z : P} (h₁ : Sbtw R 
w y z) (h₂ : Sbtw R w x y) : Sbtw R x y z
· 使用定理 `sbtw_midpoint_of_ne`：sbtw_midpoint_of_ne {x y : P} (h : x != y) : Sbtw R
 x (midpoint R x y) y
· 使用定理 `Sbtw.left_ne`：Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x != y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `right_vsub_midpoint`：right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R 
p₁ p₂ = (⅟2 : R) • (p₂ -ᵥ p₁)
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.mem_perpBisector_iff_inner_eq_zero`：mem_perpBisector_iff_
inner_eq_zero : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint Real p₁ p₂, p₂ -ᵥ p₁⟫ =
 0
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
If `p` lies on the perpendicular bisector of `ab` and `b` is strictly between `a
` and `c`,
then `p` is closer to `b` than to `c`.
-/
theorem dist_lt_of_sbtw_of_mem_perpBisector {a b c p : P}
    (h_sbtw : Sbtw ℝ a b c)
    (hp : p ∈ AffineSubspace.perpBisector a b) :
    dist p b < dist p c :=
  dist_lt_of_sbtw_of_inner_eq_zero
    (h_sbtw.trans_left_right (sbtw_midpoint_of_ne ℝ h_sbtw.left_ne)) <| by
    rw [right_vsub_midpoint, inner_smul_right,
        mem_perpBisector_iff_inner_eq_zero.mp hp, invOf_eq_inv, mul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- If `p` lies on the perpendicular bisector of `ab` and `b` is weakly between `a` and `c`,
then `p` is at least as close to `b` as to `c`. -/
/-
**EuclideanGeometry.dist_le_of_wbtw_of_mem_perpBisector** 是 Mathlib 中的一个定理，位于命名空
间 `EuclideanGeometry`。
形式化陈述：dist_le_of_wbtw_of_mem_perpBisector {a b c p : P} (h_wbtw : Wbtw Real a b 
c) (hab : a != b) (hp : p in AffineSubspace.perpBisector a b) : dist p b <= dist
 p c
参数：h_wbtw : Wbtw Real a b c；hab : a != b；hp : p in AffineSubspace.perpBisector a
 b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.dist_le_of_wbtw_of_inner_eq_zero`：dist_le_of_wbtw_of_i
nner_eq_zero {a b c p : P} (h_wbtw : Wbtw Real a b c) (h_inner : ⟪p -ᵥ a, c -ᵥ a
⟫ = 0) : dist p b <= dist p c
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Wbtw.trans_left_right`：Wbtw.trans_left_right {w x y z : P} (h₁ : Wbtw R 
w y z) (h₂ : Wbtw R w x y) : Wbtw R x y z
· 使用定理 `wbtw_midpoint`：wbtw_midpoint (x y : P) : Wbtw R x (midpoint R x y) y
· 使用定理 `Wbtw.right_mem_image_Ici_of_left_ne`：Wbtw.right_mem_image_Ici_of_left_ne
 {x y z : P} (h : Wbtw R x y z) (hne : x != y) : z in lineMap x y '' Set.Ici (1 
: R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `AffineMap.lineMap_vsub_left`：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : li
neMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `left_vsub_midpoint`：left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁
 p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.mem_perpBisector_iff_inner_eq_zero`：mem_perpBisector_iff_
inner_eq_zero : c in perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint Real p₁ p₂, p₂ -ᵥ p₁⟫ =
 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
If `p` lies on the perpendicular bisector of `ab` and `b` is weakly between `a` 
and `c`,
then `p` is at least as close to `b` as to `c`.
-/
theorem dist_le_of_wbtw_of_mem_perpBisector {a b c p : P}
    (h_wbtw : Wbtw ℝ a b c) (hab : a ≠ b)
    (hp : p ∈ AffineSubspace.perpBisector a b) :
    dist p b ≤ dist p c :=
  dist_le_of_wbtw_of_inner_eq_zero
    (h_wbtw.trans_left_right (wbtw_midpoint ℝ a b)) <| by
    rcases h_wbtw.right_mem_image_Ici_of_left_ne hab with ⟨s, -, rfl⟩
    rw [← vsub_add_vsub_cancel (AffineMap.lineMap a b s) a, AffineMap.lineMap_vsub_left,
        left_vsub_midpoint, ← neg_vsub_eq_vsub_rev b a, smul_neg, ← sub_eq_add_neg,
        inner_sub_right, inner_smul_right, inner_smul_right,
        mem_perpBisector_iff_inner_eq_zero.mp hp, mul_zero, mul_zero, sub_self]

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same applies to `c₂`. Then the
vector between `c₁` and `c₂` is orthogonal to that between `p₁` and `p₂`. (In two dimensions, this
says that the diagonals of a kite are orthogonal.) -/
/-
**EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq** 是 Mathlib 中的一个定理，位于命
名空间 `EuclideanGeometry`。
形式化陈述：inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ 
= dist p₂ c₁) (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0
参数：hc₁ : dist p₁ c₁ = dist p₂ c₁；hc₂ : dist p₁ c₂ = dist p₂ c₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_left`：mem_orthogonal_single
ton_iff_inner_left {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0
· 使用定理 `AffineSubspace.direction_perpBisector`：direction_perpBisector (p₁ p₂ : P
) : (perpBisector p₁ p₂).direction = (Real ∙ (p₂ -ᵥ p₁))ᗮ
· 使用定理 `AffineSubspace.vsub_mem_direction`：vsub_mem_direction {s : AffineSubspac
e k P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : p₂ in s) : p₁ -ᵥ p₂ in s.direction
· 使用定理 `AffineSubspace.mem_perpBisector_iff_dist_eq'`：mem_perpBisector_iff_dist_
eq' : c in perpBisector p₁ p₂ ↔ dist p₁ c = dist p₂ c

--- 原说明 ---
Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same applies to `c₂
`. Then the
vector between `c₁` and `c₂` is orthogonal to that between `p₁` and `p₂`. (In tw
o dimensions, this
says that the diagonals of a kite are orthogonal.)
-/
theorem inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
    (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 := by
  rw [← Submodule.mem_orthogonal_singleton_iff_inner_left, ← direction_perpBisector]
  apply vsub_mem_direction <;> rwa [mem_perpBisector_iff_dist_eq']

end EuclideanGeometry

variable {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [MetricSpace P']
variable [NormedAddTorsor V' P']

/-
**Isometry.preimage_perpBisector** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.preimage_perpBisector {f : P -> P'} (h : Isometry f) (p₁ p₂ : P) 
: f ⁻¹' (perpBisector (f p₁) (f p₂)) = perpBisector p₁ p₂
参数：h : Isometry f；p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Isometry.preimage_perpBisector {f : P → P'} (h : Isometry f) (p₁ p₂ : P) :
    f ⁻¹' (perpBisector (f p₁) (f p₂)) = perpBisector p₁ p₂ := by
  ext x; simp [mem_perpBisector_iff_dist_eq, h.dist_eq]
/-
**Isometry.mapsTo_perpBisector** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.mapsTo_perpBisector {f : P -> P'} (h : Isometry f) (p₁ p₂ : P) : 
MapsTo f (perpBisector p₁ p₂) (perpBisector (f p₁) (f p₂))
参数：h : Isometry f；p₁ p₂ : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Isometry.preimage_perpBisector`：Isometry.preimage_perpBisector {f : P ->
 P'} (h : Isometry f) (p₁ p₂ : P) : f ⁻¹' (perpBisector (f p₁) (f p₂)) = perpBis
ector p₁ p₂
-/
theorem Isometry.mapsTo_perpBisector {f : P → P'} (h : Isometry f) (p₁ p₂ : P) :
    MapsTo f (perpBisector p₁ p₂) (perpBisector (f p₁) (f p₂)) :=
  (h.preimage_perpBisector p₁ p₂).ge
