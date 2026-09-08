/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Oriented angles.

This file defines oriented angles in real inner product spaces.

## Main definitions

* `Orientation.oangle` is the oriented angle between two vectors with respect to an orientation.

## Implementation notes

The definitions here use the `Real.Angle` type, angles modulo `2 * π`. For some purposes,
angles modulo `π` are more convenient, because results are true for such angles with less
configuration dependence. Results that are only equalities modulo `π` can be represented
modulo `2 * π` as equalities of `(2 : ℤ) • θ`.

## References

* Evan Chen, Euclidean Geometry in Mathematical Olympiads.

-/

@[expose] public section


noncomputable section

open Module Complex

open scoped Real RealInnerProductSpace ComplexConjugate

namespace Orientation

attribute [local instance] Complex.finrank_real_complex_fact

variable {V V' : Type*}
variable [NormedAddCommGroup V] [NormedAddCommGroup V']
variable [InnerProductSpace ℝ V] [InnerProductSpace ℝ V']
variable [Fact (finrank ℝ V = 2)] [Fact (finrank ℝ V' = 2)] (o : Orientation ℝ V (Fin 2))

local notation "ω" => o.areaForm

/-- The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0.
See `InnerProductGeometry.angle` for the corresponding unoriented angle definition. -/
/-
**Orientation.oangle** 是 Mathlib 中的一个定义，位于命名空间 `Orientation`。
形式化陈述：oangle (x y : V) : Real.Angle
参数：x y : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this 
is 0.
See `InnerProductGeometry.angle` for the corresponding unoriented angle definiti
on.
-/
def oangle (x y : V) : Real.Angle :=
  Complex.arg (o.kahler x y)

/-- Oriented angles are continuous when the vectors involved are nonzero. -/
@[fun_prop]
/-
**Orientation.continuousAt_oangle** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：continuousAt_oangle {x : V × V} (hx1 : x.1 != 0) (hx2 : x.2 != 0) : Contin
uousAt (fun y : V × V => o.oangle y.1 y.2) x
参数：hx1 : x.1 != 0；hx2 : x.2 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Complex.continuousAt_arg_coe_angle`：continuousAt_arg_coe_angle (h : x !=
 0) : ContinuousAt ((↑) ∘ arg : Complex -> Real.Angle) x
· 使用定理 `Orientation.kahler_ne_zero`：kahler_ne_zero {x y : E} (hx : x != 0) (hy :
 y != 0) : o.kahler x y != 0
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
Oriented angles are continuous when the vectors involved are nonzero.
-/
theorem continuousAt_oangle {x : V × V} (hx1 : x.1 ≠ 0) (hx2 : x.2 ≠ 0) :
    ContinuousAt (fun y : V × V => o.oangle y.1 y.2) x := by
  refine (Complex.continuousAt_arg_coe_angle ?_).comp ?_
  · exact o.kahler_ne_zero hx1 hx2
  exact ((continuous_ofReal.comp continuous_inner).add
    ((continuous_ofReal.comp o.areaForm'.continuous₂).mul continuous_const)).continuousAt

/-- If the first vector passed to `oangle` is 0, the result is 0. -/
@[simp]
/-
**Orientation.oangle_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_zero_left (x : V) : o.oangle 0 x = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the first vector passed to `oangle` is 0, the result is 0.
-/
theorem oangle_zero_left (x : V) : o.oangle 0 x = 0 := by simp [oangle]

/-- If the second vector passed to `oangle` is 0, the result is 0. -/
@[simp]
/-
**Orientation.oangle_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_zero_right (x : V) : o.oangle x 0 = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the second vector passed to `oangle` is 0, the result is 0.
-/
theorem oangle_zero_right (x : V) : o.oangle x 0 = 0 := by simp [oangle]

set_option backward.isDefEq.respectTransparency false in
/-- If the two vectors passed to `oangle` are the same, the result is 0. -/
@[simp]
/-
**Orientation.oangle_self** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_self (x : V) : o.oangle x x = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.eq_1`：∀ {V : Type u_1} [inst : NormedAddCommGroup V] 
[inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)]   (o :
 Orientation …
· 使用定理 `Orientation.kahler_apply_self`：kahler_apply_self (x : E) : o.kahler x x 
= ‖x‖ ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `QuotientAddGroup.mk_zero`：∀ {G : Type u_1} [inst : AddGroup G] (N : AddS
ubgroup G) [nN : N.Normal], ↑0 = 0

--- 原说明 ---
If the two vectors passed to `oangle` are the same, the result is 0.
-/
theorem oangle_self (x : V) : o.oangle x x = 0 := by
  rw [oangle, kahler_apply_self, ← ofReal_pow]
  convert! QuotientAddGroup.mk_zero (AddSubgroup.zmultiples (2 * π))
  apply arg_ofReal_of_nonneg
  positivity

/-- If the angle between two vectors is nonzero, the first vector is nonzero. -/
/-
**Orientation.left_ne_zero_of_oangle_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orientat
ion`。
形式化陈述：left_ne_zero_of_oangle_ne_zero {x y : V} (h : o.oangle x y != 0) : x != 0
参数：h : o.oangle x y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is nonzero, the first vector is nonzero.
-/
theorem left_ne_zero_of_oangle_ne_zero {x y : V} (h : o.oangle x y ≠ 0) : x ≠ 0 := by
  rintro rfl; simp at h

/-- If the angle between two vectors is nonzero, the second vector is nonzero. -/
/-
**Orientation.right_ne_zero_of_oangle_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：right_ne_zero_of_oangle_ne_zero {x y : V} (h : o.oangle x y != 0) : y != 0
参数：h : o.oangle x y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is nonzero, the second vector is nonzero.
-/
theorem right_ne_zero_of_oangle_ne_zero {x y : V} (h : o.oangle x y ≠ 0) : y ≠ 0 := by
  rintro rfl; simp at h

/-- If the angle between two vectors is nonzero, the vectors are not equal. -/
/-
**Orientation.ne_of_oangle_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：ne_of_oangle_ne_zero {x y : V} (h : o.oangle x y != 0) : x != y
参数：h : o.oangle x y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
If the angle between two vectors is nonzero, the vectors are not equal.
-/
theorem ne_of_oangle_ne_zero {x y : V} (h : o.oangle x y ≠ 0) : x ≠ y := by
  rintro rfl; simp at h

/-- If the angle between two vectors is `π`, the first vector is nonzero. -/
/-
**Orientation.left_ne_zero_of_oangle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Orientatio
n`。
形式化陈述：left_ne_zero_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : x != 0
参数：h : o.oangle x y = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.left_ne_zero_of_oangle_ne_zero`：left_ne_zero_of_oangle_ne_ze
ro {x y : V} (h : o.oangle x y != 0) : x != 0
· 使用定理 `Real.Angle.pi_ne_zero`：pi_ne_zero : (π : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is `π`, the first vector is nonzero.
-/
theorem left_ne_zero_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π`, the second vector is nonzero. -/
/-
**Orientation.right_ne_zero_of_oangle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Orientati
on`。
形式化陈述：right_ne_zero_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : y != 0
参数：h : o.oangle x y = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.right_ne_zero_of_oangle_ne_zero`：right_ne_zero_of_oangle_ne_
zero {x y : V} (h : o.oangle x y != 0) : y != 0
· 使用定理 `Real.Angle.pi_ne_zero`：pi_ne_zero : (π : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is `π`, the second vector is nonzero.
-/
theorem right_ne_zero_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π`, the vectors are not equal. -/
/-
**Orientation.ne_of_oangle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：ne_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : x != y
参数：h : o.oangle x y = π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.ne_of_oangle_ne_zero`：ne_of_oangle_ne_zero {x y : V} (h : o.
oangle x y != 0) : x != y
· 使用定理 `Real.Angle.pi_ne_zero`：pi_ne_zero : (π : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is `π`, the vectors are not equal.
-/
theorem ne_of_oangle_eq_pi {x y : V} (h : o.oangle x y = π) : x ≠ y :=
  o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π / 2`, the first vector is nonzero. -/
/-
**Orientation.left_ne_zero_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Or
ientation`。
形式化陈述：left_ne_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 
: Real)) : x != 0
参数：h : o.oangle x y = (π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Orientation.left_ne_zero_of_oangle_ne_zero`：left_ne_zero_of_oangle_ne_ze
ro {x y : V} (h : o.oangle x y != 0) : x != 0
· 使用定理 `Real.Angle.pi_div_two_ne_zero`：pi_div_two_ne_zero : ((π / 2 : Real) : An
gle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is `π / 2`, the first vector is nonzero.
-/
theorem left_ne_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π / 2`, the second vector is nonzero. -/
/-
**Orientation.right_ne_zero_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `O
rientation`。
形式化陈述：right_ne_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2
 : Real)) : y != 0
参数：h : o.oangle x y = (π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Orientation.right_ne_zero_of_oangle_ne_zero`：right_ne_zero_of_oangle_ne_
zero {x y : V} (h : o.oangle x y != 0) : y != 0
· 使用定理 `Real.Angle.pi_div_two_ne_zero`：pi_div_two_ne_zero : ((π / 2 : Real) : An
gle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is `π / 2`, the second vector is nonzero.
-/
theorem right_ne_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `π / 2`, the vectors are not equal. -/
/-
**Orientation.ne_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：ne_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) :
 x != y
参数：h : o.oangle x y = (π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Orientation.ne_of_oangle_ne_zero`：ne_of_oangle_ne_zero {x y : V} (h : o.
oangle x y != 0) : x != y
· 使用定理 `Real.Angle.pi_div_two_ne_zero`：pi_div_two_ne_zero : ((π / 2 : Real) : An
gle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is `π / 2`, the vectors are not equal.
-/
theorem ne_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) : x ≠ y :=
  o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `-π / 2`, the first vector is nonzero. -/
/-
**Orientation.left_ne_zero_of_oangle_eq_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间
 `Orientation`。
形式化陈述：left_ne_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π
 / 2 : Real)) : x != 0
参数：h : o.oangle x y = (-π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Orientation.left_ne_zero_of_oangle_ne_zero`：left_ne_zero_of_oangle_ne_ze
ro {x y : V} (h : o.oangle x y != 0) : x != 0
· 使用定理 `Real.Angle.neg_pi_div_two_ne_zero`：neg_pi_div_two_ne_zero : ((-π / 2 : R
eal) : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is `-π / 2`, the first vector is nonzero.
-/
theorem left_ne_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) :
    x ≠ 0 :=
  o.left_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `-π / 2`, the second vector is nonzero. -/
/-
**Orientation.right_ne_zero_of_oangle_eq_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空
间 `Orientation`。
形式化陈述：right_ne_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-
π / 2 : Real)) : y != 0
参数：h : o.oangle x y = (-π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Orientation.right_ne_zero_of_oangle_ne_zero`：right_ne_zero_of_oangle_ne_
zero {x y : V} (h : o.oangle x y != 0) : y != 0
· 使用定理 `Real.Angle.neg_pi_div_two_ne_zero`：neg_pi_div_two_ne_zero : ((-π / 2 : R
eal) : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is `-π / 2`, the second vector is nonzero.
-/
theorem right_ne_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) :
    y ≠ 0 :=
  o.right_ne_zero_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the angle between two vectors is `-π / 2`, the vectors are not equal. -/
/-
**Orientation.ne_of_oangle_eq_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Orientat
ion`。
形式化陈述：ne_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : Rea
l)) : x != y
参数：h : o.oangle x y = (-π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Orientation.ne_of_oangle_ne_zero`：ne_of_oangle_ne_zero {x y : V} (h : o.
oangle x y != 0) : x != y
· 使用定理 `Real.Angle.neg_pi_div_two_ne_zero`：neg_pi_div_two_ne_zero : ((-π / 2 : R
eal) : Angle) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the angle between two vectors is `-π / 2`, the vectors are not equal.
-/
theorem ne_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) : x ≠ y :=
  o.ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : o.oangle x y ≠ 0)

/-- If the sign of the angle between two vectors is nonzero, the first vector is nonzero. -/
/-
**Orientation.left_ne_zero_of_oangle_sign_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ori
entation`。
形式化陈述：left_ne_zero_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign != 
0) : x != 0
参数：h : (o.oangle x y).sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.left_ne_zero_of_oangle_ne_zero`：left_ne_zero_of_oangle_ne_ze
ro {x y : V} (h : o.oangle x y != 0) : x != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.sign_ne_zero_iff`：sign_ne_zero_iff {θ : Angle} : θ.sign != 0 
↔ θ != 0 ∧ θ != π

--- 原说明 ---
If the sign of the angle between two vectors is nonzero, the first vector is non
zero.
-/
theorem left_ne_zero_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign ≠ 0) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between two vectors is nonzero, the second vector is nonzero. -/
/-
**Orientation.right_ne_zero_of_oangle_sign_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Or
ientation`。
形式化陈述：right_ne_zero_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign !=
 0) : y != 0
参数：h : (o.oangle x y).sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.right_ne_zero_of_oangle_ne_zero`：right_ne_zero_of_oangle_ne_
zero {x y : V} (h : o.oangle x y != 0) : y != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.sign_ne_zero_iff`：sign_ne_zero_iff {θ : Angle} : θ.sign != 0 
↔ θ != 0 ∧ θ != π

--- 原说明 ---
If the sign of the angle between two vectors is nonzero, the second vector is no
nzero.
-/
theorem right_ne_zero_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign ≠ 0) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between two vectors is nonzero, the vectors are not equal. -/
/-
**Orientation.ne_of_oangle_sign_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：ne_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign != 0) : x != 
y
参数：h : (o.oangle x y).sign != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.ne_of_oangle_ne_zero`：ne_of_oangle_ne_zero {x y : V} (h : o.
oangle x y != 0) : x != y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.sign_ne_zero_iff`：sign_ne_zero_iff {θ : Angle} : θ.sign != 0 
↔ θ != 0 ∧ θ != π

--- 原说明 ---
If the sign of the angle between two vectors is nonzero, the vectors are not equ
al.
-/
theorem ne_of_oangle_sign_ne_zero {x y : V} (h : (o.oangle x y).sign ≠ 0) : x ≠ y :=
  o.ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1

/-- If the sign of the angle between two vectors is positive, the first vector is nonzero. -/
/-
**Orientation.left_ne_zero_of_oangle_sign_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Orie
ntation`。
形式化陈述：left_ne_zero_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1)
 : x != 0
参数：h : (o.oangle x y).sign = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.left_ne_zero_of_oangle_sign_ne_zero`：left_ne_zero_of_oangle_
sign_ne_zero {x y : V} (h : (o.oangle x y).sign != 0) : x != 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between two vectors is positive, the first vector is no
nzero.
-/
theorem left_ne_zero_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is positive, the second vector is nonzero. -/
/-
**Orientation.right_ne_zero_of_oangle_sign_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Ori
entation`。
形式化陈述：right_ne_zero_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1
) : y != 0
参数：h : (o.oangle x y).sign = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.right_ne_zero_of_oangle_sign_ne_zero`：right_ne_zero_of_oangl
e_sign_ne_zero {x y : V} (h : (o.oangle x y).sign != 0) : y != 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between two vectors is positive, the second vector is n
onzero.
-/
theorem right_ne_zero_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is positive, the vectors are not equal. -/
/-
**Orientation.ne_of_oangle_sign_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：ne_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : x != y
参数：h : (o.oangle x y).sign = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.ne_of_oangle_sign_ne_zero`：ne_of_oangle_sign_ne_zero {x y : 
V} (h : (o.oangle x y).sign != 0) : x != y
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between two vectors is positive, the vectors are not eq
ual.
-/
theorem ne_of_oangle_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : x ≠ y :=
  o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is negative, the first vector is nonzero. -/
/-
**Orientation.left_ne_zero_of_oangle_sign_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `
Orientation`。
形式化陈述：left_ne_zero_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign 
= -1) : x != 0
参数：h : (o.oangle x y).sign = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.left_ne_zero_of_oangle_sign_ne_zero`：left_ne_zero_of_oangle_
sign_ne_zero {x y : V} (h : (o.oangle x y).sign != 0) : x != 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between two vectors is negative, the first vector is no
nzero.
-/
theorem left_ne_zero_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : x ≠ 0 :=
  o.left_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is negative, the second vector is nonzero. -/
/-
**Orientation.right_ne_zero_of_oangle_sign_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 
`Orientation`。
形式化陈述：right_ne_zero_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign
 = -1) : y != 0
参数：h : (o.oangle x y).sign = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.right_ne_zero_of_oangle_sign_ne_zero`：right_ne_zero_of_oangl
e_sign_ne_zero {x y : V} (h : (o.oangle x y).sign != 0) : y != 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between two vectors is negative, the second vector is n
onzero.
-/
theorem right_ne_zero_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : y ≠ 0 :=
  o.right_ne_zero_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- If the sign of the angle between two vectors is negative, the vectors are not equal. -/
/-
**Orientation.ne_of_oangle_sign_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Orientatio
n`。
形式化陈述：ne_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : x 
!= y
参数：h : (o.oangle x y).sign = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.ne_of_oangle_sign_ne_zero`：ne_of_oangle_sign_ne_zero {x y : 
V} (h : (o.oangle x y).sign != 0) : x != y
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the sign of the angle between two vectors is negative, the vectors are not eq
ual.
-/
theorem ne_of_oangle_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) : x ≠ y :=
  o.ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (o.oangle x y).sign ≠ 0)

/-- Swapping the two vectors passed to `oangle` negates the angle. -/
/-
**Orientation.oangle_rev** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_rev (x y : V) : o.oangle y x = -o.oangle x y
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.kahler_swap`：kahler_swap (x y : E) : o.kahler x y = conj (o.
kahler y x)
· 使用定理 `Complex.arg_conj_coe_angle`：arg_conj_coe_angle (x : Complex) : (arg (con
j x) : Real.Angle) = -arg x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Swapping the two vectors passed to `oangle` negates the angle.
-/
theorem oangle_rev (x y : V) : o.oangle y x = -o.oangle x y := by
  simp only [oangle, o.kahler_swap y x, Complex.arg_conj_coe_angle]

/-- Adding the angles between two vectors in each order results in 0. -/
@[simp]
/-
**Orientation.oangle_add_oangle_rev** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_oangle_rev (x y : V) : o.oangle x y + o.oangle y x = 0
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Adding the angles between two vectors in each order results in 0.
-/
theorem oangle_add_oangle_rev (x y : V) : o.oangle x y + o.oangle y x = 0 := by
  simp [o.oangle_rev y x]

/-- Negating the first vector passed to `oangle` adds `π` to the angle. -/
/-
**Orientation.oangle_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_neg_left {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle (-x) y = 
o.oangle x y + π
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.arg_neg_coe_angle`：arg_neg_coe_angle {x : Complex} (hx : x != 0)
 : (arg (-x) : Real.Angle) = arg x + π
· 使用定理 `Orientation.kahler_ne_zero`：kahler_ne_zero {x y : E} (hx : x != 0) (hy :
 y != 0) : o.kahler x y != 0

--- 原说明 ---
Negating the first vector passed to `oangle` adds `π` to the angle.
-/
theorem oangle_neg_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    o.oangle (-x) y = o.oangle x y + π := by
  simp only [oangle, map_neg]
  convert! Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

/-- Negating the second vector passed to `oangle` adds `π` to the angle. -/
/-
**Orientation.oangle_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_neg_right {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle x (-y) =
 o.oangle x y + π
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Complex.arg_neg_coe_angle`：arg_neg_coe_angle {x : Complex} (hx : x != 0)
 : (arg (-x) : Real.Angle) = arg x + π
· 使用定理 `Orientation.kahler_ne_zero`：kahler_ne_zero {x y : E} (hx : x != 0) (hy :
 y != 0) : o.kahler x y != 0

--- 原说明 ---
Negating the second vector passed to `oangle` adds `π` to the angle.
-/
theorem oangle_neg_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    o.oangle x (-y) = o.oangle x y + π := by
  simp only [oangle, map_neg]
  convert! Complex.arg_neg_coe_angle _
  exact o.kahler_ne_zero hx hy

/-- Negating the first vector passed to `oangle` does not change twice the angle. -/
@[simp]
/-
**Orientation.two_zsmul_oangle_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：two_zsmul_oangle_neg_left (x y : V) : (2 : Int) • o.oangle (-x) y = (2 : I
nt) • o.oangle x y
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle_neg_left`：oangle_neg_left {x y : V} (hx : x != 0) (hy
 : y != 0) : o.oangle (-x) y = o.oangle x y + π
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Real.Angle.two_zsmul_coe_pi`：two_zsmul_coe_pi : (2 : Int) • (π : Angle) 
= 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Negating the first vector passed to `oangle` does not change twice the angle.
-/
theorem two_zsmul_oangle_neg_left (x y : V) :
    (2 : ℤ) • o.oangle (-x) y = (2 : ℤ) • o.oangle x y := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_left hx hy]

/-- Negating the second vector passed to `oangle` does not change twice the angle. -/
@[simp]
/-
**Orientation.two_zsmul_oangle_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：two_zsmul_oangle_neg_right (x y : V) : (2 : Int) • o.oangle x (-y) = (2 : 
Int) • o.oangle x y
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle_neg_right`：oangle_neg_right {x y : V} (hx : x != 0) (
hy : y != 0) : o.oangle x (-y) = o.oangle x y + π
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Real.Angle.two_zsmul_coe_pi`：two_zsmul_coe_pi : (2 : Int) • (π : Angle) 
= 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Negating the second vector passed to `oangle` does not change twice the angle.
-/
theorem two_zsmul_oangle_neg_right (x y : V) :
    (2 : ℤ) • o.oangle x (-y) = (2 : ℤ) • o.oangle x y := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [o.oangle_neg_right hx hy]

/-- Negating both vectors passed to `oangle` does not change the angle. -/
@[simp]
/-
**Orientation.oangle_neg_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_neg_neg (x y : V) : o.oangle (-x) (-y) = o.oangle x y
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Negating both vectors passed to `oangle` does not change the angle.
-/
theorem oangle_neg_neg (x y : V) : o.oangle (-x) (-y) = o.oangle x y := by simp [oangle]

/-- Negating the first vector produces the same angle as negating the second vector. -/
/-
**Orientation.oangle_neg_left_eq_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientatio
n`。
形式化陈述：oangle_neg_left_eq_neg_right (x y : V) : o.oangle (-x) y = o.oangle x (-y)
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Orientation.oangle_neg_neg`：oangle_neg_neg (x y : V) : o.oangle (-x) (-y
) = o.oangle x y

--- 原说明 ---
Negating the first vector produces the same angle as negating the second vector.
-/
theorem oangle_neg_left_eq_neg_right (x y : V) : o.oangle (-x) y = o.oangle x (-y) := by
  rw [← neg_neg y, oangle_neg_neg, neg_neg]

/-- The angle between the negation of a nonzero vector and that vector is `π`. -/
@[simp]
/-
**Orientation.oangle_neg_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_neg_self_left {x : V} (hx : x != 0) : o.oangle (-x) x = π
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_neg_left`：oangle_neg_left {x y : V} (hx : x != 0) (hy
 : y != 0) : o.oangle (-x) y = o.oangle x y + π
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The angle between the negation of a nonzero vector and that vector is `π`.
-/
theorem oangle_neg_self_left {x : V} (hx : x ≠ 0) : o.oangle (-x) x = π := by
  simp [oangle_neg_left, hx]

/-- The angle between a nonzero vector and its negation is `π`. -/
@[simp]
/-
**Orientation.oangle_neg_self_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_neg_self_right {x : V} (hx : x != 0) : o.oangle x (-x) = π
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_neg_right`：oangle_neg_right {x y : V} (hx : x != 0) (
hy : y != 0) : o.oangle x (-y) = o.oangle x y + π
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The angle between a nonzero vector and its negation is `π`.
-/
theorem oangle_neg_self_right {x : V} (hx : x ≠ 0) : o.oangle x (-x) = π := by
  simp [oangle_neg_right, hx]

/-- Twice the angle between the negation of a vector and that vector is 0. -/
/-
**Orientation.two_zsmul_oangle_neg_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientat
ion`。
形式化陈述：two_zsmul_oangle_neg_self_left (x : V) : (2 : Int) • o.oangle (-x) x = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_neg_self_left`：oangle_neg_self_left {x : V} (hx : x !
= 0) : o.oangle (-x) x = π
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.Angle.two_zsmul_coe_pi`：two_zsmul_coe_pi : (2 : Int) • (π : Angle) 
= 0

--- 原说明 ---
Twice the angle between the negation of a vector and that vector is 0.
-/
theorem two_zsmul_oangle_neg_self_left (x : V) : (2 : ℤ) • o.oangle (-x) x = 0 := by
  by_cases hx : x = 0 <;> simp [hx]

/-- Twice the angle between a vector and its negation is 0. -/
/-
**Orientation.two_zsmul_oangle_neg_self_right** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：two_zsmul_oangle_neg_self_right (x : V) : (2 : Int) • o.oangle x (-x) = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_neg_self_right`：oangle_neg_self_right {x : V} (hx : x
 != 0) : o.oangle x (-x) = π
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.Angle.two_zsmul_coe_pi`：two_zsmul_coe_pi : (2 : Int) • (π : Angle) 
= 0

--- 原说明 ---
Twice the angle between a vector and its negation is 0.
-/
theorem two_zsmul_oangle_neg_self_right (x : V) : (2 : ℤ) • o.oangle x (-x) = 0 := by
  by_cases hx : x = 0 <;> simp [hx]

/-- Adding the angles between two vectors in each order, with the first vector in each angle
negated, results in 0. -/
@[simp]
/-
**Orientation.oangle_add_oangle_rev_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientat
ion`。
形式化陈述：oangle_add_oangle_rev_neg_left (x y : V) : o.oangle (-x) y + o.oangle (-y)
 x = 0
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_neg_left_eq_neg_right`：oangle_neg_left_eq_neg_right (
x y : V) : o.oangle (-x) y = o.oangle x (-y)
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0

--- 原说明 ---
Adding the angles between two vectors in each order, with the first vector in ea
ch angle
negated, results in 0.
-/
theorem oangle_add_oangle_rev_neg_left (x y : V) : o.oangle (-x) y + o.oangle (-y) x = 0 := by
  rw [oangle_neg_left_eq_neg_right, oangle_rev, neg_add_cancel]

/-- Adding the angles between two vectors in each order, with the second vector in each angle
negated, results in 0. -/
@[simp]
/-
**Orientation.oangle_add_oangle_rev_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：oangle_add_oangle_rev_neg_right (x y : V) : o.oangle x (-y) + o.oangle y (
-x) = 0
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_left_eq_neg_right`：oangle_neg_left_eq_neg_right (
x y : V) : o.oangle (-x) y = o.oangle x (-y)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0

--- 原说明 ---
Adding the angles between two vectors in each order, with the second vector in e
ach angle
negated, results in 0.
-/
theorem oangle_add_oangle_rev_neg_right (x y : V) : o.oangle x (-y) + o.oangle y (-x) = 0 := by
  rw [o.oangle_rev (-x), oangle_neg_left_eq_neg_right, add_neg_cancel]

/-- Multiplying the first vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
/-
**Orientation.oangle_smul_left_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_smul_left_of_pos (x y : V) {r : Real} (hr : 0 < r) : o.oangle (r • 
x) y = o.oangle x y
参数：x y : V；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Complex.arg_real_mul`：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r)
 : arg (r * x) = arg x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Multiplying the first vector passed to `oangle` by a positive real does not chan
ge the
angle.
-/
theorem oangle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
    o.oangle (r • x) y = o.oangle x y := by simp [oangle, Complex.arg_real_mul _ hr]

/-- Multiplying the second vector passed to `oangle` by a positive real does not change the
angle. -/
@[simp]
/-
**Orientation.oangle_smul_right_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_smul_right_of_pos (x y : V) {r : Real} (hr : 0 < r) : o.oangle x (r
 • y) = o.oangle x y
参数：x y : V；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Complex.arg_real_mul`：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r)
 : arg (r * x) = arg x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Multiplying the second vector passed to `oangle` by a positive real does not cha
nge the
angle.
-/
theorem oangle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) :
    o.oangle x (r • y) = o.oangle x y := by simp [oangle, Complex.arg_real_mul _ hr]

/-- Multiplying the first vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
/-
**Orientation.oangle_smul_left_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_smul_left_of_neg (x y : V) {r : Real} (hr : r < 0) : o.oangle (r • 
x) y = o.oangle (-x) y
参数：x y : V；hr : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Orientation.oangle_smul_left_of_pos`：oangle_smul_left_of_pos (x y : V) {
r : Real} (hr : 0 < r) : o.oangle (r • x) y = o.oangle x y
· 使用定理 `neg_pos_of_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a : α}, a < 0 → 0 < -a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
Multiplying the first vector passed to `oangle` by a negative real produces the 
same angle
as negating that vector.
-/
theorem oangle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
    o.oangle (r • x) y = o.oangle (-x) y := by
  rw [← neg_neg r, neg_smul, ← smul_neg, o.oangle_smul_left_of_pos _ _ (neg_pos_of_neg hr)]

/-- Multiplying the second vector passed to `oangle` by a negative real produces the same angle
as negating that vector. -/
@[simp]
/-
**Orientation.oangle_smul_right_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_smul_right_of_neg (x y : V) {r : Real} (hr : r < 0) : o.oangle x (r
 • y) = o.oangle x (-y)
参数：x y : V；hr : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Orientation.oangle_smul_right_of_pos`：oangle_smul_right_of_pos (x y : V)
 {r : Real} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y
· 使用定理 `neg_pos_of_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a : α}, a < 0 → 0 < -a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
Multiplying the second vector passed to `oangle` by a negative real produces the
 same angle
as negating that vector.
-/
theorem oangle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) :
    o.oangle x (r • y) = o.oangle x (-y) := by
  rw [← neg_neg r, neg_smul, ← smul_neg, o.oangle_smul_right_of_pos _ _ (neg_pos_of_neg hr)]

/-- The angle between a nonnegative multiple of a vector and that vector is 0. -/
@[simp]
/-
**Orientation.oangle_smul_left_self_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：oangle_smul_left_self_of_nonneg (x : V) {r : Real} (hr : 0 <= r) : o.oangl
e (r • x) x = 0
参数：x : V；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_left_of_pos`：oangle_smul_left_of_pos (x y : V) {
r : Real} (hr : 0 < r) : o.oangle (r • x) y = o.oangle x y
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0

--- 原说明 ---
The angle between a nonnegative multiple of a vector and that vector is 0.
-/
theorem oangle_smul_left_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) : o.oangle (r • x) x = 0 := by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

/-- The angle between a vector and a nonnegative multiple of that vector is 0. -/
@[simp]
/-
**Orientation.oangle_smul_right_self_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Orient
ation`。
形式化陈述：oangle_smul_right_self_of_nonneg (x : V) {r : Real} (hr : 0 <= r) : o.oang
le x (r • x) = 0
参数：x : V；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_right_of_pos`：oangle_smul_right_of_pos (x y : V)
 {r : Real} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0

--- 原说明 ---
The angle between a vector and a nonnegative multiple of that vector is 0.
-/
theorem oangle_smul_right_self_of_nonneg (x : V) {r : ℝ} (hr : 0 ≤ r) : o.oangle x (r • x) = 0 := by
  rcases hr.lt_or_eq with (h | h)
  · simp [h]
  · simp [h.symm]

/-- The angle between two nonnegative multiples of the same vector is 0. -/
@[simp]
/-
**Orientation.oangle_smul_smul_self_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：oangle_smul_smul_self_of_nonneg (x : V) {r₁ r₂ : Real} (hr₁ : 0 <= r₁) (hr
₂ : 0 <= r₂) : o.oangle (r₁ • x) (r₂ • x) = 0
参数：x : V；hr₁ : 0 <= r₁；hr₂ : 0 <= r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_left_of_pos`：oangle_smul_left_of_pos (x y : V) {
r : Real} (hr : 0 < r) : o.oangle (r • x) y = o.oangle x y
· 使用定理 `Orientation.oangle_smul_right_self_of_nonneg`：oangle_smul_right_self_of_
nonneg (x : V) {r : Real} (hr : 0 <= r) : o.oangle x (r • x) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0

--- 原说明 ---
The angle between two nonnegative multiples of the same vector is 0.
-/
theorem oangle_smul_smul_self_of_nonneg (x : V) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    o.oangle (r₁ • x) (r₂ • x) = 0 := by
  rcases hr₁.lt_or_eq with (h | h)
  · simp [h, hr₂]
  · simp [h.symm]

/-- Multiplying the first vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
/-
**Orientation.two_zsmul_oangle_smul_left_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `O
rientation`。
形式化陈述：two_zsmul_oangle_smul_left_of_ne_zero (x y : V) {r : Real} (hr : r != 0) :
 (2 : Int) • o.oangle (r • x) y = (2 : Int) • o.oangle x y
参数：x y : V；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_left_of_neg`：oangle_smul_left_of_neg (x y : V) {
r : Real} (hr : r < 0) : o.oangle (r • x) y = o.oangle (-x) y
· 使用定理 `Orientation.two_zsmul_oangle_neg_left`：two_zsmul_oangle_neg_left (x y : 
V) : (2 : Int) • o.oangle (-x) y = (2 : Int) • o.oangle x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_smul_left_of_pos`：oangle_smul_left_of_pos (x y : V) {
r : Real} (hr : 0 < r) : o.oangle (r • x) y = o.oangle x y

--- 原说明 ---
Multiplying the first vector passed to `oangle` by a nonzero real does not chang
e twice the
angle.
-/
theorem two_zsmul_oangle_smul_left_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
    (2 : ℤ) • o.oangle (r • x) y = (2 : ℤ) • o.oangle x y := by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

/-- Multiplying the second vector passed to `oangle` by a nonzero real does not change twice the
angle. -/
@[simp]
/-
**Orientation.two_zsmul_oangle_smul_right_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Orientation`。
形式化陈述：two_zsmul_oangle_smul_right_of_ne_zero (x y : V) {r : Real} (hr : r != 0) 
: (2 : Int) • o.oangle x (r • y) = (2 : Int) • o.oangle x y
参数：x y : V；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_right_of_neg`：oangle_smul_right_of_neg (x y : V)
 {r : Real} (hr : r < 0) : o.oangle x (r • y) = o.oangle x (-y)
· 使用定理 `Orientation.two_zsmul_oangle_neg_right`：two_zsmul_oangle_neg_right (x y 
: V) : (2 : Int) • o.oangle x (-y) = (2 : Int) • o.oangle x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_smul_right_of_pos`：oangle_smul_right_of_pos (x y : V)
 {r : Real} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y

--- 原说明 ---
Multiplying the second vector passed to `oangle` by a nonzero real does not chan
ge twice the
angle.
-/
theorem two_zsmul_oangle_smul_right_of_ne_zero (x y : V) {r : ℝ} (hr : r ≠ 0) :
    (2 : ℤ) • o.oangle x (r • y) = (2 : ℤ) • o.oangle x y := by
  rcases hr.lt_or_gt with (h | h) <;> simp [h]

/-- Twice the angle between a multiple of a vector and that vector is 0. -/
@[simp]
/-
**Orientation.two_zsmul_oangle_smul_left_self** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：two_zsmul_oangle_smul_left_self (x : V) {r : Real} : (2 : Int) • o.oangle 
(r • x) x = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_left_of_neg`：oangle_smul_left_of_neg (x y : V) {
r : Real} (hr : r < 0) : o.oangle (r • x) y = o.oangle (-x) y
· 使用定理 `Orientation.two_zsmul_oangle_neg_left`：two_zsmul_oangle_neg_left (x y : 
V) : (2 : Int) • o.oangle (-x) y = (2 : Int) • o.oangle x y
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_smul_left_self_of_nonneg`：oangle_smul_left_self_of_no
nneg (x : V) {r : Real} (hr : 0 <= r) : o.oangle (r • x) x = 0

--- 原说明 ---
Twice the angle between a multiple of a vector and that vector is 0.
-/
theorem two_zsmul_oangle_smul_left_self (x : V) {r : ℝ} : (2 : ℤ) • o.oangle (r • x) x = 0 := by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

/-- Twice the angle between a vector and a multiple of that vector is 0. -/
@[simp]
/-
**Orientation.two_zsmul_oangle_smul_right_self** 是 Mathlib 中的一个定理，位于命名空间 `Orient
ation`。
形式化陈述：two_zsmul_oangle_smul_right_self (x : V) {r : Real} : (2 : Int) • o.oangle
 x (r • x) = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_right_of_neg`：oangle_smul_right_of_neg (x y : V)
 {r : Real} (hr : r < 0) : o.oangle x (r • y) = o.oangle x (-y)
· 使用定理 `Orientation.two_zsmul_oangle_neg_right`：two_zsmul_oangle_neg_right (x y 
: V) : (2 : Int) • o.oangle x (-y) = (2 : Int) • o.oangle x y
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_smul_right_self_of_nonneg`：oangle_smul_right_self_of_
nonneg (x : V) {r : Real} (hr : 0 <= r) : o.oangle x (r • x) = 0

--- 原说明 ---
Twice the angle between a vector and a multiple of that vector is 0.
-/
theorem two_zsmul_oangle_smul_right_self (x : V) {r : ℝ} : (2 : ℤ) • o.oangle x (r • x) = 0 := by
  rcases lt_or_ge r 0 with (h | h) <;> simp [h]

/-- Twice the angle between two multiples of a vector is 0. -/
@[simp]
/-
**Orientation.two_zsmul_oangle_smul_smul_self** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：two_zsmul_oangle_smul_smul_self (x : V) {r₁ r₂ : Real} : (2 : Int) • o.oan
gle (r₁ • x) (r₂ • x) = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.two_zsmul_oangle_smul_left_of_ne_zero`：two_zsmul_oangle_smul
_left_of_ne_zero (x y : V) {r : Real} (hr : r != 0) : (2 : Int) • o.oangle (r • 
x) y = (2 : Int) • o.oangle x y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Orientation.two_zsmul_oangle_smul_right_self`：two_zsmul_oangle_smul_righ
t_self (x : V) {r : Real} : (2 : Int) • o.oangle x (r • x) = 0

--- 原说明 ---
Twice the angle between two multiples of a vector is 0.
-/
theorem two_zsmul_oangle_smul_smul_self (x : V) {r₁ r₂ : ℝ} :
    (2 : ℤ) • o.oangle (r₁ • x) (r₂ • x) = 0 := by by_cases h : r₁ = 0 <;> simp [h]

/-- If the spans of two vectors are equal, twice angles with those vectors on the left are
equal. -/
/-
**Orientation.two_zsmul_oangle_left_of_span_eq** 是 Mathlib 中的一个定理，位于命名空间 `Orient
ation`。
形式化陈述：two_zsmul_oangle_left_of_span_eq {x y : V} (z : V) (h : Real ∙ x = Real ∙ 
y) : (2 : Int) • o.oangle x z = (2 : Int) • o.oangle y z
参数：z : V；h : Real ∙ x = Real ∙ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_singleton_eq_span_singleton`：span_singleton_eq_span_singl
eton {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.I
sTorsionFree R M] {x y : M} : (R…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.two_zsmul_oangle_smul_left_of_ne_zero`：two_zsmul_oangle_smul
_left_of_ne_zero (x y : V) {r : Real} (hr : r != 0) : (2 : Int) • o.oangle (r • 
x) y = (2 : Int) • o.oangle x y
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0

--- 原说明 ---
If the spans of two vectors are equal, twice angles with those vectors on the le
ft are
equal.
-/
theorem two_zsmul_oangle_left_of_span_eq {x y : V} (z : V) (h : ℝ ∙ x = ℝ ∙ y) :
    (2 : ℤ) • o.oangle x z = (2 : ℤ) • o.oangle y z := by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_left_of_ne_zero _ _ (Units.ne_zero _)).symm

/-- If the spans of two vectors are equal, twice angles with those vectors on the right are
equal. -/
/-
**Orientation.two_zsmul_oangle_right_of_span_eq** 是 Mathlib 中的一个定理，位于命名空间 `Orien
tation`。
形式化陈述：two_zsmul_oangle_right_of_span_eq (x : V) {y z : V} (h : Real ∙ y = Real ∙
 z) : (2 : Int) • o.oangle x y = (2 : Int) • o.oangle x z
参数：x : V；h : Real ∙ y = Real ∙ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_singleton_eq_span_singleton`：span_singleton_eq_span_singl
eton {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.I
sTorsionFree R M] {x y : M} : (R…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.two_zsmul_oangle_smul_right_of_ne_zero`：two_zsmul_oangle_smu
l_right_of_ne_zero (x y : V) {r : Real} (hr : r != 0) : (2 : Int) • o.oangle x (
r • y) = (2 : Int) • o.oangle x y
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0

--- 原说明 ---
If the spans of two vectors are equal, twice angles with those vectors on the ri
ght are
equal.
-/
theorem two_zsmul_oangle_right_of_span_eq (x : V) {y z : V} (h : ℝ ∙ y = ℝ ∙ z) :
    (2 : ℤ) • o.oangle x y = (2 : ℤ) • o.oangle x z := by
  rw [Submodule.span_singleton_eq_span_singleton] at h
  rcases h with ⟨r, rfl⟩
  exact (o.two_zsmul_oangle_smul_right_of_ne_zero _ _ (Units.ne_zero _)).symm

/-- If the spans of two pairs of vectors are equal, twice angles between those vectors are
equal. -/
/-
**Orientation.two_zsmul_oangle_of_span_eq_of_span_eq** 是 Mathlib 中的一个定理，位于命名空间 `
Orientation`。
形式化陈述：two_zsmul_oangle_of_span_eq_of_span_eq {w x y z : V} (hwx : Real ∙ w = Rea
l ∙ x) (hyz : Real ∙ y = Real ∙ z) : (2 : Int) • o.oangle w y = (2 : Int) • o.oa
ngle x z
参数：hwx : Real ∙ w = Real ∙ x；hyz : Real ∙ y = Real ∙ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.two_zsmul_oangle_left_of_span_eq`：two_zsmul_oangle_left_of_s
pan_eq {x y : V} (z : V) (h : Real ∙ x = Real ∙ y) : (2 : Int) • o.oangle x z = 
(2 : Int) • o.oangle y z
· 使用定理 `Orientation.two_zsmul_oangle_right_of_span_eq`：two_zsmul_oangle_right_of
_span_eq (x : V) {y z : V} (h : Real ∙ y = Real ∙ z) : (2 : Int) • o.oangle x y 
= (2 : Int) • o.oangle x z

--- 原说明 ---
If the spans of two pairs of vectors are equal, twice angles between those vecto
rs are
equal.
-/
theorem two_zsmul_oangle_of_span_eq_of_span_eq {w x y z : V} (hwx : ℝ ∙ w = ℝ ∙ x)
    (hyz : ℝ ∙ y = ℝ ∙ z) : (2 : ℤ) • o.oangle w y = (2 : ℤ) • o.oangle x z := by
  rw [o.two_zsmul_oangle_left_of_span_eq y hwx, o.two_zsmul_oangle_right_of_span_eq x hyz]

/-- The oriented angle between two vectors is zero if and only if the angle with the vectors
swapped is zero. -/
/-
**Orientation.oangle_eq_zero_iff_oangle_rev_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `O
rientation`。
形式化陈述：oangle_eq_zero_iff_oangle_rev_eq_zero {x y : V} : o.oangle x y = 0 ↔ o.oan
gle y x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The oriented angle between two vectors is zero if and only if the angle with the
 vectors
swapped is zero.
-/
theorem oangle_eq_zero_iff_oangle_rev_eq_zero {x y : V} : o.oangle x y = 0 ↔ o.oangle y x = 0 := by
  rw [oangle_rev, neg_eq_zero]

/-- The oriented angle between two vectors is zero if and only if they are on the same ray. -/
/-
**Orientation.oangle_eq_zero_iff_sameRay** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：oangle_eq_zero_iff_sameRay {x y : V} : o.oangle x y = 0 ↔ SameRay Real x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.eq_1`：∀ {V : Type u_1} [inst : NormedAddCommGroup V] 
[inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)]   (o :
 Orientation …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Orientation.kahler_apply_apply`：kahler_apply_apply (x y : E) : o.kahler 
x y = ⟪x, y⟫ + ω x y • Complex.I
· 使用定理 `Complex.arg_coe_angle_eq_iff_eq_toReal`：arg_coe_angle_eq_iff_eq_toReal {
z : Complex} {θ : Real.Angle} : (arg z : Real.Angle) = θ ↔ arg z = θ.toReal
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `Complex.arg_eq_zero_iff`：arg_eq_zero_iff {z : Complex} : arg z = 0 ↔ 0 <
= z.re ∧ z.im = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay`：nonneg_inner_
and_areaForm_eq_zero_iff_sameRay (x y : E) : 0 <= ⟪x, y⟫ ∧ ω x y = 0 ↔ SameRay R
eal x y

--- 原说明 ---
The oriented angle between two vectors is zero if and only if they are on the sa
me ray.
-/
theorem oangle_eq_zero_iff_sameRay {x y : V} : o.oangle x y = 0 ↔ SameRay ℝ x y := by
  rw [oangle, kahler_apply_apply, Complex.arg_coe_angle_eq_iff_eq_toReal, Real.Angle.toReal_zero,
    Complex.arg_eq_zero_iff]
  simpa using o.nonneg_inner_and_areaForm_eq_zero_iff_sameRay x y

/-- The oriented angle between two vectors is `π` if and only if the angle with the vectors
swapped is `π`. -/
/-
**Orientation.oangle_eq_pi_iff_oangle_rev_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Orien
tation`。
形式化陈述：oangle_eq_pi_iff_oangle_rev_eq_pi {x y : V} : o.oangle x y = π ↔ o.oangle 
y x = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The oriented angle between two vectors is `π` if and only if the angle with the 
vectors
swapped is `π`.
-/
theorem oangle_eq_pi_iff_oangle_rev_eq_pi {x y : V} : o.oangle x y = π ↔ o.oangle y x = π := by
  rw [oangle_rev, neg_eq_iff_eq_neg, Real.Angle.neg_coe_pi]

/-- The oriented angle between two vectors is `π` if and only if they are nonzero and the first is
on the same ray as the negation of the second. -/
/-
**Orientation.oangle_eq_pi_iff_sameRay_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientatio
n`。
形式化陈述：oangle_eq_pi_iff_sameRay_neg {x y : V} : o.oangle x y = π ↔ x != 0 ∧ y != 
0 ∧ SameRay Real x (-y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_eq_zero_iff_sameRay`：oangle_eq_zero_iff_sameRay {x y 
: V} : o.oangle x y = 0 ↔ SameRay Real x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Real.Angle.pi_ne_zero`：pi_ne_zero : (π : Angle) != 0
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `Orientation.oangle_neg_right`：oangle_neg_right {x y : V} (hx : x != 0) (
hy : y != 0) : o.oangle x (-y) = o.oangle x y + π
· 使用定理 `Real.Angle.coe_pi_add_coe_pi`：coe_pi_add_coe_pi : (π : Real.Angle) + π =
 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Real.Angle.sub_coe_pi_eq_add_coe_pi`：sub_coe_pi_eq_add_coe_pi (θ : Angle
) : θ - π = θ + π

--- 原说明 ---
The oriented angle between two vectors is `π` if and only if they are nonzero an
d the first is
on the same ray as the negation of the second.
-/
theorem oangle_eq_pi_iff_sameRay_neg {x y : V} :
    o.oangle x y = π ↔ x ≠ 0 ∧ y ≠ 0 ∧ SameRay ℝ x (-y) := by
  rw [← o.oangle_eq_zero_iff_sameRay]
  constructor
  · intro h
    by_cases hx : x = 0; · simp [hx, Real.Angle.pi_ne_zero.symm] at h
    by_cases hy : y = 0; · simp [hy, Real.Angle.pi_ne_zero.symm] at h
    refine ⟨hx, hy, ?_⟩
    rw [o.oangle_neg_right hx hy, h, Real.Angle.coe_pi_add_coe_pi]
  · rintro ⟨hx, hy, h⟩
    rwa [o.oangle_neg_right hx hy, ← Real.Angle.sub_coe_pi_eq_add_coe_pi, sub_eq_zero] at h

/-- The oriented angle between two vectors is zero or `π` if and only if those two vectors are
not linearly independent. -/
/-
**Orientation.oangle_eq_zero_or_eq_pi_iff_not_linearIndependent** 是 Mathlib 中的一个
定理，位于命名空间 `Orientation`。
形式化陈述：oangle_eq_zero_or_eq_pi_iff_not_linearIndependent {x y : V} : o.oangle x y
 = 0 ∨ o.oangle x y = π ↔ ¬LinearIndependent Real ![x, y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_eq_zero_iff_sameRay`：oangle_eq_zero_iff_sameRay {x y 
: V} : o.oangle x y = 0 ↔ SameRay Real x y
· 使用定理 `Orientation.oangle_eq_pi_iff_sameRay_neg`：oangle_eq_pi_iff_sameRay_neg {
x y : V} : o.oangle x y = π ↔ x != 0 ∧ y != 0 ∧ SameRay Real x (-y)
· 使用定理 `sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent`：sameRay_or
_ne_zero_and_sameRay_neg_iff_not_linearIndependent {x y : M} : SameRay R x y ∨ x
 != 0 ∧ y != 0 ∧ SameRay R x (-y) ↔ ¬LinearIndepen…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The oriented angle between two vectors is zero or `π` if and only if those two v
ectors are
not linearly independent.
-/
theorem oangle_eq_zero_or_eq_pi_iff_not_linearIndependent {x y : V} :
    o.oangle x y = 0 ∨ o.oangle x y = π ↔ ¬LinearIndependent ℝ ![x, y] := by
  rw [oangle_eq_zero_iff_sameRay, oangle_eq_pi_iff_sameRay_neg,
    sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent]

/-- The oriented angle between two vectors is zero or `π` if and only if the first vector is zero
or the second is a multiple of the first. -/
/-
**Orientation.oangle_eq_zero_or_eq_pi_iff_right_eq_smul** 是 Mathlib 中的一个定理，位于命名空
间 `Orientation`。
形式化陈述：oangle_eq_zero_or_eq_pi_iff_right_eq_smul {x y : V} : o.oangle x y = 0 ∨ o
.oangle x y = π ↔ x = 0 ∨ exists r : Real, y = r • x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_eq_zero_iff_sameRay`：oangle_eq_zero_iff_sameRay {x y 
: V} : o.oangle x y = 0 ↔ SameRay Real x y
· 使用定理 `Orientation.oangle_eq_pi_iff_sameRay_neg`：oangle_eq_pi_iff_sameRay_neg {
x y : V} : o.oangle x y = π ↔ x != 0 ∧ y != 0 ∧ SameRay Real x (-y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `SameRay.exists_nonneg_left`：exists_nonneg_left (h : SameRay R x y) (hx :
 x != 0) : exists r : R, 0 <= r ∧ r • x = y
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用引理 `smul_ne_zero`：smul_ne_zero (hr : r != 0) (hm : m != 0) : r • m != 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The oriented angle between two vectors is zero or `π` if and only if the first v
ector is zero
or the second is a multiple of the first.
-/
theorem oangle_eq_zero_or_eq_pi_iff_right_eq_smul {x y : V} :
    o.oangle x y = 0 ∨ o.oangle x y = π ↔ x = 0 ∨ ∃ r : ℝ, y = r • x := by
  rw [oangle_eq_zero_iff_sameRay, oangle_eq_pi_iff_sameRay_neg]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | ⟨-, -, h⟩)
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, rfl⟩ := h.exists_nonneg_left hx
      exact Or.inr ⟨r, rfl⟩
    · by_cases hx : x = 0; · simp [hx]
      obtain ⟨r, -, hy⟩ := h.exists_nonneg_left hx
      refine Or.inr ⟨-r, ?_⟩
      simp [hy]
  · rcases h with (rfl | ⟨r, rfl⟩); · simp
    by_cases hx : x = 0; · simp [hx]
    rcases lt_trichotomy r 0 with (hr | hr | hr)
    · rw [← neg_smul]
      exact Or.inr ⟨hx, smul_ne_zero hr.ne hx,
        SameRay.sameRay_pos_smul_right x (Left.neg_pos_iff.2 hr)⟩
    · simp [hr]
    · exact Or.inl (SameRay.sameRay_pos_smul_right x hr)

/-- The oriented angle between two vectors is not zero or `π` if and only if those two vectors
are linearly independent. -/
/-
**Orientation.oangle_ne_zero_and_ne_pi_iff_linearIndependent** 是 Mathlib 中的一个定理，
位于命名空间 `Orientation`。
形式化陈述：oangle_ne_zero_and_ne_pi_iff_linearIndependent {x y : V} : o.oangle x y !=
 0 ∧ o.oangle x y != π ↔ LinearIndependent Real ![x, y]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Orientation.oangle_eq_zero_or_eq_pi_iff_not_linearIndependent`：oangle_eq
_zero_or_eq_pi_iff_not_linearIndependent {x y : V} : o.oangle x y = 0 ∨ o.oangle
 x y = π ↔ ¬LinearIndependent Real ![x, y]

--- 原说明 ---
The oriented angle between two vectors is not zero or `π` if and only if those t
wo vectors
are linearly independent.
-/
theorem oangle_ne_zero_and_ne_pi_iff_linearIndependent {x y : V} :
    o.oangle x y ≠ 0 ∧ o.oangle x y ≠ π ↔ LinearIndependent ℝ ![x, y] := by
  contrapose! +distrib; exact oangle_eq_zero_or_eq_pi_iff_not_linearIndependent o

/-- Two vectors are equal if and only if they have equal norms and zero angle between them. -/
/-
**Orientation.eq_iff_norm_eq_and_oangle_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orien
tation`。
形式化陈述：eq_iff_norm_eq_and_oangle_eq_zero (x y : V) : x = y ↔ ‖x‖ = ‖y‖ ∧ o.oangle
 x y = 0
参数：x y : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_eq_zero_iff_sameRay`：oangle_eq_zero_iff_sameRay {x y 
: V} : o.oangle x y = 0 ↔ SameRay Real x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `SameRay.refl`：refl (x : M) : SameRay R x x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SameRay.exists_nonneg_right`：exists_nonneg_right (h : SameRay R x y) (hy
 : y != 0) : exists r : R, 0 <= r ∧ x = r • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
Two vectors are equal if and only if they have equal norms and zero angle betwee
n them.
-/
theorem eq_iff_norm_eq_and_oangle_eq_zero (x y : V) : x = y ↔ ‖x‖ = ‖y‖ ∧ o.oangle x y = 0 := by
  rw [oangle_eq_zero_iff_sameRay]
  constructor
  · rintro rfl
    simp; rfl
  · rcases eq_or_ne y 0 with (rfl | hy)
    · simp
    rintro ⟨h₁, h₂⟩
    obtain ⟨r, hr, rfl⟩ := h₂.exists_nonneg_right hy
    have : ‖y‖ ≠ 0 := by simpa using hy
    obtain rfl : r = 1 := by
      apply mul_right_cancel₀ this
      simpa [norm_smul, abs_of_nonneg hr] using h₁
    simp

/-- Two vectors with equal norms are equal if and only if they have zero angle between them. -/
/-
**Orientation.eq_iff_oangle_eq_zero_of_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Orient
ation`。
形式化陈述：eq_iff_oangle_eq_zero_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : x = y ↔ o.oan
gle x y = 0
参数：h : ‖x‖ = ‖y‖。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Orientation.eq_iff_norm_eq_and_oangle_eq_zero`：eq_iff_norm_eq_and_oangle
_eq_zero (x y : V) : x = y ↔ ‖x‖ = ‖y‖ ∧ o.oangle x y = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Two vectors with equal norms are equal if and only if they have zero angle betwe
en them.
-/
theorem eq_iff_oangle_eq_zero_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : x = y ↔ o.oangle x y = 0 :=
  ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).2, fun ha =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨h, ha⟩⟩

/-- Two vectors with zero angle between them are equal if and only if they have equal norms. -/
/-
**Orientation.eq_iff_norm_eq_of_oangle_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orient
ation`。
形式化陈述：eq_iff_norm_eq_of_oangle_eq_zero {x y : V} (h : o.oangle x y = 0) : x = y 
↔ ‖x‖ = ‖y‖
参数：h : o.oangle x y = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Orientation.eq_iff_norm_eq_and_oangle_eq_zero`：eq_iff_norm_eq_and_oangle
_eq_zero (x y : V) : x = y ↔ ‖x‖ = ‖y‖ ∧ o.oangle x y = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Two vectors with zero angle between them are equal if and only if they have equa
l norms.
-/
theorem eq_iff_norm_eq_of_oangle_eq_zero {x y : V} (h : o.oangle x y = 0) : x = y ↔ ‖x‖ = ‖y‖ :=
  ⟨fun he => ((o.eq_iff_norm_eq_and_oangle_eq_zero x y).1 he).1, fun hn =>
    (o.eq_iff_norm_eq_and_oangle_eq_zero x y).2 ⟨hn, h⟩⟩

/-- Given three nonzero vectors, the angle between the first and the second plus the angle
between the second and the third equals the angle between the first and the third. -/
@[simp]
/-
**Orientation.oangle_add** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) : o.oangl
e x y + o.oangle y z = o.oangle x z
参数：hx : x != 0；hy : y != 0；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.arg_mul_coe_angle`：arg_mul_coe_angle {x y : Complex} (hx : x != 
0) (hy : y != 0) : (arg (x * y) : Real.Angle) = arg x + arg y
· 使用定理 `Orientation.kahler_ne_zero`：kahler_ne_zero {x y : E} (hx : x != 0) (hy :
 y != 0) : o.kahler x y != 0
· 使用定理 `Orientation.kahler_mul`：kahler_mul (a x y : E) : o.kahler x a * o.kahler
 a y = ‖a‖ ^ 2 * o.kahler x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_real_mul`：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r)
 : arg (r * x) = arg x
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0

--- 原说明 ---
Given three nonzero vectors, the angle between the first and the second plus the
 angle
between the second and the third equals the angle between the first and the thir
d.
-/
theorem oangle_add {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x y + o.oangle y z = o.oangle x z := by
  simp_rw [oangle]
  rw [← Complex.arg_mul_coe_angle, o.kahler_mul y x z]
  · congr 1
    exact mod_cast Complex.arg_real_mul _ (by positivity : 0 < ‖y‖ ^ 2)
  · exact o.kahler_ne_zero hx hy
  · exact o.kahler_ne_zero hy hz

/-- Given three nonzero vectors, the angle between the second and the third plus the angle
between the first and the second equals the angle between the first and the third. -/
@[simp]
/-
**Orientation.oangle_add_swap** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_swap {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) : o.
oangle y z + o.oangle x y = o.oangle x z
参数：hx : x != 0；hy : y != 0；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.oangle_add`：oangle_add {x y z : V} (hx : x != 0) (hy : y != 
0) (hz : z != 0) : o.oangle x y + o.oangle y z = o.oangle x z

--- 原说明 ---
Given three nonzero vectors, the angle between the second and the third plus the
 angle
between the first and the second equals the angle between the first and the thir
d.
-/
theorem oangle_add_swap {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle y z + o.oangle x y = o.oangle x z := by rw [add_comm, o.oangle_add hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the first and the second equals the angle between the second and the third. -/
@[simp]
/-
**Orientation.oangle_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sub_left {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) : o.
oangle x z - o.oangle x y = o.oangle y z
参数：hx : x != 0；hy : y != 0；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Orientation.oangle_add_swap`：oangle_add_swap {x y z : V} (hx : x != 0) (
hy : y != 0) (hz : z != 0) : o.oangle y z + o.oangle x y = o.oangle x z

--- 原说明 ---
Given three nonzero vectors, the angle between the first and the third minus the
 angle
between the first and the second equals the angle between the second and the thi
rd.
-/
theorem oangle_sub_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x z - o.oangle x y = o.oangle y z := by
  rw [sub_eq_iff_eq_add, o.oangle_add_swap hx hy hz]

/-- Given three nonzero vectors, the angle between the first and the third minus the angle
between the second and the third equals the angle between the first and the second. -/
@[simp]
/-
**Orientation.oangle_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sub_right {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) : o
.oangle x z - o.oangle y z = o.oangle x y
参数：hx : x != 0；hy : y != 0；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Orientation.oangle_add`：oangle_add {x y z : V} (hx : x != 0) (hy : y != 
0) (hz : z != 0) : o.oangle x y + o.oangle y z = o.oangle x z

--- 原说明 ---
Given three nonzero vectors, the angle between the first and the third minus the
 angle
between the second and the third equals the angle between the first and the seco
nd.
-/
theorem oangle_sub_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x z - o.oangle y z = o.oangle x y := by rw [sub_eq_iff_eq_add, o.oangle_add hx hy hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order results in 0. -/
/-
**Orientation.oangle_add_cyc3** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_cyc3 {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z != 0) : o.
oangle x y + o.oangle y z + o.oangle z x = 0
参数：hx : x != 0；hy : y != 0；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_add`：oangle_add {x y z : V} (hx : x != 0) (hy : y != 
0) (hz : z != 0) : o.oangle x y + o.oangle y z = o.oangle x z
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Orientation.oangle_add_oangle_rev`：oangle_add_oangle_rev (x y : V) : o.o
angle x y + o.oangle y x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given three nonzero vectors, adding the angles between them in cyclic order resu
lts in 0.
-/
theorem oangle_add_cyc3 {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x y + o.oangle y z + o.oangle z x = 0 := by simp [hx, hy, hz]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the first
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
/-
**Orientation.oangle_add_cyc3_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_cyc3_neg_left {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z !
= 0) : o.oangle (-x) y + o.oangle (-y) z + o.oangle (-z) x = π
参数：hx : x != 0；hy : y != 0；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_neg_left`：oangle_neg_left {x y : V} (hx : x != 0) (hy
 : y != 0) : o.oangle (-x) y = o.oangle x y + π
· 使用定理 `_private.Mathlib.Geometry.Euclidean.Angle.Oriented.Basic.0.Orientation.o
angle_add_cyc3_neg_left._abel_1_1`：∀ {V : Type u_1} [inst : NormedAddCommGroup V
] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)]   (o
 : Orientation …
· 使用定理 `Orientation.oangle_add_cyc3`：oangle_add_cyc3 {x y z : V} (hx : x != 0) (
hy : y != 0) (hz : z != 0) : o.oangle x y + o.oangle y z + o.oangle z x = 0
· 使用定理 `Real.Angle.coe_pi_add_coe_pi`：coe_pi_add_coe_pi : (π : Real.Angle) + π =
 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
Given three nonzero vectors, adding the angles between them in cyclic order, wit
h the first
vector in each angle negated, results in π. If the vectors add to 0, this is a v
ersion of the
sum of the angles of a triangle.
-/
theorem oangle_add_cyc3_neg_left {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle (-x) y + o.oangle (-y) z + o.oangle (-z) x = π := by
  rw [o.oangle_neg_left hx hy, o.oangle_neg_left hy hz, o.oangle_neg_left hz hx,
    show o.oangle x y + π + (o.oangle y z + π) + (o.oangle z x + π) =
      o.oangle x y + o.oangle y z + o.oangle z x + (π + π + π : Real.Angle) by abel,
    o.oangle_add_cyc3 hx hy hz, Real.Angle.coe_pi_add_coe_pi, zero_add, zero_add]

/-- Given three nonzero vectors, adding the angles between them in cyclic order, with the second
vector in each angle negated, results in π. If the vectors add to 0, this is a version of the
sum of the angles of a triangle. -/
@[simp]
/-
**Orientation.oangle_add_cyc3_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_cyc3_neg_right {x y z : V} (hx : x != 0) (hy : y != 0) (hz : z 
!= 0) : o.oangle x (-y) + o.oangle y (-z) + o.oangle z (-x) = π
参数：hx : x != 0；hy : y != 0；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Orientation.oangle_add_cyc3_neg_left`：oangle_add_cyc3_neg_left {x y z : 
V} (hx : x != 0) (hy : y != 0) (hz : z != 0) : o.oangle (-x) y + o.oangle (-y) z
 + o.oangle (-z) x = π
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given three nonzero vectors, adding the angles between them in cyclic order, wit
h the second
vector in each angle negated, results in π. If the vectors add to 0, this is a v
ersion of the
sum of the angles of a triangle.
-/
theorem oangle_add_cyc3_neg_right {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    o.oangle x (-y) + o.oangle y (-z) + o.oangle z (-x) = π := by
  simp_rw [← oangle_neg_left_eq_neg_right, o.oangle_add_cyc3_neg_left hx hy hz]

/-- Pons asinorum, oriented vector angle form. -/
/-
**Orientation.oangle_sub_eq_oangle_sub_rev_of_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 
`Orientation`。
形式化陈述：oangle_sub_eq_oangle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : o.oang
le x (x - y) = o.oangle (y - x) y
参数：h : ‖x‖ = ‖y‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.kahler_apply_self`：kahler_apply_self (x : E) : o.kahler x x 
= ‖x‖ ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pons asinorum, oriented vector angle form.
-/
theorem oangle_sub_eq_oangle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    o.oangle x (x - y) = o.oangle (y - x) y := by simp [oangle, h]

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
vector angle form. -/
/-
**Orientation.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq** 是 Mathlib 中的一个定
理，位于命名空间 `Orientation`。
形式化陈述：oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x != y) (
h : ‖x‖ = ‖y‖) : o.oangle y x = π - (2 : Int) • o.oangle (y - x) y
参数：hn : x != y；h : ‖x‖ = ‖y‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sub_eq_oangle_sub_rev_of_norm_eq`：oangle_sub_eq_oangl
e_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : o.oangle x (x - y) = o.oangle (
y - x) y
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Orientation.oangle_neg_neg`：oangle_neg_neg (x y : V) : o.oangle (-x) (-y
) = o.oangle x y
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_add_cyc3_neg_right`：oangle_add_cyc3_neg_right {x y z 
: V} (hx : x != 0) (hy : y != 0) (hz : z != 0) : o.oangle x (-y) + o.oangle y (-
z) + o.oangle z (-x) = π
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
The angle at the apex of an isosceles triangle is `π` minus twice a base angle, 
oriented
vector angle form.
-/
theorem oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x ≠ y) (h : ‖x‖ = ‖y‖) :
    o.oangle y x = π - (2 : ℤ) • o.oangle (y - x) y := by
  rw [two_zsmul]
  nth_rw 1 [← o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h]
  rw [eq_sub_iff_add_eq, ← oangle_neg_neg, ← add_assoc]
  have hy : y ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at h
    exact hn h
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (h.symm ▸ norm_ne_zero_iff.2 hy)
  convert! o.oangle_add_cyc3_neg_right (neg_ne_zero.2 hy) hx (sub_ne_zero_of_ne hn.symm) using 1
  simp

/-- The angle between two vectors, with respect to an orientation given by `Orientation.map`
with a linear isometric equivalence, equals the angle between those two vectors, transformed by
the inverse of that equivalence, with respect to the original orientation. -/
@[simp]
/-
**Orientation.oangle_map** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_map (x y : V') (f : V ≃ₗᵢ[Real] V') : (Orientation.map (Fin 2) f.to
LinearEquiv o).oangle x y = o.oangle (f.symm x) (f.symm y)
参数：x y : V'；f : V ≃ₗᵢ[Real] V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.kahler_map`：kahler_map {F : Type*} [NormedAddCommGroup F] [I
nnerProductSpace Real F] [hF : Fact (finrank Real F = 2)] (φ : E ≃ₗᵢ[Real] F) (x
 y : F) : (O…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The angle between two vectors, with respect to an orientation given by `Orientat
ion.map`
with a linear isometric equivalence, equals the angle between those two vectors,
 transformed by
the inverse of that equivalence, with respect to the original orientation.
-/
theorem oangle_map (x y : V') (f : V ≃ₗᵢ[ℝ] V') :
    (Orientation.map (Fin 2) f.toLinearEquiv o).oangle x y = o.oangle (f.symm x) (f.symm y) := by
  simp [oangle, o.kahler_map]

@[simp]
/-
**Orientation._root_.Complex.oangle** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Complex.oangle (w z : ℂ) :
    Complex.orientation.oangle w z = Complex.arg (conj w * z) := by
  simp [oangle, mul_comm z]

/-- The oriented angle on an oriented real inner product space of dimension 2 can be evaluated in
terms of a complex-number representation of the space. -/
/-
**Orientation.oangle_map_complex** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_map_complex (f : V ≃ₗᵢ[Real] Complex) (hf : Orientation.map (Fin 2)
 f.toLinearEquiv o = Complex.orientation) (x y : V) : o.oangle x y = Complex.arg
 (conj (f x) * f y)
参数：f : V ≃ₗᵢ[Real] Complex；hf : Orientation.map (Fin 2) f.toLinearEquiv o = Comp
lex.orientation；x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.finrank_real_complex_fact`：finrank_real_complex_fact : Fact (fin
rank Real Complex = 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.oangle`：∀ (w z : ℂ), Complex.orientation.oangle w z = ↑((starRin
gEnd ℂ) w * z).arg
· 使用定理 `Orientation.oangle_map`：oangle_map (x y : V') (f : V ≃ₗᵢ[Real] V') : (Or
ientation.map (Fin 2) f.toLinearEquiv o).oangle x y = o.oangle (f.symm x) (f.sym
m y)
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x

--- 原说明 ---
The oriented angle on an oriented real inner product space of dimension 2 can be
 evaluated in
terms of a complex-number representation of the space.
-/
theorem oangle_map_complex (f : V ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : V) :
    o.oangle x y = Complex.arg (conj (f x) * f y) := by
  rw [← Complex.oangle, ← hf, o.oangle_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

/-- Negating the orientation negates the value of `oangle`. -/
/-
**Orientation.oangle_neg_orientation_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientati
on`。
形式化陈述：oangle_neg_orientation_eq_neg (x y : V) : (-o).oangle x y = -o.oangle x y
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.kahler_neg_orientation`：kahler_neg_orientation (x y : E) : (
-o).kahler x y = conj (o.kahler x y)
· 使用定理 `Complex.arg_conj_coe_angle`：arg_conj_coe_angle (x : Complex) : (arg (con
j x) : Real.Angle) = -arg x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Negating the orientation negates the value of `oangle`.
-/
theorem oangle_neg_orientation_eq_neg (x y : V) : (-o).oangle x y = -o.oangle x y := by
  simp [oangle]

/-- The inner product of two vectors is the product of the norms and the cosine of the oriented
angle between the vectors. -/
/-
**Orientation.inner_eq_norm_mul_norm_mul_cos_oangle** 是 Mathlib 中的一个定理，位于命名空间 `O
rientation`。
形式化陈述：inner_eq_norm_mul_norm_mul_cos_oangle (x y : V) : ⟪x, y⟫ = ‖x‖ * ‖y‖ * Rea
l.Angle.cos (o.oangle x y)
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Real.Angle.cos_zero`：cos_zero : cos (0 : Angle) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `Orientation.oangle.eq_1`：∀ {V : Type u_1} [inst : NormedAddCommGroup V] 
[inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)]   (o :
 Orientation …
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `Complex.cos_arg`：cos_arg {x : Complex} (hx : x != 0) : Real.cos (arg x) 
= x.re / ‖x‖
· 使用定理 `Orientation.kahler_ne_zero`：kahler_ne_zero {x y : E} (hx : x != 0) (hy :
 y != 0) : o.kahler x y != 0
· 使用定理 `Orientation.norm_kahler`：norm_kahler (x y : E) : ‖o.kahler x y‖ = ‖x‖ * 
‖y‖
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
The inner product of two vectors is the product of the norms and the cosine of t
he oriented
angle between the vectors.
-/
theorem inner_eq_norm_mul_norm_mul_cos_oangle (x y : V) :
    ⟪x, y⟫ = ‖x‖ * ‖y‖ * Real.Angle.cos (o.oangle x y) := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [oangle, Real.Angle.cos_coe, Complex.cos_arg, o.norm_kahler]
  · simp only [kahler_apply_apply, real_smul, add_re, ofReal_re, mul_re, I_re, ofReal_im]
    simp [field]
  · exact o.kahler_ne_zero hx hy

/-- The cosine of the oriented angle between two nonzero vectors is the inner product divided by
the product of the norms. -/
/-
**Orientation.cos_oangle_eq_inner_div_norm_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 `O
rientation`。
形式化陈述：cos_oangle_eq_inner_div_norm_mul_norm {x y : V} (hx : x != 0) (hy : y != 0
) : Real.Angle.cos (o.oangle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖)
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.inner_eq_norm_mul_norm_mul_cos_oangle`：inner_eq_norm_mul_nor
m_mul_cos_oangle (x y : V) : ⟪x, y⟫ = ‖x‖ * ‖y‖ * Real.Angle.cos (o.oangle x y)
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₂`：div_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval / l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval / ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The cosine of the oriented angle between two nonzero vectors is the inner produc
t divided by
the product of the norms.
-/
theorem cos_oangle_eq_inner_div_norm_mul_norm {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.Angle.cos (o.oangle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) := by
  rw [o.inner_eq_norm_mul_norm_mul_cos_oangle]
  field

/-- The cosine of the oriented angle between two nonzero vectors equals that of the unoriented
angle. -/
/-
**Orientation.cos_oangle_eq_cos_angle** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：cos_oangle_eq_cos_angle {x y : V} (hx : x != 0) (hy : y != 0) : Real.Angle
.cos (o.oangle x y) = Real.cos (InnerProductGeometry.angle x y)
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.cos_oangle_eq_inner_div_norm_mul_norm`：cos_oangle_eq_inner_d
iv_norm_mul_norm {x y : V} (hx : x != 0) (hy : y != 0) : Real.Angle.cos (o.oangl
e x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖)
· 使用定理 `InnerProductGeometry.cos_angle`：cos_angle (x y : V) : Real.cos (angle x 
y) = ⟪x, y⟫ / (‖x‖ * ‖y‖)

--- 原说明 ---
The cosine of the oriented angle between two nonzero vectors equals that of the 
unoriented
angle.
-/
theorem cos_oangle_eq_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.Angle.cos (o.oangle x y) = Real.cos (InnerProductGeometry.angle x y) := by
  rw [o.cos_oangle_eq_inner_div_norm_mul_norm hx hy, InnerProductGeometry.cos_angle]

/-- The oriented angle between two nonzero vectors is plus or minus the unoriented angle. -/
/-
**Orientation.oangle_eq_angle_or_eq_neg_angle** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：oangle_eq_angle_or_eq_neg_angle {x y : V} (hx : x != 0) (hy : y != 0) : o.
oangle x y = InnerProductGeometry.angle x y ∨ o.oangle x y = -InnerProductGeomet
ry.angle x y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg`：cos_eq_real_cos_iff_eq_or_e
q_neg {θ : Angle} {ψ : Real} : cos θ = Real.cos ψ ↔ θ = ψ ∨ θ = -ψ
· 使用定理 `Orientation.cos_oangle_eq_cos_angle`：cos_oangle_eq_cos_angle {x y : V} (
hx : x != 0) (hy : y != 0) : Real.Angle.cos (o.oangle x y) = Real.cos (InnerProd
uctGeometry.angle x y)

--- 原说明 ---
The oriented angle between two nonzero vectors is plus or minus the unoriented a
ngle.
-/
theorem oangle_eq_angle_or_eq_neg_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    o.oangle x y = InnerProductGeometry.angle x y ∨
      o.oangle x y = -InnerProductGeometry.angle x y :=
  Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg.1 <| o.cos_oangle_eq_cos_angle hx hy

/-- The unoriented angle between two nonzero vectors is the absolute value of the oriented angle,
converted to a real. -/
/-
**Orientation.angle_eq_abs_oangle_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：angle_eq_abs_oangle_toReal {x y : V} (hx : x != 0) (hy : y != 0) : InnerPr
oductGeometry.angle x y = |(o.oangle x y).toReal|
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductGeometry.angle_nonneg`：angle_nonneg (x y : V) : 0 <= angle x
 y
· 使用定理 `InnerProductGeometry.angle_le_pi`：angle_le_pi (x y : V) : angle x y <= π
· 使用定理 `Orientation.oangle_eq_angle_or_eq_neg_angle`：oangle_eq_angle_or_eq_neg_a
ngle {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle x y = InnerProductGeometry
.angle x y ∨ o.oangle x y = -Inne…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Real.Angle.abs_toReal_coe_eq_self_iff`：abs_toReal_coe_eq_self_iff {θ : R
eal} : |(θ : Angle).toReal| = θ ↔ 0 <= θ ∧ θ <= π
· 使用定理 `Real.Angle.abs_toReal_neg_coe_eq_self_iff`：abs_toReal_neg_coe_eq_self_if
f {θ : Real} : |(-θ : Angle).toReal| = θ ↔ 0 <= θ ∧ θ <= π

--- 原说明 ---
The unoriented angle between two nonzero vectors is the absolute value of the or
iented angle,
converted to a real.
-/
theorem angle_eq_abs_oangle_toReal {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    InnerProductGeometry.angle x y = |(o.oangle x y).toReal| := by
  have h0 := InnerProductGeometry.angle_nonneg x y
  have hpi := InnerProductGeometry.angle_le_pi x y
  rcases o.oangle_eq_angle_or_eq_neg_angle hx hy with (h | h)
  · rw [h, eq_comm, Real.Angle.abs_toReal_coe_eq_self_iff]
    exact ⟨h0, hpi⟩
  · rw [h, eq_comm, Real.Angle.abs_toReal_neg_coe_eq_self_iff]
    exact ⟨h0, hpi⟩

/-- If the sign of the oriented angle between two vectors is zero, either one of the vectors is
zero or the unoriented angle is 0 or π. -/
/-
**Orientation.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {x y : V} (h : (o.oa
ngle x y).sign = 0) : x = 0 ∨ y = 0 ∨ InnerProductGeometry.angle x y = 0 ∨ Inner
ProductGeometry.angle x y = π
参数：h : (o.oangle x y).sign = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `InnerProductGeometry.angle_zero_right`：angle_zero_right (x : V) : angle 
x 0 = π / 2
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Orientation.angle_eq_abs_oangle_toReal`：angle_eq_abs_oangle_toReal {x y 
: V} (hx : x != 0) (hy : y != 0) : InnerProductGeometry.angle x y = |(o.oangle x
 y).toReal|
· 使用定理 `Real.Angle.sign_eq_zero_iff`：sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔
 θ = 0 ∨ θ = π
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.Angle.toReal_pi`：toReal_pi : (π : Angle).toReal = π
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π

--- 原说明 ---
If the sign of the oriented angle between two vectors is zero, either one of the
 vectors is
zero or the unoriented angle is 0 or π.
-/
theorem eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {x y : V}
    (h : (o.oangle x y).sign = 0) :
    x = 0 ∨ y = 0 ∨ InnerProductGeometry.angle x y = 0 ∨ InnerProductGeometry.angle x y = π := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.angle_eq_abs_oangle_toReal hx hy]
  rw [Real.Angle.sign_eq_zero_iff] at h
  rcases h with (h | h) <;> simp [h, Real.pi_pos.le]

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
equal, then the oriented angles are equal (even in degenerate cases). -/
/-
**Orientation.oangle_eq_of_angle_eq_of_sign_eq** 是 Mathlib 中的一个定理，位于命名空间 `Orient
ation`。
形式化陈述：oangle_eq_of_angle_eq_of_sign_eq {w x y z : V} (h : InnerProductGeometry.a
ngle w x = InnerProductGeometry.angle y z) (hs : (o.oangle w x).sign = (o.oangle
 y z).sign) : o.oangle w x = o.oangle y z
参数：h : InnerProductGeometry.angle w x = InnerProductGeometry.angle y z；hs : (o.o
angle w x).sign = (o.oangle y z).sign。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Real.Angle.sign_zero`：sign_zero : (0 : Angle).sign = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用定理 `InnerProductGeometry.angle_zero_right`：angle_zero_right (x : V) : angle 
x 0 = π / 2
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Orientation.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero`：eq_ze
ro_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero {x y : V} (h : (o.oangle x y).s
ign = 0) : x = 0 ∨ y = 0 ∨ InnerProductGeometry.angle x…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If two unoriented angles are equal, and the signs of the corresponding oriented 
angles are
equal, then the oriented angles are equal (even in degenerate cases).
-/
theorem oangle_eq_of_angle_eq_of_sign_eq {w x y z : V}
    (h : InnerProductGeometry.angle w x = InnerProductGeometry.angle y z)
    (hs : (o.oangle w x).sign = (o.oangle y z).sign) : o.oangle w x = o.oangle y z := by
  by_cases! h0 : (w = 0 ∨ x = 0) ∨ y = 0 ∨ z = 0
  · have hs' : (o.oangle w x).sign = 0 ∧ (o.oangle y z).sign = 0 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using hs.symm
      · simpa using hs.symm
      · simpa using hs
      · simpa using hs
    rcases hs' with ⟨hswx, hsyz⟩
    have h' : InnerProductGeometry.angle w x = π / 2 ∧ InnerProductGeometry.angle y z = π / 2 := by
      rcases h0 with ((rfl | rfl) | rfl | rfl)
      · simpa using h.symm
      · simpa using h.symm
      · simpa using h
      · simpa using h
    rcases h' with ⟨hwx, hyz⟩
    have hpi : π / 2 ≠ π := by
      intro hpi
      rw [div_eq_iff, eq_comm, ← sub_eq_zero, mul_two, add_sub_cancel_right] at hpi
      · exact Real.pi_pos.ne.symm hpi
      · exact two_ne_zero
    have h0wx : w = 0 ∨ x = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hswx
      simpa [hwx, Real.pi_pos.ne.symm, hpi] using h0'
    have h0yz : y = 0 ∨ z = 0 := by
      have h0' := o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero hsyz
      simpa [hyz, Real.pi_pos.ne.symm, hpi] using h0'
    rcases h0wx with (h0wx | h0wx) <;> rcases h0yz with (h0yz | h0yz) <;> simp [h0wx, h0yz]
  · rw [Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq hs]
    rwa [o.angle_eq_abs_oangle_toReal h0.1.1 h0.1.2,
      o.angle_eq_abs_oangle_toReal h0.2.1 h0.2.2] at h

/-- If the signs of two oriented angles between nonzero vectors are equal, the oriented angles are
equal if and only if the unoriented angles are equal. -/
/-
**Orientation.angle_eq_iff_oangle_eq_of_sign_eq** 是 Mathlib 中的一个定理，位于命名空间 `Orien
tation`。
形式化陈述：angle_eq_iff_oangle_eq_of_sign_eq {w x y z : V} (hw : w != 0) (hx : x != 0
) (hy : y != 0) (hz : z != 0) (hs : (o.oangle w x).sign = (o.oangle y z).sign) :
 InnerProductGeometry.angle w x = InnerProductGeometry.angle y z ↔ o.oangle w x 
= o.oangle y z
参数：hw : w != 0；hx : x != 0；hy : y != 0；hz : z != 0；hs : (o.oangle w x).sign = (o
.oangle y z).sign。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.oangle_eq_of_angle_eq_of_sign_eq`：oangle_eq_of_angle_eq_of_s
ign_eq {w x y z : V} (h : InnerProductGeometry.angle w x = InnerProductGeometry.
angle y z) (hs : (o.oangle w x).si…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.angle_eq_abs_oangle_toReal`：angle_eq_abs_oangle_toReal {x y 
: V} (hx : x != 0) (hy : y != 0) : InnerProductGeometry.angle x y = |(o.oangle x
 y).toReal|

--- 原说明 ---
If the signs of two oriented angles between nonzero vectors are equal, the orien
ted angles are
equal if and only if the unoriented angles are equal.
-/
theorem angle_eq_iff_oangle_eq_of_sign_eq {w x y z : V} (hw : w ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hs : (o.oangle w x).sign = (o.oangle y z).sign) :
    InnerProductGeometry.angle w x = InnerProductGeometry.angle y z ↔
    o.oangle w x = o.oangle y z := by
  refine ⟨fun h => o.oangle_eq_of_angle_eq_of_sign_eq h hs, fun h => ?_⟩
  rw [o.angle_eq_abs_oangle_toReal hw hx, o.angle_eq_abs_oangle_toReal hy hz, h]

/-- If two unoriented angles are equal, and the signs of the corresponding oriented angles are
negations of each other, then the oriented angles are negations of each other (even in degenerate
cases). -/
/-
**Orientation.oangle_eq_neg_of_angle_eq_of_sign_eq_neg** 是 Mathlib 中的一个引理，位于命名空间
 `Orientation`。
形式化陈述：oangle_eq_neg_of_angle_eq_of_sign_eq_neg {w x y z : V} (h : InnerProductGe
ometry.angle w x = InnerProductGeometry.angle y z) (hs : (o.oangle w x).sign = -
(o.oangle y z).sign) : o.oangle w x = -o.oangle y z
参数：h : InnerProductGeometry.angle w x = InnerProductGeometry.angle y z；hs : (o.o
angle w x).sign = -(o.oangle y z).sign。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_eq_of_angle_eq_of_sign_eq`：oangle_eq_of_angle_eq_of_s
ign_eq {w x y z : V} (h : InnerProductGeometry.angle w x = InnerProductGeometry.
angle y z) (hs : (o.oangle w x).si…
· 使用定理 `InnerProductGeometry.angle_comm`：angle_comm (x y : V) : angle x y = angl
e y x
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign

--- 原说明 ---
If two unoriented angles are equal, and the signs of the corresponding oriented 
angles are
negations of each other, then the oriented angles are negations of each other (e
ven in degenerate
cases).
-/
lemma oangle_eq_neg_of_angle_eq_of_sign_eq_neg {w x y z : V}
    (h : InnerProductGeometry.angle w x = InnerProductGeometry.angle y z)
    (hs : (o.oangle w x).sign = -(o.oangle y z).sign) : o.oangle w x = -o.oangle y z := by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg, ← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm] at h
  exact o.oangle_eq_of_angle_eq_of_sign_eq h hs

/-- If the signs of two oriented angles between nonzero vectors are negations of each other, the
oriented angles are negations of each other if and only if the unoriented angles are equal. -/
/-
**Orientation.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg** 是 Mathlib 中的一个引理，位于命名空
间 `Orientation`。
形式化陈述：angle_eq_iff_oangle_eq_neg_of_sign_eq_neg {w x y z : V} (hw : w != 0) (hx 
: x != 0) (hy : y != 0) (hz : z != 0) (hs : (o.oangle w x).sign = -(o.oangle y z
).sign) : InnerProductGeometry.angle w x = InnerProductGeometry.angle y z ↔ o.oa
ngle w x = -o.oangle y z
参数：hw : w != 0；hx : x != 0；hy : y != 0；hz : z != 0；hs : (o.oangle w x).sign = -(
o.oangle y z).sign。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `InnerProductGeometry.angle_comm`：angle_comm (x y : V) : angle x y = angl
e y x
· 使用定理 `Orientation.angle_eq_iff_oangle_eq_of_sign_eq`：angle_eq_iff_oangle_eq_of
_sign_eq {w x y z : V} (hw : w != 0) (hx : x != 0) (hy : y != 0) (hz : z != 0) (
hs : (o.oangle w x).sign = (o.oangl…
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign

--- 原说明 ---
If the signs of two oriented angles between nonzero vectors are negations of eac
h other, the
oriented angles are negations of each other if and only if the unoriented angles
 are equal.
-/
lemma angle_eq_iff_oangle_eq_neg_of_sign_eq_neg {w x y z : V} (hw : w ≠ 0) (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) (hs : (o.oangle w x).sign = -(o.oangle y z).sign) :
    InnerProductGeometry.angle w x = InnerProductGeometry.angle y z ↔
      o.oangle w x = -o.oangle y z := by
  rw [← oangle_rev]
  rw [← Real.Angle.sign_neg, ← oangle_rev] at hs
  nth_rw 2 [InnerProductGeometry.angle_comm]
  exact o.angle_eq_iff_oangle_eq_of_sign_eq hw hx hz hy hs

/-- The oriented angle between two vectors equals the unoriented angle if the sign is positive. -/
/-
**Orientation.oangle_eq_angle_of_sign_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Orientat
ion`。
形式化陈述：oangle_eq_angle_of_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) : o
.oangle x y = InnerProductGeometry.angle x y
参数：h : (o.oangle x y).sign = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Real.Angle.sign_zero`：sign_zero : (0 : Angle).sign = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Orientation.oangle_eq_angle_or_eq_neg_angle`：oangle_eq_angle_or_eq_neg_a
ngle {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle x y = InnerProductGeometry
.angle x y ∨ o.oangle x y = -Inne…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `SignType.neg_iff`：neg_iff {a : SignType} : a < 0 ↔ a = -1
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
· 使用定理 `Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi`：sign_coe_nonneg_of_nonneg
_of_le_pi {θ : Real} (h0 : 0 <= θ) (hpi : θ <= π) : 0 <= (θ : Angle).sign
· 使用定理 `InnerProductGeometry.angle_nonneg`：angle_nonneg (x y : V) : 0 <= angle x
 y
· 使用定理 `InnerProductGeometry.angle_le_pi`：angle_le_pi (x y : V) : angle x y <= π

--- 原说明 ---
The oriented angle between two vectors equals the unoriented angle if the sign i
s positive.
-/
theorem oangle_eq_angle_of_sign_eq_one {x y : V} (h : (o.oangle x y).sign = 1) :
    o.oangle x y = InnerProductGeometry.angle x y := by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_right ?_
  intro hxy
  rw [hxy, Real.Angle.sign_neg, neg_eq_iff_eq_neg, ← SignType.neg_iff, ← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

/-- The oriented angle between two vectors equals minus the unoriented angle if the sign is
negative. -/
/-
**Orientation.oangle_eq_neg_angle_of_sign_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `
Orientation`。
形式化陈述：oangle_eq_neg_angle_of_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign 
= -1) : o.oangle x y = -InnerProductGeometry.angle x y
参数：h : (o.oangle x y).sign = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Real.Angle.sign_zero`：sign_zero : (0 : Angle).sign = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Orientation.oangle_eq_angle_or_eq_neg_angle`：oangle_eq_angle_or_eq_neg_a
ngle {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle x y = InnerProductGeometry
.angle x y ∨ o.oangle x y = -Inne…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `SignType.neg_iff`：neg_iff {a : SignType} : a < 0 ↔ a = -1
· 使用定理 `Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi`：sign_coe_nonneg_of_nonneg
_of_le_pi {θ : Real} (h0 : 0 <= θ) (hpi : θ <= π) : 0 <= (θ : Angle).sign
· 使用定理 `InnerProductGeometry.angle_nonneg`：angle_nonneg (x y : V) : 0 <= angle x
 y
· 使用定理 `InnerProductGeometry.angle_le_pi`：angle_le_pi (x y : V) : angle x y <= π

--- 原说明 ---
The oriented angle between two vectors equals minus the unoriented angle if the 
sign is
negative.
-/
theorem oangle_eq_neg_angle_of_sign_eq_neg_one {x y : V} (h : (o.oangle x y).sign = -1) :
    o.oangle x y = -InnerProductGeometry.angle x y := by
  by_cases hx : x = 0; · simp [hx] at h
  by_cases hy : y = 0; · simp [hy] at h
  refine (o.oangle_eq_angle_or_eq_neg_angle hx hy).resolve_left ?_
  intro hxy
  rw [hxy, ← SignType.neg_iff, ← not_le] at h
  exact h (Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _))

/-- The oriented angle between two nonzero vectors is zero if and only if the unoriented angle
is zero. -/
/-
**Orientation.oangle_eq_zero_iff_angle_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Orient
ation`。
形式化陈述：oangle_eq_zero_iff_angle_eq_zero {x y : V} (hx : x != 0) (hy : y != 0) : o
.oangle x y = 0 ↔ InnerProductGeometry.angle x y = 0
参数：hx : x != 0；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.angle_eq_abs_oangle_toReal`：angle_eq_abs_oangle_toReal {x y 
: V} (hx : x != 0) (hy : y != 0) : InnerProductGeometry.angle x y = |(o.oangle x
 y).toReal|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Orientation.oangle_eq_angle_or_eq_neg_angle`：oangle_eq_angle_or_eq_neg_a
ngle {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle x y = InnerProductGeometry
.angle x y ∨ o.oangle x y = -Inne…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p

--- 原说明 ---
The oriented angle between two nonzero vectors is zero if and only if the unorie
nted angle
is zero.
-/
theorem oangle_eq_zero_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    o.oangle x y = 0 ↔ InnerProductGeometry.angle x y = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [o.angle_eq_abs_oangle_toReal hx hy]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

/-- The oriented angle between two vectors is `π` if and only if the unoriented angle is `π`. -/
/-
**Orientation.oangle_eq_pi_iff_angle_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Orientatio
n`。
形式化陈述：oangle_eq_pi_iff_angle_eq_pi {x y : V} : o.oangle x y = π ↔ InnerProductGe
ometry.angle x y = π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Real.Angle.pi_ne_zero`：pi_ne_zero : (π : Angle) != 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `InnerProductGeometry.angle_zero_right`：angle_zero_right (x : V) : angle 
x 0 = π / 2
· 使用定理 `Orientation.angle_eq_abs_oangle_toReal`：angle_eq_abs_oangle_toReal {x y 
: V} (hx : x != 0) (hy : y != 0) : InnerProductGeometry.angle x y = |(o.oangle x
 y).toReal|
· 使用定理 `Real.Angle.toReal_pi`：toReal_pi : (π : Angle).toReal = π
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Orientation.oangle_eq_angle_or_eq_neg_angle`：oangle_eq_angle_or_eq_neg_a
ngle {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle x y = InnerProductGeometry
.angle x y ∨ o.oangle x y = -Inne…
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p

--- 原说明 ---
The oriented angle between two vectors is `π` if and only if the unoriented angl
e is `π`.
-/
theorem oangle_eq_pi_iff_angle_eq_pi {x y : V} :
    o.oangle x y = π ↔ InnerProductGeometry.angle x y = π := by
  by_cases hx : x = 0
  · simp [hx, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  by_cases hy : y = 0
  · simp [hy, Real.Angle.pi_ne_zero.symm, div_eq_mul_inv,
      Real.pi_ne_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [o.angle_eq_abs_oangle_toReal hx hy, h]
    simp [Real.pi_pos.le]
  · have ha := o.oangle_eq_angle_or_eq_neg_angle hx hy
    rw [h] at ha
    simpa using ha

/-- One of two vectors is zero or the oriented angle between them is plus or minus `π / 2` if
and only if the inner product of those vectors is zero. -/
/-
**Orientation.eq_zero_or_oangle_eq_iff_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Orientation`。
形式化陈述：eq_zero_or_oangle_eq_iff_inner_eq_zero {x y : V} : x = 0 ∨ y = 0 ∨ o.oangl
e x y = (π / 2 : Real) ∨ o.oangle x y = (-π / 2 : Real) ↔ ⟪x, y⟫ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Orientation.angle_eq_abs_oangle_toReal`：angle_eq_abs_oangle_toReal {x y 
: V} (hx : x != 0) (hy : y != 0) : InnerProductGeometry.angle x y = |(o.oangle x
 y).toReal|
· 使用定理 `Real.Angle.abs_toReal_eq_pi_div_two_iff`：abs_toReal_eq_pi_div_two_iff {θ
 : Angle} : |θ.toReal| = π / 2 ↔ θ = (π / 2 : Real) ∨ θ = (-π / 2 : Real)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Orientation.oangle_eq_angle_or_eq_neg_angle`：oangle_eq_angle_or_eq_neg_a
ngle {x y : V} (hx : x != 0) (hy : y != 0) : o.oangle x y = InnerProductGeometry
.angle x y ∨ o.oangle x y = -Inne…

--- 原说明 ---
One of two vectors is zero or the oriented angle between them is plus or minus `
π / 2` if
and only if the inner product of those vectors is zero.
-/
theorem eq_zero_or_oangle_eq_iff_inner_eq_zero {x y : V} :
    x = 0 ∨ y = 0 ∨ o.oangle x y = (π / 2 : ℝ) ∨ o.oangle x y = (-π / 2 : ℝ) ↔ ⟪x, y⟫ = 0 := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, or_iff_right hx, or_iff_right hy]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [o.angle_eq_abs_oangle_toReal hx hy, Real.Angle.abs_toReal_eq_pi_div_two_iff]
  · convert! o.oangle_eq_angle_or_eq_neg_angle hx hy using 2 <;> rw [h]
    simp only [neg_div, Real.Angle.coe_neg]

/-- If the oriented angle between two vectors is `π / 2`, the inner product of those vectors
is zero. -/
/-
**Orientation.inner_eq_zero_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `O
rientation`。
形式化陈述：inner_eq_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2
 : Real)) : ⟪x, y⟫ = 0
参数：h : o.oangle x y = (π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Orientation.eq_zero_or_oangle_eq_iff_inner_eq_zero`：eq_zero_or_oangle_eq
_iff_inner_eq_zero {x y : V} : x = 0 ∨ y = 0 ∨ o.oangle x y = (π / 2 : Real) ∨ o
.oangle x y = (-π / 2 : Real) ↔ ⟪x, y⟫ =…

--- 原说明 ---
If the oriented angle between two vectors is `π / 2`, the inner product of those
 vectors
is zero.
-/
theorem inner_eq_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) :
    ⟪x, y⟫ = 0 :=
  o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 <| Or.inr <| Or.inr <| Or.inl h

/-- If the oriented angle between two vectors is `π / 2`, the inner product of those vectors
(reversed) is zero. -/
/-
**Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空
间 `Orientation`。
形式化陈述：inner_rev_eq_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π
 / 2 : Real)) : ⟪y, x⟫ = 0
参数：h : o.oangle x y = (π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0

--- 原说明 ---
If the oriented angle between two vectors is `π / 2`, the inner product of those
 vectors
(reversed) is zero.
-/
theorem inner_rev_eq_zero_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : ℝ)) :
    ⟪y, x⟫ = 0 := by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_pi_div_two h]

/-- If the oriented angle between two vectors is `-π / 2`, the inner product of those vectors
is zero. -/
/-
**Orientation.inner_eq_zero_of_oangle_eq_neg_pi_div_two** 是 Mathlib 中的一个定理，位于命名空
间 `Orientation`。
形式化陈述：inner_eq_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-
π / 2 : Real)) : ⟪x, y⟫ = 0
参数：h : o.oangle x y = (-π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Orientation.eq_zero_or_oangle_eq_iff_inner_eq_zero`：eq_zero_or_oangle_eq
_iff_inner_eq_zero {x y : V} : x = 0 ∨ y = 0 ∨ o.oangle x y = (π / 2 : Real) ∨ o
.oangle x y = (-π / 2 : Real) ↔ ⟪x, y⟫ =…

--- 原说明 ---
If the oriented angle between two vectors is `-π / 2`, the inner product of thos
e vectors
is zero.
-/
theorem inner_eq_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) :
    ⟪x, y⟫ = 0 :=
  o.eq_zero_or_oangle_eq_iff_inner_eq_zero.1 <| Or.inr <| Or.inr <| Or.inr h

/-- If the oriented angle between two vectors is `-π / 2`, the inner product of those vectors
(reversed) is zero. -/
/-
**Orientation.inner_rev_eq_zero_of_oangle_eq_neg_pi_div_two** 是 Mathlib 中的一个定理，位
于命名空间 `Orientation`。
形式化陈述：inner_rev_eq_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y 
= (-π / 2 : Real)) : ⟪y, x⟫ = 0
参数：h : o.oangle x y = (-π / 2 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_neg_pi_div_two`：inner_eq_zero_of_
oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : Real)) : ⟪x, y⟫
 = 0

--- 原说明 ---
If the oriented angle between two vectors is `-π / 2`, the inner product of thos
e vectors
(reversed) is zero.
-/
theorem inner_rev_eq_zero_of_oangle_eq_neg_pi_div_two {x y : V} (h : o.oangle x y = (-π / 2 : ℝ)) :
    ⟪y, x⟫ = 0 := by rw [real_inner_comm, o.inner_eq_zero_of_oangle_eq_neg_pi_div_two h]

/-- Negating the first vector passed to `oangle` negates the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_neg_left (x y : V) : (o.oangle (-x) y).sign = -(o.oangle x y).
sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Real.Angle.sign_zero`：sign_zero : (0 : Angle).sign = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `Orientation.oangle_neg_left`：oangle_neg_left {x y : V} (hx : x != 0) (hy
 : y != 0) : o.oangle (-x) y = o.oangle x y + π
· 使用定理 `Real.Angle.sign_add_pi`：sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign

--- 原说明 ---
Negating the first vector passed to `oangle` negates the sign of the angle.
-/
theorem oangle_sign_neg_left (x y : V) : (o.oangle (-x) y).sign = -(o.oangle x y).sign := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_left hx hy, Real.Angle.sign_add_pi]

/-- Negating the second vector passed to `oangle` negates the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_neg_right (x y : V) : (o.oangle x (-y)).sign = -(o.oangle x y)
.sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Real.Angle.sign_zero`：sign_zero : (0 : Angle).sign = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `Orientation.oangle_neg_right`：oangle_neg_right {x y : V} (hx : x != 0) (
hy : y != 0) : o.oangle x (-y) = o.oangle x y + π
· 使用定理 `Real.Angle.sign_add_pi`：sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign

--- 原说明 ---
Negating the second vector passed to `oangle` negates the sign of the angle.
-/
theorem oangle_sign_neg_right (x y : V) : (o.oangle x (-y)).sign = -(o.oangle x y).sign := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.oangle_neg_right hx hy, Real.Angle.sign_add_pi]

/-- Multiplying the first vector passed to `oangle` by a real multiplies the sign of the angle by
the sign of the real. -/
@[simp]
/-
**Orientation.oangle_sign_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_smul_left (x y : V) (r : Real) : (o.oangle (r • x) y).sign = S
ignType.sign r * (o.oangle x y).sign
参数：x y : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_left_of_neg`：oangle_smul_left_of_neg (x y : V) {
r : Real} (hr : r < 0) : o.oangle (r • x) y = o.oangle (-x) y
· 使用定理 `Orientation.oangle_sign_neg_left`：oangle_sign_neg_left (x y : V) : (o.oa
ngle (-x) y).sign = -(o.oangle x y).sign
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Real.Angle.sign_zero`：sign_zero : (0 : Angle).sign = 0
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Orientation.oangle_smul_left_of_pos`：oangle_smul_left_of_pos (x y : V) {
r : Real} (hr : 0 < r) : o.oangle (r • x) y = o.oangle x y
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1

--- 原说明 ---
Multiplying the first vector passed to `oangle` by a real multiplies the sign of
 the angle by
the sign of the real.
-/
theorem oangle_sign_smul_left (x y : V) (r : ℝ) :
    (o.oangle (r • x) y).sign = SignType.sign r * (o.oangle x y).sign := by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

/-- Multiplying the second vector passed to `oangle` by a real multiplies the sign of the angle by
the sign of the real. -/
@[simp]
/-
**Orientation.oangle_sign_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_smul_right (x y : V) (r : Real) : (o.oangle x (r • y)).sign = 
SignType.sign r * (o.oangle x y).sign
参数：x y : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_right_of_neg`：oangle_smul_right_of_neg (x y : V)
 {r : Real} (hr : r < 0) : o.oangle x (r • y) = o.oangle x (-y)
· 使用定理 `Orientation.oangle_sign_neg_right`：oangle_sign_neg_right (x y : V) : (o.
oangle x (-y)).sign = -(o.oangle x y).sign
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `Real.Angle.sign_zero`：sign_zero : (0 : Angle).sign = 0
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Orientation.oangle_smul_right_of_pos`：oangle_smul_right_of_pos (x y : V)
 {r : Real} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1

--- 原说明 ---
Multiplying the second vector passed to `oangle` by a real multiplies the sign o
f the angle by
the sign of the real.
-/
theorem oangle_sign_smul_right (x y : V) (r : ℝ) :
    (o.oangle x (r • y)).sign = SignType.sign r * (o.oangle x y).sign := by
  rcases lt_trichotomy r 0 with (h | h | h) <;> simp [h]

/-- Auxiliary lemma for the proof of `oangle_sign_smul_add_right`; not intended to be used
outside of that proof. -/
/-
**Orientation.oangle_smul_add_right_eq_zero_or_eq_pi_iff** 是 Mathlib 中的一个定理，位于命名
空间 `Orientation`。
形式化陈述：oangle_smul_add_right_eq_zero_or_eq_pi_iff {x y : V} (r : Real) : o.oangle
 x (r • x + y) = 0 ∨ o.oangle x (r • x + y) = π ↔ o.oangle x y = 0 ∨ o.oangle x 
y = π
参数：r : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a

--- 原说明 ---
Auxiliary lemma for the proof of `oangle_sign_smul_add_right`; not intended to b
e used
outside of that proof.
-/
theorem oangle_smul_add_right_eq_zero_or_eq_pi_iff {x y : V} (r : ℝ) :
    o.oangle x (r • x + y) = 0 ∨ o.oangle x (r • x + y) = π ↔
    o.oangle x y = 0 ∨ o.oangle x y = π := by
  simp_rw [oangle_eq_zero_or_eq_pi_iff_not_linearIndependent, Fintype.not_linearIndependent_iff,
    Fin.sum_univ_two, Fin.exists_fin_two]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • (r • x + y) = 0 at h
    refine ⟨![m 0 + m 1 * r, m 1], ?_⟩
    change (m 0 + m 1 * r) • x + m 1 • y = 0 ∧ (m 0 + m 1 * r ≠ 0 ∨ m 1 ≠ 0)
    rw [smul_add, smul_smul, ← add_assoc, ← add_smul] at h
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul, add_zero] at h0
    simp [h0] at hm
  · rcases h with ⟨m, h, hm⟩
    change m 0 • x + m 1 • y = 0 at h
    refine ⟨![m 0 - m 1 * r, m 1], ?_⟩
    change (m 0 - m 1 * r) • x + m 1 • (r • x + y) = 0 ∧ (m 0 - m 1 * r ≠ 0 ∨ m 1 ≠ 0)
    rw [sub_smul, smul_add, smul_smul, ← add_assoc, sub_add_cancel]
    refine ⟨h, not_and_or.1 fun h0 => ?_⟩
    obtain ⟨h0, h1⟩ := h0
    rw [h1] at h0 hm
    rw [zero_mul, sub_zero] at h0
    simp [h0] at hm

/-- Adding a multiple of the first vector passed to `oangle` to the second vector does not change
the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_smul_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：oangle_sign_smul_add_right (x y : V) (r : Real) : (o.oangle x (r • x + y))
.sign = (o.oangle x y).sign
参数：x y : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.Angle.sign_eq_zero_iff`：sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔
 θ = 0 ∨ θ = π
· 使用定理 `Orientation.oangle_smul_add_right_eq_zero_or_eq_pi_iff`：oangle_smul_add_
right_eq_zero_or_eq_pi_iff {x y : V} (r : Real) : o.oangle x (r • x + y) = 0 ∨ o
.oangle x (r • x + y) = π ↔ o.oangle x y = 0…
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `isConnected_univ`：isConnected_univ [ConnectedSpace α] : IsConnected (uni
v : Set α)
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `ContinuousOn.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : Topological
Space X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousOn.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `Orientation.continuousAt_oangle`：continuousAt_oangle {x : V × V} (hx1 : 
x.1 != 0) (hx2 : x.2 != 0) : ContinuousAt (fun y : V × V => o.oangle y.1 y.2) x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Adding a multiple of the first vector passed to `oangle` to the second vector do
es not change
the sign of the angle.
-/
theorem oangle_sign_smul_add_right (x y : V) (r : ℝ) :
    (o.oangle x (r • x + y)).sign = (o.oangle x y).sign := by
  by_cases h : o.oangle x y = 0 ∨ o.oangle x y = π
  · rwa [Real.Angle.sign_eq_zero_iff.2 h, Real.Angle.sign_eq_zero_iff,
      oangle_smul_add_right_eq_zero_or_eq_pi_iff]
  have h' : ∀ r' : ℝ, o.oangle x (r' • x + y) ≠ 0 ∧ o.oangle x (r' • x + y) ≠ π := by
    intro r'
    rwa [← o.oangle_smul_add_right_eq_zero_or_eq_pi_iff r', not_or] at h
  let s : Set (V × V) := (fun r' : ℝ => (x, r' • x + y)) '' Set.univ
  have hc : IsConnected s := isConnected_univ.image _ (by fun_prop)
  have hf : ContinuousOn (fun z : V × V => o.oangle z.1 z.2) s := by
    refine continuousOn_of_forall_continuousAt fun z hz => o.continuousAt_oangle ?_ ?_
    all_goals
      simp_rw [s, Set.mem_image] at hz
      obtain ⟨r', -, rfl⟩ := hz
      simp only
      intro hz
    · simpa [hz] using (h' 0).1
    · simpa [hz] using (h' r').1
  have hs : ∀ z : V × V, z ∈ s → o.oangle z.1 z.2 ≠ 0 ∧ o.oangle z.1 z.2 ≠ π := by grind
  have hx : (x, y) ∈ s := by
    convert! Set.mem_image_of_mem (fun r' : ℝ => (x, r' • x + y)) (Set.mem_univ 0)
    simp
  have hy : (x, r • x + y) ∈ s := Set.mem_image_of_mem _ (Set.mem_univ _)
  convert! Real.Angle.sign_eq_of_continuousOn hc hf hs hx hy

/-- Adding a multiple of the second vector passed to `oangle` to the first vector does not change
the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_add_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_add_smul_left (x y : V) (r : Real) : (o.oangle (x + r • y) y).
sign = (o.oangle x y).sign
参数：x y : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Orientation.oangle_sign_smul_add_right`：oangle_sign_smul_add_right (x y 
: V) (r : Real) : (o.oangle x (r • x + y)).sign = (o.oangle x y).sign
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Adding a multiple of the second vector passed to `oangle` to the first vector do
es not change
the sign of the angle.
-/
theorem oangle_sign_add_smul_left (x y : V) (r : ℝ) :
    (o.oangle (x + r • y) y).sign = (o.oangle x y).sign := by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm x, oangle_sign_smul_add_right]

/-- Subtracting a multiple of the first vector passed to `oangle` from the second vector does
not change the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_sub_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：oangle_sign_sub_smul_right (x y : V) (r : Real) : (o.oangle x (y - r • x))
.sign = (o.oangle x y).sign
参数：x y : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.oangle_sign_smul_add_right`：oangle_sign_smul_add_right (x y 
: V) (r : Real) : (o.oangle x (r • x + y)).sign = (o.oangle x y).sign

--- 原说明 ---
Subtracting a multiple of the first vector passed to `oangle` from the second ve
ctor does
not change the sign of the angle.
-/
theorem oangle_sign_sub_smul_right (x y : V) (r : ℝ) :
    (o.oangle x (y - r • x)).sign = (o.oangle x y).sign := by
  rw [sub_eq_add_neg, ← neg_smul, add_comm, oangle_sign_smul_add_right]

/-- Subtracting a multiple of the second vector passed to `oangle` from the first vector does
not change the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_sub_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_sub_smul_left (x y : V) (r : Real) : (o.oangle (x - r • y) y).
sign = (o.oangle x y).sign
参数：x y : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Orientation.oangle_sign_add_smul_left`：oangle_sign_add_smul_left (x y : 
V) (r : Real) : (o.oangle (x + r • y) y).sign = (o.oangle x y).sign

--- 原说明 ---
Subtracting a multiple of the second vector passed to `oangle` from the first ve
ctor does
not change the sign of the angle.
-/
theorem oangle_sign_sub_smul_left (x y : V) (r : ℝ) :
    (o.oangle (x - r • y) y).sign = (o.oangle x y).sign := by
  rw [sub_eq_add_neg, ← neg_smul, oangle_sign_add_smul_left]

/-- Adding the first vector passed to `oangle` to the second vector does not change the sign of
the angle. -/
@[simp]
/-
**Orientation.oangle_sign_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_add_right (x y : V) : (o.oangle x (x + y)).sign = (o.oangle x 
y).sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sign_smul_add_right`：oangle_sign_smul_add_right (x y 
: V) (r : Real) : (o.oangle x (r • x + y)).sign = (o.oangle x y).sign
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
Adding the first vector passed to `oangle` to the second vector does not change 
the sign of
the angle.
-/
theorem oangle_sign_add_right (x y : V) : (o.oangle x (x + y)).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_smul_add_right x y 1, one_smul]

/-- Adding the second vector passed to `oangle` to the first vector does not change the sign of
the angle. -/
@[simp]
/-
**Orientation.oangle_sign_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_add_left (x y : V) : (o.oangle (x + y) y).sign = (o.oangle x y
).sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sign_add_smul_left`：oangle_sign_add_smul_left (x y : 
V) (r : Real) : (o.oangle (x + r • y) y).sign = (o.oangle x y).sign
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
Adding the second vector passed to `oangle` to the first vector does not change 
the sign of
the angle.
-/
theorem oangle_sign_add_left (x y : V) : (o.oangle (x + y) y).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_add_smul_left x y 1, one_smul]

/-- Subtracting the first vector passed to `oangle` from the second vector does not change the
sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_sub_right (x y : V) : (o.oangle x (y - x)).sign = (o.oangle x 
y).sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sign_sub_smul_right`：oangle_sign_sub_smul_right (x y 
: V) (r : Real) : (o.oangle x (y - r • x)).sign = (o.oangle x y).sign
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
Subtracting the first vector passed to `oangle` from the second vector does not 
change the
sign of the angle.
-/
theorem oangle_sign_sub_right (x y : V) : (o.oangle x (y - x)).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_sub_smul_right x y 1, one_smul]

/-- Subtracting the second vector passed to `oangle` from the first vector does not change the
sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_sub_left (x y : V) : (o.oangle (x - y) y).sign = (o.oangle x y
).sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sign_sub_smul_left`：oangle_sign_sub_smul_left (x y : 
V) (r : Real) : (o.oangle (x - r • y) y).sign = (o.oangle x y).sign
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
Subtracting the second vector passed to `oangle` from the first vector does not 
change the
sign of the angle.
-/
theorem oangle_sign_sub_left (x y : V) : (o.oangle (x - y) y).sign = (o.oangle x y).sign := by
  rw [← o.oangle_sign_sub_smul_left x y 1, one_smul]

/-- Subtracting the second vector passed to `oangle` from a multiple of the first vector negates
the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_smul_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：oangle_sign_smul_sub_right (x y : V) (r : Real) : (o.oangle x (r • x - y))
.sign = -(o.oangle x y).sign
参数：x y : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sign_neg_right`：oangle_sign_neg_right (x y : V) : (o.
oangle x (-y)).sign = -(o.oangle x y).sign
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Orientation.oangle_sign_smul_add_right`：oangle_sign_smul_add_right (x y 
: V) (r : Real) : (o.oangle x (r • x + y)).sign = (o.oangle x y).sign

--- 原说明 ---
Subtracting the second vector passed to `oangle` from a multiple of the first ve
ctor negates
the sign of the angle.
-/
theorem oangle_sign_smul_sub_right (x y : V) (r : ℝ) :
    (o.oangle x (r • x - y)).sign = -(o.oangle x y).sign := by
  rw [← oangle_sign_neg_right, sub_eq_add_neg, oangle_sign_smul_add_right]

/-- Subtracting the first vector passed to `oangle` from a multiple of the second vector negates
the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_smul_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_smul_sub_left (x y : V) (r : Real) : (o.oangle (r • y - x) y).
sign = -(o.oangle x y).sign
参数：x y : V；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sign_neg_left`：oangle_sign_neg_left (x y : V) : (o.oa
ngle (-x) y).sign = -(o.oangle x y).sign
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `Orientation.oangle_sign_add_smul_left`：oangle_sign_add_smul_left (x y : 
V) (r : Real) : (o.oangle (x + r • y) y).sign = (o.oangle x y).sign

--- 原说明 ---
Subtracting the first vector passed to `oangle` from a multiple of the second ve
ctor negates
the sign of the angle.
-/
theorem oangle_sign_smul_sub_left (x y : V) (r : ℝ) :
    (o.oangle (r • y - x) y).sign = -(o.oangle x y).sign := by
  rw [← oangle_sign_neg_left, sub_eq_neg_add, oangle_sign_add_smul_left]

/-- Subtracting the second vector passed to `oangle` from the first vector negates the sign of
the angle. -/
/-
**Orientation.oangle_sign_sub_right_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientatio
n`。
形式化陈述：oangle_sign_sub_right_eq_neg (x y : V) : (o.oangle x (x - y)).sign = -(o.o
angle x y).sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sign_smul_sub_right`：oangle_sign_smul_sub_right (x y 
: V) (r : Real) : (o.oangle x (r • x - y)).sign = -(o.oangle x y).sign
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
Subtracting the second vector passed to `oangle` from the first vector negates t
he sign of
the angle.
-/
theorem oangle_sign_sub_right_eq_neg (x y : V) :
    (o.oangle x (x - y)).sign = -(o.oangle x y).sign := by
  rw [← o.oangle_sign_smul_sub_right x y 1, one_smul]

/-- Subtracting the first vector passed to `oangle` from the second vector negates the sign of
the angle. -/
/-
**Orientation.oangle_sign_sub_left_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation
`。
形式化陈述：oangle_sign_sub_left_eq_neg (x y : V) : (o.oangle (y - x) y).sign = -(o.oa
ngle x y).sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sign_smul_sub_left`：oangle_sign_smul_sub_left (x y : 
V) (r : Real) : (o.oangle (r • y - x) y).sign = -(o.oangle x y).sign
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
Subtracting the first vector passed to `oangle` from the second vector negates t
he sign of
the angle.
-/
theorem oangle_sign_sub_left_eq_neg (x y : V) :
    (o.oangle (y - x) y).sign = -(o.oangle x y).sign := by
  rw [← o.oangle_sign_smul_sub_left x y 1, one_smul]

/-- Subtracting the first vector passed to `oangle` from the second vector then swapping the
vectors does not change the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_sub_right_swap** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`
。
形式化陈述：oangle_sign_sub_right_swap (x y : V) : (o.oangle y (y - x)).sign = (o.oang
le x y).sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_eq_neg`：oangle_sign_sub_right_eq_neg (
x y : V) : (o.oangle x (x - y)).sign = -(o.oangle x y).sign
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign

--- 原说明 ---
Subtracting the first vector passed to `oangle` from the second vector then swap
ping the
vectors does not change the sign of the angle.
-/
theorem oangle_sign_sub_right_swap (x y : V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign := by
  rw [oangle_sign_sub_right_eq_neg, o.oangle_rev y x, Real.Angle.sign_neg]

/-- Subtracting the second vector passed to `oangle` from the first vector then swapping the
vectors does not change the sign of the angle. -/
@[simp]
/-
**Orientation.oangle_sign_sub_left_swap** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sign_sub_left_swap (x y : V) : (o.oangle (x - y) x).sign = (o.oangl
e x y).sign
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_left_eq_neg`：oangle_sign_sub_left_eq_neg (x 
y : V) : (o.oangle (y - x) y).sign = -(o.oangle x y).sign
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign

--- 原说明 ---
Subtracting the second vector passed to `oangle` from the first vector then swap
ping the
vectors does not change the sign of the angle.
-/
theorem oangle_sign_sub_left_swap (x y : V) : (o.oangle (x - y) x).sign = (o.oangle x y).sign := by
  rw [oangle_sign_sub_left_eq_neg, o.oangle_rev y x, Real.Angle.sign_neg]

/-- The sign of the angle between a vector, and a linear combination of that vector with a second
vector, is the sign of the factor by which the second vector is multiplied in that combination
multiplied by the sign of the angle between the two vectors. -/
/-
**Orientation.oangle_sign_smul_add_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Orienta
tion`。
形式化陈述：oangle_sign_smul_add_smul_right (x y : V) (r₁ r₂ : Real) : (o.oangle x (r₁
 • x + r₂ • y)).sign = SignType.sign r₂ * (o.oangle x y).sign
参数：x y : V；r₁ r₂ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_smul_add_right`：oangle_sign_smul_add_right (x y 
: V) (r : Real) : (o.oangle x (r • x + y)).sign = (o.oangle x y).sign
· 使用定理 `Orientation.oangle_sign_smul_right`：oangle_sign_smul_right (x y : V) (r 
: Real) : (o.oangle x (r • y)).sign = SignType.sign r * (o.oangle x y).sign
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The sign of the angle between a vector, and a linear combination of that vector 
with a second
vector, is the sign of the factor by which the second vector is multiplied in th
at combination
multiplied by the sign of the angle between the two vectors.
-/
theorem oangle_sign_smul_add_smul_right (x y : V) (r₁ r₂ : ℝ) :
    (o.oangle x (r₁ • x + r₂ • y)).sign = SignType.sign r₂ * (o.oangle x y).sign := by
  simp

/-- The sign of the angle between a linear combination of two vectors and the second vector is
the sign of the factor by which the first vector is multiplied in that combination multiplied by
the sign of the angle between the two vectors. -/
/-
**Orientation.oangle_sign_smul_add_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Orientat
ion`。
形式化陈述：oangle_sign_smul_add_smul_left (x y : V) (r₁ r₂ : Real) : (o.oangle (r₁ • 
x + r₂ • y) y).sign = SignType.sign r₁ * (o.oangle x y).sign
参数：x y : V；r₁ r₂ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.oangle_sign_smul_add_smul_right`：oangle_sign_smul_add_smul_r
ight (x y : V) (r₁ r₂ : Real) : (o.oangle x (r₁ • x + r₂ • y)).sign = SignType.s
ign r₂ * (o.oangle x y).sign
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The sign of the angle between a linear combination of two vectors and the second
 vector is
the sign of the factor by which the first vector is multiplied in that combinati
on multiplied by
the sign of the angle between the two vectors.
-/
theorem oangle_sign_smul_add_smul_left (x y : V) (r₁ r₂ : ℝ) :
    (o.oangle (r₁ • x + r₂ • y) y).sign = SignType.sign r₁ * (o.oangle x y).sign := by
  simp_rw [o.oangle_rev y, Real.Angle.sign_neg, add_comm (r₁ • x), oangle_sign_smul_add_smul_right,
    mul_neg]

/-- The sign of the angle between two linear combinations of two vectors is the sign of the
determinant of the factors in those combinations multiplied by the sign of the angle between the
two vectors. -/
/-
**Orientation.oangle_sign_smul_add_smul_smul_add_smul** 是 Mathlib 中的一个定理，位于命名空间 
`Orientation`。
形式化陈述：oangle_sign_smul_add_smul_smul_add_smul (x y : V) (r₁ r₂ r₃ r₄ : Real) : (
o.oangle (r₁ • x + r₂ • y) (r₃ • x + r₄ • y)).sign = SignType.sign (r₁ * r₄ - r₂
 * r₃) * (o.oangle x y).sign
参数：x y : V；r₁ r₂ r₃ r₄ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Left.sign_neg`：Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) =
 -sign a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Orientation.oangle_sign_smul_left`：oangle_sign_smul_left (x y : V) (r : 
Real) : (o.oangle (r • x) y).sign = SignType.sign r * (o.oangle x y).sign
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.oangle_sign_smul_add_smul_right`：oangle_sign_smul_add_smul_r
ight (x y : V) (r₁ r₂ : Real) : (o.oangle x (r₁ • x + r₂ • y)).sign = SignType.s
ign r₂ * (o.oangle x y).sign
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Real.Angle.sign_neg`：sign_neg (θ : Angle) : (-θ).sign = -θ.sign
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sign_smul_add_right`：oangle_sign_smul_add_right (x y 
: V) (r : Real) : (o.oangle x (r • x + y)).sign = (o.oangle x y).sign
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Orientation.oangle_sign_smul_right`：oangle_sign_smul_right (x y : V) (r 
: Real) : (o.oangle x (r • y)).sign = SignType.sign r * (o.oangle x y).sign
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The sign of the angle between two linear combinations of two vectors is the sign
 of the
determinant of the factors in those combinations multiplied by the sign of the a
ngle between the
two vectors.
-/
theorem oangle_sign_smul_add_smul_smul_add_smul (x y : V) (r₁ r₂ r₃ r₄ : ℝ) :
    (o.oangle (r₁ • x + r₂ • y) (r₃ • x + r₄ • y)).sign =
      SignType.sign (r₁ * r₄ - r₂ * r₃) * (o.oangle x y).sign := by
  by_cases hr₁ : r₁ = 0
  · rw [hr₁, zero_smul, zero_mul, zero_add, zero_sub, Left.sign_neg,
      oangle_sign_smul_left, add_comm, oangle_sign_smul_add_smul_right, oangle_rev,
      Real.Angle.sign_neg, sign_mul, mul_neg, mul_neg, neg_mul, mul_assoc]
  · rw [← o.oangle_sign_smul_add_right (r₁ • x + r₂ • y) (r₃ • x + r₄ • y) (-r₃ / r₁), smul_add,
      smul_smul, smul_smul, div_mul_cancel₀ _ hr₁, neg_smul, ← add_assoc, add_comm (-(r₃ • x)), ←
      sub_eq_add_neg, sub_add_cancel, ← add_smul, oangle_sign_smul_right,
      oangle_sign_smul_add_smul_left, ← mul_assoc, ← sign_mul, add_mul, mul_assoc, mul_comm r₂ r₁, ←
      mul_assoc, div_mul_cancel₀ _ hr₁, add_comm, neg_mul, ← sub_eq_add_neg, mul_comm r₄,
      mul_comm r₃]

/-- A base angle of an isosceles triangle is acute, oriented vector angle form. -/
/-
**Orientation.abs_oangle_sub_left_toReal_lt_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间
 `Orientation`。
形式化陈述：abs_oangle_sub_left_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) : |(o.o
angle (y - x) y).toReal| < π / 2
参数：h : ‖x‖ = ‖y‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Orientation.oangle_sign_sub_left_swap`：oangle_sign_sub_left_swap (x y : 
V) : (o.oangle (x - y) x).sign = (o.oangle x y).sign
· 使用定理 `Orientation.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq`：oangle_eq_
pi_sub_two_zsmul_oangle_sub_of_norm_eq {x y : V} (hn : x != y) (h : ‖x‖ = ‖y‖) :
 o.oangle y x = π - (2 : Int) • o.oangle (y - x) y
· 使用定理 `Real.Angle.sign_pi_sub`：sign_pi_sub (θ : Angle) : ((π : Angle) - θ).sign
 = θ.sign
· 使用定理 `Real.Angle.sign_two_zsmul_eq_sign_iff`：sign_two_zsmul_eq_sign_iff {θ : A
ngle} : ((2 : Int) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Orientation.oangle_eq_pi_iff_sameRay_neg`：oangle_eq_pi_iff_sameRay_neg {
x y : V} : o.oangle x y = π ↔ x != 0 ∧ y != 0 ∧ SameRay Real x (-y)
· 使用定理 `Orientation.oangle_eq_pi_iff_oangle_rev_eq_pi`：oangle_eq_pi_iff_oangle_r
ev_eq_pi {x y : V} : o.oangle x y = π ↔ o.oangle y x = π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_nonneg_left_iff_sameRay`：exists_nonneg_left_iff_sameRay (hx : x !
= 0) : (exists r : R, 0 <= r ∧ r • x = y) ↔ SameRay R x y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_eq_right`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, a + b = b ↔ a = 0
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
A base angle of an isosceles triangle is acute, oriented vector angle form.
-/
theorem abs_oangle_sub_left_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) :
    |(o.oangle (y - x) y).toReal| < π / 2 := by
  by_cases hn : x = y; · simp [hn, Real.pi_pos]
  have hs : ((2 : ℤ) • o.oangle (y - x) y).sign = (o.oangle (y - x) y).sign := by
    conv_rhs => rw [oangle_sign_sub_left_swap]
    rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hn h, Real.Angle.sign_pi_sub]
  rw [Real.Angle.sign_two_zsmul_eq_sign_iff] at hs
  rcases hs with (hs | hs)
  · rw [oangle_eq_pi_iff_oangle_rev_eq_pi, oangle_eq_pi_iff_sameRay_neg, neg_sub] at hs
    rcases hs with ⟨hy, -, hr⟩
    rw [← exists_nonneg_left_iff_sameRay hy] at hr
    rcases hr with ⟨r, hr0, hr⟩
    rw [eq_sub_iff_add_eq] at hr
    nth_rw 2 [← one_smul ℝ y] at hr
    rw [← add_smul] at hr
    rw [← hr, norm_smul, Real.norm_eq_abs, abs_of_pos (Left.add_pos_of_nonneg_of_pos hr0 one_pos),
      mul_left_eq_self₀, or_iff_left (norm_ne_zero_iff.2 hy), add_eq_right] at h
    rw [h, zero_add, one_smul] at hr
    exact False.elim (hn hr.symm)
  · exact hs

/-- A base angle of an isosceles triangle is acute, oriented vector angle form. -/
/-
**Orientation.abs_oangle_sub_right_toReal_lt_pi_div_two** 是 Mathlib 中的一个定理，位于命名空
间 `Orientation`。
形式化陈述：abs_oangle_sub_right_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) : |(o.
oangle x (x - y)).toReal| < π / 2
参数：h : ‖x‖ = ‖y‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Orientation.abs_oangle_sub_left_toReal_lt_pi_div_two`：abs_oangle_sub_lef
t_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) : |(o.oangle (y - x) y).toReal|
 < π / 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_sub_eq_oangle_sub_rev_of_norm_eq`：oangle_sub_eq_oangl
e_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) : o.oangle x (x - y) = o.oangle (
y - x) y

--- 原说明 ---
A base angle of an isosceles triangle is acute, oriented vector angle form.
-/
theorem abs_oangle_sub_right_toReal_lt_pi_div_two {x y : V} (h : ‖x‖ = ‖y‖) :
    |(o.oangle x (x - y)).toReal| < π / 2 :=
  (o.oangle_sub_eq_oangle_sub_rev_of_norm_eq h).symm ▸ o.abs_oangle_sub_left_toReal_lt_pi_div_two h

/-- `y` has equal unoriented angles to `x` and `z` if and only if it has equal oriented angles
(bisects the angle) or `x` and `z` are on the same ray. -/
/-
**Orientation.angle_eq_iff_oangle_eq_or_sameRay** 是 Mathlib 中的一个引理，位于命名空间 `Orien
tation`。
形式化陈述：angle_eq_iff_oangle_eq_or_sameRay {x y z : V} (hx : x != 0) (hz : z != 0) 
: InnerProductGeometry.angle x y = InnerProductGeometry.angle y z ↔ o.oangle x y
 = o.oangle y z ∨ SameRay Real x z
参数：hx : x != 0；hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `InnerProductGeometry.angle_zero_right`：angle_zero_right (x : V) : angle 
x 0 = π / 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `SameRay.exists_pos_left`：exists_pos_left (h : SameRay R x y) (hx : x != 
0) (hy : y != 0) : exists r : R, 0 < r ∧ r • x = y
· 使用定理 `InnerProductGeometry.angle_smul_right_of_pos`：angle_smul_right_of_pos (x
 y : V) {r : Real} (hr : 0 < r) : angle x (r • y) = angle x y
· 使用定理 `InnerProductGeometry.angle_comm`：angle_comm (x y : V) : angle x y = angl
e y x
· 使用定理 `Orientation.oangle_smul_right_of_pos`：oangle_smul_right_of_pos (x y : V)
 {r : Real} (hr : 0 < r) : o.oangle x (r • y) = o.oangle x y
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Orientation.angle_eq_iff_oangle_eq_of_sign_eq`：angle_eq_iff_oangle_eq_of
_sign_eq {w x y z : V} (hw : w != 0) (hx : x != 0) (hy : y != 0) (hz : z != 0) (
hs : (o.oangle w x).sign = (o.oangl…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.oangle_eq_zero_iff_sameRay`：oangle_eq_zero_iff_sameRay {x y 
: V} : o.oangle x y = 0 ↔ SameRay Real x y
· 使用定理 `Orientation.oangle_add`：oangle_add {x y z : V} (hx : x != 0) (hy : y != 
0) (hz : z != 0) : o.oangle x y + o.oangle y z = o.oangle x z
· 使用引理 `Orientation.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg`：angle_eq_iff_oang
le_eq_neg_of_sign_eq_neg {w x y z : V} (hw : w != 0) (hx : x != 0) (hy : y != 0)
 (hz : z != 0) (hs : (o.oangle w x).sign = …
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
`y` has equal unoriented angles to `x` and `z` if and only if it has equal orien
ted angles
(bisects the angle) or `x` and `z` are on the same ray.
-/
lemma angle_eq_iff_oangle_eq_or_sameRay {x y z : V} (hx : x ≠ 0) (hz : z ≠ 0) :
    InnerProductGeometry.angle x y = InnerProductGeometry.angle y z ↔
      o.oangle x y = o.oangle y z ∨ SameRay ℝ x z := by
  by_cases hy : y = 0
  · simp [hy]
  by_cases hr : SameRay ℝ x z
  · obtain ⟨r, hrp, rfl⟩ := hr.exists_pos_left hx hz
    simp [hr, hrp, InnerProductGeometry.angle_comm]
  simp only [hr, or_false]
  by_cases hs : (o.oangle x y).sign = (o.oangle y z).sign
  · rw [o.angle_eq_iff_oangle_eq_of_sign_eq hx hy hy hz hs]
  · have hn : o.oangle x y ≠ o.oangle y z := by grind
    simp only [hn, iff_false]
    intro he
    apply hr
    by_cases hs' : (o.oangle x y).sign = -(o.oangle y z).sign
    · rw [o.angle_eq_iff_oangle_eq_neg_of_sign_eq_neg hx hy hy hz hs'] at he
      rw [← o.oangle_eq_zero_iff_sameRay, ← o.oangle_add hx hy hz]
      simp [he]
    · have h0 : (o.oangle x y).sign = 0 ∨ (o.oangle y z).sign = 0 := by
        revert hs hs'
        generalize (o.oangle x y).sign = sxy
        generalize (o.oangle y z).sign = syz
        decide +revert
      have h0' : InnerProductGeometry.angle y z = 0 ∨ InnerProductGeometry.angle y z = π := by
        rcases h0 with h0 | h0
          <;> simpa [*] using o.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h0
      rcases h0' with h0' | h0'
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_zero_iff.1 he
        simp_all
      · rw [h0'] at he
        obtain ⟨-, r, hr0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 h0'
        obtain ⟨-, r', hr'0, rfl⟩ := InnerProductGeometry.angle_eq_pi_iff.1 he
        simp_all

end Orientation

