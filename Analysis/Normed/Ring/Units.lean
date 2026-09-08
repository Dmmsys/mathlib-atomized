/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.RingTheory.Ideal.Nonunits

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `Units.add` and `Units.ofNearby` (based on `Units.oneSub` defined elsewhere)
state, in varying forms, that perturbations of a unit are units. They are not stated
in their optimal form; more precise versions would use the spectral radius.

The first main result is `Units.isOpen`: the group of units of a normed ring with summable
geometric series is an open subset of the ring.

The function `Ring.inverse` (defined elsewhere), for a ring `R`, sends `a : R` to `a⁻¹` if `a` is a
unit and `0` if not.  The other major results of this file (notably `NormedRing.inverse_add`,
`NormedRing.inverse_add_norm` and `NormedRing.inverse_add_norm_diff_nth_order`) cover the asymptotic
properties of `Ring.inverse (x + t)` as `t → 0`.
-/

@[expose] public section

noncomputable section

open Topology
open scoped Ring

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

namespace Units

/-- In a normed ring with summable geometric series, a perturbation of a unit `x` by an
element `t` of distance less than `‖x⁻¹‖⁻¹` from `x` is a unit.
Here we construct its `Units` structure. -/
@[simps! val]
/-
**Units.add** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：add (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ
参数：x : Rˣ；t : R；h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a normed ring with summable geometric series, a perturbation of a unit `x` by
 an
element `t` of distance less than `‖x⁻¹‖⁻¹` from `x` is a unit.
Here we construct its `Units` structure.
-/
def add (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  Units.copy -- to make `add_val` true definitionally, for convenience
    (x * Units.oneSub (-((x⁻¹).1 * t)) (by
      nontriviality R using zero_lt_one
      have hpos : 0 < ‖(↑x⁻¹ : R)‖ := Units.norm_pos x⁻¹
      calc
        ‖-(↑x⁻¹ * t)‖ = ‖↑x⁻¹ * t‖ := by rw [norm_neg]
        _ ≤ ‖(↑x⁻¹ : R)‖ * ‖t‖ := norm_mul_le (x⁻¹).1 _
        _ < ‖(↑x⁻¹ : R)‖ * ‖(↑x⁻¹ : R)‖⁻¹ := by nlinarith only [h, hpos]
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)))
    (x + t) (by simp [mul_add]) _ rfl

/-- In a normed ring with summable geometric series, an element `y` of distance less
than `‖x⁻¹‖⁻¹` from `x` is a unit. Here we construct its `Units` structure. -/
@[simps! val]
/-
**Units.ofNearby** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：ofNearby (x : Rˣ) (y : R) (h : ‖y - x‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ
参数：x : Rˣ；y : R；h : ‖y - x‖ < ‖(↑x⁻¹ : R)‖⁻¹。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a normed ring with summable geometric series, an element `y` of distance less
than `‖x⁻¹‖⁻¹` from `x` is a unit. Here we construct its `Units` structure.
-/
def ofNearby (x : Rˣ) (y : R) (h : ‖y - x‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  (x.add (y - x : R) h).copy y (by simp) _ rfl

/-- The group of units of a normed ring with summable geometric series is an open subset
of the ring. -/
/-
**Units.isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSeries R], IsOpen {
x | IsUnit x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Units.norm_pos`：Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `mem_ball_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] {a
 b : E} {r : ℝ}, b ∈ Metric.ball a r ↔ ‖b - a‖ < r

--- 原说明 ---
The group of units of a normed ring with summable geometric series is an open su
bset
of the ring.
-/
protected theorem isOpen : IsOpen { x : R | IsUnit x } := by
  nontriviality R
  rw [Metric.isOpen_iff]
  rintro _ ⟨x, rfl⟩
  refine ⟨‖(↑x⁻¹ : R)‖⁻¹, _root_.inv_pos.mpr (Units.norm_pos x⁻¹), fun y hy ↦ ?_⟩
  rw [mem_ball_iff_norm] at hy
  exact (x.ofNearby y hy).isUnit
/-
**Units.nhds** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSeries R] (x : Rˣ),
 {x | IsUnit x} ∈ nhds ↑x
参数：x : Rˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Units.isOpen`：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSer
ies R], IsOpen {x | IsUnit x}
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
protected theorem nhds (x : Rˣ) : { x : R | IsUnit x } ∈ 𝓝 (x : R) :=
  IsOpen.mem_nhds Units.isOpen x.isUnit

end Units

namespace nonunits

/-- The `nonunits` in a normed ring with summable geometric series are contained in the
complement of the ball of radius `1` centered at `1 : R`. -/
/-
**nonunits.subset_compl_ball** 是 Mathlib 中的一个定理，位于命名空间 `nonunits`。
形式化陈述：subset_compl_ball : nonunits R subseteq (Metric.ball (1 : R) 1)ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_ball_iff_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] {
a b : E} {r : ℝ}, b ∈ Metric.ball a r ↔ ‖a - b‖ < r
· 使用定理 `sub_sub_self`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - (a
 - b) = b

--- 原说明 ---
The `nonunits` in a normed ring with summable geometric series are contained in 
the
complement of the ball of radius `1` centered at `1 : R`.
-/
theorem subset_compl_ball : nonunits R ⊆ (Metric.ball (1 : R) 1)ᶜ := fun x hx h₁ ↦ hx <|
  sub_sub_self 1 x ▸ (Units.oneSub (1 - x) (by rwa [mem_ball_iff_norm'] at h₁)).isUnit

-- The `nonunits` in a normed ring with summable geometric series are a closed set
/-
**nonunits.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `nonunits`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSeries R], IsClosed
 (nonunits R)
参数：nonunits R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `Units.isOpen`：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSer
ies R], IsOpen {x | IsUnit x}
-/
protected theorem isClosed : IsClosed (nonunits R) :=
  Units.isOpen.isClosed_compl

end nonunits

namespace NormedRing

open Asymptotics Filter Metric Finset Ring

/-
**NormedRing.inverse_one_sub** 是 Mathlib 中的一个定理，位于命名空间 `NormedRing`。
形式化陈述：inverse_one_sub (t : R) (h : ‖t‖ < 1) : inverse (1 - t) = ↑(Units.oneSub t
 h)⁻¹
参数：t : R；h : ‖t‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `Units.val_oneSub`：∀ {R : Type u_4} [inst : NormedRing R] [inst_1 : HasSu
mmableGeomSeries R] (t : R) (h : ‖t‖ < 1),   ↑(Units.oneSub t h) = 1 - t
-/
theorem inverse_one_sub (t : R) (h : ‖t‖ < 1) : inverse (1 - t) = ↑(Units.oneSub t h)⁻¹ := by
  rw [← inverse_unit (Units.oneSub t h), Units.val_oneSub]

/-- The formula `Ring.inverse (x + t) = Ring.inverse (1 + x⁻¹ * t) * x⁻¹` holds for `t` sufficiently
small. -/
/-
**NormedRing.inverse_add** 是 Mathlib 中的一个定理，位于命名空间 `NormedRing`。
形式化陈述：inverse_add (x : Rˣ) : forallᶠ t in 𝓝 0, ((x : R) + t)⁻¹ʳ = (1 + ↑x⁻¹ * t)
⁻¹ʳ * ↑x⁻¹
参数：x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Metric.eventually_nhds_iff`：eventually_nhds_iff {p : α -> Prop} : (foral
lᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall ⦃y⦄, dist y x < ε -> p y
· 使用定理 `Mathlib.Tactic.CancelDenoms.cancel_factors_lt`：cancel_factors_lt {α} [Fi
eld α] [LinearOrder α] [IsStrictOrderedRing α] {a b ad bd a' b' gcd : α} (ha : a
d * a = a') (hb : bd * b = b') (had…
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The formula `Ring.inverse (x + t) = Ring.inverse (1 + x⁻¹ * t) * x⁻¹` holds for 
`t` sufficiently
small.
-/
theorem inverse_add (x : Rˣ) :
    ∀ᶠ t in 𝓝 0, ((x : R) + t)⁻¹ʳ = (1 + ↑x⁻¹ * t)⁻¹ʳ * ↑x⁻¹ := by
  nontriviality R
  rw [Metric.eventually_nhds_iff]
  refine ⟨‖(↑x⁻¹ : R)‖⁻¹, by cancel_denoms, fun t ht ↦ ?_⟩
  rw [dist_zero_right] at ht
  rw [← x.val_add t ht, inverse_unit, Units.add, Units.copy_eq, mul_inv_rev, Units.val_mul,
    ← inverse_unit, Units.val_oneSub, sub_neg_eq_add]
/-
**NormedRing.inverse_one_sub_nth_order'** 是 Mathlib 中的一个定理，位于命名空间 `NormedRing`。
形式化陈述：inverse_one_sub_nth_order' (n : Nat) {t : R} (ht : ‖t‖ < 1) : inverse ((1 
: R) - t) = (∑ i in range n, t ^ i) + t ^ n * inverse (1 - t)
参数：n : Nat；ht : ‖t‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
· 使用定理 `NormedRing.inverse_one_sub`：inverse_one_sub (t : R) (h : ‖t‖ < 1) : inve
rse (1 - t) = ↑(Units.oneSub t h)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.sum_add_tsum_nat_add`：∀ {G : Type u_2} [inst : AddCommGroup G] 
[inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] {f : ℕ → G} 
  (k : ℕ), Summable…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Summable.tsum_mul_left`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFi
lter ι} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : TopologicalSpace α] [Is
TopologicalS…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
theorem inverse_one_sub_nth_order' (n : ℕ) {t : R} (ht : ‖t‖ < 1) :
    inverse ((1 : R) - t) = (∑ i ∈ range n, t ^ i) + t ^ n * inverse (1 - t) :=
  have := _root_.summable_geometric_of_norm_lt_one ht
  calc inverse (1 - t) = ∑' i : ℕ, t ^ i := inverse_one_sub t ht
    _ = ∑ i ∈ range n, t ^ i + ∑' i : ℕ, t ^ (i + n) := (this.sum_add_tsum_nat_add _).symm
    _ = (∑ i ∈ range n, t ^ i) + t ^ n * inverse (1 - t) := by
      simp only [inverse_one_sub t ht, add_comm _ n, pow_add, this.tsum_mul_left]; rfl
/-
**NormedRing.inverse_one_sub_nth_order** 是 Mathlib 中的一个定理，位于命名空间 `NormedRing`。
形式化陈述：inverse_one_sub_nth_order (n : Nat) : forallᶠ t in 𝓝 0, inverse ((1 : R) -
 t) = (∑ i in range n, t ^ i) + t ^ n * inverse (1 - t)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.eventually_nhds_iff`：eventually_nhds_iff {p : α -> Prop} : (foral
lᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall ⦃y⦄, dist y x < ε -> p y
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `NormedRing.inverse_one_sub_nth_order'`：inverse_one_sub_nth_order' (n : N
at) {t : R} (ht : ‖t‖ < 1) : inverse ((1 : R) - t) = (∑ i in range n, t ^ i) + t
 ^ n * inverse (1 - t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
-/
theorem inverse_one_sub_nth_order (n : ℕ) :
    ∀ᶠ t in 𝓝 0, inverse ((1 : R) - t) = (∑ i ∈ range n, t ^ i) + t ^ n * inverse (1 - t) :=
  Metric.eventually_nhds_iff.2 ⟨1, one_pos, fun t ht ↦ inverse_one_sub_nth_order' n <| by
    rwa [← dist_zero_right]⟩


/-- The formula
`Ring.inverse (x + t) =
  (∑ i ∈ Finset.range n, (- x⁻¹ * t) ^ i) * x⁻¹ + (- x⁻¹ * t) ^ n * Ring.inverse (x + t)`
holds for `t` sufficiently small. -/
/-
**NormedRing.inverse_add_nth_order** 是 Mathlib 中的一个定理，位于命名空间 `NormedRing`。
形式化陈述：inverse_add_nth_order (x : Rˣ) (n : Nat) : forallᶠ t in 𝓝 0, ((x : R) + t)
⁻¹ʳ = (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹ + (-↑x⁻¹ * t) ^ n * (x + t)⁻¹ʳ
参数：x : Rˣ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `mulLeft_continuous`：mulLeft_continuous (x : R) : Continuous (AddMonoidHo
m.mulLeft x)
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `NormedRing.inverse_one_sub_nth_order`：inverse_one_sub_nth_order (n : Nat
) : forallᶠ t in 𝓝 0, inverse ((1 : R) - t) = (∑ i in range n, t ^ i) + t ^ n * 
inverse (1 - t)
· 使用定理 `NormedRing.inverse_add`：inverse_add (x : Rˣ) : forallᶠ t in 𝓝 0, ((x : R
) + t)⁻¹ʳ = (1 + ↑x⁻¹ * t)⁻¹ʳ * ↑x⁻¹
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
The formula
`Ring.inverse (x + t) =
  (∑ i ∈ Finset.range n, (- x⁻¹ * t) ^ i) * x⁻¹ + (- x⁻¹ * t) ^ n * Ring.inverse
 (x + t)`
holds for `t` sufficiently small.
-/
theorem inverse_add_nth_order (x : Rˣ) (n : ℕ) :
    ∀ᶠ t in 𝓝 0, ((x : R) + t)⁻¹ʳ =
      (∑ i ∈ range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹ + (-↑x⁻¹ * t) ^ n * (x + t)⁻¹ʳ := by
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
    (mulLeft_continuous _).tendsto' _ _ <| mul_zero _
  filter_upwards [inverse_add x, hzero.eventually (inverse_one_sub_nth_order n)] with t ht ht'
  rw [neg_mul, sub_neg_eq_add] at ht'
  conv_lhs => rw [ht, ht', add_mul, ← neg_mul, mul_assoc]
  rw [ht]
/-
**NormedRing.inverse_one_sub_norm** 是 Mathlib 中的一个定理，位于命名空间 `NormedRing`。
形式化陈述：inverse_one_sub_norm : (fun t : R => inverse (1 - t)) =O[𝓝 0] (fun _t => 1
 : R -> Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 91 条，此处仅展示前 30 条）
-/
theorem inverse_one_sub_norm : (fun t : R => inverse (1 - t)) =O[𝓝 0] (fun _t => 1 : R → ℝ) := by
  simp only [IsBigO, IsBigOWith, Metric.eventually_nhds_iff]
  refine ⟨‖(1 : R)‖ + 1, (2 : ℝ)⁻¹, by simp, fun t ht ↦ ?_⟩
  rw [dist_zero_right] at ht
  have ht' : ‖t‖ < 1 := by linarith
  simp only [inverse_one_sub t ht', norm_one, mul_one]
  change ‖∑' n : ℕ, t ^ n‖ ≤ _
  have := tsum_geometric_le_of_norm_lt_one t ht'
  have : (1 - ‖t‖)⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by simp) (by linarith)
  linarith

/-- The function `fun t ↦ inverse (x + t)` is O(1) as `t → 0`. -/
/-
**NormedRing.inverse_add_norm** 是 Mathlib 中的一个定理，位于命名空间 `NormedRing`。
形式化陈述：inverse_add_norm (x : Rˣ) : (fun t : R => inverse (↑x + t)) =O[𝓝 0] fun _t
 => (1 : Real)
参数：x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g :
 α → F}, f₁ =ᶠ[l] f₂ →…
· 使用定理 `NormedRing.inverse_add`：inverse_add (x : Rˣ) : forallᶠ t in 𝓝 0, ((x : R
) + t)⁻¹ʳ = (1 + ↑x⁻¹ * t)⁻¹ʳ * ↑x⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `mulLeft_continuous`：mulLeft_continuous (x : R) : Continuous (AddMonoidHo
m.mulLeft x)
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `NormedRing.inverse_one_sub_norm`：inverse_one_sub_norm : (fun t : R => in
verse (1 - t)) =O[𝓝 0] (fun _t => 1 : R -> Real)
· 使用定理 `Asymptotics.isBigO_const_const`：isBigO_const_const (c : E) {c' : F''} (h
c' : c' != 0) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => c'
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The function `fun t ↦ inverse (x + t)` is O(1) as `t → 0`.
-/
theorem inverse_add_norm (x : Rˣ) : (fun t : R => inverse (↑x + t)) =O[𝓝 0] fun _t => (1 : ℝ) := by
  refine EventuallyEq.trans_isBigO (inverse_add x) (one_mul (1 : ℝ) ▸ ?_)
  simp only [← sub_neg_eq_add, ← neg_mul]
  have hzero : Tendsto (-(↑x⁻¹ : R) * ·) (𝓝 0) (𝓝 0) :=
    (mulLeft_continuous _).tendsto' _ _ <| mul_zero _
  exact (inverse_one_sub_norm.comp_tendsto hzero).mul (isBigO_const_const _ one_ne_zero _)

/-- The function
`fun t ↦ Ring.inverse (x + t) - (∑ i ∈ Finset.range n, (- x⁻¹ * t) ^ i) * x⁻¹`
is `O(t ^ n)` as `t → 0`. -/
/-
**NormedRing.inverse_add_norm_diff_nth_order** 是 Mathlib 中的一个定理，位于命名空间 `NormedRi
ng`。
形式化陈述：inverse_add_norm_diff_nth_order (x : Rˣ) (n : Nat) : (fun t : R => (↑x + t
)⁻¹ʳ - (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹) =O[𝓝 (0 : R)] fun t => ‖t‖ ^ n
参数：x : Rˣ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g :
 α → F}, f₁ =ᶠ[l] f₂ →…
· 使用定理 `Filter.EventuallyEq.fun_sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] 
{f f' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → (fun i => f i - 
f' i) =ᶠ[l] fun i…
· 使用定理 `NormedRing.inverse_add_nth_order`：inverse_add_nth_order (x : Rˣ) (n : Na
t) : forallᶠ t in 𝓝 0, ((x : R) + t)⁻¹ʳ = (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x
⁻¹ + (-↑x⁻¹ * t) ^ n *…
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.IsBigO.norm_right`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `NormedRing.inverse_add_norm`：inverse_add_norm (x : Rˣ) : (fun t : R => i
nverse (↑x + t)) =O[𝓝 0] fun _t => (1 : Real)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Asymptotics.IsBigO.pow`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} [NormOn…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.IsBigO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R : 
Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filter α
}   {f : α → R}, f =O[l…

--- 原说明 ---
The function
`fun t ↦ Ring.inverse (x + t) - (∑ i ∈ Finset.range n, (- x⁻¹ * t) ^ i) * x⁻¹`
is `O(t ^ n)` as `t → 0`.
-/
theorem inverse_add_norm_diff_nth_order (x : Rˣ) (n : ℕ) :
    (fun t : R => (↑x + t)⁻¹ʳ - (∑ i ∈ range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹) =O[𝓝 (0 : R)]
      fun t => ‖t‖ ^ n := by
  refine EventuallyEq.trans_isBigO (.fun_sub (inverse_add_nth_order x n) (.refl _ _)) ?_
  simp only [add_sub_cancel_left]
  refine ((isBigO_refl _ _).norm_right.mul (inverse_add_norm x)).trans ?_
  simp only [mul_one, isBigO_norm_left]
  exact ((isBigO_refl _ _).norm_right.const_mul_left _).pow _

/-- The function `fun t ↦ Ring.inverse (x + t) - x⁻¹` is `O(t)` as `t → 0`. -/
/-
**NormedRing.inverse_add_norm_diff_first_order** 是 Mathlib 中的一个定理，位于命名空间 `Normed
Ring`。
形式化陈述：inverse_add_norm_diff_first_order (x : Rˣ) : (fun t : R => (↑x + t)⁻¹ʳ - ↑
x⁻¹) =O[𝓝 0] fun t => ‖t‖
参数：x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `NormedRing.inverse_add_norm_diff_nth_order`：inverse_add_norm_diff_nth_or
der (x : Rˣ) (n : Nat) : (fun t : R => (↑x + t)⁻¹ʳ - (∑ i in range n, (-↑x⁻¹ * t
) ^ i) * ↑x⁻¹) =O[𝓝 (0 : R)] fun…

--- 原说明 ---
The function `fun t ↦ Ring.inverse (x + t) - x⁻¹` is `O(t)` as `t → 0`.
-/
theorem inverse_add_norm_diff_first_order (x : Rˣ) :
    (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖ := by
  simpa using inverse_add_norm_diff_nth_order x 1

/-- The function `fun t ↦ Ring.inverse (x + t) - x⁻¹ + x⁻¹ * t * x⁻¹` is `O(t ^ 2)` as `t → 0`. -/
/-
**NormedRing.inverse_add_norm_diff_second_order** 是 Mathlib 中的一个定理，位于命名空间 `Norme
dRing`。
形式化陈述：inverse_add_norm_diff_second_order (x : Rˣ) : (fun t : R => (↑x + t)⁻¹ʳ - 
↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖ ^ 2
参数：x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_range_zero`：∀ {M : Type u_3} [inst : AddCommMonoid M] (f : ℕ 
→ M), ∑ k ∈ Finset.range 0, f k = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NormedRing.inverse_add_norm_diff_nth_order`：inverse_add_norm_diff_nth_or
der (x : Rˣ) (n : Nat) : (fun t : R => (↑x + t)⁻¹ʳ - (∑ i in range n, (-↑x⁻¹ * t
) ^ i) * ↑x⁻¹) =O[𝓝 (0 : R)] fun…

--- 原说明 ---
The function `fun t ↦ Ring.inverse (x + t) - x⁻¹ + x⁻¹ * t * x⁻¹` is `O(t ^ 2)` 
as `t → 0`.
-/
theorem inverse_add_norm_diff_second_order (x : Rˣ) :
    (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖ ^ 2 := by
  convert! inverse_add_norm_diff_nth_order x 2 using 2
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, add_mul, one_mul,
    ← sub_sub, neg_mul, sub_neg_eq_add]

/-- The function `Ring.inverse` is continuous at each unit of `R`. -/
/-
**NormedRing.inverse_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `NormedRing`。
形式化陈述：inverse_continuousAt (x : Rˣ) : ContinuousAt inverse (x : R)
参数：x : Rˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `NormedRing.inverse_add_norm_diff_first_order`：inverse_add_norm_diff_firs
t_order (x : Rˣ) : (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖
· 使用定理 `Asymptotics.IsLittleO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' 
: α → E'} {l : Filter…
· 使用定理 `Asymptotics.isLittleO_id_const`：isLittleO_id_const {c : F''} (hc : c != 
0) : (fun x : E'' => x) =o[𝓝 0] fun _x => c
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_iff_norm_sub_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [inst
 : SeminormedAddCommGroup E] {f : α → E} {a : Filter α} {b : E},   Filter.Tendst
o f a (nhds b) ↔ Filter…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Asymptotics.IsLittleO.tendsto_div_nhds_zero`：∀ {α : Type u_1} {𝕜 : Type 
u_15} [inst : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   f =o[l] g → 
Filter.Tendsto (fun x => f x / g …

--- 原说明 ---
The function `Ring.inverse` is continuous at each unit of `R`.
-/
theorem inverse_continuousAt (x : Rˣ) : ContinuousAt inverse (x : R) := by
  have h_is_o : (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹) =o[𝓝 0] (fun _ => 1 : R → ℝ) :=
    (inverse_add_norm_diff_first_order x).trans_isLittleO (isLittleO_id_const one_ne_zero).norm_left
  have h_lim : Tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    exact tendsto_iff_norm_sub_tendsto_zero.mp tendsto_id
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero, inverse_unit]
  simpa [Function.comp_def] using h_is_o.norm_left.tendsto_div_nhds_zero.comp h_lim

end NormedRing

namespace Units

open MulOpposite Filter NormedRing

/-- In a normed ring with summable geometric series, the coercion from `Rˣ` (equipped with the
induced topology from the embedding in `R × R`) to `R` is an open embedding. -/
/-
**Units.isOpenEmbedding_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：isOpenEmbedding_val : IsOpenEmbedding (val : Rˣ -> R) where toIsEmbedding
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Units.isEmbedding_val_mk'`：isEmbedding_val_mk' {M : Type*} [Monoid M] [T
opologicalSpace M] {f : M -> M} (hc : ContinuousOn f {x : M | IsUnit x}) (hf : f
orall u : Mˣ, f…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `NormedRing.inverse_continuousAt`：inverse_continuousAt (x : Rˣ) : Continu
ousAt inverse (x : R)
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `Units.isOpen`：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSer
ies R], IsOpen {x | IsUnit x}

--- 原说明 ---
In a normed ring with summable geometric series, the coercion from `Rˣ` (equippe
d with the
induced topology from the embedding in `R × R`) to `R` is an open embedding.
-/
theorem isOpenEmbedding_val : IsOpenEmbedding (val : Rˣ → R) where
  toIsEmbedding := isEmbedding_val_mk'
    (fun _ ⟨u, hu⟩ ↦ hu ▸ (inverse_continuousAt u).continuousWithinAt) Ring.inverse_unit
  isOpen_range := Units.isOpen

/-- In a normed ring with summable geometric series, the coercion from `Rˣ` (equipped with the
induced topology from the embedding in `R × R`) to `R` is an open map. -/
/-
**Units.isOpenMap_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：isOpenMap_val : IsOpenMap (val : Rˣ -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `Units.isOpenEmbedding_val`：isOpenEmbedding_val : IsOpenEmbedding (val : 
Rˣ -> R) where toIsEmbedding

--- 原说明 ---
In a normed ring with summable geometric series, the coercion from `Rˣ` (equippe
d with the
induced topology from the embedding in `R × R`) to `R` is an open map.
-/
theorem isOpenMap_val : IsOpenMap (val : Rˣ → R) :=
  isOpenEmbedding_val.isOpenMap

end Units

namespace Ideal

/-- An ideal which contains an element within `1` of `1 : R` is the unit ideal. -/
/-
**Ideal.eq_top_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_top_of_norm_lt_one (I : Ideal R) {x : R} (hxI : x in I) (hx : ‖1 - x‖ <
 1) : I = ⊤
参数：I : Ideal R；hxI : x in I；hx : ‖1 - x‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Units.val_oneSub`：∀ {R : Type u_4} [inst : NormedRing R] [inst_1 : HasSu
mmableGeomSeries R] (t : R) (h : ‖t‖ < 1),   ↑(Units.oneSub t h) = 1 - t
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I

--- 原说明 ---
An ideal which contains an element within `1` of `1 : R` is the unit ideal.
-/
theorem eq_top_of_norm_lt_one (I : Ideal R) {x : R} (hxI : x ∈ I) (hx : ‖1 - x‖ < 1) : I = ⊤ :=
  let u := Units.oneSub (1 - x) hx
  I.eq_top_iff_one.mpr <| by
    simpa only [show u.inv * x = 1 by simp [u]] using I.mul_mem_left u.inv hxI

/-- The `Ideal.closure` of a proper ideal in a normed ring with summable
geometric series is proper. -/
/-
**Ideal.closure_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：closure_ne_top (I : Ideal R) (hI : I != ⊤) : I.closure != ⊤
参数：I : Ideal R；hI : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `coe_subset_nonunits`：coe_subset_nonunits [Semiring α] {I : Ideal α} (h :
 I != ⊤) : (I : Set α) subseteq nonunits α
· 使用定理 `nonunits.isClosed`：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGe
omSeries R], IsClosed (nonunits R)
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `one_notMem_nonunits`：one_notMem_nonunits [Monoid α] : (1 : α) ∉ nonunits
 α

--- 原说明 ---
The `Ideal.closure` of a proper ideal in a normed ring with summable
geometric series is proper.
-/
theorem closure_ne_top (I : Ideal R) (hI : I ≠ ⊤) : I.closure ≠ ⊤ := by
  have h := closure_minimal (coe_subset_nonunits hI) nonunits.isClosed
  simpa only [I.closure.eq_top_iff_one, Ne] using! mt (@h 1) one_notMem_nonunits

/-- The `Ideal.closure` of a maximal ideal in a normed ring with summable
geometric series is the ideal itself. -/
/-
**Ideal.IsMaximal.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSeries R] {I : Idea
l R}, I.IsMaximal → I.closure = I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.closure_ne_top`：closure_ne_top (I : Ideal R) (hI : I != ⊤) : I.clo
sure != ⊤
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
The `Ideal.closure` of a maximal ideal in a normed ring with summable
geometric series is the ideal itself.
-/
theorem IsMaximal.closure_eq {I : Ideal R} (hI : I.IsMaximal) : I.closure = I :=
  (hI.eq_of_le (I.closure_ne_top hI.ne_top) subset_closure).symm

/-- Maximal ideals in normed rings with summable geometric series are closed. -/
/-
**Ideal.IsMaximal.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSeries R] {I : Idea
l R} [hI : I.IsMaximal], IsClosed ↑I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Ideal.IsMaximal.closure_eq`：∀ {R : Type u_1} [inst : NormedRing R] [HasS
ummableGeomSeries R] {I : Ideal R}, I.IsMaximal → I.closure = I

--- 原说明 ---
Maximal ideals in normed rings with summable geometric series are closed.
-/
instance IsMaximal.isClosed {I : Ideal R} [hI : I.IsMaximal] : IsClosed (I : Set R) :=
  isClosed_of_closure_subset <| Eq.subset <| congr_arg ((↑) : Ideal R → Set R) hI.closure_eq

end Ideal

