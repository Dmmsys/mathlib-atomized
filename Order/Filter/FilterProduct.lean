/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Order.Filter.Ring
public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `Order.Filter.Germ`.

## Tags

ultrafilter, ultraproduct
-/

@[expose] public section


universe u v

variable {α : Type u} {β : Type v} {φ : Ultrafilter α}

namespace Filter

local notation3 "forall* "(...)", "r:(scoped p => Filter.Eventually p (Ultrafilter.toFilter φ)) => r

namespace Germ

open Ultrafilter

local notation "β*" => Germ (φ : Filter α) β

/--
Instance `instGroupWithZero` / 实例 `instGroupWithZero`

English:
instance instGroupWithZero
  signature: [GroupWithZero β]
  body: instDivInvMonoid
  __ := instMonoidWithZero
mul_inv_cancel f := inductionOn f fun f hf => coe_eq.2 (φ.em fun y => f y = 0).elim
    (fun H => (hf <| coe_eq.2 H).elim) fun H => H.mono fun _ => mul_inv_cancel₀
inv_zero := coe_eq.2 by simp only [Function.comp_def, inv_zero, EventuallyEq.rfl]

中文:
实例 instGroupWithZero
  签名: [带零群 β]
  定义体: instDivInvMonoid
  __ := instMonoidWithZero
mul_inv_cancel f := inductionOn f fun f hf => coe_eq.2 (φ.em fun y => f y = 0).elim
    (fun H => (hf <| coe_eq.2 H).elim) fun H => H.mono fun _ => mul_inv_cancel₀
inv_zero := coe_eq.2 by simp only [Function.comp_def, inv_zero, EventuallyEq.rfl]

Depends on / 依赖: instDivInvMonoid
-/
instance instGroupWithZero [GroupWithZero β] : GroupWithZero β* where
  __ := instDivInvMonoid
  __ := instMonoidWithZero
mul_inv_cancel f := inductionOn f fun f hf => coe_eq.2 (φ.em fun y => f y = 0).elim
    (fun H => (hf <| coe_eq.2 H).elim) fun H => H.mono fun _ => mul_inv_cancel₀
inv_zero := coe_eq.2 by simp only [Function.comp_def, inv_zero, EventuallyEq.rfl]

/--
Instance `instDivisionSemiring` / 实例 `instDivisionSemiring`

English:
instance instDivisionSemiring
  signature: [DivisionSemiring β]
  body: instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

中文:
实例 instDivisionSemiring
  签名: [除半环 β]
  定义体: instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

Depends on / 依赖: instSemiring
-/
instance instDivisionSemiring [DivisionSemiring β] : DivisionSemiring β* where
  toSemiring := instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

/--
Instance `instDivisionRing` / 实例 `instDivisionRing`

English:
instance instDivisionRing
  signature: [DivisionRing β]
  body: instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
实例 instDivisionRing
  签名: [除环 β]
  定义体: instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl

Depends on / 依赖: instRing
-/
instance instDivisionRing [DivisionRing β] : DivisionRing β* where
  __ := instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl

/--
Instance `instSemifield` / 实例 `instSemifield`

English:
instance instSemifield
  signature: [Semifield β]
  body: instCommSemiring
  __ := instDivisionSemiring

中文:
实例 instSemifield
  签名: [半域 β]
  定义体: instCommSemiring
  __ := instDivisionSemiring

Depends on / 依赖: instCommSemiring
-/
instance instSemifield [Semifield β] : Semifield β* where
  __ := instCommSemiring
  __ := instDivisionSemiring

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: [Field β]
  body: instCommRing
  __ := instDivisionRing

中文:
实例 instField
  签名: [域 β]
  定义体: instCommRing
  __ := instDivisionRing

Depends on / 依赖: instCommRing
-/
instance instField [Field β] : Field β* where
  __ := instCommRing
  __ := instDivisionRing

/--
theorem `coe_lt` / 定理 `coe_lt`

English:
theorem coe_lt
  given: [Preorder β] {f g : α -> β}
  statement: (f : β*) < g ↔ forall* x, f x < g x
  proof: by
  simp only [lt_iff_le_not_ge, eventually_and, coe_le, eventually_not, EventuallyLE]

中文:
定理 coe_lt
  条件: [预序 β] {f g : α -> β}
  结论: (f : β*) < g ↔ 对任意* x, f x < g x
  证明: by
  simp only [lt_iff_le_not_ge, eventually_and, coe_le, eventually_not, EventuallyLE]

Depends on / 依赖: EventuallyLE, coe_le, eventually_and, eventually_not, lt_iff_le_not_ge
-/
theorem coe_lt [Preorder β] {f g : α -> β} : (f : β*) < g ↔ forall* x, f x < g x := by
  simp only [lt_iff_le_not_ge, eventually_and, coe_le, eventually_not, EventuallyLE]

/--
theorem `coe_pos` / 定理 `coe_pos`

English:
theorem coe_pos
  given: [Preorder β] [Zero β] {f : α -> β}
  statement: 0 < (f : β*) ↔ forall* x, 0 < f x
  proof: coe_lt

中文:
定理 coe_pos
  条件: [预序 β] [零 β] {f : α -> β}
  结论: 0 < (f : β*) ↔ 对任意* x, 0 < f x
  证明: coe_lt

Depends on / 依赖: coe_lt
-/
theorem coe_pos [Preorder β] [Zero β] {f : α -> β} : 0 < (f : β*) ↔ forall* x, 0 < f x :=
  coe_lt

/--
theorem `const_lt` / 定理 `const_lt`

English:
theorem const_lt
  given: [Preorder β] {x y : β}
  statement: x < y -> (↑x : β*) < ↑y
  proof: coe_lt.mpr ∘ liftRel_const

@[simp, norm_cast]

中文:
定理 const_lt
  条件: [预序 β] {x y : β}
  结论: x < y -> (↑x : β*) < ↑y
  证明: coe_lt.mpr ∘ liftRel_const

@[simp, norm_cast]

Depends on / 依赖: coe_lt, coe_lt.mpr, liftRel_const
-/
theorem const_lt [Preorder β] {x y : β} : x < y -> (↑x : β*) < ↑y :=
  coe_lt.mpr ∘ liftRel_const

@[simp, norm_cast]
/--
theorem `const_lt_iff` / 定理 `const_lt_iff`

English:
theorem const_lt_iff
  given: [Preorder β] {x y : β}
  statement: (↑x : β*) < ↑y ↔ x < y
  proof: coe_lt.trans liftRel_const_iff

中文:
定理 const_lt_iff
  条件: [预序 β] {x y : β}
  结论: (↑x : β*) < ↑y ↔ x < y
  证明: coe_lt.trans liftRel_const_iff

Depends on / 依赖: coe_lt, coe_lt.trans, liftRel_const_iff
-/
theorem const_lt_iff [Preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
  coe_lt.trans liftRel_const_iff

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: [Preorder β]
  statement: ((· < ·) : β* -> β* -> Prop) = LiftRel (· < ·)
  proof: by
  ext ⟨f⟩ ⟨g⟩
  exact coe_lt

中文:
定理 lt_def
  条件: [预序 β]
  结论: ((· < ·) : β* -> β* -> 命题) = LiftRel (· < ·)
  证明: by
  ext ⟨f⟩ ⟨g⟩
  exact coe_lt

Depends on / 依赖: coe_lt
-/
theorem lt_def [Preorder β] : ((· < ·) : β* -> β* -> Prop) = LiftRel (· < ·) := by
  ext ⟨f⟩ ⟨g⟩
  exact coe_lt

/--
Instance `total` / 实例 `total`

English:
instance total
  signature: [LE β] [@Std.Total β (· <= ·)]
  body: ⟨fun f g =>
inductionOn₂ f g fun _f _g => eventually_or.1 Eventually.of_forall fun _x => total_of _ _ _⟩

中文:
实例 total
  签名: [LE β] [@Std.全 β (· <= ·)]
  定义体: ⟨fun f g =>
inductionOn₂ f g fun _f _g => eventually_or.1 Eventually.of_forall fun _x => total_of _ _ _⟩

Depends on / 依赖: Eventually, Eventually.of_forall, eventually_or, of_forall, total_of
-/
instance total [LE β] [@Std.Total β (· <= ·)] : @Std.Total β* (· <= ·) :=
  ⟨fun f g =>
inductionOn₂ f g fun _f _g => eventually_or.1 Eventually.of_forall fun _x => total_of _ _ _⟩

open scoped Classical in
/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: [LinearOrder β]
  body: Lattice.toLinearOrder _

中文:
实例 instLinearOrder
  签名: [线性序 β]
  定义体: Lattice.toLinearOrder _

Depends on / 依赖: Lattice, Lattice.toLinearOrder, toLinearOrder
-/
noncomputable instance instLinearOrder [LinearOrder β] : LinearOrder β* :=
  Lattice.toLinearOrder _

/--
Instance `instIsStrictOrderedRing` / 实例 `instIsStrictOrderedRing`

English:
instance instIsStrictOrderedRing
  signature: [Semiring β] [PartialOrder β] [IsStrictOrderedRing β]
  body: inductionOn x fun _f hf y z => inductionOn₂ y z fun _g _h hgh =>
coe_lt.2 (coe_lt.1 hf).mp (coe_lt.1 hgh).mono fun _a => mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right x := inductionOn x fun _f hf y z => inductionOn₂ y z fun _g _h hgh =>
coe_lt.2 (coe_lt.1 hf).mp (coe_lt.1 hgh).mono fun _a => mul_lt_mul_of_pos_right

中文:
实例 instIsStrictOrderedRing
  签名: [半环 β] [偏序 β] [是StrictOrdered环 β]
  定义体: inductionOn x fun _f hf y z => inductionOn₂ y z fun _g _h hgh =>
coe_lt.2 (coe_lt.1 hf).mp (coe_lt.1 hgh).mono fun _a => mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right x := inductionOn x fun _f hf y z => inductionOn₂ y z fun _g _h hgh =>
coe_lt.2 (coe_lt.1 hf).mp (coe_lt.1 hgh).mono fun _a => mul_lt_mul_of_pos_right

Depends on / 依赖: inductionOn
-/
instance instIsStrictOrderedRing [Semiring β] [PartialOrder β] [IsStrictOrderedRing β] :
    IsStrictOrderedRing β* where
  mul_lt_mul_of_pos_left x := inductionOn x fun _f hf y z => inductionOn₂ y z fun _g _h hgh =>
coe_lt.2 (coe_lt.1 hf).mp (coe_lt.1 hgh).mono fun _a => mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right x := inductionOn x fun _f hf y z => inductionOn₂ y z fun _g _h hgh =>
coe_lt.2 (coe_lt.1 hf).mp (coe_lt.1 hgh).mono fun _a => mul_lt_mul_of_pos_right

/--
theorem `max_def` / 定理 `max_def`

English:
theorem max_def
  given: [LinearOrder β] (x y : β*)
  statement: max x y = map₂ max x y
  proof: inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [max_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_right hi).symm
    · rw [max_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_left hi).symm

中文:
定理 max_def
  条件: [线性序 β] (x y : β*)
  结论: 最大值 x y = map₂ 最大值 x y
  证明: inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [max_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_right hi).symm
    · rw [max_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_left hi).symm

Depends on / 依赖: coe_eq, h.mono, le_total, max_eq_left, max_eq_right
-/
theorem max_def [LinearOrder β] (x y : β*) : max x y = map₂ max x y :=
  inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [max_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_right hi).symm
    · rw [max_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_left hi).symm

/--
theorem `min_def` / 定理 `min_def`

English:
theorem min_def
  given: [K : LinearOrder β] (x y : β*)
  statement: min x y = map₂ min x y
  proof: inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [min_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_left hi).symm
    · rw [min_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_right hi).symm

中文:
定理 min_def
  条件: [K : 线性序 β] (x y : β*)
  结论: 最小值 x y = map₂ 最小值 x y
  证明: inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [min_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_left hi).symm
    · rw [min_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_right hi).symm

Depends on / 依赖: coe_eq, h.mono, le_total, min_eq_left, min_eq_right
-/
theorem min_def [K : LinearOrder β] (x y : β*) : min x y = map₂ min x y :=
  inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [min_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_left hi).symm
    · rw [min_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_right hi).symm

/--
theorem `abs_def` / 定理 `abs_def`

English:
theorem abs_def
  given: [AddCommGroup β] [LinearOrder β] (x : β*)
  proof: inductionOn x fun _a => rfl

@[simp]

中文:
定理 abs_def
  条件: [加法交换群 β] [线性序 β] (x : β*)
  证明: inductionOn x fun _a => rfl

@[simp]

Depends on / 依赖: inductionOn
-/
theorem abs_def [AddCommGroup β] [LinearOrder β] (x : β*) :
    |x| = map abs x :=
  inductionOn x fun _a => rfl

@[simp]
/--
theorem `const_max` / 定理 `const_max`

English:
theorem const_max
  given: [LinearOrder β] (x y : β)
  statement: (↑(max x y : β) : β*) = max ↑x ↑y
  proof: by
  rw [max_def]; rw [map₂_const]

@[simp]

中文:
定理 const_max
  条件: [线性序 β] (x y : β)
  结论: (↑(最大值 x y : β) : β*) = 最大值 ↑x ↑y
  证明: by
  rw [max_def]; rw [map₂_const]

@[simp]

Depends on / 依赖: max_def
-/
theorem const_max [LinearOrder β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y := by
  rw [max_def]; rw [map₂_const]

@[simp]
/--
theorem `const_min` / 定理 `const_min`

English:
theorem const_min
  given: [LinearOrder β] (x y : β)
  statement: (↑(min x y : β) : β*) = min ↑x ↑y
  proof: by
  rw [min_def]; rw [map₂_const]

@[simp]

中文:
定理 const_min
  条件: [线性序 β] (x y : β)
  结论: (↑(最小值 x y : β) : β*) = 最小值 ↑x ↑y
  证明: by
  rw [min_def]; rw [map₂_const]

@[simp]

Depends on / 依赖: min_def
-/
theorem const_min [LinearOrder β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y := by
  rw [min_def]; rw [map₂_const]

@[simp]
/--
theorem `const_abs` / 定理 `const_abs`

English:
theorem const_abs
  given: [AddCommGroup β] [LinearOrder β] (x : β)
  proof: by
  rw [abs_def]; rw [map_const]

中文:
定理 const_abs
  条件: [加法交换群 β] [线性序 β] (x : β)
  证明: by
  rw [abs_def]; rw [map_const]

Depends on / 依赖: abs_def, map_const
-/
theorem const_abs [AddCommGroup β] [LinearOrder β] (x : β) :
    (↑|x| : β*) = |↑x| := by
  rw [abs_def]; rw [map_const]

end Germ

end Filter
