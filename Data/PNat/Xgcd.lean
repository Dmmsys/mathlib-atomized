/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Data.PNat.Prime

/-!
# Euclidean algorithm for ℕ

This file sets up a version of the Euclidean algorithm that only works with natural numbers.
Given `0 < a, b`, it computes the unique `(w, x, y, z, d)` such that the following identities hold:
* `a = (w + x) d`
* `b = (y + z) d`
* `w * z = x * y + 1`

`d` is then the gcd of `a` and `b`, and `a' := a / d = w + x` and `b' := b / d = y + z` are coprime.

This story is closely related to the structure of SL₂(ℕ) (as a free monoid on two generators) and
the theory of continued fractions.

## Main declarations

* `XgcdType`: Helper type in defining the gcd. Encapsulates `(wp, x, y, zp, ap, bp)`. where `wp`
  `zp`, `ap`, `bp` are the variables getting changed through the algorithm.
* `IsSpecial`: States `wp * zp = x * y + 1`
* `IsReduced`: States `ap = a ∧ bp = b`

## Notes

See `Nat.Xgcd` for a very similar algorithm allowing values in `ℤ`.
-/

@[expose] public section


open Nat

namespace PNat

/--
Definition of `XgcdType` / `XgcdType` 的定义

English:
structure XgcdType
  parameters: where
  axioms and operations (6):
    - wp : Nat
    - x : Nat
    - y : Nat
    - zp : Nat
    - ap : Nat
    - bp : Nat

中文:
结构 XgcdType
  参数: where
  公理与运算 (6 个):
    - wp : 自然数
    - x : 自然数
    - y : 自然数
    - zp : 自然数
    - ap : 自然数
    - bp : 自然数
-/
structure XgcdType where
  /-- `wp` is a variable which changes through the algorithm. -/
  wp : Nat
  /-- `x` satisfies `a / d = w + x` at the final step. -/
  x : Nat
  /-- `y` satisfies `b / d = z + y` at the final step. -/
  y : Nat
  /-- `zp` is a variable which changes through the algorithm. -/
  zp : Nat
  /-- `ap` is a variable which changes through the algorithm. -/
  ap : Nat
  /-- `bp` is a variable which changes through the algorithm. -/
  bp : Nat
  deriving Inhabited

namespace XgcdType

variable (u : XgcdType)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SizeOf XgcdType
  body: ⟨fun u => u.bp⟩

中文:
实例 :
  签名: SizeOf XgcdType
  定义体: ⟨fun u => u.bp⟩

Depends on / 依赖: u.bp
-/
instance : SizeOf XgcdType :=
  ⟨fun u => u.bp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Repr XgcdType

中文:
实例 :
  签名: Repr XgcdType
-/
instance : Repr XgcdType where
  reprPrec
  | g, _ => s!"[[[{repr (g.wp + 1)}, {repr g.x}], \
                 [{repr g.y}, {repr (g.zp + 1)}]], \
                [{repr (g.ap + 1)}, {repr (g.bp + 1)}]]"

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (w : Nat+) (x : Nat) (y : Nat) (z : Nat+) (a : Nat+) (b : Nat+)
  body: mk w.val.pred x y z.val.pred a.val.pred b.val.pred

中文:
定义 mk'
  签名: (w : 自然数+) (x : 自然数) (y : 自然数) (z : 自然数+) (a : 自然数+) (b : 自然数+)
  定义体: mk w.val.pred x y z.val.pred a.val.pred b.val.pred

Depends on / 依赖: a.val.pred, b.val.pred, w.val.pred, z.val.pred
-/
def mk' (w : Nat+) (x : Nat) (y : Nat) (z : Nat+) (a : Nat+) (b : Nat+) : XgcdType :=
  mk w.val.pred x y z.val.pred a.val.pred b.val.pred

/--
Definition of `w` / `w` 的定义

English:
definition w
  signature: : Nat+
  body: succPNat u.wp

中文:
定义 w
  签名: : 自然数+
  定义体: succPNat u.wp

Depends on / 依赖: succPNat, u.wp
-/
def w : Nat+ :=
  succPNat u.wp

/--
Definition of `z` / `z` 的定义

English:
definition z
  signature: : Nat+
  body: succPNat u.zp

中文:
定义 z
  签名: : 自然数+
  定义体: succPNat u.zp

Depends on / 依赖: succPNat, u.zp
-/
def z : Nat+ :=
  succPNat u.zp

/--
Definition of `a` / `a` 的定义

English:
definition a
  signature: : Nat+
  body: succPNat u.ap

中文:
定义 a
  签名: : 自然数+
  定义体: succPNat u.ap

Depends on / 依赖: succPNat, u.ap
-/
def a : Nat+ :=
  succPNat u.ap

/--
Definition of `b` / `b` 的定义

English:
definition b
  signature: : Nat+
  body: succPNat u.bp

中文:
定义 b
  签名: : 自然数+
  定义体: succPNat u.bp

Depends on / 依赖: succPNat, u.bp
-/
def b : Nat+ :=
  succPNat u.bp

/--
Definition of `r` / `r` 的定义

English:
definition r
  signature: : Nat
  body: (u.ap + 1) % (u.bp + 1)

中文:
定义 r
  签名: : 自然数
  定义体: (u.ap + 1) % (u.bp + 1)

Depends on / 依赖: u.ap, u.bp
-/
def r : Nat :=
  (u.ap + 1) % (u.bp + 1)

/--
Definition of `q` / `q` 的定义

English:
definition q
  signature: : Nat
  body: (u.ap + 1) / (u.bp + 1)

中文:
定义 q
  签名: : 自然数
  定义体: (u.ap + 1) / (u.bp + 1)

Depends on / 依赖: u.ap, u.bp
-/
def q : Nat :=
  (u.ap + 1) / (u.bp + 1)

/--
Definition of `qp` / `qp` 的定义

English:
definition qp
  signature: : Nat
  body: u.q - 1

中文:
定义 qp
  签名: : 自然数
  定义体: u.q - 1
-/
def qp : Nat :=
  u.q - 1

/--
Definition of `vp` / `vp` 的定义

English:
definition vp
  signature: : Nat × Nat
  body: ⟨u.wp + u.x + u.ap + u.wp * u.ap + u.x * u.bp, u.y + u.zp + u.bp + u.y * u.ap + u.zp * u.bp⟩

中文:
定义 vp
  签名: : 自然数 × 自然数
  定义体: ⟨u.wp + u.x + u.ap + u.wp * u.ap + u.x * u.bp, u.y + u.zp + u.bp + u.y * u.ap + u.zp * u.bp⟩

Depends on / 依赖: u.ap, u.bp, u.wp, u.zp
-/
def vp : Nat × Nat :=
  ⟨u.wp + u.x + u.ap + u.wp * u.ap + u.x * u.bp, u.y + u.zp + u.bp + u.y * u.ap + u.zp * u.bp⟩

/--
Definition of `v` / `v` 的定义

English:
definition v
  signature: : Nat × Nat
  body: ⟨u.w * u.a + u.x * u.b, u.y * u.a + u.z * u.b⟩

中文:
定义 v
  签名: : 自然数 × 自然数
  定义体: ⟨u.w * u.a + u.x * u.b, u.y * u.a + u.z * u.b⟩
-/
def v : Nat × Nat :=
  ⟨u.w * u.a + u.x * u.b, u.y * u.a + u.z * u.b⟩

/--
Definition of `succ₂` / `succ₂` 的定义

English:
definition succ₂
  signature: (t : Nat × Nat)
  body: ⟨t.1.succ, t.2.succ⟩

中文:
定义 succ₂
  签名: (t : 自然数 × 自然数)
  定义体: ⟨t.1.succ, t.2.succ⟩
-/
def succ₂ (t : Nat × Nat) : Nat × Nat :=
  ⟨t.1.succ, t.2.succ⟩

/--
theorem `v_eq_succ_vp` / 定理 `v_eq_succ_vp`

English:
theorem v_eq_succ_vp
  statement: u.v = succ₂ u.vp
  proof: by
  ext <;> dsimp [v, vp, w, z, a, b, succ₂] <;> ring_nf

中文:
定理 v_eq_succ_vp
  结论: u.v = succ₂ u.vp
  证明: by
  ext <;> dsimp [v, vp, w, z, a, b, succ₂] <;> ring_nf

Depends on / 依赖: ring_nf
-/
theorem v_eq_succ_vp : u.v = succ₂ u.vp := by
  ext <;> dsimp [v, vp, w, z, a, b, succ₂] <;> ring_nf

/--
Definition of `IsSpecial` / `IsSpecial` 的定义

English:
definition IsSpecial
  signature: : Prop
  body: u.wp + u.zp + u.wp * u.zp = u.x * u.y

中文:
定义 IsSpecial
  签名: : 命题
  定义体: u.wp + u.zp + u.wp * u.zp = u.x * u.y

Depends on / 依赖: u.wp, u.zp
-/
def IsSpecial : Prop :=
  u.wp + u.zp + u.wp * u.zp = u.x * u.y

/--
Definition of `IsSpecial'` / `IsSpecial'` 的定义

English:
definition IsSpecial'
  signature: : Prop
  body: u.w * u.z = succPNat (u.x * u.y)

中文:
定义 IsSpecial'
  签名: : 命题
  定义体: u.w * u.z = succPNat (u.x * u.y)

Depends on / 依赖: succPNat
-/
def IsSpecial' : Prop :=
  u.w * u.z = succPNat (u.x * u.y)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isSpecial_iff` / 定理 `isSpecial_iff`

English:
theorem isSpecial_iff
  statement: u.IsSpecial ↔ u.IsSpecial'
  proof: by
  dsimp [IsSpecial, IsSpecial']
  let ⟨wp, x, y, zp, ap, bp⟩ := u
  constructor <;> intro h <;> simp only [w, succPNat, succ_eq_add_one, z] at * <;>
    simp only [← coe_inj, mul_coe, mk_coe] at *
  · simp_all [← h]; ring
  · simp only [Nat.mul_add, Nat.add_mul, one_mul, mul_one, ← Nat.add_assoc,

中文:
定理 isSpecial_iff
  结论: u.IsSpecial ↔ u.IsSpecial'
  证明: by
  dsimp [IsSpecial, IsSpecial']
  let ⟨wp, x, y, zp, ap, bp⟩ := u
  constructor <;> intro h <;> simp only [w, succPNat, succ_eq_add_one, z] at * <;>
    simp only [← coe_inj, mul_coe, mk_coe] at *
  · simp_all [← h]; ring
  · simp only [Nat.mul_add, Nat.add_mul, one_mul, mul_one, ← Nat.add_assoc,

Depends on / 依赖: IsSpecial, Nat.add_assoc, Nat.add_mul, Nat.add_right_cancel_iff, Nat.mul_add, add_assoc, add_mul, add_right_cancel_iff, coe_inj, mk_coe, mul_add, mul_coe, mul_one, one_mul, succPNat, succ_eq_add_one
-/
theorem isSpecial_iff : u.IsSpecial ↔ u.IsSpecial' := by
  dsimp [IsSpecial, IsSpecial']
  let ⟨wp, x, y, zp, ap, bp⟩ := u
  constructor <;> intro h <;> simp only [w, succPNat, succ_eq_add_one, z] at * <;>
    simp only [← coe_inj, mul_coe, mk_coe] at *
  · simp_all [← h]; ring
  · simp only [Nat.mul_add, Nat.add_mul, one_mul, mul_one, ← Nat.add_assoc,
      Nat.add_right_cancel_iff] at h
    rw [← h]; ring

/--
Definition of `IsReduced` / `IsReduced` 的定义

English:
definition IsReduced
  signature: : Prop
  body: u.ap = u.bp

中文:
定义 是既约
  签名: : 命题
  定义体: u.ap = u.bp

Depends on / 依赖: u.ap, u.bp
-/
def IsReduced : Prop :=
  u.ap = u.bp

/--
Definition of `IsReduced'` / `IsReduced'` 的定义

English:
definition IsReduced'
  signature: : Prop
  body: u.a = u.b

中文:
定义 是既约'
  签名: : 命题
  定义体: u.a = u.b
-/
def IsReduced' : Prop :=
  u.a = u.b

/--
theorem `isReduced_iff` / 定理 `isReduced_iff`

English:
theorem isReduced_iff
  statement: u.IsReduced ↔ u.IsReduced'
  proof: succPNat_inj.symm

中文:
定理 isReduced_iff
  结论: u.是既约 ↔ u.是既约'
  证明: succPNat_inj.symm

Depends on / 依赖: succPNat_inj, succPNat_inj.symm
-/
theorem isReduced_iff : u.IsReduced ↔ u.IsReduced' :=
  succPNat_inj.symm

/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: : XgcdType where
  body: u.zp
  x := u.y
  y := u.x
  zp := u.wp
  ap := u.bp
  bp := u.ap

@[simp]

中文:
定义 flip
  签名: : XgcdType where
  定义体: u.zp
  x := u.y
  y := u.x
  zp := u.wp
  ap := u.bp
  bp := u.ap

@[simp]

Depends on / 依赖: u.zp
-/
def flip : XgcdType where
  wp := u.zp
  x := u.y
  y := u.x
  zp := u.wp
  ap := u.bp
  bp := u.ap

@[simp]
/--
theorem `flip_w` / 定理 `flip_w`

English:
theorem flip_w
  statement: (flip u).w = u.z
  proof: rfl

@[simp]

中文:
定理 flip_w
  结论: (flip u).w = u.z
  证明: rfl

@[simp]
-/
theorem flip_w : (flip u).w = u.z :=
  rfl

@[simp]
/--
theorem `flip_x` / 定理 `flip_x`

English:
theorem flip_x
  statement: (flip u).x = u.y
  proof: rfl

@[simp]

中文:
定理 flip_x
  结论: (flip u).x = u.y
  证明: rfl

@[simp]
-/
theorem flip_x : (flip u).x = u.y :=
  rfl

@[simp]
/--
theorem `flip_y` / 定理 `flip_y`

English:
theorem flip_y
  statement: (flip u).y = u.x
  proof: rfl

@[simp]

中文:
定理 flip_y
  结论: (flip u).y = u.x
  证明: rfl

@[simp]
-/
theorem flip_y : (flip u).y = u.x :=
  rfl

@[simp]
/--
theorem `flip_z` / 定理 `flip_z`

English:
theorem flip_z
  statement: (flip u).z = u.w
  proof: rfl

@[simp]

中文:
定理 flip_z
  结论: (flip u).z = u.w
  证明: rfl

@[simp]
-/
theorem flip_z : (flip u).z = u.w :=
  rfl

@[simp]
/--
theorem `flip_a` / 定理 `flip_a`

English:
theorem flip_a
  statement: (flip u).a = u.b
  proof: rfl

@[simp]

中文:
定理 flip_a
  结论: (flip u).a = u.b
  证明: rfl

@[simp]
-/
theorem flip_a : (flip u).a = u.b :=
  rfl

@[simp]
/--
theorem `flip_b` / 定理 `flip_b`

English:
theorem flip_b
  statement: (flip u).b = u.a
  proof: rfl

中文:
定理 flip_b
  结论: (flip u).b = u.a
  证明: rfl
-/
theorem flip_b : (flip u).b = u.a :=
  rfl

/--
theorem `flip_isReduced` / 定理 `flip_isReduced`

English:
theorem flip_isReduced
  statement: (flip u).IsReduced ↔ u.IsReduced
  proof: by
  dsimp [IsReduced, flip]
  constructor <;> intro h <;> exact h.symm

中文:
定理 flip_isReduced
  结论: (flip u).是既约 ↔ u.是既约
  证明: by
  dsimp [IsReduced, flip]
  constructor <;> intro h <;> exact h.symm

Depends on / 依赖: IsReduced, h.symm
-/
theorem flip_isReduced : (flip u).IsReduced ↔ u.IsReduced := by
  dsimp [IsReduced, flip]
  constructor <;> intro h <;> exact h.symm

/--
theorem `flip_isSpecial` / 定理 `flip_isSpecial`

English:
theorem flip_isSpecial
  statement: (flip u).IsSpecial ↔ u.IsSpecial
  proof: by
  dsimp [IsSpecial, flip]
  rw [mul_comm u.x]; rw [mul_comm u.zp]; rw [add_comm u.zp]

中文:
定理 flip_isSpecial
  结论: (flip u).IsSpecial ↔ u.IsSpecial
  证明: by
  dsimp [IsSpecial, flip]
  rw [mul_comm u.x]; rw [mul_comm u.zp]; rw [add_comm u.zp]

Depends on / 依赖: IsSpecial, add_comm, mul_comm, u.zp
-/
theorem flip_isSpecial : (flip u).IsSpecial ↔ u.IsSpecial := by
  dsimp [IsSpecial, flip]
  rw [mul_comm u.x]; rw [mul_comm u.zp]; rw [add_comm u.zp]

/--
theorem `flip_v` / 定理 `flip_v`

English:
theorem flip_v
  statement: (flip u).v = u.v.swap
  proof: by
  dsimp [v]
  ext
  · simp only
    ring
  · simp only
    ring

中文:
定理 flip_v
  结论: (flip u).v = u.v.swap
  证明: by
  dsimp [v]
  ext
  · simp only
    ring
  · simp only
    ring
-/
theorem flip_v : (flip u).v = u.v.swap := by
  dsimp [v]
  ext
  · simp only
    ring
  · simp only
    ring

/--
theorem `rq_eq` / 定理 `rq_eq`

English:
theorem rq_eq
  statement: u.r + (u.bp + 1) * u.q = u.ap + 1
  proof: Nat.mod_add_div (u.ap + 1) (u.bp + 1)

中文:
定理 rq_eq
  结论: u.r + (u.bp + 1) * u.q = u.ap + 1
  证明: Nat.mod_add_div (u.ap + 1) (u.bp + 1)

Depends on / 依赖: Nat.mod_add_div, mod_add_div, u.ap, u.bp
-/
theorem rq_eq : u.r + (u.bp + 1) * u.q = u.ap + 1 :=
  Nat.mod_add_div (u.ap + 1) (u.bp + 1)

/--
theorem `qp_eq` / 定理 `qp_eq`

English:
theorem qp_eq
  given: (hr : u.r = 0)
  statement: u.q = u.qp + 1
  proof: by
  by_cases hq : u.q = 0
  · let h := u.rq_eq
    rw [hr]; rw [hq]; rw [mul_zero]; rw [add_zero] at h
    cases h
  · exact (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hq)).symm

中文:
定理 qp_eq
  条件: (hr : u.r = 0)
  结论: u.q = u.qp + 1
  证明: by
  by_cases hq : u.q = 0
  · let h := u.rq_eq
    rw [hr]; rw [hq]; rw [mul_zero]; rw [add_zero] at h
    cases h
  · exact (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hq)).symm

Depends on / 依赖: Nat.pos_of_ne_zero, Nat.succ_pred_eq_of_pos, add_zero, mul_zero, pos_of_ne_zero, rq_eq, succ_pred_eq_of_pos, u.rq_eq
-/
theorem qp_eq (hr : u.r = 0) : u.q = u.qp + 1 := by
  by_cases hq : u.q = 0
  · let h := u.rq_eq
    rw [hr]; rw [hq]; rw [mul_zero]; rw [add_zero] at h
    cases h
  · exact (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hq)).symm

/--
Definition of `start` / `start` 的定义

English:
definition start
  signature: (a b : Nat+)
  body: ⟨0, 0, 0, 0, a - 1, b - 1⟩

中文:
定义 start
  签名: (a b : 自然数+)
  定义体: ⟨0, 0, 0, 0, a - 1, b - 1⟩
-/
def start (a b : Nat+) : XgcdType :=
  ⟨0, 0, 0, 0, a - 1, b - 1⟩

/--
theorem `start_isSpecial` / 定理 `start_isSpecial`

English:
theorem start_isSpecial
  given: (a b : Nat+)
  statement: (start a b).IsSpecial
  proof: by
  dsimp [start, IsSpecial]

中文:
定理 start_isSpecial
  条件: (a b : 自然数+)
  结论: (start a b).IsSpecial
  证明: by
  dsimp [start, IsSpecial]

Depends on / 依赖: IsSpecial
-/
theorem start_isSpecial (a b : Nat+) : (start a b).IsSpecial := by
  dsimp [start, IsSpecial]

/--
theorem `start_v` / 定理 `start_v`

English:
theorem start_v
  given: (a b : Nat+)
  statement: (start a b).v = ⟨a, b⟩
  proof: by
  dsimp [start, v, XgcdType.a, XgcdType.b, w, z]
  have := a.pos
  have := b.pos
  #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
  we need to re-enable model-based theory combination in `lia` for this to go through. -/
  lia +mbtc

中文:
定理 start_v
  条件: (a b : 自然数+)
  结论: (start a b).v = ⟨a, b⟩
  证明: by
  dsimp [start, v, XgcdType.a, XgcdType.b, w, z]
  have := a.pos
  have := b.pos
  #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
  we need to re-enable model-based theory combination in `lia` for this to go through. -/
  lia +mbtc

Depends on / 依赖: XgcdType, XgcdType.a, XgcdType.b, a.pos, adaptation_note, b.pos, combination, enable, github, github.com, leanprover, theory, through
-/
theorem start_v (a b : Nat+) : (start a b).v = ⟨a, b⟩ := by
  dsimp [start, v, XgcdType.a, XgcdType.b, w, z]
  have := a.pos
  have := b.pos
  #adaptation_note /-- After https://github.com/leanprover/lean4/pull/13593
  we need to re-enable model-based theory combination in `lia` for this to go through. -/
  lia +mbtc

/--
Definition of `finish` / `finish` 的定义

English:
definition finish
  signature: : XgcdType
  body: XgcdType.mk u.wp ((u.wp + 1) * u.qp + u.x) u.y (u.y * u.qp + u.zp) u.bp u.bp

中文:
定义 finish
  签名: : XgcdType
  定义体: XgcdType.mk u.wp ((u.wp + 1) * u.qp + u.x) u.y (u.y * u.qp + u.zp) u.bp u.bp

Depends on / 依赖: XgcdType, XgcdType.mk, u.bp, u.qp, u.wp, u.zp
-/
def finish : XgcdType :=
  XgcdType.mk u.wp ((u.wp + 1) * u.qp + u.x) u.y (u.y * u.qp + u.zp) u.bp u.bp

/--
theorem `finish_isReduced` / 定理 `finish_isReduced`

English:
theorem finish_isReduced
  statement: u.finish.IsReduced
  proof: by
  dsimp [IsReduced]
  rfl

中文:
定理 finish_isReduced
  结论: u.finish.是既约
  证明: by
  dsimp [IsReduced]
  rfl

Depends on / 依赖: IsReduced
-/
theorem finish_isReduced : u.finish.IsReduced := by
  dsimp [IsReduced]
  rfl

/--
theorem `finish_isSpecial` / 定理 `finish_isSpecial`

English:
theorem finish_isSpecial
  given: (hs : u.IsSpecial)
  statement: u.finish.IsSpecial
  proof: by
  dsimp [IsSpecial, finish] at hs ⊢
  rw [add_mul _ _ u.y]; rw [add_comm _ (u.x * u.y)]; rw [← hs]
  ring

中文:
定理 finish_isSpecial
  条件: (hs : u.IsSpecial)
  结论: u.finish.IsSpecial
  证明: by
  dsimp [IsSpecial, finish] at hs ⊢
  rw [add_mul _ _ u.y]; rw [add_comm _ (u.x * u.y)]; rw [← hs]
  ring

Depends on / 依赖: IsSpecial, add_comm, add_mul, finish
-/
theorem finish_isSpecial (hs : u.IsSpecial) : u.finish.IsSpecial := by
  dsimp [IsSpecial, finish] at hs ⊢
  rw [add_mul _ _ u.y]; rw [add_comm _ (u.x * u.y)]; rw [← hs]
  ring

/--
theorem `finish_v` / 定理 `finish_v`

English:
theorem finish_v
  given: (hr : u.r = 0)
  statement: u.finish.v = u.v
  proof: by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  rw [hr]; rw [zero_add] at ha
  ext
  · change (u.wp + 1) * u.b + ((u.wp + 1) * u.qp + u.x) * u.b = u.w * u.a + u.x * u.b
    have : u.wp + 1 = u.w := rfl
    rw [this]; rw [← ha]; rw [u.qp_eq hr]
    ring
  · change u.y * u.b + (u.y * u.qp + u.z) * u.

中文:
定理 finish_v
  条件: (hr : u.r = 0)
  结论: u.finish.v = u.v
  证明: by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  rw [hr]; rw [zero_add] at ha
  ext
  · change (u.wp + 1) * u.b + ((u.wp + 1) * u.qp + u.x) * u.b = u.w * u.a + u.x * u.b
    have : u.wp + 1 = u.w := rfl
    rw [this]; rw [← ha]; rw [u.qp_eq hr]
    ring
  · change u.y * u.b + (u.y * u.qp + u.z) * u.

Depends on / 依赖: qp_eq, rq_eq, u.qp, u.qp_eq, u.rq_eq, u.wp, zero_add
-/
theorem finish_v (hr : u.r = 0) : u.finish.v = u.v := by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  rw [hr]; rw [zero_add] at ha
  ext
  · change (u.wp + 1) * u.b + ((u.wp + 1) * u.qp + u.x) * u.b = u.w * u.a + u.x * u.b
    have : u.wp + 1 = u.w := rfl
    rw [this]; rw [← ha]; rw [u.qp_eq hr]
    ring
  · change u.y * u.b + (u.y * u.qp + u.z) * u.b = u.y * u.a + u.z * u.b
    rw [← ha]; rw [u.qp_eq hr]
    ring

/--
Definition of `step` / `step` 的定义

English:
definition step
  signature: : XgcdType
  body: XgcdType.mk (u.y * u.q + u.zp) u.y ((u.wp + 1) * u.q + u.x) u.wp u.bp (u.r - 1)

中文:
定义 step
  签名: : XgcdType
  定义体: XgcdType.mk (u.y * u.q + u.zp) u.y ((u.wp + 1) * u.q + u.x) u.wp u.bp (u.r - 1)

Depends on / 依赖: XgcdType, XgcdType.mk, u.bp, u.wp, u.zp
-/
def step : XgcdType :=
  XgcdType.mk (u.y * u.q + u.zp) u.y ((u.wp + 1) * u.q + u.x) u.wp u.bp (u.r - 1)

/--
theorem `step_wf` / 定理 `step_wf`

English:
theorem step_wf
  given: (hr : u.r != 0)
  statement: SizeOf.sizeOf u.step < SizeOf.sizeOf u
  proof: by
  change u.r - 1 < u.bp
  have h₀ : u.r - 1 + 1 = u.r := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hr)
  have h₁ : u.r < u.bp + 1 := Nat.mod_lt (u.ap + 1) u.bp.succ_pos
  rw [← h₀] at h₁
  exact lt_of_succ_lt_succ h₁

中文:
定理 step_wf
  条件: (hr : u.r != 0)
  结论: SizeOf.sizeOf u.step < SizeOf.sizeOf u
  证明: by
  change u.r - 1 < u.bp
  have h₀ : u.r - 1 + 1 = u.r := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hr)
  have h₁ : u.r < u.bp + 1 := Nat.mod_lt (u.ap + 1) u.bp.succ_pos
  rw [← h₀] at h₁
  exact lt_of_succ_lt_succ h₁

Depends on / 依赖: Nat.mod_lt, Nat.pos_of_ne_zero, Nat.succ_pred_eq_of_pos, lt_of_succ_lt_succ, mod_lt, pos_of_ne_zero, succ_pos, succ_pred_eq_of_pos, u.ap, u.bp, u.bp.succ_pos
-/
theorem step_wf (hr : u.r != 0) : SizeOf.sizeOf u.step < SizeOf.sizeOf u := by
  change u.r - 1 < u.bp
  have h₀ : u.r - 1 + 1 = u.r := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hr)
  have h₁ : u.r < u.bp + 1 := Nat.mod_lt (u.ap + 1) u.bp.succ_pos
  rw [← h₀] at h₁
  exact lt_of_succ_lt_succ h₁

/--
theorem `step_isSpecial` / 定理 `step_isSpecial`

English:
theorem step_isSpecial
  given: (hs : u.IsSpecial)
  statement: u.step.IsSpecial
  proof: by
  dsimp [IsSpecial, step] at hs ⊢
  rw [mul_add]; rw [mul_comm u.y u.x]; rw [← hs]
  ring

中文:
定理 step_isSpecial
  条件: (hs : u.IsSpecial)
  结论: u.step.IsSpecial
  证明: by
  dsimp [IsSpecial, step] at hs ⊢
  rw [mul_add]; rw [mul_comm u.y u.x]; rw [← hs]
  ring

Depends on / 依赖: IsSpecial, mul_add, mul_comm
-/
theorem step_isSpecial (hs : u.IsSpecial) : u.step.IsSpecial := by
  dsimp [IsSpecial, step] at hs ⊢
  rw [mul_add]; rw [mul_comm u.y u.x]; rw [← hs]
  ring

/--
theorem `step_v` / 定理 `step_v`

English:
theorem step_v
  given: (hr : u.r != 0)
  statement: u.step.v = u.v.swap
  proof: by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  let hr : u.r - 1 + 1 = u.r := (add_comm _ 1).trans (add_tsub_cancel_of_le (Nat.pos_of_ne_zero hr))
  ext
  · change ((u.y * u.q + u.z) * u.b + u.y * (u.r - 1 + 1) : Nat) = u.y * u.a + u.z * u.b
    rw [← ha]; rw [hr]
    ring
  · change ((u.w * u.q + 

中文:
定理 step_v
  条件: (hr : u.r != 0)
  结论: u.step.v = u.v.swap
  证明: by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  let hr : u.r - 1 + 1 = u.r := (add_comm _ 1).trans (add_tsub_cancel_of_le (Nat.pos_of_ne_zero hr))
  ext
  · change ((u.y * u.q + u.z) * u.b + u.y * (u.r - 1 + 1) : Nat) = u.y * u.a + u.z * u.b
    rw [← ha]; rw [hr]
    ring
  · change ((u.w * u.q + 

Depends on / 依赖: Nat.pos_of_ne_zero, add_comm, add_tsub_cancel_of_le, pos_of_ne_zero, rq_eq, u.rq_eq
-/
theorem step_v (hr : u.r != 0) : u.step.v = u.v.swap := by
  let ha : u.r + u.b * u.q = u.a := u.rq_eq
  let hr : u.r - 1 + 1 = u.r := (add_comm _ 1).trans (add_tsub_cancel_of_le (Nat.pos_of_ne_zero hr))
  ext
  · change ((u.y * u.q + u.z) * u.b + u.y * (u.r - 1 + 1) : Nat) = u.y * u.a + u.z * u.b
    rw [← ha]; rw [hr]
    ring
  · change ((u.w * u.q + u.x) * u.b + u.w * (u.r - 1 + 1) : Nat) = u.w * u.a + u.x * u.b
    rw [← ha]; rw [hr]
    ring

/--
Definition of `reduce` / `reduce` 的定义

English:
definition reduce
  signature: (u : XgcdType)
  body: dite (u.r = 0) (fun _ => u.finish) fun _h =>
    flip (reduce u.step)
decreasing_by apply u.step_wf _h

中文:
定义 reduce
  签名: (u : XgcdType)
  定义体: dite (u.r = 0) (fun _ => u.finish) fun _h =>
    flip (reduce u.step)
decreasing_by apply u.step_wf _h

Depends on / 依赖: decreasing_by, finish, step_wf, u.finish, u.step, u.step_wf
-/
def reduce (u : XgcdType) : XgcdType :=
  dite (u.r = 0) (fun _ => u.finish) fun _h =>
    flip (reduce u.step)
decreasing_by apply u.step_wf _h

/--
theorem `reduce_a` / 定理 `reduce_a`

English:
theorem reduce_a
  given: {u : XgcdType} (h : u.r = 0)
  statement: u.reduce = u.finish
  proof: by
  rw [reduce]
  exact if_pos h

中文:
定理 reduce_a
  条件: {u : XgcdType} (h : u.r = 0)
  结论: u.reduce = u.finish
  证明: by
  rw [reduce]
  exact if_pos h

Depends on / 依赖: if_pos
-/
theorem reduce_a {u : XgcdType} (h : u.r = 0) : u.reduce = u.finish := by
  rw [reduce]
  exact if_pos h

/--
theorem `reduce_b` / 定理 `reduce_b`

English:
theorem reduce_b
  given: {u : XgcdType} (h : u.r != 0)
  statement: u.reduce = u.step.reduce.flip
  proof: by
  rw [reduce]
  exact if_neg h

中文:
定理 reduce_b
  条件: {u : XgcdType} (h : u.r != 0)
  结论: u.reduce = u.step.reduce.flip
  证明: by
  rw [reduce]
  exact if_neg h

Depends on / 依赖: if_neg
-/
theorem reduce_b {u : XgcdType} (h : u.r != 0) : u.reduce = u.step.reduce.flip := by
  rw [reduce]
  exact if_neg h

/--
theorem `reduce_isReduced` / 定理 `reduce_isReduced`

English:
theorem reduce_isReduced
  statement: forall u : XgcdType, u.reduce.IsReduced
  proof: u.step_wf h
      rw [reduce_b h]; rw [flip_isReduced]
      apply reduce_isReduced

中文:
定理 reduce_isReduced
  结论: 对任意 u : XgcdType, u.reduce.是既约
  证明: u.step_wf h
      rw [reduce_b h]; rw [flip_isReduced]
      apply reduce_isReduced

Depends on / 依赖: step_wf, u.step_wf
-/
theorem reduce_isReduced : forall u : XgcdType, u.reduce.IsReduced
  | u =>
    dite (u.r = 0)
      (fun h => by
        rw [reduce_a h]
        exact u.finish_isReduced)
      fun h => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h]; rw [flip_isReduced]
      apply reduce_isReduced

/--
theorem `reduce_isReduced'` / 定理 `reduce_isReduced'`

English:
theorem reduce_isReduced'
  given: (u : XgcdType)
  statement: u.reduce.IsReduced'
  proof: (isReduced_iff _).mp u.reduce_isReduced

中文:
定理 reduce_isReduced'
  条件: (u : XgcdType)
  结论: u.reduce.是既约'
  证明: (isReduced_iff _).mp u.reduce_isReduced

Depends on / 依赖: isReduced_iff, reduce_isReduced, u.reduce_isReduced
-/
theorem reduce_isReduced' (u : XgcdType) : u.reduce.IsReduced' :=
  (isReduced_iff _).mp u.reduce_isReduced

/--
theorem `reduce_isSpecial` / 定理 `reduce_isSpecial`

English:
theorem reduce_isSpecial
  statement: forall u : XgcdType, u.IsSpecial -> u.reduce.IsSpecial
  proof: u.step_wf h
      rw [reduce_b h]
      exact (flip_isSpecial _).mpr (reduce_isSpecial _ (u.step_isSpecial hs))

中文:
定理 reduce_isSpecial
  结论: 对任意 u : XgcdType, u.IsSpecial -> u.reduce.IsSpecial
  证明: u.step_wf h
      rw [reduce_b h]
      exact (flip_isSpecial _).mpr (reduce_isSpecial _ (u.step_isSpecial hs))

Depends on / 依赖: step_wf, u.step_wf
-/
theorem reduce_isSpecial : forall u : XgcdType, u.IsSpecial -> u.reduce.IsSpecial
  | u =>
    dite (u.r = 0)
      (fun h hs => by
        rw [reduce_a h]
        exact u.finish_isSpecial hs)
      fun h hs => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h]
      exact (flip_isSpecial _).mpr (reduce_isSpecial _ (u.step_isSpecial hs))

/--
theorem `reduce_isSpecial'` / 定理 `reduce_isSpecial'`

English:
theorem reduce_isSpecial'
  given: (u : XgcdType) (hs : u.IsSpecial)
  statement: u.reduce.IsSpecial'
  proof: (isSpecial_iff _).mp (u.reduce_isSpecial hs)

中文:
定理 reduce_isSpecial'
  条件: (u : XgcdType) (hs : u.IsSpecial)
  结论: u.reduce.IsSpecial'
  证明: (isSpecial_iff _).mp (u.reduce_isSpecial hs)

Depends on / 依赖: isSpecial_iff, reduce_isSpecial, u.reduce_isSpecial
-/
theorem reduce_isSpecial' (u : XgcdType) (hs : u.IsSpecial) : u.reduce.IsSpecial' :=
  (isSpecial_iff _).mp (u.reduce_isSpecial hs)

/--
theorem `reduce_v` / 定理 `reduce_v`

English:
theorem reduce_v
  statement: forall u : XgcdType, u.reduce.v = u.v
  proof: u.step_wf h
      rw [reduce_b h]; rw [flip_v]; rw [reduce_v (step u)]; rw [step_v u h]; rw [Prod.swap_swap]

中文:
定理 reduce_v
  结论: 对任意 u : XgcdType, u.reduce.v = u.v
  证明: u.step_wf h
      rw [reduce_b h]; rw [flip_v]; rw [reduce_v (step u)]; rw [step_v u h]; rw [Prod.swap_swap]

Depends on / 依赖: step_wf, u.step_wf
-/
theorem reduce_v : forall u : XgcdType, u.reduce.v = u.v
  | u =>
    dite (u.r = 0) (fun h => by rw [reduce_a h, finish_v u h]) fun h => by
      have : SizeOf.sizeOf u.step < SizeOf.sizeOf u := u.step_wf h
      rw [reduce_b h]; rw [flip_v]; rw [reduce_v (step u)]; rw [step_v u h]; rw [Prod.swap_swap]

end XgcdType

section gcd

variable (a b : Nat+)

/--
Definition of `xgcd` / `xgcd` 的定义

English:
definition xgcd
  signature: : XgcdType
  body: (XgcdType.start a b).reduce

中文:
定义 xgcd
  签名: : XgcdType
  定义体: (XgcdType.start a b).reduce

Depends on / 依赖: XgcdType, XgcdType.start
-/
def xgcd : XgcdType :=
  (XgcdType.start a b).reduce

/--
Definition of `gcdD` / `gcdD` 的定义

English:
definition gcdD
  signature: : Nat+
  body: (xgcd a b).a

中文:
定义 gcdD
  签名: : 自然数+
  定义体: (xgcd a b).a
-/
def gcdD : Nat+ :=
  (xgcd a b).a

/--
Definition of `gcdW` / `gcdW` 的定义

English:
definition gcdW
  signature: : Nat+
  body: (xgcd a b).w

中文:
定义 gcdW
  签名: : 自然数+
  定义体: (xgcd a b).w
-/
def gcdW : Nat+ :=
  (xgcd a b).w

/--
Definition of `gcdX` / `gcdX` 的定义

English:
definition gcdX
  signature: : Nat
  body: (xgcd a b).x

中文:
定义 gcdX
  签名: : 自然数
  定义体: (xgcd a b).x
-/
def gcdX : Nat :=
  (xgcd a b).x

/--
Definition of `gcdY` / `gcdY` 的定义

English:
definition gcdY
  signature: : Nat
  body: (xgcd a b).y

中文:
定义 gcdY
  签名: : 自然数
  定义体: (xgcd a b).y
-/
def gcdY : Nat :=
  (xgcd a b).y

/--
Definition of `gcdZ` / `gcdZ` 的定义

English:
definition gcdZ
  signature: : Nat+
  body: (xgcd a b).z

中文:
定义 gcdZ
  签名: : 自然数+
  定义体: (xgcd a b).z
-/
def gcdZ : Nat+ :=
  (xgcd a b).z

/--
Definition of `gcdA'` / `gcdA'` 的定义

English:
definition gcdA'
  signature: : Nat+
  body: succPNat ((xgcd a b).wp + (xgcd a b).x)

中文:
定义 gcdA'
  签名: : 自然数+
  定义体: succPNat ((xgcd a b).wp + (xgcd a b).x)

Depends on / 依赖: succPNat
-/
def gcdA' : Nat+ :=
  succPNat ((xgcd a b).wp + (xgcd a b).x)

/--
Definition of `gcdB'` / `gcdB'` 的定义

English:
definition gcdB'
  signature: : Nat+
  body: succPNat ((xgcd a b).y + (xgcd a b).zp)

中文:
定义 gcdB'
  签名: : 自然数+
  定义体: succPNat ((xgcd a b).y + (xgcd a b).zp)

Depends on / 依赖: succPNat
-/
def gcdB' : Nat+ :=
  succPNat ((xgcd a b).y + (xgcd a b).zp)

/--
theorem `gcdA'_coe` / 定理 `gcdA'_coe`

English:
theorem gcdA'_coe
  statement: (gcdA' a b : Nat) = gcdW a b + gcdX a b
  proof: by
  dsimp [gcdA', gcdX, gcdW, XgcdType.w]
  rw [add_right_comm]

中文:
定理 gcdA'_coe
  结论: (gcdA' a b : 自然数) = gcdW a b + gcdX a b
  证明: by
  dsimp [gcdA', gcdX, gcdW, XgcdType.w]
  rw [add_right_comm]
-/
theorem gcdA'_coe : (gcdA' a b : Nat) = gcdW a b + gcdX a b := by
  dsimp [gcdA', gcdX, gcdW, XgcdType.w]
  rw [add_right_comm]

/--
theorem `gcdB'_coe` / 定理 `gcdB'_coe`

English:
theorem gcdB'_coe
  statement: (gcdB' a b : Nat) = gcdY a b + gcdZ a b
  proof: by
  dsimp [gcdB', gcdY, gcdZ, XgcdType.z]
  rw [add_assoc]

中文:
定理 gcdB'_coe
  结论: (gcdB' a b : 自然数) = gcdY a b + gcdZ a b
  证明: by
  dsimp [gcdB', gcdY, gcdZ, XgcdType.z]
  rw [add_assoc]
-/
theorem gcdB'_coe : (gcdB' a b : Nat) = gcdY a b + gcdZ a b := by
  dsimp [gcdB', gcdY, gcdZ, XgcdType.z]
  rw [add_assoc]

/--
theorem `gcd_props` / 定理 `gcd_props`

English:
theorem gcd_props
  proof: gcdD a b
    let w := gcdW a b
    let x := gcdX a b
    let y := gcdY a b
    let z := gcdZ a b
    let a' := gcdA' a b
    let b' := gcdB' a b
    w * z = succPNat (x * y) ∧
      a = a' * d ∧
        b = b' * d ∧
          z * a' = succPNat (x * b') ∧
            w * b' = succPNat (y * a') ∧ (z *

中文:
定理 gcd_props
  证明: gcdD a b
    let w := gcdW a b
    let x := gcdX a b
    let y := gcdY a b
    let z := gcdZ a b
    let a' := gcdA' a b
    let b' := gcdB' a b
    w * z = succPNat (x * y) ∧
      a = a' * d ∧
        b = b' * d ∧
          z * a' = succPNat (x * b') ∧
            w * b' = succPNat (y * a') ∧ (z *
-/
theorem gcd_props :
    let d := gcdD a b
    let w := gcdW a b
    let x := gcdX a b
    let y := gcdY a b
    let z := gcdZ a b
    let a' := gcdA' a b
    let b' := gcdB' a b
    w * z = succPNat (x * y) ∧
      a = a' * d ∧
        b = b' * d ∧
          z * a' = succPNat (x * b') ∧
            w * b' = succPNat (y * a') ∧ (z * a : Nat) = x * b + d ∧ (w * b : Nat) = y * a + d := by
  intro d w x y z a' b'
  let u := XgcdType.start a b
  let ur := u.reduce
  have hb : d = ur.b := u.reduce_isReduced'
  have ha' : (a' : Nat) = w + x := gcdA'_coe a b
  have hb' : (b' : Nat) = y + z := gcdB'_coe a b
  have hdet : w * z = succPNat (x * y) := u.reduce_isSpecial' rfl
  constructor
  · exact hdet
  have hdet' : (w * z : Nat) = x * y + 1 := by rw [← mul_coe, hdet, succPNat_coe]
  let hv : Prod.mk (w * d + x * ur.b : Nat) (y * d + z * ur.b : Nat) = ⟨a, b⟩ :=
    u.reduce_v.trans (XgcdType.start_v a b)
  rw [← hb]; rw [← add_mul]; rw [← add_mul]; rw [← ha']; rw [← hb'] at hv
  have ha'' : (a : Nat) = a' * d := (congr_arg Prod.fst hv).symm
  have hb'' : (b : Nat) = b' * d := (congr_arg Prod.snd hv).symm
  constructor
  · exact eq ha''
  constructor
  · exact eq hb''
  have hza' : (z * a' : Nat) = x * b' + 1 := by
    rw [ha']; rw [hb']; rw [mul_add]; rw [mul_add]; rw [mul_comm (z : Nat)]; rw [hdet']
    ring
  have hwb' : (w * b' : Nat) = y * a' + 1 := by
    rw [ha']; rw [hb']; rw [mul_add]; rw [mul_add]; rw [hdet']
    ring
  constructor
  · apply eq
    rw [succPNat_coe]; rw [Nat.succ_eq_add_one]; rw [mul_coe]; rw [hza']
  constructor
  · apply eq
    rw [succPNat_coe]; rw [Nat.succ_eq_add_one]; rw [mul_coe]; rw [hwb']
  grind

/--
theorem `gcd_eq` / 定理 `gcd_eq`

English:
theorem gcd_eq
  statement: gcdD a b = gcd a b
  proof: by
  rcases gcd_props a b with ⟨_, h₁, h₂, _, _, h₅, _⟩
  apply dvd_antisymm
  · apply dvd_gcd
    · exact Dvd.intro (gcdA' a b) (h₁.trans (mul_comm _ _)).symm
    · exact Dvd.intro (gcdB' a b) (h₂.trans (mul_comm _ _)).symm
  · have h₇ : (gcd a b : Nat) ∣ gcdZ a b * a := (Nat.gcd_dvd_left a b).tran

中文:
定理 gcd_eq
  结论: gcdD a b = 最大公约数 a b
  证明: by
  rcases gcd_props a b with ⟨_, h₁, h₂, _, _, h₅, _⟩
  apply dvd_antisymm
  · apply dvd_gcd
    · exact Dvd.intro (gcdA' a b) (h₁.trans (mul_comm _ _)).symm
    · exact Dvd.intro (gcdB' a b) (h₂.trans (mul_comm _ _)).symm
  · have h₇ : (gcd a b : Nat) ∣ gcdZ a b * a := (Nat.gcd_dvd_left a b).tran

Depends on / 依赖: Dvd.intro, Nat.dvd_add_iff_right, Nat.gcd_dvd_left, Nat.gcd_dvd_right, dvd_add_iff_right, dvd_antisymm, dvd_gcd, dvd_iff, dvd_mul_left, gcd_dvd_left, gcd_dvd_right, gcd_props, mul_comm
-/
theorem gcd_eq : gcdD a b = gcd a b := by
  rcases gcd_props a b with ⟨_, h₁, h₂, _, _, h₅, _⟩
  apply dvd_antisymm
  · apply dvd_gcd
    · exact Dvd.intro (gcdA' a b) (h₁.trans (mul_comm _ _)).symm
    · exact Dvd.intro (gcdB' a b) (h₂.trans (mul_comm _ _)).symm
  · have h₇ : (gcd a b : Nat) ∣ gcdZ a b * a := (Nat.gcd_dvd_left a b).trans (dvd_mul_left _ _)
    have h₈ : (gcd a b : Nat) ∣ gcdX a b * b := (Nat.gcd_dvd_right a b).trans (dvd_mul_left _ _)
    rw [h₅] at h₇
    rw [dvd_iff]
    exact (Nat.dvd_add_iff_right h₈).mpr h₇

/--
theorem `gcd_det_eq` / 定理 `gcd_det_eq`

English:
theorem gcd_det_eq
  statement: gcdW a b * gcdZ a b = succPNat (gcdX a b * gcdY a b)
  proof: (gcd_props a b).1

中文:
定理 gcd_det_eq
  结论: gcdW a b * gcdZ a b = succP自然数 (gcdX a b * gcdY a b)
  证明: (gcd_props a b).1

Depends on / 依赖: gcd_props
-/
theorem gcd_det_eq : gcdW a b * gcdZ a b = succPNat (gcdX a b * gcdY a b) :=
  (gcd_props a b).1

/--
theorem `gcd_a_eq` / 定理 `gcd_a_eq`

English:
theorem gcd_a_eq
  statement: a = gcdA' a b * gcd a b
  proof: gcd_eq a b ▸ (gcd_props a b).2.1

中文:
定理 gcd_a_eq
  结论: a = gcdA' a b * 最大公约数 a b
  证明: gcd_eq a b ▸ (gcd_props a b).2.1

Depends on / 依赖: gcd_eq, gcd_props
-/
theorem gcd_a_eq : a = gcdA' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.1

/--
theorem `gcd_b_eq` / 定理 `gcd_b_eq`

English:
theorem gcd_b_eq
  statement: b = gcdB' a b * gcd a b
  proof: gcd_eq a b ▸ (gcd_props a b).2.2.1

中文:
定理 gcd_b_eq
  结论: b = gcdB' a b * 最大公约数 a b
  证明: gcd_eq a b ▸ (gcd_props a b).2.2.1

Depends on / 依赖: gcd_eq, gcd_props
-/
theorem gcd_b_eq : b = gcdB' a b * gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.1

/--
theorem `gcd_rel_left'` / 定理 `gcd_rel_left'`

English:
theorem gcd_rel_left'
  statement: gcdZ a b * gcdA' a b = succPNat (gcdX a b * gcdB' a b)
  proof: (gcd_props a b).2.2.2.1

中文:
定理 gcd_rel_left'
  结论: gcdZ a b * gcdA' a b = succP自然数 (gcdX a b * gcdB' a b)
  证明: (gcd_props a b).2.2.2.1

Depends on / 依赖: gcd_props
-/
theorem gcd_rel_left' : gcdZ a b * gcdA' a b = succPNat (gcdX a b * gcdB' a b) :=
  (gcd_props a b).2.2.2.1

/--
theorem `gcd_rel_right'` / 定理 `gcd_rel_right'`

English:
theorem gcd_rel_right'
  statement: gcdW a b * gcdB' a b = succPNat (gcdY a b * gcdA' a b)
  proof: (gcd_props a b).2.2.2.2.1

中文:
定理 gcd_rel_right'
  结论: gcdW a b * gcdB' a b = succP自然数 (gcdY a b * gcdA' a b)
  证明: (gcd_props a b).2.2.2.2.1

Depends on / 依赖: gcd_props
-/
theorem gcd_rel_right' : gcdW a b * gcdB' a b = succPNat (gcdY a b * gcdA' a b) :=
  (gcd_props a b).2.2.2.2.1

/--
theorem `gcd_rel_left` / 定理 `gcd_rel_left`

English:
theorem gcd_rel_left
  statement: (gcdZ a b * a : Nat) = gcdX a b * b + gcd a b
  proof: gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.1

中文:
定理 gcd_rel_left
  结论: (gcdZ a b * a : 自然数) = gcdX a b * b + 最大公约数 a b
  证明: gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.1

Depends on / 依赖: gcd_eq, gcd_props
-/
theorem gcd_rel_left : (gcdZ a b * a : Nat) = gcdX a b * b + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.1

/--
theorem `gcd_rel_right` / 定理 `gcd_rel_right`

English:
theorem gcd_rel_right
  statement: (gcdW a b * b : Nat) = gcdY a b * a + gcd a b
  proof: gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.2

中文:
定理 gcd_rel_right
  结论: (gcdW a b * b : 自然数) = gcdY a b * a + 最大公约数 a b
  证明: gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.2

Depends on / 依赖: gcd_eq, gcd_props
-/
theorem gcd_rel_right : (gcdW a b * b : Nat) = gcdY a b * a + gcd a b :=
  gcd_eq a b ▸ (gcd_props a b).2.2.2.2.2.2

end gcd

end PNat
