/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `Data.Int.Cast.Basic`.

## Main declarations

* `castAddHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

@[expose] public section

assert_not_exists RelIso IsOrderedMonoid Field

open Additive Function Multiplicative Nat

variable {F ι α β : Type*}

namespace Int

/--
Definition of `ofNatHom` / `ofNatHom` 的定义

English:
definition ofNatHom
  signature: : Nat ->+* Int
  body: Nat.castRingHom Int

中文:
定义 ofNatHom
  签名: : 自然数 ->+* 整数
  定义体: Nat.castRingHom Int

Depends on / 依赖: Nat.castRingHom, castRingHom
-/
def ofNatHom : Nat ->+* Int :=
  Nat.castRingHom Int

section cast

/--
Definition of `castAddHom` / `castAddHom` 的定义

English:
definition castAddHom
  signature: (α : Type*) [AddGroupWithOne α]
  body: Int.cast
  map_zero' := cast_zero
  map_add' := cast_add

中文:
定义 castAddHom
  签名: (α : 类型) [AddGroupWithOne α]
  定义体: Int.cast
  map_zero' := cast_zero
  map_add' := cast_add

Depends on / 依赖: Int.cast
-/
def castAddHom (α : Type*) [AddGroupWithOne α] : Int ->+ α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add

section AddGroupWithOne
variable [AddGroupWithOne α]

/--
lemma `coe_castAddHom` / 引理 `coe_castAddHom`

English:
lemma coe_castAddHom
  statement: ⇑(castAddHom α) = fun x : Int => (x : α)
  proof: rfl

中文:
引理 coe_castAddHom
  结论: ⇑(castAddHom α) = fun x : 整数 => (x : α)
  证明: rfl
-/
@[simp] lemma coe_castAddHom : ⇑(castAddHom α) = fun x : Int => (x : α) := rfl

/--
lemma `_root_.Even.intCast` / 引理 `_root_.Even.intCast`

English:
lemma _root_.Even.intCast
  given: {n : Int} (h : Even n)
  statement: Even (n : α)
  proof: h.map (castAddHom α)

中文:
引理 _root_.Even.intCast
  条件: {n : 整数} (h : Even n)
  结论: Even (n : α)
  证明: h.map (castAddHom α)

Depends on / 依赖: castAddHom, h.map
-/
lemma _root_.Even.intCast {n : Int} (h : Even n) : Even (n : α) := h.map (castAddHom α)

variable [CharZero α] {m n : Int}

/--
lemma `cast_eq_zero` / 引理 `cast_eq_zero`

English:
lemma cast_eq_zero
  statement: (n : α) = 0 ↔ n = 0 where
  proof: by
    cases n
    · rw [ofNat_eq_natCast, Int.cast_natCast] at h
      exact congr_arg _ (Nat.cast_eq_zero.1 h)
    · rw [cast_negSucc, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction
  mpr h := by rw [h, cast_zero]

@[simp, norm_cast]

中文:
引理 cast_eq_zero
  结论: (n : α) = 0 ↔ n = 0 where
  证明: by
    cases n
    · rw [ofNat_eq_natCast, Int.cast_natCast] at h
      exact congr_arg _ (Nat.cast_eq_zero.1 h)
    · rw [cast_negSucc, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction
  mpr h := by rw [h, cast_zero]

@[simp, norm_cast]
-/
@[simp] lemma cast_eq_zero : (n : α) = 0 ↔ n = 0 where
  mp h := by
    cases n
    · rw [ofNat_eq_natCast, Int.cast_natCast] at h
      exact congr_arg _ (Nat.cast_eq_zero.1 h)
    · rw [cast_negSucc, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction
  mpr h := by rw [h, cast_zero]

@[simp, norm_cast]
/--
lemma `cast_inj` / 引理 `cast_inj`

English:
lemma cast_inj
  statement: (m : α) = n ↔ m = n
  proof: by rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]

中文:
引理 cast_inj
  结论: (m : α) = n ↔ m = n
  证明: by rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]

Depends on / 依赖: cast_eq_zero, cast_sub, sub_eq_zero
-/
lemma cast_inj : (m : α) = n ↔ m = n := by rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]

/--
lemma `cast_injective` / 引理 `cast_injective`

English:
lemma cast_injective
  statement: Injective (Int.cast : Int -> α)
  proof: fun _ _ => cast_inj.1

中文:
引理 cast_injective
  结论: Injective (整数.cast : 整数 -> α)
  证明: fun _ _ => cast_inj.1

Depends on / 依赖: cast_inj
-/
lemma cast_injective : Injective (Int.cast : Int -> α) := fun _ _ => cast_inj.1

/--
lemma `cast_ne_zero` / 引理 `cast_ne_zero`

English:
lemma cast_ne_zero
  statement: (n : α) != 0 ↔ n != 0
  proof: not_congr cast_eq_zero

中文:
引理 cast_ne_zero
  结论: (n : α) != 0 ↔ n != 0
  证明: not_congr cast_eq_zero

Depends on / 依赖: cast_eq_zero, not_congr
-/
lemma cast_ne_zero : (n : α) != 0 ↔ n != 0 := not_congr cast_eq_zero

/--
lemma `cast_eq_one` / 引理 `cast_eq_one`

English:
lemma cast_eq_one
  statement: (n : α) = 1 ↔ n = 1
  proof: by rw [← cast_one, cast_inj]

中文:
引理 cast_eq_one
  结论: (n : α) = 1 ↔ n = 1
  证明: by rw [← cast_one, cast_inj]
-/
@[simp] lemma cast_eq_one : (n : α) = 1 ↔ n = 1 := by rw [← cast_one, cast_inj]

/--
lemma `cast_ne_one` / 引理 `cast_ne_one`

English:
lemma cast_ne_one
  statement: (n : α) != 1 ↔ n != 1
  proof: cast_eq_one.not

中文:
引理 cast_ne_one
  结论: (n : α) != 1 ↔ n != 1
  证明: cast_eq_one.not

Depends on / 依赖: cast_eq_one, cast_eq_one.not
-/
lemma cast_ne_one : (n : α) != 1 ↔ n != 1 := cast_eq_one.not

end AddGroupWithOne

section NonAssocRing
variable [NonAssocRing α]

variable (α) in
/-- `coe : ℤ → α` as a `RingHom`. -/
@[instance_reducible]
/--
Definition of `castRingHom` / `castRingHom` 的定义

English:
definition castRingHom
  signature: : Int ->+* α where
  body: Int.cast
  map_zero' := cast_zero
  map_add' := cast_add
  map_one' := cast_one
  map_mul' := cast_mul

中文:
定义 castRingHom
  签名: : 整数 ->+* α where
  定义体: Int.cast
  map_zero' := cast_zero
  map_add' := cast_add
  map_one' := cast_one
  map_mul' := cast_mul

Depends on / 依赖: Int.cast
-/
def castRingHom : Int ->+* α where
  toFun := Int.cast
  map_zero' := cast_zero
  map_add' := cast_add
  map_one' := cast_one
  map_mul' := cast_mul

/--
lemma `coe_castRingHom` / 引理 `coe_castRingHom`

English:
lemma coe_castRingHom
  statement: ⇑(castRingHom α) = fun x : Int => (x : α)
  proof: rfl

中文:
引理 coe_castRingHom
  结论: ⇑(castRingHom α) = fun x : 整数 => (x : α)
  证明: rfl
-/
@[simp] lemma coe_castRingHom : ⇑(castRingHom α) = fun x : Int => (x : α) := rfl

/--
lemma `cast_commute` / 引理 `cast_commute`

English:
lemma cast_commute
  statement: forall (n : Int) (a : α), Commute ↑n a

中文:
引理 cast_commute
  结论: 对任意 (n : 整数) (a : α), Commute ↑n a
-/
lemma cast_commute : forall (n : Int) (a : α), Commute ↑n a
  | (n : Nat), x => by simpa using n.cast_commute x
  | -[n+1], x => by
    simpa only [cast_negSucc, Commute.neg_left_iff, Commute.neg_right_iff] using
      (n + 1).cast_commute (-x)

/--
lemma `cast_comm` / 引理 `cast_comm`

English:
lemma cast_comm
  given: (n : Int) (x : α)
  statement: n * x = x * n
  proof: (cast_commute ..).eq

中文:
引理 cast_comm
  条件: (n : 整数) (x : α)
  结论: n * x = x * n
  证明: (cast_commute ..).eq

Depends on / 依赖: cast_commute
-/
lemma cast_comm (n : Int) (x : α) : n * x = x * n := (cast_commute ..).eq

/--
lemma `commute_cast` / 引理 `commute_cast`

English:
lemma commute_cast
  given: (a : α) (n : Int)
  statement: Commute a n
  proof: (cast_commute ..).symm

中文:
引理 commute_cast
  条件: (a : α) (n : 整数)
  结论: Commute a n
  证明: (cast_commute ..).symm

Depends on / 依赖: cast_commute
-/
lemma commute_cast (a : α) (n : Int) : Commute a n := (cast_commute ..).symm

/--
lemma `_root_.zsmul_eq_mul` / 引理 `_root_.zsmul_eq_mul`

English:
lemma _root_.zsmul_eq_mul
  given: (a : α)
  statement: forall n : Int, n • a = n * a

中文:
引理 _root_.zsmul_eq_mul
  条件: (a : α)
  结论: 对任意 n : 整数, n • a = n * a
-/
@[simp] lemma _root_.zsmul_eq_mul (a : α) : forall n : Int, n • a = n * a
  | (n : Nat) => by rw [natCast_zsmul, nsmul_eq_mul, Int.cast_natCast]
  | -[n+1] => by simp [Nat.cast_succ, neg_add_rev, Int.cast_negSucc, add_mul]

/--
lemma `_root_.zsmul_eq_mul'` / 引理 `_root_.zsmul_eq_mul'`

English:
lemma _root_.zsmul_eq_mul'
  given: (a : α) (n : Int)
  statement: n • a = a * n
  proof: by
  rw [zsmul_eq_mul]; rw [(n.cast_commute a).eq]

中文:
引理 _root_.zsmul_eq_mul'
  条件: (a : α) (n : 整数)
  结论: n • a = a * n
  证明: by
  rw [zsmul_eq_mul]; rw [(n.cast_commute a).eq]

Depends on / 依赖: cast_commute, n.cast_commute, zsmul_eq_mul
-/
lemma _root_.zsmul_eq_mul' (a : α) (n : Int) : n • a = a * n := by
  rw [zsmul_eq_mul]; rw [(n.cast_commute a).eq]

end NonAssocRing

section Ring
variable [Ring α] {n : Int}

/--
lemma `_root_.Odd.intCast` / 引理 `_root_.Odd.intCast`

English:
lemma _root_.Odd.intCast
  given: (hn : Odd n)
  statement: Odd (n : α)
  proof: hn.map (castRingHom α)

中文:
引理 _root_.Odd.intCast
  条件: (hn : Odd n)
  结论: Odd (n : α)
  证明: hn.map (castRingHom α)

Depends on / 依赖: castRingHom, hn.map
-/
lemma _root_.Odd.intCast (hn : Odd n) : Odd (n : α) := hn.map (castRingHom α)

end Ring

/--
theorem `cast_dvd_cast` / 定理 `cast_dvd_cast`

English:
theorem cast_dvd_cast
  given: [Ring α] (m n : Int) (h : m ∣ n)
  statement: (m : α) ∣ (n : α)
  proof: map_dvd (Int.castRingHom α) h

中文:
定理 cast_dvd_cast
  条件: [Ring α] (m n : 整数) (h : m ∣ n)
  结论: (m : α) ∣ (n : α)
  证明: map_dvd (Int.castRingHom α) h

Depends on / 依赖: Int.castRingHom, castRingHom, map_dvd
-/
theorem cast_dvd_cast [Ring α] (m n : Int) (h : m ∣ n) : (m : α) ∣ (n : α) :=
  map_dvd (Int.castRingHom α) h

end cast

end Int

open Int

namespace SemiconjBy
variable [Ring α] {a x y : α}

/--
lemma `intCast_mul_right` / 引理 `intCast_mul_right`

English:
lemma intCast_mul_right
  given: (h : SemiconjBy a x y) (n : Int)
  statement: SemiconjBy a (n * x) (n * y)
  proof: SemiconjBy.mul_right (Int.commute_cast _ _) h

中文:
引理 intCast_mul_right
  条件: (h : SemiconjBy a x y) (n : 整数)
  结论: SemiconjBy a (n * x) (n * y)
  证明: SemiconjBy.mul_right (Int.commute_cast _ _) h
-/
@[simp] lemma intCast_mul_right (h : SemiconjBy a x y) (n : Int) : SemiconjBy a (n * x) (n * y) :=
  SemiconjBy.mul_right (Int.commute_cast _ _) h

/--
lemma `intCast_mul_left` / 引理 `intCast_mul_left`

English:
lemma intCast_mul_left
  given: (h : SemiconjBy a x y) (n : Int)
  statement: SemiconjBy (n * a) x y
  proof: SemiconjBy.mul_left (Int.cast_commute _ _) h

中文:
引理 intCast_mul_left
  条件: (h : SemiconjBy a x y) (n : 整数)
  结论: SemiconjBy (n * a) x y
  证明: SemiconjBy.mul_left (Int.cast_commute _ _) h
-/
@[simp] lemma intCast_mul_left (h : SemiconjBy a x y) (n : Int) : SemiconjBy (n * a) x y :=
  SemiconjBy.mul_left (Int.cast_commute _ _) h

/--
lemma `intCast_mul_intCast_mul` / 引理 `intCast_mul_intCast_mul`

English:
lemma intCast_mul_intCast_mul
  given: (h : SemiconjBy a x y) (m n : Int)
  proof: by simp [h]

中文:
引理 intCast_mul_intCast_mul
  条件: (h : SemiconjBy a x y) (m n : 整数)
  证明: by simp [h]
-/
lemma intCast_mul_intCast_mul (h : SemiconjBy a x y) (m n : Int) :
    SemiconjBy (m * a) (n * x) (n * y) := by simp [h]

end SemiconjBy

namespace Commute
section NonAssocRing
variable [NonAssocRing α] {a : α} {n : Int}

/--
lemma `intCast_left` / 引理 `intCast_left`

English:
lemma intCast_left
  statement: Commute (n : α) a
  proof: Int.cast_commute _ _

中文:
引理 intCast_left
  结论: Commute (n : α) a
  证明: Int.cast_commute _ _
-/
@[simp] lemma intCast_left : Commute (n : α) a := Int.cast_commute _ _

/--
lemma `intCast_right` / 引理 `intCast_right`

English:
lemma intCast_right
  statement: Commute a n
  proof: Int.commute_cast _ _

中文:
引理 intCast_right
  结论: Commute a n
  证明: Int.commute_cast _ _
-/
@[simp] lemma intCast_right : Commute a n := Int.commute_cast _ _

end NonAssocRing

section Ring
variable [Ring α] {a b : α}

/--
lemma `intCast_mul_right` / 引理 `intCast_mul_right`

English:
lemma intCast_mul_right
  given: (h : Commute a b) (m : Int)
  statement: Commute a (m * b)
  proof: by
  simp [h]

中文:
引理 intCast_mul_right
  条件: (h : Commute a b) (m : 整数)
  结论: Commute a (m * b)
  证明: by
  simp [h]
-/
lemma intCast_mul_right (h : Commute a b) (m : Int) : Commute a (m * b) := by
  simp [h]

/--
lemma `intCast_mul_left` / 引理 `intCast_mul_left`

English:
lemma intCast_mul_left
  given: (h : Commute a b) (m : Int)
  statement: Commute (m * a) b
  proof: by
  simp [h]

中文:
引理 intCast_mul_left
  条件: (h : Commute a b) (m : 整数)
  结论: Commute (m * a) b
  证明: by
  simp [h]
-/
lemma intCast_mul_left (h : Commute a b) (m : Int) : Commute (m * a) b := by
  simp [h]

/--
lemma `intCast_mul_intCast_mul` / 引理 `intCast_mul_intCast_mul`

English:
lemma intCast_mul_intCast_mul
  given: (h : Commute a b) (m n : Int)
  statement: Commute (m * a) (n * b)
  proof: SemiconjBy.intCast_mul_intCast_mul h m n

中文:
引理 intCast_mul_intCast_mul
  条件: (h : Commute a b) (m n : 整数)
  结论: Commute (m * a) (n * b)
  证明: SemiconjBy.intCast_mul_intCast_mul h m n

Depends on / 依赖: SemiconjBy, SemiconjBy.intCast_mul_intCast_mul, intCast_mul_intCast_mul
-/
lemma intCast_mul_intCast_mul (h : Commute a b) (m n : Int) : Commute (m * a) (n * b) :=
  SemiconjBy.intCast_mul_intCast_mul h m n

variable (a) (m n : Int)

/--
lemma `self_intCast_mul` / 引理 `self_intCast_mul`

English:
lemma self_intCast_mul
  statement: Commute a (n * a : α)
  proof: (Commute.refl a).intCast_mul_right n

中文:
引理 self_intCast_mul
  结论: Commute a (n * a : α)
  证明: (Commute.refl a).intCast_mul_right n

Depends on / 依赖: Commute, Commute.refl, intCast_mul_right
-/
lemma self_intCast_mul : Commute a (n * a : α) := (Commute.refl a).intCast_mul_right n

/--
lemma `intCast_mul_self` / 引理 `intCast_mul_self`

English:
lemma intCast_mul_self
  statement: Commute ((n : α) * a) a
  proof: (Commute.refl a).intCast_mul_left n

中文:
引理 intCast_mul_self
  结论: Commute ((n : α) * a) a
  证明: (Commute.refl a).intCast_mul_left n

Depends on / 依赖: Commute, Commute.refl, intCast_mul_left
-/
lemma intCast_mul_self : Commute ((n : α) * a) a := (Commute.refl a).intCast_mul_left n

/--
lemma `self_intCast_mul_intCast_mul` / 引理 `self_intCast_mul_intCast_mul`

English:
lemma self_intCast_mul_intCast_mul
  statement: Commute (m * a : α) (n * a : α)
  proof: (Commute.refl a).intCast_mul_intCast_mul m n

中文:
引理 self_intCast_mul_intCast_mul
  结论: Commute (m * a : α) (n * a : α)
  证明: (Commute.refl a).intCast_mul_intCast_mul m n

Depends on / 依赖: Commute, Commute.refl, intCast_mul_intCast_mul
-/
lemma self_intCast_mul_intCast_mul : Commute (m * a : α) (n * a : α) :=
  (Commute.refl a).intCast_mul_intCast_mul m n

end Ring
end Commute

namespace AddMonoidHom

variable {A : Type*}

/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext high]
/--
theorem `ext_int` / 定理 `ext_int`

English:
theorem ext_int
  given: [AddMonoid A] {f g : Int ->+ A} (h1 : f 1 = g 1)
  statement: f = g
  proof: have : f.comp (Int.ofNatHom : Nat ->+ Int) = g.comp (Int.ofNatHom : Nat ->+ Int) := ext_nat' _ _ h1
  have this' : forall n : Nat, f n = g n := DFunLike.ext_iff.1 this
  ext fun n => match n with
  | (n : Nat) => this' n
  | .negSucc n => eq_on_neg _ _ (this' <| n + 1)

中文:
定理 ext_int
  条件: [AddMonoid A] {f g : 整数 ->+ A} (h1 : f 1 = g 1)
  结论: f = g
  证明: have : f.comp (Int.ofNatHom : Nat ->+ Int) = g.comp (Int.ofNatHom : Nat ->+ Int) := ext_nat' _ _ h1
  have this' : forall n : Nat, f n = g n := DFunLike.ext_iff.1 this
  ext fun n => match n with
  | (n : Nat) => this' n
  | .negSucc n => eq_on_neg _ _ (this' <| n + 1)

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Int.ofNatHom, eq_on_neg, ext_iff, ext_nat, f.comp, g.comp, negSucc, ofNatHom
-/
theorem ext_int [AddMonoid A] {f g : Int ->+ A} (h1 : f 1 = g 1) : f = g :=
  have : f.comp (Int.ofNatHom : Nat ->+ Int) = g.comp (Int.ofNatHom : Nat ->+ Int) := ext_nat' _ _ h1
  have this' : forall n : Nat, f n = g n := DFunLike.ext_iff.1 this
  ext fun n => match n with
  | (n : Nat) => this' n
  | .negSucc n => eq_on_neg _ _ (this' <| n + 1)

variable [AddGroupWithOne A]

/--
theorem `eq_intCastAddHom` / 定理 `eq_intCastAddHom`

English:
theorem eq_intCastAddHom
  given: (f : Int ->+ A) (h1 : f 1 = 1)
  statement: f = Int.castAddHom A
  proof: ext_int by simp [h1]

中文:
定理 eq_intCastAddHom
  条件: (f : 整数 ->+ A) (h1 : f 1 = 1)
  结论: f = 整数.castAddHom A
  证明: ext_int by simp [h1]

Depends on / 依赖: ext_int
-/
theorem eq_intCastAddHom (f : Int ->+ A) (h1 : f 1 = 1) : f = Int.castAddHom A :=
ext_int by simp [h1]

end AddMonoidHom

namespace AddEquiv
variable {A : Type*}

/-- Two additive monoid isomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext high]
/--
theorem `ext_int` / 定理 `ext_int`

English:
theorem ext_int
  given: [AddMonoid A] {f g : Int ≃+ A} (h1 : f 1 = g 1)
  statement: f = g
  proof: toAddMonoidHom_injective AddMonoidHom.ext_int h1

中文:
定理 ext_int
  条件: [AddMonoid A] {f g : 整数 ≃+ A} (h1 : f 1 = g 1)
  结论: f = g
  证明: toAddMonoidHom_injective AddMonoidHom.ext_int h1

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext_int, ext_int, toAddMonoidHom_injective
-/
theorem ext_int [AddMonoid A] {f g : Int ≃+ A} (h1 : f 1 = g 1) : f = g :=
toAddMonoidHom_injective AddMonoidHom.ext_int h1

end AddEquiv

/--
theorem `eq_intCast'` / 定理 `eq_intCast'`

English:
theorem eq_intCast'
  statement: [AddGroupWithOne α] [FunLike F Int α] [AddMonoidHomClass F Int α]
  proof: DFunLike.ext_iff.1 (f : Int ->+ α).eq_intCastAddHom h₁

中文:
定理 eq_intCast'
  结论: [AddGroupWithOne α] [FunLike F 整数 α] [AddMonoidHomClass F 整数 α]
  证明: DFunLike.ext_iff.1 (f : Int ->+ α).eq_intCastAddHom h₁

Depends on / 依赖: DFunLike, DFunLike.ext_iff, eq_intCastAddHom, ext_iff
-/
theorem eq_intCast' [AddGroupWithOne α] [FunLike F Int α] [AddMonoidHomClass F Int α]
    (f : F) (h₁ : f 1 = 1) :
    forall n : Int, f n = n :=
DFunLike.ext_iff.1 (f : Int ->+ α).eq_intCastAddHom h₁

/--
theorem `map_intCast'` / 定理 `map_intCast'`

English:
theorem map_intCast'
  statement: [AddGroupWithOne α] [AddGroupWithOne β] [FunLike F α β]
  proof: eq_intCast' ((f : α ->+ β).comp <| Int.castAddHom _) (by simpa)

@[simp]

中文:
定理 map_intCast'
  结论: [AddGroupWithOne α] [AddGroupWithOne β] [FunLike F α β]
  证明: eq_intCast' ((f : α ->+ β).comp <| Int.castAddHom _) (by simpa)

@[simp]

Depends on / 依赖: Int.castAddHom, castAddHom, eq_intCast
-/
theorem map_intCast' [AddGroupWithOne α] [AddGroupWithOne β] [FunLike F α β]
    [AddMonoidHomClass F α β] (f : F) (h₁ : f 1 = 1) : forall n : Int, f n = n :=
  eq_intCast' ((f : α ->+ β).comp <| Int.castAddHom _) (by simpa)

@[simp]
/--
theorem `Int.castAddHom_int` / 定理 `Int.castAddHom_int`

English:
theorem Int.castAddHom_int
  statement: Int.castAddHom Int = AddMonoidHom.id Int
  proof: ((AddMonoidHom.id Int).eq_intCastAddHom rfl).symm

中文:
定理 Int.castAddHom_int
  结论: 整数.castAddHom 整数 = AddMonoidHom.id 整数
  证明: ((AddMonoidHom.id Int).eq_intCastAddHom rfl).symm

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, eq_intCastAddHom
-/
theorem Int.castAddHom_int : Int.castAddHom Int = AddMonoidHom.id Int :=
  ((AddMonoidHom.id Int).eq_intCastAddHom rfl).symm

namespace MonoidHom

variable {M : Type*} [Monoid M]

@[ext]
/--
theorem `ext_mint` / 定理 `ext_mint`

English:
theorem ext_mint
  given: {f g : Multiplicative Int ->* M} (h1 : f (ofAdd 1) = g (ofAdd 1))
  statement: f = g
  proof: MonoidHom.toAdditiveRight.injective AddMonoidHom.ext_int Additive.toMul.injective h1

中文:
定理 ext_mint
  条件: {f g : Multiplicative 整数 ->* M} (h1 : f (ofAdd 1) = g (ofAdd 1))
  结论: f = g
  证明: MonoidHom.toAdditiveRight.injective AddMonoidHom.ext_int Additive.toMul.injective h1

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext_int, Additive, Additive.toMul.injective, MonoidHom, MonoidHom.toAdditiveRight.injective, ext_int, injective, toAdditiveRight
-/
theorem ext_mint {f g : Multiplicative Int ->* M} (h1 : f (ofAdd 1) = g (ofAdd 1)) : f = g :=
MonoidHom.toAdditiveRight.injective AddMonoidHom.ext_int Additive.toMul.injective h1

/-- If two `MonoidHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
/--
theorem `ext_int` / 定理 `ext_int`

English:
theorem ext_int
  statement: {f g : Int ->* M} (h_neg_one : f (-1) = g (-1))
  proof: by
  ext (x | x)
  · exact (DFunLike.congr_fun h_nat x :)
  · rw [Int.negSucc_eq, ← neg_one_mul, f.map_mul, g.map_mul]
    congr 1
    exact mod_cast (DFunLike.congr_fun h_nat (x + 1) :)

中文:
定理 ext_int
  结论: {f g : 整数 ->* M} (h_neg_one : f (-1) = g (-1))
  证明: by
  ext (x | x)
  · exact (DFunLike.congr_fun h_nat x :)
  · rw [Int.negSucc_eq, ← neg_one_mul, f.map_mul, g.map_mul]
    congr 1
    exact mod_cast (DFunLike.congr_fun h_nat (x + 1) :)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Int.negSucc_eq, congr_fun, f.map_mul, g.map_mul, h_nat, map_mul, mod_cast, negSucc_eq, neg_one_mul
-/
theorem ext_int {f g : Int ->* M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) : f = g := by
  ext (x | x)
  · exact (DFunLike.congr_fun h_nat x :)
  · rw [Int.negSucc_eq, ← neg_one_mul, f.map_mul, g.map_mul]
    congr 1
    exact mod_cast (DFunLike.congr_fun h_nat (x + 1) :)

end MonoidHom

namespace MonoidWithZeroHom

variable {M : Type*} [MonoidWithZero M]

/-- If two `MonoidWithZeroHom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
/--
theorem `ext_int` / 定理 `ext_int`

English:
theorem ext_int
  statement: {f g : Int ->*₀ M} (h_neg_one : f (-1) = g (-1))
  proof: toMonoidHom_injective MonoidHom.ext_int h_neg_one
    MonoidHom.ext (DFunLike.congr_fun h_nat :)

中文:
定理 ext_int
  结论: {f g : 整数 ->*₀ M} (h_neg_one : f (-1) = g (-1))
  证明: toMonoidHom_injective MonoidHom.ext_int h_neg_one
    MonoidHom.ext (DFunLike.congr_fun h_nat :)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, MonoidHom, MonoidHom.ext, MonoidHom.ext_int, congr_fun, ext_int, h_nat, h_neg_one, toMonoidHom_injective
-/
theorem ext_int {f g : Int ->*₀ M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatHom.toMonoidWithZeroHom) :
    f = g :=
toMonoidHom_injective MonoidHom.ext_int h_neg_one
    MonoidHom.ext (DFunLike.congr_fun h_nat :)

end MonoidWithZeroHom

/--
theorem `ext_int'` / 定理 `ext_int'`

English:
theorem ext_int'
  statement: [MonoidWithZero α] [FunLike F Int α] [MonoidWithZeroHomClass F Int α] {f g : F}
  proof: (DFunLike.ext _ _) fun n =>
    haveI :=
      DFunLike.congr_fun
        (@MonoidWithZeroHom.ext_int _ _ (.ofClass f) (.ofClass g) h_neg_one <|
          MonoidWithZeroHom.ext_nat (h_pos _))
        n
    this

中文:
定理 ext_int'
  结论: [MonoidWithZero α] [FunLike F 整数 α] [MonoidWithZeroHomClass F 整数 α] {f g : F}
  证明: (DFunLike.ext _ _) fun n =>
    haveI :=
      DFunLike.congr_fun
        (@MonoidWithZeroHom.ext_int _ _ (.ofClass f) (.ofClass g) h_neg_one <|
          MonoidWithZeroHom.ext_nat (h_pos _))
        n
    this

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DFunLike.ext, MonoidWithZeroHom, MonoidWithZeroHom.ext_int, MonoidWithZeroHom.ext_nat, congr_fun, ext_int, ext_nat, h_neg_one, h_pos, ofClass
-/
theorem ext_int' [MonoidWithZero α] [FunLike F Int α] [MonoidWithZeroHomClass F Int α] {f g : F}
    (h_neg_one : f (-1) = g (-1)) (h_pos : forall n : Nat, 0 < n -> f n = g n) : f = g :=
  (DFunLike.ext _ _) fun n =>
    haveI :=
      DFunLike.congr_fun
        (@MonoidWithZeroHom.ext_int _ _ (.ofClass f) (.ofClass g) h_neg_one <|
          MonoidWithZeroHom.ext_nat (h_pos _))
        n
    this

section Group
variable (α) [Group α] (β) [AddGroup β]

/--
Definition of `zmultiplesHom` / `zmultiplesHom` 的定义

English:
definition zmultiplesHom
  signature: : β ≃ (Int ->+ β) where
  body: { toFun := fun n => n • x
    map_zero' := zero_zsmul x
    map_add' := fun _ _ => add_zsmul _ _ _ }
  invFun f := f 1
  left_inv := one_zsmul
right_inv f := AddMonoidHom.ext_int one_zsmul (f 1)

中文:
定义 zmultiplesHom
  签名: : β ≃ (整数 ->+ β) where
  定义体: { toFun := fun n => n • x
    map_zero' := zero_zsmul x
    map_add' := fun _ _ => add_zsmul _ _ _ }
  invFun f := f 1
  left_inv := one_zsmul
right_inv f := AddMonoidHom.ext_int one_zsmul (f 1)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext_int, add_zsmul, ext_int, invFun, left_inv, map_add, map_zero, one_zsmul, right_inv, zero_zsmul
-/
def zmultiplesHom : β ≃ (Int ->+ β) where
  toFun x :=
  { toFun := fun n => n • x
    map_zero' := zero_zsmul x
    map_add' := fun _ _ => add_zsmul _ _ _ }
  invFun f := f 1
  left_inv := one_zsmul
right_inv f := AddMonoidHom.ext_int one_zsmul (f 1)

/--
Definition of `zpowersHom` / `zpowersHom` 的定义

English:
definition zpowersHom
  signature: : α ≃ (Multiplicative Int ->* α)
  body: ofMul.trans (zmultiplesHom _).trans AddMonoidHom.toMultiplicativeLeft

中文:
定义 zpowersHom
  签名: : α ≃ (Multiplicative 整数 ->* α)
  定义体: ofMul.trans (zmultiplesHom _).trans AddMonoidHom.toMultiplicativeLeft

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicativeLeft, ofMul.trans, toMultiplicativeLeft, zmultiplesHom
-/
def zpowersHom : α ≃ (Multiplicative Int ->* α) :=
ofMul.trans (zmultiplesHom _).trans AddMonoidHom.toMultiplicativeLeft

/--
lemma `zmultiplesHom_apply` / 引理 `zmultiplesHom_apply`

English:
lemma zmultiplesHom_apply
  given: (x : β) (n : Int)
  statement: zmultiplesHom β x n = n • x
  proof: rfl

中文:
引理 zmultiplesHom_apply
  条件: (x : β) (n : 整数)
  结论: zmultiplesHom β x n = n • x
  证明: rfl
-/
@[simp] lemma zmultiplesHom_apply (x : β) (n : Int) : zmultiplesHom β x n = n • x := rfl

/--
lemma `zmultiplesHom_symm_apply` / 引理 `zmultiplesHom_symm_apply`

English:
lemma zmultiplesHom_symm_apply
  given: (f : Int ->+ β)
  statement: (zmultiplesHom β).symm f = f 1
  proof: rfl

中文:
引理 zmultiplesHom_symm_apply
  条件: (f : 整数 ->+ β)
  结论: (zmultiplesHom β).symm f = f 1
  证明: rfl
-/
@[simp] lemma zmultiplesHom_symm_apply (f : Int ->+ β) : (zmultiplesHom β).symm f = f 1 := rfl

/--
lemma `zpowersHom_apply` / 引理 `zpowersHom_apply`

English:
lemma zpowersHom_apply
  given: (x : α) (n : Multiplicative Int)
  proof: rfl

中文:
引理 zpowersHom_apply
  条件: (x : α) (n : Multiplicative 整数)
  证明: rfl
-/
@[simp] lemma zpowersHom_apply (x : α) (n : Multiplicative Int) :
    zpowersHom α x n = x ^ n.toAdd := rfl

/--
lemma `zpowersHom_symm_apply` / 引理 `zpowersHom_symm_apply`

English:
lemma zpowersHom_symm_apply
  given: (f : Multiplicative Int ->* α)
  proof: rfl

中文:
引理 zpowersHom_symm_apply
  条件: (f : Multiplicative 整数 ->* α)
  证明: rfl
-/
@[simp] lemma zpowersHom_symm_apply (f : Multiplicative Int ->* α) :
    (zpowersHom α).symm f = f (ofAdd 1) := rfl

/--
lemma `MonoidHom.apply_mint` / 引理 `MonoidHom.apply_mint`

English:
lemma MonoidHom.apply_mint
  given: (f : Multiplicative Int ->* α) (n : Multiplicative Int)
  proof: by
  rw [← zpowersHom_symm_apply]; rw [← zpowersHom_apply]; rw [Equiv.apply_symm_apply]

中文:
引理 MonoidHom.apply_mint
  条件: (f : Multiplicative 整数 ->* α) (n : Multiplicative 整数)
  证明: by
  rw [← zpowersHom_symm_apply]; rw [← zpowersHom_apply]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, zpowersHom_apply, zpowersHom_symm_apply
-/
lemma MonoidHom.apply_mint (f : Multiplicative Int ->* α) (n : Multiplicative Int) :
    f n = f (ofAdd 1) ^ n.toAdd := by
  rw [← zpowersHom_symm_apply]; rw [← zpowersHom_apply]; rw [Equiv.apply_symm_apply]

/--
lemma `AddMonoidHom.apply_int` / 引理 `AddMonoidHom.apply_int`

English:
lemma AddMonoidHom.apply_int
  given: (f : Int ->+ β) (n : Int)
  statement: f n = n • f 1
  proof: by
  rw [← zmultiplesHom_symm_apply]; rw [← zmultiplesHom_apply]; rw [Equiv.apply_symm_apply]

中文:
引理 AddMonoidHom.apply_int
  条件: (f : 整数 ->+ β) (n : 整数)
  结论: f n = n • f 1
  证明: by
  rw [← zmultiplesHom_symm_apply]; rw [← zmultiplesHom_apply]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, zmultiplesHom_apply, zmultiplesHom_symm_apply
-/
lemma AddMonoidHom.apply_int (f : Int ->+ β) (n : Int) : f n = n • f 1 := by
  rw [← zmultiplesHom_symm_apply]; rw [← zmultiplesHom_apply]; rw [Equiv.apply_symm_apply]

end Group

section CommGroup
variable (α) [CommGroup α] (β) [AddCommGroup β]

/--
Definition of `zmultiplesAddHom` / `zmultiplesAddHom` 的定义

English:
definition zmultiplesAddHom
  signature: : β ≃+ (Int ->+ β)
  body: { zmultiplesHom β with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [zsmul_add] }

中文:
定义 zmultiplesAddHom
  签名: : β ≃+ (整数 ->+ β)
  定义体: { zmultiplesHom β with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [zsmul_add] }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, map_add, zmultiplesHom, zsmul_add
-/
def zmultiplesAddHom : β ≃+ (Int ->+ β) :=
  { zmultiplesHom β with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [zsmul_add] }

/--
Definition of `zpowersMulHom` / `zpowersMulHom` 的定义

English:
definition zpowersMulHom
  signature: : α ≃* (Multiplicative Int ->* α)
  body: { zpowersHom α with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_zpow] }

中文:
定义 zpowersMulHom
  签名: : α ≃* (Multiplicative 整数 ->* α)
  定义体: { zpowersHom α with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_zpow] }

Depends on / 依赖: MonoidHom, MonoidHom.ext, map_mul, mul_zpow, zpowersHom
-/
def zpowersMulHom : α ≃* (Multiplicative Int ->* α) :=
  { zpowersHom α with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_zpow] }

variable {α}

@[simp]
/--
lemma `zpowersMulHom_apply` / 引理 `zpowersMulHom_apply`

English:
lemma zpowersMulHom_apply
  given: (x : α) (n : Multiplicative Int)
  statement: zpowersMulHom α x n = x ^ n.toAdd
  proof: rfl

@[simp]

中文:
引理 zpowersMulHom_apply
  条件: (x : α) (n : Multiplicative 整数)
  结论: zpowersMulHom α x n = x ^ n.toAdd
  证明: rfl

@[simp]
-/
lemma zpowersMulHom_apply (x : α) (n : Multiplicative Int) : zpowersMulHom α x n = x ^ n.toAdd := rfl

@[simp]
/--
lemma `zpowersMulHom_symm_apply` / 引理 `zpowersMulHom_symm_apply`

English:
lemma zpowersMulHom_symm_apply
  given: (f : Multiplicative Int ->* α)
  proof: rfl

中文:
引理 zpowersMulHom_symm_apply
  条件: (f : Multiplicative 整数 ->* α)
  证明: rfl
-/
lemma zpowersMulHom_symm_apply (f : Multiplicative Int ->* α) :
    (zpowersMulHom α).symm f = f (ofAdd 1) := rfl

/--
lemma `zmultiplesAddHom_apply` / 引理 `zmultiplesAddHom_apply`

English:
lemma zmultiplesAddHom_apply
  given: (x : β) (n : Int)
  statement: zmultiplesAddHom β x n = n • x
  proof: rfl

中文:
引理 zmultiplesAddHom_apply
  条件: (x : β) (n : 整数)
  结论: zmultiplesAddHom β x n = n • x
  证明: rfl
-/
@[simp] lemma zmultiplesAddHom_apply (x : β) (n : Int) : zmultiplesAddHom β x n = n • x := rfl

/--
lemma `zmultiplesAddHom_symm_apply` / 引理 `zmultiplesAddHom_symm_apply`

English:
lemma zmultiplesAddHom_symm_apply
  given: (f : Int ->+ β)
  statement: (zmultiplesAddHom β).symm f = f 1
  proof: rfl

中文:
引理 zmultiplesAddHom_symm_apply
  条件: (f : 整数 ->+ β)
  结论: (zmultiplesAddHom β).symm f = f 1
  证明: rfl
-/
@[simp] lemma zmultiplesAddHom_symm_apply (f : Int ->+ β) : (zmultiplesAddHom β).symm f = f 1 := rfl

end CommGroup

section NonAssocRing

variable [NonAssocRing α] [NonAssocRing β]

@[simp]
/--
theorem `eq_intCast` / 定理 `eq_intCast`

English:
theorem eq_intCast
  given: [FunLike F Int α] [RingHomClass F Int α] (f : F) (n : Int)
  statement: f n = n
  proof: eq_intCast' f (map_one _) n

@[simp]

中文:
定理 eq_intCast
  条件: [FunLike F 整数 α] [RingHomClass F 整数 α] (f : F) (n : 整数)
  结论: f n = n
  证明: eq_intCast' f (map_one _) n

@[simp]

Depends on / 依赖: eq_intCast, map_one
-/
theorem eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) (n : Int) : f n = n :=
  eq_intCast' f (map_one _) n

@[simp]
/--
theorem `map_intCast` / 定理 `map_intCast`

English:
theorem map_intCast
  given: [FunLike F α β] [RingHomClass F α β] (f : F) (n : Int)
  statement: f n = n
  proof: eq_intCast ((f : α ->+* β).comp (Int.castRingHom α)) n

中文:
定理 map_intCast
  条件: [FunLike F α β] [RingHomClass F α β] (f : F) (n : 整数)
  结论: f n = n
  证明: eq_intCast ((f : α ->+* β).comp (Int.castRingHom α)) n

Depends on / 依赖: Int.castRingHom, castRingHom, eq_intCast
-/
theorem map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n : Int) : f n = n :=
  eq_intCast ((f : α ->+* β).comp (Int.castRingHom α)) n

namespace RingHom

/--
theorem `eq_intCast'` / 定理 `eq_intCast'`

English:
theorem eq_intCast'
  given: (f : Int ->+* α)
  statement: f = Int.castRingHom α
  proof: RingHom.ext eq_intCast f

中文:
定理 eq_intCast'
  条件: (f : 整数 ->+* α)
  结论: f = 整数.castRingHom α
  证明: RingHom.ext eq_intCast f

Depends on / 依赖: RingHom, RingHom.ext, eq_intCast
-/
theorem eq_intCast' (f : Int ->+* α) : f = Int.castRingHom α :=
RingHom.ext eq_intCast f

/--
theorem `ext_int` / 定理 `ext_int`

English:
theorem ext_int
  given: {R : Type*} [NonAssocSemiring R] (f g : Int ->+* R)
  statement: f = g
  proof: coe_addMonoidHom_injective AddMonoidHom.ext_int f.map_one.trans g.map_one.symm

中文:
定理 ext_int
  条件: {R : 类型} [NonAssocSemiring R] (f g : 整数 ->+* R)
  结论: f = g
  证明: coe_addMonoidHom_injective AddMonoidHom.ext_int f.map_one.trans g.map_one.symm

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext_int, coe_addMonoidHom_injective, ext_int, f.map_one.trans, g.map_one.symm, map_one
-/
theorem ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+* R) : f = g :=
coe_addMonoidHom_injective AddMonoidHom.ext_int f.map_one.trans g.map_one.symm

/--
Instance `Int.subsingleton_ringHom` / 实例 `Int.subsingleton_ringHom`

English:
instance Int.subsingleton_ringHom
  signature: {R : Type*} [NonAssocSemiring R]
  body: ⟨RingHom.ext_int⟩

中文:
实例 Int.subsingleton_ringHom
  签名: {R : 类型} [NonAssocSemiring R]
  定义体: ⟨RingHom.ext_int⟩

Depends on / 依赖: RingHom, RingHom.ext_int, ext_int
-/
instance Int.subsingleton_ringHom {R : Type*} [NonAssocSemiring R] : Subsingleton (Int ->+* R) :=
  ⟨RingHom.ext_int⟩

end RingHom

end NonAssocRing

@[simp]
/--
theorem `Int.castRingHom_int` / 定理 `Int.castRingHom_int`

English:
theorem Int.castRingHom_int
  statement: Int.castRingHom Int = RingHom.id Int
  proof: (RingHom.id Int).eq_intCast'.symm

中文:
定理 Int.castRingHom_int
  结论: 整数.castRingHom 整数 = RingHom.id 整数
  证明: (RingHom.id Int).eq_intCast'.symm

Depends on / 依赖: RingHom, RingHom.id, eq_intCast
-/
theorem Int.castRingHom_int : Int.castRingHom Int = RingHom.id Int :=
  (RingHom.id Int).eq_intCast'.symm
