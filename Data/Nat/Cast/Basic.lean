/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Divisibility.Hom
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat

/-!
# Cast of natural numbers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`Nat.cast`).

## Main declarations

* `castAddMonoidHom`: `cast` bundled as an `AddMonoidHom`.
* `castRingHom`: `cast` bundled as a `RingHom`.
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Commute.zero_right Commute.add_right abs_eq_max_neg
  NeZero.natCast_ne
-- TODO: `MulOpposite.op_natCast` was not intended to be imported
-- assert_not_exists MulOpposite.op_natCast

open Additive Multiplicative

variable {α β : Type*}

namespace Nat

/--
Definition of `castAddMonoidHom` / `castAddMonoidHom` 的定义

English:
definition castAddMonoidHom
  signature: (α : Type*) [AddMonoidWithOne α]
  body: Nat.cast
  map_add' := cast_add
  map_zero' := cast_zero

@[simp]

中文:
定义 castAddMonoidHom
  签名: (α : 类型) [AddMonoidWithOne α]
  定义体: Nat.cast
  map_add' := cast_add
  map_zero' := cast_zero

@[simp]

Depends on / 依赖: Nat.cast
-/
def castAddMonoidHom (α : Type*) [AddMonoidWithOne α] :
    Nat ->+ α where
  toFun := Nat.cast
  map_add' := cast_add
  map_zero' := cast_zero

@[simp]
/--
theorem `coe_castAddMonoidHom` / 定理 `coe_castAddMonoidHom`

English:
theorem coe_castAddMonoidHom
  given: [AddMonoidWithOne α]
  statement: (castAddMonoidHom α : Nat -> α) = Nat.cast
  proof: rfl

中文:
定理 coe_castAddMonoidHom
  条件: [AddMonoidWithOne α]
  结论: (castAddMonoidHom α : 自然数 -> α) = 自然数.cast
  证明: rfl
-/
theorem coe_castAddMonoidHom [AddMonoidWithOne α] : (castAddMonoidHom α : Nat -> α) = Nat.cast :=
  rfl

/--
lemma `_root_.Even.natCast` / 引理 `_root_.Even.natCast`

English:
lemma _root_.Even.natCast
  given: [AddMonoidWithOne α] {n : Nat} (hn : Even n)
  statement: Even (n : α)
  proof: hn.map Nat.castAddMonoidHom α

中文:
引理 _root_.Even.natCast
  条件: [AddMonoidWithOne α] {n : 自然数} (hn : Even n)
  结论: Even (n : α)
  证明: hn.map Nat.castAddMonoidHom α

Depends on / 依赖: Nat.castAddMonoidHom, castAddMonoidHom, hn.map
-/
lemma _root_.Even.natCast [AddMonoidWithOne α] {n : Nat} (hn : Even n) : Even (n : α) :=
hn.map Nat.castAddMonoidHom α

section NonAssocSemiring
variable [NonAssocSemiring α]

/--
lemma `cast_mul` / 引理 `cast_mul`

English:
lemma cast_mul
  given: (m n : Nat)
  statement: ((m * n : Nat) : α) = m * n
  proof: by
  induction n <;> simp [mul_add, *]

中文:
引理 cast_mul
  条件: (m n : 自然数)
  结论: ((m * n : 自然数) : α) = m * n
  证明: by
  induction n <;> simp [mul_add, *]
-/
@[simp, norm_cast] lemma cast_mul (m n : Nat) : ((m * n : Nat) : α) = m * n := by
  induction n <;> simp [mul_add, *]

variable (α) in
/-- `Nat.cast : ℕ → α` as a `RingHom` -/
@[instance_reducible]
/--
Definition of `castRingHom` / `castRingHom` 的定义

English:
definition castRingHom
  signature: : Nat ->+* α
  body: { castAddMonoidHom α with toFun := Nat.cast, map_one' := cast_one, map_mul' := cast_mul }

中文:
定义 castRingHom
  签名: : 自然数 ->+* α
  定义体: { castAddMonoidHom α with toFun := Nat.cast, map_one' := cast_one, map_mul' := cast_mul }

Depends on / 依赖: Nat.cast, castAddMonoidHom, cast_mul, cast_one, map_mul, map_one
-/
def castRingHom : Nat ->+* α :=
  { castAddMonoidHom α with toFun := Nat.cast, map_one' := cast_one, map_mul' := cast_mul }

/--
lemma `coe_castRingHom` / 引理 `coe_castRingHom`

English:
lemma coe_castRingHom
  statement: (castRingHom α : Nat -> α) = Nat.cast
  proof: rfl

中文:
引理 coe_castRingHom
  结论: (castRingHom α : 自然数 -> α) = 自然数.cast
  证明: rfl
-/
@[simp, norm_cast] lemma coe_castRingHom : (castRingHom α : Nat -> α) = Nat.cast := rfl

/--
lemma `_root_.nsmul_eq_mul'` / 引理 `_root_.nsmul_eq_mul'`

English:
lemma _root_.nsmul_eq_mul'
  given: (a : α) (n : Nat)
  statement: n • a = a * n
  proof: by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, mul_zero]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, mul_add, mul_one]

中文:
引理 _root_.nsmul_eq_mul'
  条件: (a : α) (n : 自然数)
  结论: n • a = a * n
  证明: by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, mul_zero]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, mul_add, mul_one]

Depends on / 依赖: Nat.cast_succ, Nat.cast_zero, cast_succ, cast_zero, mul_add, mul_one, mul_zero, succ_nsmul, zero_nsmul
-/
lemma _root_.nsmul_eq_mul' (a : α) (n : Nat) : n • a = a * n := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, mul_zero]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, mul_add, mul_one]

/--
lemma `ofNat_nsmul_eq_mul` / 引理 `ofNat_nsmul_eq_mul`

English:
lemma ofNat_nsmul_eq_mul
  given: (n : Nat) [n.AtLeastTwo] (a : α)
  statement: ofNat(n) • a = ofNat(n) * a
  proof: by
  simp [nsmul_eq_mul]

中文:
引理 ofNat_nsmul_eq_mul
  条件: (n : 自然数) [n.AtLeastTwo] (a : α)
  结论: of自然数(n) • a = of自然数(n) * a
  证明: by
  simp [nsmul_eq_mul]

Depends on / 依赖: nsmul_eq_mul
-/
lemma ofNat_nsmul_eq_mul (n : Nat) [n.AtLeastTwo] (a : α) : ofNat(n) • a = ofNat(n) * a := by
  simp [nsmul_eq_mul]

end NonAssocSemiring

section Semiring
variable [Semiring α] {m n : Nat}

@[simp, norm_cast]
/--
lemma `cast_pow` / 引理 `cast_pow`

English:
lemma cast_pow
  given: (m : Nat)
  statement: forall n : Nat, ↑(m ^ n) = (m ^ n : α)

中文:
引理 cast_pow
  条件: (m : 自然数)
  结论: 对任意 n : 自然数, ↑(m ^ n) = (m ^ n : α)
-/
lemma cast_pow (m : Nat) : forall n : Nat, ↑(m ^ n) = (m ^ n : α)
  | 0 => by simp
  | n + 1 => by rw [_root_.pow_succ', _root_.pow_succ', cast_mul, cast_pow m n]

@[gcongr]
/--
lemma `cast_dvd_cast` / 引理 `cast_dvd_cast`

English:
lemma cast_dvd_cast
  given: (h : m ∣ n)
  statement: (m : α) ∣ (n : α)
  proof: map_dvd (Nat.castRingHom α) h

alias _root_.Dvd.dvd.natCast := cast_dvd_cast

中文:
引理 cast_dvd_cast
  条件: (h : m ∣ n)
  结论: (m : α) ∣ (n : α)
  证明: map_dvd (Nat.castRingHom α) h

alias _root_.Dvd.dvd.natCast := cast_dvd_cast

Depends on / 依赖: Nat.castRingHom, castRingHom, map_dvd
-/
lemma cast_dvd_cast (h : m ∣ n) : (m : α) ∣ (n : α) := map_dvd (Nat.castRingHom α) h

alias _root_.Dvd.dvd.natCast := cast_dvd_cast

end Semiring
end Nat

section AddMonoidHomClass

variable {A B F : Type*} [AddMonoidWithOne B] [FunLike F Nat A] [AddMonoidWithOne A]

-- these versions are primed so that the `RingHomClass` versions aren't
/--
theorem `eq_natCast'` / 定理 `eq_natCast'`

English:
theorem eq_natCast'
  given: [AddMonoidHomClass F Nat A] (f : F) (h1 : f 1 = 1)
  statement: forall n : Nat, f n = n

中文:
定理 eq_natCast'
  条件: [AddMonoidHomClass F 自然数 A] (f : F) (h1 : f 1 = 1)
  结论: 对任意 n : 自然数, f n = n
-/
theorem eq_natCast' [AddMonoidHomClass F Nat A] (f : F) (h1 : f 1 = 1) : forall n : Nat, f n = n
  | 0 => by simp
  | n + 1 => by rw [map_add, h1, eq_natCast' f h1 n, Nat.cast_add_one]

/--
theorem `map_natCast'` / 定理 `map_natCast'`

English:
theorem map_natCast'
  statement: {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
  proof: eq_natCast' ((f : A ->+ B).comp <| Nat.castAddMonoidHom _) (by simpa)

中文:
定理 map_natCast'
  结论: {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
  证明: eq_natCast' ((f : A ->+ B).comp <| Nat.castAddMonoidHom _) (by simpa)

Depends on / 依赖: Nat.castAddMonoidHom, castAddMonoidHom, eq_natCast
-/
theorem map_natCast' {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
    (f : F) (h : f 1 = 1) :
    forall n : Nat, f n = n :=
  eq_natCast' ((f : A ->+ B).comp <| Nat.castAddMonoidHom _) (by simpa)

/--
theorem `map_ofNat'` / 定理 `map_ofNat'`

English:
theorem map_ofNat'
  statement: {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
  proof: map_natCast' f h n

中文:
定理 map_ofNat'
  结论: {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
  证明: map_natCast' f h n

Depends on / 依赖: map_natCast
-/
theorem map_ofNat' {A} [AddMonoidWithOne A] [FunLike F A B] [AddMonoidHomClass F A B]
    (f : F) (h : f 1 = 1) (n : Nat) [n.AtLeastTwo] : f (OfNat.ofNat n) = OfNat.ofNat n :=
  map_natCast' f h n

end AddMonoidHomClass

section MonoidWithZeroHomClass

variable {A F : Type*} [MulZeroOneClass A] [FunLike F Nat A]

/--
theorem `ext_nat''` / 定理 `ext_nat''`

English:
theorem ext_nat''
  given: [ZeroHomClass F Nat A] (f g : F) (h_pos : forall {n : Nat}, 0 < n -> f n = g n)
  proof: by
  apply DFunLike.ext
  rintro (_ | n)
  · simp
  · exact h_pos n.succ_pos

@[ext]

中文:
定理 ext_nat''
  条件: [ZeroHomClass F 自然数 A] (f g : F) (h_pos : 对任意 {n : 自然数}, 0 < n -> f n = g n)
  证明: by
  apply DFunLike.ext
  rintro (_ | n)
  · simp
  · exact h_pos n.succ_pos

@[ext]

Depends on / 依赖: DFunLike, DFunLike.ext, h_pos, n.succ_pos, succ_pos
-/
theorem ext_nat'' [ZeroHomClass F Nat A] (f g : F) (h_pos : forall {n : Nat}, 0 < n -> f n = g n) :
    f = g := by
  apply DFunLike.ext
  rintro (_ | n)
  · simp
  · exact h_pos n.succ_pos

@[ext]
/--
theorem `MonoidWithZeroHom.ext_nat` / 定理 `MonoidWithZeroHom.ext_nat`

English:
theorem MonoidWithZeroHom.ext_nat
  given: {f g : Nat ->*₀ A}
  statement: (forall {n : Nat}, 0 < n -> f n = g n) -> f = g
  proof: ext_nat'' f g

中文:
定理 MonoidWithZeroHom.ext_nat
  条件: {f g : 自然数 ->*₀ A}
  结论: (对任意 {n : 自然数}, 0 < n -> f n = g n) -> f = g
  证明: ext_nat'' f g

Depends on / 依赖: ext_nat
-/
theorem MonoidWithZeroHom.ext_nat {f g : Nat ->*₀ A} : (forall {n : Nat}, 0 < n -> f n = g n) -> f = g :=
  ext_nat'' f g

end MonoidWithZeroHomClass

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

@[simp]
/--
theorem `eq_natCast` / 定理 `eq_natCast`

English:
theorem eq_natCast
  given: [FunLike F Nat R] [RingHomClass F Nat R] (f : F)
  statement: forall n, f n = n
  proof: eq_natCast' f map_one f

@[simp]

中文:
定理 eq_natCast
  条件: [FunLike F 自然数 R] [RingHomClass F 自然数 R] (f : F)
  结论: 对任意 n, f n = n
  证明: eq_natCast' f map_one f

@[simp]

Depends on / 依赖: eq_natCast, map_one
-/
theorem eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) : forall n, f n = n :=
eq_natCast' f map_one f

@[simp]
/--
theorem `map_natCast` / 定理 `map_natCast`

English:
theorem map_natCast
  given: [FunLike F R S] [RingHomClass F R S] (f : F)
  statement: forall n : Nat, f (n : R) = n
  proof: map_natCast' f map_one f

中文:
定理 map_natCast
  条件: [FunLike F R S] [RingHomClass F R S] (f : F)
  结论: 对任意 n : 自然数, f (n : R) = n
  证明: map_natCast' f map_one f

Depends on / 依赖: map_natCast, map_one
-/
theorem map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : forall n : Nat, f (n : R) = n :=
map_natCast' f map_one f

/--
theorem `map_ofNat` / 定理 `map_ofNat`

English:
theorem map_ofNat
  given: [FunLike F R S] [RingHomClass F R S] (f : F) (n : Nat) [Nat.AtLeastTwo n]
  proof: map_natCast f n

中文:
定理 map_ofNat
  条件: [FunLike F R S] [RingHomClass F R S] (f : F) (n : 自然数) [自然数.AtLeastTwo n]
  证明: map_natCast f n

Depends on / 依赖: map_natCast
-/
theorem map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : Nat) [Nat.AtLeastTwo n] :
    (f ofNat(n) : S) = OfNat.ofNat n :=
  map_natCast f n

/--
theorem `ext_nat` / 定理 `ext_nat`

English:
theorem ext_nat
  given: [FunLike F Nat R] [RingHomClass F Nat R] (f g : F)
  statement: f = g
  proof: ext_nat' f g by simp

中文:
定理 ext_nat
  条件: [FunLike F 自然数 R] [RingHomClass F 自然数 R] (f g : F)
  结论: f = g
  证明: ext_nat' f g by simp

Depends on / 依赖: ext_nat
-/
theorem ext_nat [FunLike F Nat R] [RingHomClass F Nat R] (f g : F) : f = g :=
ext_nat' f g by simp

/--
theorem `NeZero.nat_of_neZero` / 定理 `NeZero.nat_of_neZero`

English:
theorem NeZero.nat_of_neZero
  statement: {R S} [NonAssocSemiring R] [NonAssocSemiring S]
  proof: .of_map (f := f) (neZero := by simp only [map_natCast, hn])

中文:
定理 NeZero.nat_of_neZero
  结论: {R S} [NonAssocSemiring R] [NonAssocSemiring S]
  证明: .of_map (f := f) (neZero := by simp only [map_natCast, hn])

Depends on / 依赖: map_natCast, neZero, of_map
-/
theorem NeZero.nat_of_neZero {R S} [NonAssocSemiring R] [NonAssocSemiring S]
    {F} [FunLike F R S] [RingHomClass F R S] (f : F)
    {n : Nat} [hn : NeZero (n : S)] : NeZero (n : R) :=
  .of_map (f := f) (neZero := by simp only [map_natCast, hn])

end RingHomClass

namespace RingHom

/--
theorem `eq_natCast'` / 定理 `eq_natCast'`

English:
theorem eq_natCast'
  given: {R} [NonAssocSemiring R] (f : Nat ->+* R)
  statement: f = Nat.castRingHom R
  proof: RingHom.ext eq_natCast f

中文:
定理 eq_natCast'
  条件: {R} [NonAssocSemiring R] (f : 自然数 ->+* R)
  结论: f = 自然数.castRingHom R
  证明: RingHom.ext eq_natCast f

Depends on / 依赖: RingHom, RingHom.ext, eq_natCast
-/
theorem eq_natCast' {R} [NonAssocSemiring R] (f : Nat ->+* R) : f = Nat.castRingHom R :=
RingHom.ext eq_natCast f

end RingHom

@[simp, norm_cast]
/--
theorem `Nat.cast_id` / 定理 `Nat.cast_id`

English:
theorem Nat.cast_id
  given: (n : Nat)
  statement: n.cast = n
  proof: rfl

@[simp]

中文:
定理 Nat.cast_id
  条件: (n : 自然数)
  结论: n.cast = n
  证明: rfl

@[simp]
-/
theorem Nat.cast_id (n : Nat) : n.cast = n :=
  rfl

@[simp]
/--
theorem `Nat.castRingHom_nat` / 定理 `Nat.castRingHom_nat`

English:
theorem Nat.castRingHom_nat
  statement: Nat.castRingHom Nat = RingHom.id Nat
  proof: rfl

中文:
定理 Nat.castRingHom_nat
  结论: 自然数.castRingHom 自然数 = RingHom.id 自然数
  证明: rfl
-/
theorem Nat.castRingHom_nat : Nat.castRingHom Nat = RingHom.id Nat :=
  rfl

/--
Instance `Nat.uniqueRingHom` / 实例 `Nat.uniqueRingHom`

English:
instance Nat.uniqueRingHom
  signature: {R : Type*} [NonAssocSemiring R]
  body: Nat.castRingHom R
  uniq := RingHom.eq_natCast'

中文:
实例 Nat.uniqueRingHom
  签名: {R : 类型} [NonAssocSemiring R]
  定义体: Nat.castRingHom R
  uniq := RingHom.eq_natCast'

Depends on / 依赖: Nat.castRingHom, castRingHom
-/
instance Nat.uniqueRingHom {R : Type*} [NonAssocSemiring R] : Unique (Nat ->+* R) where
  default := Nat.castRingHom R
  uniq := RingHom.eq_natCast'

namespace Pi

variable {π : α -> Type*}

section NatCast
variable [forall a, NatCast (π a)]

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: : NatCast (forall a, π a) where natCast n _
  body: n

@[simp]

中文:
实例 instNatCast
  签名: : 自然数Cast (对任意 a, π a) where natCast n _
  定义体: n

@[simp]
-/
instance instNatCast : NatCast (forall a, π a) where natCast n _ := n

@[simp]
/--
theorem `natCast_apply` / 定理 `natCast_apply`

English:
theorem natCast_apply
  given: (n : Nat) (a : α)
  statement: (n : forall a, π a) a = n
  proof: rfl

@[push ←]

中文:
定理 natCast_apply
  条件: (n : 自然数) (a : α)
  结论: (n : 对任意 a, π a) a = n
  证明: rfl

@[push ←]
-/
theorem natCast_apply (n : Nat) (a : α) : (n : forall a, π a) a = n :=
  rfl

@[push ←]
/--
theorem `natCast_def` / 定理 `natCast_def`

English:
theorem natCast_def
  given: (n : Nat)
  statement: (n : forall a, π a) = fun _ => ↑n
  proof: rfl

中文:
定理 natCast_def
  条件: (n : 自然数)
  结论: (n : 对任意 a, π a) = fun _ => ↑n
  证明: rfl
-/
theorem natCast_def (n : Nat) : (n : forall a, π a) = fun _ => ↑n :=
  rfl

end NatCast

section OfNat

-- This instance is low priority, as `to_additive` only works with the one that comes from `One`
-- and `Zero`.
instance (priority := low) instOfNat (n : Nat) [forall i, OfNat (π i) n] : OfNat ((i : α) -> π i) n where
  ofNat _ := OfNat.ofNat n

@[simp]
/--
theorem `ofNat_apply` / 定理 `ofNat_apply`

English:
theorem ofNat_apply
  given: (n : Nat) [forall i, OfNat (π i) n] (a : α)
  statement: (ofNat(n) : forall a, π a) a = ofNat(n)
  proof: rfl

@[push ←]

中文:
定理 ofNat_apply
  条件: (n : 自然数) [对任意 i, Of自然数 (π i) n] (a : α)
  结论: (of自然数(n) : 对任意 a, π a) a = of自然数(n)
  证明: rfl

@[push ←]
-/
theorem ofNat_apply (n : Nat) [forall i, OfNat (π i) n] (a : α) : (ofNat(n) : forall a, π a) a = ofNat(n) := rfl

@[push ←]
/--
lemma `ofNat_def` / 引理 `ofNat_def`

English:
lemma ofNat_def
  given: (n : Nat) [forall i, OfNat (π i) n]
  statement: (OfNat.ofNat n : forall a, π a) = fun _ => ofNat(n)
  proof: rfl

中文:
引理 ofNat_def
  条件: (n : 自然数) [对任意 i, Of自然数 (π i) n]
  结论: (Of自然数.of自然数 n : 对任意 a, π a) = fun _ => of自然数(n)
  证明: rfl
-/
lemma ofNat_def (n : Nat) [forall i, OfNat (π i) n] : (OfNat.ofNat n : forall a, π a) = fun _ => ofNat(n) := rfl

end OfNat

end Pi

/--
theorem `Sum.elim_natCast_natCast` / 定理 `Sum.elim_natCast_natCast`

English:
theorem Sum.elim_natCast_natCast
  given: {α β γ : Type*} [NatCast γ] (n : Nat)
  proof: Sum.elim_lam_const_lam_const (γ := γ) n

中文:
定理 Sum.elim_natCast_natCast
  条件: {α β γ : 类型} [自然数Cast γ] (n : 自然数)
  证明: Sum.elim_lam_const_lam_const (γ := γ) n

Depends on / 依赖: Sum.elim_lam_const_lam_const, elim_lam_const_lam_const
-/
theorem Sum.elim_natCast_natCast {α β γ : Type*} [NatCast γ] (n : Nat) :
    Sum.elim (n : α -> γ) (n : β -> γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
