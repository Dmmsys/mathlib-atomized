/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Casts of rational numbers into characteristic zero fields (or division rings).
-/

@[expose] public section

open Function

variable {F ι α β : Type*}

namespace Rat
variable [DivisionRing α] [CharZero α] {p q : Rat}

@[stacks 09FR "Characteristic zero case."]
/--
lemma `cast_injective` / 引理 `cast_injective`

English:
lemma cast_injective
  statement: Injective ((↑) : Rat -> α)
  proof: Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) != 0 := Nat.cast_ne_zero.2 d₂0
    rw [mk_eq_divInt]; rw [mk_eq_divInt] at h ⊢
    rw [cast_divInt_of_ne_zero _ (by simpa)]; rw [cast_divInt_of_ne_zero _ (by simpa)] at h
    norm_cast at h
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.ca

中文:
引理 cast_injective
  结论: 单射 ((↑) : 有理数 -> α)
  证明: Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) != 0 := Nat.cast_ne_zero.2 d₂0
    rw [mk_eq_divInt]; rw [mk_eq_divInt] at h ⊢
    rw [cast_divInt_of_ne_zero _ (by simpa)]; rw [cast_divInt_of_ne_zero _ (by simpa)] at h
    norm_cast at h
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.ca

Depends on / 依赖: Nat.cast_ne_zero, cast_ne_zero
-/
lemma cast_injective : Injective ((↑) : Rat -> α)
  | ⟨n₁, d₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩, h => by
    have d₁a : (d₁ : α) != 0 := Nat.cast_ne_zero.2 d₁0
    have d₂a : (d₂ : α) != 0 := Nat.cast_ne_zero.2 d₂0
    rw [mk_eq_divInt]; rw [mk_eq_divInt] at h ⊢
    rw [cast_divInt_of_ne_zero _ (by simpa)]; rw [cast_divInt_of_ne_zero _ (by simpa)] at h
    norm_cast at h
    rwa [eq_div_iff_mul_eq d₂a, division_def, mul_assoc, (d₁.cast_commute (d₂ : α)).inv_left₀.eq,
      ← mul_assoc, ← division_def, eq_comm, eq_div_iff_mul_eq d₁a, eq_comm, ← Int.cast_natCast d₁,
      ← Int.cast_mul, ← Int.cast_natCast d₂, ← Int.cast_mul, Int.cast_inj, ← mkRat_eq_iff d₁0 d₂0]
      at h

/--
lemma `cast_inj` / 引理 `cast_inj`

English:
lemma cast_inj
  statement: (p : α) = q ↔ p = q
  proof: cast_injective.eq_iff

中文:
引理 cast_inj
  结论: (p : α) = q ↔ p = q
  证明: cast_injective.eq_iff
-/
@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff

/--
lemma `cast_eq_zero` / 引理 `cast_eq_zero`

English:
lemma cast_eq_zero
  statement: (p : α) = 0 ↔ p = 0
  proof: cast_injective.eq_iff' cast_zero

中文:
引理 cast_eq_zero
  结论: (p : α) = 0 ↔ p = 0
  证明: cast_injective.eq_iff' cast_zero
-/
@[simp, norm_cast] lemma cast_eq_zero : (p : α) = 0 ↔ p = 0 := cast_injective.eq_iff' cast_zero
/--
lemma `cast_ne_zero` / 引理 `cast_ne_zero`

English:
lemma cast_ne_zero
  statement: (p : α) != 0 ↔ p != 0
  proof: cast_eq_zero.ne

中文:
引理 cast_ne_zero
  结论: (p : α) != 0 ↔ p != 0
  证明: cast_eq_zero.ne

Depends on / 依赖: cast_eq_zero, cast_eq_zero.ne
-/
lemma cast_ne_zero : (p : α) != 0 ↔ p != 0 := cast_eq_zero.ne

/--
lemma `cast_add` / 引理 `cast_add`

English:
lemma cast_add
  given: (p q : Rat)
  statement: ↑(p + q) = (p + q : α)
  proof: cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

中文:
引理 cast_add
  条件: (p q : 有理数)
  结论: ↑(p + q) = (p + q : α)
  证明: cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')
-/
@[simp, norm_cast] lemma cast_add (p q : Rat) : ↑(p + q) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

/--
lemma `cast_sub` / 引理 `cast_sub`

English:
lemma cast_sub
  given: (p q : Rat)
  statement: ↑(p - q) = (p - q : α)
  proof: cast_sub_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

中文:
引理 cast_sub
  条件: (p q : 有理数)
  结论: ↑(p - q) = (p - q : α)
  证明: cast_sub_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')
-/
@[simp, norm_cast] lemma cast_sub (p q : Rat) : ↑(p - q) = (p - q : α) :=
  cast_sub_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

/--
lemma `cast_mul` / 引理 `cast_mul`

English:
lemma cast_mul
  given: (p q : Rat)
  statement: ↑(p * q) = (p * q : α)
  proof: cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

中文:
引理 cast_mul
  条件: (p q : 有理数)
  结论: ↑(p * q) = (p * q : α)
  证明: cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')
-/
@[simp, norm_cast] lemma cast_mul (p q : Rat) : ↑(p * q) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.pos.ne') (Nat.cast_ne_zero.2 q.pos.ne')

variable (α) in
/--
Definition of `castHom` / `castHom` 的定义

English:
definition castHom
  signature: : Rat ->+* α where
  body: (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

中文:
定义 castHom
  签名: : 有理数 ->+* α where
  定义体: (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add
-/
def castHom : Rat ->+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

/--
lemma `coe_castHom` / 引理 `coe_castHom`

English:
lemma coe_castHom
  statement: ⇑(castHom α) = ((↑) : Rat -> α)
  proof: rfl

中文:
引理 coe_castHom
  结论: ⇑(castHom α) = ((↑) : 有理数 -> α)
  证明: rfl
-/
@[simp] lemma coe_castHom : ⇑(castHom α) = ((↑) : Rat -> α) := rfl

/--
lemma `cast_inv` / 引理 `cast_inv`

English:
lemma cast_inv
  given: (p : Rat)
  statement: ↑(p⁻¹) = (p⁻¹ : α)
  proof: map_inv₀ (castHom α) _

中文:
引理 cast_inv
  条件: (p : 有理数)
  结论: ↑(p⁻¹) = (p⁻¹ : α)
  证明: map_inv₀ (castHom α) _
-/
@[simp, norm_cast] lemma cast_inv (p : Rat) : ↑(p⁻¹) = (p⁻¹ : α) := map_inv₀ (castHom α) _
/--
lemma `cast_div` / 引理 `cast_div`

English:
lemma cast_div
  given: (p q : Rat)
  statement: ↑(p / q) = (p / q : α)
  proof: map_div₀ (castHom α) ..

@[simp, norm_cast]

中文:
引理 cast_div
  条件: (p q : 有理数)
  结论: ↑(p / q) = (p / q : α)
  证明: map_div₀ (castHom α) ..

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma cast_div (p q : Rat) : ↑(p / q) = (p / q : α) := map_div₀ (castHom α) ..

@[simp, norm_cast]
/--
lemma `cast_zpow` / 引理 `cast_zpow`

English:
lemma cast_zpow
  given: (p : Rat) (n : Int)
  statement: ↑(p ^ n) = (p ^ n : α)
  proof: map_zpow₀ (castHom α) ..

@[norm_cast]

中文:
引理 cast_zpow
  条件: (p : 有理数) (n : 整数)
  结论: ↑(p ^ n) = (p ^ n : α)
  证明: map_zpow₀ (castHom α) ..

@[norm_cast]

Depends on / 依赖: castHom
-/
lemma cast_zpow (p : Rat) (n : Int) : ↑(p ^ n) = (p ^ n : α) := map_zpow₀ (castHom α) ..

@[norm_cast]
/--
theorem `cast_divInt` / 定理 `cast_divInt`

English:
theorem cast_divInt
  given: (a b : Int)
  statement: (a /. b : α) = a / b
  proof: by
  simp only [divInt_eq_div, cast_div, cast_intCast]

中文:
定理 cast_div整数
  条件: (a b : 整数)
  结论: (a /. b : α) = a / b
  证明: by
  simp only [divInt_eq_div, cast_div, cast_intCast]

Depends on / 依赖: cast_div, cast_intCast, divInt_eq_div
-/
theorem cast_divInt (a b : Int) : (a /. b : α) = a / b := by
  simp only [divInt_eq_div, cast_div, cast_intCast]

end Rat

namespace NNRat
variable [DivisionSemiring α] [CharZero α] {p q : Rat>=0}

/--
lemma `cast_injective` / 引理 `cast_injective`

English:
lemma cast_injective
  statement: Injective ((↑) : Rat>=0 -> α)
  proof: by
  rintro p q hpq
  rw [NNRat.cast_def]; rw [NNRat.cast_def]; rw [Commute.div_eq_div_iff] at hpq
  on_goal 1 => rw [← p.num_div_den, ← q.num_div_den, div_eq_div_iff]
  · norm_cast at hpq ⊢
  any_goals norm_cast
  any_goals apply den_ne_zero
  exact Nat.cast_commute ..

中文:
引理 cast_injective
  结论: 单射 ((↑) : 有理数>=0 -> α)
  证明: by
  rintro p q hpq
  rw [NNRat.cast_def]; rw [NNRat.cast_def]; rw [Commute.div_eq_div_iff] at hpq
  on_goal 1 => rw [← p.num_div_den, ← q.num_div_den, div_eq_div_iff]
  · norm_cast at hpq ⊢
  any_goals norm_cast
  any_goals apply den_ne_zero
  exact Nat.cast_commute ..

Depends on / 依赖: Commute, Commute.div_eq_div_iff, NNRat.cast_def, Nat.cast_commute, any_goals, cast_commute, cast_def, den_ne_zero, div_eq_div_iff, num_div_den, on_goal, p.num_div_den, q.num_div_den
-/
lemma cast_injective : Injective ((↑) : Rat>=0 -> α) := by
  rintro p q hpq
  rw [NNRat.cast_def]; rw [NNRat.cast_def]; rw [Commute.div_eq_div_iff] at hpq
  on_goal 1 => rw [← p.num_div_den, ← q.num_div_den, div_eq_div_iff]
  · norm_cast at hpq ⊢
  any_goals norm_cast
  any_goals apply den_ne_zero
  exact Nat.cast_commute ..

/--
lemma `cast_inj` / 引理 `cast_inj`

English:
lemma cast_inj
  statement: (p : α) = q ↔ p = q
  proof: cast_injective.eq_iff

中文:
引理 cast_inj
  结论: (p : α) = q ↔ p = q
  证明: cast_injective.eq_iff
-/
@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff

/--
lemma `cast_eq_zero` / 引理 `cast_eq_zero`

English:
lemma cast_eq_zero
  statement: (q : α) = 0 ↔ q = 0
  proof: by rw [← cast_zero, cast_inj]

中文:
引理 cast_eq_zero
  结论: (q : α) = 0 ↔ q = 0
  证明: by rw [← cast_zero, cast_inj]
-/
@[simp, norm_cast] lemma cast_eq_zero : (q : α) = 0 ↔ q = 0 := by rw [← cast_zero, cast_inj]
/--
lemma `cast_ne_zero` / 引理 `cast_ne_zero`

English:
lemma cast_ne_zero
  statement: (q : α) != 0 ↔ q != 0
  proof: cast_eq_zero.not

中文:
引理 cast_ne_zero
  结论: (q : α) != 0 ↔ q != 0
  证明: cast_eq_zero.not

Depends on / 依赖: cast_eq_zero, cast_eq_zero.not
-/
lemma cast_ne_zero : (q : α) != 0 ↔ q != 0 := cast_eq_zero.not

/--
lemma `cast_add` / 引理 `cast_add`

English:
lemma cast_add
  given: (p q : Rat>=0)
  statement: ↑(p + q) = (p + q : α)
  proof: cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

中文:
引理 cast_add
  条件: (p q : 有理数>=0)
  结论: ↑(p + q) = (p + q : α)
  证明: cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')
-/
@[simp, norm_cast] lemma cast_add (p q : Rat>=0) : ↑(p + q) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

/--
lemma `cast_mul` / 引理 `cast_mul`

English:
lemma cast_mul
  given: (p q)
  statement: (p * q : Rat>=0) = (p * q : α)
  proof: cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

中文:
引理 cast_mul
  条件: (p q)
  结论: (p * q : 有理数>=0) = (p * q : α)
  证明: cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')
-/
@[simp, norm_cast] lemma cast_mul (p q) : (p * q : Rat>=0) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

variable (α) in
/--
Definition of `castHom` / `castHom` 的定义

English:
definition castHom
  signature: : Rat>=0 ->+* α where
  body: (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

中文:
定义 castHom
  签名: : 有理数>=0 ->+* α where
  定义体: (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add
-/
def castHom : Rat>=0 ->+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

/--
lemma `coe_castHom` / 引理 `coe_castHom`

English:
lemma coe_castHom
  statement: ⇑(castHom α) = (↑)
  proof: rfl

中文:
引理 coe_castHom
  结论: ⇑(castHom α) = (↑)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_castHom : ⇑(castHom α) = (↑) := rfl

/--
lemma `cast_inv` / 引理 `cast_inv`

English:
lemma cast_inv
  given: (p)
  statement: (p⁻¹ : Rat>=0) = (p : α)⁻¹
  proof: map_inv₀ (castHom α) _

中文:
引理 cast_inv
  条件: (p)
  结论: (p⁻¹ : 有理数>=0) = (p : α)⁻¹
  证明: map_inv₀ (castHom α) _
-/
@[simp, norm_cast] lemma cast_inv (p) : (p⁻¹ : Rat>=0) = (p : α)⁻¹ := map_inv₀ (castHom α) _
/--
lemma `cast_div` / 引理 `cast_div`

English:
lemma cast_div
  given: (p q)
  statement: (p / q : Rat>=0) = (p / q : α)
  proof: map_div₀ (castHom α) ..

@[simp, norm_cast]

中文:
引理 cast_div
  条件: (p q)
  结论: (p / q : 有理数>=0) = (p / q : α)
  证明: map_div₀ (castHom α) ..

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma cast_div (p q) : (p / q : Rat>=0) = (p / q : α) := map_div₀ (castHom α) ..

@[simp, norm_cast]
/--
lemma `cast_zpow` / 引理 `cast_zpow`

English:
lemma cast_zpow
  given: (q : Rat>=0) (p : Int)
  statement: ↑(q ^ p) = ((q : α) ^ p : α)
  proof: map_zpow₀ (castHom α) ..

@[simp]

中文:
引理 cast_zpow
  条件: (q : 有理数>=0) (p : 整数)
  结论: ↑(q ^ p) = ((q : α) ^ p : α)
  证明: map_zpow₀ (castHom α) ..

@[simp]

Depends on / 依赖: castHom
-/
lemma cast_zpow (q : Rat>=0) (p : Int) : ↑(q ^ p) = ((q : α) ^ p : α) := map_zpow₀ (castHom α) ..

@[simp]
/--
lemma `cast_divNat` / 引理 `cast_divNat`

English:
lemma cast_divNat
  given: (a b : Nat)
  statement: (divNat a b : α) = a / b
  proof: by
  rw [← cast_natCast]; rw [← cast_natCast b]; rw [← cast_div]
  congr
  ext
  apply Rat.mkRat_eq_div

中文:
引理 cast_div自然数
  条件: (a b : 自然数)
  结论: (div自然数 a b : α) = a / b
  证明: by
  rw [← cast_natCast]; rw [← cast_natCast b]; rw [← cast_div]
  congr
  ext
  apply Rat.mkRat_eq_div

Depends on / 依赖: Rat.mkRat_eq_div, cast_div, cast_natCast, mkRat_eq_div
-/
lemma cast_divNat (a b : Nat) : (divNat a b : α) = a / b := by
  rw [← cast_natCast]; rw [← cast_natCast b]; rw [← cast_div]
  congr
  ext
  apply Rat.mkRat_eq_div

end NNRat
