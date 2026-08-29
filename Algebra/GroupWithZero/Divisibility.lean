/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Data.Nat.Basic

/-!
# Divisibility in groups with zero.

Lemmas about divisibility in groups and monoids with zero.

-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

variable {α : Type*}

section SemigroupWithZero

variable [SemigroupWithZero α] {a : α}

/--
theorem `eq_zero_of_zero_dvd` / 定理 `eq_zero_of_zero_dvd`

English:
theorem eq_zero_of_zero_dvd
  given: (h : 0 ∣ a)
  statement: a = 0
  proof: Dvd.elim h fun c H' => H'.trans (zero_mul c)

中文:
定理 eq_zero_of_zero_dvd
  条件: (h : 0 ∣ a)
  结论: a = 0
  证明: Dvd.elim h fun c H' => H'.trans (zero_mul c)

Depends on / 依赖: Dvd.elim, zero_mul
-/
theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
  Dvd.elim h fun c H' => H'.trans (zero_mul c)

/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
product with zero equals `a` iff `a` equals zero. -/
@[simp]
/--
theorem `zero_dvd_iff` / 定理 `zero_dvd_iff`

English:
theorem zero_dvd_iff
  statement: 0 ∣ a ↔ a = 0
  proof: ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    exact ⟨0, by simp⟩⟩

@[simp]

中文:
定理 zero_dvd_iff
  结论: 0 ∣ a ↔ a = 0
  证明: ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    exact ⟨0, by simp⟩⟩

@[simp]

Depends on / 依赖: eq_zero_of_zero_dvd
-/
theorem zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
  ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    exact ⟨0, by simp⟩⟩

@[simp]
/--
theorem `dvd_zero` / 定理 `dvd_zero`

English:
theorem dvd_zero
  given: (a : α)
  statement: a ∣ 0
  proof: Dvd.intro 0 (by simp)

中文:
定理 dvd_zero
  条件: (a : α)
  结论: a ∣ 0
  证明: Dvd.intro 0 (by simp)

Depends on / 依赖: Dvd.intro
-/
theorem dvd_zero (a : α) : a ∣ 0 :=
  Dvd.intro 0 (by simp)

end SemigroupWithZero

/--
theorem `mul_dvd_mul_iff_left` / 定理 `mul_dvd_mul_iff_left`

English:
theorem mul_dvd_mul_iff_left
  given: [MonoidWithZero α] [IsLeftCancelMulZero α] {a b c : α} (ha : a != 0)
  proof: exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha]

中文:
定理 mul_dvd_mul_iff_left
  条件: [带零幺半群 α] [是左消去MulZero α] {a b c : α} (ha : a != 0)
  证明: exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha]

Depends on / 依赖: exists_congr, mul_assoc, mul_right_inj
-/
theorem mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCancelMulZero α] {a b c : α} (ha : a != 0) :
    a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha]

/--
theorem `mul_dvd_mul_iff_right` / 定理 `mul_dvd_mul_iff_right`

English:
theorem mul_dvd_mul_iff_right
  given: [CommMonoidWithZero α] [IsCancelMulZero α] {a b c : α} (hc : c != 0)
  proof: exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc]

中文:
定理 mul_dvd_mul_iff_right
  条件: [带零交换幺半群 α] [是乘零消去 α] {a b c : α} (hc : c != 0)
  证明: exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc]

Depends on / 依赖: exists_congr, mul_left_inj, mul_right_comm
-/
theorem mul_dvd_mul_iff_right [CommMonoidWithZero α] [IsCancelMulZero α] {a b c : α} (hc : c != 0) :
    a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc]

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/--
Definition of `DvdNotUnit` / `DvdNotUnit` 的定义

English:
definition DvdNotUnit
  signature: (a b : α)
  body: a != 0 ∧ exists x, ¬IsUnit x ∧ b = a * x

中文:
定义 DvdNotUnit
  签名: (a b : α)
  定义体: a != 0 ∧ exists x, ¬IsUnit x ∧ b = a * x

Depends on / 依赖: IsUnit
-/
def DvdNotUnit (a b : α) : Prop :=
  a != 0 ∧ exists x, ¬IsUnit x ∧ b = a * x

/--
theorem `dvdNotUnit_of_dvd_of_not_dvd` / 定理 `dvdNotUnit_of_dvd_of_not_dvd`

English:
theorem dvdNotUnit_of_dvd_of_not_dvd
  given: {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a)
  statement: DvdNotUnit a b
  proof: by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
  · rcases hd with ⟨c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    rintro ⟨u, rfl⟩
    simp at hnd

中文:
定理 dvdNotUnit_of_dvd_of_not_dvd
  条件: {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a)
  结论: DvdNotUnit a b
  证明: by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
  · rcases hd with ⟨c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    rintro ⟨u, rfl⟩
    simp at hnd

Depends on / 依赖: dvd_zero
-/
theorem dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
  · rcases hd with ⟨c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    rintro ⟨u, rfl⟩
    simp at hnd

variable {x y : α}

/--
theorem `isRelPrime_zero_left` / 定理 `isRelPrime_zero_left`

English:
theorem isRelPrime_zero_left
  statement: IsRelPrime 0 x ↔ IsUnit x
  proof: ⟨(· (dvd_zero _) dvd_rfl), IsUnit.isRelPrime_right⟩

中文:
定理 isRelPrime_zero_left
  结论: IsRelPrime 0 x ↔ 是单位 x
  证明: ⟨(· (dvd_zero _) dvd_rfl), IsUnit.isRelPrime_right⟩

Depends on / 依赖: IsUnit, IsUnit.isRelPrime_right, dvd_rfl, dvd_zero, isRelPrime_right
-/
theorem isRelPrime_zero_left : IsRelPrime 0 x ↔ IsUnit x :=
  ⟨(· (dvd_zero _) dvd_rfl), IsUnit.isRelPrime_right⟩

/--
theorem `isRelPrime_zero_right` / 定理 `isRelPrime_zero_right`

English:
theorem isRelPrime_zero_right
  statement: IsRelPrime x 0 ↔ IsUnit x
  proof: isRelPrime_comm.trans isRelPrime_zero_left

中文:
定理 isRelPrime_zero_right
  结论: IsRelPrime x 0 ↔ 是单位 x
  证明: isRelPrime_comm.trans isRelPrime_zero_left

Depends on / 依赖: isRelPrime_comm, isRelPrime_comm.trans, isRelPrime_zero_left
-/
theorem isRelPrime_zero_right : IsRelPrime x 0 ↔ IsUnit x :=
  isRelPrime_comm.trans isRelPrime_zero_left

/--
theorem `not_isRelPrime_zero_zero` / 定理 `not_isRelPrime_zero_zero`

English:
theorem not_isRelPrime_zero_zero
  given: [Nontrivial α]
  statement: ¬IsRelPrime (0 : α) 0
  proof: mt isRelPrime_zero_right.mp not_isUnit_zero

中文:
定理 not_isRelPrime_zero_zero
  条件: [非平凡 α]
  结论: ¬IsRelPrime (0 : α) 0
  证明: mt isRelPrime_zero_right.mp not_isUnit_zero

Depends on / 依赖: isRelPrime_zero_right, isRelPrime_zero_right.mp, not_isUnit_zero
-/
theorem not_isRelPrime_zero_zero [Nontrivial α] : ¬IsRelPrime (0 : α) 0 :=
  mt isRelPrime_zero_right.mp not_isUnit_zero

/--
theorem `IsRelPrime.ne_zero_or_ne_zero` / 定理 `IsRelPrime.ne_zero_or_ne_zero`

English:
theorem IsRelPrime.ne_zero_or_ne_zero
  given: [Nontrivial α] (h : IsRelPrime x y)
  statement: x != 0 ∨ y != 0
  proof: not_or_of_imp by rintro rfl rfl; exact not_isRelPrime_zero_zero h

中文:
定理 IsRelPrime.ne_zero_or_ne_zero
  条件: [非平凡 α] (h : IsRelPrime x y)
  结论: x != 0 ∨ y != 0
  证明: not_or_of_imp by rintro rfl rfl; exact not_isRelPrime_zero_zero h

Depends on / 依赖: not_isRelPrime_zero_zero, not_or_of_imp
-/
theorem IsRelPrime.ne_zero_or_ne_zero [Nontrivial α] (h : IsRelPrime x y) : x != 0 ∨ y != 0 :=
not_or_of_imp by rintro rfl rfl; exact not_isRelPrime_zero_zero h

end CommMonoidWithZero

/--
theorem `isRelPrime_of_no_nonunits_factors` / 定理 `isRelPrime_of_no_nonunits_factors`

English:
theorem isRelPrime_of_no_nonunits_factors
  statement: [MonoidWithZero α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
  proof: by
  refine fun z hx hy => by_contra fun h => H z h ?_ hx hy
  rintro rfl; exact nonzero ⟨zero_dvd_iff.1 hx, zero_dvd_iff.1 hy⟩

中文:
定理 isRelPrime_of_no_nonunits_factors
  结论: [带零幺半群 α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
  证明: by
  refine fun z hx hy => by_contra fun h => H z h ?_ hx hy
  rintro rfl; exact nonzero ⟨zero_dvd_iff.1 hx, zero_dvd_iff.1 hy⟩

Depends on / 依赖: nonzero, zero_dvd_iff
-/
theorem isRelPrime_of_no_nonunits_factors [MonoidWithZero α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : forall z, ¬ IsUnit z -> z != 0 -> z ∣ x -> ¬z ∣ y) : IsRelPrime x y := by
  refine fun z hx hy => by_contra fun h => H z h ?_ hx hy
  rintro rfl; exact nonzero ⟨zero_dvd_iff.1 hx, zero_dvd_iff.1 hy⟩

/--
theorem `dvd_and_not_dvd_iff` / 定理 `dvd_and_not_dvd_iff`

English:
theorem dvd_and_not_dvd_iff
  given: [CommMonoidWithZero α] [IsCancelMulZero α] {x y : α}
  proof: ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by simp [hx0] at hyx,
      ⟨d, mt isUnit_iff_dvd_one.1 fun ⟨e, he⟩ => hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one
⟨e, mul_left_cancel₀ hx0 by conv

中文:
定理 dvd_and_not_dvd_iff
  条件: [带零交换幺半群 α] [是乘零消去 α] {x y : α}
  证明: ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by simp [hx0] at hyx,
      ⟨d, mt isUnit_iff_dvd_one.1 fun ⟨e, he⟩ => hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one
⟨e, mul_left_cancel₀ hx0 by conv

Depends on / 依赖: isUnit_iff_dvd_one, isUnit_of_dvd_one, mul_assoc, mul_one
-/
theorem dvd_and_not_dvd_iff [CommMonoidWithZero α] [IsCancelMulZero α] {x y : α} :
    x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by simp [hx0] at hyx,
      ⟨d, mt isUnit_iff_dvd_one.1 fun ⟨e, he⟩ => hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one
⟨e, mul_left_cancel₀ hx0 by conv =>
            lhs
            rw [he]; rw [hdx]
            simp [mul_assoc]⟩)⟩⟩

section MonoidWithZero

variable [MonoidWithZero α]

/--
theorem `ne_zero_of_dvd_ne_zero` / 定理 `ne_zero_of_dvd_ne_zero`

English:
theorem ne_zero_of_dvd_ne_zero
  given: {p q : α} (h₁ : q != 0) (h₂ : p ∣ q)
  statement: p != 0
  proof: by
  rcases h₂ with ⟨u, rfl⟩
  exact left_ne_zero_of_mul h₁

中文:
定理 ne_zero_of_dvd_ne_zero
  条件: {p q : α} (h₁ : q != 0) (h₂ : p ∣ q)
  结论: p != 0
  证明: by
  rcases h₂ with ⟨u, rfl⟩
  exact left_ne_zero_of_mul h₁

Depends on / 依赖: left_ne_zero_of_mul
-/
theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (h₂ : p ∣ q) : p != 0 := by
  rcases h₂ with ⟨u, rfl⟩
  exact left_ne_zero_of_mul h₁

/--
theorem `isPrimal_zero` / 定理 `isPrimal_zero`

English:
theorem isPrimal_zero
  statement: IsPrimal (0 : α)
  proof: fun a b h => ⟨a, b, dvd_rfl, dvd_rfl, (zero_dvd_iff.mp h).symm⟩

中文:
定理 isPrimal_zero
  结论: IsPrimal (0 : α)
  证明: fun a b h => ⟨a, b, dvd_rfl, dvd_rfl, (zero_dvd_iff.mp h).symm⟩

Depends on / 依赖: dvd_rfl, zero_dvd_iff, zero_dvd_iff.mp
-/
theorem isPrimal_zero : IsPrimal (0 : α) :=
  fun a b h => ⟨a, b, dvd_rfl, dvd_rfl, (zero_dvd_iff.mp h).symm⟩

/--
theorem `IsPrimal.mul` / 定理 `IsPrimal.mul`

English:
theorem IsPrimal.mul
  statement: {α} [CommMonoidWithZero α] [IsCancelMulZero α] {m n : α}
  proof: by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm]; rw [mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_d

中文:
定理 IsPrimal.mul
  结论: {α} [带零交换幺半群 α] [是乘零消去 α] {m n : α}
  证明: by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm]; rw [mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_d

Depends on / 依赖: dvd_of_mul_right_dvd, eq_or_ne, mul_dvd_mul_iff_left, mul_dvd_mul_left, mul_mul_mul_comm, zero_mul
-/
theorem IsPrimal.mul {α} [CommMonoidWithZero α] [IsCancelMulZero α] {m n : α}
    (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n) := by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm]; rw [mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_dvd_mul_left _ h₂, mul_mul_mul_comm _ _ _ _⟩

end MonoidWithZero

section CancelCommMonoidWithZero

variable [CommMonoidWithZero α] [IsCancelMulZero α] {a b : α} {m n : Nat}

section Subsingleton
variable [Subsingleton αˣ]

/--
theorem `dvd_antisymm` / 定理 `dvd_antisymm`

English:
theorem dvd_antisymm
  statement: a ∣ b -> b ∣ a -> a = b
  proof: by
  rintro ⟨c, rfl⟩ ⟨d, hcd⟩
  rw [mul_assoc]; rw [eq_comm]; rw [mul_right_eq_self₀]; rw [mul_eq_one] at hcd
  obtain ⟨rfl, -⟩ | rfl := hcd <;> simp

中文:
定理 dvd_antisymm
  结论: a ∣ b -> b ∣ a -> a = b
  证明: by
  rintro ⟨c, rfl⟩ ⟨d, hcd⟩
  rw [mul_assoc]; rw [eq_comm]; rw [mul_right_eq_self₀]; rw [mul_eq_one] at hcd
  obtain ⟨rfl, -⟩ | rfl := hcd <;> simp

Depends on / 依赖: eq_comm, mul_assoc, mul_eq_one
-/
theorem dvd_antisymm : a ∣ b -> b ∣ a -> a = b := by
  rintro ⟨c, rfl⟩ ⟨d, hcd⟩
  rw [mul_assoc]; rw [eq_comm]; rw [mul_right_eq_self₀]; rw [mul_eq_one] at hcd
  obtain ⟨rfl, -⟩ | rfl := hcd <;> simp

/--
theorem `dvd_antisymm'` / 定理 `dvd_antisymm'`

English:
theorem dvd_antisymm'
  statement: a ∣ b -> b ∣ a -> b = a
  proof: flip dvd_antisymm

alias Dvd.dvd.antisymm := dvd_antisymm

alias Dvd.dvd.antisymm' := dvd_antisymm'

中文:
定理 dvd_antisymm'
  结论: a ∣ b -> b ∣ a -> b = a
  证明: flip dvd_antisymm

alias Dvd.dvd.antisymm := dvd_antisymm

alias Dvd.dvd.antisymm' := dvd_antisymm'

Depends on / 依赖: dvd_antisymm
-/
theorem dvd_antisymm' : a ∣ b -> b ∣ a -> b = a :=
  flip dvd_antisymm

alias Dvd.dvd.antisymm := dvd_antisymm

alias Dvd.dvd.antisymm' := dvd_antisymm'

/--
theorem `eq_of_forall_dvd` / 定理 `eq_of_forall_dvd`

English:
theorem eq_of_forall_dvd
  given: (h : forall c, a ∣ c ↔ b ∣ c)
  statement: a = b
  proof: ((h _).2 dvd_rfl).antisymm (h _).1 dvd_rfl

中文:
定理 eq_of_对任意_dvd
  条件: (h : 对任意 c, a ∣ c ↔ b ∣ c)
  结论: a = b
  证明: ((h _).2 dvd_rfl).antisymm (h _).1 dvd_rfl

Depends on / 依赖: antisymm, dvd_rfl
-/
theorem eq_of_forall_dvd (h : forall c, a ∣ c ↔ b ∣ c) : a = b :=
((h _).2 dvd_rfl).antisymm (h _).1 dvd_rfl

/--
theorem `eq_of_forall_dvd'` / 定理 `eq_of_forall_dvd'`

English:
theorem eq_of_forall_dvd'
  given: (h : forall c, c ∣ a ↔ c ∣ b)
  statement: a = b
  proof: ((h _).1 dvd_rfl).antisymm (h _).2 dvd_rfl

中文:
定理 eq_of_对任意_dvd'
  条件: (h : 对任意 c, c ∣ a ↔ c ∣ b)
  结论: a = b
  证明: ((h _).1 dvd_rfl).antisymm (h _).2 dvd_rfl

Depends on / 依赖: antisymm, dvd_rfl
-/
theorem eq_of_forall_dvd' (h : forall c, c ∣ a ↔ c ∣ b) : a = b :=
((h _).1 dvd_rfl).antisymm (h _).2 dvd_rfl

end Subsingleton

/--
lemma `pow_dvd_pow_iff` / 引理 `pow_dvd_pow_iff`

English:
lemma pow_dvd_pow_iff
  given: (ha₀ : a != 0) (ha : ¬IsUnit a)
  statement: a ^ n ∣ a ^ m ↔ n <= m
  proof: by
  constructor
  · intro h
    rw [← not_lt]
    intro hmn
    apply ha
    have : a ^ m * a ∣ a ^ m * 1 := by
      rw [← pow_succ]; rw [mul_one]
      exact (pow_dvd_pow _ (Nat.succ_le_of_lt hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← isUnit_iff_dvd_one] at this
    apply pow_ne_zero m ha₀
  

中文:
引理 pow_dvd_pow_iff
  条件: (ha₀ : a != 0) (ha : ¬是单位 a)
  结论: a ^ n ∣ a ^ m ↔ n <= m
  证明: by
  constructor
  · intro h
    rw [← not_lt]
    intro hmn
    apply ha
    have : a ^ m * a ∣ a ^ m * 1 := by
      rw [← pow_succ]; rw [mul_one]
      exact (pow_dvd_pow _ (Nat.succ_le_of_lt hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← isUnit_iff_dvd_one] at this
    apply pow_ne_zero m ha₀
  

Depends on / 依赖: Nat.succ_le_of_lt, isUnit_iff_dvd_one, mul_dvd_mul_iff_left, mul_one, not_lt, pow_dvd_pow, pow_ne_zero, pow_succ, succ_le_of_lt
-/
lemma pow_dvd_pow_iff (ha₀ : a != 0) (ha : ¬IsUnit a) : a ^ n ∣ a ^ m ↔ n <= m := by
  constructor
  · intro h
    rw [← not_lt]
    intro hmn
    apply ha
    have : a ^ m * a ∣ a ^ m * 1 := by
      rw [← pow_succ]; rw [mul_one]
      exact (pow_dvd_pow _ (Nat.succ_le_of_lt hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← isUnit_iff_dvd_one] at this
    apply pow_ne_zero m ha₀
  · apply pow_dvd_pow

end CancelCommMonoidWithZero

section GroupWithZero
variable [GroupWithZero α]

/-- `∣` is not a useful definition if an inverse is available. -/
@[simp]
/--
lemma `GroupWithZero.dvd_iff` / 引理 `GroupWithZero.dvd_iff`

English:
lemma GroupWithZero.dvd_iff
  given: {m n : α}
  statement: m ∣ n ↔ (m = 0 -> n = 0)
  proof: by
  refine ⟨fun ⟨a, ha⟩ hm => ?_, fun h => ?_⟩
  · simp [hm, ha]
  · refine ⟨m⁻¹ * n, ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    · rw [mul_inv_cancel_left₀ (mt h hn)]

中文:
引理 带零群.dvd_iff
  条件: {m n : α}
  结论: m ∣ n ↔ (m = 0 -> n = 0)
  证明: by
  refine ⟨fun ⟨a, ha⟩ hm => ?_, fun h => ?_⟩
  · simp [hm, ha]
  · refine ⟨m⁻¹ * n, ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    · rw [mul_inv_cancel_left₀ (mt h hn)]

Depends on / 依赖: eq_or_ne
-/
lemma GroupWithZero.dvd_iff {m n : α} : m ∣ n ↔ (m = 0 -> n = 0) := by
  refine ⟨fun ⟨a, ha⟩ hm => ?_, fun h => ?_⟩
  · simp [hm, ha]
  · refine ⟨m⁻¹ * n, ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    · rw [mul_inv_cancel_left₀ (mt h hn)]

end GroupWithZero
