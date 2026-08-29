/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Ideal.Nonunits

/-!

# Local rings

We prove basic properties of local rings.

-/

public section

variable {R S : Type*}

namespace IsLocalRing

section Semiring

variable [Semiring R]

/--
theorem `of_isUnit_or_isUnit_of_isUnit_add` / 定理 `of_isUnit_or_isUnit_of_isUnit_add`

English:
theorem of_isUnit_or_isUnit_of_isUnit_add
  statement: [Nontrivial R]
  proof: ⟨fun {a b} hab => h a b hab.symm ▸ isUnit_one⟩

中文:
定理 of_isUnit_or_isUnit_of_isUnit_add
  结论: [非平凡 R]
  证明: ⟨fun {a b} hab => h a b hab.symm ▸ isUnit_one⟩

Depends on / 依赖: hab.symm, isUnit_one
-/
theorem of_isUnit_or_isUnit_of_isUnit_add [Nontrivial R]
    (h : forall a b : R, IsUnit (a + b) -> IsUnit a ∨ IsUnit b) : IsLocalRing R :=
⟨fun {a b} hab => h a b hab.symm ▸ isUnit_one⟩

/--
theorem `of_nonunits_add` / 定理 `of_nonunits_add`

English:
theorem of_nonunits_add
  statement: [Nontrivial R]
  proof: or_iff_not_and_not.2 fun H => h a b H.1 H.2 hab.symm ▸ isUnit_one

中文:
定理 of_nonunits_add
  结论: [非平凡 R]
  证明: or_iff_not_and_not.2 fun H => h a b H.1 H.2 hab.symm ▸ isUnit_one

Depends on / 依赖: hab.symm, isUnit_one, or_iff_not_and_not
-/
theorem of_nonunits_add [Nontrivial R]
    (h : forall a b : R, a in nonunits R -> b in nonunits R -> a + b in nonunits R) : IsLocalRing R where
  isUnit_or_isUnit_of_add_one {a b} hab :=
or_iff_not_and_not.2 fun H => h a b H.1 H.2 hab.symm ▸ isUnit_one

variable [IsLocalRing R]

/--
theorem `isUnit_or_isUnit_of_isUnit_add` / 定理 `isUnit_or_isUnit_of_isUnit_add`

English:
theorem isUnit_or_isUnit_of_isUnit_add
  given: {a b : R} (h : IsUnit (a + b))
  statement: IsUnit a ∨ IsUnit b
  proof: by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one]; rw [mul_add] at hu
  apply Or.imp _ _ (isUnit_or_isUnit_of_add_one hu) <;> exact (u⁻¹.isUnit_units_mul _).mp

中文:
定理 isUnit_or_isUnit_of_isUnit_add
  条件: {a b : R} (h : 是单位 (a + b))
  结论: 是单位 a ∨ 是单位 b
  证明: by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one]; rw [mul_add] at hu
  apply Or.imp _ _ (isUnit_or_isUnit_of_add_one hu) <;> exact (u⁻¹.isUnit_units_mul _).mp

Depends on / 依赖: Or.imp, Units.inv_mul_eq_one, inv_mul_eq_one, isUnit_or_isUnit_of_add_one, isUnit_units_mul, mul_add
-/
theorem isUnit_or_isUnit_of_isUnit_add {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one]; rw [mul_add] at hu
  apply Or.imp _ _ (isUnit_or_isUnit_of_add_one hu) <;> exact (u⁻¹.isUnit_units_mul _).mp

/--
theorem `nonunits_add` / 定理 `nonunits_add`

English:
theorem nonunits_add
  given: {a b : R} (ha : a in nonunits R) (hb : b in nonunits R)
  statement: a + b in nonunits R
  proof: fun H => not_or_intro ha hb (isUnit_or_isUnit_of_isUnit_add H)

中文:
定理 nonunits_add
  条件: {a b : R} (ha : a in nonunits R) (hb : b in nonunits R)
  结论: a + b in nonunits R
  证明: fun H => not_or_intro ha hb (isUnit_or_isUnit_of_isUnit_add H)

Depends on / 依赖: isUnit_or_isUnit_of_isUnit_add, not_or_intro
-/
theorem nonunits_add {a b : R} (ha : a in nonunits R) (hb : b in nonunits R) : a + b in nonunits R :=
  fun H => not_or_intro ha hb (isUnit_or_isUnit_of_isUnit_add H)

variable (R) in
/--
Definition of `nonunitsAddSubmonoid` / `nonunitsAddSubmonoid` 的定义

English:
definition nonunitsAddSubmonoid
  signature: : AddSubmonoid R where
  body: nonunits R
  zero_mem' := by simp
  add_mem' := nonunits_add

中文:
定义 nonunitsAddSubmonoid
  签名: : 加法子幺半群 R where
  定义体: nonunits R
  zero_mem' := by simp
  add_mem' := nonunits_add
-/
@[expose] def nonunitsAddSubmonoid : AddSubmonoid R where
  carrier := nonunits R
  zero_mem' := by simp
  add_mem' := nonunits_add

/--
theorem `exists_of_isUnit_sum` / 定理 `exists_of_isUnit_sum`

English:
theorem exists_of_isUnit_sum
  statement: {ι : Type*} {s : Finset ι} {f : ι -> R}
  proof: by
  contrapose! h; exact (nonunitsAddSubmonoid R).sum_mem h

中文:
定理 存在_of_isUnit_sum
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> R}
  证明: by
  contrapose! h; exact (nonunitsAddSubmonoid R).sum_mem h

Depends on / 依赖: contrapose, nonunitsAddSubmonoid, sum_mem
-/
theorem exists_of_isUnit_sum {ι : Type*} {s : Finset ι} {f : ι -> R}
    (h : IsUnit (∑ i in s, f i)) : exists i in s, IsUnit (f i) := by
  contrapose! h; exact (nonunitsAddSubmonoid R).sum_mem h

end Semiring

section CommSemiring

variable [CommSemiring R]

/--
theorem `of_unique_max_ideal` / 定理 `of_unique_max_ideal`

English:
theorem of_unique_max_ideal
  given: (h : exists! I : Ideal R, I.IsMaximal)
  statement: IsLocalRing R
  proof: @of_nonunits_add _ _
    (nontrivial_of_ne (0 : R) 1 <|
      let ⟨I, Imax, _⟩ := h
fun H : 0 = 1 => Imax.1.1 I.eq_top_iff_one.2 H ▸ I.zero_mem)
    fun x y hx hy H =>
    let ⟨I, Imax, Iuniq⟩ := h
    let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx
    let ⟨Iy, Iymax, Hy⟩ := exists_max_i

中文:
定理 of_unique_max_ideal
  条件: (h : 存在! I : 理想 R, I.是极大)
  结论: 是局部环 R
  证明: @of_nonunits_add _ _
    (nontrivial_of_ne (0 : R) 1 <|
      let ⟨I, Imax, _⟩ := h
fun H : 0 = 1 => Imax.1.1 I.eq_top_iff_one.2 H ▸ I.zero_mem)
    fun x y hx hy H =>
    let ⟨I, Imax, Iuniq⟩ := h
    let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx
    let ⟨Iy, Iymax, Hy⟩ := exists_max_i

Depends on / 依赖: I.add_mem, I.eq_top_iff_one, I.eq_top_of_isUnit_mem, I.zero_mem, add_mem, eq_top_iff_one, eq_top_of_isUnit_mem, exists_max_ideal_of_mem_nonunits, nontrivial_of_ne, of_nonunits_add, zero_mem
-/
theorem of_unique_max_ideal (h : exists! I : Ideal R, I.IsMaximal) : IsLocalRing R :=
  @of_nonunits_add _ _
    (nontrivial_of_ne (0 : R) 1 <|
      let ⟨I, Imax, _⟩ := h
fun H : 0 = 1 => Imax.1.1 I.eq_top_iff_one.2 H ▸ I.zero_mem)
    fun x y hx hy H =>
    let ⟨I, Imax, Iuniq⟩ := h
    let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx
    let ⟨Iy, Iymax, Hy⟩ := exists_max_ideal_of_mem_nonunits hy
    have xmemI : x in I := Iuniq Ix Ixmax ▸ Hx
    have ymemI : y in I := Iuniq Iy Iymax ▸ Hy
Imax.1.1 I.eq_top_of_isUnit_mem (I.add_mem xmemI ymemI) H

/--
theorem `of_unique_nonzero_prime` / 定理 `of_unique_nonzero_prime`

English:
theorem of_unique_nonzero_prime
  given: (h : exists! P : Ideal R, P != ⊥ ∧ Ideal.IsPrime P)
  statement: IsLocalRing R
  proof: of_unique_max_ideal
    (by
      rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩
      refine ⟨P, ⟨⟨hPnot_top, ?_⟩⟩, fun M hM => hPunique _ ⟨?_, Ideal.IsMaximal.isPrime hM⟩⟩
      · refine Ideal.maximal_of_no_maximal fun M hPM hM => ne_of_lt hPM ?_
        exact (hPunique _ ⟨ne_bot_of_gt hPM

中文:
定理 of_unique_nonzero_prime
  条件: (h : 存在! P : 理想 R, P != ⊥ ∧ 理想.是素 P)
  结论: 是局部环 R
  证明: of_unique_max_ideal
    (by
      rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩
      refine ⟨P, ⟨⟨hPnot_top, ?_⟩⟩, fun M hM => hPunique _ ⟨?_, Ideal.IsMaximal.isPrime hM⟩⟩
      · refine Ideal.maximal_of_no_maximal fun M hPM hM => ne_of_lt hPM ?_
        exact (hPunique _ ⟨ne_bot_of_gt hPM

Depends on / 依赖: Ideal.IsMaximal.isPrime, Ideal.maximal_of_no_maximal, IsMaximal, bot_lt_iff_ne_bot, hPnonzero, hPnot_top, hPunique, isPrime, maximal_of_no_maximal, ne_bot_of_gt, ne_of_lt, of_unique_max_ideal
-/
theorem of_unique_nonzero_prime (h : exists! P : Ideal R, P != ⊥ ∧ Ideal.IsPrime P) : IsLocalRing R :=
  of_unique_max_ideal
    (by
      rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩
      refine ⟨P, ⟨⟨hPnot_top, ?_⟩⟩, fun M hM => hPunique _ ⟨?_, Ideal.IsMaximal.isPrime hM⟩⟩
      · refine Ideal.maximal_of_no_maximal fun M hPM hM => ne_of_lt hPM ?_
        exact (hPunique _ ⟨ne_bot_of_gt hPM, Ideal.IsMaximal.isPrime hM⟩).symm
      · rintro rfl
        exact hPnot_top (hM.1.2 P (bot_lt_iff_ne_bot.2 hPnonzero)))

end CommSemiring

section Ring

variable [Ring R]

/--
theorem `of_isUnit_or_isUnit_one_sub_self` / 定理 `of_isUnit_or_isUnit_one_sub_self`

English:
theorem of_isUnit_or_isUnit_one_sub_self
  given: [Nontrivial R] (h : forall a : R, IsUnit a ∨ IsUnit (1 - a))
  proof: ⟨fun {a b} hab => add_sub_cancel_left a b ▸ hab.symm ▸ h a⟩

中文:
定理 of_isUnit_or_isUnit_one_sub_self
  条件: [非平凡 R] (h : 对任意 a : R, 是单位 a ∨ 是单位 (1 - a))
  证明: ⟨fun {a b} hab => add_sub_cancel_left a b ▸ hab.symm ▸ h a⟩

Depends on / 依赖: add_sub_cancel_left, hab.symm
-/
theorem of_isUnit_or_isUnit_one_sub_self [Nontrivial R] (h : forall a : R, IsUnit a ∨ IsUnit (1 - a)) :
    IsLocalRing R :=
  ⟨fun {a b} hab => add_sub_cancel_left a b ▸ hab.symm ▸ h a⟩

end Ring

section CommRing

variable [CommRing R] [IsLocalRing R]

/--
theorem `isUnit_or_isUnit_one_sub_self` / 定理 `isUnit_or_isUnit_one_sub_self`

English:
theorem isUnit_or_isUnit_one_sub_self
  given: (a : R)
  statement: IsUnit a ∨ IsUnit (1 - a)
  proof: isUnit_or_isUnit_of_isUnit_add (add_sub_cancel a 1).symm ▸ isUnit_one

中文:
定理 isUnit_or_isUnit_one_sub_self
  条件: (a : R)
  结论: 是单位 a ∨ 是单位 (1 - a)
  证明: isUnit_or_isUnit_of_isUnit_add (add_sub_cancel a 1).symm ▸ isUnit_one

Depends on / 依赖: add_sub_cancel, isUnit_one, isUnit_or_isUnit_of_isUnit_add
-/
theorem isUnit_or_isUnit_one_sub_self (a : R) : IsUnit a ∨ IsUnit (1 - a) :=
isUnit_or_isUnit_of_isUnit_add (add_sub_cancel a 1).symm ▸ isUnit_one

/--
theorem `isUnit_of_mem_nonunits_one_sub_self` / 定理 `isUnit_of_mem_nonunits_one_sub_self`

English:
theorem isUnit_of_mem_nonunits_one_sub_self
  given: (a : R) (h : 1 - a in nonunits R)
  statement: IsUnit a
  proof: or_iff_not_imp_right.1 (isUnit_or_isUnit_one_sub_self a) h

中文:
定理 isUnit_of_mem_nonunits_one_sub_self
  条件: (a : R) (h : 1 - a in nonunits R)
  结论: 是单位 a
  证明: or_iff_not_imp_right.1 (isUnit_or_isUnit_one_sub_self a) h

Depends on / 依赖: isUnit_or_isUnit_one_sub_self, or_iff_not_imp_right
-/
theorem isUnit_of_mem_nonunits_one_sub_self (a : R) (h : 1 - a in nonunits R) : IsUnit a :=
  or_iff_not_imp_right.1 (isUnit_or_isUnit_one_sub_self a) h

/--
theorem `isUnit_one_sub_self_of_mem_nonunits` / 定理 `isUnit_one_sub_self_of_mem_nonunits`

English:
theorem isUnit_one_sub_self_of_mem_nonunits
  given: (a : R) (h : a in nonunits R)
  statement: IsUnit (1 - a)
  proof: or_iff_not_imp_left.1 (isUnit_or_isUnit_one_sub_self a) h

中文:
定理 isUnit_one_sub_self_of_mem_nonunits
  条件: (a : R) (h : a in nonunits R)
  结论: 是单位 (1 - a)
  证明: or_iff_not_imp_left.1 (isUnit_or_isUnit_one_sub_self a) h

Depends on / 依赖: isUnit_or_isUnit_one_sub_self, or_iff_not_imp_left
-/
theorem isUnit_one_sub_self_of_mem_nonunits (a : R) (h : a in nonunits R) : IsUnit (1 - a) :=
  or_iff_not_imp_left.1 (isUnit_or_isUnit_one_sub_self a) h

/--
theorem `of_surjective'` / 定理 `of_surjective'`

English:
theorem of_surjective'
  given: [Ring S] [Nontrivial S] (f : R ->+* S) (hf : Function.Surjective f)
  proof: of_isUnit_or_isUnit_one_sub_self (by
    intro b
    obtain ⟨a, rfl⟩ := hf b
apply (isUnit_or_isUnit_one_sub_self a).imp RingHom.isUnit_map _
    rw [← f.map_one]; rw [← f.map_sub]
    apply f.isUnit_map)

中文:
定理 of_surjective'
  条件: [环 S] [非平凡 S] (f : R ->+* S) (hf : 函数.满射 f)
  证明: of_isUnit_or_isUnit_one_sub_self (by
    intro b
    obtain ⟨a, rfl⟩ := hf b
apply (isUnit_or_isUnit_one_sub_self a).imp RingHom.isUnit_map _
    rw [← f.map_one]; rw [← f.map_sub]
    apply f.isUnit_map)

Depends on / 依赖: RingHom, RingHom.isUnit_map, f.isUnit_map, f.map_one, f.map_sub, isUnit_map, isUnit_or_isUnit_one_sub_self, map_one, map_sub, of_isUnit_or_isUnit_one_sub_self
-/
theorem of_surjective' [Ring S] [Nontrivial S] (f : R ->+* S) (hf : Function.Surjective f) :
    IsLocalRing S :=
  of_isUnit_or_isUnit_one_sub_self (by
    intro b
    obtain ⟨a, rfl⟩ := hf b
apply (isUnit_or_isUnit_one_sub_self a).imp RingHom.isUnit_map _
    rw [← f.map_one]; rw [← f.map_sub]
    apply f.isUnit_map)

end CommRing

end IsLocalRing

namespace Field

variable (K : Type*) [Field K]

-- see Note [lower instance priority]
instance (priority := 100) : IsLocalRing K := by
  classical exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    if h : a = 0 then Or.inr (by rw [h, sub_zero]; exact isUnit_one)
else Or.inl IsUnit.mk0 a h

end Field
