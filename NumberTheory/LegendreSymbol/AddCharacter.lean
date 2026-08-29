/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.ZMod.Units

/-!
# Additive characters of finite rings and fields

This file collects some results on additive characters whose domain is (the additive group of)
a finite ring or field.

## Main definitions and results

We define an additive character `ψ` to be *primitive* if `mulShift ψ a` is trivial only when
`a = 0`.

We show that when `ψ` is primitive, then the map `a ↦ mulShift ψ a` is injective
(`AddChar.to_mulShift_inj_of_isPrimitive`) and that `ψ` is primitive when `R` is a field
and `ψ` is nontrivial (`AddChar.IsNontrivial.isPrimitive`).

We also show that there are primitive additive characters on `R` (with suitable
target `R'`) when `R` is a field or `R = ZMod n` (`AddChar.primitiveCharFiniteField`
and `AddChar.primitiveZModChar`).

Finally, we show that the sum of all character values is zero when the character
is nontrivial (and the target is a domain); see `AddChar.sum_eq_zero_of_isNontrivial`.

## Tags

additive character
-/

@[expose] public section

assert_not_exists MeasureTheory.integral

universe u v

namespace AddChar

section Additive

-- The domain and target of our additive characters. Now we restrict to a ring in the domain.
variable {R : Type u} [CommRing R] {R' : Type v} [CommMonoid R']

/--
lemma `val_mem_rootsOfUnity` / 引理 `val_mem_rootsOfUnity`

English:
lemma val_mem_rootsOfUnity
  given: (φ : AddChar R R') (a : R) (h : 0 < ringChar R)
  proof: by
  simp only [mem_rootsOfUnity', IsUnit.unit_spec, Nat.toPNat'_coe, h, ↓reduceIte,
    ← map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, map_zero_eq_one]

中文:
引理 val_mem_rootsOfUnity
  条件: (φ : AddChar R R') (a : R) (h : 0 < ringChar R)
  证明: by
  simp only [mem_rootsOfUnity', IsUnit.unit_spec, Nat.toPNat'_coe, h, ↓reduceIte,
    ← map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, map_zero_eq_one]

Depends on / 依赖: CharP.cast_eq_zero, IsUnit, IsUnit.unit_spec, Nat.toPNat, _coe, cast_eq_zero, map_nsmul_eq_pow, map_zero_eq_one, mem_rootsOfUnity, nsmul_eq_mul, reduceIte, toPNat, unit_spec, zero_mul
-/
lemma val_mem_rootsOfUnity (φ : AddChar R R') (a : R) (h : 0 < ringChar R) :
    (φ.val_isUnit a).unit in rootsOfUnity (ringChar R).toPNat' R' := by
  simp only [mem_rootsOfUnity', IsUnit.unit_spec, Nat.toPNat'_coe, h, ↓reduceIte,
    ← map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, map_zero_eq_one]

/--
Definition of `IsPrimitive` / `IsPrimitive` 的定义

English:
definition IsPrimitive
  signature: (ψ : AddChar R R')
  body: forall ⦃a : R⦄, a != 0 -> mulShift ψ a != 1

中文:
定义 IsPrimitive
  签名: (ψ : AddChar R R')
  定义体: forall ⦃a : R⦄, a != 0 -> mulShift ψ a != 1

Depends on / 依赖: mulShift
-/
def IsPrimitive (ψ : AddChar R R') : Prop := forall ⦃a : R⦄, a != 0 -> mulShift ψ a != 1

/--
lemma `IsPrimitive.compMulHom_of_isPrimitive` / 引理 `IsPrimitive.compMulHom_of_isPrimitive`

English:
lemma IsPrimitive.compMulHom_of_isPrimitive
  statement: {R'' : Type*} [CommMonoid R''] {φ : AddChar R R'}
  proof: fun a ha => by
  simpa [DFunLike.ext_iff] using (MonoidHom.compAddChar_injective_right f hf).ne (hφ ha)

中文:
引理 IsPrimitive.compMulHom_of_isPrimitive
  结论: {R'' : 类型} [CommMonoid R''] {φ : AddChar R R'}
  证明: fun a ha => by
  simpa [DFunLike.ext_iff] using (MonoidHom.compAddChar_injective_right f hf).ne (hφ ha)

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MonoidHom, MonoidHom.compAddChar_injective_right, compAddChar_injective_right, ext_iff
-/
lemma IsPrimitive.compMulHom_of_isPrimitive {R'' : Type*} [CommMonoid R''] {φ : AddChar R R'}
    {f : R' ->* R''} (hφ : φ.IsPrimitive) (hf : Function.Injective f) :
    (f.compAddChar φ).IsPrimitive := fun a ha => by
  simpa [DFunLike.ext_iff] using (MonoidHom.compAddChar_injective_right f hf).ne (hφ ha)

/--
theorem `to_mulShift_inj_of_isPrimitive` / 定理 `to_mulShift_inj_of_isPrimitive`

English:
theorem to_mulShift_inj_of_isPrimitive
  given: {ψ : AddChar R R'} (hψ : IsPrimitive ψ)
  proof: by
  intro a b h
  apply_fun fun x => x * mulShift ψ (-b) at h
  simp only [mulShift_mul, mulShift_zero, add_neg_cancel] at h
  simpa [← sub_eq_add_neg, sub_eq_zero] using (hψ · h)

中文:
定理 to_mulShift_inj_of_isPrimitive
  条件: {ψ : AddChar R R'} (hψ : IsPrimitive ψ)
  证明: by
  intro a b h
  apply_fun fun x => x * mulShift ψ (-b) at h
  simp only [mulShift_mul, mulShift_zero, add_neg_cancel] at h
  simpa [← sub_eq_add_neg, sub_eq_zero] using (hψ · h)

Depends on / 依赖: add_neg_cancel, apply_fun, mulShift, mulShift_mul, mulShift_zero, sub_eq_add_neg, sub_eq_zero
-/
theorem to_mulShift_inj_of_isPrimitive {ψ : AddChar R R'} (hψ : IsPrimitive ψ) :
    Function.Injective ψ.mulShift := by
  intro a b h
  apply_fun fun x => x * mulShift ψ (-b) at h
  simp only [mulShift_mul, mulShift_zero, add_neg_cancel] at h
  simpa [← sub_eq_add_neg, sub_eq_zero] using (hψ · h)

-- `AddCommGroup.equiv_direct_sum_zmod_of_fintype`
-- gives the structure theorem for finite abelian groups.
-- This could be used to show that the map above is a bijection.
-- We leave this for a later occasion.
/--
theorem `IsPrimitive.of_ne_one` / 定理 `IsPrimitive.of_ne_one`

English:
theorem IsPrimitive.of_ne_one
  given: {F : Type u} [Field F] {ψ : AddChar F R'} (hψ : ψ != 1)
  proof: fun a ha h => hψ by simpa [mulShift_mulShift, ha] using! congr_arg (mulShift · a⁻¹) h

中文:
定理 IsPrimitive.of_ne_one
  条件: {F : 类型u} [Field F] {ψ : AddChar F R'} (hψ : ψ != 1)
  证明: fun a ha h => hψ by simpa [mulShift_mulShift, ha] using! congr_arg (mulShift · a⁻¹) h

Depends on / 依赖: congr_arg, mulShift, mulShift_mulShift
-/
theorem IsPrimitive.of_ne_one {F : Type u} [Field F] {ψ : AddChar F R'} (hψ : ψ != 1) :
    IsPrimitive ψ :=
fun a ha h => hψ by simpa [mulShift_mulShift, ha] using! congr_arg (mulShift · a⁻¹) h

/--
lemma `not_isPrimitive_mulShift` / 引理 `not_isPrimitive_mulShift`

English:
lemma not_isPrimitive_mulShift
  statement: [Finite R] (e : AddChar R R') {r : R}
  proof: by
  simp only [IsPrimitive, not_forall]
  simp only [isUnit_iff_mem_nonZeroDivisors_of_finite,
    mem_nonZeroDivisors_iff_right, not_forall] at hr
  rcases hr with ⟨x, h, h'⟩
  exact ⟨x, h', by simp only [mulShift_mulShift, mul_comm r, h, mulShift_zero, not_ne_iff]⟩

中文:
引理 not_isPrimitive_mulShift
  结论: [Finite R] (e : AddChar R R') {r : R}
  证明: by
  simp only [IsPrimitive, not_forall]
  simp only [isUnit_iff_mem_nonZeroDivisors_of_finite,
    mem_nonZeroDivisors_iff_right, not_forall] at hr
  rcases hr with ⟨x, h, h'⟩
  exact ⟨x, h', by simp only [mulShift_mulShift, mul_comm r, h, mulShift_zero, not_ne_iff]⟩

Depends on / 依赖: IsPrimitive, isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff_right, mulShift_mulShift, mulShift_zero, mul_comm, not_forall, not_ne_iff
-/
lemma not_isPrimitive_mulShift [Finite R] (e : AddChar R R') {r : R}
    (hr : ¬ IsUnit r) : ¬ IsPrimitive (e.mulShift r) := by
  simp only [IsPrimitive, not_forall]
  simp only [isUnit_iff_mem_nonZeroDivisors_of_finite,
    mem_nonZeroDivisors_iff_right, not_forall] at hr
  rcases hr with ⟨x, h, h'⟩
  exact ⟨x, h', by simp only [mulShift_mulShift, mul_comm r, h, mulShift_zero, not_ne_iff]⟩

/--
Definition of `PrimitiveAddChar` / `PrimitiveAddChar` 的定义

English:
structure PrimitiveAddChar
  parameters: (R : Type u) [CommRing R] (R' : Type v) [Field R']
  axioms and operations (3):
    - n : Nat+
    - char : AddChar R (CyclotomicField n R')
    - prim : IsPrimitive char

中文:
结构 PrimitiveAddChar
  参数: (R : 类型u) [CommRing R] (R' : 类型v) [Field R']
  公理与运算 (3 个):
    - n : 自然数+
    - char : AddChar R (CyclotomicField n R')
    - prim : IsPrimitive char
-/
structure PrimitiveAddChar (R : Type u) [CommRing R] (R' : Type v) [Field R'] where
  /-- The first projection from `PrimitiveAddChar`, giving the cyclotomic field. -/
  n : Nat+
  /-- The second projection from `PrimitiveAddChar`, giving the character. -/
  char : AddChar R (CyclotomicField n R')
  /-- The third projection from `PrimitiveAddChar`, showing that `χ.char` is primitive. -/
  prim : IsPrimitive char

/-!
### Additive characters on `ZMod n`
-/

section ZMod

variable {N : Nat} [NeZero N] {R : Type*} [CommRing R] (e : AddChar (ZMod N) R)

/--
lemma `exists_divisor_of_not_isPrimitive` / 引理 `exists_divisor_of_not_isPrimitive`

English:
lemma exists_divisor_of_not_isPrimitive
  given: (he : ¬e.IsPrimitive)
  proof: by
  simp_rw [IsPrimitive, not_forall, not_ne_iff] at he
  rcases he with ⟨b, hb_ne, hb⟩
  -- We have `AddChar.mulShift e b = 1`, but `b ≠ 0`.
  obtain ⟨d, hd, u, hu, rfl⟩ := b.eq_unit_mul_divisor
  refine ⟨d, hd, lt_of_le_of_ne (Nat.le_of_dvd (NeZero.pos _) hd) ?_, ?_⟩
  · exact fun h => by simp on

中文:
引理 exists_divisor_of_not_isPrimitive
  条件: (he : ¬e.IsPrimitive)
  证明: by
  simp_rw [IsPrimitive, not_forall, not_ne_iff] at he
  rcases he with ⟨b, hb_ne, hb⟩
  -- We have `AddChar.mulShift e b = 1`, but `b ≠ 0`.
  obtain ⟨d, hd, u, hu, rfl⟩ := b.eq_unit_mul_divisor
  refine ⟨d, hd, lt_of_le_of_ne (Nat.le_of_dvd (NeZero.pos _) hd) ?_, ?_⟩
  · exact fun h => by simp on

Depends on / 依赖: IsPrimitive, hb_ne, not_forall, not_ne_iff, simp_rw
-/
lemma exists_divisor_of_not_isPrimitive (he : ¬e.IsPrimitive) :
    exists d : Nat, d ∣ N ∧ d < N ∧ e.mulShift d = 1 := by
  simp_rw [IsPrimitive, not_forall, not_ne_iff] at he
  rcases he with ⟨b, hb_ne, hb⟩
  -- We have `AddChar.mulShift e b = 1`, but `b ≠ 0`.
  obtain ⟨d, hd, u, hu, rfl⟩ := b.eq_unit_mul_divisor
  refine ⟨d, hd, lt_of_le_of_ne (Nat.le_of_dvd (NeZero.pos _) hd) ?_, ?_⟩
  · exact fun h => by simp only [h, ZMod.natCast_self, mul_zero, ne_eq, not_true_eq_false] at hb_ne
  · rw [← mulShift_unit_eq_one_iff _ hu, ← hb, mul_comm]
    ext1 y
    rw [mulShift_apply]; rw [mulShift_apply]; rw [mulShift_apply]; rw [mul_assoc]

end ZMod

section ZModChar

variable {C : Type v} [CommMonoid C]

section ZModCharDef


/--
Definition of `zmodChar` / `zmodChar` 的定义

English:
definition zmodChar
  signature: (n : Nat) [NeZero n] {ζ : C} (hζ : ζ ^ n = 1)
  body: ζ ^ a.val
  map_zero_eq_one' := by simp only [ZMod.val_zero, pow_zero]
  map_add_eq_mul' x y := by simp only [ZMod.val_add, ← pow_eq_pow_mod _ hζ, ← pow_add]

中文:
定义 zmodChar
  签名: (n : 自然数) [NeZero n] {ζ : C} (hζ : ζ ^ n = 1)
  定义体: ζ ^ a.val
  map_zero_eq_one' := by simp only [ZMod.val_zero, pow_zero]
  map_add_eq_mul' x y := by simp only [ZMod.val_add, ← pow_eq_pow_mod _ hζ, ← pow_add]

Depends on / 依赖: a.val
-/
def zmodChar (n : Nat) [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) : AddChar (ZMod n) C where
  toFun a := ζ ^ a.val
  map_zero_eq_one' := by simp only [ZMod.val_zero, pow_zero]
  map_add_eq_mul' x y := by simp only [ZMod.val_add, ← pow_eq_pow_mod _ hζ, ← pow_add]

/--
theorem `zmodChar_apply` / 定理 `zmodChar_apply`

English:
theorem zmodChar_apply
  given: {n : Nat} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : ZMod n)
  proof: rfl

中文:
定理 zmodChar_apply
  条件: {n : 自然数} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : ZMod n)
  证明: rfl
-/
theorem zmodChar_apply {n : Nat} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : ZMod n) :
    zmodChar n hζ a = ζ ^ a.val :=
  rfl

/--
theorem `zmodChar_apply'` / 定理 `zmodChar_apply'`

English:
theorem zmodChar_apply'
  given: {n : Nat} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : Nat)
  proof: by
  rw [pow_eq_pow_mod a hζ]; rw [zmodChar_apply]; rw [ZMod.val_natCast]

中文:
定理 zmodChar_apply'
  条件: {n : 自然数} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : 自然数)
  证明: by
  rw [pow_eq_pow_mod a hζ]; rw [zmodChar_apply]; rw [ZMod.val_natCast]

Depends on / 依赖: ZMod.val_natCast, pow_eq_pow_mod, val_natCast, zmodChar_apply
-/
theorem zmodChar_apply' {n : Nat} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : Nat) :
    zmodChar n hζ a = ζ ^ a := by
  rw [pow_eq_pow_mod a hζ]; rw [zmodChar_apply]; rw [ZMod.val_natCast]

end ZModCharDef

/--
theorem `zmod_char_ne_one_iff` / 定理 `zmod_char_ne_one_iff`

English:
theorem zmod_char_ne_one_iff
  given: (n : Nat) [NeZero n] (ψ : AddChar (ZMod n) C)
  statement: ψ != 1 ↔ ψ 1 != 1
  proof: by
  rw [ne_one_iff]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  contrapose!
  rintro h₁ a
  have ha₁ : a = a.val • (1 : ZMod ↑n) := by
    rw [nsmul_eq_mul]; rw [mul_one]; exact (ZMod.natCast_zmod_val a).symm
  rw [ha₁]; rw [map_nsmul_eq_pow]; rw [h₁]; rw [one_pow]

中文:
定理 zmod_char_ne_one_iff
  条件: (n : 自然数) [NeZero n] (ψ : AddChar (ZMod n) C)
  结论: ψ != 1 ↔ ψ 1 != 1
  证明: by
  rw [ne_one_iff]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  contrapose!
  rintro h₁ a
  have ha₁ : a = a.val • (1 : ZMod ↑n) := by
    rw [nsmul_eq_mul]; rw [mul_one]; exact (ZMod.natCast_zmod_val a).symm
  rw [ha₁]; rw [map_nsmul_eq_pow]; rw [h₁]; rw [one_pow]

Depends on / 依赖: ZMod.natCast_zmod_val, a.val, contrapose, map_nsmul_eq_pow, mul_one, natCast_zmod_val, ne_one_iff, nsmul_eq_mul, one_pow
-/
theorem zmod_char_ne_one_iff (n : Nat) [NeZero n] (ψ : AddChar (ZMod n) C) : ψ != 1 ↔ ψ 1 != 1 := by
  rw [ne_one_iff]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  contrapose!
  rintro h₁ a
  have ha₁ : a = a.val • (1 : ZMod ↑n) := by
    rw [nsmul_eq_mul]; rw [mul_one]; exact (ZMod.natCast_zmod_val a).symm
  rw [ha₁]; rw [map_nsmul_eq_pow]; rw [h₁]; rw [one_pow]

/--
theorem `IsPrimitive.zmod_char_eq_one_iff` / 定理 `IsPrimitive.zmod_char_eq_one_iff`

English:
theorem IsPrimitive.zmod_char_eq_one_iff
  statement: (n : Nat) [NeZero n]
  proof: by
  refine ⟨fun h => not_imp_comm.mp (@hψ a) ?_, fun ha => by rw [ha, map_zero_eq_one]⟩
  rw [zmod_char_ne_one_iff n (mulShift ψ a)]; rw [mulShift_apply]; rw [mul_one]; rw [h]; rw [Classical.not_not]

中文:
定理 IsPrimitive.zmod_char_eq_one_iff
  结论: (n : 自然数) [NeZero n]
  证明: by
  refine ⟨fun h => not_imp_comm.mp (@hψ a) ?_, fun ha => by rw [ha, map_zero_eq_one]⟩
  rw [zmod_char_ne_one_iff n (mulShift ψ a)]; rw [mulShift_apply]; rw [mul_one]; rw [h]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, map_zero_eq_one, mulShift, mulShift_apply, mul_one, not_imp_comm, not_imp_comm.mp, not_not, zmod_char_ne_one_iff
-/
theorem IsPrimitive.zmod_char_eq_one_iff (n : Nat) [NeZero n]
    {ψ : AddChar (ZMod n) C} (hψ : IsPrimitive ψ) (a : ZMod n) :
    ψ a = 1 ↔ a = 0 := by
  refine ⟨fun h => not_imp_comm.mp (@hψ a) ?_, fun ha => by rw [ha, map_zero_eq_one]⟩
  rw [zmod_char_ne_one_iff n (mulShift ψ a)]; rw [mulShift_apply]; rw [mul_one]; rw [h]; rw [Classical.not_not]

/--
theorem `zmod_char_primitive_of_eq_one_only_at_zero` / 定理 `zmod_char_primitive_of_eq_one_only_at_zero`

English:
theorem zmod_char_primitive_of_eq_one_only_at_zero
  statement: (n : Nat) (ψ : AddChar (ZMod n) C)
  proof: by
  intro a ha hf
  have h : mulShift ψ a 1 = (1 : AddChar (ZMod n) C) (1 : ZMod n) :=
    congr_fun (congr_arg (↑) hf) 1
  rw [mulShift_apply]; rw [mul_one] at h; norm_cast at h
  exact ha (hψ a h)

中文:
定理 zmod_char_primitive_of_eq_one_only_at_zero
  结论: (n : 自然数) (ψ : AddChar (ZMod n) C)
  证明: by
  intro a ha hf
  have h : mulShift ψ a 1 = (1 : AddChar (ZMod n) C) (1 : ZMod n) :=
    congr_fun (congr_arg (↑) hf) 1
  rw [mulShift_apply]; rw [mul_one] at h; norm_cast at h
  exact ha (hψ a h)

Depends on / 依赖: AddChar, congr_arg, congr_fun, mulShift, mulShift_apply, mul_one
-/
theorem zmod_char_primitive_of_eq_one_only_at_zero (n : Nat) (ψ : AddChar (ZMod n) C)
    (hψ : forall a, ψ a = 1 -> a = 0) : IsPrimitive ψ := by
  intro a ha hf
  have h : mulShift ψ a 1 = (1 : AddChar (ZMod n) C) (1 : ZMod n) :=
    congr_fun (congr_arg (↑) hf) 1
  rw [mulShift_apply]; rw [mul_one] at h; norm_cast at h
  exact ha (hψ a h)

/--
theorem `zmodChar_primitive_of_primitive_root` / 定理 `zmodChar_primitive_of_primitive_root`

English:
theorem zmodChar_primitive_of_primitive_root
  given: (n : Nat) [NeZero n] {ζ : C} (h : IsPrimitiveRoot ζ n)
  proof: by
  apply zmod_char_primitive_of_eq_one_only_at_zero
  intro a ha
  rw [zmodChar_apply]; rw [← pow_zero ζ] at ha
  exact (ZMod.val_eq_zero a).mp (IsPrimitiveRoot.pow_inj h (ZMod.val_lt a) (NeZero.pos _) ha)

中文:
定理 zmodChar_primitive_of_primitive_root
  条件: (n : 自然数) [NeZero n] {ζ : C} (h : IsPrimitiveRoot ζ n)
  证明: by
  apply zmod_char_primitive_of_eq_one_only_at_zero
  intro a ha
  rw [zmodChar_apply]; rw [← pow_zero ζ] at ha
  exact (ZMod.val_eq_zero a).mp (IsPrimitiveRoot.pow_inj h (ZMod.val_lt a) (NeZero.pos _) ha)

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.pow_inj, NeZero, NeZero.pos, ZMod.val_eq_zero, ZMod.val_lt, pow_inj, pow_zero, val_eq_zero, val_lt, zmodChar_apply, zmod_char_primitive_of_eq_one_only_at_zero
-/
theorem zmodChar_primitive_of_primitive_root (n : Nat) [NeZero n] {ζ : C} (h : IsPrimitiveRoot ζ n) :
    IsPrimitive (zmodChar n ((IsPrimitiveRoot.iff_def ζ n).mp h).left) := by
  apply zmod_char_primitive_of_eq_one_only_at_zero
  intro a ha
  rw [zmodChar_apply]; rw [← pow_zero ζ] at ha
  exact (ZMod.val_eq_zero a).mp (IsPrimitiveRoot.pow_inj h (ZMod.val_lt a) (NeZero.pos _) ha)

/--
Definition of `primitiveZModChar` / `primitiveZModChar` 的定义

English:
definition primitiveZModChar
  signature: (n : Nat+) (F' : Type v) [Field F'] (h : (n : F') != 0)
  body: have : NeZero (n : F') := ⟨h⟩
  ⟨n, zmodChar n (IsCyclotomicExtension.zeta_pow n F' _),
    zmodChar_primitive_of_primitive_root n (IsCyclotomicExtension.zeta_spec n F' _)⟩

中文:
定义 primitiveZModChar
  签名: (n : 自然数+) (F' : 类型v) [Field F'] (h : (n : F') != 0)
  定义体: have : NeZero (n : F') := ⟨h⟩
  ⟨n, zmodChar n (IsCyclotomicExtension.zeta_pow n F' _),
    zmodChar_primitive_of_primitive_root n (IsCyclotomicExtension.zeta_spec n F' _)⟩

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.zeta_pow, IsCyclotomicExtension.zeta_spec, NeZero, zeta_pow, zeta_spec, zmodChar, zmodChar_primitive_of_primitive_root
-/
noncomputable def primitiveZModChar (n : Nat+) (F' : Type v) [Field F'] (h : (n : F') != 0) :
    PrimitiveAddChar (ZMod n) F' :=
  have : NeZero (n : F') := ⟨h⟩
  ⟨n, zmodChar n (IsCyclotomicExtension.zeta_pow n F' _),
    zmodChar_primitive_of_primitive_root n (IsCyclotomicExtension.zeta_spec n F' _)⟩

end ZModChar

end Additive

/-!
### Existence of a primitive additive character on a finite field
-/

/--
Definition of `FiniteField.primitiveChar` / `FiniteField.primitiveChar` 的定义

English:
definition FiniteField.primitiveChar
  signature: (F F' : Type*) [Field F] [Finite F] [Field F']
  body: by
  let p := ringChar F
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  let pp := p.toPNat hp.1.pos
  have hp₂ : ¬ringChar F' ∣ p := by
    rcases CharP.char_is_prime_or_zero F' (ringChar F') with hq | hq
    · exact mt (Nat.Prime.dvd_iff_eq hp.1 (Nat.Prime.ne_one hq)).mp h.symm
    · rw [

中文:
定义 FiniteField.primitiveChar
  签名: (F F' : 类型) [Field F] [Finite F] [Field F']
  定义体: by
  let p := ringChar F
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  let pp := p.toPNat hp.1.pos
  have hp₂ : ¬ringChar F' ∣ p := by
    rcases CharP.char_is_prime_or_zero F' (ringChar F') with hq | hq
    · exact mt (Nat.Prime.dvd_iff_eq hp.1 (Nat.Prime.ne_one hq)).mp h.symm
    · rw [

Depends on / 依赖: Algebra, CharP.char_is_prime, CharP.char_is_prime_or_zero, Nat.Prime.dvd_iff_eq, Nat.Prime.ne_one, Nat.Prime.ne_zero, NeZero, NeZero.of_not_dvd, ZMod.algebra, algebra, char.compAddMonoidHom, char_is_prime, char_is_prime_or_zero, compAddMonoidHom, dvd_iff_eq, h.symm, neZero_iff, neZero_iff.mp, ne_one, ne_zero
-/
noncomputable def FiniteField.primitiveChar (F F' : Type*) [Field F] [Finite F] [Field F']
    (h : ringChar F' != ringChar F) : PrimitiveAddChar F F' := by
  let p := ringChar F
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  let pp := p.toPNat hp.1.pos
  have hp₂ : ¬ringChar F' ∣ p := by
    rcases CharP.char_is_prime_or_zero F' (ringChar F') with hq | hq
    · exact mt (Nat.Prime.dvd_iff_eq hp.1 (Nat.Prime.ne_one hq)).mp h.symm
    · rw [hq]
      exact fun hf => Nat.Prime.ne_zero hp.1 (zero_dvd_iff.mp hf)
  let ψ := primitiveZModChar pp F' (neZero_iff.mp (NeZero.of_not_dvd F' hp₂))
  letI : Algebra (ZMod p) F := ZMod.algebra _ _
  let ψ' := ψ.char.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom
  have hψ' : ψ' != 1 := by
    obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
    rw [one_mul] at ha
    exact ne_one_iff.2
⟨a, fun hf => ha (ψ.prim.zmod_char_eq_one_iff pp <| Algebra.trace (ZMod p) F a).mp hf⟩
  exact ⟨ψ.n, ψ', IsPrimitive.of_ne_one hψ'⟩
/-!
### The sum of all character values
-/

section sum

variable {R : Type*} [AddGroup R] [Fintype R] {R' : Type*} [CommRing R']

/--
theorem `sum_eq_zero_of_ne_one` / 定理 `sum_eq_zero_of_ne_one`

English:
theorem sum_eq_zero_of_ne_one
  given: [IsDomain R'] {ψ : AddChar R R'} (hψ : ψ != 1)
  statement: ∑ a, ψ a = 0
  proof: by
  rcases ne_one_iff.1 hψ with ⟨b, hb⟩
  have h₁ : ∑ a : R, ψ (b + a) = ∑ a : R, ψ a :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective b) _ _ fun x => rfl
  simp_rw [map_add_eq_mul] at h₁
  have h₂ : ∑ a : R, ψ a = Finset.univ.sum ↑ψ := rfl
  rw [← Finset.mul_sum]; rw [h₂] at h₁
  exact e

中文:
定理 sum_eq_zero_of_ne_one
  条件: [IsDomain R'] {ψ : AddChar R R'} (hψ : ψ != 1)
  结论: ∑ a, ψ a = 0
  证明: by
  rcases ne_one_iff.1 hψ with ⟨b, hb⟩
  have h₁ : ∑ a : R, ψ (b + a) = ∑ a : R, ψ a :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective b) _ _ fun x => rfl
  simp_rw [map_add_eq_mul] at h₁
  have h₂ : ∑ a : R, ψ a = Finset.univ.sum ↑ψ := rfl
  rw [← Finset.mul_sum]; rw [h₂] at h₁
  exact e

Depends on / 依赖: AddGroup, AddGroup.addLeft_bijective, Finset, Finset.mul_sum, Finset.univ.sum, Fintype, Fintype.sum_bijective, addLeft_bijective, eq_zero_of_mul_eq_self_left, map_add_eq_mul, mul_sum, ne_one_iff, simp_rw, sum_bijective
-/
theorem sum_eq_zero_of_ne_one [IsDomain R'] {ψ : AddChar R R'} (hψ : ψ != 1) : ∑ a, ψ a = 0 := by
  rcases ne_one_iff.1 hψ with ⟨b, hb⟩
  have h₁ : ∑ a : R, ψ (b + a) = ∑ a : R, ψ a :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective b) _ _ fun x => rfl
  simp_rw [map_add_eq_mul] at h₁
  have h₂ : ∑ a : R, ψ a = Finset.univ.sum ↑ψ := rfl
  rw [← Finset.mul_sum]; rw [h₂] at h₁
  exact eq_zero_of_mul_eq_self_left hb h₁

/--
theorem `sum_eq_card_of_eq_one` / 定理 `sum_eq_card_of_eq_one`

English:
theorem sum_eq_card_of_eq_one
  given: {ψ : AddChar R R'} (hψ : ψ = 1)
  proof: by simp [hψ]

中文:
定理 sum_eq_card_of_eq_one
  条件: {ψ : AddChar R R'} (hψ : ψ = 1)
  证明: by simp [hψ]
-/
theorem sum_eq_card_of_eq_one {ψ : AddChar R R'} (hψ : ψ = 1) :
    ∑ a, ψ a = Fintype.card R := by simp [hψ]

end sum

/--
theorem `sum_mulShift` / 定理 `sum_mulShift`

English:
theorem sum_mulShift
  statement: {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
  proof: by
  split_ifs with h
  · -- case `b = 0`
    simp only [h, mul_zero, map_zero_eq_one, Finset.sum_const, Nat.smul_one_eq_cast]
    rfl
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    exact mod_cast sum_eq_zero_of_ne_one (hψ h)

中文:
定理 sum_mulShift
  结论: {R : 类型} [CommRing R] [Fintype R] [DecidableEq R]
  证明: by
  split_ifs with h
  · -- case `b = 0`
    simp only [h, mul_zero, map_zero_eq_one, Finset.sum_const, Nat.smul_one_eq_cast]
    rfl
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    exact mod_cast sum_eq_zero_of_ne_one (hψ h)

Depends on / 依赖: Finset, Finset.sum_const, Nat.smul_one_eq_cast, map_zero_eq_one, mod_cast, mul_comm, mul_zero, simp_rw, smul_one_eq_cast, split_ifs, sum_const, sum_eq_zero_of_ne_one
-/
theorem sum_mulShift {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar R R'} (b : R)
    (hψ : IsPrimitive ψ) : ∑ x : R, ψ (x * b) = if b = 0 then Fintype.card R else 0 := by
  split_ifs with h
  · -- case `b = 0`
    simp only [h, mul_zero, map_zero_eq_one, Finset.sum_const, Nat.smul_one_eq_cast]
    rfl
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    exact mod_cast sum_eq_zero_of_ne_one (hψ h)

/-!
### Complex-valued additive characters
-/

section Ring

variable {R : Type*} [CommRing R]

/--
lemma `starComp_eq_inv` / 引理 `starComp_eq_inv`

English:
lemma starComp_eq_inv
  given: (hR : 0 < ringChar R) {φ : AddChar R Complex}
  proof: by
  ext1 a
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe,
    Function.comp_apply, inv_apply']
have H := Complex.norm_eq_one_of_mem_rootsOfUnity φ.val_mem_rootsOfUnity a hR
  exact (Complex.inv_eq_conj H).symm

中文:
引理 starComp_eq_inv
  条件: (hR : 0 < ringChar R) {φ : AddChar R Complex}
  证明: by
  ext1 a
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe,
    Function.comp_apply, inv_apply']
have H := Complex.norm_eq_one_of_mem_rootsOfUnity φ.val_mem_rootsOfUnity a hR
  exact (Complex.inv_eq_conj H).symm

Depends on / 依赖: Complex.inv_eq_conj, Complex.norm_eq_one_of_mem_rootsOfUnity, Function, Function.comp_apply, LocallyFiniteOrder, MonoidHom, MonoidHom.coe_coe, MonoidHom.coe_compAddChar, RingHom, RingHom.toMonoidHom_eq_coe, _root_, _root_.LocallyFiniteOrder.toLocallyFiniteOrderTop, coe_coe, coe_compAddChar, comp_apply, inv_apply, inv_eq_conj, norm_eq_one_of_mem_rootsOfUnity, toLocallyFiniteOrderTop, toMonoidHom_eq_coe
-/
lemma starComp_eq_inv (hR : 0 < ringChar R) {φ : AddChar R Complex} :
    (starRingEnd Complex).compAddChar φ = φ⁻¹ := by
  ext1 a
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe,
    Function.comp_apply, inv_apply']
have H := Complex.norm_eq_one_of_mem_rootsOfUnity φ.val_mem_rootsOfUnity a hR
  exact (Complex.inv_eq_conj H).symm

/--
lemma `starComp_apply` / 引理 `starComp_apply`

English:
lemma starComp_apply
  given: (hR : 0 < ringChar R) {φ : AddChar R Complex} (a : R)
  proof: by
  rw [← starComp_eq_inv hR]
  rfl

中文:
引理 starComp_apply
  条件: (hR : 0 < ringChar R) {φ : AddChar R Complex} (a : R)
  证明: by
  rw [← starComp_eq_inv hR]
  rfl

Depends on / 依赖: starComp_eq_inv
-/
lemma starComp_apply (hR : 0 < ringChar R) {φ : AddChar R Complex} (a : R) :
    (starRingEnd Complex) (φ a) = φ⁻¹ a := by
  rw [← starComp_eq_inv hR]
  rfl

end Ring

end AddChar
