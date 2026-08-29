/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!

# The exponent of purely inseparable extensions

This file defines the exponent of a purely inseparable extension (if one exists) and
some related results.

Most results are stated using `ringExpChar K` rather than using `[ExpChar K p]` parameter because
it gives cleaner API. To use the results in a context with `[ExpChar K p]`, consider using
`ringExpChar.eq K p` for substitution.

## Main definitions

- `IsPurelyInseparable.HasExponent`: typeclass to assert a purely inseparable field extension
  `L / K` has an exponent, that is a smallest natural number `e` such that
  `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`.
- `IsPurelyInseparable.exponent`: the exponent of a purely inseparable field extension.
- `IsPurelyInseparable.elemExponent`: the exponent of an element of a purely inseparable
  field extension, that is the smallest natural number `e` such that `a ^ ringExpChar K ^ e ∈ K`.
- `IsPurelyInseparable.iterateFrobenius`: the iterated Frobenius map (ring homomorphism) `L →+* K`
  for purely inseparable field extension `L / K` with exponent; for `n ≥ exponent K L`, it acts like
  `x ↦ x ^ p ^ n` but the codomain is the base field `K`.
- `IsPurelyInseparable.iterateFrobeniusₛₗ`: version of `iterateFrobenius` as a semilinear map over
  a subfield `F` of `K`, w.r.t. the iterated Frobenius homomorphism on `F`.

## Tags

purely inseparable

-/

@[expose] public section

namespace IsPurelyInseparable

variable (F K L : Type*)

section Ring

variable [CommRing K] [Ring L] [Algebra K L]

/-- A predicate class on a ring extension saying that there is a natural number `e`
such that `a ^ ringExpChar K ^ e ∈ K` for all `a ∈ L`. -/
@[mk_iff]
/--
Definition of `HasExponent` / `HasExponent` 的定义

English:
class HasExponent
  parameters: : Prop where
  axioms and operations (1):
    - has_exponent : exists e, forall a, a ^ ringExpChar K ^ e in (algebraMap K L).range

中文:
类 有Exponent
  参数: : 命题 where
  公理与运算 (1 个):
    - has_exponent : 存在 e, 对任意 a, a ^ ringExpChar K ^ e in (algebraMap K L).range
-/
class HasExponent : Prop where
  has_exponent : exists e, forall a, a ^ ringExpChar K ^ e in (algebraMap K L).range

/--
theorem `hasExponent_iff'` / 定理 `hasExponent_iff'`

English:
theorem hasExponent_iff'
  given: (p : Nat) [ExpChar K p]
  proof: ringExpChar.eq K p ▸ hasExponent_iff K L

中文:
定理 hasExponent_iff'
  条件: (p : 自然数) [ExpChar K p]
  证明: ringExpChar.eq K p ▸ hasExponent_iff K L

Depends on / 依赖: hasExponent_iff, ringExpChar, ringExpChar.eq
-/
theorem hasExponent_iff' (p : Nat) [ExpChar K p] :
    HasExponent K L ↔ exists e, forall (a : L), a ^ p ^ e in (algebraMap K L).range :=
  ringExpChar.eq K p ▸ hasExponent_iff K L

open scoped Classical in
/--
Definition of `exponent` / `exponent` 的定义

English:
definition exponent
  signature: [HasExponent K L]
  body: Nat.find ‹HasExponent K L›.has_exponent

中文:
定义 exponent
  签名: [有Exponent K L]
  定义体: Nat.find ‹HasExponent K L›.has_exponent

Depends on / 依赖: HasExponent, Nat.find, has_exponent
-/
noncomputable def exponent [HasExponent K L] : Nat :=
  Nat.find ‹HasExponent K L›.has_exponent

variable {L}

/--
theorem `exponent_def` / 定理 `exponent_def`

English:
theorem exponent_def
  given: [HasExponent K L] (a : L)
  proof: by
  classical
  exact Nat.find_spec ‹HasExponent K L›.has_exponent a

中文:
定理 exponent_def
  条件: [有Exponent K L] (a : L)
  证明: by
  classical
  exact Nat.find_spec ‹HasExponent K L›.has_exponent a

Depends on / 依赖: HasExponent, Nat.find_spec, classical, find_spec, has_exponent
-/
theorem exponent_def [HasExponent K L] (a : L) :
    a ^ ringExpChar K ^ exponent K L in (algebraMap K L).range := by
  classical
  exact Nat.find_spec ‹HasExponent K L›.has_exponent a

/--
theorem `exponent_def'` / 定理 `exponent_def'`

English:
theorem exponent_def'
  given: [HasExponent K L] (p : Nat) [ExpChar K p] (a : L)
  proof: ringExpChar.eq K p ▸ exponent_def K a

中文:
定理 exponent_def'
  条件: [有Exponent K L] (p : 自然数) [ExpChar K p] (a : L)
  证明: ringExpChar.eq K p ▸ exponent_def K a

Depends on / 依赖: exponent_def, ringExpChar, ringExpChar.eq
-/
theorem exponent_def' [HasExponent K L] (p : Nat) [ExpChar K p] (a : L) :
    a ^ p ^ exponent K L in (algebraMap K L).range :=
  ringExpChar.eq K p ▸ exponent_def K a

variable {K}

/--
theorem `exponent_min` / 定理 `exponent_min`

English:
theorem exponent_min
  given: [HasExponent K L] {e : Nat} (h : e < exponent K L)
  proof: by
  classical
exact not_forall.mp Nat.find_min ‹HasExponent K L›.has_exponent h

中文:
定理 exponent_min
  条件: [有Exponent K L] {e : 自然数} (h : e < exponent K L)
  证明: by
  classical
exact not_forall.mp Nat.find_min ‹HasExponent K L›.has_exponent h

Depends on / 依赖: HasExponent, Nat.find_min, classical, find_min, has_exponent, not_forall, not_forall.mp
-/
theorem exponent_min [HasExponent K L] {e : Nat} (h : e < exponent K L) :
    exists a, a ^ ringExpChar K ^ e ∉ (algebraMap K L).range := by
  classical
exact not_forall.mp Nat.find_min ‹HasExponent K L›.has_exponent h

/--
theorem `exponent_min'` / 定理 `exponent_min'`

English:
theorem exponent_min'
  given: [HasExponent K L] (p : Nat) [ExpChar K p] {e : Nat} (h : e < exponent K L)
  proof: ringExpChar.eq K p ▸ exponent_min h

中文:
定理 exponent_min'
  条件: [有Exponent K L] (p : 自然数) [ExpChar K p] {e : 自然数} (h : e < exponent K L)
  证明: ringExpChar.eq K p ▸ exponent_min h

Depends on / 依赖: exponent_min, ringExpChar, ringExpChar.eq
-/
theorem exponent_min' [HasExponent K L] (p : Nat) [ExpChar K p] {e : Nat} (h : e < exponent K L) :
    exists a, a ^ p ^ e ∉ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ exponent_min h

end Ring

section IsDomain

variable [Field K] [Ring L] [IsDomain L] [Algebra K L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasExponent
  signature: K L] : IsPurelyInseparable K L
  body: let ⟨n, h⟩ := ‹HasExponent K L›.has_exponent
  (isPurelyInseparable_iff_pow_mem K (ringExpChar K)).mpr fun x => ⟨n, h x⟩

中文:
实例 [有Exponent
  签名: K L] : 是纯不可分 K L
  定义体: let ⟨n, h⟩ := ‹HasExponent K L›.has_exponent
  (isPurelyInseparable_iff_pow_mem K (ringExpChar K)).mpr fun x => ⟨n, h x⟩

Depends on / 依赖: HasExponent, has_exponent, isPurelyInseparable_iff_pow_mem, ringExpChar
-/
instance [HasExponent K L] : IsPurelyInseparable K L :=
  let ⟨n, h⟩ := ‹HasExponent K L›.has_exponent
  (isPurelyInseparable_iff_pow_mem K (ringExpChar K)).mpr fun x => ⟨n, h x⟩

end IsDomain

section Field

open Polynomial

variable [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
variable {L}

open scoped Classical in
/--
Definition of `elemExponent` / `elemExponent` 的定义

English:
definition elemExponent
  signature: (a : L)
  body: Nat.find minpoly_eq_X_pow_sub_C K (ringExpChar K) a

中文:
定义 elemExponent
  签名: (a : L)
  定义体: Nat.find minpoly_eq_X_pow_sub_C K (ringExpChar K) a

Depends on / 依赖: Nat.find, minpoly_eq_X_pow_sub_C, ringExpChar
-/
noncomputable def elemExponent (a : L) : Nat :=
Nat.find minpoly_eq_X_pow_sub_C K (ringExpChar K) a

variable {K} in
/--
theorem `elemExponent_eq_zero_of_mem_range` / 定理 `elemExponent_eq_zero_of_mem_range`

English:
theorem elemExponent_eq_zero_of_mem_range
  given: {a : L} (h : a in (algebraMap K L).range)
  proof: by
  classical
  apply (Nat.find_eq_zero _).mpr
  rw [pow_zero]; rw [pow_one]
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy ▸ minpoly.eq_X_sub_C L y⟩

中文:
定理 elemExponent_eq_zero_of_mem_range
  条件: {a : L} (h : a in (algebraMap K L).range)
  证明: by
  classical
  apply (Nat.find_eq_zero _).mpr
  rw [pow_zero]; rw [pow_one]
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy ▸ minpoly.eq_X_sub_C L y⟩

Depends on / 依赖: Nat.find_eq_zero, classical, eq_X_sub_C, find_eq_zero, minpoly, minpoly.eq_X_sub_C, pow_one, pow_zero
-/
theorem elemExponent_eq_zero_of_mem_range {a : L} (h : a in (algebraMap K L).range) :
    elemExponent K a = 0 := by
  classical
  apply (Nat.find_eq_zero _).mpr
  rw [pow_zero]; rw [pow_one]
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy ▸ minpoly.eq_X_sub_C L y⟩

/--
theorem `elemExponent_eq_zero_of_charZero` / 定理 `elemExponent_eq_zero_of_charZero`

English:
theorem elemExponent_eq_zero_of_charZero
  given: (a : L) [CharZero K]
  proof: elemExponent_eq_zero_of_mem_range surjective_algebraMap_of_isSeparable K L a

中文:
定理 elemExponent_eq_zero_of_charZero
  条件: (a : L) [特征零 K]
  证明: elemExponent_eq_zero_of_mem_range surjective_algebraMap_of_isSeparable K L a

Depends on / 依赖: elemExponent_eq_zero_of_mem_range, surjective_algebraMap_of_isSeparable
-/
theorem elemExponent_eq_zero_of_charZero (a : L) [CharZero K] :
    elemExponent K a = 0 :=
elemExponent_eq_zero_of_mem_range surjective_algebraMap_of_isSeparable K L a

open scoped Classical in
/--
Definition of `elemReduct` / `elemReduct` 的定义

English:
definition elemReduct
  signature: (a : L)
  body: Classical.choose Nat.find_spec minpoly_eq_X_pow_sub_C K (ringExpChar K) a

中文:
定义 elemReduct
  签名: (a : L)
  定义体: Classical.choose Nat.find_spec minpoly_eq_X_pow_sub_C K (ringExpChar K) a

Depends on / 依赖: Classical, Classical.choose, Nat.find_spec, find_spec, minpoly_eq_X_pow_sub_C, ringExpChar
-/
noncomputable def elemReduct (a : L) : K :=
Classical.choose Nat.find_spec minpoly_eq_X_pow_sub_C K (ringExpChar K) a

/--
theorem `minpoly_eq` / 定理 `minpoly_eq`

English:
theorem minpoly_eq
  given: (a : L)
  proof: by
  classical
exact Classical.choose_spec Nat.find_spec minpoly_eq_X_pow_sub_C K (ringExpChar K) a

中文:
定理 minpoly_eq
  条件: (a : L)
  证明: by
  classical
exact Classical.choose_spec Nat.find_spec minpoly_eq_X_pow_sub_C K (ringExpChar K) a

Depends on / 依赖: Classical, Classical.choose_spec, Nat.find_spec, choose_spec, classical, find_spec, minpoly_eq_X_pow_sub_C, ringExpChar
-/
theorem minpoly_eq (a : L) :
    minpoly K a = X ^ ringExpChar K ^ elemExponent K a - C (elemReduct K a) := by
  classical
exact Classical.choose_spec Nat.find_spec minpoly_eq_X_pow_sub_C K (ringExpChar K) a

/--
theorem `minpoly_eq'` / 定理 `minpoly_eq'`

English:
theorem minpoly_eq'
  given: (p : Nat) [ExpChar K p] (a : L)
  proof: ringExpChar.eq K p ▸ minpoly_eq K a

中文:
定理 minpoly_eq'
  条件: (p : 自然数) [ExpChar K p] (a : L)
  证明: ringExpChar.eq K p ▸ minpoly_eq K a

Depends on / 依赖: minpoly_eq, ringExpChar, ringExpChar.eq
-/
theorem minpoly_eq' (p : Nat) [ExpChar K p] (a : L) :
    minpoly K a = X ^ p ^ elemExponent K a - C (elemReduct K a) :=
  ringExpChar.eq K p ▸ minpoly_eq K a

/--
theorem `minpoly_natDegree_eq` / 定理 `minpoly_natDegree_eq`

English:
theorem minpoly_natDegree_eq
  given: (a : L)
  proof: by
  rw [minpoly_eq K a]; rw [natDegree_sub_C]; rw [natDegree_pow]; rw [natDegree_X]; rw [mul_one]

中文:
定理 minpoly_natDegree_eq
  条件: (a : L)
  证明: by
  rw [minpoly_eq K a]; rw [natDegree_sub_C]; rw [natDegree_pow]; rw [natDegree_X]; rw [mul_one]

Depends on / 依赖: minpoly_eq, mul_one, natDegree_X, natDegree_pow, natDegree_sub_C
-/
theorem minpoly_natDegree_eq (a : L) :
    (minpoly K a).natDegree = ringExpChar K ^ elemExponent K a := by
  rw [minpoly_eq K a]; rw [natDegree_sub_C]; rw [natDegree_pow]; rw [natDegree_X]; rw [mul_one]

/--
theorem `minpoly_natDegree_eq'` / 定理 `minpoly_natDegree_eq'`

English:
theorem minpoly_natDegree_eq'
  given: (p : Nat) [ExpChar K p] (a : L)
  proof: ringExpChar.eq K p ▸ minpoly_natDegree_eq K a

中文:
定理 minpoly_natDegree_eq'
  条件: (p : 自然数) [ExpChar K p] (a : L)
  证明: ringExpChar.eq K p ▸ minpoly_natDegree_eq K a

Depends on / 依赖: minpoly_natDegree_eq, ringExpChar, ringExpChar.eq
-/
theorem minpoly_natDegree_eq' (p : Nat) [ExpChar K p] (a : L) :
    (minpoly K a).natDegree = p ^ elemExponent K a :=
  ringExpChar.eq K p ▸ minpoly_natDegree_eq K a

/--
theorem `algebraMap_elemReduct_eq` / 定理 `algebraMap_elemReduct_eq`

English:
theorem algebraMap_elemReduct_eq
  given: (a : L)
  proof: by
  have := minpoly_eq K a ▸ minpoly.aeval K a
  rwa [map_sub, aeval_C, map_pow, aeval_X, sub_eq_zero, eq_comm] at this

中文:
定理 algebraMap_elemReduct_eq
  条件: (a : L)
  证明: by
  have := minpoly_eq K a ▸ minpoly.aeval K a
  rwa [map_sub, aeval_C, map_pow, aeval_X, sub_eq_zero, eq_comm] at this

Depends on / 依赖: aeval_C, aeval_X, eq_comm, map_pow, map_sub, minpoly, minpoly.aeval, minpoly_eq, sub_eq_zero
-/
theorem algebraMap_elemReduct_eq (a : L) :
    algebraMap K L (elemReduct K a) = a ^ ringExpChar K ^ elemExponent K a := by
  have := minpoly_eq K a ▸ minpoly.aeval K a
  rwa [map_sub, aeval_C, map_pow, aeval_X, sub_eq_zero, eq_comm] at this

/--
theorem `algebraMap_elemReduct_eq'` / 定理 `algebraMap_elemReduct_eq'`

English:
theorem algebraMap_elemReduct_eq'
  given: (p : Nat) [ExpChar K p] (a : L)
  proof: ringExpChar.eq K p ▸ algebraMap_elemReduct_eq K a

中文:
定理 algebraMap_elemReduct_eq'
  条件: (p : 自然数) [ExpChar K p] (a : L)
  证明: ringExpChar.eq K p ▸ algebraMap_elemReduct_eq K a

Depends on / 依赖: algebraMap_elemReduct_eq, ringExpChar, ringExpChar.eq
-/
theorem algebraMap_elemReduct_eq' (p : Nat) [ExpChar K p] (a : L) :
    algebraMap K L (elemReduct K a) = a ^ p ^ elemExponent K a :=
  ringExpChar.eq K p ▸ algebraMap_elemReduct_eq K a

/--
theorem `elemExponent_def` / 定理 `elemExponent_def`

English:
theorem elemExponent_def
  given: (a : L)
  proof: RingHom.mem_range.mpr ⟨_, algebraMap_elemReduct_eq K a⟩

中文:
定理 elemExponent_def
  条件: (a : L)
  证明: RingHom.mem_range.mpr ⟨_, algebraMap_elemReduct_eq K a⟩

Depends on / 依赖: RingHom, RingHom.mem_range.mpr, algebraMap_elemReduct_eq, mem_range
-/
theorem elemExponent_def (a : L) :
    a ^ ringExpChar K ^ elemExponent K a in (algebraMap K L).range :=
RingHom.mem_range.mpr ⟨_, algebraMap_elemReduct_eq K a⟩

/--
theorem `elemExponent_def'` / 定理 `elemExponent_def'`

English:
theorem elemExponent_def'
  given: (p : Nat) [ExpChar K p] (a : L)
  proof: ringExpChar.eq K p ▸ elemExponent_def K a

中文:
定理 elemExponent_def'
  条件: (p : 自然数) [ExpChar K p] (a : L)
  证明: ringExpChar.eq K p ▸ elemExponent_def K a

Depends on / 依赖: elemExponent_def, ringExpChar, ringExpChar.eq
-/
theorem elemExponent_def' (p : Nat) [ExpChar K p] (a : L) :
    a ^ p ^ elemExponent K a in (algebraMap K L).range :=
  ringExpChar.eq K p ▸ elemExponent_def K a

variable {K} in
/--
theorem `elemExponent_le_of_pow_mem` / 定理 `elemExponent_le_of_pow_mem`

English:
theorem elemExponent_le_of_pow_mem
  statement: {a : L} {n : Nat}
  proof: by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact elemExponent_eq_zero_of_charZero K a ▸ Nat.zero_le _
· obtain ⟨y, hy⟩ := RingHom.mem_range.mp h
    let f := X ^ ringExpChar K ^ n - C y
    have hf₁ : f.aeval a = 0 := by rwa [map_sub, aeval_C, aeval_X_pow, sub_eq_ze

中文:
定理 elemExponent_le_of_pow_mem
  结论: {a : L} {n : 自然数}
  证明: by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact elemExponent_eq_zero_of_charZero K a ▸ Nat.zero_le _
· obtain ⟨y, hy⟩ := RingHom.mem_range.mp h
    let f := X ^ ringExpChar K ^ n - C y
    have hf₁ : f.aeval a = 0 := by rwa [map_sub, aeval_C, aeval_X_pow, sub_eq_ze

Depends on / 依赖: ExpChar, ExpChar.exists, Nat.pos_iff_ne_zero.mp, Nat.zero_le, RingHom, RingHom.mem_range.mp, aeval_C, aeval_X_pow, elemExponent_eq_zero_of_charZero, eq_comm, expChar_pow_pos, f.Monic, f.aeval, f.natDegree, map_sub, mem_range, monic_X_pow_sub_C, natDegree, natDegree_X, natDegree_pow
-/
theorem elemExponent_le_of_pow_mem {a : L} {n : Nat}
    (h : a ^ ringExpChar K ^ n in (algebraMap K L).range) : elemExponent K a <= n := by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact elemExponent_eq_zero_of_charZero K a ▸ Nat.zero_le _
· obtain ⟨y, hy⟩ := RingHom.mem_range.mp h
    let f := X ^ ringExpChar K ^ n - C y
    have hf₁ : f.aeval a = 0 := by rwa [map_sub, aeval_C, aeval_X_pow, sub_eq_zero, eq_comm]
have hf₂ : f.Monic := monic_X_pow_sub_C y Nat.pos_iff_ne_zero.mp expChar_pow_pos K _ _
    have hf₃ : f.natDegree = ringExpChar K ^ n := by
      rw [natDegree_sub_C]; rw [natDegree_pow]; rw [natDegree_X]; rw [mul_one]
exact (Nat.pow_le_pow_iff_right <| Nat.Prime.one_lt hp).mp
      ringExpChar.eq K p ▸ hf₃ ▸ minpoly_natDegree_eq K a ▸
      natDegree_le_natDegree (minpoly.min K a hf₂ hf₁)

variable {K} in
/--
theorem `elemExponent_le_of_pow_mem'` / 定理 `elemExponent_le_of_pow_mem'`

English:
theorem elemExponent_le_of_pow_mem'
  statement: (p : Nat) [ExpChar K p] {a : L} {n : Nat}
  proof: elemExponent_le_of_pow_mem (ringExpChar.eq K p ▸ h)

中文:
定理 elemExponent_le_of_pow_mem'
  结论: (p : 自然数) [ExpChar K p] {a : L} {n : 自然数}
  证明: elemExponent_le_of_pow_mem (ringExpChar.eq K p ▸ h)

Depends on / 依赖: elemExponent_le_of_pow_mem, ringExpChar, ringExpChar.eq
-/
theorem elemExponent_le_of_pow_mem' (p : Nat) [ExpChar K p] {a : L} {n : Nat}
    (h : a ^ p ^ n in (algebraMap K L).range) : elemExponent K a <= n :=
  elemExponent_le_of_pow_mem (ringExpChar.eq K p ▸ h)

variable {K} in
/--
theorem `elemExponent_min` / 定理 `elemExponent_min`

English:
theorem elemExponent_min
  given: {a : L} {n : Nat} (h : n < elemExponent K a)
  proof: fun hn => (Nat.not_lt_of_ge <| elemExponent_le_of_pow_mem hn) h

中文:
定理 elemExponent_min
  条件: {a : L} {n : 自然数} (h : n < elemExponent K a)
  证明: fun hn => (Nat.not_lt_of_ge <| elemExponent_le_of_pow_mem hn) h

Depends on / 依赖: Nat.not_lt_of_ge, elemExponent_le_of_pow_mem, not_lt_of_ge
-/
theorem elemExponent_min {a : L} {n : Nat} (h : n < elemExponent K a) :
    a ^ ringExpChar K ^ n ∉ (algebraMap K L).range :=
  fun hn => (Nat.not_lt_of_ge <| elemExponent_le_of_pow_mem hn) h

/--
theorem `elemExponent_min'` / 定理 `elemExponent_min'`

English:
theorem elemExponent_min'
  given: (p : Nat) [ExpChar K p] {a : L} {n : Nat} (h : n < elemExponent K a)
  proof: ringExpChar.eq K p ▸ elemExponent_min h

中文:
定理 elemExponent_min'
  条件: (p : 自然数) [ExpChar K p] {a : L} {n : 自然数} (h : n < elemExponent K a)
  证明: ringExpChar.eq K p ▸ elemExponent_min h

Depends on / 依赖: elemExponent_min, ringExpChar, ringExpChar.eq
-/
theorem elemExponent_min' (p : Nat) [ExpChar K p] {a : L} {n : Nat} (h : n < elemExponent K a) :
    a ^ p ^ n ∉ (algebraMap K L).range :=
  ringExpChar.eq K p ▸ elemExponent_min h

/--
theorem `elemExponent_le_exponent` / 定理 `elemExponent_le_exponent`

English:
theorem elemExponent_le_exponent
  given: [HasExponent K L] (a : L)
  proof: elemExponent_le_of_pow_mem exponent_def K a

中文:
定理 elemExponent_le_exponent
  条件: [有Exponent K L] (a : L)
  证明: elemExponent_le_of_pow_mem exponent_def K a

Depends on / 依赖: elemExponent_le_of_pow_mem, exponent_def
-/
theorem elemExponent_le_exponent [HasExponent K L] (a : L) :
    elemExponent K a <= exponent K L :=
elemExponent_le_of_pow_mem exponent_def K a

variable {K} in
/--
Instance `hasExponent_of_finiteDimensional` / 实例 `hasExponent_of_finiteDimensional`

English:
instance hasExponent_of_finiteDimensional
  signature: [FiniteDimensional K L]
  body: by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact ⟨0, fun a => surjective_algebraMap_of_isSeparable K L _⟩
  · let e := Nat.log (ringExpChar K) (Module.finrank K L)
    refine ⟨e, fun a => ⟨elemReduct K a ^ ringExpChar K ^ (e - elemExponent K a), ?_⟩⟩
    have h_elem

中文:
实例 hasExponent_of_finiteDimensional
  签名: [有限维 K L]
  定义体: by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact ⟨0, fun a => surjective_algebraMap_of_isSeparable K L _⟩
  · let e := Nat.log (ringExpChar K) (Module.finrank K L)
    refine ⟨e, fun a => ⟨elemReduct K a ^ ringExpChar K ^ (e - elemExponent K a), ?_⟩⟩
    have h_elem

Depends on / 依赖: ExpChar, ExpChar.exists, Module, Module.finrank, Nat.Prime.one_lt, Nat.le_log_of_pow_le, Nat.log, algebraMap_elemReduct_eq, elemExponent, elemReduct, finrank, h_elemexp_bound, le_log_of_pow_le, map_pow, minpoly, minpoly.natDegree_le, minpoly_natDegree_eq, natDegree_le, one_lt, ringExpChar
-/
instance hasExponent_of_finiteDimensional [FiniteDimensional K L] :
    HasExponent K L := by
  let ⟨p, _⟩ := ExpChar.exists K
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · exact ⟨0, fun a => surjective_algebraMap_of_isSeparable K L _⟩
  · let e := Nat.log (ringExpChar K) (Module.finrank K L)
    refine ⟨e, fun a => ⟨elemReduct K a ^ ringExpChar K ^ (e - elemExponent K a), ?_⟩⟩
    have h_elemexp_bound (a : L) : elemExponent K a <= e :=
      Nat.le_log_of_pow_le (Nat.Prime.one_lt <| ringExpChar.eq K p ▸ hp)
        (minpoly_natDegree_eq K a ▸ minpoly.natDegree_le a)
    rw [map_pow]; rw [algebraMap_elemReduct_eq]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.add_sub_cancel' (h_elemexp_bound a)]

end Field

section Frobenius

/-
This section defines the iterated Frobenius map `x ↦ x ^ p ^ n` for a purely inseparable
field extension `L / K` with exponent, with the base field `K` as a codomain, when
`n ≥ exponent K L`.
We define it both as a ring homomorphism and a semilinear map over a subfield `F` of `K`.

Implementation note: the API exposes arguments `{n : ℕ} (hn : exponent K L ≤ n)` to define the
action `x ↦ x ^ p ^ n` instead of just `(n : ℕ)` with action `x ↦ x ^ p ^ (exponent K L + n)`
to avoid problems with definitional equality when using the semilinear map version.
-/

variable [Field K] [Field L] [Algebra K L] [HasExponent K L]
variable (p : Nat) [ExpChar K p]

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def iterateFrobeniusAux (n : Nat)
  body: fun a => elemReduct K a ^ p ^ (n - elemExponent K a)

中文:
定义 noncomputable
  签名: def iterateFrobeniusAux (n : 自然数)
  定义体: fun a => elemReduct K a ^ p ^ (n - elemExponent K a)
-/
private noncomputable def iterateFrobeniusAux (n : Nat) : L -> K :=
  fun a => elemReduct K a ^ p ^ (n - elemExponent K a)

variable {L} in
/--
theorem `algebraMap_iterateFrobeniusAux` / 定理 `algebraMap_iterateFrobeniusAux`

English:
theorem algebraMap_iterateFrobeniusAux
  given: {n : Nat} (hn : exponent K L <= n) (a : L)
  proof: by
  rw [iterateFrobeniusAux]; rw [map_pow]; rw [algebraMap_elemReduct_eq' K p]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.add_sub_cancel' (elemExponent_le_exponent K a).trans hn]

中文:
定理 algebraMap_iterateFrobeniusAux
  条件: {n : 自然数} (hn : exponent K L <= n) (a : L)
  证明: by
  rw [iterateFrobeniusAux]; rw [map_pow]; rw [algebraMap_elemReduct_eq' K p]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.add_sub_cancel' (elemExponent_le_exponent K a).trans hn]
-/
private theorem algebraMap_iterateFrobeniusAux {n : Nat} (hn : exponent K L <= n) (a : L) :
    algebraMap K L (iterateFrobeniusAux K L p n a) = a ^ p ^ n := by
  rw [iterateFrobeniusAux]; rw [map_pow]; rw [algebraMap_elemReduct_eq' K p]; rw [← pow_mul]; rw [← pow_add]; rw [Nat.add_sub_cancel' (elemExponent_le_exponent K a).trans hn]

section RingHom

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `iterateFrobenius` / `iterateFrobenius` 的定义

English:
definition iterateFrobenius
  signature: {n : Nat} (hn : exponent K L <= n)
  body: iterateFrobeniusAux K L p n
  map_zero' := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_zero]; rw [algebraMap_iterateFrobeniusAux K p hn 0]; rw [zero_pow]
exact Nat.pos_iff_ne_zero.mp expChar_pow_pos K p n
  map_add' a b := by
    have inj := (algebraMap K L).injective
    ha

中文:
定义 iterateFrobenius
  签名: {n : 自然数} (hn : exponent K L <= n)
  定义体: iterateFrobeniusAux K L p n
  map_zero' := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_zero]; rw [algebraMap_iterateFrobeniusAux K p hn 0]; rw [zero_pow]
exact Nat.pos_iff_ne_zero.mp expChar_pow_pos K p n
  map_add' a b := by
    have inj := (algebraMap K L).injective
    ha

Depends on / 依赖: iterateFrobeniusAux
-/
noncomputable def iterateFrobenius {n : Nat} (hn : exponent K L <= n) : L ->+* K where
  toFun := iterateFrobeniusAux K L p n
  map_zero' := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_zero]; rw [algebraMap_iterateFrobeniusAux K p hn 0]; rw [zero_pow]
exact Nat.pos_iff_ne_zero.mp expChar_pow_pos K p n
  map_add' a b := by
    have inj := (algebraMap K L).injective
    have : ExpChar L p := expChar_of_injective_ringHom inj p
    apply inj
    rw [(algebraMap K L).map_add]; rw [algebraMap_iterateFrobeniusAux K p hn a]; rw [algebraMap_iterateFrobeniusAux K p hn b]; rw [algebraMap_iterateFrobeniusAux K p hn (a + b)]; rw [add_pow_expChar_pow a b]
  map_one' := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_one]; rw [algebraMap_iterateFrobeniusAux K p hn 1]; rw [one_pow]
  map_mul' a b := by
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_mul]; rw [algebraMap_iterateFrobeniusAux K p hn a]; rw [algebraMap_iterateFrobeniusAux K p hn b]; rw [algebraMap_iterateFrobeniusAux K p hn (a * b)]; rw [mul_pow]

variable {L} in
/--
theorem `algebraMap_iterateFrobenius` / 定理 `algebraMap_iterateFrobenius`

English:
theorem algebraMap_iterateFrobenius
  given: {n : Nat} (hn : exponent K L <= n) (a : L)
  proof: algebraMap_iterateFrobeniusAux K p hn a

中文:
定理 algebraMap_iterateFrobenius
  条件: {n : 自然数} (hn : exponent K L <= n) (a : L)
  证明: algebraMap_iterateFrobeniusAux K p hn a

Depends on / 依赖: algebraMap_iterateFrobeniusAux
-/
theorem algebraMap_iterateFrobenius {n : Nat} (hn : exponent K L <= n) (a : L) :
    algebraMap K L (iterateFrobenius K L p hn a) = a ^ p ^ n :=
  algebraMap_iterateFrobeniusAux K p hn a

variable {K} in
/--
theorem `iterateFrobenius_algebraMap` / 定理 `iterateFrobenius_algebraMap`

English:
theorem iterateFrobenius_algebraMap
  given: {n : Nat} (hn : exponent K L <= n) (a : K)
  proof: by
  apply (algebraMap K L).injective
  rw [map_pow]; rw [algebraMap_iterateFrobenius K p hn]

中文:
定理 iterateFrobenius_algebraMap
  条件: {n : 自然数} (hn : exponent K L <= n) (a : K)
  证明: by
  apply (algebraMap K L).injective
  rw [map_pow]; rw [algebraMap_iterateFrobenius K p hn]

Depends on / 依赖: algebraMap, algebraMap_iterateFrobenius, injective, map_pow
-/
theorem iterateFrobenius_algebraMap {n : Nat} (hn : exponent K L <= n) (a : K) :
    iterateFrobenius K L p hn (algebraMap K L a) = a ^ p ^ n := by
  apply (algebraMap K L).injective
  rw [map_pow]; rw [algebraMap_iterateFrobenius K p hn]

end RingHom

section Semilinear

variable [Field F] [Algebra F K] [Algebra F L] [IsScalarTower F K L]
variable [ExpChar F p]

/--
Definition of `iterateFrobeniusₛₗ` / `iterateFrobeniusₛₗ` 的定义

English:
definition iterateFrobeniusₛₗ
  signature: {n : Nat} (hn : exponent K L <= n)
  body: iterateFrobenius K L p hn
  map_smul' r a := by
    dsimp [iterateFrobenius]
    rw [Algebra.smul_def _ (iterateFrobeniusAux K L p n a)]
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_mul]; rw [← IsScalarTower.algebraMap_apply]; rw [algebraMap_iterateFrobeniusAux K p hn a]; rw [al

中文:
定义 iterateFrobeniusₛₗ
  签名: {n : 自然数} (hn : exponent K L <= n)
  定义体: iterateFrobenius K L p hn
  map_smul' r a := by
    dsimp [iterateFrobenius]
    rw [Algebra.smul_def _ (iterateFrobeniusAux K L p n a)]
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_mul]; rw [← IsScalarTower.algebraMap_apply]; rw [algebraMap_iterateFrobeniusAux K p hn a]; rw [al

Depends on / 依赖: iterateFrobenius
-/
noncomputable def iterateFrobeniusₛₗ {n : Nat} (hn : exponent K L <= n) :
    L ->ₛₗ[_root_.iterateFrobenius F p n] K where
  __ := iterateFrobenius K L p hn
  map_smul' r a := by
    dsimp [iterateFrobenius]
    rw [Algebra.smul_def _ (iterateFrobeniusAux K L p n a)]
    apply (algebraMap K L).injective
    rw [(algebraMap K L).map_mul]; rw [← IsScalarTower.algebraMap_apply]; rw [algebraMap_iterateFrobeniusAux K p hn a]; rw [algebraMap_iterateFrobeniusAux K p hn (r • a)]; rw [iterateFrobenius_def]; rw [map_pow]; rw [Algebra.smul_def]; rw [mul_pow]

/--
theorem `algebraMap_iterateFrobeniusₛₗ` / 定理 `algebraMap_iterateFrobeniusₛₗ`

English:
theorem algebraMap_iterateFrobeniusₛₗ
  given: {n : Nat} (hn : exponent K L <= n) (a : L)
  proof: algebraMap_iterateFrobenius K p hn a

中文:
定理 algebraMap_iterateFrobeniusₛₗ
  条件: {n : 自然数} (hn : exponent K L <= n) (a : L)
  证明: algebraMap_iterateFrobenius K p hn a

Depends on / 依赖: algebraMap_iterateFrobenius
-/
theorem algebraMap_iterateFrobeniusₛₗ {n : Nat} (hn : exponent K L <= n) (a : L) :
    algebraMap K L (iterateFrobeniusₛₗ F K L p hn a) = a ^ p ^ n :=
  algebraMap_iterateFrobenius K p hn a

/--
theorem `iterateFrobeniusₛₗ_algebraMap` / 定理 `iterateFrobeniusₛₗ_algebraMap`

English:
theorem iterateFrobeniusₛₗ_algebraMap
  given: {n : Nat} (hn : exponent K L <= n) (a : K)
  proof: iterateFrobenius_algebraMap L p hn a

中文:
定理 iterateFrobeniusₛₗ_algebraMap
  条件: {n : 自然数} (hn : exponent K L <= n) (a : K)
  证明: iterateFrobenius_algebraMap L p hn a

Depends on / 依赖: iterateFrobenius_algebraMap
-/
theorem iterateFrobeniusₛₗ_algebraMap {n : Nat} (hn : exponent K L <= n) (a : K) :
    iterateFrobeniusₛₗ F K L p hn (algebraMap K L a) = a ^ p ^ n :=
  iterateFrobenius_algebraMap L p hn a

/--
theorem `iterateFrobeniusₛₗ_algebraMap_base` / 定理 `iterateFrobeniusₛₗ_algebraMap_base`

English:
theorem iterateFrobeniusₛₗ_algebraMap_base
  given: {n : Nat} (hn : exponent K L <= n) (a : F)
  proof: by
  apply (algebraMap K L).injective
  rw [← map_pow]; rw [← IsScalarTower.algebraMap_apply]; rw [map_pow]; rw [algebraMap_iterateFrobeniusₛₗ F K L p hn]

中文:
定理 iterateFrobeniusₛₗ_algebraMap_base
  条件: {n : 自然数} (hn : exponent K L <= n) (a : F)
  证明: by
  apply (algebraMap K L).injective
  rw [← map_pow]; rw [← IsScalarTower.algebraMap_apply]; rw [map_pow]; rw [algebraMap_iterateFrobeniusₛₗ F K L p hn]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply, injective, map_pow
-/
theorem iterateFrobeniusₛₗ_algebraMap_base {n : Nat} (hn : exponent K L <= n) (a : F) :
    iterateFrobeniusₛₗ F K L p hn (algebraMap F L a) = (algebraMap F K a) ^ p ^ n := by
  apply (algebraMap K L).injective
  rw [← map_pow]; rw [← IsScalarTower.algebraMap_apply]; rw [map_pow]; rw [algebraMap_iterateFrobeniusₛₗ F K L p hn]

end Semilinear

end Frobenius

end IsPurelyInseparable
