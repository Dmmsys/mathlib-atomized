/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Integer Complement

We define the complement of the integers in the complex plane and give some basic lemmas about it.
We also show that the upper half plane embeds into the integer complement.

-/

@[expose] public section

open UpperHalfPlane

/--
Definition of `Complex.integerComplement` / `Complex.integerComplement` 的定义

English:
definition Complex.integerComplement
  body: (Set.range ((↑) : Int -> Complex))ᶜ

中文:
定义 Complex.integerComplement
  定义体: (Set.range ((↑) : Int -> Complex))ᶜ

Depends on / 依赖: Set.range
-/
def Complex.integerComplement := (Set.range ((↑) : Int -> Complex))ᶜ

namespace Complex

local notation "Complex_Int" => integerComplement

/--
lemma `integerComplement_eq` / 引理 `integerComplement_eq`

English:
lemma integerComplement_eq
  statement: Complex_Int = {z : Complex | ¬ exists (n : Int), n = z}
  proof: rfl

中文:
引理 integerComplement_eq
  结论: Complex_整数 = {z : Complex | ¬ 存在 (n : 整数), n = z}
  证明: rfl
-/
lemma integerComplement_eq : Complex_Int = {z : Complex | ¬ exists (n : Int), n = z} := rfl

/--
lemma `mem_integerComplement_iff` / 引理 `mem_integerComplement_iff`

English:
lemma mem_integerComplement_iff
  given: {x : Complex}
  statement: x in Complex_Int ↔ ¬ exists (n : Int), n = x
  proof: Iff.rfl

@[deprecated (since := "2026-01-29")]
alias integerComplement.mem_iff := mem_integerComplement_iff

@[simp]

中文:
引理 mem_integerComplement_iff
  条件: {x : Complex}
  结论: x in Complex_整数 ↔ ¬ 存在 (n : 整数), n = x
  证明: Iff.rfl

@[deprecated (since := "2026-01-29")]
alias integerComplement.mem_iff := mem_integerComplement_iff

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma mem_integerComplement_iff {x : Complex} : x in Complex_Int ↔ ¬ exists (n : Int), n = x := Iff.rfl

@[deprecated (since := "2026-01-29")]
alias integerComplement.mem_iff := mem_integerComplement_iff

@[simp]
/--
lemma `_root_.UpperHalfPlane.coe_mem_integerComplement` / 引理 `_root_.UpperHalfPlane.coe_mem_integerComplement`

English:
lemma _root_.UpperHalfPlane.coe_mem_integerComplement
  given: (z : ℍ)
  statement: ↑z in Complex_Int
  proof: not_exists.mpr fun x hx => ne_intCast z x hx.symm

@[simp]

中文:
引理 _root_.UpperHalfPlane.coe_mem_integerComplement
  条件: (z : ℍ)
  结论: ↑z in Complex_整数
  证明: not_exists.mpr fun x hx => ne_intCast z x hx.symm

@[simp]

Depends on / 依赖: hx.symm, ne_intCast, not_exists, not_exists.mpr
-/
lemma _root_.UpperHalfPlane.coe_mem_integerComplement (z : ℍ) : ↑z in Complex_Int :=
  not_exists.mpr fun x hx => ne_intCast z x hx.symm

@[simp]
/--
lemma `add_intCast_mem_integerComplement` / 引理 `add_intCast_mem_integerComplement`

English:
lemma add_intCast_mem_integerComplement
  given: {x : Complex} (a : Int)
  statement: x + (a : Complex) in Complex_Int ↔ x in Complex_Int
  proof: by
  simp only [mem_integerComplement_iff, not_iff_not]
  exact ⟨(Exists.elim · fun n hn => ⟨n - a, by simp [hn]⟩),
    (Exists.elim · fun n hn => ⟨n + a, by simp [hn]⟩)⟩

@[deprecated (since := "2026-01-29")]
alias integerComplement.add_coe_int_mem := add_intCast_mem_integerComplement

中文:
引理 add_intCast_mem_integerComplement
  条件: {x : Complex} (a : 整数)
  结论: x + (a : Complex) in Complex_整数 ↔ x in Complex_整数
  证明: by
  simp only [mem_integerComplement_iff, not_iff_not]
  exact ⟨(Exists.elim · fun n hn => ⟨n - a, by simp [hn]⟩),
    (Exists.elim · fun n hn => ⟨n + a, by simp [hn]⟩)⟩

@[deprecated (since := "2026-01-29")]
alias integerComplement.add_coe_int_mem := add_intCast_mem_integerComplement

Depends on / 依赖: Exists, Exists.elim, mem_integerComplement_iff, not_iff_not
-/
lemma add_intCast_mem_integerComplement {x : Complex} (a : Int) : x + (a : Complex) in Complex_Int ↔ x in Complex_Int := by
  simp only [mem_integerComplement_iff, not_iff_not]
  exact ⟨(Exists.elim · fun n hn => ⟨n - a, by simp [hn]⟩),
    (Exists.elim · fun n hn => ⟨n + a, by simp [hn]⟩)⟩

@[deprecated (since := "2026-01-29")]
alias integerComplement.add_coe_int_mem := add_intCast_mem_integerComplement

/--
lemma `integerComplement.ne_zero` / 引理 `integerComplement.ne_zero`

English:
lemma integerComplement.ne_zero
  given: {x : Complex} (hx : x in Complex_Int)
  statement: x != 0
  proof: fun hx' => hx ⟨0, by exact_mod_cast hx'.symm⟩

中文:
引理 integerComplement.ne_zero
  条件: {x : Complex} (hx : x in Complex_整数)
  结论: x != 0
  证明: fun hx' => hx ⟨0, by exact_mod_cast hx'.symm⟩
-/
lemma integerComplement.ne_zero {x : Complex} (hx : x in Complex_Int) : x != 0 :=
  fun hx' => hx ⟨0, by exact_mod_cast hx'.symm⟩

/--
lemma `integerComplement_add_ne_zero` / 引理 `integerComplement_add_ne_zero`

English:
lemma integerComplement_add_ne_zero
  given: {x : Complex} (hx : x in Complex_Int) (a : Int)
  statement: x + (a : Complex) != 0
  proof: integerComplement.ne_zero ((add_intCast_mem_integerComplement a).mpr hx)

中文:
引理 integerComplement_add_ne_zero
  条件: {x : Complex} (hx : x in Complex_整数) (a : 整数)
  结论: x + (a : Complex) != 0
  证明: integerComplement.ne_zero ((add_intCast_mem_integerComplement a).mpr hx)

Depends on / 依赖: add_intCast_mem_integerComplement, integerComplement, integerComplement.ne_zero, ne_zero
-/
lemma integerComplement_add_ne_zero {x : Complex} (hx : x in Complex_Int) (a : Int) : x + (a : Complex) != 0 :=
  integerComplement.ne_zero ((add_intCast_mem_integerComplement a).mpr hx)

/--
lemma `integerComplement.ne_one` / 引理 `integerComplement.ne_one`

English:
lemma integerComplement.ne_one
  given: {x : Complex} (hx : x in Complex_Int)
  statement: x != 1
  proof: fun hx' => hx ⟨1, by exact_mod_cast hx'.symm⟩

中文:
引理 integerComplement.ne_one
  条件: {x : Complex} (hx : x in Complex_整数)
  结论: x != 1
  证明: fun hx' => hx ⟨1, by exact_mod_cast hx'.symm⟩
-/
lemma integerComplement.ne_one {x : Complex} (hx : x in Complex_Int) : x != 1 :=
  fun hx' => hx ⟨1, by exact_mod_cast hx'.symm⟩

/--
lemma `integerComplement_pow_two_ne_pow_two` / 引理 `integerComplement_pow_two_ne_pow_two`

English:
lemma integerComplement_pow_two_ne_pow_two
  given: {x : Complex} (hx : x in Complex_Int) (n : Int)
  statement: x ^ 2 != n ^ 2
  proof: by
  have := not_exists.mp hx n
  have := not_exists.mp hx (-n)
  simp_all [sq_eq_sq_iff_eq_or_eq_neg, eq_comm]

中文:
引理 integerComplement_pow_two_ne_pow_two
  条件: {x : Complex} (hx : x in Complex_整数) (n : 整数)
  结论: x ^ 2 != n ^ 2
  证明: by
  have := not_exists.mp hx n
  have := not_exists.mp hx (-n)
  simp_all [sq_eq_sq_iff_eq_or_eq_neg, eq_comm]

Depends on / 依赖: eq_comm, not_exists, not_exists.mp, sq_eq_sq_iff_eq_or_eq_neg
-/
lemma integerComplement_pow_two_ne_pow_two {x : Complex} (hx : x in Complex_Int) (n : Int) : x ^ 2 != n ^ 2 := by
  have := not_exists.mp hx n
  have := not_exists.mp hx (-n)
  simp_all [sq_eq_sq_iff_eq_or_eq_neg, eq_comm]

/--
lemma `upperHalfPlane_inter_integerComplement` / 引理 `upperHalfPlane_inter_integerComplement`

English:
lemma upperHalfPlane_inter_integerComplement
  proof: by
  apply Set.inter_eq_self_of_subset_left
  exact fun z hz => UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩

中文:
引理 upperHalfPlane_inter_integerComplement
  证明: by
  apply Set.inter_eq_self_of_subset_left
  exact fun z hz => UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩

Depends on / 依赖: Set.inter_eq_self_of_subset_left, UpperHalfPlane, UpperHalfPlane.coe_mem_integerComplement, coe_mem_integerComplement, inter_eq_self_of_subset_left
-/
lemma upperHalfPlane_inter_integerComplement :
    {z : Complex | 0 < z.im} inter Complex_Int = {z : Complex | 0 < z.im} := by
  apply Set.inter_eq_self_of_subset_left
  exact fun z hz => UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩

/--
lemma `_root_.UpperHalfPlane.int_div_mem_integerComplement` / 引理 `_root_.UpperHalfPlane.int_div_mem_integerComplement`

English:
lemma _root_.UpperHalfPlane.int_div_mem_integerComplement
  given: (z : ℍ) {n : Int} (hn : n != 0)
  proof: by
  rintro ⟨_, hm⟩
  have : (n / (z : Complex)).im != 0 := by simp [div_im, z.ne_zero, hn, z.im_ne_zero]
  simpa [← hm]

中文:
引理 _root_.UpperHalfPlane.int_div_mem_integerComplement
  条件: (z : ℍ) {n : 整数} (hn : n != 0)
  证明: by
  rintro ⟨_, hm⟩
  have : (n / (z : Complex)).im != 0 := by simp [div_im, z.ne_zero, hn, z.im_ne_zero]
  simpa [← hm]

Depends on / 依赖: div_im, im_ne_zero, ne_zero, z.im_ne_zero, z.ne_zero
-/
lemma _root_.UpperHalfPlane.int_div_mem_integerComplement (z : ℍ) {n : Int} (hn : n != 0) :
    n / (z : Complex) in Complex_Int := by
  rintro ⟨_, hm⟩
  have : (n / (z : Complex)).im != 0 := by simp [div_im, z.ne_zero, hn, z.im_ne_zero]
  simpa [← hm]

end Complex
