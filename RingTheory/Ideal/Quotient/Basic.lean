/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Congruence.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.FinCases

/-!
# Ideal quotients

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `RingCon.Quotient` for quotients of (possibly non-commutative) semirings.

## Main definitions

- `Ideal.Quotient.Ring`: the quotient of a ring `R` by a two-sided ideal `I : Ideal R`

-/

@[expose] public section

open Set

variable {ι ι' R S : Type*} [Ring R] (I J : Ideal R) {a b : R}

namespace Ideal.Quotient

@[simp]
/--
lemma `mk_span_range` / 引理 `mk_span_range`

English:
lemma mk_span_range
  given: (f : ι -> R) [(span (range f)).IsTwoSided] (i : ι)
  proof: by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

中文:
引理 mk_span_range
  条件: (f : ι -> R) [(span (range f)).是TwoSided] (i : ι)
  证明: by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.subset_span, Quotient, eq_zero_iff_mem, subset_span
-/
lemma mk_span_range (f : ι -> R) [(span (range f)).IsTwoSided] (i : ι) :
    mk (span (.range f)) (f i) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

variable {I} {x y : R}

/--
theorem `zero_eq_one_iff` / 定理 `zero_eq_one_iff`

English:
theorem zero_eq_one_iff
  statement: (0 : R ⧸ I) = 1 ↔ I = ⊤
  proof: eq_comm.trans (Submodule.Quotient.mk_eq_zero _).trans (eq_top_iff_one _).symm

中文:
定理 zero_eq_one_iff
  结论: (0 : R ⧸ I) = 1 ↔ I = ⊤
  证明: eq_comm.trans (Submodule.Quotient.mk_eq_zero _).trans (eq_top_iff_one _).symm

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk_eq_zero, eq_comm, eq_comm.trans, eq_top_iff_one, mk_eq_zero
-/
theorem zero_eq_one_iff : (0 : R ⧸ I) = 1 ↔ I = ⊤ :=
eq_comm.trans (Submodule.Quotient.mk_eq_zero _).trans (eq_top_iff_one _).symm

/--
theorem `zero_ne_one_iff` / 定理 `zero_ne_one_iff`

English:
theorem zero_ne_one_iff
  statement: (0 : R ⧸ I) != 1 ↔ I != ⊤
  proof: not_congr zero_eq_one_iff

中文:
定理 zero_ne_one_iff
  结论: (0 : R ⧸ I) != 1 ↔ I != ⊤
  证明: not_congr zero_eq_one_iff

Depends on / 依赖: not_congr, zero_eq_one_iff
-/
theorem zero_ne_one_iff : (0 : R ⧸ I) != 1 ↔ I != ⊤ :=
  not_congr zero_eq_one_iff

/--
lemma `subsingleton_iff` / 引理 `subsingleton_iff`

English:
lemma subsingleton_iff
  statement: Subsingleton (R ⧸ I) ↔ I = ⊤
  proof: Submodule.Quotient.subsingleton_iff

中文:
引理 subsingleton_iff
  结论: 子单例 (R ⧸ I) ↔ I = ⊤
  证明: Submodule.Quotient.subsingleton_iff
-/
protected lemma subsingleton_iff : Subsingleton (R ⧸ I) ↔ I = ⊤ :=
  Submodule.Quotient.subsingleton_iff

/--
lemma `nontrivial_iff` / 引理 `nontrivial_iff`

English:
lemma nontrivial_iff
  statement: Nontrivial (R ⧸ I) ↔ I != ⊤
  proof: Submodule.Quotient.nontrivial_iff

中文:
引理 nontrivial_iff
  结论: 非平凡 (R ⧸ I) ↔ I != ⊤
  证明: Submodule.Quotient.nontrivial_iff
-/
protected lemma nontrivial_iff : Nontrivial (R ⧸ I) ↔ I != ⊤ :=
  Submodule.Quotient.nontrivial_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (R ⧸ (⊤ : Ideal R))
  body: ⟨⟨0⟩, by rintro ⟨x⟩; exact Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩

中文:
实例 :
  签名: 唯一 (R ⧸ (⊤ : 理想 R))
  定义体: ⟨⟨0⟩, by rintro ⟨x⟩; exact Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩

Depends on / 依赖: Quotient, Quotient.eq_zero_iff_mem.mpr, Submodule, Submodule.mem_top, eq_zero_iff_mem, mem_top
-/
instance : Unique (R ⧸ (⊤ : Ideal R)) :=
  ⟨⟨0⟩, by rintro ⟨x⟩; exact Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩

variable [I.IsTwoSided]

-- this instance is harder to find than the one via `Algebra α (R ⧸ I)`, so use a lower priority
instance (priority := 100) isScalarTower_right {α} [SMul α R] [IsScalarTower α R R] :
    IsScalarTower α (R ⧸ I) (R ⧸ I) :=
  (Quotient.ringCon I).isScalarTower_right

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass α R R]
  body: (Quotient.ringCon I).smulCommClass

中文:
实例 smulCommClass
  签名: {α} [标量乘法 α R] [标量塔 α R R] [标量交换类 α R R]
  定义体: (Quotient.ringCon I).smulCommClass

Depends on / 依赖: Quotient, Quotient.ringCon, ringCon, smulCommClass
-/
instance smulCommClass {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass α R R] :
    SMulCommClass α (R ⧸ I) (R ⧸ I) :=
  (Quotient.ringCon I).smulCommClass

/--
Instance `smulCommClass'` / 实例 `smulCommClass'`

English:
instance smulCommClass'
  signature: {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass R α R]
  body: (Quotient.ringCon I).smulCommClass'

中文:
实例 smulCommClass'
  签名: {α} [标量乘法 α R] [标量塔 α R R] [标量交换类 R α R]
  定义体: (Quotient.ringCon I).smulCommClass'

Depends on / 依赖: Quotient, Quotient.ringCon, ringCon, smulCommClass
-/
instance smulCommClass' {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass R α R] :
    SMulCommClass (R ⧸ I) α (R ⧸ I) :=
  (Quotient.ringCon I).smulCommClass'

/--
theorem `eq_zero_iff_dvd` / 定理 `eq_zero_iff_dvd`

English:
theorem eq_zero_iff_dvd
  given: {R} [CommRing R] (x y : R)
  proof: by
  rw [Ideal.Quotient.eq_zero_iff_mem]; rw [Ideal.mem_span_singleton]

@[simp]

中文:
定理 eq_zero_iff_dvd
  条件: {R} [交换环 R] (x y : R)
  证明: by
  rw [Ideal.Quotient.eq_zero_iff_mem]; rw [Ideal.mem_span_singleton]

@[simp]

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Quotient, eq_zero_iff_mem, mem_span_singleton
-/
theorem eq_zero_iff_dvd {R} [CommRing R] (x y : R) :
    Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y = 0 ↔ x ∣ y := by
  rw [Ideal.Quotient.eq_zero_iff_mem]; rw [Ideal.mem_span_singleton]

@[simp]
/--
lemma `mk_singleton_self` / 引理 `mk_singleton_self`

English:
lemma mk_singleton_self
  given: (x : R) [(Ideal.span {x}).IsTwoSided]
  statement: mk (Ideal.span {x}) x = 0
  proof: (Submodule.Quotient.mk_eq_zero _).mpr (mem_span_singleton_self _)

中文:
引理 mk_singleton_self
  条件: (x : R) [(理想.span {x}).是TwoSided]
  结论: mk (理想.span {x}) x = 0
  证明: (Submodule.Quotient.mk_eq_zero _).mpr (mem_span_singleton_self _)

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk_eq_zero, mem_span_singleton_self, mk_eq_zero
-/
lemma mk_singleton_self (x : R) [(Ideal.span {x}).IsTwoSided] : mk (Ideal.span {x}) x = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (mem_span_singleton_self _)

variable (I)

/--
Instance `noZeroDivisors` / 实例 `noZeroDivisors`

English:
instance noZeroDivisors
  signature: [hI : I.IsPrime]
  body: Quotient.inductionOn₂' a b fun {_ _} hab =>
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim (Or.inl ∘ eq_zero_iff_mem.2)
        (Or.inr ∘ eq_zero_iff_mem.2)

中文:
实例 noZeroDivisors
  签名: [hI : I.是素]
  定义体: Quotient.inductionOn₂' a b fun {_ _} hab =>
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim (Or.inl ∘ eq_zero_iff_mem.2)
        (Or.inr ∘ eq_zero_iff_mem.2)

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
instance noZeroDivisors [hI : I.IsPrime] : NoZeroDivisors (R ⧸ I) where
    eq_zero_or_eq_zero_of_mul_eq_zero {a b} := Quotient.inductionOn₂' a b fun {_ _} hab =>
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim (Or.inl ∘ eq_zero_iff_mem.2)
        (Or.inr ∘ eq_zero_iff_mem.2)

/--
Instance `isDomain` / 实例 `isDomain`

English:
instance isDomain
  signature: [hI : I.IsPrime]
  body: let _ := Quotient.nontrivial_iff.mpr hI.1
  NoZeroDivisors.to_isDomain _

中文:
实例 isDomain
  签名: [hI : I.是素]
  定义体: let _ := Quotient.nontrivial_iff.mpr hI.1
  NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, Quotient, Quotient.nontrivial_iff.mpr, nontrivial_iff, to_isDomain
-/
instance isDomain [hI : I.IsPrime] : IsDomain (R ⧸ I) :=
  let _ := Quotient.nontrivial_iff.mpr hI.1
  NoZeroDivisors.to_isDomain _

/--
theorem `isDomain_iff_prime` / 定理 `isDomain_iff_prime`

English:
theorem isDomain_iff_prime
  statement: IsDomain (R ⧸ I) ↔ I.IsPrime
  proof: by
  refine ⟨fun H => ⟨zero_ne_one_iff.1 ?_, fun {x y} h => ?_⟩, fun h => inferInstance⟩
  · have : Nontrivial (R ⧸ I) := ⟨H.2.1⟩
    exact zero_ne_one
  · simp only [← eq_zero_iff_mem, (mk I).map_mul] at h ⊢
    have := @IsDomain.to_noZeroDivisors (R ⧸ I) _ H
    exact eq_zero_or_eq_zero_of_mul_eq_

中文:
定理 isDomain_iff_prime
  结论: 是整环 (R ⧸ I) ↔ I.是素
  证明: by
  refine ⟨fun H => ⟨zero_ne_one_iff.1 ?_, fun {x y} h => ?_⟩, fun h => inferInstance⟩
  · have : Nontrivial (R ⧸ I) := ⟨H.2.1⟩
    exact zero_ne_one
  · simp only [← eq_zero_iff_mem, (mk I).map_mul] at h ⊢
    have := @IsDomain.to_noZeroDivisors (R ⧸ I) _ H
    exact eq_zero_or_eq_zero_of_mul_eq_

Depends on / 依赖: IsDomain, IsDomain.to_noZeroDivisors, Nontrivial, eq_zero_iff_mem, eq_zero_or_eq_zero_of_mul_eq_zero, map_mul, to_noZeroDivisors, zero_ne_one, zero_ne_one_iff
-/
theorem isDomain_iff_prime : IsDomain (R ⧸ I) ↔ I.IsPrime := by
  refine ⟨fun H => ⟨zero_ne_one_iff.1 ?_, fun {x y} h => ?_⟩, fun h => inferInstance⟩
  · have : Nontrivial (R ⧸ I) := ⟨H.2.1⟩
    exact zero_ne_one
  · simp only [← eq_zero_iff_mem, (mk I).map_mul] at h ⊢
    have := @IsDomain.to_noZeroDivisors (R ⧸ I) _ H
    exact eq_zero_or_eq_zero_of_mul_eq_zero h

set_option backward.isDefEq.respectTransparency false in
variable {I} in
/--
theorem `exists_inv` / 定理 `exists_inv`

English:
theorem exists_inv
  given: [hI : I.IsMaximal]
  proof: by
  apply exists_right_inv_of_exists_left_inv
  rintro ⟨a⟩ h
  rcases hI.exists_inv (mt eq_zero_iff_mem.2 h) with ⟨b, c, hc, abc⟩
  refine ⟨mk _ b, Quot.sound ?_⟩
  simp only [Submodule.quotientRel_def]
  rw [← eq_sub_iff_add_eq'] at abc
  rwa [abc, ← neg_mem_iff (G := R) (H := I), neg_sub] at hc

中文:
定理 存在_inv
  条件: [hI : I.是极大]
  证明: by
  apply exists_right_inv_of_exists_left_inv
  rintro ⟨a⟩ h
  rcases hI.exists_inv (mt eq_zero_iff_mem.2 h) with ⟨b, c, hc, abc⟩
  refine ⟨mk _ b, Quot.sound ?_⟩
  simp only [Submodule.quotientRel_def]
  rw [← eq_sub_iff_add_eq'] at abc
  rwa [abc, ← neg_mem_iff (G := R) (H := I), neg_sub] at hc

Depends on / 依赖: Quot.sound, Submodule, Submodule.quotientRel_def, eq_sub_iff_add_eq, eq_zero_iff_mem, exists_inv, exists_right_inv_of_exists_left_inv, hI.exists_inv, neg_mem_iff, neg_sub, quotientRel_def
-/
theorem exists_inv [hI : I.IsMaximal] :
    forall {a : R ⧸ I}, a != 0 -> exists b : R ⧸ I, a * b = 1 := by
  apply exists_right_inv_of_exists_left_inv
  rintro ⟨a⟩ h
  rcases hI.exists_inv (mt eq_zero_iff_mem.2 h) with ⟨b, c, hc, abc⟩
  refine ⟨mk _ b, Quot.sound ?_⟩
  simp only [Submodule.quotientRel_def]
  rw [← eq_sub_iff_add_eq'] at abc
  rwa [abc, ← neg_mem_iff (G := R) (H := I), neg_sub] at hc

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev groupWithZero [hI : I.IsMaximal]
  body: fast_instance%
  { inv := fun a => if ha : a = 0 then 0 else Classical.choose (exists_inv ha)
    mul_inv_cancel := fun a (ha : a != 0) =>
      show a * dite _ _ _ = _ by rw [dif_neg ha]; exact Classical.choose_spec (exists_inv ha)
    inv_zero := dif_pos rfl
    __ := Quotient.nontrivial_iff.mpr h

中文:
缩写 noncomputable
  签名: abbrev groupWithZero [hI : I.是极大]
  定义体: fast_instance%
  { inv := fun a => if ha : a = 0 then 0 else Classical.choose (exists_inv ha)
    mul_inv_cancel := fun a (ha : a != 0) =>
      show a * dite _ _ _ = _ by rw [dif_neg ha]; exact Classical.choose_spec (exists_inv ha)
    inv_zero := dif_pos rfl
    __ := Quotient.nontrivial_iff.mpr h
-/
protected noncomputable abbrev groupWithZero [hI : I.IsMaximal] :
    GroupWithZero (R ⧸ I) := fast_instance%
  { inv := fun a => if ha : a = 0 then 0 else Classical.choose (exists_inv ha)
    mul_inv_cancel := fun a (ha : a != 0) =>
      show a * dite _ _ _ = _ by rw [dif_neg ha]; exact Classical.choose_spec (exists_inv ha)
    inv_zero := dif_pos rfl
    __ := Quotient.nontrivial_iff.mpr hI.out.1 }

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev divisionRing [I.IsMaximal]
  body: fast_instance%
  { __ := ring _
    __ := Quotient.groupWithZero _
    nnqsmul := _
    nnqsmul_def _ _ := rfl
    qsmul := _
    qsmul_def _ _ := rfl }

中文:
缩写 noncomputable
  签名: abbrev divisionRing [I.是极大]
  定义体: fast_instance%
  { __ := ring _
    __ := Quotient.groupWithZero _
    nnqsmul := _
    nnqsmul_def _ _ := rfl
    qsmul := _
    qsmul_def _ _ := rfl }
-/
protected noncomputable abbrev divisionRing [I.IsMaximal] : DivisionRing (R ⧸ I) := fast_instance%
  { __ := ring _
    __ := Quotient.groupWithZero _
    nnqsmul := _
    nnqsmul_def _ _ := rfl
    qsmul := _
    qsmul_def _ _ := rfl }

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev field {R} [CommRing R] (I : Ideal R) [I.IsMaximal]
  body: fast_instance%
  { __ := commRing _
    __ := Quotient.divisionRing I }

中文:
缩写 noncomputable
  签名: abbrev field {R} [交换环 R] (I : 理想 R) [I.是极大]
  定义体: fast_instance%
  { __ := commRing _
    __ := Quotient.divisionRing I }
-/
protected noncomputable abbrev field {R} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Field (R ⧸ I) := fast_instance%
  { __ := commRing _
    __ := Quotient.divisionRing I }

/--
theorem `maximal_of_isField` / 定理 `maximal_of_isField`

English:
theorem maximal_of_isField
  given: {R} [CommRing R] (I : Ideal R) (hqf : IsField (R ⧸ I))
  proof: by
  apply Ideal.isMaximal_iff.2
  constructor
  · intro h
    rcases hqf.exists_pair_ne with ⟨⟨x⟩, ⟨y⟩, hxy⟩
    exact hxy (Ideal.Quotient.eq.2 (mul_one (x - y) ▸ I.mul_mem_left _ h))
  · intro J x hIJ hxnI hxJ
    rcases hqf.mul_inv_cancel (mt Ideal.Quotient.eq_zero_iff_mem.1 hxnI) with ⟨⟨y⟩, hy⟩


中文:
定理 maximal_of_isField
  条件: {R} [交换环 R] (I : 理想 R) (hqf : 是域 (R ⧸ I))
  证明: by
  apply Ideal.isMaximal_iff.2
  constructor
  · intro h
    rcases hqf.exists_pair_ne with ⟨⟨x⟩, ⟨y⟩, hxy⟩
    exact hxy (Ideal.Quotient.eq.2 (mul_one (x - y) ▸ I.mul_mem_left _ h))
  · intro J x hIJ hxnI hxJ
    rcases hqf.mul_inv_cancel (mt Ideal.Quotient.eq_zero_iff_mem.1 hxnI) with ⟨⟨y⟩, hy⟩


Depends on / 依赖: I.mul_mem_left, Ideal.Quotient.eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.isMaximal_iff, J.mul_mem_right, J.sub_mem, Quotient, eq_zero_iff_mem, exists_pair_ne, hqf.exists_pair_ne, hqf.mul_inv_cancel, isMaximal_iff, mul_inv_cancel, mul_mem_left, mul_mem_right, mul_one, sub_add, sub_mem, sub_self, zero_add
-/
theorem maximal_of_isField {R} [CommRing R] (I : Ideal R) (hqf : IsField (R ⧸ I)) :
    I.IsMaximal := by
  apply Ideal.isMaximal_iff.2
  constructor
  · intro h
    rcases hqf.exists_pair_ne with ⟨⟨x⟩, ⟨y⟩, hxy⟩
    exact hxy (Ideal.Quotient.eq.2 (mul_one (x - y) ▸ I.mul_mem_left _ h))
  · intro J x hIJ hxnI hxJ
    rcases hqf.mul_inv_cancel (mt Ideal.Quotient.eq_zero_iff_mem.1 hxnI) with ⟨⟨y⟩, hy⟩
    rw [← zero_add (1 : R)]; rw [← sub_self (x * y)]; rw [sub_add]
    exact J.sub_mem (J.mul_mem_right _ hxJ) (hIJ (Ideal.Quotient.eq.1 hy))

/--
theorem `maximal_ideal_iff_isField_quotient` / 定理 `maximal_ideal_iff_isField_quotient`

English:
theorem maximal_ideal_iff_isField_quotient
  given: {R} [CommRing R] (I : Ideal R)
  proof: ⟨fun h =>
    let _i := @Quotient.field _ _ I h
    Field.toIsField _,
    maximal_of_isField _⟩

中文:
定理 maximal_ideal_iff_isField_quotient
  条件: {R} [交换环 R] (I : 理想 R)
  证明: ⟨fun h =>
    let _i := @Quotient.field _ _ I h
    Field.toIsField _,
    maximal_of_isField _⟩

Depends on / 依赖: Field.toIsField, Quotient, Quotient.field, maximal_of_isField, toIsField
-/
theorem maximal_ideal_iff_isField_quotient {R} [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) :=
  ⟨fun h =>
    let _i := @Quotient.field _ _ I h
    Field.toIsField _,
    maximal_of_isField _⟩

end Quotient

section Pi

/--
Instance `modulePi` / 实例 `modulePi`

English:
instance modulePi
  signature: [I.IsTwoSided]
  body: Quotient.liftOn₂' c m (fun r m => Submodule.Quotient.mk <| r • m) by
      intro c₁ m₁ c₂ m₂ hc hm
      apply Ideal.Quotient.eq.2
      rw [Submodule.quotientRel_def] at hc hm
      intro i
      exact I.mul_sub_mul_mem hc (hm i)
  one_smul := by rintro ⟨a⟩; exact congr_arg _ (one_smul _ _)
  mul_s

中文:
实例 modulePi
  签名: [I.是TwoSided]
  定义体: Quotient.liftOn₂' c m (fun r m => Submodule.Quotient.mk <| r • m) by
      intro c₁ m₁ c₂ m₂ hc hm
      apply Ideal.Quotient.eq.2
      rw [Submodule.quotientRel_def] at hc hm
      intro i
      exact I.mul_sub_mul_mem hc (hm i)
  one_smul := by rintro ⟨a⟩; exact congr_arg _ (one_smul _ _)
  mul_s

Depends on / 依赖: I.mul_sub_mul_mem, Ideal.Quotient.eq, Quotient, Quotient.liftOn, Submodule, Submodule.Quotient.mk, Submodule.quotientRel_def, add_smul, congr_arg, mul_smul, mul_sub_mul_mem, one_smul, quotientRel_def, smul_add, smul_zero
-/
instance modulePi [I.IsTwoSided] : Module (R ⧸ I) ((ι -> R) ⧸ pi fun _ => I) where
  smul c m :=
Quotient.liftOn₂' c m (fun r m => Submodule.Quotient.mk <| r • m) by
      intro c₁ m₁ c₂ m₂ hc hm
      apply Ideal.Quotient.eq.2
      rw [Submodule.quotientRel_def] at hc hm
      intro i
      exact I.mul_sub_mul_mem hc (hm i)
  one_smul := by rintro ⟨a⟩; exact congr_arg _ (one_smul _ _)
  mul_smul := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact congr_arg _ (mul_smul _ _ _)
  smul_add := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact congr_arg _ (smul_add _ _ _)
  smul_zero := by rintro ⟨a⟩; exact congr_arg _ (smul_zero _)
  add_smul := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact congr_arg _ (add_smul _ _ _)
  zero_smul := by rintro ⟨a⟩; exact congr_arg _ (zero_smul _ _)

variable (ι) in
/--
Definition of `piQuotEquiv` / `piQuotEquiv` 的定义

English:
definition piQuotEquiv
  signature: [I.IsTwoSided]
  body: Quotient.liftOn' x (fun f i => Ideal.Quotient.mk I (f i)) fun _ _ hab =>
    funext fun i => (Submodule.Quotient.eq' _).2 (QuotientAddGroup.leftRel_apply.mp hab i)
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
  map_smul' := by rintro ⟨_⟩ ⟨_⟩; rfl
  invFun x := Ideal.Quotient.mk _ (Quotient.out <| x ·)
  lef

中文:
定义 piQuotEquiv
  签名: [I.是TwoSided]
  定义体: Quotient.liftOn' x (fun f i => Ideal.Quotient.mk I (f i)) fun _ _ hab =>
    funext fun i => (Submodule.Quotient.eq' _).2 (QuotientAddGroup.leftRel_apply.mp hab i)
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
  map_smul' := by rintro ⟨_⟩ ⟨_⟩; rfl
  invFun x := Ideal.Quotient.mk _ (Quotient.out <| x ·)
  lef

Depends on / 依赖: Ideal.Quotient.mk, Quotient, Quotient.liftOn, liftOn
-/
noncomputable def piQuotEquiv [I.IsTwoSided] : ((ι -> R) ⧸ pi fun _ => I) ≃ₗ[R ⧸ I] ι -> (R ⧸ I) where
  toFun x := Quotient.liftOn' x (fun f i => Ideal.Quotient.mk I (f i)) fun _ _ hab =>
    funext fun i => (Submodule.Quotient.eq' _).2 (QuotientAddGroup.leftRel_apply.mp hab i)
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
  map_smul' := by rintro ⟨_⟩ ⟨_⟩; rfl
  invFun x := Ideal.Quotient.mk _ (Quotient.out <| x ·)
  left_inv := by
    rintro ⟨x⟩
    exact Ideal.Quotient.eq.2 fun i => Ideal.Quotient.eq.1 (Quotient.out_eq' _)
  right_inv x := funext fun i => Quotient.out_eq' (x i)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_pi` / 定理 `map_pi`

English:
theorem map_pi
  statement: [I.IsTwoSided] [Finite ι] (x : ι -> R) (hi : forall i, x i in I)
  proof: by
  classical
    cases nonempty_fintype ι
    rw [pi_eq_sum_univ x]
    simp only [Finset.sum_apply, smul_eq_mul, map_sum, Pi.smul_apply, map_smul]
    exact I.sum_mem fun j _ => I.mul_mem_right _ (hi j)

中文:
定理 map_pi
  结论: [I.是TwoSided] [有限 ι] (x : ι -> R) (hi : 对任意 i, x i in I)
  证明: by
  classical
    cases nonempty_fintype ι
    rw [pi_eq_sum_univ x]
    simp only [Finset.sum_apply, smul_eq_mul, map_sum, Pi.smul_apply, map_smul]
    exact I.sum_mem fun j _ => I.mul_mem_right _ (hi j)

Depends on / 依赖: Finset, Finset.sum_apply, I.mul_mem_right, I.sum_mem, Pi.smul_apply, classical, map_smul, map_sum, mul_mem_right, nonempty_fintype, pi_eq_sum_univ, smul_apply, smul_eq_mul, sum_apply, sum_mem
-/
theorem map_pi [I.IsTwoSided] [Finite ι] (x : ι -> R) (hi : forall i, x i in I)
    (f : (ι -> R) ->ₗ[R] ι' -> R) (i : ι') : f x i in I := by
  classical
    cases nonempty_fintype ι
    rw [pi_eq_sum_univ x]
    simp only [Finset.sum_apply, smul_eq_mul, map_sum, Pi.smul_apply, map_smul]
    exact I.sum_mem fun j _ => I.mul_mem_right _ (hi j)

end Pi

open scoped Pointwise in
/--
lemma `univ_eq_iUnion_image_add` / 引理 `univ_eq_iUnion_image_add`

English:
lemma univ_eq_iUnion_image_add
  statement: (Set.univ (α := R)) = ⋃ x : R ⧸ I, x.out +ᵥ (I : Set R)
  proof: QuotientAddGroup.univ_eq_iUnion_vadd I.toAddSubgroup

中文:
引理 univ_eq_iUnion_image_add
  结论: (集合.univ (α := R)) = ⋃ x : R ⧸ I, x.out +ᵥ (I : 集合 R)
  证明: QuotientAddGroup.univ_eq_iUnion_vadd I.toAddSubgroup

Depends on / 依赖: x.out
-/
lemma univ_eq_iUnion_image_add : (Set.univ (α := R)) = ⋃ x : R ⧸ I, x.out +ᵥ (I : Set R) :=
  QuotientAddGroup.univ_eq_iUnion_vadd I.toAddSubgroup

end Ideal

/--
lemma `finite_iff_ideal_quotient` / 引理 `finite_iff_ideal_quotient`

English:
lemma finite_iff_ideal_quotient
  given: (I : Ideal R)
  statement: Finite R ↔ Finite I ∧ Finite (R ⧸ I)
  proof: finite_iff_addSubgroup_quotient I.toAddSubgroup

中文:
引理 finite_iff_ideal_quotient
  条件: (I : 理想 R)
  结论: 有限 R ↔ 有限 I ∧ 有限 (R ⧸ I)
  证明: finite_iff_addSubgroup_quotient I.toAddSubgroup

Depends on / 依赖: I.toAddSubgroup, finite_iff_addSubgroup_quotient, toAddSubgroup
-/
lemma finite_iff_ideal_quotient (I : Ideal R) : Finite R ↔ Finite I ∧ Finite (R ⧸ I) :=
  finite_iff_addSubgroup_quotient I.toAddSubgroup

/--
lemma `Finite.of_ideal_quotient` / 引理 `Finite.of_ideal_quotient`

English:
lemma Finite.of_ideal_quotient
  given: (I : Ideal R) [Finite I] [Finite (R ⧸ I)]
  statement: Finite R
  proof: by
  rw [finite_iff_ideal_quotient]; constructor <;> assumption

中文:
引理 有限.of_ideal_quotient
  条件: (I : 理想 R) [有限 I] [有限 (R ⧸ I)]
  结论: 有限 R
  证明: by
  rw [finite_iff_ideal_quotient]; constructor <;> assumption

Depends on / 依赖: finite_iff_ideal_quotient
-/
lemma Finite.of_ideal_quotient (I : Ideal R) [Finite I] [Finite (R ⧸ I)] : Finite R := by
  rw [finite_iff_ideal_quotient]; constructor <;> assumption
