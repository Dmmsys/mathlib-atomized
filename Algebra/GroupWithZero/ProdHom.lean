/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Homomorphisms for products of groups with zero

This file defines homomorphisms for products of groups with zero,
which is identified with the `WithZero` of the product of the units of the groups.

The product of groups with zero `WithZero (αˣ × βˣ)` is a
group with zero itself with natural inclusions.

TODO: Give `GrpWithZero` instances of `HasBinaryProducts` and `HasBinaryCoproducts`,
as well as a terminal object.

-/

@[expose] public section

namespace MonoidWithZeroHom

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
/--
lemma `one_apply_apply_eq` / 引理 `one_apply_apply_eq`

English:
lemma one_apply_apply_eq
  statement: {M₀ N₀ G₀ : Type*}
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero]
    rwa [map_ne_zero f]

中文:
引理 one_apply_apply_eq
  结论: {M₀ N₀ G₀ : 类型}
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero]
    rwa [map_ne_zero f]

Depends on / 依赖: eq_or_ne, map_ne_zero, one_apply_of_ne_zero
-/
lemma one_apply_apply_eq {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ => x = 0] [DecidablePred fun x : N₀ => x = 0]
    (f : M₀ ->*₀ N₀) (x : M₀) :
    (1 : N₀ ->*₀ G₀) (f x) = (1 : M₀ ->*₀ G₀) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero]
    rwa [map_ne_zero f]

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
/--
lemma `one_comp` / 引理 `one_comp`

English:
lemma one_comp
  statement: {M₀ N₀ G₀ : Type*}
  proof: ext one_apply_apply_eq _

中文:
引理 one_comp
  结论: {M₀ N₀ G₀ : 类型}
  证明: ext one_apply_apply_eq _

Depends on / 依赖: one_apply_apply_eq
-/
lemma one_comp {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ => x = 0] [DecidablePred fun x : N₀ => x = 0]
    (f : M₀ ->*₀ N₀) :
    (1 : N₀ ->*₀ G₀).comp f = (1 : M₀ ->*₀ G₀) :=
ext one_apply_apply_eq _

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: [DecidablePred fun x : G₀ => x = 0]
  body: (WithZero.map' (.inl _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

中文:
定义 inl
  签名: [DecidablePred fun x : G₀ => x = 0]
  定义体: (WithZero.map' (.inl _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

Depends on / 依赖: WithZero, WithZero.map, WithZero.withZeroUnitsEquiv.symm, ofClass, withZeroUnitsEquiv
-/
def inl [DecidablePred fun x : G₀ => x = 0] : G₀ ->*₀ WithZero (G₀ˣ × H₀ˣ) :=
  (WithZero.map' (.inl _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: [DecidablePred fun x : H₀ => x = 0]
  body: (WithZero.map' (.inr _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

中文:
定义 inr
  签名: [DecidablePred fun x : H₀ => x = 0]
  定义体: (WithZero.map' (.inr _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

Depends on / 依赖: WithZero, WithZero.map, WithZero.withZeroUnitsEquiv.symm, ofClass, withZeroUnitsEquiv
-/
def inr [DecidablePred fun x : H₀ => x = 0] : H₀ ->*₀ WithZero (G₀ˣ × H₀ˣ) :=
  (WithZero.map' (.inr _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : WithZero (G₀ˣ × H₀ˣ) ->*₀ G₀
  body: WithZero.lift' ((Units.coeHom _).comp (.fst ..))

中文:
定义 fst
  签名: : WithZero (G₀ˣ × H₀ˣ) ->*₀ G₀
  定义体: WithZero.lift' ((Units.coeHom _).comp (.fst ..))

Depends on / 依赖: Units.coeHom, WithZero, WithZero.lift, coeHom
-/
def fst : WithZero (G₀ˣ × H₀ˣ) ->*₀ G₀ :=
  WithZero.lift' ((Units.coeHom _).comp (.fst ..))

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : WithZero (G₀ˣ × H₀ˣ) ->*₀ H₀
  body: WithZero.lift' ((Units.coeHom _).comp (.snd ..))

中文:
定义 snd
  签名: : WithZero (G₀ˣ × H₀ˣ) ->*₀ H₀
  定义体: WithZero.lift' ((Units.coeHom _).comp (.snd ..))

Depends on / 依赖: Units.coeHom, WithZero, WithZero.lift, coeHom
-/
def snd : WithZero (G₀ˣ × H₀ˣ) ->*₀ H₀ :=
  WithZero.lift' ((Units.coeHom _).comp (.snd ..))

variable {G₀ H₀}

@[simp]
/--
lemma `inl_apply_unit` / 引理 `inl_apply_unit`

English:
lemma inl_apply_unit
  given: [DecidablePred fun x : G₀ => x = 0] (x : G₀ˣ)
  proof: by
  simp [inl]

@[simp]

中文:
引理 inl_apply_unit
  条件: [DecidablePred fun x : G₀ => x = 0] (x : G₀ˣ)
  证明: by
  simp [inl]

@[simp]
-/
lemma inl_apply_unit [DecidablePred fun x : G₀ => x = 0] (x : G₀ˣ) :
    inl G₀ H₀ x = ((x, (1 : H₀ˣ)) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [inl]

@[simp]
/--
lemma `inr_apply_unit` / 引理 `inr_apply_unit`

English:
lemma inr_apply_unit
  given: [DecidablePred fun x : H₀ => x = 0] (x : H₀ˣ)
  proof: by
  simp [inr]

中文:
引理 inr_apply_unit
  条件: [DecidablePred fun x : H₀ => x = 0] (x : H₀ˣ)
  证明: by
  simp [inr]

Depends on / 依赖: Quotient, Quotient.full_whiskeringLeft_functor, full_whiskeringLeft_functor
-/
lemma inr_apply_unit [DecidablePred fun x : H₀ => x = 0] (x : H₀ˣ) :
    inr G₀ H₀ x = (((1 : G₀ˣ), x) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [inr]

/--
lemma `fst_apply_coe` / 引理 `fst_apply_coe`

English:
lemma fst_apply_coe
  given: (x : G₀ˣ × H₀ˣ)
  statement: fst G₀ H₀ x = x.fst
  proof: by rfl

中文:
引理 fst_apply_coe
  条件: (x : G₀ˣ × H₀ˣ)
  结论: fst G₀ H₀ x = x.fst
  证明: by rfl

Depends on / 依赖: Quotient, Quotient.faithful_whiskeringLeft_functor, faithful_whiskeringLeft_functor
-/
@[simp] lemma fst_apply_coe (x : G₀ˣ × H₀ˣ) : fst G₀ H₀ x = x.fst := by rfl
/--
lemma `snd_apply_coe` / 引理 `snd_apply_coe`

English:
lemma snd_apply_coe
  given: (x : G₀ˣ × H₀ˣ)
  statement: snd G₀ H₀ x = x.snd
  proof: by rfl

中文:
引理 snd_apply_coe
  条件: (x : G₀ˣ × H₀ˣ)
  结论: snd G₀ H₀ x = x.snd
  证明: by rfl
-/
@[simp] lemma snd_apply_coe (x : G₀ˣ × H₀ˣ) : snd G₀ H₀ x = x.snd := by rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `fst_inl` / 定理 `fst_inl`

English:
theorem fst_inl
  given: [DecidablePred fun x : G₀ => x = 0] (x : G₀)
  proof: by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, fst, inl]

@[simp]

中文:
定理 fst_inl
  条件: [DecidablePred fun x : G₀ => x = 0] (x : G₀)
  证明: by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, fst, inl]

@[simp]

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, WithZero, WithZero.withZeroUnitsEquiv, eq_zero_or_unit, withZeroUnitsEquiv
-/
theorem fst_inl [DecidablePred fun x : G₀ => x = 0] (x : G₀) :
    fst _ H₀ (inl _ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, fst, inl]

@[simp]
/--
theorem `fst_comp_inl` / 定理 `fst_comp_inl`

English:
theorem fst_comp_inl
  given: [DecidablePred fun x : G₀ => x = 0]
  proof: ext fun _ => fst_inl _

中文:
定理 fst_comp_inl
  条件: [DecidablePred fun x : G₀ => x = 0]
  证明: ext fun _ => fst_inl _

Depends on / 依赖: fst_inl
-/
theorem fst_comp_inl [DecidablePred fun x : G₀ => x = 0] :
    (fst ..).comp (inl G₀ H₀) = .id _ :=
  ext fun _ => fst_inl _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `snd_comp_inl` / 定理 `snd_comp_inl`

English:
theorem snd_comp_inl
  given: [DecidablePred fun x : G₀ => x = 0]
  proof: by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, snd, inl]

中文:
定理 snd_comp_inl
  条件: [DecidablePred fun x : G₀ => x = 0]
  证明: by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, snd, inl]

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, WithZero, WithZero.withZeroUnitsEquiv, eq_zero_or_unit, withZeroUnitsEquiv
-/
theorem snd_comp_inl [DecidablePred fun x : G₀ => x = 0] :
    (snd ..).comp (inl G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, snd, inl]

/--
theorem `snd_inl_apply_of_ne_zero` / 定理 `snd_inl_apply_of_ne_zero`

English:
theorem snd_inl_apply_of_ne_zero
  given: [DecidablePred fun x : G₀ => x = 0] {x : G₀} (hx : x != 0)
  proof: by
  rw [← comp_apply]; rw [snd_comp_inl]; rw [one_apply_of_ne_zero hx]

中文:
定理 snd_inl_apply_of_ne_zero
  条件: [DecidablePred fun x : G₀ => x = 0] {x : G₀} (hx : x != 0)
  证明: by
  rw [← comp_apply]; rw [snd_comp_inl]; rw [one_apply_of_ne_zero hx]

Depends on / 依赖: comp_apply, one_apply_of_ne_zero, snd_comp_inl
-/
theorem snd_inl_apply_of_ne_zero [DecidablePred fun x : G₀ => x = 0] {x : G₀} (hx : x != 0) :
    snd _ _ (inl _ H₀ x) = 1 := by
  rw [← comp_apply]; rw [snd_comp_inl]; rw [one_apply_of_ne_zero hx]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `fst_comp_inr` / 定理 `fst_comp_inr`

English:
theorem fst_comp_inr
  given: [DecidablePred fun x : H₀ => x = 0]
  proof: by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, fst, inr]

中文:
定理 fst_comp_inr
  条件: [DecidablePred fun x : H₀ => x = 0]
  证明: by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, fst, inr]

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, WithZero, WithZero.withZeroUnitsEquiv, eq_zero_or_unit, withZeroUnitsEquiv
-/
theorem fst_comp_inr [DecidablePred fun x : H₀ => x = 0] :
    (fst ..).comp (inr G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, fst, inr]

/--
theorem `fst_inr_apply_of_ne_zero` / 定理 `fst_inr_apply_of_ne_zero`

English:
theorem fst_inr_apply_of_ne_zero
  given: [DecidablePred fun x : H₀ => x = 0] {x : H₀} (hx : x != 0)
  proof: by
  rw [← comp_apply]; rw [fst_comp_inr]; rw [one_apply_of_ne_zero hx]

中文:
定理 fst_inr_apply_of_ne_zero
  条件: [DecidablePred fun x : H₀ => x = 0] {x : H₀} (hx : x != 0)
  证明: by
  rw [← comp_apply]; rw [fst_comp_inr]; rw [one_apply_of_ne_zero hx]

Depends on / 依赖: comp_apply, fst_comp_inr, one_apply_of_ne_zero
-/
theorem fst_inr_apply_of_ne_zero [DecidablePred fun x : H₀ => x = 0] {x : H₀} (hx : x != 0) :
    fst _ _ (inr G₀ _ x) = 1 := by
  rw [← comp_apply]; rw [fst_comp_inr]; rw [one_apply_of_ne_zero hx]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `snd_inr` / 定理 `snd_inr`

English:
theorem snd_inr
  given: [DecidablePred fun x : H₀ => x = 0] (x : H₀)
  proof: by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, snd, inr]

@[simp]

中文:
定理 snd_inr
  条件: [DecidablePred fun x : H₀ => x = 0] (x : H₀)
  证明: by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, snd, inr]

@[simp]

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, WithZero, WithZero.withZeroUnitsEquiv, eq_zero_or_unit, withZeroUnitsEquiv
-/
theorem snd_inr [DecidablePred fun x : H₀ => x = 0] (x : H₀) :
    snd _ _ (inr G₀ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, snd, inr]

@[simp]
/--
theorem `snd_comp_inr` / 定理 `snd_comp_inr`

English:
theorem snd_comp_inr
  given: [DecidablePred fun x : H₀ => x = 0]
  proof: ext fun _ => snd_inr _

中文:
定理 snd_comp_inr
  条件: [DecidablePred fun x : H₀ => x = 0]
  证明: ext fun _ => snd_inr _

Depends on / 依赖: snd_inr
-/
theorem snd_comp_inr [DecidablePred fun x : H₀ => x = 0] :
    (snd ..).comp (inr G₀ H₀) = .id _ :=
  ext fun _ => snd_inr _

/--
lemma `inl_injective` / 引理 `inl_injective`

English:
lemma inl_injective
  given: [DecidablePred fun x : G₀ => x = 0]
  proof: Function.HasLeftInverse.injective ⟨fst .., fun _ => by simp⟩

中文:
引理 inl_injective
  条件: [DecidablePred fun x : G₀ => x = 0]
  证明: Function.HasLeftInverse.injective ⟨fst .., fun _ => by simp⟩

Depends on / 依赖: Function, Function.HasLeftInverse.injective, HasLeftInverse, injective
-/
lemma inl_injective [DecidablePred fun x : G₀ => x = 0] :
    Function.Injective (inl G₀ H₀) :=
  Function.HasLeftInverse.injective ⟨fst .., fun _ => by simp⟩

/--
lemma `inr_injective` / 引理 `inr_injective`

English:
lemma inr_injective
  given: [DecidablePred fun x : H₀ => x = 0]
  proof: Function.HasLeftInverse.injective ⟨snd .., fun _ => by simp⟩

中文:
引理 inr_injective
  条件: [DecidablePred fun x : H₀ => x = 0]
  证明: Function.HasLeftInverse.injective ⟨snd .., fun _ => by simp⟩

Depends on / 依赖: Function, Function.HasLeftInverse.injective, HasLeftInverse, injective
-/
lemma inr_injective [DecidablePred fun x : H₀ => x = 0] :
    Function.Injective (inr G₀ H₀) :=
  Function.HasLeftInverse.injective ⟨snd .., fun _ => by simp⟩

/--
lemma `fst_surjective` / 引理 `fst_surjective`

English:
lemma fst_surjective
  statement: Function.Surjective (fst G₀ H₀)
  proof: by
  classical
  exact Function.HasRightInverse.surjective ⟨inl .., fun _ => by simp⟩

中文:
引理 fst_surjective
  结论: 函数.满射 (fst G₀ H₀)
  证明: by
  classical
  exact Function.HasRightInverse.surjective ⟨inl .., fun _ => by simp⟩

Depends on / 依赖: Function, Function.HasRightInverse.surjective, HasRightInverse, classical, surjective
-/
lemma fst_surjective : Function.Surjective (fst G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨inl .., fun _ => by simp⟩

/--
lemma `snd_surjective` / 引理 `snd_surjective`

English:
lemma snd_surjective
  statement: Function.Surjective (snd G₀ H₀)
  proof: by
  classical
  exact Function.HasRightInverse.surjective ⟨inr .., fun _ => by simp⟩

中文:
引理 snd_surjective
  结论: 函数.满射 (snd G₀ H₀)
  证明: by
  classical
  exact Function.HasRightInverse.surjective ⟨inr .., fun _ => by simp⟩

Depends on / 依赖: Function, Function.HasRightInverse.surjective, HasRightInverse, classical, surjective
-/
lemma snd_surjective : Function.Surjective (snd G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨inr .., fun _ => by simp⟩

variable [DecidablePred fun x : G₀ => x = 0] [DecidablePred fun x : H₀ => x = 0]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `inl_mul_inr_eq_mk_of_unit` / 定理 `inl_mul_inr_eq_mk_of_unit`

English:
theorem inl_mul_inr_eq_mk_of_unit
  given: (m : G₀ˣ) (n : H₀ˣ)
  proof: by
  simp [inl, WithZero.withZeroUnitsEquiv, inr, ← WithZero.coe_mul]

中文:
定理 inl_mul_inr_eq_mk_of_unit
  条件: (m : G₀ˣ) (n : H₀ˣ)
  证明: by
  simp [inl, WithZero.withZeroUnitsEquiv, inr, ← WithZero.coe_mul]

Depends on / 依赖: WithZero, WithZero.coe_mul, WithZero.withZeroUnitsEquiv, coe_mul, withZeroUnitsEquiv
-/
theorem inl_mul_inr_eq_mk_of_unit (m : G₀ˣ) (n : H₀ˣ) :
    (inl G₀ H₀ m * inr G₀ H₀ n) = (m, n) := by
  simp [inl, WithZero.withZeroUnitsEquiv, inr, ← WithZero.coe_mul]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `commute_inl_inr` / 定理 `commute_inl_inr`

English:
theorem commute_inl_inr
  given: (m : G₀) (n : H₀)
  statement: Commute (inl G₀ H₀ m) (inr G₀ H₀ n)
  proof: by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit m <;>
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit n <;>
  simp [inl, inr, WithZero.withZeroUnitsEquiv, commute_iff_eq, ← WithZero.coe_mul]

中文:
定理 commute_inl_inr
  条件: (m : G₀) (n : H₀)
  结论: Commute (inl G₀ H₀ m) (inr G₀ H₀ n)
  证明: by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit m <;>
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit n <;>
  simp [inl, inr, WithZero.withZeroUnitsEquiv, commute_iff_eq, ← WithZero.coe_mul]

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, WithZero, WithZero.coe_mul, WithZero.withZeroUnitsEquiv, coe_mul, commute_iff_eq, eq_zero_or_unit, withZeroUnitsEquiv
-/
theorem commute_inl_inr (m : G₀) (n : H₀) : Commute (inl G₀ H₀ m) (inr G₀ H₀ n) := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit m <;>
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit n <;>
  simp [inl, inr, WithZero.withZeroUnitsEquiv, commute_iff_eq, ← WithZero.coe_mul]

end MonoidWithZeroHom
