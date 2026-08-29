/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Data.ENat.Lattice

/-!
# Injective dimension

In an abelian category `C`, we shall say that `X : C` has Injective dimension `< n`
if all `Ext Y X i` vanish when `n ≤ i`. This defines a type class
`HasInjectiveDimensionLT X n`. We also define a type class
`HasInjectiveDimensionLE X n` as an abbreviation for
`HasInjectiveDimensionLT X (n + 1)`.
(Note that the fact that `X` is a zero object is equivalent to the condition
`HasInjectiveDimensionLT X 0`, but this cannot be expressed in terms of
`HasInjectiveDimensionLE`.)

We also define the Injective dimension in `WithBot ℕ∞` as `injectiveDimension`,
`injectiveDimension X = ⊥` iff `X` is zero and behaves as expected on non-negative values.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Abelian Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/--
Definition of `HasInjectiveDimensionLT` / `HasInjectiveDimensionLT` 的定义

English:
class HasInjectiveDimensionLT
  parameters: (X : C) (n : Nat)
  (no additional axioms)

中文:
类 HasInjectiveDimensionLT
  参数: (X : C) (n : 自然数)
  (无附加公理)

Depends on / 依赖: HasExt, HasExt.standard, standard
-/
class HasInjectiveDimensionLT (X : C) (n : Nat) : Prop where mk' ::
  subsingleton' (i : Nat) (hi : n <= i) ⦃Y : C⦄ :
    letI := HasExt.standard C
    Subsingleton (Ext.{max u v} Y X i)

/--
Definition of `HasInjectiveDimensionLE` / `HasInjectiveDimensionLE` 的定义

English:
abbreviation HasInjectiveDimensionLE
  signature: (X : C) (n : Nat)
  body: HasInjectiveDimensionLT X (n + 1)

中文:
缩写 HasInjectiveDimensionLE
  签名: (X : C) (n : 自然数)
  定义体: HasInjectiveDimensionLT X (n + 1)

Depends on / 依赖: HasInjectiveDimensionLT
-/
abbrev HasInjectiveDimensionLE (X : C) (n : Nat) : Prop :=
  HasInjectiveDimensionLT X (n + 1)

namespace HasInjectiveDimensionLT

variable [HasExt.{w} C] (X : C) (n : Nat)

/--
lemma `subsingleton` / 引理 `subsingleton`

English:
lemma subsingleton
  given: [hX : HasInjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C)
  proof: by
  let := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

中文:
引理 subsingleton
  条件: [hX : HasInjectiveDimensionLT X n] (i : 自然数) (hi : n <= i) (Y : C)
  证明: by
  let := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

Depends on / 依赖: Ext.chgUniv, HasExt, HasExt.standard, chgUniv, hX.subsingleton, standard, subsingleton, symm.subsingleton
-/
lemma subsingleton [hX : HasInjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C) :
    Subsingleton (Ext.{w} Y X i) := by
  let := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

variable {X n} in
/--
lemma `mk` / 引理 `mk`

English:
lemma mk
  given: (hX : forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext Y X i), e = 0)
  proof: by
    have : Subsingleton (Ext Y X i) := ⟨fun e₁ e₂ => by simp only [hX i hi]⟩
    let := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

中文:
引理 mk
  条件: (hX : 对任意 (i : 自然数) (_ : n <= i) ⦃Y : C⦄, 对任意 (e : Ext Y X i), e = 0)
  证明: by
    have : Subsingleton (Ext Y X i) := ⟨fun e₁ e₂ => by simp only [hX i hi]⟩
    let := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

Depends on / 依赖: Ext.chgUniv, HasExt, HasExt.standard, Subsingleton, chgUniv, standard, subsingleton, symm.subsingleton
-/
lemma mk (hX : forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext Y X i), e = 0) :
    HasInjectiveDimensionLT X n where
  subsingleton' i hi Y := by
    have : Subsingleton (Ext Y X i) := ⟨fun e₁ e₂ => by simp only [hX i hi]⟩
    let := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

end HasInjectiveDimensionLT

/--
lemma `Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT` / 引理 `Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT`

English:
lemma Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT
  statement: [HasExt.{w} C]
  proof: (HasInjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

中文:
引理 Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT
  结论: [HasExt.{w} C]
  证明: (HasInjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

Depends on / 依赖: HasInjectiveDimensionLT, HasInjectiveDimensionLT.subsingleton, subsingleton
-/
lemma Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT [HasExt.{w} C]
    {X Y : C} {i : Nat} (e : Ext Y X i) (n : Nat) [HasInjectiveDimensionLT X n]
    (hi : n <= i) : e = 0 :=
  (HasInjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

section

variable (X : C) (n : Nat)

/--
lemma `hasInjectiveDimensionLT_iff` / 引理 `hasInjectiveDimensionLT_iff`

English:
lemma hasInjectiveDimensionLT_iff
  given: [HasExt.{w} C]
  proof: ⟨fun _ _ hi _ e => e.eq_zero_of_hasInjectiveDimensionLT n hi,
    HasInjectiveDimensionLT.mk⟩

中文:
引理 hasInjectiveDimensionLT_iff
  条件: [HasExt.{w} C]
  证明: ⟨fun _ _ hi _ e => e.eq_zero_of_hasInjectiveDimensionLT n hi,
    HasInjectiveDimensionLT.mk⟩

Depends on / 依赖: HasInjectiveDimensionLT, HasInjectiveDimensionLT.mk, e.eq_zero_of_hasInjectiveDimensionLT, eq_zero_of_hasInjectiveDimensionLT
-/
lemma hasInjectiveDimensionLT_iff [HasExt.{w} C] :
    HasInjectiveDimensionLT X n ↔
      forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext Y X i), e = 0 :=
  ⟨fun _ _ hi _ e => e.eq_zero_of_hasInjectiveDimensionLT n hi,
    HasInjectiveDimensionLT.mk⟩

variable {X} in
/--
lemma `Limits.IsZero.hasInjectiveDimensionLT_zero` / 引理 `Limits.IsZero.hasInjectiveDimensionLT_zero`

English:
lemma Limits.IsZero.hasInjectiveDimensionLT_zero
  given: (hX : IsZero X)
  proof: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.comp_mk₀_id]; rw [hX.eq_zero_of_tgt (𝟙 X)]; rw [Ext.mk₀_zero]; rw [Ext.comp_zero]

中文:
引理 Limits.IsZero.hasInjectiveDimensionLT_zero
  条件: (hX : IsZero X)
  证明: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.comp_mk₀_id]; rw [hX.eq_zero_of_tgt (𝟙 X)]; rw [Ext.mk₀_zero]; rw [Ext.comp_zero]

Depends on / 依赖: Ext.comp_zero, Ext.mk, F.Faithful, Faithful, HasExt, HasExt.standard, IsThin, Quiver, Quiver.IsThin, comp_zero, e.comp_mk, eq_zero_of_tgt, hX.eq_zero_of_tgt, hasInjectiveDimensionLT_iff, standard
-/
lemma Limits.IsZero.hasInjectiveDimensionLT_zero (hX : IsZero X) :
    HasInjectiveDimensionLT X 0 := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.comp_mk₀_id]; rw [hX.eq_zero_of_tgt (𝟙 X)]; rw [Ext.mk₀_zero]; rw [Ext.comp_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasInjectiveDimensionLT (0 : C) 0
  body: (isZero_zero C).hasInjectiveDimensionLT_zero

中文:
实例 :
  签名: HasInjectiveDimensionLT (0 : C) 0
  定义体: (isZero_zero C).hasInjectiveDimensionLT_zero

Depends on / 依赖: hasInjectiveDimensionLT_zero, isZero_zero
-/
instance : HasInjectiveDimensionLT (0 : C) 0 :=
  (isZero_zero C).hasInjectiveDimensionLT_zero

/--
lemma `isZero_of_hasInjectiveDimensionLT_zero` / 引理 `isZero_of_hasInjectiveDimensionLT_zero`

English:
lemma isZero_of_hasInjectiveDimensionLT_zero
  given: [HasInjectiveDimensionLT X 0]
  statement: IsZero X
  proof: by
  let := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT _ 0 (by rfl)

中文:
引理 isZero_of_hasInjectiveDimensionLT_zero
  条件: [HasInjectiveDimensionLT X 0]
  结论: IsZero X
  证明: by
  let := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT _ 0 (by rfl)

Depends on / 依赖: Abelian, Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT, Ext.homEquiv, Ext.mk, HasExt, HasExt.standard, IsZero, IsZero.iff_id_eq_zero, eq_zero_of_hasInjectiveDimensionLT, iff_id_eq_zero, injective, standard, symm.injective
-/
lemma isZero_of_hasInjectiveDimensionLT_zero [HasInjectiveDimensionLT X 0] : IsZero X := by
  let := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT _ 0 (by rfl)

/--
lemma `hasInjectiveDimensionLT_zero_iff_isZero` / 引理 `hasInjectiveDimensionLT_zero_iff_isZero`

English:
lemma hasInjectiveDimensionLT_zero_iff_isZero
  statement: HasInjectiveDimensionLT X 0 ↔ IsZero X
  proof: ⟨fun _ => isZero_of_hasInjectiveDimensionLT_zero X, fun h => h.hasInjectiveDimensionLT_zero⟩

中文:
引理 hasInjectiveDimensionLT_zero_iff_isZero
  结论: HasInjectiveDimensionLT X 0 ↔ IsZero X
  证明: ⟨fun _ => isZero_of_hasInjectiveDimensionLT_zero X, fun h => h.hasInjectiveDimensionLT_zero⟩

Depends on / 依赖: h.hasInjectiveDimensionLT_zero, hasInjectiveDimensionLT_zero, isZero_of_hasInjectiveDimensionLT_zero
-/
lemma hasInjectiveDimensionLT_zero_iff_isZero : HasInjectiveDimensionLT X 0 ↔ IsZero X :=
  ⟨fun _ => isZero_of_hasInjectiveDimensionLT_zero X, fun h => h.hasInjectiveDimensionLT_zero⟩

/--
lemma `hasInjectiveDimensionLT_of_ge` / 引理 `hasInjectiveDimensionLT_of_ge`

English:
lemma hasInjectiveDimensionLT_of_ge
  statement: (m : Nat) (h : n <= m)
  proof: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasInjectiveDimensionLT n (by lia)

中文:
引理 hasInjectiveDimensionLT_of_ge
  结论: (m : 自然数) (h : n <= m)
  证明: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasInjectiveDimensionLT n (by lia)

Depends on / 依赖: HasExt, HasExt.standard, e.eq_zero_of_hasInjectiveDimensionLT, eq_zero_of_hasInjectiveDimensionLT, hasInjectiveDimensionLT_iff, standard
-/
lemma hasInjectiveDimensionLT_of_ge (m : Nat) (h : n <= m)
    [HasInjectiveDimensionLT X n] :
    HasInjectiveDimensionLT X m := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasInjectiveDimensionLT n (by lia)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasInjectiveDimensionLT
  signature: X n] (k
  body: hasInjectiveDimensionLT_of_ge X n (n + k) (by lia)

中文:
实例 [HasInjectiveDimensionLT
  签名: X n] (k
  定义体: hasInjectiveDimensionLT_of_ge X n (n + k) (by lia)

Depends on / 依赖: hasInjectiveDimensionLT_of_ge
-/
instance [HasInjectiveDimensionLT X n] (k : Nat) :
    HasInjectiveDimensionLT X (n + k) :=
  hasInjectiveDimensionLT_of_ge X n (n + k) (by lia)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasInjectiveDimensionLT
  signature: X n] (k
  body: hasInjectiveDimensionLT_of_ge X n (k + n) (by lia)

中文:
实例 [HasInjectiveDimensionLT
  签名: X n] (k
  定义体: hasInjectiveDimensionLT_of_ge X n (k + n) (by lia)

Depends on / 依赖: hasInjectiveDimensionLT_of_ge
-/
instance [HasInjectiveDimensionLT X n] (k : Nat) :
    HasInjectiveDimensionLT X (k + n) :=
  hasInjectiveDimensionLT_of_ge X n (k + n) (by lia)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasInjectiveDimensionLT
  signature: X n] :
  body: inferInstanceAs (HasInjectiveDimensionLT X (n + 1))

中文:
实例 [HasInjectiveDimensionLT
  签名: X n] :
  定义体: inferInstanceAs (HasInjectiveDimensionLT X (n + 1))

Depends on / 依赖: HasInjectiveDimensionLT
-/
instance [HasInjectiveDimensionLT X n] :
    HasInjectiveDimensionLT X n.succ :=
  inferInstanceAs (HasInjectiveDimensionLT X (n + 1))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Injective
  signature: X] : HasInjectiveDimensionLT X 1
  body: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_injective

中文:
实例 [Injective
  签名: X] : HasInjectiveDimensionLT X 1
  定义体: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_injective

Depends on / 依赖: HasExt, HasExt.standard, e.eq_zero_of_injective, eq_zero_of_injective, hasInjectiveDimensionLT_iff, standard
-/
instance [Injective X] : HasInjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_injective

variable {X} in
/--
lemma `injective_iff_subsingleton_ext_one` / 引理 `injective_iff_subsingleton_ext_one`

English:
lemma injective_iff_subsingleton_ext_one
  given: [HasExt.{w} C]
  proof: by
  refine ⟨fun h => HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h => ⟨fun f g _ => ?_⟩⟩
  obtain ⟨φ, hφ⟩ := Ext.contravariant_sequence_exact₁ { exact := ShortComplex.exact_cokernel g } _
    (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surject

中文:
引理 injective_iff_subsingleton_ext_one
  条件: [HasExt.{w} C]
  证明: by
  refine ⟨fun h => HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h => ⟨fun f g _ => ?_⟩⟩
  obtain ⟨φ, hφ⟩ := Ext.contravariant_sequence_exact₁ { exact := ShortComplex.exact_cokernel g } _
    (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surject

Depends on / 依赖: Ext.contravariant_sequence_exact, Ext.homEquiv, Ext.mk, HasInjectiveDimensionLT, HasInjectiveDimensionLT.subsingleton, ShortComplex, ShortComplex.exact_cokernel, exact_cokernel, injective, subsingleton, surjective, symm.injective, symm.surjective, zero_add
-/
lemma injective_iff_subsingleton_ext_one [HasExt.{w} C] :
    Injective X ↔ forall ⦃Y : C⦄, Subsingleton (Ext Y X 1) := by
  refine ⟨fun h => HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h => ⟨fun f g _ => ?_⟩⟩
  obtain ⟨φ, hφ⟩ := Ext.contravariant_sequence_exact₁ { exact := ShortComplex.exact_cokernel g } _
    (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective φ
  exact ⟨φ, Ext.homEquiv₀.symm.injective (by simpa using hφ)⟩

variable {X} in
/--
lemma `injective_iff_hasInjectiveDimensionLT_one` / 引理 `injective_iff_hasInjectiveDimensionLT_one`

English:
lemma injective_iff_hasInjectiveDimensionLT_one
  proof: by
  let := HasExt.standard C
  exact ⟨fun _ => inferInstance, fun _ => injective_iff_subsingleton_ext_one.2
    (HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩

中文:
引理 injective_iff_hasInjectiveDimensionLT_one
  证明: by
  let := HasExt.standard C
  exact ⟨fun _ => inferInstance, fun _ => injective_iff_subsingleton_ext_one.2
    (HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩

Depends on / 依赖: HasExt, HasExt.standard, HasInjectiveDimensionLT, HasInjectiveDimensionLT.subsingleton, injective_iff_subsingleton_ext_one, standard, subsingleton
-/
lemma injective_iff_hasInjectiveDimensionLT_one :
    Injective X ↔ HasInjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  exact ⟨fun _ => inferInstance, fun _ => injective_iff_subsingleton_ext_one.2
    (HasInjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩

instance (priority := low) [HasInjectiveDimensionLT X 1] : Injective X :=
  injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›

end

/--
lemma `Retract.hasInjectiveDimensionLT` / 引理 `Retract.hasInjectiveDimensionLT`

English:
lemma Retract.hasInjectiveDimensionLT
  statement: {X Y : C} (h : Retract X Y) (n : Nat)
  proof: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.comp_mk₀_id]; rw [← h.retract]; rw [← Ext.mk₀_comp_mk₀]; rw [← Ext.comp_assoc_of_second_deg_zero]; rw [(x.comp (Ext.mk₀ h.i) (add_zero i)).eq_zero_of_hasInjectiveDimensionLT n hi]; rw [Ext.zero_comp]

中文:
引理 Retract.hasInjectiveDimensionLT
  结论: {X Y : C} (h : Retract X Y) (n : 自然数)
  证明: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.comp_mk₀_id]; rw [← h.retract]; rw [← Ext.mk₀_comp_mk₀]; rw [← Ext.comp_assoc_of_second_deg_zero]; rw [(x.comp (Ext.mk₀ h.i) (add_zero i)).eq_zero_of_hasInjectiveDimensionLT n hi]; rw [Ext.zero_comp]

Depends on / 依赖: Ext.comp_assoc_of_second_deg_zero, Ext.mk, Ext.zero_comp, HasExt, HasExt.standard, add_zero, comp_assoc_of_second_deg_zero, eq_zero_of_hasInjectiveDimensionLT, h.retract, hasInjectiveDimensionLT_iff, retract, standard, x.comp, x.comp_mk, zero_comp
-/
lemma Retract.hasInjectiveDimensionLT {X Y : C} (h : Retract X Y) (n : Nat)
    [HasInjectiveDimensionLT Y n] :
    HasInjectiveDimensionLT X n := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.comp_mk₀_id]; rw [← h.retract]; rw [← Ext.mk₀_comp_mk₀]; rw [← Ext.comp_assoc_of_second_deg_zero]; rw [(x.comp (Ext.mk₀ h.i) (add_zero i)).eq_zero_of_hasInjectiveDimensionLT n hi]; rw [Ext.zero_comp]

/--
lemma `hasInjectiveDimensionLT_of_iso` / 引理 `hasInjectiveDimensionLT_of_iso`

English:
lemma hasInjectiveDimensionLT_of_iso
  statement: {X X' : C} (e : X ≅ X') (n : Nat)
  proof: e.symm.retract.hasInjectiveDimensionLT n

中文:
引理 hasInjectiveDimensionLT_of_iso
  结论: {X X' : C} (e : X ≅ X') (n : 自然数)
  证明: e.symm.retract.hasInjectiveDimensionLT n

Depends on / 依赖: e.symm.retract.hasInjectiveDimensionLT, hasInjectiveDimensionLT, retract
-/
lemma hasInjectiveDimensionLT_of_iso {X X' : C} (e : X ≅ X') (n : Nat)
    [HasInjectiveDimensionLT X n] :
    HasInjectiveDimensionLT X' n :=
  e.symm.retract.hasInjectiveDimensionLT n

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (n : Nat)
include hS

-- In the following lemmas, the parameters `HasInjectiveDimensionLT` are
-- explicit as it is unlikely we may infer them, unless the short complex `S`
-- was declared reducible

/--
lemma `hasInjectiveDimensionLT_X₂` / 引理 `hasInjectiveDimensionLT_X₂`

English:
lemma hasInjectiveDimensionLT_X₂
  statement: (h₁ : HasInjectiveDimensionLT S.X₁ n)
  proof: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₂ _ hS x₂
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasInjectiveDimensionLT n hi]; rw [Ext.zero_comp]

中文:
引理 hasInjectiveDimensionLT_X₂
  结论: (h₁ : HasInjectiveDimensionLT S.X₁ n)
  证明: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₂ _ hS x₂
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasInjectiveDimensionLT n hi]; rw [Ext.zero_comp]

Depends on / 依赖: Ext.covariant_sequence_exact, Ext.eq_zero_of_hasInjectiveDimensionLT, Ext.zero_comp, HasExt, HasExt.standard, eq_zero_of_hasInjectiveDimensionLT, hasInjectiveDimensionLT_iff, standard, zero_comp
-/
lemma hasInjectiveDimensionLT_X₂ (h₁ : HasInjectiveDimensionLT S.X₁ n)
    (h₃ : HasInjectiveDimensionLT S.X₃ n) :
    HasInjectiveDimensionLT S.X₂ n := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₂ _ hS x₂
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasInjectiveDimensionLT n hi]; rw [Ext.zero_comp]

/--
lemma `hasInjectiveDimensionLT_X₁` / 引理 `hasInjectiveDimensionLT_X₁`

English:
lemma hasInjectiveDimensionLT_X₁
  statement: (h₁ : HasInjectiveDimensionLT S.X₃ n)
  proof: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x₃
      (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) hi) rfl
    rw [x₁.eq_zero_of_hasInjectiveDimensionLT n (by lia)]; rw [Ext.ze

中文:
引理 hasInjectiveDimensionLT_X₁
  结论: (h₁ : HasInjectiveDimensionLT S.X₃ n)
  证明: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x₃
      (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) hi) rfl
    rw [x₁.eq_zero_of_hasInjectiveDimensionLT n (by lia)]; rw [Ext.ze

Depends on / 依赖: Ext.covariant_sequence_exact, Ext.eq_zero_of_hasInjectiveDimensionLT, Ext.zero_comp, HasExt, HasExt.standard, eq_zero_of_hasInjectiveDimensionLT, hasInjectiveDimensionLT_iff, standard, zero_comp
-/
lemma hasInjectiveDimensionLT_X₁ (h₁ : HasInjectiveDimensionLT S.X₃ n)
    (h₂ : HasInjectiveDimensionLT S.X₂ (n + 1)) :
    HasInjectiveDimensionLT S.X₁ (n + 1) := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x₃
      (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) hi) rfl
    rw [x₁.eq_zero_of_hasInjectiveDimensionLT n (by lia)]; rw [Ext.zero_comp]

/--
lemma `hasInjectiveDimensionLT_X₃` / 引理 `hasInjectiveDimensionLT_X₃`

English:
lemma hasInjectiveDimensionLT_X₃
  statement: (h₂ : HasInjectiveDimensionLT S.X₂ n)
  proof: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) (by lia))
  rw [x₂.eq_zero_of_hasInjectiveDimensionLT n (by lia)]; rw [Ext.zero_comp]

中文:
引理 hasInjectiveDimensionLT_X₃
  结论: (h₂ : HasInjectiveDimensionLT S.X₂ n)
  证明: by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) (by lia))
  rw [x₂.eq_zero_of_hasInjectiveDimensionLT n (by lia)]; rw [Ext.zero_comp]

Depends on / 依赖: Ext.covariant_sequence_exact, Ext.eq_zero_of_hasInjectiveDimensionLT, Ext.zero_comp, HasExt, HasExt.standard, add_comm, eq_zero_of_hasInjectiveDimensionLT, hasInjectiveDimensionLT_iff, standard, zero_comp
-/
lemma hasInjectiveDimensionLT_X₃ (h₂ : HasInjectiveDimensionLT S.X₂ n)
    (h₃ : HasInjectiveDimensionLT S.X₁ (n + 1)) :
    HasInjectiveDimensionLT S.X₃ n := by
  let := HasExt.standard C
  rw [hasInjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasInjectiveDimensionLT _ (n + 1) (by lia))
  rw [x₂.eq_zero_of_hasInjectiveDimensionLT n (by lia)]; rw [Ext.zero_comp]

/--
lemma `hasInjectiveDimensionLT_X₃_iff` / 引理 `hasInjectiveDimensionLT_X₃_iff`

English:
lemma hasInjectiveDimensionLT_X₃_iff
  given: (n : Nat) (h₂ : Injective S.X₂)
  proof: ⟨fun _ => hS.hasInjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ => hS.hasInjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

中文:
引理 hasInjectiveDimensionLT_X₃_iff
  条件: (n : 自然数) (h₂ : Injective S.X₂)
  证明: ⟨fun _ => hS.hasInjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ => hS.hasInjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

Depends on / 依赖: hS.hasInjectiveDimensionLT_X
-/
lemma hasInjectiveDimensionLT_X₃_iff (n : Nat) (h₂ : Injective S.X₂) :
    HasInjectiveDimensionLT S.X₃ (n + 1) ↔ HasInjectiveDimensionLT S.X₁ (n + 2) :=
  ⟨fun _ => hS.hasInjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ => hS.hasInjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

end ShortExact

end ShortComplex

instance (X Y : C) (n : Nat) [HasInjectiveDimensionLT X n]
    [HasInjectiveDimensionLT Y n] :
    HasInjectiveDimensionLT (X ⊞ Y) n :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact.hasInjectiveDimensionLT_X₂ n ‹_› ‹_›

/--
lemma `hasInjectiveDimensionLT_of_enoughProjectives` / 引理 `hasInjectiveDimensionLT_of_enoughProjectives`

English:
lemma hasInjectiveDimensionLT_of_enoughProjectives
  statement: [HasExt.{w} C] [EnoughProjectives C] (X : C)
  proof: by
  suffices forall ⦃d : Nat⦄ ⦃Y : C⦄ (e : Ext Y X d) (k : Nat), d = n + k -> e = 0 from
    HasInjectiveDimensionLT.mk (fun i hi Y e => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact this e k rfl)
  intro d Y e k hd
  induction k generalizing d Y with
  | zero =>
    obtain rfl

中文:
引理 hasInjectiveDimensionLT_of_enoughProjectives
  结论: [HasExt.{w} C] [EnoughProjectives C] (X : C)
  证明: by
  suffices forall ⦃d : Nat⦄ ⦃Y : C⦄ (e : Ext Y X d) (k : Nat), d = n + k -> e = 0 from
    HasInjectiveDimensionLT.mk (fun i hi Y e => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact this e k rfl)
  intro d Y e k hd
  induction k generalizing d Y with
  | zero =>
    obtain rfl

Depends on / 依赖: EnoughProjectives, EnoughProjectives.presentation, HasInjectiveDimensionLT, HasInjectiveDimensionLT.mk, Nat.exists_eq_add_of_le, ShortComplex, ShortComplex.exact_kernel, ShortComplex.mk, ShortExact, condition, exact_kernel, exists_eq_add_of_le, generalizing, kernel, kernel.condition, presentation, subsingleton
-/
lemma hasInjectiveDimensionLT_of_enoughProjectives [HasExt.{w} C] [EnoughProjectives C] (X : C)
    (n : Nat) (hX : forall Y : C, Subsingleton (Ext Y X n)) : HasInjectiveDimensionLT X n := by
  suffices forall ⦃d : Nat⦄ ⦃Y : C⦄ (e : Ext Y X d) (k : Nat), d = n + k -> e = 0 from
    HasInjectiveDimensionLT.mk (fun i hi Y e => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact this e k rfl)
  intro d Y e k hd
  induction k generalizing d Y with
  | zero =>
    obtain rfl : d = n := by simpa using hd
    subsingleton
  | succ k hk =>
    let ⟨p⟩ := EnoughProjectives.presentation Y
    have h : (ShortComplex.mk _ _ (kernel.condition p.f)).ShortExact :=
      { exact := ShortComplex.exact_kernel p.f }
    have hd : (n + k) + 1 = d := by lia
    obtain ⟨x, rfl⟩ := Ext.contravariant_sequence_exact₃ h X e
      (by subst hd; apply Ext.eq_zero_of_projective) ((add_comm _ _).trans hd)
    simp [hk x rfl]

end CategoryTheory

section InjectiveDimension

namespace CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/--
Definition of `injectiveDimension` / `injectiveDimension` 的定义

English:
definition injectiveDimension
  signature: (X : C)
  body: sInf {n : WithBot Nat∞ | forall (i : Nat), n < i -> HasInjectiveDimensionLT X i}

中文:
定义 injectiveDimension
  签名: (X : C)
  定义体: sInf {n : WithBot Nat∞ | forall (i : Nat), n < i -> HasInjectiveDimensionLT X i}

Depends on / 依赖: HasInjectiveDimensionLT, WithBot
-/
noncomputable def injectiveDimension (X : C) : WithBot Nat∞ :=
  sInf {n : WithBot Nat∞ | forall (i : Nat), n < i -> HasInjectiveDimensionLT X i}

/--
lemma `injectiveDimension_eq_of_iso` / 引理 `injectiveDimension_eq_of_iso`

English:
lemma injectiveDimension_eq_of_iso
  given: {X Y : C} (e : X ≅ Y)
  proof: by
  simp only [injectiveDimension]
  congr! 5
  exact ⟨fun h => hasInjectiveDimensionLT_of_iso e _,
    fun h => hasInjectiveDimensionLT_of_iso e.symm _⟩

中文:
引理 injectiveDimension_eq_of_iso
  条件: {X Y : C} (e : X ≅ Y)
  证明: by
  simp only [injectiveDimension]
  congr! 5
  exact ⟨fun h => hasInjectiveDimensionLT_of_iso e _,
    fun h => hasInjectiveDimensionLT_of_iso e.symm _⟩

Depends on / 依赖: e.symm, hasInjectiveDimensionLT_of_iso, injectiveDimension
-/
lemma injectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    injectiveDimension X = injectiveDimension Y := by
  simp only [injectiveDimension]
  congr! 5
  exact ⟨fun h => hasInjectiveDimensionLT_of_iso e _,
    fun h => hasInjectiveDimensionLT_of_iso e.symm _⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Retract.injectiveDimension_le` / 引理 `Retract.injectiveDimension_le`

English:
lemma Retract.injectiveDimension_le
  given: {X Y : C} (h : Retract X Y)
  proof: sInf_le_sInf_of_subset_insert_top (fun n hn => by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasInjectiveDimensionLT i)

中文:
引理 Retract.injectiveDimension_le
  条件: {X Y : C} (h : Retract X Y)
  证明: sInf_le_sInf_of_subset_insert_top (fun n hn => by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasInjectiveDimensionLT i)

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, Set.insert_eq_of_mem, Set.mem_ofPred_eq, forall_iff, h.hasInjectiveDimensionLT, hasInjectiveDimensionLT, implies_true, insert_eq_of_mem, mem_ofPred_eq, not_top_lt, sInf_le_sInf_of_subset_insert_top
-/
lemma Retract.injectiveDimension_le {X Y : C} (h : Retract X Y) :
    injectiveDimension X <= injectiveDimension Y :=
  sInf_le_sInf_of_subset_insert_top (fun n hn => by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasInjectiveDimensionLT i)

/--
lemma `injectiveDimension_lt_iff` / 引理 `injectiveDimension_lt_iff`

English:
lemma injectiveDimension_lt_iff
  given: {X : C} {n : Nat}
  proof: by
  refine ⟨fun h => ?_, fun h => sInf_lt_iff.2 ?_⟩
  · have : injectiveDimension X in _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_ofPred_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ => hasInjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n, 

中文:
引理 injectiveDimension_lt_iff
  条件: {X : C} {n : 自然数}
  证明: by
  refine ⟨fun h => ?_, fun h => sInf_lt_iff.2 ?_⟩
  · have : injectiveDimension X in _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_ofPred_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ => hasInjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n, 

Depends on / 依赖: ENat.WithBot.lt_add_one_iff, Set.mem_ofPred_eq, WithBot, csInf_mem, hasInjectiveDimensionLT_of_ge, injectiveDimension, lt_add_one_iff, mem_ofPred_eq, sInf_lt_iff
-/
lemma injectiveDimension_lt_iff {X : C} {n : Nat} :
    injectiveDimension X < n ↔ HasInjectiveDimensionLT X n := by
  refine ⟨fun h => ?_, fun h => sInf_lt_iff.2 ?_⟩
  · have : injectiveDimension X in _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_ofPred_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ => hasInjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n, fun i hi => hasInjectiveDimensionLT_of_ge _ (n + 1) _ (by simpa using hi),
        by simp [ENat.WithBot.lt_add_one_iff]⟩

/--
lemma `injectiveDimension_le_iff` / 引理 `injectiveDimension_le_iff`

English:
lemma injectiveDimension_le_iff
  given: (X : C) (n : Nat)
  proof: by
  simp [← injectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]

中文:
引理 injectiveDimension_le_iff
  条件: (X : C) (n : 自然数)
  证明: by
  simp [← injectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]

Depends on / 依赖: ENat.WithBot.lt_add_one_iff, WithBot, injectiveDimension_lt_iff, lt_add_one_iff
-/
lemma injectiveDimension_le_iff (X : C) (n : Nat) :
    injectiveDimension X <= n ↔ HasInjectiveDimensionLE X n := by
  simp [← injectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]

/--
lemma `injectiveDimension_ge_iff` / 引理 `injectiveDimension_ge_iff`

English:
lemma injectiveDimension_ge_iff
  given: (X : C) (n : Nat)
  proof: by
  contrapose!; exact injectiveDimension_lt_iff

中文:
引理 injectiveDimension_ge_iff
  条件: (X : C) (n : 自然数)
  证明: by
  contrapose!; exact injectiveDimension_lt_iff

Depends on / 依赖: contrapose, injectiveDimension_lt_iff
-/
lemma injectiveDimension_ge_iff (X : C) (n : Nat) :
    n <= injectiveDimension X ↔ ¬ HasInjectiveDimensionLT X n := by
  contrapose!; exact injectiveDimension_lt_iff

/--
lemma `injectiveDimension_eq_bot_iff` / 引理 `injectiveDimension_eq_bot_iff`

English:
lemma injectiveDimension_eq_bot_iff
  given: (X : C)
  proof: by
  rw [← hasInjectiveDimensionLT_zero_iff_isZero]; rw [← injectiveDimension_lt_iff]; rw [Nat.cast_zero]; rw [← WithBot.lt_coe_bot]; rw [bot_eq_zero']; rw [WithBot.coe_zero]

中文:
引理 injectiveDimension_eq_bot_iff
  条件: (X : C)
  证明: by
  rw [← hasInjectiveDimensionLT_zero_iff_isZero]; rw [← injectiveDimension_lt_iff]; rw [Nat.cast_zero]; rw [← WithBot.lt_coe_bot]; rw [bot_eq_zero']; rw [WithBot.coe_zero]

Depends on / 依赖: Nat.cast_zero, WithBot, WithBot.coe_zero, WithBot.lt_coe_bot, bot_eq_zero, cast_zero, coe_zero, hasInjectiveDimensionLT_zero_iff_isZero, injectiveDimension_lt_iff, lt_coe_bot
-/
lemma injectiveDimension_eq_bot_iff (X : C) :
    injectiveDimension X = ⊥ ↔ Limits.IsZero X := by
  rw [← hasInjectiveDimensionLT_zero_iff_isZero]; rw [← injectiveDimension_lt_iff]; rw [Nat.cast_zero]; rw [← WithBot.lt_coe_bot]; rw [bot_eq_zero']; rw [WithBot.coe_zero]

/--
lemma `injectiveDimension_ne_top_iff` / 引理 `injectiveDimension_ne_top_iff`

English:
lemma injectiveDimension_ne_top_iff
  given: (X : C)
  proof: by
  generalize hd : injectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← injectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_eq,

中文:
引理 injectiveDimension_ne_top_iff
  条件: (X : C)
  证明: by
  generalize hd : injectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← injectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_eq,

Depends on / 依赖: ENat.natCast_ne_top, WithBot, WithBot.coe_eq_coe, WithBot.coe_top, bot_ne_top, coe_eq_coe, coe_top, false_and, false_or, generalize, injectiveDimension, injectiveDimension_le_iff, natCast_ne_top, ne_eq, not_false_eq_true, not_true_eq_false, top_le_iff, true_and, true_iff
-/
lemma injectiveDimension_ne_top_iff (X : C) :
    injectiveDimension X != ⊤ ↔ exists n, HasInjectiveDimensionLE X n := by
  generalize hd : injectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← injectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_eq, not_true_eq_false, false_and, true_and, false_or] at this
      obtain ⟨n, hn⟩ := this
      rw [← injectiveDimension_le_iff]; rw [hd]; rw [WithBot.coe_top]; rw [top_le_iff] at hn
      exact ENat.natCast_ne_top _ ((WithBot.coe_eq_coe).1 hn)
    | coe d =>
      simp only [ne_eq, WithBot.coe_eq_top, ENat.natCast_ne_top, not_false_eq_true, true_iff]
      exact ⟨d, by simpa only [← injectiveDimension_le_iff] using! hd.le⟩

end CategoryTheory

end InjectiveDimension
