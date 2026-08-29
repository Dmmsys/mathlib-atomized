/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Data.ENat.Lattice

/-!
# Projective dimension

In an abelian category `C`, we shall say that `X : C` has projective dimension `< n`
if all `Ext X Y i` vanish when `n ≤ i`. This defines a type class
`HasProjectiveDimensionLT X n`. We also define a type class
`HasProjectiveDimensionLE X n` as an abbreviation for
`HasProjectiveDimensionLT X (n + 1)`.
(Note that the fact that `X` is a zero object is equivalent to the condition
`HasProjectiveDimensionLT X 0`, but this cannot be expressed in terms of
`HasProjectiveDimensionLE`.)

We also define the projective dimension in `WithBot ℕ∞` as `projectiveDimension`,
`projectiveDimension X = ⊥` iff `X` is zero and behaves as expected on non-negative values.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Abelian Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/--
Definition of `HasProjectiveDimensionLT` / `HasProjectiveDimensionLT` 的定义

English:
class HasProjectiveDimensionLT
  parameters: (X : C) (n : Nat)
  (no additional axioms)

中文:
类 有ProjectiveDimensionLT
  参数: (X : C) (n : 自然数)
  (无附加公理)

Depends on / 依赖: HasExt, HasExt.standard, standard
-/
class HasProjectiveDimensionLT (X : C) (n : Nat) : Prop where mk' ::
  subsingleton' (i : Nat) (hi : n <= i) ⦃Y : C⦄ :
    letI := HasExt.standard C
    Subsingleton (Ext.{max u v} X Y i)

/--
Definition of `HasProjectiveDimensionLE` / `HasProjectiveDimensionLE` 的定义

English:
abbreviation HasProjectiveDimensionLE
  signature: (X : C) (n : Nat)
  body: HasProjectiveDimensionLT X (n + 1)

中文:
缩写 HasProjectiveDimensionLE
  签名: (X : C) (n : 自然数)
  定义体: HasProjectiveDimensionLT X (n + 1)

Depends on / 依赖: HasProjectiveDimensionLT
-/
abbrev HasProjectiveDimensionLE (X : C) (n : Nat) : Prop :=
  HasProjectiveDimensionLT X (n + 1)

namespace HasProjectiveDimensionLT

variable [HasExt.{w} C] (X : C) (n : Nat)

/--
lemma `subsingleton` / 引理 `subsingleton`

English:
lemma subsingleton
  given: [hX : HasProjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C)
  proof: by
  let := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

中文:
引理 subsingleton
  条件: [hX : 有ProjectiveDimensionLT X n] (i : 自然数) (hi : n <= i) (Y : C)
  证明: by
  let := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

Depends on / 依赖: Ext.chgUniv, HasExt, HasExt.standard, chgUniv, hX.subsingleton, standard, subsingleton, symm.subsingleton
-/
lemma subsingleton [hX : HasProjectiveDimensionLT X n] (i : Nat) (hi : n <= i) (Y : C) :
    Subsingleton (Ext.{w} X Y i) := by
  let := HasExt.standard C
  have := hX.subsingleton' i hi
  exact Ext.chgUniv.{w, max u v}.symm.subsingleton

variable {X n} in
/--
lemma `mk` / 引理 `mk`

English:
lemma mk
  given: (hX : forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext X Y i), e = 0)
  proof: by
    have : Subsingleton (Ext X Y i) := ⟨fun e₁ e₂ => by simp only [hX i hi]⟩
    let := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

中文:
引理 mk
  条件: (hX : 对任意 (i : 自然数) (_ : n <= i) ⦃Y : C⦄, 对任意 (e : Ext X Y i), e = 0)
  证明: by
    have : Subsingleton (Ext X Y i) := ⟨fun e₁ e₂ => by simp only [hX i hi]⟩
    let := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

Depends on / 依赖: Ext.chgUniv, HasExt, HasExt.standard, Subsingleton, chgUniv, standard, subsingleton, symm.subsingleton
-/
lemma mk (hX : forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext X Y i), e = 0) :
    HasProjectiveDimensionLT X n where
  subsingleton' i hi Y := by
    have : Subsingleton (Ext X Y i) := ⟨fun e₁ e₂ => by simp only [hX i hi]⟩
    let := HasExt.standard C
    exact Ext.chgUniv.{max u v, w}.symm.subsingleton

end HasProjectiveDimensionLT

/--
lemma `Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT` / 引理 `Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT`

English:
lemma Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT
  statement: [HasExt.{w} C]
  proof: (HasProjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

中文:
引理 交换.Ext.eq_zero_of_hasProjectiveDimensionLT
  结论: [HasExt.{w} C]
  证明: (HasProjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

Depends on / 依赖: HasProjectiveDimensionLT, HasProjectiveDimensionLT.subsingleton, subsingleton
-/
lemma Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT [HasExt.{w} C]
    {X Y : C} {i : Nat} (e : Ext X Y i) (n : Nat) [HasProjectiveDimensionLT X n]
    (hi : n <= i) : e = 0 :=
  (HasProjectiveDimensionLT.subsingleton X n i hi Y).elim _ _

section

variable (X : C) (n : Nat)

/--
lemma `hasProjectiveDimensionLT_iff` / 引理 `hasProjectiveDimensionLT_iff`

English:
lemma hasProjectiveDimensionLT_iff
  given: [HasExt.{w} C]
  proof: ⟨fun _ _ hi _ e => e.eq_zero_of_hasProjectiveDimensionLT n hi,
    HasProjectiveDimensionLT.mk⟩

中文:
引理 hasProjectiveDimensionLT_iff
  条件: [HasExt.{w} C]
  证明: ⟨fun _ _ hi _ e => e.eq_zero_of_hasProjectiveDimensionLT n hi,
    HasProjectiveDimensionLT.mk⟩

Depends on / 依赖: HasProjectiveDimensionLT, HasProjectiveDimensionLT.mk, e.eq_zero_of_hasProjectiveDimensionLT, eq_zero_of_hasProjectiveDimensionLT
-/
lemma hasProjectiveDimensionLT_iff [HasExt.{w} C] :
    HasProjectiveDimensionLT X n ↔
      forall (i : Nat) (_ : n <= i) ⦃Y : C⦄, forall (e : Ext X Y i), e = 0 :=
  ⟨fun _ _ hi _ e => e.eq_zero_of_hasProjectiveDimensionLT n hi,
    HasProjectiveDimensionLT.mk⟩

variable {X} in
/--
lemma `Limits.IsZero.hasProjectiveDimensionLT_zero` / 引理 `Limits.IsZero.hasProjectiveDimensionLT_zero`

English:
lemma Limits.IsZero.hasProjectiveDimensionLT_zero
  given: (hX : IsZero X)
  proof: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.mk₀_id_comp]; rw [hX.eq_of_src (𝟙 X) 0]; rw [Ext.mk₀_zero]; rw [Ext.zero_comp]

中文:
引理 Limits.是零.hasProjectiveDimensionLT_zero
  条件: (hX : 是零 X)
  证明: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.mk₀_id_comp]; rw [hX.eq_of_src (𝟙 X) 0]; rw [Ext.mk₀_zero]; rw [Ext.zero_comp]

Depends on / 依赖: Ext.mk, Ext.zero_comp, HasExt, HasExt.standard, e.mk, eq_of_src, hX.eq_of_src, hasProjectiveDimensionLT_iff, standard, zero_comp
-/
lemma Limits.IsZero.hasProjectiveDimensionLT_zero (hX : IsZero X) :
    HasProjectiveDimensionLT X 0 := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  rw [← e.mk₀_id_comp]; rw [hX.eq_of_src (𝟙 X) 0]; rw [Ext.mk₀_zero]; rw [Ext.zero_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasProjectiveDimensionLT (0 : C) 0
  body: (isZero_zero C).hasProjectiveDimensionLT_zero

中文:
实例 :
  签名: 有ProjectiveDimensionLT (0 : C) 0
  定义体: (isZero_zero C).hasProjectiveDimensionLT_zero
-/
instance : HasProjectiveDimensionLT (0 : C) 0 :=
  (isZero_zero C).hasProjectiveDimensionLT_zero

/--
lemma `isZero_of_hasProjectiveDimensionLT_zero` / 引理 `isZero_of_hasProjectiveDimensionLT_zero`

English:
lemma isZero_of_hasProjectiveDimensionLT_zero
  given: [HasProjectiveDimensionLT X 0]
  statement: IsZero X
  proof: by
  let := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ 0 (by rfl)

中文:
引理 isZero_of_hasProjectiveDimensionLT_zero
  条件: [有ProjectiveDimensionLT X 0]
  结论: 是零 X
  证明: by
  let := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ 0 (by rfl)

Depends on / 依赖: Abelian, Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT, Ext.homEquiv, Ext.mk, HasExt, HasExt.standard, IsZero, IsZero.iff_id_eq_zero, eq_zero_of_hasProjectiveDimensionLT, iff_id_eq_zero, injective, standard, symm.injective
-/
lemma isZero_of_hasProjectiveDimensionLT_zero [HasProjectiveDimensionLT X 0] : IsZero X := by
  let := HasExt.standard C
  rw [IsZero.iff_id_eq_zero]
  apply Ext.homEquiv₀.symm.injective
  simpa only [Ext.homEquiv₀_symm_apply, Ext.mk₀_zero]
    using Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ 0 (by rfl)

/--
lemma `hasProjectiveDimensionLT_zero_iff_isZero` / 引理 `hasProjectiveDimensionLT_zero_iff_isZero`

English:
lemma hasProjectiveDimensionLT_zero_iff_isZero
  statement: HasProjectiveDimensionLT X 0 ↔ IsZero X
  proof: ⟨fun _ => isZero_of_hasProjectiveDimensionLT_zero X, fun h => h.hasProjectiveDimensionLT_zero⟩

中文:
引理 hasProjectiveDimensionLT_zero_iff_isZero
  结论: 有ProjectiveDimensionLT X 0 ↔ 是零 X
  证明: ⟨fun _ => isZero_of_hasProjectiveDimensionLT_zero X, fun h => h.hasProjectiveDimensionLT_zero⟩

Depends on / 依赖: h.hasProjectiveDimensionLT_zero, hasProjectiveDimensionLT_zero, isZero_of_hasProjectiveDimensionLT_zero
-/
lemma hasProjectiveDimensionLT_zero_iff_isZero : HasProjectiveDimensionLT X 0 ↔ IsZero X :=
  ⟨fun _ => isZero_of_hasProjectiveDimensionLT_zero X, fun h => h.hasProjectiveDimensionLT_zero⟩

/--
lemma `hasProjectiveDimensionLT_of_ge` / 引理 `hasProjectiveDimensionLT_of_ge`

English:
lemma hasProjectiveDimensionLT_of_ge
  statement: (m : Nat) (h : n <= m)
  proof: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasProjectiveDimensionLT n (by lia)

中文:
引理 hasProjectiveDimensionLT_of_ge
  结论: (m : 自然数) (h : n <= m)
  证明: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasProjectiveDimensionLT n (by lia)

Depends on / 依赖: HasExt, HasExt.standard, e.eq_zero_of_hasProjectiveDimensionLT, eq_zero_of_hasProjectiveDimensionLT, hasProjectiveDimensionLT_iff, standard
-/
lemma hasProjectiveDimensionLT_of_ge (m : Nat) (h : n <= m)
    [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X m := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  exact e.eq_zero_of_hasProjectiveDimensionLT n (by lia)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasProjectiveDimensionLT
  signature: X n] (k
  body: hasProjectiveDimensionLT_of_ge X n (n + k) (by lia)

中文:
实例 [有ProjectiveDimensionLT
  签名: X n] (k
  定义体: hasProjectiveDimensionLT_of_ge X n (n + k) (by lia)
-/
instance [HasProjectiveDimensionLT X n] (k : Nat) :
    HasProjectiveDimensionLT X (n + k) :=
  hasProjectiveDimensionLT_of_ge X n (n + k) (by lia)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasProjectiveDimensionLT
  signature: X n] (k
  body: hasProjectiveDimensionLT_of_ge X n (k + n) (by lia)

中文:
实例 [有ProjectiveDimensionLT
  签名: X n] (k
  定义体: hasProjectiveDimensionLT_of_ge X n (k + n) (by lia)
-/
instance [HasProjectiveDimensionLT X n] (k : Nat) :
    HasProjectiveDimensionLT X (k + n) :=
  hasProjectiveDimensionLT_of_ge X n (k + n) (by lia)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasProjectiveDimensionLT
  signature: X n] :
  body: inferInstanceAs (HasProjectiveDimensionLT X (n + 1))

中文:
实例 [有ProjectiveDimensionLT
  签名: X n] :
  定义体: inferInstanceAs (HasProjectiveDimensionLT X (n + 1))
-/
instance [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X n.succ :=
  inferInstanceAs (HasProjectiveDimensionLT X (n + 1))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Projective
  signature: X] : HasProjectiveDimensionLT X 1
  body: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_projective

中文:
实例 [投射
  签名: X] : 有ProjectiveDimensionLT X 1
  定义体: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_projective
-/
instance [Projective X] : HasProjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y e
  obtain _ | i := i
  · simp at hi
  · exact e.eq_zero_of_projective

variable {X} in
/--
lemma `projective_iff_subsingleton_ext_one` / 引理 `projective_iff_subsingleton_ext_one`

English:
lemma projective_iff_subsingleton_ext_one
  given: [HasExt.{w} C]
  proof: by
  refine ⟨fun h => HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h => ⟨fun f g _ => ?_⟩⟩
  obtain ⟨φ, hφ⟩ :=
    Ext.covariant_sequence_exact₃ _ { exact := ShortComplex.exact_kernel g }
      (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjec

中文:
引理 projective_iff_subsingleton_ext_one
  条件: [HasExt.{w} C]
  证明: by
  refine ⟨fun h => HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h => ⟨fun f g _ => ?_⟩⟩
  obtain ⟨φ, hφ⟩ :=
    Ext.covariant_sequence_exact₃ _ { exact := ShortComplex.exact_kernel g }
      (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjec

Depends on / 依赖: Ext.covariant_sequence_exact, Ext.homEquiv, Ext.mk, HasProjectiveDimensionLT, HasProjectiveDimensionLT.subsingleton, ShortComplex, ShortComplex.exact_kernel, exact_kernel, injective, subsingleton, surjective, symm.injective, symm.surjective, zero_add
-/
lemma projective_iff_subsingleton_ext_one [HasExt.{w} C] :
    Projective X ↔ forall ⦃Y : C⦄, Subsingleton (Ext X Y 1) := by
  refine ⟨fun h => HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl),
    fun h => ⟨fun f g _ => ?_⟩⟩
  obtain ⟨φ, hφ⟩ :=
    Ext.covariant_sequence_exact₃ _ { exact := ShortComplex.exact_kernel g }
      (Ext.mk₀ f) (zero_add 1) (by subsingleton)
  obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective φ
  exact ⟨φ, Ext.homEquiv₀.symm.injective (by simpa using hφ)⟩

variable {X} in
/--
lemma `projective_iff_hasProjectiveDimensionLT_one` / 引理 `projective_iff_hasProjectiveDimensionLT_one`

English:
lemma projective_iff_hasProjectiveDimensionLT_one
  proof: by
  let := HasExt.standard C
  exact ⟨fun _ => inferInstance, fun _ => projective_iff_subsingleton_ext_one.2
    (HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩

中文:
引理 projective_iff_hasProjectiveDimensionLT_one
  证明: by
  let := HasExt.standard C
  exact ⟨fun _ => inferInstance, fun _ => projective_iff_subsingleton_ext_one.2
    (HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩

Depends on / 依赖: HasExt, HasExt.standard, HasProjectiveDimensionLT, HasProjectiveDimensionLT.subsingleton, StructuredArrow, StructuredArrow.isEquivalenceMap, projective_iff_subsingleton_ext_one, standard, subsingleton
-/
lemma projective_iff_hasProjectiveDimensionLT_one :
    Projective X ↔ HasProjectiveDimensionLT X 1 := by
  let := HasExt.standard C
  exact ⟨fun _ => inferInstance, fun _ => projective_iff_subsingleton_ext_one.2
    (HasProjectiveDimensionLT.subsingleton X 1 1 (by rfl))⟩

/--
lemma `projective_iff_hasProjectiveDimensionLE_zero` / 引理 `projective_iff_hasProjectiveDimensionLE_zero`

English:
lemma projective_iff_hasProjectiveDimensionLE_zero
  statement: Projective X ↔ HasProjectiveDimensionLE X 0
  proof: projective_iff_hasProjectiveDimensionLT_one

中文:
引理 projective_iff_hasProjectiveDimensionLE_zero
  结论: 投射 X ↔ HasProjectiveDimensionLE X 0
  证明: projective_iff_hasProjectiveDimensionLT_one

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isEquivalenceMap, projective_iff_hasProjectiveDimensionLT_one
-/
lemma projective_iff_hasProjectiveDimensionLE_zero : Projective X ↔ HasProjectiveDimensionLE X 0 :=
  projective_iff_hasProjectiveDimensionLT_one

instance (priority := low) [HasProjectiveDimensionLT X 1] : Projective X :=
  projective_iff_hasProjectiveDimensionLT_one.mpr ‹_›

end

/--
lemma `Retract.hasProjectiveDimensionLT` / 引理 `Retract.hasProjectiveDimensionLT`

English:
lemma Retract.hasProjectiveDimensionLT
  statement: {X Y : C} (h : Retract X Y) (n : Nat)
  proof: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.mk₀_id_comp]; rw [← h.retract]; rw [← Ext.mk₀_comp_mk₀]; rw [Ext.comp_assoc_of_second_deg_zero]; rw [((Ext.mk₀ h.r).comp x (zero_add i)).eq_zero_of_hasProjectiveDimensionLT n hi]; rw [Ext.comp_zero]

中文:
引理 收缩.hasProjectiveDimensionLT
  结论: {X Y : C} (h : 收缩 X Y) (n : 自然数)
  证明: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.mk₀_id_comp]; rw [← h.retract]; rw [← Ext.mk₀_comp_mk₀]; rw [Ext.comp_assoc_of_second_deg_zero]; rw [((Ext.mk₀ h.r).comp x (zero_add i)).eq_zero_of_hasProjectiveDimensionLT n hi]; rw [Ext.comp_zero]

Depends on / 依赖: Ext.comp_assoc_of_second_deg_zero, Ext.comp_zero, Ext.mk, HasExt, HasExt.standard, comp_assoc_of_second_deg_zero, comp_zero, eq_zero_of_hasProjectiveDimensionLT, h.retract, hasProjectiveDimensionLT_iff, retract, standard, x.mk, zero_add
-/
lemma Retract.hasProjectiveDimensionLT {X Y : C} (h : Retract X Y) (n : Nat)
    [HasProjectiveDimensionLT Y n] :
    HasProjectiveDimensionLT X n := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi T x
  rw [← x.mk₀_id_comp]; rw [← h.retract]; rw [← Ext.mk₀_comp_mk₀]; rw [Ext.comp_assoc_of_second_deg_zero]; rw [((Ext.mk₀ h.r).comp x (zero_add i)).eq_zero_of_hasProjectiveDimensionLT n hi]; rw [Ext.comp_zero]

/--
lemma `hasProjectiveDimensionLT_of_iso` / 引理 `hasProjectiveDimensionLT_of_iso`

English:
lemma hasProjectiveDimensionLT_of_iso
  statement: {X X' : C} (e : X ≅ X') (n : Nat)
  proof: e.symm.retract.hasProjectiveDimensionLT n

中文:
引理 hasProjectiveDimensionLT_of_iso
  结论: {X X' : C} (e : X ≅ X') (n : 自然数)
  证明: e.symm.retract.hasProjectiveDimensionLT n

Depends on / 依赖: e.symm.retract.hasProjectiveDimensionLT, hasProjectiveDimensionLT, retract
-/
lemma hasProjectiveDimensionLT_of_iso {X X' : C} (e : X ≅ X') (n : Nat)
    [HasProjectiveDimensionLT X n] :
    HasProjectiveDimensionLT X' n :=
  e.symm.retract.hasProjectiveDimensionLT n

namespace ShortComplex

namespace ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (n : Nat)
include hS

-- In the following lemmas, the parameters `HasProjectiveDimensionLT` are
-- explicit as it is unlikely we may infer them, unless the short complex `S`
-- was declared reducible

/--
lemma `hasProjectiveDimensionLT_X₂` / 引理 `hasProjectiveDimensionLT_X₂`

English:
lemma hasProjectiveDimensionLT_X₂
  statement: (h₁ : HasProjectiveDimensionLT S.X₁ n)
  proof: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.contravariant_sequence_exact₂ hS _ x₂
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasProjectiveDimensionLT n hi]; rw [Ext.comp_zero]

中文:
引理 hasProjectiveDimensionLT_X₂
  结论: (h₁ : 有ProjectiveDimensionLT S.X₁ n)
  证明: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.contravariant_sequence_exact₂ hS _ x₂
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasProjectiveDimensionLT n hi]; rw [Ext.comp_zero]

Depends on / 依赖: Ext.comp_zero, Ext.contravariant_sequence_exact, Ext.eq_zero_of_hasProjectiveDimensionLT, HasExt, HasExt.standard, comp_zero, eq_zero_of_hasProjectiveDimensionLT, hasProjectiveDimensionLT_iff, standard
-/
lemma hasProjectiveDimensionLT_X₂ (h₁ : HasProjectiveDimensionLT S.X₁ n)
    (h₃ : HasProjectiveDimensionLT S.X₃ n) :
    HasProjectiveDimensionLT S.X₂ n := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₂
  obtain ⟨x₃, rfl⟩ := Ext.contravariant_sequence_exact₂ hS _ x₂
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ n hi)
  rw [x₃.eq_zero_of_hasProjectiveDimensionLT n hi]; rw [Ext.comp_zero]

/--
lemma `hasProjectiveDimensionLT_X₃` / 引理 `hasProjectiveDimensionLT_X₃`

English:
lemma hasProjectiveDimensionLT_X₃
  statement: (h₁ : HasProjectiveDimensionLT S.X₁ n)
  proof: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.contravariant_sequence_exact₃ hS _ x₃
      (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) hi) (add_comm _ _)
    rw [x₁.eq_zero_of_hasProjectiveDimensionLT n (by

中文:
引理 hasProjectiveDimensionLT_X₃
  结论: (h₁ : 有ProjectiveDimensionLT S.X₁ n)
  证明: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.contravariant_sequence_exact₃ hS _ x₃
      (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) hi) (add_comm _ _)
    rw [x₁.eq_zero_of_hasProjectiveDimensionLT n (by

Depends on / 依赖: Ext.comp_zero, Ext.contravariant_sequence_exact, Ext.eq_zero_of_hasProjectiveDimensionLT, HasExt, HasExt.standard, add_comm, comp_zero, eq_zero_of_hasProjectiveDimensionLT, hasProjectiveDimensionLT_iff, standard
-/
lemma hasProjectiveDimensionLT_X₃ (h₁ : HasProjectiveDimensionLT S.X₁ n)
    (h₂ : HasProjectiveDimensionLT S.X₂ (n + 1)) :
    HasProjectiveDimensionLT S.X₃ (n + 1) := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  rintro (_ | i) hi Y x₃
  · simp at hi
  · obtain ⟨x₁, rfl⟩ := Ext.contravariant_sequence_exact₃ hS _ x₃
      (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) hi) (add_comm _ _)
    rw [x₁.eq_zero_of_hasProjectiveDimensionLT n (by lia)]; rw [Ext.comp_zero]

/--
lemma `hasProjectiveDimensionLT_X₁` / 引理 `hasProjectiveDimensionLT_X₁`

English:
lemma hasProjectiveDimensionLT_X₁
  statement: (h₂ : HasProjectiveDimensionLT S.X₂ n)
  proof: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.contravariant_sequence_exact₁ hS _ x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) (by lia))
  rw [x₂.eq_zero_of_hasProjectiveDimensionLT n (by lia)]; rw [Ext.comp_z

中文:
引理 hasProjectiveDimensionLT_X₁
  结论: (h₂ : 有ProjectiveDimensionLT S.X₂ n)
  证明: by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.contravariant_sequence_exact₁ hS _ x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) (by lia))
  rw [x₂.eq_zero_of_hasProjectiveDimensionLT n (by lia)]; rw [Ext.comp_z

Depends on / 依赖: Ext.comp_zero, Ext.contravariant_sequence_exact, Ext.eq_zero_of_hasProjectiveDimensionLT, HasExt, HasExt.standard, add_comm, comp_zero, eq_zero_of_hasProjectiveDimensionLT, hasProjectiveDimensionLT_iff, standard
-/
lemma hasProjectiveDimensionLT_X₁ (h₂ : HasProjectiveDimensionLT S.X₂ n)
    (h₃ : HasProjectiveDimensionLT S.X₃ (n + 1)) :
    HasProjectiveDimensionLT S.X₁ n := by
  let := HasExt.standard C
  rw [hasProjectiveDimensionLT_iff]
  intro i hi Y x₁
  obtain ⟨x₂, rfl⟩ := Ext.contravariant_sequence_exact₁ hS _ x₁ (add_comm _ _)
    (Ext.eq_zero_of_hasProjectiveDimensionLT _ (n + 1) (by lia))
  rw [x₂.eq_zero_of_hasProjectiveDimensionLT n (by lia)]; rw [Ext.comp_zero]

/--
lemma `hasProjectiveDimensionLT_X₃_iff` / 引理 `hasProjectiveDimensionLT_X₃_iff`

English:
lemma hasProjectiveDimensionLT_X₃_iff
  given: (n : Nat) (h₂ : Projective S.X₂)
  proof: ⟨fun _ => hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ => hS.hasProjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

中文:
引理 hasProjectiveDimensionLT_X₃_iff
  条件: (n : 自然数) (h₂ : 投射 S.X₂)
  证明: ⟨fun _ => hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ => hS.hasProjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

Depends on / 依赖: hS.hasProjectiveDimensionLT_X
-/
lemma hasProjectiveDimensionLT_X₃_iff (n : Nat) (h₂ : Projective S.X₂) :
    HasProjectiveDimensionLT S.X₃ (n + 2) ↔ HasProjectiveDimensionLT S.X₁ (n + 1) :=
  ⟨fun _ => hS.hasProjectiveDimensionLT_X₁ (n + 1) inferInstance inferInstance,
    fun _ => hS.hasProjectiveDimensionLT_X₃ (n + 1) inferInstance inferInstance⟩

end ShortExact

end ShortComplex

instance (X Y : C) (n : Nat) [HasProjectiveDimensionLT X n] [HasProjectiveDimensionLT Y n] :
    HasProjectiveDimensionLT (X ⊞ Y) n :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact.hasProjectiveDimensionLT_X₂ n ‹_› ‹_›

/--
lemma `hasProjectiveDimensionLT_of_enoughInjectives` / 引理 `hasProjectiveDimensionLT_of_enoughInjectives`

English:
lemma hasProjectiveDimensionLT_of_enoughInjectives
  statement: [HasExt.{w} C] [EnoughInjectives C] (X : C)
  proof: by
  suffices forall ⦃d : Nat⦄ ⦃Y : C⦄ (e : Ext X Y d) (k : Nat), d = n + k -> e = 0 from
    HasProjectiveDimensionLT.mk (fun i hi Y e => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact this e k rfl)
  intro d Y e k hd
  induction k generalizing d Y with
  | zero =>
    obtain rf

中文:
引理 hasProjectiveDimensionLT_of_enoughInjectives
  结论: [HasExt.{w} C] [有足够单射 C] (X : C)
  证明: by
  suffices forall ⦃d : Nat⦄ ⦃Y : C⦄ (e : Ext X Y d) (k : Nat), d = n + k -> e = 0 from
    HasProjectiveDimensionLT.mk (fun i hi Y e => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact this e k rfl)
  intro d Y e k hd
  induction k generalizing d Y with
  | zero =>
    obtain rf

Depends on / 依赖: EnoughInjectives, EnoughInjectives.presentation, HasProjectiveDimensionLT, HasProjectiveDimensionLT.mk, Nat.exists_eq_add_of_le, ShortComplex, ShortComplex.exact_cokernel, ShortComplex.mk, ShortExact, cokernel, cokernel.condition, condition, exact_cokernel, exists_eq_add_of_le, generalizing, presentation, subsingleton
-/
lemma hasProjectiveDimensionLT_of_enoughInjectives [HasExt.{w} C] [EnoughInjectives C] (X : C)
    (n : Nat) (hX : forall Y : C, Subsingleton (Ext X Y n)) : HasProjectiveDimensionLT X n := by
  suffices forall ⦃d : Nat⦄ ⦃Y : C⦄ (e : Ext X Y d) (k : Nat), d = n + k -> e = 0 from
    HasProjectiveDimensionLT.mk (fun i hi Y e => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact this e k rfl)
  intro d Y e k hd
  induction k generalizing d Y with
  | zero =>
    obtain rfl : d = n := by simpa using hd
    subsingleton
  | succ k hk =>
    let ⟨p⟩ := EnoughInjectives.presentation Y
    have h : (ShortComplex.mk _ _ (cokernel.condition p.f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel p.f }
    have hd : n + k + 1 = d := by lia
    obtain ⟨x, rfl⟩ := Ext.covariant_sequence_exact₁ X h e
      (by subst hd; apply Ext.eq_zero_of_injective) hd
    simp [hk x rfl]

end CategoryTheory

section ProjectiveDimension

namespace CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Abelian C]

/--
Definition of `projectiveDimension` / `projectiveDimension` 的定义

English:
definition projectiveDimension
  signature: (X : C)
  body: sInf {n : WithBot Nat∞ | forall (i : Nat), n < i -> HasProjectiveDimensionLT X i}

中文:
定义 projectiveDimension
  签名: (X : C)
  定义体: sInf {n : WithBot Nat∞ | forall (i : Nat), n < i -> HasProjectiveDimensionLT X i}

Depends on / 依赖: HasProjectiveDimensionLT, WithBot
-/
noncomputable def projectiveDimension (X : C) : WithBot Nat∞ :=
  sInf {n : WithBot Nat∞ | forall (i : Nat), n < i -> HasProjectiveDimensionLT X i}

/--
lemma `projectiveDimension_eq_of_iso` / 引理 `projectiveDimension_eq_of_iso`

English:
lemma projectiveDimension_eq_of_iso
  given: {X Y : C} (e : X ≅ Y)
  proof: by
  simp only [projectiveDimension]
  congr! 5
  exact ⟨fun h => hasProjectiveDimensionLT_of_iso e _,
    fun h => hasProjectiveDimensionLT_of_iso e.symm _⟩

中文:
引理 projectiveDimension_eq_of_iso
  条件: {X Y : C} (e : X ≅ Y)
  证明: by
  simp only [projectiveDimension]
  congr! 5
  exact ⟨fun h => hasProjectiveDimensionLT_of_iso e _,
    fun h => hasProjectiveDimensionLT_of_iso e.symm _⟩

Depends on / 依赖: e.symm, hasProjectiveDimensionLT_of_iso, projectiveDimension
-/
lemma projectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    projectiveDimension X = projectiveDimension Y := by
  simp only [projectiveDimension]
  congr! 5
  exact ⟨fun h => hasProjectiveDimensionLT_of_iso e _,
    fun h => hasProjectiveDimensionLT_of_iso e.symm _⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Retract.projectiveDimension_le` / 引理 `Retract.projectiveDimension_le`

English:
lemma Retract.projectiveDimension_le
  given: {X Y : C} (h : Retract X Y)
  proof: sInf_le_sInf_of_subset_insert_top (fun n hn => by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasProjectiveDimensionLT i)

中文:
引理 收缩.projectiveDimension_le
  条件: {X Y : C} (h : 收缩 X Y)
  证明: sInf_le_sInf_of_subset_insert_top (fun n hn => by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasProjectiveDimensionLT i)

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, Set.insert_eq_of_mem, Set.mem_ofPred_eq, forall_iff, h.hasProjectiveDimensionLT, hasProjectiveDimensionLT, implies_true, insert_eq_of_mem, mem_ofPred_eq, not_top_lt, sInf_le_sInf_of_subset_insert_top
-/
lemma Retract.projectiveDimension_le {X Y : C} (h : Retract X Y) :
    projectiveDimension X <= projectiveDimension Y :=
  sInf_le_sInf_of_subset_insert_top (fun n hn => by
    simp only [Set.mem_ofPred_eq, not_top_lt, IsEmpty.forall_iff, implies_true,
      Set.insert_eq_of_mem] at hn ⊢
    intro i hi
    have := hn i hi
    exact h.hasProjectiveDimensionLT i)

/--
lemma `projectiveDimension_lt_iff` / 引理 `projectiveDimension_lt_iff`

English:
lemma projectiveDimension_lt_iff
  given: {X : C} {n : Nat}
  proof: by
  refine ⟨fun h => ?_, fun h => sInf_lt_iff.2 ?_⟩
  · have : projectiveDimension X in _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_ofPred_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ => hasProjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n

中文:
引理 projectiveDimension_lt_iff
  条件: {X : C} {n : 自然数}
  证明: by
  refine ⟨fun h => ?_, fun h => sInf_lt_iff.2 ?_⟩
  · have : projectiveDimension X in _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_ofPred_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ => hasProjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n

Depends on / 依赖: ENat.WithBot.lt_add_one_iff, Set.mem_ofPred_eq, WithBot, csInf_mem, hasProjectiveDimensionLT_of_ge, lt_add_one_iff, mem_ofPred_eq, projectiveDimension, sInf_lt_iff
-/
lemma projectiveDimension_lt_iff {X : C} {n : Nat} :
    projectiveDimension X < n ↔ HasProjectiveDimensionLT X n := by
  refine ⟨fun h => ?_, fun h => sInf_lt_iff.2 ?_⟩
  · have : projectiveDimension X in _ := csInf_mem ⟨⊤, by simp⟩
    simp only [Set.mem_ofPred_eq] at this
    exact this _ h
  · obtain _ | n := n
    · exact ⟨⊥, fun _ _ => hasProjectiveDimensionLT_of_ge _ 0 _ (by simp), by decide⟩
    · exact ⟨n, fun i hi => hasProjectiveDimensionLT_of_ge _ (n + 1) _ (by simpa using hi),
        by simp [ENat.WithBot.lt_add_one_iff]⟩

/--
lemma `projectiveDimension_le_iff` / 引理 `projectiveDimension_le_iff`

English:
lemma projectiveDimension_le_iff
  given: (X : C) (n : Nat)
  proof: by
  simp [← projectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]

中文:
引理 projectiveDimension_le_iff
  条件: (X : C) (n : 自然数)
  证明: by
  simp [← projectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]

Depends on / 依赖: ENat.WithBot.lt_add_one_iff, WithBot, lt_add_one_iff, projectiveDimension_lt_iff
-/
lemma projectiveDimension_le_iff (X : C) (n : Nat) :
    projectiveDimension X <= n ↔ HasProjectiveDimensionLE X n := by
  simp [← projectiveDimension_lt_iff, ← ENat.WithBot.lt_add_one_iff]

/--
lemma `projectiveDimension_ge_iff` / 引理 `projectiveDimension_ge_iff`

English:
lemma projectiveDimension_ge_iff
  given: (X : C) (n : Nat)
  proof: by
  contrapose!; exact projectiveDimension_lt_iff

中文:
引理 projectiveDimension_ge_iff
  条件: (X : C) (n : 自然数)
  证明: by
  contrapose!; exact projectiveDimension_lt_iff

Depends on / 依赖: contrapose, projectiveDimension_lt_iff
-/
lemma projectiveDimension_ge_iff (X : C) (n : Nat) :
    n <= projectiveDimension X ↔ ¬ HasProjectiveDimensionLT X n := by
  contrapose!; exact projectiveDimension_lt_iff

/--
lemma `projectiveDimension_eq_bot_iff` / 引理 `projectiveDimension_eq_bot_iff`

English:
lemma projectiveDimension_eq_bot_iff
  given: (X : C)
  proof: by
  rw [← hasProjectiveDimensionLT_zero_iff_isZero]; rw [← projectiveDimension_lt_iff]; rw [Nat.cast_zero]; rw [← WithBot.lt_coe_bot]; rw [bot_eq_zero']; rw [WithBot.coe_zero]

中文:
引理 projectiveDimension_eq_bot_iff
  条件: (X : C)
  证明: by
  rw [← hasProjectiveDimensionLT_zero_iff_isZero]; rw [← projectiveDimension_lt_iff]; rw [Nat.cast_zero]; rw [← WithBot.lt_coe_bot]; rw [bot_eq_zero']; rw [WithBot.coe_zero]

Depends on / 依赖: Nat.cast_zero, WithBot, WithBot.coe_zero, WithBot.lt_coe_bot, bot_eq_zero, cast_zero, coe_zero, hasProjectiveDimensionLT_zero_iff_isZero, lt_coe_bot, projectiveDimension_lt_iff
-/
lemma projectiveDimension_eq_bot_iff (X : C) :
    projectiveDimension X = ⊥ ↔ Limits.IsZero X := by
  rw [← hasProjectiveDimensionLT_zero_iff_isZero]; rw [← projectiveDimension_lt_iff]; rw [Nat.cast_zero]; rw [← WithBot.lt_coe_bot]; rw [bot_eq_zero']; rw [WithBot.coe_zero]

/--
lemma `projectiveDimension_ne_top_iff` / 引理 `projectiveDimension_ne_top_iff`

English:
lemma projectiveDimension_ne_top_iff
  given: (X : C)
  proof: by
  generalize hd : projectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← projectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_e

中文:
引理 projectiveDimension_ne_top_iff
  条件: (X : C)
  证明: by
  generalize hd : projectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← projectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_e

Depends on / 依赖: ENat.natCast_ne_top, WithBot, WithBot.coe_eq_coe, WithBot.coe_top, bot_ne_top, coe_eq_coe, coe_top, false_and, false_or, generalize, natCast_ne_top, ne_eq, not_false_eq_true, not_true_eq_false, projectiveDimension, projectiveDimension_le_iff, top_le_iff, true_and, true_iff
-/
lemma projectiveDimension_ne_top_iff (X : C) :
    projectiveDimension X != ⊤ ↔ exists n, HasProjectiveDimensionLE X n := by
  generalize hd : projectiveDimension X = d
  induction d with
  | bot =>
    simp only [ne_eq, bot_ne_top, not_false_eq_true, true_iff]
    exact ⟨0, by simp [← projectiveDimension_le_iff, hd]⟩
  | coe d =>
    induction d with
    | top =>
      by_contra!
      simp only [WithBot.coe_top, ne_eq, not_true_eq_false, false_and, true_and, false_or] at this
      obtain ⟨n, hn⟩ := this
      rw [← projectiveDimension_le_iff]; rw [hd]; rw [WithBot.coe_top]; rw [top_le_iff] at hn
      exact ENat.natCast_ne_top _ ((WithBot.coe_eq_coe).1 hn)
    | coe d =>
      simp only [ne_eq, WithBot.coe_eq_top, ENat.natCast_ne_top, not_false_eq_true, true_iff]
      exact ⟨d, by simpa only [← projectiveDimension_le_iff] using! hd.le⟩

/--
lemma `projectiveDimension_eq_zero_iff` / 引理 `projectiveDimension_eq_zero_iff`

English:
lemma projectiveDimension_eq_zero_iff
  given: (X : C)
  proof: by
  rw [← projectiveDimension_eq_bot_iff]; rw [projective_iff_hasProjectiveDimensionLE_zero]; rw [← projectiveDimension_le_iff]; rw [← WithBot.lt_zero_iff_eq_bot]; rw [not_lt]; rw [Nat.cast_zero]; rw [le_antisymm_iff]

中文:
引理 projectiveDimension_eq_zero_iff
  条件: (X : C)
  证明: by
  rw [← projectiveDimension_eq_bot_iff]; rw [projective_iff_hasProjectiveDimensionLE_zero]; rw [← projectiveDimension_le_iff]; rw [← WithBot.lt_zero_iff_eq_bot]; rw [not_lt]; rw [Nat.cast_zero]; rw [le_antisymm_iff]

Depends on / 依赖: Nat.cast_zero, WithBot, WithBot.lt_zero_iff_eq_bot, cast_zero, le_antisymm_iff, lt_zero_iff_eq_bot, not_lt, projectiveDimension_eq_bot_iff, projectiveDimension_le_iff, projective_iff_hasProjectiveDimensionLE_zero
-/
lemma projectiveDimension_eq_zero_iff (X : C) :
    projectiveDimension X = 0 ↔ Projective X ∧ ¬ Limits.IsZero X := by
  rw [← projectiveDimension_eq_bot_iff]; rw [projective_iff_hasProjectiveDimensionLE_zero]; rw [← projectiveDimension_le_iff]; rw [← WithBot.lt_zero_iff_eq_bot]; rw [not_lt]; rw [Nat.cast_zero]; rw [le_antisymm_iff]

end CategoryTheory

end ProjectiveDimension
