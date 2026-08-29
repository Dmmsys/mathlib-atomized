/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Class group map induced by an extension of domains

For an injective extension `A → B` of commutative domains (equivalently `Module.IsTorsionFree A B`),
we construct the group homomorphism `ClassGroup.extendedHom : ClassGroup A →* ClassGroup B` given by
pushing fractional ideals forward along the algebra map.

## Main definitions

- `ClassGroup.extendedHom A B`: the induced map between the class groups.
- `ClassGroup.extendedIdeal A B`: the extension of a nonzero integral ideal.

## Main results

- `ClassGroup.extendedHom_mk`: compatibility with representatives as fractional ideals.
- `ClassGroup.extendedHom_mk0`: compatibility with representatives as nonzero integral ideals.
- `ClassGroup.extendedHom_comp`: compatibility of extension in a tower `A → B → C`.
- `ClassGroup.extendedHom_eq_one_of_forall_isPrincipal`: if the extension of every ideal is
  principal, then `ClassGroup.extendedHom A B` is trivial.
-/

public section

open scoped nonZeroDivisors

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.IsTorsionFree A B]

namespace ClassGroup

section CommRing

variable [IsDomain A] [IsDomain B]

/--
Definition of `extendedHom` / `extendedHom` 的定义

English:
definition extendedHom
  signature: : ClassGroup A ->* ClassGroup B
  body: QuotientGroup.map _ _
    (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      refine ⟨Units.mk0 (IsFractionRing.map (j := algebraMap A B)
        (FaithfulSMul.algebraMap_injective _ _) (α : FractionRing A))
        (by simp [α.ne_zero]), ?_

中文:
定义 extendedHom
  签名: : ClassGroup A ->* ClassGroup B
  定义体: QuotientGroup.map _ _
    (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      refine ⟨Units.mk0 (IsFractionRing.map (j := algebraMap A B)
        (FaithfulSMul.algebraMap_injective _ _) (α : FractionRing A))
        (by simp [α.ne_zero]), ?_

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, FractionalIdeal, FractionalIdeal.extendedHom, FractionalIdeal.extendedHom_spanSingleton, IsFractionRing, IsFractionRing.map, QuotientGroup, QuotientGroup.map, Units.coe_map, Units.map, Units.mk0, Units.val_mk0, algebraMap, algebraMap_injective, coe_map, coe_toPrincipalIdeal, extendedHom, extendedHom_spanSingleton
-/
noncomputable def extendedHom : ClassGroup A ->* ClassGroup B :=
  QuotientGroup.map _ _
    (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      refine ⟨Units.mk0 (IsFractionRing.map (j := algebraMap A B)
        (FaithfulSMul.algebraMap_injective _ _) (α : FractionRing A))
        (by simp [α.ne_zero]), ?_⟩
      simpa [coe_toPrincipalIdeal, Units.coe_map, Units.val_mk0] using!
        (FractionalIdeal.extendedHom_spanSingleton (FractionRing B) B _).symm)

@[simp]
/--
lemma `extendedHom_quotientMk` / 引理 `extendedHom_quotientMk`

English:
lemma extendedHom_quotientMk
  given: (α : (FractionalIdeal A⁰ (FractionRing A))ˣ)
  proof: by
  rfl

@[simp]

中文:
引理 extendedHom_quotientMk
  条件: (α : (FractionalIdeal A⁰ (FractionRing A))ˣ)
  证明: by
  rfl

@[simp]
-/
lemma extendedHom_quotientMk (α : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extendedHom A B (QuotientGroup.mk α) = QuotientGroup.mk
      (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom α) := by
  rfl

@[simp]
/--
theorem `extendedHom_mk` / 定理 `extendedHom_mk`

English:
theorem extendedHom_mk
  given: (I : (FractionalIdeal A⁰ (FractionRing A))ˣ)
  proof: by
  rw [← ClassGroup.Quot_mk_eq_mk]; rw [← ClassGroup.Quot_mk_eq_mk]
  exact extendedHom_quotientMk A B I

中文:
定理 extendedHom_mk
  条件: (I : (FractionalIdeal A⁰ (FractionRing A))ˣ)
  证明: by
  rw [← ClassGroup.Quot_mk_eq_mk]; rw [← ClassGroup.Quot_mk_eq_mk]
  exact extendedHom_quotientMk A B I

Depends on / 依赖: ClassGroup, ClassGroup.Quot_mk_eq_mk, Quot_mk_eq_mk, extendedHom_quotientMk
-/
theorem extendedHom_mk (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extendedHom A B (ClassGroup.mk _ I) = ClassGroup.mk _
        (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom I) := by
  rw [← ClassGroup.Quot_mk_eq_mk]; rw [← ClassGroup.Quot_mk_eq_mk]
  exact extendedHom_quotientMk A B I

/--
Definition of `extendedIdeal` / `extendedIdeal` 的定义

English:
abbreviation extendedIdeal
  signature: (I : (Ideal A)⁰)
  body: ⟨I.1.map (algebraMap A B), mem_nonZeroDivisors_iff_ne_zero.mpr
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩

@[simp]

中文:
缩写 extendedIdeal
  签名: (I : (理想 A)⁰)
  定义体: ⟨I.1.map (algebraMap A B), mem_nonZeroDivisors_iff_ne_zero.mpr
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩

@[simp]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Ideal.map_eq_bot_iff_of_injective, algebraMap, algebraMap_injective, map_eq_bot_iff_of_injective, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mp, mem_nonZeroDivisors_iff_ne_zero.mpr, not.mpr
-/
abbrev extendedIdeal (I : (Ideal A)⁰) : (Ideal B)⁰ :=
⟨I.1.map (algebraMap A B), mem_nonZeroDivisors_iff_ne_zero.mpr
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩

@[simp]
/--
theorem `extendedIdeal_extendedIdeal` / 定理 `extendedIdeal_extendedIdeal`

English:
theorem extendedIdeal_extendedIdeal
  statement: (C : Type*) [CommRing C] [IsDomain C] [Algebra B C]
  proof: by
  simp [Ideal.map_map, IsScalarTower.algebraMap_eq A B C]

中文:
定理 extendedIdeal_extendedIdeal
  结论: (C : 类型) [交换环 C] [是整环 C] [代数 B C]
  证明: by
  simp [Ideal.map_map, IsScalarTower.algebraMap_eq A B C]

Depends on / 依赖: Ideal.map_map, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap_eq, map_map
-/
theorem extendedIdeal_extendedIdeal (C : Type*) [CommRing C] [IsDomain C] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Module.IsTorsionFree B C]
    [Module.IsTorsionFree A C] (I : (Ideal A)⁰) :
    extendedIdeal B C (extendedIdeal A B I) = extendedIdeal A C I := by
  simp [Ideal.map_map, IsScalarTower.algebraMap_eq A B C]

end CommRing

section DedekindDomain

variable [IsDedekindDomain A] (C : Type*) [CommRing C] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
  [IsDedekindDomain C]

/--
theorem `extendedHom_mk0'` / 定理 `extendedHom_mk0'`

English:
theorem extendedHom_mk0'
  given: [IsDomain B] (I : (Ideal A)⁰)
  proof: by
  rw [← ClassGroup.mk_mk0 (FractionRing A)]; rw [extendedHom_mk]

中文:
定理 extendedHom_mk0'
  条件: [是整环 B] (I : (理想 A)⁰)
  证明: by
  rw [← ClassGroup.mk_mk0 (FractionRing A)]; rw [extendedHom_mk]

Depends on / 依赖: ClassGroup, ClassGroup.mk_mk0, FractionRing, extendedHom_mk, mk_mk0
-/
theorem extendedHom_mk0' [IsDomain B] (I : (Ideal A)⁰) :
    extendedHom A B (ClassGroup.mk0 I) =
      ClassGroup.mk _ (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom
      (FractionalIdeal.mk0 (FractionRing A) I)) := by
  rw [← ClassGroup.mk_mk0 (FractionRing A)]; rw [extendedHom_mk]

variable [IsDedekindDomain B]

/--
lemma `extendedHom_mk0` / 引理 `extendedHom_mk0`

English:
lemma extendedHom_mk0
  given: (I : (Ideal A)⁰)
  proof: by
  rw [mk0_eq_quotientMk]; rw [mk0_eq_quotientMk]; rw [extendedHom_quotientMk]
  congr; ext : 1
  exact FractionalIdeal.extendedHom_coeIdeal_eq_map (L := FractionRing B) (B := B) _


@[simp]

中文:
引理 extendedHom_mk0
  条件: (I : (理想 A)⁰)
  证明: by
  rw [mk0_eq_quotientMk]; rw [mk0_eq_quotientMk]; rw [extendedHom_quotientMk]
  congr; ext : 1
  exact FractionalIdeal.extendedHom_coeIdeal_eq_map (L := FractionRing B) (B := B) _


@[simp]

Depends on / 依赖: FractionRing, FractionalIdeal, FractionalIdeal.extendedHom_coeIdeal_eq_map, extendedHom_coeIdeal_eq_map, extendedHom_quotientMk, mk0_eq_quotientMk
-/
lemma extendedHom_mk0 (I : (Ideal A)⁰) :
    extendedHom A B (ClassGroup.mk0 I) = ClassGroup.mk0 (extendedIdeal A B I) := by
  rw [mk0_eq_quotientMk]; rw [mk0_eq_quotientMk]; rw [extendedHom_quotientMk]
  congr; ext : 1
  exact FractionalIdeal.extendedHom_coeIdeal_eq_map (L := FractionRing B) (B := B) _


@[simp]
/--
theorem `extendedHom_comp_apply` / 定理 `extendedHom_comp_apply`

English:
theorem extendedHom_comp_apply
  given: (x : ClassGroup A)
  proof: by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0 A B I]; rw [extendedHom_mk0 B C (extendedIdeal A B I)]; rw [extendedHom_mk0 A C I]; rw [extendedIdeal_extendedIdeal]

中文:
定理 extendedHom_comp_apply
  条件: (x : ClassGroup A)
  证明: by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0 A B I]; rw [extendedHom_mk0 B C (extendedIdeal A B I)]; rw [extendedHom_mk0 A C I]; rw [extendedIdeal_extendedIdeal]

Depends on / 依赖: ClassGroup, ClassGroup.mk0_surjective, extendedHom_mk0, extendedIdeal, extendedIdeal_extendedIdeal, mk0_surjective
-/
theorem extendedHom_comp_apply (x : ClassGroup A) :
      extendedHom B C (extendedHom A B x) = extendedHom A C x := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0 A B I]; rw [extendedHom_mk0 B C (extendedIdeal A B I)]; rw [extendedHom_mk0 A C I]; rw [extendedIdeal_extendedIdeal]

/--
theorem `extendedHom_comp` / 定理 `extendedHom_comp`

English:
theorem extendedHom_comp
  statement: (extendedHom B C).comp (extendedHom A B) = extendedHom A C
  proof: by
  ext x
  exact extendedHom_comp_apply A B C x

中文:
定理 extendedHom_comp
  结论: (extendedHom B C).comp (extendedHom A B) = extendedHom A C
  证明: by
  ext x
  exact extendedHom_comp_apply A B C x

Depends on / 依赖: extendedHom_comp_apply
-/
theorem extendedHom_comp : (extendedHom B C).comp (extendedHom A B) = extendedHom A C := by
  ext x
  exact extendedHom_comp_apply A B C x

/--
theorem `extendedHom_eq_one_of_forall_isPrincipal` / 定理 `extendedHom_eq_one_of_forall_isPrincipal`

English:
theorem extendedHom_eq_one_of_forall_isPrincipal
  proof: by
  ext x
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0]; rw [MonoidHom.one_apply]
  exact (ClassGroup.mk0_eq_one_iff (extendedIdeal A B I).2).mpr (by simpa using h I)

中文:
定理 extendedHom_eq_one_of_对任意_isPrincipal
  证明: by
  ext x
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0]; rw [MonoidHom.one_apply]
  exact (ClassGroup.mk0_eq_one_iff (extendedIdeal A B I).2).mpr (by simpa using h I)

Depends on / 依赖: ClassGroup, ClassGroup.mk0_eq_one_iff, ClassGroup.mk0_surjective, MonoidHom, MonoidHom.one_apply, extendedHom_mk0, extendedIdeal, mk0_eq_one_iff, mk0_surjective, one_apply
-/
theorem extendedHom_eq_one_of_forall_isPrincipal
    (h : forall I : (Ideal A), (I.map (algebraMap A B)).IsPrincipal) : extendedHom A B = 1 := by
  ext x
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0]; rw [MonoidHom.one_apply]
  exact (ClassGroup.mk0_eq_one_iff (extendedIdeal A B I).2).mpr (by simpa using h I)

end DedekindDomain

end ClassGroup

end
