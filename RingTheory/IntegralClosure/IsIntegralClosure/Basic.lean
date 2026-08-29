/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

import Mathlib.RingTheory.Polynomial.Subring

/-!
# # Integral closure as a characteristic predicate

We prove basic properties of `IsIntegralClosure`.

-/

@[expose] public section

open Module Polynomial Submodule

section inv

open Algebra

variable {R S : Type*}

/--
theorem `IsIntegral.isUnit` / 定理 `IsIntegral.isUnit`

English:
theorem IsIntegral.isUnit
  statement: [Field R] [Ring S] [IsDomain S] [Algebra R S] {x : S}
  proof: have : FiniteDimensional R (R[x]) := .of_fg int.fg_adjoin_singleton
  (FiniteDimensional.isUnit R (K := R[x])
(x := ⟨x, subset_adjoin rfl⟩) mt Subtype.ext_iff.mp h0).map (R[x]).val

中文:
定理 是整.isUnit
  结论: [域 R] [环 S] [是整环 S] [代数 R S] {x : S}
  证明: have : FiniteDimensional R (R[x]) := .of_fg int.fg_adjoin_singleton
  (FiniteDimensional.isUnit R (K := R[x])
(x := ⟨x, subset_adjoin rfl⟩) mt Subtype.ext_iff.mp h0).map (R[x]).val

Depends on / 依赖: FiniteDimensional, FiniteDimensional.isUnit, Subtype, Subtype.ext_iff.mp, ext_iff, fg_adjoin_singleton, int.fg_adjoin_singleton, isUnit, of_fg, subset_adjoin
-/
theorem IsIntegral.isUnit [Field R] [Ring S] [IsDomain S] [Algebra R S] {x : S}
    (int : IsIntegral R x) (h0 : x != 0) : IsUnit x :=
  have : FiniteDimensional R (R[x]) := .of_fg int.fg_adjoin_singleton
  (FiniteDimensional.isUnit R (K := R[x])
(x := ⟨x, subset_adjoin rfl⟩) mt Subtype.ext_iff.mp h0).map (R[x]).val

/--
theorem `isField_of_isIntegral_of_isField'` / 定理 `isField_of_isIntegral_of_isField'`

English:
theorem isField_of_isIntegral_of_isField'
  statement: [CommRing R] [CommRing S] [IsDomain S]
  proof: ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    let := hR.toField
    obtain ⟨y, rfl⟩ := (Algebra.IsIntegral.isIntegral (R := R) x).isUnit hx
    exact ⟨y.inv, y.val_inv⟩

中文:
定理 isField_of_is整数egral_of_isField'
  结论: [交换环 R] [交换环 S] [是整环 S]
  证明: ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    let := hR.toField
    obtain ⟨y, rfl⟩ := (Algebra.IsIntegral.isIntegral (R := R) x).isUnit hx
    exact ⟨y.inv, y.val_inv⟩

Depends on / 依赖: zero_ne_one
-/
theorem isField_of_isIntegral_of_isField' [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] (hR : IsField R) : IsField S where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    let := hR.toField
    obtain ⟨y, rfl⟩ := (Algebra.IsIntegral.isIntegral (R := R) x).isUnit hx
    exact ⟨y.inv, y.val_inv⟩

variable [Field R] [DivisionRing S] [Algebra R S] {x : S} {A : Subalgebra R S}

/--
theorem `IsIntegral.inv_mem_adjoin` / 定理 `IsIntegral.inv_mem_adjoin`

English:
theorem IsIntegral.inv_mem_adjoin
  given: (int : IsIntegral R x)
  statement: x⁻¹ in R[x]
  proof: by
  obtain rfl | h0 := eq_or_ne x 0
  · rw [inv_zero]; exact Subalgebra.zero_mem _
  have : FiniteDimensional R (R[x]) := .of_fg int.fg_adjoin_singleton
  obtain ⟨⟨y, hy⟩, h1⟩ := FiniteDimensional.exists_mul_eq_one R
    (K := R[x]) (x := ⟨x, subset_adjoin rfl⟩) (mt Subtype.ext_iff.mp h0)
  rwa [← mul_left_cancel₀ h0 ((Subtype.ext_iff.mp h1).trans (mul_inv_cancel₀ h0).symm)]

中文:
定理 是整.inv_mem_adjoin
  条件: (int : 是整 R x)
  结论: x⁻¹ in R[x]
  证明: by
  obtain rfl | h0 := eq_or_ne x 0
  · rw [inv_zero]; exact Subalgebra.zero_mem _
  have : FiniteDimensional R (R[x]) := .of_fg int.fg_adjoin_singleton
  obtain ⟨⟨y, hy⟩, h1⟩ := FiniteDimensional.exists_mul_eq_one R
    (K := R[x]) (x := ⟨x, subset_adjoin rfl⟩) (mt Subtype.ext_iff.mp h0)
  rwa [← mul_left_cancel₀ h0 ((Subtype.ext_iff.mp h1).trans (mul_inv_cancel₀ h0).symm)]

Depends on / 依赖: FiniteDimensional, FiniteDimensional.exists_mul_eq_one, Subalgebra, Subalgebra.zero_mem, Subtype, Subtype.ext_iff.mp, eq_or_ne, exists_mul_eq_one, ext_iff, fg_adjoin_singleton, int.fg_adjoin_singleton, inv_zero, of_fg, subset_adjoin, zero_mem
-/
theorem IsIntegral.inv_mem_adjoin (int : IsIntegral R x) : x⁻¹ in R[x] := by
  obtain rfl | h0 := eq_or_ne x 0
  · rw [inv_zero]; exact Subalgebra.zero_mem _
  have : FiniteDimensional R (R[x]) := .of_fg int.fg_adjoin_singleton
  obtain ⟨⟨y, hy⟩, h1⟩ := FiniteDimensional.exists_mul_eq_one R
    (K := R[x]) (x := ⟨x, subset_adjoin rfl⟩) (mt Subtype.ext_iff.mp h0)
  rwa [← mul_left_cancel₀ h0 ((Subtype.ext_iff.mp h1).trans (mul_inv_cancel₀ h0).symm)]

/--
theorem `IsIntegral.inv_mem` / 定理 `IsIntegral.inv_mem`

English:
theorem IsIntegral.inv_mem
  given: (int : IsIntegral R x) (hx : x in A)
  statement: x⁻¹ in A
  proof: adjoin_le (Set.singleton_subset_iff.mpr hx) int.inv_mem_adjoin

中文:
定理 是整.inv_mem
  条件: (int : 是整 R x) (hx : x in A)
  结论: x⁻¹ in A
  证明: adjoin_le (Set.singleton_subset_iff.mpr hx) int.inv_mem_adjoin

Depends on / 依赖: Set.singleton_subset_iff.mpr, adjoin_le, int.inv_mem_adjoin, inv_mem_adjoin, singleton_subset_iff
-/
theorem IsIntegral.inv_mem (int : IsIntegral R x) (hx : x in A) : x⁻¹ in A :=
  adjoin_le (Set.singleton_subset_iff.mpr hx) int.inv_mem_adjoin

/--
theorem `Algebra.IsIntegral.inv_mem` / 定理 `Algebra.IsIntegral.inv_mem`

English:
theorem Algebra.IsIntegral.inv_mem
  given: [Algebra.IsIntegral R A] (hx : x in A)
  statement: x⁻¹ in A
  proof: ((isIntegral_algHom_iff A.val Subtype.val_injective).mpr <|
    Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : A)).inv_mem hx

中文:
定理 代数.是整.inv_mem
  条件: [代数.是整 R A] (hx : x in A)
  结论: x⁻¹ in A
  证明: ((isIntegral_algHom_iff A.val Subtype.val_injective).mpr <|
    Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : A)).inv_mem hx

Depends on / 依赖: A.val, Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, Subtype, Subtype.val_injective, inv_mem, isIntegral, isIntegral_algHom_iff, val_injective
-/
theorem Algebra.IsIntegral.inv_mem [Algebra.IsIntegral R A] (hx : x in A) : x⁻¹ in A :=
  ((isIntegral_algHom_iff A.val Subtype.val_injective).mpr <|
    Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : A)).inv_mem hx

/--
theorem `IsIntegral.inv` / 定理 `IsIntegral.inv`

English:
theorem IsIntegral.inv
  given: (int : IsIntegral R x)
  statement: IsIntegral R x⁻¹
  proof: .of_mem_of_fg _ int.fg_adjoin_singleton _ int.inv_mem_adjoin

中文:
定理 是整.inv
  条件: (int : 是整 R x)
  结论: 是整 R x⁻¹
  证明: .of_mem_of_fg _ int.fg_adjoin_singleton _ int.inv_mem_adjoin

Depends on / 依赖: fg_adjoin_singleton, int.fg_adjoin_singleton, int.inv_mem_adjoin, inv_mem_adjoin, of_mem_of_fg
-/
theorem IsIntegral.inv (int : IsIntegral R x) : IsIntegral R x⁻¹ :=
  .of_mem_of_fg _ int.fg_adjoin_singleton _ int.inv_mem_adjoin

/--
theorem `IsIntegral.mem_of_inv_mem` / 定理 `IsIntegral.mem_of_inv_mem`

English:
theorem IsIntegral.mem_of_inv_mem
  given: (int : IsIntegral R x) (inv_mem : x⁻¹ in A)
  statement: x in A
  proof: by
  rw [← inv_inv x]; exact int.inv.inv_mem inv_mem

中文:
定理 是整.mem_of_inv_mem
  条件: (int : 是整 R x) (inv_mem : x⁻¹ in A)
  结论: x in A
  证明: by
  rw [← inv_inv x]; exact int.inv.inv_mem inv_mem

Depends on / 依赖: int.inv.inv_mem, inv_inv, inv_mem
-/
theorem IsIntegral.mem_of_inv_mem (int : IsIntegral R x) (inv_mem : x⁻¹ in A) : x in A := by
  rw [← inv_inv x]; exact int.inv.inv_mem inv_mem

end inv

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] {f : R ->+* S}

/--
theorem `Algebra.IsIntegral.finite` / 定理 `Algebra.IsIntegral.finite`

English:
theorem Algebra.IsIntegral.finite
  given: [Algebra.IsIntegral R A] [h' : Algebra.FiniteType R A]
  proof: have ⟨s, hs⟩ := h'
  ⟨by apply hs ▸ fg_adjoin_of_finite s.finite_toSet fun x _ => Algebra.IsIntegral.isIntegral x⟩

中文:
定理 代数.是整.finite
  条件: [代数.是整 R A] [h' : 代数.有限型 R A]
  证明: have ⟨s, hs⟩ := h'
  ⟨by apply hs ▸ fg_adjoin_of_finite s.finite_toSet fun x _ => Algebra.IsIntegral.isIntegral x⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, fg_adjoin_of_finite, finite_toSet, isIntegral, s.finite_toSet
-/
theorem Algebra.IsIntegral.finite [Algebra.IsIntegral R A] [h' : Algebra.FiniteType R A] :
    Module.Finite R A :=
  have ⟨s, hs⟩ := h'
  ⟨by apply hs ▸ fg_adjoin_of_finite s.finite_toSet fun x _ => Algebra.IsIntegral.isIntegral x⟩

/--
theorem `Algebra.finite_iff_isIntegral_and_finiteType` / 定理 `Algebra.finite_iff_isIntegral_and_finiteType`

English:
theorem Algebra.finite_iff_isIntegral_and_finiteType
  proof: ⟨fun _ => ⟨⟨.of_finite R⟩, inferInstance⟩, fun ⟨h, _⟩ => h.finite⟩

中文:
定理 代数.finite_iff_is整数egral_and_finiteType
  证明: ⟨fun _ => ⟨⟨.of_finite R⟩, inferInstance⟩, fun ⟨h, _⟩ => h.finite⟩

Depends on / 依赖: finite, h.finite, of_finite
-/
theorem Algebra.finite_iff_isIntegral_and_finiteType :
    Module.Finite R A ↔ Algebra.IsIntegral R A ∧ Algebra.FiniteType R A :=
  ⟨fun _ => ⟨⟨.of_finite R⟩, inferInstance⟩, fun ⟨h, _⟩ => h.finite⟩

/--
theorem `RingHom.IsIntegral.to_finite` / 定理 `RingHom.IsIntegral.to_finite`

English:
theorem RingHom.IsIntegral.to_finite
  given: (h : f.IsIntegral) (h' : f.FiniteType)
  statement: f.Finite
  proof: let _ := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨h⟩
  Algebra.IsIntegral.finite (h' := h')

alias RingHom.Finite.of_isIntegral_of_finiteType := RingHom.IsIntegral.to_finite

中文:
定理 环态射.是整.to_finite
  条件: (h : f.是整) (h' : f.有限型)
  结论: f.有限
  证明: let _ := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨h⟩
  Algebra.IsIntegral.finite (h' := h')

alias RingHom.Finite.of_isIntegral_of_finiteType := RingHom.IsIntegral.to_finite

Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.IsIntegral.finite, IsIntegral, f.toAlgebra, finite, toAlgebra
-/
theorem RingHom.IsIntegral.to_finite (h : f.IsIntegral) (h' : f.FiniteType) : f.Finite :=
  let _ := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨h⟩
  Algebra.IsIntegral.finite (h' := h')

alias RingHom.Finite.of_isIntegral_of_finiteType := RingHom.IsIntegral.to_finite

/--
theorem `RingHom.finite_iff_isIntegral_and_finiteType` / 定理 `RingHom.finite_iff_isIntegral_and_finiteType`

English:
theorem RingHom.finite_iff_isIntegral_and_finiteType
  statement: f.Finite ↔ f.IsIntegral ∧ f.FiniteType
  proof: ⟨fun h => ⟨h.to_isIntegral, h.to_finiteType⟩, fun ⟨h, h'⟩ => h.to_finite h'⟩

中文:
定理 环态射.finite_iff_is整数egral_and_finiteType
  结论: f.有限 ↔ f.是整 ∧ f.有限型
  证明: ⟨fun h => ⟨h.to_isIntegral, h.to_finiteType⟩, fun ⟨h, h'⟩ => h.to_finite h'⟩

Depends on / 依赖: h.to_finite, h.to_finiteType, h.to_isIntegral, to_finite, to_finiteType, to_isIntegral
-/
theorem RingHom.finite_iff_isIntegral_and_finiteType : f.Finite ↔ f.IsIntegral ∧ f.FiniteType :=
  ⟨fun h => ⟨h.to_isIntegral, h.to_finiteType⟩, fun ⟨h, h'⟩ => h.to_finite h'⟩

variable (f : R ->+* S) (R A)

/--
theorem `mem_integralClosure_iff_mem_fg` / 定理 `mem_integralClosure_iff_mem_fg`

English:
theorem mem_integralClosure_iff_mem_fg
  given: {r : A}
  proof: ⟨fun hr =>
    ⟨Algebra.adjoin R {r}, hr.fg_adjoin_singleton, Algebra.subset_adjoin rfl⟩,
    fun ⟨M, Hf, hrM⟩ => .of_mem_of_fg M Hf _ hrM⟩

中文:
定理 mem_integralClosure_iff_mem_fg
  条件: {r : A}
  证明: ⟨fun hr =>
    ⟨Algebra.adjoin R {r}, hr.fg_adjoin_singleton, Algebra.subset_adjoin rfl⟩,
    fun ⟨M, Hf, hrM⟩ => .of_mem_of_fg M Hf _ hrM⟩

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, adjoin, fg_adjoin_singleton, hr.fg_adjoin_singleton, of_mem_of_fg, subset_adjoin
-/
theorem mem_integralClosure_iff_mem_fg {r : A} :
    r in integralClosure R A ↔ exists M : Subalgebra R A, M.toSubmodule.FG ∧ r in M :=
  ⟨fun hr =>
    ⟨Algebra.adjoin R {r}, hr.fg_adjoin_singleton, Algebra.subset_adjoin rfl⟩,
    fun ⟨M, Hf, hrM⟩ => .of_mem_of_fg M Hf _ hrM⟩

variable {R A}

/--
theorem `adjoin_le_integralClosure` / 定理 `adjoin_le_integralClosure`

English:
theorem adjoin_le_integralClosure
  given: {x : A} (hx : IsIntegral R x)
  proof: by
  rw [Algebra.adjoin_le_iff]
  simp only [SetLike.mem_coe, Set.singleton_subset_iff]
  exact hx

中文:
定理 adjoin_le_integralClosure
  条件: {x : A} (hx : 是整 R x)
  证明: by
  rw [Algebra.adjoin_le_iff]
  simp only [SetLike.mem_coe, Set.singleton_subset_iff]
  exact hx

Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike, SetLike.mem_coe, adjoin_le_iff, mem_coe, singleton_subset_iff
-/
theorem adjoin_le_integralClosure {x : A} (hx : IsIntegral R x) :
    Algebra.adjoin R {x} <= integralClosure R A := by
  rw [Algebra.adjoin_le_iff]
  simp only [SetLike.mem_coe, Set.singleton_subset_iff]
  exact hx

/--
theorem `le_integralClosure_iff_isIntegral` / 定理 `le_integralClosure_iff_isIntegral`

English:
theorem le_integralClosure_iff_isIntegral
  given: {S : Subalgebra R A}
  proof: SetLike.forall.symm.trans
    (forall_congr' fun x =>
      show IsIntegral R (algebraMap S A x) ↔ IsIntegral R x from
        isIntegral_algebraMap_iff Subtype.coe_injective).trans
      Algebra.isIntegral_def.symm

中文:
定理 le_integralClosure_iff_is整数egral
  条件: {S : 子代数 R A}
  证明: SetLike.forall.symm.trans
    (forall_congr' fun x =>
      show IsIntegral R (algebraMap S A x) ↔ IsIntegral R x from
        isIntegral_algebraMap_iff Subtype.coe_injective).trans
      Algebra.isIntegral_def.symm

Depends on / 依赖: Algebra, Algebra.isIntegral_def.symm, IsIntegral, SetLike, SetLike.forall.symm.trans, Subtype, Subtype.coe_injective, algebraMap, coe_injective, forall_congr, isIntegral_algebraMap_iff, isIntegral_def
-/
theorem le_integralClosure_iff_isIntegral {S : Subalgebra R A} :
    S <= integralClosure R A ↔ Algebra.IsIntegral R S :=
SetLike.forall.symm.trans
    (forall_congr' fun x =>
      show IsIntegral R (algebraMap S A x) ↔ IsIntegral R x from
        isIntegral_algebraMap_iff Subtype.coe_injective).trans
      Algebra.isIntegral_def.symm

/--
theorem `Algebra.IsIntegral.adjoin` / 定理 `Algebra.IsIntegral.adjoin`

English:
theorem Algebra.IsIntegral.adjoin
  given: {S : Set A} (hS : forall x in S, IsIntegral R x)
  proof: le_integralClosure_iff_isIntegral.mp adjoin_le hS

中文:
定理 代数.是整.adjoin
  条件: {S : 集合 A} (hS : 对任意 x in S, 是整 R x)
  证明: le_integralClosure_iff_isIntegral.mp adjoin_le hS

Depends on / 依赖: adjoin_le, le_integralClosure_iff_isIntegral, le_integralClosure_iff_isIntegral.mp
-/
theorem Algebra.IsIntegral.adjoin {S : Set A} (hS : forall x in S, IsIntegral R x) :
    Algebra.IsIntegral R (adjoin R S) :=
le_integralClosure_iff_isIntegral.mp adjoin_le hS

/--
theorem `integralClosure_eq_top_iff` / 定理 `integralClosure_eq_top_iff`

English:
theorem integralClosure_eq_top_iff
  statement: integralClosure R A = ⊤ ↔ Algebra.IsIntegral R A
  proof: by
  rw [← top_le_iff]; rw [le_integralClosure_iff_isIntegral]; rw [(Subalgebra.topEquiv (R := R) (A := A)).isIntegral_iff] -- explicit arguments for speedup

中文:
定理 integralClosure_eq_top_iff
  结论: integralClosure R A = ⊤ ↔ 代数.是整 R A
  证明: by
  rw [← top_le_iff]; rw [le_integralClosure_iff_isIntegral]; rw [(Subalgebra.topEquiv (R := R) (A := A)).isIntegral_iff] -- explicit arguments for speedup

Depends on / 依赖: Subalgebra, Subalgebra.topEquiv, arguments, explicit, isIntegral_iff, le_integralClosure_iff_isIntegral, speedup, topEquiv, top_le_iff
-/
theorem integralClosure_eq_top_iff : integralClosure R A = ⊤ ↔ Algebra.IsIntegral R A := by
  rw [← top_le_iff]; rw [le_integralClosure_iff_isIntegral]; rw [(Subalgebra.topEquiv (R := R) (A := A)).isIntegral_iff] -- explicit arguments for speedup

/--
theorem `Algebra.isIntegral_sup` / 定理 `Algebra.isIntegral_sup`

English:
theorem Algebra.isIntegral_sup
  given: {S T : Subalgebra R A}
  proof: by
  simp_rw [← le_integralClosure_iff_isIntegral, sup_le_iff]

中文:
定理 代数.is整数egral_sup
  条件: {S T : 子代数 R A}
  证明: by
  simp_rw [← le_integralClosure_iff_isIntegral, sup_le_iff]

Depends on / 依赖: le_integralClosure_iff_isIntegral, simp_rw, sup_le_iff
-/
theorem Algebra.isIntegral_sup {S T : Subalgebra R A} :
    Algebra.IsIntegral R (S ⊔ T : Subalgebra R A) ↔
      Algebra.IsIntegral R S ∧ Algebra.IsIntegral R T := by
  simp_rw [← le_integralClosure_iff_isIntegral, sup_le_iff]

/--
theorem `Algebra.isIntegral_iSup` / 定理 `Algebra.isIntegral_iSup`

English:
theorem Algebra.isIntegral_iSup
  given: {ι} (S : ι -> Subalgebra R A)
  proof: by
  simp_rw [← le_integralClosure_iff_isIntegral, iSup_le_iff]

中文:
定理 代数.is整数egral_iSup
  条件: {ι} (S : ι -> 子代数 R A)
  证明: by
  simp_rw [← le_integralClosure_iff_isIntegral, iSup_le_iff]

Depends on / 依赖: iSup_le_iff, le_integralClosure_iff_isIntegral, simp_rw
-/
theorem Algebra.isIntegral_iSup {ι} (S : ι -> Subalgebra R A) :
    Algebra.IsIntegral R ↑(iSup S) ↔ forall i, Algebra.IsIntegral R (S i) := by
  simp_rw [← le_integralClosure_iff_isIntegral, iSup_le_iff]

/--
theorem `integralClosure_map_algEquiv` / 定理 `integralClosure_map_algEquiv`

English:
theorem integralClosure_map_algEquiv
  given: [Algebra R S] (f : A ≃ₐ[R] S)
  proof: by
  ext y
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.map f
  · intro hy
    use f.symm y, hy.map (f.symm : S ->ₐ[R] A)
    simp

中文:
定理 integralClosure_map_algEquiv
  条件: [代数 R S] (f : A ≃ₐ[R] S)
  证明: by
  ext y
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.map f
  · intro hy
    use f.symm y, hy.map (f.symm : S ->ₐ[R] A)
    simp

Depends on / 依赖: Subalgebra, Subalgebra.mem_map, f.symm, hx.map, hy.map, mem_map
-/
theorem integralClosure_map_algEquiv [Algebra R S] (f : A ≃ₐ[R] S) :
    (integralClosure R A).map (f : A ->ₐ[R] S) = integralClosure R S := by
  ext y
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.map f
  · intro hy
    use f.symm y, hy.map (f.symm : S ->ₐ[R] A)
    simp

/--
Definition of `AlgHom.mapIntegralClosure` / `AlgHom.mapIntegralClosure` 的定义

English:
definition AlgHom.mapIntegralClosure
  signature: [Algebra R S] (f : A ->ₐ[R] S)
  body: (f.domRestrict (integralClosure R A)).codRestrict (integralClosure R S) (fun ⟨_, h⟩ => h.map f)

@[simp]

中文:
定义 代数态射.map整数egralClosure
  签名: [代数 R S] (f : A ->ₐ[R] S)
  定义体: (f.domRestrict (integralClosure R A)).codRestrict (integralClosure R S) (fun ⟨_, h⟩ => h.map f)

@[simp]

Depends on / 依赖: codRestrict, domRestrict, f.domRestrict, h.map, integralClosure
-/
def AlgHom.mapIntegralClosure [Algebra R S] (f : A ->ₐ[R] S) :
    integralClosure R A ->ₐ[R] integralClosure R S :=
  (f.domRestrict (integralClosure R A)).codRestrict (integralClosure R S) (fun ⟨_, h⟩ => h.map f)

@[simp]
/--
theorem `AlgHom.coe_mapIntegralClosure` / 定理 `AlgHom.coe_mapIntegralClosure`

English:
theorem AlgHom.coe_mapIntegralClosure
  statement: [Algebra R S] (f : A ->ₐ[R] S)
  proof: rfl

中文:
定理 代数态射.coe_map整数egralClosure
  结论: [代数 R S] (f : A ->ₐ[R] S)
  证明: rfl
-/
theorem AlgHom.coe_mapIntegralClosure [Algebra R S] (f : A ->ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl

/--
Definition of `AlgEquiv.mapIntegralClosure` / `AlgEquiv.mapIntegralClosure` 的定义

English:
definition AlgEquiv.mapIntegralClosure
  signature: [Algebra R S] (f : A ≃ₐ[R] S)
  body: AlgEquiv.ofAlgHom (f : A ->ₐ[R] S).mapIntegralClosure (f.symm : S ->ₐ[R] A).mapIntegralClosure
    (AlgHom.ext fun _ => Subtype.ext (f.right_inv _))
    (AlgHom.ext fun _ => Subtype.ext (f.left_inv _))

@[simp]

中文:
定义 代数等价.map整数egralClosure
  签名: [代数 R S] (f : A ≃ₐ[R] S)
  定义体: AlgEquiv.ofAlgHom (f : A ->ₐ[R] S).mapIntegralClosure (f.symm : S ->ₐ[R] A).mapIntegralClosure
    (AlgHom.ext fun _ => Subtype.ext (f.right_inv _))
    (AlgHom.ext fun _ => Subtype.ext (f.left_inv _))

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, AlgHom, AlgHom.ext, Subtype, Subtype.ext, f.left_inv, f.right_inv, f.symm, left_inv, mapIntegralClosure, ofAlgHom, right_inv
-/
def AlgEquiv.mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S) :
    integralClosure R A ≃ₐ[R] integralClosure R S :=
  AlgEquiv.ofAlgHom (f : A ->ₐ[R] S).mapIntegralClosure (f.symm : S ->ₐ[R] A).mapIntegralClosure
    (AlgHom.ext fun _ => Subtype.ext (f.right_inv _))
    (AlgHom.ext fun _ => Subtype.ext (f.left_inv _))

@[simp]
/--
theorem `AlgEquiv.coe_mapIntegralClosure` / 定理 `AlgEquiv.coe_mapIntegralClosure`

English:
theorem AlgEquiv.coe_mapIntegralClosure
  statement: [Algebra R S] (f : A ≃ₐ[R] S)
  proof: rfl

中文:
定理 代数等价.coe_map整数egralClosure
  结论: [代数 R S] (f : A ≃ₐ[R] S)
  证明: rfl
-/
theorem AlgEquiv.coe_mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl

/--
theorem `integralClosure.isIntegral` / 定理 `integralClosure.isIntegral`

English:
theorem integralClosure.isIntegral
  given: (x : integralClosure R A)
  statement: IsIntegral R x
  proof: let ⟨p, hpm, hpx⟩ := x.2
  ⟨p, hpm,
Subtype.ext by
      rwa [← aeval_def, ← Subalgebra.val_apply, aeval_algHom_apply] at hpx⟩

中文:
定理 integralClosure.is整数egral
  条件: (x : integralClosure R A)
  结论: 是整 R x
  证明: let ⟨p, hpm, hpx⟩ := x.2
  ⟨p, hpm,
Subtype.ext by
      rwa [← aeval_def, ← Subalgebra.val_apply, aeval_algHom_apply] at hpx⟩

Depends on / 依赖: Subalgebra, Subalgebra.val_apply, Subtype, Subtype.ext, aeval_algHom_apply, aeval_def, val_apply
-/
theorem integralClosure.isIntegral (x : integralClosure R A) : IsIntegral R x :=
  let ⟨p, hpm, hpx⟩ := x.2
  ⟨p, hpm,
Subtype.ext by
      rwa [← aeval_def, ← Subalgebra.val_apply, aeval_algHom_apply] at hpx⟩

/--
Instance `integralClosure.AlgebraIsIntegral` / 实例 `integralClosure.AlgebraIsIntegral`

English:
instance integralClosure.AlgebraIsIntegral
  signature: : Algebra.IsIntegral R (integralClosure R A)
  body: ⟨integralClosure.isIntegral⟩

中文:
实例 integralClosure.AlgebraIs整数egral
  签名: : 代数.是整 R (integralClosure R A)
  定义体: ⟨integralClosure.isIntegral⟩

Depends on / 依赖: integralClosure, integralClosure.isIntegral, isIntegral
-/
instance integralClosure.AlgebraIsIntegral : Algebra.IsIntegral R (integralClosure R A) :=
  ⟨integralClosure.isIntegral⟩

/--
theorem `IsIntegral.of_mul_unit` / 定理 `IsIntegral.of_mul_unit`

English:
theorem IsIntegral.of_mul_unit
  statement: {x y : B} {r : R} (hr : algebraMap R B r * y = 1)
  proof: by
  obtain ⟨p, p_monic, hp⟩ := hx
  refine ⟨scaleRoots p r, (monic_scaleRoots_iff r).2 p_monic, ?_⟩
  convert! scaleRoots_aeval_eq_zero hp
  rw [Algebra.commutes] at hr ⊢
  rw [mul_assoc]; rw [hr]; rw [mul_one]; rfl

中文:
定理 是整.of_mul_unit
  结论: {x y : B} {r : R} (hr : algebraMap R B r * y = 1)
  证明: by
  obtain ⟨p, p_monic, hp⟩ := hx
  refine ⟨scaleRoots p r, (monic_scaleRoots_iff r).2 p_monic, ?_⟩
  convert! scaleRoots_aeval_eq_zero hp
  rw [Algebra.commutes] at hr ⊢
  rw [mul_assoc]; rw [hr]; rw [mul_one]; rfl

Depends on / 依赖: Algebra, Algebra.commutes, commutes, convert, monic_scaleRoots_iff, mul_assoc, mul_one, p_monic, scaleRoots, scaleRoots_aeval_eq_zero
-/
theorem IsIntegral.of_mul_unit {x y : B} {r : R} (hr : algebraMap R B r * y = 1)
    (hx : IsIntegral R (x * y)) : IsIntegral R x := by
  obtain ⟨p, p_monic, hp⟩ := hx
  refine ⟨scaleRoots p r, (monic_scaleRoots_iff r).2 p_monic, ?_⟩
  convert! scaleRoots_aeval_eq_zero hp
  rw [Algebra.commutes] at hr ⊢
  rw [mul_assoc]; rw [hr]; rw [mul_one]; rfl

/--
theorem `RingHom.IsIntegralElem.of_mul_unit` / 定理 `RingHom.IsIntegralElem.of_mul_unit`

English:
theorem RingHom.IsIntegralElem.of_mul_unit
  statement: (x y : S) (r : R) (hr : f r * y = 1)
  proof: letI : Algebra R S := f.toAlgebra
  IsIntegral.of_mul_unit hr hx

中文:
定理 环态射.Is整数egralElem.of_mul_unit
  结论: (x y : S) (r : R) (hr : f r * y = 1)
  证明: letI : Algebra R S := f.toAlgebra
  IsIntegral.of_mul_unit hr hx

Depends on / 依赖: Algebra, IsIntegral, IsIntegral.of_mul_unit, f.toAlgebra, of_mul_unit, toAlgebra
-/
theorem RingHom.IsIntegralElem.of_mul_unit (x y : S) (r : R) (hr : f r * y = 1)
    (hx : f.IsIntegralElem (x * y)) : f.IsIntegralElem x :=
  letI : Algebra R S := f.toAlgebra
  IsIntegral.of_mul_unit hr hx

/--
theorem `IsIntegral.of_mem_closure'` / 定理 `IsIntegral.of_mem_closure'`

English:
theorem IsIntegral.of_mem_closure'
  given: (G : Set A) (hG : forall x in G, IsIntegral R x)
  proof: fun _ hx =>
  Subring.closure_induction hG isIntegral_zero isIntegral_one (fun _ _ _ _ => IsIntegral.add)
    (fun _ _ => IsIntegral.neg) (fun _ _ _ _ => IsIntegral.mul) hx

中文:
定理 是整.of_mem_closure'
  条件: (G : 集合 A) (hG : 对任意 x in G, 是整 R x)
  证明: fun _ hx =>
  Subring.closure_induction hG isIntegral_zero isIntegral_one (fun _ _ _ _ => IsIntegral.add)
    (fun _ _ => IsIntegral.neg) (fun _ _ _ _ => IsIntegral.mul) hx
-/
theorem IsIntegral.of_mem_closure' (G : Set A) (hG : forall x in G, IsIntegral R x) :
    forall x in Subring.closure G, IsIntegral R x := fun _ hx =>
  Subring.closure_induction hG isIntegral_zero isIntegral_one (fun _ _ _ _ => IsIntegral.add)
    (fun _ _ => IsIntegral.neg) (fun _ _ _ _ => IsIntegral.mul) hx

/--
theorem `IsIntegral.of_mem_closure''` / 定理 `IsIntegral.of_mem_closure''`

English:
theorem IsIntegral.of_mem_closure''
  statement: {S : Type*} [CommRing S] {f : R ->+* S} (G : Set S)
  proof: fun x hx =>
  @IsIntegral.of_mem_closure' R S _ _ f.toAlgebra G hG x hx

中文:
定理 是整.of_mem_closure''
  结论: {S : 类型} [交换环 S] {f : R ->+* S} (G : 集合 S)
  证明: fun x hx =>
  @IsIntegral.of_mem_closure' R S _ _ f.toAlgebra G hG x hx
-/
theorem IsIntegral.of_mem_closure'' {S : Type*} [CommRing S] {f : R ->+* S} (G : Set S)
    (hG : forall x in G, f.IsIntegralElem x) : forall x in Subring.closure G, f.IsIntegralElem x := fun x hx =>
  @IsIntegral.of_mem_closure' R S _ _ f.toAlgebra G hG x hx

/--
theorem `IsIntegral.pow` / 定理 `IsIntegral.pow`

English:
theorem IsIntegral.pow
  given: {x : B} (h : IsIntegral R x) (n : Nat)
  statement: IsIntegral R (x ^ n)
  proof: .of_mem_of_fg _ h.fg_adjoin_singleton _
    Subalgebra.pow_mem _ (by exact Algebra.subset_adjoin rfl) _

中文:
定理 是整.pow
  条件: {x : B} (h : 是整 R x) (n : 自然数)
  结论: 是整 R (x ^ n)
  证明: .of_mem_of_fg _ h.fg_adjoin_singleton _
    Subalgebra.pow_mem _ (by exact Algebra.subset_adjoin rfl) _

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Subalgebra, Subalgebra.pow_mem, fg_adjoin_singleton, h.fg_adjoin_singleton, of_mem_of_fg, pow_mem, subset_adjoin
-/
theorem IsIntegral.pow {x : B} (h : IsIntegral R x) (n : Nat) : IsIntegral R (x ^ n) :=
.of_mem_of_fg _ h.fg_adjoin_singleton _
    Subalgebra.pow_mem _ (by exact Algebra.subset_adjoin rfl) _

/--
theorem `IsIntegral.nsmul` / 定理 `IsIntegral.nsmul`

English:
theorem IsIntegral.nsmul
  given: {x : B} (h : IsIntegral R x) (n : Nat)
  statement: IsIntegral R (n • x)
  proof: h.smul n

中文:
定理 是整.nsmul
  条件: {x : B} (h : 是整 R x) (n : 自然数)
  结论: 是整 R (n • x)
  证明: h.smul n

Depends on / 依赖: h.smul
-/
theorem IsIntegral.nsmul {x : B} (h : IsIntegral R x) (n : Nat) : IsIntegral R (n • x) :=
  h.smul n

/--
theorem `IsIntegral.zsmul` / 定理 `IsIntegral.zsmul`

English:
theorem IsIntegral.zsmul
  given: {x : B} (h : IsIntegral R x) (n : Int)
  statement: IsIntegral R (n • x)
  proof: h.smul n

中文:
定理 是整.zsmul
  条件: {x : B} (h : 是整 R x) (n : 整数)
  结论: 是整 R (n • x)
  证明: h.smul n

Depends on / 依赖: h.smul
-/
theorem IsIntegral.zsmul {x : B} (h : IsIntegral R x) (n : Int) : IsIntegral R (n • x) :=
  h.smul n

/--
theorem `IsIntegral.multiset_prod` / 定理 `IsIntegral.multiset_prod`

English:
theorem IsIntegral.multiset_prod
  given: {s : Multiset A} (h : forall x in s, IsIntegral R x)
  proof: (integralClosure R A).multiset_prod_mem h

中文:
定理 是整.multiset_prod
  条件: {s : Multiset A} (h : 对任意 x in s, 是整 R x)
  证明: (integralClosure R A).multiset_prod_mem h

Depends on / 依赖: integralClosure, multiset_prod_mem
-/
theorem IsIntegral.multiset_prod {s : Multiset A} (h : forall x in s, IsIntegral R x) :
    IsIntegral R s.prod :=
  (integralClosure R A).multiset_prod_mem h

/--
theorem `IsIntegral.multiset_sum` / 定理 `IsIntegral.multiset_sum`

English:
theorem IsIntegral.multiset_sum
  given: {s : Multiset A} (h : forall x in s, IsIntegral R x)
  proof: (integralClosure R A).multiset_sum_mem h

中文:
定理 是整.multiset_sum
  条件: {s : Multiset A} (h : 对任意 x in s, 是整 R x)
  证明: (integralClosure R A).multiset_sum_mem h

Depends on / 依赖: integralClosure, multiset_sum_mem
-/
theorem IsIntegral.multiset_sum {s : Multiset A} (h : forall x in s, IsIntegral R x) :
    IsIntegral R s.sum :=
  (integralClosure R A).multiset_sum_mem h

/--
theorem `IsIntegral.prod` / 定理 `IsIntegral.prod`

English:
theorem IsIntegral.prod
  given: {α : Type*} {s : Finset α} (f : α -> A) (h : forall x in s, IsIntegral R (f x))
  proof: (integralClosure R A).prod_mem h

中文:
定理 是整.乘积
  条件: {α : 类型} {s : 有限集 α} (f : α -> A) (h : 对任意 x in s, 是整 R (f x))
  证明: (integralClosure R A).prod_mem h

Depends on / 依赖: integralClosure, prod_mem
-/
theorem IsIntegral.prod {α : Type*} {s : Finset α} (f : α -> A) (h : forall x in s, IsIntegral R (f x)) :
    IsIntegral R (∏ x in s, f x) :=
  (integralClosure R A).prod_mem h

/--
theorem `IsIntegral.sum` / 定理 `IsIntegral.sum`

English:
theorem IsIntegral.sum
  given: {α : Type*} {s : Finset α} (f : α -> A) (h : forall x in s, IsIntegral R (f x))
  proof: (integralClosure R A).sum_mem h

中文:
定理 是整.求和
  条件: {α : 类型} {s : 有限集 α} (f : α -> A) (h : 对任意 x in s, 是整 R (f x))
  证明: (integralClosure R A).sum_mem h

Depends on / 依赖: integralClosure, sum_mem
-/
theorem IsIntegral.sum {α : Type*} {s : Finset α} (f : α -> A) (h : forall x in s, IsIntegral R (f x)) :
    IsIntegral R (∑ x in s, f x) :=
  (integralClosure R A).sum_mem h

/--
theorem `IsIntegral.det` / 定理 `IsIntegral.det`

English:
theorem IsIntegral.det
  statement: {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n A}
  proof: by
  rw [Matrix.det_apply]
  exact IsIntegral.sum _ fun σ _hσ => (IsIntegral.prod _ fun i _hi => h _ _).zsmul _

@[simp]

中文:
定理 是整.det
  结论: {n : 类型} [有限类型 n] [DecidableEq n] {M : 矩阵 n n A}
  证明: by
  rw [Matrix.det_apply]
  exact IsIntegral.sum _ fun σ _hσ => (IsIntegral.prod _ fun i _hi => h _ _).zsmul _

@[simp]

Depends on / 依赖: IsIntegral, IsIntegral.prod, IsIntegral.sum, Matrix, Matrix.det_apply, det_apply
-/
theorem IsIntegral.det {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n A}
    (h : forall i j, IsIntegral R (M i j)) : IsIntegral R M.det := by
  rw [Matrix.det_apply]
  exact IsIntegral.sum _ fun σ _hσ => (IsIntegral.prod _ fun i _hi => h _ _).zsmul _

@[simp]
/--
theorem `IsIntegral.pow_iff` / 定理 `IsIntegral.pow_iff`

English:
theorem IsIntegral.pow_iff
  given: {x : A} {n : Nat} (hn : 0 < n)
  statement: IsIntegral R (x ^ n) ↔ IsIntegral R x
  proof: ⟨IsIntegral.of_pow hn, fun hx => hx.pow n⟩

中文:
定理 是整.pow_iff
  条件: {x : A} {n : 自然数} (hn : 0 < n)
  结论: 是整 R (x ^ n) ↔ 是整 R x
  证明: ⟨IsIntegral.of_pow hn, fun hx => hx.pow n⟩

Depends on / 依赖: IsIntegral, IsIntegral.of_pow, hx.pow, of_pow
-/
theorem IsIntegral.pow_iff {x : A} {n : Nat} (hn : 0 < n) : IsIntegral R (x ^ n) ↔ IsIntegral R x :=
  ⟨IsIntegral.of_pow hn, fun hx => hx.pow n⟩

section Pushout

variable (R S A) [Algebra R S] [int : Algebra.IsIntegral R S]
variable (SA : Type*) [CommRing SA] [Algebra R SA] [Algebra S SA] [Algebra A SA]
  [IsScalarTower R S SA] [IsScalarTower R A SA]

/--
theorem `Algebra.IsPushout.isIntegral'` / 定理 `Algebra.IsPushout.isIntegral'`

English:
theorem Algebra.IsPushout.isIntegral'
  given: [IsPushout R A S SA]
  statement: Algebra.IsIntegral A SA
  proof: (equiv R A S SA).isIntegral_iff.mp inferInstance

中文:
定理 代数.是推出.is整数egral'
  条件: [是推出 R A S SA]
  结论: 代数.是整 A SA
  证明: (equiv R A S SA).isIntegral_iff.mp inferInstance

Depends on / 依赖: isIntegral_iff, isIntegral_iff.mp
-/
theorem Algebra.IsPushout.isIntegral' [IsPushout R A S SA] : Algebra.IsIntegral A SA :=
  (equiv R A S SA).isIntegral_iff.mp inferInstance

/--
theorem `Algebra.IsPushout.isIntegral` / 定理 `Algebra.IsPushout.isIntegral`

English:
theorem Algebra.IsPushout.isIntegral
  given: [h : IsPushout R S A SA]
  statement: Algebra.IsIntegral A SA
  proof: h.symm.isIntegral'

中文:
定理 代数.是推出.is整数egral
  条件: [h : 是推出 R S A SA]
  结论: 代数.是整 A SA
  证明: h.symm.isIntegral'

Depends on / 依赖: h.symm.isIntegral, isIntegral
-/
theorem Algebra.IsPushout.isIntegral [h : IsPushout R S A SA] : Algebra.IsIntegral A SA :=
  h.symm.isIntegral'

attribute [local instance] Polynomial.algebra in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsIntegral R[X] S[X]
  body: Algebra.IsPushout.isIntegral R _ S _

中文:
实例 :
  签名: 代数.是整 R[X] S[X]
  定义体: Algebra.IsPushout.isIntegral R _ S _

Depends on / 依赖: Algebra, Algebra.IsPushout.isIntegral, IsPushout, isIntegral
-/
instance : Algebra.IsIntegral R[X] S[X] := Algebra.IsPushout.isIntegral R _ S _

attribute [local instance] MvPolynomial.algebraMvPolynomial in
instance {σ} : Algebra.IsIntegral (MvPolynomial σ R) (MvPolynomial σ S) :=
  Algebra.IsPushout.isIntegral R _ S _

end Pushout

section

variable (p : R[X]) (x : S)

/--
theorem `RingHom.isIntegralElem_leadingCoeff_mul` / 定理 `RingHom.isIntegralElem_leadingCoeff_mul`

English:
theorem RingHom.isIntegralElem_leadingCoeff_mul
  given: (h : p.eval₂ f x = 0)
  proof: by
  by_cases h' : 1 <= p.natDegree
  · use integralNormalization p
    have : p != 0 := fun h'' => by
      rw [h'']; rw [natDegree_zero] at h'
      exact Nat.not_succ_le_zero 0 h'
    use monic_integralNormalization this
    rw [integralNormalization_eval₂_leadingCoeff_mul h' f x]; rw [h]; rw [mul_zero]
  · by_cases hp : p.map f = 0
    · apply_fun fun q => coeff q p.natDegree at hp
      rw [coeff_map]; rw [coeff_zero]; rw [coeff_natDegree] at hp
      rw [hp]; rw [zero_mul]
      exact f.isIntegralElem_zero
    · rw [Nat.one_le_iff_ne_zero, Classical.not_not] at h'
      rw [eq_C_of_natDegree_eq_zero h']; rw [eval₂_C] at h
      suffices p.map f = 0 by exact (hp this).elim
      rw [eq_C_of_natDegree_eq_zero h']; rw [map_C]; rw [h]; rw [C_eq_zero]

中文:
定理 环态射.is整数egralElem_leadingCoeff_mul
  条件: (h : p.eval₂ f x = 0)
  证明: by
  by_cases h' : 1 <= p.natDegree
  · use integralNormalization p
    have : p != 0 := fun h'' => by
      rw [h'']; rw [natDegree_zero] at h'
      exact Nat.not_succ_le_zero 0 h'
    use monic_integralNormalization this
    rw [integralNormalization_eval₂_leadingCoeff_mul h' f x]; rw [h]; rw [mul_zero]
  · by_cases hp : p.map f = 0
    · apply_fun fun q => coeff q p.natDegree at hp
      rw [coeff_map]; rw [coeff_zero]; rw [coeff_natDegree] at hp
      rw [hp]; rw [zero_mul]
      exact f.isIntegralElem_zero
    · rw [Nat.one_le_iff_ne_zero, Classical.not_not] at h'
      rw [eq_C_of_natDegree_eq_zero h']; rw [eval₂_C] at h
      suffices p.map f = 0 by exact (hp this).elim
      rw [eq_C_of_natDegree_eq_zero h']; rw [map_C]; rw [h]; rw [C_eq_zero]

Depends on / 依赖: Nat.not_succ_le_zero, Nat.one_le_iff_ne_zero, apply_fun, coeff_map, coeff_natDegree, coeff_zero, f.isIntegralElem_zero, integralNormalization, isIntegralElem_zero, monic_integralNormalization, mul_zero, natDegree, natDegree_zero, not_succ_le_zero, one_le_iff_ne_zero, p.map, p.natDegree, zero_mul
-/
theorem RingHom.isIntegralElem_leadingCoeff_mul (h : p.eval₂ f x = 0) :
    f.IsIntegralElem (f p.leadingCoeff * x) := by
  by_cases h' : 1 <= p.natDegree
  · use integralNormalization p
    have : p != 0 := fun h'' => by
      rw [h'']; rw [natDegree_zero] at h'
      exact Nat.not_succ_le_zero 0 h'
    use monic_integralNormalization this
    rw [integralNormalization_eval₂_leadingCoeff_mul h' f x]; rw [h]; rw [mul_zero]
  · by_cases hp : p.map f = 0
    · apply_fun fun q => coeff q p.natDegree at hp
      rw [coeff_map]; rw [coeff_zero]; rw [coeff_natDegree] at hp
      rw [hp]; rw [zero_mul]
      exact f.isIntegralElem_zero
    · rw [Nat.one_le_iff_ne_zero, Classical.not_not] at h'
      rw [eq_C_of_natDegree_eq_zero h']; rw [eval₂_C] at h
      suffices p.map f = 0 by exact (hp this).elim
      rw [eq_C_of_natDegree_eq_zero h']; rw [map_C]; rw [h]; rw [C_eq_zero]

/--
theorem `isIntegral_leadingCoeff_smul` / 定理 `isIntegral_leadingCoeff_smul`

English:
theorem isIntegral_leadingCoeff_smul
  given: [Algebra R S] (h : aeval x p = 0)
  proof: by
  rw [aeval_def] at h
  rw [Algebra.smul_def]
  exact (algebraMap R S).isIntegralElem_leadingCoeff_mul p x h

中文:
定理 is整数egral_leadingCoeff_smul
  条件: [代数 R S] (h : aeval x p = 0)
  证明: by
  rw [aeval_def] at h
  rw [Algebra.smul_def]
  exact (algebraMap R S).isIntegralElem_leadingCoeff_mul p x h

Depends on / 依赖: Algebra, Algebra.smul_def, aeval_def, algebraMap, isIntegralElem_leadingCoeff_mul, smul_def
-/
theorem isIntegral_leadingCoeff_smul [Algebra R S] (h : aeval x p = 0) :
    IsIntegral R (p.leadingCoeff • x) := by
  rw [aeval_def] at h
  rw [Algebra.smul_def]
  exact (algebraMap R S).isIntegralElem_leadingCoeff_mul p x h

end

/--
lemma `Polynomial.Monic.quotient_isIntegralElem` / 引理 `Polynomial.Monic.quotient_isIntegralElem`

English:
lemma Polynomial.Monic.quotient_isIntegralElem
  statement: {g : S[X]} (mon : g.Monic) {I : Ideal S[X]}
  proof: by
  exact ⟨g, mon, by
  rw [← (Ideal.Quotient.eq_zero_iff_mem.mpr h)]; rw [eval₂_eq_sum_range]
  nth_rw 3 [(as_sum_range_C_mul_X_pow g)]
  simp only [map_sum, algebraMap_eq, RingHom.coe_comp, Function.comp_apply, map_mul, map_pow]⟩

中文:
引理 多项式.Monic.quotient_is整数egralElem
  结论: {g : S[X]} (mon : g.Monic) {I : 理想 S[X]}
  证明: by
  exact ⟨g, mon, by
  rw [← (Ideal.Quotient.eq_zero_iff_mem.mpr h)]; rw [eval₂_eq_sum_range]
  nth_rw 3 [(as_sum_range_C_mul_X_pow g)]
  simp only [map_sum, algebraMap_eq, RingHom.coe_comp, Function.comp_apply, map_mul, map_pow]⟩

Depends on / 依赖: Function, Function.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr, Quotient, RingHom, RingHom.coe_comp, algebraMap_eq, as_sum_range_C_mul_X_pow, coe_comp, comp_apply, eq_zero_iff_mem, map_mul, map_pow, map_sum, nth_rw
-/
lemma Polynomial.Monic.quotient_isIntegralElem {g : S[X]} (mon : g.Monic) {I : Ideal S[X]}
    (h : g in I) :
    ((Ideal.Quotient.mk I).comp (algebraMap S S[X])).IsIntegralElem (Ideal.Quotient.mk I X) := by
  exact ⟨g, mon, by
  rw [← (Ideal.Quotient.eq_zero_iff_mem.mpr h)]; rw [eval₂_eq_sum_range]
  nth_rw 3 [(as_sum_range_C_mul_X_pow g)]
  simp only [map_sum, algebraMap_eq, RingHom.coe_comp, Function.comp_apply, map_mul, map_pow]⟩

/--
lemma `Polynomial.Monic.quotient_isIntegral` / 引理 `Polynomial.Monic.quotient_isIntegral`

English:
lemma Polynomial.Monic.quotient_isIntegral
  given: {g : S[X]} (mon : g.Monic) {I : Ideal S[X]} (h : g in I)
  proof: by
  have eq_top : Algebra.adjoin S {(Ideal.Quotient.mkₐ S I) X} = ⊤ := by
    ext g
    constructor
    · simp only [Algebra.mem_top, implies_true]
    · intro _
      obtain ⟨g', hg⟩ := Ideal.Quotient.mkₐ_surjective S I g
      have : g = (Polynomial.aeval ((Ideal.Quotient.mkₐ S I) X)) g' := by
        nth_rw 1 [← hg, aeval_eq_sum_range' (lt_add_one _),
          as_sum_range_C_mul_X_pow g', map_sum]
        simp only [Polynomial.C_mul', ← map_pow, map_smul]
      exact this ▸ (aeval_mem_adjoin_singleton S ((Ideal.Quotient.mk I) Polynomial.X))
  exact fun a => (eq_top ▸ adjoin_le_integralClosure <| mon.quotient_isIntegralElem h)
    Algebra.mem_top

中文:
引理 多项式.Monic.quotient_is整数egral
  条件: {g : S[X]} (mon : g.Monic) {I : 理想 S[X]} (h : g in I)
  证明: by
  have eq_top : Algebra.adjoin S {(Ideal.Quotient.mkₐ S I) X} = ⊤ := by
    ext g
    constructor
    · simp only [Algebra.mem_top, implies_true]
    · intro _
      obtain ⟨g', hg⟩ := Ideal.Quotient.mkₐ_surjective S I g
      have : g = (Polynomial.aeval ((Ideal.Quotient.mkₐ S I) X)) g' := by
        nth_rw 1 [← hg, aeval_eq_sum_range' (lt_add_one _),
          as_sum_range_C_mul_X_pow g', map_sum]
        simp only [Polynomial.C_mul', ← map_pow, map_smul]
      exact this ▸ (aeval_mem_adjoin_singleton S ((Ideal.Quotient.mk I) Polynomial.X))
  exact fun a => (eq_top ▸ adjoin_le_integralClosure <| mon.quotient_isIntegralElem h)
    Algebra.mem_top

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.mem_top, C_mul, Ideal.Quotient.mk, Polynomial, Polynomial.C_mul, Polynomial.X, Polynomial.aeval, Quotient, adjoin, aeval_eq_sum_range, aeval_mem_adjoin_singleton, as_sum_range_C_mul_X_pow, eq_top, implies_true, lt_add_one, map_pow, map_smul, map_sum
-/
lemma Polynomial.Monic.quotient_isIntegral {g : S[X]} (mon : g.Monic) {I : Ideal S[X]} (h : g in I) :
    ((Ideal.Quotient.mkₐ S I).comp (Algebra.ofId S S[X])).IsIntegral := by
  have eq_top : Algebra.adjoin S {(Ideal.Quotient.mkₐ S I) X} = ⊤ := by
    ext g
    constructor
    · simp only [Algebra.mem_top, implies_true]
    · intro _
      obtain ⟨g', hg⟩ := Ideal.Quotient.mkₐ_surjective S I g
      have : g = (Polynomial.aeval ((Ideal.Quotient.mkₐ S I) X)) g' := by
        nth_rw 1 [← hg, aeval_eq_sum_range' (lt_add_one _),
          as_sum_range_C_mul_X_pow g', map_sum]
        simp only [Polynomial.C_mul', ← map_pow, map_smul]
      exact this ▸ (aeval_mem_adjoin_singleton S ((Ideal.Quotient.mk I) Polynomial.X))
  exact fun a => (eq_top ▸ adjoin_le_integralClosure <| mon.quotient_isIntegralElem h)
    Algebra.mem_top

end

section IsIntegralClosure

/--
Instance `integralClosure.isIntegralClosure` / 实例 `integralClosure.isIntegralClosure`

English:
instance integralClosure.isIntegralClosure
  signature: (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  body: Subtype.coe_injective
  isIntegral_iff {x} := ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨⟨_, h⟩, rfl⟩; exact h⟩

中文:
实例 integralClosure.is整数egralClosure
  签名: (R A : 类型) [交换环 R] [交换环 A] [代数 R A]
  定义体: Subtype.coe_injective
  isIntegral_iff {x} := ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨⟨_, h⟩, rfl⟩; exact h⟩

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
instance integralClosure.isIntegralClosure (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    IsIntegralClosure (integralClosure R A) R A where
  algebraMap_injective := Subtype.coe_injective
  isIntegral_iff {x} := ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨⟨_, h⟩, rfl⟩; exact h⟩

namespace IsIntegralClosure

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R B] [Algebra A B] [IsIntegralClosure A R B]
variable (R B)

/--
theorem `isIntegral` / 定理 `isIntegral`

English:
theorem isIntegral
  given: [Algebra R A] [IsScalarTower R A B] (x : A)
  statement: IsIntegral R x
  proof: (isIntegral_algebraMap_iff (algebraMap_injective A R B)).mp
    show IsIntegral R (algebraMap A B x) from isIntegral_iff.mpr ⟨x, rfl⟩

中文:
定理 is整数egral
  条件: [代数 R A] [标量塔 R A B] (x : A)
  结论: 是整 R x
  证明: (isIntegral_algebraMap_iff (algebraMap_injective A R B)).mp
    show IsIntegral R (algebraMap A B x) from isIntegral_iff.mpr ⟨x, rfl⟩
-/
protected theorem isIntegral [Algebra R A] [IsScalarTower R A B] (x : A) : IsIntegral R x :=
(isIntegral_algebraMap_iff (algebraMap_injective A R B)).mp
    show IsIntegral R (algebraMap A B x) from isIntegral_iff.mpr ⟨x, rfl⟩

/--
theorem `isIntegral_algebra` / 定理 `isIntegral_algebra`

English:
theorem isIntegral_algebra
  given: [Algebra R A] [IsScalarTower R A B]
  statement: Algebra.IsIntegral R A
  proof: ⟨fun x => IsIntegralClosure.isIntegral R B x⟩

中文:
定理 is整数egral_algebra
  条件: [代数 R A] [标量塔 R A B]
  结论: 代数.是整 R A
  证明: ⟨fun x => IsIntegralClosure.isIntegral R B x⟩

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral, isIntegral
-/
theorem isIntegral_algebra [Algebra R A] [IsScalarTower R A B] : Algebra.IsIntegral R A :=
  ⟨fun x => IsIntegralClosure.isIntegral R B x⟩

/--
lemma `isTorsionFree` / 引理 `isTorsionFree`

English:
lemma isTorsionFree
  given: [Module R A] [IsScalarTower R A B] [IsTorsionFree R B]
  statement: IsTorsionFree R A
  proof: by
  refine
    Function.Injective.moduleIsTorsionFree _ (IsIntegralClosure.algebraMap_injective A R B)
      fun _ _ => ?_
  simp only [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc]

中文:
引理 isTorsionFree
  条件: [模 R A] [标量塔 R A B] [是无挠 R B]
  结论: 是无挠 R A
  证明: by
  refine
    Function.Injective.moduleIsTorsionFree _ (IsIntegralClosure.algebraMap_injective A R B)
      fun _ _ => ?_
  simp only [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Function, Function.Injective.moduleIsTorsionFree, Injective, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsScalarTower, IsScalarTower.smul_assoc, algebraMap_eq_smul_one, algebraMap_injective, moduleIsTorsionFree, smul_assoc
-/
lemma isTorsionFree [Module R A] [IsScalarTower R A B] [IsTorsionFree R B] : IsTorsionFree R A := by
  refine
    Function.Injective.moduleIsTorsionFree _ (IsIntegralClosure.algebraMap_injective A R B)
      fun _ _ => ?_
  simp only [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc]

variable {R} (A) {B}

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (x : B) (hx : IsIntegral R x)
  body: Classical.choose (isIntegral_iff.mp hx)

@[simp]

中文:
定义 mk'
  签名: (x : B) (hx : 是整 R x)
  定义体: Classical.choose (isIntegral_iff.mp hx)

@[simp]

Depends on / 依赖: Classical, Classical.choose, isIntegral_iff, isIntegral_iff.mp
-/
noncomputable def mk' (x : B) (hx : IsIntegral R x) : A :=
  Classical.choose (isIntegral_iff.mp hx)

@[simp]
/--
theorem `algebraMap_mk'` / 定理 `algebraMap_mk'`

English:
theorem algebraMap_mk'
  given: (x : B) (hx : IsIntegral R x)
  statement: algebraMap A B (mk' A x hx) = x
  proof: Classical.choose_spec (isIntegral_iff.mp hx)

@[simp]

中文:
定理 algebraMap_mk'
  条件: (x : B) (hx : 是整 R x)
  结论: algebraMap A B (mk' A x hx) = x
  证明: Classical.choose_spec (isIntegral_iff.mp hx)

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, isIntegral_iff, isIntegral_iff.mp
-/
theorem algebraMap_mk' (x : B) (hx : IsIntegral R x) : algebraMap A B (mk' A x hx) = x :=
  Classical.choose_spec (isIntegral_iff.mp hx)

@[simp]
/--
theorem `mk'_one` / 定理 `mk'_one`

English:
theorem mk'_one
  given: (h : IsIntegral R (1 : B) := isIntegral_one)
  statement: mk' A 1 h = 1
  proof: algebraMap_injective A R B by rw [algebraMap_mk', map_one]

@[simp]

中文:
定理 mk'_one
  条件: (h : 是整 R (1 : B) := is整数egral_one)
  结论: mk' A 1 h = 1
  证明: algebraMap_injective A R B by rw [algebraMap_mk', map_one]

@[simp]
-/
theorem mk'_one (h : IsIntegral R (1 : B) := isIntegral_one) : mk' A 1 h = 1 :=
algebraMap_injective A R B by rw [algebraMap_mk', map_one]

@[simp]
/--
theorem `mk'_zero` / 定理 `mk'_zero`

English:
theorem mk'_zero
  given: (h : IsIntegral R (0 : B) := isIntegral_zero)
  statement: mk' A 0 h = 0
  proof: algebraMap_injective A R B by rw [algebraMap_mk', map_zero]

@[simp]

中文:
定理 mk'_zero
  条件: (h : 是整 R (0 : B) := is整数egral_zero)
  结论: mk' A 0 h = 0
  证明: algebraMap_injective A R B by rw [algebraMap_mk', map_zero]

@[simp]
-/
theorem mk'_zero (h : IsIntegral R (0 : B) := isIntegral_zero) : mk' A 0 h = 0 :=
algebraMap_injective A R B by rw [algebraMap_mk', map_zero]

@[simp]
/--
theorem `mk'_add` / 定理 `mk'_add`

English:
theorem mk'_add
  given: (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y)
  proof: algebraMap_injective A R B by simp only [algebraMap_mk', map_add]

@[simp]

中文:
定理 mk'_add
  条件: (x y : B) (hx : 是整 R x) (hy : 是整 R y)
  证明: algebraMap_injective A R B by simp only [algebraMap_mk', map_add]

@[simp]
-/
theorem mk'_add (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x + y) (hx.add hy) = mk' A x hx + mk' A y hy :=
algebraMap_injective A R B by simp only [algebraMap_mk', map_add]

@[simp]
/--
theorem `mk'_mul` / 定理 `mk'_mul`

English:
theorem mk'_mul
  given: (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y)
  proof: algebraMap_injective A R B by simp only [algebraMap_mk', map_mul]

@[simp]

中文:
定理 mk'_mul
  条件: (x y : B) (hx : 是整 R x) (hy : 是整 R y)
  证明: algebraMap_injective A R B by simp only [algebraMap_mk', map_mul]

@[simp]
-/
theorem mk'_mul (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x * y) (hx.mul hy) = mk' A x hx * mk' A y hy :=
algebraMap_injective A R B by simp only [algebraMap_mk', map_mul]

@[simp]
/--
theorem `mk'_algebraMap` / 定理 `mk'_algebraMap`

English:
theorem mk'_algebraMap
  statement: [Algebra R A] [IsScalarTower R A B] (x : R)
  proof: algebraMap_injective A R B by rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply]

中文:
定理 mk'_algebraMap
  结论: [代数 R A] [标量塔 R A B] (x : R)
  证明: algebraMap_injective A R B by rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply]
-/
theorem mk'_algebraMap [Algebra R A] [IsScalarTower R A B] (x : R)
    (h : IsIntegral R (algebraMap R B x) := isIntegral_algebraMap) :
    IsIntegralClosure.mk' A (algebraMap R B x) h = algebraMap R A x :=
algebraMap_injective A R B by rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply]

/--
theorem `isField` / 定理 `isField`

English:
theorem isField
  given: [Algebra R A] [IsScalarTower R A B] [IsDomain A] (hR : IsField R)
  proof: have := IsIntegralClosure.isIntegral_algebra R (A := A) B
  isField_of_isIntegral_of_isField' hR

中文:
定理 isField
  条件: [代数 R A] [标量塔 R A B] [是整环 A] (hR : 是域 R)
  证明: have := IsIntegralClosure.isIntegral_algebra R (A := A) B
  isField_of_isIntegral_of_isField' hR

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_algebra, isField_of_isIntegral_of_isField, isIntegral_algebra
-/
theorem isField [Algebra R A] [IsScalarTower R A B] [IsDomain A] (hR : IsField R) :
    IsField A :=
  have := IsIntegralClosure.isIntegral_algebra R (A := A) B
  isField_of_isIntegral_of_isField' hR

/--
theorem `of_algEquiv` / 定理 `of_algEquiv`

English:
theorem of_algEquiv
  statement: {S : Type*} [CommRing S] [Algebra A S] [Algebra R S]
  proof: funext_iff.2 h ▸ f.injective.comp (IsIntegralClosure.algebraMap_injective A R B)
  isIntegral_iff {x} := by simp [← isIntegral_algEquiv f.symm,
    IsIntegralClosure.isIntegral_iff (A := A), h, ← f.symm.injective.eq_iff]

中文:
定理 of_algEquiv
  结论: {S : 类型} [交换环 S] [代数 A S] [代数 R S]
  证明: funext_iff.2 h ▸ f.injective.comp (IsIntegralClosure.algebraMap_injective A R B)
  isIntegral_iff {x} := by simp [← isIntegral_algEquiv f.symm,
    IsIntegralClosure.isIntegral_iff (A := A), h, ← f.symm.injective.eq_iff]

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isIntegral_iff, algebraMap_injective, eq_iff, f.injective.comp, f.symm, f.symm.injective.eq_iff, funext_iff, injective, isIntegral_algEquiv, isIntegral_iff
-/
theorem of_algEquiv {S : Type*} [CommRing S] [Algebra A S] [Algebra R S]
    (f : B ≃ₐ[R] S) (h : forall x, algebraMap A S x = f (algebraMap A B x)) :
    IsIntegralClosure A R S where
  algebraMap_injective :=
    funext_iff.2 h ▸ f.injective.comp (IsIntegralClosure.algebraMap_injective A R B)
  isIntegral_iff {x} := by simp [← isIntegral_algEquiv f.symm,
    IsIntegralClosure.isIntegral_iff (A := A), h, ← f.symm.injective.eq_iff]

section lift

variable (B) {S : Type*} [CommRing S] [Algebra R S]
-- split from above, since otherwise it does not synthesize `Semiring S`
variable [Algebra S B] [IsScalarTower R S B]
variable [Algebra R A] [IsScalarTower R A B] [isIntegral : Algebra.IsIntegral R S]
variable (R)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : S ->ₐ[R] A where
  body: mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))
  map_one' := by simp only [map_one, mk'_one]
  map_zero' := by simp only [map_zero, mk'_zero]
  map_add' x y := by simp_rw [← mk'_add, map_add]
  map_mul' x y := by simp_rw [← mk'_mul, map_mul]
  commutes' x := by simp_rw [← IsScalarTower.algebraMap_apply, mk'_algebraMap]

@[simp]

中文:
定义 lift
  签名: : S ->ₐ[R] A where
  定义体: mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))
  map_one' := by simp only [map_one, mk'_one]
  map_zero' := by simp only [map_zero, mk'_zero]
  map_add' x y := by simp_rw [← mk'_add, map_add]
  map_mul' x y := by simp_rw [← mk'_mul, map_mul]
  commutes' x := by simp_rw [← IsScalarTower.algebraMap_apply, mk'_algebraMap]

@[simp]

Depends on / 依赖: IsIntegral, IsIntegral.algebraMap, algebraMap
-/
noncomputable def lift : S ->ₐ[R] A where
  toFun x := mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))
  map_one' := by simp only [map_one, mk'_one]
  map_zero' := by simp only [map_zero, mk'_zero]
  map_add' x y := by simp_rw [← mk'_add, map_add]
  map_mul' x y := by simp_rw [← mk'_mul, map_mul]
  commutes' x := by simp_rw [← IsScalarTower.algebraMap_apply, mk'_algebraMap]

@[simp]
/--
theorem `algebraMap_lift` / 定理 `algebraMap_lift`

English:
theorem algebraMap_lift
  given: (x : S)
  statement: algebraMap A B (lift R A B x) = algebraMap S B x
  proof: algebraMap_mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))

中文:
定理 algebraMap_lift
  条件: (x : S)
  结论: algebraMap A B (lift R A B x) = algebraMap S B x
  证明: algebraMap_mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, IsIntegral.algebraMap, algebraMap, algebraMap_mk, isIntegral
-/
theorem algebraMap_lift (x : S) : algebraMap A B (lift R A B x) = algebraMap S B x :=
  algebraMap_mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))

end lift

section Equiv

variable (R B) (A' : Type*) [CommRing A']
variable [Algebra A' B] [IsIntegralClosure A' R B]
variable [Algebra R A] [Algebra R A'] [IsScalarTower R A B] [IsScalarTower R A' B]

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : A ≃ₐ[R] A'
  body: AlgEquiv.ofAlgHom
    (lift R A' B (isIntegral := isIntegral_algebra R B))
    (lift R A B (isIntegral := isIntegral_algebra R B))
    (by ext x; apply algebraMap_injective A' R B; simp)
    (by ext x; apply algebraMap_injective A R B; simp)

@[simp]

中文:
定义 equiv
  签名: : A ≃ₐ[R] A'
  定义体: AlgEquiv.ofAlgHom
    (lift R A' B (isIntegral := isIntegral_algebra R B))
    (lift R A B (isIntegral := isIntegral_algebra R B))
    (by ext x; apply algebraMap_injective A' R B; simp)
    (by ext x; apply algebraMap_injective A R B; simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, algebraMap_injective, isIntegral, isIntegral_algebra, ofAlgHom
-/
noncomputable def equiv : A ≃ₐ[R] A' :=
  AlgEquiv.ofAlgHom
    (lift R A' B (isIntegral := isIntegral_algebra R B))
    (lift R A B (isIntegral := isIntegral_algebra R B))
    (by ext x; apply algebraMap_injective A' R B; simp)
    (by ext x; apply algebraMap_injective A R B; simp)

@[simp]
/--
theorem `algebraMap_equiv` / 定理 `algebraMap_equiv`

English:
theorem algebraMap_equiv
  given: (x : A)
  statement: algebraMap A' B (equiv R A B A' x) = algebraMap A B x
  proof: algebraMap_lift R A' B (isIntegral := isIntegral_algebra R B) x

中文:
定理 algebraMap_equiv
  条件: (x : A)
  结论: algebraMap A' B (equiv R A B A' x) = algebraMap A B x
  证明: algebraMap_lift R A' B (isIntegral := isIntegral_algebra R B) x

Depends on / 依赖: algebraMap_lift, isIntegral, isIntegral_algebra
-/
theorem algebraMap_equiv (x : A) : algebraMap A' B (equiv R A B A' x) = algebraMap A B x :=
  algebraMap_lift R A' B (isIntegral := isIntegral_algebra R B) x

end Equiv

end IsIntegralClosure

end IsIntegralClosure

section Algebra

open Algebra

variable {R A B S T : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S] [CommRing T]
variable [Algebra A B] [Algebra R B] (f : R ->+* S) (g : S ->+* T)
variable [Algebra R A] [IsScalarTower R A B]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isIntegral_trans` / 定理 `isIntegral_trans`

English:
theorem isIntegral_trans
  given: [Algebra.IsIntegral R A] (x : B) (hx : IsIntegral A x)
  proof: by
  rcases hx with ⟨p, pmonic, hp⟩
  let S := adjoin R (p.coeffs : Set A)
have : Module.Finite R S := ⟨(Subalgebra.toSubmodule S).fg_top.mpr
    fg_adjoin_of_finite p.coeffs.finite_toSet fun a _ => Algebra.IsIntegral.isIntegral a⟩
  let p' : S[X] := p.toSubring S.toSubring subset_adjoin
  have hSx : IsIntegral S x := ⟨p', (p.monic_toSubring _ _).mpr pmonic, by
    rw [IsScalarTower.algebraMap_eq S A B]; rw [← eval₂_map]
    convert! hp; apply p.map_toSubring S.toSubring⟩
  let Sx := Subalgebra.toSubmodule (S[x])
  let MSx : Module S Sx := SMulMemClass.toModule _ -- the next line times out without this
  have : Module.Finite S Sx := .of_fg hSx.fg_adjoin_singleton
  refine .of_mem_of_fg ((S[x]).restrictScalars R) ?_ _
    ((Subalgebra.mem_restrictScalars R).mpr <| subset_adjoin rfl)
  rw [← Module.Finite.iff_fg]
  let : SMul S Sx := { MSx with } -- need this even though MSx is there
  have : IsScalarTower R S Sx :=
    Submodule.isScalarTower Sx -- Lean looks for `Module A Sx` without this
  exact Module.Finite.trans S Sx

中文:
定理 is整数egral_trans
  条件: [代数.是整 R A] (x : B) (hx : 是整 A x)
  证明: by
  rcases hx with ⟨p, pmonic, hp⟩
  let S := adjoin R (p.coeffs : Set A)
have : Module.Finite R S := ⟨(Subalgebra.toSubmodule S).fg_top.mpr
    fg_adjoin_of_finite p.coeffs.finite_toSet fun a _ => Algebra.IsIntegral.isIntegral a⟩
  let p' : S[X] := p.toSubring S.toSubring subset_adjoin
  have hSx : IsIntegral S x := ⟨p', (p.monic_toSubring _ _).mpr pmonic, by
    rw [IsScalarTower.algebraMap_eq S A B]; rw [← eval₂_map]
    convert! hp; apply p.map_toSubring S.toSubring⟩
  let Sx := Subalgebra.toSubmodule (S[x])
  let MSx : Module S Sx := SMulMemClass.toModule _ -- the next line times out without this
  have : Module.Finite S Sx := .of_fg hSx.fg_adjoin_singleton
  refine .of_mem_of_fg ((S[x]).restrictScalars R) ?_ _
    ((Subalgebra.mem_restrictScalars R).mpr <| subset_adjoin rfl)
  rw [← Module.Finite.iff_fg]
  let : SMul S Sx := { MSx with } -- need this even though MSx is there
  have : IsScalarTower R S Sx :=
    Submodule.isScalarTower Sx -- Lean looks for `Module A Sx` without this
  exact Module.Finite.trans S Sx

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, Finite, IsIntegral, IsScalarTower, IsScalarTower.algebraMap_eq, Module, Module.Finite, S.toSubring, Subalgebra, Subalgebra.toSubmodule, adjoin, algebraMap_eq, coeffs, convert, fg_adjoin_of_finite, fg_top, fg_top.mpr, finite_toSet, isIntegral
-/
theorem isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx : IsIntegral A x) :
    IsIntegral R x := by
  rcases hx with ⟨p, pmonic, hp⟩
  let S := adjoin R (p.coeffs : Set A)
have : Module.Finite R S := ⟨(Subalgebra.toSubmodule S).fg_top.mpr
    fg_adjoin_of_finite p.coeffs.finite_toSet fun a _ => Algebra.IsIntegral.isIntegral a⟩
  let p' : S[X] := p.toSubring S.toSubring subset_adjoin
  have hSx : IsIntegral S x := ⟨p', (p.monic_toSubring _ _).mpr pmonic, by
    rw [IsScalarTower.algebraMap_eq S A B]; rw [← eval₂_map]
    convert! hp; apply p.map_toSubring S.toSubring⟩
  let Sx := Subalgebra.toSubmodule (S[x])
  let MSx : Module S Sx := SMulMemClass.toModule _ -- the next line times out without this
  have : Module.Finite S Sx := .of_fg hSx.fg_adjoin_singleton
  refine .of_mem_of_fg ((S[x]).restrictScalars R) ?_ _
    ((Subalgebra.mem_restrictScalars R).mpr <| subset_adjoin rfl)
  rw [← Module.Finite.iff_fg]
  let : SMul S Sx := { MSx with } -- need this even though MSx is there
  have : IsScalarTower R S Sx :=
    Submodule.isScalarTower Sx -- Lean looks for `Module A Sx` without this
  exact Module.Finite.trans S Sx

variable (A) in
/--
theorem `Algebra.IsIntegral.trans` / 定理 `Algebra.IsIntegral.trans`

English:
theorem Algebra.IsIntegral.trans
  proof: ⟨fun x => isIntegral_trans x (Algebra.IsIntegral.isIntegral (R := A) x)⟩

中文:
定理 代数.是整.trans
  证明: ⟨fun x => isIntegral_trans x (Algebra.IsIntegral.isIntegral (R := A) x)⟩
-/
protected theorem Algebra.IsIntegral.trans
    [Algebra.IsIntegral R A] [Algebra.IsIntegral A B] : Algebra.IsIntegral R B :=
  ⟨fun x => isIntegral_trans x (Algebra.IsIntegral.isIntegral (R := A) x)⟩

/--
theorem `RingHom.IsIntegral.trans` / 定理 `RingHom.IsIntegral.trans`

English:
theorem RingHom.IsIntegral.trans
  proof: let _ := f.toAlgebra; let _ := g.toAlgebra; let _ := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : Algebra.IsIntegral S T := ⟨hg⟩
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.trans S
  Algebra.IsIntegral.isIntegral

中文:
定理 环态射.是整.trans
  证明: let _ := f.toAlgebra; let _ := g.toAlgebra; let _ := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : Algebra.IsIntegral S T := ⟨hg⟩
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.trans S
  Algebra.IsIntegral.isIntegral
-/
protected theorem RingHom.IsIntegral.trans
    (hf : f.IsIntegral) (hg : g.IsIntegral) : (g.comp f).IsIntegral :=
  let _ := f.toAlgebra; let _ := g.toAlgebra; let _ := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : Algebra.IsIntegral S T := ⟨hg⟩
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.trans S
  Algebra.IsIntegral.isIntegral

/--
lemma `IsIntegralClosure.tower_top` / 引理 `IsIntegralClosure.tower_top`

English:
lemma IsIntegralClosure.tower_top
  statement: {B C : Type*} [CommSemiring C] [CommRing B]
  proof: ⟨IsIntegralClosure.algebraMap_injective _ R _,
   fun hx => (IsIntegralClosure.isIntegral_iff).mp (isIntegral_trans (R := R) _ hx),
   fun hx => ((IsIntegralClosure.isIntegral_iff (R := R)).mpr hx).tower_top⟩

中文:
引理 是整闭包.tower_top
  结论: {B C : 类型} [交换半环 C] [交换环 B]
  证明: ⟨IsIntegralClosure.algebraMap_injective _ R _,
   fun hx => (IsIntegralClosure.isIntegral_iff).mp (isIntegral_trans (R := R) _ hx),
   fun hx => ((IsIntegralClosure.isIntegral_iff (R := R)).mpr hx).tower_top⟩

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isIntegral_iff, algebraMap_injective, isIntegral_iff, isIntegral_trans, tower_top
-/
lemma IsIntegralClosure.tower_top {B C : Type*} [CommSemiring C] [CommRing B]
    [Algebra R B] [Algebra A B] [Algebra C B] [IsScalarTower R A B]
    [IsIntegralClosure C R B] [Algebra.IsIntegral R A] :
    IsIntegralClosure C A B :=
  ⟨IsIntegralClosure.algebraMap_injective _ R _,
   fun hx => (IsIntegralClosure.isIntegral_iff).mp (isIntegral_trans (R := R) _ hx),
   fun hx => ((IsIntegralClosure.isIntegral_iff (R := R)).mpr hx).tower_top⟩

/--
theorem `RingHom.isIntegral_of_surjective` / 定理 `RingHom.isIntegral_of_surjective`

English:
theorem RingHom.isIntegral_of_surjective
  given: (hf : Function.Surjective f)
  statement: f.IsIntegral
  proof: fun x => (hf x).recOn fun _y hy => hy ▸ f.isIntegralElem_map

中文:
定理 环态射.is整数egral_of_surjective
  条件: (hf : 函数.满射 f)
  结论: f.是整
  证明: fun x => (hf x).recOn fun _y hy => hy ▸ f.isIntegralElem_map

Depends on / 依赖: f.isIntegralElem_map, isIntegralElem_map
-/
theorem RingHom.isIntegral_of_surjective (hf : Function.Surjective f) : f.IsIntegral :=
  fun x => (hf x).recOn fun _y hy => hy ▸ f.isIntegralElem_map

/--
theorem `IsIntegral.tower_bot` / 定理 `IsIntegral.tower_bot`

English:
theorem IsIntegral.tower_bot
  statement: (H : Function.Injective (algebraMap A B)) {x : A}
  proof: (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) H).mp h

nonrec theorem RingHom.IsIntegral.tower_bot (hg : Function.Injective g)
    (hfg : (g.comp f).IsIntegral) : f.IsIntegral :=
  letI := f.toAlgebra; letI := g.toAlgebra; letI := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  fun x => IsIntegral.tower_bot hg (hfg (g x))

中文:
定理 是整.tower_bot
  结论: (H : 函数.单射 (algebraMap A B)) {x : A}
  证明: (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) H).mp h

nonrec theorem RingHom.IsIntegral.tower_bot (hg : Function.Injective g)
    (hfg : (g.comp f).IsIntegral) : f.IsIntegral :=
  letI := f.toAlgebra; letI := g.toAlgebra; letI := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  fun x => IsIntegral.tower_bot hg (hfg (g x))

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, isIntegral_algHom_iff, toAlgHom
-/
theorem IsIntegral.tower_bot (H : Function.Injective (algebraMap A B)) {x : A}
    (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) H).mp h

nonrec theorem RingHom.IsIntegral.tower_bot (hg : Function.Injective g)
    (hfg : (g.comp f).IsIntegral) : f.IsIntegral :=
  letI := f.toAlgebra; letI := g.toAlgebra; letI := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  fun x => IsIntegral.tower_bot hg (hfg (g x))

variable (T) in
/--
theorem `Algebra.IsIntegral.tower_bot` / 定理 `Algebra.IsIntegral.tower_bot`

English:
theorem Algebra.IsIntegral.tower_bot
  statement: [IsDomain S] [Algebra R S] [Algebra R T] [Algebra S T]
  proof: by
    apply RingHom.IsIntegral.tower_bot (algebraMap R S) (algebraMap S T)
      (FaithfulSMul.algebraMap_injective S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral

中文:
定理 代数.是整.tower_bot
  结论: [是整环 S] [代数 R S] [代数 R T] [代数 S T]
  证明: by
    apply RingHom.IsIntegral.tower_bot (algebraMap R S) (algebraMap S T)
      (FaithfulSMul.algebraMap_injective S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsIntegral, IsScalarTower, IsScalarTower.algebraMap_eq, RingHom, RingHom.IsIntegral.tower_bot, algebraMap, algebraMap_eq, algebraMap_injective, h.isIntegral, isIntegral, tower_bot
-/
theorem Algebra.IsIntegral.tower_bot [IsDomain S] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsTorsionFree S T] [Nontrivial T] [IsScalarTower R S T]
    [h : Algebra.IsIntegral R T] : Algebra.IsIntegral R S where
  isIntegral := by
    apply RingHom.IsIntegral.tower_bot (algebraMap R S) (algebraMap S T)
      (FaithfulSMul.algebraMap_injective S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral

/--
theorem `IsIntegral.tower_bot_of_field` / 定理 `IsIntegral.tower_bot_of_field`

English:
theorem IsIntegral.tower_bot_of_field
  statement: {R A B : Type*} [CommRing R] [Field A]
  proof: h.tower_bot (algebraMap A B).injective

中文:
定理 是整.tower_bot_of_field
  结论: {R A B : 类型} [交换环 R] [域 A]
  证明: h.tower_bot (algebraMap A B).injective

Depends on / 依赖: algebraMap, h.tower_bot, injective, tower_bot
-/
theorem IsIntegral.tower_bot_of_field {R A B : Type*} [CommRing R] [Field A]
    [Ring B] [Nontrivial B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    {x : A} (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  h.tower_bot (algebraMap A B).injective

/--
theorem `RingHom.isIntegralElem.of_comp` / 定理 `RingHom.isIntegralElem.of_comp`

English:
theorem RingHom.isIntegralElem.of_comp
  given: {x : T} (h : (g.comp f).IsIntegralElem x)
  proof: let ⟨p, hp, hp'⟩ := h
  ⟨p.map f, hp.map f, by rwa [← eval₂_map] at hp'⟩

中文:
定理 环态射.is整数egralElem.of_comp
  条件: {x : T} (h : (g.comp f).Is整数egralElem x)
  证明: let ⟨p, hp, hp'⟩ := h
  ⟨p.map f, hp.map f, by rwa [← eval₂_map] at hp'⟩

Depends on / 依赖: hp.map, p.map
-/
theorem RingHom.isIntegralElem.of_comp {x : T} (h : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x :=
  let ⟨p, hp, hp'⟩ := h
  ⟨p.map f, hp.map f, by rwa [← eval₂_map] at hp'⟩

/--
theorem `RingHom.IsIntegral.tower_top` / 定理 `RingHom.IsIntegral.tower_top`

English:
theorem RingHom.IsIntegral.tower_top
  given: (h : (g.comp f).IsIntegral)
  statement: g.IsIntegral
  proof: fun x => RingHom.isIntegralElem.of_comp f g (h x)

中文:
定理 环态射.是整.tower_top
  条件: (h : (g.comp f).是整)
  结论: g.是整
  证明: fun x => RingHom.isIntegralElem.of_comp f g (h x)

Depends on / 依赖: RingHom, RingHom.isIntegralElem.of_comp, isIntegralElem, of_comp
-/
theorem RingHom.IsIntegral.tower_top (h : (g.comp f).IsIntegral) : g.IsIntegral :=
  fun x => RingHom.isIntegralElem.of_comp f g (h x)

variable (R) in
/--
theorem `Algebra.IsIntegral.tower_top` / 定理 `Algebra.IsIntegral.tower_top`

English:
theorem Algebra.IsIntegral.tower_top
  statement: [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  proof: by
    apply RingHom.IsIntegral.tower_top (algebraMap R S) (algebraMap S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral

中文:
定理 代数.是整.tower_top
  结论: [代数 R S] [代数 R T] [代数 S T] [标量塔 R S T]
  证明: by
    apply RingHom.IsIntegral.tower_top (algebraMap R S) (algebraMap S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral

Depends on / 依赖: IsIntegral, IsScalarTower, IsScalarTower.algebraMap_eq, RingHom, RingHom.IsIntegral.tower_top, algebraMap, algebraMap_eq, h.isIntegral, isIntegral, tower_top
-/
theorem Algebra.IsIntegral.tower_top [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [h : Algebra.IsIntegral R T] : Algebra.IsIntegral S T where
  isIntegral := by
    apply RingHom.IsIntegral.tower_top (algebraMap R S) (algebraMap S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `RingHom.IsIntegral.quotient` / 定理 `RingHom.IsIntegral.quotient`

English:
theorem RingHom.IsIntegral.quotient
  given: {I : Ideal S} (hf : f.IsIntegral)
  proof: by
  rintro ⟨x⟩
  obtain ⟨p, p_monic, hpx⟩ := hf x
  refine ⟨p.map (Ideal.Quotient.mk _), p_monic.map _, ?_⟩
  simpa only [hom_eval₂, eval₂_map] using! congr_arg (Ideal.Quotient.mk I) hpx

中文:
定理 环态射.是整.quotient
  条件: {I : 理想 S} (hf : f.是整)
  证明: by
  rintro ⟨x⟩
  obtain ⟨p, p_monic, hpx⟩ := hf x
  refine ⟨p.map (Ideal.Quotient.mk _), p_monic.map _, ?_⟩
  simpa only [hom_eval₂, eval₂_map] using! congr_arg (Ideal.Quotient.mk I) hpx

Depends on / 依赖: Ideal.Quotient.mk, Quotient, congr_arg, p.map, p_monic, p_monic.map
-/
theorem RingHom.IsIntegral.quotient {I : Ideal S} (hf : f.IsIntegral) :
    (Ideal.quotientMap I f le_rfl).IsIntegral := by
  rintro ⟨x⟩
  obtain ⟨p, p_monic, hpx⟩ := hf x
  refine ⟨p.map (Ideal.Quotient.mk _), p_monic.map _, ?_⟩
  simpa only [hom_eval₂, eval₂_map] using! congr_arg (Ideal.Quotient.mk I) hpx

instance {I : Ideal A} [Algebra.IsIntegral R A] : Algebra.IsIntegral R (A ⧸ I) :=
  Algebra.IsIntegral.trans A

/--
Instance `Algebra.IsIntegral.quotient` / 实例 `Algebra.IsIntegral.quotient`

English:
instance Algebra.IsIntegral.quotient
  signature: {I : Ideal A} [Algebra.IsIntegral R A]
  body: ⟨RingHom.IsIntegral.quotient (algebraMap R A) Algebra.IsIntegral.isIntegral⟩

中文:
实例 代数.是整.quotient
  签名: {I : 理想 A} [代数.是整 R A]
  定义体: ⟨RingHom.IsIntegral.quotient (algebraMap R A) Algebra.IsIntegral.isIntegral⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, RingHom, RingHom.IsIntegral.quotient, algebraMap, isIntegral, quotient
-/
instance Algebra.IsIntegral.quotient {I : Ideal A} [Algebra.IsIntegral R A] :
    Algebra.IsIntegral (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  ⟨RingHom.IsIntegral.quotient (algebraMap R A) Algebra.IsIntegral.isIntegral⟩

/--
theorem `isIntegral_quotientMap_iff` / 定理 `isIntegral_quotientMap_iff`

English:
theorem isIntegral_quotientMap_iff
  given: {I : Ideal S}
  proof: by
  let g := Ideal.Quotient.mk (I.comap f)
  -- Porting note: added type ascription
  have : (Ideal.quotientMap I f le_rfl).comp g = (Ideal.Quotient.mk I).comp f :=
    Ideal.quotientMap_comp_mk le_rfl
  refine ⟨fun h => ?_, fun h => RingHom.IsIntegral.tower_top g _ (this ▸ h)⟩
  refine this ▸ RingHom.IsIntegral.trans g (Ideal.quotientMap I f le_rfl) ?_ h
  exact g.isIntegral_of_surjective Ideal.Quotient.mk_surjective

中文:
定理 is整数egral_quotientMap_iff
  条件: {I : 理想 S}
  证明: by
  let g := Ideal.Quotient.mk (I.comap f)
  -- Porting note: added type ascription
  have : (Ideal.quotientMap I f le_rfl).comp g = (Ideal.Quotient.mk I).comp f :=
    Ideal.quotientMap_comp_mk le_rfl
  refine ⟨fun h => ?_, fun h => RingHom.IsIntegral.tower_top g _ (this ▸ h)⟩
  refine this ▸ RingHom.IsIntegral.trans g (Ideal.quotientMap I f le_rfl) ?_ h
  exact g.isIntegral_of_surjective Ideal.Quotient.mk_surjective

Depends on / 依赖: I.comap, Ideal.Quotient.mk, Quotient
-/
theorem isIntegral_quotientMap_iff {I : Ideal S} :
    (Ideal.quotientMap I f le_rfl).IsIntegral ↔
      ((Ideal.Quotient.mk I).comp f : R ->+* S ⧸ I).IsIntegral := by
  let g := Ideal.Quotient.mk (I.comap f)
  -- Porting note: added type ascription
  have : (Ideal.quotientMap I f le_rfl).comp g = (Ideal.Quotient.mk I).comp f :=
    Ideal.quotientMap_comp_mk le_rfl
  refine ⟨fun h => ?_, fun h => RingHom.IsIntegral.tower_top g _ (this ▸ h)⟩
  refine this ▸ RingHom.IsIntegral.trans g (Ideal.quotientMap I f le_rfl) ?_ h
  exact g.isIntegral_of_surjective Ideal.Quotient.mk_surjective

/--
theorem `RingHom.IsIntegral.kerLift` / 定理 `RingHom.IsIntegral.kerLift`

English:
theorem RingHom.IsIntegral.kerLift
  given: {f : S ->+* T} (hf : f.IsIntegral)
  statement: f.kerLift.IsIntegral
  proof: RingHom.IsIntegral.tower_top (Ideal.Quotient.mk (RingHom.ker f)) f.kerLift hf

中文:
定理 环态射.是整.kerLift
  条件: {f : S ->+* T} (hf : f.是整)
  结论: f.kerLift.是整
  证明: RingHom.IsIntegral.tower_top (Ideal.Quotient.mk (RingHom.ker f)) f.kerLift hf

Depends on / 依赖: Ideal.Quotient.mk, IsIntegral, Quotient, RingHom, RingHom.IsIntegral.tower_top, RingHom.ker, f.kerLift, kerLift, tower_top
-/
theorem RingHom.IsIntegral.kerLift {f : S ->+* T} (hf : f.IsIntegral) : f.kerLift.IsIntegral :=
  RingHom.IsIntegral.tower_top (Ideal.Quotient.mk (RingHom.ker f)) f.kerLift hf

/--
theorem `RingHom.IsIntegral.isLocalHom` / 定理 `RingHom.IsIntegral.isLocalHom`

English:
theorem RingHom.IsIntegral.isLocalHom
  statement: {f : R ->+* S} (hf : f.IsIntegral)
  proof: by
    -- `f a` is invertible in `S`, and we need to show that `(f a)⁻¹` is of the form `f b`.
    -- Let `p : R[X]` be monic with root `(f a)⁻¹`,
    obtain ⟨p, p_monic, hp⟩ := hf (ha.unit⁻¹ : _)
    -- and `q` be `p` with coefficients reversed (so `q(a) = q'(a) * a + 1`).
    -- We have `q(a) = 0`, so `-q'(a)` is the inverse of `a`.
    refine .of_mul_eq_one (-p.reverse.divX.eval a) ?_
    nth_rewrite 1 [mul_neg, ← eval_X (x := a), ← eval_mul, ← p_monic, ← coeff_zero_reverse,
      ← add_eq_zero_iff_neg_eq, ← eval_C (a := p.reverse.coeff 0), ← eval_add, X_mul_divX_add,
      ← (injective_iff_map_eq_zero' _).mp inj, ← eval₂_hom]
    rwa [← eval₂_reverse_eq_zero_iff] at hp

中文:
定理 环态射.是整.isLocalHom
  结论: {f : R ->+* S} (hf : f.是整)
  证明: by
    -- `f a` is invertible in `S`, and we need to show that `(f a)⁻¹` is of the form `f b`.
    -- Let `p : R[X]` be monic with root `(f a)⁻¹`,
    obtain ⟨p, p_monic, hp⟩ := hf (ha.unit⁻¹ : _)
    -- and `q` be `p` with coefficients reversed (so `q(a) = q'(a) * a + 1`).
    -- We have `q(a) = 0`, so `-q'(a)` is the inverse of `a`.
    refine .of_mul_eq_one (-p.reverse.divX.eval a) ?_
    nth_rewrite 1 [mul_neg, ← eval_X (x := a), ← eval_mul, ← p_monic, ← coeff_zero_reverse,
      ← add_eq_zero_iff_neg_eq, ← eval_C (a := p.reverse.coeff 0), ← eval_add, X_mul_divX_add,
      ← (injective_iff_map_eq_zero' _).mp inj, ← eval₂_hom]
    rwa [← eval₂_reverse_eq_zero_iff] at hp
-/
theorem RingHom.IsIntegral.isLocalHom {f : R ->+* S} (hf : f.IsIntegral)
    (inj : Function.Injective f) : IsLocalHom f where
  map_nonunit a ha := by
    -- `f a` is invertible in `S`, and we need to show that `(f a)⁻¹` is of the form `f b`.
    -- Let `p : R[X]` be monic with root `(f a)⁻¹`,
    obtain ⟨p, p_monic, hp⟩ := hf (ha.unit⁻¹ : _)
    -- and `q` be `p` with coefficients reversed (so `q(a) = q'(a) * a + 1`).
    -- We have `q(a) = 0`, so `-q'(a)` is the inverse of `a`.
    refine .of_mul_eq_one (-p.reverse.divX.eval a) ?_
    nth_rewrite 1 [mul_neg, ← eval_X (x := a), ← eval_mul, ← p_monic, ← coeff_zero_reverse,
      ← add_eq_zero_iff_neg_eq, ← eval_C (a := p.reverse.coeff 0), ← eval_add, X_mul_divX_add,
      ← (injective_iff_map_eq_zero' _).mp inj, ← eval₂_hom]
    rwa [← eval₂_reverse_eq_zero_iff] at hp

variable [Algebra R S] [Algebra.IsIntegral R S]

variable (R S) in
/--
Instance `Algebra.IsIntegral.isLocalHom` / 实例 `Algebra.IsIntegral.isLocalHom`

English:
instance Algebra.IsIntegral.isLocalHom
  signature: [FaithfulSMul R S]
  body: (algebraMap_isIntegral_iff.mpr ‹_›).isLocalHom (FaithfulSMul.algebraMap_injective R S)

中文:
实例 代数.是整.isLocalHom
  签名: [忠实标量乘法 R S]
  定义体: (algebraMap_isIntegral_iff.mpr ‹_›).isLocalHom (FaithfulSMul.algebraMap_injective R S)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, algebraMap_isIntegral_iff, algebraMap_isIntegral_iff.mpr, isLocalHom
-/
instance Algebra.IsIntegral.isLocalHom [FaithfulSMul R S] : IsLocalHom (algebraMap R S) :=
  (algebraMap_isIntegral_iff.mpr ‹_›).isLocalHom (FaithfulSMul.algebraMap_injective R S)

/--
theorem `isField_of_isIntegral_of_isField` / 定理 `isField_of_isIntegral_of_isField`

English:
theorem isField_of_isIntegral_of_isField
  statement: (hRS : Function.Injective (algebraMap R S))
  proof: have := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
  IsLocalHom.isField hRS hS

中文:
定理 isField_of_is整数egral_of_isField
  结论: (hRS : 函数.单射 (algebraMap R S))
  证明: have := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
  IsLocalHom.isField hRS hS

Depends on / 依赖: And.left, IsLocalHom, IsLocalHom.isField, _interior_eq_self, faithfulSMul_iff_algebraMap_injective, hasBasis_nhdsSet, isField
-/
theorem isField_of_isIntegral_of_isField (hRS : Function.Injective (algebraMap R S))
    (hS : IsField S) : IsField R :=
  have := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
  IsLocalHom.isField hRS hS

/--
theorem `Algebra.IsIntegral.isField_iff_isField` / 定理 `Algebra.IsIntegral.isField_iff_isField`

English:
theorem Algebra.IsIntegral.isField_iff_isField
  statement: [IsDomain S]
  proof: ⟨isField_of_isIntegral_of_isField', isField_of_isIntegral_of_isField hRS⟩

中文:
定理 代数.是整.isField_iff_isField
  结论: [是整环 S]
  证明: ⟨isField_of_isIntegral_of_isField', isField_of_isIntegral_of_isField hRS⟩

Depends on / 依赖: isField_of_isIntegral_of_isField
-/
theorem Algebra.IsIntegral.isField_iff_isField [IsDomain S]
    (hRS : Function.Injective (algebraMap R S)) : IsField R ↔ IsField S :=
  ⟨isField_of_isIntegral_of_isField', isField_of_isIntegral_of_isField hRS⟩

/--
theorem `Ideal.IsMaximal.ne_bot_of_isIntegral_int` / 定理 `Ideal.IsMaximal.ne_bot_of_isIntegral_int`

English:
theorem Ideal.IsMaximal.ne_bot_of_isIntegral_int
  proof: Ring.ne_bot_of_isMaximal_of_not_isField ‹_› fun h => Int.not_isField
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective Int R) h)

中文:
定理 理想.是极大.ne_bot_of_is整数egral_int
  证明: Ring.ne_bot_of_isMaximal_of_not_isField ‹_› fun h => Int.not_isField
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective Int R) h)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Int.not_isField, Ring.ne_bot_of_isMaximal_of_not_isField, algebraMap_injective, isField_of_isIntegral_of_isField, ne_bot_of_isMaximal_of_not_isField, not_isField
-/
theorem Ideal.IsMaximal.ne_bot_of_isIntegral_int
    [CharZero R] [Algebra.IsIntegral Int R] (I : Ideal R) [I.IsMaximal] : I != ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField ‹_› fun h => Int.not_isField
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective Int R) h)

variable (R) in
/--
theorem `Algebra.ker_algebraMap_isMaximal_of_isIntegral` / 定理 `Algebra.ker_algebraMap_isMaximal_of_isIntegral`

English:
theorem Algebra.ker_algebraMap_isMaximal_of_isIntegral
  statement: (k : Type*) [Field k] [Algebra R k]
  proof: by
  have := Ideal.bot_isMaximal (K := k)
  rw [RingHom.ker]; rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_of_isIntegral_of_isField Ideal.algebraMap_quotient_injective
    (Ideal.Quotient.field _).toIsField

中文:
定理 代数.ker_algebraMap_isMaximal_of_is整数egral
  结论: (k : 类型) [域 k] [代数 R k]
  证明: by
  have := Ideal.bot_isMaximal (K := k)
  rw [RingHom.ker]; rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_of_isIntegral_of_isField Ideal.algebraMap_quotient_injective
    (Ideal.Quotient.field _).toIsField

Depends on / 依赖: Ideal.Quotient.field, Ideal.Quotient.maximal_ideal_iff_isField_quotient, Ideal.algebraMap_quotient_injective, Ideal.bot_isMaximal, Quotient, RingHom, RingHom.ker, algebraMap_quotient_injective, bot_isMaximal, isField_of_isIntegral_of_isField, maximal_ideal_iff_isField_quotient, toIsField
-/
theorem Algebra.ker_algebraMap_isMaximal_of_isIntegral (k : Type*) [Field k] [Algebra R k]
    [Algebra.IsIntegral R k] : (RingHom.ker (algebraMap R k)).IsMaximal := by
  have := Ideal.bot_isMaximal (K := k)
  rw [RingHom.ker]; rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_of_isIntegral_of_isField Ideal.algebraMap_quotient_injective
    (Ideal.Quotient.field _).toIsField

end Algebra

/--
theorem `integralClosure_idem` / 定理 `integralClosure_idem`

English:
theorem integralClosure_idem
  given: {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  proof: letI := (integralClosure R A).algebra
  eq_bot_iff.2 fun x hx => Algebra.mem_bot.2
    ⟨⟨x, isIntegral_trans (A := integralClosure R A) x hx⟩, rfl⟩

中文:
定理 integralClosure_idem
  条件: {R A : 类型} [交换环 R] [交换环 A] [代数 R A]
  证明: letI := (integralClosure R A).algebra
  eq_bot_iff.2 fun x hx => Algebra.mem_bot.2
    ⟨⟨x, isIntegral_trans (A := integralClosure R A) x hx⟩, rfl⟩

Depends on / 依赖: Algebra, Algebra.mem_bot, algebra, eq_bot_iff, integralClosure, isIntegral_trans, mem_bot
-/
theorem integralClosure_idem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    integralClosure (integralClosure R A) A = ⊥ :=
  letI := (integralClosure R A).algebra
  eq_bot_iff.2 fun x hx => Algebra.mem_bot.2
    ⟨⟨x, isIntegral_trans (A := integralClosure R A) x hx⟩, rfl⟩

section IsDomain

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain (integralClosure R S)
  body: inferInstance

中文:
实例 :
  签名: 是整环 (integralClosure R S)
  定义体: inferInstance
-/
instance : IsDomain (integralClosure R S) :=
  inferInstance

/--
theorem `roots_mem_integralClosure` / 定理 `roots_mem_integralClosure`

English:
theorem roots_mem_integralClosure
  statement: {f : R[X]} (hf : f.Monic) {a : S}
  proof: ⟨f, hf, (eval₂_eq_eval_map _).trans (mem_roots <| (hf.map _).ne_zero).1 ha⟩

中文:
定理 roots_mem_integralClosure
  结论: {f : R[X]} (hf : f.Monic) {a : S}
  证明: ⟨f, hf, (eval₂_eq_eval_map _).trans (mem_roots <| (hf.map _).ne_zero).1 ha⟩

Depends on / 依赖: hf.map, mem_roots, ne_zero
-/
theorem roots_mem_integralClosure {f : R[X]} (hf : f.Monic) {a : S}
    (ha : a in f.aroots S) : a in integralClosure R S :=
⟨f, hf, (eval₂_eq_eval_map _).trans (mem_roots <| (hf.map _).ne_zero).1 ha⟩

end IsDomain
