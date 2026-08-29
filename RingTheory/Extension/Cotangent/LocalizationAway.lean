/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Cotangent and localization away

Let `R → S → T` be algebras such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P : R[X] → S` with kernel `I` and
`Q : S[Y] → T` is the canonical `S`-presentation of `T` with kernel `K`.
Denote by `J` the kernel of the composition `R[X,Y] → T`.

This file proves `J/J² ≃ₗ[T] T ⊗[S] (I/I²) × K/K²`. For this we establish the exact sequence:
```
0 → T ⊗[S] (I/I²) → J/J² → K/K² → 0
```
and use that `K/K²` is free, so the sequence splits. The first part of the file
shows the exactness on the left and the rest of the file deduces the exact sequence
and the splitting from the Jacobi Zariski sequence.

## Main results

- `Algebra.Generators.liftBaseChange_injective`:
  `T ⊗[S] (I/I²) → J/J²` is injective if `T` is the localization of `S` away from an element.
- `Algebra.Generators.cotangentCompLocalizationAwayEquiv`: `J/J² ≃ₗ[T] T ⊗[S] (I/I²) × K/K²`.
-/

@[expose] public section

open TensorProduct MvPolynomial

namespace Algebra.Generators

variable {R S T ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (g : S) [IsLocalization.Away g T] (P : Generators R S ι)

/--
lemma `comp_localizationAway_ker` / 引理 `comp_localizationAway_ker`

English:
lemma comp_localizationAway_ker
  statement: (P : Generators R S ι) (f : P.Ring)
  proof: by
  have : (localizationAway T g).ker = Ideal.map ((localizationAway T g).ofComp P).toAlgHom
      (Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1}) := by
    rw [Ideal.map_span]; rw [Set.image_singleton]; rw [map_sub]; rw [map_mul]; rw [map_one]; rw [ker_localizationAw

中文:
引理 comp_localizationAway_ker
  结论: (P : Generators R S ι) (f : P.Ring)
  证明: by
  have : (localizationAway T g).ker = Ideal.map ((localizationAway T g).ofComp P).toAlgHom
      (Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1}) := by
    rw [Ideal.map_span]; rw [Set.image_singleton]; rw [map_sub]; rw [map_mul]; rw [map_one]; rw [ker_localizationAw

Depends on / 依赖: Algebra, Algebra.Generators.map_toComp_ker, Generators, Hom.toAlgHom_X, Ideal.comap_map_of_surjective, Ideal.map, Ideal.map_span, Ideal.span, MvPolynomial, MvPolynomial.X, MvPolynomial.rename, Set.image_singleton, Sum.elim_inl, Sum.inl, Sum.inr, comap_map_of_surjective, elim_inl, image_singleton, ker_comp_eq_sup, ker_localizationAway
-/
lemma comp_localizationAway_ker (P : Generators R S ι) (f : P.Ring)
    (h : algebraMap P.Ring S f = g) :
    ((Generators.localizationAway T g).comp P).ker =
      Ideal.map ((Generators.localizationAway T g).toComp P).toAlgHom P.ker ⊔
        Ideal.span {rename Sum.inr f * X (Sum.inl ()) - 1} := by
  have : (localizationAway T g).ker = Ideal.map ((localizationAway T g).ofComp P).toAlgHom
      (Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1}) := by
    rw [Ideal.map_span]; rw [Set.image_singleton]; rw [map_sub]; rw [map_mul]; rw [map_one]; rw [ker_localizationAway]; rw [Hom.toAlgHom_X]; rw [toAlgHom_ofComp_rename]; rw [h]; rw [ofComp_val]; rw [Sum.elim_inl]
  rw [ker_comp_eq_sup]; rw [Algebra.Generators.map_toComp_ker]; rw [this]; rw [Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective _ P)]; rw [← RingHom.ker_eq_comap_bot]; rw [← sup_assoc]
  simp

variable (T) in
/-- If `R[X] → S` generates `S`, `T` is the localization of `S` away from `g` and
`f` is a pre-image of `g` in `R[X]`, this is the `R`-algebra map `R[X,Y] →ₐ[R] (R[X]/I²)[1/f]`
defined via mapping `Y` to `1/f`. -/
noncomputable
/--
Definition of `compLocalizationAwayAlgHom` / `compLocalizationAwayAlgHom` 的定义

English:
definition compLocalizationAwayAlgHom
  signature: : ((Generators.localizationAway T g).comp P).Ring ->ₐ[R]
  body: aeval (R := R) (S₁ := Localization.Away _)
    (Sum.elim
      (fun _ => IsLocalization.Away.invSelf <| (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)))
      (fun i : ι => algebraMap P.Ring _ (X i)))

中文:
定义 compLocalizationAwayAlgHom
  签名: : ((Generators.localizationAway T g).comp P).Ring ->ₐ[R]
  定义体: aeval (R := R) (S₁ := Localization.Away _)
    (Sum.elim
      (fun _ => IsLocalization.Away.invSelf <| (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)))
      (fun i : ι => algebraMap P.Ring _ (X i)))

Depends on / 依赖: Ideal.Quotient.mk, IsLocalization, IsLocalization.Away.invSelf, Localization, Localization.Away, P.Ring, P.ker, Quotient, Sum.elim, algebraMap, invSelf
-/
def compLocalizationAwayAlgHom : ((Generators.localizationAway T g).comp P).Ring ->ₐ[R]
      Localization.Away (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)) :=
  aeval (R := R) (S₁ := Localization.Away _)
    (Sum.elim
      (fun _ => IsLocalization.Away.invSelf <| (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)))
      (fun i : ι => algebraMap P.Ring _ (X i)))

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `compLocalizationAwayAlgHom_toAlgHom_toComp` / 引理 `compLocalizationAwayAlgHom_toAlgHom_toComp`

English:
lemma compLocalizationAwayAlgHom_toAlgHom_toComp
  given: (x : P.Ring)
  proof: by
  simp only [toComp_toAlgHom, compLocalizationAwayAlgHom, comp,
    localizationAway, AlgHom.toRingHom_eq_coe, aeval_rename,
    Sum.elim_comp_inr, ← IsScalarTower.toAlgHom_apply (R := R), ← comp_aeval_apply,
    aeval_X_left_apply]

@[simp]

中文:
引理 compLocalizationAwayAlgHom_toAlgHom_toComp
  条件: (x : P.Ring)
  证明: by
  simp only [toComp_toAlgHom, compLocalizationAwayAlgHom, comp,
    localizationAway, AlgHom.toRingHom_eq_coe, aeval_rename,
    Sum.elim_comp_inr, ← IsScalarTower.toAlgHom_apply (R := R), ← comp_aeval_apply,
    aeval_X_left_apply]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, IsScalarTower, IsScalarTower.toAlgHom_apply, Sum.elim_comp_inr, aeval_X_left_apply, aeval_rename, compLocalizationAwayAlgHom, comp_aeval_apply, elim_comp_inr, localizationAway, toAlgHom_apply, toComp_toAlgHom, toRingHom_eq_coe
-/
lemma compLocalizationAwayAlgHom_toAlgHom_toComp (x : P.Ring) :
    compLocalizationAwayAlgHom T g P (((localizationAway T g).toComp P).toAlgHom x) =
      algebraMap P.Ring _ x := by
  simp only [toComp_toAlgHom, compLocalizationAwayAlgHom, comp,
    localizationAway, AlgHom.toRingHom_eq_coe, aeval_rename,
    Sum.elim_comp_inr, ← IsScalarTower.toAlgHom_apply (R := R), ← comp_aeval_apply,
    aeval_X_left_apply]

@[simp]
/--
lemma `compLocalizationAwayAlgHom_X_inl` / 引理 `compLocalizationAwayAlgHom_X_inl`

English:
lemma compLocalizationAwayAlgHom_X_inl
  statement: compLocalizationAwayAlgHom T g P (X (Sum.inl ())) =
  proof: by
  simp [compLocalizationAwayAlgHom]

中文:
引理 compLocalizationAwayAlgHom_X_inl
  结论: compLocalizationAwayAlgHom T g P (X (Sum.inl ())) =
  证明: by
  simp [compLocalizationAwayAlgHom]

Depends on / 依赖: compLocalizationAwayAlgHom
-/
lemma compLocalizationAwayAlgHom_X_inl : compLocalizationAwayAlgHom T g P (X (Sum.inl ())) =
      IsLocalization.Away.invSelf ((Ideal.Quotient.mk (P.ker ^ 2)) (P.σ g)) := by
  simp [compLocalizationAwayAlgHom]

/--
lemma `compLocalizationAwayAlgHom_relation_eq_zero` / 引理 `compLocalizationAwayAlgHom_relation_eq_zero`

English:
lemma compLocalizationAwayAlgHom_relation_eq_zero
  proof: by
  rw [map_sub]; rw [map_one]; rw [map_mul]; rw [← toComp_toAlgHom (Generators.localizationAway T g) P]
  change (compLocalizationAwayAlgHom T g P)
    (((localizationAway T g).toComp P).toAlgHom _) * _ - _ = _
  rw [compLocalizationAwayAlgHom_toAlgHom_toComp]; rw [compLocalizationAwayAlgHom_X_inl

中文:
引理 compLocalizationAwayAlgHom_relation_eq_zero
  证明: by
  rw [map_sub]; rw [map_one]; rw [map_mul]; rw [← toComp_toAlgHom (Generators.localizationAway T g) P]
  change (compLocalizationAwayAlgHom T g P)
    (((localizationAway T g).toComp P).toAlgHom _) * _ - _ = _
  rw [compLocalizationAwayAlgHom_toAlgHom_toComp]; rw [compLocalizationAwayAlgHom_X_inl

Depends on / 依赖: Generators, Generators.localizationAway, IsScalarTower, IsScalarTower.algebraMap_apply, Localization, Localization.Away, P.Ring, P.ker, algebraMap_apply, compLocalizationAwayAlgHom, compLocalizationAwayAlgHom_X_inl, compLocalizationAwayAlgHom_toAlgHom_toComp, localizationAway, map_mul, map_one, map_sub, toAlgHom, toComp, toComp_toAlgHom
-/
lemma compLocalizationAwayAlgHom_relation_eq_zero :
    compLocalizationAwayAlgHom T g P (rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1) = 0 := by
  rw [map_sub]; rw [map_one]; rw [map_mul]; rw [← toComp_toAlgHom (Generators.localizationAway T g) P]
  change (compLocalizationAwayAlgHom T g P)
    (((localizationAway T g).toComp P).toAlgHom _) * _ - _ = _
  rw [compLocalizationAwayAlgHom_toAlgHom_toComp]; rw [compLocalizationAwayAlgHom_X_inl]; rw [IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away _)]
  simp

/--
lemma `sq_ker_comp_le_ker_compLocalizationAwayAlgHom` / 引理 `sq_ker_comp_le_ker_compLocalizationAwayAlgHom`

English:
lemma sq_ker_comp_le_ker_compLocalizationAwayAlgHom
  proof: by
  have hsple {x} (hx : x in Ideal.span {(rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1}) :
        (compLocalizationAwayAlgHom T g P) x = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul]; rw [compLocalizationAwayAlgHom_relation_eq_zero]; rw [zero_mul]
  rw [comp_local

中文:
引理 sq_ker_comp_le_ker_compLocalizationAwayAlgHom
  证明: by
  have hsple {x} (hx : x in Ideal.span {(rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1}) :
        (compLocalizationAwayAlgHom T g P) x = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul]; rw [compLocalizationAwayAlgHom_relation_eq_zero]; rw [zero_mul]
  rw [comp_local

Depends on / 依赖: Ideal.map_le_iff_le_comap, Ideal.map_mul, Ideal.mem_span_singleton.mp, Ideal.mul_sup, Ideal.span, Ideal.sup_mul, Sum.inl, Sum.inr, compLocalizationAwayAlgHom, compLocalizationAwayAlgHom_relation_eq_zero, comp_localizationAway_ker, map_le_iff_le_comap, map_mul, mem_span_singleton, mul_sup, sup_le, sup_mul, zero_mul
-/
lemma sq_ker_comp_le_ker_compLocalizationAwayAlgHom :
    ((localizationAway T g).comp P).ker ^ 2 <=
      RingHom.ker (compLocalizationAwayAlgHom T g P) := by
  have hsple {x} (hx : x in Ideal.span {(rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1}) :
        (compLocalizationAwayAlgHom T g P) x = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul]; rw [compLocalizationAwayAlgHom_relation_eq_zero]; rw [zero_mul]
  rw [comp_localizationAway_ker _ _ (P.σ g) (by simp)]; rw [sq]; rw [Ideal.sup_mul]; rw [Ideal.mul_sup]; rw [Ideal.mul_sup]
  apply sup_le
  · apply sup_le
    · rw [← Ideal.map_mul, Ideal.map_le_iff_le_comap, ← sq]
      intro x hx
      simp only [Ideal.mem_comap, RingHom.mem_ker,
        compLocalizationAwayAlgHom_toAlgHom_toComp (T := T) g P x]
      rw [IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away _)]; rw [Ideal.Quotient.algebraMap_eq]; rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; rw [map_zero]
    · rw [Ideal.mul_le]
      intro x hx y hy
      simp [hsple hy]
  · apply sup_le <;>
    · rw [Ideal.mul_le]
      intro x hx y hy
      simp [hsple hx]

set_option backward.isDefEq.respectTransparency false in
/--
Let `R → S → T` be algebras such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P` with kernel `I` and `Q` is the
canonical `S`-presentation of `T`. Denote by `J` the kernel of the composition
`R[X,Y] → T`. Then `T ⊗[S] (I/I²) → J/J²` is injective.
-/
@[stacks 08JZ "part of (1)"]
/--
lemma `liftBaseChange_injective_of_isLocalizationAway` / 引理 `liftBaseChange_injective_of_isLocalizationAway`

English:
lemma liftBaseChange_injective_of_isLocalizationAway
  proof: by
  set Q := Generators.localizationAway T g
  algebraize [((Generators.localizationAway T g).toComp P).toAlgHom.toRingHom]
  let f : P.Ring ⧸ P.ker ^ 2 := P.σ g
  let π := compLocalizationAwayAlgHom T g P
  refine IsLocalizedModule.injective_of_map_zero (Submonoid.powers g)
    (TensorProduct.mk S

中文:
引理 liftBaseChange_injective_of_isLocalizationAway
  证明: by
  set Q := Generators.localizationAway T g
  algebraize [((Generators.localizationAway T g).toComp P).toAlgHom.toRingHom]
  let f : P.Ring ⧸ P.ker ^ 2 := P.σ g
  let π := compLocalizationAwayAlgHom T g P
  refine IsLocalizedModule.injective_of_map_zero (Submonoid.powers g)
    (TensorProduct.mk S

Depends on / 依赖: Algebra, Algebra.Extension.Cotangent.mk_surjective, Cotangent, Extension, Generators, Generators.localizationAway, IsLocalizedModule, IsLocalizedModule.injective_of_map_zero, IsScalarTower, IsScalarTower.algebraMap_apply, Localization, Localization.Away, P.Ring, P.ker, P.toExtension.Cotangent, Submonoid, Submonoid.powers, TensorProduct, TensorProduct.mk, algebraMap
-/
lemma liftBaseChange_injective_of_isLocalizationAway :
    Function.Injective (LinearMap.liftBaseChange T
      (Extension.Cotangent.map
        ((Generators.localizationAway T g).toComp P).toExtensionHom)) := by
  set Q := Generators.localizationAway T g
  algebraize [((Generators.localizationAway T g).toComp P).toAlgHom.toRingHom]
  let f : P.Ring ⧸ P.ker ^ 2 := P.σ g
  let π := compLocalizationAwayAlgHom T g P
  refine IsLocalizedModule.injective_of_map_zero (Submonoid.powers g)
    (TensorProduct.mk S T P.toExtension.Cotangent 1) (fun x hx => ?_)
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  suffices h : algebraMap P.Ring (Localization.Away f) x.val = 0 by
    rw [IsScalarTower.algebraMap_apply _ (P.Ring ⧸ P.ker ^ 2) _]; rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f)] at h
    obtain ⟨⟨m, ⟨n, rfl⟩⟩, hm⟩ := h
    rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers g)]
    use ⟨g ^ n, n, rfl⟩
    dsimp [f] at hm
    rw [← map_pow]; rw [← map_mul]; rw [Ideal.Quotient.eq_zero_iff_mem] at hm
    simp only [Submonoid.smul_def]
    rw [show g = algebraMap P.Ring S (P.σ g) by simp]; rw [← map_pow]; rw [algebraMap_smul]; rw [← map_smul]; rw [Extension.Cotangent.mk_eq_zero_iff]
    simpa using! hm
  rw [← compLocalizationAwayAlgHom_toAlgHom_toComp (T := T)]
  apply sq_ker_comp_le_ker_compLocalizationAwayAlgHom
  simpa only [LinearEquiv.coe_coe, LinearMap.ringLmapEquivSelf_symm_apply,
    mk_apply, lift.tmul, LinearMap.coe_restrictScalars, LinearMap.coe_smulRight,
    Module.End.one_apply, LinearMap.smul_apply, one_smul, Algebra.Extension.Cotangent.map_mk,
    Extension.Cotangent.mk_eq_zero_iff] using! hx

/--
Definition of `cotangentCompAwaySec` / `cotangentCompAwaySec` 的定义

English:
definition cotangentCompAwaySec
  signature: (x : ((localizationAway T g).comp P).toExtension.Cotangent)
  body: (basisCotangentAway T g).constr T fun _ => x

中文:
定义 cotangentCompAwaySec
  签名: (x : ((localizationAway T g).comp P).toExtension.Cotangent)
  定义体: (basisCotangentAway T g).constr T fun _ => x

Depends on / 依赖: basisCotangentAway, constr
-/
noncomputable def cotangentCompAwaySec (x : ((localizationAway T g).comp P).toExtension.Cotangent) :
    (localizationAway T g).toExtension.Cotangent ->ₗ[T]
      ((localizationAway T g).comp P).toExtension.Cotangent :=
  (basisCotangentAway T g).constr T fun _ => x

variable (x : ((localizationAway T g).comp P).toExtension.Cotangent)

/--
lemma `cotangentCompAwaySec_apply` / 引理 `cotangentCompAwaySec_apply`

English:
lemma cotangentCompAwaySec_apply
  proof: by
  rw [← basisCotangentAway_apply _ ()]; rw [cotangentCompAwaySec]; rw [Module.Basis.constr_basis]

中文:
引理 cotangentCompAwaySec_apply
  证明: by
  rw [← basisCotangentAway_apply _ ()]; rw [cotangentCompAwaySec]; rw [Module.Basis.constr_basis]

Depends on / 依赖: Module, Module.Basis.constr_basis, basisCotangentAway_apply, constr_basis, cotangentCompAwaySec
-/
lemma cotangentCompAwaySec_apply :
    cotangentCompAwaySec g P x (cMulXSubOneCotangent T g) = x := by
  rw [← basisCotangentAway_apply _ ()]; rw [cotangentCompAwaySec]; rw [Module.Basis.constr_basis]

variable {x}
  (hx : Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom x =
    cMulXSubOneCotangent T g)

include hx in
/--
lemma `map_comp_cotangentCompAwaySec` / 引理 `map_comp_cotangentCompAwaySec`

English:
lemma map_comp_cotangentCompAwaySec
  proof: by
  refine (basisCotangentAway T g).ext fun r => ?_
  simpa only [LinearMap.coe_comp, Function.comp_apply, basisCotangentAway_apply,
    cotangentCompAwaySec_apply]

中文:
引理 map_comp_cotangentCompAwaySec
  证明: by
  refine (basisCotangentAway T g).ext fun r => ?_
  simpa only [LinearMap.coe_comp, Function.comp_apply, basisCotangentAway_apply,
    cotangentCompAwaySec_apply]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, basisCotangentAway, basisCotangentAway_apply, coe_comp, comp_apply, cotangentCompAwaySec_apply
-/
lemma map_comp_cotangentCompAwaySec :
    (Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom) ∘ₗ
      cotangentCompAwaySec g P x = .id := by
  refine (basisCotangentAway T g).ext fun r => ?_
  simpa only [LinearMap.coe_comp, Function.comp_apply, basisCotangentAway_apply,
    cotangentCompAwaySec_apply]

/--
Let `S` be generated over `R` by `P : R[X] → S` with kernel `I` and let `T`
be the localization of `S` away from `g` generated over `S` by `S[Y] → T` with
kernel `K`.
Denote by `J` the kernel of the induced `R[X, Y] → T`. Then
`J/J² ≃ₗ[T] T ⊗[S] (I/I²) × (K/K²)`.

This is the splitting characterised by `x ↦ (0, g * X - 1)`.
-/
@[stacks 08JZ "(1)"]
noncomputable
/--
Definition of `cotangentCompLocalizationAwayEquiv` / `cotangentCompLocalizationAwayEquiv` 的定义

English:
definition cotangentCompLocalizationAwayEquiv
  signature: :
  body: ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).1

中文:
定义 cotangentCompLocalizationAwayEquiv
  签名: :
  定义体: ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).1

Depends on / 依赖: Cotangent, Cotangent.exact, cotangentCompAwaySec, liftBaseChange_injective_of_isLocalizationAway, localizationAway, map_comp_cotangentCompAwaySec, splitSurjectiveEquiv
-/
def cotangentCompLocalizationAwayEquiv :
    ((localizationAway T g).comp P).toExtension.Cotangent ≃ₗ[T]
      T otimes[S] P.toExtension.Cotangent × (Generators.localizationAway T g).toExtension.Cotangent :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).1

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `cotangentCompLocalizationAwayEquiv_symm_inr` / 引理 `cotangentCompLocalizationAwayEquiv_symm_inr`

English:
lemma cotangentCompLocalizationAwayEquiv_symm_inr
  proof: by
  simpa [cotangentCompLocalizationAwayEquiv, Function.Exact.splitSurjectiveEquiv] using
    cotangentCompAwaySec_apply g P x

中文:
引理 cotangentCompLocalizationAwayEquiv_symm_inr
  证明: by
  simpa [cotangentCompLocalizationAwayEquiv, Function.Exact.splitSurjectiveEquiv] using
    cotangentCompAwaySec_apply g P x

Depends on / 依赖: Function, Function.Exact.splitSurjectiveEquiv, cotangentCompAwaySec_apply, cotangentCompLocalizationAwayEquiv, splitSurjectiveEquiv
-/
lemma cotangentCompLocalizationAwayEquiv_symm_inr :
    (cotangentCompLocalizationAwayEquiv g P hx).symm
      (0, cMulXSubOneCotangent T g) = x := by
  simpa [cotangentCompLocalizationAwayEquiv, Function.Exact.splitSurjectiveEquiv] using
    cotangentCompAwaySec_apply g P x

/--
lemma `cotangentCompLocalizationAwayEquiv_symm_comp_inl` / 引理 `cotangentCompLocalizationAwayEquiv_symm_comp_inl`

English:
lemma cotangentCompLocalizationAwayEquiv_symm_comp_inl
  proof: ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x,
      map_comp_cotangentCompAwaySec g P hx⟩).2.left.symm

@[simp]

中文:
引理 cotangentCompLocalizationAwayEquiv_symm_comp_inl
  证明: ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x,
      map_comp_cotangentCompAwaySec g P hx⟩).2.left.symm

@[simp]

Depends on / 依赖: Cotangent, Cotangent.exact, cotangentCompAwaySec, left.symm, liftBaseChange_injective_of_isLocalizationAway, localizationAway, map_comp_cotangentCompAwaySec, splitSurjectiveEquiv
-/
lemma cotangentCompLocalizationAwayEquiv_symm_comp_inl :
    (cotangentCompLocalizationAwayEquiv g P hx).symm.toLinearMap ∘ₗ
      .inl T (T otimes[S] P.toExtension.Cotangent) (localizationAway T g).toExtension.Cotangent =
      .liftBaseChange T
        (Extension.Cotangent.map ((localizationAway T g).toComp P).toExtensionHom) :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x,
      map_comp_cotangentCompAwaySec g P hx⟩).2.left.symm

@[simp]
/--
lemma `cotangentCompLocalizationAwayEquiv_symm_inl` / 引理 `cotangentCompLocalizationAwayEquiv_symm_inl`

English:
lemma cotangentCompLocalizationAwayEquiv_symm_inl
  given: (a : T otimes[S] P.toExtension.Cotangent)
  proof: by
  simp [← cotangentCompLocalizationAwayEquiv_symm_comp_inl g P hx]

中文:
引理 cotangentCompLocalizationAwayEquiv_symm_inl
  条件: (a : T otimes[S] P.toExtension.Cotangent)
  证明: by
  simp [← cotangentCompLocalizationAwayEquiv_symm_comp_inl g P hx]

Depends on / 依赖: cotangentCompLocalizationAwayEquiv_symm_comp_inl
-/
lemma cotangentCompLocalizationAwayEquiv_symm_inl (a : T otimes[S] P.toExtension.Cotangent) :
    (cotangentCompLocalizationAwayEquiv g P hx).symm (a, 0) = LinearMap.liftBaseChange T
        (Extension.Cotangent.map ((localizationAway T g).toComp P).toExtensionHom) a := by
  simp [← cotangentCompLocalizationAwayEquiv_symm_comp_inl g P hx]

/--
lemma `snd_comp_cotangentCompLocalizationAwayEquiv` / 引理 `snd_comp_cotangentCompLocalizationAwayEquiv`

English:
lemma snd_comp_cotangentCompLocalizationAwayEquiv
  proof: ((Cotangent.exact (localizationAway T g) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).2.right.symm

@[simp]

中文:
引理 snd_comp_cotangentCompLocalizationAwayEquiv
  证明: ((Cotangent.exact (localizationAway T g) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).2.right.symm

@[simp]

Depends on / 依赖: Cotangent, Cotangent.exact, cotangentCompAwaySec, liftBaseChange_injective_of_isLocalizationAway, localizationAway, map_comp_cotangentCompAwaySec, right.symm, splitSurjectiveEquiv
-/
lemma snd_comp_cotangentCompLocalizationAwayEquiv :
    LinearMap.snd T (T otimes[S] P.toExtension.Cotangent) (localizationAway T g).toExtension.Cotangent ∘ₗ
      (cotangentCompLocalizationAwayEquiv g P hx).toLinearMap =
      Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom :=
  ((Cotangent.exact (localizationAway T g) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).2.right.symm

@[simp]
/--
lemma `snd_cotangentCompLocalizationAwayEquiv` / 引理 `snd_cotangentCompLocalizationAwayEquiv`

English:
lemma snd_cotangentCompLocalizationAwayEquiv
  proof: by
  simp [← snd_comp_cotangentCompLocalizationAwayEquiv g P hx]

中文:
引理 snd_cotangentCompLocalizationAwayEquiv
  证明: by
  simp [← snd_comp_cotangentCompLocalizationAwayEquiv g P hx]

Depends on / 依赖: snd_comp_cotangentCompLocalizationAwayEquiv
-/
lemma snd_cotangentCompLocalizationAwayEquiv
    (a : ((localizationAway T g).comp P).toExtension.Cotangent) :
    (cotangentCompLocalizationAwayEquiv g P hx a).2 =
      Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom a := by
  simp [← snd_comp_cotangentCompLocalizationAwayEquiv g P hx]

end Algebra.Generators
