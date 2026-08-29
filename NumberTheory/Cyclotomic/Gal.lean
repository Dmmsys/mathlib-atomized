/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Galois group of cyclotomic extensions

In this file, we show the relationship between the Galois group of `K(ζₙ)` and `(ZMod n)ˣ`;
it is always a subgroup, and if the `n`th cyclotomic polynomial is irreducible, they are isomorphic.

## Main results

* `IsPrimitiveRoot.autToPow_injective`: `IsPrimitiveRoot.autToPow` is injective
  in the case that it's considered over a cyclotomic field extension.
* `IsCyclotomicExtension.autEquivPow`: If the `n`th cyclotomic polynomial is irreducible in `K`,
  then `IsPrimitiveRoot.autToPow` is a `MulEquiv` (for example, in `ℚ` and certain `𝔽ₚ`).
* `galXPowEquivUnitsZMod`, `galCyclotomicEquivUnitsZMod`: Repackage
  `IsCyclotomicExtension.autEquivPow` in terms of `Polynomial.Gal`.
* `IsCyclotomicExtension.Aut.commGroup`: Cyclotomic extensions are abelian.

## References

* https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf

## TODO

* We currently can get away with the fact that the power of a primitive root is a primitive root,
  but the correct long-term solution for computing other explicit Galois groups is creating
  `PowerBasis.map_conjugate`; but figuring out the exact correct assumptions + proof for this is
  mathematically nontrivial. (Current thoughts: the correct condition is that the annihilating
  ideal of both elements is equal. This may not hold in an ID, and definitely holds in an ICD.)

-/

@[expose] public section


variable {n : Nat} [NeZero n] (K : Type*) [Field K] {L : Type*} {μ : L}

open Polynomial IsCyclotomicExtension

open scoped Cyclotomic

namespace IsPrimitiveRoot

variable [CommRing L] [IsDomain L] (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

/--
theorem `autToPow_injective` / 定理 `autToPow_injective`

English:
theorem autToPow_injective
  statement: Function.Injective hμ.autToPow K
  proof: by
  intro f g hfg
  have : f.toAlgHom = g.toAlgHom := by
    apply (hμ.powerBasis K).algHom_ext
    rw [AlgEquiv.coe_toAlgHom]; rw [AlgEquiv.coe_toAlgHom]; rw [powerBasis_gen]; rw [← autToPow_spec K hμ g]; rw [← autToPow_spec K hμ f]; rw [hfg]
  exact AlgEquiv.coe_toAlgHom_injective this

中文:
定理 autToPow_injective
  结论: 函数.单射 hμ.autToPow K
  证明: by
  intro f g hfg
  have : f.toAlgHom = g.toAlgHom := by
    apply (hμ.powerBasis K).algHom_ext
    rw [AlgEquiv.coe_toAlgHom]; rw [AlgEquiv.coe_toAlgHom]; rw [powerBasis_gen]; rw [← autToPow_spec K hμ g]; rw [← autToPow_spec K hμ f]; rw [hfg]
  exact AlgEquiv.coe_toAlgHom_injective this

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom_injective, algHom_ext, autToPow_spec, coe_toAlgHom, coe_toAlgHom_injective, f.toAlgHom, g.toAlgHom, powerBasis, powerBasis_gen, toAlgHom
-/
theorem autToPow_injective : Function.Injective hμ.autToPow K := by
  intro f g hfg
  have : f.toAlgHom = g.toAlgHom := by
    apply (hμ.powerBasis K).algHom_ext
    rw [AlgEquiv.coe_toAlgHom]; rw [AlgEquiv.coe_toAlgHom]; rw [powerBasis_gen]; rw [← autToPow_spec K hμ g]; rw [← autToPow_spec K hμ f]; rw [hfg]
  exact AlgEquiv.coe_toAlgHom_injective this

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable [CommRing L] [IsDomain L] (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

variable {K} (L)

/-- The `MulEquiv` that takes an automorphism `f` to the element `k : (ZMod n)ˣ` such that
  `f μ = μ ^ k` for any root of unity `μ`. A strengthening of `IsPrimitiveRoot.autToPow`. -/
@[simps]
/--
Definition of `autEquivPow` / `autEquivPow` 的定义

English:
definition autEquivPow
  signature: (h : Irreducible (cyclotomic n K))
  body: let hζ := zeta_spec n K L
  let hμ t := hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime t)
  { (zeta_spec n K L).autToPow K with
    invFun := fun t =>
      (hζ.powerBasis K).equivOfMinpoly ((hμ t).powerBasis K)
        (by
          have := IsCyclotomicExtension.neZero' n K L
          simp only [I

中文:
定义 autEquivPow
  签名: (h : 不可约 (cyclotomic n K))
  定义体: let hζ := zeta_spec n K L
  let hμ t := hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime t)
  { (zeta_spec n K L).autToPow K with
    invFun := fun t =>
      (hζ.powerBasis K).equivOfMinpoly ((hμ t).powerBasis K)
        (by
          have := IsCyclotomicExtension.neZero' n K L
          simp only [I

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.neZero, IsPrimitiveRoot, IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible, IsPrimitiveRoot.powerBasis_gen, ZMod.val_coe_unit_coprime, autToPow, equivOfMinpoly, invFun, minpoly_eq_cyclotomic_of_irreducible, neZero, pow_of_coprime, powerBasis, powerBasis_gen, symm.trans, val_coe_unit_coprime, zeta_spec
-/
noncomputable def autEquivPow (h : Irreducible (cyclotomic n K)) : Gal(L/K) ≃* (ZMod n)ˣ :=
  let hζ := zeta_spec n K L
  let hμ t := hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime t)
  { (zeta_spec n K L).autToPow K with
    invFun := fun t =>
      (hζ.powerBasis K).equivOfMinpoly ((hμ t).powerBasis K)
        (by
          have := IsCyclotomicExtension.neZero' n K L
          simp only [IsPrimitiveRoot.powerBasis_gen]
          have hr :=
            IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
              ((zeta_spec n K L).pow_of_coprime _ (ZMod.val_coe_unit_coprime t)) h
          exact ((zeta_spec n K L).minpoly_eq_cyclotomic_of_irreducible h).symm.trans hr)
    left_inv := fun f => by
      simp only [MonoidHom.toFun_eq_coe]
      apply AlgEquiv.coe_toAlgHom_injective
      apply (hζ.powerBasis K).algHom_ext
      simp only [AlgEquiv.coe_toAlgHom]
      rw [PowerBasis.equivOfMinpoly_gen]
      simp only [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.autToPow_spec]
    right_inv := fun x => by
      simp only [MonoidHom.toFun_eq_coe]
      generalize_proofs _ h
      have key := hζ.autToPow_spec K ((hζ.powerBasis K).equivOfMinpoly ((hμ x).powerBasis K) h)
      have := (hζ.powerBasis K).equivOfMinpoly_gen ((hμ x).powerBasis K) h
      rw [hζ.powerBasis_gen K] at this
      rw [this]; rw [IsPrimitiveRoot.powerBasis_gen] at key
      nth_rw 1 5 [← hζ.val_toRootsOfUnity_coe] at key
      simp only [← rootsOfUnity.coe_pow] at key
      replace key := rootsOfUnity.coe_injective key
      rw [pow_eq_pow_iff_modEq]; rw [← Subgroup.orderOf_coe]; rw [← orderOf_units]; rw [hζ.val_toRootsOfUnity_coe]; rw [← (zeta_spec n K L).eq_orderOf]; rw [← ZMod.natCast_eq_natCast_iff] at key
      simp only [ZMod.natCast_val, ZMod.cast_id', id] at key
      exact Units.ext key }

variable (h : Irreducible (cyclotomic n K)) {L}

/--
Definition of `fromZetaAut` / `fromZetaAut` 的定义

English:
definition fromZetaAut
  signature: : Gal(L/K)
  body: let hζ := (zeta_spec n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one
(autEquivPow L h).symm
ZMod.unitOfCoprime hζ.choose
((zeta_spec n K L).pow_iff_coprime (NeZero.pos _) hζ.choose).mp hζ.choose_spec.2.symm ▸ hμ

中文:
定义 fromZetaAut
  签名: : Gal(L/K)
  定义体: let hζ := (zeta_spec n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one
(autEquivPow L h).symm
ZMod.unitOfCoprime hζ.choose
((zeta_spec n K L).pow_iff_coprime (NeZero.pos _) hζ.choose).mp hζ.choose_spec.2.symm ▸ hμ

Depends on / 依赖: NeZero, NeZero.pos, ZMod.unitOfCoprime, autEquivPow, choose_spec, eq_pow_of_pow_eq_one, pow_eq_one, pow_iff_coprime, unitOfCoprime, zeta_spec
-/
noncomputable def fromZetaAut : Gal(L/K) :=
  let hζ := (zeta_spec n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one
(autEquivPow L h).symm
ZMod.unitOfCoprime hζ.choose
((zeta_spec n K L).pow_iff_coprime (NeZero.pos _) hζ.choose).mp hζ.choose_spec.2.symm ▸ hμ

/--
theorem `fromZetaAut_spec` / 定理 `fromZetaAut_spec`

English:
theorem fromZetaAut_spec
  statement: fromZetaAut hμ h (zeta n K L) = μ
  proof: by
  simp_rw [fromZetaAut, autEquivPow_symm_apply]
  generalize_proofs hζ h _ hμ _
  nth_rewrite 4 [← hζ.powerBasis_gen K]
  rw [PowerBasis.equivOfMinpoly_gen]; rw [hμ.powerBasis_gen K]
  convert! h.choose_spec.2
  exact ZMod.val_cast_of_lt h.choose_spec.1

中文:
定理 fromZetaAut_spec
  结论: fromZetaAut hμ h (zeta n K L) = μ
  证明: by
  simp_rw [fromZetaAut, autEquivPow_symm_apply]
  generalize_proofs hζ h _ hμ _
  nth_rewrite 4 [← hζ.powerBasis_gen K]
  rw [PowerBasis.equivOfMinpoly_gen]; rw [hμ.powerBasis_gen K]
  convert! h.choose_spec.2
  exact ZMod.val_cast_of_lt h.choose_spec.1

Depends on / 依赖: PowerBasis, PowerBasis.equivOfMinpoly_gen, ZMod.val_cast_of_lt, autEquivPow_symm_apply, choose_spec, convert, equivOfMinpoly_gen, fromZetaAut, generalize_proofs, h.choose_spec, nth_rewrite, powerBasis_gen, simp_rw, val_cast_of_lt
-/
theorem fromZetaAut_spec : fromZetaAut hμ h (zeta n K L) = μ := by
  simp_rw [fromZetaAut, autEquivPow_symm_apply]
  generalize_proofs hζ h _ hμ _
  nth_rewrite 4 [← hζ.powerBasis_gen K]
  rw [PowerBasis.equivOfMinpoly_gen]; rw [hμ.powerBasis_gen K]
  convert! h.choose_spec.2
  exact ZMod.val_cast_of_lt h.choose_spec.1

end IsCyclotomicExtension

section Gal

variable [Field L] [Algebra K L] [IsCyclotomicExtension {n} K L]
  (h : Irreducible (cyclotomic n K)) {K}

/--
Definition of `galCyclotomicEquivUnitsZMod` / `galCyclotomicEquivUnitsZMod` 的定义

English:
definition galCyclotomicEquivUnitsZMod
  signature: : (cyclotomic n K).Gal ≃* (ZMod n)ˣ
  body: (AlgEquiv.autCongr
          (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (cyclotomic n K).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

中文:
定义 galCyclotomicEquivUnitsZMod
  签名: : (cyclotomic n K).Gal ≃* (ZMod n)ˣ
  定义体: (AlgEquiv.autCongr
          (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (cyclotomic n K).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

Depends on / 依赖: AlgEquiv, AlgEquiv.autCongr, IsCyclotomicExtension, IsCyclotomicExtension.autEquivPow, IsSplittingField, IsSplittingField.algEquiv, SplittingField, algEquiv, autCongr, autEquivPow, cyclotomic, symm.trans
-/
noncomputable def galCyclotomicEquivUnitsZMod : (cyclotomic n K).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
          (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (cyclotomic n K).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

/--
Definition of `galXPowEquivUnitsZMod` / `galXPowEquivUnitsZMod` 的定义

English:
definition galXPowEquivUnitsZMod
  signature: : (X ^ n - 1 : K[X]).Gal ≃* (ZMod n)ˣ
  body: (AlgEquiv.autCongr
      (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (X ^ n - 1 : K[X]).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

中文:
定义 galXPowEquivUnitsZMod
  签名: : (X ^ n - 1 : K[X]).Gal ≃* (ZMod n)ˣ
  定义体: (AlgEquiv.autCongr
      (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (X ^ n - 1 : K[X]).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

Depends on / 依赖: AlgEquiv, AlgEquiv.autCongr, IsCyclotomicExtension, IsCyclotomicExtension.autEquivPow, IsSplittingField, IsSplittingField.algEquiv, SplittingField, algEquiv, autCongr, autEquivPow, symm.trans
-/
noncomputable def galXPowEquivUnitsZMod : (X ^ n - 1 : K[X]).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
      (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (X ^ n - 1 : K[X]).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

end Gal
