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


variable {n : ℕ} [NeZero n] (K : Type*) [Field K] {L : Type*} {μ : L}

open Polynomial IsCyclotomicExtension

open scoped Cyclotomic

namespace IsPrimitiveRoot

variable [CommRing L] [IsDomain L] (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

/-- `IsPrimitiveRoot.autToPow` is injective in the case that it's considered over a cyclotomic
field extension. -/
/-
**IsPrimitiveRoot.autToPow_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`
。
形式化陈述：autToPow_injective : Function.Injective hμ.autToPow K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerBasis.algHom_ext`：algHom_ext {S' : Type*} [Semiring S'] [Algebra R 
S'] (pb : PowerBasis R S) ⦃f g : S ->ₐ[R] S'⦄ (h : f pb.gen = g pb.gen) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.coe_toAlgHom`：coe_toAlgHom : DFunLike.coe e.toAlgHom = e
· 使用定理 `IsPrimitiveRoot.powerBasis_gen`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.autToPow_spec`：autToPow_spec [NeZero n] (f : S ≃ₐ[R] S) 
: μ ^ (hμ.autToPow R f : ZMod n).val = f μ
· 使用定理 `AlgEquiv.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.Injec
tive ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ->ₐ[R] A₂)

--- 原说明 ---
`IsPrimitiveRoot.autToPow` is injective in the case that it's considered over a 
cyclotomic
field extension.
-/
theorem autToPow_injective : Function.Injective <| hμ.autToPow K := by
  intro f g hfg
  have : f.toAlgHom = g.toAlgHom := by
    apply (hμ.powerBasis K).algHom_ext
    rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, powerBasis_gen,
      ← autToPow_spec K hμ g, ← autToPow_spec K hμ f, hfg]
  exact AlgEquiv.coe_toAlgHom_injective this

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable [CommRing L] [IsDomain L] (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

variable {K} (L)

/-- The `MulEquiv` that takes an automorphism `f` to the element `k : (ZMod n)ˣ` such that
  `f μ = μ ^ k` for any root of unity `μ`. A strengthening of `IsPrimitiveRoot.autToPow`. -/
@[simps]
/-
**IsCyclotomicExtension.autEquivPow** 是 Mathlib 中的一个定义，位于命名空间 `IsCyclotomicExten
sion`。
形式化陈述：autEquivPow (h : Irreducible (cyclotomic n K)) : Gal(L/K) ≃* (ZMod n)ˣ
参数：h : Irreducible (cyclotomic n K)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MulEquiv` that takes an automorphism `f` to the element `k : (ZMod n)ˣ` suc
h that
  `f μ = μ ^ k` for any root of unity `μ`. A strengthening of `IsPrimitiveRoot.a
utToPow`.
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
      rw [this, IsPrimitiveRoot.powerBasis_gen] at key
      nth_rw 1 5 [← hζ.val_toRootsOfUnity_coe] at key
      simp only [← rootsOfUnity.coe_pow] at key
      replace key := rootsOfUnity.coe_injective key
      rw [pow_eq_pow_iff_modEq, ← Subgroup.orderOf_coe, ← orderOf_units, hζ.val_toRootsOfUnity_coe,
        ← (zeta_spec n K L).eq_orderOf, ← ZMod.natCast_eq_natCast_iff] at key
      simp only [ZMod.natCast_val, ZMod.cast_id', id] at key
      exact Units.ext key }

variable (h : Irreducible (cyclotomic n K)) {L}

/-- Maps `μ` to the `AlgEquiv` that sends `IsCyclotomicExtension.zeta` to `μ`. -/
/-
**IsCyclotomicExtension.fromZetaAut** 是 Mathlib 中的一个定义，位于命名空间 `IsCyclotomicExten
sion`。
形式化陈述：fromZetaAut : Gal(L/K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps `μ` to the `AlgEquiv` that sends `IsCyclotomicExtension.zeta` to `μ`.
-/
noncomputable def fromZetaAut : Gal(L/K) :=
  let hζ := (zeta_spec n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one
  (autEquivPow L h).symm <|
    ZMod.unitOfCoprime hζ.choose <|
      ((zeta_spec n K L).pow_iff_coprime (NeZero.pos _) hζ.choose).mp <| hζ.choose_spec.2.symm ▸ hμ
/-
**IsCyclotomicExtension.fromZetaAut_spec** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomic
Extension`。
形式化陈述：fromZetaAut_spec : fromZetaAut hμ h (zeta n K L) = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.autEquivPow_symm_apply`：∀ {n : ℕ} [inst : NeZero n
] {K : Type u_1} [inst_1 : Field K] (L : Type u_2) [inst_2 : CommRing L] [inst_3
 : IsDomain L]   [inst_4 : Algebra…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.powerBasis_gen`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `PowerBasis.equivOfMinpoly_gen`：equivOfMinpoly_gen (pb : PowerBasis A S) 
(pb' : PowerBasis A S') (h : minpoly A pb.gen = minpoly A pb'.gen) : pb.equivOfM
inpoly pb' h pb.gen…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ZMod.val_cast_of_lt`：val_cast_of_lt {n : Nat} {a : Nat} (h : a < n) : (a
 : ZMod n).val = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem fromZetaAut_spec : fromZetaAut hμ h (zeta n K L) = μ := by
  simp_rw [fromZetaAut, autEquivPow_symm_apply]
  generalize_proofs hζ h _ hμ _
  nth_rewrite 4 [← hζ.powerBasis_gen K]
  rw [PowerBasis.equivOfMinpoly_gen, hμ.powerBasis_gen K]
  convert! h.choose_spec.2
  exact ZMod.val_cast_of_lt h.choose_spec.1

end IsCyclotomicExtension

section Gal

variable [Field L] [Algebra K L] [IsCyclotomicExtension {n} K L]
  (h : Irreducible (cyclotomic n K)) {K}

/-- `IsCyclotomicExtension.autEquivPow` repackaged in terms of `Gal`.
Asserts that the Galois group of `cyclotomic n K` is equivalent to `(ZMod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
/-
**galCyclotomicEquivUnitsZMod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：galCyclotomicEquivUnitsZMod : (cyclotomic n K).Gal ≃* (ZMod n)ˣ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.splitting_field_cyclotomic`：splitting_field_cyclot
omic : IsSplittingField K L (cyclotomic n K)

--- 原说明 ---
`IsCyclotomicExtension.autEquivPow` repackaged in terms of `Gal`.
Asserts that the Galois group of `cyclotomic n K` is equivalent to `(ZMod n)ˣ`
if `cyclotomic n K` is irreducible in the base field.
-/
noncomputable def galCyclotomicEquivUnitsZMod : (cyclotomic n K).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
          (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (cyclotomic n K).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

/-- `IsCyclotomicExtension.autEquivPow` repackaged in terms of `Gal`.
Asserts that the Galois group of `X ^ n - 1` is equivalent to `(ZMod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
/-
**galXPowEquivUnitsZMod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：galXPowEquivUnitsZMod : (X ^ n - 1 : K[X]).Gal ≃* (ZMod n)ˣ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.isSplittingField_X_pow_sub_one`：isSplittingField_X
_pow_sub_one : IsSplittingField K L (X ^ n - 1)

--- 原说明 ---
`IsCyclotomicExtension.autEquivPow` repackaged in terms of `Gal`.
Asserts that the Galois group of `X ^ n - 1` is equivalent to `(ZMod n)ˣ`
if `cyclotomic n K` is irreducible in the base field.
-/
noncomputable def galXPowEquivUnitsZMod : (X ^ n - 1 : K[X]).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
      (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (X ^ n - 1 : K[X]).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

end Gal

