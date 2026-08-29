/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`SMul`, `MulAction`, `DistribMulAction`, `Module`, `Algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite-dimensional complex vector space is a finite-dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines bundled versions of four standard maps (respectively, the real part, the imaginary
part, the embedding of `ℝ` in `ℂ`, and the complex conjugate):

* `Complex.reLm` (`ℝ`-linear map);
* `Complex.imLm` (`ℝ`-linear map);
* `Complex.ofRealAm` (`ℝ`-algebra (homo)morphism);
* `Complex.conjAe` (`ℝ`-algebra equivalence).

It also provides a universal property of the complex numbers `Complex.lift`, which constructs a
`ℂ →ₐ[ℝ] A` into any `ℝ`-algebra `A` given a square root of `-1`.

In addition, this file provides a decomposition into `realPart` and `imaginaryPart` for any
element of a `StarModule` over `ℂ`.

## Notation

* `ℜ` and `ℑ` for the `realPart` and `imaginaryPart`, respectively, in the locale
  `ComplexStarModule`.
-/

@[expose] public section

assert_not_exists NNReal
namespace Complex

open ComplexConjugate

open scoped Complex.SMul

variable {R : Type*} {S : Type*}

attribute [local ext] Complex.ext


/- The priority of the following instances has been manually lowered, as when they don't apply
they lead Lean to a very costly path, and most often they don't apply (most actions on `ℂ` don't
come from actions on `ℝ`). See https://github.com/leanprover-community/mathlib4/pull/11980 -/

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [SMul R Real] [SMul S Real] [SMulCommClass R S Real] : SMulCommClass R S Complex where
  smul_comm r s x := by ext <;> simp [smul_re, smul_im, smul_comm]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [SMul R S] [SMul R Real] [SMul S Real] [IsScalarTower R S Real] :
    IsScalarTower R S Complex where
  smul_assoc r s x := by ext <;> simp [smul_re, smul_im, smul_assoc]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [SMul R Real] [SMul Rᵐᵒᵖ Real] [IsCentralScalar R Real] :
    IsCentralScalar R Complex where
  op_smul_eq_smul r x := by ext <;> simp [smul_re, smul_im, op_smul_eq_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) mulAction [Monoid R] [MulAction R Real] : MulAction R Complex where
  one_smul x := by ext <;> simp [smul_re, smul_im, one_smul]
  mul_smul r s x := by ext <;> simp [smul_re, smul_im, mul_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) distribSMul [DistribSMul R Real] : DistribSMul R Complex where
  smul_add r x y := by ext <;> simp [smul_re, smul_im, smul_add]
  smul_zero r := by ext <;> simp [smul_re, smul_im, smul_zero]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 90) [Semiring R] [DistribMulAction R Real] : DistribMulAction R Complex :=
  { Complex.distribSMul, Complex.mulAction with }

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 100) instModule [Semiring R] [Module R Real] : Module R Complex where
  add_smul r s x := by ext <;> simp [smul_re, smul_im, add_smul]
  zero_smul r := by ext <;> simp [smul_re, smul_im, zero_smul]

-- priority manually adjusted in https://github.com/leanprover-community/mathlib4/pull/11980
instance (priority := 95) instAlgebraOfReal [CommSemiring R] [Algebra R Real] : Algebra R Complex where
  algebraMap := Complex.ofRealHom.comp (algebraMap R Real)
  smul_def' := fun r x => by ext <;> simp [smul_re, smul_im, Algebra.smul_def]
  commutes' := fun r ⟨xr, xi⟩ => by ext <;> simp [Algebra.commutes]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarModule Real Complex
  body: ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_ofReal]⟩

@[simp]

中文:
实例 :
  签名: StarModule 实数 Complex
  定义体: ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_ofReal]⟩

@[simp]

Depends on / 依赖: conj_ofReal, map_mul, real_smul, star_def, star_trivial
-/
instance : StarModule Real Complex :=
  ⟨fun r x => by simp only [star_def, star_trivial, real_smul, map_mul, conj_ofReal]⟩

@[simp]
/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  statement: (algebraMap Real Complex : Real -> Complex) = ((↑) : Real -> Complex)
  proof: rfl

example : (Semiring.toNatAlgebra : Algebra Nat Complex) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl

example : (Ring.toIntAlgebra Complex : Algebra Int Complex) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl

example : Module.restrictScalars Real C

中文:
定理 coe_algebraMap
  结论: (algebraMap 实数 Complex : 实数 -> Complex) = ((↑) : 实数 -> Complex)
  证明: rfl

example : (Semiring.toNatAlgebra : Algebra Nat Complex) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl

example : (Ring.toIntAlgebra Complex : Algebra Int Complex) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl

example : Module.restrictScalars Real C
-/
theorem coe_algebraMap : (algebraMap Real Complex : Real -> Complex) = ((↑) : Real -> Complex) :=
  rfl

example : (Semiring.toNatAlgebra : Algebra Nat Complex) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl

example : (Ring.toIntAlgebra Complex : Algebra Int Complex) = Complex.instAlgebraOfReal := by
  with_reducible_and_instances rfl

example : Module.restrictScalars Real Complex Complex = Complex.instModule := by
  with_reducible_and_instances rfl

section

variable {A : Type*} [Semiring A] [Algebra Real A]

/-- We need this lemma since `Complex.coe_algebraMap` diverts the simp-normal form away from
`AlgHom.commutes`. -/
@[simp]
/--
theorem `_root_.AlgHom.map_coe_real_complex` / 定理 `_root_.AlgHom.map_coe_real_complex`

English:
theorem _root_.AlgHom.map_coe_real_complex
  given: (f : Complex ->ₐ[Real] A) (x : Real)
  statement: f x = algebraMap Real A x
  proof: f.commutes x

中文:
定理 _root_.AlgHom.map_coe_real_complex
  条件: (f : Complex ->ₐ[实数] A) (x : 实数)
  结论: f x = algebraMap 实数 A x
  证明: f.commutes x

Depends on / 依赖: commutes, f.commutes
-/
theorem _root_.AlgHom.map_coe_real_complex (f : Complex ->ₐ[Real] A) (x : Real) : f x = algebraMap Real A x :=
  f.commutes x

/-- Two `ℝ`-algebra homomorphisms from `ℂ` are equal if they agree on `Complex.I`. -/
@[ext]
/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  given: ⦃f g
  statement: Complex ->ₐ[Real] A⦄ (h : f I = g I) : f = g
  proof: by
  ext ⟨x, y⟩
  simp only [mk_eq_add_mul_I, map_add, AlgHom.map_coe_real_complex, map_mul, h]

中文:
定理 algHom_ext
  条件: ⦃f g
  结论: Complex ->ₐ[实数] A⦄ (h : f I = g I) : f = g
  证明: by
  ext ⟨x, y⟩
  simp only [mk_eq_add_mul_I, map_add, AlgHom.map_coe_real_complex, map_mul, h]

Depends on / 依赖: AlgHom, AlgHom.map_coe_real_complex, map_add, map_coe_real_complex, map_mul, mk_eq_add_mul_I
-/
theorem algHom_ext ⦃f g : Complex ->ₐ[Real] A⦄ (h : f I = g I) : f = g := by
  ext ⟨x, y⟩
  simp only [mk_eq_add_mul_I, map_add, AlgHom.map_coe_real_complex, map_mul, h]

end

open Module Submodule

/--
Definition of `basisOneI` / `basisOneI` 的定义

English:
definition basisOneI
  signature: : Basis (Fin 2) Real Complex
  body: .ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
      right_inv := fun c => by
        ext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      map_smul' := fun c z => by simp }

@[simp]

中文:
定义 basisOneI
  签名: : Basis (Fin 2) 实数 Complex
  定义体: .ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
      right_inv := fun c => by
        ext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      map_smul' := fun c z => by simp }

@[simp]

Depends on / 依赖: fin_cases, invFun, left_inv, map_add, map_smul, ofEquivFun, right_inv, z.im, z.re
-/
noncomputable def basisOneI : Basis (Fin 2) Real Complex :=
  .ofEquivFun
    { toFun := fun z => ![z.re, z.im]
      invFun := fun c => c 0 + c 1 • I
      left_inv := fun z => by simp
      right_inv := fun c => by
        ext i
        fin_cases i <;> simp
      map_add' := fun z z' => by simp
      map_smul' := fun c z => by simp }

@[simp]
/--
theorem `coe_basisOneI_repr` / 定理 `coe_basisOneI_repr`

English:
theorem coe_basisOneI_repr
  given: (z : Complex)
  statement: ⇑(basisOneI.repr z) = ![z.re, z.im]
  proof: rfl

@[simp]

中文:
定理 coe_basisOneI_repr
  条件: (z : Complex)
  结论: ⇑(basisOneI.repr z) = ![z.re, z.im]
  证明: rfl

@[simp]
-/
theorem coe_basisOneI_repr (z : Complex) : ⇑(basisOneI.repr z) = ![z.re, z.im] :=
  rfl

@[simp]
/--
theorem `coe_basisOneI` / 定理 `coe_basisOneI`

English:
theorem coe_basisOneI
  statement: ⇑basisOneI = ![1, I]
  proof: funext fun i =>
Basis.apply_eq_iff.mpr
      Finsupp.ext fun j => by
        fin_cases i <;> fin_cases j <;> simp

中文:
定理 coe_basisOneI
  结论: ⇑basisOneI = ![1, I]
  证明: funext fun i =>
Basis.apply_eq_iff.mpr
      Finsupp.ext fun j => by
        fin_cases i <;> fin_cases j <;> simp

Depends on / 依赖: Basis.apply_eq_iff.mpr, Finsupp, Finsupp.ext, apply_eq_iff, fin_cases
-/
theorem coe_basisOneI : ⇑basisOneI = ![1, I] :=
  funext fun i =>
Basis.apply_eq_iff.mpr
      Finsupp.ext fun j => by
        fin_cases i <;> fin_cases j <;> simp

end Complex

/-- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance (priority := 900) Module.complexToReal (E : Type*) [AddCommGroup E] [Module Complex E] :
    Module Real E :=
  .restrictScalars Real Complex E

/-- Register as an instance (with low priority) the fact that a complex algebra is also a real
algebra. -/
instance (priority := 900) Algebra.complexToReal {A : Type*} [Semiring A] [Algebra Complex A] :
    Algebra Real A :=
  .restrictScalars Real Complex A

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
example : Prod.algebra Real Complex Complex = (Prod.algebra Complex Complex Complex).complexToReal := rfl

-- try to make sure we're not introducing diamonds but we will need
-- `reducible_and_instances` which currently fails https://github.com/leanprover-community/mathlib4/issues/10906
example {ι : Type*} [Fintype ι] :
    Pi.algebra (R := Real) ι (fun _ => Complex) = (Pi.algebra (R := Complex) ι (fun _ => Complex)).complexToReal :=
  rfl

example {A : Type*} [Ring A] [inst : Algebra Complex A] :
    (inst.complexToReal).toModule = (inst.toModule).complexToReal := by
  with_reducible_and_instances rfl

@[simp, norm_cast]
/--
theorem `Complex.coe_smul` / 定理 `Complex.coe_smul`

English:
theorem Complex.coe_smul
  given: {E : Type*} [AddCommGroup E] [Module Complex E] (x : Real) (y : E)
  proof: rfl

中文:
定理 Complex.coe_smul
  条件: {E : 类型} [AddCommGroup E] [Module Complex E] (x : 实数) (y : E)
  证明: rfl
-/
theorem Complex.coe_smul {E : Type*} [AddCommGroup E] [Module Complex E] (x : Real) (y : E) :
    (x : Complex) • y = x • y :=
  rfl

/-- The scalar action of `ℝ` on a `ℂ`-module `E` induced by `Module.complexToReal` commutes with
another scalar action of `M` on `E` whenever the action of `ℂ` commutes with the action of `M`. -/
instance (priority := 900) SMulCommClass.complexToReal {M E : Type*} [AddCommGroup E] [Module Complex E]
    [SMul M E] [SMulCommClass Complex M E] : SMulCommClass Real M E where
  smul_comm r _ _ := smul_comm (r : Complex) _ _

/--
Instance `IsScalarTower.complexToReal` / 实例 `IsScalarTower.complexToReal`

English:
instance IsScalarTower.complexToReal
  signature: {M E : Type*} [AddCommGroup M] [Module Complex M] [AddCommGroup E]
  body: smul_assoc (r : Complex) _ _

中文:
实例 IsScalarTower.complexToReal
  签名: {M E : 类型} [AddCommGroup M] [Module Complex M] [AddCommGroup E]
  定义体: smul_assoc (r : Complex) _ _

Depends on / 依赖: smul_assoc
-/
instance IsScalarTower.complexToReal {M E : Type*} [AddCommGroup M] [Module Complex M] [AddCommGroup E]
    [Module Complex E] [SMul M E] [IsScalarTower Complex M E] : IsScalarTower Real M E where
  smul_assoc r _ _ := smul_assoc (r : Complex) _ _

-- check that the following instance is implied by the one above.
example (E : Type*) [AddCommGroup E] [Module Complex E] : IsScalarTower Real Complex E := inferInstance

instance (priority := 900) StarModule.complexToReal {E : Type*} [AddCommGroup E] [Star E]
    [Module Complex E] [StarModule Complex E] : StarModule Real E :=
  ⟨fun r a => by rw [← smul_one_smul Complex r a, star_smul, star_smul, star_one, smul_one_smul]⟩

namespace Complex

open ComplexConjugate

/--
Definition of `reLm` / `reLm` 的定义

English:
definition reLm
  signature: : Complex ->ₗ[Real] Real where
  body: x.re
  map_add' := add_re
  map_smul' := by simp

@[simp]

中文:
定义 reLm
  签名: : Complex ->ₗ[实数] 实数 where
  定义体: x.re
  map_add' := add_re
  map_smul' := by simp

@[simp]

Depends on / 依赖: x.re
-/
def reLm : Complex ->ₗ[Real] Real where
  toFun x := x.re
  map_add' := add_re
  map_smul' := by simp

@[simp]
/--
theorem `reLm_coe` / 定理 `reLm_coe`

English:
theorem reLm_coe
  statement: ⇑reLm = re
  proof: rfl

中文:
定理 reLm_coe
  结论: ⇑reLm = re
  证明: rfl
-/
theorem reLm_coe : ⇑reLm = re :=
  rfl

/--
Definition of `imLm` / `imLm` 的定义

English:
definition imLm
  signature: : Complex ->ₗ[Real] Real where
  body: x.im
  map_add' := add_im
  map_smul' := by simp

@[simp]

中文:
定义 imLm
  签名: : Complex ->ₗ[实数] 实数 where
  定义体: x.im
  map_add' := add_im
  map_smul' := by simp

@[simp]

Depends on / 依赖: x.im
-/
def imLm : Complex ->ₗ[Real] Real where
  toFun x := x.im
  map_add' := add_im
  map_smul' := by simp

@[simp]
/--
theorem `imLm_coe` / 定理 `imLm_coe`

English:
theorem imLm_coe
  statement: ⇑imLm = im
  proof: rfl

中文:
定理 imLm_coe
  结论: ⇑imLm = im
  证明: rfl
-/
theorem imLm_coe : ⇑imLm = im :=
  rfl

/--
Definition of `ofRealAm` / `ofRealAm` 的定义

English:
definition ofRealAm
  signature: : Real ->ₐ[Real] Complex
  body: Algebra.ofId Real Complex

@[simp]

中文:
定义 ofRealAm
  签名: : 实数 ->ₐ[实数] Complex
  定义体: Algebra.ofId Real Complex

@[simp]

Depends on / 依赖: Algebra, Algebra.ofId
-/
def ofRealAm : Real ->ₐ[Real] Complex :=
  Algebra.ofId Real Complex

@[simp]
/--
theorem `ofRealAm_coe` / 定理 `ofRealAm_coe`

English:
theorem ofRealAm_coe
  statement: ⇑ofRealAm = ((↑) : Real -> Complex)
  proof: rfl

中文:
定理 ofRealAm_coe
  结论: ⇑of实数Am = ((↑) : 实数 -> Complex)
  证明: rfl
-/
theorem ofRealAm_coe : ⇑ofRealAm = ((↑) : Real -> Complex) :=
  rfl

/--
Definition of `conjAe` / `conjAe` 的定义

English:
definition conjAe
  signature: : Complex ≃ₐ[Real] Complex
  body: { conj with
    invFun := conj
    left_inv := star_star
    right_inv := star_star
    commutes' := conj_ofReal }

@[simp]

中文:
定义 conjAe
  签名: : Complex ≃ₐ[实数] Complex
  定义体: { conj with
    invFun := conj
    left_inv := star_star
    right_inv := star_star
    commutes' := conj_ofReal }

@[simp]

Depends on / 依赖: commutes, conj_ofReal, invFun, left_inv, right_inv, star_star
-/
def conjAe : Complex ≃ₐ[Real] Complex :=
  { conj with
    invFun := conj
    left_inv := star_star
    right_inv := star_star
    commutes' := conj_ofReal }

@[simp]
/--
theorem `conjAe_coe` / 定理 `conjAe_coe`

English:
theorem conjAe_coe
  statement: ⇑conjAe = conj
  proof: rfl

中文:
定理 conjAe_coe
  结论: ⇑conjAe = conj
  证明: rfl
-/
theorem conjAe_coe : ⇑conjAe = conj :=
  rfl

/-- The matrix representation of `conjAe`. -/
@[simp]
/--
theorem `toMatrix_conjAe` / 定理 `toMatrix_conjAe`

English:
theorem toMatrix_conjAe
  proof: by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

中文:
定理 toMatrix_conjAe
  证明: by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_apply, fin_cases, toMatrix_apply
-/
theorem toMatrix_conjAe :
    conjAe.toLinearEquiv.toLinearMap.toMatrix basisOneI basisOneI = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]

/--
theorem `real_algHom_eq_id_or_conj` / 定理 `real_algHom_eq_id_or_conj`

English:
theorem real_algHom_eq_id_or_conj
  given: (f : Complex ->ₐ[Real] Complex)
  statement: f = AlgHom.id Real Complex ∨ f = conjAe
  proof: by
  refine
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp ?_ ?_ <;>
    refine fun h => algHom_ext ?_
  exacts [h, conj_I.symm ▸ h]

中文:
定理 real_algHom_eq_id_or_conj
  条件: (f : Complex ->ₐ[实数] Complex)
  结论: f = AlgHom.id 实数 Complex ∨ f = conjAe
  证明: by
  refine
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp ?_ ?_ <;>
    refine fun h => algHom_ext ?_
  exacts [h, conj_I.symm ▸ h]

Depends on / 依赖: I_sq, algHom_ext, conj_I, conj_I.symm, eq_or_eq_neg_of_sq_eq_sq, exacts, map_neg, map_one, map_pow
-/
theorem real_algHom_eq_id_or_conj (f : Complex ->ₐ[Real] Complex) : f = AlgHom.id Real Complex ∨ f = conjAe := by
  refine
      (eq_or_eq_neg_of_sq_eq_sq (f I) I <| by rw [← map_pow, I_sq, map_neg, map_one]).imp ?_ ?_ <;>
    refine fun h => algHom_ext ?_
  exacts [h, conj_I.symm ▸ h]

/-- The natural `LinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
/--
Definition of `equivRealProdLm` / `equivRealProdLm` 的定义

English:
definition equivRealProdLm
  signature: : Complex ≃ₗ[Real] Real × Real
  body: { equivRealProdAddHom with
    map_smul' := fun r c => by simp }

中文:
定义 equivRealProdLm
  签名: : Complex ≃ₗ[实数] 实数 × 实数
  定义体: { equivRealProdAddHom with
    map_smul' := fun r c => by simp }

Depends on / 依赖: equivRealProdAddHom, map_smul
-/
def equivRealProdLm : Complex ≃ₗ[Real] Real × Real :=
  { equivRealProdAddHom with
    map_smul' := fun r c => by simp }

/--
theorem `equivRealProdLm_symm_apply` / 定理 `equivRealProdLm_symm_apply`

English:
theorem equivRealProdLm_symm_apply
  given: (p : Real × Real)
  proof: Complex.equivRealProd_symm_apply p

中文:
定理 equivRealProdLm_symm_apply
  条件: (p : 实数 × 实数)
  证明: Complex.equivRealProd_symm_apply p

Depends on / 依赖: Complex.equivRealProd_symm_apply, equivRealProd_symm_apply
-/
theorem equivRealProdLm_symm_apply (p : Real × Real) :
    Complex.equivRealProdLm.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

section lift

variable {A : Type*} [Ring A] [Algebra Real A]

open Algebra

/--
Definition of `liftAux` / `liftAux` 的定义

English:
definition liftAux
  signature: (I' : A) (hf : I' * I' = -1)
  body: AlgHom.ofLinearMap
    ((Algebra.linearMap Real A).comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap Real A 1 + (0 : Real) • I' = 1 by rw [map_one, zero_smul, add_zero]) ?_

中文:
定义 liftAux
  签名: (I' : A) (hf : I' * I' = -1)
  定义体: AlgHom.ofLinearMap
    ((Algebra.linearMap Real A).comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap Real A 1 + (0 : Real) • I' = 1 by rw [map_one, zero_smul, add_zero]) ?_

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, Algebra, Algebra.linearMap, LinearMap, LinearMap.toSpanSingleton, add_zero, algebraMap, linearMap, map_one, ofLinearMap, toSpanSingleton, zero_smul
-/
def liftAux (I' : A) (hf : I' * I' = -1) : Complex ->ₐ[Real] A :=
  AlgHom.ofLinearMap
    ((Algebra.linearMap Real A).comp reLm + (LinearMap.toSpanSingleton _ _ I').comp imLm)
    (show algebraMap Real A 1 + (0 : Real) • I' = 1 by rw [map_one, zero_smul, add_zero]) ?_
where finally
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
  rw [mk_mul_mk]
  change
    algebraMap Real A (x₁ * x₂ - y₁ * y₂) + (x₁ * y₂ + y₁ * x₂) • I' =
      (algebraMap Real A x₁ + y₁ • I') * (algebraMap Real A x₂ + y₂ • I')
  rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [add_comm _ (y₁ • I' * y₂ • I')]; rw [add_add_add_comm]
  congr 1
  -- equate "real" and "imaginary" parts
  · rw [smul_mul_smul_comm, hf, smul_neg, ← algebraMap_eq_smul_one, ← sub_eq_add_neg,
      ← map_mul, ← map_sub]
  · rw [smul_def, smul_def, smul_def, ← right_comm _ x₂,
      ← mul_assoc, ← add_mul, ← map_mul, ← map_mul, ← map_add]

@[simp]
/--
theorem `liftAux_apply` / 定理 `liftAux_apply`

English:
theorem liftAux_apply
  given: (I' : A) (hI') (z : Complex)
  statement: liftAux I' hI' z = algebraMap Real A z.re + z.im • I'
  proof: rfl

中文:
定理 liftAux_apply
  条件: (I' : A) (hI') (z : Complex)
  结论: liftAux I' hI' z = algebraMap 实数 A z.re + z.im • I'
  证明: rfl
-/
theorem liftAux_apply (I' : A) (hI') (z : Complex) : liftAux I' hI' z = algebraMap Real A z.re + z.im • I' :=
  rfl

/--
theorem `liftAux_apply_I` / 定理 `liftAux_apply_I`

English:
theorem liftAux_apply_I
  given: (I' : A) (hI')
  statement: liftAux I' hI' I = I'
  proof: by simp

@[simp]

中文:
定理 liftAux_apply_I
  条件: (I' : A) (hI')
  结论: liftAux I' hI' I = I'
  证明: by simp

@[simp]
-/
theorem liftAux_apply_I (I' : A) (hI') : liftAux I' hI' I = I' := by simp

@[simp]
/--
theorem `adjoin_I` / 定理 `adjoin_I`

English:
theorem adjoin_I
  statement: Real[I] = ⊤
  proof: by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.re_add_im]; rw [← smul_eq_mul]; rw [← Complex.coe_algebraMap]
  exact add_mem (algebraMap_mem _ _) (Subalgebra.smul_mem _ (subset_adjoin <| by simp) _)

@[simp]

中文:
定理 adjoin_I
  结论: 实数[I] = ⊤
  证明: by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.re_add_im]; rw [← smul_eq_mul]; rw [← Complex.coe_algebraMap]
  exact add_mem (algebraMap_mem _ _) (Subalgebra.smul_mem _ (subset_adjoin <| by simp) _)

@[simp]

Depends on / 依赖: Complex.coe_algebraMap, Subalgebra, Subalgebra.smul_mem, add_mem, algebraMap_mem, coe_algebraMap, re_add_im, smul_eq_mul, smul_mem, subset_adjoin, top_unique, x.re_add_im
-/
theorem adjoin_I : Real[I] = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.re_add_im]; rw [← smul_eq_mul]; rw [← Complex.coe_algebraMap]
  exact add_mem (algebraMap_mem _ _) (Subalgebra.smul_mem _ (subset_adjoin <| by simp) _)

@[simp]
/--
theorem `range_liftAux` / 定理 `range_liftAux`

English:
theorem range_liftAux
  given: (I' : A) (hI')
  statement: (liftAux I' hI').range = Real[I']
  proof: by
  simp_rw [← Algebra.map_top, ← adjoin_I, AlgHom.map_adjoin, Set.image_singleton, liftAux_apply_I]

中文:
定理 range_liftAux
  条件: (I' : A) (hI')
  结论: (liftAux I' hI').range = 实数[I']
  证明: by
  simp_rw [← Algebra.map_top, ← adjoin_I, AlgHom.map_adjoin, Set.image_singleton, liftAux_apply_I]

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, Algebra, Algebra.map_top, Set.image_singleton, adjoin_I, image_singleton, liftAux_apply_I, map_adjoin, map_top, simp_rw
-/
theorem range_liftAux (I' : A) (hI') : (liftAux I' hI').range = Real[I'] := by
  simp_rw [← Algebra.map_top, ← adjoin_I, AlgHom.map_adjoin, Set.image_singleton, liftAux_apply_I]

/-- A universal property of the complex numbers, providing a unique `ℂ →ₐ[ℝ] A` for every element
of `A` which squares to `-1`.

This can be used to embed the complex numbers in the `Quaternion`s.

This isomorphism is named to match the very similar `Zsqrtd.lift`. -/
@[simps +simpRhs]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : { I' : A // I' * I' = -1 } ≃ (Complex ->ₐ[Real] A) where
  body: liftAux I' I'.prop
  invFun F := ⟨F I, by rw [← map_mul, I_mul_I, map_neg, map_one]⟩
left_inv I' := Subtype.ext liftAux_apply_I (I' : A) I'.prop
right_inv _ := algHom_ext liftAux_apply_I _ _

中文:
定义 lift
  签名: : { I' : A // I' * I' = -1 } ≃ (Complex ->ₐ[实数] A) where
  定义体: liftAux I' I'.prop
  invFun F := ⟨F I, by rw [← map_mul, I_mul_I, map_neg, map_one]⟩
left_inv I' := Subtype.ext liftAux_apply_I (I' : A) I'.prop
right_inv _ := algHom_ext liftAux_apply_I _ _

Depends on / 依赖: liftAux
-/
def lift : { I' : A // I' * I' = -1 } ≃ (Complex ->ₐ[Real] A) where
  toFun I' := liftAux I' I'.prop
  invFun F := ⟨F I, by rw [← map_mul, I_mul_I, map_neg, map_one]⟩
left_inv I' := Subtype.ext liftAux_apply_I (I' : A) I'.prop
right_inv _ := algHom_ext liftAux_apply_I _ _

-- When applied to `Complex.I` itself, `lift` is the identity.
@[simp]
/--
theorem `liftAux_I` / 定理 `liftAux_I`

English:
theorem liftAux_I
  statement: liftAux I I_mul_I = AlgHom.id Real Complex
  proof: algHom_ext liftAux_apply_I _ _

中文:
定理 liftAux_I
  结论: liftAux I I_mul_I = AlgHom.id 实数 Complex
  证明: algHom_ext liftAux_apply_I _ _

Depends on / 依赖: algHom_ext, liftAux_apply_I
-/
theorem liftAux_I : liftAux I I_mul_I = AlgHom.id Real Complex :=
algHom_ext liftAux_apply_I _ _

-- When applied to `-Complex.I`, `lift` is conjugation, `conj`.
@[simp]
/--
theorem `liftAux_neg_I` / 定理 `liftAux_neg_I`

English:
theorem liftAux_neg_I
  statement: liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conjAe
  proof: algHom_ext (liftAux_apply_I _ _).trans conj_I.symm

中文:
定理 liftAux_neg_I
  结论: liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conjAe
  证明: algHom_ext (liftAux_apply_I _ _).trans conj_I.symm

Depends on / 依赖: algHom_ext, conj_I, conj_I.symm, liftAux_apply_I
-/
theorem liftAux_neg_I : liftAux (-I) ((neg_mul_neg _ _).trans I_mul_I) = conjAe :=
algHom_ext (liftAux_apply_I _ _).trans conj_I.symm

end lift

end Complex

section RealImaginaryPart

open Complex

variable {A : Type*}

section AddCommGroup

variable [AddCommGroup A] [Module Complex A] [StarAddMonoid A] [StarModule Complex A]

/--
lemma `Complex.I_mem_skewAdjoint` / 引理 `Complex.I_mem_skewAdjoint`

English:
lemma Complex.I_mem_skewAdjoint
  statement: I in skewAdjoint Complex
  proof: by simp [skewAdjoint.mem_iff]

中文:
引理 Complex.I_mem_skewAdjoint
  结论: I in skewAdjoint Complex
  证明: by simp [skewAdjoint.mem_iff]

Depends on / 依赖: mem_iff, skewAdjoint, skewAdjoint.mem_iff
-/
lemma Complex.I_mem_skewAdjoint : I in skewAdjoint Complex := by simp [skewAdjoint.mem_iff]

/--
lemma `Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint` / 引理 `Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint`

English:
lemma Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint
  given: {a : A}
  proof: by
  simp [skewAdjoint.mem_iff, IsSelfAdjoint, smul_right_inj]

中文:
引理 Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint
  条件: {a : A}
  证明: by
  simp [skewAdjoint.mem_iff, IsSelfAdjoint, smul_right_inj]
-/
@[simp] lemma Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint {a : A} :
    I • a in skewAdjoint A ↔ IsSelfAdjoint a := by
  simp [skewAdjoint.mem_iff, IsSelfAdjoint, smul_right_inj]

/--
lemma `Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint` / 引理 `Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint`

English:
lemma Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint
  given: {a : A}
  proof: by
  simp [← I_smul_mem_skewAdjoint_iff_isSelfAdjoint, smul_smul]

中文:
引理 Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint
  条件: {a : A}
  证明: by
  simp [← I_smul_mem_skewAdjoint_iff_isSelfAdjoint, smul_smul]
-/
@[simp] lemma Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint {a : A} :
    IsSelfAdjoint (I • a) ↔ a in skewAdjoint A := by
  simp [← I_smul_mem_skewAdjoint_iff_isSelfAdjoint, smul_smul]

/-- Create a `selfAdjoint` element from a `skewAdjoint` element by multiplying by the scalar
`-Complex.I`. -/
@[simps]
/--
Definition of `skewAdjoint.negISMul` / `skewAdjoint.negISMul` 的定义

English:
definition skewAdjoint.negISMul
  signature: : skewAdjoint A ->ₗ[Real] selfAdjoint A where
  body: ⟨-I • ↑a, by simp [selfAdjoint.mem_iff]⟩
  map_add' a b := by simp
  map_smul' a b := by ext; simp [smul_comm I]

中文:
定义 skewAdjoint.negISMul
  签名: : skewAdjoint A ->ₗ[实数] selfAdjoint A where
  定义体: ⟨-I • ↑a, by simp [selfAdjoint.mem_iff]⟩
  map_add' a b := by simp
  map_smul' a b := by ext; simp [smul_comm I]

Depends on / 依赖: mem_iff, selfAdjoint, selfAdjoint.mem_iff
-/
def skewAdjoint.negISMul : skewAdjoint A ->ₗ[Real] selfAdjoint A where
  toFun a := ⟨-I • ↑a, by simp [selfAdjoint.mem_iff]⟩
  map_add' a b := by simp
  map_smul' a b := by ext; simp [smul_comm I]

/--
theorem `skewAdjoint.I_smul_neg_I` / 定理 `skewAdjoint.I_smul_neg_I`

English:
theorem skewAdjoint.I_smul_neg_I
  given: (a : skewAdjoint A)
  statement: I • (skewAdjoint.negISMul a : A) = a
  proof: by
  simp [smul_smul]

中文:
定理 skewAdjoint.I_smul_neg_I
  条件: (a : skewAdjoint A)
  结论: I • (skewAdjoint.negISMul a : A) = a
  证明: by
  simp [smul_smul]

Depends on / 依赖: smul_smul
-/
theorem skewAdjoint.I_smul_neg_I (a : skewAdjoint A) : I • (skewAdjoint.negISMul a : A) = a := by
  simp [smul_smul]

/--
Definition of `realPart` / `realPart` 的定义

English:
definition realPart
  signature: : A ->ₗ[Real] selfAdjoint A
  body: selfAdjointPart Real

中文:
定义 realPart
  签名: : A ->ₗ[实数] selfAdjoint A
  定义体: selfAdjointPart Real

Depends on / 依赖: selfAdjointPart
-/
noncomputable def realPart : A ->ₗ[Real] selfAdjoint A :=
  selfAdjointPart Real

/--
Definition of `imaginaryPart` / `imaginaryPart` 的定义

English:
definition imaginaryPart
  signature: : A ->ₗ[Real] selfAdjoint A
  body: skewAdjoint.negISMul.comp (skewAdjointPart Real)

@[inherit_doc]
scoped[ComplexStarModule] notation "ℜ" => realPart
@[inherit_doc]
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

中文:
定义 imaginaryPart
  签名: : A ->ₗ[实数] selfAdjoint A
  定义体: skewAdjoint.negISMul.comp (skewAdjointPart Real)

@[inherit_doc]
scoped[ComplexStarModule] notation "ℜ" => realPart
@[inherit_doc]
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

Depends on / 依赖: negISMul, skewAdjoint, skewAdjoint.negISMul.comp, skewAdjointPart
-/
noncomputable def imaginaryPart : A ->ₗ[Real] selfAdjoint A :=
  skewAdjoint.negISMul.comp (skewAdjointPart Real)

@[inherit_doc]
scoped[ComplexStarModule] notation "ℜ" => realPart
@[inherit_doc]
scoped[ComplexStarModule] notation "ℑ" => imaginaryPart

open ComplexStarModule

/--
theorem `realPart_apply_coe` / 定理 `realPart_apply_coe`

English:
theorem realPart_apply_coe
  given: (a : A)
  statement: (ℜ a : A) = (2 : Real)⁻¹ • (a + star a)
  proof: by
  simp [realPart]

中文:
定理 realPart_apply_coe
  条件: (a : A)
  结论: (ℜ a : A) = (2 : 实数)⁻¹ • (a + star a)
  证明: by
  simp [realPart]

Depends on / 依赖: realPart
-/
theorem realPart_apply_coe (a : A) : (ℜ a : A) = (2 : Real)⁻¹ • (a + star a) := by
  simp [realPart]

/--
theorem `imaginaryPart_apply_coe` / 定理 `imaginaryPart_apply_coe`

English:
theorem imaginaryPart_apply_coe
  given: (a : A)
  statement: (ℑ a : A) = -I • (2 : Real)⁻¹ • (a - star a)
  proof: by
  simp [imaginaryPart]

中文:
定理 imaginaryPart_apply_coe
  条件: (a : A)
  结论: (ℑ a : A) = -I • (2 : 实数)⁻¹ • (a - star a)
  证明: by
  simp [imaginaryPart]

Depends on / 依赖: imaginaryPart
-/
theorem imaginaryPart_apply_coe (a : A) : (ℑ a : A) = -I • (2 : Real)⁻¹ • (a - star a) := by
  simp [imaginaryPart]

/--
theorem `realPart_add_I_smul_imaginaryPart` / 定理 `realPart_add_I_smul_imaginaryPart`

English:
theorem realPart_add_I_smul_imaginaryPart
  given: (a : A)
  statement: (ℜ a : A) + I • (ℑ a : A) = a
  proof: by
  simp [realPart, imaginaryPart, smul_smul, ← smul_add, inv_smul_eq_iff₀, two_smul]

@[simp]

中文:
定理 realPart_add_I_smul_imaginaryPart
  条件: (a : A)
  结论: (ℜ a : A) + I • (ℑ a : A) = a
  证明: by
  simp [realPart, imaginaryPart, smul_smul, ← smul_add, inv_smul_eq_iff₀, two_smul]

@[simp]

Depends on / 依赖: imaginaryPart, realPart, smul_add, smul_smul, two_smul
-/
theorem realPart_add_I_smul_imaginaryPart (a : A) : (ℜ a : A) + I • (ℑ a : A) = a := by
  simp [realPart, imaginaryPart, smul_smul, ← smul_add, inv_smul_eq_iff₀, two_smul]

@[simp]
/--
theorem `realPart_I_smul` / 定理 `realPart_I_smul`

English:
theorem realPart_I_smul
  given: (a : A)
  statement: ℜ (I • a) = -ℑ a
  proof: by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I, sub_eq_add_neg, add_comm]

@[simp]

中文:
定理 realPart_I_smul
  条件: (a : A)
  结论: ℜ (I • a) = -ℑ a
  证明: by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I, sub_eq_add_neg, add_comm]

@[simp]

Depends on / 依赖: add_comm, imaginaryPart_apply_coe, realPart_apply_coe, smul_comm, sub_eq_add_neg
-/
theorem realPart_I_smul (a : A) : ℜ (I • a) = -ℑ a := by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I, sub_eq_add_neg, add_comm]

@[simp]
/--
theorem `imaginaryPart_I_smul` / 定理 `imaginaryPart_I_smul`

English:
theorem imaginaryPart_I_smul
  given: (a : A)
  statement: ℑ (I • a) = ℜ a
  proof: by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I (2⁻¹ : Real), smul_smul I]

中文:
定理 imaginaryPart_I_smul
  条件: (a : A)
  结论: ℑ (I • a) = ℜ a
  证明: by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I (2⁻¹ : Real), smul_smul I]

Depends on / 依赖: imaginaryPart_apply_coe, realPart_apply_coe, smul_comm, smul_smul
-/
theorem imaginaryPart_I_smul (a : A) : ℑ (I • a) = ℜ a := by
  ext
  simp [realPart_apply_coe, imaginaryPart_apply_coe, smul_comm I (2⁻¹ : Real), smul_smul I]

/--
theorem `realPart_smul` / 定理 `realPart_smul`

English:
theorem realPart_smul
  given: (z : Complex) (a : A)
  statement: ℜ (z • a) = z.re • ℜ a - z.im • ℑ a
  proof: by
  have := by congrm (ℜ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]

中文:
定理 realPart_smul
  条件: (z : Complex) (a : A)
  结论: ℜ (z • a) = z.re • ℜ a - z.im • ℑ a
  证明: by
  have := by congrm (ℜ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]

Depends on / 依赖: add_smul, congrm, re_add_im, smul_smul, sub_eq_add_neg
-/
theorem realPart_smul (z : Complex) (a : A) : ℜ (z • a) = z.re • ℜ a - z.im • ℑ a := by
  have := by congrm (ℜ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul, sub_eq_add_neg]

/--
theorem `imaginaryPart_smul` / 定理 `imaginaryPart_smul`

English:
theorem imaginaryPart_smul
  given: (z : Complex) (a : A)
  statement: ℑ (z • a) = z.re • ℑ a + z.im • ℜ a
  proof: by
  have := by congrm (ℑ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul]

中文:
定理 imaginaryPart_smul
  条件: (z : Complex) (a : A)
  结论: ℑ (z • a) = z.re • ℑ a + z.im • ℜ a
  证明: by
  have := by congrm (ℑ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul]

Depends on / 依赖: add_smul, congrm, re_add_im, smul_smul
-/
theorem imaginaryPart_smul (z : Complex) (a : A) : ℑ (z • a) = z.re • ℑ a + z.im • ℜ a := by
  have := by congrm (ℑ ($((re_add_im z).symm) • a))
  simpa [-re_add_im, add_smul, ← smul_smul]

/--
lemma `skewAdjointPart_eq_I_smul_imaginaryPart` / 引理 `skewAdjointPart_eq_I_smul_imaginaryPart`

English:
lemma skewAdjointPart_eq_I_smul_imaginaryPart
  given: (x : A)
  proof: by
  simp [imaginaryPart_apply_coe, smul_smul]

中文:
引理 skewAdjointPart_eq_I_smul_imaginaryPart
  条件: (x : A)
  证明: by
  simp [imaginaryPart_apply_coe, smul_smul]

Depends on / 依赖: imaginaryPart_apply_coe, smul_smul
-/
lemma skewAdjointPart_eq_I_smul_imaginaryPart (x : A) :
    (skewAdjointPart Real x : A) = I • (imaginaryPart x : A) := by
  simp [imaginaryPart_apply_coe, smul_smul]

/--
lemma `imaginaryPart_eq_neg_I_smul_skewAdjointPart` / 引理 `imaginaryPart_eq_neg_I_smul_skewAdjointPart`

English:
lemma imaginaryPart_eq_neg_I_smul_skewAdjointPart
  given: (x : A)
  proof: rfl

中文:
引理 imaginaryPart_eq_neg_I_smul_skewAdjointPart
  条件: (x : A)
  证明: rfl
-/
lemma imaginaryPart_eq_neg_I_smul_skewAdjointPart (x : A) :
    (imaginaryPart x : A) = -I • (skewAdjointPart Real x : A) :=
  rfl

/--
lemma `IsSelfAdjoint.coe_realPart` / 引理 `IsSelfAdjoint.coe_realPart`

English:
lemma IsSelfAdjoint.coe_realPart
  given: {x : A} (hx : IsSelfAdjoint x)
  proof: hx.coe_selfAdjointPart_apply Real

nonrec lemma IsSelfAdjoint.imaginaryPart {x : A} (hx : IsSelfAdjoint x) :
    ℑ x = 0 := by
  rw [imaginaryPart]; rw [LinearMap.comp_apply]; rw [hx.skewAdjointPart_apply _]; rw [map_zero]

中文:
引理 IsSelfAdjoint.coe_realPart
  条件: {x : A} (hx : IsSelfAdjoint x)
  证明: hx.coe_selfAdjointPart_apply Real

nonrec lemma IsSelfAdjoint.imaginaryPart {x : A} (hx : IsSelfAdjoint x) :
    ℑ x = 0 := by
  rw [imaginaryPart]; rw [LinearMap.comp_apply]; rw [hx.skewAdjointPart_apply _]; rw [map_zero]

Depends on / 依赖: coe_selfAdjointPart_apply, hx.coe_selfAdjointPart_apply
-/
lemma IsSelfAdjoint.coe_realPart {x : A} (hx : IsSelfAdjoint x) :
    (ℜ x : A) = x :=
  hx.coe_selfAdjointPart_apply Real

nonrec lemma IsSelfAdjoint.imaginaryPart {x : A} (hx : IsSelfAdjoint x) :
    ℑ x = 0 := by
  rw [imaginaryPart]; rw [LinearMap.comp_apply]; rw [hx.skewAdjointPart_apply _]; rw [map_zero]

/--
lemma `realPart_comp_subtype_selfAdjoint` / 引理 `realPart_comp_subtype_selfAdjoint`

English:
lemma realPart_comp_subtype_selfAdjoint
  proof: selfAdjointPart_comp_subtype_selfAdjoint Real

中文:
引理 realPart_comp_subtype_selfAdjoint
  证明: selfAdjointPart_comp_subtype_selfAdjoint Real

Depends on / 依赖: selfAdjointPart_comp_subtype_selfAdjoint
-/
lemma realPart_comp_subtype_selfAdjoint :
    realPart.comp (selfAdjoint.submodule Real A).subtype = LinearMap.id :=
  selfAdjointPart_comp_subtype_selfAdjoint Real

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `imaginaryPart_comp_subtype_selfAdjoint` / 引理 `imaginaryPart_comp_subtype_selfAdjoint`

English:
lemma imaginaryPart_comp_subtype_selfAdjoint
  proof: by
  ext; simp [imaginaryPart]

@[simp]

中文:
引理 imaginaryPart_comp_subtype_selfAdjoint
  证明: by
  ext; simp [imaginaryPart]

@[simp]

Depends on / 依赖: imaginaryPart
-/
lemma imaginaryPart_comp_subtype_selfAdjoint :
    imaginaryPart.comp (selfAdjoint.submodule Real A).subtype = 0 := by
  ext; simp [imaginaryPart]

@[simp]
/--
lemma `selfAdjoint.realPart_coe` / 引理 `selfAdjoint.realPart_coe`

English:
lemma selfAdjoint.realPart_coe
  given: {x : selfAdjoint A}
  statement: ℜ (x : A) = x
  proof: Subtype.ext x.property.coe_realPart

@[simp]

中文:
引理 selfAdjoint.realPart_coe
  条件: {x : selfAdjoint A}
  结论: ℜ (x : A) = x
  证明: Subtype.ext x.property.coe_realPart

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, coe_realPart, property, x.property.coe_realPart
-/
lemma selfAdjoint.realPart_coe {x : selfAdjoint A} : ℜ (x : A) = x :=
  Subtype.ext x.property.coe_realPart

@[simp]
/--
lemma `selfAdjoint.imaginaryPart_coe` / 引理 `selfAdjoint.imaginaryPart_coe`

English:
lemma selfAdjoint.imaginaryPart_coe
  given: {x : selfAdjoint A}
  statement: ℑ (x : A) = 0
  proof: x.property.imaginaryPart

中文:
引理 selfAdjoint.imaginaryPart_coe
  条件: {x : selfAdjoint A}
  结论: ℑ (x : A) = 0
  证明: x.property.imaginaryPart

Depends on / 依赖: imaginaryPart, property, x.property.imaginaryPart
-/
lemma selfAdjoint.imaginaryPart_coe {x : selfAdjoint A} : ℑ (x : A) = 0 :=
  x.property.imaginaryPart

/--
lemma `imaginaryPart_realPart` / 引理 `imaginaryPart_realPart`

English:
lemma imaginaryPart_realPart
  given: {x : A}
  statement: ℑ (ℜ x : A) = 0
  proof: (ℜ x).property.imaginaryPart

中文:
引理 imaginaryPart_realPart
  条件: {x : A}
  结论: ℑ (ℜ x : A) = 0
  证明: (ℜ x).property.imaginaryPart

Depends on / 依赖: imaginaryPart, property, property.imaginaryPart
-/
lemma imaginaryPart_realPart {x : A} : ℑ (ℜ x : A) = 0 :=
  (ℜ x).property.imaginaryPart

/--
lemma `imaginaryPart_imaginaryPart` / 引理 `imaginaryPart_imaginaryPart`

English:
lemma imaginaryPart_imaginaryPart
  given: {x : A}
  statement: ℑ (ℑ x : A) = 0
  proof: (ℑ x).property.imaginaryPart

中文:
引理 imaginaryPart_imaginaryPart
  条件: {x : A}
  结论: ℑ (ℑ x : A) = 0
  证明: (ℑ x).property.imaginaryPart

Depends on / 依赖: imaginaryPart, property, property.imaginaryPart
-/
lemma imaginaryPart_imaginaryPart {x : A} : ℑ (ℑ x : A) = 0 :=
  (ℑ x).property.imaginaryPart

/--
lemma `realPart_idem` / 引理 `realPart_idem`

English:
lemma realPart_idem
  given: {x : A}
  statement: ℜ (ℜ x : A) = ℜ x
  proof: Subtype.ext (ℜ x).property.coe_realPart

中文:
引理 realPart_idem
  条件: {x : A}
  结论: ℜ (ℜ x : A) = ℜ x
  证明: Subtype.ext (ℜ x).property.coe_realPart

Depends on / 依赖: Subtype, Subtype.ext, coe_realPart, property, property.coe_realPart
-/
lemma realPart_idem {x : A} : ℜ (ℜ x : A) = ℜ x :=
Subtype.ext (ℜ x).property.coe_realPart

/--
lemma `realPart_imaginaryPart` / 引理 `realPart_imaginaryPart`

English:
lemma realPart_imaginaryPart
  given: {x : A}
  statement: ℜ (ℑ x : A) = ℑ x
  proof: Subtype.ext (ℑ x).property.coe_realPart

中文:
引理 realPart_imaginaryPart
  条件: {x : A}
  结论: ℜ (ℑ x : A) = ℑ x
  证明: Subtype.ext (ℑ x).property.coe_realPart

Depends on / 依赖: Subtype, Subtype.ext, coe_realPart, property, property.coe_realPart
-/
lemma realPart_imaginaryPart {x : A} : ℜ (ℑ x : A) = ℑ x :=
Subtype.ext (ℑ x).property.coe_realPart

/--
lemma `realPart_surjective` / 引理 `realPart_surjective`

English:
lemma realPart_surjective
  statement: Function.Surjective (realPart (A := A))
  proof: fun x => ⟨(x : A), Subtype.ext x.property.coe_realPart⟩

中文:
引理 realPart_surjective
  结论: Function.Surjective (realPart (A := A))
  证明: fun x => ⟨(x : A), Subtype.ext x.property.coe_realPart⟩
-/
lemma realPart_surjective : Function.Surjective (realPart (A := A)) :=
  fun x => ⟨(x : A), Subtype.ext x.property.coe_realPart⟩

/--
lemma `imaginaryPart_surjective` / 引理 `imaginaryPart_surjective`

English:
lemma imaginaryPart_surjective
  statement: Function.Surjective (imaginaryPart (A := A))
  proof: fun x =>
⟨I • (x : A), Subtype.ext by simp only [imaginaryPart_I_smul, x.property.coe_realPart]⟩

中文:
引理 imaginaryPart_surjective
  结论: Function.Surjective (imaginaryPart (A := A))
  证明: fun x =>
⟨I • (x : A), Subtype.ext by simp only [imaginaryPart_I_smul, x.property.coe_realPart]⟩
-/
lemma imaginaryPart_surjective : Function.Surjective (imaginaryPart (A := A)) :=
  fun x =>
⟨I • (x : A), Subtype.ext by simp only [imaginaryPart_I_smul, x.property.coe_realPart]⟩

/--
lemma `ComplexStarModule.ext` / 引理 `ComplexStarModule.ext`

English:
lemma ComplexStarModule.ext
  given: {x y : A} (h₁ : ℜ x = ℜ y) (h₂ : ℑ x = ℑ y)
  statement: x = y
  proof: by
  rw [← realPart_add_I_smul_imaginaryPart x]; rw [← realPart_add_I_smul_imaginaryPart y]; rw [h₁]; rw [h₂]

中文:
引理 ComplexStarModule.ext
  条件: {x y : A} (h₁ : ℜ x = ℜ y) (h₂ : ℑ x = ℑ y)
  结论: x = y
  证明: by
  rw [← realPart_add_I_smul_imaginaryPart x]; rw [← realPart_add_I_smul_imaginaryPart y]; rw [h₁]; rw [h₂]

Depends on / 依赖: realPart_add_I_smul_imaginaryPart
-/
lemma ComplexStarModule.ext {x y : A} (h₁ : ℜ x = ℜ y) (h₂ : ℑ x = ℑ y) : x = y := by
  rw [← realPart_add_I_smul_imaginaryPart x]; rw [← realPart_add_I_smul_imaginaryPart y]; rw [h₁]; rw [h₂]

/--
lemma `ComplexStarModule.ext_iff` / 引理 `ComplexStarModule.ext_iff`

English:
lemma ComplexStarModule.ext_iff
  given: {x y : A}
  statement: x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y where
  proof: by grind
  mpr h := ext h.1 h.2

中文:
引理 ComplexStarModule.ext_iff
  条件: {x y : A}
  结论: x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y where
  证明: by grind
  mpr h := ext h.1 h.2
-/
lemma ComplexStarModule.ext_iff {x y : A} : x = y ↔ ℜ x = ℜ y ∧ ℑ x = ℑ y where
  mp := by grind
  mpr h := ext h.1 h.2

section StarHomClass

variable {B F : Type*} [AddCommGroup B] [Module Complex B] [StarAddMonoid B] [StarModule Complex B]
    [FunLike F A B] [StarHomClass F A B] [LinearMapClass F Complex A B]

/--
lemma `map_realPart` / 引理 `map_realPart`

English:
lemma map_realPart
  given: (f : F) (x : A)
  statement: f (ℜ x) = ℜ (f x)
  proof: by
  simp [realPart_apply_coe, ← Complex.coe_smul, map_star]

中文:
引理 map_realPart
  条件: (f : F) (x : A)
  结论: f (ℜ x) = ℜ (f x)
  证明: by
  simp [realPart_apply_coe, ← Complex.coe_smul, map_star]

Depends on / 依赖: Complex.coe_smul, coe_smul, map_star, realPart_apply_coe
-/
lemma map_realPart (f : F) (x : A) : f (ℜ x) = ℜ (f x) := by
  simp [realPart_apply_coe, ← Complex.coe_smul, map_star]

/--
lemma `map_imaginaryPart` / 引理 `map_imaginaryPart`

English:
lemma map_imaginaryPart
  given: (f : F) (x : A)
  statement: f (ℑ x) = ℑ (f x)
  proof: by
  simp [imaginaryPart_apply_coe, ← Complex.coe_smul, map_star]

中文:
引理 map_imaginaryPart
  条件: (f : F) (x : A)
  结论: f (ℑ x) = ℑ (f x)
  证明: by
  simp [imaginaryPart_apply_coe, ← Complex.coe_smul, map_star]

Depends on / 依赖: Complex.coe_smul, coe_smul, imaginaryPart_apply_coe, map_star
-/
lemma map_imaginaryPart (f : F) (x : A) : f (ℑ x) = ℑ (f x) := by
  simp [imaginaryPart_apply_coe, ← Complex.coe_smul, map_star]

end StarHomClass

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ker_imaginaryPart` / 定理 `ker_imaginaryPart`

English:
theorem ker_imaginaryPart
  statement: imaginaryPart.ker = selfAdjoint.submodule Real A
  proof: by
  ext x
  simp [selfAdjoint.submodule, selfAdjoint.mem_iff, imaginaryPart, Subtype.ext_iff]
  grind

@[simp]

中文:
定理 ker_imaginaryPart
  结论: imaginaryPart.ker = selfAdjoint.submodule 实数 A
  证明: by
  ext x
  simp [selfAdjoint.submodule, selfAdjoint.mem_iff, imaginaryPart, Subtype.ext_iff]
  grind

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, imaginaryPart, mem_iff, selfAdjoint, selfAdjoint.mem_iff, selfAdjoint.submodule, submodule
-/
theorem ker_imaginaryPart : imaginaryPart.ker = selfAdjoint.submodule Real A := by
  ext x
  simp [selfAdjoint.submodule, selfAdjoint.mem_iff, imaginaryPart, Subtype.ext_iff]
  grind

@[simp]
/--
lemma `imaginaryPart_eq_zero_iff` / 引理 `imaginaryPart_eq_zero_iff`

English:
lemma imaginaryPart_eq_zero_iff
  given: {x : A}
  statement: ℑ x = 0 ↔ IsSelfAdjoint x
  proof: by
  simpa [-ker_imaginaryPart] using! SetLike.ext_iff.mp ker_imaginaryPart x

中文:
引理 imaginaryPart_eq_zero_iff
  条件: {x : A}
  结论: ℑ x = 0 ↔ IsSelfAdjoint x
  证明: by
  simpa [-ker_imaginaryPart] using! SetLike.ext_iff.mp ker_imaginaryPart x

Depends on / 依赖: SetLike, SetLike.ext_iff.mp, ext_iff, ker_imaginaryPart
-/
lemma imaginaryPart_eq_zero_iff {x : A} : ℑ x = 0 ↔ IsSelfAdjoint x := by
  simpa [-ker_imaginaryPart] using! SetLike.ext_iff.mp ker_imaginaryPart x

open Submodule

/--
lemma `span_selfAdjoint` / 引理 `span_selfAdjoint`

English:
lemma span_selfAdjoint
  statement: span Complex (selfAdjoint A : Set A) = ⊤
  proof: by
  refine eq_top_iff'.mpr fun x => ?_
  rw [← realPart_add_I_smul_imaginaryPart x]
exact add_mem (subset_span (ℜ x).property)
SMulMemClass.smul_mem _ subset_span (ℑ x).property

中文:
引理 span_selfAdjoint
  结论: span Complex (selfAdjoint A : Set A) = ⊤
  证明: by
  refine eq_top_iff'.mpr fun x => ?_
  rw [← realPart_add_I_smul_imaginaryPart x]
exact add_mem (subset_span (ℜ x).property)
SMulMemClass.smul_mem _ subset_span (ℑ x).property

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, add_mem, eq_top_iff, property, realPart_add_I_smul_imaginaryPart, smul_mem, subset_span
-/
lemma span_selfAdjoint : span Complex (selfAdjoint A : Set A) = ⊤ := by
  refine eq_top_iff'.mpr fun x => ?_
  rw [← realPart_add_I_smul_imaginaryPart x]
exact add_mem (subset_span (ℜ x).property)
SMulMemClass.smul_mem _ subset_span (ℑ x).property

end AddCommGroup

open scoped ComplexStarModule

/-- The natural `ℝ`-linear equivalence between `selfAdjoint ℂ` and `ℝ`. -/
@[simps apply symm_apply]
/--
Definition of `Complex.selfAdjointEquiv` / `Complex.selfAdjointEquiv` 的定义

English:
definition Complex.selfAdjointEquiv
  signature: : selfAdjoint Complex ≃ₗ[Real] Real where
  body: fun z => (z : Complex).re
  invFun := fun x => ⟨x, conj_ofReal x⟩
left_inv := fun z => Subtype.ext conj_eq_iff_re.mp z.property.star_eq
  map_add' := by simp
  map_smul' := by simp

中文:
定义 Complex.selfAdjointEquiv
  签名: : selfAdjoint Complex ≃ₗ[实数] 实数 where
  定义体: fun z => (z : Complex).re
  invFun := fun x => ⟨x, conj_ofReal x⟩
left_inv := fun z => Subtype.ext conj_eq_iff_re.mp z.property.star_eq
  map_add' := by simp
  map_smul' := by simp
-/
def Complex.selfAdjointEquiv : selfAdjoint Complex ≃ₗ[Real] Real where
  toFun := fun z => (z : Complex).re
  invFun := fun x => ⟨x, conj_ofReal x⟩
left_inv := fun z => Subtype.ext conj_eq_iff_re.mp z.property.star_eq
  map_add' := by simp
  map_smul' := by simp

/--
lemma `Complex.coe_selfAdjointEquiv` / 引理 `Complex.coe_selfAdjointEquiv`

English:
lemma Complex.coe_selfAdjointEquiv
  given: (z : selfAdjoint Complex)
  proof: by
  simpa [selfAdjointEquiv_symm_apply]
    using (congr_arg Subtype.val <| Complex.selfAdjointEquiv.left_inv z)

@[simp]

中文:
引理 Complex.coe_selfAdjointEquiv
  条件: (z : selfAdjoint Complex)
  证明: by
  simpa [selfAdjointEquiv_symm_apply]
    using (congr_arg Subtype.val <| Complex.selfAdjointEquiv.left_inv z)

@[simp]

Depends on / 依赖: Complex.selfAdjointEquiv.left_inv, Subtype, Subtype.val, congr_arg, left_inv, selfAdjointEquiv, selfAdjointEquiv_symm_apply
-/
lemma Complex.coe_selfAdjointEquiv (z : selfAdjoint Complex) :
    (selfAdjointEquiv z : Complex) = z := by
  simpa [selfAdjointEquiv_symm_apply]
    using (congr_arg Subtype.val <| Complex.selfAdjointEquiv.left_inv z)

@[simp]
/--
lemma `realPart_ofReal` / 引理 `realPart_ofReal`

English:
lemma realPart_ofReal
  given: (r : Real)
  statement: (ℜ (r : Complex) : Complex) = r
  proof: by
  rw [realPart_apply_coe]; rw [star_def]; rw [conj_ofReal]; rw [← two_smul Real (r : Complex)]
  simp

@[simp]

中文:
引理 realPart_ofReal
  条件: (r : 实数)
  结论: (ℜ (r : Complex) : Complex) = r
  证明: by
  rw [realPart_apply_coe]; rw [star_def]; rw [conj_ofReal]; rw [← two_smul Real (r : Complex)]
  simp

@[simp]

Depends on / 依赖: conj_ofReal, realPart_apply_coe, star_def, two_smul
-/
lemma realPart_ofReal (r : Real) : (ℜ (r : Complex) : Complex) = r := by
  rw [realPart_apply_coe]; rw [star_def]; rw [conj_ofReal]; rw [← two_smul Real (r : Complex)]
  simp

@[simp]
/--
lemma `imaginaryPart_ofReal` / 引理 `imaginaryPart_ofReal`

English:
lemma imaginaryPart_ofReal
  given: (r : Real)
  statement: ℑ (r : Complex) = 0
  proof: by
  ext1; simp [imaginaryPart_apply_coe, conj_ofReal]

中文:
引理 imaginaryPart_ofReal
  条件: (r : 实数)
  结论: ℑ (r : Complex) = 0
  证明: by
  ext1; simp [imaginaryPart_apply_coe, conj_ofReal]

Depends on / 依赖: IsBoundedSMul, IsBoundedSMul.of_norm_smul_le, conj_ofReal, imaginaryPart_apply_coe, norm_smul_le, of_norm_smul_le
-/
lemma imaginaryPart_ofReal (r : Real) : ℑ (r : Complex) = 0 := by
  ext1; simp [imaginaryPart_apply_coe, conj_ofReal]

/--
lemma `Complex.coe_realPart` / 引理 `Complex.coe_realPart`

English:
lemma Complex.coe_realPart
  given: (z : Complex)
  statement: (ℜ z : Complex) = z.re
  proof: by
  conv_lhs => rw [← re_add_im z]
  simp [-re_add_im, realPart_I_smul, mul_comm _ I, ← smul_eq_mul]

中文:
引理 Complex.coe_realPart
  条件: (z : Complex)
  结论: (ℜ z : Complex) = z.re
  证明: by
  conv_lhs => rw [← re_add_im z]
  simp [-re_add_im, realPart_I_smul, mul_comm _ I, ← smul_eq_mul]

Depends on / 依赖: conv_lhs, mul_comm, re_add_im, realPart_I_smul, smul_eq_mul
-/
lemma Complex.coe_realPart (z : Complex) : (ℜ z : Complex) = z.re := by
  conv_lhs => rw [← re_add_im z]
  simp [-re_add_im, realPart_I_smul, mul_comm _ I, ← smul_eq_mul]

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing A] [StarRing A] [Module Complex A] [IsScalarTower Complex A A]
  [SMulCommClass Complex A A] [StarModule Complex A]

/--
lemma `star_mul_self_add_self_mul_star` / 引理 `star_mul_self_add_self_mul_star`

English:
lemma star_mul_self_add_self_mul_star
  given: (a : A)
  proof: have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a + a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) + $(a_eq) * (star $(a_eq)))
    _ = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) := by
      simp [mul_add, add_mul, smul_smul, mul_smul_comm,
        smul_mul_assoc]
      abel

中文:
引理 star_mul_self_add_self_mul_star
  条件: (a : A)
  证明: have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a + a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) + $(a_eq) * (star $(a_eq)))
    _ = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) := by
      simp [mul_add, add_mul, smul_smul, mul_smul_comm,
        smul_mul_assoc]
      abel

Depends on / 依赖: a_eq, add_mul, mul_add, mul_smul_comm, realPart_add_I_smul_imaginaryPart, smul_mul_assoc, smul_smul
-/
lemma star_mul_self_add_self_mul_star (a : A) :
    star a * a + a * star a = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) :=
  have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a + a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) + $(a_eq) * (star $(a_eq)))
    _ = 2 • (ℜ a * ℜ a + ℑ a * ℑ a) := by
      simp [mul_add, add_mul, smul_smul, mul_smul_comm,
        smul_mul_assoc]
      abel

/--
lemma `star_mul_self_sub_self_mul_star` / 引理 `star_mul_self_sub_self_mul_star`

English:
lemma star_mul_self_sub_self_mul_star
  given: (a : A)
  proof: have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a - a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) - $(a_eq) * (star $(a_eq)))
    _ = 2 • I • (ℜ a * ℑ a - ℑ a * ℜ a) := by
      simp [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul]
      module

中文:
引理 star_mul_self_sub_self_mul_star
  条件: (a : A)
  证明: have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a - a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) - $(a_eq) * (star $(a_eq)))
    _ = 2 • I • (ℜ a * ℑ a - ℑ a * ℜ a) := by
      simp [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul]
      module

Depends on / 依赖: a_eq, add_mul, module, mul_add, mul_smul_comm, realPart_add_I_smul_imaginaryPart, smul_mul_assoc, smul_smul
-/
lemma star_mul_self_sub_self_mul_star (a : A) :
    star a * a - a * star a = 2 • I • (ℜ a * ℑ a - ℑ a * ℜ a) :=
  have a_eq := (realPart_add_I_smul_imaginaryPart a).symm
  calc
    star a * a - a * star a = _ :=
      congr((star $(a_eq)) * $(a_eq) - $(a_eq) * (star $(a_eq)))
    _ = 2 • I • (ℜ a * ℑ a - ℑ a * ℜ a) := by
      simp [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul]
      module

/--
lemma `isStarNormal_iff_commute_realPart_imaginaryPart` / 引理 `isStarNormal_iff_commute_realPart_imaginaryPart`

English:
lemma isStarNormal_iff_commute_realPart_imaginaryPart
  given: {x : A}
  proof: by
  rw [isStarNormal_iff]; rw [commute_iff_eq]; rw [← sub_eq_zero]; rw [star_mul_self_sub_self_mul_star]; rw [two_smul Nat]; rw [← two_smul Complex]; rw [smul_eq_zero_iff_right two_ne_zero]; rw [smul_eq_zero_iff_right I_ne_zero]; rw [sub_eq_zero]; rw [commute_iff_eq]

中文:
引理 isStarNormal_iff_commute_realPart_imaginaryPart
  条件: {x : A}
  证明: by
  rw [isStarNormal_iff]; rw [commute_iff_eq]; rw [← sub_eq_zero]; rw [star_mul_self_sub_self_mul_star]; rw [two_smul Nat]; rw [← two_smul Complex]; rw [smul_eq_zero_iff_right two_ne_zero]; rw [smul_eq_zero_iff_right I_ne_zero]; rw [sub_eq_zero]; rw [commute_iff_eq]

Depends on / 依赖: I_ne_zero, commute_iff_eq, isStarNormal_iff, smul_eq_zero_iff_right, star_mul_self_sub_self_mul_star, sub_eq_zero, two_ne_zero, two_smul
-/
lemma isStarNormal_iff_commute_realPart_imaginaryPart {x : A} :
    IsStarNormal x ↔ Commute (ℜ x : A) (ℑ x : A) := by
  rw [isStarNormal_iff]; rw [commute_iff_eq]; rw [← sub_eq_zero]; rw [star_mul_self_sub_self_mul_star]; rw [two_smul Nat]; rw [← two_smul Complex]; rw [smul_eq_zero_iff_right two_ne_zero]; rw [smul_eq_zero_iff_right I_ne_zero]; rw [sub_eq_zero]; rw [commute_iff_eq]

/--
lemma `Commute.realPart_imaginaryPart` / 引理 `Commute.realPart_imaginaryPart`

English:
lemma Commute.realPart_imaginaryPart
  given: (x : A) [IsStarNormal x]
  proof: isStarNormal_iff_commute_realPart_imaginaryPart.mp inferInstance

中文:
引理 Commute.realPart_imaginaryPart
  条件: (x : A) [IsStarNormal x]
  证明: isStarNormal_iff_commute_realPart_imaginaryPart.mp inferInstance

Depends on / 依赖: isStarNormal_iff_commute_realPart_imaginaryPart, isStarNormal_iff_commute_realPart_imaginaryPart.mp
-/
lemma Commute.realPart_imaginaryPart (x : A) [IsStarNormal x] :
    Commute (ℜ x : A) (ℑ x : A) :=
  isStarNormal_iff_commute_realPart_imaginaryPart.mp inferInstance

/--
lemma `star_mul_self_eq_realPart_sq_add_imaginaryPart_sq` / 引理 `star_mul_self_eq_realPart_sq_add_imaginaryPart_sq`

English:
lemma star_mul_self_eq_realPart_sq_add_imaginaryPart_sq
  given: (x : A) [hx : IsStarNormal x]
  proof: calc
  star x * x = ℜ x * ℜ x + ℑ x * ℑ x + Complex.I • (ℜ x * ℑ x - ℑ x * ℜ x) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
    simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
    grind
  _ = _ := by simp [Commute.realPart_imaginaryPart x |>.eq]

中文:
引理 star_mul_self_eq_realPart_sq_add_imaginaryPart_sq
  条件: (x : A) [hx : IsStarNormal x]
  证明: calc
  star x * x = ℜ x * ℜ x + ℑ x * ℑ x + Complex.I • (ℜ x * ℑ x - ℑ x * ℜ x) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
    simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
    grind
  _ = _ := by simp [Commute.realPart_imaginaryPart x |>.eq]
-/
lemma star_mul_self_eq_realPart_sq_add_imaginaryPart_sq (x : A) [hx : IsStarNormal x] :
    star x * x = ℜ x * ℜ x + ℑ x * ℑ x := calc
  star x * x = ℜ x * ℜ x + ℑ x * ℑ x + Complex.I • (ℜ x * ℑ x - ℑ x * ℜ x) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart x]
    simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
    grind
  _ = _ := by simp [Commute.realPart_imaginaryPart x |>.eq]

end NonUnitalNonAssocRing

section StarOrderedRing

variable [NonUnitalRing A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Module Complex A] [StarModule Complex A]

/--
lemma `nonneg_iff_realPart_imaginaryPart` / 引理 `nonneg_iff_realPart_imaginaryPart`

English:
lemma nonneg_iff_realPart_imaginaryPart
  given: {a : A}
  proof: by
  refine ⟨fun h => ⟨?_, h.isSelfAdjoint.imaginaryPart⟩, fun h => ?_⟩
  · simpa +singlePass [← h.isSelfAdjoint.coe_realPart] using! h
  · rw [← realPart_add_I_smul_imaginaryPart a, h.2]
    simpa using! h.1

中文:
引理 nonneg_iff_realPart_imaginaryPart
  条件: {a : A}
  证明: by
  refine ⟨fun h => ⟨?_, h.isSelfAdjoint.imaginaryPart⟩, fun h => ?_⟩
  · simpa +singlePass [← h.isSelfAdjoint.coe_realPart] using! h
  · rw [← realPart_add_I_smul_imaginaryPart a, h.2]
    simpa using! h.1

Depends on / 依赖: coe_realPart, h.isSelfAdjoint.coe_realPart, h.isSelfAdjoint.imaginaryPart, imaginaryPart, isSelfAdjoint, realPart_add_I_smul_imaginaryPart, singlePass
-/
lemma nonneg_iff_realPart_imaginaryPart {a : A} :
    0 <= a ↔ 0 <= ℜ a ∧ ℑ a = 0 := by
  refine ⟨fun h => ⟨?_, h.isSelfAdjoint.imaginaryPart⟩, fun h => ?_⟩
  · simpa +singlePass [← h.isSelfAdjoint.coe_realPart] using! h
  · rw [← realPart_add_I_smul_imaginaryPart a, h.2]
    simpa using! h.1

/--
lemma `nonpos_iff_realPart_imaginaryPart` / 引理 `nonpos_iff_realPart_imaginaryPart`

English:
lemma nonpos_iff_realPart_imaginaryPart
  given: {a : A}
  proof: by
  simpa using nonneg_iff_realPart_imaginaryPart (a := -a)

中文:
引理 nonpos_iff_realPart_imaginaryPart
  条件: {a : A}
  证明: by
  simpa using nonneg_iff_realPart_imaginaryPart (a := -a)

Depends on / 依赖: nonneg_iff_realPart_imaginaryPart
-/
lemma nonpos_iff_realPart_imaginaryPart {a : A} :
    a <= 0 ↔ ℜ a <= 0 ∧ ℑ a = 0 := by
  simpa using nonneg_iff_realPart_imaginaryPart (a := -a)

/--
lemma `realPart_nonneg_of_nonneg` / 引理 `realPart_nonneg_of_nonneg`

English:
lemma realPart_nonneg_of_nonneg
  given: {a : A} (ha : 0 <= a)
  statement: 0 <= ℜ a
  proof: .1 nonneg_iff_realPart_imaginaryPart.mp ha

中文:
引理 realPart_nonneg_of_nonneg
  条件: {a : A} (ha : 0 <= a)
  结论: 0 <= ℜ a
  证明: .1 nonneg_iff_realPart_imaginaryPart.mp ha

Depends on / 依赖: nonneg_iff_realPart_imaginaryPart, nonneg_iff_realPart_imaginaryPart.mp
-/
lemma realPart_nonneg_of_nonneg {a : A} (ha : 0 <= a) : 0 <= ℜ a :=
.1 nonneg_iff_realPart_imaginaryPart.mp ha

/--
lemma `realPart_nonpos_of_nonpos` / 引理 `realPart_nonpos_of_nonpos`

English:
lemma realPart_nonpos_of_nonpos
  given: {a : A} (ha : a <= 0)
  statement: ℜ a <= 0
  proof: .1 nonpos_iff_realPart_imaginaryPart.mp ha

中文:
引理 realPart_nonpos_of_nonpos
  条件: {a : A} (ha : a <= 0)
  结论: ℜ a <= 0
  证明: .1 nonpos_iff_realPart_imaginaryPart.mp ha

Depends on / 依赖: nonpos_iff_realPart_imaginaryPart, nonpos_iff_realPart_imaginaryPart.mp
-/
lemma realPart_nonpos_of_nonpos {a : A} (ha : a <= 0) : ℜ a <= 0 :=
.1 nonpos_iff_realPart_imaginaryPart.mp ha

/--
lemma `le_iff_realPart_imaginaryPart` / 引理 `le_iff_realPart_imaginaryPart`

English:
lemma le_iff_realPart_imaginaryPart
  given: {a b : A}
  proof: by
  simpa [sub_eq_zero, eq_comm (a := ℑ a)] using nonneg_iff_realPart_imaginaryPart (a := b - a)

中文:
引理 le_iff_realPart_imaginaryPart
  条件: {a b : A}
  证明: by
  simpa [sub_eq_zero, eq_comm (a := ℑ a)] using nonneg_iff_realPart_imaginaryPart (a := b - a)

Depends on / 依赖: eq_comm, nonneg_iff_realPart_imaginaryPart, sub_eq_zero
-/
lemma le_iff_realPart_imaginaryPart {a b : A} :
    a <= b ↔ ℜ a <= ℜ b ∧ ℑ a = ℑ b := by
  simpa [sub_eq_zero, eq_comm (a := ℑ a)] using nonneg_iff_realPart_imaginaryPart (a := b - a)

/--
lemma `imaginaryPart_eq_of_le` / 引理 `imaginaryPart_eq_of_le`

English:
lemma imaginaryPart_eq_of_le
  given: {a b : A} (hab : a <= b)
  proof: .2 le_iff_realPart_imaginaryPart.mp hab

中文:
引理 imaginaryPart_eq_of_le
  条件: {a b : A} (hab : a <= b)
  证明: .2 le_iff_realPart_imaginaryPart.mp hab

Depends on / 依赖: le_iff_realPart_imaginaryPart, le_iff_realPart_imaginaryPart.mp
-/
lemma imaginaryPart_eq_of_le {a b : A} (hab : a <= b) :
    ℑ a = ℑ b :=
.2 le_iff_realPart_imaginaryPart.mp hab

/--
lemma `realPart_mono` / 引理 `realPart_mono`

English:
lemma realPart_mono
  given: {a b : A} (hab : a <= b)
  proof: .1 le_iff_realPart_imaginaryPart.mp hab

中文:
引理 realPart_mono
  条件: {a b : A} (hab : a <= b)
  证明: .1 le_iff_realPart_imaginaryPart.mp hab

Depends on / 依赖: le_iff_realPart_imaginaryPart, le_iff_realPart_imaginaryPart.mp
-/
lemma realPart_mono {a b : A} (hab : a <= b) :
    ℜ a <= ℜ b :=
.1 le_iff_realPart_imaginaryPart.mp hab

end StarOrderedRing

@[simp]
/--
lemma `realPart_one` / 引理 `realPart_one`

English:
lemma realPart_one
  given: [Ring A] [StarRing A] [Module Complex A] [StarModule Complex A]
  proof: by
  ext; simp [realPart_apply_coe, ← two_smul Real]

中文:
引理 realPart_one
  条件: [Ring A] [StarRing A] [Module Complex A] [StarModule Complex A]
  证明: by
  ext; simp [realPart_apply_coe, ← two_smul Real]

Depends on / 依赖: realPart_apply_coe, two_smul
-/
lemma realPart_one [Ring A] [StarRing A] [Module Complex A] [StarModule Complex A] :
    ℜ (1 : A) = 1 := by
  ext; simp [realPart_apply_coe, ← two_smul Real]

/--
lemma `mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one` / 引理 `mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one`

English:
lemma mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one
  statement: [Ring A]
  proof: by
  rw [Unitary.mem_iff]
  refine ⟨fun ⟨h, h'⟩ => ?_, fun ⟨hx, h⟩ => ?_⟩
  · have : IsStarNormal x := ⟨h.trans h'.symm⟩
    exact ⟨this, by simp [sq, ← star_mul_self_eq_realPart_sq_add_imaginaryPart_sq x, h]⟩
  · simp [← hx.star_comm_self.eq, star_mul_self_eq_realPart_sq_add_imaginaryPart_sq, ← sq,

中文:
引理 mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one
  结论: [Ring A]
  证明: by
  rw [Unitary.mem_iff]
  refine ⟨fun ⟨h, h'⟩ => ?_, fun ⟨hx, h⟩ => ?_⟩
  · have : IsStarNormal x := ⟨h.trans h'.symm⟩
    exact ⟨this, by simp [sq, ← star_mul_self_eq_realPart_sq_add_imaginaryPart_sq x, h]⟩
  · simp [← hx.star_comm_self.eq, star_mul_self_eq_realPart_sq_add_imaginaryPart_sq, ← sq,

Depends on / 依赖: IsStarNormal, Unitary, Unitary.mem_iff, h.trans, hx.star_comm_self.eq, mem_iff, star_comm_self, star_mul_self_eq_realPart_sq_add_imaginaryPart_sq
-/
lemma mem_unitary_iff_isStarNormal_and_realPart_sq_add_imaginaryPart_sq_eq_one [Ring A]
    [StarRing A] [Module Complex A] [SMulCommClass Complex A A] [IsScalarTower Complex A A] [StarModule Complex A] {x : A} :
    x in unitary A ↔ IsStarNormal x ∧ ℜ x ^ 2 + ℑ x ^ 2 = (1 : A) := by
  rw [Unitary.mem_iff]
  refine ⟨fun ⟨h, h'⟩ => ?_, fun ⟨hx, h⟩ => ?_⟩
  · have : IsStarNormal x := ⟨h.trans h'.symm⟩
    exact ⟨this, by simp [sq, ← star_mul_self_eq_realPart_sq_add_imaginaryPart_sq x, h]⟩
  · simp [← hx.star_comm_self.eq, star_mul_self_eq_realPart_sq_add_imaginaryPart_sq, ← sq, h]

instance {F E A : Type*} [AddCommGroup E] [PartialOrder E]
    [StarAddMonoid E] [SelfAdjointDecompose E] [Module Complex E] [StarModule Complex E]
    [NonUnitalRing A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Module Complex A] [StarModule Complex A]
    [FunLike F E A] [OrderHomClass F E A] [LinearMapClass F Complex E A] :
    StarHomClass F E A where
  map_star φ x := by
    rw [← realPart_add_I_smul_imaginaryPart x]
    simp [(ℜ x).2.map' φ, IsSelfAdjoint.star_eq, (ℑ x).2.map' φ]

end RealImaginaryPart
