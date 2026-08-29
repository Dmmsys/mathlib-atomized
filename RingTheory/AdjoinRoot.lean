/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Adjoining roots of polynomials

This file defines the commutative ring `AdjoinRoot f`, the ring R[X]/(f) obtained from a
commutative ring `R` and a polynomial `f : R[X]`. If furthermore `R` is a field and `f` is
irreducible, the field structure on `AdjoinRoot f` is constructed.

We suggest stating results on `IsAdjoinRoot` instead of `AdjoinRoot` to achieve higher
generality, since `IsAdjoinRoot` works for all different constructions of `R[α]`
including `AdjoinRoot f = R[X]/(f)` itself.

## Main definitions and results

The main definitions are in the `AdjoinRoot` namespace.

* `mk f : R[X] →+* AdjoinRoot f`, the natural ring homomorphism.

* `of f : R →+* AdjoinRoot f`, the natural ring homomorphism.

* `root f : AdjoinRoot f`, the image of X in R[X]/(f).

* `lift (i : R →+* S) (x : S) (h : f.eval₂ i x = 0) : (AdjoinRoot f) →+* S`, the ring
  homomorphism from R[X]/(f) to S extending `i : R →+* S` and sending `X` to `x`.

* `lift_hom (x : S) (hfx : aeval x f = 0) : AdjoinRoot f →ₐ[R] S`, the algebra
  homomorphism from R[X]/(f) to S extending `algebraMap R S` and sending `X` to `x`

* `equiv : (AdjoinRoot f →ₐ[F] E) ≃ {x // x ∈ f.aroots E}` a
  bijection between algebra homomorphisms from `AdjoinRoot` and roots of `f` in `S`

-/

@[expose] public section

noncomputable section

open Algebra (FinitePresentation FiniteType)
open Ideal Module Polynomial

variable {R S T U K : Type*}

/--
Definition of `AdjoinRoot` / `AdjoinRoot` 的定义

English:
definition AdjoinRoot
  signature: [CommRing R] (f : R[X])
  body: Polynomial R ⧸ (span {f} : Ideal R[X])

中文:
定义 AdjoinRoot
  签名: [交换环 R] (f : R[X])
  定义体: Polynomial R ⧸ (span {f} : Ideal R[X])

Depends on / 依赖: Polynomial
-/
def AdjoinRoot [CommRing R] (f : R[X]) : Type _ :=
  Polynomial R ⧸ (span {f} : Ideal R[X])

namespace AdjoinRoot

section CommRing

variable [CommRing R] (f g : R[X])

deriving instance Inhabited for AdjoinRoot

/--
Instance `instSMulAdjoinRoot` / 实例 `instSMulAdjoinRoot`

English:
instance instSMulAdjoinRoot
  signature: [DistribSMul S R] [IsScalarTower S R R]
  body: inferInstanceAs SMul S (_ ⧸ _)

中文:
实例 instSMulAdjoinRoot
  签名: [分配标量乘法 S R] [标量塔 S R R]
  定义体: inferInstanceAs SMul S (_ ⧸ _)
-/
instance instSMulAdjoinRoot [DistribSMul S R] [IsScalarTower S R R] : SMul S (AdjoinRoot f) :=
inferInstanceAs SMul S (_ ⧸ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (AdjoinRoot f)
  body: letI := instSMulAdjoinRoot (S := Nat) (R := R); (· • ·)
  zsmul := letI := instSMulAdjoinRoot (S := Int) (R := R); (· • ·)
__ : CommRing (AdjoinRoot f) := inferInstanceAs CommRing (_ ⧸ _)

中文:
实例 :
  签名: 交换环 (AdjoinRoot f)
  定义体: letI := instSMulAdjoinRoot (S := Nat) (R := R); (· • ·)
  zsmul := letI := instSMulAdjoinRoot (S := Int) (R := R); (· • ·)
__ : CommRing (AdjoinRoot f) := inferInstanceAs CommRing (_ ⧸ _)

Depends on / 依赖: instSMulAdjoinRoot
-/
instance : CommRing (AdjoinRoot f) where
  nsmul := letI := instSMulAdjoinRoot (S := Nat) (R := R); (· • ·)
  zsmul := letI := instSMulAdjoinRoot (S := Int) (R := R); (· • ·)
__ : CommRing (AdjoinRoot f) := inferInstanceAs CommRing (_ ⧸ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: S R] [IsScalarTower S R R] : DistribSMul S (AdjoinRoot f)
  body: inferInstanceAs DistribSMul S (_ ⧸ _)

中文:
实例 [分配标量乘法
  签名: S R] [标量塔 S R R] : 分配标量乘法 S (AdjoinRoot f)
  定义体: inferInstanceAs DistribSMul S (_ ⧸ _)

Depends on / 依赖: DistribSMul
-/
instance [DistribSMul S R] [IsScalarTower S R R] : DistribSMul S (AdjoinRoot f) :=
inferInstanceAs DistribSMul S (_ ⧸ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq (AdjoinRoot f)
  body: Classical.decEq _

中文:
实例 :
  签名: DecidableEq (AdjoinRoot f)
  定义体: Classical.decEq _

Depends on / 依赖: Classical, Classical.decEq
-/
instance : DecidableEq (AdjoinRoot f) :=
  Classical.decEq _

/--
theorem `nontrivial` / 定理 `nontrivial`

English:
theorem nontrivial
  given: [IsDomain R] (h : degree f != 0)
  statement: Nontrivial (AdjoinRoot f)
  proof: by
  simp only [AdjoinRoot, Quotient.nontrivial_iff, Ne, span_singleton_eq_top,
    Polynomial.isUnit_iff, not_exists, not_and]
  rintro x hx rfl
  exact h (degree_C hx.ne_zero)

中文:
定理 nontrivial
  条件: [是整环 R] (h : degree f != 0)
  结论: 非平凡 (AdjoinRoot f)
  证明: by
  simp only [AdjoinRoot, Quotient.nontrivial_iff, Ne, span_singleton_eq_top,
    Polynomial.isUnit_iff, not_exists, not_and]
  rintro x hx rfl
  exact h (degree_C hx.ne_zero)
-/
protected theorem nontrivial [IsDomain R] (h : degree f != 0) : Nontrivial (AdjoinRoot f) := by
  simp only [AdjoinRoot, Quotient.nontrivial_iff, Ne, span_singleton_eq_top,
    Polynomial.isUnit_iff, not_exists, not_and]
  rintro x hx rfl
  exact h (degree_C hx.ne_zero)

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : R[X] ->+* AdjoinRoot f
  body: Ideal.Quotient.mk _

@[elab_as_elim]

中文:
定义 mk
  签名: : R[X] ->+* AdjoinRoot f
  定义体: Ideal.Quotient.mk _

@[elab_as_elim]

Depends on / 依赖: Ideal.Quotient.mk, Quotient
-/
def mk : R[X] ->+* AdjoinRoot f :=
  Ideal.Quotient.mk _

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: {C : AdjoinRoot f -> Prop} (x : AdjoinRoot f) (ih : forall p : R[X], C (mk f p))
  proof: Quotient.inductionOn' x ih

中文:
定理 induction_on
  条件: {C : AdjoinRoot f -> 命题} (x : AdjoinRoot f) (ih : 对任意 p : R[X], C (mk f p))
  证明: Quotient.inductionOn' x ih

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem induction_on {C : AdjoinRoot f -> Prop} (x : AdjoinRoot f) (ih : forall p : R[X], C (mk f p)) :
    C x :=
  Quotient.inductionOn' x ih

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : R ->+* AdjoinRoot f
  body: (mk f).comp C

@[simp]

中文:
定义 of
  签名: : R ->+* AdjoinRoot f
  定义体: (mk f).comp C

@[simp]
-/
def of : R ->+* AdjoinRoot f :=
  (mk f).comp C

@[simp]
/--
theorem `smul_mk` / 定理 `smul_mk`

English:
theorem smul_mk
  given: [DistribSMul S R] [IsScalarTower S R R] (a : S) (x : R[X])
  proof: rfl

中文:
定理 smul_mk
  条件: [分配标量乘法 S R] [标量塔 S R R] (a : S) (x : R[X])
  证明: rfl
-/
theorem smul_mk [DistribSMul S R] [IsScalarTower S R R] (a : S) (x : R[X]) :
    a • mk f x = mk f (a • x) :=
  rfl

/--
theorem `smul_of` / 定理 `smul_of`

English:
theorem smul_of
  given: [DistribSMul S R] [IsScalarTower S R R] (a : S) (x : R)
  proof: by rw [of, RingHom.comp_apply, RingHom.comp_apply, smul_mk, smul_C]

中文:
定理 smul_of
  条件: [分配标量乘法 S R] [标量塔 S R R] (a : S) (x : R)
  证明: by rw [of, RingHom.comp_apply, RingHom.comp_apply, smul_mk, smul_C]

Depends on / 依赖: RingHom, RingHom.comp_apply, comp_apply, smul_C, smul_mk
-/
theorem smul_of [DistribSMul S R] [IsScalarTower S R R] (a : S) (x : R) :
    a • of f x = of f (a • x) := by rw [of, RingHom.comp_apply, RingHom.comp_apply, smul_mk, smul_C]

instance (R₁ R₂ : Type*) [SMul R₁ R₂] [DistribSMul R₁ R] [DistribSMul R₂ R] [IsScalarTower R₁ R R]
    [IsScalarTower R₂ R R] [IsScalarTower R₁ R₂ R] (f : R[X]) :
    IsScalarTower R₁ R₂ (AdjoinRoot f) :=
inferInstanceAs IsScalarTower R₁ R₂ (_ ⧸ _)

instance (R₁ R₂ : Type*) [DistribSMul R₁ R] [DistribSMul R₂ R] [IsScalarTower R₁ R R]
    [IsScalarTower R₂ R R] [SMulCommClass R₁ R₂ R] (f : R[X]) :
    SMulCommClass R₁ R₂ (AdjoinRoot f) :=
inferInstanceAs SMulCommClass R₁ R₂ (_ ⧸ _)

/--
Instance `isScalarTower_right` / 实例 `isScalarTower_right`

English:
instance isScalarTower_right
  signature: [DistribSMul S R] [IsScalarTower S R R]
  body: inferInstanceAs IsScalarTower S (_ ⧸ _) (_ ⧸ _)

中文:
实例 isScalarTower_right
  签名: [分配标量乘法 S R] [标量塔 S R R]
  定义体: inferInstanceAs IsScalarTower S (_ ⧸ _) (_ ⧸ _)

Depends on / 依赖: IsScalarTower
-/
instance isScalarTower_right [DistribSMul S R] [IsScalarTower S R R] :
    IsScalarTower S (AdjoinRoot f) (AdjoinRoot f) :=
inferInstanceAs IsScalarTower S (_ ⧸ _) (_ ⧸ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [DistribMulAction S R] [IsScalarTower S R R] (f
  body: inferInstanceAs DistribMulAction S (_ ⧸ _)

中文:
实例 [幺半群
  签名: S] [分配乘法作用 S R] [标量塔 S R R] (f
  定义体: inferInstanceAs DistribMulAction S (_ ⧸ _)

Depends on / 依赖: DistribMulAction
-/
instance [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (f : R[X]) :
    DistribMulAction S (AdjoinRoot f) :=
inferInstanceAs DistribMulAction S (_ ⧸ _)

/-- `R[x]/(f)` is `R`-algebra -/
@[stacks 09FX "second part"]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: S] [Algebra S R] : Algebra S (AdjoinRoot f)
  body: inferInstanceAs Algebra S (_ ⧸ _)

中文:
实例 [交换半环
  签名: S] [代数 S R] : 代数 S (AdjoinRoot f)
  定义体: inferInstanceAs Algebra S (_ ⧸ _)

Depends on / 依赖: Algebra
-/
instance [CommSemiring S] [Algebra S R] : Algebra S (AdjoinRoot f) :=
inferInstanceAs Algebra S (_ ⧸ _)

/- TODO : generalise base ring -/
/--
Definition of `mkₐ` / `mkₐ` 的定义

English:
definition mkₐ
  signature: : R[X] ->ₐ[R] AdjoinRoot f
  body: Ideal.Quotient.mkₐ R _

中文:
定义 mkₐ
  签名: : R[X] ->ₐ[R] AdjoinRoot f
  定义体: Ideal.Quotient.mkₐ R _

Depends on / 依赖: Ideal.Quotient.mk, Quotient
-/
def mkₐ : R[X] ->ₐ[R] AdjoinRoot f :=
  Ideal.Quotient.mkₐ R _

/--
theorem `mkₐ_toRingHom` / 定理 `mkₐ_toRingHom`

English:
theorem mkₐ_toRingHom
  statement: ↑(mkₐ f) = mk f
  proof: rfl

中文:
定理 mkₐ_toRingHom
  结论: ↑(mkₐ f) = mk f
  证明: rfl
-/
@[simp, norm_cast] theorem mkₐ_toRingHom : ↑(mkₐ f) = mk f := rfl

/--
theorem `coe_mkₐ` / 定理 `coe_mkₐ`

English:
theorem coe_mkₐ
  statement: ⇑(mkₐ f) = mk f
  proof: rfl

@[simp]

中文:
定理 coe_mkₐ
  结论: ⇑(mkₐ f) = mk f
  证明: rfl

@[simp]
-/
@[simp] theorem coe_mkₐ : ⇑(mkₐ f) = mk f := rfl

@[simp]
/--
theorem `algebraMap_eq` / 定理 `algebraMap_eq`

English:
theorem algebraMap_eq
  statement: algebraMap R (AdjoinRoot f) = of f
  proof: rfl

中文:
定理 algebraMap_eq
  结论: algebraMap R (AdjoinRoot f) = of f
  证明: rfl
-/
theorem algebraMap_eq : algebraMap R (AdjoinRoot f) = of f :=
  rfl

variable (S) in
/--
theorem `algebraMap_eq'` / 定理 `algebraMap_eq'`

English:
theorem algebraMap_eq'
  given: [CommSemiring S] [Algebra S R]
  proof: rfl

中文:
定理 algebraMap_eq'
  条件: [交换半环 S] [代数 S R]
  证明: rfl
-/
theorem algebraMap_eq' [CommSemiring S] [Algebra S R] :
    algebraMap S (AdjoinRoot f) = (of f).comp (algebraMap S R) :=
  rfl

/--
Instance `finiteType` / 实例 `finiteType`

English:
instance finiteType
  signature: [CommSemiring S] [Algebra S R] [FiniteType S R]
  body: inferInstanceAs FiniteType S (_ ⧸ (_ : Ideal R[X]))

中文:
实例 finiteType
  签名: [交换半环 S] [代数 S R] [有限型 S R]
  定义体: inferInstanceAs FiniteType S (_ ⧸ (_ : Ideal R[X]))

Depends on / 依赖: FiniteType
-/
instance finiteType [CommSemiring S] [Algebra S R] [FiniteType S R] :
    FiniteType S (AdjoinRoot f) :=
inferInstanceAs FiniteType S (_ ⧸ (_ : Ideal R[X]))

/--
Instance `finitePresentation` / 实例 `finitePresentation`

English:
instance finitePresentation
  signature: [CommRing S] [Algebra S R] [FinitePresentation S R]
  body: .quotient (Submodule.fg_span_singleton f)

中文:
实例 finitePresentation
  签名: [交换环 S] [代数 S R] [有限呈现 S R]
  定义体: .quotient (Submodule.fg_span_singleton f)

Depends on / 依赖: Submodule, Submodule.fg_span_singleton, fg_span_singleton, quotient
-/
instance finitePresentation [CommRing S] [Algebra S R] [FinitePresentation S R] :
    FinitePresentation S (AdjoinRoot f) :=
  .quotient (Submodule.fg_span_singleton f)

/--
Definition of `root` / `root` 的定义

English:
definition root
  signature: : AdjoinRoot f
  body: mk f X

中文:
定义 root
  签名: : AdjoinRoot f
  定义体: mk f X
-/
def root : AdjoinRoot f :=
  mk f X

section Algebra
variable [CommSemiring S] [Semiring T] [Algebra S R] [Algebra S T] (p : R[X])

variable (S) in
/--
Definition of `ofAlgHom` / `ofAlgHom` 的定义

English:
abbreviation ofAlgHom
  signature: : R ->ₐ[S] AdjoinRoot p
  body: Algebra.algHom S R AdjoinRoot p

中文:
缩写 ofAlgHom
  签名: : R ->ₐ[S] AdjoinRoot p
  定义体: Algebra.algHom S R AdjoinRoot p

Depends on / 依赖: AdjoinRoot, Algebra, Algebra.algHom, algHom
-/
abbrev ofAlgHom : R ->ₐ[S] AdjoinRoot p := Algebra.algHom S R AdjoinRoot p

/--
lemma `toRingHom_ofAlgHom` / 引理 `toRingHom_ofAlgHom`

English:
lemma toRingHom_ofAlgHom
  statement: ofAlgHom S p = of p
  proof: rfl

中文:
引理 toRingHom_ofAlgHom
  结论: ofAlgHom S p = of p
  证明: rfl
-/
@[simp] lemma toRingHom_ofAlgHom : ofAlgHom S p = of p := rfl

/--
lemma `coe_ofAlgHom` / 引理 `coe_ofAlgHom`

English:
lemma coe_ofAlgHom
  statement: ⇑(ofAlgHom S p) = of p
  proof: rfl

中文:
引理 coe_ofAlgHom
  结论: ⇑(ofAlgHom S p) = of p
  证明: rfl
-/
@[simp] lemma coe_ofAlgHom : ⇑(ofAlgHom S p) = of p := rfl

variable {p}

@[ext high] -- This should have higher precedence than `RingHom.ext`.
/--
lemma `ringHom_ext` / 引理 `ringHom_ext`

English:
lemma ringHom_ext
  statement: {f g : AdjoinRoot p ->+* T} (hAlg : f.comp (of p) = g.comp (of p))
  proof: by
  apply Ideal.Quotient.ringHom_ext
  ext x
  · simpa using! congr($(hAlg) x)
  · simpa

@[ext high] -- This should have higher precedence than `AlgHom.ext`.

中文:
引理 ringHom_ext
  结论: {f g : AdjoinRoot p ->+* T} (hAlg : f.comp (of p) = g.comp (of p))
  证明: by
  apply Ideal.Quotient.ringHom_ext
  ext x
  · simpa using! congr($(hAlg) x)
  · simpa

@[ext high] -- This should have higher precedence than `AlgHom.ext`.

Depends on / 依赖: Ideal.Quotient.ringHom_ext, Quotient, ringHom_ext
-/
lemma ringHom_ext {f g : AdjoinRoot p ->+* T} (hAlg : f.comp (of p) = g.comp (of p))
    (hRoot : f (root p) = g (root p)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  · simpa using! congr($(hAlg) x)
  · simpa

@[ext high] -- This should have higher precedence than `AlgHom.ext`.
/--
lemma `algHom_ext'` / 引理 `algHom_ext'`

English:
lemma algHom_ext'
  statement: {f g : AdjoinRoot p ->ₐ[S] T}
  proof: by
  apply AlgHom.coe_ringHom_injective; exact ringHom_ext congr(($hAlg).toRingHom) hRoot

中文:
引理 algHom_ext'
  结论: {f g : AdjoinRoot p ->ₐ[S] T}
  证明: by
  apply AlgHom.coe_ringHom_injective; exact ringHom_ext congr(($hAlg).toRingHom) hRoot

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, coe_ringHom_injective, ringHom_ext, toRingHom
-/
lemma algHom_ext' {f g : AdjoinRoot p ->ₐ[S] T}
    (hAlg : f.comp (ofAlgHom S p) = g.comp (ofAlgHom S p))
    (hRoot : f (root p) = g (root p)) : f = g := by
  apply AlgHom.coe_ringHom_injective; exact ringHom_ext congr(($hAlg).toRingHom) hRoot

end Algebra

variable {f g}

/--
Instance `hasCoeT` / 实例 `hasCoeT`

English:
instance hasCoeT
  signature: : CoeTC R (AdjoinRoot f)
  body: ⟨of f⟩

中文:
实例 hasCoeT
  签名: : CoeTC R (AdjoinRoot f)
  定义体: ⟨of f⟩
-/
instance hasCoeT : CoeTC R (AdjoinRoot f) :=
  ⟨of f⟩

/-- Two `R`-`AlgHom` from `AdjoinRoot f` to the same `R`-algebra are the same iff
they agree on `root f`. -/
@[ext high] -- This should have higher precedence than `algHom_ext'`.
/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  statement: [Semiring S] [Algebra R S] {g₁ g₂ : AdjoinRoot f ->ₐ[R] S}
  proof: Ideal.Quotient.algHom_ext R Polynomial.algHom_ext h

@[simp]

中文:
定理 algHom_ext
  结论: [半环 S] [代数 R S] {g₁ g₂ : AdjoinRoot f ->ₐ[R] S}
  证明: Ideal.Quotient.algHom_ext R Polynomial.algHom_ext h

@[simp]

Depends on / 依赖: Ideal.Quotient.algHom_ext, Polynomial, Polynomial.algHom_ext, Quotient, algHom_ext
-/
theorem algHom_ext [Semiring S] [Algebra R S] {g₁ g₂ : AdjoinRoot f ->ₐ[R] S}
    (h : g₁ (root f) = g₂ (root f)) : g₁ = g₂ :=
Ideal.Quotient.algHom_ext R Polynomial.algHom_ext h

@[simp]
/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {g h : R[X]}
  statement: mk f g = mk f h ↔ f ∣ g - h
  proof: Ideal.Quotient.eq.trans Ideal.mem_span_singleton

@[simp]

中文:
定理 mk_eq_mk
  条件: {g h : R[X]}
  结论: mk f g = mk f h ↔ f ∣ g - h
  证明: Ideal.Quotient.eq.trans Ideal.mem_span_singleton

@[simp]

Depends on / 依赖: Ideal.Quotient.eq.trans, Ideal.mem_span_singleton, Quotient, mem_span_singleton
-/
theorem mk_eq_mk {g h : R[X]} : mk f g = mk f h ↔ f ∣ g - h :=
  Ideal.Quotient.eq.trans Ideal.mem_span_singleton

@[simp]
/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: {g : R[X]}
  statement: mk f g = 0 ↔ f ∣ g
  proof: mk_eq_mk.trans by rw [sub_zero]

@[simp]

中文:
定理 mk_eq_zero
  条件: {g : R[X]}
  结论: mk f g = 0 ↔ f ∣ g
  证明: mk_eq_mk.trans by rw [sub_zero]

@[simp]

Depends on / 依赖: mk_eq_mk, mk_eq_mk.trans, sub_zero
-/
theorem mk_eq_zero {g : R[X]} : mk f g = 0 ↔ f ∣ g :=
mk_eq_mk.trans by rw [sub_zero]

@[simp]
/--
theorem `mk_self` / 定理 `mk_self`

English:
theorem mk_self
  statement: mk f f = 0
  proof: Quotient.sound' QuotientAddGroup.leftRel_apply.mpr (mem_span_singleton.2 <| by simp)

@[simp]

中文:
定理 mk_self
  结论: mk f f = 0
  证明: Quotient.sound' QuotientAddGroup.leftRel_apply.mpr (mem_span_singleton.2 <| by simp)

@[simp]

Depends on / 依赖: Quotient, Quotient.sound, QuotientAddGroup, QuotientAddGroup.leftRel_apply.mpr, leftRel_apply, mem_span_singleton
-/
theorem mk_self : mk f f = 0 :=
Quotient.sound' QuotientAddGroup.leftRel_apply.mpr (mem_span_singleton.2 <| by simp)

@[simp]
/--
theorem `mk_C` / 定理 `mk_C`

English:
theorem mk_C
  given: (x : R)
  statement: mk f (C x) = x
  proof: rfl

@[simp]

中文:
定理 mk_C
  条件: (x : R)
  结论: mk f (C x) = x
  证明: rfl

@[simp]
-/
theorem mk_C (x : R) : mk f (C x) = x :=
  rfl

@[simp]
/--
theorem `mk_X` / 定理 `mk_X`

English:
theorem mk_X
  statement: mk f X = root f
  proof: rfl

中文:
定理 mk_X
  结论: mk f X = root f
  证明: rfl
-/
theorem mk_X : mk f X = root f :=
  rfl

/--
theorem `mk_ne_zero_of_degree_lt` / 定理 `mk_ne_zero_of_degree_lt`

English:
theorem mk_ne_zero_of_degree_lt
  given: (hf : Monic f) {g : R[X]} (h0 : g != 0) (hd : degree g < degree f)
  proof: mk_eq_zero.not.2 hf.not_dvd_of_degree_lt h0 hd

中文:
定理 mk_ne_zero_of_degree_lt
  条件: (hf : Monic f) {g : R[X]} (h0 : g != 0) (hd : degree g < degree f)
  证明: mk_eq_zero.not.2 hf.not_dvd_of_degree_lt h0 hd

Depends on / 依赖: hf.not_dvd_of_degree_lt, mk_eq_zero, mk_eq_zero.not, not_dvd_of_degree_lt
-/
theorem mk_ne_zero_of_degree_lt (hf : Monic f) {g : R[X]} (h0 : g != 0) (hd : degree g < degree f) :
    mk f g != 0 :=
mk_eq_zero.not.2 hf.not_dvd_of_degree_lt h0 hd

/--
theorem `mk_ne_zero_of_natDegree_lt` / 定理 `mk_ne_zero_of_natDegree_lt`

English:
theorem mk_ne_zero_of_natDegree_lt
  statement: (hf : Monic f) {g : R[X]} (h0 : g != 0)
  proof: mk_eq_zero.not.2 hf.not_dvd_of_natDegree_lt h0 hd

中文:
定理 mk_ne_zero_of_natDegree_lt
  结论: (hf : Monic f) {g : R[X]} (h0 : g != 0)
  证明: mk_eq_zero.not.2 hf.not_dvd_of_natDegree_lt h0 hd

Depends on / 依赖: hf.not_dvd_of_natDegree_lt, mk_eq_zero, mk_eq_zero.not, not_dvd_of_natDegree_lt
-/
theorem mk_ne_zero_of_natDegree_lt (hf : Monic f) {g : R[X]} (h0 : g != 0)
    (hd : natDegree g < natDegree f) : mk f g != 0 :=
mk_eq_zero.not.2 hf.not_dvd_of_natDegree_lt h0 hd

/--
theorem `aeval_eq_of_algebra` / 定理 `aeval_eq_of_algebra`

English:
theorem aeval_eq_of_algebra
  given: [CommRing S] [Algebra R S] (f : S[X]) (p : R[X])
  proof: by
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C, Polynomial.map_C, mk_C]
    rw [IsScalarTower.algebraMap_apply R S]
    simp
  | add p q _ _ => simp_all
  | monomial n a _ => simp_all [pow_add, ← mul_assoc]

@[simp]

中文:
定理 aeval_eq_of_algebra
  条件: [交换环 S] [代数 R S] (f : S[X]) (p : R[X])
  证明: by
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C, Polynomial.map_C, mk_C]
    rw [IsScalarTower.algebraMap_apply R S]
    simp
  | add p q _ _ => simp_all
  | monomial n a _ => simp_all [pow_add, ← mul_assoc]

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, Polynomial, Polynomial.aeval_C, Polynomial.induction_on, Polynomial.map_C, aeval_C, algebraMap_apply, induction_on, map_C, mk_C, monomial, mul_assoc, pow_add
-/
theorem aeval_eq_of_algebra [CommRing S] [Algebra R S] (f : S[X]) (p : R[X]) :
    aeval (root f) p = mk f (map (algebraMap R S) p) := by
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C, Polynomial.map_C, mk_C]
    rw [IsScalarTower.algebraMap_apply R S]
    simp
  | add p q _ _ => simp_all
  | monomial n a _ => simp_all [pow_add, ← mul_assoc]

@[simp]
/--
theorem `aeval_eq` / 定理 `aeval_eq`

English:
theorem aeval_eq
  given: (p : R[X])
  statement: aeval (root f) p = mk f p
  proof: by
  rw [aeval_eq_of_algebra]; rw [Algebra.algebraMap_self]; rw [Polynomial.map_id]

中文:
定理 aeval_eq
  条件: (p : R[X])
  结论: aeval (root f) p = mk f p
  证明: by
  rw [aeval_eq_of_algebra]; rw [Algebra.algebraMap_self]; rw [Polynomial.map_id]

Depends on / 依赖: Algebra, Algebra.algebraMap_self, Polynomial, Polynomial.map_id, aeval_eq_of_algebra, algebraMap_self, map_id
-/
theorem aeval_eq (p : R[X]) : aeval (root f) p = mk f p := by
  rw [aeval_eq_of_algebra]; rw [Algebra.algebraMap_self]; rw [Polynomial.map_id]

/--
theorem `adjoinRoot_eq_top` / 定理 `adjoinRoot_eq_top`

English:
theorem adjoinRoot_eq_top
  statement: Algebra.adjoin R ({root f} : Set (AdjoinRoot f)) = ⊤
  proof: by
  refine Algebra.eq_top_iff.2 fun x => ?_
  induction x using AdjoinRoot.induction_on with
    | ih p => exact (Algebra.adjoin_singleton_eq_range_aeval R (root f)).symm ▸ ⟨p, aeval_eq p⟩

@[simp]

中文:
定理 adjoinRoot_eq_top
  结论: 代数.adjoin R ({root f} : 集合 (AdjoinRoot f)) = ⊤
  证明: by
  refine Algebra.eq_top_iff.2 fun x => ?_
  induction x using AdjoinRoot.induction_on with
    | ih p => exact (Algebra.adjoin_singleton_eq_range_aeval R (root f)).symm ▸ ⟨p, aeval_eq p⟩

@[simp]

Depends on / 依赖: AdjoinRoot, AdjoinRoot.induction_on, Algebra, Algebra.adjoin_singleton_eq_range_aeval, Algebra.eq_top_iff, adjoin_singleton_eq_range_aeval, aeval_eq, eq_top_iff, induction_on
-/
theorem adjoinRoot_eq_top : Algebra.adjoin R ({root f} : Set (AdjoinRoot f)) = ⊤ := by
  refine Algebra.eq_top_iff.2 fun x => ?_
  induction x using AdjoinRoot.induction_on with
    | ih p => exact (Algebra.adjoin_singleton_eq_range_aeval R (root f)).symm ▸ ⟨p, aeval_eq p⟩

@[simp]
/--
theorem `eval₂_root` / 定理 `eval₂_root`

English:
theorem eval₂_root
  given: (f : R[X])
  statement: f.eval₂ (of f) (root f) = 0
  proof: by
  rw [← algebraMap_eq]; rw [← aeval_def]; rw [aeval_eq]; rw [mk_self]

中文:
定理 eval₂_root
  条件: (f : R[X])
  结论: f.eval₂ (of f) (root f) = 0
  证明: by
  rw [← algebraMap_eq]; rw [← aeval_def]; rw [aeval_eq]; rw [mk_self]

Depends on / 依赖: aeval_def, aeval_eq, algebraMap_eq, mk_self
-/
theorem eval₂_root (f : R[X]) : f.eval₂ (of f) (root f) = 0 := by
  rw [← algebraMap_eq]; rw [← aeval_def]; rw [aeval_eq]; rw [mk_self]

/--
theorem `isRoot_root` / 定理 `isRoot_root`

English:
theorem isRoot_root
  given: (f : R[X])
  statement: IsRoot (f.map (of f)) (root f)
  proof: by
  rw [IsRoot]; rw [eval_map]; rw [eval₂_root]

中文:
定理 isRoot_root
  条件: (f : R[X])
  结论: IsRoot (f.map (of f)) (root f)
  证明: by
  rw [IsRoot]; rw [eval_map]; rw [eval₂_root]

Depends on / 依赖: IsRoot, eval_map
-/
theorem isRoot_root (f : R[X]) : IsRoot (f.map (of f)) (root f) := by
  rw [IsRoot]; rw [eval_map]; rw [eval₂_root]

/--
theorem `isAlgebraic_root` / 定理 `isAlgebraic_root`

English:
theorem isAlgebraic_root
  given: (hf : f != 0)
  statement: IsAlgebraic R (root f)
  proof: ⟨f, hf, eval₂_root f⟩

中文:
定理 isAlgebraic_root
  条件: (hf : f != 0)
  结论: 是代数 R (root f)
  证明: ⟨f, hf, eval₂_root f⟩
-/
theorem isAlgebraic_root (hf : f != 0) : IsAlgebraic R (root f) :=
  ⟨f, hf, eval₂_root f⟩

/--
theorem `of.injective_of_degree_ne_zero` / 定理 `of.injective_of_degree_ne_zero`

English:
theorem of.injective_of_degree_ne_zero
  given: [IsDomain R] (hf : f.degree != 0)
  proof: by
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [AdjoinRoot.of]; rw [RingHom.comp_apply]; rw [AdjoinRoot.mk_eq_zero] at hp
  by_cases h : f = 0
  · exact C_eq_zero.mp (eq_zero_of_zero_dvd (by rwa [h] at hp))
  · contrapose! hf with h_contra
    rw [← degree_C h_contra]
    apply le_antisymm (d

中文:
定理 of.injective_of_degree_ne_zero
  条件: [是整环 R] (hf : f.degree != 0)
  证明: by
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [AdjoinRoot.of]; rw [RingHom.comp_apply]; rw [AdjoinRoot.mk_eq_zero] at hp
  by_cases h : f = 0
  · exact C_eq_zero.mp (eq_zero_of_zero_dvd (by rwa [h] at hp))
  · contrapose! hf with h_contra
    rw [← degree_C h_contra]
    apply le_antisymm (d

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk_eq_zero, AdjoinRoot.of, C_eq_zero, C_eq_zero.mp, RingHom, RingHom.comp_apply, comp_apply, contrapose, degree_C, degree_le_of_dvd, eq_zero_of_zero_dvd, h_contra, injective_iff_map_eq_zero, le_antisymm, mk_eq_zero, zero_le_degree_iff
-/
theorem of.injective_of_degree_ne_zero [IsDomain R] (hf : f.degree != 0) :
    Function.Injective (AdjoinRoot.of f) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [AdjoinRoot.of]; rw [RingHom.comp_apply]; rw [AdjoinRoot.mk_eq_zero] at hp
  by_cases h : f = 0
  · exact C_eq_zero.mp (eq_zero_of_zero_dvd (by rwa [h] at hp))
  · contrapose! hf with h_contra
    rw [← degree_C h_contra]
    apply le_antisymm (degree_le_of_dvd hp (by rwa [Ne, C_eq_zero])) _
    rwa [degree_C h_contra, zero_le_degree_iff]

variable [CommRing S]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (i : R ->+* S) (x : S) (h : f.eval₂ i x = 0)
  body: by
  apply Ideal.Quotient.lift _ (eval₂RingHom i x)
  intro g H
  rcases mem_span_singleton.1 H with ⟨y, hy⟩
  rw [hy]; rw [map_mul]; rw [coe_eval₂RingHom]; rw [h]; rw [zero_mul]

中文:
定义 lift
  签名: (i : R ->+* S) (x : S) (h : f.eval₂ i x = 0)
  定义体: by
  apply Ideal.Quotient.lift _ (eval₂RingHom i x)
  intro g H
  rcases mem_span_singleton.1 H with ⟨y, hy⟩
  rw [hy]; rw [map_mul]; rw [coe_eval₂RingHom]; rw [h]; rw [zero_mul]

Depends on / 依赖: Ideal.Quotient.lift, Quotient, map_mul, mem_span_singleton, zero_mul
-/
def lift (i : R ->+* S) (x : S) (h : f.eval₂ i x = 0) : AdjoinRoot f ->+* S := by
  apply Ideal.Quotient.lift _ (eval₂RingHom i x)
  intro g H
  rcases mem_span_singleton.1 H with ⟨y, hy⟩
  rw [hy]; rw [map_mul]; rw [coe_eval₂RingHom]; rw [h]; rw [zero_mul]

variable {i : R ->+* S} {a : S} (h : f.eval₂ i a = 0)

@[simp]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  given: (g : R[X])
  statement: lift i a h (mk f g) = g.eval₂ i a
  proof: Ideal.Quotient.lift_mk _ _ _

@[simp]

中文:
定理 lift_mk
  条件: (g : R[X])
  结论: lift i a h (mk f g) = g.eval₂ i a
  证明: Ideal.Quotient.lift_mk _ _ _

@[simp]

Depends on / 依赖: Ideal.Quotient.lift_mk, Quotient, lift_mk
-/
theorem lift_mk (g : R[X]) : lift i a h (mk f g) = g.eval₂ i a :=
  Ideal.Quotient.lift_mk _ _ _

@[simp]
/--
theorem `lift_root` / 定理 `lift_root`

English:
theorem lift_root
  statement: lift i a h (root f) = a
  proof: by rw [root, lift_mk, eval₂_X]

@[simp]

中文:
定理 lift_root
  结论: lift i a h (root f) = a
  证明: by rw [root, lift_mk, eval₂_X]

@[simp]

Depends on / 依赖: lift_mk
-/
theorem lift_root : lift i a h (root f) = a := by rw [root, lift_mk, eval₂_X]

@[simp]
/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: {x : R}
  statement: lift i a h x = i x
  proof: by rw [← mk_C x, lift_mk, eval₂_C]

@[simp]

中文:
定理 lift_of
  条件: {x : R}
  结论: lift i a h x = i x
  证明: by rw [← mk_C x, lift_mk, eval₂_C]

@[simp]

Depends on / 依赖: lift_mk, mk_C
-/
theorem lift_of {x : R} : lift i a h x = i x := by rw [← mk_C x, lift_mk, eval₂_C]

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  statement: (lift i a h).comp (of f) = i
  proof: RingHom.ext fun _ => @lift_of _ _ _ _ _ _ _ h _

中文:
定理 lift_comp_of
  结论: (lift i a h).comp (of f) = i
  证明: RingHom.ext fun _ => @lift_of _ _ _ _ _ _ _ h _

Depends on / 依赖: RingHom, RingHom.ext, lift_of
-/
theorem lift_comp_of : (lift i a h).comp (of f) = i :=
  RingHom.ext fun _ => @lift_of _ _ _ _ _ _ _ h _

section
variable [CommRing T] [Algebra S R] [Algebra S T] (p : R[X])

/--
Definition of `liftAlgHom` / `liftAlgHom` 的定义

English:
definition liftAlgHom
  signature: (i : R ->ₐ[S] T) (x : T) (h : p.eval₂ i x = 0)
  body: lift i.toRingHom _ h
  commutes' r := by simp [lift_of h, AdjoinRoot.algebraMap_eq']

中文:
定义 liftAlgHom
  签名: (i : R ->ₐ[S] T) (x : T) (h : p.eval₂ i x = 0)
  定义体: lift i.toRingHom _ h
  commutes' r := by simp [lift_of h, AdjoinRoot.algebraMap_eq']

Depends on / 依赖: i.toRingHom, toRingHom
-/
def liftAlgHom (i : R ->ₐ[S] T) (x : T) (h : p.eval₂ i x = 0) : AdjoinRoot p ->ₐ[S] T where
  __ := lift i.toRingHom _ h
  commutes' r := by simp [lift_of h, AdjoinRoot.algebraMap_eq']

/--
lemma `toRingHom_liftAlgHom` / 引理 `toRingHom_liftAlgHom`

English:
lemma toRingHom_liftAlgHom
  given: (i : R ->ₐ[S] T) (x : T) (h)
  proof: rfl

中文:
引理 toRingHom_liftAlgHom
  条件: (i : R ->ₐ[S] T) (x : T) (h)
  证明: rfl
-/
@[simp] lemma toRingHom_liftAlgHom (i : R ->ₐ[S] T) (x : T) (h) :
    (liftAlgHom p i x h : AdjoinRoot p ->+* T) = lift i.toRingHom _ h := rfl

/--
lemma `coe_liftAlgHom` / 引理 `coe_liftAlgHom`

English:
lemma coe_liftAlgHom
  given: (i : R ->ₐ[S] T) (x : T) (h)
  statement: ⇑(liftAlgHom p i x h) = lift i.toRingHom _ h
  proof: rfl

@[simp]

中文:
引理 coe_liftAlgHom
  条件: (i : R ->ₐ[S] T) (x : T) (h)
  结论: ⇑(liftAlgHom p i x h) = lift i.toRingHom _ h
  证明: rfl

@[simp]
-/
lemma coe_liftAlgHom (i : R ->ₐ[S] T) (x : T) (h) : ⇑(liftAlgHom p i x h) = lift i.toRingHom _ h :=
  rfl

@[simp]
/--
lemma `liftAlgHom_of` / 引理 `liftAlgHom_of`

English:
lemma liftAlgHom_of
  given: (i : R ->ₐ[S] T) (x : T) (h) (r : R)
  statement: liftAlgHom p i x h (of p r) = i r
  proof: by
  simp [liftAlgHom]

@[simp]

中文:
引理 liftAlgHom_of
  条件: (i : R ->ₐ[S] T) (x : T) (h) (r : R)
  结论: liftAlgHom p i x h (of p r) = i r
  证明: by
  simp [liftAlgHom]

@[simp]

Depends on / 依赖: liftAlgHom
-/
lemma liftAlgHom_of (i : R ->ₐ[S] T) (x : T) (h) (r : R) : liftAlgHom p i x h (of p r) = i r := by
  simp [liftAlgHom]

@[simp]
/--
lemma `liftAlgHom_mk` / 引理 `liftAlgHom_mk`

English:
lemma liftAlgHom_mk
  given: (i : R ->ₐ[S] T) (x : T) (h) (f : R[X])
  proof: rfl

@[simp]

中文:
引理 liftAlgHom_mk
  条件: (i : R ->ₐ[S] T) (x : T) (h) (f : R[X])
  证明: rfl

@[simp]
-/
lemma liftAlgHom_mk (i : R ->ₐ[S] T) (x : T) (h) (f : R[X]) :
    liftAlgHom p i x h (mk p f) = eval₂ i x f := rfl

@[simp]
/--
lemma `liftAlgHom_root` / 引理 `liftAlgHom_root`

English:
lemma liftAlgHom_root
  given: (i : R ->ₐ[S] T) (x : T) (h)
  statement: liftAlgHom p i x h (root p) = x
  proof: by
  simp [liftAlgHom]

中文:
引理 liftAlgHom_root
  条件: (i : R ->ₐ[S] T) (x : T) (h)
  结论: liftAlgHom p i x h (root p) = x
  证明: by
  simp [liftAlgHom]

Depends on / 依赖: liftAlgHom
-/
lemma liftAlgHom_root (i : R ->ₐ[S] T) (x : T) (h) : liftAlgHom p i x h (root p) = x := by
  simp [liftAlgHom]

end

section deprecated
variable (f) [Algebra R S]

@[simp]
/--
theorem `aeval_algHom_eq_zero` / 定理 `aeval_algHom_eq_zero`

English:
theorem aeval_algHom_eq_zero
  given: (ϕ : AdjoinRoot f ->ₐ[R] S)
  statement: aeval (ϕ (root f)) f = 0
  proof: by
  have h : ϕ.toRingHom.comp (of f) = algebraMap R S := RingHom.ext_iff.mpr ϕ.commutes
  rw [aeval_def]; rw [← h]; rw [← map_zero ϕ.toRingHom]; rw [← eval₂_root f]; rw [hom_eval₂]
  rfl

中文:
定理 aeval_algHom_eq_zero
  条件: (ϕ : AdjoinRoot f ->ₐ[R] S)
  结论: aeval (ϕ (root f)) f = 0
  证明: by
  have h : ϕ.toRingHom.comp (of f) = algebraMap R S := RingHom.ext_iff.mpr ϕ.commutes
  rw [aeval_def]; rw [← h]; rw [← map_zero ϕ.toRingHom]; rw [← eval₂_root f]; rw [hom_eval₂]
  rfl

Depends on / 依赖: RingHom, RingHom.ext_iff.mpr, aeval_def, algebraMap, commutes, ext_iff, map_zero, toRingHom, toRingHom.comp
-/
theorem aeval_algHom_eq_zero (ϕ : AdjoinRoot f ->ₐ[R] S) : aeval (ϕ (root f)) f = 0 := by
  have h : ϕ.toRingHom.comp (of f) = algebraMap R S := RingHom.ext_iff.mpr ϕ.commutes
  rw [aeval_def]; rw [← h]; rw [← map_zero ϕ.toRingHom]; rw [← eval₂_root f]; rw [hom_eval₂]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `liftAlgHom_eq_algHom` / 定理 `liftAlgHom_eq_algHom`

English:
theorem liftAlgHom_eq_algHom
  given: (ϕ : AdjoinRoot f ->ₐ[R] S)
  proof: by
  ext
  simp

中文:
定理 liftAlgHom_eq_algHom
  条件: (ϕ : AdjoinRoot f ->ₐ[R] S)
  证明: by
  ext
  simp
-/
theorem liftAlgHom_eq_algHom (ϕ : AdjoinRoot f ->ₐ[R] S) :
    liftAlgHom f (Algebra.ofId R S) (ϕ (root f)) (aeval_algHom_eq_zero f ϕ) = ϕ := by
  ext
  simp

end deprecated

section AdjoinInv

@[simp]
/--
theorem `root_isInv` / 定理 `root_isInv`

English:
theorem root_isInv
  given: (r : R)
  statement: of _ r * root (C r * X - 1) = 1
  proof: by
  convert! sub_eq_zero.1 ((eval₂_sub _).symm.trans <| eval₂_root <| C r * X - 1) <;>
    simp only [eval₂_mul, eval₂_C, eval₂_X, eval₂_one]

中文:
定理 root_isInv
  条件: (r : R)
  结论: of _ r * root (C r * X - 1) = 1
  证明: by
  convert! sub_eq_zero.1 ((eval₂_sub _).symm.trans <| eval₂_root <| C r * X - 1) <;>
    simp only [eval₂_mul, eval₂_C, eval₂_X, eval₂_one]

Depends on / 依赖: convert, sub_eq_zero, symm.trans
-/
theorem root_isInv (r : R) : of _ r * root (C r * X - 1) = 1 := by
  convert! sub_eq_zero.1 ((eval₂_sub _).symm.trans <| eval₂_root <| C r * X - 1) <;>
    simp only [eval₂_mul, eval₂_C, eval₂_X, eval₂_one]

/--
theorem `algHom_subsingleton` / 定理 `algHom_subsingleton`

English:
theorem algHom_subsingleton
  given: {S : Type*} [CommRing S] [Algebra R S] {r : R}
  proof: ⟨fun f g =>
    algHom_ext
      (@inv_unique _ _ (algebraMap R S r) _ _
        (by rw [← f.commutes, ← map_mul, algebraMap_eq, root_isInv, map_one])
        (by rw [← g.commutes, ← map_mul, algebraMap_eq, root_isInv, map_one]))⟩

中文:
定理 algHom_subsingleton
  条件: {S : 类型} [交换环 S] [代数 R S] {r : R}
  证明: ⟨fun f g =>
    algHom_ext
      (@inv_unique _ _ (algebraMap R S r) _ _
        (by rw [← f.commutes, ← map_mul, algebraMap_eq, root_isInv, map_one])
        (by rw [← g.commutes, ← map_mul, algebraMap_eq, root_isInv, map_one]))⟩

Depends on / 依赖: algHom_ext, algebraMap, algebraMap_eq, commutes, f.commutes, g.commutes, inv_unique, map_mul, map_one, root_isInv
-/
theorem algHom_subsingleton {S : Type*} [CommRing S] [Algebra R S] {r : R} :
    Subsingleton (AdjoinRoot (C r * X - 1) ->ₐ[R] S) :=
  ⟨fun f g =>
    algHom_ext
      (@inv_unique _ _ (algebraMap R S r) _ _
        (by rw [← f.commutes, ← map_mul, algebraMap_eq, root_isInv, map_one])
        (by rw [← g.commutes, ← map_mul, algebraMap_eq, root_isInv, map_one]))⟩

end AdjoinInv

section Prime

/--
theorem `isDomain_of_prime` / 定理 `isDomain_of_prime`

English:
theorem isDomain_of_prime
  given: (hf : Prime f)
  statement: IsDomain (AdjoinRoot f)
  proof: (Ideal.Quotient.isDomain_iff_prime (span {f} : Ideal R[X])).mpr
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf

中文:
定理 isDomain_of_prime
  条件: (hf : 素 f)
  结论: 是整环 (AdjoinRoot f)
  证明: (Ideal.Quotient.isDomain_iff_prime (span {f} : Ideal R[X])).mpr
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf

Depends on / 依赖: Ideal.Quotient.isDomain_iff_prime, Ideal.span_singleton_prime, Quotient, hf.ne_zero, isDomain_iff_prime, ne_zero, span_singleton_prime
-/
theorem isDomain_of_prime (hf : Prime f) : IsDomain (AdjoinRoot f) :=
(Ideal.Quotient.isDomain_iff_prime (span {f} : Ideal R[X])).mpr
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf

/--
theorem `noZeroSMulDivisors_of_prime_of_degree_ne_zero` / 定理 `noZeroSMulDivisors_of_prime_of_degree_ne_zero`

English:
theorem noZeroSMulDivisors_of_prime_of_degree_ne_zero
  statement: [IsDomain R] (hf : Prime f)
  proof: haveI := isDomain_of_prime hf
  isTorsionFree_iff_algebraMap_injective.mpr (of.injective_of_degree_ne_zero hf')

中文:
定理 noZeroSMulDivisors_of_prime_of_degree_ne_zero
  结论: [是整环 R] (hf : 素 f)
  证明: haveI := isDomain_of_prime hf
  isTorsionFree_iff_algebraMap_injective.mpr (of.injective_of_degree_ne_zero hf')

Depends on / 依赖: injective_of_degree_ne_zero, isDomain_of_prime, isTorsionFree_iff_algebraMap_injective, isTorsionFree_iff_algebraMap_injective.mpr, of.injective_of_degree_ne_zero
-/
theorem noZeroSMulDivisors_of_prime_of_degree_ne_zero [IsDomain R] (hf : Prime f)
    (hf' : f.degree != 0) : IsTorsionFree R (AdjoinRoot f) :=
  haveI := isDomain_of_prime hf
  isTorsionFree_iff_algebraMap_injective.mpr (of.injective_of_degree_ne_zero hf')

end Prime

variable [CommRing T]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S) (p : R[X]) (q : S[X]) (h : q ∣ p.map f)
  body: lift ((of _).comp f) (root q) by simpa [← Polynomial.eval₂_map, ← algebraMap_eq, ← aeval_def]

中文:
定义 map
  签名: (f : R ->+* S) (p : R[X]) (q : S[X]) (h : q ∣ p.map f)
  定义体: lift ((of _).comp f) (root q) by simpa [← Polynomial.eval₂_map, ← algebraMap_eq, ← aeval_def]

Depends on / 依赖: Polynomial, Polynomial.eval, aeval_def, algebraMap_eq
-/
def map (f : R ->+* S) (p : R[X]) (q : S[X]) (h : q ∣ p.map f) : AdjoinRoot p ->+* AdjoinRoot q :=
lift ((of _).comp f) (root q) by simpa [← Polynomial.eval₂_map, ← algebraMap_eq, ← aeval_def]

/--
lemma `map_of` / 引理 `map_of`

English:
lemma map_of
  given: (f : R ->+* S) (p : R[X]) (q : S[X]) (h) (r : R)
  proof: by simp [map]

中文:
引理 map_of
  条件: (f : R ->+* S) (p : R[X]) (q : S[X]) (h) (r : R)
  证明: by simp [map]
-/
@[simp] lemma map_of (f : R ->+* S) (p : R[X]) (q : S[X]) (h) (r : R) :
    map f p q h (of p r) = f r := by simp [map]

/--
lemma `map_root` / 引理 `map_root`

English:
lemma map_root
  given: (f : R ->+* S) (p : R[X]) (q : S[X]) (h)
  statement: map f p q h (root p) = root q
  proof: by
  simp [map]

中文:
引理 map_root
  条件: (f : R ->+* S) (p : R[X]) (q : S[X]) (h)
  结论: map f p q h (root p) = root q
  证明: by
  simp [map]
-/
@[simp] lemma map_root (f : R ->+* S) (p : R[X]) (q : S[X]) (h) : map f p q h (root p) = root q := by
  simp [map]

/--
lemma `map_comp_map` / 引理 `map_comp_map`

English:
lemma map_comp_map
  given: (f : R ->+* S) (g : S ->+* T) (p : R[X]) (q : S[X]) (r : T[X]) (hf hg)
  proof: by ext <;> simp

中文:
引理 map_comp_map
  条件: (f : R ->+* S) (g : S ->+* T) (p : R[X]) (q : S[X]) (r : T[X]) (hf hg)
  证明: by ext <;> simp
-/
lemma map_comp_map (f : R ->+* S) (g : S ->+* T) (p : R[X]) (q : S[X]) (r : T[X]) (hf hg) :
    (map g q r hg).comp (map f p q hf) =
      map (g.comp f) p r
        (hg.trans <| by simpa [Polynomial.map_map] using Polynomial.map_dvd g hf) := by ext <;> simp

/--
Definition of `mapRingEquiv` / `mapRingEquiv` 的定义

English:
definition mapRingEquiv
  signature: (f : R ≃+* S) (p : R[X]) (q : S[X]) (h : Associated (p.map f) q)
  body: .ofRingHom
    (map f p q h.symm.dvd)
    (map f.symm q p <| by
      simpa [Polynomial.map_map] using map_dvd f.symm.toRingHom h.dvd)
    (by ext <;> simp) (by ext <;> simp)

中文:
定义 mapRingEquiv
  签名: (f : R ≃+* S) (p : R[X]) (q : S[X]) (h : Associated (p.map f) q)
  定义体: .ofRingHom
    (map f p q h.symm.dvd)
    (map f.symm q p <| by
      simpa [Polynomial.map_map] using map_dvd f.symm.toRingHom h.dvd)
    (by ext <;> simp) (by ext <;> simp)

Depends on / 依赖: Polynomial, Polynomial.map_map, f.symm, f.symm.toRingHom, h.dvd, h.symm.dvd, map_dvd, map_map, ofRingHom, toRingHom
-/
def mapRingEquiv (f : R ≃+* S) (p : R[X]) (q : S[X]) (h : Associated (p.map f) q) :
    AdjoinRoot p ≃+* AdjoinRoot q :=
  .ofRingHom
    (map f p q h.symm.dvd)
    (map f.symm q p <| by
      simpa [Polynomial.map_map] using map_dvd f.symm.toRingHom h.dvd)
    (by ext <;> simp) (by ext <;> simp)

/--
lemma `coe_mapRingEquiv` / 引理 `coe_mapRingEquiv`

English:
lemma coe_mapRingEquiv
  given: (f : R ≃+* S) (p : R[X]) (q : S[X]) (h)
  proof: rfl

中文:
引理 coe_mapRingEquiv
  条件: (f : R ≃+* S) (p : R[X]) (q : S[X]) (h)
  证明: rfl
-/
@[simp] lemma coe_mapRingEquiv (f : R ≃+* S) (p : R[X]) (q : S[X]) (h) :
    ⇑(mapRingEquiv f p q h) = map f p q h.symm.dvd := rfl

/--
lemma `symm_mapRingEquiv` / 引理 `symm_mapRingEquiv`

English:
lemma symm_mapRingEquiv
  given: (f : R ≃+* S) (p : R[X]) (q : S[X]) (h)
  proof: rfl

中文:
引理 symm_mapRingEquiv
  条件: (f : R ≃+* S) (p : R[X]) (q : S[X]) (h)
  证明: rfl
-/
@[simp] lemma symm_mapRingEquiv (f : R ≃+* S) (p : R[X]) (q : S[X]) (h) :
    (mapRingEquiv f p q h).symm = mapRingEquiv f.symm q p (by
      simpa [Polynomial.map_map] using associated_map_map f.symm.toRingHom h.symm) := rfl

variable [CommRing U] [Algebra R S] [Algebra R T] [Algebra R U]

/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: (f : S ->ₐ[R] T) (p : S[X]) (q : T[X]) (h : q ∣ p.map f)
  body: map f p q h
  commutes' r := by simp [map, AdjoinRoot.algebraMap_eq']

中文:
定义 mapAlgHom
  签名: (f : S ->ₐ[R] T) (p : S[X]) (q : T[X]) (h : q ∣ p.map f)
  定义体: map f p q h
  commutes' r := by simp [map, AdjoinRoot.algebraMap_eq']
-/
def mapAlgHom (f : S ->ₐ[R] T) (p : S[X]) (q : T[X]) (h : q ∣ p.map f) :
    AdjoinRoot p ->ₐ[R] AdjoinRoot q where
  __ := map f p q h
  commutes' r := by simp [map, AdjoinRoot.algebraMap_eq']

/--
lemma `coe_mapAlgHom` / 引理 `coe_mapAlgHom`

English:
lemma coe_mapAlgHom
  given: (f : S ->ₐ[R] T) (p : S[X]) (q : T[X]) (h)
  proof: rfl

中文:
引理 coe_mapAlgHom
  条件: (f : S ->ₐ[R] T) (p : S[X]) (q : T[X]) (h)
  证明: rfl
-/
@[simp] lemma coe_mapAlgHom (f : S ->ₐ[R] T) (p : S[X]) (q : T[X]) (h) :
    ⇑(mapAlgHom f p q h) = map f p q h := rfl

/--
lemma `mapAlgHom_comp_mapAlghom` / 引理 `mapAlgHom_comp_mapAlghom`

English:
lemma mapAlgHom_comp_mapAlghom
  statement: (f : S ->ₐ[R] T) (g : T ->ₐ[R] U) (p : S[X]) (q : T[X]) (r : U[X])
  proof: by
  aesop

中文:
引理 mapAlgHom_comp_mapAlghom
  结论: (f : S ->ₐ[R] T) (g : T ->ₐ[R] U) (p : S[X]) (q : T[X]) (r : U[X])
  证明: by
  aesop
-/
lemma mapAlgHom_comp_mapAlghom (f : S ->ₐ[R] T) (g : T ->ₐ[R] U) (p : S[X]) (q : T[X]) (r : U[X])
    (hf hg) :
    (mapAlgHom g q r hg).comp (mapAlgHom f p q hf) =
      mapAlgHom (g.comp f) p r
        (hg.trans <| by simpa [Polynomial.map_map] using! Polynomial.map_dvd g.toRingHom hf) := by
  aesop

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapAlgEquiv` / `mapAlgEquiv` 的定义

English:
definition mapAlgEquiv
  signature: (f : S ≃ₐ[R] T) (p : S[X]) (q : T[X]) (h : Associated (p.map f) q)
  body: .ofAlgHom
    (mapAlgHom f p q h.symm.dvd)
    (mapAlgHom f.symm q p <| by
      -- FIXME: Coercion hell. See https://github.com/leanprover-community/mathlib4/issues/31365.
      have : (RingHomClass.toRingHom f.toRingEquiv.symm).comp (RingHomClass.toRingHom f) =
        .id S := by ext; exact f.sym

中文:
定义 mapAlgEquiv
  签名: (f : S ≃ₐ[R] T) (p : S[X]) (q : T[X]) (h : Associated (p.map f) q)
  定义体: .ofAlgHom
    (mapAlgHom f p q h.symm.dvd)
    (mapAlgHom f.symm q p <| by
      -- FIXME: Coercion hell. See https://github.com/leanprover-community/mathlib4/issues/31365.
      have : (RingHomClass.toRingHom f.toRingEquiv.symm).comp (RingHomClass.toRingHom f) =
        .id S := by ext; exact f.sym

Depends on / 依赖: f.symm, h.symm.dvd, mapAlgHom, ofAlgHom
-/
def mapAlgEquiv (f : S ≃ₐ[R] T) (p : S[X]) (q : T[X]) (h : Associated (p.map f) q) :
    AdjoinRoot p ≃ₐ[R] AdjoinRoot q :=
  .ofAlgHom
    (mapAlgHom f p q h.symm.dvd)
    (mapAlgHom f.symm q p <| by
      -- FIXME: Coercion hell. See https://github.com/leanprover-community/mathlib4/issues/31365.
      have : (RingHomClass.toRingHom f.toRingEquiv.symm).comp (RingHomClass.toRingHom f) =
        .id S := by ext; exact f.symm_apply_apply _
      simpa [Polynomial.map_map, -RingEquiv.symm_mk, this] using! map_dvd f.symm.toRingHom h.dvd)
    (by ext <;> simp) (by ext <;> simp)

/--
lemma `coe_mapAlgEquiv` / 引理 `coe_mapAlgEquiv`

English:
lemma coe_mapAlgEquiv
  given: (f : S ≃ₐ[R] T) (p : S[X]) (q : T[X]) (h)
  proof: rfl

中文:
引理 coe_mapAlgEquiv
  条件: (f : S ≃ₐ[R] T) (p : S[X]) (q : T[X]) (h)
  证明: rfl
-/
@[simp] lemma coe_mapAlgEquiv (f : S ≃ₐ[R] T) (p : S[X]) (q : T[X]) (h) :
    ⇑(mapAlgEquiv f p q h) = map f p q h.symm.dvd := rfl

/--
lemma `symm_mapAlgEquiv` / 引理 `symm_mapAlgEquiv`

English:
lemma symm_mapAlgEquiv
  given: (f : S ≃ₐ[R] T) (p : S[X]) (q : T[X]) (h)
  proof: rfl

中文:
引理 symm_mapAlgEquiv
  条件: (f : S ≃ₐ[R] T) (p : S[X]) (q : T[X]) (h)
  证明: rfl
-/
@[simp] lemma symm_mapAlgEquiv (f : S ≃ₐ[R] T) (p : S[X]) (q : T[X]) (h) :
    (mapAlgEquiv f p q h).symm = mapAlgEquiv f.symm q p (by
      -- FIXME: Coercion hell. See https://github.com/leanprover-community/mathlib4/issues/31365.
      have : (RingHomClass.toRingHom f.toRingEquiv.symm).comp (RingHomClass.toRingHom f) =
        .id S := by ext; exact f.symm_apply_apply _
      simpa [Polynomial.map_map, -RingEquiv.symm_mk, this]
        using! associated_map_map f.symm.toRingHom h.symm) := rfl

variable (R) in
/--
Definition of `algHomOfDvd` / `algHomOfDvd` 的定义

English:
definition algHomOfDvd
  signature: (f g : S[X]) (hgf : g ∣ f)
  body: mapAlgHom (.id R S) _ _ by simpa

中文:
定义 algHomOfDvd
  签名: (f g : S[X]) (hgf : g ∣ f)
  定义体: mapAlgHom (.id R S) _ _ by simpa

Depends on / 依赖: mapAlgHom
-/
noncomputable def algHomOfDvd (f g : S[X]) (hgf : g ∣ f) : AdjoinRoot f ->ₐ[R] AdjoinRoot g :=
mapAlgHom (.id R S) _ _ by simpa

/--
lemma `coe_algHomOfDvd` / 引理 `coe_algHomOfDvd`

English:
lemma coe_algHomOfDvd
  given: (f g : S[X]) (hgf)
  proof: rfl

中文:
引理 coe_algHomOfDvd
  条件: (f g : S[X]) (hgf)
  证明: rfl
-/
lemma coe_algHomOfDvd (f g : S[X]) (hgf) :
    ⇑(algHomOfDvd R f g hgf) =
      liftAlgHom f (Algebra.ofId ..) (root g) ((aeval_eq _).trans <| by simp [mk_eq_zero, hgf]) :=
  rfl

/--
lemma `algHomOfDvd_root` / 引理 `algHomOfDvd_root`

English:
lemma algHomOfDvd_root
  given: (f g : S[X]) (hgf)
  statement: algHomOfDvd R f g hgf (root f) = root g
  proof: by
  simp [algHomOfDvd]

中文:
引理 algHomOfDvd_root
  条件: (f g : S[X]) (hgf)
  结论: algHomOfDvd R f g hgf (root f) = root g
  证明: by
  simp [algHomOfDvd]
-/
@[simp] lemma algHomOfDvd_root (f g : S[X]) (hgf) : algHomOfDvd R f g hgf (root f) = root g := by
  simp [algHomOfDvd]

variable (R) in
/--
Definition of `algEquivOfAssociated` / `algEquivOfAssociated` 的定义

English:
definition algEquivOfAssociated
  signature: (f g : S[X]) (hfg : Associated f g)
  body: mapAlgEquiv .refl f g by simpa

中文:
定义 algEquivOfAssociated
  签名: (f g : S[X]) (hfg : Associated f g)
  定义体: mapAlgEquiv .refl f g by simpa

Depends on / 依赖: mapAlgEquiv
-/
noncomputable def algEquivOfAssociated (f g : S[X]) (hfg : Associated f g) :
AdjoinRoot f ≃ₐ[R] AdjoinRoot g := mapAlgEquiv .refl f g by simpa

/--
lemma `coe_algEquivOfAssociated` / 引理 `coe_algEquivOfAssociated`

English:
lemma coe_algEquivOfAssociated
  given: (f g : S[X]) (hfg)
  proof: rfl

中文:
引理 coe_algEquivOfAssociated
  条件: (f g : S[X]) (hfg)
  证明: rfl
-/
lemma coe_algEquivOfAssociated (f g : S[X]) (hfg) :
    ⇑(algEquivOfAssociated R f g hfg) = algHomOfDvd R f g hfg.symm.dvd := rfl

/--
lemma `algEquivOfAssociated_symm` / 引理 `algEquivOfAssociated_symm`

English:
lemma algEquivOfAssociated_symm
  given: (f g : S[X]) (hfg)
  proof: rfl

中文:
引理 algEquivOfAssociated_symm
  条件: (f g : S[X]) (hfg)
  证明: rfl
-/
@[simp] lemma algEquivOfAssociated_symm (f g : S[X]) (hfg) :
    (algEquivOfAssociated R f g hfg).symm = algEquivOfAssociated R g f hfg.symm := rfl

/--
lemma `algEquivOfAssociated_toAlgHom` / 引理 `algEquivOfAssociated_toAlgHom`

English:
lemma algEquivOfAssociated_toAlgHom
  given: (f g : S[X]) (hfg)
  proof: rfl

中文:
引理 algEquivOfAssociated_toAlgHom
  条件: (f g : S[X]) (hfg)
  证明: rfl
-/
lemma algEquivOfAssociated_toAlgHom (f g : S[X]) (hfg) :
    (algEquivOfAssociated R f g hfg).toAlgHom = algHomOfDvd R f g hfg.symm.dvd := rfl

/--
lemma `algEquivOfAssociated_root` / 引理 `algEquivOfAssociated_root`

English:
lemma algEquivOfAssociated_root
  given: (f g : S[X]) (hfg)
  proof: by
  rw [coe_algEquivOfAssociated]; rw [algHomOfDvd_root]

中文:
引理 algEquivOfAssociated_root
  条件: (f g : S[X]) (hfg)
  证明: by
  rw [coe_algEquivOfAssociated]; rw [algHomOfDvd_root]
-/
@[simp] lemma algEquivOfAssociated_root (f g : S[X]) (hfg) :
    algEquivOfAssociated R f g hfg (root f) = root g := by
  rw [coe_algEquivOfAssociated]; rw [algHomOfDvd_root]

variable (R) in
/--
Definition of `algEquivOfEq` / `algEquivOfEq` 的定义

English:
definition algEquivOfEq
  signature: (f g : S[X]) (hfg : f = g)
  body: algEquivOfAssociated R f g (by rw [hfg])

中文:
定义 algEquivOfEq
  签名: (f g : S[X]) (hfg : f = g)
  定义体: algEquivOfAssociated R f g (by rw [hfg])

Depends on / 依赖: algEquivOfAssociated
-/
noncomputable def algEquivOfEq (f g : S[X]) (hfg : f = g) : AdjoinRoot f ≃ₐ[R] AdjoinRoot g :=
  algEquivOfAssociated R f g (by rw [hfg])

/--
lemma `coe_algEquivOfEq` / 引理 `coe_algEquivOfEq`

English:
lemma coe_algEquivOfEq
  given: (f g : S[X]) (hfg)
  proof: rfl

中文:
引理 coe_algEquivOfEq
  条件: (f g : S[X]) (hfg)
  证明: rfl
-/
lemma coe_algEquivOfEq (f g : S[X]) (hfg) :
    ⇑(algEquivOfEq R f g hfg) = algHomOfDvd R f g hfg.symm.dvd := rfl

/--
lemma `algEquivOfEq_symm` / 引理 `algEquivOfEq_symm`

English:
lemma algEquivOfEq_symm
  given: (f g : S[X]) (hfg)
  proof: rfl

中文:
引理 algEquivOfEq_symm
  条件: (f g : S[X]) (hfg)
  证明: rfl
-/
@[simp] lemma algEquivOfEq_symm (f g : S[X]) (hfg) :
    (algEquivOfEq R f g hfg).symm = algEquivOfEq R g f hfg.symm := rfl

/--
lemma `algEquivOfEq_toAlgHom` / 引理 `algEquivOfEq_toAlgHom`

English:
lemma algEquivOfEq_toAlgHom
  given: (f g : S[X]) (hfg)
  proof: rfl

中文:
引理 algEquivOfEq_toAlgHom
  条件: (f g : S[X]) (hfg)
  证明: rfl
-/
lemma algEquivOfEq_toAlgHom (f g : S[X]) (hfg) :
    (algEquivOfEq R f g hfg).toAlgHom = algHomOfDvd R f g hfg.symm.dvd := rfl

/--
lemma `algEquivOfEq_root` / 引理 `algEquivOfEq_root`

English:
lemma algEquivOfEq_root
  given: (f g : S[X]) (hfg)
  statement: algEquivOfEq R f g hfg (root f) = root g
  proof: by
  rw [coe_algEquivOfEq]; rw [algHomOfDvd_root]

中文:
引理 algEquivOfEq_root
  条件: (f g : S[X]) (hfg)
  结论: algEquivOfEq R f g hfg (root f) = root g
  证明: by
  rw [coe_algEquivOfEq]; rw [algHomOfDvd_root]

Depends on / 依赖: algHomOfDvd_root, coe_algEquivOfEq
-/
lemma algEquivOfEq_root (f g : S[X]) (hfg) : algEquivOfEq R f g hfg (root f) = root g := by
  rw [coe_algEquivOfEq]; rw [algHomOfDvd_root]

end CommRing

section Irreducible

variable [Field K] {f : K[X]}

/--
Instance `span_maximal_of_irreducible` / 实例 `span_maximal_of_irreducible`

English:
instance span_maximal_of_irreducible
  signature: [Fact (Irreducible f)]
  body: PrincipalIdealRing.isMaximal_of_irreducible Fact.out

中文:
实例 span_maximal_of_irreducible
  签名: [Fact (不可约 f)]
  定义体: PrincipalIdealRing.isMaximal_of_irreducible Fact.out

Depends on / 依赖: Fact.out, PrincipalIdealRing, PrincipalIdealRing.isMaximal_of_irreducible, isMaximal_of_irreducible
-/
instance span_maximal_of_irreducible [Fact (Irreducible f)] : (span {f}).IsMaximal :=
PrincipalIdealRing.isMaximal_of_irreducible Fact.out

/--
Instance `instGroupWithZero` / 实例 `instGroupWithZero`

English:
instance instGroupWithZero
  signature: [Fact (Irreducible f)]
  body: fast_instance% Quotient.groupWithZero (span {f} : Ideal K[X])

中文:
实例 instGroupWithZero
  签名: [Fact (不可约 f)]
  定义体: fast_instance% Quotient.groupWithZero (span {f} : Ideal K[X])

Depends on / 依赖: Quotient, Quotient.groupWithZero, fast_instance, groupWithZero
-/
noncomputable instance instGroupWithZero [Fact (Irreducible f)] : GroupWithZero (AdjoinRoot f) :=
  fast_instance% Quotient.groupWithZero (span {f} : Ideal K[X])

/-- If `R` is a field and `f` is irreducible, then `AdjoinRoot f` is a field -/
@[stacks 09FX "first part, see also 09FI"]
/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: [Fact (Irreducible f)]
  body: instCommRing _
  __ := instGroupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by
    rw [← map_natCast (of f)]; rw [← map_natCast (of f)]; rw [← map_div₀]; rw [← NNRat.cast_def]; rfl
  ratCast_def q := by
    rw [← map_natCast (of f)]; rw [← map_intCast (of f)]; rw [← map_div

中文:
实例 instField
  签名: [Fact (不可约 f)]
  定义体: instCommRing _
  __ := instGroupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by
    rw [← map_natCast (of f)]; rw [← map_natCast (of f)]; rw [← map_div₀]; rw [← NNRat.cast_def]; rfl
  ratCast_def q := by
    rw [← map_natCast (of f)]; rw [← map_intCast (of f)]; rw [← map_div

Depends on / 依赖: instCommRing
-/
noncomputable instance instField [Fact (Irreducible f)] : Field (AdjoinRoot f) where
  __ := instCommRing _
  __ := instGroupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by
    rw [← map_natCast (of f)]; rw [← map_natCast (of f)]; rw [← map_div₀]; rw [← NNRat.cast_def]; rfl
  ratCast_def q := by
    rw [← map_natCast (of f)]; rw [← map_intCast (of f)]; rw [← map_div₀]; rw [← Rat.cast_def]; rfl
  nnqsmul_def q x :=
    AdjoinRoot.induction_on f (C := fun y => q • y = (of f) q * y) x fun p => by
      simp only [smul_mk, of, RingHom.comp_apply, ← (mk f).map_mul, Polynomial.nnqsmul_eq_C_mul]
  qsmul_def q x :=
    -- Porting note: I gave the explicit motive and changed `rw` to `simp`.
    AdjoinRoot.induction_on f (C := fun y => q • y = (of f) q * y) x fun p => by
      simp only [smul_mk, of, RingHom.comp_apply, ← (mk f).map_mul, Polynomial.qsmul_eq_C_mul]

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  given: (h : degree f != 0)
  statement: Function.Injective ((↑) : K -> AdjoinRoot f)
  proof: have := AdjoinRoot.nontrivial f h
  (of f).injective

中文:
定理 coe_injective
  条件: (h : degree f != 0)
  结论: 函数.单射 ((↑) : K -> AdjoinRoot f)
  证明: have := AdjoinRoot.nontrivial f h
  (of f).injective

Depends on / 依赖: AdjoinRoot, AdjoinRoot.nontrivial, injective, nontrivial
-/
theorem coe_injective (h : degree f != 0) : Function.Injective ((↑) : K -> AdjoinRoot f) :=
  have := AdjoinRoot.nontrivial f h
  (of f).injective

/--
theorem `coe_injective'` / 定理 `coe_injective'`

English:
theorem coe_injective'
  given: [Fact (Irreducible f)]
  statement: Function.Injective ((↑) : K -> AdjoinRoot f)
  proof: (of f).injective

中文:
定理 coe_injective'
  条件: [Fact (不可约 f)]
  结论: 函数.单射 ((↑) : K -> AdjoinRoot f)
  证明: (of f).injective

Depends on / 依赖: injective
-/
theorem coe_injective' [Fact (Irreducible f)] : Function.Injective ((↑) : K -> AdjoinRoot f) :=
  (of f).injective

variable (f)

/--
theorem `mul_div_root_cancel` / 定理 `mul_div_root_cancel`

English:
theorem mul_div_root_cancel
  given: [Fact (Irreducible f)]
  proof: (isRoot_root _).mul_div_eq

中文:
定理 mul_div_root_cancel
  条件: [Fact (不可约 f)]
  证明: (isRoot_root _).mul_div_eq

Depends on / 依赖: isRoot_root, mul_div_eq
-/
theorem mul_div_root_cancel [Fact (Irreducible f)] :
    (X - C (root f)) * ((f.map (of f)) / (X - C (root f))) = f.map (of f) :=
  (isRoot_root _).mul_div_eq

end Irreducible

section IsNoetherianRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: R] [IsNoetherianRing R] {f
  body: Ideal.Quotient.isNoetherianRing _

中文:
实例 [交换环
  签名: R] [是Noether环 R] {f
  定义体: Ideal.Quotient.isNoetherianRing _

Depends on / 依赖: Ideal.Quotient.isNoetherianRing, Quotient, isNoetherianRing
-/
instance [CommRing R] [IsNoetherianRing R] {f : R[X]} : IsNoetherianRing (AdjoinRoot f) :=
  Ideal.Quotient.isNoetherianRing _

end IsNoetherianRing

section PowerBasis

variable [CommRing R] {g : R[X]}

/--
theorem `isIntegral_root'` / 定理 `isIntegral_root'`

English:
theorem isIntegral_root'
  given: (hg : g.Monic)
  statement: IsIntegral R (root g)
  proof: ⟨g, hg, eval₂_root g⟩

中文:
定理 is整数egral_root'
  条件: (hg : g.Monic)
  结论: 是整 R (root g)
  证明: ⟨g, hg, eval₂_root g⟩
-/
theorem isIntegral_root' (hg : g.Monic) : IsIntegral R (root g) :=
  ⟨g, hg, eval₂_root g⟩

/--
Definition of `modByMonicHom` / `modByMonicHom` 的定义

English:
definition modByMonicHom
  signature: (hg : g.Monic)
  body: (Submodule.liftQ _ (Polynomial.modByMonicHom g)
        fun f (hf : f in (Ideal.span {g}).restrictScalars R) =>
        (mem_ker_modByMonic hg).mpr (Ideal.mem_span_singleton.mp hf)).comp <|
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {g} : Ideal R[X])).symm.toLinearMap

@[simp]

中文:
定义 modByMonicHom
  签名: (hg : g.Monic)
  定义体: (Submodule.liftQ _ (Polynomial.modByMonicHom g)
        fun f (hf : f in (Ideal.span {g}).restrictScalars R) =>
        (mem_ker_modByMonic hg).mpr (Ideal.mem_span_singleton.mp hf)).comp <|
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {g} : Ideal R[X])).symm.toLinearMap

@[simp]

Depends on / 依赖: Ideal.mem_span_singleton.mp, Ideal.span, Polynomial, Polynomial.modByMonicHom, Quotient, Submodule, Submodule.Quotient.restrictScalarsEquiv, Submodule.liftQ, mem_ker_modByMonic, mem_span_singleton, modByMonicHom, restrictScalars, restrictScalarsEquiv, symm.toLinearMap, toLinearMap
-/
def modByMonicHom (hg : g.Monic) : AdjoinRoot g ->ₗ[R] R[X] :=
  (Submodule.liftQ _ (Polynomial.modByMonicHom g)
        fun f (hf : f in (Ideal.span {g}).restrictScalars R) =>
        (mem_ker_modByMonic hg).mpr (Ideal.mem_span_singleton.mp hf)).comp <|
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {g} : Ideal R[X])).symm.toLinearMap

@[simp]
/--
theorem `modByMonicHom_mk` / 定理 `modByMonicHom_mk`

English:
theorem modByMonicHom_mk
  given: (hg : g.Monic) (f : R[X])
  statement: modByMonicHom hg (mk g f) = f %ₘ g
  proof: rfl

中文:
定理 modByMonicHom_mk
  条件: (hg : g.Monic) (f : R[X])
  结论: modByMonicHom hg (mk g f) = f %ₘ g
  证明: rfl
-/
theorem modByMonicHom_mk (hg : g.Monic) (f : R[X]) : modByMonicHom hg (mk g f) = f %ₘ g :=
  rfl

/--
theorem `mk_leftInverse` / 定理 `mk_leftInverse`

English:
theorem mk_leftInverse
  given: (hg : g.Monic)
  statement: Function.LeftInverse (mk g) (modByMonicHom hg)
  proof: by
  intro f
  induction f using AdjoinRoot.induction_on
  rw [modByMonicHom_mk hg]; rw [mk_eq_mk]; rw [modByMonic_eq_sub_mul_div]; rw [sub_sub_cancel_left]; rw [dvd_neg]
  apply dvd_mul_right

中文:
定理 mk_leftInverse
  条件: (hg : g.Monic)
  结论: 函数.左逆 (mk g) (modByMonicHom hg)
  证明: by
  intro f
  induction f using AdjoinRoot.induction_on
  rw [modByMonicHom_mk hg]; rw [mk_eq_mk]; rw [modByMonic_eq_sub_mul_div]; rw [sub_sub_cancel_left]; rw [dvd_neg]
  apply dvd_mul_right

Depends on / 依赖: AdjoinRoot, AdjoinRoot.induction_on, dvd_mul_right, dvd_neg, induction_on, mk_eq_mk, modByMonicHom_mk, modByMonic_eq_sub_mul_div, sub_sub_cancel_left
-/
theorem mk_leftInverse (hg : g.Monic) : Function.LeftInverse (mk g) (modByMonicHom hg) := by
  intro f
  induction f using AdjoinRoot.induction_on
  rw [modByMonicHom_mk hg]; rw [mk_eq_mk]; rw [modByMonic_eq_sub_mul_div]; rw [sub_sub_cancel_left]; rw [dvd_neg]
  apply dvd_mul_right

/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective (mk g)
  proof: Ideal.Quotient.mk_surjective

中文:
定理 mk_surjective
  结论: 函数.满射 (mk g)
  证明: Ideal.Quotient.mk_surjective

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, mk_surjective
-/
theorem mk_surjective : Function.Surjective (mk g) :=
  Ideal.Quotient.mk_surjective

/--
Definition of `powerBasisAux'` / `powerBasisAux'` 的定义

English:
definition powerBasisAux'
  signature: (hg : g.Monic)
  body: .ofEquivFun
    { toFun := fun f i => (modByMonicHom hg f).coeff i
invFun := fun c => mk g ∑ i : Fin g.natDegree, monomial i (c i)
      map_add' := fun f₁ f₂ =>
        funext fun i => by simp only [(modByMonicHom hg).map_add, coeff_add, Pi.add_apply]
      map_smul' := fun f₁ f₂ =>
        funext 

中文:
定义 powerBasisAux'
  签名: (hg : g.Monic)
  定义体: .ofEquivFun
    { toFun := fun f i => (modByMonicHom hg f).coeff i
invFun := fun c => mk g ∑ i : Fin g.natDegree, monomial i (c i)
      map_add' := fun f₁ f₂ =>
        funext fun i => by simp only [(modByMonicHom hg).map_add, coeff_add, Pi.add_apply]
      map_smul' := fun f₁ f₂ =>
        funext 

Depends on / 依赖: AdjoinRoot, AdjoinRoot.induction_on, Eq.symm, Pi.add_apply, Pi.smul_apply, RingHom, RingHom.id_apply, add_apply, coeff_add, coeff_smul, degree_, g.natDegree, id_apply, induction_on, invFun, left_inv, map_add, map_smul, mk_eq_mk, mk_eq_mk.mpr
-/
def powerBasisAux' (hg : g.Monic) : Basis (Fin g.natDegree) R (AdjoinRoot g) :=
  .ofEquivFun
    { toFun := fun f i => (modByMonicHom hg f).coeff i
invFun := fun c => mk g ∑ i : Fin g.natDegree, monomial i (c i)
      map_add' := fun f₁ f₂ =>
        funext fun i => by simp only [(modByMonicHom hg).map_add, coeff_add, Pi.add_apply]
      map_smul' := fun f₁ f₂ =>
        funext fun i => by
          simp only [(modByMonicHom hg).map_smul, coeff_smul, Pi.smul_apply, RingHom.id_apply]
left_inv f := AdjoinRoot.induction_on _ f fun f => Eq.symm mk_eq_mk.mpr by
        simp only [modByMonicHom_mk, sum_modByMonic_coeff hg degree_le_natDegree]
        rw [modByMonic_eq_sub_mul_div]; rw [sub_sub_cancel]
        exact dvd_mul_right _ _
      right_inv := fun x =>
        funext fun i => by
          nontriviality R
          simp only [modByMonicHom_mk]
          rw [(modByMonic_eq_self_iff hg).mpr]; rw [finsetSum_coeff]
          · simp_rw [coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
          · simp_rw [← C_mul_X_pow_eq_monomial]
            exact (degree_eq_natDegree <| hg.ne_zero).symm ▸ degree_sum_fin_lt _ }

-- This lemma could be autogenerated by `@[simps]` but unfortunately that would require
-- unfolding that causes a timeout.
-- This lemma should have the simp tag but this causes a lint issue.
/--
theorem `powerBasisAux'_repr_symm_apply` / 定理 `powerBasisAux'_repr_symm_apply`

English:
theorem powerBasisAux'_repr_symm_apply
  given: (hg : g.Monic) (c : Fin g.natDegree ->₀ R)
  proof: rfl

中文:
定理 powerBasisAux'_repr_symm_apply
  条件: (hg : g.Monic) (c : 有限集 g.natDegree ->₀ R)
  证明: rfl
-/
theorem powerBasisAux'_repr_symm_apply (hg : g.Monic) (c : Fin g.natDegree ->₀ R) :
    (powerBasisAux' hg).repr.symm c = mk g (∑ i : Fin _, monomial i (c i)) :=
  rfl

-- This lemma could be autogenerated by `@[simps]` but unfortunately that would require
-- unfolding that causes a timeout.
@[simp]
/--
theorem `powerBasisAux'_repr_apply_to_fun` / 定理 `powerBasisAux'_repr_apply_to_fun`

English:
theorem powerBasisAux'_repr_apply_to_fun
  given: (hg : g.Monic) (f : AdjoinRoot g) (i : Fin g.natDegree)
  proof: rfl

中文:
定理 powerBasisAux'_repr_apply_to_fun
  条件: (hg : g.Monic) (f : AdjoinRoot g) (i : 有限集 g.natDegree)
  证明: rfl
-/
theorem powerBasisAux'_repr_apply_to_fun (hg : g.Monic) (f : AdjoinRoot g) (i : Fin g.natDegree) :
    (powerBasisAux' hg).repr f i = (modByMonicHom hg f).coeff ↑i :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The power basis `1, root g, ..., root g ^ (d - 1)` for `AdjoinRoot g`,
where `g` is a monic polynomial of degree `d`. -/
@[simps]
/--
Definition of `powerBasis'` / `powerBasis'` 的定义

English:
definition powerBasis'
  signature: (hg : g.Monic)
  body: root g
  dim := g.natDegree
  basis := powerBasisAux' hg
  basis_eq_pow i := by
    simp only [powerBasisAux', Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, monomial_one_right_eq_X_pow, (mk g).map_pow, mk_X]
    · intro j _ hj
      rw [←

中文:
定义 powerBasis'
  签名: (hg : g.Monic)
  定义体: root g
  dim := g.natDegree
  basis := powerBasisAux' hg
  basis_eq_pow i := by
    simp only [powerBasisAux', Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, monomial_one_right_eq_X_pow, (mk g).map_pow, mk_X]
    · intro j _ hj
      rw [←
-/
def powerBasis' (hg : g.Monic) : PowerBasis R (AdjoinRoot g) where
  gen := root g
  dim := g.natDegree
  basis := powerBasisAux' hg
  basis_eq_pow i := by
    simp only [powerBasisAux', Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, monomial_one_right_eq_X_pow, (mk g).map_pow, mk_X]
    · intro j _ hj
      rw [← monomial_zero_right _]; rw [Pi.single_eq_of_ne hj]
    -- Fix `DecidableEq` mismatch
    · intros
      have := Finset.mem_univ i
      contradiction

/--
lemma `_root_.Polynomial.Monic.free_adjoinRoot` / 引理 `_root_.Polynomial.Monic.free_adjoinRoot`

English:
lemma _root_.Polynomial.Monic.free_adjoinRoot
  given: (hg : g.Monic)
  statement: Module.Free R (AdjoinRoot g)
  proof: .of_basis (powerBasis' hg).basis

中文:
引理 _root_.多项式.Monic.free_adjoinRoot
  条件: (hg : g.Monic)
  结论: 模.自由 R (AdjoinRoot g)
  证明: .of_basis (powerBasis' hg).basis

Depends on / 依赖: of_basis, powerBasis
-/
lemma _root_.Polynomial.Monic.free_adjoinRoot (hg : g.Monic) : Module.Free R (AdjoinRoot g) :=
  .of_basis (powerBasis' hg).basis

/--
lemma `_root_.Polynomial.Monic.finite_adjoinRoot` / 引理 `_root_.Polynomial.Monic.finite_adjoinRoot`

English:
lemma _root_.Polynomial.Monic.finite_adjoinRoot
  given: (hg : g.Monic)
  statement: Module.Finite R (AdjoinRoot g)
  proof: .of_basis (powerBasis' hg).basis

中文:
引理 _root_.多项式.Monic.finite_adjoinRoot
  条件: (hg : g.Monic)
  结论: 模.有限 R (AdjoinRoot g)
  证明: .of_basis (powerBasis' hg).basis

Depends on / 依赖: of_basis, powerBasis
-/
lemma _root_.Polynomial.Monic.finite_adjoinRoot (hg : g.Monic) : Module.Finite R (AdjoinRoot g) :=
  .of_basis (powerBasis' hg).basis

/--
lemma `_root_.Polynomial.Monic.free_quotient` / 引理 `_root_.Polynomial.Monic.free_quotient`

English:
lemma _root_.Polynomial.Monic.free_quotient
  given: (hg : g.Monic)
  proof: hg.free_adjoinRoot

中文:
引理 _root_.多项式.Monic.free_quotient
  条件: (hg : g.Monic)
  证明: hg.free_adjoinRoot

Depends on / 依赖: free_adjoinRoot, hg.free_adjoinRoot
-/
lemma _root_.Polynomial.Monic.free_quotient (hg : g.Monic) :
    Module.Free R (R[X] ⧸ Ideal.span {g}) :=
  hg.free_adjoinRoot

/--
lemma `_root_.Polynomial.Monic.finite_quotient` / 引理 `_root_.Polynomial.Monic.finite_quotient`

English:
lemma _root_.Polynomial.Monic.finite_quotient
  given: (hg : g.Monic)
  proof: hg.finite_adjoinRoot

中文:
引理 _root_.多项式.Monic.finite_quotient
  条件: (hg : g.Monic)
  证明: hg.finite_adjoinRoot

Depends on / 依赖: finite_adjoinRoot, hg.finite_adjoinRoot
-/
lemma _root_.Polynomial.Monic.finite_quotient (hg : g.Monic) :
    Module.Finite R (R[X] ⧸ Ideal.span {g}) :=
  hg.finite_adjoinRoot

variable [Field K] {f : K[X]}

/--
theorem `isIntegral_root` / 定理 `isIntegral_root`

English:
theorem isIntegral_root
  given: (hf : f != 0)
  statement: IsIntegral K (root f)
  proof: (isAlgebraic_root hf).isIntegral

中文:
定理 is整数egral_root
  条件: (hf : f != 0)
  结论: 是整 K (root f)
  证明: (isAlgebraic_root hf).isIntegral

Depends on / 依赖: isAlgebraic_root, isIntegral
-/
theorem isIntegral_root (hf : f != 0) : IsIntegral K (root f) :=
  (isAlgebraic_root hf).isIntegral

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `minpoly_root` / 定理 `minpoly_root`

English:
theorem minpoly_root
  given: (hf : f != 0)
  statement: minpoly K (root f) = f * C f.leadingCoeff⁻¹
  proof: by
  have f'_monic : Monic _ := monic_mul_leadingCoeff_inv hf
  refine (minpoly.unique K _ f'_monic ?_ ?_).symm
  · rw [map_mul, aeval_eq, mk_self, zero_mul]
  intro q q_monic q_aeval
  have commutes : (lift (algebraMap K (AdjoinRoot f)) (root f) q_aeval).comp (mk q) = mk f := by
    ext
    · simp 

中文:
定理 minpoly_root
  条件: (hf : f != 0)
  结论: minpoly K (root f) = f * C f.leadingCoeff⁻¹
  证明: by
  have f'_monic : Monic _ := monic_mul_leadingCoeff_inv hf
  refine (minpoly.unique K _ f'_monic ?_ ?_).symm
  · rw [map_mul, aeval_eq, mk_self, zero_mul]
  intro q q_monic q_aeval
  have commutes : (lift (algebraMap K (AdjoinRoot f)) (root f) q_aeval).comp (mk q) = mk f := by
    ext
    · simp 

Depends on / 依赖: AdjoinRoot, Nat.cast_le, RingHom, RingHom.comp_apply, _monic, _monic.ne_zero, aeval_eq, algebraMap, cast_le, commutes, comp_apply, degree_eq_natDegree, lift_of, lift_root, map_mul, minpoly, minpoly.unique, mk_C, mk_X, mk_self
-/
theorem minpoly_root (hf : f != 0) : minpoly K (root f) = f * C f.leadingCoeff⁻¹ := by
  have f'_monic : Monic _ := monic_mul_leadingCoeff_inv hf
  refine (minpoly.unique K _ f'_monic ?_ ?_).symm
  · rw [map_mul, aeval_eq, mk_self, zero_mul]
  intro q q_monic q_aeval
  have commutes : (lift (algebraMap K (AdjoinRoot f)) (root f) q_aeval).comp (mk q) = mk f := by
    ext
    · simp only [RingHom.comp_apply, mk_C, lift_of]
      rfl
    · simp only [RingHom.comp_apply, mk_X, lift_root]
  rw [degree_eq_natDegree f'_monic.ne_zero]; rw [degree_eq_natDegree q_monic.ne_zero]; rw [Nat.cast_le]; rw [natDegree_mul hf]; rw [natDegree_C]; rw [add_zero]
  · apply natDegree_le_of_dvd
    · have : mk f q = 0 := by rw [← commutes, RingHom.comp_apply, mk_self, map_zero]
      exact mk_eq_zero.1 this
    · exact q_monic.ne_zero
  · rwa [Ne, C_eq_zero, inv_eq_zero, leadingCoeff_eq_zero]

/--
Definition of `powerBasisAux` / `powerBasisAux` 的定义

English:
definition powerBasisAux
  signature: (hf : f != 0)
  body: by
  let f' := f * C f.leadingCoeff⁻¹
  have deg_f' : f'.natDegree = f.natDegree := by
    rw [natDegree_mul hf]; rw [natDegree_C]; rw [add_zero]
    · rwa [Ne, C_eq_zero, inv_eq_zero, leadingCoeff_eq_zero]
  have minpoly_eq : minpoly K (root f) = f' := minpoly_root hf
  apply Basis.mk (v := fun i :

中文:
定义 powerBasisAux
  签名: (hf : f != 0)
  定义体: by
  let f' := f * C f.leadingCoeff⁻¹
  have deg_f' : f'.natDegree = f.natDegree := by
    rw [natDegree_mul hf]; rw [natDegree_C]; rw [add_zero]
    · rwa [Ne, C_eq_zero, inv_eq_zero, leadingCoeff_eq_zero]
  have minpoly_eq : minpoly K (root f) = f' := minpoly_root hf
  apply Basis.mk (v := fun i :

Depends on / 依赖: Basis.mk, C_eq_zero, add_zero, deg_f, f.leadingCoeff, f.natDegree, i.val, inv_eq_zero, isIntegral_root, leadingCoeff, leadingCoeff_eq_zero, linearIndependent_pow, mem_span_pow, minpoly, minpoly_eq, minpoly_root, natDegree, natDegree_C, natDegree_mul
-/
def powerBasisAux (hf : f != 0) : Basis (Fin f.natDegree) K (AdjoinRoot f) := by
  let f' := f * C f.leadingCoeff⁻¹
  have deg_f' : f'.natDegree = f.natDegree := by
    rw [natDegree_mul hf]; rw [natDegree_C]; rw [add_zero]
    · rwa [Ne, C_eq_zero, inv_eq_zero, leadingCoeff_eq_zero]
  have minpoly_eq : minpoly K (root f) = f' := minpoly_root hf
  apply Basis.mk (v := fun i : Fin f.natDegree => root f ^ i.val)
  · rw [← deg_f', ← minpoly_eq]
    exact linearIndependent_pow (root f)
  · rintro y -
    rw [← deg_f']; rw [← minpoly_eq]
    apply (isIntegral_root hf).mem_span_pow
    obtain ⟨g⟩ := y
    use g
    rw [aeval_eq]
    rfl

/-- The power basis `1, root f, ..., root f ^ (d - 1)` for `AdjoinRoot f`,
where `f` is an irreducible polynomial over a field of degree `d`. -/
@[simps!]
/--
Definition of `powerBasis` / `powerBasis` 的定义

English:
definition powerBasis
  signature: (hf : f != 0)
  body: root f
  dim := f.natDegree
  basis := powerBasisAux hf
  basis_eq_pow := by simp [powerBasisAux]

中文:
定义 powerBasis
  签名: (hf : f != 0)
  定义体: root f
  dim := f.natDegree
  basis := powerBasisAux hf
  basis_eq_pow := by simp [powerBasisAux]
-/
def powerBasis (hf : f != 0) : PowerBasis K (AdjoinRoot f) where
  gen := root f
  dim := f.natDegree
  basis := powerBasisAux hf
  basis_eq_pow := by simp [powerBasisAux]

/--
theorem `minpoly_powerBasis_gen` / 定理 `minpoly_powerBasis_gen`

English:
theorem minpoly_powerBasis_gen
  given: (hf : f != 0)
  proof: by
  rw [powerBasis_gen]; rw [minpoly_root hf]

中文:
定理 minpoly_powerBasis_gen
  条件: (hf : f != 0)
  证明: by
  rw [powerBasis_gen]; rw [minpoly_root hf]

Depends on / 依赖: minpoly_root, powerBasis_gen
-/
theorem minpoly_powerBasis_gen (hf : f != 0) :
    minpoly K (powerBasis hf).gen = f * C f.leadingCoeff⁻¹ := by
  rw [powerBasis_gen]; rw [minpoly_root hf]

/--
theorem `minpoly_powerBasis_gen_of_monic` / 定理 `minpoly_powerBasis_gen_of_monic`

English:
theorem minpoly_powerBasis_gen_of_monic
  given: (hf : f.Monic) (hf' : f != 0 := hf.ne_zero)
  proof: by
  rw [minpoly_powerBasis_gen hf']; rw [hf.leadingCoeff]; rw [inv_one]; rw [C.map_one]; rw [mul_one]

中文:
定理 minpoly_powerBasis_gen_of_monic
  条件: (hf : f.Monic) (hf' : f != 0 := hf.ne_zero)
  证明: by
  rw [minpoly_powerBasis_gen hf']; rw [hf.leadingCoeff]; rw [inv_one]; rw [C.map_one]; rw [mul_one]

Depends on / 依赖: hf.ne_zero, ne_zero
-/
theorem minpoly_powerBasis_gen_of_monic (hf : f.Monic) (hf' : f != 0 := hf.ne_zero) :
    minpoly K (powerBasis hf').gen = f := by
  rw [minpoly_powerBasis_gen hf']; rw [hf.leadingCoeff]; rw [inv_one]; rw [C.map_one]; rw [mul_one]

/--
theorem `_root_.finrank_quotient_span_eq_natDegree` / 定理 `_root_.finrank_quotient_span_eq_natDegree`

English:
theorem _root_.finrank_quotient_span_eq_natDegree
  given: {f : K[X]}
  proof: by
  by_cases hf : f = 0
  · rw [hf, natDegree_zero,
      ((Submodule.quotEquivOfEqBot _ (by simp)).restrictScalars K).finrank_eq]
    exact finrank_of_not_finite Polynomial.not_finite
  rw [PowerBasis.finrank]
  exact AdjoinRoot.powerBasis_dim hf

中文:
定理 _root_.finrank_quotient_span_eq_natDegree
  条件: {f : K[X]}
  证明: by
  by_cases hf : f = 0
  · rw [hf, natDegree_zero,
      ((Submodule.quotEquivOfEqBot _ (by simp)).restrictScalars K).finrank_eq]
    exact finrank_of_not_finite Polynomial.not_finite
  rw [PowerBasis.finrank]
  exact AdjoinRoot.powerBasis_dim hf

Depends on / 依赖: AdjoinRoot, AdjoinRoot.powerBasis_dim, Polynomial, Polynomial.not_finite, PowerBasis, PowerBasis.finrank, Submodule, Submodule.quotEquivOfEqBot, finrank, finrank_eq, finrank_of_not_finite, natDegree_zero, not_finite, powerBasis_dim, quotEquivOfEqBot, restrictScalars
-/
theorem _root_.finrank_quotient_span_eq_natDegree {f : K[X]} :
    Module.finrank K (K[X] ⧸ Ideal.span {f}) = f.natDegree := by
  by_cases hf : f = 0
  · rw [hf, natDegree_zero,
      ((Submodule.quotEquivOfEqBot _ (by simp)).restrictScalars K).finrank_eq]
    exact finrank_of_not_finite Polynomial.not_finite
  rw [PowerBasis.finrank]
  exact AdjoinRoot.powerBasis_dim hf

end PowerBasis

section Equiv

section minpoly

variable [CommRing R] [CommRing S] [Algebra R S] (x : S) (R)

open Algebra Polynomial

/--
Definition of `Minpoly.toAdjoin` / `Minpoly.toAdjoin` 的定义

English:
definition Minpoly.toAdjoin
  signature: : AdjoinRoot (minpoly R x) ->ₐ[R] adjoin R ({x} : Set S)
  body: liftAlgHom _ (Algebra.ofId R <| adjoin R {x}) ⟨x, self_mem_adjoin_singleton R x⟩
    (by change aeval _ _ = _; simp [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe])

中文:
定义 Minpoly.toAdjoin
  签名: : AdjoinRoot (minpoly R x) ->ₐ[R] adjoin R ({x} : 集合 S)
  定义体: liftAlgHom _ (Algebra.ofId R <| adjoin R {x}) ⟨x, self_mem_adjoin_singleton R x⟩
    (by change aeval _ _ = _; simp [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe])

Depends on / 依赖: Algebra, Algebra.ofId, Subalgebra, Subalgebra.coe_eq_zero, adjoin, aeval_subalgebra_coe, coe_eq_zero, liftAlgHom, self_mem_adjoin_singleton
-/
def Minpoly.toAdjoin : AdjoinRoot (minpoly R x) ->ₐ[R] adjoin R ({x} : Set S) :=
  liftAlgHom _ (Algebra.ofId R <| adjoin R {x}) ⟨x, self_mem_adjoin_singleton R x⟩
    (by change aeval _ _ = _; simp [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe])

variable {R x}

@[simp]
/--
theorem `Minpoly.coe_toAdjoin` / 定理 `Minpoly.coe_toAdjoin`

English:
theorem Minpoly.coe_toAdjoin
  proof: rfl

中文:
定理 Minpoly.coe_toAdjoin
  证明: rfl
-/
theorem Minpoly.coe_toAdjoin :
    ⇑(Minpoly.toAdjoin R x) = liftAlgHom (minpoly R x) (Algebra.ofId R <| adjoin R {x})
      ⟨x, self_mem_adjoin_singleton R x⟩
      (by change aeval _ _ = _; simp [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe]) := rfl

/--
theorem `Minpoly.coe_toAdjoin_mk_X` / 定理 `Minpoly.coe_toAdjoin_mk_X`

English:
theorem Minpoly.coe_toAdjoin_mk_X
  statement: Minpoly.toAdjoin R x (mk (minpoly R x) X) = x
  proof: by simp

中文:
定理 Minpoly.coe_toAdjoin_mk_X
  结论: Minpoly.toAdjoin R x (mk (minpoly R x) X) = x
  证明: by simp
-/
theorem Minpoly.coe_toAdjoin_mk_X : Minpoly.toAdjoin R x (mk (minpoly R x) X) = x := by simp

variable (R x)

/--
theorem `Minpoly.toAdjoin.surjective` / 定理 `Minpoly.toAdjoin.surjective`

English:
theorem Minpoly.toAdjoin.surjective
  statement: Function.Surjective (Minpoly.toAdjoin R x)
  proof: by
  rw [← AlgHom.range_eq_top]; rw [_root_.eq_top_iff]; rw [← adjoin_adjoin_coe_preimage]
  exact adjoin_le fun ⟨y₁, y₂⟩ h => ⟨mk (minpoly R x) X, by simpa using h.symm⟩

中文:
定理 Minpoly.toAdjoin.surjective
  结论: 函数.满射 (Minpoly.toAdjoin R x)
  证明: by
  rw [← AlgHom.range_eq_top]; rw [_root_.eq_top_iff]; rw [← adjoin_adjoin_coe_preimage]
  exact adjoin_le fun ⟨y₁, y₂⟩ h => ⟨mk (minpoly R x) X, by simpa using h.symm⟩

Depends on / 依赖: AlgHom, AlgHom.range_eq_top, _root_, _root_.eq_top_iff, adjoin_adjoin_coe_preimage, adjoin_le, eq_top_iff, h.symm, minpoly, range_eq_top
-/
theorem Minpoly.toAdjoin.surjective : Function.Surjective (Minpoly.toAdjoin R x) := by
  rw [← AlgHom.range_eq_top]; rw [_root_.eq_top_iff]; rw [← adjoin_adjoin_coe_preimage]
  exact adjoin_le fun ⟨y₁, y₂⟩ h => ⟨mk (minpoly R x) X, by simpa using h.symm⟩

end minpoly

section Equiv'

variable [CommRing R] [CommRing S] [Algebra R S]
variable (g : R[X]) (pb : PowerBasis R S)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `S` is an extension of `R` with power basis `pb` and `g` is a monic polynomial over `R`
such that `pb.gen` has a minimal polynomial `g`, then `S` is isomorphic to `AdjoinRoot g`.

Compare `PowerBasis.equivOfRoot`, which would require
`h₂ : aeval pb.gen (minpoly R (root g)) = 0`; that minimal polynomial is not
guaranteed to be identical to `g`. -/
@[simps -fullyApplied]
/--
Definition of `equiv'` / `equiv'` 的定义

English:
definition equiv'
  signature: (h₁ : aeval (root g) (minpoly R pb.gen) = 0) (h₂ : aeval pb.gen g = 0)
  body: AdjoinRoot.liftAlgHom g _ pb.gen h₂
  toFun := AdjoinRoot.liftAlgHom g _ pb.gen h₂
  invFun := pb.lift (root g) h₁
  left_inv x := AdjoinRoot.induction_on _ x fun x => by
    change pb.lift _ _ (aeval _ _) = _; rw [pb.lift_aeval, aeval_eq]
  right_inv x := by
    nontriviality S
    obtain ⟨f, _hf, 

中文:
定义 equiv'
  签名: (h₁ : aeval (root g) (minpoly R pb.gen) = 0) (h₂ : aeval pb.gen g = 0)
  定义体: AdjoinRoot.liftAlgHom g _ pb.gen h₂
  toFun := AdjoinRoot.liftAlgHom g _ pb.gen h₂
  invFun := pb.lift (root g) h₁
  left_inv x := AdjoinRoot.induction_on _ x fun x => by
    change pb.lift _ _ (aeval _ _) = _; rw [pb.lift_aeval, aeval_eq]
  right_inv x := by
    nontriviality S
    obtain ⟨f, _hf, 

Depends on / 依赖: AdjoinRoot, AdjoinRoot.liftAlgHom, liftAlgHom, pb.gen
-/
def equiv' (h₁ : aeval (root g) (minpoly R pb.gen) = 0) (h₂ : aeval pb.gen g = 0) :
    AdjoinRoot g ≃ₐ[R] S where
  __ := AdjoinRoot.liftAlgHom g _ pb.gen h₂
  toFun := AdjoinRoot.liftAlgHom g _ pb.gen h₂
  invFun := pb.lift (root g) h₁
  left_inv x := AdjoinRoot.induction_on _ x fun x => by
    change pb.lift _ _ (aeval _ _) = _; rw [pb.lift_aeval, aeval_eq]
  right_inv x := by
    nontriviality S
    obtain ⟨f, _hf, rfl⟩ := pb.exists_eq_aeval x
    rw [pb.lift_aeval]; rw [aeval_eq]; rw [liftAlgHom_mk]; rw [Polynomial.aeval_def]; rw [Algebra.toRingHom_ofId]

-- This lemma should have the simp tag but this causes a lint issue.
set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `equiv'_toAlgHom` / 定理 `equiv'_toAlgHom`

English:
theorem equiv'_toAlgHom
  given: (h₁ : aeval (root g) (minpoly R pb.gen) = 0) (h₂ : aeval pb.gen g = 0)
  proof: rfl

中文:
定理 equiv'_toAlgHom
  条件: (h₁ : aeval (root g) (minpoly R pb.gen) = 0) (h₂ : aeval pb.gen g = 0)
  证明: rfl
-/
theorem equiv'_toAlgHom (h₁ : aeval (root g) (minpoly R pb.gen) = 0) (h₂ : aeval pb.gen g = 0) :
    (equiv' g pb h₁ h₂).toAlgHom = AdjoinRoot.liftAlgHom g _ pb.gen h₂ :=
  rfl

-- This lemma should have the simp tag but this causes a lint issue.
set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `equiv'_symm_toAlgHom` / 定理 `equiv'_symm_toAlgHom`

English:
theorem equiv'_symm_toAlgHom
  statement: (h₁ : aeval (root g) (minpoly R pb.gen) = 0)
  proof: rfl

中文:
定理 equiv'_symm_toAlgHom
  结论: (h₁ : aeval (root g) (minpoly R pb.gen) = 0)
  证明: rfl
-/
theorem equiv'_symm_toAlgHom (h₁ : aeval (root g) (minpoly R pb.gen) = 0)
    (h₂ : aeval pb.gen g = 0) : (equiv' g pb h₁ h₂).symm.toAlgHom = pb.lift (root g) h₁ :=
  rfl

end Equiv'

section Field

variable (L F : Type*) [Field F] [CommRing L] [IsDomain L] [Algebra F L]

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (f : F[X]) (hf : f != 0)
  body: (powerBasis hf).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [powerBasis_gen]; rw [minpoly_root hf]; rw [aroots_mul]; rw [aroots_C]; rw [add_zero]; rw [Equiv.refl_apply]
      exact (monic_mul_leadingCoeff_inv hf).ne_zero)

中文:
定义 equiv
  签名: (f : F[X]) (hf : f != 0)
  定义体: (powerBasis hf).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [powerBasis_gen]; rw [minpoly_root hf]; rw [aroots_mul]; rw [aroots_C]; rw [add_zero]; rw [Equiv.refl_apply]
      exact (monic_mul_leadingCoeff_inv hf).ne_zero)

Depends on / 依赖: Equiv.refl, Equiv.refl_apply, add_zero, aroots_C, aroots_mul, liftEquiv, minpoly_root, monic_mul_leadingCoeff_inv, ne_zero, powerBasis, powerBasis_gen, refl_apply, subtypeEquiv
-/
def equiv (f : F[X]) (hf : f != 0) :
    (AdjoinRoot f ->ₐ[F] L) ≃ { x // x in f.aroots L } :=
  (powerBasis hf).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [powerBasis_gen]; rw [minpoly_root hf]; rw [aroots_mul]; rw [aroots_C]; rw [add_zero]; rw [Equiv.refl_apply]
      exact (monic_mul_leadingCoeff_inv hf).ne_zero)

end Field

end Equiv

-- TODO: consider splitting the file here. In the current mathlib3, the only result
-- that depends any of these lemmas was
-- `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` in `NumberTheory.KummerDedekind`
-- that uses
-- `PowerBasis.quotientEquivQuotientMinpolyMap == PowerBasis.quotientEquivQuotientMinpolyMap`
section

open Ideal DoubleQuot Polynomial

variable [CommRing R] (I : Ideal R) (f : R[X])

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `quotMapOfEquivQuotMapCMapMk` / `quotMapOfEquivQuotMapCMapMk` 的定义

English:
definition quotMapOfEquivQuotMapCMapMk
  signature: :
  body: Ideal.quotEquivOfEq (by rw [of, AdjoinRoot.mk, Ideal.map_map])

中文:
定义 quotMapOfEquivQuotMapCMapMk
  签名: :
  定义体: Ideal.quotEquivOfEq (by rw [of, AdjoinRoot.mk, Ideal.map_map])

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk, Ideal.map_map, Ideal.quotEquivOfEq, map_map, quotEquivOfEq
-/
def quotMapOfEquivQuotMapCMapMk :
    AdjoinRoot f ⧸ I.map (of f) ≃+*
      AdjoinRoot f ⧸ (I.map (C : R ->+* R[X])).map (AdjoinRoot.mk f) :=
  Ideal.quotEquivOfEq (by rw [of, AdjoinRoot.mk, Ideal.map_map])

set_option backward.isDefEq.respectTransparency.types false in
@[deprecated (since := "2026-03-02")]
alias quotMapOfEquivQuotMapCMapSpanMk := quotMapOfEquivQuotMapCMapMk

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `quotMapOfEquivQuotMapCMapMk_mk` / 定理 `quotMapOfEquivQuotMapCMapMk_mk`

English:
theorem quotMapOfEquivQuotMapCMapMk_mk
  given: (x : AdjoinRoot f)
  proof: rfl

@[deprecated (since := "2026-03-02")]
alias quotMapOfEquivQuotMapCMapSpanMk_mk := quotMapOfEquivQuotMapCMapMk_mk

中文:
定理 quotMapOfEquivQuotMapCMapMk_mk
  条件: (x : AdjoinRoot f)
  证明: rfl

@[deprecated (since := "2026-03-02")]
alias quotMapOfEquivQuotMapCMapSpanMk_mk := quotMapOfEquivQuotMapCMapMk_mk
-/
theorem quotMapOfEquivQuotMapCMapMk_mk (x : AdjoinRoot f) :
    quotMapOfEquivQuotMapCMapMk I f (Ideal.Quotient.mk (I.map (of f)) x) =
      Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk (span {f})) (I.map (C : R ->+* R[X]))) x := rfl

@[deprecated (since := "2026-03-02")]
alias quotMapOfEquivQuotMapCMapSpanMk_mk := quotMapOfEquivQuotMapCMapMk_mk

--this lemma should have the simp tag but this causes a lint issue
set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `quotMapOfEquivQuotMapCMapMk_symm_mk` / 定理 `quotMapOfEquivQuotMapCMapMk_symm_mk`

English:
theorem quotMapOfEquivQuotMapCMapMk_symm_mk
  given: (x : AdjoinRoot f)
  proof: by
  rw [quotMapOfEquivQuotMapCMapMk]; rw [Ideal.quotEquivOfEq_symm]
  exact Ideal.quotEquivOfEq_mk _ _

@[deprecated (since := "2026-03-02")]
alias quotMapOfEquivQuotMapCMapSpanMk_symm_mk := quotMapOfEquivQuotMapCMapMk_symm_mk

中文:
定理 quotMapOfEquivQuotMapCMapMk_symm_mk
  条件: (x : AdjoinRoot f)
  证明: by
  rw [quotMapOfEquivQuotMapCMapMk]; rw [Ideal.quotEquivOfEq_symm]
  exact Ideal.quotEquivOfEq_mk _ _

@[deprecated (since := "2026-03-02")]
alias quotMapOfEquivQuotMapCMapSpanMk_symm_mk := quotMapOfEquivQuotMapCMapMk_symm_mk

Depends on / 依赖: Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_symm, quotEquivOfEq_mk, quotEquivOfEq_symm, quotMapOfEquivQuotMapCMapMk
-/
theorem quotMapOfEquivQuotMapCMapMk_symm_mk (x : AdjoinRoot f) :
    (quotMapOfEquivQuotMapCMapMk I f).symm
        (Ideal.Quotient.mk ((I.map (C : R ->+* R[X])).map (Ideal.Quotient.mk (span {f}))) x) =
      Ideal.Quotient.mk (I.map (of f)) x := by
  rw [quotMapOfEquivQuotMapCMapMk]; rw [Ideal.quotEquivOfEq_symm]
  exact Ideal.quotEquivOfEq_mk _ _

@[deprecated (since := "2026-03-02")]
alias quotMapOfEquivQuotMapCMapSpanMk_symm_mk := quotMapOfEquivQuotMapCMapMk_symm_mk

/--
Definition of `quotMapCMapSpanMkEquivQuotMapCQuotMapMk` / `quotMapCMapSpanMkEquivQuotMapCQuotMapMk` 的定义

English:
definition quotMapCMapSpanMkEquivQuotMapCQuotMapMk
  signature: :
  body: quotQuotEquivComm (Ideal.span ({f} : Set R[X])) (I.map (C : R ->+* R[X]))

@[deprecated (since := "2026-03-02")]
alias quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk := quotMapCMapSpanMkEquivQuotMapCQuotMapMk

中文:
定义 quotMapCMapSpanMkEquivQuotMapCQuotMapMk
  签名: :
  定义体: quotQuotEquivComm (Ideal.span ({f} : Set R[X])) (I.map (C : R ->+* R[X]))

@[deprecated (since := "2026-03-02")]
alias quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk := quotMapCMapSpanMkEquivQuotMapCQuotMapMk

Depends on / 依赖: I.map, Ideal.span, quotQuotEquivComm
-/
def quotMapCMapSpanMkEquivQuotMapCQuotMapMk :
    AdjoinRoot f ⧸ (I.map (C : R ->+* R[X])).map (AdjoinRoot.mk f) ≃+*
      (R[X] ⧸ I.map (C : R ->+* R[X])) ⧸
        (span ({f} : Set R[X])).map (Ideal.Quotient.mk (I.map (C : R ->+* R[X]))) :=
  quotQuotEquivComm (Ideal.span ({f} : Set R[X])) (I.map (C : R ->+* R[X]))

@[deprecated (since := "2026-03-02")]
alias quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk := quotMapCMapSpanMkEquivQuotMapCQuotMapMk

-- This lemma should have the simp tag but this causes a lint issue.
/--
theorem `quotMapCMapSpanMkEquivQuotMapCQuotMapMk_mk` / 定理 `quotMapCMapSpanMkEquivQuotMapCQuotMapMk_mk`

English:
theorem quotMapCMapSpanMkEquivQuotMapCQuotMapMk_mk
  given: (p : R[X])
  proof: rfl

@[deprecated (since := "2026-03-02")]
alias quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk_mk := quotMapCMapSpanMkEquivQuotMapCQuotMapMk_mk

@[simp]

中文:
定理 quotMapCMapSpanMkEquivQuotMapCQuotMapMk_mk
  条件: (p : R[X])
  证明: rfl

@[deprecated (since := "2026-03-02")]
alias quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk_mk := quotMapCMapSpanMkEquivQuotMapCQuotMapMk_mk

@[simp]
-/
theorem quotMapCMapSpanMkEquivQuotMapCQuotMapMk_mk (p : R[X]) :
    quotMapCMapSpanMkEquivQuotMapCQuotMapMk I f (Ideal.Quotient.mk _ (mk f p)) =
      quotQuotMk (I.map C) (span {f}) p :=
  rfl

@[deprecated (since := "2026-03-02")]
alias quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk_mk := quotMapCMapSpanMkEquivQuotMapCQuotMapMk_mk

@[simp]
/--
theorem `quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk` / 定理 `quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk`

English:
theorem quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk
  given: (p : R[X])
  proof: rfl

@[deprecated (since := "2026-03-02")]
alias quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk_symm_quotQuotMk :=
  quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk

中文:
定理 quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk
  条件: (p : R[X])
  证明: rfl

@[deprecated (since := "2026-03-02")]
alias quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk_symm_quotQuotMk :=
  quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk
-/
theorem quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk (p : R[X]) :
    (quotMapCMapSpanMkEquivQuotMapCQuotMapMk I f).symm (quotQuotMk (I.map C) (span {f}) p) =
      Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk (span {f})) (I.map (C : R ->+* R[X])))
        (mk f p) :=
  rfl

@[deprecated (since := "2026-03-02")]
alias quotMapCMapSpanMkEquivQuotMapCQuotMapSpanMk_symm_quotQuotMk :=
  quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk

/--
Definition of `Polynomial.quotQuotEquivComm` / `Polynomial.quotQuotEquivComm` 的定义

English:
definition Polynomial.quotQuotEquivComm
  signature: :
  body: quotientEquiv (span ({f.map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))))
    (span {Ideal.Quotient.mk (I.map Polynomial.C) f}) (polynomialQuotientEquivQuotientPolynomial I)
    (by
      rw [map_span]; rw [Set.image_singleton]; rw [RingEquiv.coe_toRingHom]; rw [polynomialQuotientEquivQuotient

中文:
定义 多项式.quotQuotEquivComm
  签名: :
  定义体: quotientEquiv (span ({f.map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))))
    (span {Ideal.Quotient.mk (I.map Polynomial.C) f}) (polynomialQuotientEquivQuotientPolynomial I)
    (by
      rw [map_span]; rw [Set.image_singleton]; rw [RingEquiv.coe_toRingHom]; rw [polynomialQuotientEquivQuotient

Depends on / 依赖: I.map, Ideal.Quotient.mk, Polynomial, Polynomial.C, Quotient, RingEquiv, RingEquiv.coe_toRingHom, Set.image_singleton, coe_toRingHom, f.map, image_singleton, map_span, polynomialQuotientEquivQuotientPolynomial, polynomialQuotientEquivQuotientPolynomial_map_mk, quotientEquiv
-/
def Polynomial.quotQuotEquivComm :
    (R ⧸ I)[X] ⧸ span ({f.map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))) ≃+*
      (R[X] ⧸ (I.map C)) ⧸ span ({(Ideal.Quotient.mk (I.map C)) f} : Set (R[X] ⧸ (I.map C))) :=
  quotientEquiv (span ({f.map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))))
    (span {Ideal.Quotient.mk (I.map Polynomial.C) f}) (polynomialQuotientEquivQuotientPolynomial I)
    (by
      rw [map_span]; rw [Set.image_singleton]; rw [RingEquiv.coe_toRingHom]; rw [polynomialQuotientEquivQuotientPolynomial_map_mk I f])

@[simp]
/--
theorem `Polynomial.quotQuotEquivComm_mk` / 定理 `Polynomial.quotQuotEquivComm_mk`

English:
theorem Polynomial.quotQuotEquivComm_mk
  given: (p : R[X])
  proof: by
  simp only [Polynomial.quotQuotEquivComm, quotientEquiv_mk,
    polynomialQuotientEquivQuotientPolynomial_map_mk]

@[simp]

中文:
定理 多项式.quotQuotEquivComm_mk
  条件: (p : R[X])
  证明: by
  simp only [Polynomial.quotQuotEquivComm, quotientEquiv_mk,
    polynomialQuotientEquivQuotientPolynomial_map_mk]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.quotQuotEquivComm, polynomialQuotientEquivQuotientPolynomial_map_mk, quotQuotEquivComm, quotientEquiv_mk
-/
theorem Polynomial.quotQuotEquivComm_mk (p : R[X]) :
    (Polynomial.quotQuotEquivComm I f) (Ideal.Quotient.mk _ (p.map (Ideal.Quotient.mk I))) =
      Ideal.Quotient.mk (span ({(Ideal.Quotient.mk (I.map C)) f} : Set (R[X] ⧸ (I.map C))))
      (Ideal.Quotient.mk (I.map C) p) := by
  simp only [Polynomial.quotQuotEquivComm, quotientEquiv_mk,
    polynomialQuotientEquivQuotientPolynomial_map_mk]

@[simp]
/--
theorem `Polynomial.quotQuotEquivComm_symm_mk_mk` / 定理 `Polynomial.quotQuotEquivComm_symm_mk_mk`

English:
theorem Polynomial.quotQuotEquivComm_symm_mk_mk
  given: (p : R[X])
  proof: by
  simp only [Polynomial.quotQuotEquivComm, quotientEquiv_symm_mk,
    polynomialQuotientEquivQuotientPolynomial_symm_mk]

中文:
定理 多项式.quotQuotEquivComm_symm_mk_mk
  条件: (p : R[X])
  证明: by
  simp only [Polynomial.quotQuotEquivComm, quotientEquiv_symm_mk,
    polynomialQuotientEquivQuotientPolynomial_symm_mk]

Depends on / 依赖: Polynomial, Polynomial.quotQuotEquivComm, polynomialQuotientEquivQuotientPolynomial_symm_mk, quotQuotEquivComm, quotientEquiv_symm_mk
-/
theorem Polynomial.quotQuotEquivComm_symm_mk_mk (p : R[X]) :
    (Polynomial.quotQuotEquivComm I f).symm (Ideal.Quotient.mk (span
    ({(Ideal.Quotient.mk (I.map C)) f} : Set (R[X] ⧸ (I.map C)))) (Ideal.Quotient.mk (I.map C) p)) =
      Ideal.Quotient.mk (span {f.map (Ideal.Quotient.mk I)}) (p.map (Ideal.Quotient.mk I)) := by
  simp only [Polynomial.quotQuotEquivComm, quotientEquiv_symm_mk,
    polynomialQuotientEquivQuotientPolynomial_symm_mk]

/--
Definition of `quotAdjoinRootEquivQuotPolynomialQuot` / `quotAdjoinRootEquivQuotPolynomialQuot` 的定义

English:
definition quotAdjoinRootEquivQuotPolynomialQuot
  signature: :
  body: (quotMapOfEquivQuotMapCMapMk I f).trans
    ((quotMapCMapSpanMkEquivQuotMapCQuotMapMk I f).trans
      ((Ideal.quotEquivOfEq (by rw [map_span, Set.image_singleton])).trans
        (Polynomial.quotQuotEquivComm I f).symm))

中文:
定义 quotAdjoinRootEquivQuotPolynomialQuot
  签名: :
  定义体: (quotMapOfEquivQuotMapCMapMk I f).trans
    ((quotMapCMapSpanMkEquivQuotMapCQuotMapMk I f).trans
      ((Ideal.quotEquivOfEq (by rw [map_span, Set.image_singleton])).trans
        (Polynomial.quotQuotEquivComm I f).symm))

Depends on / 依赖: Ideal.quotEquivOfEq, Polynomial, Polynomial.quotQuotEquivComm, Set.image_singleton, image_singleton, map_span, quotEquivOfEq, quotMapCMapSpanMkEquivQuotMapCQuotMapMk, quotMapOfEquivQuotMapCMapMk, quotQuotEquivComm
-/
def quotAdjoinRootEquivQuotPolynomialQuot :
    AdjoinRoot f ⧸ I.map (of f) ≃+*
    (R ⧸ I)[X] ⧸ span ({f.map (Ideal.Quotient.mk I)} : Set (R ⧸ I)[X]) :=
  (quotMapOfEquivQuotMapCMapMk I f).trans
    ((quotMapCMapSpanMkEquivQuotMapCQuotMapMk I f).trans
      ((Ideal.quotEquivOfEq (by rw [map_span, Set.image_singleton])).trans
        (Polynomial.quotQuotEquivComm I f).symm))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `quotAdjoinRootEquivQuotPolynomialQuot_mk_of` / 定理 `quotAdjoinRootEquivQuotPolynomialQuot_mk_of`

English:
theorem quotAdjoinRootEquivQuotPolynomialQuot_mk_of
  given: (p : R[X])
  proof: rfl

@[simp]

中文:
定理 quotAdjoinRootEquivQuotPolynomialQuot_mk_of
  条件: (p : R[X])
  证明: rfl

@[simp]
-/
theorem quotAdjoinRootEquivQuotPolynomialQuot_mk_of (p : R[X]) :
    quotAdjoinRootEquivQuotPolynomialQuot I f (Ideal.Quotient.mk (I.map (of f)) (mk f p)) =
      Ideal.Quotient.mk (span ({f.map (Ideal.Quotient.mk I)} : Set (R ⧸ I)[X]))
      (p.map (Ideal.Quotient.mk I)) := rfl

@[simp]
/--
theorem `quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk` / 定理 `quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk`

English:
theorem quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk
  given: (p : R[X])
  proof: by
  rw [quotAdjoinRootEquivQuotPolynomialQuot]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_symm]; rw [Polynomial.quotQuotEquivComm_mk]; rw [Ideal.quotEquivOfEq_symm]; rw [Ideal.quotEquivOfEq_mk]; rw [←
    RingHom.comp_apply

中文:
定理 quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk
  条件: (p : R[X])
  证明: by
  rw [quotAdjoinRootEquivQuotPolynomialQuot]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_symm]; rw [Polynomial.quotQuotEquivComm_mk]; rw [Ideal.quotEquivOfEq_symm]; rw [Ideal.quotEquivOfEq_mk]; rw [←
    RingHom.comp_apply

Depends on / 依赖: DoubleQuot, DoubleQuot.quotQuotMk, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_symm, Polynomial, Polynomial.quotQuotEquivComm_mk, RingEquiv, RingEquiv.symm_symm, RingEquiv.symm_trans_apply, RingHom, RingHom.comp_apply, comp_apply, quotAdjoinRootEquivQuotPolynomialQuot, quotEquivOfEq_mk, quotEquivOfEq_symm, quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk, quotMapOfEquivQuotMapCMapMk_symm_mk, quotQuotEquivComm_mk, quotQuotMk, symm_symm
-/
theorem quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk (p : R[X]) :
    (quotAdjoinRootEquivQuotPolynomialQuot I f).symm
        (Ideal.Quotient.mk (span ({f.map (Ideal.Quotient.mk I)} : Set (R ⧸ I)[X]))
        (p.map (Ideal.Quotient.mk I))) =
      Ideal.Quotient.mk (I.map (of f)) (mk f p) := by
  rw [quotAdjoinRootEquivQuotPolynomialQuot]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_trans_apply]; rw [RingEquiv.symm_symm]; rw [Polynomial.quotQuotEquivComm_mk]; rw [Ideal.quotEquivOfEq_symm]; rw [Ideal.quotEquivOfEq_mk]; rw [←
    RingHom.comp_apply]; rw [← DoubleQuot.quotQuotMk]; rw [quotMapCMapSpanMkEquivQuotMapCQuotMapMk_symm_quotQuotMk]; rw [quotMapOfEquivQuotMapCMapMk_symm_mk]

/-- Promote `AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot` to an `AlgEquiv`. -/
@[simps!]
/--
Definition of `quotEquivQuotMap` / `quotEquivQuotMap` 的定义

English:
definition quotEquivQuotMap
  signature: (f : R[X]) (I : Ideal R)
  body: AlgEquiv.ofRingEquiv
    (show forall x, (quotAdjoinRootEquivQuotPolynomialQuot I f) (algebraMap R _ x) = algebraMap R _ x
      from fun x => by
      have :
        algebraMap R (AdjoinRoot f ⧸ Ideal.map (of f) I) x =
          Ideal.Quotient.mk (Ideal.map (AdjoinRoot.of f) I) ((mk f) (C x)) :=
  

中文:
定义 quotEquivQuotMap
  签名: (f : R[X]) (I : 理想 R)
  定义体: AlgEquiv.ofRingEquiv
    (show forall x, (quotAdjoinRootEquivQuotPolynomialQuot I f) (algebraMap R _ x) = algebraMap R _ x
      from fun x => by
      have :
        algebraMap R (AdjoinRoot f ⧸ Ideal.map (of f) I) x =
          Ideal.Quotient.mk (Ideal.map (AdjoinRoot.of f) I) ((mk f) (C x)) :=
  

Depends on / 依赖: AdjoinRoot, AdjoinRoot.of, AlgEquiv, AlgEquiv.ofRingEquiv, Ideal.Quotient.mk, Ideal.map, Polynomial, Polynomial.algebraMap_apply, Quotient, Quotient.alg_map_eq, Quotient.algebraMap_eq, RingHom, RingHom.comp_apply, alg_map_eq, algebraMap, algebraMap_apply, algebraMap_eq, comp_apply, map_C, ofRingEquiv
-/
noncomputable def quotEquivQuotMap (f : R[X]) (I : Ideal R) :
    (AdjoinRoot f ⧸ Ideal.map (of f) I) ≃ₐ[R]
      (R ⧸ I)[X] ⧸ Ideal.span ({Polynomial.map (Ideal.Quotient.mk I) f} : Set (R ⧸ I)[X]) :=
  AlgEquiv.ofRingEquiv
    (show forall x, (quotAdjoinRootEquivQuotPolynomialQuot I f) (algebraMap R _ x) = algebraMap R _ x
      from fun x => by
      have :
        algebraMap R (AdjoinRoot f ⧸ Ideal.map (of f) I) x =
          Ideal.Quotient.mk (Ideal.map (AdjoinRoot.of f) I) ((mk f) (C x)) :=
        rfl
      rw [this]; rw [quotAdjoinRootEquivQuotPolynomialQuot_mk_of]; rw [map_C]; rw [Quotient.alg_map_eq]
      simp only [RingHom.comp_apply, Quotient.algebraMap_eq, Polynomial.algebraMap_apply])

/--
theorem `quotEquivQuotMap_apply_mk` / 定理 `quotEquivQuotMap_apply_mk`

English:
theorem quotEquivQuotMap_apply_mk
  given: (f g : R[X]) (I : Ideal R)
  proof: by
  rw [AdjoinRoot.quotEquivQuotMap_apply]; rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]

中文:
定理 quotEquivQuotMap_apply_mk
  条件: (f g : R[X]) (I : 理想 R)
  证明: by
  rw [AdjoinRoot.quotEquivQuotMap_apply]; rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]

Depends on / 依赖: AdjoinRoot, AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of, AdjoinRoot.quotEquivQuotMap_apply, quotAdjoinRootEquivQuotPolynomialQuot_mk_of, quotEquivQuotMap_apply
-/
theorem quotEquivQuotMap_apply_mk (f g : R[X]) (I : Ideal R) :
    AdjoinRoot.quotEquivQuotMap f I (Ideal.Quotient.mk (Ideal.map (of f) I) (AdjoinRoot.mk f g)) =
      Ideal.Quotient.mk (Ideal.span ({Polynomial.map (Ideal.Quotient.mk I) f} : Set (R ⧸ I)[X]))
      (g.map (Ideal.Quotient.mk I)) := by
  rw [AdjoinRoot.quotEquivQuotMap_apply]; rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]

/--
theorem `quotEquivQuotMap_symm_apply_mk` / 定理 `quotEquivQuotMap_symm_apply_mk`

English:
theorem quotEquivQuotMap_symm_apply_mk
  given: (f g : R[X]) (I : Ideal R)
  proof: by
  rw [AdjoinRoot.quotEquivQuotMap_symm_apply]; rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk]

中文:
定理 quotEquivQuotMap_symm_apply_mk
  条件: (f g : R[X]) (I : 理想 R)
  证明: by
  rw [AdjoinRoot.quotEquivQuotMap_symm_apply]; rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk]

Depends on / 依赖: AdjoinRoot, AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk, AdjoinRoot.quotEquivQuotMap_symm_apply, quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk, quotEquivQuotMap_symm_apply
-/
theorem quotEquivQuotMap_symm_apply_mk (f g : R[X]) (I : Ideal R) :
    (AdjoinRoot.quotEquivQuotMap f I).symm (Ideal.Quotient.mk _
      (Polynomial.map (Ideal.Quotient.mk I) g)) =
        Ideal.Quotient.mk (Ideal.map (of f) I) (AdjoinRoot.mk f g) := by
  rw [AdjoinRoot.quotEquivQuotMap_symm_apply]; rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_symm_mk_mk]

end

section TensorProduct
variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [CommRing U] [Algebra R U] {p : Polynomial S}

open Algebra TensorProduct

variable (p) in
/--
Definition of `tensorAlgEquiv` / `tensorAlgEquiv` 的定义

English:
definition tensorAlgEquiv
  signature: (p : S[X]) (q : (T otimes[R] S)[X]) (h : p.map includeRight.toRingHom = q)
  body: by
  refine .ofAlgHom
    (Algebra.TensorProduct.lift (algHom T T _)
      (mapAlgHom includeRight p q <| by exact h.symm.dvd) fun _ _ => .all ..)
    (liftAlgHom _ (Algebra.TensorProduct.map (AlgHom.id T T)
      (((Algebra.ofId S (AdjoinRoot p))).restrictScalars R)) (1 otimesₜ root _) ?_) ?_ ?_
  

中文:
定义 tensorAlgEquiv
  签名: (p : S[X]) (q : (T otimes[R] S)[X]) (h : p.map includeRight.toRingHom = q)
  定义体: by
  refine .ofAlgHom
    (Algebra.TensorProduct.lift (algHom T T _)
      (mapAlgHom includeRight p q <| by exact h.symm.dvd) fun _ _ => .all ..)
    (liftAlgHom _ (Algebra.TensorProduct.map (AlgHom.id T T)
      (((Algebra.ofId S (AdjoinRoot p))).restrictScalars R)) (1 otimesₜ root _) ?_) ?_ ?_
  

Depends on / 依赖: AdjoinRoot, AlgHom, AlgHom.id, AlgHom.toRingHom_eq_coe, Algebra, Algebra.TensorProduct.lift, Algebra.TensorProduct.map, Algebra.ofId, Polynomial, Polynomial.eval, TensorProduct, algHom, h.symm.dvd, includeRight, liftAlgHom, mapAlgHom, map_comp_includeRight, ofAlgHom, restrictScalars, toRingHom
-/
def tensorAlgEquiv (p : S[X]) (q : (T otimes[R] S)[X]) (h : p.map includeRight.toRingHom = q) :
    T otimes[R] AdjoinRoot p ≃ₐ[T] AdjoinRoot q := by
  refine .ofAlgHom
    (Algebra.TensorProduct.lift (algHom T T _)
      (mapAlgHom includeRight p q <| by exact h.symm.dvd) fun _ _ => .all ..)
    (liftAlgHom _ (Algebra.TensorProduct.map (AlgHom.id T T)
      (((Algebra.ofId S (AdjoinRoot p))).restrictScalars R)) (1 otimesₜ root _) ?_) ?_ ?_
  · simp only [← h, AlgHom.toRingHom_eq_coe]
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((Algebra.TensorProduct.map (AlgHom.id R T) _).comp _).toRingHom _ _ = _
    simp only [map_comp_includeRight, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      AlgHom.coe_restrictScalars, ← Polynomial.eval₂_map]
    change Polynomial.eval₂ _ ((RingHomClass.toRingHom includeRight) (root p)) (p.map (of _)) = _
    rw [Polynomial.eval₂_hom]
    simp [Polynomial.eval_map]
  · ext
    · simp [Algebra.ofId_apply]
    simp
  · ext : 3 <;> simp

/--
lemma `tensorAlgEquiv_root` / 引理 `tensorAlgEquiv_root`

English:
lemma tensorAlgEquiv_root
  given: (p : S[X]) (q : Polynomial (T otimes[R] S)) (h)
  proof: by simp [tensorAlgEquiv]

中文:
引理 tensorAlgEquiv_root
  条件: (p : S[X]) (q : 多项式 (T otimes[R] S)) (h)
  证明: by simp [tensorAlgEquiv]
-/
@[simp] lemma tensorAlgEquiv_root (p : S[X]) (q : Polynomial (T otimes[R] S)) (h) :
    tensorAlgEquiv p q h (1 otimesₜ root p) = root q := by simp [tensorAlgEquiv]

/--
lemma `tensorAlgEquiv_of` / 引理 `tensorAlgEquiv_of`

English:
lemma tensorAlgEquiv_of
  given: (p : S[X]) (q : Polynomial (T otimes[R] S)) (h) {x : S}
  proof: by simp [tensorAlgEquiv]

中文:
引理 tensorAlgEquiv_of
  条件: (p : S[X]) (q : 多项式 (T otimes[R] S)) (h) {x : S}
  证明: by simp [tensorAlgEquiv]
-/
@[simp] lemma tensorAlgEquiv_of (p : S[X]) (q : Polynomial (T otimes[R] S)) (h) {x : S} :
    tensorAlgEquiv p q h (1 otimesₜ of p x) = of q (1 otimesₜ x):= by simp [tensorAlgEquiv]

end TensorProduct

end AdjoinRoot

namespace PowerBasis

open AdjoinRoot AlgEquiv

variable [CommRing R] [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `α` have minimal polynomial `f` over `R` and `I` be an ideal of `R`,
then `R[α] / (I) = (R[x] / (f)) / pS = (R/p)[x] / (f mod p)`. -/
@[simps!]
/--
Definition of `quotientEquivQuotientMinpolyMap` / `quotientEquivQuotientMinpolyMap` 的定义

English:
definition quotientEquivQuotientMinpolyMap
  signature: (pb : PowerBasis R S) (I : Ideal R)
  body: (ofRingEquiv
        (show forall x,
            (Ideal.quotientEquiv _ (Ideal.map (AdjoinRoot.of (minpoly R pb.gen)) I)
                  (AdjoinRoot.equiv' (minpoly R pb.gen) pb
                        (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
                        (minpoly.aeval _ _)).s

中文:
定义 quotientEquivQuotientMinpolyMap
  签名: (pb : PowerBasis R S) (I : 理想 R)
  定义体: (ofRingEquiv
        (show forall x,
            (Ideal.quotientEquiv _ (Ideal.map (AdjoinRoot.of (minpoly R pb.gen)) I)
                  (AdjoinRoot.equiv' (minpoly R pb.gen) pb
                        (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
                        (minpoly.aeval _ _)).s

Depends on / 依赖: AdjoinRoot, AdjoinRoot.aeval_eq, AdjoinRoot.algebraMap_eq, AdjoinRoot.equiv, AdjoinRoot.mk_self, AdjoinRoot.of, AlgEquiv, AlgEquiv.coe_ringHom_commutes, AlgHom, AlgHom.comp_algebraMap, I.map, Ideal.Quotient.mk_algebraMap, Ideal.map, Ideal.map_map, Ideal.quotientEquiv, Ideal.quotientEquiv_apply, Quotient, aeval_eq, algebraMap, algebraMap_eq
-/
noncomputable def quotientEquivQuotientMinpolyMap (pb : PowerBasis R S) (I : Ideal R) :
    (S ⧸ I.map (algebraMap R S)) ≃ₐ[R]
      Polynomial (R ⧸ I) ⧸
        Ideal.span ({(minpoly R pb.gen).map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))) :=
  (ofRingEquiv
        (show forall x,
            (Ideal.quotientEquiv _ (Ideal.map (AdjoinRoot.of (minpoly R pb.gen)) I)
                  (AdjoinRoot.equiv' (minpoly R pb.gen) pb
                        (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
                        (minpoly.aeval _ _)).symm.toRingEquiv
                  (by rw [Ideal.map_map,
                      ← AlgEquiv.coe_ringHom_commutes, ← AdjoinRoot.algebraMap_eq,
                      AlgHom.comp_algebraMap]))
                (algebraMap R (S ⧸ I.map (algebraMap R S)) x) = algebraMap R _ x from fun x => by
                  rw [← Ideal.Quotient.mk_algebraMap]; rw [Ideal.quotientEquiv_apply]; rw [RingHom.toFun_eq_coe]; rw [Ideal.quotientMap_mk]; rw [RingEquiv.coe_toRingHom]; rw [AlgEquiv.coe_ringEquiv]; rw [AlgEquiv.commutes]; rw [Quotient.mk_algebraMap])).trans (AdjoinRoot.quotEquivQuotMap _ _)

-- This lemma should have the simp tag but this causes a lint issue.
/--
theorem `quotientEquivQuotientMinpolyMap_apply_mk` / 定理 `quotientEquivQuotientMinpolyMap_apply_mk`

English:
theorem quotientEquivQuotientMinpolyMap_apply_mk
  given: (pb : PowerBasis R S) (I : Ideal R) (g : R[X])
  proof: by
  rw [PowerBasis.quotientEquivQuotientMinpolyMap]; rw [AlgEquiv.trans_apply]; rw [AlgEquiv.ofRingEquiv_apply]; rw [quotientEquiv_mk]; rw [AlgEquiv.coe_ringEquiv]; rw [AdjoinRoot.equiv'_symm_apply]; rw [PowerBasis.lift_aeval]; rw [AdjoinRoot.aeval_eq]; rw [AdjoinRoot.quotEquivQuotMap_apply_mk]

中文:
定理 quotientEquivQuotientMinpolyMap_apply_mk
  条件: (pb : PowerBasis R S) (I : 理想 R) (g : R[X])
  证明: by
  rw [PowerBasis.quotientEquivQuotientMinpolyMap]; rw [AlgEquiv.trans_apply]; rw [AlgEquiv.ofRingEquiv_apply]; rw [quotientEquiv_mk]; rw [AlgEquiv.coe_ringEquiv]; rw [AdjoinRoot.equiv'_symm_apply]; rw [PowerBasis.lift_aeval]; rw [AdjoinRoot.aeval_eq]; rw [AdjoinRoot.quotEquivQuotMap_apply_mk]

Depends on / 依赖: AdjoinRoot, AdjoinRoot.aeval_eq, AdjoinRoot.equiv, AdjoinRoot.quotEquivQuotMap_apply_mk, AlgEquiv, AlgEquiv.coe_ringEquiv, AlgEquiv.ofRingEquiv_apply, AlgEquiv.trans_apply, PowerBasis, PowerBasis.lift_aeval, PowerBasis.quotientEquivQuotientMinpolyMap, _symm_apply, aeval_eq, coe_ringEquiv, lift_aeval, ofRingEquiv_apply, quotEquivQuotMap_apply_mk, quotientEquivQuotientMinpolyMap, quotientEquiv_mk, trans_apply
-/
theorem quotientEquivQuotientMinpolyMap_apply_mk (pb : PowerBasis R S) (I : Ideal R) (g : R[X]) :
    pb.quotientEquivQuotientMinpolyMap I (Ideal.Quotient.mk (I.map (algebraMap R S))
      (aeval pb.gen g)) = Ideal.Quotient.mk
        (Ideal.span ({(minpoly R pb.gen).map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))))
          (g.map (Ideal.Quotient.mk I)) := by
  rw [PowerBasis.quotientEquivQuotientMinpolyMap]; rw [AlgEquiv.trans_apply]; rw [AlgEquiv.ofRingEquiv_apply]; rw [quotientEquiv_mk]; rw [AlgEquiv.coe_ringEquiv]; rw [AdjoinRoot.equiv'_symm_apply]; rw [PowerBasis.lift_aeval]; rw [AdjoinRoot.aeval_eq]; rw [AdjoinRoot.quotEquivQuotMap_apply_mk]

-- This lemma should have the simp tag but this causes a lint issue.
set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `quotientEquivQuotientMinpolyMap_symm_apply_mk` / 定理 `quotientEquivQuotientMinpolyMap_symm_apply_mk`

English:
theorem quotientEquivQuotientMinpolyMap_symm_apply_mk
  statement: (pb : PowerBasis R S) (I : Ideal R)
  proof: by
  simp [quotientEquivQuotientMinpolyMap, aeval_def]

中文:
定理 quotientEquivQuotientMinpolyMap_symm_apply_mk
  结论: (pb : PowerBasis R S) (I : 理想 R)
  证明: by
  simp [quotientEquivQuotientMinpolyMap, aeval_def]

Depends on / 依赖: aeval_def, quotientEquivQuotientMinpolyMap
-/
theorem quotientEquivQuotientMinpolyMap_symm_apply_mk (pb : PowerBasis R S) (I : Ideal R)
    (g : R[X]) :
    (pb.quotientEquivQuotientMinpolyMap I).symm (Ideal.Quotient.mk (Ideal.span
      ({(minpoly R pb.gen).map (Ideal.Quotient.mk I)} : Set (Polynomial (R ⧸ I))))
        (g.map (Ideal.Quotient.mk I))) = Ideal.Quotient.mk (I.map (algebraMap R S))
          (aeval pb.gen g) := by
  simp [quotientEquivQuotientMinpolyMap, aeval_def]

end PowerBasis

/--
theorem `Irreducible.exists_dvd_monic_irreducible_of_isIntegral` / 定理 `Irreducible.exists_dvd_monic_irreducible_of_isIntegral`

English:
theorem Irreducible.exists_dvd_monic_irreducible_of_isIntegral
  statement: {K L : Type*}
  proof: by
  have := Fact.mk hf
  have h := hf.ne_zero
  have h2 := isIntegral_trans (R := K) _ (AdjoinRoot.isIntegral_root h)
  have h3 := (AdjoinRoot.minpoly_root h) ▸ minpoly.dvd_map_of_isScalarTower K L (AdjoinRoot.root f)
  exact ⟨_, minpoly.monic h2, minpoly.irreducible h2, dvd_of_mul_right_dvd h3⟩

中文:
定理 不可约.存在_dvd_monic_irreducible_of_is整数egral
  结论: {K L : 类型}
  证明: by
  have := Fact.mk hf
  have h := hf.ne_zero
  have h2 := isIntegral_trans (R := K) _ (AdjoinRoot.isIntegral_root h)
  have h3 := (AdjoinRoot.minpoly_root h) ▸ minpoly.dvd_map_of_isScalarTower K L (AdjoinRoot.root f)
  exact ⟨_, minpoly.monic h2, minpoly.irreducible h2, dvd_of_mul_right_dvd h3⟩

Depends on / 依赖: AdjoinRoot, AdjoinRoot.isIntegral_root, AdjoinRoot.minpoly_root, AdjoinRoot.root, Fact.mk, dvd_map_of_isScalarTower, dvd_of_mul_right_dvd, hf.ne_zero, irreducible, isIntegral_root, isIntegral_trans, minpoly, minpoly.dvd_map_of_isScalarTower, minpoly.irreducible, minpoly.monic, minpoly_root, ne_zero
-/
theorem Irreducible.exists_dvd_monic_irreducible_of_isIntegral {K L : Type*}
    [CommRing K] [IsDomain K] [Field L] [Algebra K L] [Algebra.IsIntegral K L] {f : L[X]}
    (hf : Irreducible f) : exists g : K[X], g.Monic ∧ Irreducible g ∧ f ∣ g.map (algebraMap K L) := by
  have := Fact.mk hf
  have h := hf.ne_zero
  have h2 := isIntegral_trans (R := K) _ (AdjoinRoot.isIntegral_root h)
  have h3 := (AdjoinRoot.minpoly_root h) ▸ minpoly.dvd_map_of_isScalarTower K L (AdjoinRoot.root f)
  exact ⟨_, minpoly.monic h2, minpoly.irreducible h2, dvd_of_mul_right_dvd h3⟩

/--
lemma `Polynomial.Monic.exists_splits_map.` / 引理 `Polynomial.Monic.exists_splits_map.`

English:
lemma Polynomial.Monic.exists_splits_map.{u}
  proof: by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing R with | h n IH =>
  by_cases hpu : IsUnit p
  · obtain rfl := hp.eq_one_of_isUnit hpu
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, by simp⟩
  obtain ⟨q, hq⟩ : X - C (AdjoinRoot.roo

中文:
引理 多项式.Monic.存在_splits_map.{u}
  证明: by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing R with | h n IH =>
  by_cases hpu : IsUnit p
  · obtain rfl := hp.eq_one_of_isUnit hpu
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, by simp⟩
  obtain ⟨q, hq⟩ : X - C (AdjoinRoot.roo

Depends on / 依赖: AdjoinRoot, AdjoinRoot.algebraMap_eq, AdjoinRoot.root, IsUnit, Nat.strong_induction_on, algebraMap, algebraMap_eq, dvd_iff_isRoot, eq_one_of_isUnit, finite, free_adjoinRoot, generalizing, hp.eq_one_of_isUnit, hp.finite, hp.free_adjoinRoot, hp.map, monic_X_sub_C, natDegree, of_mul_monic_left, p.map
-/
lemma Polynomial.Monic.exists_splits_map.{u}
    {R : Type u} [CommRing R] [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    exists (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S) (_ : Module.Free R S)
      (_ : Nontrivial S), (p.map (algebraMap R S)).Splits := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing R with | h n IH =>
  by_cases hpu : IsUnit p
  · obtain rfl := hp.eq_one_of_isUnit hpu
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, by simp⟩
  obtain ⟨q, hq⟩ : X - C (AdjoinRoot.root p) ∣ p.map (algebraMap _ _) := by
    simp [dvd_iff_isRoot, -AdjoinRoot.algebraMap_eq]
  have hqm : q.Monic := .of_mul_monic_left (monic_X_sub_C (.root _)) (hq ▸ hp.map _)
  have := hp.free_adjoinRoot
  have := hp.finite_adjoinRoot
  have : Nontrivial (AdjoinRoot p) := Ideal.Quotient.nontrivial_iff.mpr (by simpa)
  obtain ⟨S, _, _, _, _, _, hS⟩ := IH _
    (by rw [← hn, ← hp.natDegree_map (algebraMap R (AdjoinRoot p)), hq,
      Monic.natDegree_mul (monic_X_sub_C _) hqm]; simp) hqm rfl
  algebraize [(algebraMap (AdjoinRoot p) S).comp (algebraMap R (AdjoinRoot p))]
  refine ⟨S, ‹_›, ‹_›, .trans (AdjoinRoot p) _, .trans (S := AdjoinRoot p), ‹_›, ?_⟩
  rw [IsScalarTower.algebraMap_eq R (AdjoinRoot p)]; rw [← Polynomial.map_map]; rw [hq]; rw [Polynomial.map_mul]
  exact .mul (by simp) hS
