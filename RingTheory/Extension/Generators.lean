/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Extension.Basic

/-!

# Generators of algebras

## Main definition

- `Algebra.Generators`: A family of generators of an `R`-algebra `S` consists of
  1. `ι`: The type of variables.
  2. `val : ι → S`: The assignment of each variable to a value.
  3. `σ`: A set-theoretic section of the induced `R`-algebra homomorphism `R[X] → S`, where we
     write `R[X]` for `R[ι]`.

- `Algebra.Generators.Hom`: Given a commuting square
  ```
  R --→ P = R[X] ---→ S
  | |
  ↓ ↓
  R' -→ P' = R'[X'] → S
  ```
  A hom between `P` and `P'` is an assignment `X → P'` such that the arrows commute.

- `Algebra.Generators.Cotangent`: The cotangent space w.r.t. `P = R[X] → S`, i.e. the
  space `I/I²` with `I` being the kernel of the presentation.

- `Algebra.Generators.mvPolynomial`: The canonical `R`-generators of the polynomial algebra
  `MvPolynomial ι R`, indexed by `ι` via the variables `X`.

## TODOs

Currently, Lean does not see through the `ι` field of terms of `Generators R S` obtained
from constructions, e.g. composition. This causes fragile and cumbersome proofs, because
`simp` and `rw` often don't work properly. `Generators R S` (and `Presentation R S`, etc.) should
be refactored in a way that makes these equalities reducibly def-eq, for example
by unbundling the `ι` field or making the field globally reducible in constructions using
unification hints.

-/

@[expose] public section

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) (ι : Type w) [CommRing R] [CommRing S] [Algebra R S]

/--
Definition of `Algebra.Generators` / `Algebra.Generators` 的定义

English:
structure Algebra.Generators
  parameters: where
  axioms and operations (5):
    - val : ι -> S
    - σ' : S -> MvPolynomial ι R
    - aeval_val_σ' : forall s, aeval val (σ' s) = s
    - algebra : Algebra (MvPolynomial ι R) S  [default: (aeval val).toAlgebra]
    - algebraMap_eq : algebraMap (MvPolynomial ι R) S = aeval (R := R) val  [default: by rfl]

中文:
结构 代数.生成元
  参数: where
  公理与运算 (5 个):
    - val : ι -> S
    - σ' : S -> 多元多项式 ι R
    - aeval_val_σ' : 对任意 s, aeval val (σ' s) = s
    - algebra : 代数 (多元多项式 ι R) S  [默认: (aeval val).toAlgebra]
    - algebraMap_eq : algebraMap (多元多项式 ι R) S = aeval (R := R) val  [默认: by rfl]

Depends on / 依赖: toAlgebra
-/
structure Algebra.Generators where
  /-- The assignment of each variable to a value in `S`. -/
  val : ι -> S
  /-- A section of `R[X] → S`. -/
  σ' : S -> MvPolynomial ι R
  aeval_val_σ' : forall s, aeval val (σ' s) = s
  /-- An `R[X]`-algebra instance on `S`. The default is the one induced by the map `R[X] → S`,
  but this causes a diamond if there is an existing instance. -/
  algebra : Algebra (MvPolynomial ι R) S := (aeval val).toAlgebra
  algebraMap_eq :
    algebraMap (MvPolynomial ι R) S = aeval (R := R) val := by rfl

namespace Algebra.Generators

variable {R S ι}
variable (P : Generators R S ι)

set_option linter.unusedVariables false in
/-- The polynomial ring w.r.t. a family of generators. -/
@[nolint unusedArguments]
protected
/--
Definition of `Ring` / `Ring` 的定义

English:
abbreviation Ring
  signature: (P : Generators R S ι)
  body: MvPolynomial ι R

中文:
缩写 环
  签名: (P : 生成元 R S ι)
  定义体: MvPolynomial ι R

Depends on / 依赖: MvPolynomial
-/
abbrev Ring (P : Generators R S ι) : Type (max w u) := MvPolynomial ι R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra P.Ring S
  body: P.algebra

中文:
实例 :
  签名: 代数 P.环 S
  定义体: P.algebra

Depends on / 依赖: P.algebra, algebra
-/
instance : Algebra P.Ring S := P.algebra

/--
Definition of `σ` / `σ` 的定义

English:
definition σ
  signature: : S -> P.Ring
  body: P.σ'

中文:
定义 σ
  签名: : S -> P.环
  定义体: P.σ'
-/
def σ : S -> P.Ring := P.σ'

/--
Definition of `Simps.σ` / `Simps.σ` 的定义

English:
definition Simps.σ
  signature: : S -> P.Ring
  body: P.σ

initialize_simps_projections Algebra.Generators (σ' -> σ)

@[simp]

中文:
定义 Simps.σ
  签名: : S -> P.环
  定义体: P.σ

initialize_simps_projections Algebra.Generators (σ' -> σ)

@[simp]
-/
def Simps.σ : S -> P.Ring := P.σ

initialize_simps_projections Algebra.Generators (σ' -> σ)

@[simp]
/--
lemma `aeval_val_σ` / 引理 `aeval_val_σ`

English:
lemma aeval_val_σ
  given: (s)
  statement: aeval P.val (P.σ s) = s
  proof: P.aeval_val_σ' s

中文:
引理 aeval_val_σ
  条件: (s)
  结论: aeval P.val (P.σ s) = s
  证明: P.aeval_val_σ' s

Depends on / 依赖: P.aeval_val_
-/
lemma aeval_val_σ (s) : aeval P.val (P.σ s) = s := P.aeval_val_σ' s

noncomputable instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
IsScalarTower R₀ P.Ring S := IsScalarTower.of_algebraMap_eq'
  P.algebraMap_eq ▸ ((aeval (R := R) P.val).comp_algebraMap_of_tower R₀).symm

@[simp]
/--
lemma `algebraMap_apply` / 引理 `algebraMap_apply`

English:
lemma algebraMap_apply
  given: (x)
  statement: algebraMap P.Ring S x = aeval (R := R) P.val x
  proof: by
  simp [algebraMap_eq]

@[simp]

中文:
引理 algebraMap_apply
  条件: (x)
  结论: algebraMap P.环 S x = aeval (R := R) P.val x
  证明: by
  simp [algebraMap_eq]

@[simp]

Depends on / 依赖: P.val, algebraMap_eq
-/
lemma algebraMap_apply (x) : algebraMap P.Ring S x = aeval (R := R) P.val x := by
  simp [algebraMap_eq]

@[simp]
/--
lemma `σ_smul` / 引理 `σ_smul`

English:
lemma σ_smul
  given: (x y)
  statement: P.σ x • y = x * y
  proof: by
  rw [Algebra.smul_def]; rw [algebraMap_apply]; rw [aeval_val_σ]

中文:
引理 σ_smul
  条件: (x y)
  结论: P.σ x • y = x * y
  证明: by
  rw [Algebra.smul_def]; rw [algebraMap_apply]; rw [aeval_val_σ]

Depends on / 依赖: Algebra, Algebra.smul_def, algebraMap_apply, smul_def
-/
lemma σ_smul (x y) : P.σ x • y = x * y := by
  rw [Algebra.smul_def]; rw [algebraMap_apply]; rw [aeval_val_σ]

/--
lemma `σ_injective` / 引理 `σ_injective`

English:
lemma σ_injective
  statement: P.σ.Injective
  proof: by
  intro x y e
  rw [← P.aeval_val_σ x]; rw [← P.aeval_val_σ y]; rw [e]

中文:
引理 σ_injective
  结论: P.σ.单射
  证明: by
  intro x y e
  rw [← P.aeval_val_σ x]; rw [← P.aeval_val_σ y]; rw [e]

Depends on / 依赖: P.aeval_val_
-/
lemma σ_injective : P.σ.Injective := by
  intro x y e
  rw [← P.aeval_val_σ x]; rw [← P.aeval_val_σ y]; rw [e]

/--
lemma `aeval_val_surjective` / 引理 `aeval_val_surjective`

English:
lemma aeval_val_surjective
  statement: Function.Surjective (aeval (R := R) P.val)
  proof: fun x => ⟨P.σ x, by simp⟩

中文:
引理 aeval_val_surjective
  结论: 函数.满射 (aeval (R := R) P.val)
  证明: fun x => ⟨P.σ x, by simp⟩

Depends on / 依赖: P.val
-/
lemma aeval_val_surjective : Function.Surjective (aeval (R := R) P.val) :=
  fun x => ⟨P.σ x, by simp⟩

/--
lemma `algebraMap_surjective` / 引理 `algebraMap_surjective`

English:
lemma algebraMap_surjective
  statement: Function.Surjective (algebraMap P.Ring S)
  proof: (⟨_, P.algebraMap_apply _ ▸ P.aeval_val_σ ·⟩)

中文:
引理 algebraMap_surjective
  结论: 函数.满射 (algebraMap P.环 S)
  证明: (⟨_, P.algebraMap_apply _ ▸ P.aeval_val_σ ·⟩)

Depends on / 依赖: P.aeval_val_, P.algebraMap_apply, algebraMap_apply
-/
lemma algebraMap_surjective : Function.Surjective (algebraMap P.Ring S) :=
  (⟨_, P.algebraMap_apply _ ▸ P.aeval_val_σ ·⟩)

section Construction

/-- Construct `Generators` from an assignment `I → S` such that `R[X] → S` is surjective. -/
@[simps val]
noncomputable
/--
Definition of `ofSurjective` / `ofSurjective` 的定义

English:
definition ofSurjective
  signature: (val : ι -> S) (h : Function.Surjective (aeval (R := R) val))
  body: val
  σ' x := (h x).choose
  aeval_val_σ' x := (h x).choose_spec

中文:
定义 ofSurjective
  签名: (val : ι -> S) (h : 函数.满射 (aeval (R := R) val))
  定义体: val
  σ' x := (h x).choose
  aeval_val_σ' x := (h x).choose_spec
-/
def ofSurjective (val : ι -> S) (h : Function.Surjective (aeval (R := R) val)) :
    Generators R S ι where
  val := val
  σ' x := (h x).choose
  aeval_val_σ' x := (h x).choose_spec

/--
Definition of `ofSurjectiveAlgebraMap` / `ofSurjectiveAlgebraMap` 的定义

English:
definition ofSurjectiveAlgebraMap
  signature: (h : Function.Surjective (algebraMap R S))
  body: ofSurjective PEmpty.elim fun s => by
    use C (h s).choose
    simp [(h s).choose_spec]

中文:
定义 ofSurjectiveAlgebraMap
  签名: (h : 函数.满射 (algebraMap R S))
  定义体: ofSurjective PEmpty.elim fun s => by
    use C (h s).choose
    simp [(h s).choose_spec]

Depends on / 依赖: PEmpty, PEmpty.elim, choose_spec, new_name, ofSurjective, syntax, to_fun
-/
noncomputable def ofSurjectiveAlgebraMap (h : Function.Surjective (algebraMap R S)) :
    Generators R S PEmpty.{w + 1} :=
ofSurjective PEmpty.elim fun s => by
    use C (h s).choose
    simp [(h s).choose_spec]

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Generators R R PEmpty.{w + 1}
  body: ofSurjectiveAlgebraMap by
  rw [algebraMap_self]
  exact RingHomSurjective.is_surjective

中文:
定义 id
  签名: : 生成元 R R 命题空.{w + 1}
  定义体: ofSurjectiveAlgebraMap by
  rw [algebraMap_self]
  exact RingHomSurjective.is_surjective

Depends on / 依赖: RingHomSurjective, RingHomSurjective.is_surjective, algebraMap_self, is_surjective, ofSurjectiveAlgebraMap
-/
noncomputable def id : Generators R R PEmpty.{w + 1} := ofSurjectiveAlgebraMap by
  rw [algebraMap_self]
  exact RingHomSurjective.is_surjective

variable (R ι) in
/-- The canonical `R`-generators of the polynomial algebra `MvPolynomial ι R`,
indexed by `ι` via the variables `X`. -/
@[simps σ, simps -fullyApplied val]
/--
Definition of `mvPolynomial` / `mvPolynomial` 的定义

English:
definition mvPolynomial
  signature: : Generators R (MvPolynomial ι R) ι where
  body: X
  σ' f := f
  aeval_val_σ' := aeval_X_left_apply

中文:
定义 mvPolynomial
  签名: : 生成元 R (多元多项式 ι R) ι where
  定义体: X
  σ' f := f
  aeval_val_σ' := aeval_X_left_apply
-/
noncomputable def mvPolynomial : Generators R (MvPolynomial ι R) ι where
  val := X
  σ' f := f
  aeval_val_σ' := aeval_X_left_apply

/-- Construct `Generators` from an assignment `I → S` such that `R[X] → S` is surjective. -/
noncomputable
/--
Definition of `ofAlgHom` / `ofAlgHom` 的定义

English:
definition ofAlgHom
  signature: {I : Type*} (f : MvPolynomial I R ->ₐ[R] S) (h : Function.Surjective f)
  body: ofSurjective (f ∘ X) (by rwa [show aeval (f ∘ X) = f by ext; simp])

中文:
定义 ofAlgHom
  签名: {I : 类型} (f : 多元多项式 I R ->ₐ[R] S) (h : 函数.满射 f)
  定义体: ofSurjective (f ∘ X) (by rwa [show aeval (f ∘ X) = f by ext; simp])

Depends on / 依赖: ofSurjective
-/
def ofAlgHom {I : Type*} (f : MvPolynomial I R ->ₐ[R] S) (h : Function.Surjective f) :
    Generators R S I :=
  ofSurjective (f ∘ X) (by rwa [show aeval (f ∘ X) = f by ext; simp])

/-- Construct `Generators` from a family of generators of `S`. -/
noncomputable
/--
Definition of `ofSet` / `ofSet` 的定义

English:
definition ofSet
  signature: {s : Set S} (hs : Algebra.adjoin R s = ⊤)
  body: by
  refine ofSurjective (Subtype.val : s -> S) ?_
  rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
    Subtype.range_coe_subtype, Set.ofPred_mem_eq]

中文:
定义 ofSet
  签名: {s : 集合 S} (hs : 代数.adjoin R s = ⊤)
  定义体: by
  refine ofSurjective (Subtype.val : s -> S) ?_
  rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
    Subtype.range_coe_subtype, Set.ofPred_mem_eq]

Depends on / 依赖: AlgHom, AlgHom.range_eq_top, Algebra, Algebra.adjoin_range_eq_range_aeval, Set.ofPred_mem_eq, Subtype, Subtype.range_coe_subtype, Subtype.val, adjoin_range_eq_range_aeval, ofPred_mem_eq, ofSurjective, range_coe_subtype, range_eq_top
-/
def ofSet {s : Set S} (hs : Algebra.adjoin R s = ⊤) : Generators R S s := by
  refine ofSurjective (Subtype.val : s -> S) ?_
  rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
    Subtype.range_coe_subtype, Set.ofPred_mem_eq]

variable (R S) in
/-- The `Generators` containing the whole algebra, which induces the canonical map `R[S] → S`. -/
@[simps]
noncomputable
/--
Definition of `self` / `self` 的定义

English:
definition self
  signature: : Generators R S S where
  body: _root_.id
  σ' := X
  aeval_val_σ' := aeval_X _

中文:
定义 self
  签名: : 生成元 R S S where
  定义体: _root_.id
  σ' := X
  aeval_val_σ' := aeval_X _

Depends on / 依赖: _root_, _root_.id
-/
def self : Generators R S S where
  val := _root_.id
  σ' := X
  aeval_val_σ' := aeval_X _

/-- The extension `R[X₁,...,Xₙ] → S` given a family of generators. -/
@[simps]
noncomputable
/--
Definition of `toExtension` / `toExtension` 的定义

English:
definition toExtension
  signature: : Extension R S where
  body: P.Ring
  σ := P.σ
  algebraMap_σ := by simp

中文:
定义 toExtension
  签名: : 扩张 R S where
  定义体: P.Ring
  σ := P.σ
  algebraMap_σ := by simp

Depends on / 依赖: P.Ring
-/
def toExtension : Extension R S where
  Ring := P.Ring
  σ := P.σ
  algebraMap_σ := by simp

/--
Definition of `ofAlgEquiv` / `ofAlgEquiv` 的定义

English:
definition ofAlgEquiv
  body: e ∘ P.val
  σ' := P.σ ∘ e.symm
  aeval_val_σ' t := by
    rw [Function.comp_def]; rw [← AlgHom.coe_coe e]; rw [← MvPolynomial.comp_aeval_apply]
    simp

@[simp]

中文:
定义 ofAlgEquiv
  定义体: e ∘ P.val
  σ' := P.σ ∘ e.symm
  aeval_val_σ' t := by
    rw [Function.comp_def]; rw [← AlgHom.coe_coe e]; rw [← MvPolynomial.comp_aeval_apply]
    simp

@[simp]

Depends on / 依赖: P.val
-/
noncomputable def ofAlgEquiv
    (P : Generators R S ι) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    Generators R T ι where
  val := e ∘ P.val
  σ' := P.σ ∘ e.symm
  aeval_val_σ' t := by
    rw [Function.comp_def]; rw [← AlgHom.coe_coe e]; rw [← MvPolynomial.comp_aeval_apply]
    simp

@[simp]
/--
lemma `ofAlgEquiv_val` / 引理 `ofAlgEquiv_val`

English:
lemma ofAlgEquiv_val
  given: (P : Generators R S ι) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T)
  proof: rfl

中文:
引理 ofAlgEquiv_val
  条件: (P : 生成元 R S ι) {T : 类型} [交换环 T] [代数 R T] (e : S ≃ₐ[R] T)
  证明: rfl

Depends on / 依赖: variable
-/
lemma ofAlgEquiv_val (P : Generators R S ι) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    (P.ofAlgEquiv e).val = e ∘ P.val :=
  rfl

section Localization

variable (r : R) [IsLocalization.Away r S]

variable (S) in
/-- If `S` is the localization of `R` away from `r`, we obtain a canonical generator mapping
to the inverse of `r`. -/
@[simps val, simps -isSimp σ]
noncomputable
/--
Definition of `localizationAway` / `localizationAway` 的定义

English:
definition localizationAway
  signature: : Generators R S Unit where
  body: IsLocalization.Away.invSelf r
  σ' s :=
    letI a : R := (IsLocalization.Away.sec r s).1
    letI n : Nat := (IsLocalization.Away.sec r s).2
    C a * X () ^ n
  aeval_val_σ' s := by
    rw [map_mul]; rw [algHom_C]; rw [map_pow]; rw [aeval_X]
    simp only [← IsLocalization.Away.sec_spec, map_pow, IsLocalization.Away.invSelf]
    rw [← IsLocalization.mk'_pow]; rw [one_pow]; rw [← IsLocalization.mk'_one (M := Submonoid.powers r) S r]
    rw [← IsLocalization.mk'_pow]; rw [one_pow]; rw [mul_assoc]; rw [← IsLocalization.mk'_mul]
    rw [mul_one]; rw [one_mul]; rw [IsLocalization.mk'_pow]
    simp

中文:
定义 localizationAway
  签名: : 生成元 R S 单元 where
  定义体: IsLocalization.Away.invSelf r
  σ' s :=
    letI a : R := (IsLocalization.Away.sec r s).1
    letI n : Nat := (IsLocalization.Away.sec r s).2
    C a * X () ^ n
  aeval_val_σ' s := by
    rw [map_mul]; rw [algHom_C]; rw [map_pow]; rw [aeval_X]
    simp only [← IsLocalization.Away.sec_spec, map_pow, IsLocalization.Away.invSelf]
    rw [← IsLocalization.mk'_pow]; rw [one_pow]; rw [← IsLocalization.mk'_one (M := Submonoid.powers r) S r]
    rw [← IsLocalization.mk'_pow]; rw [one_pow]; rw [mul_assoc]; rw [← IsLocalization.mk'_mul]
    rw [mul_one]; rw [one_mul]; rw [IsLocalization.mk'_pow]
    simp

Depends on / 依赖: IsLocalization, IsLocalization.Away.invSelf, invSelf
-/
def localizationAway : Generators R S Unit where
  val _ := IsLocalization.Away.invSelf r
  σ' s :=
    letI a : R := (IsLocalization.Away.sec r s).1
    letI n : Nat := (IsLocalization.Away.sec r s).2
    C a * X () ^ n
  aeval_val_σ' s := by
    rw [map_mul]; rw [algHom_C]; rw [map_pow]; rw [aeval_X]
    simp only [← IsLocalization.Away.sec_spec, map_pow, IsLocalization.Away.invSelf]
    rw [← IsLocalization.mk'_pow]; rw [one_pow]; rw [← IsLocalization.mk'_one (M := Submonoid.powers r) S r]
    rw [← IsLocalization.mk'_pow]; rw [one_pow]; rw [mul_assoc]; rw [← IsLocalization.mk'_mul]
    rw [mul_one]; rw [one_mul]; rw [IsLocalization.mk'_pow]
    simp

end Localization

variable {ι' : Type*} {T} [CommRing T] [Algebra R T]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given two families of generators `S[X] → T` and `R[Y] → S`,
we may construct the family of generators `R[X, Y] → T`. -/
@[simps val, simps -isSimp σ]
noncomputable
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: [Algebra S T] [IsScalarTower R S T]
  body: Sum.elim Q.val (algebraMap S T ∘ P.val)
  σ' x := (AddMonoidAlgebra.coeff <| Q.σ x).sum fun n r =>
    rename .inr (P.σ r) * monomial (n.mapDomain .inl) 1
  aeval_val_σ' s := by
    have (x : P.Ring) : aeval (algebraMap S T ∘ P.val) x = algebraMap S T (aeval P.val x) := by
      rw [map_aeval]; rw [aeval_def]; rw [coe_eval₂Hom]; rw [← IsScalarTower.algebraMap_eq]; rw [Function.comp_def]
    conv_rhs => rw [← Q.aeval_val_σ s, (Q.σ s).as_sum]
    simp [aeval_rename, this, aeval_monomial, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Finsupp.sum, MvPolynomial.finsupp_support_eq_support, MvPolynomial.coeff]

中文:
定义 comp
  签名: [代数 S T] [标量塔 R S T]
  定义体: Sum.elim Q.val (algebraMap S T ∘ P.val)
  σ' x := (AddMonoidAlgebra.coeff <| Q.σ x).sum fun n r =>
    rename .inr (P.σ r) * monomial (n.mapDomain .inl) 1
  aeval_val_σ' s := by
    have (x : P.Ring) : aeval (algebraMap S T ∘ P.val) x = algebraMap S T (aeval P.val x) := by
      rw [map_aeval]; rw [aeval_def]; rw [coe_eval₂Hom]; rw [← IsScalarTower.algebraMap_eq]; rw [Function.comp_def]
    conv_rhs => rw [← Q.aeval_val_σ s, (Q.σ s).as_sum]
    simp [aeval_rename, this, aeval_monomial, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Finsupp.sum, MvPolynomial.finsupp_support_eq_support, MvPolynomial.coeff]

Depends on / 依赖: P.val, Q.val, Sum.elim, algebraMap
-/
def comp [Algebra S T] [IsScalarTower R S T]
    (Q : Generators S T ι') (P : Generators R S ι) : Generators R T (ι' oplus ι) where
  val := Sum.elim Q.val (algebraMap S T ∘ P.val)
  σ' x := (AddMonoidAlgebra.coeff <| Q.σ x).sum fun n r =>
    rename .inr (P.σ r) * monomial (n.mapDomain .inl) 1
  aeval_val_σ' s := by
    have (x : P.Ring) : aeval (algebraMap S T ∘ P.val) x = algebraMap S T (aeval P.val x) := by
      rw [map_aeval]; rw [aeval_def]; rw [coe_eval₂Hom]; rw [← IsScalarTower.algebraMap_eq]; rw [Function.comp_def]
    conv_rhs => rw [← Q.aeval_val_σ s, (Q.σ s).as_sum]
    simp [aeval_rename, this, aeval_monomial, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Finsupp.sum, MvPolynomial.finsupp_support_eq_support, MvPolynomial.coeff]

variable (S) in
/-- If `R → S → T` is a tower of algebras, a family of generators `R[X] → T`
gives a family of generators `S[X] → T`. -/
@[simps val]
noncomputable
/--
Definition of `extendScalars` / `extendScalars` 的定义

English:
definition extendScalars
  signature: [Algebra S T] [IsScalarTower R S T] (P : Generators R T ι)
  body: P.val
  σ' x := map (algebraMap R S) (P.σ x)
  aeval_val_σ' s := by simp [@aeval_def S, ← IsScalarTower.algebraMap_eq, ← @aeval_def R]

中文:
定义 extendScalars
  签名: [代数 S T] [标量塔 R S T] (P : 生成元 R T ι)
  定义体: P.val
  σ' x := map (algebraMap R S) (P.σ x)
  aeval_val_σ' s := by simp [@aeval_def S, ← IsScalarTower.algebraMap_eq, ← @aeval_def R]

Depends on / 依赖: P.val
-/
def extendScalars [Algebra S T] [IsScalarTower R S T] (P : Generators R T ι) :
    Generators S T ι where
  val := P.val
  σ' x := map (algebraMap R S) (P.σ x)
  aeval_val_σ' s := by simp [@aeval_def S, ← IsScalarTower.algebraMap_eq, ← @aeval_def R]

/-- If `P` is a family of generators of `S` over `R` and `T` is an `R`-algebra, we
obtain a natural family of generators of `T ⊗[R] S` over `T`. -/
@[simps! val]
noncomputable
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: (T) [CommRing T] [Algebra R T] (P : Generators R S ι)
  body: by
  apply Generators.ofSurjective (fun x => 1 otimesₜ[R] P.val x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
    let X := P.σ b
    use a • MvPolynomial.map (algebraMap R T) X
    simp only [LinearMapClass.map_smul, X, aeval_map_algebraMap]
    have : forall y : P.Ring,
      aeval (fun x => (1 otimesₜ[R] P.val x : T otimes[R] S)) y = 1 otimesₜ aeval (fun x => P.val x) y := by
      intro y
      induction y using MvPolynomial.induction_on with
      | C a =>
        rw [aeval_C]; rw [aeval_C]; rw [TensorProduct.algebraMap_apply]; rw [algebraMap_eq_smul_one]; rw [smul_tmul]; rw [algebraMap_eq_smul_one]
      | add p q hp hq => simp [map_add, tmul_add, hp, hq]
      | mul_X p i hp => simp [hp]
    rw [this]; rw [P.aeval_val_σ]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one]
  | add x y ex ey =>
    obtain ⟨a, ha⟩ := ex
    obtain ⟨b, hb⟩ := ey
    use (a + b)
    rw [map_add]; rw [ha]; rw [hb]

中文:
定义 baseChange
  签名: (T) [交换环 T] [代数 R T] (P : 生成元 R S ι)
  定义体: by
  apply Generators.ofSurjective (fun x => 1 otimesₜ[R] P.val x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
    let X := P.σ b
    use a • MvPolynomial.map (algebraMap R T) X
    simp only [LinearMapClass.map_smul, X, aeval_map_algebraMap]
    have : forall y : P.Ring,
      aeval (fun x => (1 otimesₜ[R] P.val x : T otimes[R] S)) y = 1 otimesₜ aeval (fun x => P.val x) y := by
      intro y
      induction y using MvPolynomial.induction_on with
      | C a =>
        rw [aeval_C]; rw [aeval_C]; rw [TensorProduct.algebraMap_apply]; rw [algebraMap_eq_smul_one]; rw [smul_tmul]; rw [algebraMap_eq_smul_one]
      | add p q hp hq => simp [map_add, tmul_add, hp, hq]
      | mul_X p i hp => simp [hp]
    rw [this]; rw [P.aeval_val_σ]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one]
  | add x y ex ey =>
    obtain ⟨a, ha⟩ := ex
    obtain ⟨b, hb⟩ := ey
    use (a + b)
    rw [map_add]; rw [ha]; rw [hb]

Depends on / 依赖: Generators, Generators.ofSurjective, LinearMapClass, LinearMapClass.map_smul, MvPolynomial, MvPolynomial.induction_on, MvPolynomial.map, P.Ring, P.val, TensorProduct, TensorProduct.induction_on, aeval_C, aeval_map_algebraMap, algebraMap, induction_on, map_smul, map_zero, ofSurjective, otimes
-/
def baseChange (T) [CommRing T] [Algebra R T] (P : Generators R S ι) :
    Generators T (T otimes[R] S) ι := by
  apply Generators.ofSurjective (fun x => 1 otimesₜ[R] P.val x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
    let X := P.σ b
    use a • MvPolynomial.map (algebraMap R T) X
    simp only [LinearMapClass.map_smul, X, aeval_map_algebraMap]
    have : forall y : P.Ring,
      aeval (fun x => (1 otimesₜ[R] P.val x : T otimes[R] S)) y = 1 otimesₜ aeval (fun x => P.val x) y := by
      intro y
      induction y using MvPolynomial.induction_on with
      | C a =>
        rw [aeval_C]; rw [aeval_C]; rw [TensorProduct.algebraMap_apply]; rw [algebraMap_eq_smul_one]; rw [smul_tmul]; rw [algebraMap_eq_smul_one]
      | add p q hp hq => simp [map_add, tmul_add, hp, hq]
      | mul_X p i hp => simp [hp]
    rw [this]; rw [P.aeval_val_σ]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one]
  | add x y ex ey =>
    obtain ⟨a, ha⟩ := ex
    obtain ⟨b, hb⟩ := ey
    use (a + b)
    rw [map_add]; rw [ha]; rw [hb]

set_option backward.defeqAttrib.useBackward true in
variable (T) in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `baseChangeFromBaseChange` / `baseChangeFromBaseChange` 的定义

English:
definition baseChangeFromBaseChange
  signature: :
  body: .ofAlgHom (MvPolynomial.algebraTensorAlgEquiv R T).toAlgHom by
    dsimp [Extension.baseChange]
    ext
    simp [RingHom.algebraMap_toAlgebra]

中文:
定义 baseChangeFromBaseChange
  签名: :
  定义体: .ofAlgHom (MvPolynomial.algebraTensorAlgEquiv R T).toAlgHom by
    dsimp [Extension.baseChange]
    ext
    simp [RingHom.algebraMap_toAlgebra]

Depends on / 依赖: P.baseChange, baseChange, toExtension
-/
noncomputable def baseChangeFromBaseChange :
    (P.toExtension.baseChange (T := T)).Hom (P.baseChange (T := T)).toExtension :=
.ofAlgHom (MvPolynomial.algebraTensorAlgEquiv R T).toAlgHom by
    dsimp [Extension.baseChange]
    ext
    simp [RingHom.algebraMap_toAlgebra]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `baseChangeFromBaseChange_apply` / 引理 `baseChangeFromBaseChange_apply`

English:
lemma baseChangeFromBaseChange_apply
  given: (x : P.toExtension.baseChange.Ring)
  proof: rfl

中文:
引理 baseChangeFromBaseChange_apply
  条件: (x : P.toExtension.baseChange.环)
  证明: rfl
-/
lemma baseChangeFromBaseChange_apply (x : P.toExtension.baseChange.Ring) :
    dsimp% (P.baseChangeFromBaseChange T).toRingHom x = MvPolynomial.algebraTensorAlgEquiv R T x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
variable (T) in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `baseChangeToBaseChange` / `baseChangeToBaseChange` 的定义

English:
definition baseChangeToBaseChange
  signature: :
  body: .ofAlgHom (MvPolynomial.algebraTensorAlgEquiv R T).symm.toAlgHom by
    dsimp [Extension.baseChange]
    ext
    simp [RingHom.algebraMap_toAlgebra]

中文:
定义 baseChangeToBaseChange
  签名: :
  定义体: .ofAlgHom (MvPolynomial.algebraTensorAlgEquiv R T).symm.toAlgHom by
    dsimp [Extension.baseChange]
    ext
    simp [RingHom.algebraMap_toAlgebra]

Depends on / 依赖: P.toExtension.baseChange, baseChange, toExtension, toExtension.Hom
-/
noncomputable def baseChangeToBaseChange :
    (P.baseChange (T := T)).toExtension.Hom (P.toExtension.baseChange (T := T)) :=
.ofAlgHom (MvPolynomial.algebraTensorAlgEquiv R T).symm.toAlgHom by
    dsimp [Extension.baseChange]
    ext
    simp [RingHom.algebraMap_toAlgebra]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `baseChangeToBaseChange_apply` / 引理 `baseChangeToBaseChange_apply`

English:
lemma baseChangeToBaseChange_apply
  given: (x : (baseChange T P).toExtension.Ring)
  proof: rfl

中文:
引理 baseChangeToBaseChange_apply
  条件: (x : (baseChange T P).toExtension.环)
  证明: rfl
-/
lemma baseChangeToBaseChange_apply (x : (baseChange T P).toExtension.Ring) :
    dsimp% (P.baseChangeToBaseChange T).toRingHom x =
      (MvPolynomial.algebraTensorAlgEquiv R T).symm x :=
  rfl

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (P : Generators R S ι) (b : ι' -> S)
  body: .ofSurjective (Sum.elim P.val b) fun s => by
    use rename Sum.inl (P.σ s)
    simp [aeval_rename]

@[simp]

中文:
定义 extend
  签名: (P : 生成元 R S ι) (b : ι' -> S)
  定义体: .ofSurjective (Sum.elim P.val b) fun s => by
    use rename Sum.inl (P.σ s)
    simp [aeval_rename]

@[simp]

Depends on / 依赖: P.val, Sum.elim, Sum.inl, aeval_rename, ofSurjective
-/
noncomputable def extend (P : Generators R S ι) (b : ι' -> S) : Generators R S (ι oplus ι') :=
  .ofSurjective (Sum.elim P.val b) fun s => by
    use rename Sum.inl (P.σ s)
    simp [aeval_rename]

@[simp]
/--
lemma `extend_val_inl` / 引理 `extend_val_inl`

English:
lemma extend_val_inl
  given: (P : Generators R S ι) (b : ι' -> S) (i : ι)
  proof: rfl

@[simp]

中文:
引理 extend_val_inl
  条件: (P : 生成元 R S ι) (b : ι' -> S) (i : ι)
  证明: rfl

@[simp]
-/
lemma extend_val_inl (P : Generators R S ι) (b : ι' -> S) (i : ι) :
    (P.extend b).val (.inl i) = P.val i := rfl

@[simp]
/--
lemma `extend_val_inr` / 引理 `extend_val_inr`

English:
lemma extend_val_inr
  given: (P : Generators R S ι) (b : ι' -> S) (i : ι')
  proof: rfl

中文:
引理 extend_val_inr
  条件: (P : 生成元 R S ι) (b : ι' -> S) (i : ι')
  证明: rfl
-/
lemma extend_val_inr (P : Generators R S ι) (b : ι' -> S) (i : ι') :
    (P.extend b).val (.inr i) = b i := rfl

/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (P : Generators R S ι') (e : ι ≃ ι')
  body: P.val ∘ e
  σ' := rename e.symm ∘ P.σ
  aeval_val_σ' s := by
    conv_rhs => rw [← P.aeval_val_σ s]
    rw [← MvPolynomial.aeval_rename]
    simp

中文:
定义 reindex
  签名: (P : 生成元 R S ι') (e : ι ≃ ι')
  定义体: P.val ∘ e
  σ' := rename e.symm ∘ P.σ
  aeval_val_σ' s := by
    conv_rhs => rw [← P.aeval_val_σ s]
    rw [← MvPolynomial.aeval_rename]
    simp

Depends on / 依赖: P.val
-/
noncomputable def reindex (P : Generators R S ι') (e : ι ≃ ι') :
    Generators R S ι where
  val := P.val ∘ e
  σ' := rename e.symm ∘ P.σ
  aeval_val_σ' s := by
    conv_rhs => rw [← P.aeval_val_σ s]
    rw [← MvPolynomial.aeval_rename]
    simp

/--
lemma `reindex_val` / 引理 `reindex_val`

English:
lemma reindex_val
  given: (P : Generators R S ι') (e : ι ≃ ι')
  proof: rfl

中文:
引理 reindex_val
  条件: (P : 生成元 R S ι') (e : ι ≃ ι')
  证明: rfl
-/
lemma reindex_val (P : Generators R S ι') (e : ι ≃ ι') :
    (P.reindex e).val = P.val ∘ e :=
  rfl

section

variable {σ : Type*} {I : Ideal (MvPolynomial σ R)}
  (s : MvPolynomial σ R ⧸ I -> MvPolynomial σ R)
  (hs : forall x, Ideal.Quotient.mk _ (s x) = x)

/--
The naive generators for a quotient `R[Xᵢ] ⧸ I`.
If the definitional equality of the section matters, it can be explicitly provided.
-/
@[simps val]
noncomputable
/--
Definition of `naive` / `naive` 的定义

English:
definition naive
  signature: (s : MvPolynomial σ R ⧸ I -> MvPolynomial σ R :=
  body: Ideal.Quotient.mk _ (X i)
  σ' := s
  aeval_val_σ' x := by
    conv_rhs => rw [← hs x, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_unique (Ideal.Quotient.mkₐ _ I)]
    simp [Function.comp_def]
  algebra := inferInstance
  algebraMap_eq := by ext x <;> simp [IsScalarTower.algebraMap_apply R (MvPolynomial σ R)]

中文:
定义 naive
  签名: (s : 多元多项式 σ R ⧸ I -> 多元多项式 σ R :=
  定义体: Ideal.Quotient.mk _ (X i)
  σ' := s
  aeval_val_σ' x := by
    conv_rhs => rw [← hs x, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_unique (Ideal.Quotient.mkₐ _ I)]
    simp [Function.comp_def]
  algebra := inferInstance
  algebraMap_eq := by ext x <;> simp [IsScalarTower.algebraMap_apply R (MvPolynomial σ R)]

Depends on / 依赖: Function, Function.comp_def, Function.surjInv, Function.surjInv_eq, Generators, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, IsScalarTower, IsScalarTower.algebraMap_apply, MvPolynomial, Quotient, aeval_unique, algebra, algebraMap_apply, algebraMap_eq, comp_def, conv_rhs, mk_surjective, surjInv, surjInv_eq
-/
def naive (s : MvPolynomial σ R ⧸ I -> MvPolynomial σ R :=
      Function.surjInv Ideal.Quotient.mk_surjective)
    (hs : forall x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq) :
    Generators R (MvPolynomial σ R ⧸ I) σ where
  val i := Ideal.Quotient.mk _ (X i)
  σ' := s
  aeval_val_σ' x := by
    conv_rhs => rw [← hs x, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_unique (Ideal.Quotient.mkₐ _ I)]
    simp [Function.comp_def]
  algebra := inferInstance
  algebraMap_eq := by ext x <;> simp [IsScalarTower.algebraMap_apply R (MvPolynomial σ R)]

/--
lemma `naive_σ` / 引理 `naive_σ`

English:
lemma naive_σ
  statement: (Generators.naive s hs).σ = s
  proof: rfl

中文:
引理 naive_σ
  结论: (生成元.naive s hs).σ = s
  证明: rfl
-/
@[simp] lemma naive_σ : (Generators.naive s hs).σ = s := rfl

end

/--
lemma `finiteType` / 引理 `finiteType`

English:
lemma finiteType
  given: {α : Type*} [Finite α] (P : Generators R S α)
  statement: FiniteType R S
  proof: .of_surjective (IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective

中文:
引理 finiteType
  条件: {α : 类型} [有限 α] (P : 生成元 R S α)
  结论: 有限型 R S
  证明: .of_surjective (IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, P.Ring, P.algebraMap_surjective, algebraMap_surjective, of_surjective, toAlgHom
-/
lemma finiteType {α : Type*} [Finite α] (P : Generators R S α) : FiniteType R S :=
  .of_surjective (IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective

/--
lemma `_root_.Algebra.FiniteType.iff_exists_generators` / 引理 `_root_.Algebra.FiniteType.iff_exists_generators`

English:
lemma _root_.Algebra.FiniteType.iff_exists_generators
  proof: by
  refine ⟨fun h => ?_, fun ⟨n, ⟨P⟩⟩ => P.finiteType⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
exact ⟨n, ⟨.ofSurjective (fun i => f (X i)) by rwa [aeval_unique f] at hf⟩⟩

中文:
引理 _root_.代数.有限型.iff_存在_generators
  证明: by
  refine ⟨fun h => ?_, fun ⟨n, ⟨P⟩⟩ => P.finiteType⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
exact ⟨n, ⟨.ofSurjective (fun i => f (X i)) by rwa [aeval_unique f] at hf⟩⟩

Depends on / 依赖: Algebra, Algebra.FiniteType.iff_quotient_mvPolynomial, FiniteType, P.finiteType, aeval_unique, finiteType, iff_quotient_mvPolynomial, ofSurjective
-/
lemma _root_.Algebra.FiniteType.iff_exists_generators :
    FiniteType R S ↔ exists (n : Nat), Nonempty (Generators R S (Fin n)) := by
  refine ⟨fun h => ?_, fun ⟨n, ⟨P⟩⟩ => P.finiteType⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
exact ⟨n, ⟨.ofSurjective (fun i => f (X i)) by rwa [aeval_unique f] at hf⟩⟩

end Construction

variable {R' S' ι' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S'] (P' : Generators R' S' ι')
variable {R'' S'' ι'' : Type*} [CommRing R''] [CommRing S''] [Algebra R'' S'']
  (P'' : Generators R'' S'' ι'')

section Hom

section

variable [Algebra R R'] [Algebra R' R''] [Algebra R' S'']
variable [Algebra S S'] [Algebra S' S''] [Algebra S S'']

/-- Given a commuting square
R --→ P = R[X] ---→ S
| |
↓ ↓
R' -→ P' = R'[X'] → S
A hom between `P` and `P'` is an assignment `I → P'` such that the arrows commute.
Also see `Algebra.Generators.Hom.equivAlgHom`.
-/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: where
  axioms and operations (2):
    - val : ι -> P'.Ring
    - aeval_val : forall i, aeval P'.val (val i) = algebraMap S S' (P.val i)

中文:
结构 态射
  参数: where
  公理与运算 (2 个):
    - val : ι -> P'.环
    - aeval_val : 对任意 i, aeval P'.val (val i) = algebraMap S S' (P.val i)
-/
structure Hom where
  /-- The assignment of each variable in `I` to a value in `P' = R'[X']`. -/
  val : ι -> P'.Ring
  aeval_val : forall i, aeval P'.val (val i) = algebraMap S S' (P.val i)

attribute [simp] Hom.aeval_val

variable {P P'}

/-- A hom between two families of generators gives
an algebra homomorphism between the polynomial rings. -/
noncomputable
/--
Definition of `Hom.toAlgHom` / `Hom.toAlgHom` 的定义

English:
definition Hom.toAlgHom
  signature: (f : Hom P P')
  body: MvPolynomial.aeval f.val

中文:
定义 态射.toAlgHom
  签名: (f : 态射 P P')
  定义体: MvPolynomial.aeval f.val
-/
def Hom.toAlgHom (f : Hom P P') : P.Ring ->ₐ[R] P'.Ring := MvPolynomial.aeval f.val

variable [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] in
@[simp]
/--
lemma `Hom.algebraMap_toAlgHom` / 引理 `Hom.algebraMap_toAlgHom`

English:
lemma Hom.algebraMap_toAlgHom
  given: (f : Hom P P') (x)
  statement: MvPolynomial.aeval P'.val (f.toAlgHom x) =
  proof: by
  suffices ((MvPolynomial.aeval P'.val).restrictScalars R).comp f.toAlgHom =
      (IsScalarTower.toAlgHom R S S').comp (MvPolynomial.aeval P.val) from
    DFunLike.congr_fun this x
  apply MvPolynomial.algHom_ext
  intro i
  simp [Hom.toAlgHom]

中文:
引理 态射.algebraMap_toAlgHom
  条件: (f : 态射 P P') (x)
  结论: 多元多项式.aeval P'.val (f.toAlgHom x) =
  证明: by
  suffices ((MvPolynomial.aeval P'.val).restrictScalars R).comp f.toAlgHom =
      (IsScalarTower.toAlgHom R S S').comp (MvPolynomial.aeval P.val) from
    DFunLike.congr_fun this x
  apply MvPolynomial.algHom_ext
  intro i
  simp [Hom.toAlgHom]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Hom.toAlgHom, IsScalarTower, IsScalarTower.toAlgHom, MvPolynomial, MvPolynomial.aeval, MvPolynomial.algHom_ext, P.val, algHom_ext, congr_fun, f.toAlgHom, restrictScalars, toAlgHom
-/
lemma Hom.algebraMap_toAlgHom (f : Hom P P') (x) : MvPolynomial.aeval P'.val (f.toAlgHom x) =
    algebraMap S S' (MvPolynomial.aeval P.val x) := by
  suffices ((MvPolynomial.aeval P'.val).restrictScalars R).comp f.toAlgHom =
      (IsScalarTower.toAlgHom R S S').comp (MvPolynomial.aeval P.val) from
    DFunLike.congr_fun this x
  apply MvPolynomial.algHom_ext
  intro i
  simp [Hom.toAlgHom]

/--
lemma `Hom.algebraMap_toAlgHom'` / 引理 `Hom.algebraMap_toAlgHom'`

English:
lemma Hom.algebraMap_toAlgHom'
  statement: [Algebra R' S] [IsScalarTower R R' S]
  proof: f.algebraMap_toAlgHom _

@[simp]

中文:
引理 态射.algebraMap_toAlgHom'
  结论: [代数 R' S] [标量塔 R R' S]
  证明: f.algebraMap_toAlgHom _

@[simp]

Depends on / 依赖: algebraMap_toAlgHom, f.algebraMap_toAlgHom
-/
lemma Hom.algebraMap_toAlgHom' [Algebra R' S] [IsScalarTower R R' S]
    {P' : Generators R' S ι'} (f : Hom P P') (x : P.Ring) :
    MvPolynomial.aeval P'.val (f.toAlgHom x) = MvPolynomial.aeval P.val x :=
  f.algebraMap_toAlgHom _

@[simp]
/--
lemma `Hom.toAlgHom_X` / 引理 `Hom.toAlgHom_X`

English:
lemma Hom.toAlgHom_X
  given: (f : Hom P P') (i)
  statement: f.toAlgHom (.X i) = f.val i
  proof: MvPolynomial.aeval_X f.val i

中文:
引理 态射.toAlgHom_X
  条件: (f : 态射 P P') (i)
  结论: f.toAlgHom (.X i) = f.val i
  证明: MvPolynomial.aeval_X f.val i

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval_X, aeval_X, f.val
-/
lemma Hom.toAlgHom_X (f : Hom P P') (i) : f.toAlgHom (.X i) = f.val i :=
  MvPolynomial.aeval_X f.val i

/--
lemma `Hom.toAlgHom_C` / 引理 `Hom.toAlgHom_C`

English:
lemma Hom.toAlgHom_C
  given: (f : Hom P P') (r)
  statement: f.toAlgHom (.C r) = .C (algebraMap _ _ r)
  proof: MvPolynomial.aeval_C f.val r

中文:
引理 态射.toAlgHom_C
  条件: (f : 态射 P P') (r)
  结论: f.toAlgHom (.C r) = .C (algebraMap _ _ r)
  证明: MvPolynomial.aeval_C f.val r

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval_C, aeval_C, f.val
-/
lemma Hom.toAlgHom_C (f : Hom P P') (r) : f.toAlgHom (.C r) = .C (algebraMap _ _ r) :=
  MvPolynomial.aeval_C f.val r

/--
lemma `Hom.toAlgHom_monomial` / 引理 `Hom.toAlgHom_monomial`

English:
lemma Hom.toAlgHom_monomial
  given: (f : Generators.Hom P P') (v r)
  proof: by
  rw [toAlgHom]; rw [aeval_monomial]; rw [Algebra.smul_def]

中文:
引理 态射.toAlgHom_monomial
  条件: (f : 生成元.态射 P P') (v r)
  证明: by
  rw [toAlgHom]; rw [aeval_monomial]; rw [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, aeval_monomial, smul_def, toAlgHom
-/
lemma Hom.toAlgHom_monomial (f : Generators.Hom P P') (v r) :
    f.toAlgHom (monomial v r) = r • v.prod (f.val · ^ ·) := by
  rw [toAlgHom]; rw [aeval_monomial]; rw [Algebra.smul_def]

variable [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] in
/-- Giving a hom between two families of generators is equivalent to
giving an algebra homomorphism between the polynomial rings. -/
@[simps]
noncomputable
/--
Definition of `Hom.equivAlgHom` / `Hom.equivAlgHom` 的定义

English:
definition Hom.equivAlgHom
  signature: :
  body: ⟨f.toAlgHom, f.algebraMap_toAlgHom⟩
  invFun f := ⟨fun i => f.1 (.X i), fun i => by simp [f.2]⟩
  left_inv f := by ext; simp
  right_inv f := by ext; simp

中文:
定义 态射.equivAlgHom
  签名: :
  定义体: ⟨f.toAlgHom, f.algebraMap_toAlgHom⟩
  invFun f := ⟨fun i => f.1 (.X i), fun i => by simp [f.2]⟩
  left_inv f := by ext; simp
  right_inv f := by ext; simp

Depends on / 依赖: algebraMap_toAlgHom, f.algebraMap_toAlgHom, f.toAlgHom, toAlgHom
-/
def Hom.equivAlgHom :
    Hom P P' ≃ { f : P.Ring ->ₐ[R] P'.Ring //
      forall x, aeval P'.val (f x) = algebraMap S S' (aeval P.val x) } where
  toFun f := ⟨f.toAlgHom, f.algebraMap_toAlgHom⟩
  invFun f := ⟨fun i => f.1 (.X i), fun i => by simp [f.2]⟩
  left_inv f := by ext; simp
  right_inv f := by ext; simp

variable (P P')

/-- The hom from `P` to `P'` given by the designated section of `P'`. -/
@[simps]
/--
Definition of `defaultHom` / `defaultHom` 的定义

English:
definition defaultHom
  signature: : Hom P P'
  body: ⟨P'.σ ∘ algebraMap S S' ∘ P.val, fun x => by simp⟩

中文:
定义 defaultHom
  签名: : 态射 P P'
  定义体: ⟨P'.σ ∘ algebraMap S S' ∘ P.val, fun x => by simp⟩

Depends on / 依赖: P.val, algebraMap
-/
def defaultHom : Hom P P' := ⟨P'.σ ∘ algebraMap S S' ∘ P.val, fun x => by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Hom P P')
  body: ⟨defaultHom P P'⟩

中文:
实例 :
  签名: 可居 (态射 P P')
  定义体: ⟨defaultHom P P'⟩

Depends on / 依赖: defaultHom
-/
instance : Inhabited (Hom P P') := ⟨defaultHom P P'⟩

/-- The identity hom. -/
@[simps]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Hom.id
  body: ⟨X, by simp⟩

@[simp]

中文:
定义 noncomputable
  签名: def 态射.id
  定义体: ⟨X, by simp⟩

@[simp]
-/
protected noncomputable def Hom.id : Hom P P := ⟨X, by simp⟩

@[simp]
/--
lemma `Hom.toAlgHom_id` / 引理 `Hom.toAlgHom_id`

English:
lemma Hom.toAlgHom_id
  statement: Hom.toAlgHom (.id P) = AlgHom.id _ _
  proof: by ext1; simp

中文:
引理 态射.toAlgHom_id
  结论: 态射.toAlgHom (.id P) = 代数态射.id _ _
  证明: by ext1; simp
-/
lemma Hom.toAlgHom_id : Hom.toAlgHom (.id P) = AlgHom.id _ _ := by ext1; simp

variable {P P' P''}

/-- The composition of two homs. -/
@[simps]
/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
  body: aeval f.val (g.val x)
  aeval_val x := by
    rw [IsScalarTower.algebraMap_apply S S' S'']; rw [← g.aeval_val]
    induction g.val x using MvPolynomial.induction_on with
    | C r => simp [← IsScalarTower.algebraMap_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
    | mul_X p i hp => simp only [map_mul, hp, aeval_X, aeval_val]

@[simp]

中文:
定义 态射.comp
  签名: [标量塔 R' R'' S''] [标量塔 R' S' S'']
  定义体: aeval f.val (g.val x)
  aeval_val x := by
    rw [IsScalarTower.algebraMap_apply S S' S'']; rw [← g.aeval_val]
    induction g.val x using MvPolynomial.induction_on with
    | C r => simp [← IsScalarTower.algebraMap_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
    | mul_X p i hp => simp only [map_mul, hp, aeval_X, aeval_val]

@[simp]
-/
noncomputable def Hom.comp [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
    [IsScalarTower S S' S''] (f : Hom P' P'') (g : Hom P P') : Hom P P'' where
  val x := aeval f.val (g.val x)
  aeval_val x := by
    rw [IsScalarTower.algebraMap_apply S S' S'']; rw [← g.aeval_val]
    induction g.val x using MvPolynomial.induction_on with
    | C r => simp [← IsScalarTower.algebraMap_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
    | mul_X p i hp => simp only [map_mul, hp, aeval_X, aeval_val]

@[simp]
/--
lemma `Hom.comp_id` / 引理 `Hom.comp_id`

English:
lemma Hom.comp_id
  given: [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] (f : Hom P P')
  proof: by ext; simp

中文:
引理 态射.comp_id
  条件: [代数 R S'] [标量塔 R R' S'] [标量塔 R S S'] (f : 态射 P P')
  证明: by ext; simp
-/
lemma Hom.comp_id [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] (f : Hom P P') :
    f.comp (Hom.id P) = f := by ext; simp

end

@[simp]
/--
lemma `Hom.id_comp` / 引理 `Hom.id_comp`

English:
lemma Hom.id_comp
  given: [Algebra S S'] (f : Hom P P')
  statement: (Hom.id P').comp f = f
  proof: by
  ext; simp [Hom.id, aeval_X_left]

中文:
引理 态射.id_comp
  条件: [代数 S S'] (f : 态射 P P')
  结论: (态射.id P').comp f = f
  证明: by
  ext; simp [Hom.id, aeval_X_left]
-/
lemma Hom.id_comp [Algebra S S'] (f : Hom P P') : (Hom.id P').comp f = f := by
  ext; simp [Hom.id, aeval_X_left]

variable [Algebra R R'] [Algebra R' R''] [Algebra R' S'']
variable [Algebra S S'] [Algebra S' S''] [Algebra S S'']

@[simp]
/--
lemma `Hom.toAlgHom_comp_apply` / 引理 `Hom.toAlgHom_comp_apply`

English:
lemma Hom.toAlgHom_comp_apply
  proof: by
  induction x using MvPolynomial.induction_on with
  | C r => simp only [← MvPolynomial.algebraMap_eq, AlgHom.map_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul_X p i hp => simp only [map_mul, hp, toAlgHom_X, comp_val]; rfl

中文:
引理 态射.toAlgHom_comp_apply
  证明: by
  induction x using MvPolynomial.induction_on with
  | C r => simp only [← MvPolynomial.algebraMap_eq, AlgHom.map_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul_X p i hp => simp only [map_mul, hp, toAlgHom_X, comp_val]; rfl

Depends on / 依赖: AlgHom, AlgHom.map_algebraMap, MvPolynomial, MvPolynomial.algebraMap_eq, MvPolynomial.induction_on, algebraMap_eq, comp_val, induction_on, map_add, map_algebraMap, map_mul, mul_X, toAlgHom_X
-/
lemma Hom.toAlgHom_comp_apply
    [Algebra R R''] [IsScalarTower R R' R''] [IsScalarTower R' R'' S'']
    [IsScalarTower R' S' S''] [IsScalarTower S S' S'']
    (f : Hom P P') (g : Hom P' P'') (x) :
    (g.comp f).toAlgHom x = g.toAlgHom (f.toAlgHom x) := by
  induction x using MvPolynomial.induction_on with
  | C r => simp only [← MvPolynomial.algebraMap_eq, AlgHom.map_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul_X p i hp => simp only [map_mul, hp, toAlgHom_X, comp_val]; rfl

variable {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Given families of generators `X ⊆ T` over `S` and `Y ⊆ S` over `R`,
there is a map of generators `R[Y] → R[X, Y]`. -/
@[simps]
noncomputable
/--
Definition of `toComp` / `toComp` 的定义

English:
definition toComp
  signature: (Q : Generators S T ι') (P : Generators R S ι)
  body: X (.inr i)
  aeval_val i := by simp

中文:
定义 toComp
  签名: (Q : 生成元 S T ι') (P : 生成元 R S ι)
  定义体: X (.inr i)
  aeval_val i := by simp
-/
def toComp (Q : Generators S T ι') (P : Generators R S ι) : Hom P (Q.comp P) where
  val i := X (.inr i)
  aeval_val i := by simp

/--
lemma `toComp_toAlgHom` / 引理 `toComp_toAlgHom`

English:
lemma toComp_toAlgHom
  given: (Q : Generators S T ι') (P : Generators R S ι)
  proof: by rw [rename_eq_aeval]; rfl

中文:
引理 toComp_toAlgHom
  条件: (Q : 生成元 S T ι') (P : 生成元 R S ι)
  证明: by rw [rename_eq_aeval]; rfl

Depends on / 依赖: rename_eq_aeval
-/
lemma toComp_toAlgHom (Q : Generators S T ι') (P : Generators R S ι) :
    (Q.toComp P).toAlgHom = rename Sum.inr := by rw [rename_eq_aeval]; rfl

/-- Given families of generators `X ⊆ T` over `S` and `Y ⊆ S` over `R`,
there is a map of generators `R[X, Y] → S[X]`. -/
@[simps]
noncomputable
/--
Definition of `ofComp` / `ofComp` 的定义

English:
definition ofComp
  signature: (Q : Generators S T ι') (P : Generators R S ι)
  body: i.elim X (C ∘ P.val)
  aeval_val i := by cases i <;> simp

中文:
定义 ofComp
  签名: (Q : 生成元 S T ι') (P : 生成元 R S ι)
  定义体: i.elim X (C ∘ P.val)
  aeval_val i := by cases i <;> simp

Depends on / 依赖: P.val, i.elim
-/
def ofComp (Q : Generators S T ι') (P : Generators R S ι) : Hom (Q.comp P) Q where
  val i := i.elim X (C ∘ P.val)
  aeval_val i := by cases i <;> simp

/--
lemma `ofComp_toAlgHom_monomial_sumElim` / 引理 `ofComp_toAlgHom_monomial_sumElim`

English:
lemma ofComp_toAlgHom_monomial_sumElim
  given: (Q : Generators S T ι') (P : Generators R S ι) (v₁ v₂ a)
  proof: by
  rw [Hom.toAlgHom_monomial]; rw [monomial_eq]
  simp only [ofComp_val, aeval_monomial]
  rw [Finsupp.prod_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, ← map_pow, ← map_finsuppProd,
    C_mul, Algebra.smul_def, MvPolynomial.algebraMap_apply, mul_assoc]
  nth_rw 2 [mul_comm]

中文:
引理 ofComp_toAlgHom_monomial_sumElim
  条件: (Q : 生成元 S T ι') (P : 生成元 R S ι) (v₁ v₂ a)
  证明: by
  rw [Hom.toAlgHom_monomial]; rw [monomial_eq]
  simp only [ofComp_val, aeval_monomial]
  rw [Finsupp.prod_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, ← map_pow, ← map_finsuppProd,
    C_mul, Algebra.smul_def, MvPolynomial.algebraMap_apply, mul_assoc]
  nth_rw 2 [mul_comm]

Depends on / 依赖: Algebra, Algebra.smul_def, C_mul, Finsupp, Finsupp.prod_sumElim, Function, Function.comp_def, Hom.toAlgHom_monomial, MvPolynomial, MvPolynomial.algebraMap_apply, Sum.elim_inl, Sum.elim_inr, aeval_monomial, algebraMap_apply, comp_def, elim_inl, elim_inr, map_finsuppProd, map_pow, monomial_eq
-/
lemma ofComp_toAlgHom_monomial_sumElim (Q : Generators S T ι') (P : Generators R S ι) (v₁ v₂ a) :
    (Q.ofComp P).toAlgHom (monomial (Finsupp.sumElim v₁ v₂) a) =
      monomial v₁ (aeval P.val (monomial v₂ a)) := by
  rw [Hom.toAlgHom_monomial]; rw [monomial_eq]
  simp only [ofComp_val, aeval_monomial]
  rw [Finsupp.prod_sumElim]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, ← map_pow, ← map_finsuppProd,
    C_mul, Algebra.smul_def, MvPolynomial.algebraMap_apply, mul_assoc]
  nth_rw 2 [mul_comm]

/--
lemma `toComp_toAlgHom_monomial` / 引理 `toComp_toAlgHom_monomial`

English:
lemma toComp_toAlgHom_monomial
  given: (Q : Generators S T ι') (P : Generators R S ι) (j a)
  proof: by
  convert! rename_monomial _ _ _
  · ext f (i₁ | i₂)
    simp [rename_eq_aeval]
    rfl
  · ext f (i₁ | i₂) <;>
      simp [Finsupp.mapDomain_of_notMem_range, Finsupp.mapDomain_apply Sum.inr_injective]

@[simp]

中文:
引理 toComp_toAlgHom_monomial
  条件: (Q : 生成元 S T ι') (P : 生成元 R S ι) (j a)
  证明: by
  convert! rename_monomial _ _ _
  · ext f (i₁ | i₂)
    simp [rename_eq_aeval]
    rfl
  · ext f (i₁ | i₂) <;>
      simp [Finsupp.mapDomain_of_notMem_range, Finsupp.mapDomain_apply Sum.inr_injective]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_apply, Finsupp.mapDomain_of_notMem_range, Sum.inr_injective, convert, inr_injective, mapDomain_apply, mapDomain_of_notMem_range, rename_eq_aeval, rename_monomial
-/
lemma toComp_toAlgHom_monomial (Q : Generators S T ι') (P : Generators R S ι) (j a) :
    (Q.toComp P).toAlgHom (monomial j a) =
      monomial (Finsupp.sumElim 0 j) a := by
  convert! rename_monomial _ _ _
  · ext f (i₁ | i₂)
    simp [rename_eq_aeval]
    rfl
  · ext f (i₁ | i₂) <;>
      simp [Finsupp.mapDomain_of_notMem_range, Finsupp.mapDomain_apply Sum.inr_injective]

@[simp]
/--
lemma `toAlgHom_ofComp_rename` / 引理 `toAlgHom_ofComp_rename`

English:
lemma toAlgHom_ofComp_rename
  given: (Q : Generators S T ι') (P : Generators R S ι) (p : P.Ring)
  proof: have : (Q.ofComp P).toAlgHom.comp (rename Sum.inr) =
    (IsScalarTower.toAlgHom R S Q.Ring).comp (IsScalarTower.toAlgHom R P.Ring S) := by ext; simp
  DFunLike.congr_fun this p

中文:
引理 toAlgHom_ofComp_rename
  条件: (Q : 生成元 S T ι') (P : 生成元 R S ι) (p : P.环)
  证明: have : (Q.ofComp P).toAlgHom.comp (rename Sum.inr) =
    (IsScalarTower.toAlgHom R S Q.Ring).comp (IsScalarTower.toAlgHom R P.Ring S) := by ext; simp
  DFunLike.congr_fun this p

Depends on / 依赖: DFunLike, DFunLike.congr_fun, IsScalarTower, IsScalarTower.toAlgHom, P.Ring, Q.Ring, Q.ofComp, Sum.inr, congr_fun, ofComp, toAlgHom, toAlgHom.comp
-/
lemma toAlgHom_ofComp_rename (Q : Generators S T ι') (P : Generators R S ι) (p : P.Ring) :
    (Q.ofComp P).toAlgHom ((rename Sum.inr) p) = C (algebraMap _ _ p) :=
  have : (Q.ofComp P).toAlgHom.comp (rename Sum.inr) =
    (IsScalarTower.toAlgHom R S Q.Ring).comp (IsScalarTower.toAlgHom R P.Ring S) := by ext; simp
  DFunLike.congr_fun this p

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toAlgHom_ofComp_surjective` / 引理 `toAlgHom_ofComp_surjective`

English:
lemma toAlgHom_ofComp_surjective
  given: (Q : Generators S T ι') (P : Generators R S ι)
  proof: by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      use MvPolynomial.rename Sum.inr (P.σ a)
      simp only [Hom.toAlgHom, ofComp, Generators.comp, MvPolynomial.aeval_rename,
        Sum.elim_comp_inr]
      simp_rw [Function.comp_def, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.toAlgHom_apply R,
        ← MvPolynomial.comp_aeval]
      simp
  | add p q hp hq =>
      obtain ⟨p, rfl⟩ := hp
      obtain ⟨q, rfl⟩ := hq
      use p + q
      simp
  | mul_X p i hp =>
      obtain ⟨(p : MvPolynomial (ι' oplus ι) R), rfl⟩ := hp
      use p * MvPolynomial.X (R := R) (Sum.inl i)
      simp [Algebra.Generators.ofComp, Algebra.Generators.Hom.toAlgHom]

中文:
引理 toAlgHom_ofComp_surjective
  条件: (Q : 生成元 S T ι') (P : 生成元 R S ι)
  证明: by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      use MvPolynomial.rename Sum.inr (P.σ a)
      simp only [Hom.toAlgHom, ofComp, Generators.comp, MvPolynomial.aeval_rename,
        Sum.elim_comp_inr]
      simp_rw [Function.comp_def, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.toAlgHom_apply R,
        ← MvPolynomial.comp_aeval]
      simp
  | add p q hp hq =>
      obtain ⟨p, rfl⟩ := hp
      obtain ⟨q, rfl⟩ := hq
      use p + q
      simp
  | mul_X p i hp =>
      obtain ⟨(p : MvPolynomial (ι' oplus ι) R), rfl⟩ := hp
      use p * MvPolynomial.X (R := R) (Sum.inl i)
      simp [Algebra.Generators.ofComp, Algebra.Generators.Hom.toAlgHom]

Depends on / 依赖: Function, Function.comp_def, Generators, Generators.comp, Hom.toAlgHom, IsScalarTower, IsScalarTower.toAlgHom_apply, MvPolynomial, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, MvPolynomial.comp_aeval, MvPolynomial.induction_on, MvPolynomial.rename, Sum.elim_comp_inr, Sum.inr, aeval_rename, algebraMap_eq, comp_aeval, comp_def, elim_comp_inr
-/
lemma toAlgHom_ofComp_surjective (Q : Generators S T ι') (P : Generators R S ι) :
    Function.Surjective (Q.ofComp P).toAlgHom := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      use MvPolynomial.rename Sum.inr (P.σ a)
      simp only [Hom.toAlgHom, ofComp, Generators.comp, MvPolynomial.aeval_rename,
        Sum.elim_comp_inr]
      simp_rw [Function.comp_def, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.toAlgHom_apply R,
        ← MvPolynomial.comp_aeval]
      simp
  | add p q hp hq =>
      obtain ⟨p, rfl⟩ := hp
      obtain ⟨q, rfl⟩ := hq
      use p + q
      simp
  | mul_X p i hp =>
      obtain ⟨(p : MvPolynomial (ι' oplus ι) R), rfl⟩ := hp
      use p * MvPolynomial.X (R := R) (Sum.inl i)
      simp [Algebra.Generators.ofComp, Algebra.Generators.Hom.toAlgHom]

/-- Given families of generators `X ⊆ T`, there is a map `R[X] → S[X]`. -/
@[simps]
noncomputable
/--
Definition of `toExtendScalars` / `toExtendScalars` 的定义

English:
definition toExtendScalars
  signature: (P : Generators R T ι)
  body: X
  aeval_val i := by simp

中文:
定义 toExtendScalars
  签名: (P : 生成元 R T ι)
  定义体: X
  aeval_val i := by simp
-/
def toExtendScalars (P : Generators R T ι) : Hom P (P.extendScalars S) where
  val := X
  aeval_val i := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {P P'} in
/-- Reinterpret a hom between generators as a hom between extensions. -/
@[simps]
noncomputable
/--
Definition of `Hom.toExtensionHom` / `Hom.toExtensionHom` 的定义

English:
definition Hom.toExtensionHom
  signature: [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
  body: f.toAlgHom.toRingHom
  toRingHom_algebraMap x := by simp
  algebraMap_toRingHom x := by simp

中文:
定义 态射.toExtensionHom
  签名: [代数 R S'] [标量塔 R R' S'] [标量塔 R S S']
  定义体: f.toAlgHom.toRingHom
  toRingHom_algebraMap x := by simp
  algebraMap_toRingHom x := by simp

Depends on / 依赖: f.toAlgHom.toRingHom, toAlgHom, toRingHom
-/
def Hom.toExtensionHom [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (f : P.Hom P') : P.toExtension.Hom P'.toExtension where
  toRingHom := f.toAlgHom.toRingHom
  toRingHom_algebraMap x := by simp
  algebraMap_toRingHom x := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `Hom.toExtensionHom_id` / 引理 `Hom.toExtensionHom_id`

English:
lemma Hom.toExtensionHom_id
  statement: Hom.toExtensionHom (.id P) = .id _
  proof: by ext; simp

中文:
引理 态射.toExtensionHom_id
  结论: 态射.toExtensionHom (.id P) = .id _
  证明: by ext; simp
-/
lemma Hom.toExtensionHom_id : Hom.toExtensionHom (.id P) = .id _ := by ext; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `Hom.toExtensionHom_comp` / 引理 `Hom.toExtensionHom_comp`

English:
lemma Hom.toExtensionHom_comp
  statement: [Algebra R S'] [IsScalarTower R S S']
  proof: by ext; simp

中文:
引理 态射.toExtensionHom_comp
  结论: [代数 R S'] [标量塔 R S S']
  证明: by ext; simp
-/
lemma Hom.toExtensionHom_comp [Algebra R S'] [IsScalarTower R S S']
    [Algebra R R''] [Algebra R S''] [IsScalarTower R R'' S'']
    [IsScalarTower R S S''] [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
    [IsScalarTower S S' S''] [IsScalarTower R R' R''] [IsScalarTower R R' S']
    (f : P'.Hom P'') (g : P.Hom P') :
    toExtensionHom (f.comp g) = f.toExtensionHom.comp g.toExtensionHom := by ext; simp

/--
lemma `Hom.toExtensionHom_toAlgHom_apply` / 引理 `Hom.toExtensionHom_toAlgHom_apply`

English:
lemma Hom.toExtensionHom_toAlgHom_apply
  statement: [Algebra R S'] [IsScalarTower R R' S']
  proof: rfl

中文:
引理 态射.toExtensionHom_toAlgHom_apply
  结论: [代数 R S'] [标量塔 R R' S']
  证明: rfl
-/
lemma Hom.toExtensionHom_toAlgHom_apply [Algebra R S'] [IsScalarTower R R' S']
    [IsScalarTower R S S'] (f : P.Hom P') (x) :
    f.toExtensionHom.toAlgHom x = f.toAlgHom x := rfl

/--
Definition of `ker` / `ker` 的定义

English:
abbreviation ker
  signature: : Ideal P.Ring
  body: P.toExtension.ker

中文:
缩写 ker
  签名: : 理想 P.环
  定义体: P.toExtension.ker

Depends on / 依赖: P.toExtension.ker, toExtension
-/
noncomputable abbrev ker : Ideal P.Ring := P.toExtension.ker

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ker_eq_ker_aeval_val` / 引理 `ker_eq_ker_aeval_val`

English:
lemma ker_eq_ker_aeval_val
  statement: P.ker = RingHom.ker (aeval P.val)
  proof: by
  simp only [ker, Extension.ker, toExtension_Ring, algebraMap_eq]
  rfl

中文:
引理 ker_eq_ker_aeval_val
  结论: P.ker = 环态射.ker (aeval P.val)
  证明: by
  simp only [ker, Extension.ker, toExtension_Ring, algebraMap_eq]
  rfl

Depends on / 依赖: Extension, Extension.ker, algebraMap_eq, toExtension_Ring
-/
lemma ker_eq_ker_aeval_val : P.ker = RingHom.ker (aeval P.val) := by
  simp only [ker, Extension.ker, toExtension_Ring, algebraMap_eq]
  rfl

/--
lemma `ker_mvPolynomial` / 引理 `ker_mvPolynomial`

English:
lemma ker_mvPolynomial
  statement: (mvPolynomial R ι).ker = ⊥
  proof: by
  simp [ker_eq_ker_aeval_val, SetLike.ext_iff, aeval_X_left]

中文:
引理 ker_mvPolynomial
  结论: (mvPolynomial R ι).ker = ⊥
  证明: by
  simp [ker_eq_ker_aeval_val, SetLike.ext_iff, aeval_X_left]

Depends on / 依赖: SetLike, SetLike.ext_iff, aeval_X_left, ext_iff, ker_eq_ker_aeval_val
-/
lemma ker_mvPolynomial : (mvPolynomial R ι).ker = ⊥ := by
  simp [ker_eq_ker_aeval_val, SetLike.ext_iff, aeval_X_left]

variable {P} in
/--
lemma `aeval_val_eq_zero` / 引理 `aeval_val_eq_zero`

English:
lemma aeval_val_eq_zero
  given: {x} (hx : x in P.ker)
  statement: aeval P.val x = 0
  proof: by rwa [← algebraMap_apply]

中文:
引理 aeval_val_eq_zero
  条件: {x} (hx : x in P.ker)
  结论: aeval P.val x = 0
  证明: by rwa [← algebraMap_apply]

Depends on / 依赖: algebraMap_apply
-/
lemma aeval_val_eq_zero {x} (hx : x in P.ker) : aeval P.val x = 0 := by rwa [← algebraMap_apply]

/--
lemma `ker_naive` / 引理 `ker_naive`

English:
lemma ker_naive
  statement: {σ : Type*} {I : Ideal (MvPolynomial σ R)}
  proof: I.mk_ker

中文:
引理 ker_naive
  结论: {σ : 类型} {I : 理想 (多元多项式 σ R)}
  证明: I.mk_ker

Depends on / 依赖: I.mk_ker, mk_ker
-/
lemma ker_naive {σ : Type*} {I : Ideal (MvPolynomial σ R)}
    (s : MvPolynomial σ R ⧸ I -> MvPolynomial σ R) (hs : forall x, Ideal.Quotient.mk _ (s x) = x) :
    (Generators.naive s hs).ker = I :=
  I.mk_ker

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `ker_ofAlgHom` / 引理 `ker_ofAlgHom`

English:
lemma ker_ofAlgHom
  given: {I : Type*} (f : MvPolynomial I R ->ₐ[R] S) (h : Function.Surjective ⇑f)
  proof: by
  change RingHom.ker _ = _
  congr
  exact MvPolynomial.ringHom_ext (by simp) (by simp [ofAlgHom])

@[simp]

中文:
引理 ker_ofAlgHom
  条件: {I : 类型} (f : 多元多项式 I R ->ₐ[R] S) (h : 函数.满射 ⇑f)
  证明: by
  change RingHom.ker _ = _
  congr
  exact MvPolynomial.ringHom_ext (by simp) (by simp [ofAlgHom])

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.ringHom_ext, RingHom, RingHom.ker, ofAlgHom, ringHom_ext
-/
lemma ker_ofAlgHom {I : Type*} (f : MvPolynomial I R ->ₐ[R] S) (h : Function.Surjective ⇑f) :
    (ofAlgHom f h).ker = RingHom.ker f.toRingHom := by
  change RingHom.ker _ = _
  congr
  exact MvPolynomial.ringHom_ext (by simp) (by simp [ofAlgHom])

@[simp]
/--
lemma `ker_ofAlgEquiv` / 引理 `ker_ofAlgEquiv`

English:
lemma ker_ofAlgEquiv
  given: (P : Generators R S ι) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T)
  proof: by
  rw [ker_eq_ker_aeval_val]; rw [ofAlgEquiv_val]; rw [Function.comp_def]; rw [← AlgHom.coe_coe]; rw [← MvPolynomial.comp_aeval]; rw [← AlgHom.comap_ker]; rw [← RingHom.ker_coe_toRingHom]; rw [AlgHomClass.toRingHom_toAlgHom]; rw [AlgHom.ker_coe_equiv]; rw [← RingHom.ker_eq_comap_bot]; rw [← ker_eq_ker_aeval_val]

中文:
引理 ker_ofAlgEquiv
  条件: (P : 生成元 R S ι) {T : 类型} [交换环 T] [代数 R T] (e : S ≃ₐ[R] T)
  证明: by
  rw [ker_eq_ker_aeval_val]; rw [ofAlgEquiv_val]; rw [Function.comp_def]; rw [← AlgHom.coe_coe]; rw [← MvPolynomial.comp_aeval]; rw [← AlgHom.comap_ker]; rw [← RingHom.ker_coe_toRingHom]; rw [AlgHomClass.toRingHom_toAlgHom]; rw [AlgHom.ker_coe_equiv]; rw [← RingHom.ker_eq_comap_bot]; rw [← ker_eq_ker_aeval_val]

Depends on / 依赖: AlgHom, AlgHom.coe_coe, AlgHom.comap_ker, AlgHom.ker_coe_equiv, AlgHomClass, AlgHomClass.toRingHom_toAlgHom, Function, Function.comp_def, MvPolynomial, MvPolynomial.comp_aeval, RingHom, RingHom.ker_coe_toRingHom, RingHom.ker_eq_comap_bot, coe_coe, comap_ker, comp_aeval, comp_def, ker_coe_equiv, ker_coe_toRingHom, ker_eq_comap_bot
-/
lemma ker_ofAlgEquiv (P : Generators R S ι) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    (P.ofAlgEquiv e).ker = P.ker := by
  rw [ker_eq_ker_aeval_val]; rw [ofAlgEquiv_val]; rw [Function.comp_def]; rw [← AlgHom.coe_coe]; rw [← MvPolynomial.comp_aeval]; rw [← AlgHom.comap_ker]; rw [← RingHom.ker_coe_toRingHom]; rw [AlgHomClass.toRingHom_toAlgHom]; rw [AlgHom.ker_coe_equiv]; rw [← RingHom.ker_eq_comap_bot]; rw [← ker_eq_ker_aeval_val]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `map_toComp_ker` / 引理 `map_toComp_ker`

English:
lemma map_toComp_ker
  given: (Q : Generators S T ι') (P : Generators R S ι)
  proof: by
  let : DecidableEq (ι' ->₀ Nat) := Classical.decEq _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro x (hx : algebraMap P.Ring S x = 0)
    have : (Q.ofComp P).toAlgHom.comp (Q.toComp P).toAlgHom = IsScalarTower.toAlgHom R _ _ := by
      ext1; simp
    simp only [Ideal.mem_comap,
      RingHom.mem_ker, ← AlgHom.comp_apply, this, IsScalarTower.toAlgHom_apply]
    rw [IsScalarTower.algebraMap_apply P.Ring S]; rw [hx]; rw [map_zero]
  · rintro x (h₂ : (Q.ofComp P).toAlgHom x = 0)
    let e : (ι' oplus ι ->₀ Nat) ≃+ (ι' ->₀ Nat) × (ι ->₀ Nat) :=
      Finsupp.sumFinsuppAddEquivProdFinsupp
    suffices ∑ v in (support x).map e, (monomial (e.symm v)) (coeff (e.symm v) x) in
        Ideal.map (Q.toComp P).toAlgHom.toRingHom P.ker by
      simpa only [AlgHom.toRingHom_eq_coe, Finset.sum_map, Equiv.coe_toEmbedding,
        EquivLike.coe_coe, AddEquiv.symm_apply_apply, support_sum_monomial_coeff] using! this
    rw [← Finset.sum_fiberwise_of_maps_to (fun i => Finset.mem_image_of_mem Prod.fst)]
    refine sum_mem fun i hi => ?_
    convert_to monomial (e.symm (i, 0)) 1 * (Q.toComp P).toAlgHom.toRingHom
      (∑ j in (support x).map e.toEmbedding with j.1 = i, monomial j.2 (coeff (e.symm j) x)) in _
    · rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain rfl := (Finset.mem_filter.mp hj).2
      obtain ⟨i, j⟩ := j
      clear hj hi
      have : (Q.toComp P).toAlgHom (monomial j (coeff (e.symm (i, j)) x)) =
          monomial (e.symm (0, j)) (coeff (e.symm (i, j)) x) :=
        toComp_toAlgHom_monomial ..
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          this]
      rw [monomial_mul]; rw [← map_add]; rw [Prod.mk_add_mk]; rw [add_zero]; rw [zero_add]; rw [one_mul]
    · apply Ideal.mul_mem_left
      refine Ideal.mem_map_of_mem _ ?_
      simp only [ker_eq_ker_aeval_val, AddEquiv.toEquiv_eq_coe, RingHom.mem_ker, map_sum]
      rw [← coeff_zero i]; rw [← h₂]
      clear h₂ hi
      have (x : (Q.comp P).Ring) : (Function.support fun a => if a.1 = i then aeval P.val
          (monomial a.2 (coeff (e.symm a) x)) else 0) subseteq SetLike.coe ((support x).map e) := by
        rw [← Set.compl_subset_compl]
        intro j
        obtain ⟨j, rfl⟩ := e.surjective j
        simp_all
      rw [Finset.sum_filter]; rw [← finsum_eq_sum_of_support_subset _ (this x)]
      induction x using MvPolynomial.induction_on' with
      | monomial v a =>
        rw [finsum_eq_sum_of_support_subset _ (this _)]; rw [← Finset.sum_filter]
        obtain ⟨v, rfl⟩ := e.symm.surjective v
        -- Rewrite `e` in the right-hand side only.
        conv_rhs => simp only [e, Finsupp.sumFinsuppAddEquivProdFinsupp,
          Finsupp.sumFinsuppEquivProdFinsupp, AddEquiv.symm_mk, AddEquiv.coe_mk,
          Equiv.coe_fn_symm_mk, ofComp_toAlgHom_monomial_sumElim]
        classical
        simp only [coeff_monomial, ← e.injective.eq_iff,
          map_zero, AddEquiv.apply_symm_apply, apply_ite]
        rw [← apply_ite]; rw [Finset.sum_ite_eq]
        simp only [Finset.mem_filter, Finset.mem_map_equiv, AddEquiv.coe_toEquiv_symm,
          mem_support_iff, coeff_monomial, ↓reduceIte, ne_eq, ite_and, ite_not]
        split
        · simp only [*, map_zero, ite_self]
        · congr
      | add p q hp hq =>
        simp only [coeff_add, map_add, ite_add_zero]
        rw [finsum_add_distrib]; rw [hp]; rw [hq]
        · refine (((support p).map e).finite_toSet.subset ?_)
          convert! this p
        · refine (((support q).map e).finite_toSet.subset ?_)
          convert! this q

中文:
引理 map_toComp_ker
  条件: (Q : 生成元 S T ι') (P : 生成元 R S ι)
  证明: by
  let : DecidableEq (ι' ->₀ Nat) := Classical.decEq _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro x (hx : algebraMap P.Ring S x = 0)
    have : (Q.ofComp P).toAlgHom.comp (Q.toComp P).toAlgHom = IsScalarTower.toAlgHom R _ _ := by
      ext1; simp
    simp only [Ideal.mem_comap,
      RingHom.mem_ker, ← AlgHom.comp_apply, this, IsScalarTower.toAlgHom_apply]
    rw [IsScalarTower.algebraMap_apply P.Ring S]; rw [hx]; rw [map_zero]
  · rintro x (h₂ : (Q.ofComp P).toAlgHom x = 0)
    let e : (ι' oplus ι ->₀ Nat) ≃+ (ι' ->₀ Nat) × (ι ->₀ Nat) :=
      Finsupp.sumFinsuppAddEquivProdFinsupp
    suffices ∑ v in (support x).map e, (monomial (e.symm v)) (coeff (e.symm v) x) in
        Ideal.map (Q.toComp P).toAlgHom.toRingHom P.ker by
      simpa only [AlgHom.toRingHom_eq_coe, Finset.sum_map, Equiv.coe_toEmbedding,
        EquivLike.coe_coe, AddEquiv.symm_apply_apply, support_sum_monomial_coeff] using! this
    rw [← Finset.sum_fiberwise_of_maps_to (fun i => Finset.mem_image_of_mem Prod.fst)]
    refine sum_mem fun i hi => ?_
    convert_to monomial (e.symm (i, 0)) 1 * (Q.toComp P).toAlgHom.toRingHom
      (∑ j in (support x).map e.toEmbedding with j.1 = i, monomial j.2 (coeff (e.symm j) x)) in _
    · rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain rfl := (Finset.mem_filter.mp hj).2
      obtain ⟨i, j⟩ := j
      clear hj hi
      have : (Q.toComp P).toAlgHom (monomial j (coeff (e.symm (i, j)) x)) =
          monomial (e.symm (0, j)) (coeff (e.symm (i, j)) x) :=
        toComp_toAlgHom_monomial ..
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          this]
      rw [monomial_mul]; rw [← map_add]; rw [Prod.mk_add_mk]; rw [add_zero]; rw [zero_add]; rw [one_mul]
    · apply Ideal.mul_mem_left
      refine Ideal.mem_map_of_mem _ ?_
      simp only [ker_eq_ker_aeval_val, AddEquiv.toEquiv_eq_coe, RingHom.mem_ker, map_sum]
      rw [← coeff_zero i]; rw [← h₂]
      clear h₂ hi
      have (x : (Q.comp P).Ring) : (Function.support fun a => if a.1 = i then aeval P.val
          (monomial a.2 (coeff (e.symm a) x)) else 0) subseteq SetLike.coe ((support x).map e) := by
        rw [← Set.compl_subset_compl]
        intro j
        obtain ⟨j, rfl⟩ := e.surjective j
        simp_all
      rw [Finset.sum_filter]; rw [← finsum_eq_sum_of_support_subset _ (this x)]
      induction x using MvPolynomial.induction_on' with
      | monomial v a =>
        rw [finsum_eq_sum_of_support_subset _ (this _)]; rw [← Finset.sum_filter]
        obtain ⟨v, rfl⟩ := e.symm.surjective v
        -- Rewrite `e` in the right-hand side only.
        conv_rhs => simp only [e, Finsupp.sumFinsuppAddEquivProdFinsupp,
          Finsupp.sumFinsuppEquivProdFinsupp, AddEquiv.symm_mk, AddEquiv.coe_mk,
          Equiv.coe_fn_symm_mk, ofComp_toAlgHom_monomial_sumElim]
        classical
        simp only [coeff_monomial, ← e.injective.eq_iff,
          map_zero, AddEquiv.apply_symm_apply, apply_ite]
        rw [← apply_ite]; rw [Finset.sum_ite_eq]
        simp only [Finset.mem_filter, Finset.mem_map_equiv, AddEquiv.coe_toEquiv_symm,
          mem_support_iff, coeff_monomial, ↓reduceIte, ne_eq, ite_and, ite_not]
        split
        · simp only [*, map_zero, ite_self]
        · congr
      | add p q hp hq =>
        simp only [coeff_add, map_add, ite_add_zero]
        rw [finsum_add_distrib]; rw [hp]; rw [hq]
        · refine (((support p).map e).finite_toSet.subset ?_)
          convert! this p
        · refine (((support q).map e).finite_toSet.subset ?_)
          convert! this q

Depends on / 依赖: AlgHom, AlgHom.comp_apply, Classical, Classical.decEq, DecidableEq, Ideal.map_le_iff_le_comap, Ideal.mem_comap, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.toAlgHom, IsScalarTower.toAlgHom_apply, P.Ring, Q.ofComp, Q.toComp, RingHom, RingHom.mem_ker, algebraMap, algebraMap_apply, comp_apply, le_antisymm
-/
lemma map_toComp_ker (Q : Generators S T ι') (P : Generators R S ι) :
    P.ker.map (Q.toComp P).toAlgHom = RingHom.ker (Q.ofComp P).toAlgHom := by
  let : DecidableEq (ι' ->₀ Nat) := Classical.decEq _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro x (hx : algebraMap P.Ring S x = 0)
    have : (Q.ofComp P).toAlgHom.comp (Q.toComp P).toAlgHom = IsScalarTower.toAlgHom R _ _ := by
      ext1; simp
    simp only [Ideal.mem_comap,
      RingHom.mem_ker, ← AlgHom.comp_apply, this, IsScalarTower.toAlgHom_apply]
    rw [IsScalarTower.algebraMap_apply P.Ring S]; rw [hx]; rw [map_zero]
  · rintro x (h₂ : (Q.ofComp P).toAlgHom x = 0)
    let e : (ι' oplus ι ->₀ Nat) ≃+ (ι' ->₀ Nat) × (ι ->₀ Nat) :=
      Finsupp.sumFinsuppAddEquivProdFinsupp
    suffices ∑ v in (support x).map e, (monomial (e.symm v)) (coeff (e.symm v) x) in
        Ideal.map (Q.toComp P).toAlgHom.toRingHom P.ker by
      simpa only [AlgHom.toRingHom_eq_coe, Finset.sum_map, Equiv.coe_toEmbedding,
        EquivLike.coe_coe, AddEquiv.symm_apply_apply, support_sum_monomial_coeff] using! this
    rw [← Finset.sum_fiberwise_of_maps_to (fun i => Finset.mem_image_of_mem Prod.fst)]
    refine sum_mem fun i hi => ?_
    convert_to monomial (e.symm (i, 0)) 1 * (Q.toComp P).toAlgHom.toRingHom
      (∑ j in (support x).map e.toEmbedding with j.1 = i, monomial j.2 (coeff (e.symm j) x)) in _
    · rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      obtain rfl := (Finset.mem_filter.mp hj).2
      obtain ⟨i, j⟩ := j
      clear hj hi
      have : (Q.toComp P).toAlgHom (monomial j (coeff (e.symm (i, j)) x)) =
          monomial (e.symm (0, j)) (coeff (e.symm (i, j)) x) :=
        toComp_toAlgHom_monomial ..
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          this]
      rw [monomial_mul]; rw [← map_add]; rw [Prod.mk_add_mk]; rw [add_zero]; rw [zero_add]; rw [one_mul]
    · apply Ideal.mul_mem_left
      refine Ideal.mem_map_of_mem _ ?_
      simp only [ker_eq_ker_aeval_val, AddEquiv.toEquiv_eq_coe, RingHom.mem_ker, map_sum]
      rw [← coeff_zero i]; rw [← h₂]
      clear h₂ hi
      have (x : (Q.comp P).Ring) : (Function.support fun a => if a.1 = i then aeval P.val
          (monomial a.2 (coeff (e.symm a) x)) else 0) subseteq SetLike.coe ((support x).map e) := by
        rw [← Set.compl_subset_compl]
        intro j
        obtain ⟨j, rfl⟩ := e.surjective j
        simp_all
      rw [Finset.sum_filter]; rw [← finsum_eq_sum_of_support_subset _ (this x)]
      induction x using MvPolynomial.induction_on' with
      | monomial v a =>
        rw [finsum_eq_sum_of_support_subset _ (this _)]; rw [← Finset.sum_filter]
        obtain ⟨v, rfl⟩ := e.symm.surjective v
        -- Rewrite `e` in the right-hand side only.
        conv_rhs => simp only [e, Finsupp.sumFinsuppAddEquivProdFinsupp,
          Finsupp.sumFinsuppEquivProdFinsupp, AddEquiv.symm_mk, AddEquiv.coe_mk,
          Equiv.coe_fn_symm_mk, ofComp_toAlgHom_monomial_sumElim]
        classical
        simp only [coeff_monomial, ← e.injective.eq_iff,
          map_zero, AddEquiv.apply_symm_apply, apply_ite]
        rw [← apply_ite]; rw [Finset.sum_ite_eq]
        simp only [Finset.mem_filter, Finset.mem_map_equiv, AddEquiv.coe_toEquiv_symm,
          mem_support_iff, coeff_monomial, ↓reduceIte, ne_eq, ite_and, ite_not]
        split
        · simp only [*, map_zero, ite_self]
        · congr
      | add p q hp hq =>
        simp only [coeff_add, map_add, ite_add_zero]
        rw [finsum_add_distrib]; rw [hp]; rw [hq]
        · refine (((support p).map e).finite_toSet.subset ?_)
          convert! this p
        · refine (((support q).map e).finite_toSet.subset ?_)
          convert! this q

/--
Given `R[X] → S` and `S[Y] → T`, this is the lift of an element in `ker(S[Y] → T)`
to `ker(R[X][Y] → S[Y] → T)` constructed from `P.σ`.
-/
noncomputable
/--
Definition of `kerCompPreimage` / `kerCompPreimage` 的定义

English:
definition kerCompPreimage
  signature: (Q : Generators S T ι') (P : Generators R S ι) (x : Q.ker)
  body: by
  refine ⟨(AddMonoidAlgebra.coeff x.1).sum fun n r => ?_, ?_⟩
  · -- The use of `refine` is intentional to control the elaboration order
    -- so that the term has type `(Q.comp P).Ring` and not `MvPolynomial (Q.ι ⊕ P.ι) R`
    refine rename ?_ (P.σ r) * monomial ?_ 1
    exacts [Sum.inr, n.mapDomain Sum.inl]
  · simp only [ker_eq_ker_aeval_val, RingHom.mem_ker]
    conv_rhs => rw [← aeval_val_eq_zero x.2, ← x.1.support_sum_monomial_coeff]
    simp only [Finsupp.sum, map_sum, map_mul, aeval_rename, Function.comp_def, comp_val,
      Sum.elim_inr, aeval_monomial, map_one, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Sum.elim_inl, one_mul]
    congr! with v i
    simp_rw [← IsScalarTower.toAlgHom_apply R, ← comp_aeval, AlgHom.comp_apply, P.aeval_val_σ,
      coeff]

中文:
定义 kerCompPreimage
  签名: (Q : 生成元 S T ι') (P : 生成元 R S ι) (x : Q.ker)
  定义体: by
  refine ⟨(AddMonoidAlgebra.coeff x.1).sum fun n r => ?_, ?_⟩
  · -- The use of `refine` is intentional to control the elaboration order
    -- so that the term has type `(Q.comp P).Ring` and not `MvPolynomial (Q.ι ⊕ P.ι) R`
    refine rename ?_ (P.σ r) * monomial ?_ 1
    exacts [Sum.inr, n.mapDomain Sum.inl]
  · simp only [ker_eq_ker_aeval_val, RingHom.mem_ker]
    conv_rhs => rw [← aeval_val_eq_zero x.2, ← x.1.support_sum_monomial_coeff]
    simp only [Finsupp.sum, map_sum, map_mul, aeval_rename, Function.comp_def, comp_val,
      Sum.elim_inr, aeval_monomial, map_one, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Sum.elim_inl, one_mul]
    congr! with v i
    simp_rw [← IsScalarTower.toAlgHom_apply R, ← comp_aeval, AlgHom.comp_apply, P.aeval_val_σ,
      coeff]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff, control, elaboration, intentional
-/
def kerCompPreimage (Q : Generators S T ι') (P : Generators R S ι) (x : Q.ker) :
    (Q.comp P).ker := by
  refine ⟨(AddMonoidAlgebra.coeff x.1).sum fun n r => ?_, ?_⟩
  · -- The use of `refine` is intentional to control the elaboration order
    -- so that the term has type `(Q.comp P).Ring` and not `MvPolynomial (Q.ι ⊕ P.ι) R`
    refine rename ?_ (P.σ r) * monomial ?_ 1
    exacts [Sum.inr, n.mapDomain Sum.inl]
  · simp only [ker_eq_ker_aeval_val, RingHom.mem_ker]
    conv_rhs => rw [← aeval_val_eq_zero x.2, ← x.1.support_sum_monomial_coeff]
    simp only [Finsupp.sum, map_sum, map_mul, aeval_rename, Function.comp_def, comp_val,
      Sum.elim_inr, aeval_monomial, map_one, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
      Sum.elim_inl, one_mul]
    congr! with v i
    simp_rw [← IsScalarTower.toAlgHom_apply R, ← comp_aeval, AlgHom.comp_apply, P.aeval_val_σ,
      coeff]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ofComp_kerCompPreimage` / 引理 `ofComp_kerCompPreimage`

English:
lemma ofComp_kerCompPreimage
  given: (Q : Generators S T ι') (P : Generators R S ι) (x : Q.ker)
  proof: by
  conv_rhs => rw [← x.1.support_sum_monomial_coeff]
  rw [kerCompPreimage]; rw [map_finsuppSum]; rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, Hom.toAlgHom_monomial]
  rw [one_smul]; rw [Finsupp.prod_mapDomain_index_inj Sum.inl_injective]
  rw [rename_eq_aeval]; rw [← AlgHom.comp_apply]; rw [comp_aeval]
  simp only [ofComp_val, Sum.elim_inr, Function.comp_apply,
    Sum.elim_inl, monomial_eq, Hom.toAlgHom_X]
  congr 1
  rw [aeval_def]; rw [IsScalarTower.algebraMap_eq R S]; rw [← MvPolynomial.algebraMap_eq]; rw [← coe_eval₂Hom]; rw [← map_aeval]; rw [P.aeval_val_σ]
  simp [coeff]

中文:
引理 ofComp_kerCompPreimage
  条件: (Q : 生成元 S T ι') (P : 生成元 R S ι) (x : Q.ker)
  证明: by
  conv_rhs => rw [← x.1.support_sum_monomial_coeff]
  rw [kerCompPreimage]; rw [map_finsuppSum]; rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, Hom.toAlgHom_monomial]
  rw [one_smul]; rw [Finsupp.prod_mapDomain_index_inj Sum.inl_injective]
  rw [rename_eq_aeval]; rw [← AlgHom.comp_apply]; rw [comp_aeval]
  simp only [ofComp_val, Sum.elim_inr, Function.comp_apply,
    Sum.elim_inl, monomial_eq, Hom.toAlgHom_X]
  congr 1
  rw [aeval_def]; rw [IsScalarTower.algebraMap_eq R S]; rw [← MvPolynomial.algebraMap_eq]; rw [← coe_eval₂Hom]; rw [← map_aeval]; rw [P.aeval_val_σ]
  simp [coeff]

Depends on / 依赖: AlgHom, AlgHom.comp_apply, Finset, Finset.sum_congr, Finsupp, Finsupp.prod_mapDomain_index_inj, Finsupp.sum, Function, Function.comp_apply, Hom.toAlgHom_X, Hom.toAlgHom_monomial, IsScalarTower, IsScalarTower.algebraMap_eq, Sum.elim_inl, Sum.elim_inr, Sum.inl_injective, aeval_def, algebraMap_eq, comp_aeval, comp_apply
-/
lemma ofComp_kerCompPreimage (Q : Generators S T ι') (P : Generators R S ι) (x : Q.ker) :
    (Q.ofComp P).toAlgHom (kerCompPreimage Q P x) = x := by
  conv_rhs => rw [← x.1.support_sum_monomial_coeff]
  rw [kerCompPreimage]; rw [map_finsuppSum]; rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, Hom.toAlgHom_monomial]
  rw [one_smul]; rw [Finsupp.prod_mapDomain_index_inj Sum.inl_injective]
  rw [rename_eq_aeval]; rw [← AlgHom.comp_apply]; rw [comp_aeval]
  simp only [ofComp_val, Sum.elim_inr, Function.comp_apply,
    Sum.elim_inl, monomial_eq, Hom.toAlgHom_X]
  congr 1
  rw [aeval_def]; rw [IsScalarTower.algebraMap_eq R S]; rw [← MvPolynomial.algebraMap_eq]; rw [← coe_eval₂Hom]; rw [← map_aeval]; rw [P.aeval_val_σ]
  simp [coeff]

/--
lemma `map_ofComp_ker` / 引理 `map_ofComp_ker`

English:
lemma map_ofComp_ker
  given: (Q : Generators S T ι') (P : Generators R S ι)
  proof: by
  ext x
  rw [Ideal.mem_map_iff_of_surjective _ (toAlgHom_ofComp_surjective Q P)]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [ker_eq_ker_aeval_val,
      RingHom.mem_ker] at hx ⊢
    rw [← hx]; rw [Hom.algebraMap_toAlgHom]; rw [algebraMap_self_apply]
  · intro hx
    exact ⟨_, (kerCompPreimage Q P ⟨x, hx⟩).2, ofComp_kerCompPreimage Q P ⟨x, hx⟩⟩

中文:
引理 map_ofComp_ker
  条件: (Q : 生成元 S T ι') (P : 生成元 R S ι)
  证明: by
  ext x
  rw [Ideal.mem_map_iff_of_surjective _ (toAlgHom_ofComp_surjective Q P)]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [ker_eq_ker_aeval_val,
      RingHom.mem_ker] at hx ⊢
    rw [← hx]; rw [Hom.algebraMap_toAlgHom]; rw [algebraMap_self_apply]
  · intro hx
    exact ⟨_, (kerCompPreimage Q P ⟨x, hx⟩).2, ofComp_kerCompPreimage Q P ⟨x, hx⟩⟩

Depends on / 依赖: Hom.algebraMap_toAlgHom, Ideal.mem_map_iff_of_surjective, RingHom, RingHom.mem_ker, algebraMap_self_apply, algebraMap_toAlgHom, kerCompPreimage, ker_eq_ker_aeval_val, mem_ker, mem_map_iff_of_surjective, ofComp_kerCompPreimage, toAlgHom_ofComp_surjective
-/
lemma map_ofComp_ker (Q : Generators S T ι') (P : Generators R S ι) :
    Ideal.map (Q.ofComp P).toAlgHom (Q.comp P).ker = Q.ker := by
  ext x
  rw [Ideal.mem_map_iff_of_surjective _ (toAlgHom_ofComp_surjective Q P)]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [ker_eq_ker_aeval_val,
      RingHom.mem_ker] at hx ⊢
    rw [← hx]; rw [Hom.algebraMap_toAlgHom]; rw [algebraMap_self_apply]
  · intro hx
    exact ⟨_, (kerCompPreimage Q P ⟨x, hx⟩).2, ofComp_kerCompPreimage Q P ⟨x, hx⟩⟩

/--
lemma `ker_comp_eq_sup` / 引理 `ker_comp_eq_sup`

English:
lemma ker_comp_eq_sup
  given: (Q : Generators S T ι') (P : Generators R S ι)
  proof: by
  rw [← map_ofComp_ker Q P]; rw [Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective Q P)]
  rw [← sup_assoc]; rw [Algebra.Generators.map_toComp_ker]; rw [← RingHom.ker_eq_comap_bot]
  apply le_antisymm (le_trans le_sup_right le_sup_left)
  simp only [le_sup_left, sup_of_le_left, sup_le_iff, le_refl, and_true]
  intro x hx
  simp only [RingHom.mem_ker] at hx
  rw [Generators.ker_eq_ker_aeval_val]; rw [RingHom.mem_ker]; rw [← algebraMap_self_apply (MvPolynomial.aeval _ x)]
  rw [← Generators.Hom.algebraMap_toAlgHom (Q.ofComp P)]; rw [hx]; rw [map_zero]

中文:
引理 ker_comp_eq_sup
  条件: (Q : 生成元 S T ι') (P : 生成元 R S ι)
  证明: by
  rw [← map_ofComp_ker Q P]; rw [Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective Q P)]
  rw [← sup_assoc]; rw [Algebra.Generators.map_toComp_ker]; rw [← RingHom.ker_eq_comap_bot]
  apply le_antisymm (le_trans le_sup_right le_sup_left)
  simp only [le_sup_left, sup_of_le_left, sup_le_iff, le_refl, and_true]
  intro x hx
  simp only [RingHom.mem_ker] at hx
  rw [Generators.ker_eq_ker_aeval_val]; rw [RingHom.mem_ker]; rw [← algebraMap_self_apply (MvPolynomial.aeval _ x)]
  rw [← Generators.Hom.algebraMap_toAlgHom (Q.ofComp P)]; rw [hx]; rw [map_zero]

Depends on / 依赖: Algebra, Algebra.Generators.map_toComp_ker, Generators, Generators.Hom.algeb, Generators.ker_eq_ker_aeval_val, Ideal.comap_map_of_surjective, MvPolynomial, MvPolynomial.aeval, RingHom, RingHom.ker_eq_comap_bot, RingHom.mem_ker, algebraMap_self_apply, and_true, comap_map_of_surjective, ker_eq_comap_bot, ker_eq_ker_aeval_val, le_antisymm, le_refl, le_sup_left, le_sup_right
-/
lemma ker_comp_eq_sup (Q : Generators S T ι') (P : Generators R S ι) :
    (Q.comp P).ker =
      Ideal.map (Q.toComp P).toAlgHom P.ker ⊔ Ideal.comap (Q.ofComp P).toAlgHom Q.ker := by
  rw [← map_ofComp_ker Q P]; rw [Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective Q P)]
  rw [← sup_assoc]; rw [Algebra.Generators.map_toComp_ker]; rw [← RingHom.ker_eq_comap_bot]
  apply le_antisymm (le_trans le_sup_right le_sup_left)
  simp only [le_sup_left, sup_of_le_left, sup_le_iff, le_refl, and_true]
  intro x hx
  simp only [RingHom.mem_ker] at hx
  rw [Generators.ker_eq_ker_aeval_val]; rw [RingHom.mem_ker]; rw [← algebraMap_self_apply (MvPolynomial.aeval _ x)]
  rw [← Generators.Hom.algebraMap_toAlgHom (Q.ofComp P)]; rw [hx]; rw [map_zero]

/--
lemma `toAlgHom_ofComp_localizationAway` / 引理 `toAlgHom_ofComp_localizationAway`

English:
lemma toAlgHom_ofComp_localizationAway
  given: (g : S) [IsLocalization.Away g T]
  proof: by
  simp [Generators.Hom.toAlgHom, Generators.ofComp, aeval_rename]

中文:
引理 toAlgHom_ofComp_localizationAway
  条件: (g : S) [是Localization.Away g T]
  证明: by
  simp [Generators.Hom.toAlgHom, Generators.ofComp, aeval_rename]

Depends on / 依赖: Generators, Generators.Hom.toAlgHom, Generators.ofComp, aeval_rename, ofComp, toAlgHom
-/
lemma toAlgHom_ofComp_localizationAway (g : S) [IsLocalization.Away g T] :
    ((localizationAway T g).ofComp P).toAlgHom
      (rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1) = C g * X () - 1 := by
  simp [Generators.Hom.toAlgHom, Generators.ofComp, aeval_rename]

end Hom

end Algebra.Generators

namespace Algebra.Extension

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical homomorphism of extensions from the universal extension `R[S] → S`
(given by `Generators.self R S`) to any extension `P` defined via the designated section `P.σ`. -/
@[simps!]
noncomputable
/--
Definition of `defaultHom` / `defaultHom` 的定义

English:
definition defaultHom
  signature: (P : Extension.{w} R S)
  body: .ofAlgHom (MvPolynomial.aeval P.σ) (by dsimp; ext; simp)

中文:
定义 defaultHom
  签名: (P : 扩张.{w} R S)
  定义体: .ofAlgHom (MvPolynomial.aeval P.σ) (by dsimp; ext; simp)

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, ofAlgHom
-/
def defaultHom (P : Extension.{w} R S) : (Generators.self R S).toExtension.Hom P :=
  .ofAlgHom (MvPolynomial.aeval P.σ) (by dsimp; ext; simp)

end Algebra.Extension
