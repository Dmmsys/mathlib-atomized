/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# The bialgebra structure on monoid algebras

Given a monoid `M`, a commutative semiring `R` and an `R`-bialgebra `A`, this file collects results
about the `R`-bialgebra instance on `A[M]` inherited from the corresponding structure on its
coefficients, building upon results in `Mathlib/RingTheory/Coalgebra/MonoidAlgebra.lean` about the
coalgebra structure.

## Main definitions

* `(Add)MonoidAlgebra.instBialgebra`: the `R`-bialgebra structure on `A[M]` when `M` is an (add)
  monoid and `A` is an `R`-bialgebra.
* `LaurentPolynomial.instBialgebra`: the `R`-bialgebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-bialgebra.
* `(Add)MonoidAlgebra.mapDomainBialgHomEquiv`: isomorphism between `R`-bialgebra homs `A[G] → A[H]`
  and groups homs `G → H` when `G` and `H` are an (add) group and `A` is an `R`-bialgebra.
-/

public noncomputable section

open TensorProduct Bialgebra Coalgebra Function WithConv

variable {R S A B G H I M N O : Type*}

namespace MonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

@[to_additive (dont_translate := R A) (attr := simp) isGroupLikeElem_single_one]
/--
lemma `isGroupLikeElem_single_one` / 引理 `isGroupLikeElem_single_one`

English:
lemma isGroupLikeElem_single_one
  given: (g : G)
  statement: IsGroupLikeElem R (single g 1 : A[G]) where
  proof: by simp
  comul_eq_tmul_self := by simp [Algebra.TensorProduct.one_def]

中文:
引理 isGroupLikeElem_single_one
  条件: (g : G)
  结论: 是GroupLikeElem R (single g 1 : A[G]) where
  证明: by simp
  comul_eq_tmul_self := by simp [Algebra.TensorProduct.one_def]

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, TensorProduct, comul_eq_tmul_self, one_def
-/
lemma isGroupLikeElem_single_one (g : G) : IsGroupLikeElem R (single g 1 : A[G]) where
  counit_eq_one := by simp
  comul_eq_tmul_self := by simp [Algebra.TensorProduct.one_def]

/-- A group algebra is spanned by its group-like elements. -/
@[to_additive (dont_translate := R A) (attr := simp) span_isGroupLikeElem]
/--
lemma `span_isGroupLikeElem` / 引理 `span_isGroupLikeElem`

English:
lemma span_isGroupLikeElem
  statement: Submodule.span A {a : A[G] | IsGroupLikeElem R a} = ⊤
  proof: eq_top_mono (Submodule.span_mono <| Set.range_subset_iff.2 isGroupLikeElem_single_one) by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.range_eq_top_of_surjective _ fun x =>
      ⟨x.coeff, by simp [Finsupp.linearCombination_apply]⟩

中文:
引理 span_isGroupLikeElem
  结论: 子模.span A {a : A[G] | 是GroupLikeElem R a} = ⊤
  证明: eq_top_mono (Submodule.span_mono <| Set.range_subset_iff.2 isGroupLikeElem_single_one) by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.range_eq_top_of_surjective _ fun x =>
      ⟨x.coeff, by simp [Finsupp.linearCombination_apply]⟩

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.range_linearCombination, LinearMap, LinearMap.range_eq_top_of_surjective, Set.range_subset_iff, Submodule, Submodule.span_mono, eq_top_mono, isGroupLikeElem_single_one, linearCombination_apply, range_eq_top_of_surjective, range_linearCombination, range_subset_iff, span_mono, x.coeff
-/
lemma span_isGroupLikeElem : Submodule.span A {a : A[G] | IsGroupLikeElem R a} = ⊤ :=
eq_top_mono (Submodule.span_mono <| Set.range_subset_iff.2 isGroupLikeElem_single_one) by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.range_eq_top_of_surjective _ fun x =>
      ⟨x.coeff, by simp [Finsupp.linearCombination_apply]⟩

variable [Monoid M] [Monoid N] [Monoid O]

variable (R A M) in
@[to_additive (dont_translate := R A)]
/--
Instance `instBialgebra` / 实例 `instBialgebra`

English:
instance instBialgebra
  signature: : Bialgebra R A[M] where
  body: by simp only [one_def, counit_single, Bialgebra.counit_one]
  mul_compr₂_counit := by ext; simp
  comul_one := by
    simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, lsingle_apply]
  mul_compr₂_comul := by
    ext a b c d
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.compr₂_apply,
      LinearMap.mul_apply', single_mul_single, comul_single, Bialgebra.comul_mul,
      ← (Coalgebra.Repr.arbitrary R b).eq, ← (Coalgebra.Repr.arbitrary R d).eq, Finset.sum_mul_sum,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, TensorProduct.map_tmul, lsingle_apply,
      LinearMap.compl₁₂_apply, LinearMap.coe_sum, Finset.sum_apply,
      Finset.sum_comm (s := (Coalgebra.Repr.arbitrary R b).index)]

中文:
实例 instBialgebra
  签名: : 双代数 R A[M] where
  定义体: by simp only [one_def, counit_single, Bialgebra.counit_one]
  mul_compr₂_counit := by ext; simp
  comul_one := by
    simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, lsingle_apply]
  mul_compr₂_comul := by
    ext a b c d
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.compr₂_apply,
      LinearMap.mul_apply', single_mul_single, comul_single, Bialgebra.comul_mul,
      ← (Coalgebra.Repr.arbitrary R b).eq, ← (Coalgebra.Repr.arbitrary R d).eq, Finset.sum_mul_sum,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, TensorProduct.map_tmul, lsingle_apply,
      LinearMap.compl₁₂_apply, LinearMap.coe_sum, Finset.sum_apply,
      Finset.sum_comm (s := (Coalgebra.Repr.arbitrary R b).index)]

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, Bialgebra, Bialgebra.comul_mul, Bialgebra.comul_one, Bialgebra.counit_one, Coalgebra, Coalgebra.Repr.arbitrary, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.compr, LinearMap.mul_apply, TensorProduct, TensorProduct.map_tmul, arbitrary, coe_comp, comp_apply, comul_mul
-/
instance instBialgebra : Bialgebra R A[M] where
  counit_one := by simp only [one_def, counit_single, Bialgebra.counit_one]
  mul_compr₂_counit := by ext; simp
  comul_one := by
    simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, lsingle_apply]
  mul_compr₂_comul := by
    ext a b c d
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.compr₂_apply,
      LinearMap.mul_apply', single_mul_single, comul_single, Bialgebra.comul_mul,
      ← (Coalgebra.Repr.arbitrary R b).eq, ← (Coalgebra.Repr.arbitrary R d).eq, Finset.sum_mul_sum,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, TensorProduct.map_tmul, lsingle_apply,
      LinearMap.compl₁₂_apply, LinearMap.coe_sum, Finset.sum_apply,
      Finset.sum_comm (s := (Coalgebra.Repr.arbitrary R b).index)]

-- TODO: Generalise to `A[M] →ₐc[R] A[N]` under `Bialgebra R A`
variable (R) in
/-- If `f : M → N` is a monoid hom, then `MonoidAlgebra.mapDomain f` is a bialgebra hom between
their monoid algebras. -/
@[expose, to_additive (attr := simps!) (dont_translate := R)
/-- If `f : M → N` is an additive monoid hom, then `MonoidAlgebra.mapDomain f` is a bialgebra hom
between their additive monoid algebras. -/]
/--
Definition of `mapDomainBialgHom` / `mapDomainBialgHom` 的定义

English:
definition mapDomainBialgHom
  signature: (f : M ->* N)
  body: .ofAlgHom (mapDomainAlgHom R R f) (by ext; simp) (by ext; simp)

@[to_additive (attr := simp)]

中文:
定义 mapDomainBialgHom
  签名: (f : M ->* N)
  定义体: .ofAlgHom (mapDomainAlgHom R R f) (by ext; simp) (by ext; simp)

@[to_additive (attr := simp)]

Depends on / 依赖: mapDomainAlgHom, ofAlgHom
-/
def mapDomainBialgHom (f : M ->* N) : R[M] ->ₐc[R] R[N] :=
  .ofAlgHom (mapDomainAlgHom R R f) (by ext; simp) (by ext; simp)

@[to_additive (attr := simp)]
/--
lemma `mapDomainBialgHom_id` / 引理 `mapDomainBialgHom_id`

English:
lemma mapDomainBialgHom_id
  statement: mapDomainBialgHom R (.id M) = .id R R[M]
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
引理 mapDomainBialgHom_id
  结论: mapDomainBialgHom R (.id M) = .id R R[M]
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
lemma mapDomainBialgHom_id : mapDomainBialgHom R (.id M) = .id R R[M] := by ext; simp

@[to_additive (attr := simp)]
/--
lemma `mapDomainBialgHom_comp` / 引理 `mapDomainBialgHom_comp`

English:
lemma mapDomainBialgHom_comp
  given: (f : N ->* O) (g : M ->* N)
  proof: by
  ext; simp [Finsupp.mapDomain_comp]

@[to_additive]

中文:
引理 mapDomainBialgHom_comp
  条件: (f : N ->* O) (g : M ->* N)
  证明: by
  ext; simp [Finsupp.mapDomain_comp]

@[to_additive]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_comp, mapDomain_comp
-/
lemma mapDomainBialgHom_comp (f : N ->* O) (g : M ->* N) :
    mapDomainBialgHom R (f.comp g) = (mapDomainBialgHom R f).comp (mapDomainBialgHom R g) := by
  ext; simp [Finsupp.mapDomain_comp]

@[to_additive]
/--
lemma `mapDomainBialgHom_mapDomainBialgHom` / 引理 `mapDomainBialgHom_mapDomainBialgHom`

English:
lemma mapDomainBialgHom_mapDomainBialgHom
  given: (f : N ->* O) (g : M ->* N) (x : R[M])
  proof: by
  ext; simp

@[to_additive (attr := simp)]

中文:
引理 mapDomainBialgHom_mapDomainBialgHom
  条件: (f : N ->* O) (g : M ->* N) (x : R[M])
  证明: by
  ext; simp

@[to_additive (attr := simp)]
-/
lemma mapDomainBialgHom_mapDomainBialgHom (f : N ->* O) (g : M ->* N) (x : R[M]) :
    mapDomainBialgHom R f (mapDomainBialgHom R g x) = mapDomainBialgHom R (f.comp g) x := by
  ext; simp

@[to_additive (attr := simp)]
/--
lemma `mapDomainBialgHom_single` / 引理 `mapDomainBialgHom_single`

English:
lemma mapDomainBialgHom_single
  given: (f : M ->* N) (m : M) (r : R)
  proof: mapDomain_single

中文:
引理 mapDomainBialgHom_single
  条件: (f : M ->* N) (m : M) (r : R)
  证明: mapDomain_single

Depends on / 依赖: mapDomain_single
-/
lemma mapDomainBialgHom_single (f : M ->* N) (m : M) (r : R) :
    mapDomainBialgHom R f (single m r) = single (f m) r := mapDomain_single

/-- A `R`-bialgebra homomorphism from `A[M]` is uniquely defined by its
values on the functions `single m 1` and `single 1 a`.

See note [partially-applied ext lemmas]. Note that the first assumption isn't written as an
equality of `MonoidHom`s because `of` doesn't additivise. -/
@[to_additive (dont_translate := A) (attr := ext high)
/-- A `R`-bialgebra homomorphism from `A[M]` is uniquely defined by its
values on the functions `single m 1` and `single 1 a`.

See note [partially-applied ext lemmas]. Note that the first assumption isn't written as an
equality of `AddMonoidHom`s because `of` doesn't multiplicativise. -/]
/--
lemma `bialgHom_ext` / 引理 `bialgHom_ext`

English:
lemma bialgHom_ext
  given: ⦃φ₁ φ₂
  statement: A[M] ->ₐc[R] B⦄
  proof: BialgHom.coe_toAlgHom_injective algHom_ext single_one_right single_one_left

中文:
引理 bialgHom_ext
  条件: ⦃φ₁ φ₂
  结论: A[M] ->ₐc[R] B⦄
  证明: BialgHom.coe_toAlgHom_injective algHom_ext single_one_right single_one_left

Depends on / 依赖: BialgHom, BialgHom.coe_toAlgHom_injective, algHom_ext, coe_toAlgHom_injective, single_one_left, single_one_right
-/
lemma bialgHom_ext ⦃φ₁ φ₂ : A[M] ->ₐc[R] B⦄
  (single_one_right : forall (m : M), φ₁ (single m 1) = φ₂ (single m 1))
  (single_one_left : (φ₁ : A[M] ->ₐ[R] B).comp singleOneAlgHom =
    (φ₂ : A[M] ->ₐ[R] B).comp singleOneAlgHom) : φ₁ = φ₂ :=
BialgHom.coe_toAlgHom_injective algHom_ext single_one_right single_one_left

/--
lemma `bialgHom_ext'` / 引理 `bialgHom_ext'`

English:
lemma bialgHom_ext'
  given: ⦃φ₁ φ₂
  statement: A[M] ->ₐc[R] B⦄
  proof: BialgHom.coe_toAlgHom_injective algHom_ext' single_one_right single_one_left

@[to_additive (attr := simp)]

中文:
引理 bialgHom_ext'
  条件: ⦃φ₁ φ₂
  结论: A[M] ->ₐc[R] B⦄
  证明: BialgHom.coe_toAlgHom_injective algHom_ext' single_one_right single_one_left

@[to_additive (attr := simp)]

Depends on / 依赖: BialgHom, BialgHom.coe_toAlgHom_injective, algHom_ext, coe_toAlgHom_injective, single_one_left, single_one_right
-/
lemma bialgHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐc[R] B⦄
    (single_one_right : (φ₁ : A[M] ->* B).comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M))
    (single_one_left : (φ₁ : A[M] ->ₐ[R] B).comp singleOneAlgHom =
      (φ₂ : A[M] ->ₐ[R] B).comp singleOneAlgHom) : φ₁ = φ₂ :=
BialgHom.coe_toAlgHom_injective algHom_ext' single_one_right single_one_left

@[to_additive (attr := simp)]
/--
lemma `counit_domCongr` / 引理 `counit_domCongr`

English:
lemma counit_domCongr
  given: (e : M ≃* N) (x : A[M])
  statement: counit (R := R) (domCongr R A e x) = counit x
  proof: by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

中文:
引理 counit_domCongr
  条件: (e : M ≃* N) (x : A[M])
  结论: counit (R := R) (domCongr R A e x) = counit x
  证明: by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.induction_linear, counit, domCongr, induction_linear
-/
lemma counit_domCongr (e : M ≃* N) (x : A[M]) : counit (R := R) (domCongr R A e x) = counit x := by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

variable (R A) in
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[expose, to_additive (attr := simps! -isSimp) (dont_translate := R A)
/-- Isomorphic monoids have isomorphic monoid algebras. -/]
/--
Definition of `domCongrBialgEquiv` / `domCongrBialgEquiv` 的定义

English:
definition domCongrBialgEquiv
  signature: (e : M ≃* N)
  body: .ofAlgEquiv (domCongr R A e) (by ext <;> simp) by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

中文:
定义 domCongrBialgEquiv
  签名: (e : M ≃* N)
  定义体: .ofAlgEquiv (domCongr R A e) (by ext <;> simp) by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

Depends on / 依赖: Coalgebra, Coalgebra.Repr.arbitrary, arbitrary, domCongr, ofAlgEquiv
-/
def domCongrBialgEquiv (e : M ≃* N) : A[M] ≃ₐc[R] A[N] :=
.ofAlgEquiv (domCongr R A e) (by ext <;> simp) by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
@[expose, to_additive (dont_translate := R)
/-- The trivial monoid algebra is isomorphic to the base ring. -/]
/--
Definition of `bialgEquivOfSubsingleton` / `bialgEquivOfSubsingleton` 的定义

English:
definition bialgEquivOfSubsingleton
  signature: [Subsingleton M]
  body: counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    change (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

中文:
定义 bialgEquivOfSubsingleton
  签名: [子单例 M]
  定义体: counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    change (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

Depends on / 依赖: LinearOrder, Subsingleton, WellFoundedLT, counitBialgHom
-/
def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    change (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

/--
lemma `isGroupLikeElem_of` / 引理 `isGroupLikeElem_of`

English:
lemma isGroupLikeElem_of
  given: (m : M)
  statement: IsGroupLikeElem R (of A M m)
  proof: isGroupLikeElem_single_one ..

中文:
引理 isGroupLikeElem_of
  条件: (m : M)
  结论: 是GroupLikeElem R (of A M m)
  证明: isGroupLikeElem_single_one ..

Depends on / 依赖: isGroupLikeElem_single_one
-/
lemma isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m) := isGroupLikeElem_single_one ..

/-- The `R`-bialgebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[expose, simps!]
/--
Definition of `liftGroupLikeBialgHom` / `liftGroupLikeBialgHom` 的定义

English:
definition liftGroupLikeBialgHom
  signature: : R[GroupLike R A] ->ₐc[R] A
  body: .ofAlgHom (lift R A (GroupLike R A) { toFun g := g.1, map_one' := by simp, map_mul' := by simp })
    (by ext; simp) (by ext; simp)

中文:
定义 liftGroupLikeBialgHom
  签名: : R[群状 R A] ->ₐc[R] A
  定义体: .ofAlgHom (lift R A (GroupLike R A) { toFun g := g.1, map_one' := by simp, map_mul' := by simp })
    (by ext; simp) (by ext; simp)

Depends on / 依赖: GroupLike, map_mul, map_one, ofAlgHom
-/
def liftGroupLikeBialgHom : R[GroupLike R A] ->ₐc[R] A :=
  .ofAlgHom (lift R A (GroupLike R A) { toFun g := g.1, map_one' := by simp, map_mul' := by simp })
    (by ext; simp) (by ext; simp)

variable (R A M) in
/-- The bialgebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of
`Additive`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[expose, simps! -isSimp]
/--
Definition of `toAdditiveBialgEquiv` / `toAdditiveBialgEquiv` 的定义

English:
definition toAdditiveBialgEquiv
  signature: : A[M] ≃ₐc[R] AddMonoidAlgebra A (Additive M)
  body: .ofAlgEquiv (toAdditiveAlgEquiv R A M) (by ext <;> simp) by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]

中文:
定义 toAdditiveBialgEquiv
  签名: : A[M] ≃ₐc[R] 加法幺半群代数 A (加性 M)
  定义体: .ofAlgEquiv (toAdditiveAlgEquiv R A M) (by ext <;> simp) by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]

Depends on / 依赖: Coalgebra, Coalgebra.Repr.arbitrary, arbitrary, ofAlgEquiv, toAdditiveAlgEquiv
-/
def toAdditiveBialgEquiv : A[M] ≃ₐc[R] AddMonoidAlgebra A (Additive M) :=
.ofAlgEquiv (toAdditiveAlgEquiv R A M) (by ext <;> simp) by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]
/--
lemma `toAdditiveBialgEquiv_single` / 引理 `toAdditiveBialgEquiv_single`

English:
lemma toAdditiveBialgEquiv_single
  given: (m : M) (a : A)
  proof: by
  simp [toAdditiveBialgEquiv]

中文:
引理 toAdditiveBialgEquiv_single
  条件: (m : M) (a : A)
  证明: by
  simp [toAdditiveBialgEquiv]

Depends on / 依赖: toAdditiveBialgEquiv
-/
lemma toAdditiveBialgEquiv_single (m : M) (a : A) :
    toAdditiveBialgEquiv R A M (single m a) = .single (.ofMul m) a := by
  simp [toAdditiveBialgEquiv]

end Semiring

section CommSemiring
variable [CommSemiring A]

section Algebra
variable [Algebra R A] [Monoid M]

variable (R M A) in
/--
Definition of `liftMulEquiv` / `liftMulEquiv` 的定义

English:
definition liftMulEquiv
  signature: : (M ->* A) ≃* WithConv (R[M] ->ₐ[R] A) where
  body: (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

@[to_additive (dont_translate := R A) (attr := simp) convMul_algHom_single_one]

中文:
定义 liftMulEquiv
  签名: : (M ->* A) ≃* WithConv (R[M] ->ₐ[R] A) where
  定义体: (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

@[to_additive (dont_translate := R A) (attr := simp) convMul_algHom_single_one]

Depends on / 依赖: WithConv, WithConv.equiv
-/
def liftMulEquiv : (M ->* A) ≃* WithConv (R[M] ->ₐ[R] A) where
  toEquiv := (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

@[to_additive (dont_translate := R A) (attr := simp) convMul_algHom_single_one]
/--
lemma `convMul_algHom_single_one` / 引理 `convMul_algHom_single_one`

English:
lemma convMul_algHom_single_one
  given: (f g : WithConv <| R[M] ->ₐ[R] A) (x : M)
  proof: by simp [AlgHom.convMul_apply]

中文:
引理 convMul_algHom_single_one
  条件: (f g : WithConv <| R[M] ->ₐ[R] A) (x : M)
  证明: by simp [AlgHom.convMul_apply]

Depends on / 依赖: AlgHom, AlgHom.convMul_apply, convMul_apply
-/
lemma convMul_algHom_single_one (f g : WithConv <| R[M] ->ₐ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by simp [AlgHom.convMul_apply]

end Algebra

variable [Bialgebra R A]

@[to_additive (dont_translate := R A) (attr := simp) convMul_bialgHom_single_one]
/--
lemma `convMul_bialgHom_single_one` / 引理 `convMul_bialgHom_single_one`

English:
lemma convMul_bialgHom_single_one
  given: [CommMonoid M] (f g : WithConv <| R[M] ->ₐc[R] A) (x : M)
  proof: by
  simp only [BialgHom.convMul_def, BialgHom.coe_comp, Function.comp_apply]
  change mulBialgHom R A (Bialgebra.TensorProduct.map f.ofConv g.ofConv (comul (single x 1))) = _
  simp [Bialgebra.TensorProduct.map_tmul]

中文:
引理 convMul_bialgHom_single_one
  条件: [交换幺半群 M] (f g : WithConv <| R[M] ->ₐc[R] A) (x : M)
  证明: by
  simp only [BialgHom.convMul_def, BialgHom.coe_comp, Function.comp_apply]
  change mulBialgHom R A (Bialgebra.TensorProduct.map f.ofConv g.ofConv (comul (single x 1))) = _
  simp [Bialgebra.TensorProduct.map_tmul]

Depends on / 依赖: BialgHom, BialgHom.coe_comp, BialgHom.convMul_def, Bialgebra, Bialgebra.TensorProduct.map, Bialgebra.TensorProduct.map_tmul, Function, Function.comp_apply, TensorProduct, coe_comp, comp_apply, convMul_def, f.ofConv, g.ofConv, map_tmul, mulBialgHom, ofConv, single
-/
lemma convMul_bialgHom_single_one [CommMonoid M] (f g : WithConv <| R[M] ->ₐc[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp only [BialgHom.convMul_def, BialgHom.coe_comp, Function.comp_apply]
  change mulBialgHom R A (Bialgebra.TensorProduct.map f.ofConv g.ofConv (comul (single x 1))) = _
  simp [Bialgebra.TensorProduct.map_tmul]

end CommSemiring

section CommMonoid
variable [CommMonoid M] [CommMonoid N]

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `mapDomainBialgHom_mul` / 引理 `mapDomainBialgHom_mul`

English:
lemma mapDomainBialgHom_mul
  given: (f g : M ->* N)
  proof: by ext; simp

中文:
引理 mapDomainBialgHom_mul
  条件: (f g : M ->* N)
  证明: by ext; simp
-/
lemma mapDomainBialgHom_mul (f g : M ->* N) :
    mapDomainBialgHom R (f * g) =
      ofConv ((toConv <| mapDomainBialgHom R f) * (toConv <| mapDomainBialgHom R g)) := by ext; simp

/--
lemma `comulAlgHom_comp_mapRingHom` / 引理 `comulAlgHom_comp_mapRingHom`

English:
lemma comulAlgHom_comp_mapRingHom
  given: (f : R ->+* S)
  proof: by ext <;> simp

中文:
引理 comulAlgHom_comp_mapRingHom
  条件: (f : R ->+* S)
  证明: by ext <;> simp
-/
lemma comulAlgHom_comp_mapRingHom (f : R ->+* S) :
    (comulAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRingHom M f) (mapRingHom M f) (by simp)
        (by simp)) (comulAlgHom R R[M]).toRingHom := by ext <;> simp

/--
lemma `counitAlgHom_comp_mapRingHom` / 引理 `counitAlgHom_comp_mapRingHom`

English:
lemma counitAlgHom_comp_mapRingHom
  given: (f : R ->+* S)
  proof: by ext <;> simp

中文:
引理 counitAlgHom_comp_mapRingHom
  条件: (f : R ->+* S)
  证明: by ext <;> simp
-/
lemma counitAlgHom_comp_mapRingHom (f : R ->+* S) :
    (counitAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRingHom M f) =
      f.comp (counitAlgHom R R[M]).toRingHom := by ext <;> simp

end CommMonoid
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

open Submodule in
@[to_additive (dont_translate := R) isGroupLikeElem_iff_mem_range_single_one]
/--
lemma `isGroupLikeElem_iff_mem_range_single_one` / 引理 `isGroupLikeElem_iff_mem_range_single_one`

English:
lemma isGroupLikeElem_iff_mem_range_single_one
  given: {x : R[M]}
  proof: by
    by_contra h
    have : LinearIndepOn R id (insert x <| .range (single · 1)) :=
linearIndepOn_isGroupLikeElem.mono by simp [Set.subset_def, hx]
    have : x.coeff.sum single ∉ span R (.range (single · 1)) := by
      simpa using this.notMem_span_of_insert h
refine this sum_mem fun g hg => ?_
    rw [← mul_one (x.coeff g)]; rw [← smul_eq_mul]; rw [← smul_single]
exact smul_mem _ _ subset_span Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_single_one _

中文:
引理 isGroupLikeElem_iff_mem_range_single_one
  条件: {x : R[M]}
  证明: by
    by_contra h
    have : LinearIndepOn R id (insert x <| .range (single · 1)) :=
linearIndepOn_isGroupLikeElem.mono by simp [Set.subset_def, hx]
    have : x.coeff.sum single ∉ span R (.range (single · 1)) := by
      simpa using this.notMem_span_of_insert h
refine this sum_mem fun g hg => ?_
    rw [← mul_one (x.coeff g)]; rw [← smul_eq_mul]; rw [← smul_single]
exact smul_mem _ _ subset_span Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_single_one _

Depends on / 依赖: LinearIndepOn, Set.mem_range_self, Set.subset_def, insert, isGroupLikeElem_single_one, linearIndepOn_isGroupLikeElem, linearIndepOn_isGroupLikeElem.mono, mem_range_self, mul_one, notMem_span_of_insert, single, smul_eq_mul, smul_mem, smul_single, subset_def, subset_span, sum_mem, this.notMem_span_of_insert, x.coeff, x.coeff.sum
-/
lemma isGroupLikeElem_iff_mem_range_single_one {x : R[M]} :
    IsGroupLikeElem R x ↔ x in Set.range (single · 1) where
  mp hx := by
    by_contra h
    have : LinearIndepOn R id (insert x <| .range (single · 1)) :=
linearIndepOn_isGroupLikeElem.mono by simp [Set.subset_def, hx]
    have : x.coeff.sum single ∉ span R (.range (single · 1)) := by
      simpa using this.notMem_span_of_insert h
refine this sum_mem fun g hg => ?_
    rw [← mul_one (x.coeff g)]; rw [← smul_eq_mul]; rw [← smul_single]
exact smul_mem _ _ subset_span Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_single_one _

section MulOneClass
variable [MulOneClass M] {x : R[M]}

/--
lemma `isGroupLikeElem_iff_mem_range_of` / 引理 `isGroupLikeElem_iff_mem_range_of`

English:
lemma isGroupLikeElem_iff_mem_range_of
  statement: IsGroupLikeElem R x ↔ x in Set.range (of R M)
  proof: isGroupLikeElem_iff_mem_range_single_one

中文:
引理 isGroupLikeElem_iff_mem_range_of
  结论: 是GroupLikeElem R x ↔ x in 集合.range (of R M)
  证明: isGroupLikeElem_iff_mem_range_single_one

Depends on / 依赖: isGroupLikeElem_iff_mem_range_single_one
-/
lemma isGroupLikeElem_iff_mem_range_of : IsGroupLikeElem R x ↔ x in Set.range (of R M) :=
  isGroupLikeElem_iff_mem_range_single_one

end MulOneClass

section Group
variable [Group G] [Group H] [Group I]

@[to_additive (dont_translate := R)]
/--
Definition of `mapDomainOfBialgHomFun` / `mapDomainOfBialgHomFun` 的定义

English:
definition mapDomainOfBialgHomFun
  signature: (f : R[G] ->ₐc[R] R[H]) (g : G)
  body: (isGroupLikeElem_iff_mem_range_single_one.1 <| (isGroupLikeElem_single_one g).map f).choose

@[to_additive (dont_translate := R) (attr := simp)]

中文:
定义 mapDomainOfBialgHomFun
  签名: (f : R[G] ->ₐc[R] R[H]) (g : G)
  定义体: (isGroupLikeElem_iff_mem_range_single_one.1 <| (isGroupLikeElem_single_one g).map f).choose

@[to_additive (dont_translate := R) (attr := simp)]
-/
private def mapDomainOfBialgHomFun (f : R[G] ->ₐc[R] R[H]) (g : G) : H :=
  (isGroupLikeElem_iff_mem_range_single_one.1 <| (isGroupLikeElem_single_one g).map f).choose

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `single_mapDomainOfBialgHomFun_one` / 引理 `single_mapDomainOfBialgHomFun_one`

English:
lemma single_mapDomainOfBialgHomFun_one
  given: (f : R[G] ->ₐc[R] R[H]) (g : G)
  proof: (isGroupLikeElem_iff_mem_range_single_one.1 <| (isGroupLikeElem_single_one g).map f).choose_spec

中文:
引理 single_mapDomainOfBialgHomFun_one
  条件: (f : R[G] ->ₐc[R] R[H]) (g : G)
  证明: (isGroupLikeElem_iff_mem_range_single_one.1 <| (isGroupLikeElem_single_one g).map f).choose_spec
-/
private lemma single_mapDomainOfBialgHomFun_one (f : R[G] ->ₐc[R] R[H]) (g : G) :
    single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_single_one.1 <| (isGroupLikeElem_single_one g).map f).choose_spec

/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `MonoidAlgebra.mapDomainBialgHom` for the forward map. -/
@[to_additive (dont_translate := R)
/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `MonoidAlgebra.mapDomainBialgHom` for the forward map. -/]
/--
Definition of `mapDomainOfBialgHom` / `mapDomainOfBialgHom` 的定义

English:
definition mapDomainOfBialgHom
  signature: (f : R[G] ->ₐc[R] R[H])
  body: mapDomainOfBialgHomFun f
map_one' := single_left_injective (R := R) one_ne_zero by simp [← one_def]
  map_mul' g₁ g₂ := by
    refine single_left_injective (R := R) one_ne_zero ?_
    simp only [single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : R)]; rw [← single_mul_single]; rw [← single_mul_single]; rw [map_mul]
    simp

@[to_additive (dont_translate := R) (attr := simp)]

中文:
定义 mapDomainOfBialgHom
  签名: (f : R[G] ->ₐc[R] R[H])
  定义体: mapDomainOfBialgHomFun f
map_one' := single_left_injective (R := R) one_ne_zero by simp [← one_def]
  map_mul' g₁ g₂ := by
    refine single_left_injective (R := R) one_ne_zero ?_
    simp only [single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : R)]; rw [← single_mul_single]; rw [← single_mul_single]; rw [map_mul]
    simp

@[to_additive (dont_translate := R) (attr := simp)]

Depends on / 依赖: mapDomainOfBialgHomFun
-/
def mapDomainOfBialgHom (f : R[G] ->ₐc[R] R[H]) : G ->* H where
  toFun := mapDomainOfBialgHomFun f
map_one' := single_left_injective (R := R) one_ne_zero by simp [← one_def]
  map_mul' g₁ g₂ := by
    refine single_left_injective (R := R) one_ne_zero ?_
    simp only [single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : R)]; rw [← single_mul_single]; rw [← single_mul_single]; rw [map_mul]
    simp

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `single_mapDomainOfBialgHom` / 引理 `single_mapDomainOfBialgHom`

English:
lemma single_mapDomainOfBialgHom
  given: (f : R[G] ->ₐc[R] R[H]) (g : G) (r : R)
  proof: by
  rw [← mul_one r]; rw [← smul_eq_mul]; rw [← smul_single]; rw [← smul_single]; rw [map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[to_additive (dont_translate := R) (attr := simp)]

中文:
引理 single_mapDomainOfBialgHom
  条件: (f : R[G] ->ₐc[R] R[H]) (g : G) (r : R)
  证明: by
  rw [← mul_one r]; rw [← smul_eq_mul]; rw [← smul_single]; rw [← smul_single]; rw [map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[to_additive (dont_translate := R) (attr := simp)]

Depends on / 依赖: map_smul, mul_one, single_mapDomainOfBialgHomFun_one, smul_eq_mul, smul_single
-/
lemma single_mapDomainOfBialgHom (f : R[G] ->ₐc[R] R[H]) (g : G) (r : R) :
    single (mapDomainOfBialgHom f g) r = f (single g r) := by
  rw [← mul_one r]; rw [← smul_eq_mul]; rw [← smul_single]; rw [← smul_single]; rw [map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `mapDomainBialgHom_mapDomainOfBialgHom` / 引理 `mapDomainBialgHom_mapDomainOfBialgHom`

English:
lemma mapDomainBialgHom_mapDomainOfBialgHom
  given: (f : R[G] ->ₐc[R] R[H])
  proof: by
  ext x : 1
  · rw [mapDomainBialgHom_single]
    exact single_mapDomainOfBialgHomFun_one f x
  · ext

@[to_additive (dont_translate := R) (attr := simp)]

中文:
引理 mapDomainBialgHom_mapDomainOfBialgHom
  条件: (f : R[G] ->ₐc[R] R[H])
  证明: by
  ext x : 1
  · rw [mapDomainBialgHom_single]
    exact single_mapDomainOfBialgHomFun_one f x
  · ext

@[to_additive (dont_translate := R) (attr := simp)]

Depends on / 依赖: mapDomainBialgHom_single, single_mapDomainOfBialgHomFun_one
-/
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : R[G] ->ₐc[R] R[H]) :
    mapDomainBialgHom R (mapDomainOfBialgHom f) = f := by
  ext x : 1
  · rw [mapDomainBialgHom_single]
    exact single_mapDomainOfBialgHomFun_one f x
  · ext

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `mapDomainOfBialgHom_mapDomainBialgHom` / 引理 `mapDomainOfBialgHom_mapDomainBialgHom`

English:
lemma mapDomainOfBialgHom_mapDomainBialgHom
  given: (f : G ->* H)
  proof: by
  ext g; refine single_left_injective (R := R) one_ne_zero ?_; simp [single_mapDomainOfBialgHom]

@[to_additive (attr := simp)]

中文:
引理 mapDomainOfBialgHom_mapDomainBialgHom
  条件: (f : G ->* H)
  证明: by
  ext g; refine single_left_injective (R := R) one_ne_zero ?_; simp [single_mapDomainOfBialgHom]

@[to_additive (attr := simp)]

Depends on / 依赖: one_ne_zero, single_left_injective, single_mapDomainOfBialgHom
-/
lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G ->* H) :
    mapDomainOfBialgHom (mapDomainBialgHom (R := R) f) = f := by
  ext g; refine single_left_injective (R := R) one_ne_zero ?_; simp [single_mapDomainOfBialgHom]

@[to_additive (attr := simp)]
/--
lemma `mapDomainOfBialgHom_id` / 引理 `mapDomainOfBialgHom_id`

English:
lemma mapDomainOfBialgHom_id
  statement: mapDomainOfBialgHom (.id R R[G]) = .id _
  proof: by
  simp [← mapDomainBialgHom_id]

@[to_additive (attr := simp)]

中文:
引理 mapDomainOfBialgHom_id
  结论: mapDomainOfBialgHom (.id R R[G]) = .id _
  证明: by
  simp [← mapDomainBialgHom_id]

@[to_additive (attr := simp)]

Depends on / 依赖: mapDomainBialgHom_id
-/
lemma mapDomainOfBialgHom_id : mapDomainOfBialgHom (.id R R[G]) = .id _ := by
  simp [← mapDomainBialgHom_id]

@[to_additive (attr := simp)]
/--
lemma `mapDomainOfBialgHom_comp` / 引理 `mapDomainOfBialgHom_comp`

English:
lemma mapDomainOfBialgHom_comp
  given: (f : R[H] ->ₐc[R] R[I]) (g : R[G] ->ₐc[R] R[H])
  proof: by
  rw [← mapDomainOfBialgHom_mapDomainBialgHom (R := R)
    ((mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g))]; rw [mapDomainBialgHom_comp]; rw [mapDomainBialgHom_mapDomainOfBialgHom]; rw [mapDomainBialgHom_mapDomainOfBialgHom]

中文:
引理 mapDomainOfBialgHom_comp
  条件: (f : R[H] ->ₐc[R] R[I]) (g : R[G] ->ₐc[R] R[H])
  证明: by
  rw [← mapDomainOfBialgHom_mapDomainBialgHom (R := R)
    ((mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g))]; rw [mapDomainBialgHom_comp]; rw [mapDomainBialgHom_mapDomainOfBialgHom]; rw [mapDomainBialgHom_mapDomainOfBialgHom]

Depends on / 依赖: mapDomainBialgHom_comp, mapDomainBialgHom_mapDomainOfBialgHom, mapDomainOfBialgHom, mapDomainOfBialgHom_mapDomainBialgHom
-/
lemma mapDomainOfBialgHom_comp (f : R[H] ->ₐc[R] R[I]) (g : R[G] ->ₐc[R] R[H]) :
    mapDomainOfBialgHom (f.comp g) = (mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g) := by
  rw [← mapDomainOfBialgHom_mapDomainBialgHom (R := R)
    ((mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g))]; rw [mapDomainBialgHom_comp]; rw [mapDomainBialgHom_mapDomainOfBialgHom]; rw [mapDomainBialgHom_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/
@[expose, to_additive (attr := simps)
/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/]
/--
Definition of `mapDomainBialgHomEquiv` / `mapDomainBialgHomEquiv` 的定义

English:
definition mapDomainBialgHomEquiv
  signature: : (G ->* H) ≃ (R[G] ->ₐc[R] R[H]) where
  body: mapDomainBialgHom R
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

中文:
定义 mapDomainBialgHomEquiv
  签名: : (G ->* H) ≃ (R[G] ->ₐc[R] R[H]) where
  定义体: mapDomainBialgHom R
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

Depends on / 依赖: mapDomainBialgHom
-/
def mapDomainBialgHomEquiv : (G ->* H) ≃ (R[G] ->ₐc[R] R[H]) where
  toFun := mapDomainBialgHom R
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

end Group

section CommGroup
variable [CommGroup G] [CommGroup H]

/-- The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group
algebras over a domain. -/
@[expose, simps!]
/--
Definition of `mapDomainBialgHomMulEquiv` / `mapDomainBialgHomMulEquiv` 的定义

English:
definition mapDomainBialgHomMulEquiv
  signature: : (G ->* H) ≃* WithConv (R[G] ->ₐc[R] R[H]) where
  body: mapDomainBialgHomEquiv.trans (WithConv.equiv _).symm
  map_mul' f g := by simp

中文:
定义 mapDomainBialgHomMulEquiv
  签名: : (G ->* H) ≃* WithConv (R[G] ->ₐc[R] R[H]) where
  定义体: mapDomainBialgHomEquiv.trans (WithConv.equiv _).symm
  map_mul' f g := by simp

Depends on / 依赖: WithConv, WithConv.equiv, mapDomainBialgHomEquiv, mapDomainBialgHomEquiv.trans
-/
def mapDomainBialgHomMulEquiv : (G ->* H) ≃* WithConv (R[G] ->ₐc[R] R[H]) where
  toEquiv := mapDomainBialgHomEquiv.trans (WithConv.equiv _).symm
  map_mul' f g := by simp

end CommGroup
end CommRing
end MonoidAlgebra

namespace AddMonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B] [AddMonoid M] [AddMonoid N]

/--
lemma `bialgHom_ext'` / 引理 `bialgHom_ext'`

English:
lemma bialgHom_ext'
  given: ⦃φ₁ φ₂
  statement: A[M] ->ₐc[R] B⦄
  proof: BialgHom.coe_toAlgHom_injective algHom_ext' single_one_right single_one_left

中文:
引理 bialgHom_ext'
  条件: ⦃φ₁ φ₂
  结论: A[M] ->ₐc[R] B⦄
  证明: BialgHom.coe_toAlgHom_injective algHom_ext' single_one_right single_one_left

Depends on / 依赖: BialgHom, BialgHom.coe_toAlgHom_injective, algHom_ext, coe_toAlgHom_injective, single_one_left, single_one_right
-/
lemma bialgHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐc[R] B⦄
    (single_one_right : (φ₁ : A[M] ->* B).comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M))
    (single_one_left : (φ₁ : A[M] ->ₐ[R] B).comp singleZeroAlgHom =
      (φ₂ : A[M] ->ₐ[R] B).comp singleZeroAlgHom) : φ₁ = φ₂ :=
BialgHom.coe_toAlgHom_injective algHom_ext' single_one_right single_one_left

/--
lemma `isGroupLikeElem_of` / 引理 `isGroupLikeElem_of`

English:
lemma isGroupLikeElem_of
  given: (m : M)
  statement: IsGroupLikeElem R (of A M m)
  proof: isGroupLikeElem_single_one ..

中文:
引理 isGroupLikeElem_of
  条件: (m : M)
  结论: 是GroupLikeElem R (of A M m)
  证明: isGroupLikeElem_single_one ..

Depends on / 依赖: isGroupLikeElem_single_one
-/
lemma isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m) := isGroupLikeElem_single_one ..

variable (R A M) in
/-- The bialgebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[expose, simps! -isSimp]
/--
Definition of `toMultiplicativeBialgEquiv` / `toMultiplicativeBialgEquiv` 的定义

English:
definition toMultiplicativeBialgEquiv
  signature: : A[M] ≃ₐc[R] MonoidAlgebra A (Multiplicative M)
  body: .ofAlgEquiv (toMultiplicativeAlgEquiv R A M) (by ext <;> simp) by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]

中文:
定义 toMultiplicativeBialgEquiv
  签名: : A[M] ≃ₐc[R] 幺半群代数 A (Multiplicative M)
  定义体: .ofAlgEquiv (toMultiplicativeAlgEquiv R A M) (by ext <;> simp) by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]

Depends on / 依赖: Coalgebra, Coalgebra.Repr.arbitrary, arbitrary, ofAlgEquiv, toMultiplicativeAlgEquiv
-/
def toMultiplicativeBialgEquiv : A[M] ≃ₐc[R] MonoidAlgebra A (Multiplicative M) :=
.ofAlgEquiv (toMultiplicativeAlgEquiv R A M) (by ext <;> simp) by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]
/--
lemma `toMultiplicativeBialgEquiv_single` / 引理 `toMultiplicativeBialgEquiv_single`

English:
lemma toMultiplicativeBialgEquiv_single
  given: (m : M) (a : A)
  proof: by
  simp [toMultiplicativeBialgEquiv]

中文:
引理 toMultiplicativeBialgEquiv_single
  条件: (m : M) (a : A)
  证明: by
  simp [toMultiplicativeBialgEquiv]

Depends on / 依赖: toMultiplicativeBialgEquiv
-/
lemma toMultiplicativeBialgEquiv_single (m : M) (a : A) :
    toMultiplicativeBialgEquiv R A M (single m a) = .single (.ofAdd m) a := by
  simp [toMultiplicativeBialgEquiv]

end Semiring

section CommSemiring
variable [CommSemiring A] [Algebra R A] [AddMonoid M]

variable (R M A) in
/--
Definition of `liftMulEquiv` / `liftMulEquiv` 的定义

English:
definition liftMulEquiv
  signature: : (Multiplicative M ->* A) ≃* WithConv (R[M] ->ₐ[R] A) where
  body: (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

中文:
定义 liftMulEquiv
  签名: : (Multiplicative M ->* A) ≃* WithConv (R[M] ->ₐ[R] A) where
  定义体: (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

Depends on / 依赖: WithConv, WithConv.equiv
-/
def liftMulEquiv : (Multiplicative M ->* A) ≃* WithConv (R[M] ->ₐ[R] A) where
  toEquiv := (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

end CommSemiring

section AddCommMonoid
variable [AddCommMonoid M] [AddCommMonoid N]

/--
lemma `comulAlgHom_comp_mapRingHom` / 引理 `comulAlgHom_comp_mapRingHom`

English:
lemma comulAlgHom_comp_mapRingHom
  given: (f : R ->+* S)
  proof: by ext <;> simp

中文:
引理 comulAlgHom_comp_mapRingHom
  条件: (f : R ->+* S)
  证明: by ext <;> simp
-/
lemma comulAlgHom_comp_mapRingHom (f : R ->+* S) :
    (comulAlgHom S S[M]).toRingHom.comp (mapRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRingHom M f) (mapRingHom M f)
        (by ext; simp) (by ext; simp))
        (comulAlgHom R R[M]).toRingHom := by ext <;> simp

/--
lemma `counitAlgHom_comp_mapRingHom` / 引理 `counitAlgHom_comp_mapRingHom`

English:
lemma counitAlgHom_comp_mapRingHom
  given: (f : R ->+* S)
  proof: by ext <;> simp

中文:
引理 counitAlgHom_comp_mapRingHom
  条件: (f : R ->+* S)
  证明: by ext <;> simp
-/
lemma counitAlgHom_comp_mapRingHom (f : R ->+* S) :
    (counitAlgHom S S[M]).toRingHom.comp (mapRingHom M f) =
      f.comp (counitAlgHom R R[M]).toRingHom := by ext <;> simp

end AddCommMonoid
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

section AddZeroClass
variable [AddZeroClass M] {x : R[M]}

/--
lemma `isGroupLikeElem_iff_mem_range_of` / 引理 `isGroupLikeElem_iff_mem_range_of`

English:
lemma isGroupLikeElem_iff_mem_range_of
  statement: IsGroupLikeElem R x ↔ x in Set.range (of R M)
  proof: isGroupLikeElem_iff_mem_range_single_one

中文:
引理 isGroupLikeElem_iff_mem_range_of
  结论: 是GroupLikeElem R x ↔ x in 集合.range (of R M)
  证明: isGroupLikeElem_iff_mem_range_single_one

Depends on / 依赖: isGroupLikeElem_iff_mem_range_single_one
-/
lemma isGroupLikeElem_iff_mem_range_of : IsGroupLikeElem R x ↔ x in Set.range (of R M) :=
  isGroupLikeElem_iff_mem_range_single_one

end AddZeroClass

section AddCommGroup
variable [AddCommGroup G] [AddCommGroup H]

/--
Definition of `mapDomainBialgHomAddEquiv` / `mapDomainBialgHomAddEquiv` 的定义

English:
definition mapDomainBialgHomAddEquiv
  signature: : (G ->+ H) ≃+ Additive (WithConv <| R[G] ->ₐc[R] R[H]) where
  body: mapDomainBialgHomEquiv.trans (WithConv.equiv _).symm.trans Additive.ofMul
  map_add' f g := by simp

中文:
定义 mapDomainBialgHomAddEquiv
  签名: : (G ->+ H) ≃+ 加性 (WithConv <| R[G] ->ₐc[R] R[H]) where
  定义体: mapDomainBialgHomEquiv.trans (WithConv.equiv _).symm.trans Additive.ofMul
  map_add' f g := by simp

Depends on / 依赖: Additive, Additive.ofMul, WithConv, WithConv.equiv, mapDomainBialgHomEquiv, mapDomainBialgHomEquiv.trans, symm.trans
-/
def mapDomainBialgHomAddEquiv : (G ->+ H) ≃+ Additive (WithConv <| R[G] ->ₐc[R] R[H]) where
toEquiv := mapDomainBialgHomEquiv.trans (WithConv.equiv _).symm.trans Additive.ofMul
  map_add' f g := by simp

end AddCommGroup
end CommRing
end AddMonoidAlgebra

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A]

/--
Instance `instBialgebra` / 实例 `instBialgebra`

English:
instance instBialgebra
  signature: : Bialgebra R A[T;T⁻¹]
  body: inferInstanceAs Bialgebra R A[Int]

@[simp]

中文:
实例 instBialgebra
  签名: : 双代数 R A[T;T⁻¹]
  定义体: inferInstanceAs Bialgebra R A[Int]

@[simp]

Depends on / 依赖: Bialgebra
-/
instance instBialgebra : Bialgebra R A[T;T⁻¹] :=
inferInstanceAs Bialgebra R A[Int]

@[simp]
/--
theorem `comul_T` / 定理 `comul_T`

English:
theorem comul_T
  given: (n : Int)
  statement: comul (T n : A[T;T⁻¹]) = T n otimesₜ[R] T n
  proof: by simp [T, -single_eq_C_mul_T]

@[simp]

中文:
定理 comul_T
  条件: (n : 整数)
  结论: comul (T n : A[T;T⁻¹]) = T n otimesₜ[R] T n
  证明: by simp [T, -single_eq_C_mul_T]

@[simp]

Depends on / 依赖: single_eq_C_mul_T
-/
theorem comul_T (n : Int) : comul (T n : A[T;T⁻¹]) = T n otimesₜ[R] T n := by simp [T, -single_eq_C_mul_T]

@[simp]
/--
theorem `counit_T` / 定理 `counit_T`

English:
theorem counit_T
  given: (n : Int)
  proof: by
  simp [T, -single_eq_C_mul_T]

中文:
定理 counit_T
  条件: (n : 整数)
  证明: by
  simp [T, -single_eq_C_mul_T]

Depends on / 依赖: single_eq_C_mul_T
-/
theorem counit_T (n : Int) :
    Coalgebra.counit (R := R) (T n : A[T;T⁻¹]) = 1 := by
  simp [T, -single_eq_C_mul_T]

end LaurentPolynomial
