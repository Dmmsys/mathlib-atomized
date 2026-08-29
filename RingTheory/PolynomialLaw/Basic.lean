/-
Copyright (c) 2025 Antoine Chambert-Loir & María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir & María-Inés de Frutos-Fernández
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-! # Polynomial laws on modules

Let `M` and `N` be a modules over a commutative ring `R`.
A polynomial law `f : PolynomialLaw R M N`, with notation `f : M →ₚₗₗ[R] N`,
is a “law” that assigns a natural map `PolynomialLaw.toFun' f S : S ⊗[R] M → S ⊗[R] N`
for every `R`-algebra `S`.

For type-theoretic reasons, if `R : Type u`, then the definition of the polynomial map `f`
is restricted to `R`-algebras `S` such that `S : Type u`.
Using the fact that a module is the direct limit of its finitely generated submodules, that a
finitely generated subalgebra is a quotient of a polynomial ring in the universe `u`, plus
the commutation of tensor products with direct limits, we extend the functor
to all `R`-algebras.

The two fields involving the definition of `PolynomialLaw`,
`PolynomialLaw.toFun'` and `PolynomialLaw.isCompat'` are primed.
They are superseded by their universe-polymorphic counterparts,
the definition `PolynomialLaw.toFun` and the lemma `PolynomialLaw.isCompat`
which should be used once the theory is properly stated.

For constructions of general definitions of `PolynomialLaw`
at a universe-polymorphic level, one needs to lift
elements in a tensor product to smaller universes.
For this, one can make use of
`PolynomialLaw.exists_lift` or `PolynomialLaw.exists_lift'`,
or establish appropriate generalizations.

## Main definitions/lemmas

* Instance : `Module R (M →ₚₗ[R] N)` shows that polynomial laws form an `R`-module.

* `PolynomialLaw.ground f` is the map `M → N` corresponding to `PolynomialLaw.toFun' f R` under
  the isomorphisms `R ⊗[R] M ≃ₗ[R] M`, and similarly for `N`.

In further works, we construct the coefficients of a polynomial law and show the relation with
polynomials (when the module `M` is free and finite).

## Implementation notes

In the literature, the theory is written for commutative rings, but this implementation
only assumes `R` is a commutative semiring.

## References

* [Roby, Norbert. 1963. «Lois polynomes et lois formelles en théorie des modules».
  Annales scientifiques de l’École Normale Supérieure 80 (3): 213‑348](Roby-1963)

-/

@[expose] public section

universe u v w

noncomputable section PolynomialLaw

open scoped TensorProduct

open LinearMap TensorProduct AlgHom RingCon

/-- A polynomial law `M →ₚₗ[R] N` between `R`-modules is a functorial family of maps
`S ⊗[R] M → S ⊗[R] N`, for all `R`-algebras `S`.

For universe reasons, `S` has to be restricted to the same universe as `R`. -/
@[ext]
/--
Definition of `PolynomialLaw` / `PolynomialLaw` 的定义

English:
structure PolynomialLaw
  parameters: (R : Type u) [CommSemiring R]
  axioms and operations (2):
    - toFun'((S : Type u) [CommSemiring S] [Algebra R S]) : S otimes[R] M -> S otimes[R] N
    - isCompat'({S : Type u} [CommSemiring S] [Algebra R S] {S' : Type u} [CommSemiring S'] [Algebra R S'] (φ : S ->ₐ[R] S')) : φ.toLinearMap.rTensor N ∘ toFun' S = toFun' S' ∘ φ.toLinearMap.rTensor M  [default: by aesop]

中文:
结构 PolynomialLaw
  参数: (R : 类型u) [CommSemiring R]
  公理与运算 (2 个):
    - toFun'((S : 类型u) [CommSemiring S] [Algebra R S]) : S otimes[R] M -> S otimes[R] N
    - isCompat'({S : 类型u} [CommSemiring S] [Algebra R S] {S' : 类型u} [CommSemiring S'] [Algebra R S'] (φ : S ->ₐ[R] S')) : φ.toLinearMap.rTensor N ∘ toFun' S = toFun' S' ∘ φ.toLinearMap.rTensor M  [默认: by aesop]
-/
structure PolynomialLaw (R : Type u) [CommSemiring R]
    (M : Type*) [AddCommMonoid M] [Module R M] (N : Type*) [AddCommMonoid N] [Module R N] where
  /-- The functions `S ⊗[R] M → S ⊗[R] N` underlying a polynomial law -/
  toFun' (S : Type u) [CommSemiring S] [Algebra R S] : S otimes[R] M -> S otimes[R] N
  /-- The compatibility relations between the functions underlying a polynomial law -/
  isCompat' {S : Type u} [CommSemiring S] [Algebra R S]
    {S' : Type u} [CommSemiring S'] [Algebra R S'] (φ : S ->ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ toFun' S = toFun' S' ∘ φ.toLinearMap.rTensor M := by aesop

/-- `M →ₚₗ[R] N` is the type of `R`-polynomial laws from `M` to `N`. -/
notation:25 M " ->ₚₗ[" R:25 "] " N:0 => PolynomialLaw R M N

@[local simp]
/--
theorem `PolynomialLaw.isCompat_apply'` / 定理 `PolynomialLaw.isCompat_apply'`

English:
theorem PolynomialLaw.isCompat_apply'
  proof: by
  simpa only using! congr_fun (f.isCompat' φ) x

中文:
定理 PolynomialLaw.isCompat_apply'
  证明: by
  simpa only using! congr_fun (f.isCompat' φ) x

Depends on / 依赖: congr_fun, f.isCompat, isCompat
-/
theorem PolynomialLaw.isCompat_apply'
    {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N] {f : M ->ₚₗ[R] N}
    {S : Type u} [CommSemiring S] [Algebra R S] {S' : Type u} [CommSemiring S'] [Algebra R S']
    (φ : S ->ₐ[R] S') (x : S otimes[R] M) :
    (φ.toLinearMap.rTensor N) ((f.toFun' S) x) = (f.toFun' S') (φ.toLinearMap.rTensor M x) := by
  simpa only using! congr_fun (f.isCompat' φ) x

attribute [local simp] PolynomialLaw.isCompat_apply'

namespace PolynomialLaw

section Module

section CommSemiring

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N] (r a b : R) (f g : M ->ₚₗ[R] N)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (M ->ₚₗ[R] N)
  body: ⟨{ toFun' _ := 0 }⟩

@[simp]

中文:
实例 :
  签名: Zero (M ->ₚₗ[R] N)
  定义体: ⟨{ toFun' _ := 0 }⟩

@[simp]
-/
instance : Zero (M ->ₚₗ[R] N) := ⟨{ toFun' _ := 0 }⟩

@[simp]
/--
theorem `zero_def` / 定理 `zero_def`

English:
theorem zero_def
  given: (S : Type u) [CommSemiring S] [Algebra R S]
  proof: rfl

中文:
定理 zero_def
  条件: (S : 类型u) [CommSemiring S] [Algebra R S]
  证明: rfl
-/
theorem zero_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (0 : PolynomialLaw R M N).toFun' S = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (PolynomialLaw R M N)
  body: ⟨Zero.zero⟩

中文:
实例 :
  签名: Inhabited (PolynomialLaw R M N)
  定义体: ⟨Zero.zero⟩

Depends on / 依赖: Zero.zero
-/
instance : Inhabited (PolynomialLaw R M N) := ⟨Zero.zero⟩

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : M ->ₚₗ[R] M where
  body: _root_.id

中文:
定义 id
  签名: : M ->ₚₗ[R] M where
  定义体: _root_.id

Depends on / 依赖: _root_, _root_.id
-/
def id : M ->ₚₗ[R] M where
  toFun' S _ _ := _root_.id

/--
theorem `id_apply'` / 定理 `id_apply'`

English:
theorem id_apply'
  given: {S : Type u} [CommSemiring S] [Algebra R S]
  proof: rfl

中文:
定理 id_apply'
  条件: {S : 类型u} [CommSemiring S] [Algebra R S]
  证明: rfl
-/
theorem id_apply' {S : Type u} [CommSemiring S] [Algebra R S] :
    (id : M ->ₚₗ[R] M).toFun' S = _root_.id := rfl

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : M ->ₚₗ[R] N where
  body: f.toFun' S + g.toFun' S

中文:
定义 add
  签名: : M ->ₚₗ[R] N where
  定义体: f.toFun' S + g.toFun' S

Depends on / 依赖: f.toFun, g.toFun
-/
noncomputable def add : M ->ₚₗ[R] N where
  toFun' S _ _ := f.toFun' S + g.toFun' S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (PolynomialLaw R M N)
  body: ⟨add⟩

@[simp]

中文:
实例 :
  签名: Add (PolynomialLaw R M N)
  定义体: ⟨add⟩

@[simp]
-/
instance : Add (PolynomialLaw R M N) := ⟨add⟩

@[simp]
/--
theorem `add_def` / 定理 `add_def`

English:
theorem add_def
  given: (S : Type u) [CommSemiring S] [Algebra R S]
  proof: rfl

中文:
定理 add_def
  条件: (S : 类型u) [CommSemiring S] [Algebra R S]
  证明: rfl
-/
theorem add_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (f + g).toFun' S = f.toFun' S + g.toFun' S := rfl

/--
theorem `add_def_apply` / 定理 `add_def_apply`

English:
theorem add_def_apply
  given: (S : Type u) [CommSemiring S] [Algebra R S] (m : S otimes[R] M)
  proof: rfl

中文:
定理 add_def_apply
  条件: (S : 类型u) [CommSemiring S] [Algebra R S] (m : S otimes[R] M)
  证明: rfl
-/
theorem add_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S otimes[R] M) :
    (f + g).toFun' S m = f.toFun' S m + g.toFun' S m := rfl

/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: : M ->ₚₗ[R] N where
  body: r • f.toFun' S

中文:
定义 smul
  签名: : M ->ₚₗ[R] N where
  定义体: r • f.toFun' S

Depends on / 依赖: f.toFun
-/
def smul : M ->ₚₗ[R] N where
  toFun' S _ _ := r • f.toFun' S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (M ->ₚₗ[R] N)
  body: ⟨smul⟩

@[simp]

中文:
实例 :
  签名: SMul R (M ->ₚₗ[R] N)
  定义体: ⟨smul⟩

@[simp]
-/
instance : SMul R (M ->ₚₗ[R] N) := ⟨smul⟩

@[simp]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (S : Type u) [CommSemiring S] [Algebra R S]
  proof: rfl

中文:
定理 smul_def
  条件: (S : 类型u) [CommSemiring S] [Algebra R S]
  证明: rfl
-/
theorem smul_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (r • f).toFun' S = r • f.toFun' S := rfl

/--
theorem `smul_def_apply` / 定理 `smul_def_apply`

English:
theorem smul_def_apply
  given: (S : Type u) [CommSemiring S] [Algebra R S] (m : S otimes[R] M)
  proof: rfl

中文:
定理 smul_def_apply
  条件: (S : 类型u) [CommSemiring S] [Algebra R S] (m : S otimes[R] M)
  证明: rfl
-/
theorem smul_def_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S otimes[R] M) :
    (r • f).toFun' S m = r • f.toFun' S m := rfl

/--
theorem `add_smul` / 定理 `add_smul`

English:
theorem add_smul
  statement: (a + b) • f = a • f + b • f
  proof: by
  ext; simp only [add_def, smul_def, _root_.add_smul]

中文:
定理 add_smul
  结论: (a + b) • f = a • f + b • f
  证明: by
  ext; simp only [add_def, smul_def, _root_.add_smul]

Depends on / 依赖: _root_, _root_.add_smul, add_def, add_smul, smul_def, smul_left_def
-/
theorem add_smul : (a + b) • f = a • f + b • f := by
  ext; simp only [add_def, smul_def, _root_.add_smul]

/--
theorem `zero_smul` / 定理 `zero_smul`

English:
theorem zero_smul
  statement: (0 : R) • f = 0
  proof: by
  ext S; simp only [smul_def, _root_.zero_smul, zero_def, Pi.zero_apply]

中文:
定理 zero_smul
  结论: (0 : R) • f = 0
  证明: by
  ext S; simp only [smul_def, _root_.zero_smul, zero_def, Pi.zero_apply]

Depends on / 依赖: Pi.zero_apply, _root_, _root_.zero_smul, isScalarTower, smul_def, zero_apply, zero_def, zero_smul
-/
theorem zero_smul : (0 : R) • f = 0 := by
  ext S; simp only [smul_def, _root_.zero_smul, zero_def, Pi.zero_apply]

/--
theorem `one_smul` / 定理 `one_smul`

English:
theorem one_smul
  statement: (1 : R) • f = f
  proof: by
  ext S; simp only [smul_def, Pi.smul_apply, _root_.one_smul]

中文:
定理 one_smul
  结论: (1 : R) • f = f
  证明: by
  ext S; simp only [smul_def, Pi.smul_apply, _root_.one_smul]

Depends on / 依赖: Pi.smul_apply, _root_, _root_.one_smul, one_smul, smul_apply, smul_def, smul_left_def, smul_right_def, toVal_smul
-/
theorem one_smul : (1 : R) • f = f := by
  ext S; simp only [smul_def, Pi.smul_apply, _root_.one_smul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction R (M ->ₚₗ[R] N)
  body: one_smul
  mul_smul a b f := by ext; simp only [smul_def, mul_smul]

中文:
实例 :
  签名: MulAction R (M ->ₚₗ[R] N)
  定义体: one_smul
  mul_smul a b f := by ext; simp only [smul_def, mul_smul]

Depends on / 依赖: one_smul
-/
instance : MulAction R (M ->ₚₗ[R] N) where
  one_smul := one_smul
  mul_smul a b f := by ext; simp only [smul_def, mul_smul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (M ->ₚₗ[R] N)
  body: by ext; simp only [add_def, add_assoc]
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f := (n : R) • f
  nsmul_zero f := by simp_rw [HSMul.hSMul, SMul.smul]; simp only [Nat.cast_zero, zero_smul f]
  nsmul_succ

中文:
实例 :
  签名: AddCommMonoid (M ->ₚₗ[R] N)
  定义体: by ext; simp only [add_def, add_assoc]
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f := (n : R) • f
  nsmul_zero f := by simp_rw [HSMul.hSMul, SMul.smul]; simp only [Nat.cast_zero, zero_smul f]
  nsmul_succ

Depends on / 依赖: HSMul.hSMul, Nat.cast_add, Nat.cast_one, Nat.cast_zero, SMul.smul, add_assoc, add_comm, add_def, add_smul, add_zero, cast_add, cast_one, cast_zero, nsmul_succ, nsmul_zero, one_smul, simp_rw, zero_add, zero_def, zero_smul
-/
instance : AddCommMonoid (M ->ₚₗ[R] N) where
  add_assoc f g h := by ext; simp only [add_def, add_assoc]
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f := (n : R) • f
  nsmul_zero f := by simp_rw [HSMul.hSMul, SMul.smul]; simp only [Nat.cast_zero, zero_smul f]
  nsmul_succ n f := by
    simp_rw [HSMul.hSMul, SMul.smul]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  add_comm f g := by ext; simp only [add_def, add_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (M ->ₚₗ[R] N)
  body: rfl
  smul_add a f g := by ext; simp only [smul_def, add_def, smul_add]
  add_smul := add_smul
  zero_smul := zero_smul

中文:
实例 :
  签名: Module R (M ->ₚₗ[R] N)
  定义体: rfl
  smul_add a f g := by ext; simp only [smul_def, add_def, smul_add]
  add_smul := add_smul
  zero_smul := zero_smul
-/
instance : Module R (M ->ₚₗ[R] N) where
  smul_zero a := rfl
  smul_add a f g := by ext; simp only [smul_def, add_def, smul_add]
  add_smul := add_smul
  zero_smul := zero_smul

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]
  (f : M ->ₚₗ[R] N)

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: : M ->ₚₗ[R] N where
  body: (-1 : R) • f.toFun' S

中文:
定义 neg
  签名: : M ->ₚₗ[R] N where
  定义体: (-1 : R) • f.toFun' S

Depends on / 依赖: f.toFun
-/
noncomputable def neg : M ->ₚₗ[R] N where
  toFun' S _ _ := (-1 : R) • f.toFun' S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (M ->ₚₗ[R] N)
  body: ⟨neg⟩

@[simp]

中文:
实例 :
  签名: Neg (M ->ₚₗ[R] N)
  定义体: ⟨neg⟩

@[simp]
-/
instance : Neg (M ->ₚₗ[R] N) := ⟨neg⟩

@[simp]
/--
theorem `neg_def` / 定理 `neg_def`

English:
theorem neg_def
  given: (S : Type u) [CommSemiring S] [Algebra R S]
  proof: rfl

中文:
定理 neg_def
  条件: (S : 类型u) [CommSemiring S] [Algebra R S]
  证明: rfl
-/
theorem neg_def (S : Type u) [CommSemiring S] [Algebra R S] :
    (-f).toFun' S = (-1 : R) • f.toFun' S := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (M ->ₚₗ[R] N)
  body: (n : R) • f
  zsmul_zero' f := by simp_rw [HSMul.hSMul, SMul.smul]; simp only [Int.cast_zero, zero_smul]
  zsmul_succ' n f := by
    simp_rw [HSMul.hSMul, SMul.smul]
    simp only [Nat.cast_succ, Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
  zsmul_neg' n f := by
    simp_rw [HS

中文:
实例 :
  签名: AddCommGroup (M ->ₚₗ[R] N)
  定义体: (n : R) • f
  zsmul_zero' f := by simp_rw [HSMul.hSMul, SMul.smul]; simp only [Int.cast_zero, zero_smul]
  zsmul_succ' n f := by
    simp_rw [HSMul.hSMul, SMul.smul]
    simp only [Nat.cast_succ, Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
  zsmul_neg' n f := by
    simp_rw [HS
-/
instance : AddCommGroup (M ->ₚₗ[R] N) where
  zsmul n f := (n : R) • f
  zsmul_zero' f := by simp_rw [HSMul.hSMul, SMul.smul]; simp only [Int.cast_zero, zero_smul]
  zsmul_succ' n f := by
    simp_rw [HSMul.hSMul, SMul.smul]
    simp only [Nat.cast_succ, Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
  zsmul_neg' n f := by
    simp_rw [HSMul.hSMul, SMul.smul]
    ext S _ _ m
    rw [neg_def]
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, add_smul,
      add_def_apply, smul_def_apply, Nat.succ_eq_add_one, Int.cast_add, Int.cast_natCast,
      Int.cast_one, one_smul, add_def, smul_def, Pi.smul_apply, Pi.add_apply, smul_add,
      smul_smul, neg_mul, one_mul]
    rw [add_comm]
  neg_add_cancel f := by
    ext S _ _ m
    simp only [add_def_apply, neg_def, Pi.smul_apply, zero_def, Pi.zero_apply]
    nth_rewrite 2 [← _root_.one_smul (M := R) (b := f.toFun' S m)]
    rw [← _root_.add_smul]
    simp only [neg_add_cancel, _root_.zero_smul]
  add_comm f g := by ext; simp only [add_def, add_comm]

end CommRing

end Module

section ground

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
variable (f : M ->ₚₗ[R] N)

/--
Definition of `ground` / `ground` 的定义

English:
definition ground
  signature: : M -> N
  body: (TensorProduct.lid R N) ∘ (f.toFun' R) ∘ (TensorProduct.lid R M).symm

中文:
定义 ground
  签名: : M -> N
  定义体: (TensorProduct.lid R N) ∘ (f.toFun' R) ∘ (TensorProduct.lid R M).symm

Depends on / 依赖: TensorProduct, TensorProduct.lid, f.toFun, of_ringEquiv_left
-/
def ground : M -> N := (TensorProduct.lid R N) ∘ (f.toFun' R) ∘ (TensorProduct.lid R M).symm

/--
theorem `ground_apply` / 定理 `ground_apply`

English:
theorem ground_apply
  given: (m : M)
  statement: f.ground m = TensorProduct.lid R N (f.toFun' R (1 otimesₜ[R] m))
  proof: rfl

中文:
定理 ground_apply
  条件: (m : M)
  结论: f.ground m = TensorProduct.lid R N (f.toFun' R (1 otimesₜ[R] m))
  证明: rfl
-/
theorem ground_apply (m : M) : f.ground m = TensorProduct.lid R N (f.toFun' R (1 otimesₜ[R] m)) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (M ->ₚₗ[R] N) (fun _ => M -> N)
  body: ground

中文:
实例 :
  签名: CoeFun (M ->ₚₗ[R] N) (fun _ => M -> N)
  定义体: ground

Depends on / 依赖: ground
-/
instance : CoeFun (M ->ₚₗ[R] N) (fun _ => M -> N) where
  coe := ground

/--
theorem `one_tmul_ground_apply'` / 定理 `one_tmul_ground_apply'`

English:
theorem one_tmul_ground_apply'
  given: {S : Type u} [CommSemiring S] [Algebra R S] (x : M)
  proof: by
  rw [ground_apply]
  convert! f.isCompat_apply' (Algebra.algHom R R S) (1 otimesₜ[R] x)
  · simp only [includeRight_lid]
  · rw [rTensor_tmul, toLinearMap_apply, map_one]

中文:
定理 one_tmul_ground_apply'
  条件: {S : 类型u} [CommSemiring S] [Algebra R S] (x : M)
  证明: by
  rw [ground_apply]
  convert! f.isCompat_apply' (Algebra.algHom R R S) (1 otimesₜ[R] x)
  · simp only [includeRight_lid]
  · rw [rTensor_tmul, toLinearMap_apply, map_one]

Depends on / 依赖: Algebra, Algebra.algHom, algHom, convert, f.isCompat_apply, ground_apply, includeRight_lid, isCompat_apply, map_one, rTensor_tmul, toLinearMap_apply
-/
theorem one_tmul_ground_apply' {S : Type u} [CommSemiring S] [Algebra R S] (x : M) :
    1 otimesₜ (f.ground x) = (f.toFun' S) (1 otimesₜ x) := by
  rw [ground_apply]
  convert! f.isCompat_apply' (Algebra.algHom R R S) (1 otimesₜ[R] x)
  · simp only [includeRight_lid]
  · rw [rTensor_tmul, toLinearMap_apply, map_one]

/--
Definition of `lground` / `lground` 的定义

English:
definition lground
  signature: : (M ->ₚₗ[R] N) ->ₗ[R] (M -> N) where
  body: ground
  map_add' x y := by ext m; simp [ground]
  map_smul' r x := by ext m; simp [ground]

中文:
定义 lground
  签名: : (M ->ₚₗ[R] N) ->ₗ[R] (M -> N) where
  定义体: ground
  map_add' x y := by ext m; simp [ground]
  map_smul' r x := by ext m; simp [ground]

Depends on / 依赖: ground
-/
def lground : (M ->ₚₗ[R] N) ->ₗ[R] (M -> N) where
  toFun := ground
  map_add' x y := by ext m; simp [ground]
  map_smul' r x := by ext m; simp [ground]

/--
theorem `ground_id` / 定理 `ground_id`

English:
theorem ground_id
  statement: (id : M ->ₚₗ[R] M).ground = _root_.id
  proof: by
  ext; simp [ground_apply, id_apply']

中文:
定理 ground_id
  结论: (id : M ->ₚₗ[R] M).ground = _root_.id
  证明: by
  ext; simp [ground_apply, id_apply']

Depends on / 依赖: ground_apply, id_apply
-/
theorem ground_id : (id : M ->ₚₗ[R] M).ground = _root_.id := by
  ext; simp [ground_apply, id_apply']

/--
theorem `ground_id_apply` / 定理 `ground_id_apply`

English:
theorem ground_id_apply
  given: (m : M)
  statement: (id : M ->ₚₗ[R] M).ground m = m
  proof: by
  rw [ground_id]; rw [id_eq]

中文:
定理 ground_id_apply
  条件: (m : M)
  结论: (id : M ->ₚₗ[R] M).ground m = m
  证明: by
  rw [ground_id]; rw [id_eq]

Depends on / 依赖: IsLocalization, IsLocalization.isLocalization_iff_of_algEquiv, algEquiv, ground_id, id_eq, isLocalization_iff_of_algEquiv
-/
theorem ground_id_apply (m : M) : (id : M ->ₚₗ[R] M).ground m = m := by
  rw [ground_id]; rw [id_eq]

end ground

section Composition

variable {R : Type u} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {P : Type*} [AddCommMonoid P] [Module R P]
variable {Q : Type*} [AddCommMonoid Q] [Module R Q]
variable (f : M ->ₚₗ[R] N) (g : N ->ₚₗ[R] P) (h : P ->ₚₗ[R] Q)

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : N ->ₚₗ[R] P) (f : M ->ₚₗ[R] N)
  body: (g.toFun' S).comp (f.toFun' S)
  isCompat' φ := by ext; simp only [Function.comp_apply, isCompat_apply']

中文:
定义 comp
  签名: (g : N ->ₚₗ[R] P) (f : M ->ₚₗ[R] N)
  定义体: (g.toFun' S).comp (f.toFun' S)
  isCompat' φ := by ext; simp only [Function.comp_apply, isCompat_apply']

Depends on / 依赖: f.toFun, g.toFun
-/
def comp (g : N ->ₚₗ[R] P) (f : M ->ₚₗ[R] N) : M ->ₚₗ[R] P where
  toFun' S _ _ := (g.toFun' S).comp (f.toFun' S)
  isCompat' φ := by ext; simp only [Function.comp_apply, isCompat_apply']

/--
theorem `comp_toFun'` / 定理 `comp_toFun'`

English:
theorem comp_toFun'
  given: (S : Type u) [CommSemiring S] [Algebra R S]
  proof: rfl

中文:
定理 comp_toFun'
  条件: (S : 类型u) [CommSemiring S] [Algebra R S]
  证明: rfl
-/
theorem comp_toFun' (S : Type u) [CommSemiring S] [Algebra R S] :
    (g.comp f).toFun' S = (g.toFun' S).comp (f.toFun' S) := rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: h.comp (g.comp f) = (h.comp g).comp f
  proof: rfl

中文:
定理 comp_assoc
  结论: h.comp (g.comp f) = (h.comp g).comp f
  证明: rfl
-/
theorem comp_assoc : h.comp (g.comp f) = (h.comp g).comp f := rfl

/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  statement: g.comp id = g
  proof: by ext; rfl

中文:
定理 comp_id
  结论: g.comp id = g
  证明: by ext; rfl
-/
theorem comp_id : g.comp id = g := by ext; rfl

/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  statement: id.comp f = f
  proof: by ext; rfl

中文:
定理 id_comp
  结论: id.comp f = f
  证明: by ext; rfl
-/
theorem id_comp : id.comp f = f := by ext; rfl

end Composition

section Universe

open scoped TensorProduct

open MvPolynomial

variable (R : Type u) [CommSemiring R]
  (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N]
  (S : Type v) [CommSemiring S] [Algebra R S]
  (f : M ->ₚₗ[R] N)

section Lift

open LinearMap

-- The universe of `PolynomialLaw.lifts` is computed by the compiler
/--
Definition of `lifts` / `lifts` 的定义

English:
definition lifts
  signature: : Type _
  body: Σ (s : Finset S), (MvPolynomial (Fin s.card) R) otimes[R] M

中文:
定义 lifts
  签名: : Type _
  定义体: Σ (s : Finset S), (MvPolynomial (Fin s.card) R) otimes[R] M

Depends on / 依赖: Finset, MvPolynomial, otimes, s.card
-/
def lifts : Type _ := Σ (s : Finset S), (MvPolynomial (Fin s.card) R) otimes[R] M


variable {S}

/--
Definition of `φ` / `φ` 的定义

English:
definition φ
  signature: (s : Finset S)
  body: aeval (R := R) (fun n => (s.equivFin.symm n : S))

中文:
定义 φ
  签名: (s : Finset S)
  定义体: aeval (R := R) (fun n => (s.equivFin.symm n : S))

Depends on / 依赖: equivFin, s.equivFin.symm
-/
def φ (s : Finset S) : MvPolynomial (Fin s.card) R ->ₐ[R] S :=
  aeval (R := R) (fun n => (s.equivFin.symm n : S))

/--
theorem `range_φ` / 定理 `range_φ`

English:
theorem range_φ
  given: (s : Finset S)
  statement: (φ R s).range = Algebra.adjoin R s
  proof: by
  simp only [φ]
  rw [← Algebra.adjoin_range_eq_range_aeval]
  congr
  rw [← Function.comp_def]; rw [Set.range_comp]
  simp only [Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe_subtype, Finset.setOfPred_mem]

中文:
定理 range_φ
  条件: (s : Finset S)
  结论: (φ R s).range = Algebra.adjoin R s
  证明: by
  simp only [φ]
  rw [← Algebra.adjoin_range_eq_range_aeval]
  congr
  rw [← Function.comp_def]; rw [Set.range_comp]
  simp only [Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe_subtype, Finset.setOfPred_mem]

Depends on / 依赖: Algebra, Algebra.adjoin_range_eq_range_aeval, Equiv.range_eq_univ, Finset, Finset.setOfPred_mem, Function, Function.comp_def, Set.image_univ, Set.range_comp, Subtype, Subtype.range_coe_subtype, adjoin_range_eq_range_aeval, comp_def, image_univ, range_coe_subtype, range_comp, range_eq_univ, setOfPred_mem
-/
theorem range_φ (s : Finset S) : (φ R s).range = Algebra.adjoin R s := by
  simp only [φ]
  rw [← Algebra.adjoin_range_eq_range_aeval]
  congr
  rw [← Function.comp_def]; rw [Set.range_comp]
  simp only [Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe_subtype, Finset.setOfPred_mem]

variable (S)

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : lifts R M S -> S otimes[R] M
  body: fun ⟨s, p⟩ => rTensor M (φ R s).toLinearMap p

中文:
定义 π
  签名: : lifts R M S -> S otimes[R] M
  定义体: fun ⟨s, p⟩ => rTensor M (φ R s).toLinearMap p

Depends on / 依赖: rTensor, toLinearMap
-/
def π : lifts R M S -> S otimes[R] M := fun ⟨s, p⟩ => rTensor M (φ R s).toLinearMap p

variable {R M N}

/--
Definition of `toFunLifted` / `toFunLifted` 的定义

English:
definition toFunLifted
  signature: : lifts R M S -> S otimes[R] N
  body: fun ⟨s, p⟩ => rTensor N (φ R s).toLinearMap (f.toFun' (MvPolynomial (Fin s.card) R) p)

中文:
定义 toFunLifted
  签名: : lifts R M S -> S otimes[R] N
  定义体: fun ⟨s, p⟩ => rTensor N (φ R s).toLinearMap (f.toFun' (MvPolynomial (Fin s.card) R) p)

Depends on / 依赖: MvPolynomial, f.toFun, rTensor, s.card, toLinearMap
-/
def toFunLifted : lifts R M S -> S otimes[R] N :=
  fun ⟨s, p⟩ => rTensor N (φ R s).toLinearMap (f.toFun' (MvPolynomial (Fin s.card) R) p)

/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: : S otimes[R] M -> S otimes[R] N
  body: Function.extend (π R M S) (f.toFunLifted S) (fun _ => 0)

中文:
定义 toFun
  签名: : S otimes[R] M -> S otimes[R] N
  定义体: Function.extend (π R M S) (f.toFunLifted S) (fun _ => 0)

Depends on / 依赖: Function, Function.extend, extend, f.toFunLifted, toFunLifted
-/
def toFun : S otimes[R] M -> S otimes[R] N := Function.extend (π R M S) (f.toFunLifted S) (fun _ => 0)

variable {S}

/--
theorem `exists_range_φ_eq_of_fg` / 定理 `exists_range_φ_eq_of_fg`

English:
theorem exists_range_φ_eq_of_fg
  given: {B : Subalgebra R S} (hB : Subalgebra.FG B)
  proof: ⟨hB.choose, by simp only [range_φ, hB.choose_spec]⟩

中文:
定理 exists_range_φ_eq_of_fg
  条件: {B : Subalgebra R S} (hB : Subalgebra.FG B)
  证明: ⟨hB.choose, by simp only [range_φ, hB.choose_spec]⟩

Depends on / 依赖: choose_spec, hB.choose, hB.choose_spec
-/
theorem exists_range_φ_eq_of_fg {B : Subalgebra R S} (hB : Subalgebra.FG B) :
    exists s : Finset S, (φ R s).range = B :=
  ⟨hB.choose, by simp only [range_φ, hB.choose_spec]⟩

section diagrams

variable
    {A : Type u} [CommSemiring A] [Algebra R A] {φ : A ->ₐ[R] S} (p : A otimes[R] M)
    {T : Type w} [CommSemiring T] [Algebra R T]
    {B : Type u} [CommSemiring B] [Algebra R B] {ψ : B ->ₐ[R] T} (q : B otimes[R] M)
    (g : A ->ₐ[R] B) (h : S ->ₐ[R] T)

/--
theorem `toFun'_eq_of_diagram` / 定理 `toFun'_eq_of_diagram`

English:
theorem toFun'_eq_of_diagram
  proof: by
  let θ := (quotientKerEquivRangeₐ (R := R) ψ).symm.toAlgHom.comp
    (h'.comp (quotientKerEquivRangeₐ φ).toAlgHom)
  have ht : (h.comp φ.range.val).comp (quotientKerEquivRangeₐ φ).toAlgHom =
      ψ.range.val.comp ((quotientKerEquivRangeₐ ψ).toAlgHom.comp θ) := by
    simp only [θ, ← AlgHom.comp

中文:
定理 toFun'_eq_of_diagram
  证明: by
  let θ := (quotientKerEquivRangeₐ (R := R) ψ).symm.toAlgHom.comp
    (h'.comp (quotientKerEquivRangeₐ φ).toAlgHom)
  have ht : (h.comp φ.range.val).comp (quotientKerEquivRangeₐ φ).toAlgHom =
      ψ.range.val.comp ((quotientKerEquivRangeₐ ψ).toAlgHom.comp θ) := by
    simp only [θ, ← AlgHom.comp

Depends on / 依赖: AlgHom, AlgHom.comp_assoc, comp_assoc, h.comp, range.val, range.val.comp, symm.toAlgHom.comp, toAlgHom, toAlgHom.comp, val_comp_rangeRestrict
-/
theorem toFun'_eq_of_diagram
    (h : S ->ₐ[R] T) (h' : φ.range ->ₐ[R] ψ.range)
    (hh' : ψ.range.val.comp h' = h.comp φ.range.val)
    (hpq : (h'.comp φ.rangeRestrict).toLinearMap.rTensor M p =
      ψ.rangeRestrict.toLinearMap.rTensor M q) :
    (h.comp φ).toLinearMap.rTensor N (f.toFun' A p) =
      ψ.toLinearMap.rTensor N (f.toFun' B q) := by
  let θ := (quotientKerEquivRangeₐ (R := R) ψ).symm.toAlgHom.comp
    (h'.comp (quotientKerEquivRangeₐ φ).toAlgHom)
  have ht : (h.comp φ.range.val).comp (quotientKerEquivRangeₐ φ).toAlgHom =
      ψ.range.val.comp ((quotientKerEquivRangeₐ ψ).toAlgHom.comp θ) := by
    simp only [θ, ← AlgHom.comp_assoc, ← hh']
    simp [AlgHom.comp_assoc]
  rw [← φ.val_comp_rangeRestrict]; rw [← quotientKerEquivRangeₐ_comp_mkₐ φ]; rw [← ψ.val_comp_rangeRestrict]; rw [← quotientKerEquivRangeₐ_comp_mkₐ ψ]; rw [← AlgHom.comp_assoc]; rw [← AlgHom.comp_assoc _]; rw [ht]
  simp only [AlgHom.comp_toLinearMap, rTensor_comp_apply]
  apply congr_arg
  rw [← rTensor_comp_apply]; rw [← AlgHom.comp_toLinearMap]; rw [isCompat_apply']; rw [isCompat_apply']; rw [AlgHom.comp_toLinearMap]; rw [rTensor_comp_apply]; rw [isCompat_apply']
  apply congr_arg
  simp only [θ, ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap, AlgHom.comp_assoc]
  rw [quotientKerEquivRangeₐ_comp_mkₐ]; rw [comp_toLinearMap]; rw [rTensor_comp_apply]; rw [hpq]; rw [← rTensor_comp_apply]; rw [← comp_toLinearMap]; rw [← quotientKerEquivRangeₐ_comp_mkₐ]; rw [← AlgHom.comp_assoc]
  simp

/--
theorem `toFun'_eq_of_inclusion` / 定理 `toFun'_eq_of_inclusion`

English:
theorem toFun'_eq_of_inclusion
  statement: {ψ : B ->ₐ[R] S} (h : φ.range <= ψ.range)
  proof: toFun'_eq_of_diagram f p q (AlgHom.id R S) (Subalgebra.inclusion h) (by ext x; simp) hpq

中文:
定理 toFun'_eq_of_inclusion
  结论: {ψ : B ->ₐ[R] S} (h : φ.range <= ψ.range)
  证明: toFun'_eq_of_diagram f p q (AlgHom.id R S) (Subalgebra.inclusion h) (by ext x; simp) hpq
-/
theorem toFun'_eq_of_inclusion {ψ : B ->ₐ[R] S} (h : φ.range <= ψ.range)
    (hpq : ((Subalgebra.inclusion h).comp
      φ.rangeRestrict).toLinearMap.rTensor M p = ψ.rangeRestrict.toLinearMap.rTensor M q) :
    φ.toLinearMap.rTensor N (f.toFun' A p) = ψ.toLinearMap.rTensor N (f.toFun' B q) :=
  toFun'_eq_of_diagram f p q (AlgHom.id R S) (Subalgebra.inclusion h) (by ext x; simp) hpq

end diagrams

/--
theorem `factorsThrough_toFunLifted_π` / 定理 `factorsThrough_toFunLifted_π`

English:
theorem factorsThrough_toFunLifted_π
  proof: by
  rintro ⟨s, p⟩ ⟨s', p'⟩ h
  simp only [toFunLifted]
  set u := rTensor M (φ R s).rangeRestrict.toLinearMap p with hu
  have uFG : Subalgebra.FG (R := R) (φ R s).range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  set u' := rTensor M (φ R s').rangeRestric

中文:
定理 factorsThrough_toFunLifted_π
  证明: by
  rintro ⟨s, p⟩ ⟨s', p'⟩ h
  simp only [toFunLifted]
  set u := rTensor M (φ R s).rangeRestrict.toLinearMap p with hu
  have uFG : Subalgebra.FG (R := R) (φ R s).range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  set u' := rTensor M (φ R s').rangeRestric

Depends on / 依赖: Algebra, Algebra.FiniteType.out, Algebra.map_top, FiniteType, Subalgebra, Subalgebra.FG, Subalgebra.FG.map, Subalgebra.val, map_top, rTensor, rangeRestrict, rangeRestrict.toLinearMap, toFunLifted, toLinearMap
-/
theorem factorsThrough_toFunLifted_π :
    Function.FactorsThrough (f.toFunLifted S) (π R M S) := by
  rintro ⟨s, p⟩ ⟨s', p'⟩ h
  simp only [toFunLifted]
  set u := rTensor M (φ R s).rangeRestrict.toLinearMap p with hu
  have uFG : Subalgebra.FG (R := R) (φ R s).range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  set u' := rTensor M (φ R s').rangeRestrict.toLinearMap p' with hu'
  have u'FG : Subalgebra.FG (R := R) (φ R s').range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  have huu' : rTensor M (Subalgebra.val _).toLinearMap u =
    rTensor M (Subalgebra.val _).toLinearMap u' := by
    simp only [π] at h
    simp only [hu, hu', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap,
      val_comp_rangeRestrict, h]
  obtain ⟨B, hAB, hA'B, ⟨t, hB⟩, h⟩ :=
    TensorProduct.Algebra.eq_of_fg_of_subtype_eq' (R := R) uFG u'FG huu'
  rw [← range_φ R t]; rw [eq_comm] at hB
  have hAB' : (φ R s).range <= (φ R t).range := le_trans hAB (le_of_eq hB)
  have hA'B' : (φ R s').range <= (φ R t).range := le_trans hA'B (le_of_eq hB)
  have : exists q : MvPolynomial (Fin t.card) R otimes[R] M, rTensor M (toLinearMap (φ R t).rangeRestrict) q =
      rTensor M ((Subalgebra.inclusion (le_of_eq hB)).comp
        (Subalgebra.inclusion hAB)).toLinearMap u :=
    rTensor_surjective _ (rangeRestrict_surjective _) _
  obtain ⟨q, hq⟩ := this
  rw [toFun'_eq_of_inclusion f p q hAB']; rw [toFun'_eq_of_inclusion f p' q hA'B']
  · simp only [hq, comp_toLinearMap, rTensor_comp, LinearMap.comp_apply]
    rw [← hu']; rw [h]
    simp only [← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    rfl
  · simp only [hq, hu, ← LinearMap.comp_apply, comp_toLinearMap, rTensor_comp]
    congr; ext; rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toFun_eq_rTensor_φ_toFun'` / 定理 `toFun_eq_rTensor_φ_toFun'`

English:
theorem toFun_eq_rTensor_φ_toFun'
  statement: {t : S otimes[R] M} {s : Finset S}
  proof: by
  rw [PolynomialLaw.toFun]; rw [← ha]; rw [(factorsThrough_toFunLifted_π f).extend_apply]; rw [toFunLifted]

中文:
定理 toFun_eq_rTensor_φ_toFun'
  结论: {t : S otimes[R] M} {s : Finset S}
  证明: by
  rw [PolynomialLaw.toFun]; rw [← ha]; rw [(factorsThrough_toFunLifted_π f).extend_apply]; rw [toFunLifted]

Depends on / 依赖: PolynomialLaw, PolynomialLaw.toFun, extend_apply, toFunLifted
-/
theorem toFun_eq_rTensor_φ_toFun' {t : S otimes[R] M} {s : Finset S}
    {p : MvPolynomial (Fin s.card) R otimes[R] M} (ha : π R M S (⟨s, p⟩ : lifts R M S) = t) :
    f.toFun S t = (φ R s).toLinearMap.rTensor N (f.toFun' _ p) := by
  rw [PolynomialLaw.toFun]; rw [← ha]; rw [(factorsThrough_toFunLifted_π f).extend_apply]; rw [toFunLifted]

/--
theorem `exists_lift_of_mem_range_rTensor` / 定理 `exists_lift_of_mem_range_rTensor`

English:
theorem exists_lift_of_mem_range_rTensor
  proof: by
  obtain ⟨u, hu⟩ := ht
  suffices h_surj : Function.Surjective ((φ.rangeRestrict.toLinearMap).rTensor M) by
    obtain ⟨p, hp⟩ := h_surj ((Subalgebra.inclusion hφ).toLinearMap.rTensor M u)
    use p
    rw [← hu]; rw [← Subalgebra.val_comp_inclusion hφ]; rw [comp_toLinearMap]; rw [rTensor_comp]; 

中文:
定理 exists_lift_of_mem_range_rTensor
  证明: by
  obtain ⟨u, hu⟩ := ht
  suffices h_surj : Function.Surjective ((φ.rangeRestrict.toLinearMap).rTensor M) by
    obtain ⟨p, hp⟩ := h_surj ((Subalgebra.inclusion hφ).toLinearMap.rTensor M u)
    use p
    rw [← hu]; rw [← Subalgebra.val_comp_inclusion hφ]; rw [comp_toLinearMap]; rw [rTensor_comp]; 

Depends on / 依赖: Function, Function.Surjective, LinearMap, LinearMap.comp_apply, Subalgebra, Subalgebra.inclusion, Subalgebra.val_comp_inclusion, Surjective, comp_apply, comp_toLinearMap, h_surj, inclusion, rTensor, rTensor_comp, rTensor_surjective, rangeRestrict, rangeRestrict.toLinearMap, rangeRestrict_surjective, toLinearMap, toLinearMap.rTensor
-/
theorem exists_lift_of_mem_range_rTensor
    {T : Type*} [CommSemiring T] [Algebra R T]
    (A : Subalgebra R T) {φ : S ->ₐ[R] T} (hφ : A <= φ.range) {t : T otimes[R] M}
    (ht : t in range ((Subalgebra.val A).toLinearMap.rTensor M)) :
    exists s : S otimes[R] M, φ.toLinearMap.rTensor M s = t := by
  obtain ⟨u, hu⟩ := ht
  suffices h_surj : Function.Surjective ((φ.rangeRestrict.toLinearMap).rTensor M) by
    obtain ⟨p, hp⟩ := h_surj ((Subalgebra.inclusion hφ).toLinearMap.rTensor M u)
    use p
    rw [← hu]; rw [← Subalgebra.val_comp_inclusion hφ]; rw [comp_toLinearMap]; rw [rTensor_comp]; rw [LinearMap.comp_apply]; rw [← hp]; rw [← LinearMap.comp_apply]; rw [← rTensor_comp]; rw [← comp_toLinearMap]
    simp
  exact rTensor_surjective M (rangeRestrict_surjective φ)

/--
theorem `π_surjective` / 定理 `π_surjective`

English:
theorem π_surjective
  statement: Function.Surjective (π R M S)
  proof: by
  intro t
  obtain ⟨B : Subalgebra R S, hB : B.FG, ht : t in range _⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨s : Finset S, hs : (PolynomialLaw.φ R s).range = B⟩ := exists_range_φ_eq_of_fg hB
  obtain ⟨p, hp⟩ := exists_lift_of_mem_range_rTensor B (le_of_eq hs.symm) ht
  exact ⟨⟨s, p⟩, h

中文:
定理 π_surjective
  结论: Function.Surjective (π R M S)
  证明: by
  intro t
  obtain ⟨B : Subalgebra R S, hB : B.FG, ht : t in range _⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨s : Finset S, hs : (PolynomialLaw.φ R s).range = B⟩ := exists_range_φ_eq_of_fg hB
  obtain ⟨p, hp⟩ := exists_lift_of_mem_range_rTensor B (le_of_eq hs.symm) ht
  exact ⟨⟨s, p⟩, h

Depends on / 依赖: Algebra, B.FG, Finset, PolynomialLaw, Subalgebra, TensorProduct, TensorProduct.Algebra.exists_of_fg, exists_lift_of_mem_range_rTensor, exists_of_fg, hs.symm, le_of_eq
-/
theorem π_surjective : Function.Surjective (π R M S) := by
  intro t
  obtain ⟨B : Subalgebra R S, hB : B.FG, ht : t in range _⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨s : Finset S, hs : (PolynomialLaw.φ R s).range = B⟩ := exists_range_φ_eq_of_fg hB
  obtain ⟨p, hp⟩ := exists_lift_of_mem_range_rTensor B (le_of_eq hs.symm) ht
  exact ⟨⟨s, p⟩, hp⟩

/--
theorem `exists_lift` / 定理 `exists_lift`

English:
theorem exists_lift
  given: (t : S otimes[R] M)
  statement: exists (n : Nat) (ψ : MvPolynomial (Fin n) R ->ₐ[R] S)
  proof: by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  use s.card, φ R s, p, ha

中文:
定理 exists_lift
  条件: (t : S otimes[R] M)
  结论: 存在 (n : 自然数) (ψ : MvPolynomial (Fin n) R ->ₐ[R] S)
  证明: by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  use s.card, φ R s, p, ha

Depends on / 依赖: s.card
-/
theorem exists_lift (t : S otimes[R] M) : exists (n : Nat) (ψ : MvPolynomial (Fin n) R ->ₐ[R] S)
    (p : MvPolynomial (Fin n) R otimes[R] M), ψ.toLinearMap.rTensor M p = t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  use s.card, φ R s, p, ha

/--
theorem `exists_lift'` / 定理 `exists_lift'`

English:
theorem exists_lift'
  given: (t : S otimes[R] M) (s : S)
  statement: exists (n : Nat) (ψ : MvPolynomial (Fin n) R ->ₐ[R] S)
  proof: by
  obtain ⟨A, hA, ht⟩ := TensorProduct.Algebra.exists_of_fg t
  have hB : Subalgebra.FG (A ⊔ Algebra.adjoin R ({s} : Finset S)) :=
    Subalgebra.FG.sup hA (Subalgebra.fg_adjoin_finset _)
  obtain ⟨gen, hgen⟩ := exists_range_φ_eq_of_fg hB
  have hAB : A <= A ⊔ Algebra.adjoin R ({s} : Finset S) := 

中文:
定理 exists_lift'
  条件: (t : S otimes[R] M) (s : S)
  结论: 存在 (n : 自然数) (ψ : MvPolynomial (Fin n) R ->ₐ[R] S)
  证明: by
  obtain ⟨A, hA, ht⟩ := TensorProduct.Algebra.exists_of_fg t
  have hB : Subalgebra.FG (A ⊔ Algebra.adjoin R ({s} : Finset S)) :=
    Subalgebra.FG.sup hA (Subalgebra.fg_adjoin_finset _)
  obtain ⟨gen, hgen⟩ := exists_range_φ_eq_of_fg hB
  have hAB : A <= A ⊔ Algebra.adjoin R ({s} : Finset S) := 

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, Finset, Finset.coe_singleton, Set.sup_eq_un, Subalgebra, Subalgebra.FG, Subalgebra.FG.sup, Subalgebra.fg_adjoin_finset, TensorProduct, TensorProduct.Algebra.exists_of_fg, adjoin, coe_singleton, exists_lift_of_mem_range_rTensor, exists_of_fg, fg_adjoin_finset, le_sup_left, subset_adjoin, sup_eq_un
-/
theorem exists_lift' (t : S otimes[R] M) (s : S) : exists (n : Nat) (ψ : MvPolynomial (Fin n) R ->ₐ[R] S)
    (p : MvPolynomial (Fin n) R otimes[R] M) (q : MvPolynomial (Fin n) R),
      ψ.toLinearMap.rTensor M p = t ∧ ψ q = s := by
  obtain ⟨A, hA, ht⟩ := TensorProduct.Algebra.exists_of_fg t
  have hB : Subalgebra.FG (A ⊔ Algebra.adjoin R ({s} : Finset S)) :=
    Subalgebra.FG.sup hA (Subalgebra.fg_adjoin_finset _)
  obtain ⟨gen, hgen⟩ := exists_range_φ_eq_of_fg hB
  have hAB : A <= A ⊔ Algebra.adjoin R ({s} : Finset S) := le_sup_left
  rw [← hgen] at hAB
  obtain ⟨p, hp⟩ := exists_lift_of_mem_range_rTensor _ hAB ht
  have hs : s in (φ R gen).range := by
    rw [hgen]
    apply Algebra.subset_adjoin
    simp only [Finset.coe_singleton, Set.sup_eq_union, Set.mem_union, SetLike.mem_coe]
    exact Or.inr (Algebra.subset_adjoin rfl)
  use gen.card, φ R gen, p, hs.choose, hp, hs.choose_spec

/-- For semirings in the universe `u`, `PolynomialLaw.toFun` coincides
with `PolynomialLaw.toFun'`. -/
@[simp]
/--
theorem `toFun'_eq_toFun` / 定理 `toFun'_eq_toFun`

English:
theorem toFun'_eq_toFun
  given: (S : Type u) [CommSemiring S] [Algebra R S]
  proof: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [f.toFun_eq_rTensor_φ_toFun' ha, f.isCompat_apply']
  exact congr_arg _ ha.symm

中文:
定理 toFun'_eq_toFun
  条件: (S : 类型u) [CommSemiring S] [Algebra R S]
  证明: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [f.toFun_eq_rTensor_φ_toFun' ha, f.isCompat_apply']
  exact congr_arg _ ha.symm

Depends on / 依赖: Completion, v.Completion
-/
theorem toFun'_eq_toFun (S : Type u) [CommSemiring S] [Algebra R S] :
    f.toFun' S = f.toFun S := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [f.toFun_eq_rTensor_φ_toFun' ha, f.isCompat_apply']
  exact congr_arg _ ha.symm

/--
theorem `isCompat_apply` / 定理 `isCompat_apply`

English:
theorem isCompat_apply
  given: {T : Type w} [CommSemiring T] [Algebra R T] (h : S ->ₐ[R] T) (t : S otimes[R] M)
  proof: by
  classical
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  let s' := s.image h
  let h' : (φ R s).range ->ₐ[R] (φ R s').range :=
    (h.comp (Subalgebra.val _)).codRestrict (φ R s').range (by
    rintro ⟨x, hx⟩
    simp only [range_φ] at hx ⊢
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Functio

中文:
定理 isCompat_apply
  条件: {T : Type w} [CommSemiring T] [Algebra R T] (h : S ->ₐ[R] T) (t : S otimes[R] M)
  证明: by
  classical
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  let s' := s.image h
  let h' : (φ R s).range ->ₐ[R] (φ R s').range :=
    (h.comp (Subalgebra.val _)).codRestrict (φ R s').range (by
    rintro ⟨x, hx⟩
    simp only [range_φ] at hx ⊢
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Functio

Depends on / 依赖: AlgHom, AlgHom.coe_comp, Algebra, Algebra.adjoin_image, Finset, Finset.coe_image, Finset.mem_image_of_mem, Function, Function.comp_apply, Subalgebra, Subalgebra.coe_val, Subalgebra.val, adjoin_image, classical, codRestrict, coe_comp, coe_image, coe_val, comp_apply, eq_h_comp
-/
theorem isCompat_apply {T : Type w} [CommSemiring T] [Algebra R T] (h : S ->ₐ[R] T) (t : S otimes[R] M) :
    rTensor N h.toLinearMap (f.toFun S t) = f.toFun T (rTensor M h.toLinearMap t) := by
  classical
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  let s' := s.image h
  let h' : (φ R s).range ->ₐ[R] (φ R s').range :=
    (h.comp (Subalgebra.val _)).codRestrict (φ R s').range (by
    rintro ⟨x, hx⟩
    simp only [range_φ] at hx ⊢
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply, Finset.coe_image,
      Algebra.adjoin_image, s']
    exact ⟨x, hx, rfl⟩)
  let j : Fin s.card -> Fin s'.card :=
    (s'.equivFin) ∘ (fun ⟨x, hx⟩ => ⟨h x, Finset.mem_image_of_mem h hx⟩) ∘ (s.equivFin).symm
  have eq_h_comp : (φ R s').comp (rename j) = h.comp (φ R s) := by
    ext p
    simp only [φ, AlgHom.comp_apply, aeval_rename, comp_aeval]
    congr
    ext n
    simp only [Function.comp_apply, Equiv.symm_apply_apply, j]
  let p' := rTensor M (rename j).toLinearMap p
  have ha' : π R M T (⟨s', p'⟩ : lifts R M T) = rTensor M h.toLinearMap t := by
    simp only [← ha, π, p', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap, eq_h_comp]
  rw [toFun_eq_rTensor_φ_toFun' f ha]; rw [toFun_eq_rTensor_φ_toFun' f ha']; rw [← LinearMap.comp_apply]; rw [← rTensor_comp]; rw [← comp_toLinearMap]
  apply toFun'_eq_of_diagram f p p' h h'
  · simp only [val_comp_codRestrict, h']
  · simp only [p', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    congr
    ext n
    simp only [AlgHom.coe_comp, Function.comp_apply, coe_codRestrict,
      Subalgebra.coe_val, rename_X, h', j]
    simp only [φ, aeval_X, Equiv.symm_apply_apply]

/--
theorem `isCompat` / 定理 `isCompat`

English:
theorem isCompat
  given: {T : Type w} [CommSemiring T] [Algebra R T] (h : S ->ₐ[R] T)
  proof: by
  ext t
  simp only [Function.comp_apply, PolynomialLaw.isCompat_apply]

中文:
定理 isCompat
  条件: {T : Type w} [CommSemiring T] [Algebra R T] (h : S ->ₐ[R] T)
  证明: by
  ext t
  simp only [Function.comp_apply, PolynomialLaw.isCompat_apply]

Depends on / 依赖: Function, Function.comp_apply, PolynomialLaw, PolynomialLaw.isCompat_apply, comp_apply, isCompat_apply
-/
theorem isCompat {T : Type w} [CommSemiring T] [Algebra R T] (h : S ->ₐ[R] T) :
    h.toLinearMap.rTensor N ∘ f.toFun S = f.toFun T ∘ h.toLinearMap.rTensor M := by
  ext t
  simp only [Function.comp_apply, PolynomialLaw.isCompat_apply]

end Lift

section Module

variable
  {R : Type u} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
  (r a b : R) (f g : M ->ₚₗ[R] N)
  {S : Type*} [CommSemiring S] [Algebra R S]

/-- Extension of `PolynomialLaw.zero_def` -/
@[simp]
/--
theorem `toFun_zero` / 定理 `toFun_zero`

English:
theorem toFun_zero
  statement: (0 : M ->ₚₗ[R] N).toFun S = 0
  proof: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, zero_def, Pi.zero_apply, _root_.map_zero]

中文:
定理 toFun_zero
  结论: (0 : M ->ₚₗ[R] N).toFun S = 0
  证明: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, zero_def, Pi.zero_apply, _root_.map_zero]

Depends on / 依赖: Pi.zero_apply, _root_, _root_.map_zero, map_zero, zero_apply, zero_def
-/
theorem toFun_zero : (0 : M ->ₚₗ[R] N).toFun S = 0 := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, zero_def, Pi.zero_apply, _root_.map_zero]

/-- Extension of `PolynomialLaw.add_def_apply` -/
@[simp]
/--
theorem `toFun_add_apply` / 定理 `toFun_add_apply`

English:
theorem toFun_add_apply
  given: (t : S otimes[R] M)
  proof: by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [Pi.add_apply, toFun_eq_rTensor_φ_toFun' _ ha, add_def, map_add]

中文:
定理 toFun_add_apply
  条件: (t : S otimes[R] M)
  证明: by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [Pi.add_apply, toFun_eq_rTensor_φ_toFun' _ ha, add_def, map_add]

Depends on / 依赖: Pi.add_apply, add_apply, add_def, map_add
-/
theorem toFun_add_apply (t : S otimes[R] M) :
    (f + g).toFun S t = f.toFun S t + g.toFun S t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [Pi.add_apply, toFun_eq_rTensor_φ_toFun' _ ha, add_def, map_add]

/-- Extension of `PolynomialLaw.add_def` -/
@[simp]
/--
theorem `toFun_add` / 定理 `toFun_add`

English:
theorem toFun_add
  proof: by
  ext t
  simp only [Pi.add_apply, toFun_add_apply]

@[simp]

中文:
定理 toFun_add
  证明: by
  ext t
  simp only [Pi.add_apply, toFun_add_apply]

@[simp]

Depends on / 依赖: Pi.add_apply, add_apply, toFun_add_apply
-/
theorem toFun_add :
    (f + g).toFun S = f.toFun S + g.toFun S := by
  ext t
  simp only [Pi.add_apply, toFun_add_apply]

@[simp]
/--
theorem `toFun_neg` / 定理 `toFun_neg`

English:
theorem toFun_neg
  statement: {R : Type u} [CommRing R]
  proof: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, neg_def, Pi.smul_apply, map_smul]

中文:
定理 toFun_neg
  结论: {R : 类型u} [CommRing R]
  证明: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, neg_def, Pi.smul_apply, map_smul]

Depends on / 依赖: Pi.smul_apply, map_smul, neg_def, smul_apply
-/
theorem toFun_neg {R : Type u} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : M ->ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] :
    (-f).toFun S = (-1 : R) • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, neg_def, Pi.smul_apply, map_smul]

variable (S) in
/-- Extension of `PolynomialLaw.smul_def` -/
@[simp]
/--
theorem `toFun_smul` / 定理 `toFun_smul`

English:
theorem toFun_smul
  statement: (r • f).toFun S = r • (f.toFun S)
  proof: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, smul_def, Pi.smul_apply, map_smul]

中文:
定理 toFun_smul
  结论: (r • f).toFun S = r • (f.toFun S)
  证明: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, smul_def, Pi.smul_apply, map_smul]

Depends on / 依赖: Pi.smul_apply, map_smul, smul_apply, smul_def
-/
theorem toFun_smul : (r • f).toFun S = r • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_rTensor_φ_toFun' _ ha, smul_def, Pi.smul_apply, map_smul]

end Module

section ground

variable {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M ->ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S]

/--
theorem `one_tmul_ground` / 定理 `one_tmul_ground`

English:
theorem one_tmul_ground
  given: (x : M)
  proof: by
  simp only [ground, toFun'_eq_toFun]
  convert! f.isCompat_apply (Algebra.ofId R S) (1 otimesₜ[R] x)
  · simp only [Function.comp_apply, TensorProduct.lid_symm_apply, TensorProduct.includeRight_lid]
    congr
  · rw [rTensor_tmul, toLinearMap_apply, _root_.map_one]

中文:
定理 one_tmul_ground
  条件: (x : M)
  证明: by
  simp only [ground, toFun'_eq_toFun]
  convert! f.isCompat_apply (Algebra.ofId R S) (1 otimesₜ[R] x)
  · simp only [Function.comp_apply, TensorProduct.lid_symm_apply, TensorProduct.includeRight_lid]
    congr
  · rw [rTensor_tmul, toLinearMap_apply, _root_.map_one]

Depends on / 依赖: Algebra, Algebra.ofId, Function, Function.comp_apply, TensorProduct, TensorProduct.includeRight_lid, TensorProduct.lid_symm_apply, _eq_toFun, _root_, _root_.map_one, comp_apply, convert, f.isCompat_apply, ground, includeRight_lid, isCompat_apply, lid_symm_apply, map_one, rTensor_tmul, toLinearMap_apply
-/
theorem one_tmul_ground (x : M) :
    1 otimesₜ f.ground x = f.toFun S (1 otimesₜ x) := by
  simp only [ground, toFun'_eq_toFun]
  convert! f.isCompat_apply (Algebra.ofId R S) (1 otimesₜ[R] x)
  · simp only [Function.comp_apply, TensorProduct.lid_symm_apply, TensorProduct.includeRight_lid]
    congr
  · rw [rTensor_tmul, toLinearMap_apply, _root_.map_one]

end ground

section Comp

variable {R : Type u} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
  {P : Type*} [AddCommMonoid P] [Module R P]
  {Q : Type*} [AddCommMonoid Q] [Module R Q]
  (f : M ->ₚₗ[R] N) (g : N ->ₚₗ[R] P) (h : P ->ₚₗ[R] Q)

/-- Extension of `MvPolynomial.comp_toFun'` -/
@[simp]
/--
theorem `toFun_comp` / 定理 `toFun_comp`

English:
theorem toFun_comp
  given: (S : Type*) [CommSemiring S] [Algebra R S]
  proof: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  have hb : PolynomialLaw.π R N S ⟨s, f.toFun' _ p⟩ = f.toFun S t := by
    simp only [toFun_eq_rTensor_φ_toFun' _ ha, π]
  rw [Function.comp_apply]; rw [toFun_eq_rTensor_φ_toFun' _ hb]; rw [toFun_eq_rTensor_φ_toFun' _ ha]; rw [comp_toFun']; rw [Fun

中文:
定理 toFun_comp
  条件: (S : 类型) [CommSemiring S] [Algebra R S]
  证明: by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  have hb : PolynomialLaw.π R N S ⟨s, f.toFun' _ p⟩ = f.toFun S t := by
    simp only [toFun_eq_rTensor_φ_toFun' _ ha, π]
  rw [Function.comp_apply]; rw [toFun_eq_rTensor_φ_toFun' _ hb]; rw [toFun_eq_rTensor_φ_toFun' _ ha]; rw [comp_toFun']; rw [Fun

Depends on / 依赖: Function, Function.comp_apply, PolynomialLaw, comp_apply, comp_toFun, f.toFun
-/
theorem toFun_comp (S : Type*) [CommSemiring S] [Algebra R S] :
    (g.comp f).toFun S = (g.toFun S).comp (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  have hb : PolynomialLaw.π R N S ⟨s, f.toFun' _ p⟩ = f.toFun S t := by
    simp only [toFun_eq_rTensor_φ_toFun' _ ha, π]
  rw [Function.comp_apply]; rw [toFun_eq_rTensor_φ_toFun' _ hb]; rw [toFun_eq_rTensor_φ_toFun' _ ha]; rw [comp_toFun']; rw [Function.comp_apply]

/--
theorem `toFun_comp_apply` / 定理 `toFun_comp_apply`

English:
theorem toFun_comp_apply
  given: (S : Type*) [CommSemiring S] [Algebra R S] (m : S otimes[R] M)
  proof: by
  simp only [toFun_comp, Function.comp_apply]

中文:
定理 toFun_comp_apply
  条件: (S : 类型) [CommSemiring S] [Algebra R S] (m : S otimes[R] M)
  证明: by
  simp only [toFun_comp, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, toFun_comp
-/
theorem toFun_comp_apply (S : Type*) [CommSemiring S] [Algebra R S] (m : S otimes[R] M) :
    (g.comp f).toFun S m = (g.toFun S) (f.toFun S m) := by
  simp only [toFun_comp, Function.comp_apply]

end Comp

end Universe

end PolynomialLaw
