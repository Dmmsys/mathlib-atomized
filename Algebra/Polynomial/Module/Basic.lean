/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Polynomial module

In this file, we define the polynomial module for an `R`-module `M`, i.e. the `R[X]`-module `M[X]`.

This is defined as a type alias `PolynomialModule R M := ℕ →₀ M`, since there might be different
module structures on `ℕ →₀ M` of interest. See the docstring of `PolynomialModule` for details.
-/

@[expose] public noncomputable section
universe u v
open Polynomial

/-- The `R[X]`-module `M[X]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `M[X]` when `M` is a ring.

We require all the module instances `Module S (PolynomialModule R M)` to factor through `R` except
`Module R[X] (PolynomialModule R M)`.
In this constraint, we have the following instances for example :
- `R` acts on `PolynomialModule R R[X]`
- `R[X]` acts on `PolynomialModule R R[X]` as `R[Y]` acting on `R[X][Y]`
- `R` acts on `PolynomialModule R[X] R[X]`
- `R[X]` acts on `PolynomialModule R[X] R[X]` as `R[X]` acting on `R[X][Y]`
- `R[X][X]` acts on `PolynomialModule R[X] R[X]` as `R[X][Y]` acting on itself

This is also the reason why `R` is included in the alias, or else there will be two different
instances of `Module R[X] (PolynomialModule R[X])`.

See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2315065.20polynomial.20modules
for the full discussion.
-/
@[nolint unusedArguments]
/--
Definition of `PolynomialModule` / `PolynomialModule` 的定义

English:
structure PolynomialModule
  parameters: (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  axioms and operations (2):
    - ofCoeff((R)) : :
    - coeff : Nat ->₀ M

中文:
结构 多项式模
  参数: (R M : 类型) [交换环 R] [加法交换群 M] [模 R M]
  公理与运算 (2 个):
    - ofCoeff((R)) : :
    - coeff : 自然数 ->₀ M
-/
structure PolynomialModule (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  /-- Construct an element of the polynomial module `M[[]]` from its coefficients `ℕ →₀ M`. -/
  ofCoeff (R) ::
  /-- The coefficients `ℕ →₀ M` of an element of the additive monoid algebra `M[X]`. -/
  coeff : Nat ->₀ M

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

namespace PolynomialModule
variable {x y : PolynomialModule R M} {r r₁ r₂ : R} {m m' m₁ m₂ m₁' m₂' : M}

/--
lemma `coeff_ofCoeff` / 引理 `coeff_ofCoeff`

English:
lemma coeff_ofCoeff
  given: (x : Nat ->₀ M)
  statement: (ofCoeff R x).coeff = x
  proof: rfl

中文:
引理 coeff_ofCoeff
  条件: (x : 自然数 ->₀ M)
  结论: (ofCoeff R x).coeff = x
  证明: rfl
-/
lemma coeff_ofCoeff (x : Nat ->₀ M) : (ofCoeff R x).coeff = x := rfl
/--
lemma `ofCoeff_coeff` / 引理 `ofCoeff_coeff`

English:
lemma ofCoeff_coeff
  given: (x : PolynomialModule R M)
  statement: ofCoeff R x.coeff = x
  proof: rfl

中文:
引理 ofCoeff_coeff
  条件: (x : 多项式模 R M)
  结论: ofCoeff R x.coeff = x
  证明: rfl
-/
lemma ofCoeff_coeff (x : PolynomialModule R M) : ofCoeff R x.coeff = x := rfl

variable (R) in
/-- `PolynomialModule.coeff` as an equiv. -/
@[simps! apply symm_apply]
/--
Definition of `coeffEquiv` / `coeffEquiv` 的定义

English:
definition coeffEquiv
  signature: : PolynomialModule R M ≃ (Nat ->₀ M) where
  body: coeff
  invFun := ofCoeff R
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 coeffEquiv
  签名: : 多项式模 R M ≃ (自然数 ->₀ M) where
  定义体: coeff
  invFun := ofCoeff R
  left_inv _ := rfl
  right_inv _ := rfl
-/
def coeffEquiv : PolynomialModule R M ≃ (Nat ->₀ M) where
  toFun := coeff
  invFun := ofCoeff R
  left_inv _ := rfl
  right_inv _ := rfl

/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {P : PolynomialModule R M -> Prop}
  statement: (forall p, P p) ↔ forall q, P (ofCoeff R q)
  proof: (coeffEquiv R).forall_congr_left

中文:
引理 «对任意»
  条件: {P : 多项式模 R M -> 命题}
  结论: (对任意 p, P p) ↔ 对任意 q, P (ofCoeff R q)
  证明: (coeffEquiv R).forall_congr_left
-/
lemma «forall» {P : PolynomialModule R M -> Prop} : (forall p, P p) ↔ forall q, P (ofCoeff R q) :=
  (coeffEquiv R).forall_congr_left

/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {P : PolynomialModule R M -> Prop}
  statement: (exists p, P p) ↔ exists q, P (ofCoeff R q)
  proof: (coeffEquiv R).exists_congr_left

中文:
引理 «存在»
  条件: {P : 多项式模 R M -> 命题}
  结论: (存在 p, P p) ↔ 存在 q, P (ofCoeff R q)
  证明: (coeffEquiv R).exists_congr_left
-/
lemma «exists» {P : PolynomialModule R M -> Prop} : (exists p, P p) ↔ exists q, P (ofCoeff R q) :=
  (coeffEquiv R).exists_congr_left

/--
lemma `coeff_injective` / 引理 `coeff_injective`

English:
lemma coeff_injective
  statement: (coeff : PolynomialModule R M -> Nat ->₀ M).Injective
  proof: (coeffEquiv R).injective

中文:
引理 coeff_injective
  结论: (coeff : 多项式模 R M -> 自然数 ->₀ M).单射
  证明: (coeffEquiv R).injective

Depends on / 依赖: coeffEquiv, injective
-/
lemma coeff_injective : (coeff : PolynomialModule R M -> Nat ->₀ M).Injective :=
  (coeffEquiv R).injective

/--
lemma `ofCoeff_injective` / 引理 `ofCoeff_injective`

English:
lemma ofCoeff_injective
  statement: (ofCoeff R : (Nat ->₀ M) -> PolynomialModule R M).Injective
  proof: (coeffEquiv R).symm.injective

@[simp]

中文:
引理 ofCoeff_injective
  结论: (ofCoeff R : (自然数 ->₀ M) -> 多项式模 R M).单射
  证明: (coeffEquiv R).symm.injective

@[simp]

Depends on / 依赖: coeffEquiv, injective, symm.injective
-/
lemma ofCoeff_injective : (ofCoeff R : (Nat ->₀ M) -> PolynomialModule R M).Injective :=
  (coeffEquiv R).symm.injective

@[simp]
/--
lemma `coeff_inj` / 引理 `coeff_inj`

English:
lemma coeff_inj
  statement: x.coeff = y.coeff ↔ x = y
  proof: coeff_injective.eq_iff

中文:
引理 coeff_inj
  结论: x.coeff = y.coeff ↔ x = y
  证明: coeff_injective.eq_iff

Depends on / 依赖: coeff_injective, coeff_injective.eq_iff, eq_iff
-/
lemma coeff_inj : x.coeff = y.coeff ↔ x = y := coeff_injective.eq_iff

/--
lemma `ofCoeff_inj` / 引理 `ofCoeff_inj`

English:
lemma ofCoeff_inj
  given: {x y : Nat ->₀ M}
  statement: ofCoeff R x = ofCoeff R y ↔ x = y
  proof: ofCoeff_injective.eq_iff

@[ext] alias ⟨ext, _⟩ := coeff_inj

中文:
引理 ofCoeff_inj
  条件: {x y : 自然数 ->₀ M}
  结论: ofCoeff R x = ofCoeff R y ↔ x = y
  证明: ofCoeff_injective.eq_iff

@[ext] alias ⟨ext, _⟩ := coeff_inj

Depends on / 依赖: eq_iff, ofCoeff_injective, ofCoeff_injective.eq_iff
-/
lemma ofCoeff_inj {x y : Nat ->₀ M} : ofCoeff R x = ofCoeff R y ↔ x = y := ofCoeff_injective.eq_iff

@[ext] alias ⟨ext, _⟩ := coeff_inj

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (PolynomialModule R M)
  body: fast_instance% (coeffEquiv R).inhabited

中文:
实例 instInhabited
  签名: : 可居 (多项式模 R M)
  定义体: fast_instance% (coeffEquiv R).inhabited

Depends on / 依赖: coeffEquiv, fast_instance, inhabited
-/
instance instInhabited : Inhabited (PolynomialModule R M) := fast_instance% (coeffEquiv R).inhabited

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nontrivial M]
  body: (coeffEquiv R).nontrivial

中文:
实例 instNontrivial
  签名: [非平凡 M]
  定义体: (coeffEquiv R).nontrivial

Depends on / 依赖: coeffEquiv, nontrivial
-/
instance instNontrivial [Nontrivial M] : Nontrivial (PolynomialModule R M) :=
  (coeffEquiv R).nontrivial

/--
Instance `instUnique` / 实例 `instUnique`

English:
instance instUnique
  signature: [Subsingleton M]
  body: fast_instance%
  (coeffEquiv R).unique

中文:
实例 instUnique
  签名: [子单例 M]
  定义体: fast_instance%
  (coeffEquiv R).unique

Depends on / 依赖: fast_instance
-/
instance instUnique [Subsingleton M] : Unique (PolynomialModule R M) := fast_instance%
  (coeffEquiv R).unique

/--
Instance `instDecidableEq` / 实例 `instDecidableEq`

English:
instance instDecidableEq
  signature: [DecidableEq M]
  body: (coeffEquiv R).decidableEq

中文:
实例 instDecidableEq
  签名: [DecidableEq M]
  定义体: (coeffEquiv R).decidableEq

Depends on / 依赖: coeffEquiv, decidableEq
-/
instance instDecidableEq [DecidableEq M] : DecidableEq (PolynomialModule R M) :=
  (coeffEquiv R).decidableEq

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (PolynomialModule R M)
  body: fast_instance%
  (coeffEquiv R).addCommGroup

中文:
实例 instAddCommGroup
  签名: : 加法交换群 (多项式模 R M)
  定义体: fast_instance%
  (coeffEquiv R).addCommGroup

Depends on / 依赖: fast_instance
-/
instance instAddCommGroup : AddCommGroup (PolynomialModule R M) := fast_instance%
  (coeffEquiv R).addCommGroup

/-- `PolynomialModule.coeff` as an `AddEquiv`. -/
@[simps! apply symm_apply]
/--
Definition of `coeffAddEquiv` / `coeffAddEquiv` 的定义

English:
definition coeffAddEquiv
  signature: : PolynomialModule R M ≃+ (Nat ->₀ M)
  body: (coeffEquiv R).addEquiv

中文:
定义 coeffAddEquiv
  签名: : 多项式模 R M ≃+ (自然数 ->₀ M)
  定义体: (coeffEquiv R).addEquiv

Depends on / 依赖: addEquiv, coeffEquiv
-/
def coeffAddEquiv : PolynomialModule R M ≃+ (Nat ->₀ M) := (coeffEquiv R).addEquiv

/--
lemma `coeff_zero` / 引理 `coeff_zero`

English:
lemma coeff_zero
  statement: coeff (0 : PolynomialModule R M) = 0
  proof: rfl

中文:
引理 coeff_zero
  结论: coeff (0 : 多项式模 R M) = 0
  证明: rfl
-/
@[simp] lemma coeff_zero : coeff (0 : PolynomialModule R M) = 0 := rfl
/--
lemma `ofCoeff_zero` / 引理 `ofCoeff_zero`

English:
lemma ofCoeff_zero
  statement: (ofCoeff R 0 : PolynomialModule R M) = 0
  proof: rfl

中文:
引理 ofCoeff_zero
  结论: (ofCoeff R 0 : 多项式模 R M) = 0
  证明: rfl
-/
@[simp] lemma ofCoeff_zero : (ofCoeff R 0 : PolynomialModule R M) = 0 := rfl
/--
lemma `coeff_eq_zero` / 引理 `coeff_eq_zero`

English:
lemma coeff_eq_zero
  statement: coeff x = 0 ↔ x = 0
  proof: coeff_inj

中文:
引理 coeff_eq_zero
  结论: coeff x = 0 ↔ x = 0
  证明: coeff_inj
-/
@[simp] lemma coeff_eq_zero : coeff x = 0 ↔ x = 0 := coeff_inj
/--
lemma `ofCoeff_eq_zero` / 引理 `ofCoeff_eq_zero`

English:
lemma ofCoeff_eq_zero
  given: {x : Nat ->₀ M}
  statement: ofCoeff R x = 0 ↔ x = 0
  proof: ofCoeff_inj

中文:
引理 ofCoeff_eq_zero
  条件: {x : 自然数 ->₀ M}
  结论: ofCoeff R x = 0 ↔ x = 0
  证明: ofCoeff_inj
-/
@[simp] lemma ofCoeff_eq_zero {x : Nat ->₀ M} : ofCoeff R x = 0 ↔ x = 0 :=
  ofCoeff_inj

/--
lemma `coeff_add` / 引理 `coeff_add`

English:
lemma coeff_add
  given: (x y : PolynomialModule R M)
  statement: coeff (x + y) = coeff x + coeff y
  proof: rfl

中文:
引理 coeff_add
  条件: (x y : 多项式模 R M)
  结论: coeff (x + y) = coeff x + coeff y
  证明: rfl
-/
@[simp] lemma coeff_add (x y : PolynomialModule R M) : coeff (x + y) = coeff x + coeff y := rfl
/--
lemma `ofCoeff_add` / 引理 `ofCoeff_add`

English:
lemma ofCoeff_add
  given: (x y : Nat ->₀ M)
  statement: ofCoeff R (x + y) = ofCoeff R x + ofCoeff R y
  proof: rfl

@[simp]

中文:
引理 ofCoeff_add
  条件: (x y : 自然数 ->₀ M)
  结论: ofCoeff R (x + y) = ofCoeff R x + ofCoeff R y
  证明: rfl

@[simp]
-/
@[simp] lemma ofCoeff_add (x y : Nat ->₀ M) : ofCoeff R (x + y) = ofCoeff R x + ofCoeff R y := rfl

@[simp]
/--
lemma `coeff_sum` / 引理 `coeff_sum`

English:
lemma coeff_sum
  given: (s : Finset ι) (f : ι -> PolynomialModule R M)
  proof: map_sum coeffAddEquiv ..

@[simp]

中文:
引理 coeff_sum
  条件: (s : 有限集 ι) (f : ι -> 多项式模 R M)
  证明: map_sum coeffAddEquiv ..

@[simp]

Depends on / 依赖: coeffAddEquiv, map_sum
-/
lemma coeff_sum (s : Finset ι) (f : ι -> PolynomialModule R M) :
    coeff (∑ i in s, f i) = ∑ i in s, coeff (f i) := map_sum coeffAddEquiv ..

@[simp]
/--
lemma `ofCoeff_sum` / 引理 `ofCoeff_sum`

English:
lemma ofCoeff_sum
  given: (s : Finset ι) (f : ι -> Nat ->₀ M)
  proof: map_sum coeffAddEquiv.symm ..

@[simp]

中文:
引理 ofCoeff_sum
  条件: (s : 有限集 ι) (f : ι -> 自然数 ->₀ M)
  证明: map_sum coeffAddEquiv.symm ..

@[simp]

Depends on / 依赖: coeffAddEquiv, coeffAddEquiv.symm, map_sum
-/
lemma ofCoeff_sum (s : Finset ι) (f : ι -> Nat ->₀ M) :
    ofCoeff R (∑ i in s, f i) = ∑ i in s, ofCoeff R (f i) := map_sum coeffAddEquiv.symm ..

@[simp]
/--
lemma `coeff_finsuppSum` / 引理 `coeff_finsuppSum`

English:
lemma coeff_finsuppSum
  given: [AddCommMonoid N] (f : ι ->₀ N) (g : ι -> N -> PolynomialModule R M)
  proof: map_finsuppSum coeffAddEquiv ..

@[simp]

中文:
引理 coeff_finsuppSum
  条件: [加法交换幺半群 N] (f : ι ->₀ N) (g : ι -> N -> 多项式模 R M)
  证明: map_finsuppSum coeffAddEquiv ..

@[simp]

Depends on / 依赖: coeffAddEquiv, map_finsuppSum
-/
lemma coeff_finsuppSum [AddCommMonoid N] (f : ι ->₀ N) (g : ι -> N -> PolynomialModule R M) :
    coeff (f.sum g) = f.sum (fun i n => coeff (g i n)) := map_finsuppSum coeffAddEquiv ..

@[simp]
/--
lemma `ofCoeff_finsuppSum` / 引理 `ofCoeff_finsuppSum`

English:
lemma ofCoeff_finsuppSum
  given: [AddCommMonoid N] (f : ι ->₀ N) (g : ι -> N -> Nat ->₀ M)
  proof: map_finsuppSum coeffAddEquiv.symm ..

中文:
引理 ofCoeff_finsuppSum
  条件: [加法交换幺半群 N] (f : ι ->₀ N) (g : ι -> N -> 自然数 ->₀ M)
  证明: map_finsuppSum coeffAddEquiv.symm ..

Depends on / 依赖: coeffAddEquiv, coeffAddEquiv.symm, map_finsuppSum
-/
lemma ofCoeff_finsuppSum [AddCommMonoid N] (f : ι ->₀ N) (g : ι -> N -> Nat ->₀ M) :
    ofCoeff R (f.sum g) = f.sum (fun i n => ofCoeff R (g i n)) :=
  map_finsuppSum coeffAddEquiv.symm ..

variable (R) in
/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (n : Nat) (m : M)
  body: .ofCoeff R .single n m

中文:
定义 single
  签名: (n : 自然数) (m : M)
  定义体: .ofCoeff R .single n m

Depends on / 依赖: ofCoeff, single
-/
def single (n : Nat) (m : M) : PolynomialModule R M := .ofCoeff R .single n m

/--
lemma `coeff_single` / 引理 `coeff_single`

English:
lemma coeff_single
  given: (n : Nat) (m : M)
  statement: (single R n m).coeff = .single n m
  proof: rfl

中文:
引理 coeff_single
  条件: (n : 自然数) (m : M)
  结论: (single R n m).coeff = .single n m
  证明: rfl
-/
@[simp] lemma coeff_single (n : Nat) (m : M) : (single R n m).coeff = .single n m := rfl
/--
lemma `ofCoeff_single` / 引理 `ofCoeff_single`

English:
lemma ofCoeff_single
  given: (n : Nat) (m : M)
  statement: ofCoeff R (.single n m) = single R n m
  proof: rfl

@[deprecated (since := "2026-06-18")] alias single_apply := coeff_single

中文:
引理 ofCoeff_single
  条件: (n : 自然数) (m : M)
  结论: ofCoeff R (.single n m) = single R n m
  证明: rfl

@[deprecated (since := "2026-06-18")] alias single_apply := coeff_single
-/
@[simp] lemma ofCoeff_single (n : Nat) (m : M) : ofCoeff R (.single n m) = single R n m := rfl

@[deprecated (since := "2026-06-18")] alias single_apply := coeff_single

/--
lemma `single_zero` / 引理 `single_zero`

English:
lemma single_zero
  given: (n : Nat)
  statement: single R n (0 : M) = 0
  proof: by simp [single]

@[simp]

中文:
引理 single_zero
  条件: (n : 自然数)
  结论: single R n (0 : M) = 0
  证明: by simp [single]

@[simp]
-/
@[simp] lemma single_zero (n : Nat) : single R n (0 : M) = 0 := by simp [single]

@[simp]
/--
lemma `single_add` / 引理 `single_add`

English:
lemma single_add
  given: (n : Nat) (m₁ m₂ : M)
  proof: by ext; simp

中文:
引理 single_add
  条件: (n : 自然数) (m₁ m₂ : M)
  证明: by ext; simp
-/
lemma single_add (n : Nat) (m₁ m₂ : M) :
    single R n (m₁ + m₂) = single R n m₁ + single R n m₂ := by ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module S (PolynomialModule R M)
  body: (coeffEquiv R).module _

中文:
实例 :
  签名: 模 S (多项式模 R M)
  定义体: (coeffEquiv R).module _

Depends on / 依赖: coeffEquiv, module
-/
instance : Module S (PolynomialModule R M) := (coeffEquiv R).module _

instance (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] :
    IsScalarTower S R (PolynomialModule R M) := (coeffEquiv R).isScalarTower _ _

variable (R S) in
/-- `PolynomialModule.coeff` as a linear equiv. -/
@[simps! apply symm_apply]
/--
Definition of `coeffLinearEquiv` / `coeffLinearEquiv` 的定义

English:
definition coeffLinearEquiv
  signature: : PolynomialModule R M ≃ₗ[S] Nat ->₀ M
  body: (coeffEquiv _).linearEquiv _

中文:
定义 coeffLinearEquiv
  签名: : 多项式模 R M ≃ₗ[S] 自然数 ->₀ M
  定义体: (coeffEquiv _).linearEquiv _

Depends on / 依赖: coeffEquiv, linearEquiv
-/
def coeffLinearEquiv : PolynomialModule R M ≃ₗ[S] Nat ->₀ M := (coeffEquiv _).linearEquiv _

variable (R) in
/--
Definition of `lsingle` / `lsingle` 的定义

English:
definition lsingle
  signature: (i : Nat)
  body: (coeffLinearEquiv R R).symm.comp Finsupp.lsingle i

中文:
定义 lsingle
  签名: (i : 自然数)
  定义体: (coeffLinearEquiv R R).symm.comp Finsupp.lsingle i

Depends on / 依赖: Finsupp, Finsupp.lsingle, coeffLinearEquiv, lsingle, symm.comp
-/
def lsingle (i : Nat) : M ->ₗ[R] PolynomialModule R M :=
(coeffLinearEquiv R R).symm.comp Finsupp.lsingle i

/--
theorem `lsingle_apply` / 定理 `lsingle_apply`

English:
theorem lsingle_apply
  given: (i : Nat) (m : M) (n : Nat)
  statement: (lsingle R i m).coeff n = ite (i = n) m 0
  proof: Finsupp.single_apply

中文:
定理 lsingle_apply
  条件: (i : 自然数) (m : M) (n : 自然数)
  结论: (lsingle R i m).coeff n = ite (i = n) m 0
  证明: Finsupp.single_apply

Depends on / 依赖: Finsupp, Finsupp.single_apply, single_apply
-/
theorem lsingle_apply (i : Nat) (m : M) (n : Nat) : (lsingle R i m).coeff n = ite (i = n) m 0 :=
  Finsupp.single_apply

/--
theorem `single_smul` / 定理 `single_smul`

English:
theorem single_smul
  given: (i : Nat) (r : R) (m : M)
  statement: single R i (r • m) = r • single R i m
  proof: (lsingle R i).map_smul r m

@[elab_as_elim]

中文:
定理 single_smul
  条件: (i : 自然数) (r : R) (m : M)
  结论: single R i (r • m) = r • single R i m
  证明: (lsingle R i).map_smul r m

@[elab_as_elim]

Depends on / 依赖: lsingle, map_smul
-/
theorem single_smul (i : Nat) (r : R) (m : M) : single R i (r • m) = r • single R i m :=
  (lsingle R i).map_smul r m

@[elab_as_elim]
/--
lemma `induction_linear` / 引理 `induction_linear`

English:
lemma induction_linear
  statement: {p : PolynomialModule R M -> Prop} (x : PolynomialModule R M) (zero : p 0)
  proof: Finsupp.induction_linear (motive := (p <| ofCoeff R ·)) x.coeff zero (fun _ _ => add _ _)
    (fun _ _ => single _ _)

中文:
引理 induction_linear
  结论: {p : 多项式模 R M -> 命题} (x : 多项式模 R M) (zero : p 0)
  证明: Finsupp.induction_linear (motive := (p <| ofCoeff R ·)) x.coeff zero (fun _ _ => add _ _)
    (fun _ _ => single _ _)

Depends on / 依赖: Finsupp, Finsupp.induction_linear, induction_linear, motive, ofCoeff, single, x.coeff
-/
lemma induction_linear {p : PolynomialModule R M -> Prop} (x : PolynomialModule R M) (zero : p 0)
    (add : forall x y : PolynomialModule R M, p x -> p y -> p (x + y))
    (single : forall n m, p (single R n m)) : p x :=
  Finsupp.induction_linear (motive := (p <| ofCoeff R ·)) x.coeff zero (fun _ _ => add _ _)
    (fun _ _ => single _ _)

/--
Instance `polynomialModule` / 实例 `polynomialModule`

English:
instance polynomialModule
  signature: : Module R[X] (PolynomialModule R M)
  body: inferInstanceAs Module R[X] Module.AEval' (coeffLinearEquiv R R).symm.comp
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap

中文:
实例 polynomialModule
  签名: : 模 R[X] (多项式模 R M)
  定义体: inferInstanceAs Module R[X] Module.AEval' (coeffLinearEquiv R R).symm.comp
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap

Depends on / 依赖: Finsupp, Finsupp.lmapDomain, Module, Module.AEval, Nat.succ, coeffLinearEquiv, lmapDomain, symm.comp, toLinearMap
-/
instance polynomialModule : Module R[X] (PolynomialModule R M) :=
inferInstanceAs Module R[X] Module.AEval' (coeffLinearEquiv R R).symm.comp
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (f : R[X]) (m : PolynomialModule R M)
  proof: by
  rfl

中文:
引理 smul_def
  条件: (f : R[X]) (m : 多项式模 R M)
  证明: by
  rfl
-/
lemma smul_def (f : R[X]) (m : PolynomialModule R M) :
    f • m = aeval ((coeffLinearEquiv R R).symm.comp <|
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap) f m := by
  rfl

/--
Instance `isScalarTower'` / 实例 `isScalarTower'`

English:
instance isScalarTower'
  signature: (M : Type u) [AddCommGroup M] [Module R M] [Module S M]
  body: by
  have : IsScalarTower R R[X] (PolynomialModule R M) :=
inferInstanceAs IsScalarTower R R[X] Module.AEval' (coeffLinearEquiv R R).symm.comp
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap
  constructor
  intro x y z
  rw [← @IsScalarTower.algebraMap_smul S R]; rw [← @IsScalarTower.algebraMap_smul S R]; rw [smul_assoc]

中文:
实例 isScalarTower'
  签名: (M : 类型u) [加法交换群 M] [模 R M] [模 S M]
  定义体: by
  have : IsScalarTower R R[X] (PolynomialModule R M) :=
inferInstanceAs IsScalarTower R R[X] Module.AEval' (coeffLinearEquiv R R).symm.comp
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap
  constructor
  intro x y z
  rw [← @IsScalarTower.algebraMap_smul S R]; rw [← @IsScalarTower.algebraMap_smul S R]; rw [smul_assoc]

Depends on / 依赖: Finsupp, Finsupp.lmapDomain, IsScalarTower, IsScalarTower.algebraMap_smul, Module, Module.AEval, Nat.succ, PolynomialModule, algebraMap_smul, coeffLinearEquiv, lmapDomain, smul_assoc, symm.comp, toLinearMap
-/
instance isScalarTower' (M : Type u) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower S R M] : IsScalarTower S R[X] (PolynomialModule R M) := by
  have : IsScalarTower R R[X] (PolynomialModule R M) :=
inferInstanceAs IsScalarTower R R[X] Module.AEval' (coeffLinearEquiv R R).symm.comp
    (Finsupp.lmapDomain M R Nat.succ).comp (coeffLinearEquiv R R).toLinearMap
  constructor
  intro x y z
  rw [← @IsScalarTower.algebraMap_smul S R]; rw [← @IsScalarTower.algebraMap_smul S R]; rw [smul_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `monomial_smul_single` / 定理 `monomial_smul_single`

English:
theorem monomial_smul_single
  given: (i : Nat) (r : R) (j : Nat) (m : M)
  proof: by
  simp only [Module.End.mul_apply, Polynomial.aeval_monomial, Module.End.pow_apply,
    Module.algebraMap_end_apply, smul_def]
  induction i generalizing r j m with
  | zero =>
    rw [Function.iterate_zero]; rw [zero_add]
    exact congr(ofCoeff R $(Finsupp.smul_single r j m))
  | succ n hn =>
    rw [Function.iterate_succ]; rw [Function.comp_apply]; rw [add_assoc]; rw [← hn]
    congr 2
    rw [Nat.one_add]
    exact congr(ofCoeff R $(Finsupp.mapDomain_single))

@[simp]

中文:
定理 monomial_smul_single
  条件: (i : 自然数) (r : R) (j : 自然数) (m : M)
  证明: by
  simp only [Module.End.mul_apply, Polynomial.aeval_monomial, Module.End.pow_apply,
    Module.algebraMap_end_apply, smul_def]
  induction i generalizing r j m with
  | zero =>
    rw [Function.iterate_zero]; rw [zero_add]
    exact congr(ofCoeff R $(Finsupp.smul_single r j m))
  | succ n hn =>
    rw [Function.iterate_succ]; rw [Function.comp_apply]; rw [add_assoc]; rw [← hn]
    congr 2
    rw [Nat.one_add]
    exact congr(ofCoeff R $(Finsupp.mapDomain_single))

@[simp]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_single, Finsupp.smul_single, Function, Function.comp_apply, Function.iterate_succ, Function.iterate_zero, Module, Module.End.mul_apply, Module.End.pow_apply, Module.algebraMap_end_apply, Nat.one_add, Polynomial, Polynomial.aeval_monomial, add_assoc, aeval_monomial, algebraMap_end_apply, comp_apply, generalizing, iterate_succ
-/
theorem monomial_smul_single (i : Nat) (r : R) (j : Nat) (m : M) :
    monomial i r • single R j m = single R (i + j) (r • m) := by
  simp only [Module.End.mul_apply, Polynomial.aeval_monomial, Module.End.pow_apply,
    Module.algebraMap_end_apply, smul_def]
  induction i generalizing r j m with
  | zero =>
    rw [Function.iterate_zero]; rw [zero_add]
    exact congr(ofCoeff R $(Finsupp.smul_single r j m))
  | succ n hn =>
    rw [Function.iterate_succ]; rw [Function.comp_apply]; rw [add_assoc]; rw [← hn]
    congr 2
    rw [Nat.one_add]
    exact congr(ofCoeff R $(Finsupp.mapDomain_single))

@[simp]
/--
theorem `monomial_smul_lsingle` / 定理 `monomial_smul_lsingle`

English:
theorem monomial_smul_lsingle
  given: (i : Nat) (r : R) (j : Nat) (m : M)
  proof: monomial_smul_single ..

@[simp]

中文:
定理 monomial_smul_lsingle
  条件: (i : 自然数) (r : R) (j : 自然数) (m : M)
  证明: monomial_smul_single ..

@[simp]

Depends on / 依赖: monomial_smul_single
-/
theorem monomial_smul_lsingle (i : Nat) (r : R) (j : Nat) (m : M) :
    (monomial i) r • lsingle R j m = lsingle R (i + j) (r • m) :=
  monomial_smul_single ..

@[simp]
/--
theorem `monomial_smul_apply` / 定理 `monomial_smul_apply`

English:
theorem monomial_smul_apply
  given: (i : Nat) (r : R) (g : PolynomialModule R M) (n : Nat)
  proof: by
  induction g using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [smul_add, hp, hq, ite_add_ite]
  | single =>
    simp [monomial_smul_single, Finsupp.single_apply]
    grind

@[simp]

中文:
定理 monomial_smul_apply
  条件: (i : 自然数) (r : R) (g : 多项式模 R M) (n : 自然数)
  证明: by
  induction g using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [smul_add, hp, hq, ite_add_ite]
  | single =>
    simp [monomial_smul_single, Finsupp.single_apply]
    grind

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_apply, PolynomialModule, PolynomialModule.induction_linear, induction_linear, ite_add_ite, monomial_smul_single, single, single_apply, smul_add
-/
theorem monomial_smul_apply (i : Nat) (r : R) (g : PolynomialModule R M) (n : Nat) :
    (monomial i r • g).coeff n = ite (i <= n) (r • g.coeff (n - i)) 0 := by
  induction g using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [smul_add, hp, hq, ite_add_ite]
  | single =>
    simp [monomial_smul_single, Finsupp.single_apply]
    grind

@[simp]
/--
theorem `smul_single_apply` / 定理 `smul_single_apply`

English:
theorem smul_single_apply
  given: (i : Nat) (f : R[X]) (m : M) (n : Nat)
  proof: by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ite_add_ite]
  | monomial => simp; grind [monomial_smul_single, coeff_monomial, zero_smul]

中文:
定理 smul_single_apply
  条件: (i : 自然数) (f : R[X]) (m : M) (n : 自然数)
  证明: by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ite_add_ite]
  | monomial => simp; grind [monomial_smul_single, coeff_monomial, zero_smul]

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_smul, coeff_monomial, induction_on, ite_add_ite, monomial, monomial_smul_single, zero_smul
-/
theorem smul_single_apply (i : Nat) (f : R[X]) (m : M) (n : Nat) :
    (f • single R i m).coeff n = ite (i <= n) (f.coeff (n - i) • m) 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ite_add_ite]
  | monomial => simp; grind [monomial_smul_single, coeff_monomial, zero_smul]

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (f : R[X]) (g : PolynomialModule R M) (n : Nat)
  proof: by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ← Finset.sum_add_distrib]
  | monomial f_n f_a =>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
      (monomial f_n f_a).coeff i • g.coeff j]; rw [monomial_smul_apply]
    simp [Polynomial.coeff_monomial]

中文:
定理 smul_apply
  条件: (f : R[X]) (g : 多项式模 R M) (n : 自然数)
  证明: by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ← Finset.sum_add_distrib]
  | monomial f_n f_a =>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
      (monomial f_n f_a).coeff i • g.coeff j]; rw [monomial_smul_apply]
    simp [Polynomial.coeff_monomial]

Depends on / 依赖: Finset, Finset.Nat.sum_antidiagonal_eq_sum_range_succ, Finset.sum_add_distrib, Polynomial, Polynomial.coeff_monomial, Polynomial.induction_on, add_smul, coeff_monomial, g.coeff, induction_on, monomial, monomial_smul_apply, sum_add_distrib, sum_antidiagonal_eq_sum_range_succ
-/
theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : Nat) :
    (f • g).coeff n = ∑ x in Finset.antidiagonal n, f.coeff x.1 • g.coeff x.2 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_smul, hp, hq, ← Finset.sum_add_distrib]
  | monomial f_n f_a =>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
      (monomial f_n f_a).coeff i • g.coeff j]; rw [monomial_smul_apply]
    simp [Polynomial.coeff_monomial]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `equivPolynomialSelf` / `equivPolynomialSelf` 的定义

English:
definition equivPolynomialSelf
  signature: : PolynomialModule R R ≃ₗ[R[X]] R[X] where
  body: coeffAddEquiv.trans AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso R).symm.toAddEquiv
  map_smul' r x := by
    dsimp
    induction x using induction_linear with
    | zero => simp
    | add _ _ hp hq => simp_all [smul_add, mul_add]
    | single n a =>
    ext i
    simp only [coeffAddEquiv_apply, AddMonoidAlgebra.coeffAddEquiv_symm_apply,
      toFinsuppIso_symm_apply, coeff_ofFinsupp, smul_single_apply, smul_eq_mul, coeff_single,
      AddMonoidAlgebra.ofCoeff_single, ofFinsupp_single]
    split_ifs with hn
    · rw [show i = (i - n) + n by lia, Polynomial.coeff_mul_monomial]
      simp
    · rw [Polynomial.coeff_mul, Finset.sum_eq_zero]
      simp [Polynomial.coeff_monomial]
      lia

中文:
定义 equivPolynomialSelf
  签名: : 多项式模 R R ≃ₗ[R[X]] R[X] where
  定义体: coeffAddEquiv.trans AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso R).symm.toAddEquiv
  map_smul' r x := by
    dsimp
    induction x using induction_linear with
    | zero => simp
    | add _ _ hp hq => simp_all [smul_add, mul_add]
    | single n a =>
    ext i
    simp only [coeffAddEquiv_apply, AddMonoidAlgebra.coeffAddEquiv_symm_apply,
      toFinsuppIso_symm_apply, coeff_ofFinsupp, smul_single_apply, smul_eq_mul, coeff_single,
      AddMonoidAlgebra.ofCoeff_single, ofFinsupp_single]
    split_ifs with hn
    · rw [show i = (i - n) + n by lia, Polynomial.coeff_mul_monomial]
      simp
    · rw [Polynomial.coeff_mul, Finset.sum_eq_zero]
      simp [Polynomial.coeff_monomial]
      lia

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeffAddEquiv.symm.trans, coeffAddEquiv, coeffAddEquiv.trans
-/
def equivPolynomialSelf : PolynomialModule R R ≃ₗ[R[X]] R[X] where
toAddEquiv := coeffAddEquiv.trans AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso R).symm.toAddEquiv
  map_smul' r x := by
    dsimp
    induction x using induction_linear with
    | zero => simp
    | add _ _ hp hq => simp_all [smul_add, mul_add]
    | single n a =>
    ext i
    simp only [coeffAddEquiv_apply, AddMonoidAlgebra.coeffAddEquiv_symm_apply,
      toFinsuppIso_symm_apply, coeff_ofFinsupp, smul_single_apply, smul_eq_mul, coeff_single,
      AddMonoidAlgebra.ofCoeff_single, ofFinsupp_single]
    split_ifs with hn
    · rw [show i = (i - n) + n by lia, Polynomial.coeff_mul_monomial]
      simp
    · rw [Polynomial.coeff_mul, Finset.sum_eq_zero]
      simp [Polynomial.coeff_monomial]
      lia

/--
Definition of `equivPolynomial` / `equivPolynomial` 的定义

English:
definition equivPolynomial
  signature: {S : Type*} [CommRing S] [Algebra R S]
  body: coeffAddEquiv.trans AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso _).symm.toAddEquiv
  map_smul' _ _ := rfl

@[simp]

中文:
定义 equivPolynomial
  签名: {S : 类型} [交换环 S] [代数 R S]
  定义体: coeffAddEquiv.trans AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso _).symm.toAddEquiv
  map_smul' _ _ := rfl

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeffAddEquiv.symm.trans, coeffAddEquiv, coeffAddEquiv.trans
-/
def equivPolynomial {S : Type*} [CommRing S] [Algebra R S] : PolynomialModule R S ≃ₗ[R] S[X] where
toAddEquiv := coeffAddEquiv.trans AddMonoidAlgebra.coeffAddEquiv.symm.trans
    (toFinsuppIso _).symm.toAddEquiv
  map_smul' _ _ := rfl

@[simp]
/--
lemma `equivPolynomialSelf_apply_eq` / 引理 `equivPolynomialSelf_apply_eq`

English:
lemma equivPolynomialSelf_apply_eq
  given: (p : PolynomialModule R R)
  proof: rfl

@[simp]

中文:
引理 equivPolynomialSelf_apply_eq
  条件: (p : 多项式模 R R)
  证明: rfl

@[simp]
-/
lemma equivPolynomialSelf_apply_eq (p : PolynomialModule R R) :
    equivPolynomialSelf p = equivPolynomial p := rfl

@[simp]
/--
lemma `equivPolynomial_single` / 引理 `equivPolynomial_single`

English:
lemma equivPolynomial_single
  given: {S : Type*} [CommRing S] [Algebra R S] (n : Nat) (x : S)
  proof: rfl

@[simp]

中文:
引理 equivPolynomial_single
  条件: {S : 类型} [交换环 S] [代数 R S] (n : 自然数) (x : S)
  证明: rfl

@[simp]
-/
lemma equivPolynomial_single {S : Type*} [CommRing S] [Algebra R S] (n : Nat) (x : S) :
    equivPolynomial (single R n x) = monomial n x := rfl

@[simp]
/--
lemma `equivPolynomial_symm_monomial` / 引理 `equivPolynomial_symm_monomial`

English:
lemma equivPolynomial_symm_monomial
  given: {S : Type*} [CommRing S] [Algebra R S] (n : Nat) (x : S)
  proof: rfl

@[simp]

中文:
引理 equivPolynomial_symm_monomial
  条件: {S : 类型} [交换环 S] [代数 R S] (n : 自然数) (x : S)
  证明: rfl

@[simp]
-/
lemma equivPolynomial_symm_monomial {S : Type*} [CommRing S] [Algebra R S] (n : Nat) (x : S) :
    equivPolynomial.symm (monomial n x) = single R n x := rfl

@[simp]
/--
lemma `equivPolynomial_symm_one` / 引理 `equivPolynomial_symm_one`

English:
lemma equivPolynomial_symm_one
  given: {S : Type*} [CommRing S] [Algebra R S]
  proof: rfl

中文:
引理 equivPolynomial_symm_one
  条件: {S : 类型} [交换环 S] [代数 R S]
  证明: rfl
-/
lemma equivPolynomial_symm_one {S : Type*} [CommRing S] [Algebra R S] :
    equivPolynomial.symm (1 : S[X]) = single R 0 1 := rfl

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']
variable [Module R M']

/-- Two `R`-linear maps from `PolynomialModule R M` which are equal
after pre-composition with every `lsingle R a` are equal. -/
@[ext high]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {f g : PolynomialModule R M ->ₗ[R] M'}
  proof: by
  simpa [← DFunLike.coe_fn_eq, funext_iff, PolynomialModule.forall] using Finsupp.lhom_ext'
    (φ := f.comp (coeffLinearEquiv R R).symm.toLinearMap)
    (ψ := g.comp (coeffLinearEquiv R R (M := M)).symm.toLinearMap) h

中文:
定理 hom_ext
  结论: {f g : 多项式模 R M ->ₗ[R] M'}
  证明: by
  simpa [← DFunLike.coe_fn_eq, funext_iff, PolynomialModule.forall] using Finsupp.lhom_ext'
    (φ := f.comp (coeffLinearEquiv R R).symm.toLinearMap)
    (ψ := g.comp (coeffLinearEquiv R R (M := M)).symm.toLinearMap) h

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, Finsupp, Finsupp.lhom_ext, PolynomialModule, PolynomialModule.forall, coe_fn_eq, coeffLinearEquiv, f.comp, funext_iff, g.comp, lhom_ext, symm.toLinearMap, toLinearMap
-/
theorem hom_ext {f g : PolynomialModule R M ->ₗ[R] M'}
    (h : forall a, f ∘ₗ lsingle R a = g ∘ₗ lsingle R a) : f = g := by
  simpa [← DFunLike.coe_fn_eq, funext_iff, PolynomialModule.forall] using Finsupp.lhom_ext'
    (φ := f.comp (coeffLinearEquiv R R).symm.toLinearMap)
    (ψ := g.comp (coeffLinearEquiv R R (M := M)).symm.toLinearMap) h

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₗ[R] M')
  body: (coeffLinearEquiv ..).symm.toLinearMap.comp (Finsupp.mapRange.linearMap f).comp
    (coeffLinearEquiv ..).toLinearMap

@[simp]

中文:
定义 map
  签名: (f : M ->ₗ[R] M')
  定义体: (coeffLinearEquiv ..).symm.toLinearMap.comp (Finsupp.mapRange.linearMap f).comp
    (coeffLinearEquiv ..).toLinearMap

@[simp]

Depends on / 依赖: Finsupp, Finsupp.mapRange.linearMap, coeffLinearEquiv, linearMap, mapRange, symm.toLinearMap.comp, toLinearMap
-/
def map (f : M ->ₗ[R] M') : PolynomialModule R M ->ₗ[R] PolynomialModule R' M' :=
(coeffLinearEquiv ..).symm.toLinearMap.comp (Finsupp.mapRange.linearMap f).comp
    (coeffLinearEquiv ..).toLinearMap

@[simp]
/--
theorem `map_single` / 定理 `map_single`

English:
theorem map_single
  given: (f : M ->ₗ[R] M') (i : Nat) (m : M)
  proof: by simp [map]

@[simp]

中文:
定理 map_single
  条件: (f : M ->ₗ[R] M') (i : 自然数) (m : M)
  证明: by simp [map]

@[simp]
-/
theorem map_single (f : M ->ₗ[R] M') (i : Nat) (m : M) :
    map R' f (single R i m) = single R' i (f m) := by simp [map]

@[simp]
/--
theorem `map_lsingle` / 定理 `map_lsingle`

English:
theorem map_lsingle
  given: (f : M ->ₗ[R] M') (i : Nat) (m : M)
  proof: map_single ..

中文:
定理 map_lsingle
  条件: (f : M ->ₗ[R] M') (i : 自然数) (m : M)
  证明: map_single ..

Depends on / 依赖: map_single
-/
theorem map_lsingle (f : M ->ₗ[R] M') (i : Nat) (m : M) :
    map R' f (lsingle R i m) = lsingle R' i (f m) :=
  map_single ..

variable [Algebra R R'] [IsScalarTower R R' M']

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (f : M ->ₗ[R] M') (p : R[X]) (q : PolynomialModule R M)
  proof: by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, e₁, e₂, Polynomial.map_add, add_smul]
    | monomial => rw [monomial_smul_single, map_single, Polynomial.map_monomial, map_single,
        monomial_smul_single, f.map_smul, algebraMap_smul]

中文:
定理 map_smul
  条件: (f : M ->ₗ[R] M') (p : R[X]) (q : 多项式模 R M)
  证明: by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, e₁, e₂, Polynomial.map_add, add_smul]
    | monomial => rw [monomial_smul_single, map_single, Polynomial.map_monomial, map_single,
        monomial_smul_single, f.map_smul, algebraMap_smul]

Depends on / 依赖: Polynomial, Polynomial.induction_on, Polynomial.map_add, Polynomial.map_monomial, add_smul, algebraMap_smul, f.map_smul, induction_linear, induction_on, map_add, map_monomial, map_single, map_smul, map_zero, monomial, monomial_smul_single, single, smul_add, smul_zero
-/
theorem map_smul (f : M ->ₗ[R] M') (p : R[X]) (q : PolynomialModule R M) :
    map R' f (p • q) = p.map (algebraMap R R') • map R' f q := by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, e₁, e₂, Polynomial.map_add, add_smul]
    | monomial => rw [monomial_smul_single, map_single, Polynomial.map_monomial, map_single,
        monomial_smul_single, f.map_smul, algebraMap_smul]

set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluate a polynomial `p : PolynomialModule R M` at `r : R`. -/
@[simps! -isSimp]
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (r : R)
  body: p.coeff.sum fun i m => r ^ i • m
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _
  map_smul' s m := by
    refine (Finsupp.sum_smul_index' ?_).trans ?_
    · exact fun i => smul_zero _
    · simp_rw [RingHom.id_apply, Finsupp.smul_sum]
      congr
      ext i c
      rw [smul_comm]

@[simp]

中文:
定义 eval
  签名: (r : R)
  定义体: p.coeff.sum fun i m => r ^ i • m
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _
  map_smul' s m := by
    refine (Finsupp.sum_smul_index' ?_).trans ?_
    · exact fun i => smul_zero _
    · simp_rw [RingHom.id_apply, Finsupp.smul_sum]
      congr
      ext i c
      rw [smul_comm]

@[simp]

Depends on / 依赖: p.coeff.sum
-/
def eval (r : R) : PolynomialModule R M ->ₗ[R] M where
  toFun p := p.coeff.sum fun i m => r ^ i • m
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _
  map_smul' s m := by
    refine (Finsupp.sum_smul_index' ?_).trans ?_
    · exact fun i => smul_zero _
    · simp_rw [RingHom.id_apply, Finsupp.smul_sum]
      congr
      ext i c
      rw [smul_comm]

@[simp]
/--
theorem `eval_single` / 定理 `eval_single`

English:
theorem eval_single
  given: (r : R) (i : Nat) (m : M)
  statement: eval r (single R i m) = r ^ i • m
  proof: Finsupp.sum_single_index (smul_zero _)

@[simp]

中文:
定理 eval_single
  条件: (r : R) (i : 自然数) (m : M)
  结论: eval r (single R i m) = r ^ i • m
  证明: Finsupp.sum_single_index (smul_zero _)

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_single_index, smul_zero, sum_single_index
-/
theorem eval_single (r : R) (i : Nat) (m : M) : eval r (single R i m) = r ^ i • m :=
  Finsupp.sum_single_index (smul_zero _)

@[simp]
/--
theorem `eval_lsingle` / 定理 `eval_lsingle`

English:
theorem eval_lsingle
  given: (r : R) (i : Nat) (m : M)
  statement: eval r (lsingle R i m) = r ^ i • m
  proof: eval_single r i m

@[simp]

中文:
定理 eval_lsingle
  条件: (r : R) (i : 自然数) (m : M)
  结论: eval r (lsingle R i m) = r ^ i • m
  证明: eval_single r i m

@[simp]

Depends on / 依赖: eval_single
-/
theorem eval_lsingle (r : R) (i : Nat) (m : M) : eval r (lsingle R i m) = r ^ i • m :=
  eval_single r i m

@[simp]
/--
theorem `eval_smul` / 定理 `eval_smul`

English:
theorem eval_smul
  given: (p : R[X]) (q : PolynomialModule R M) (r : R)
  proof: by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, Polynomial.eval_add, e₁, e₂, add_smul]
    | monomial => simp only [monomial_smul_single, Polynomial.eval_monomial, eval_single]; module

@[simp]

中文:
定理 eval_smul
  条件: (p : R[X]) (q : 多项式模 R M) (r : R)
  证明: by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, Polynomial.eval_add, e₁, e₂, add_smul]
    | monomial => simp only [monomial_smul_single, Polynomial.eval_monomial, eval_single]; module

@[simp]

Depends on / 依赖: Polynomial, Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.induction_on, add_smul, eval_add, eval_monomial, eval_single, induction_linear, induction_on, map_add, map_zero, module, monomial, monomial_smul_single, single, smul_add, smul_zero
-/
theorem eval_smul (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (p • q) = p.eval r • eval r q := by
  induction q using induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add f g e₁ e₂ => rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  | single i m =>
    induction p using Polynomial.induction_on' with
    | add _ _ e₁ e₂ => rw [add_smul, map_add, Polynomial.eval_add, e₁, e₂, add_smul]
    | monomial => simp only [monomial_smul_single, Polynomial.eval_monomial, eval_single]; module

@[simp]
/--
theorem `eval_map` / 定理 `eval_map`

English:
theorem eval_map
  given: (f : M ->ₗ[R] M') (q : PolynomialModule R M) (r : R)
  proof: by
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => simp only [map_single, eval_single, f.map_smul]; module

@[simp]

中文:
定理 eval_map
  条件: (f : M ->ₗ[R] M') (q : 多项式模 R M) (r : R)
  证明: by
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => simp only [map_single, eval_single, f.map_smul]; module

@[simp]

Depends on / 依赖: eval_single, f.map_smul, induction_linear, map_add, map_single, map_smul, map_zero, module, simp_rw, single
-/
theorem eval_map (f : M ->ₗ[R] M') (q : PolynomialModule R M) (r : R) :
    eval (algebraMap R R' r) (map R' f q) = f (eval r q) := by
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => simp only [map_single, eval_single, f.map_smul]; module

@[simp]
/--
theorem `eval_map'` / 定理 `eval_map'`

English:
theorem eval_map'
  given: (f : M ->ₗ[R] M) (q : PolynomialModule R M) (r : R)
  proof: eval_map R f q r

@[simp]

中文:
定理 eval_map'
  条件: (f : M ->ₗ[R] M) (q : 多项式模 R M) (r : R)
  证明: eval_map R f q r

@[simp]

Depends on / 依赖: eval_map
-/
theorem eval_map' (f : M ->ₗ[R] M) (q : PolynomialModule R M) (r : R) :
    eval r (map R f q) = f (eval r q) :=
  eval_map R f q r

@[simp]
/--
lemma `aeval_equivPolynomial` / 引理 `aeval_equivPolynomial`

English:
lemma aeval_equivPolynomial
  statement: {S : Type*} [CommRing S] [Algebra S R]
  proof: by
  induction f using induction_linear with
  | zero => simp
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => rw [equivPolynomial_single, aeval_monomial, mul_comm, map_single,
      Algebra.linearMap_apply, eval_single, smul_eq_mul]

中文:
引理 aeval_equivPolynomial
  结论: {S : 类型} [交换环 S] [代数 S R]
  证明: by
  induction f using induction_linear with
  | zero => simp
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => rw [equivPolynomial_single, aeval_monomial, mul_comm, map_single,
      Algebra.linearMap_apply, eval_single, smul_eq_mul]

Depends on / 依赖: Algebra, Algebra.linearMap_apply, aeval_monomial, equivPolynomial_single, eval_single, induction_linear, linearMap_apply, map_add, map_single, mul_comm, simp_rw, single, smul_eq_mul
-/
lemma aeval_equivPolynomial {S : Type*} [CommRing S] [Algebra S R]
    (f : PolynomialModule S S) (x : R) :
    aeval x (equivPolynomial f) = eval x (map R (Algebra.linearMap S R) f) := by
  induction f using induction_linear with
  | zero => simp
  | add f g e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m => rw [equivPolynomial_single, aeval_monomial, mul_comm, map_single,
      Algebra.linearMap_apply, eval_single, smul_eq_mul]

/-- `comp p q` is the composition of `p : R[X]` and `q : M[X]` as `q(p(x))`. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (p : R[X])
  body: LinearMap.comp ((eval p).restrictScalars R) (map R[X] (lsingle R 0))

中文:
定义 comp
  签名: (p : R[X])
  定义体: LinearMap.comp ((eval p).restrictScalars R) (map R[X] (lsingle R 0))

Depends on / 依赖: LinearMap, LinearMap.comp, lsingle, restrictScalars
-/
def comp (p : R[X]) : PolynomialModule R M ->ₗ[R] PolynomialModule R M :=
  LinearMap.comp ((eval p).restrictScalars R) (map R[X] (lsingle R 0))

/--
theorem `comp_single` / 定理 `comp_single`

English:
theorem comp_single
  given: (p : R[X]) (i : Nat) (m : M)
  statement: comp p (single R i m) = p ^ i • single R 0 m
  proof: by
  rw [comp_apply]; rw [map_single]; rw [eval_single]
  rfl

中文:
定理 comp_single
  条件: (p : R[X]) (i : 自然数) (m : M)
  结论: comp p (single R i m) = p ^ i • single R 0 m
  证明: by
  rw [comp_apply]; rw [map_single]; rw [eval_single]
  rfl

Depends on / 依赖: comp_apply, eval_single, map_single
-/
theorem comp_single (p : R[X]) (i : Nat) (m : M) : comp p (single R i m) = p ^ i • single R 0 m := by
  rw [comp_apply]; rw [map_single]; rw [eval_single]
  rfl

/--
theorem `comp_eval` / 定理 `comp_eval`

English:
theorem comp_eval
  given: (p : R[X]) (q : PolynomialModule R M) (r : R)
  proof: by
  rw [← LinearMap.comp_apply]
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add _ _ e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m =>
    rw [LinearMap.comp_apply]; rw [comp_single]; rw [eval_single]; rw [eval_smul]; rw [eval_single]; rw [eval_pow]
    module

中文:
定理 comp_eval
  条件: (p : R[X]) (q : 多项式模 R M) (r : R)
  证明: by
  rw [← LinearMap.comp_apply]
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add _ _ e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m =>
    rw [LinearMap.comp_apply]; rw [comp_single]; rw [eval_single]; rw [eval_smul]; rw [eval_single]; rw [eval_pow]
    module

Depends on / 依赖: LinearMap, LinearMap.comp_apply, comp_apply, comp_single, eval_pow, eval_single, eval_smul, induction_linear, map_add, map_zero, module, simp_rw, single
-/
theorem comp_eval (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (comp p q) = eval (p.eval r) q := by
  rw [← LinearMap.comp_apply]
  induction q using induction_linear with
  | zero => simp_rw [map_zero]
  | add _ _ e₁ e₂ => simp_rw [map_add, e₁, e₂]
  | single i m =>
    rw [LinearMap.comp_apply]; rw [comp_single]; rw [eval_single]; rw [eval_smul]; rw [eval_single]; rw [eval_pow]
    module

/--
theorem `comp_smul` / 定理 `comp_smul`

English:
theorem comp_smul
  given: (p p' : R[X]) (q : PolynomialModule R M)
  proof: by
  rw [comp_apply]; rw [map_smul]; rw [eval_smul]; rw [Polynomial.comp]; rw [Polynomial.eval_map]; rw [comp_apply]
  rfl

中文:
定理 comp_smul
  条件: (p p' : R[X]) (q : 多项式模 R M)
  证明: by
  rw [comp_apply]; rw [map_smul]; rw [eval_smul]; rw [Polynomial.comp]; rw [Polynomial.eval_map]; rw [comp_apply]
  rfl

Depends on / 依赖: Polynomial, Polynomial.comp, Polynomial.eval_map, comp_apply, eval_map, eval_smul, map_smul
-/
theorem comp_smul (p p' : R[X]) (q : PolynomialModule R M) :
    comp p (p' • q) = p'.comp p • comp p q := by
  rw [comp_apply]; rw [map_smul]; rw [eval_smul]; rw [Polynomial.comp]; rw [Polynomial.eval_map]; rw [comp_apply]
  rfl

end PolynomialModule
