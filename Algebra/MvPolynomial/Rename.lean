/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Renaming variables of polynomials

This file establishes the `rename` operation on multivariate polynomials,
which modifies the set of variables.

## Main declarations

* `MvPolynomial.rename`
* `MvPolynomial.renameEquiv`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ α`

-/

@[expose] public section


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

namespace MvPolynomial

section Rename

/--
Definition of `rename` / `rename` 的定义

English:
definition rename
  signature: (f : σ -> τ)
  body: AddMonoidAlgebra.mapDomainAlgHom _ _ (mapDomain.addMonoidHom f)

中文:
定义 rename
  签名: (f : σ -> τ)
  定义体: AddMonoidAlgebra.mapDomainAlgHom _ _ (mapDomain.addMonoidHom f)

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mapDomainAlgHom, addMonoidHom, mapDomain, mapDomain.addMonoidHom, mapDomainAlgHom
-/
def rename (f : σ -> τ) : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R :=
  AddMonoidAlgebra.mapDomainAlgHom _ _ (mapDomain.addMonoidHom f)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `rename_C` / 定理 `rename_C`

English:
theorem rename_C
  given: (f : σ -> τ) (r : R)
  statement: rename f (C r) = C r
  proof: by
  unfold rename C monomial MvPolynomial; simp

@[simp]

中文:
定理 rename_C
  条件: (f : σ -> τ) (r : R)
  结论: rename f (C r) = C r
  证明: by
  unfold rename C monomial MvPolynomial; simp

@[simp]

Depends on / 依赖: MvPolynomial, monomial
-/
theorem rename_C (f : σ -> τ) (r : R) : rename f (C r) = C r := by
  unfold rename C monomial MvPolynomial; simp

@[simp]
/--
theorem `rename_X` / 定理 `rename_X`

English:
theorem rename_X
  given: (f : σ -> τ) (i : σ)
  statement: rename f (X i : MvPolynomial σ R) = X (f i)
  proof: by
  simp [MvPolynomial, rename, X, monomial]

@[simp]

中文:
定理 rename_X
  条件: (f : σ -> τ) (i : σ)
  结论: rename f (X i : 多元多项式 σ R) = X (f i)
  证明: by
  simp [MvPolynomial, rename, X, monomial]

@[simp]

Depends on / 依赖: MvPolynomial, monomial
-/
theorem rename_X (f : σ -> τ) (i : σ) : rename f (X i : MvPolynomial σ R) = X (f i) := by
  simp [MvPolynomial, rename, X, monomial]

@[simp]
/--
lemma `rename_zero` / 引理 `rename_zero`

English:
lemma rename_zero
  given: (f : σ -> τ)
  statement: (0 : MvPolynomial σ R).rename f = 0
  proof: rfl

中文:
引理 rename_zero
  条件: (f : σ -> τ)
  结论: (0 : 多元多项式 σ R).rename f = 0
  证明: rfl
-/
lemma rename_zero (f : σ -> τ) : (0 : MvPolynomial σ R).rename f = 0 := rfl

/--
theorem `map_rename` / 定理 `map_rename`

English:
theorem map_rename
  given: (f : R ->+* S) (g : σ -> τ) (p : MvPolynomial σ R)
  proof: by
  apply MvPolynomial.induction_on p
    (fun a => by simp only [map_C, rename_C])
    (fun p q hp hq => by simp only [hp, hq, map_add]) fun p n hp => by
    simp only [hp, rename_X, map_X, map_mul]

中文:
定理 map_rename
  条件: (f : R ->+* S) (g : σ -> τ) (p : 多元多项式 σ R)
  证明: by
  apply MvPolynomial.induction_on p
    (fun a => by simp only [map_C, rename_C])
    (fun p q hp hq => by simp only [hp, hq, map_add]) fun p n hp => by
    simp only [hp, rename_X, map_X, map_mul]

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, induction_on, map_C, map_X, map_add, map_mul, rename_C, rename_X
-/
theorem map_rename (f : R ->+* S) (g : σ -> τ) (p : MvPolynomial σ R) :
    map f (rename g p) = rename g (map f p) := by
  apply MvPolynomial.induction_on p
    (fun a => by simp only [map_C, rename_C])
    (fun p q hp hq => by simp only [hp, hq, map_add]) fun p n hp => by
    simp only [hp, rename_X, map_X, map_mul]

/--
lemma `map_comp_rename` / 引理 `map_comp_rename`

English:
lemma map_comp_rename
  given: (f : R ->+* S) (g : σ -> τ)
  proof: RingHom.ext fun p => map_rename f g p

@[simp]

中文:
引理 map_comp_rename
  条件: (f : R ->+* S) (g : σ -> τ)
  证明: RingHom.ext fun p => map_rename f g p

@[simp]

Depends on / 依赖: RingHom, RingHom.ext, map_rename
-/
lemma map_comp_rename (f : R ->+* S) (g : σ -> τ) :
    (map f).comp (rename g).toRingHom = (rename g).toRingHom.comp (map f) :=
  RingHom.ext fun p => map_rename f g p

@[simp]
/--
theorem `rename_rename` / 定理 `rename_rename`

English:
theorem rename_rename
  given: (f : σ -> τ) (g : τ -> α) (p : MvPolynomial σ R)
  proof: by
  simp [MvPolynomial, rename, mapDomain.addMonoidHom_comp]

中文:
定理 rename_rename
  条件: (f : σ -> τ) (g : τ -> α) (p : 多元多项式 σ R)
  证明: by
  simp [MvPolynomial, rename, mapDomain.addMonoidHom_comp]

Depends on / 依赖: MvPolynomial, addMonoidHom_comp, mapDomain, mapDomain.addMonoidHom_comp
-/
theorem rename_rename (f : σ -> τ) (g : τ -> α) (p : MvPolynomial σ R) :
    rename g (rename f p) = rename (g ∘ f) p := by
  simp [MvPolynomial, rename, mapDomain.addMonoidHom_comp]

/--
lemma `rename_comp_rename` / 引理 `rename_comp_rename`

English:
lemma rename_comp_rename
  given: (f : σ -> τ) (g : τ -> α)
  proof: AlgHom.ext fun p => rename_rename f g p

@[simp]

中文:
引理 rename_comp_rename
  条件: (f : σ -> τ) (g : τ -> α)
  证明: AlgHom.ext fun p => rename_rename f g p

@[simp]
-/
lemma rename_comp_rename (f : σ -> τ) (g : τ -> α) :
    (rename (R := R) g).comp (rename f) = rename (g ∘ f) :=
  AlgHom.ext fun p => rename_rename f g p

@[simp]
/--
theorem `rename_id` / 定理 `rename_id`

English:
theorem rename_id
  statement: rename id = AlgHom.id R (MvPolynomial σ R)
  proof: by simp [MvPolynomial, rename]

中文:
定理 rename_id
  结论: rename id = 代数态射.id R (多元多项式 σ R)
  证明: by simp [MvPolynomial, rename]

Depends on / 依赖: MvPolynomial
-/
theorem rename_id : rename id = AlgHom.id R (MvPolynomial σ R) := by simp [MvPolynomial, rename]

/--
lemma `rename_id_apply` / 引理 `rename_id_apply`

English:
lemma rename_id_apply
  given: (p : MvPolynomial σ R)
  statement: rename id p = p
  proof: by
  simp

中文:
引理 rename_id_apply
  条件: (p : 多元多项式 σ R)
  结论: rename id p = p
  证明: by
  simp
-/
lemma rename_id_apply (p : MvPolynomial σ R) : rename id p = p := by
  simp

/--
theorem `rename_monomial` / 定理 `rename_monomial`

English:
theorem rename_monomial
  given: (f : σ -> τ) (d : σ ->₀ Nat) (r : R)
  proof: by
  simp [MvPolynomial, rename, monomial]

中文:
定理 rename_monomial
  条件: (f : σ -> τ) (d : σ ->₀ 自然数) (r : R)
  证明: by
  simp [MvPolynomial, rename, monomial]

Depends on / 依赖: MvPolynomial, monomial
-/
theorem rename_monomial (f : σ -> τ) (d : σ ->₀ Nat) (r : R) :
    rename f (monomial d r) = monomial (d.mapDomain f) r := by
  simp [MvPolynomial, rename, monomial]

/--
lemma `rename_eq_aeval` / 引理 `rename_eq_aeval`

English:
lemma rename_eq_aeval
  given: (f : σ -> τ)
  statement: rename (R := R) f = aeval (X ∘ f)
  proof: by ext; simp

@[deprecated (since := "2026-06-18")] alias rename_eq := rename_eq_aeval

中文:
引理 rename_eq_aeval
  条件: (f : σ -> τ)
  结论: rename (R := R) f = aeval (X ∘ f)
  证明: by ext; simp

@[deprecated (since := "2026-06-18")] alias rename_eq := rename_eq_aeval
-/
lemma rename_eq_aeval (f : σ -> τ) : rename (R := R) f = aeval (X ∘ f) := by ext; simp

@[deprecated (since := "2026-06-18")] alias rename_eq := rename_eq_aeval

/--
theorem `rename_injective` / 定理 `rename_injective`

English:
theorem rename_injective
  given: (f : σ -> τ) (hf : Function.Injective f)
  proof: AddMonoidAlgebra.mapDomain_injective (Finsupp.mapDomain_injective hf)

@[simp]

中文:
定理 rename_injective
  条件: (f : σ -> τ) (hf : 函数.单射 f)
  证明: AddMonoidAlgebra.mapDomain_injective (Finsupp.mapDomain_injective hf)

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mapDomain_injective, Finsupp, Finsupp.mapDomain_injective, mapDomain_injective
-/
theorem rename_injective (f : σ -> τ) (hf : Function.Injective f) :
    Function.Injective (rename f : MvPolynomial σ R -> MvPolynomial τ R) :=
  AddMonoidAlgebra.mapDomain_injective (Finsupp.mapDomain_injective hf)

@[simp]
/--
lemma `rename_eq_zero_iff_of_injective` / 引理 `rename_eq_zero_iff_of_injective`

English:
lemma rename_eq_zero_iff_of_injective
  statement: (p : MvPolynomial σ R) {f : σ -> τ}
  proof: by
  rw [← rename_zero f]; rw [(MvPolynomial.rename_injective _ hf).eq_iff]

中文:
引理 rename_eq_zero_iff_of_injective
  结论: (p : 多元多项式 σ R) {f : σ -> τ}
  证明: by
  rw [← rename_zero f]; rw [(MvPolynomial.rename_injective _ hf).eq_iff]

Depends on / 依赖: MvPolynomial, MvPolynomial.rename_injective, eq_iff, rename_injective, rename_zero
-/
lemma rename_eq_zero_iff_of_injective (p : MvPolynomial σ R) {f : σ -> τ}
    (hf : f.Injective) : p.rename f = 0 ↔ p = 0 := by
  rw [← rename_zero f]; rw [(MvPolynomial.rename_injective _ hf).eq_iff]

/--
theorem `rename_leftInverse` / 定理 `rename_leftInverse`

English:
theorem rename_leftInverse
  given: {f : σ -> τ} {g : τ -> σ} (hf : Function.LeftInverse f g)
  proof: by
  intro x
  simp [hf.comp_eq_id]

中文:
定理 rename_leftInverse
  条件: {f : σ -> τ} {g : τ -> σ} (hf : 函数.左逆 f g)
  证明: by
  intro x
  simp [hf.comp_eq_id]

Depends on / 依赖: comp_eq_id, hf.comp_eq_id
-/
theorem rename_leftInverse {f : σ -> τ} {g : τ -> σ} (hf : Function.LeftInverse f g) :
    Function.LeftInverse (rename f : MvPolynomial σ R -> MvPolynomial τ R) (rename g) := by
  intro x
  simp [hf.comp_eq_id]

/--
theorem `rename_rightInverse` / 定理 `rename_rightInverse`

English:
theorem rename_rightInverse
  given: {f : σ -> τ} {g : τ -> σ} (hf : Function.RightInverse f g)
  proof: rename_leftInverse hf

中文:
定理 rename_rightInverse
  条件: {f : σ -> τ} {g : τ -> σ} (hf : 函数.右逆 f g)
  证明: rename_leftInverse hf

Depends on / 依赖: rename_leftInverse
-/
theorem rename_rightInverse {f : σ -> τ} {g : τ -> σ} (hf : Function.RightInverse f g) :
    Function.RightInverse (rename f : MvPolynomial σ R -> MvPolynomial τ R) (rename g) :=
  rename_leftInverse hf

/--
theorem `rename_surjective` / 定理 `rename_surjective`

English:
theorem rename_surjective
  given: (f : σ -> τ) (hf : Function.Surjective f)
  proof: .surjective let ⟨_, hf⟩ := hf.hasRightInverse; rename_rightInverse hf

中文:
定理 rename_surjective
  条件: (f : σ -> τ) (hf : 函数.满射 f)
  证明: .surjective let ⟨_, hf⟩ := hf.hasRightInverse; rename_rightInverse hf

Depends on / 依赖: hasRightInverse, hf.hasRightInverse, rename_rightInverse, surjective
-/
theorem rename_surjective (f : σ -> τ) (hf : Function.Surjective f) :
    Function.Surjective (rename f : MvPolynomial σ R -> MvPolynomial τ R) :=
.surjective let ⟨_, hf⟩ := hf.hasRightInverse; rename_rightInverse hf

section

variable {f : σ -> τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

open scoped Classical in
/--
Definition of `killCompl` / `killCompl` 的定义

English:
definition killCompl
  signature: : MvPolynomial τ R ->ₐ[R] MvPolynomial σ R
  body: aeval fun i => if h : i in Set.range f then X (Equiv.ofInjective f hf).symm ⟨i, h⟩ else 0

中文:
定义 killCompl
  签名: : 多元多项式 τ R ->ₐ[R] 多元多项式 σ R
  定义体: aeval fun i => if h : i in Set.range f then X (Equiv.ofInjective f hf).symm ⟨i, h⟩ else 0

Depends on / 依赖: Equiv.ofInjective, Set.range, ofInjective
-/
def killCompl : MvPolynomial τ R ->ₐ[R] MvPolynomial σ R :=
aeval fun i => if h : i in Set.range f then X (Equiv.ofInjective f hf).symm ⟨i, h⟩ else 0

/--
theorem `killCompl_C` / 定理 `killCompl_C`

English:
theorem killCompl_C
  given: (r : R)
  statement: killCompl hf (C r) = C r
  proof: algHom_C _ _

中文:
定理 killCompl_C
  条件: (r : R)
  结论: killCompl hf (C r) = C r
  证明: algHom_C _ _

Depends on / 依赖: algHom_C
-/
theorem killCompl_C (r : R) : killCompl hf (C r) = C r := algHom_C _ _

/--
theorem `killCompl_comp_rename` / 定理 `killCompl_comp_rename`

English:
theorem killCompl_comp_rename
  statement: (killCompl hf).comp (rename f) = AlgHom.id R _
  proof: algHom_ext fun i => by
    dsimp
    rw [rename_X]; rw [killCompl]; rw [aeval_X]; rw [dif_pos ⟨i]; rw [rfl⟩]; rw [Equiv.ofInjective_symm_apply]

@[simp]

中文:
定理 killCompl_comp_rename
  结论: (killCompl hf).comp (rename f) = 代数态射.id R _
  证明: algHom_ext fun i => by
    dsimp
    rw [rename_X]; rw [killCompl]; rw [aeval_X]; rw [dif_pos ⟨i]; rw [rfl⟩]; rw [Equiv.ofInjective_symm_apply]

@[simp]

Depends on / 依赖: Equiv.ofInjective_symm_apply, aeval_X, algHom_ext, dif_pos, killCompl, ofInjective_symm_apply, rename_X
-/
theorem killCompl_comp_rename : (killCompl hf).comp (rename f) = AlgHom.id R _ :=
  algHom_ext fun i => by
    dsimp
    rw [rename_X]; rw [killCompl]; rw [aeval_X]; rw [dif_pos ⟨i]; rw [rfl⟩]; rw [Equiv.ofInjective_symm_apply]

@[simp]
/--
theorem `killCompl_rename_app` / 定理 `killCompl_rename_app`

English:
theorem killCompl_rename_app
  given: (p : MvPolynomial σ R)
  statement: killCompl hf (rename f p) = p
  proof: AlgHom.congr_fun (killCompl_comp_rename hf) p

中文:
定理 killCompl_rename_app
  条件: (p : 多元多项式 σ R)
  结论: killCompl hf (rename f p) = p
  证明: AlgHom.congr_fun (killCompl_comp_rename hf) p

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, killCompl_comp_rename
-/
theorem killCompl_rename_app (p : MvPolynomial σ R) : killCompl hf (rename f p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename hf) p

/--
lemma `killCompl_map` / 引理 `killCompl_map`

English:
lemma killCompl_map
  given: (φ : R ->+* S) (p : MvPolynomial τ R)
  proof: by
  simp only [← AlgHom.coe_toRingHom, ← RingHom.comp_apply]
  congr
  ext i n
  · simp
  · by_cases h : i in Set.range f <;> simp [killCompl, h]

@[simp]

中文:
引理 killCompl_map
  条件: (φ : R ->+* S) (p : 多元多项式 τ R)
  证明: by
  simp only [← AlgHom.coe_toRingHom, ← RingHom.comp_apply]
  congr
  ext i n
  · simp
  · by_cases h : i in Set.range f <;> simp [killCompl, h]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, RingHom, RingHom.comp_apply, Set.range, coe_toRingHom, comp_apply, killCompl
-/
lemma killCompl_map (φ : R ->+* S) (p : MvPolynomial τ R) :
    (p.map φ).killCompl hf = (p.killCompl hf).map φ := by
  simp only [← AlgHom.coe_toRingHom, ← RingHom.comp_apply]
  congr
  ext i n
  · simp
  · by_cases h : i in Set.range f <;> simp [killCompl, h]

@[simp]
/--
lemma `killCompl_monomial_mapDomain` / 引理 `killCompl_monomial_mapDomain`

English:
lemma killCompl_monomial_mapDomain
  given: {s : σ ->₀ Nat} {c : R}
  proof: by
  simp [← rename_monomial]

中文:
引理 killCompl_monomial_mapDomain
  条件: {s : σ ->₀ 自然数} {c : R}
  证明: by
  simp [← rename_monomial]

Depends on / 依赖: DenselyOrdered, LinearOrderedSemiField, LinearOrderedSemiField.toDenselyOrdered, rename_monomial, toDenselyOrdered
-/
lemma killCompl_monomial_mapDomain {s : σ ->₀ Nat} {c : R} :
    (monomial (s.mapDomain f) c).killCompl hf = monomial s c := by
  simp [← rename_monomial]

/--
lemma `killCompl_monomial_eq_zero_of_notMem_range` / 引理 `killCompl_monomial_eq_zero_of_notMem_range`

English:
lemma killCompl_monomial_eq_zero_of_notMem_range
  statement: {s : τ ->₀ Nat} (c : R)
  proof: by
  rw [killCompl]; rw [aeval_monomial]; rw [Finsupp.prod]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero ha
  simp [hs, zero_pow (Finsupp.mem_support_iff.mp ha)]

中文:
引理 killCompl_monomial_eq_zero_of_notMem_range
  结论: {s : τ ->₀ 自然数} (c : R)
  证明: by
  rw [killCompl]; rw [aeval_monomial]; rw [Finsupp.prod]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero ha
  simp [hs, zero_pow (Finsupp.mem_support_iff.mp ha)]

Depends on / 依赖: Finset, Finset.prod_eq_zero, Finsupp, Finsupp.mem_support_iff.mp, Finsupp.prod, aeval_monomial, killCompl, mem_support_iff, mul_eq_zero_of_right, prod_eq_zero, zero_pow
-/
lemma killCompl_monomial_eq_zero_of_notMem_range {s : τ ->₀ Nat} (c : R)
    {a : τ} (ha : a in s.support) (hs : a ∉ Set.range f) :
    (monomial s c).killCompl hf = 0 := by
  rw [killCompl]; rw [aeval_monomial]; rw [Finsupp.prod]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero ha
  simp [hs, zero_pow (Finsupp.mem_support_iff.mp ha)]

/--
lemma `killCompl_monomial_eq_zero_of_not_subset` / 引理 `killCompl_monomial_eq_zero_of_not_subset`

English:
lemma killCompl_monomial_eq_zero_of_not_subset
  statement: {s : τ ->₀ Nat} (c : R)
  proof: have ⟨_, ha, hs⟩ := Set.not_subset.mp hs
  killCompl_monomial_eq_zero_of_notMem_range hf c ha hs

中文:
引理 killCompl_monomial_eq_zero_of_not_subset
  结论: {s : τ ->₀ 自然数} (c : R)
  证明: have ⟨_, ha, hs⟩ := Set.not_subset.mp hs
  killCompl_monomial_eq_zero_of_notMem_range hf c ha hs

Depends on / 依赖: Set.not_subset.mp, killCompl_monomial_eq_zero_of_notMem_range, not_subset
-/
lemma killCompl_monomial_eq_zero_of_not_subset {s : τ ->₀ Nat} (c : R)
    (hs : ¬ ↑s.support subseteq Set.range f) : (monomial s c).killCompl hf = 0 :=
  have ⟨_, ha, hs⟩ := Set.not_subset.mp hs
  killCompl_monomial_eq_zero_of_notMem_range hf c ha hs

/--
lemma `killCompl_monomial_eq_monomial_comapDomain_of_subset` / 引理 `killCompl_monomial_eq_monomial_comapDomain_of_subset`

English:
lemma killCompl_monomial_eq_monomial_comapDomain_of_subset
  statement: {s : τ ->₀ Nat} (c : R)
  proof: by
  nth_rw 1 [← s.mapDomain_comapDomain f hf hs, killCompl_monomial_mapDomain]

中文:
引理 killCompl_monomial_eq_monomial_comapDomain_of_subset
  结论: {s : τ ->₀ 自然数} (c : R)
  证明: by
  nth_rw 1 [← s.mapDomain_comapDomain f hf hs, killCompl_monomial_mapDomain]

Depends on / 依赖: killCompl_monomial_mapDomain, mapDomain_comapDomain, nth_rw, s.mapDomain_comapDomain
-/
lemma killCompl_monomial_eq_monomial_comapDomain_of_subset {s : τ ->₀ Nat} (c : R)
    (hs : ↑s.support subseteq Set.range f) :
    (monomial s c).killCompl hf = monomial (s.comapDomain f hf.injOn) c := by
  nth_rw 1 [← s.mapDomain_comapDomain f hf hs, killCompl_monomial_mapDomain]

/--
lemma `killCompl_monomial` / 引理 `killCompl_monomial`

English:
lemma killCompl_monomial
  given: {s} {c : R} [Decidable (↑s.support subseteq Set.range f)]
  proof: by
  split_ifs with h
  · exact killCompl_monomial_eq_monomial_comapDomain_of_subset hf c h
  · exact killCompl_monomial_eq_zero_of_not_subset hf c h

中文:
引理 killCompl_monomial
  条件: {s} {c : R} [可判定 (↑s.support subseteq 集合.range f)]
  证明: by
  split_ifs with h
  · exact killCompl_monomial_eq_monomial_comapDomain_of_subset hf c h
  · exact killCompl_monomial_eq_zero_of_not_subset hf c h

Depends on / 依赖: killCompl_monomial_eq_monomial_comapDomain_of_subset, killCompl_monomial_eq_zero_of_not_subset, split_ifs
-/
lemma killCompl_monomial {s} {c : R} [Decidable (↑s.support subseteq Set.range f)] :
    (monomial s c).killCompl hf =
      if ↑s.support subseteq Set.range f then monomial (s.comapDomain f hf.injOn) c else 0 := by
  split_ifs with h
  · exact killCompl_monomial_eq_monomial_comapDomain_of_subset hf c h
  · exact killCompl_monomial_eq_zero_of_not_subset hf c h

/--
lemma `coeff_killCompl` / 引理 `coeff_killCompl`

English:
lemma coeff_killCompl
  given: {s}
  proof: by
  classical
  apply p.induction_on' (P := fun p => (p.killCompl hf).coeff s = p.coeff (s.mapDomain f))
  · intro u r
    rw [killCompl_monomial]
    split_ifs with h
    · simp [← (Finsupp.mapDomain_injective hf).eq_iff, u.mapDomain_comapDomain _ hf h]
    · simp? says simp only [coeff_zero, coef

中文:
引理 coeff_killCompl
  条件: {s}
  证明: by
  classical
  apply p.induction_on' (P := fun p => (p.killCompl hf).coeff s = p.coeff (s.mapDomain f))
  · intro u r
    rw [killCompl_monomial]
    split_ifs with h
    · simp [← (Finsupp.mapDomain_injective hf).eq_iff, u.mapDomain_comapDomain _ hf h]
    · simp? says simp only [coeff_zero, coef

Depends on / 依赖: Finsupp, Finsupp.mapDomain_injective, Finsupp.mapDomain_support, SetLike, SetLike.coe_subset_coe.mpr, classical, coe_subset_coe, coeff_monomial, coeff_zero, contrapose, eq_iff, induction_on, killCompl, killCompl_monomial, mapDomain, mapDomain_comapDomain, mapDomain_injective, mapDomain_support, p.coeff, p.induction_on
-/
lemma coeff_killCompl {s} :
    (p.killCompl hf).coeff s = p.coeff (s.mapDomain f) := by
  classical
  apply p.induction_on' (P := fun p => (p.killCompl hf).coeff s = p.coeff (s.mapDomain f))
  · intro u r
    rw [killCompl_monomial]
    split_ifs with h
    · simp [← (Finsupp.mapDomain_injective hf).eq_iff, u.mapDomain_comapDomain _ hf h]
    · simp? says simp only [coeff_zero, coeff_monomial, right_eq_ite_iff]
      intro rfl
      contrapose! h
apply subset_trans SetLike.coe_subset_coe.mpr Finsupp.mapDomain_support
      simp
  · simp_intro ..

/--
lemma `support_killCompl` / 引理 `support_killCompl`

English:
lemma support_killCompl
  given: {p : MvPolynomial τ R}
  proof: by
  ext x
  simp [coeff_killCompl]

中文:
引理 support_killCompl
  条件: {p : 多元多项式 τ R}
  证明: by
  ext x
  simp [coeff_killCompl]

Depends on / 依赖: coeff_killCompl
-/
lemma support_killCompl {p : MvPolynomial τ R} :
    (p.killCompl hf).support =
      p.support.preimage (Finsupp.mapDomain f) (Finsupp.mapDomain_injective hf).injOn := by
  ext x
  simp [coeff_killCompl]

end

section

variable (R)

/-- `MvPolynomial.rename e` is an equivalence when `e` is. -/
@[simps apply]
/--
Definition of `renameEquiv` / `renameEquiv` 的定义

English:
definition renameEquiv
  signature: (f : σ ≃ τ)
  body: { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id_apply]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id_apply] }

@[simp]

中文:
定义 renameEquiv
  签名: (f : σ ≃ τ)
  定义体: { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id_apply]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id_apply] }

@[simp]

Depends on / 依赖: f.self_comp_symm, f.symm, f.symm_comp_self, invFun, left_inv, rename_id_apply, rename_rename, right_inv, self_comp_symm, symm_comp_self
-/
def renameEquiv (f : σ ≃ τ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R :=
  { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id_apply]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id_apply] }

@[simp]
/--
theorem `renameEquiv_refl` / 定理 `renameEquiv_refl`

English:
theorem renameEquiv_refl
  statement: renameEquiv R (Equiv.refl σ) = AlgEquiv.refl
  proof: AlgEquiv.ext (by simp)

@[simp]

中文:
定理 renameEquiv_refl
  结论: renameEquiv R (等价.refl σ) = 代数等价.refl
  证明: AlgEquiv.ext (by simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ext
-/
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl :=
  AlgEquiv.ext (by simp)

@[simp]
/--
theorem `renameEquiv_symm` / 定理 `renameEquiv_symm`

English:
theorem renameEquiv_symm
  given: (f : σ ≃ τ)
  statement: (renameEquiv R f).symm = renameEquiv R f.symm
  proof: rfl

@[simp]

中文:
定理 renameEquiv_symm
  条件: (f : σ ≃ τ)
  结论: (renameEquiv R f).symm = renameEquiv R f.symm
  证明: rfl

@[simp]
-/
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm :=
  rfl

@[simp]
/--
theorem `renameEquiv_trans` / 定理 `renameEquiv_trans`

English:
theorem renameEquiv_trans
  given: (e : σ ≃ τ) (f : τ ≃ α)
  proof: AlgEquiv.ext (rename_rename e f)

中文:
定理 renameEquiv_trans
  条件: (e : σ ≃ τ) (f : τ ≃ α)
  证明: AlgEquiv.ext (rename_rename e f)

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, rename_rename
-/
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ α) :
    (renameEquiv R e).trans (renameEquiv R f) = renameEquiv R (e.trans f) :=
  AlgEquiv.ext (rename_rename e f)

end

section

variable (f : R ->+* S) (k : σ -> τ) (g : τ -> S) (p : MvPolynomial σ R)

/--
theorem `eval₂_rename` / 定理 `eval₂_rename`

English:
theorem eval₂_rename
  statement: (rename k p).eval₂ f g = p.eval₂ f (g ∘ k)
  proof: by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

中文:
定理 eval₂_rename
  结论: (rename k p).eval₂ f g = p.eval₂ f (g ∘ k)
  证明: by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, induction_on, intros
-/
theorem eval₂_rename : (rename k p).eval₂ f g = p.eval₂ f (g ∘ k) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

/--
theorem `eval_rename` / 定理 `eval_rename`

English:
theorem eval_rename
  given: (g : τ -> R) (p : MvPolynomial σ R)
  statement: eval g (rename k p) = eval (g ∘ k) p
  proof: eval₂_rename _ _ _ _

中文:
定理 eval_rename
  条件: (g : τ -> R) (p : 多元多项式 σ R)
  结论: eval g (rename k p) = eval (g ∘ k) p
  证明: eval₂_rename _ _ _ _
-/
theorem eval_rename (g : τ -> R) (p : MvPolynomial σ R) : eval g (rename k p) = eval (g ∘ k) p :=
  eval₂_rename _ _ _ _

/--
theorem `eval₂Hom_rename` / 定理 `eval₂Hom_rename`

English:
theorem eval₂Hom_rename
  statement: eval₂Hom f g (rename k p) = eval₂Hom f (g ∘ k) p
  proof: eval₂_rename _ _ _ _

中文:
定理 eval₂Hom_rename
  结论: eval₂Hom f g (rename k p) = eval₂Hom f (g ∘ k) p
  证明: eval₂_rename _ _ _ _
-/
theorem eval₂Hom_rename : eval₂Hom f g (rename k p) = eval₂Hom f (g ∘ k) p :=
  eval₂_rename _ _ _ _

/--
theorem `aeval_rename` / 定理 `aeval_rename`

English:
theorem aeval_rename
  given: [Algebra R S]
  statement: aeval g (rename k p) = aeval (g ∘ k) p
  proof: eval₂Hom_rename _ _ _ _

中文:
定理 aeval_rename
  条件: [代数 R S]
  结论: aeval g (rename k p) = aeval (g ∘ k) p
  证明: eval₂Hom_rename _ _ _ _
-/
theorem aeval_rename [Algebra R S] : aeval g (rename k p) = aeval (g ∘ k) p :=
  eval₂Hom_rename _ _ _ _

/--
lemma `aeval_comp_rename` / 引理 `aeval_comp_rename`

English:
lemma aeval_comp_rename
  given: [Algebra R S]
  proof: AlgHom.ext fun p => aeval_rename k g p

中文:
引理 aeval_comp_rename
  条件: [代数 R S]
  证明: AlgHom.ext fun p => aeval_rename k g p

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval
-/
lemma aeval_comp_rename [Algebra R S] :
    (aeval (R := R) g).comp (rename k) = MvPolynomial.aeval (g ∘ k) :=
  AlgHom.ext fun p => aeval_rename k g p

/--
theorem `rename_eval₂` / 定理 `rename_eval₂`

English:
theorem rename_eval₂
  given: (g : τ -> MvPolynomial σ R)
  proof: by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

中文:
定理 rename_eval₂
  条件: (g : τ -> 多元多项式 σ R)
  证明: by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, induction_on, intros
-/
theorem rename_eval₂ (g : τ -> MvPolynomial σ R) :
    rename k (p.eval₂ C (g ∘ k)) = (rename k p).eval₂ C (rename k ∘ g) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

/--
theorem `rename_prod_mk_eval₂` / 定理 `rename_prod_mk_eval₂`

English:
theorem rename_prod_mk_eval₂
  given: (j : τ) (g : σ -> MvPolynomial σ R)
  proof: by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

中文:
定理 rename_prod_mk_eval₂
  条件: (j : τ) (g : σ -> 多元多项式 σ R)
  证明: by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, induction_on, intros
-/
theorem rename_prod_mk_eval₂ (j : τ) (g : σ -> MvPolynomial σ R) :
    rename (Prod.mk j) (p.eval₂ C g) = p.eval₂ C fun x => rename (Prod.mk j) (g x) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

/--
theorem `eval₂_rename_prod_mk` / 定理 `eval₂_rename_prod_mk`

English:
theorem eval₂_rename_prod_mk
  given: (g : σ × τ -> S) (i : σ) (p : MvPolynomial τ R)
  proof: by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

中文:
定理 eval₂_rename_prod_mk
  条件: (g : σ × τ -> S) (i : σ) (p : 多元多项式 τ R)
  证明: by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, induction_on, intros
-/
theorem eval₂_rename_prod_mk (g : σ × τ -> S) (i : σ) (p : MvPolynomial τ R) :
    (rename (Prod.mk i) p).eval₂ f g = eval₂ f (fun j => g (i, j)) p := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

/--
theorem `eval_rename_prod_mk` / 定理 `eval_rename_prod_mk`

English:
theorem eval_rename_prod_mk
  given: (g : σ × τ -> R) (i : σ) (p : MvPolynomial τ R)
  proof: eval₂_rename_prod_mk (RingHom.id _) _ _ _

中文:
定理 eval_rename_prod_mk
  条件: (g : σ × τ -> R) (i : σ) (p : 多元多项式 τ R)
  证明: eval₂_rename_prod_mk (RingHom.id _) _ _ _

Depends on / 依赖: RingHom, RingHom.id
-/
theorem eval_rename_prod_mk (g : σ × τ -> R) (i : σ) (p : MvPolynomial τ R) :
    eval g (rename (Prod.mk i) p) = eval (fun j => g (i, j)) p :=
  eval₂_rename_prod_mk (RingHom.id _) _ _ _

end

/--
theorem `exists_finset_rename` / 定理 `exists_finset_rename`

English:
theorem exists_finset_rename
  given: (p : MvPolynomial σ R)
  proof: by
  classical
  apply induction_on p
  · intro r
    exact ⟨∅, C r, by rw [rename_C]⟩
  · rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩
    refine ⟨s union t, ⟨?_, ?_⟩⟩
    · refine rename (Subtype.map id ?_) p + rename (Subtype.map id ?_) q <;>
        simp +contextual only [id, true_or, or_true,
          F

中文:
定理 存在_finset_rename
  条件: (p : 多元多项式 σ R)
  证明: by
  classical
  apply induction_on p
  · intro r
    exact ⟨∅, C r, by rw [rename_C]⟩
  · rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩
    refine ⟨s union t, ⟨?_, ?_⟩⟩
    · refine rename (Subtype.map id ?_) p + rename (Subtype.map id ?_) q <;>
        simp +contextual only [id, true_or, or_true,
          F

Depends on / 依赖: Finset, Finset.mem_union, Subtype, Subtype.map, classical, contextual, forall_true_iff, induction_on, insert, map_add, mem_insert_self, mem_union, or_true, rename_C, rename_rename, s.mem_insert_self, true_or
-/
theorem exists_finset_rename (p : MvPolynomial σ R) :
    exists (s : Finset σ) (q : MvPolynomial { x // x in s } R), p = rename (↑) q := by
  classical
  apply induction_on p
  · intro r
    exact ⟨∅, C r, by rw [rename_C]⟩
  · rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩
    refine ⟨s union t, ⟨?_, ?_⟩⟩
    · refine rename (Subtype.map id ?_) p + rename (Subtype.map id ?_) q <;>
        simp +contextual only [id, true_or, or_true,
          Finset.mem_union, forall_true_iff]
    · simp only [rename_rename, map_add]
      rfl
  · rintro p n ⟨s, p, rfl⟩
    refine ⟨insert n s, ⟨?_, ?_⟩⟩
    · refine rename (Subtype.map id ?_) p * X ⟨n, s.mem_insert_self n⟩
      simp +contextual only [id, or_true, Finset.mem_insert, forall_true_iff]
    · simp only [rename_rename, rename_X, map_mul]
      rfl

/--
theorem `exists_finset_rename₂` / 定理 `exists_finset_rename₂`

English:
theorem exists_finset_rename₂
  given: (p₁ p₂ : MvPolynomial σ R)
  proof: by
  obtain ⟨s₁, q₁, rfl⟩ := exists_finset_rename p₁
  obtain ⟨s₂, q₂, rfl⟩ := exists_finset_rename p₂
  classical
    use s₁ union s₂
    use rename (fun x => ⟨x, Finset.subset_union_left x.2⟩) q₁
    use rename (fun x => ⟨x, Finset.subset_union_right x.2⟩) q₂
    constructor <;> simp [Function.com

中文:
定理 存在_finset_rename₂
  条件: (p₁ p₂ : 多元多项式 σ R)
  证明: by
  obtain ⟨s₁, q₁, rfl⟩ := exists_finset_rename p₁
  obtain ⟨s₂, q₂, rfl⟩ := exists_finset_rename p₂
  classical
    use s₁ union s₂
    use rename (fun x => ⟨x, Finset.subset_union_left x.2⟩) q₁
    use rename (fun x => ⟨x, Finset.subset_union_right x.2⟩) q₂
    constructor <;> simp [Function.com

Depends on / 依赖: Finset, Finset.subset_union_left, Finset.subset_union_right, Function, Function.comp_def, classical, comp_def, exists_finset_rename, subset_union_left, subset_union_right
-/
theorem exists_finset_rename₂ (p₁ p₂ : MvPolynomial σ R) :
    exists (s : Finset σ) (q₁ q₂ : MvPolynomial s R), p₁ = rename (↑) q₁ ∧ p₂ = rename (↑) q₂ := by
  obtain ⟨s₁, q₁, rfl⟩ := exists_finset_rename p₁
  obtain ⟨s₂, q₂, rfl⟩ := exists_finset_rename p₂
  classical
    use s₁ union s₂
    use rename (fun x => ⟨x, Finset.subset_union_left x.2⟩) q₁
    use rename (fun x => ⟨x, Finset.subset_union_right x.2⟩) q₂
    constructor <;> simp [Function.comp_def]

/--
theorem `exists_fin_rename` / 定理 `exists_fin_rename`

English:
theorem exists_fin_rename
  given: (p : MvPolynomial σ R)
  proof: by
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  let n := Fintype.card { x // x in s }
  let e := Fintype.equivFin { x // x in s }
  refine ⟨n, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective, rename e q, ?_⟩
  rw [← rename_rename]; rw [rename_rename e]
  simp only [Function.comp_def, E

中文:
定理 存在_fin_rename
  条件: (p : 多元多项式 σ R)
  证明: by
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  let n := Fintype.card { x // x in s }
  let e := Fintype.equivFin { x // x in s }
  refine ⟨n, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective, rename e q, ?_⟩
  rw [← rename_rename]; rw [rename_rename e]
  simp only [Function.comp_def, E

Depends on / 依赖: Equiv.symm_apply_apply, Fintype, Fintype.card, Fintype.equivFin, Function, Function.comp_def, Subtype, Subtype.val_injective.comp, comp_def, e.symm, e.symm.injective, equivFin, exists_finset_rename, injective, rename_rename, symm_apply_apply, val_injective
-/
theorem exists_fin_rename (p : MvPolynomial σ R) :
    exists (n : Nat) (f : Fin n -> σ) (_hf : Injective f) (q : MvPolynomial (Fin n) R), p = rename f q := by
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  let n := Fintype.card { x // x in s }
  let e := Fintype.equivFin { x // x in s }
  refine ⟨n, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective, rename e q, ?_⟩
  rw [← rename_rename]; rw [rename_rename e]
  simp only [Function.comp_def, Equiv.symm_apply_apply, rename_rename]

end Rename

/--
theorem `eval₂_cast_comp` / 定理 `eval₂_cast_comp`

English:
theorem eval₂_cast_comp
  given: (f : σ -> τ) (c : Int ->+* R) (g : τ -> R) (p : MvPolynomial σ Int)
  proof: (eval₂_rename c f g p).symm

中文:
定理 eval₂_cast_comp
  条件: (f : σ -> τ) (c : 整数 ->+* R) (g : τ -> R) (p : 多元多项式 σ 整数)
  证明: (eval₂_rename c f g p).symm
-/
theorem eval₂_cast_comp (f : σ -> τ) (c : Int ->+* R) (g : τ -> R) (p : MvPolynomial σ Int) :
    eval₂ c (g ∘ f) p = eval₂ c g (rename f p) := (eval₂_rename c f g p).symm

section Coeff

@[simp]
/--
theorem `coeff_rename_mapDomain` / 定理 `coeff_rename_mapDomain`

English:
theorem coeff_rename_mapDomain
  given: (f : σ -> τ) (hf : Injective f) (φ : MvPolynomial σ R) (d : σ ->₀ Nat)
  proof: by
  classical
  induction φ using MvPolynomial.induction_on' with
  | monomial u r =>
    rw [rename_monomial]; rw [coeff_monomial]; rw [coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hf).eq_iff]
  | add =>
    simp only [*, map_add, coeff_add]

@[simp]

中文:
定理 coeff_rename_mapDomain
  条件: (f : σ -> τ) (hf : 单射 f) (φ : 多元多项式 σ R) (d : σ ->₀ 自然数)
  证明: by
  classical
  induction φ using MvPolynomial.induction_on' with
  | monomial u r =>
    rw [rename_monomial]; rw [coeff_monomial]; rw [coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hf).eq_iff]
  | add =>
    simp only [*, map_add, coeff_add]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_injective, MvPolynomial, MvPolynomial.induction_on, classical, coeff_add, coeff_monomial, eq_iff, induction_on, mapDomain_injective, map_add, monomial, rename_monomial
-/
theorem coeff_rename_mapDomain (f : σ -> τ) (hf : Injective f) (φ : MvPolynomial σ R) (d : σ ->₀ Nat) :
    (rename f φ).coeff (d.mapDomain f) = φ.coeff d := by
  classical
  induction φ using MvPolynomial.induction_on' with
  | monomial u r =>
    rw [rename_monomial]; rw [coeff_monomial]; rw [coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hf).eq_iff]
  | add =>
    simp only [*, map_add, coeff_add]

@[simp]
/--
theorem `coeff_rename_embDomain` / 定理 `coeff_rename_embDomain`

English:
theorem coeff_rename_embDomain
  given: (f : σ ↪ τ) (φ : MvPolynomial σ R) (d : σ ->₀ Nat)
  proof: by
  rw [Finsupp.embDomain_eq_mapDomain f]; rw [coeff_rename_mapDomain f f.injective]

中文:
定理 coeff_rename_embDomain
  条件: (f : σ ↪ τ) (φ : 多元多项式 σ R) (d : σ ->₀ 自然数)
  证明: by
  rw [Finsupp.embDomain_eq_mapDomain f]; rw [coeff_rename_mapDomain f f.injective]

Depends on / 依赖: Finsupp, Finsupp.embDomain_eq_mapDomain, coeff_rename_mapDomain, embDomain_eq_mapDomain, f.injective, injective
-/
theorem coeff_rename_embDomain (f : σ ↪ τ) (φ : MvPolynomial σ R) (d : σ ->₀ Nat) :
    (rename f φ).coeff (d.embDomain f) = φ.coeff d := by
  rw [Finsupp.embDomain_eq_mapDomain f]; rw [coeff_rename_mapDomain f f.injective]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeff_rename_eq_zero` / 定理 `coeff_rename_eq_zero`

English:
theorem coeff_rename_eq_zero
  statement: (f : σ -> τ) (φ : MvPolynomial σ R) (d : τ ->₀ Nat)
  proof: by
  classical
  rw [← notMem_support_iff]
  intro H
  replace H := mapDomain_support H
  rw [Finset.mem_image] at H
  obtain ⟨u, hu, rfl⟩ := H
  specialize h u rfl
  rw [Finsupp.mem_support_iff] at hu
  contradiction

中文:
定理 coeff_rename_eq_zero
  结论: (f : σ -> τ) (φ : 多元多项式 σ R) (d : τ ->₀ 自然数)
  证明: by
  classical
  rw [← notMem_support_iff]
  intro H
  replace H := mapDomain_support H
  rw [Finset.mem_image] at H
  obtain ⟨u, hu, rfl⟩ := H
  specialize h u rfl
  rw [Finsupp.mem_support_iff] at hu
  contradiction

Depends on / 依赖: Finset, Finset.mem_image, Finsupp, Finsupp.mem_support_iff, classical, mapDomain_support, mem_image, mem_support_iff, notMem_support_iff, replace, specialize
-/
theorem coeff_rename_eq_zero (f : σ -> τ) (φ : MvPolynomial σ R) (d : τ ->₀ Nat)
    (h : forall u : σ ->₀ Nat, u.mapDomain f = d -> φ.coeff u = 0) : (rename f φ).coeff d = 0 := by
  classical
  rw [← notMem_support_iff]
  intro H
  replace H := mapDomain_support H
  rw [Finset.mem_image] at H
  obtain ⟨u, hu, rfl⟩ := H
  specialize h u rfl
  rw [Finsupp.mem_support_iff] at hu
  contradiction

/--
theorem `coeff_rename_ne_zero` / 定理 `coeff_rename_ne_zero`

English:
theorem coeff_rename_ne_zero
  statement: (f : σ -> τ) (φ : MvPolynomial σ R) (d : τ ->₀ Nat)
  proof: by
  contrapose! h
  apply coeff_rename_eq_zero _ _ _ h

@[simp]

中文:
定理 coeff_rename_ne_zero
  结论: (f : σ -> τ) (φ : 多元多项式 σ R) (d : τ ->₀ 自然数)
  证明: by
  contrapose! h
  apply coeff_rename_eq_zero _ _ _ h

@[simp]

Depends on / 依赖: coeff_rename_eq_zero, contrapose
-/
theorem coeff_rename_ne_zero (f : σ -> τ) (φ : MvPolynomial σ R) (d : τ ->₀ Nat)
    (h : (rename f φ).coeff d != 0) : exists u : σ ->₀ Nat, u.mapDomain f = d ∧ φ.coeff u != 0 := by
  contrapose! h
  apply coeff_rename_eq_zero _ _ _ h

@[simp]
/--
theorem `constantCoeff_rename` / 定理 `constantCoeff_rename`

English:
theorem constantCoeff_rename
  given: {τ : Type*} (f : σ -> τ) (φ : MvPolynomial σ R)
  proof: by
  apply φ.induction_on
  · intro a
    simp only [constantCoeff_C, rename_C]
  · intro p q hp hq
    simp only [hp, hq, map_add]
  · intro p n hp
    simp only [hp, rename_X, constantCoeff_X, map_mul]

中文:
定理 constantCoeff_rename
  条件: {τ : 类型} (f : σ -> τ) (φ : 多元多项式 σ R)
  证明: by
  apply φ.induction_on
  · intro a
    simp only [constantCoeff_C, rename_C]
  · intro p q hp hq
    simp only [hp, hq, map_add]
  · intro p n hp
    simp only [hp, rename_X, constantCoeff_X, map_mul]

Depends on / 依赖: constantCoeff_C, constantCoeff_X, induction_on, map_add, map_mul, rename_C, rename_X
-/
theorem constantCoeff_rename {τ : Type*} (f : σ -> τ) (φ : MvPolynomial σ R) :
    constantCoeff (rename f φ) = constantCoeff φ := by
  apply φ.induction_on
  · intro a
    simp only [constantCoeff_C, rename_C]
  · intro p q hp hq
    simp only [hp, hq, map_add]
  · intro p n hp
    simp only [hp, rename_X, constantCoeff_X, map_mul]

end Coeff

section Support

/--
theorem `support_rename_of_injective` / 定理 `support_rename_of_injective`

English:
theorem support_rename_of_injective
  statement: {p : MvPolynomial σ R} {f : σ -> τ} [DecidableEq τ]
  proof: Finsupp.mapDomain_support_of_injective (Finsupp.mapDomain_injective h) _

中文:
定理 support_rename_of_injective
  结论: {p : 多元多项式 σ R} {f : σ -> τ} [DecidableEq τ]
  证明: Finsupp.mapDomain_support_of_injective (Finsupp.mapDomain_injective h) _

Depends on / 依赖: Finsupp, Finsupp.mapDomain_injective, Finsupp.mapDomain_support_of_injective, mapDomain_injective, mapDomain_support_of_injective
-/
theorem support_rename_of_injective {p : MvPolynomial σ R} {f : σ -> τ} [DecidableEq τ]
    (h : Function.Injective f) :
    (rename f p).support = Finset.image (Finsupp.mapDomain f) p.support :=
  Finsupp.mapDomain_support_of_injective (Finsupp.mapDomain_injective h) _

/--
lemma `support_rename_killCompl_subset` / 引理 `support_rename_killCompl_subset`

English:
lemma support_rename_killCompl_subset
  given: {p : MvPolynomial τ R} {f : σ -> τ} (hf : f.Injective)
  proof: by
  classical
  rw [MvPolynomial.support_rename_of_injective hf]; rw [support_killCompl]; rw [Finset.image_preimage]
  exact Finset.filter_subset ..

中文:
引理 support_rename_killCompl_subset
  条件: {p : 多元多项式 τ R} {f : σ -> τ} (hf : f.单射)
  证明: by
  classical
  rw [MvPolynomial.support_rename_of_injective hf]; rw [support_killCompl]; rw [Finset.image_preimage]
  exact Finset.filter_subset ..

Depends on / 依赖: Finset, Finset.filter_subset, Finset.image_preimage, MvPolynomial, MvPolynomial.support_rename_of_injective, classical, filter_subset, image_preimage, support_killCompl, support_rename_of_injective
-/
lemma support_rename_killCompl_subset {p : MvPolynomial τ R} {f : σ -> τ} (hf : f.Injective) :
    ((p.killCompl hf).rename f).support subseteq p.support := by
  classical
  rw [MvPolynomial.support_rename_of_injective hf]; rw [support_killCompl]; rw [Finset.image_preimage]
  exact Finset.filter_subset ..

end Support

end MvPolynomial
