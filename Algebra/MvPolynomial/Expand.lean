/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.Order.Ring.Finset

/-!
## Expand multivariate polynomials

Given a multivariate polynomial `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some natural number `n`.
This operation is called `MvPolynomial.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPolynomial.expand`: expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

@[expose] public section


namespace MvPolynomial

section CommSemiring

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : Nat)

/--
Definition of `expand` / `expand` 的定义

English:
definition expand
  signature: : MvPolynomial σ R ->ₐ[R] MvPolynomial σ R
  body: bind₁ fun i => X i ^ p

中文:
定义 expand
  签名: : 多元多项式 σ R ->ₐ[R] 多元多项式 σ R
  定义体: bind₁ fun i => X i ^ p
-/
noncomputable def expand : MvPolynomial σ R ->ₐ[R] MvPolynomial σ R :=
  bind₁ fun i => X i ^ p

/--
theorem `coe_expand` / 定理 `coe_expand`

English:
theorem coe_expand
  proof: rfl

中文:
定理 coe_expand
  证明: rfl

Depends on / 依赖: MvPolynomial
-/
theorem coe_expand :
    (expand p (R := R) (σ := σ)) = eval₂ C ((fun s => X s : σ -> MvPolynomial σ R) ^ p) := rfl

/--
theorem `expand_C` / 定理 `expand_C`

English:
theorem expand_C
  given: (r : R)
  statement: expand p (C r : MvPolynomial σ R) = C r
  proof: eval₂Hom_C _ _ _

@[simp]

中文:
定理 expand_C
  条件: (r : R)
  结论: expand p (C r : 多元多项式 σ R) = C r
  证明: eval₂Hom_C _ _ _

@[simp]
-/
theorem expand_C (r : R) : expand p (C r : MvPolynomial σ R) = C r :=
  eval₂Hom_C _ _ _

@[simp]
/--
theorem `expand_X` / 定理 `expand_X`

English:
theorem expand_X
  given: (i : σ)
  statement: expand p (X i : MvPolynomial σ R) = X i ^ p
  proof: eval₂Hom_X' _ _ _

@[simp]

中文:
定理 expand_X
  条件: (i : σ)
  结论: expand p (X i : 多元多项式 σ R) = X i ^ p
  证明: eval₂Hom_X' _ _ _

@[simp]
-/
theorem expand_X (i : σ) : expand p (X i : MvPolynomial σ R) = X i ^ p :=
  eval₂Hom_X' _ _ _

@[simp]
/--
theorem `expand_monomial` / 定理 `expand_monomial`

English:
theorem expand_monomial
  given: (d : σ ->₀ Nat) (r : R)
  proof: by
  rw [expand]; rw [bind₁_monomial]; rw [monomial_eq]; rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul]
  · simp

@[simp]

中文:
定理 expand_monomial
  条件: (d : σ ->₀ 自然数) (r : R)
  证明: by
  rw [expand]; rw [bind₁_monomial]; rw [monomial_eq]; rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul]
  · simp

@[simp]

Depends on / 依赖: Finsupp, Finsupp.prod_of_support_subset, Finsupp.support_smul, expand, monomial_eq, pow_mul, prod_of_support_subset, support_smul
-/
theorem expand_monomial (d : σ ->₀ Nat) (r : R) :
    expand p (monomial d r) = monomial (p • d) r := by
  rw [expand]; rw [bind₁_monomial]; rw [monomial_eq]; rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul]
  · simp

@[simp]
/--
lemma `expand_zero` / 引理 `expand_zero`

English:
lemma expand_zero
  proof: by
  ext1 i
  simp

中文:
引理 expand_zero
  证明: by
  ext1 i
  simp

Depends on / 依赖: Algebra, Algebra.ofId, MvPolynomial, MvPolynomial.aeval
-/
lemma expand_zero :
    expand 0 (σ := σ) (R := R) = .comp (Algebra.ofId R _) (MvPolynomial.aeval (1 : σ -> R)) := by
  ext1 i
  simp

/--
lemma `expand_zero_apply` / 引理 `expand_zero_apply`

English:
lemma expand_zero_apply
  given: (f : MvPolynomial σ R)
  statement: expand 0 f = .C (MvPolynomial.eval 1 f)
  proof: by
  simp

@[simp]

中文:
引理 expand_zero_apply
  条件: (f : 多元多项式 σ R)
  结论: expand 0 f = .C (多元多项式.eval 1 f)
  证明: by
  simp

@[simp]
-/
lemma expand_zero_apply (f : MvPolynomial σ R) : expand 0 f = .C (MvPolynomial.eval 1 f) := by
  simp

@[simp]
/--
theorem `expand_one` / 定理 `expand_one`

English:
theorem expand_one
  statement: expand 1 = AlgHom.id R (MvPolynomial σ R)
  proof: by
  ext1 i
  simp

中文:
定理 expand_one
  结论: expand 1 = 代数态射.id R (多元多项式 σ R)
  证明: by
  ext1 i
  simp
-/
theorem expand_one : expand 1 = AlgHom.id R (MvPolynomial σ R) := by
  ext1 i
  simp

/--
theorem `expand_one_apply` / 定理 `expand_one_apply`

English:
theorem expand_one_apply
  given: (f : MvPolynomial σ R)
  statement: expand 1 f = f
  proof: by simp

中文:
定理 expand_one_apply
  条件: (f : 多元多项式 σ R)
  结论: expand 1 f = f
  证明: by simp
-/
theorem expand_one_apply (f : MvPolynomial σ R) : expand 1 f = f := by simp

/--
theorem `expand_mul_eq_comp` / 定理 `expand_mul_eq_comp`

English:
theorem expand_mul_eq_comp
  given: (q : Nat)
  proof: by
  ext1 i
  simp [pow_mul]

中文:
定理 expand_mul_eq_comp
  条件: (q : 自然数)
  证明: by
  ext1 i
  simp [pow_mul]

Depends on / 依赖: expand, pow_mul
-/
theorem expand_mul_eq_comp (q : Nat) :
    expand (σ := σ) (R := R) (p * q) = (expand p).comp (expand q) := by
  ext1 i
  simp [pow_mul]

/--
theorem `expand_mul` / 定理 `expand_mul`

English:
theorem expand_mul
  given: (q : Nat) (φ : MvPolynomial σ R)
  statement: φ.expand (p * q) = (φ.expand q).expand p
  proof: DFunLike.congr_fun (expand_mul_eq_comp p q) φ

@[simp]

中文:
定理 expand_mul
  条件: (q : 自然数) (φ : 多元多项式 σ R)
  结论: φ.expand (p * q) = (φ.expand q).expand p
  证明: DFunLike.congr_fun (expand_mul_eq_comp p q) φ

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, expand_mul_eq_comp
-/
theorem expand_mul (q : Nat) (φ : MvPolynomial σ R) : φ.expand (p * q) = (φ.expand q).expand p :=
  DFunLike.congr_fun (expand_mul_eq_comp p q) φ

@[simp]
/--
lemma `coeff_expand_smul` / 引理 `coeff_expand_smul`

English:
lemma coeff_expand_smul
  given: (hp : p != 0) (φ : MvPolynomial σ R) (m : σ ->₀ Nat)
  proof: by
  classical
  induction φ using induction_on' <;> simp [*, nsmul_right_inj hp]

@[simp]

中文:
引理 coeff_expand_smul
  条件: (hp : p != 0) (φ : 多元多项式 σ R) (m : σ ->₀ 自然数)
  证明: by
  classical
  induction φ using induction_on' <;> simp [*, nsmul_right_inj hp]

@[simp]

Depends on / 依赖: classical, induction_on, nsmul_right_inj
-/
lemma coeff_expand_smul (hp : p != 0) (φ : MvPolynomial σ R) (m : σ ->₀ Nat) :
    (expand p φ).coeff (p • m) = φ.coeff m := by
  classical
  induction φ using induction_on' <;> simp [*, nsmul_right_inj hp]

@[simp]
/--
lemma `coeff_expand_zero` / 引理 `coeff_expand_zero`

English:
lemma coeff_expand_zero
  given: (hp : p != 0) (φ : MvPolynomial σ R)
  proof: calc (expand p φ).coeff 0 = (expand p φ).coeff (p • 0) := by rw [smul_zero]
                          _ = φ.coeff 0 := by rw [coeff_expand_smul p hp]

中文:
引理 coeff_expand_zero
  条件: (hp : p != 0) (φ : 多元多项式 σ R)
  证明: calc (expand p φ).coeff 0 = (expand p φ).coeff (p • 0) := by rw [smul_zero]
                          _ = φ.coeff 0 := by rw [coeff_expand_smul p hp]

Depends on / 依赖: coeff_expand_smul, expand, smul_zero
-/
lemma coeff_expand_zero (hp : p != 0) (φ : MvPolynomial σ R) :
    (expand p φ).coeff 0 = φ.coeff 0 :=
  calc (expand p φ).coeff 0 = (expand p φ).coeff (p • 0) := by rw [smul_zero]
                          _ = φ.coeff 0 := by rw [coeff_expand_smul p hp]

/--
theorem `expand_injective` / 定理 `expand_injective`

English:
theorem expand_injective
  given: {n : Nat} (hn : 0 < n)
  statement: Function.Injective (expand n (R := R) (σ := σ))
  proof: fun g g' H => by
    ext d
    rw [← coeff_expand_smul _ (n.ne_zero_iff_zero_lt.mpr hn)]; rw [H]; rw [coeff_expand_smul _
      (n.ne_zero_iff_zero_lt.mpr hn)]

中文:
定理 expand_injective
  条件: {n : 自然数} (hn : 0 < n)
  结论: 函数.单射 (expand n (R := R) (σ := σ))
  证明: fun g g' H => by
    ext d
    rw [← coeff_expand_smul _ (n.ne_zero_iff_zero_lt.mpr hn)]; rw [H]; rw [coeff_expand_smul _
      (n.ne_zero_iff_zero_lt.mpr hn)]
-/
theorem expand_injective {n : Nat} (hn : 0 < n) : Function.Injective (expand n (R := R) (σ := σ)) :=
  fun g g' H => by
    ext d
    rw [← coeff_expand_smul _ (n.ne_zero_iff_zero_lt.mpr hn)]; rw [H]; rw [coeff_expand_smul _
      (n.ne_zero_iff_zero_lt.mpr hn)]

/--
theorem `expand_inj` / 定理 `expand_inj`

English:
theorem expand_inj
  given: {p : Nat} (hp : 0 < p) {f g : MvPolynomial σ R}
  proof: (expand_injective hp).eq_iff

中文:
定理 expand_inj
  条件: {p : 自然数} (hp : 0 < p) {f g : 多元多项式 σ R}
  证明: (expand_injective hp).eq_iff

Depends on / 依赖: eq_iff, expand_injective
-/
theorem expand_inj {p : Nat} (hp : 0 < p) {f g : MvPolynomial σ R} :
    expand p f = expand p g ↔ f = g := (expand_injective hp).eq_iff

/--
theorem `expand_eq_zero` / 定理 `expand_eq_zero`

English:
theorem expand_eq_zero
  given: {p : Nat} (hp : 0 < p) {f : MvPolynomial σ R}
  statement: expand p f = 0 ↔ f = 0
  proof: (expand_injective hp).eq_iff' (map_zero _)

中文:
定理 expand_eq_zero
  条件: {p : 自然数} (hp : 0 < p) {f : 多元多项式 σ R}
  结论: expand p f = 0 ↔ f = 0
  证明: (expand_injective hp).eq_iff' (map_zero _)

Depends on / 依赖: eq_iff, expand_injective, map_zero
-/
theorem expand_eq_zero {p : Nat} (hp : 0 < p) {f : MvPolynomial σ R} : expand p f = 0 ↔ f = 0 :=
  (expand_injective hp).eq_iff' (map_zero _)

/--
theorem `expand_ne_zero` / 定理 `expand_ne_zero`

English:
theorem expand_ne_zero
  given: {p : Nat} (hp : 0 < p) {f : MvPolynomial σ R}
  statement: expand p f != 0 ↔ f != 0
  proof: (expand_eq_zero hp).not

中文:
定理 expand_ne_zero
  条件: {p : 自然数} (hp : 0 < p) {f : 多元多项式 σ R}
  结论: expand p f != 0 ↔ f != 0
  证明: (expand_eq_zero hp).not

Depends on / 依赖: expand_eq_zero
-/
theorem expand_ne_zero {p : Nat} (hp : 0 < p) {f : MvPolynomial σ R} : expand p f != 0 ↔ f != 0 :=
  (expand_eq_zero hp).not

/--
theorem `expand_eq_C` / 定理 `expand_eq_C`

English:
theorem expand_eq_C
  given: {p : Nat} (hp : 0 < p) {f : MvPolynomial σ R} {r : R}
  proof: by
  rw [← expand_C]; rw [expand_inj hp]; rw [expand_C]

中文:
定理 expand_eq_C
  条件: {p : 自然数} (hp : 0 < p) {f : 多元多项式 σ R} {r : R}
  证明: by
  rw [← expand_C]; rw [expand_inj hp]; rw [expand_C]

Depends on / 依赖: expand_C, expand_inj
-/
theorem expand_eq_C {p : Nat} (hp : 0 < p) {f : MvPolynomial σ R} {r : R} :
    expand p f = C r ↔ f = C r := by
  rw [← expand_C]; rw [expand_inj hp]; rw [expand_C]

/--
theorem `expand_comp_bind₁` / 定理 `expand_comp_bind₁`

English:
theorem expand_comp_bind₁
  given: (p : Nat) (f : σ -> MvPolynomial τ R)
  proof: by
  ext1 i
  simp

中文:
定理 expand_comp_bind₁
  条件: (p : 自然数) (f : σ -> 多元多项式 τ R)
  证明: by
  ext1 i
  simp
-/
theorem expand_comp_bind₁ (p : Nat) (f : σ -> MvPolynomial τ R) :
    (expand p).comp (bind₁ f) = bind₁ fun i => expand p (f i) := by
  ext1 i
  simp

/--
theorem `expand_bind₁` / 定理 `expand_bind₁`

English:
theorem expand_bind₁
  given: (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R)
  proof: by
  rw [← AlgHom.comp_apply]; rw [expand_comp_bind₁]

@[simp]

中文:
定理 expand_bind₁
  条件: (f : σ -> 多元多项式 τ R) (φ : 多元多项式 σ R)
  证明: by
  rw [← AlgHom.comp_apply]; rw [expand_comp_bind₁]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.comp_apply, comp_apply
-/
theorem expand_bind₁ (f : σ -> MvPolynomial τ R) (φ : MvPolynomial σ R) :
    expand p (bind₁ f φ) = bind₁ (fun i => expand p (f i)) φ := by
  rw [← AlgHom.comp_apply]; rw [expand_comp_bind₁]

@[simp]
/--
theorem `map_expand` / 定理 `map_expand`

English:
theorem map_expand
  given: (f : R ->+* S) (φ : MvPolynomial σ R)
  proof: by simp [expand, map_bind₁]

@[simp]

中文:
定理 map_expand
  条件: (f : R ->+* S) (φ : 多元多项式 σ R)
  证明: by simp [expand, map_bind₁]

@[simp]

Depends on / 依赖: expand
-/
theorem map_expand (f : R ->+* S) (φ : MvPolynomial σ R) :
    map f (expand p φ) = expand p (map f φ) := by simp [expand, map_bind₁]

@[simp]
/--
theorem `rename_comp_expand` / 定理 `rename_comp_expand`

English:
theorem rename_comp_expand
  given: (f : σ -> τ)
  proof: by
  ext1 i
  simp

@[simp]

中文:
定理 rename_comp_expand
  条件: (f : σ -> τ)
  证明: by
  ext1 i
  simp

@[simp]
-/
theorem rename_comp_expand (f : σ -> τ) :
    (rename f).comp (expand p) =
      (expand p).comp (rename f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R) := by
  ext1 i
  simp

@[simp]
/--
theorem `rename_expand` / 定理 `rename_expand`

English:
theorem rename_expand
  given: (f : σ -> τ) (φ : MvPolynomial σ R)
  proof: DFunLike.congr_fun (rename_comp_expand p f) φ

中文:
定理 rename_expand
  条件: (f : σ -> τ) (φ : 多元多项式 σ R)
  证明: DFunLike.congr_fun (rename_comp_expand p f) φ

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, rename_comp_expand
-/
theorem rename_expand (f : σ -> τ) (φ : MvPolynomial σ R) :
    rename f (expand p φ) = expand p (rename f φ) :=
  DFunLike.congr_fun (rename_comp_expand p f) φ

/--
lemma `eval₂Hom_comp_expand` / 引理 `eval₂Hom_comp_expand`

English:
lemma eval₂Hom_comp_expand
  given: (f : R ->+* S) (g : σ -> S)
  proof: by
  ext <;> simp

@[simp]

中文:
引理 eval₂Hom_comp_expand
  条件: (f : R ->+* S) (g : σ -> S)
  证明: by
  ext <;> simp

@[simp]

Depends on / 依赖: MvPolynomial
-/
lemma eval₂Hom_comp_expand (f : R ->+* S) (g : σ -> S) :
    (eval₂Hom f g).comp (expand p (σ := σ) (R := R) : MvPolynomial σ R ->+* MvPolynomial σ R) =
      eval₂Hom f (g ^ p) := by
  ext <;> simp

@[simp]
/--
lemma `eval₂_expand` / 引理 `eval₂_expand`

English:
lemma eval₂_expand
  given: (f : R ->+* S) (g : σ -> S) (φ : MvPolynomial σ R)
  proof: DFunLike.congr_fun (eval₂Hom_comp_expand p f g) φ

@[simp]

中文:
引理 eval₂_expand
  条件: (f : R ->+* S) (g : σ -> S) (φ : 多元多项式 σ R)
  证明: DFunLike.congr_fun (eval₂Hom_comp_expand p f g) φ

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
lemma eval₂_expand (f : R ->+* S) (g : σ -> S) (φ : MvPolynomial σ R) :
    eval₂ f g (expand p φ) = eval₂ f (g ^ p) φ :=
  DFunLike.congr_fun (eval₂Hom_comp_expand p f g) φ

@[simp]
/--
lemma `aeval_comp_expand` / 引理 `aeval_comp_expand`

English:
lemma aeval_comp_expand
  given: {A : Type*} [CommSemiring A] [Algebra R A] (f : σ -> A)
  proof: by
  ext; simp

@[simp]

中文:
引理 aeval_comp_expand
  条件: {A : 类型} [交换半环 A] [代数 R A] (f : σ -> A)
  证明: by
  ext; simp

@[simp]
-/
lemma aeval_comp_expand {A : Type*} [CommSemiring A] [Algebra R A] (f : σ -> A) :
    (aeval f).comp (expand p) = aeval (R := R) (f ^ p) := by
  ext; simp

@[simp]
/--
lemma `aeval_expand` / 引理 `aeval_expand`

English:
lemma aeval_expand
  statement: {A : Type*} [CommSemiring A] [Algebra R A]
  proof: eval₂_expand ..

@[simp]

中文:
引理 aeval_expand
  结论: {A : 类型} [交换半环 A] [代数 R A]
  证明: eval₂_expand ..

@[simp]
-/
lemma aeval_expand {A : Type*} [CommSemiring A] [Algebra R A]
    (f : σ -> A) (φ : MvPolynomial σ R) :
    aeval f (expand p φ) = aeval (f ^ p) φ :=
  eval₂_expand ..

@[simp]
/--
lemma `eval_expand` / 引理 `eval_expand`

English:
lemma eval_expand
  given: (f : σ -> R) (φ : MvPolynomial σ R)
  proof: eval₂_expand ..

中文:
引理 eval_expand
  条件: (f : σ -> R) (φ : 多元多项式 σ R)
  证明: eval₂_expand ..
-/
lemma eval_expand (f : σ -> R) (φ : MvPolynomial σ R) :
    eval f (expand p φ) = eval (f ^ p) φ :=
  eval₂_expand ..

section

variable {p} (φ : MvPolynomial σ R)

/--
lemma `support_expand_subset` / 引理 `support_expand_subset`

English:
lemma support_expand_subset
  given: [DecidableEq σ]
  proof: by
  conv_lhs => rw [φ.as_sum]
  simp only [map_sum, expand_monomial]
  refine MvPolynomial.support_sum.trans ?_
  aesop (add simp Finset.subset_iff)

中文:
引理 support_expand_subset
  条件: [DecidableEq σ]
  证明: by
  conv_lhs => rw [φ.as_sum]
  simp only [map_sum, expand_monomial]
  refine MvPolynomial.support_sum.trans ?_
  aesop (add simp Finset.subset_iff)

Depends on / 依赖: Finset, Finset.subset_iff, MvPolynomial, MvPolynomial.support_sum.trans, as_sum, conv_lhs, expand_monomial, map_sum, subset_iff, support_sum
-/
lemma support_expand_subset [DecidableEq σ] :
    (expand p φ).support subseteq φ.support.image (p • ·) := by
  conv_lhs => rw [φ.as_sum]
  simp only [map_sum, expand_monomial]
  refine MvPolynomial.support_sum.trans ?_
  aesop (add simp Finset.subset_iff)

/--
lemma `coeff_expand_of_not_dvd` / 引理 `coeff_expand_of_not_dvd`

English:
lemma coeff_expand_of_not_dvd
  given: {m : σ ->₀ Nat} {i : σ} (h : ¬ p ∣ m i)
  proof: by
  classical
  contrapose! h
  grw [← mem_support_iff, support_expand_subset, Finset.mem_image] at h
  rcases h with ⟨a, -, rfl⟩
  exact ⟨a i, by simp⟩

中文:
引理 coeff_expand_of_not_dvd
  条件: {m : σ ->₀ 自然数} {i : σ} (h : ¬ p ∣ m i)
  证明: by
  classical
  contrapose! h
  grw [← mem_support_iff, support_expand_subset, Finset.mem_image] at h
  rcases h with ⟨a, -, rfl⟩
  exact ⟨a i, by simp⟩

Depends on / 依赖: Finset, Finset.mem_image, classical, contrapose, mem_image, mem_support_iff, support_expand_subset
-/
lemma coeff_expand_of_not_dvd {m : σ ->₀ Nat} {i : σ} (h : ¬ p ∣ m i) :
    (expand p φ).coeff m = 0 := by
  classical
  contrapose! h
  grw [← mem_support_iff, support_expand_subset, Finset.mem_image] at h
  rcases h with ⟨a, -, rfl⟩
  exact ⟨a i, by simp⟩

/--
lemma `support_expand` / 引理 `support_expand`

English:
lemma support_expand
  given: [DecidableEq σ] (hp : p != 0)
  proof: by
  refine (support_expand_subset φ).antisymm ?_
  simp [Finset.image_subset_iff, hp]

中文:
引理 support_expand
  条件: [DecidableEq σ] (hp : p != 0)
  证明: by
  refine (support_expand_subset φ).antisymm ?_
  simp [Finset.image_subset_iff, hp]

Depends on / 依赖: Finset, Finset.image_subset_iff, antisymm, image_subset_iff, support_expand_subset
-/
lemma support_expand [DecidableEq σ] (hp : p != 0) :
    (expand p φ).support = φ.support.image (p • ·) := by
  refine (support_expand_subset φ).antisymm ?_
  simp [Finset.image_subset_iff, hp]

/--
theorem `totalDegree_expand` / 定理 `totalDegree_expand`

English:
theorem totalDegree_expand
  given: (f : MvPolynomial σ R)
  proof: by
  classical
  rcases p.eq_zero_or_pos with hp | hp
  · simp [hp]
  by_cases hf : f = 0
  · rw [hf, map_zero, totalDegree_zero, zero_mul]
  simp_rw [totalDegree_eq, support_expand _ (p.ne_zero_iff_zero_lt.mpr hp)]
  simp only [Finsupp.card_toMultiset, Finset.sup_image, Finset.sup_mul₀, Function.comp_def]
  congr! 2 with d
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (by simp)]
  simp [Finsupp.sum, Finset.sum_mul, mul_comm p]

中文:
定理 totalDegree_expand
  条件: (f : 多元多项式 σ R)
  证明: by
  classical
  rcases p.eq_zero_or_pos with hp | hp
  · simp [hp]
  by_cases hf : f = 0
  · rw [hf, map_zero, totalDegree_zero, zero_mul]
  simp_rw [totalDegree_eq, support_expand _ (p.ne_zero_iff_zero_lt.mpr hp)]
  simp only [Finsupp.card_toMultiset, Finset.sup_image, Finset.sup_mul₀, Function.comp_def]
  congr! 2 with d
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (by simp)]
  simp [Finsupp.sum, Finset.sum_mul, mul_comm p]

Depends on / 依赖: Finset, Finset.sum_mul, Finset.sup_image, Finset.sup_mul, Finsupp, Finsupp.card_toMultiset, Finsupp.sum, Finsupp.sum_of_support_subset, Finsupp.support_smul, Function, Function.comp_def, card_toMultiset, classical, comp_def, eq_zero_or_pos, map_zero, mul_comm, ne_zero_iff_zero_lt, p.eq_zero_or_pos, p.ne_zero_iff_zero_lt.mpr
-/
theorem totalDegree_expand (f : MvPolynomial σ R) :
    (expand p f).totalDegree = f.totalDegree * p := by
  classical
  rcases p.eq_zero_or_pos with hp | hp
  · simp [hp]
  by_cases hf : f = 0
  · rw [hf, map_zero, totalDegree_zero, zero_mul]
  simp_rw [totalDegree_eq, support_expand _ (p.ne_zero_iff_zero_lt.mpr hp)]
  simp only [Finsupp.card_toMultiset, Finset.sup_image, Finset.sup_mul₀, Function.comp_def]
  congr! 2 with d
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (by simp)]
  simp [Finsupp.sum, Finset.sum_mul, mul_comm p]

end

end CommSemiring

section CommRing

variable (R σ : Type*) [CommRing R]

/--
theorem `isLocalHom_expand` / 定理 `isLocalHom_expand`

English:
theorem isLocalHom_expand
  given: {p : Nat} (hp : p != 0)
  statement: IsLocalHom (expand p (R := R) (σ := σ))
  proof: by
  refine ⟨fun f hf => ?_⟩
  rw [MvPolynomial.isUnit_iff] at hf ⊢
  simp only [coeff_expand_zero p hp] at hf
  refine ⟨hf.1, fun i hi => ?_⟩
  rw [← coeff_expand_smul p hp]
  apply hf.2
  simp [hi, hp]

中文:
定理 isLocalHom_expand
  条件: {p : 自然数} (hp : p != 0)
  结论: 是Local态射 (expand p (R := R) (σ := σ))
  证明: by
  refine ⟨fun f hf => ?_⟩
  rw [MvPolynomial.isUnit_iff] at hf ⊢
  simp only [coeff_expand_zero p hp] at hf
  refine ⟨hf.1, fun i hi => ?_⟩
  rw [← coeff_expand_smul p hp]
  apply hf.2
  simp [hi, hp]

Depends on / 依赖: MvPolynomial, MvPolynomial.isUnit_iff, coeff_expand_smul, coeff_expand_zero, isUnit_iff
-/
theorem isLocalHom_expand {p : Nat} (hp : p != 0) : IsLocalHom (expand p (R := R) (σ := σ)) := by
  refine ⟨fun f hf => ?_⟩
  rw [MvPolynomial.isUnit_iff] at hf ⊢
  simp only [coeff_expand_zero p hp] at hf
  refine ⟨hf.1, fun i hi => ?_⟩
  rw [← coeff_expand_smul p hp]
  apply hf.2
  simp [hi, hp]

variable {R}

/--
theorem `of_irreducible_expand` / 定理 `of_irreducible_expand`

English:
theorem of_irreducible_expand
  statement: {p : Nat} (hp : p != 0) {f : MvPolynomial σ R}
  proof: let _ := isLocalHom_expand R σ hp
  hf.of_map

中文:
定理 of_irreducible_expand
  结论: {p : 自然数} (hp : p != 0) {f : 多元多项式 σ R}
  证明: let _ := isLocalHom_expand R σ hp
  hf.of_map

Depends on / 依赖: hf.of_map, isLocalHom_expand, of_map
-/
theorem of_irreducible_expand {p : Nat} (hp : p != 0) {f : MvPolynomial σ R}
    (hf : Irreducible (expand p f)) :
    Irreducible f :=
  let _ := isLocalHom_expand R σ hp
  hf.of_map

end CommRing

end MvPolynomial
