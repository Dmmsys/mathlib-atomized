/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Multivariate polynomials over a ring

Many results about polynomials hold when the coefficient ring is a commutative semiring.
Some stronger results can be derived when we assume this semiring is a ring.

This file does not define any new operations, but proves some of these stronger results.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommRing R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/

@[expose] public section


noncomputable section

open Set Function Finsupp

universe u v

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : Nat} {n m : σ} {s : σ ->₀ Nat}

section CommRing

variable [CommRing R]
variable {p q : MvPolynomial σ R}

variable (σ a a')

@[simp]
/--
theorem `C_sub` / 定理 `C_sub`

English:
theorem C_sub
  statement: (C (a - a') : MvPolynomial σ R) = C a - C a'
  proof: map_sub _ _ _

@[simp]

中文:
定理 C_sub
  结论: (C (a - a') : 多元多项式 σ R) = C a - C a'
  证明: map_sub _ _ _

@[simp]

Depends on / 依赖: map_sub
-/
theorem C_sub : (C (a - a') : MvPolynomial σ R) = C a - C a' :=
  map_sub _ _ _

@[simp]
/--
theorem `C_neg` / 定理 `C_neg`

English:
theorem C_neg
  statement: (C (-a) : MvPolynomial σ R) = -C a
  proof: map_neg _ _

@[simp]

中文:
定理 C_neg
  结论: (C (-a) : 多元多项式 σ R) = -C a
  证明: map_neg _ _

@[simp]

Depends on / 依赖: map_neg
-/
theorem C_neg : (C (-a) : MvPolynomial σ R) = -C a :=
  map_neg _ _

@[simp]
/--
theorem `coeff_neg` / 定理 `coeff_neg`

English:
theorem coeff_neg
  given: (m : σ ->₀ Nat) (p : MvPolynomial σ R)
  statement: coeff m (-p) = -coeff m p
  proof: Finsupp.neg_apply _ _

@[simp, grind =]

中文:
定理 coeff_neg
  条件: (m : σ ->₀ 自然数) (p : 多元多项式 σ R)
  结论: coeff m (-p) = -coeff m p
  证明: Finsupp.neg_apply _ _

@[simp, grind =]

Depends on / 依赖: Finsupp, Finsupp.neg_apply, neg_apply
-/
theorem coeff_neg (m : σ ->₀ Nat) (p : MvPolynomial σ R) : coeff m (-p) = -coeff m p :=
  Finsupp.neg_apply _ _

@[simp, grind =]
/--
theorem `coeff_sub` / 定理 `coeff_sub`

English:
theorem coeff_sub
  given: (m : σ ->₀ Nat) (p q : MvPolynomial σ R)
  statement: coeff m (p - q) = coeff m p - coeff m q
  proof: Finsupp.sub_apply _ _ _

中文:
定理 coeff_sub
  条件: (m : σ ->₀ 自然数) (p q : 多元多项式 σ R)
  结论: coeff m (p - q) = coeff m p - coeff m q
  证明: Finsupp.sub_apply _ _ _

Depends on / 依赖: Finsupp, Finsupp.sub_apply, sub_apply
-/
theorem coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ R) : coeff m (p - q) = coeff m p - coeff m q :=
  Finsupp.sub_apply _ _ _

/--
lemma `support_neg` / 引理 `support_neg`

English:
lemma support_neg
  statement: (-p).support = p.support
  proof: by ext; simp

中文:
引理 support_neg
  结论: (-p).support = p.support
  证明: by ext; simp
-/
@[simp] lemma support_neg : (-p).support = p.support := by ext; simp

/--
theorem `support_sub` / 定理 `support_sub`

English:
theorem support_sub
  given: [DecidableEq σ] (p q : MvPolynomial σ R)
  proof: Finsupp.support_sub

中文:
定理 support_sub
  条件: [DecidableEq σ] (p q : 多元多项式 σ R)
  证明: Finsupp.support_sub

Depends on / 依赖: Finsupp, Finsupp.support_sub, support_sub
-/
theorem support_sub [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p - q).support subseteq p.support union q.support :=
  Finsupp.support_sub

variable {σ} (p)

/--
theorem `notMem_support_sub_monomial_sub_monomial` / 定理 `notMem_support_sub_monomial_sub_monomial`

English:
theorem notMem_support_sub_monomial_sub_monomial
  statement: (d d' : σ ->₀ Nat) (c : R)
  proof: by
  classical
  rw [notMem_support_iff]; rw [coeff_sub]; rw [coeff_sub]; rw [coeff_monomial]; rw [coeff_monomial]; rw [if_pos rfl]; rw [if_neg hdd'.symm]; rw [sub_zero]; rw [hc]; rw [sub_self]

中文:
定理 notMem_support_sub_monomial_sub_monomial
  结论: (d d' : σ ->₀ 自然数) (c : R)
  证明: by
  classical
  rw [notMem_support_iff]; rw [coeff_sub]; rw [coeff_sub]; rw [coeff_monomial]; rw [coeff_monomial]; rw [if_pos rfl]; rw [if_neg hdd'.symm]; rw [sub_zero]; rw [hc]; rw [sub_self]

Depends on / 依赖: classical, coeff_monomial, coeff_sub, if_neg, if_pos, notMem_support_iff, sub_self, sub_zero
-/
theorem notMem_support_sub_monomial_sub_monomial (d d' : σ ->₀ Nat) (c : R)
    (hdd' : d != d') (hc : coeff d p = c) :
    d ∉ (p - (monomial d c - monomial d' c)).support := by
  classical
  rw [notMem_support_iff]; rw [coeff_sub]; rw [coeff_sub]; rw [coeff_monomial]; rw [coeff_monomial]; rw [if_pos rfl]; rw [if_neg hdd'.symm]; rw [sub_zero]; rw [hc]; rw [sub_self]

/--
theorem `support_sub_monomial_sub_monomial_subset` / 定理 `support_sub_monomial_sub_monomial_subset`

English:
theorem support_sub_monomial_sub_monomial_subset
  statement: [DecidableEq σ] (d d' : σ ->₀ Nat) (c : R)
  proof: by
  classical
  intro x hx
  have hd_not := notMem_support_sub_monomial_sub_monomial p d d' c hdd' hc
  rcases Finset.mem_union.mp (support_sub σ p _ hx) with hp | hdelta
  · by_cases hxd : x = d
    · exact absurd (hxd ▸ hx) hd_not
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxd, hp⟩)

中文:
定理 support_sub_monomial_sub_monomial_subset
  结论: [DecidableEq σ] (d d' : σ ->₀ 自然数) (c : R)
  证明: by
  classical
  intro x hx
  have hd_not := notMem_support_sub_monomial_sub_monomial p d d' c hdd' hc
  rcases Finset.mem_union.mp (support_sub σ p _ hx) with hp | hdelta
  · by_cases hxd : x = d
    · exact absurd (hxd ▸ hx) hd_not
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxd, hp⟩)

Depends on / 依赖: Finset, Finset.mem_erase.mpr, Finset.mem_singleton.mp, Finset.mem_union.mp, Finset.mem_union_left, Finset.notMem_empty, absurd, classical, hd_not, hdelta, mem_erase, mem_singleton, mem_union, mem_union_left, notMem_empty, notMem_support_sub_monomial_sub_monomial, split_ifs, support_monomial, support_sub
-/
theorem support_sub_monomial_sub_monomial_subset [DecidableEq σ] (d d' : σ ->₀ Nat) (c : R)
    (hdd' : d != d') (hc : coeff d p = c) :
    (p - (monomial d c - monomial d' c)).support subseteq p.support.erase d union {d'} := by
  classical
  intro x hx
  have hd_not := notMem_support_sub_monomial_sub_monomial p d d' c hdd' hc
  rcases Finset.mem_union.mp (support_sub σ p _ hx) with hp | hdelta
  · by_cases hxd : x = d
    · exact absurd (hxd ▸ hx) hd_not
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxd, hp⟩)
  rcases Finset.mem_union.mp (support_sub σ _ _ hdelta) with h1 | h2
  · rw [support_monomial] at h1
    split_ifs at h1
    · exact absurd h1 (Finset.notMem_empty _)
    exact absurd ((Finset.mem_singleton.mp h1) ▸ hx) hd_not
  rw [support_monomial] at h2
  split_ifs at h2
  · exact absurd h2 (Finset.notMem_empty _)
  exact Finset.mem_union_right _ (by rwa [Finset.mem_singleton] at h2 ⊢)

section Degrees

@[simp]
/--
theorem `degrees_neg` / 定理 `degrees_neg`

English:
theorem degrees_neg
  given: (p : MvPolynomial σ R)
  statement: (-p).degrees = p.degrees
  proof: by
  rw [degrees]; rw [support_neg]; rfl

中文:
定理 degrees_neg
  条件: (p : 多元多项式 σ R)
  结论: (-p).degrees = p.degrees
  证明: by
  rw [degrees]; rw [support_neg]; rfl

Depends on / 依赖: degrees, support_neg
-/
theorem degrees_neg (p : MvPolynomial σ R) : (-p).degrees = p.degrees := by
  rw [degrees]; rw [support_neg]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `degrees_sub_le` / 定理 `degrees_sub_le`

English:
theorem degrees_sub_le
  given: [DecidableEq σ] {p q : MvPolynomial σ R}
  proof: by
  simpa [degrees_def] using! AddMonoidAlgebra.supDegree_sub_le

中文:
定理 degrees_sub_le
  条件: [DecidableEq σ] {p q : 多元多项式 σ R}
  证明: by
  simpa [degrees_def] using! AddMonoidAlgebra.supDegree_sub_le

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.supDegree_sub_le, degrees_def, supDegree_sub_le
-/
theorem degrees_sub_le [DecidableEq σ] {p q : MvPolynomial σ R} :
    (p - q).degrees <= p.degrees union q.degrees := by
  simpa [degrees_def] using! AddMonoidAlgebra.supDegree_sub_le

end Degrees

section Degrees

@[simp]
/--
theorem `degreeOf_neg` / 定理 `degreeOf_neg`

English:
theorem degreeOf_neg
  given: (i : σ) (p : MvPolynomial σ R)
  statement: degreeOf i (-p) = degreeOf i p
  proof: by
  rw [degreeOf]; rw [degreeOf]; rw [degrees_neg]

中文:
定理 degreeOf_neg
  条件: (i : σ) (p : 多元多项式 σ R)
  结论: degreeOf i (-p) = degreeOf i p
  证明: by
  rw [degreeOf]; rw [degreeOf]; rw [degrees_neg]

Depends on / 依赖: degreeOf, degrees_neg
-/
theorem degreeOf_neg (i : σ) (p : MvPolynomial σ R) : degreeOf i (-p) = degreeOf i p := by
  rw [degreeOf]; rw [degreeOf]; rw [degrees_neg]

/--
theorem `degreeOf_sub_le` / 定理 `degreeOf_sub_le`

English:
theorem degreeOf_sub_le
  given: (i : σ) (p q : MvPolynomial σ R)
  proof: by
  simpa only [sub_eq_add_neg, degreeOf_neg] using degreeOf_add_le i p (-q)

中文:
定理 degreeOf_sub_le
  条件: (i : σ) (p q : 多元多项式 σ R)
  证明: by
  simpa only [sub_eq_add_neg, degreeOf_neg] using degreeOf_add_le i p (-q)

Depends on / 依赖: degreeOf_add_le, degreeOf_neg, sub_eq_add_neg
-/
theorem degreeOf_sub_le (i : σ) (p q : MvPolynomial σ R) :
    degreeOf i (p - q) <= max (degreeOf i p) (degreeOf i q) := by
  simpa only [sub_eq_add_neg, degreeOf_neg] using degreeOf_add_le i p (-q)

end Degrees

section Vars

@[simp]
/--
theorem `vars_neg` / 定理 `vars_neg`

English:
theorem vars_neg
  statement: (-p).vars = p.vars
  proof: by simp [vars, degrees_neg]

中文:
定理 vars_neg
  结论: (-p).vars = p.vars
  证明: by simp [vars, degrees_neg]

Depends on / 依赖: degrees_neg
-/
theorem vars_neg : (-p).vars = p.vars := by simp [vars, degrees_neg]

/--
theorem `vars_sub_subset` / 定理 `vars_sub_subset`

English:
theorem vars_sub_subset
  given: [DecidableEq σ]
  statement: (p - q).vars subseteq p.vars union q.vars
  proof: by
  convert! vars_add_subset p (-q) using 2 <;> simp [sub_eq_add_neg]

@[simp]

中文:
定理 vars_sub_subset
  条件: [DecidableEq σ]
  结论: (p - q).vars subseteq p.vars union q.vars
  证明: by
  convert! vars_add_subset p (-q) using 2 <;> simp [sub_eq_add_neg]

@[simp]

Depends on / 依赖: convert, sub_eq_add_neg, vars_add_subset
-/
theorem vars_sub_subset [DecidableEq σ] : (p - q).vars subseteq p.vars union q.vars := by
  convert! vars_add_subset p (-q) using 2 <;> simp [sub_eq_add_neg]

@[simp]
/--
theorem `vars_sub_of_disjoint` / 定理 `vars_sub_of_disjoint`

English:
theorem vars_sub_of_disjoint
  given: [DecidableEq σ] (hpq : Disjoint p.vars q.vars)
  proof: by
  rw [← vars_neg q] at hpq
  convert! vars_add_of_disjoint hpq using 2 <;> simp [sub_eq_add_neg]

中文:
定理 vars_sub_of_disjoint
  条件: [DecidableEq σ] (hpq : Disjoint p.vars q.vars)
  证明: by
  rw [← vars_neg q] at hpq
  convert! vars_add_of_disjoint hpq using 2 <;> simp [sub_eq_add_neg]

Depends on / 依赖: convert, sub_eq_add_neg, vars_add_of_disjoint, vars_neg
-/
theorem vars_sub_of_disjoint [DecidableEq σ] (hpq : Disjoint p.vars q.vars) :
    (p - q).vars = p.vars union q.vars := by
  rw [← vars_neg q] at hpq
  convert! vars_add_of_disjoint hpq using 2 <;> simp [sub_eq_add_neg]

end Vars

section Eval

variable [CommRing S]
variable (f : R ->+* S) (g : σ -> S)

@[simp]
/--
theorem `eval₂_sub` / 定理 `eval₂_sub`

English:
theorem eval₂_sub
  statement: (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g
  proof: (eval₂Hom f g).map_sub _ _

中文:
定理 eval₂_sub
  结论: (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g
  证明: (eval₂Hom f g).map_sub _ _

Depends on / 依赖: map_sub
-/
theorem eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g :=
  (eval₂Hom f g).map_sub _ _

/--
theorem `eval_sub` / 定理 `eval_sub`

English:
theorem eval_sub
  given: (f : σ -> R)
  statement: eval f (p - q) = eval f p - eval f q
  proof: eval₂_sub _ _ _

@[simp]

中文:
定理 eval_sub
  条件: (f : σ -> R)
  结论: eval f (p - q) = eval f p - eval f q
  证明: eval₂_sub _ _ _

@[simp]
-/
theorem eval_sub (f : σ -> R) : eval f (p - q) = eval f p - eval f q :=
  eval₂_sub _ _ _

@[simp]
/--
theorem `eval₂_neg` / 定理 `eval₂_neg`

English:
theorem eval₂_neg
  statement: (-p).eval₂ f g = -p.eval₂ f g
  proof: (eval₂Hom f g).map_neg _

中文:
定理 eval₂_neg
  结论: (-p).eval₂ f g = -p.eval₂ f g
  证明: (eval₂Hom f g).map_neg _

Depends on / 依赖: map_neg
-/
theorem eval₂_neg : (-p).eval₂ f g = -p.eval₂ f g :=
  (eval₂Hom f g).map_neg _

/--
theorem `eval_neg` / 定理 `eval_neg`

English:
theorem eval_neg
  given: (f : σ -> R)
  statement: eval f (-p) = -eval f p
  proof: eval₂_neg _ _ _

中文:
定理 eval_neg
  条件: (f : σ -> R)
  结论: eval f (-p) = -eval f p
  证明: eval₂_neg _ _ _
-/
theorem eval_neg (f : σ -> R) : eval f (-p) = -eval f p :=
  eval₂_neg _ _ _

/--
theorem `hom_C` / 定理 `hom_C`

English:
theorem hom_C
  given: (f : MvPolynomial σ Int ->+* S) (n : Int)
  statement: f (C n) = (n : S)
  proof: eq_intCast (f.comp C) n

中文:
定理 hom_C
  条件: (f : 多元多项式 σ 整数 ->+* S) (n : 整数)
  结论: f (C n) = (n : S)
  证明: eq_intCast (f.comp C) n

Depends on / 依赖: eq_intCast, f.comp
-/
theorem hom_C (f : MvPolynomial σ Int ->+* S) (n : Int) : f (C n) = (n : S) :=
  eq_intCast (f.comp C) n

/-- A ring homomorphism `f : Z[X_1, X_2, ...] → R`
is determined by the evaluations `f(X_1)`, `f(X_2)`, ... -/
@[simp]
/--
theorem `eval₂Hom_X` / 定理 `eval₂Hom_X`

English:
theorem eval₂Hom_X
  given: {R : Type u} (c : Int ->+* S) (f : MvPolynomial R Int ->+* S) (x : MvPolynomial R Int)
  proof: by
  apply MvPolynomial.induction_on x
    (fun n => by
      rw [hom_C f]; rw [eval₂_C]
      exact eq_intCast c n)
    (fun p q hp hq => by
      rw [eval₂_add]; rw [hp]; rw [hq]
      exact (f.map_add _ _).symm)
    (fun p n hp => by
      rw [eval₂_mul]; rw [eval₂_X]; rw [hp]
      exact (f.map_

中文:
定理 eval₂Hom_X
  条件: {R : 类型u} (c : 整数 ->+* S) (f : 多元多项式 R 整数 ->+* S) (x : 多元多项式 R 整数)
  证明: by
  apply MvPolynomial.induction_on x
    (fun n => by
      rw [hom_C f]; rw [eval₂_C]
      exact eq_intCast c n)
    (fun p q hp hq => by
      rw [eval₂_add]; rw [hp]; rw [hq]
      exact (f.map_add _ _).symm)
    (fun p n hp => by
      rw [eval₂_mul]; rw [eval₂_X]; rw [hp]
      exact (f.map_

Depends on / 依赖: MvPolynomial, MvPolynomial.induction_on, eq_intCast, f.map_add, f.map_mul, hom_C, induction_on, map_add, map_mul
-/
theorem eval₂Hom_X {R : Type u} (c : Int ->+* S) (f : MvPolynomial R Int ->+* S) (x : MvPolynomial R Int) :
    eval₂ c (f ∘ X) x = f x := by
  apply MvPolynomial.induction_on x
    (fun n => by
      rw [hom_C f]; rw [eval₂_C]
      exact eq_intCast c n)
    (fun p q hp hq => by
      rw [eval₂_add]; rw [hp]; rw [hq]
      exact (f.map_add _ _).symm)
    (fun p n hp => by
      rw [eval₂_mul]; rw [eval₂_X]; rw [hp]
      exact (f.map_mul _ _).symm)

/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: : (MvPolynomial σ Int ->+* S) ≃ (σ -> S) where
  body: f ∘ X
  invFun f := eval₂Hom (Int.castRingHom S) f
left_inv _ := RingHom.ext eval₂Hom_X _ _
  right_inv f := funext fun x => by simp only [coe_eval₂Hom, Function.comp_apply, eval₂_X]

中文:
定义 homEquiv
  签名: : (多元多项式 σ 整数 ->+* S) ≃ (σ -> S) where
  定义体: f ∘ X
  invFun f := eval₂Hom (Int.castRingHom S) f
left_inv _ := RingHom.ext eval₂Hom_X _ _
  right_inv f := funext fun x => by simp only [coe_eval₂Hom, Function.comp_apply, eval₂_X]
-/
def homEquiv : (MvPolynomial σ Int ->+* S) ≃ (σ -> S) where
  toFun f := f ∘ X
  invFun f := eval₂Hom (Int.castRingHom S) f
left_inv _ := RingHom.ext eval₂Hom_X _ _
  right_inv f := funext fun x => by simp only [coe_eval₂Hom, Function.comp_apply, eval₂_X]

end Eval

section DegreeOf

/--
theorem `degreeOf_sub_lt` / 定理 `degreeOf_sub_lt`

English:
theorem degreeOf_sub_lt
  statement: {x : σ} {f g : MvPolynomial σ R} {k : Nat} (h : 0 < k)
  proof: by
  rw [degreeOf_lt_iff h]
  grind [degreeOf_lt_iff]

中文:
定理 degreeOf_sub_lt
  结论: {x : σ} {f g : 多元多项式 σ R} {k : 自然数} (h : 0 < k)
  证明: by
  rw [degreeOf_lt_iff h]
  grind [degreeOf_lt_iff]

Depends on / 依赖: degreeOf_lt_iff
-/
theorem degreeOf_sub_lt {x : σ} {f g : MvPolynomial σ R} {k : Nat} (h : 0 < k)
    (hf : forall m : σ ->₀ Nat, m in f.support -> k <= m x -> coeff m f = coeff m g)
    (hg : forall m : σ ->₀ Nat, m in g.support -> k <= m x -> coeff m f = coeff m g) :
    degreeOf x (f - g) < k := by
  rw [degreeOf_lt_iff h]
  grind [degreeOf_lt_iff]

end DegreeOf

section TotalDegree

@[simp]
/--
theorem `totalDegree_neg` / 定理 `totalDegree_neg`

English:
theorem totalDegree_neg
  given: (a : MvPolynomial σ R)
  statement: (-a).totalDegree = a.totalDegree
  proof: by
  simp only [totalDegree, support_neg]

中文:
定理 totalDegree_neg
  条件: (a : 多元多项式 σ R)
  结论: (-a).totalDegree = a.totalDegree
  证明: by
  simp only [totalDegree, support_neg]

Depends on / 依赖: support_neg, totalDegree
-/
theorem totalDegree_neg (a : MvPolynomial σ R) : (-a).totalDegree = a.totalDegree := by
  simp only [totalDegree, support_neg]

/--
theorem `totalDegree_sub` / 定理 `totalDegree_sub`

English:
theorem totalDegree_sub
  given: (a b : MvPolynomial σ R)
  proof: calc
    (a - b).totalDegree = (a + -b).totalDegree := by rw [sub_eq_add_neg]
    _ <= max a.totalDegree (-b).totalDegree := totalDegree_add a (-b)
    _ = max a.totalDegree b.totalDegree := by rw [totalDegree_neg]

中文:
定理 totalDegree_sub
  条件: (a b : 多元多项式 σ R)
  证明: calc
    (a - b).totalDegree = (a + -b).totalDegree := by rw [sub_eq_add_neg]
    _ <= max a.totalDegree (-b).totalDegree := totalDegree_add a (-b)
    _ = max a.totalDegree b.totalDegree := by rw [totalDegree_neg]

Depends on / 依赖: a.totalDegree, b.totalDegree, sub_eq_add_neg, totalDegree, totalDegree_add, totalDegree_neg
-/
theorem totalDegree_sub (a b : MvPolynomial σ R) :
    (a - b).totalDegree <= max a.totalDegree b.totalDegree :=
  calc
    (a - b).totalDegree = (a + -b).totalDegree := by rw [sub_eq_add_neg]
    _ <= max a.totalDegree (-b).totalDegree := totalDegree_add a (-b)
    _ = max a.totalDegree b.totalDegree := by rw [totalDegree_neg]

/--
theorem `totalDegree_sub_C_le` / 定理 `totalDegree_sub_C_le`

English:
theorem totalDegree_sub_C_le
  given: (p : MvPolynomial σ R) (r : R)
  proof: (totalDegree_sub _ _).trans_eq by rw [totalDegree_C, Nat.max_zero]

中文:
定理 totalDegree_sub_C_le
  条件: (p : 多元多项式 σ R) (r : R)
  证明: (totalDegree_sub _ _).trans_eq by rw [totalDegree_C, Nat.max_zero]

Depends on / 依赖: Nat.max_zero, max_zero, totalDegree_C, totalDegree_sub, trans_eq
-/
theorem totalDegree_sub_C_le (p : MvPolynomial σ R) (r : R) :
    totalDegree (p - C r) <= totalDegree p :=
(totalDegree_sub _ _).trans_eq by rw [totalDegree_C, Nat.max_zero]

end TotalDegree

end CommRing

end MvPolynomial
