/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.WittVector.Basic
public meta import Mathlib.Lean.Elab.Tactic.Basic
/-!
# The `IsPoly` predicate

`WittVector.IsPoly` is a (type-valued) predicate on functions `f : Π R, 𝕎 R → 𝕎 R`.
It asserts that there is a family of polynomials `φ : ℕ → MvPolynomial ℕ ℤ`,
such that the `n`th coefficient of `f x` is equal to `φ n` evaluated on the coefficients of `x`.
Many operations on Witt vectors satisfy this predicate (or an analogue for higher arity functions).
We say that such a function `f` is a *polynomial function*.

The power of satisfying this predicate comes from `WittVector.IsPoly.ext`.
It shows that if `φ` and `ψ` witness that `f` and `g` are polynomial functions,
then `f = g` not merely when `φ = ψ`, but in fact it suffices to prove
```
∀ n, bind₁ φ (wittPolynomial p _ n) = bind₁ ψ (wittPolynomial p _ n)
```
(in other words, when evaluating the Witt polynomials on `φ` and `ψ`, we get the same values)
which will then imply `φ = ψ` and hence `f = g`.

Even though this sufficient condition looks somewhat intimidating,
it is rather pleasant to check in practice;
more so than direct checking of `φ = ψ`.

In practice, we apply this technique to show that the composition of `WittVector.frobenius`
and `WittVector.verschiebung` is equal to multiplication by `p`.

## Main declarations

* `WittVector.IsPoly`, `WittVector.IsPoly₂`:
  two predicates that assert that a unary/binary function on Witt vectors
  is polynomial in the coefficients of the input values.
* `WittVector.IsPoly.ext`, `WittVector.IsPoly₂.ext`:
  two polynomial functions are equal if their families of polynomials are equal
  after evaluating the Witt polynomials on them.
* `WittVector.IsPoly.comp` (+ many variants) show that unary/binary compositions
  of polynomial functions are polynomial.
* `WittVector.idIsPoly`, `WittVector.negIsPoly`,
  `WittVector.addIsPoly₂`, `WittVector.mulIsPoly₂`:
  several well-known operations are polynomial functions
  (for Verschiebung, Frobenius, and multiplication by `p`, see their respective files).

## On higher arity analogues

Ideally, there should be a predicate `IsPolyₙ` for functions of higher arity,
together with `IsPolyₙ.comp` that shows how such functions compose.
Since mathlib does not have a library on composition of higher arity functions,
we have only implemented the unary and binary variants so far.
Nullary functions (a.k.a. constants) are treated
as constant functions and fall under the unary case.

## Tactics

There are important metaprograms defined in this file:
the tactics `ghost_simp` and `ghost_calc` and the attribute `@[ghost_simps]`.
These are used in combination to discharge proofs of identities between polynomial functions.

The `ghost_calc` tactic makes use of the `IsPoly` and `IsPoly₂` typeclass and its instances.
(In Lean 3, there was an `@[is_poly]` attribute to manage these instances,
because typeclass resolution did not play well with function composition.
This no longer seems to be an issue, so that such instances can be defined directly.)

Any lemma doing "ring equation rewriting" with polynomial functions should be tagged
`@[ghost_simps]`, e.g.
```lean
@[ghost_simps]
lemma bind₁_frobenius_poly_wittPolynomial (n : ℕ) :
    bind₁ (frobenius_poly p) (wittPolynomial p ℤ n) = (wittPolynomial p ℤ (n+1))
```

Proofs of identities between polynomial functions will often follow the pattern
```lean
  ghost_calc _
  <minor preprocessing>
  ghost_simp
```

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section

namespace WittVector

universe u

variable {p : Nat} {R S : Type u} {idx : Type*} [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

open MvPolynomial

open Function (uncurry)

variable (p)

noncomputable section



/--
theorem `poly_eq_of_wittPolynomial_bind_eq'` / 定理 `poly_eq_of_wittPolynomial_bind_eq'`

English:
theorem poly_eq_of_wittPolynomial_bind_eq'
  statement: [Fact p.Prime] (f g : Nat -> MvPolynomial (idx × Nat) Int)
  proof: by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom Rat) ∘ fam) (xInTermsOfW p Rat n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bi

中文:
定理 poly_eq_of_wittPolynomial_bind_eq'
  结论: [Fact p.Prime] (f g : 自然数 -> MvPolynomial (idx × 自然数) 整数)
  证明: by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom Rat) ∘ fam) (xInTermsOfW p Rat n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bi

Depends on / 依赖: Function, Function.comp_def, Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map, MvPolynomial.map_injective, castRingHom, cast_injective, comp_def, congr_arg, funext_iff, map_injective, map_wittPolynomial, replace, xInTermsOfW
-/
theorem poly_eq_of_wittPolynomial_bind_eq' [Fact p.Prime] (f g : Nat -> MvPolynomial (idx × Nat) Int)
    (h : forall n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom Rat) ∘ fam) (xInTermsOfW p Rat n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h

/--
theorem `poly_eq_of_wittPolynomial_bind_eq` / 定理 `poly_eq_of_wittPolynomial_bind_eq`

English:
theorem poly_eq_of_wittPolynomial_bind_eq
  statement: [Fact p.Prime] (f g : Nat -> MvPolynomial Nat Int)
  proof: by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom Rat) ∘ fam) (xInTermsOfW p Rat n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bi

中文:
定理 poly_eq_of_wittPolynomial_bind_eq
  结论: [Fact p.Prime] (f g : 自然数 -> MvPolynomial 自然数 整数)
  证明: by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom Rat) ∘ fam) (xInTermsOfW p Rat n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bi

Depends on / 依赖: ContinuousEval, ContinuousEval.toContinuousMapClass, ContinuousMapClass, Function, Function.comp_def, Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map, MvPolynomial.map_injective, castRingHom, cast_injective, comp_def, congr_arg, funext_iff, map_injective, map_wittPolynomial, replace, toContinuousMapClass, xInTermsOfW
-/
theorem poly_eq_of_wittPolynomial_bind_eq [Fact p.Prime] (f g : Nat -> MvPolynomial Nat Int)
    (h : forall n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom Rat) ∘ fam) (xInTermsOfW p Rat n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h

-- Ideally, we would generalise this to n-ary functions
-- But we don't have a good theory of n-ary compositions in mathlib
/--
Definition of `IsPoly` / `IsPoly` 的定义

English:
class IsPoly
  parameters: (f : forall ⦃R⦄ [CommRing R], WittVector p R -> 𝕎 R)
  (no additional axioms)

中文:
类 IsPoly
  参数: (f : 对任意 ⦃R⦄ [CommRing R], WittVector p R -> 𝕎 R)
  (无附加公理)

Depends on / 依赖: ContinuousEval, ContinuousEval.toContinuousEvalConst, ContinuousEvalConst, toContinuousEvalConst
-/
class IsPoly (f : forall ⦃R⦄ [CommRing R], WittVector p R -> 𝕎 R) : Prop where mk' ::
  poly :
    exists φ : Nat -> MvPolynomial Nat Int,
      forall ⦃R⦄ [CommRing R] (x : 𝕎 R), (f x).coeff = fun n => aeval x.coeff (φ n)

/--
Instance `idIsPoly` / 实例 `idIsPoly`

English:
instance idIsPoly
  signature: : IsPoly p fun _ _ => id
  body: ⟨⟨X, by intros; simp only [aeval_X, id]⟩⟩

中文:
实例 idIsPoly
  签名: : IsPoly p fun _ _ => id
  定义体: ⟨⟨X, by intros; simp only [aeval_X, id]⟩⟩

Depends on / 依赖: aeval_X, intros
-/
instance idIsPoly : IsPoly p fun _ _ => id :=
  ⟨⟨X, by intros; simp only [aeval_X, id]⟩⟩

/--
Instance `idIsPolyI'` / 实例 `idIsPolyI'`

English:
instance idIsPolyI'
  signature: : IsPoly p fun _ _ a => a
  body: WittVector.idIsPoly _

中文:
实例 idIsPolyI'
  签名: : IsPoly p fun _ _ a => a
  定义体: WittVector.idIsPoly _

Depends on / 依赖: WittVector, WittVector.idIsPoly, idIsPoly
-/
instance idIsPolyI' : IsPoly p fun _ _ a => a :=
  WittVector.idIsPoly _

namespace IsPoly

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (IsPoly p fun _ _ => id)
  body: ⟨WittVector.idIsPoly p⟩

中文:
实例 :
  签名: Inhabited (IsPoly p fun _ _ => id)
  定义体: ⟨WittVector.idIsPoly p⟩

Depends on / 依赖: WittVector, WittVector.idIsPoly, idIsPoly
-/
instance : Inhabited (IsPoly p fun _ _ => id) :=
  ⟨WittVector.idIsPoly p⟩

variable {p}

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : IsPoly p g)
  proof: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf]; rw [hg]; rw [poly_eq_of_wittPolynomial_bind_eq p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift Int) (mk p fun i => ⟨x i⟩) k
  simp only [ghostComponent_apply, aeval_eq_ev

中文:
定理 ext
  结论: [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : IsPoly p g)
  证明: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf]; rw [hg]; rw [poly_eq_of_wittPolynomial_bind_eq p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift Int) (mk p fun i => ⟨x i⟩) k
  simp only [ghostComponent_apply, aeval_eq_ev

Depends on / 依赖: MvPolynomial, MvPolynomial.eval, MvPolynomial.funext, RingEquiv, RingEquiv.coe_toRingHom, ULift.ringEquiv.symm, all_goals, coe_toRingHom, convert, ghostComponent_apply, injective, intros, poly_eq_of_wittPolynomial_bind_eq, ringEquiv, specialize
-/
theorem ext [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : IsPoly p g)
    (h : forall (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R) (n : Nat),
        ghostComponent n (f x) = ghostComponent n (g x)) :
    forall (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R), f x = g x := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf]; rw [hg]; rw [poly_eq_of_wittPolynomial_bind_eq p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift Int) (mk p fun i => ⟨x i⟩) k
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  apply (ULift.ringEquiv.symm : Int ≃+* _).injective
  simp only [← RingEquiv.coe_toRingHom, map_eval₂Hom]
  convert! h using 1
  all_goals
    simp only [hf, hg, MvPolynomial.eval, map_eval₂Hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    simp only [coeff_mk]; rfl

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: {g f} [hg : IsPoly p g] [hf : IsPoly p f]
  body: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [aeval_bind₁, Function.comp, hg, hf]

中文:
实例 comp
  签名: {g f} [hg : IsPoly p g] [hf : IsPoly p f]
  定义体: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [aeval_bind₁, Function.comp, hg, hf]

Depends on / 依赖: Function, Function.comp, intros
-/
instance comp {g f} [hg : IsPoly p g] [hf : IsPoly p f] :
    IsPoly p fun R _Rcr => @g R _Rcr ∘ @f R _Rcr := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [aeval_bind₁, Function.comp, hg, hf]

end IsPoly

/--
Definition of `IsPoly₂` / `IsPoly₂` 的定义

English:
class IsPoly₂
  parameters: (f : forall ⦃R⦄ [CommRing R], WittVector p R -> 𝕎 R -> 𝕎 R)
  (no additional axioms)

中文:
类 IsPoly₂
  参数: (f : 对任意 ⦃R⦄ [CommRing R], WittVector p R -> 𝕎 R -> 𝕎 R)
  (无附加公理)
-/
class IsPoly₂ (f : forall ⦃R⦄ [CommRing R], WittVector p R -> 𝕎 R -> 𝕎 R) : Prop where mk' ::
  poly :
    exists φ : Nat -> MvPolynomial (Fin 2 × Nat) Int,
      forall ⦃R⦄ [CommRing R] (x y : 𝕎 R), (f x y).coeff = fun n => peval (φ n) ![x.coeff, y.coeff]

variable {p}

/--
Instance `IsPoly₂.comp` / 实例 `IsPoly₂.comp`

English:
instance IsPoly₂.comp
  signature: {h f g} [hh : IsPoly₂ p h] [hf : IsPoly p f] [hg : IsPoly p g]
  body: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  obtain ⟨χ, hh⟩ := hh
  refine ⟨⟨fun n => bind₁ (uncurry <|
    ![fun k => rename (Prod.mk (0 : Fin 2)) (φ k),
      fun k => rename (Prod.mk (1 : Fin 2)) (ψ k)]) (χ n), ?_⟩⟩
  intros
  funext n
  simp +unfoldPartialApp only [peval, aeval_bind₁, hh, 

中文:
实例 IsPoly₂.comp
  签名: {h f g} [hh : IsPoly₂ p h] [hf : IsPoly p f] [hg : IsPoly p g]
  定义体: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  obtain ⟨χ, hh⟩ := hh
  refine ⟨⟨fun n => bind₁ (uncurry <|
    ![fun k => rename (Prod.mk (0 : Fin 2)) (φ k),
      fun k => rename (Prod.mk (1 : Fin 2)) (ψ k)]) (χ n), ?_⟩⟩
  intros
  funext n
  simp +unfoldPartialApp only [peval, aeval_bind₁, hh, 

Depends on / 依赖: Function, Function.comp_def, Prod.mk, comp_def, fin_cases, intros, uncurry, unfoldPartialApp
-/
instance IsPoly₂.comp {h f g} [hh : IsPoly₂ p h] [hf : IsPoly p f] [hg : IsPoly p g] :
    IsPoly₂ p fun _ _Rcr x y => h (f x) (g y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  obtain ⟨χ, hh⟩ := hh
  refine ⟨⟨fun n => bind₁ (uncurry <|
    ![fun k => rename (Prod.mk (0 : Fin 2)) (φ k),
      fun k => rename (Prod.mk (1 : Fin 2)) (ψ k)]) (χ n), ?_⟩⟩
  intros
  funext n
  simp +unfoldPartialApp only [peval, aeval_bind₁, hh, hf, hg,
    uncurry]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, n⟩
  fin_cases i <;> simp [aeval_eq_eval₂Hom, eval₂Hom_rename, Function.comp_def]

/--
Instance `IsPoly.comp₂` / 实例 `IsPoly.comp₂`

English:
instance IsPoly.comp₂
  signature: {g f} [hg : IsPoly p g] [hf : IsPoly₂ p f]
  body: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [peval, aeval_bind₁, hg, hf]

中文:
实例 IsPoly.comp₂
  签名: {g f} [hg : IsPoly p g] [hf : IsPoly₂ p f]
  定义体: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [peval, aeval_bind₁, hg, hf]

Depends on / 依赖: intros
-/
instance IsPoly.comp₂ {g f} [hg : IsPoly p g] [hf : IsPoly₂ p f] :
    IsPoly₂ p fun _ _Rcr x y => g (f x y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [peval, aeval_bind₁, hg, hf]

/--
Instance `IsPoly₂.diag` / 实例 `IsPoly₂.diag`

English:
instance IsPoly₂.diag
  signature: {f} [hf : IsPoly₂ p f]
  body: by
  obtain ⟨φ, hf⟩ := hf
  refine ⟨⟨fun n => bind₁ (uncurry ![X, X]) (φ n), ?_⟩⟩
  intros; funext n
  simp +unfoldPartialApp only [hf, peval, uncurry, aeval_bind₁]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, k⟩
  fin_cases i <;> simp

中文:
实例 IsPoly₂.diag
  签名: {f} [hf : IsPoly₂ p f]
  定义体: by
  obtain ⟨φ, hf⟩ := hf
  refine ⟨⟨fun n => bind₁ (uncurry ![X, X]) (φ n), ?_⟩⟩
  intros; funext n
  simp +unfoldPartialApp only [hf, peval, uncurry, aeval_bind₁]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, k⟩
  fin_cases i <;> simp

Depends on / 依赖: fin_cases, intros, uncurry, unfoldPartialApp
-/
instance IsPoly₂.diag {f} [hf : IsPoly₂ p f] : IsPoly p fun _ _Rcr x => f x x := by
  obtain ⟨φ, hf⟩ := hf
  refine ⟨⟨fun n => bind₁ (uncurry ![X, X]) (φ n), ?_⟩⟩
  intros; funext n
  simp +unfoldPartialApp only [hf, peval, uncurry, aeval_bind₁]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, k⟩
  fin_cases i <;> simp

/--
Instance `negIsPoly` / 实例 `negIsPoly`

English:
instance negIsPoly
  signature: [Fact p.Prime]
  body: ⟨⟨fun n => rename Prod.snd (wittNeg p n), by
      intros; funext n
      rw [neg_coeff]; rw [aeval_eq_eval₂Hom]; rw [eval₂Hom_rename]
      apply eval₂Hom_congr rfl _ rfl
      ext ⟨i, k⟩; fin_cases i; rfl⟩⟩

中文:
实例 negIsPoly
  签名: [Fact p.Prime]
  定义体: ⟨⟨fun n => rename Prod.snd (wittNeg p n), by
      intros; funext n
      rw [neg_coeff]; rw [aeval_eq_eval₂Hom]; rw [eval₂Hom_rename]
      apply eval₂Hom_congr rfl _ rfl
      ext ⟨i, k⟩; fin_cases i; rfl⟩⟩

Depends on / 依赖: Prod.snd, fin_cases, intros, neg_coeff, wittNeg
-/
instance negIsPoly [Fact p.Prime] : IsPoly p fun R _ => @Neg.neg (𝕎 R) _ :=
  ⟨⟨fun n => rename Prod.snd (wittNeg p n), by
      intros; funext n
      rw [neg_coeff]; rw [aeval_eq_eval₂Hom]; rw [eval₂Hom_rename]
      apply eval₂Hom_congr rfl _ rfl
      ext ⟨i, k⟩; fin_cases i; rfl⟩⟩

section ZeroOne

/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/
/--
Instance `zeroIsPoly` / 实例 `zeroIsPoly`

English:
instance zeroIsPoly
  signature: [Fact p.Prime]
  body: ⟨⟨0, by intros; funext n; simp only [Pi.zero_apply, map_zero, zero_coeff]⟩⟩

@[simp]

中文:
实例 zeroIsPoly
  签名: [Fact p.Prime]
  定义体: ⟨⟨0, by intros; funext n; simp only [Pi.zero_apply, map_zero, zero_coeff]⟩⟩

@[simp]

Depends on / 依赖: Pi.zero_apply, intros, map_zero, zero_apply, zero_coeff
-/
instance zeroIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 0 :=
  ⟨⟨0, by intros; funext n; simp only [Pi.zero_apply, map_zero, zero_coeff]⟩⟩

@[simp]
/--
theorem `bind₁_zero_wittPolynomial` / 定理 `bind₁_zero_wittPolynomial`

English:
theorem bind₁_zero_wittPolynomial
  given: [Fact p.Prime] (n : Nat)
  proof: by
  rw [← aeval_eq_bind₁]; rw [aeval_zero]; rw [constantCoeff_wittPolynomial]; rw [map_zero]

中文:
定理 bind₁_zero_wittPolynomial
  条件: [Fact p.Prime] (n : 自然数)
  证明: by
  rw [← aeval_eq_bind₁]; rw [aeval_zero]; rw [constantCoeff_wittPolynomial]; rw [map_zero]

Depends on / 依赖: aeval_zero, constantCoeff_wittPolynomial, map_zero
-/
theorem bind₁_zero_wittPolynomial [Fact p.Prime] (n : Nat) :
    bind₁ (0 : Nat -> MvPolynomial Nat R) (wittPolynomial p R n) = 0 := by
  rw [← aeval_eq_bind₁]; rw [aeval_zero]; rw [constantCoeff_wittPolynomial]; rw [map_zero]

/--
Definition of `onePoly` / `onePoly` 的定义

English:
definition onePoly
  signature: (n : Nat)
  body: if n = 0 then 1 else 0

@[simp]

中文:
定义 onePoly
  签名: (n : 自然数)
  定义体: if n = 0 then 1 else 0

@[simp]
-/
def onePoly (n : Nat) : MvPolynomial Nat Int :=
  if n = 0 then 1 else 0

@[simp]
/--
theorem `bind₁_onePoly_wittPolynomial` / 定理 `bind₁_onePoly_wittPolynomial`

English:
theorem bind₁_onePoly_wittPolynomial
  given: [hp : Fact p.Prime] (n : Nat)
  proof: by
  rw [wittPolynomial_eq_sum_C_mul_X_pow]; rw [map_sum]; rw [Finset.sum_eq_single 0]
  · simp only [onePoly, one_pow, one_mul, map_pow, C_1, pow_zero, bind₁_X_right, if_true]
  · intro i _hi hi0
    simp only [onePoly, if_neg hi0, zero_pow (pow_ne_zero _ hp.1.ne_zero), mul_zero, map_pow,
      bin

中文:
定理 bind₁_onePoly_wittPolynomial
  条件: [hp : Fact p.Prime] (n : 自然数)
  证明: by
  rw [wittPolynomial_eq_sum_C_mul_X_pow]; rw [map_sum]; rw [Finset.sum_eq_single 0]
  · simp only [onePoly, one_pow, one_mul, map_pow, C_1, pow_zero, bind₁_X_right, if_true]
  · intro i _hi hi0
    simp only [onePoly, if_neg hi0, zero_pow (pow_ne_zero _ hp.1.ne_zero), mul_zero, map_pow,
      bin

Depends on / 依赖: Finset, Finset.sum_eq_single, if_neg, if_true, map_mul, map_pow, map_sum, mul_zero, ne_zero, onePoly, one_mul, one_pow, pow_ne_zero, pow_zero, sum_eq_single, wittPolynomial_eq_sum_C_mul_X_pow, zero_pow
-/
theorem bind₁_onePoly_wittPolynomial [hp : Fact p.Prime] (n : Nat) :
    bind₁ onePoly (wittPolynomial p Int n) = 1 := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow]; rw [map_sum]; rw [Finset.sum_eq_single 0]
  · simp only [onePoly, one_pow, one_mul, map_pow, C_1, pow_zero, bind₁_X_right, if_true]
  · intro i _hi hi0
    simp only [onePoly, if_neg hi0, zero_pow (pow_ne_zero _ hp.1.ne_zero), mul_zero, map_pow,
      bind₁_X_right, map_mul]
  · simp

/--
Instance `oneIsPoly` / 实例 `oneIsPoly`

English:
instance oneIsPoly
  signature: [Fact p.Prime]
  body: ⟨⟨onePoly, by
      intros; funext n; cases n
      · simp only [one_coeff_zero, onePoly, ite_true, map_one]
      · simp only [Nat.succ_pos', one_coeff_eq_of_pos, onePoly, Nat.succ_ne_zero, ite_false,
          map_zero]
  ⟩⟩

中文:
实例 oneIsPoly
  签名: [Fact p.Prime]
  定义体: ⟨⟨onePoly, by
      intros; funext n; cases n
      · simp only [one_coeff_zero, onePoly, ite_true, map_one]
      · simp only [Nat.succ_pos', one_coeff_eq_of_pos, onePoly, Nat.succ_ne_zero, ite_false,
          map_zero]
  ⟩⟩

Depends on / 依赖: Nat.succ_ne_zero, Nat.succ_pos, intros, ite_false, ite_true, map_one, map_zero, onePoly, one_coeff_eq_of_pos, one_coeff_zero, succ_ne_zero, succ_pos
-/
instance oneIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 1 :=
  ⟨⟨onePoly, by
      intros; funext n; cases n
      · simp only [one_coeff_zero, onePoly, ite_true, map_one]
      · simp only [Nat.succ_pos', one_coeff_eq_of_pos, onePoly, Nat.succ_ne_zero, ite_false,
          map_zero]
  ⟩⟩

end ZeroOne

/--
Instance `addIsPoly₂` / 实例 `addIsPoly₂`

English:
instance addIsPoly₂
  signature: [Fact p.Prime]
  body: ⟨⟨wittAdd p, by intros; ext; exact add_coeff _ _ _⟩⟩

中文:
实例 addIsPoly₂
  签名: [Fact p.Prime]
  定义体: ⟨⟨wittAdd p, by intros; ext; exact add_coeff _ _ _⟩⟩

Depends on / 依赖: add_coeff, intros, wittAdd
-/
instance addIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· + ·) :=
  ⟨⟨wittAdd p, by intros; ext; exact add_coeff _ _ _⟩⟩

/--
Instance `mulIsPoly₂` / 实例 `mulIsPoly₂`

English:
instance mulIsPoly₂
  signature: [Fact p.Prime]
  body: ⟨⟨wittMul p, by intros; ext; exact mul_coeff _ _ _⟩⟩

中文:
实例 mulIsPoly₂
  签名: [Fact p.Prime]
  定义体: ⟨⟨wittMul p, by intros; ext; exact mul_coeff _ _ _⟩⟩

Depends on / 依赖: intros, mul_coeff, wittMul
-/
instance mulIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· * ·) :=
  ⟨⟨wittMul p, by intros; ext; exact mul_coeff _ _ _⟩⟩

-- unfortunately this is not universe polymorphic, merely because `f` isn't
/--
theorem `IsPoly.map` / 定理 `IsPoly.map`

English:
theorem IsPoly.map
  given: [Fact p.Prime] {f} (hf : IsPoly p f) (g : R ->+* S) (x : 𝕎 R)
  proof: by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  -- see `IsPoly₂.map` for a slightly more general proof strategy
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp_rw [map_coeff, hf, map_aeval, funext (map_coef

中文:
定理 IsPoly.map
  条件: [Fact p.Prime] {f} (hf : IsPoly p f) (g : R ->+* S) (x : 𝕎 R)
  证明: by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  -- see `IsPoly₂.map` for a slightly more general proof strategy
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp_rw [map_coeff, hf, map_aeval, funext (map_coef
-/
theorem IsPoly.map [Fact p.Prime] {f} (hf : IsPoly p f) (g : R ->+* S) (x : 𝕎 R) :
    map g (f x) = f (map g x) := by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  -- see `IsPoly₂.map` for a slightly more general proof strategy
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp_rw [map_coeff, hf, map_aeval, funext (map_coeff g _), RingHom.ext_int _ (algebraMap Int S),
    aeval_eq_eval₂Hom]

namespace IsPoly₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fact
  signature: p.Prime] : Inhabited (IsPoly₂ p (fun _ _ => (· + ·)))
  body: ⟨addIsPoly₂⟩

中文:
实例 [Fact
  签名: p.Prime] : Inhabited (IsPoly₂ p (fun _ _ => (· + ·)))
  定义体: ⟨addIsPoly₂⟩
-/
instance [Fact p.Prime] : Inhabited (IsPoly₂ p (fun _ _ => (· + ·))) :=
  ⟨addIsPoly₂⟩

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g)
  proof: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf]; rw [hg]; rw [poly_eq_of_wittPolynomial_bind_eq' p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift Int) (mk p fun i => ⟨x (0, i)⟩) (mk p fun i => ⟨x (1, i)⟩) k
  simp only [

中文:
定理 ext
  结论: [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g)
  证明: by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf]; rw [hg]; rw [poly_eq_of_wittPolynomial_bind_eq' p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift Int) (mk p fun i => ⟨x (0, i)⟩) (mk p fun i => ⟨x (1, i)⟩) k
  simp only [

Depends on / 依赖: MvPolynomial, MvPolynomial.eval, MvPolynomial.funext, RingEquiv, RingEquiv.coe_toRingHom, ULift.ringEquiv.symm, all_goals, coe_toRingHom, convert, ghostComponent_apply, injective, intros, map_ev, poly_eq_of_wittPolynomial_bind_eq, ringEquiv, specialize
-/
theorem ext [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g)
    (h : forall (R : Type u) [_Rcr : CommRing R] (x y : 𝕎 R) (n : Nat),
        ghostComponent n (f x y) = ghostComponent n (g x y)) :
    forall (R) [_Rcr : CommRing R] (x y : 𝕎 R), f x y = g x y := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf]; rw [hg]; rw [poly_eq_of_wittPolynomial_bind_eq' p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift Int) (mk p fun i => ⟨x (0, i)⟩) (mk p fun i => ⟨x (1, i)⟩) k
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  apply (ULift.ringEquiv.symm : Int ≃+* _).injective
  simp only [← RingEquiv.coe_toRingHom, map_eval₂Hom]
  convert! h using 1
  all_goals
    simp only [hf, hg, MvPolynomial.eval, map_eval₂Hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext ⟨b, _⟩
    fin_cases b <;> simp only [coeff_mk, uncurry] <;> rfl

-- unfortunately this is not universe polymorphic, merely because `f` isn't
/--
theorem `map` / 定理 `map`

English:
theorem map
  given: [Fact p.Prime] {f} (hf : IsPoly₂ p f) (g : R ->+* S) (x y : 𝕎 R)
  proof: by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp +unfoldPartialApp only [map_coeff, hf, map_aeval, peval, uncurry]
  apply eval₂Hom_congr (RingHom.ext_int _ _) _

中文:
定理 map
  条件: [Fact p.Prime] {f} (hf : IsPoly₂ p f) (g : R ->+* S) (x y : 𝕎 R)
  证明: by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp +unfoldPartialApp only [map_coeff, hf, map_aeval, peval, uncurry]
  apply eval₂Hom_congr (RingHom.ext_int _ _) _
-/
theorem map [Fact p.Prime] {f} (hf : IsPoly₂ p f) (g : R ->+* S) (x y : 𝕎 R) :
    map g (f x y) = f (map g x) (map g y) := by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp +unfoldPartialApp only [map_coeff, hf, map_aeval, peval, uncurry]
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  ext ⟨i, k⟩
  fin_cases i <;> simp

end IsPoly₂

attribute [ghost_simps] AlgHom.id_apply map_natCast RingHom.map_zero RingHom.map_one RingHom.map_mul
  RingHom.map_add RingHom.map_sub RingHom.map_neg RingHom.id_apply mul_add add_mul add_zero zero_add
  mul_one one_mul mul_zero zero_mul Nat.succ_ne_zero add_tsub_cancel_right
  Nat.succ_eq_add_one if_true eq_self_iff_true if_false forall_true_iff forall₂_true_iff
  forall₃_true_iff

end

namespace Tactic
open Lean Parser.Tactic Elab.Tactic

/-- A macro for a common simplification when rewriting with ghost component equations. -/
syntax (name := ghostSimp) "ghost_simp" (simpArgs)? : tactic

macro_rules
  | `(tactic| ghost_simp $[[$simpArgs,*]]?) => do
.getD #[] let args := simpArgs.map (·.getElems)
    `(tactic| simp only [← sub_eq_add_neg, ghost_simps, $args,*])


/-- `ghost_calc` is a tactic for proving identities between polynomial functions.
Typically, when faced with a goal like
```lean
∀ (x y : 𝕎 R), verschiebung (x * frobenius y) = verschiebung x * y
```
you can
1. call `ghost_calc`
2. do a small amount of manual work -- maybe nothing, maybe `rintro`, etc
3. call `ghost_simp`

and this will close the goal.

`ghost_calc` cannot detect whether you are dealing with unary or binary polynomial functions.
You must give it arguments to determine this.
If you are proving a universally quantified goal like the above,
call `ghost_calc _ _`.
If the variables are introduced already, call `ghost_calc x y`.
In the unary case, use `ghost_calc _` or `ghost_calc x`.

`ghost_calc` is a light wrapper around type class inference.
All it does is apply the appropriate extensionality lemma and try to infer the resulting goals.
This is subtle and Lean's elaborator doesn't like it because of the HO unification involved,
so it is easier (and prettier) to put it in a tactic script.
-/
syntax (name := ghostCalc) "ghost_calc" (ppSpace colGt term:max)* : tactic

private meta def runIntro (ref : Syntax) (n : Name) : TacticM FVarId := do
  let fvarId ← liftMetaTacticAux fun g => do
    let (fv, g') ← g.intro n
    return (fv, [g'])
  withMainContext do
    Elab.Term.addLocalVarInfo ref (mkFVar fvarId)
  return fvarId

private meta def getLocalOrIntro (t : Term) : TacticM FVarId := do
  match t with
    | `(_) => runIntro t `_
| `($id:ident) => getFVarId id > runIntro id id.getId
    | _ => Elab.throwUnsupportedSyntax

elab_rules : tactic | `(tactic| ghost_calc $[$ids']*) => do
  let ids ← ids'.mapM getLocalOrIntro
  withMainContext do
  let idsS ← ids.mapM (fun id => Elab.Term.exprToSyntax (.fvar id))
  let some (α, lhs, rhs) := (← getMainTarget'').eq?
    | throwError "ghost_calc expecting target to be an equality"
  let (``WittVector, #[_, R]) := α.getAppFnArgs
    | throwError "ghost_calc expecting target to be an equality of `WittVector`s"
  let instR ← Meta.synthInstance (← Meta.mkAppM ``CommRing #[R])
  unless instR.isFVar do
    throwError "{← Meta.inferType instR} instance is not local"
  let f ← Meta.mkLambdaFVars (#[R, instR] ++ ids.map .fvar) lhs
  let g ← Meta.mkLambdaFVars (#[R, instR] ++ ids.map .fvar) rhs
  let fS ← Elab.Term.exprToSyntax f
  let gS ← Elab.Term.exprToSyntax g
  match idsS with
    | #[x] => evalTactic (← `(tactic| refine IsPoly.ext (f := $fS) (g := $gS) ?_ ?_ ?_ _ $x))
    | #[x, y] => evalTactic (← `(tactic| refine IsPoly₂.ext (f := $fS) (g := $gS) ?_ ?_ ?_ _ $x $y))
    | _ => throwError "ghost_calc takes either one or two arguments"
let nm ← withMainContext
    if let .fvar fvarId := (R : Expr) then
      fvarId.getUserName
    else
      Meta.getUnusedUserName `R
evalTactic ← `(tactic| iterate 2 infer_instance)
  let R := mkIdent nm
evalTactic ← `(tactic| clear! $R)
evalTactic ← `(tactic| intro $(mkIdent nm):ident $(mkIdent (.str nm "_inst")):ident $ids'*)

end Tactic

end WittVector
