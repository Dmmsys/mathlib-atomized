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

variable {p : ℕ} {R S : Type u} {idx : Type*} [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

open MvPolynomial

open Function (uncurry)

variable (p)

noncomputable section

/-!
### The `IsPoly` predicate
-/


/-
**WittVector.poly_eq_of_wittPolynomial_bind_eq'** 是 Mathlib 中的一个定理，位于命名空间 `WittV
ector`。
形式化陈述：poly_eq_of_wittPolynomial_bind_eq' [Fact p.Prime] (f g : Nat -> MvPolynomi
al (idx × Nat) Int) (h : forall n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wit
tPolynomial p _ n)) : f = g
参数：f g : Nat -> MvPolynomial (idx × Nat) Int；h : forall n, bind₁ f (wittPolynomi
al p _ n) = bind₁ g (wittPolynomial p _ n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.map_bind₁`：map_bind₁ (f : R ->+* S) (g : σ -> MvPolynomial 
τ R) (φ : MvPolynomial σ R) : map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g
 i)) (map f …
· 使用定理 `map_wittPolynomial`：map_wittPolynomial (f : R ->+* S) (n : Nat) : map f 
(W n) = W n
· 使用定理 `bind₁_wittPolynomial_xInTermsOfW`：bind₁_wittPolynomial_xInTermsOfW [Inve
rtible (p : R)] (n : Nat) : bind₁ (W_ R) (xInTermsOfW p R n) = X n
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i

--- 原说明 ---
### The `IsPoly` predicate
-/
theorem poly_eq_of_wittPolynomial_bind_eq' [Fact p.Prime] (f g : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h
/-
**WittVector.poly_eq_of_wittPolynomial_bind_eq** 是 Mathlib 中的一个定理，位于命名空间 `WittVe
ctor`。
形式化陈述：poly_eq_of_wittPolynomial_bind_eq [Fact p.Prime] (f g : Nat -> MvPolynomia
l Nat Int) (h : forall n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomi
al p _ n)) : f = g
参数：f g : Nat -> MvPolynomial Nat Int；h : forall n, bind₁ f (wittPolynomial p _ n
) = bind₁ g (wittPolynomial p _ n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.map_bind₁`：map_bind₁ (f : R ->+* S) (g : σ -> MvPolynomial 
τ R) (φ : MvPolynomial σ R) : map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g
 i)) (map f …
· 使用定理 `map_wittPolynomial`：map_wittPolynomial (f : R ->+* S) (n : Nat) : map f 
(W n) = W n
· 使用定理 `bind₁_wittPolynomial_xInTermsOfW`：bind₁_wittPolynomial_xInTermsOfW [Inve
rtible (p : R)] (n : Nat) : bind₁ (W_ R) (xInTermsOfW p R n) = X n
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
-/
theorem poly_eq_of_wittPolynomial_bind_eq [Fact p.Prime] (f g : ℕ → MvPolynomial ℕ ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp_def, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h

-- Ideally, we would generalise this to n-ary functions
-- But we don't have a good theory of n-ary compositions in mathlib
/--
A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbitrary base rings
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.

See also `WittVector.IsPoly₂` for the binary variant.

The `ghost_calc` tactic makes use of the `IsPoly` and `IsPoly₂` typeclass and its instances.
(In Lean 3, there was an `@[is_poly]` attribute to manage these instances,
because typeclass resolution did not play well with function composition.
This no longer seems to be an issue, so that such instances can be defined directly.)
-/
/-
**WittVector.IsPoly** 是 Mathlib 中的一个归纳类型，位于命名空间 `WittVector`。
形式化陈述：(p : ℕ) → (⦃R : Type u_2⦄ → [CommRing R] → WittVector p R → WittVector p R
) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbi
trary base rings
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` suc
h that the `n`th
coefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.

See also `WittVector.IsPoly₂` for the binary variant.

The `ghost_calc` tactic makes use of the `IsPoly` and `IsPoly₂` typeclass and it
s instances.
(In Lean 3, there was an `@[is_poly]` attribute to manage these instances,
because typeclass resolution did not play well with function composition.
This no longer seems to be an issue, so that such instances can be defined direc
tly.)
-/
class IsPoly (f : ∀ ⦃R⦄ [CommRing R], WittVector p R → 𝕎 R) : Prop where mk' ::
  poly :
    ∃ φ : ℕ → MvPolynomial ℕ ℤ,
      ∀ ⦃R⦄ [CommRing R] (x : 𝕎 R), (f x).coeff = fun n => aeval x.coeff (φ n)

/-- The identity function on Witt vectors is a polynomial function. -/
/-
**WittVector.idIsPoly** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：idIsPoly : IsPoly p fun _ _ => id
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The identity function on Witt vectors is a polynomial function.
-/
instance idIsPoly : IsPoly p fun _ _ => id :=
  ⟨⟨X, by intros; simp only [aeval_X, id]⟩⟩
/-
**WittVector.idIsPolyI'** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：idIsPolyI' : IsPoly p fun _ _ a => a
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance idIsPolyI' : IsPoly p fun _ _ a => a :=
  WittVector.idIsPoly _

namespace IsPoly

/-
**WittVector.IsPoly.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector.IsPoly`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (IsPoly p fun _ _ => id) :=
  ⟨WittVector.idIsPoly p⟩

variable {p}
/-
**WittVector.IsPoly.ext** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.IsPoly`。
形式化陈述：ext [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : IsPoly p g) (h : forall (
R : Type u) [_Rcr : CommRing R] (x : 𝕎 R) (n : Nat), ghostComponent n (f x) = gh
ostComponent n (g x)) : forall (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R), f x =
 g x
参数：hf : IsPoly p f；hg : IsPoly p g；h : forall (R : Type u) [_Rcr : CommRing R] (
x : 𝕎 R) (n : Nat), ghostComponent n (f x) = ghostComponent n (g x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.poly_eq_of_wittPolynomial_bind_eq`：poly_eq_of_wittPolynomial_
bind_eq [Fact p.Prime] (f g : Nat -> MvPolynomial Nat Int) (h : forall n, bind₁ 
f (wittPolynomial p _ n) = bind₁ g…
· 使用定理 `MvPolynomial.funext`：funext {σ : Type*} {p q : MvPolynomial σ R} (h : fo
rall x : σ -> R, eval x p = eval x q) : p = q
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.hom_bind₁`：hom_bind₁ (f : MvPolynomial τ R ->+* S) (g : σ -
> MvPolynomial τ R) (φ : MvPolynomial σ R) : f (bind₁ g φ) = eval₂Hom (f.comp C)
 (fun i => f…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `MvPolynomial.map_eval₂Hom`：map_eval₂Hom [CommSemiring S₂] (f : R ->+* S₁
) (g : σ -> S₁) (φ : S₁ ->+* S₂) (p : MvPolynomial σ R) : φ (eval₂Hom f g p) = e
val₂Hom (φ.comp…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
-/
theorem ext [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : IsPoly p g)
    (h : ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R) (n : ℕ),
        ghostComponent n (f x) = ghostComponent n (g x)) :
    ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R), f x = g x := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf, hg, poly_eq_of_wittPolynomial_bind_eq p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift ℤ) (mk p fun i => ⟨x i⟩) k
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  apply (ULift.ringEquiv.symm : ℤ ≃+* _).injective
  simp only [← RingEquiv.coe_toRingHom, map_eval₂Hom]
  convert! h using 1
  all_goals
    simp only [hf, hg, MvPolynomial.eval, map_eval₂Hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    simp only [coeff_mk]; rfl

/-- The composition of polynomial functions is polynomial. -/
/-
**WittVector.IsPoly.comp** 是 Mathlib 中的一个实例，位于命名空间 `WittVector.IsPoly`。
形式化陈述：comp {g f} [hg : IsPoly p g] [hf : IsPoly p f] : IsPoly p fun R _Rcr => @g
 R _Rcr ∘ @f R _Rcr
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.aeval_bind₁`：aeval_bind₁ [Algebra R S] (f : τ -> S) (g : σ 
-> MvPolynomial τ R) (φ : MvPolynomial σ R) : aeval f (bind₁ g φ) = aeval (fun i
 => aeval f (g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of polynomial functions is polynomial.
-/
instance comp {g f} [hg : IsPoly p g] [hf : IsPoly p f] :
    IsPoly p fun R _Rcr => @g R _Rcr ∘ @f R _Rcr := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [aeval_bind₁, Function.comp, hg, hf]

end IsPoly

/-- A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.

See also `WittVector.IsPoly` for the unary variant.

The `ghost_calc` tactic makes use of the `IsPoly` and `IsPoly₂` typeclass and its instances.
(In Lean 3, there was an `@[is_poly]` attribute to manage these instances,
because typeclass resolution did not play well with function composition.
This no longer seems to be an issue, so that such instances can be defined directly.)
-/
/-
**WittVector.IsPoly** 是 Mathlib 中的一个归纳类型，位于命名空间 `WittVector`。
形式化陈述：(p : ℕ) → (⦃R : Type u_2⦄ → [CommRing R] → WittVector p R → WittVector p R
) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` suc
h that the `n`th
coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` an
d `y`.

See also `WittVector.IsPoly` for the unary variant.

The `ghost_calc` tactic makes use of the `IsPoly` and `IsPoly₂` typeclass and it
s instances.
(In Lean 3, there was an `@[is_poly]` attribute to manage these instances,
because typeclass resolution did not play well with function composition.
This no longer seems to be an issue, so that such instances can be defined direc
tly.)
-/
class IsPoly₂ (f : ∀ ⦃R⦄ [CommRing R], WittVector p R → 𝕎 R → 𝕎 R) : Prop where mk' ::
  poly :
    ∃ φ : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ,
      ∀ ⦃R⦄ [CommRing R] (x y : 𝕎 R), (f x y).coeff = fun n => peval (φ n) ![x.coeff, y.coeff]

variable {p}

/-- The composition of polynomial functions is polynomial. -/
/-
**WittVector.IsPoly** 是 Mathlib 中的一个归纳类型，位于命名空间 `WittVector`。
形式化陈述：(p : ℕ) → (⦃R : Type u_2⦄ → [CommRing R] → WittVector p R → WittVector p R
) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of polynomial functions is polynomial.
-/
instance IsPoly₂.comp {h f g} [hh : IsPoly₂ p h] [hf : IsPoly p f] [hg : IsPoly p g] :
    IsPoly₂ p fun _ _Rcr x y => h (f x) (g y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  obtain ⟨χ, hh⟩ := hh
  refine ⟨⟨fun n ↦ bind₁ (uncurry <|
    ![fun k ↦ rename (Prod.mk (0 : Fin 2)) (φ k),
      fun k ↦ rename (Prod.mk (1 : Fin 2)) (ψ k)]) (χ n), ?_⟩⟩
  intros
  funext n
  simp +unfoldPartialApp only [peval, aeval_bind₁, hh, hf, hg,
    uncurry]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, n⟩
  fin_cases i <;> simp [aeval_eq_eval₂Hom, eval₂Hom_rename, Function.comp_def]

/-- The composition of a polynomial function with a binary polynomial function is polynomial. -/
/-
**WittVector.IsPoly.comp** 是 Mathlib 中的一个实例，位于命名空间 `WittVector.IsPoly`。
形式化陈述：comp {g f} [hg : IsPoly p g] [hf : IsPoly p f] : IsPoly p fun R _Rcr => @g
 R _Rcr ∘ @f R _Rcr
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.aeval_bind₁`：aeval_bind₁ [Algebra R S] (f : τ -> S) (g : σ 
-> MvPolynomial τ R) (φ : MvPolynomial σ R) : aeval f (bind₁ g φ) = aeval (fun i
 => aeval f (g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of a polynomial function with a binary polynomial function is po
lynomial.
-/
instance IsPoly.comp₂ {g f} [hg : IsPoly p g] [hf : IsPoly₂ p f] :
    IsPoly₂ p fun _ _Rcr x y => g (f x y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [peval, aeval_bind₁, hg, hf]

/-- The diagonal `fun x ↦ f x x` of a polynomial function `f` is polynomial. -/
/-
**WittVector.IsPoly** 是 Mathlib 中的一个归纳类型，位于命名空间 `WittVector`。
形式化陈述：(p : ℕ) → (⦃R : Type u_2⦄ → [CommRing R] → WittVector p R → WittVector p R
) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal `fun x ↦ f x x` of a polynomial function `f` is polynomial.
-/
instance IsPoly₂.diag {f} [hf : IsPoly₂ p f] : IsPoly p fun _ _Rcr x => f x x := by
  obtain ⟨φ, hf⟩ := hf
  refine ⟨⟨fun n => bind₁ (uncurry ![X, X]) (φ n), ?_⟩⟩
  intros; funext n
  simp +unfoldPartialApp only [hf, peval, uncurry, aeval_bind₁]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, k⟩
  fin_cases i <;> simp

/-- The additive negation is a polynomial function on Witt vectors. -/
/-
**WittVector.negIsPoly** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：negIsPoly [Fact p.Prime] : IsPoly p fun R _ => @Neg.neg (𝕎 R) _
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.neg_coeff`：neg_coeff (x : 𝕎 R) (n : Nat) : (-x).coeff n = pev
al (wittNeg p n) ![x.coeff]
· 使用定理 `MvPolynomial.aeval_eq_eval₂Hom`：aeval_eq_eval₂Hom (p : MvPolynomial σ R)
 : aeval f p = eval₂Hom (algebraMap R S₁) f p
· 使用定理 `MvPolynomial.eval₂Hom_rename`：eval₂Hom_rename : eval₂Hom f g (rename k p
) = eval₂Hom f (g ∘ k) p
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
The additive negation is a polynomial function on Witt vectors.
-/
instance negIsPoly [Fact p.Prime] : IsPoly p fun R _ => @Neg.neg (𝕎 R) _ :=
  ⟨⟨fun n => rename Prod.snd (wittNeg p n), by
      intros; funext n
      rw [neg_coeff, aeval_eq_eval₂Hom, eval₂Hom_rename]
      apply eval₂Hom_congr rfl _ rfl
      ext ⟨i, k⟩; fin_cases i; rfl⟩⟩

section ZeroOne

/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/
/-- The function that is constantly zero on Witt vectors is a polynomial function. -/
/-
**WittVector.zeroIsPoly** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：zeroIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 0
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The function that is constantly zero on Witt vectors is a polynomial function.
-/
instance zeroIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 0 :=
  ⟨⟨0, by intros; funext n; simp only [Pi.zero_apply, map_zero, zero_coeff]⟩⟩

@[simp]
/-
**WittVector.bind** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_zero_wittPolynomial [Fact p.Prime] (n : ℕ) :
    bind₁ (0 : ℕ → MvPolynomial ℕ R) (wittPolynomial p R n) = 0 := by
  rw [← aeval_eq_bind₁, aeval_zero, constantCoeff_wittPolynomial, map_zero]

/-- The coefficients of `1 : 𝕎 R` as polynomials. -/
/-
**WittVector.onePoly** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：onePoly (n : Nat) : MvPolynomial Nat Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coefficients of `1 : 𝕎 R` as polynomials.
-/
def onePoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 1 else 0

@[simp]
/-
**WittVector.bind** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind₁_onePoly_wittPolynomial [hp : Fact p.Prime] (n : ℕ) :
    bind₁ onePoly (wittPolynomial p ℤ n) = 1 := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow, map_sum, Finset.sum_eq_single 0]
  · simp only [onePoly, one_pow, one_mul, map_pow, C_1, pow_zero, bind₁_X_right, if_true]
  · intro i _hi hi0
    simp only [onePoly, if_neg hi0, zero_pow (pow_ne_zero _ hp.1.ne_zero), mul_zero, map_pow,
      bind₁_X_right, map_mul]
  · simp

/-- The function that is constantly one on Witt vectors is a polynomial function. -/
/-
**WittVector.oneIsPoly** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：oneIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 1
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.one_coeff_zero`：one_coeff_zero : (1 : 𝕎 R).coeff 0 = 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.one_coeff_eq_of_pos`：one_coeff_eq_of_pos (n : Nat) (hn : 0 < 
n) : coeff (1 : 𝕎 R) n = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…

--- 原说明 ---
The function that is constantly one on Witt vectors is a polynomial function.
-/
instance oneIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 1 :=
  ⟨⟨onePoly, by
      intros; funext n; cases n
      · simp only [one_coeff_zero, onePoly, ite_true, map_one]
      · simp only [Nat.succ_pos', one_coeff_eq_of_pos, onePoly, Nat.succ_ne_zero, ite_false,
          map_zero]
  ⟩⟩

end ZeroOne

/-- Addition of Witt vectors is a polynomial function. -/
/-
**WittVector.addIsPoly** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Addition of Witt vectors is a polynomial function.
-/
instance addIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· + ·) :=
  ⟨⟨wittAdd p, by intros; ext; exact add_coeff _ _ _⟩⟩

/-- Multiplication of Witt vectors is a polynomial function. -/
/-
**WittVector.mulIsPoly** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of Witt vectors is a polynomial function.
-/
instance mulIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· * ·) :=
  ⟨⟨wittMul p, by intros; ext; exact mul_coeff _ _ _⟩⟩

-- unfortunately this is not universe polymorphic, merely because `f` isn't
/-
**WittVector.IsPoly.map** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.IsPoly`。
形式化陈述：∀ {p : ℕ} {R S : Type u} [inst : CommRing R] [inst_1 : CommRing S] [inst_2
 : Fact (Nat.Prime p)]   {f : ⦃R : Type u⦄ → [CommRing R] → WittVector p R → Wit
tVector p R},   WittVector.IsPoly p f → ∀ (g : R →+* S) (x : WittVector p R), (W
ittVector.map g) (f x) = f ((WittVector.map g) x)
参数：Nat.Prime p；g : R →+* S；x : WittVector p R；WittVector.map g；f x；(WittVector.m
ap g) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WittVector.map_coeff`：map_coeff (f : R ->+* S) (x : 𝕎 R) (n : Nat) : (ma
p f x).coeff n = f (x.coeff n)
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsPoly.map [Fact p.Prime] {f} (hf : IsPoly p f) (g : R →+* S) (x : 𝕎 R) :
    map g (f x) = f (map g x) := by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  -- see `IsPoly₂.map` for a slightly more general proof strategy
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp_rw [map_coeff, hf, map_aeval, funext (map_coeff g _), RingHom.ext_int _ (algebraMap ℤ S),
    aeval_eq_eval₂Hom]

namespace IsPoly₂

/-
**WittVector.IsPoly₂.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector.IsPoly₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fact p.Prime] : Inhabited (IsPoly₂ p (fun _ _ => (· + ·))) :=
  ⟨addIsPoly₂⟩
/-
**WittVector.IsPoly₂.ext** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.IsPoly₂`。
形式化陈述：ext [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g) (h : forall
 (R : Type u) [_Rcr : CommRing R] (x y : 𝕎 R) (n : Nat), ghostComponent n (f x y
) = ghostComponent n (g x y)) : forall (R) [_Rcr : CommRing R] (x y : 𝕎 R), f x 
y = g x y
参数：hf : IsPoly₂ p f；hg : IsPoly₂ p g；h : forall (R : Type u) [_Rcr : CommRing R]
 (x y : 𝕎 R) (n : Nat), ghostComponent n (f x y) = ghostComponent n (g x y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.poly_eq_of_wittPolynomial_bind_eq'`：poly_eq_of_wittPolynomial
_bind_eq' [Fact p.Prime] (f g : Nat -> MvPolynomial (idx × Nat) Int) (h : forall
 n, bind₁ f (wittPolynomial p _ n) …
· 使用定理 `MvPolynomial.funext`：funext {σ : Type*} {p q : MvPolynomial σ R} (h : fo
rall x : σ -> R, eval x p = eval x q) : p = q
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.hom_bind₁`：hom_bind₁ (f : MvPolynomial τ R ->+* S) (g : σ -
> MvPolynomial τ R) (φ : MvPolynomial σ R) : f (bind₁ g φ) = eval₂Hom (f.comp C)
 (fun i => f…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `MvPolynomial.map_eval₂Hom`：map_eval₂Hom [CommSemiring S₂] (f : R ->+* S₁
) (g : σ -> S₁) (φ : S₁ ->+* S₂) (p : MvPolynomial σ R) : φ (eval₂Hom f g p) = e
val₂Hom (φ.comp…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem ext [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g)
    (h : ∀ (R : Type u) [_Rcr : CommRing R] (x y : 𝕎 R) (n : ℕ),
        ghostComponent n (f x y) = ghostComponent n (g x y)) :
    ∀ (R) [_Rcr : CommRing R] (x y : 𝕎 R), f x y = g x y := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf, hg, poly_eq_of_wittPolynomial_bind_eq' p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift ℤ) (mk p fun i => ⟨x (0, i)⟩) (mk p fun i => ⟨x (1, i)⟩) k
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  apply (ULift.ringEquiv.symm : ℤ ≃+* _).injective
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
/-
**WittVector.IsPoly₂.map** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.IsPoly₂`。
形式化陈述：map [Fact p.Prime] {f} (hf : IsPoly₂ p f) (g : R ->+* S) (x y : 𝕎 R) : map
 g (f x y) = f (map g x) (map g y)
参数：hf : IsPoly₂ p f；g : R ->+* S；x y : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem map [Fact p.Prime] {f} (hf : IsPoly₂ p f) (g : R →+* S) (x y : 𝕎 R) :
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
    let args := simpArgs.map (·.getElems) |>.getD #[]
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
    | `($id:ident) => getFVarId id <|> runIntro id id.getId
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
  let nm ← withMainContext <|
    if let .fvar fvarId := (R : Expr) then
      fvarId.getUserName
    else
      Meta.getUnusedUserName `R
  evalTactic <| ← `(tactic| iterate 2 infer_instance)
  let R := mkIdent nm
  evalTactic <| ← `(tactic| clear! $R)
  evalTactic <| ← `(tactic| intro $(mkIdent nm):ident $(mkIdent (.str nm "_inst")):ident $ids'*)

end Tactic

end WittVector

