/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.StructurePolynomial

/-!
# Witt vectors

In this file we define the type of `p`-typical Witt vectors and ring operations on it.
The ring axioms are verified in `Mathlib/RingTheory/WittVector/Basic.lean`.

For a fixed commutative ring `R` and prime `p`,
a Witt vector `x : 𝕎 R` is an infinite sequence `ℕ → R` of elements of `R`.
However, the ring operations `+` and `*` are not defined in the obvious component-wise way.
Instead, these operations are defined via certain polynomials
using the machinery in `Mathlib/RingTheory/WittVector/StructurePolynomial.lean`.
The `n`th value of the sum of two Witt vectors can depend on the `0`-th through `n`th values
of the summands. This effectively simulates a “carrying” operation.

## Main definitions

* `WittVector p R`: the type of `p`-typical Witt vectors with coefficients in `R`.
* `WittVector.coeff x n`: projects the `n`th value of the Witt vector `x`.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


noncomputable section

/--
Definition of `WittVector` / `WittVector` 的定义

English:
structure WittVector
  parameters: (p : Nat) (R : Type*)
  (no additional axioms)

中文:
结构 WittVector
  参数: (p : 自然数) (R : 类型)
  (无附加公理)
-/
structure WittVector (p : Nat) (R : Type*) where mk' ::
  /-- `x.coeff n` is the `n`th coefficient of the Witt vector `x`.

  This concept does not have a standard name in the literature.
  -/
  coeff : Nat -> R

/--
Definition of `WittVector.mk` / `WittVector.mk` 的定义

English:
definition WittVector.mk
  signature: (p : Nat) {R : Type*} (coeff : Nat -> R)
  body: mk' coeff

中文:
定义 WittVector.mk
  签名: (p : 自然数) {R : 类型} (coeff : 自然数 -> R)
  定义体: mk' coeff
-/
def WittVector.mk (p : Nat) {R : Type*} (coeff : Nat -> R) : WittVector p R := mk' coeff

variable {p : Nat}

/- We cannot make this `localized` notation, because the `p` on the RHS doesn't occur on the left
Hiding the `p` in the notation is very convenient, so we opt for repeating the `local notation`
in other files that use Witt vectors. -/
local notation "𝕎" => WittVector p -- type as `\bbW`

namespace WittVector

variable {R : Type*}

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n)
  statement: x = y
  proof: by
  cases x
  cases y
  simp only at h
  simp [funext_iff, h]

中文:
定理 ext
  条件: {x y : 𝕎 R} (h : 对任意 n, x.coeff n = y.coeff n)
  结论: x = y
  证明: by
  cases x
  cases y
  simp only at h
  simp [funext_iff, h]

Depends on / 依赖: funext_iff
-/
theorem ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : x = y := by
  cases x
  cases y
  simp only at h
  simp [funext_iff, h]

/--
theorem `coeff_surjective` / 定理 `coeff_surjective`

English:
theorem coeff_surjective
  given: (n : Nat)
  proof: fun x => ⟨(mk p fun _ => x), rfl⟩

中文:
定理 coeff_surjective
  条件: (n : 自然数)
  证明: fun x => ⟨(mk p fun _ => x), rfl⟩
-/
theorem coeff_surjective (n : Nat) :
    Function.Surjective (fun (x : 𝕎 R) => x.coeff n) :=
  fun x => ⟨(mk p fun _ => x), rfl⟩

variable (p)

@[simp]
/--
theorem `coeff_mk` / 定理 `coeff_mk`

English:
theorem coeff_mk
  given: (x : Nat -> R)
  statement: (mk p x).coeff = x
  proof: rfl

中文:
定理 coeff_mk
  条件: (x : 自然数 -> R)
  结论: (mk p x).coeff = x
  证明: rfl
-/
theorem coeff_mk (x : Nat -> R) : (mk p x).coeff = x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor (WittVector p)
  body: mk p (f ∘ v.coeff)
  mapConst a _ := mk p fun _ => a

中文:
实例 :
  签名: Functor (WittVector p)
  定义体: mk p (f ∘ v.coeff)
  mapConst a _ := mk p fun _ => a

Depends on / 依赖: v.coeff
-/
instance : Functor (WittVector p) where
  map f v := mk p (f ∘ v.coeff)
  mapConst a _ := mk p fun _ => a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor (WittVector p)
  body: rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

中文:
实例 :
  签名: LawfulFunctor (WittVector p)
  定义体: rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
-/
instance : LawfulFunctor (WittVector p) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

variable [hp : Fact p.Prime] [CommRing R]

open MvPolynomial

section RingOperations

/--
Definition of `wittZero` / `wittZero` 的定义

English:
definition wittZero
  signature: : Nat -> MvPolynomial (Fin 0 × Nat) Int
  body: wittStructureInt p 0

中文:
定义 wittZero
  签名: : 自然数 -> MvPolynomial (Fin 0 × 自然数) 整数
  定义体: wittStructureInt p 0

Depends on / 依赖: wittStructureInt
-/
def wittZero : Nat -> MvPolynomial (Fin 0 × Nat) Int :=
  wittStructureInt p 0

/--
Definition of `wittOne` / `wittOne` 的定义

English:
definition wittOne
  signature: : Nat -> MvPolynomial (Fin 0 × Nat) Int
  body: wittStructureInt p 1

中文:
定义 wittOne
  签名: : 自然数 -> MvPolynomial (Fin 0 × 自然数) 整数
  定义体: wittStructureInt p 1

Depends on / 依赖: wittStructureInt
-/
def wittOne : Nat -> MvPolynomial (Fin 0 × Nat) Int :=
  wittStructureInt p 1

/--
Definition of `wittAdd` / `wittAdd` 的定义

English:
definition wittAdd
  signature: : Nat -> MvPolynomial (Fin 2 × Nat) Int
  body: wittStructureInt p (X 0 + X 1)

中文:
定义 wittAdd
  签名: : 自然数 -> MvPolynomial (Fin 2 × 自然数) 整数
  定义体: wittStructureInt p (X 0 + X 1)

Depends on / 依赖: wittStructureInt
-/
def wittAdd : Nat -> MvPolynomial (Fin 2 × Nat) Int :=
  wittStructureInt p (X 0 + X 1)

/--
Definition of `wittNSMul` / `wittNSMul` 的定义

English:
definition wittNSMul
  signature: (n : Nat)
  body: wittStructureInt p (n • X (0 : (Fin 1)))

中文:
定义 wittNSMul
  签名: (n : 自然数)
  定义体: wittStructureInt p (n • X (0 : (Fin 1)))

Depends on / 依赖: wittStructureInt
-/
def wittNSMul (n : Nat) : Nat -> MvPolynomial (Fin 1 × Nat) Int :=
  wittStructureInt p (n • X (0 : (Fin 1)))

/--
Definition of `wittZSMul` / `wittZSMul` 的定义

English:
definition wittZSMul
  signature: (n : Int)
  body: wittStructureInt p (n • X (0 : (Fin 1)))

中文:
定义 wittZSMul
  签名: (n : 整数)
  定义体: wittStructureInt p (n • X (0 : (Fin 1)))

Depends on / 依赖: wittStructureInt
-/
def wittZSMul (n : Int) : Nat -> MvPolynomial (Fin 1 × Nat) Int :=
  wittStructureInt p (n • X (0 : (Fin 1)))

/--
Definition of `wittSub` / `wittSub` 的定义

English:
definition wittSub
  signature: : Nat -> MvPolynomial (Fin 2 × Nat) Int
  body: wittStructureInt p (X 0 - X 1)

中文:
定义 wittSub
  签名: : 自然数 -> MvPolynomial (Fin 2 × 自然数) 整数
  定义体: wittStructureInt p (X 0 - X 1)

Depends on / 依赖: wittStructureInt
-/
def wittSub : Nat -> MvPolynomial (Fin 2 × Nat) Int :=
  wittStructureInt p (X 0 - X 1)

/--
Definition of `wittMul` / `wittMul` 的定义

English:
definition wittMul
  signature: : Nat -> MvPolynomial (Fin 2 × Nat) Int
  body: wittStructureInt p (X 0 * X 1)

中文:
定义 wittMul
  签名: : 自然数 -> MvPolynomial (Fin 2 × 自然数) 整数
  定义体: wittStructureInt p (X 0 * X 1)

Depends on / 依赖: wittStructureInt
-/
def wittMul : Nat -> MvPolynomial (Fin 2 × Nat) Int :=
  wittStructureInt p (X 0 * X 1)

/--
Definition of `wittNeg` / `wittNeg` 的定义

English:
definition wittNeg
  signature: : Nat -> MvPolynomial (Fin 1 × Nat) Int
  body: wittStructureInt p (-X 0)

中文:
定义 wittNeg
  签名: : 自然数 -> MvPolynomial (Fin 1 × 自然数) 整数
  定义体: wittStructureInt p (-X 0)

Depends on / 依赖: wittStructureInt
-/
def wittNeg : Nat -> MvPolynomial (Fin 1 × Nat) Int :=
  wittStructureInt p (-X 0)

/--
Definition of `wittPow` / `wittPow` 的定义

English:
definition wittPow
  signature: (n : Nat)
  body: wittStructureInt p (X 0 ^ n)

中文:
定义 wittPow
  签名: (n : 自然数)
  定义体: wittStructureInt p (X 0 ^ n)

Depends on / 依赖: wittStructureInt
-/
def wittPow (n : Nat) : Nat -> MvPolynomial (Fin 1 × Nat) Int :=
  wittStructureInt p (X 0 ^ n)

variable {p}


/--
Definition of `peval` / `peval` 的定义

English:
definition peval
  signature: {k : Nat} (φ : MvPolynomial (Fin k × Nat) Int) (x : Fin k -> Nat -> R)
  body: aeval (Function.uncurry x) φ

中文:
定义 peval
  签名: {k : 自然数} (φ : MvPolynomial (Fin k × 自然数) 整数) (x : Fin k -> 自然数 -> R)
  定义体: aeval (Function.uncurry x) φ

Depends on / 依赖: Function, Function.uncurry, uncurry
-/
def peval {k : Nat} (φ : MvPolynomial (Fin k × Nat) Int) (x : Fin k -> Nat -> R) : R :=
  aeval (Function.uncurry x) φ

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: {k : Nat} (φ : Nat -> MvPolynomial (Fin k × Nat) Int) (x : Fin k -> 𝕎 R)
  body: mk p fun n => peval (φ n) fun i => (x i).coeff

中文:
定义 eval
  签名: {k : 自然数} (φ : 自然数 -> MvPolynomial (Fin k × 自然数) 整数) (x : Fin k -> 𝕎 R)
  定义体: mk p fun n => peval (φ n) fun i => (x i).coeff
-/
def eval {k : Nat} (φ : Nat -> MvPolynomial (Fin k × Nat) Int) (x : Fin k -> 𝕎 R) : 𝕎 R :=
  mk p fun n => peval (φ n) fun i => (x i).coeff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (𝕎 R)
  body: ⟨eval (wittZero p) ![]⟩

中文:
实例 :
  签名: Zero (𝕎 R)
  定义体: ⟨eval (wittZero p) ![]⟩

Depends on / 依赖: wittZero
-/
instance : Zero (𝕎 R) :=
  ⟨eval (wittZero p) ![]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (𝕎 R)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (𝕎 R)
  定义体: ⟨0⟩
-/
instance : Inhabited (𝕎 R) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (𝕎 R)
  body: ⟨eval (wittOne p) ![]⟩

中文:
实例 :
  签名: One (𝕎 R)
  定义体: ⟨eval (wittOne p) ![]⟩

Depends on / 依赖: wittOne
-/
instance : One (𝕎 R) :=
  ⟨eval (wittOne p) ![]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (𝕎 R)
  body: ⟨fun x y => eval (wittAdd p) ![x, y]⟩

中文:
实例 :
  签名: Add (𝕎 R)
  定义体: ⟨fun x y => eval (wittAdd p) ![x, y]⟩

Depends on / 依赖: wittAdd
-/
instance : Add (𝕎 R) :=
  ⟨fun x y => eval (wittAdd p) ![x, y]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (𝕎 R)
  body: ⟨fun x y => eval (wittSub p) ![x, y]⟩

中文:
实例 :
  签名: Sub (𝕎 R)
  定义体: ⟨fun x y => eval (wittSub p) ![x, y]⟩

Depends on / 依赖: wittSub
-/
instance : Sub (𝕎 R) :=
  ⟨fun x y => eval (wittSub p) ![x, y]⟩

/--
Instance `hasNatScalar` / 实例 `hasNatScalar`

English:
instance hasNatScalar
  signature: : SMul Nat (𝕎 R)
  body: ⟨fun n x => eval (wittNSMul p n) ![x]⟩

中文:
实例 hasNatScalar
  签名: : SMul 自然数 (𝕎 R)
  定义体: ⟨fun n x => eval (wittNSMul p n) ![x]⟩

Depends on / 依赖: wittNSMul
-/
instance hasNatScalar : SMul Nat (𝕎 R) :=
  ⟨fun n x => eval (wittNSMul p n) ![x]⟩

/--
Instance `hasIntScalar` / 实例 `hasIntScalar`

English:
instance hasIntScalar
  signature: : SMul Int (𝕎 R)
  body: ⟨fun n x => eval (wittZSMul p n) ![x]⟩

中文:
实例 hasIntScalar
  签名: : SMul 整数 (𝕎 R)
  定义体: ⟨fun n x => eval (wittZSMul p n) ![x]⟩

Depends on / 依赖: wittZSMul
-/
instance hasIntScalar : SMul Int (𝕎 R) :=
  ⟨fun n x => eval (wittZSMul p n) ![x]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (𝕎 R)
  body: ⟨fun x y => eval (wittMul p) ![x, y]⟩

中文:
实例 :
  签名: Mul (𝕎 R)
  定义体: ⟨fun x y => eval (wittMul p) ![x, y]⟩

Depends on / 依赖: wittMul
-/
instance : Mul (𝕎 R) :=
  ⟨fun x y => eval (wittMul p) ![x, y]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (𝕎 R)
  body: ⟨fun x => eval (wittNeg p) ![x]⟩

中文:
实例 :
  签名: Neg (𝕎 R)
  定义体: ⟨fun x => eval (wittNeg p) ![x]⟩

Depends on / 依赖: wittNeg
-/
instance : Neg (𝕎 R) :=
  ⟨fun x => eval (wittNeg p) ![x]⟩

/--
Instance `hasNatPow` / 实例 `hasNatPow`

English:
instance hasNatPow
  signature: : Pow (𝕎 R) Nat
  body: ⟨fun x n => eval (wittPow p n) ![x]⟩

中文:
实例 hasNatPow
  签名: : Pow (𝕎 R) 自然数
  定义体: ⟨fun x n => eval (wittPow p n) ![x]⟩

Depends on / 依赖: wittPow
-/
instance hasNatPow : Pow (𝕎 R) Nat :=
  ⟨fun x n => eval (wittPow p n) ![x]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (𝕎 R)
  body: ⟨Nat.unaryCast⟩

中文:
实例 :
  签名: 自然数Cast (𝕎 R)
  定义体: ⟨Nat.unaryCast⟩

Depends on / 依赖: Nat.unaryCast, unaryCast
-/
instance : NatCast (𝕎 R) :=
  ⟨Nat.unaryCast⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (𝕎 R)
  body: ⟨Int.castDef⟩

中文:
实例 :
  签名: 整数Cast (𝕎 R)
  定义体: ⟨Int.castDef⟩

Depends on / 依赖: Int.castDef, castDef
-/
instance : IntCast (𝕎 R) :=
  ⟨Int.castDef⟩

end RingOperations

section WittStructureSimplifications

@[simp]
/--
theorem `wittZero_eq_zero` / 定理 `wittZero_eq_zero`

English:
theorem wittZero_eq_zero
  given: (n : Nat)
  statement: wittZero p n = 0
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittZero, wittStructureRat, bind₁, aeval_zero', constantCoeff_xInTermsOfW, map_zero,
    map_wittStructureInt]

@[simp]

中文:
定理 wittZero_eq_zero
  条件: (n : 自然数)
  结论: wittZero p n = 0
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittZero, wittStructureRat, bind₁, aeval_zero', constantCoeff_xInTermsOfW, map_zero,
    map_wittStructureInt]

@[simp]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, aeval_zero, castRingHom, cast_injective, constantCoeff_xInTermsOfW, map_injective, map_wittStructureInt, map_zero, wittStructureRat, wittZero
-/
theorem wittZero_eq_zero (n : Nat) : wittZero p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittZero, wittStructureRat, bind₁, aeval_zero', constantCoeff_xInTermsOfW, map_zero,
    map_wittStructureInt]

@[simp]
/--
theorem `wittOne_zero_eq_one` / 定理 `wittOne_zero_eq_one`

English:
theorem wittOne_zero_eq_one
  statement: wittOne p 0 = 1
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittOne, wittStructureRat, xInTermsOfW_zero, map_one, bind₁_X_right,
    map_wittStructureInt]

@[simp]

中文:
定理 wittOne_zero_eq_one
  结论: wittOne p 0 = 1
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittOne, wittStructureRat, xInTermsOfW_zero, map_one, bind₁_X_right,
    map_wittStructureInt]

@[simp]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, castRingHom, cast_injective, map_injective, map_one, map_wittStructureInt, wittOne, wittStructureRat, xInTermsOfW_zero
-/
theorem wittOne_zero_eq_one : wittOne p 0 = 1 := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittOne, wittStructureRat, xInTermsOfW_zero, map_one, bind₁_X_right,
    map_wittStructureInt]

@[simp]
/--
theorem `wittOne_pos_eq_zero` / 定理 `wittOne_pos_eq_zero`

English:
theorem wittOne_pos_eq_zero
  given: (n : Nat) (hn : 0 < n)
  statement: wittOne p n = 0
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittOne, wittStructureRat, map_zero, map_one, map_wittStructureInt]
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [xInTermsOfW_eq]
  simp only [map_mul, map_sub, map_sum, map_pow, bind₁

中文:
定理 wittOne_pos_eq_zero
  条件: (n : 自然数) (hn : 0 < n)
  结论: wittOne p n = 0
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittOne, wittStructureRat, map_zero, map_one, map_wittStructureInt]
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [xInTermsOfW_eq]
  simp only [map_mul, map_sub, map_sum, map_pow, bind₁

Depends on / 依赖: Finset, Finset.sum_eq_single, Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, Nat.strong_induction_on, castRingHom, cast_injective, map_injective, map_mul, map_one, map_pow, map_sub, map_sum, map_wittStructureInt, map_zero, one_mul, one_pow, pow_zero
-/
theorem wittOne_pos_eq_zero (n : Nat) (hn : 0 < n) : wittOne p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittOne, wittStructureRat, map_zero, map_one, map_wittStructureInt]
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [xInTermsOfW_eq]
  simp only [map_mul, map_sub, map_sum, map_pow, bind₁_X_right,
    bind₁_C_right]
  rw [sub_mul]; rw [one_mul]
  rw [Finset.sum_eq_single 0]
  · simp only [one_mul, pow_zero]
    simp only [one_pow, one_mul, xInTermsOfW_zero, sub_self, bind₁_X_right]
  · intro i hin hi0
    rw [Finset.mem_range] at hin
    rw [IH _ hin (Nat.pos_of_ne_zero hi0)]; rw [zero_pow (pow_ne_zero _ hp.1.ne_zero)]; rw [mul_zero]
  · grind

@[simp]
/--
theorem `wittAdd_zero` / 定理 `wittAdd_zero`

English:
theorem wittAdd_zero
  statement: wittAdd p 0 = X (0, 0) + X (1, 0)
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittAdd, wittStructureRat, map_add, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]

中文:
定理 wittAdd_zero
  结论: wittAdd p 0 = X (0, 0) + X (1, 0)
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittAdd, wittStructureRat, map_add, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, castRingHom, cast_injective, map_X, map_add, map_injective, map_wittStructureInt, rename_X, wittAdd, wittPolynomial_zero, wittStructureRat, xInTermsOfW_zero
-/
theorem wittAdd_zero : wittAdd p 0 = X (0, 0) + X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittAdd, wittStructureRat, map_add, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]
/--
theorem `wittSub_zero` / 定理 `wittSub_zero`

English:
theorem wittSub_zero
  statement: wittSub p 0 = X (0, 0) - X (1, 0)
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittSub, wittStructureRat, map_sub, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]

中文:
定理 wittSub_zero
  结论: wittSub p 0 = X (0, 0) - X (1, 0)
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittSub, wittStructureRat, map_sub, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, castRingHom, cast_injective, map_X, map_injective, map_sub, map_wittStructureInt, rename_X, wittPolynomial_zero, wittStructureRat, wittSub, xInTermsOfW_zero
-/
theorem wittSub_zero : wittSub p 0 = X (0, 0) - X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittSub, wittStructureRat, map_sub, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]
/--
theorem `wittMul_zero` / 定理 `wittMul_zero`

English:
theorem wittMul_zero
  statement: wittMul p 0 = X (0, 0) * X (1, 0)
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittMul, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_mul, bind₁_X_right, map_wittStructureInt]

@[simp]

中文:
定理 wittMul_zero
  结论: wittMul p 0 = X (0, 0) * X (1, 0)
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittMul, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_mul, bind₁_X_right, map_wittStructureInt]

@[simp]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, castRingHom, cast_injective, map_X, map_injective, map_mul, map_wittStructureInt, rename_X, wittMul, wittPolynomial_zero, wittStructureRat, xInTermsOfW_zero
-/
theorem wittMul_zero : wittMul p 0 = X (0, 0) * X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittMul, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_mul, bind₁_X_right, map_wittStructureInt]

@[simp]
/--
theorem `wittNeg_zero` / 定理 `wittNeg_zero`

English:
theorem wittNeg_zero
  statement: wittNeg p 0 = -X (0, 0)
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittNeg, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_neg, bind₁_X_right, map_wittStructureInt]

@[simp]

中文:
定理 wittNeg_zero
  结论: wittNeg p 0 = -X (0, 0)
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittNeg, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_neg, bind₁_X_right, map_wittStructureInt]

@[simp]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, castRingHom, cast_injective, map_X, map_injective, map_neg, map_wittStructureInt, rename_X, wittNeg, wittPolynomial_zero, wittStructureRat, xInTermsOfW_zero
-/
theorem wittNeg_zero : wittNeg p 0 = -X (0, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [wittNeg, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_neg, bind₁_X_right, map_wittStructureInt]

@[simp]
/--
theorem `constantCoeff_wittAdd` / 定理 `constantCoeff_wittAdd`

English:
theorem constantCoeff_wittAdd
  given: (n : Nat)
  statement: constantCoeff (wittAdd p n) = 0
  proof: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [add_zero, map_add, constantCoeff_X]

@[simp]

中文:
定理 constantCoeff_wittAdd
  条件: (n : 自然数)
  结论: constantCoeff (wittAdd p n) = 0
  证明: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [add_zero, map_add, constantCoeff_X]

@[simp]

Depends on / 依赖: add_zero, constantCoeff_X, constantCoeff_wittStructureInt, map_add
-/
theorem constantCoeff_wittAdd (n : Nat) : constantCoeff (wittAdd p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [add_zero, map_add, constantCoeff_X]

@[simp]
/--
theorem `constantCoeff_wittSub` / 定理 `constantCoeff_wittSub`

English:
theorem constantCoeff_wittSub
  given: (n : Nat)
  statement: constantCoeff (wittSub p n) = 0
  proof: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [sub_zero, map_sub, constantCoeff_X]

@[simp]

中文:
定理 constantCoeff_wittSub
  条件: (n : 自然数)
  结论: constantCoeff (wittSub p n) = 0
  证明: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [sub_zero, map_sub, constantCoeff_X]

@[simp]

Depends on / 依赖: constantCoeff_X, constantCoeff_wittStructureInt, map_sub, sub_zero
-/
theorem constantCoeff_wittSub (n : Nat) : constantCoeff (wittSub p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [sub_zero, map_sub, constantCoeff_X]

@[simp]
/--
theorem `constantCoeff_wittMul` / 定理 `constantCoeff_wittMul`

English:
theorem constantCoeff_wittMul
  given: (n : Nat)
  statement: constantCoeff (wittMul p n) = 0
  proof: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [mul_zero, map_mul, constantCoeff_X]

@[simp]

中文:
定理 constantCoeff_wittMul
  条件: (n : 自然数)
  结论: constantCoeff (wittMul p n) = 0
  证明: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [mul_zero, map_mul, constantCoeff_X]

@[simp]

Depends on / 依赖: constantCoeff_X, constantCoeff_wittStructureInt, map_mul, mul_zero
-/
theorem constantCoeff_wittMul (n : Nat) : constantCoeff (wittMul p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [mul_zero, map_mul, constantCoeff_X]

@[simp]
/--
theorem `constantCoeff_wittNeg` / 定理 `constantCoeff_wittNeg`

English:
theorem constantCoeff_wittNeg
  given: (n : Nat)
  statement: constantCoeff (wittNeg p n) = 0
  proof: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [neg_zero, map_neg, constantCoeff_X]

@[simp]

中文:
定理 constantCoeff_wittNeg
  条件: (n : 自然数)
  结论: constantCoeff (wittNeg p n) = 0
  证明: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [neg_zero, map_neg, constantCoeff_X]

@[simp]

Depends on / 依赖: constantCoeff_X, constantCoeff_wittStructureInt, map_neg, neg_zero
-/
theorem constantCoeff_wittNeg (n : Nat) : constantCoeff (wittNeg p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [neg_zero, map_neg, constantCoeff_X]

@[simp]
/--
theorem `constantCoeff_wittNSMul` / 定理 `constantCoeff_wittNSMul`

English:
theorem constantCoeff_wittNSMul
  given: (m : Nat) (n : Nat)
  statement: constantCoeff (wittNSMul p m n) = 0
  proof: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_nsmul, constantCoeff_X]

@[simp]

中文:
定理 constantCoeff_wittNSMul
  条件: (m : 自然数) (n : 自然数)
  结论: constantCoeff (wittNSMul p m n) = 0
  证明: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_nsmul, constantCoeff_X]

@[simp]

Depends on / 依赖: constantCoeff_X, constantCoeff_wittStructureInt, map_nsmul, smul_zero
-/
theorem constantCoeff_wittNSMul (m : Nat) (n : Nat) : constantCoeff (wittNSMul p m n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_nsmul, constantCoeff_X]

@[simp]
/--
theorem `constantCoeff_wittZSMul` / 定理 `constantCoeff_wittZSMul`

English:
theorem constantCoeff_wittZSMul
  given: (z : Int) (n : Nat)
  statement: constantCoeff (wittZSMul p z n) = 0
  proof: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_zsmul, constantCoeff_X]

中文:
定理 constantCoeff_wittZSMul
  条件: (z : 整数) (n : 自然数)
  结论: constantCoeff (wittZSMul p z n) = 0
  证明: by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_zsmul, constantCoeff_X]

Depends on / 依赖: constantCoeff_X, constantCoeff_wittStructureInt, map_zsmul, smul_zero
-/
theorem constantCoeff_wittZSMul (z : Int) (n : Nat) : constantCoeff (wittZSMul p z n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_zsmul, constantCoeff_X]

end WittStructureSimplifications

section Coeff

variable (R)

@[simp]
/--
theorem `zero_coeff` / 定理 `zero_coeff`

English:
theorem zero_coeff
  given: (n : Nat)
  statement: (0 : 𝕎 R).coeff n = 0
  proof: show (aeval _ (wittZero p n) : R) = 0 by simp only [wittZero_eq_zero, map_zero]

@[simp]

中文:
定理 zero_coeff
  条件: (n : 自然数)
  结论: (0 : 𝕎 R).coeff n = 0
  证明: show (aeval _ (wittZero p n) : R) = 0 by simp only [wittZero_eq_zero, map_zero]

@[simp]

Depends on / 依赖: e.toOpenPartialHomeomorph.symm, map_zero, toOpenPartialHomeomorph, wittZero, wittZero_eq_zero
-/
theorem zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0 :=
  show (aeval _ (wittZero p n) : R) = 0 by simp only [wittZero_eq_zero, map_zero]

@[simp]
/--
theorem `one_coeff_zero` / 定理 `one_coeff_zero`

English:
theorem one_coeff_zero
  statement: (1 : 𝕎 R).coeff 0 = 1
  proof: show (aeval _ (wittOne p 0) : R) = 1 by simp only [wittOne_zero_eq_one, map_one]

@[simp]

中文:
定理 one_coeff_zero
  结论: (1 : 𝕎 R).coeff 0 = 1
  证明: show (aeval _ (wittOne p 0) : R) = 1 by simp only [wittOne_zero_eq_one, map_one]

@[simp]

Depends on / 依赖: map_one, wittOne, wittOne_zero_eq_one
-/
theorem one_coeff_zero : (1 : 𝕎 R).coeff 0 = 1 :=
  show (aeval _ (wittOne p 0) : R) = 1 by simp only [wittOne_zero_eq_one, map_one]

@[simp]
/--
theorem `one_coeff_eq_of_pos` / 定理 `one_coeff_eq_of_pos`

English:
theorem one_coeff_eq_of_pos
  given: (n : Nat) (hn : 0 < n)
  statement: coeff (1 : 𝕎 R) n = 0
  proof: show (aeval _ (wittOne p n) : R) = 0 by simp only [hn, wittOne_pos_eq_zero, map_zero]

中文:
定理 one_coeff_eq_of_pos
  条件: (n : 自然数) (hn : 0 < n)
  结论: coeff (1 : 𝕎 R) n = 0
  证明: show (aeval _ (wittOne p n) : R) = 0 by simp only [hn, wittOne_pos_eq_zero, map_zero]

Depends on / 依赖: map_zero, wittOne, wittOne_pos_eq_zero
-/
theorem one_coeff_eq_of_pos (n : Nat) (hn : 0 < n) : coeff (1 : 𝕎 R) n = 0 :=
  show (aeval _ (wittOne p n) : R) = 0 by simp only [hn, wittOne_pos_eq_zero, map_zero]

variable {p R}

@[simp]
/--
theorem `v2_coeff` / 定理 `v2_coeff`

English:
theorem v2_coeff
  given: {p' R'} (x y : WittVector p' R') (i : Fin 2)
  proof: by fin_cases i <;> simp

中文:
定理 v2_coeff
  条件: {p' R'} (x y : WittVector p' R') (i : Fin 2)
  证明: by fin_cases i <;> simp

Depends on / 依赖: fin_cases
-/
theorem v2_coeff {p' R'} (x y : WittVector p' R') (i : Fin 2) :
    (![x, y] i).coeff = ![x.coeff, y.coeff] i := by fin_cases i <;> simp

/--
theorem `add_coeff` / 定理 `add_coeff`

English:
theorem add_coeff
  given: (x y : 𝕎 R) (n : Nat)
  proof: by
  simp [(· + ·), Add.add, eval]

中文:
定理 add_coeff
  条件: (x y : 𝕎 R) (n : 自然数)
  证明: by
  simp [(· + ·), Add.add, eval]

Depends on / 依赖: Add.add
-/
theorem add_coeff (x y : 𝕎 R) (n : Nat) :
    (x + y).coeff n = peval (wittAdd p n) ![x.coeff, y.coeff] := by
  simp [(· + ·), Add.add, eval]

/--
theorem `sub_coeff` / 定理 `sub_coeff`

English:
theorem sub_coeff
  given: (x y : 𝕎 R) (n : Nat)
  proof: by
  simp [(· - ·), Sub.sub, eval]

中文:
定理 sub_coeff
  条件: (x y : 𝕎 R) (n : 自然数)
  证明: by
  simp [(· - ·), Sub.sub, eval]

Depends on / 依赖: Sub.sub
-/
theorem sub_coeff (x y : 𝕎 R) (n : Nat) :
    (x - y).coeff n = peval (wittSub p n) ![x.coeff, y.coeff] := by
  simp [(· - ·), Sub.sub, eval]

/--
theorem `mul_coeff` / 定理 `mul_coeff`

English:
theorem mul_coeff
  given: (x y : 𝕎 R) (n : Nat)
  proof: by
  simp [(· * ·), Mul.mul, eval]

中文:
定理 mul_coeff
  条件: (x y : 𝕎 R) (n : 自然数)
  证明: by
  simp [(· * ·), Mul.mul, eval]

Depends on / 依赖: Mul.mul
-/
theorem mul_coeff (x y : 𝕎 R) (n : Nat) :
    (x * y).coeff n = peval (wittMul p n) ![x.coeff, y.coeff] := by
  simp [(· * ·), Mul.mul, eval]

/--
theorem `neg_coeff` / 定理 `neg_coeff`

English:
theorem neg_coeff
  given: (x : 𝕎 R) (n : Nat)
  statement: (-x).coeff n = peval (wittNeg p n) ![x.coeff]
  proof: by
  simp [Neg.neg, eval, Matrix.cons_fin_one]

中文:
定理 neg_coeff
  条件: (x : 𝕎 R) (n : 自然数)
  结论: (-x).coeff n = peval (wittNeg p n) ![x.coeff]
  证明: by
  simp [Neg.neg, eval, Matrix.cons_fin_one]

Depends on / 依赖: Matrix, Matrix.cons_fin_one, Neg.neg, cons_fin_one
-/
theorem neg_coeff (x : 𝕎 R) (n : Nat) : (-x).coeff n = peval (wittNeg p n) ![x.coeff] := by
  simp [Neg.neg, eval, Matrix.cons_fin_one]

/--
theorem `nsmul_coeff` / 定理 `nsmul_coeff`

English:
theorem nsmul_coeff
  given: (m : Nat) (x : 𝕎 R) (n : Nat)
  proof: by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]

中文:
定理 nsmul_coeff
  条件: (m : 自然数) (x : 𝕎 R) (n : 自然数)
  证明: by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]

Depends on / 依赖: Matrix, Matrix.cons_fin_one, SMul.smul, cons_fin_one
-/
theorem nsmul_coeff (m : Nat) (x : 𝕎 R) (n : Nat) :
    (m • x).coeff n = peval (wittNSMul p m n) ![x.coeff] := by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]

/--
theorem `zsmul_coeff` / 定理 `zsmul_coeff`

English:
theorem zsmul_coeff
  given: (m : Int) (x : 𝕎 R) (n : Nat)
  proof: by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]

中文:
定理 zsmul_coeff
  条件: (m : 整数) (x : 𝕎 R) (n : 自然数)
  证明: by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]

Depends on / 依赖: Matrix, Matrix.cons_fin_one, SMul.smul, cons_fin_one
-/
theorem zsmul_coeff (m : Int) (x : 𝕎 R) (n : Nat) :
    (m • x).coeff n = peval (wittZSMul p m n) ![x.coeff] := by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]

/--
theorem `pow_coeff` / 定理 `pow_coeff`

English:
theorem pow_coeff
  given: (m : Nat) (x : 𝕎 R) (n : Nat)
  proof: by
  simp [(· ^ ·), Pow.pow, eval, Matrix.cons_fin_one]

中文:
定理 pow_coeff
  条件: (m : 自然数) (x : 𝕎 R) (n : 自然数)
  证明: by
  simp [(· ^ ·), Pow.pow, eval, Matrix.cons_fin_one]

Depends on / 依赖: Matrix, Matrix.cons_fin_one, Pow.pow, cons_fin_one
-/
theorem pow_coeff (m : Nat) (x : 𝕎 R) (n : Nat) :
    (x ^ m).coeff n = peval (wittPow p m n) ![x.coeff] := by
  simp [(· ^ ·), Pow.pow, eval, Matrix.cons_fin_one]

/--
theorem `add_coeff_zero` / 定理 `add_coeff_zero`

English:
theorem add_coeff_zero
  given: (x y : 𝕎 R)
  statement: (x + y).coeff 0 = x.coeff 0 + y.coeff 0
  proof: by
  simp [add_coeff, peval, Function.uncurry]

中文:
定理 add_coeff_zero
  条件: (x y : 𝕎 R)
  结论: (x + y).coeff 0 = x.coeff 0 + y.coeff 0
  证明: by
  simp [add_coeff, peval, Function.uncurry]

Depends on / 依赖: Function, Function.uncurry, add_coeff, uncurry
-/
theorem add_coeff_zero (x y : 𝕎 R) : (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  simp [add_coeff, peval, Function.uncurry]

/--
theorem `mul_coeff_zero` / 定理 `mul_coeff_zero`

English:
theorem mul_coeff_zero
  given: (x y : 𝕎 R)
  statement: (x * y).coeff 0 = x.coeff 0 * y.coeff 0
  proof: by
  simp [mul_coeff, peval, Function.uncurry]

中文:
定理 mul_coeff_zero
  条件: (x y : 𝕎 R)
  结论: (x * y).coeff 0 = x.coeff 0 * y.coeff 0
  证明: by
  simp [mul_coeff, peval, Function.uncurry]

Depends on / 依赖: Function, Function.uncurry, mul_coeff, uncurry
-/
theorem mul_coeff_zero (x y : 𝕎 R) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  simp [mul_coeff, peval, Function.uncurry]

end Coeff

/--
theorem `wittAdd_vars` / 定理 `wittAdd_vars`

English:
theorem wittAdd_vars
  given: (n : Nat)
  statement: (wittAdd p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  proof: wittStructureInt_vars _ _ _

中文:
定理 wittAdd_vars
  条件: (n : 自然数)
  结论: (wittAdd p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  证明: wittStructureInt_vars _ _ _

Depends on / 依赖: wittStructureInt_vars
-/
theorem wittAdd_vars (n : Nat) : (wittAdd p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

/--
theorem `wittSub_vars` / 定理 `wittSub_vars`

English:
theorem wittSub_vars
  given: (n : Nat)
  statement: (wittSub p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  proof: wittStructureInt_vars _ _ _

中文:
定理 wittSub_vars
  条件: (n : 自然数)
  结论: (wittSub p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  证明: wittStructureInt_vars _ _ _

Depends on / 依赖: wittStructureInt_vars
-/
theorem wittSub_vars (n : Nat) : (wittSub p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

/--
theorem `wittMul_vars` / 定理 `wittMul_vars`

English:
theorem wittMul_vars
  given: (n : Nat)
  statement: (wittMul p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  proof: wittStructureInt_vars _ _ _

中文:
定理 wittMul_vars
  条件: (n : 自然数)
  结论: (wittMul p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  证明: wittStructureInt_vars _ _ _

Depends on / 依赖: wittStructureInt_vars
-/
theorem wittMul_vars (n : Nat) : (wittMul p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

/--
theorem `wittNeg_vars` / 定理 `wittNeg_vars`

English:
theorem wittNeg_vars
  given: (n : Nat)
  statement: (wittNeg p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  proof: wittStructureInt_vars _ _ _

中文:
定理 wittNeg_vars
  条件: (n : 自然数)
  结论: (wittNeg p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  证明: wittStructureInt_vars _ _ _

Depends on / 依赖: wittStructureInt_vars
-/
theorem wittNeg_vars (n : Nat) : (wittNeg p n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

/--
theorem `wittNSMul_vars` / 定理 `wittNSMul_vars`

English:
theorem wittNSMul_vars
  given: (m : Nat) (n : Nat)
  proof: wittStructureInt_vars _ _ _

中文:
定理 wittNSMul_vars
  条件: (m : 自然数) (n : 自然数)
  证明: wittStructureInt_vars _ _ _

Depends on / 依赖: wittStructureInt_vars
-/
theorem wittNSMul_vars (m : Nat) (n : Nat) :
    (wittNSMul p m n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

/--
theorem `wittZSMul_vars` / 定理 `wittZSMul_vars`

English:
theorem wittZSMul_vars
  given: (m : Int) (n : Nat)
  proof: wittStructureInt_vars _ _ _

中文:
定理 wittZSMul_vars
  条件: (m : 整数) (n : 自然数)
  证明: wittStructureInt_vars _ _ _

Depends on / 依赖: wittStructureInt_vars
-/
theorem wittZSMul_vars (m : Int) (n : Nat) :
    (wittZSMul p m n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

/--
theorem `wittPow_vars` / 定理 `wittPow_vars`

English:
theorem wittPow_vars
  given: (m : Nat) (n : Nat)
  statement: (wittPow p m n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  proof: wittStructureInt_vars _ _ _

中文:
定理 wittPow_vars
  条件: (m : 自然数) (n : 自然数)
  结论: (wittPow p m n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1)
  证明: wittStructureInt_vars _ _ _

Depends on / 依赖: wittStructureInt_vars
-/
theorem wittPow_vars (m : Nat) (n : Nat) : (wittPow p m n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

end WittVector
