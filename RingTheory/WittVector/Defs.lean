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

/-- `WittVector p R` is the ring of `p`-typical Witt vectors over the commutative ring `R`,
where `p` is a prime number.

If `p` is invertible in `R`, this ring is isomorphic to `ℕ → R` (the product of `ℕ` copies of `R`).
If `R` is a ring of characteristic `p`, then `WittVector p R` is a ring of characteristic `0`.
The canonical example is `WittVector p (ZMod p)`,
which is isomorphic to the `p`-adic integers `ℤ_[p]`. -/
/-
**WittVector** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℕ → Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WittVector p R` is the ring of `p`-typical Witt vectors over the commutative ri
ng `R`,
where `p` is a prime number.

If `p` is invertible in `R`, this ring is isomorphic to `ℕ → R` (the product of 
`ℕ` copies of `R`).
If `R` is a ring of characteristic `p`, then `WittVector p R` is a ring of chara
cteristic `0`.
The canonical example is `WittVector p (ZMod p)`,
which is isomorphic to the `p`-adic integers `ℤ_[p]`.
-/
structure WittVector (p : ℕ) (R : Type*) where mk' ::
  /-- `x.coeff n` is the `n`th coefficient of the Witt vector `x`.

  This concept does not have a standard name in the literature.
  -/
  coeff : ℕ → R

/-- Construct a Witt vector `mk p x : 𝕎 R` from a sequence `x` of elements of `R`.

This is preferred over `WittVector.mk'` because it has `p` explicit.
-/
/-
**WittVector.mk** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WittVector.mk (p : Nat) {R : Type*} (coeff : Nat -> R) : WittVector p R
参数：p : Nat；coeff : Nat -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a Witt vector `mk p x : 𝕎 R` from a sequence `x` of elements of `R`.

This is preferred over `WittVector.mk'` because it has `p` explicit.
-/
def WittVector.mk (p : ℕ) {R : Type*} (coeff : ℕ → R) : WittVector p R := mk' coeff

variable {p : ℕ}

/- We cannot make this `localized` notation, because the `p` on the RHS doesn't occur on the left
Hiding the `p` in the notation is very convenient, so we opt for repeating the `local notation`
in other files that use Witt vectors. -/
local notation "𝕎" => WittVector p -- type as `\bbW`

namespace WittVector

variable {R : Type*}

@[ext]
/-
**WittVector.ext** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : x = y
参数：h : forall n, x.coeff n = y.coeff n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.mk'.injEq`：∀ {p : ℕ} {R : Type u_1} (coeff coeff_1 : ℕ → R), 
({ coeff := coeff } = { coeff := coeff_1 }) = (coeff = coeff_1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext {x y : 𝕎 R} (h : ∀ n, x.coeff n = y.coeff n) : x = y := by
  cases x
  cases y
  simp only at h
  simp [funext_iff, h]
/-
**WittVector.coeff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_surjective (n : Nat) : Function.Surjective (fun (x : 𝕎 R) => x.coeff
 n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_surjective (n : ℕ) :
    Function.Surjective (fun (x : 𝕎 R) ↦ x.coeff n) :=
  fun x ↦ ⟨(mk p fun _ ↦ x), rfl⟩

variable (p)

@[simp]
/-
**WittVector.coeff_mk** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_mk (x : Nat -> R) : (mk p x).coeff = x
参数：x : Nat -> R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_mk (x : ℕ → R) : (mk p x).coeff = x :=
  rfl

/-- These instances are not needed for the rest of the development,
but it is interesting to establish early on that `WittVector p` is a lawful functor. -/
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These instances are not needed for the rest of the development,
but it is interesting to establish early on that `WittVector p` is a lawful func
tor.
-/
instance : Functor (WittVector p) where
  map f v := mk p (f ∘ v.coeff)
  mapConst a _ := mk p fun _ => a
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulFunctor (WittVector p) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

variable [hp : Fact p.Prime] [CommRing R]

open MvPolynomial

section RingOperations

/-- The polynomials used for defining the element `0` of the ring of Witt vectors. -/
/-
**WittVector.wittZero** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittZero : Nat -> MvPolynomial (Fin 0 × Nat) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials used for defining the element `0` of the ring of Witt vectors.
-/
def wittZero : ℕ → MvPolynomial (Fin 0 × ℕ) ℤ :=
  wittStructureInt p 0

/-- The polynomials used for defining the element `1` of the ring of Witt vectors. -/
/-
**WittVector.wittOne** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittOne : Nat -> MvPolynomial (Fin 0 × Nat) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials used for defining the element `1` of the ring of Witt vectors.
-/
def wittOne : ℕ → MvPolynomial (Fin 0 × ℕ) ℤ :=
  wittStructureInt p 1

/-- The polynomials used for defining the addition of the ring of Witt vectors. -/
/-
**WittVector.wittAdd** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittAdd : Nat -> MvPolynomial (Fin 2 × Nat) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials used for defining the addition of the ring of Witt vectors.
-/
def wittAdd : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ :=
  wittStructureInt p (X 0 + X 1)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
/-
**WittVector.wittNSMul** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittNSMul (n : Nat) : Nat -> MvPolynomial (Fin 1 × Nat) Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials used for defining repeated addition of the ring of Witt vectors.
-/
def wittNSMul (n : ℕ) : ℕ → MvPolynomial (Fin 1 × ℕ) ℤ :=
  wittStructureInt p (n • X (0 : (Fin 1)))

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
/-
**WittVector.wittZSMul** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittZSMul (n : Int) : Nat -> MvPolynomial (Fin 1 × Nat) Int
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials used for defining repeated addition of the ring of Witt vectors.
-/
def wittZSMul (n : ℤ) : ℕ → MvPolynomial (Fin 1 × ℕ) ℤ :=
  wittStructureInt p (n • X (0 : (Fin 1)))

/-- The polynomials used for describing the subtraction of the ring of Witt vectors. -/
/-
**WittVector.wittSub** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittSub : Nat -> MvPolynomial (Fin 2 × Nat) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials used for describing the subtraction of the ring of Witt vectors.
-/
def wittSub : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ :=
  wittStructureInt p (X 0 - X 1)

/-- The polynomials used for defining the multiplication of the ring of Witt vectors. -/
/-
**WittVector.wittMul** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittMul : Nat -> MvPolynomial (Fin 2 × Nat) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials used for defining the multiplication of the ring of Witt vectors
.
-/
def wittMul : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ :=
  wittStructureInt p (X 0 * X 1)

/-- The polynomials used for defining the negation of the ring of Witt vectors. -/
/-
**WittVector.wittNeg** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittNeg : Nat -> MvPolynomial (Fin 1 × Nat) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials used for defining the negation of the ring of Witt vectors.
-/
def wittNeg : ℕ → MvPolynomial (Fin 1 × ℕ) ℤ :=
  wittStructureInt p (-X 0)

/-- The polynomials used for defining repeated addition of the ring of Witt vectors. -/
/-
**WittVector.wittPow** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：wittPow (n : Nat) : Nat -> MvPolynomial (Fin 1 × Nat) Int
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomials used for defining repeated addition of the ring of Witt vectors.
-/
def wittPow (n : ℕ) : ℕ → MvPolynomial (Fin 1 × ℕ) ℤ :=
  wittStructureInt p (X 0 ^ n)

variable {p}


/-- An auxiliary definition used in `WittVector.eval`.
Evaluates a polynomial whose variables come from the disjoint union of `k` copies of `ℕ`,
with a curried evaluation `x`.
This can be defined more generally but we use only a specific instance here. -/
/-
**WittVector.peval** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：peval {k : Nat} (φ : MvPolynomial (Fin k × Nat) Int) (x : Fin k -> Nat -> 
R) : R
参数：φ : MvPolynomial (Fin k × Nat) Int；x : Fin k -> Nat -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition used in `WittVector.eval`.
Evaluates a polynomial whose variables come from the disjoint union of `k` copie
s of `ℕ`,
with a curried evaluation `x`.
This can be defined more generally but we use only a specific instance here.
-/
def peval {k : ℕ} (φ : MvPolynomial (Fin k × ℕ) ℤ) (x : Fin k → ℕ → R) : R :=
  aeval (Function.uncurry x) φ

/-- Let `φ` be a family of polynomials, indexed by natural numbers, whose variables come from the
disjoint union of `k` copies of `ℕ`, and let `xᵢ` be a Witt vector for `0 ≤ i < k`.

`eval φ x` evaluates `φ` mapping the variable `X_(i, n)` to the `n`th coefficient of `xᵢ`.

Instantiating `φ` with certain polynomials defined in
`Mathlib/RingTheory/WittVector/StructurePolynomial.lean` establishes the
ring operations on `𝕎 R`. For example, `WittVector.wittAdd` is such a `φ` with `k = 2`;
evaluating this at `(x₀, x₁)` gives us the sum of two Witt vectors `x₀ + x₁`.
-/
/-
**WittVector.eval** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：eval {k : Nat} (φ : Nat -> MvPolynomial (Fin k × Nat) Int) (x : Fin k -> 𝕎
 R) : 𝕎 R
参数：φ : Nat -> MvPolynomial (Fin k × Nat) Int；x : Fin k -> 𝕎 R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `φ` be a family of polynomials, indexed by natural numbers, whose variables 
come from the
disjoint union of `k` copies of `ℕ`, and let `xᵢ` be a Witt vector for `0 ≤ i < 
k`.

`eval φ x` evaluates `φ` mapping the variable `X_(i, n)` to the `n`th coefficien
t of `xᵢ`.

Instantiating `φ` with certain polynomials defined in
`Mathlib/RingTheory/WittVector/StructurePolynomial.lean` establishes the
ring operations on `𝕎 R`. For example, `WittVector.wittAdd` is such a `φ` with `
k = 2`;
evaluating this at `(x₀, x₁)` gives us the sum of two Witt vectors `x₀ + x₁`.
-/
def eval {k : ℕ} (φ : ℕ → MvPolynomial (Fin k × ℕ) ℤ) (x : Fin k → 𝕎 R) : 𝕎 R :=
  mk p fun n => peval (φ n) fun i => (x i).coeff
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (𝕎 R) :=
  ⟨eval (wittZero p) ![]⟩
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (𝕎 R) :=
  ⟨0⟩
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (𝕎 R) :=
  ⟨eval (wittOne p) ![]⟩
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (𝕎 R) :=
  ⟨fun x y => eval (wittAdd p) ![x, y]⟩
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (𝕎 R) :=
  ⟨fun x y => eval (wittSub p) ![x, y]⟩
/-
**WittVector.hasNatScalar** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：hasNatScalar : SMul Nat (𝕎 R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNatScalar : SMul ℕ (𝕎 R) :=
  ⟨fun n x => eval (wittNSMul p n) ![x]⟩
/-
**WittVector.hasIntScalar** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：hasIntScalar : SMul Int (𝕎 R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasIntScalar : SMul ℤ (𝕎 R) :=
  ⟨fun n x => eval (wittZSMul p n) ![x]⟩
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (𝕎 R) :=
  ⟨fun x y => eval (wittMul p) ![x, y]⟩
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (𝕎 R) :=
  ⟨fun x => eval (wittNeg p) ![x]⟩
/-
**WittVector.hasNatPow** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
形式化陈述：hasNatPow : Pow (𝕎 R) Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNatPow : Pow (𝕎 R) ℕ :=
  ⟨fun x n => eval (wittPow p n) ![x]⟩
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (𝕎 R) :=
  ⟨Nat.unaryCast⟩
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (𝕎 R) :=
  ⟨Int.castDef⟩

end RingOperations

section WittStructureSimplifications

@[simp]
/-
**WittVector.wittZero_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittZero_eq_zero (n : Nat) : wittZero p n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `MvPolynomial.aeval_zero'`：aeval_zero' (p : MvPolynomial σ R) : aeval (fu
n _ => 0 : σ -> S₁) p = algebraMap _ _ (constantCoeff p)
· 使用定理 `constantCoeff_xInTermsOfW`：constantCoeff_xInTermsOfW [hp : Fact p.Prime]
 [Invertible (p : R)] (n : Nat) : constantCoeff (xInTermsOfW p R n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem wittZero_eq_zero (n : ℕ) : wittZero p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittZero, wittStructureRat, bind₁, aeval_zero', constantCoeff_xInTermsOfW, map_zero,
    map_wittStructureInt]

@[simp]
/-
**WittVector.wittOne_zero_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittOne_zero_eq_one : wittOne p 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `xInTermsOfW_zero`：xInTermsOfW_zero [Invertible (p : R)] : xInTermsOfW p 
R 0 = X 0
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem wittOne_zero_eq_one : wittOne p 0 = 1 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittOne, wittStructureRat, xInTermsOfW_zero, map_one, bind₁_X_right,
    map_wittStructureInt]

@[simp]
/-
**WittVector.wittOne_pos_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittOne_pos_eq_zero (n : Nat) (hn : 0 < n) : wittOne p n = 0
参数：n : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `xInTermsOfW_eq`：xInTermsOfW_eq [Invertible (p : R)] {n : Nat} : xInTerms
OfW p R n = (X n - ∑ i in range n, C ((p : R) ^ i) * xInTermsOfW p R i ^ p ^ (n 
- i)…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `MvPolynomial.bind₁_C_right`：bind₁_C_right (f : σ -> MvPolynomial τ R) (x
) : bind₁ f (C x) = C x
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 47 条，此处仅展示前 30 条）
-/
theorem wittOne_pos_eq_zero (n : ℕ) (hn : 0 < n) : wittOne p n = 0 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittOne, wittStructureRat, map_zero, map_one, map_wittStructureInt]
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [xInTermsOfW_eq]
  simp only [map_mul, map_sub, map_sum, map_pow, bind₁_X_right,
    bind₁_C_right]
  rw [sub_mul, one_mul]
  rw [Finset.sum_eq_single 0]
  · simp only [one_mul, pow_zero]
    simp only [one_pow, one_mul, xInTermsOfW_zero, sub_self, bind₁_X_right]
  · intro i hin hi0
    rw [Finset.mem_range] at hin
    rw [IH _ hin (Nat.pos_of_ne_zero hi0), zero_pow (pow_ne_zero _ hp.1.ne_zero), mul_zero]
  · grind

@[simp]
/-
**WittVector.wittAdd_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittAdd_zero : wittAdd p 0 = X (0, 0) + X (1, 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `xInTermsOfW_zero`：xInTermsOfW_zero [Invertible (p : R)] : xInTermsOfW p 
R 0 = X 0
· 使用定理 `wittPolynomial_zero`：wittPolynomial_zero : wittPolynomial p R 0 = X 0
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem wittAdd_zero : wittAdd p 0 = X (0, 0) + X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittAdd, wittStructureRat, map_add, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]
/-
**WittVector.wittSub_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittSub_zero : wittSub p 0 = X (0, 0) - X (1, 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `xInTermsOfW_zero`：xInTermsOfW_zero [Invertible (p : R)] : xInTermsOfW p 
R 0 = X 0
· 使用定理 `wittPolynomial_zero`：wittPolynomial_zero : wittPolynomial p R 0 = X 0
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem wittSub_zero : wittSub p 0 = X (0, 0) - X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittSub, wittStructureRat, map_sub, rename_X, xInTermsOfW_zero, map_X,
    wittPolynomial_zero, bind₁_X_right, map_wittStructureInt]

@[simp]
/-
**WittVector.wittMul_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittMul_zero : wittMul p 0 = X (0, 0) * X (1, 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `xInTermsOfW_zero`：xInTermsOfW_zero [Invertible (p : R)] : xInTermsOfW p 
R 0 = X 0
· 使用定理 `wittPolynomial_zero`：wittPolynomial_zero : wittPolynomial p R 0 = X 0
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem wittMul_zero : wittMul p 0 = X (0, 0) * X (1, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittMul, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_mul, bind₁_X_right, map_wittStructureInt]

@[simp]
/-
**WittVector.wittNeg_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittNeg_zero : wittNeg p 0 = -X (0, 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.map_injective`：map_injective (hf : Function.Injective f) : 
Function.Injective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_wittStructureInt`：map_wittStructureInt (Φ : MvPolynomial idx Int) (n
 : Nat) : map (Int.castRingHom Rat) (wittStructureInt p Φ n) = wittStructureRat 
p (map (In…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPolynomial.bind₁_X_right`：bind₁_X_right (f : σ -> MvPolynomial τ R) (i
 : σ) : bind₁ f (X i) = f i
· 使用定理 `xInTermsOfW_zero`：xInTermsOfW_zero [Invertible (p : R)] : xInTermsOfW p 
R 0 = X 0
· 使用定理 `wittPolynomial_zero`：wittPolynomial_zero : wittPolynomial p R 0 = X 0
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem wittNeg_zero : wittNeg p 0 = -X (0, 0) := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [wittNeg, wittStructureRat, rename_X, xInTermsOfW_zero, map_X, wittPolynomial_zero,
    map_neg, bind₁_X_right, map_wittStructureInt]

@[simp]
/-
**WittVector.constantCoeff_wittAdd** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：constantCoeff_wittAdd (n : Nat) : constantCoeff (wittAdd p n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `constantCoeff_wittStructureInt`：constantCoeff_wittStructureInt (Φ : MvPo
lynomial idx Int) (h : constantCoeff Φ = 0) (n : Nat) : constantCoeff (wittStruc
tureInt p Φ n) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_wittAdd (n : ℕ) : constantCoeff (wittAdd p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [add_zero, map_add, constantCoeff_X]

@[simp]
/-
**WittVector.constantCoeff_wittSub** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：constantCoeff_wittSub (n : Nat) : constantCoeff (wittSub p n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `constantCoeff_wittStructureInt`：constantCoeff_wittStructureInt (Φ : MvPo
lynomial idx Int) (h : constantCoeff Φ = 0) (n : Nat) : constantCoeff (wittStruc
tureInt p Φ n) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_wittSub (n : ℕ) : constantCoeff (wittSub p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [sub_zero, map_sub, constantCoeff_X]

@[simp]
/-
**WittVector.constantCoeff_wittMul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：constantCoeff_wittMul (n : Nat) : constantCoeff (wittMul p n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `constantCoeff_wittStructureInt`：constantCoeff_wittStructureInt (Φ : MvPo
lynomial idx Int) (h : constantCoeff Φ = 0) (n : Nat) : constantCoeff (wittStruc
tureInt p Φ n) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_wittMul (n : ℕ) : constantCoeff (wittMul p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [mul_zero, map_mul, constantCoeff_X]

@[simp]
/-
**WittVector.constantCoeff_wittNeg** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：constantCoeff_wittNeg (n : Nat) : constantCoeff (wittNeg p n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `constantCoeff_wittStructureInt`：constantCoeff_wittStructureInt (Φ : MvPo
lynomial idx Int) (h : constantCoeff Φ = 0) (n : Nat) : constantCoeff (wittStruc
tureInt p Φ n) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_wittNeg (n : ℕ) : constantCoeff (wittNeg p n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [neg_zero, map_neg, constantCoeff_X]

@[simp]
/-
**WittVector.constantCoeff_wittNSMul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：constantCoeff_wittNSMul (m : Nat) (n : Nat) : constantCoeff (wittNSMul p m
 n) = 0
参数：m : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `constantCoeff_wittStructureInt`：constantCoeff_wittStructureInt (Φ : MvPo
lynomial idx Int) (h : constantCoeff Φ = 0) (n : Nat) : constantCoeff (wittStruc
tureInt p Φ n) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_wittNSMul (m : ℕ) (n : ℕ) : constantCoeff (wittNSMul p m n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_nsmul, constantCoeff_X]

@[simp]
/-
**WittVector.constantCoeff_wittZSMul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：constantCoeff_wittZSMul (z : Int) (n : Nat) : constantCoeff (wittZSMul p z
 n) = 0
参数：z : Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `constantCoeff_wittStructureInt`：constantCoeff_wittStructureInt (Φ : MvPo
lynomial idx Int) (h : constantCoeff Φ = 0) (n : Nat) : constantCoeff (wittStruc
tureInt p Φ n) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_wittZSMul (z : ℤ) (n : ℕ) : constantCoeff (wittZSMul p z n) = 0 := by
  apply constantCoeff_wittStructureInt p _ _ n
  simp only [smul_zero, map_zsmul, constantCoeff_X]

end WittStructureSimplifications

section Coeff

variable (R)

@[simp]
/-
**WittVector.zero_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.wittZero_eq_zero`：wittZero_eq_zero (n : Nat) : wittZero p n =
 0
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
-/
theorem zero_coeff (n : ℕ) : (0 : 𝕎 R).coeff n = 0 :=
  show (aeval _ (wittZero p n) : R) = 0 by simp only [wittZero_eq_zero, map_zero]

@[simp]
/-
**WittVector.one_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：one_coeff_zero : (1 : 𝕎 R).coeff 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.wittOne_zero_eq_one`：wittOne_zero_eq_one : wittOne p 0 = 1
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_coeff_zero : (1 : 𝕎 R).coeff 0 = 1 :=
  show (aeval _ (wittOne p 0) : R) = 1 by simp only [wittOne_zero_eq_one, map_one]

@[simp]
/-
**WittVector.one_coeff_eq_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：one_coeff_eq_of_pos (n : Nat) (hn : 0 < n) : coeff (1 : 𝕎 R) n = 0
参数：n : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.wittOne_pos_eq_zero`：wittOne_pos_eq_zero (n : Nat) (hn : 0 < 
n) : wittOne p n = 0
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
-/
theorem one_coeff_eq_of_pos (n : ℕ) (hn : 0 < n) : coeff (1 : 𝕎 R) n = 0 :=
  show (aeval _ (wittOne p n) : R) = 0 by simp only [hn, wittOne_pos_eq_zero, map_zero]

variable {p R}

@[simp]
/-
**WittVector.v2_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：v2_coeff {p' R'} (x y : WittVector p' R') (i : Fin 2) : (![x, y] i).coeff 
= ![x.coeff, y.coeff] i
参数：x y : WittVector p' R'；i : Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem v2_coeff {p' R'} (x y : WittVector p' R') (i : Fin 2) :
    (![x, y] i).coeff = ![x.coeff, y.coeff] i := by fin_cases i <;> simp
/-
**WittVector.add_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：add_coeff (x y : 𝕎 R) (n : Nat) : (x + y).coeff n = peval (wittAdd p n) ![
x.coeff, y.coeff]
参数：x y : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WittVector.v2_coeff`：v2_coeff {p' R'} (x y : WittVector p' R') (i : Fin 
2) : (![x, y] i).coeff = ![x.coeff, y.coeff] i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_coeff (x y : 𝕎 R) (n : ℕ) :
    (x + y).coeff n = peval (wittAdd p n) ![x.coeff, y.coeff] := by
  simp [(· + ·), Add.add, eval]
/-
**WittVector.sub_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：sub_coeff (x y : 𝕎 R) (n : Nat) : (x - y).coeff n = peval (wittSub p n) ![
x.coeff, y.coeff]
参数：x y : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WittVector.v2_coeff`：v2_coeff {p' R'} (x y : WittVector p' R') (i : Fin 
2) : (![x, y] i).coeff = ![x.coeff, y.coeff] i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_coeff (x y : 𝕎 R) (n : ℕ) :
    (x - y).coeff n = peval (wittSub p n) ![x.coeff, y.coeff] := by
  simp [(· - ·), Sub.sub, eval]
/-
**WittVector.mul_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_coeff (x y : 𝕎 R) (n : Nat) : (x * y).coeff n = peval (wittMul p n) ![
x.coeff, y.coeff]
参数：x y : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WittVector.v2_coeff`：v2_coeff {p' R'} (x y : WittVector p' R') (i : Fin 
2) : (![x, y] i).coeff = ![x.coeff, y.coeff] i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_coeff (x y : 𝕎 R) (n : ℕ) :
    (x * y).coeff n = peval (wittMul p n) ![x.coeff, y.coeff] := by
  simp [(· * ·), Mul.mul, eval]
/-
**WittVector.neg_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：neg_coeff (x : 𝕎 R) (n : Nat) : (-x).coeff n = peval (wittNeg p n) ![x.coe
ff]
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Matrix.cons_fin_one`：cons_fin_one (x : α) (u : Fin 0 -> α) : vecCons x u
 = fun _ => x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_coeff (x : 𝕎 R) (n : ℕ) : (-x).coeff n = peval (wittNeg p n) ![x.coeff] := by
  simp [Neg.neg, eval, Matrix.cons_fin_one]
/-
**WittVector.nsmul_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：nsmul_coeff (m : Nat) (x : 𝕎 R) (n : Nat) : (m • x).coeff n = peval (wittN
SMul p m n) ![x.coeff]
参数：m : Nat；x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Matrix.cons_fin_one`：cons_fin_one (x : α) (u : Fin 0 -> α) : vecCons x u
 = fun _ => x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nsmul_coeff (m : ℕ) (x : 𝕎 R) (n : ℕ) :
    (m • x).coeff n = peval (wittNSMul p m n) ![x.coeff] := by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]
/-
**WittVector.zsmul_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：zsmul_coeff (m : Int) (x : 𝕎 R) (n : Nat) : (m • x).coeff n = peval (wittZ
SMul p m n) ![x.coeff]
参数：m : Int；x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Matrix.cons_fin_one`：cons_fin_one (x : α) (u : Fin 0 -> α) : vecCons x u
 = fun _ => x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zsmul_coeff (m : ℤ) (x : 𝕎 R) (n : ℕ) :
    (m • x).coeff n = peval (wittZSMul p m n) ![x.coeff] := by
  simp [(· • ·), SMul.smul, eval, Matrix.cons_fin_one]
/-
**WittVector.pow_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：pow_coeff (m : Nat) (x : 𝕎 R) (n : Nat) : (x ^ m).coeff n = peval (wittPow
 p m n) ![x.coeff]
参数：m : Nat；x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Matrix.cons_fin_one`：cons_fin_one (x : α) (u : Fin 0 -> α) : vecCons x u
 = fun _ => x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_coeff (m : ℕ) (x : 𝕎 R) (n : ℕ) :
    (x ^ m).coeff n = peval (wittPow p m n) ![x.coeff] := by
  simp [(· ^ ·), Pow.pow, eval, Matrix.cons_fin_one]
/-
**WittVector.add_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：add_coeff_zero (x y : 𝕎 R) : (x + y).coeff 0 = x.coeff 0 + y.coeff 0
参数：x y : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.add_coeff`：add_coeff (x y : 𝕎 R) (n : Nat) : (x + y).coeff n 
= peval (wittAdd p n) ![x.coeff, y.coeff]
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WittVector.wittAdd_zero`：wittAdd_zero : wittAdd p 0 = X (0, 0) + X (1, 0
)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_coeff_zero (x y : 𝕎 R) : (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  simp [add_coeff, peval, Function.uncurry]
/-
**WittVector.mul_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mul_coeff_zero (x y : 𝕎 R) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0
参数：x y : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.mul_coeff`：mul_coeff (x y : 𝕎 R) (n : Nat) : (x * y).coeff n 
= peval (wittMul p n) ![x.coeff, y.coeff]
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WittVector.wittMul_zero`：wittMul_zero : wittMul p 0 = X (0, 0) * X (1, 0
)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_coeff_zero (x y : 𝕎 R) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  simp [mul_coeff, peval, Function.uncurry]

end Coeff

/-
**WittVector.wittAdd_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittAdd_vars (n : Nat) : (wittAdd p n).vars subseteq Finset.univ ×ˢ Finset
.range (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wittStructureInt_vars`：wittStructureInt_vars [Fintype idx] (Φ : MvPolyno
mial idx Int) (n : Nat) : (wittStructureInt p Φ n).vars subseteq Finset.univ ×ˢ 
Finset.rang…
-/
theorem wittAdd_vars (n : ℕ) : (wittAdd p n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _
/-
**WittVector.wittSub_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittSub_vars (n : Nat) : (wittSub p n).vars subseteq Finset.univ ×ˢ Finset
.range (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wittStructureInt_vars`：wittStructureInt_vars [Fintype idx] (Φ : MvPolyno
mial idx Int) (n : Nat) : (wittStructureInt p Φ n).vars subseteq Finset.univ ×ˢ 
Finset.rang…
-/
theorem wittSub_vars (n : ℕ) : (wittSub p n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _
/-
**WittVector.wittMul_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittMul_vars (n : Nat) : (wittMul p n).vars subseteq Finset.univ ×ˢ Finset
.range (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wittStructureInt_vars`：wittStructureInt_vars [Fintype idx] (Φ : MvPolyno
mial idx Int) (n : Nat) : (wittStructureInt p Φ n).vars subseteq Finset.univ ×ˢ 
Finset.rang…
-/
theorem wittMul_vars (n : ℕ) : (wittMul p n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _
/-
**WittVector.wittNeg_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittNeg_vars (n : Nat) : (wittNeg p n).vars subseteq Finset.univ ×ˢ Finset
.range (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wittStructureInt_vars`：wittStructureInt_vars [Fintype idx] (Φ : MvPolyno
mial idx Int) (n : Nat) : (wittStructureInt p Φ n).vars subseteq Finset.univ ×ˢ 
Finset.rang…
-/
theorem wittNeg_vars (n : ℕ) : (wittNeg p n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _
/-
**WittVector.wittNSMul_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittNSMul_vars (m : Nat) (n : Nat) : (wittNSMul p m n).vars subseteq Finse
t.univ ×ˢ Finset.range (n + 1)
参数：m : Nat；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wittStructureInt_vars`：wittStructureInt_vars [Fintype idx] (Φ : MvPolyno
mial idx Int) (n : Nat) : (wittStructureInt p Φ n).vars subseteq Finset.univ ×ˢ 
Finset.rang…
-/
theorem wittNSMul_vars (m : ℕ) (n : ℕ) :
    (wittNSMul p m n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _
/-
**WittVector.wittZSMul_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittZSMul_vars (m : Int) (n : Nat) : (wittZSMul p m n).vars subseteq Finse
t.univ ×ˢ Finset.range (n + 1)
参数：m : Int；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wittStructureInt_vars`：wittStructureInt_vars [Fintype idx] (Φ : MvPolyno
mial idx Int) (n : Nat) : (wittStructureInt p Φ n).vars subseteq Finset.univ ×ˢ 
Finset.rang…
-/
theorem wittZSMul_vars (m : ℤ) (n : ℕ) :
    (wittZSMul p m n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _
/-
**WittVector.wittPow_vars** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：wittPow_vars (m : Nat) (n : Nat) : (wittPow p m n).vars subseteq Finset.un
iv ×ˢ Finset.range (n + 1)
参数：m : Nat；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `wittStructureInt_vars`：wittStructureInt_vars [Fintype idx] (Φ : MvPolyno
mial idx Int) (n : Nat) : (wittStructureInt p Φ n).vars subseteq Finset.univ ×ˢ 
Finset.rang…
-/
theorem wittPow_vars (m : ℕ) (n : ℕ) : (wittPow p m n).vars ⊆ Finset.univ ×ˢ Finset.range (n + 1) :=
  wittStructureInt_vars _ _ _

end WittVector

