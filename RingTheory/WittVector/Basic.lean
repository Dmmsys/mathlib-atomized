/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.MvPolynomial.Counit
public import Mathlib.Algebra.MvPolynomial.Invertible
public import Mathlib.RingTheory.WittVector.Defs

/-!
# Witt vectors

This file verifies that the ring operations on `WittVector p R`
satisfy the axioms of a commutative ring.

## Main definitions

* `WittVector.map`: lifts a ring homomorphism `R →+* S` to a ring homomorphism `𝕎 R →+* 𝕎 S`.
* `WittVector.ghostComponent n x`: evaluates the `n`th Witt polynomial
  on the first `n` coefficients of `x`, producing a value in `R`.
  This is a ring homomorphism.
* `WittVector.ghostMap`: a ring homomorphism `𝕎 R →+* (ℕ → R)`, obtained by packaging
  all the ghost components together.
  If `p` is invertible in `R`, then the ghost map is an equivalence,
  which we use to define the ring operations on `𝕎 R`.
* `WittVector.CommRing`: the ring structure induced by the ghost components.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## Implementation details

As we prove that the ghost components respect the ring operations, we face a number of repetitive
proofs. To avoid duplicating code we factor these proofs into a custom tactic, only slightly more
powerful than a tactic macro. This tactic is not particularly useful outside of its applications
in this file.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/

@[expose] public section


noncomputable section

open MvPolynomial Function

variable {p : Nat} {R S : Type*} [CommRing R] [CommRing S]
variable {α : Type*} {β : Type*}

local notation "𝕎" => WittVector p
local notation "W_" => wittPolynomial p

-- type as `\bbW`
open scoped Witt

namespace WittVector

/--
Definition of `mapFun` / `mapFun` 的定义

English:
definition mapFun
  signature: (f : α -> β)
  body: fun x => mk _ (f ∘ x.coeff)

中文:
定义 mapFun
  签名: (f : α -> β)
  定义体: fun x => mk _ (f ∘ x.coeff)

Depends on / 依赖: x.coeff
-/
def mapFun (f : α -> β) : 𝕎 α -> 𝕎 β := fun x => mk _ (f ∘ x.coeff)

namespace mapFun

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (f : α -> β) (hf : Injective f)
  statement: Injective (mapFun f : 𝕎 α -> 𝕎 β)
  proof: fun _ _ h => ext fun n => hf (congr_arg (fun x => coeff x n) h :)

中文:
定理 injective
  条件: (f : α -> β) (hf : 单射 f)
  结论: 单射 (mapFun f : 𝕎 α -> 𝕎 β)
  证明: fun _ _ h => ext fun n => hf (congr_arg (fun x => coeff x n) h :)

Depends on / 依赖: congr_arg
-/
theorem injective (f : α -> β) (hf : Injective f) : Injective (mapFun f : 𝕎 α -> 𝕎 β) :=
  fun _ _ h => ext fun n => hf (congr_arg (fun x => coeff x n) h :)

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (f : α -> β) (hf : Surjective f)
  statement: Surjective (mapFun f : 𝕎 α -> 𝕎 β)
  proof: fun x =>
⟨mk _ fun n => Classical.choose hf x.coeff n,
    by ext n; simp only [mapFun, coeff_mk, comp_apply, Classical.choose_spec (hf (x.coeff n))]⟩

中文:
定理 surjective
  条件: (f : α -> β) (hf : 满射 f)
  结论: 满射 (mapFun f : 𝕎 α -> 𝕎 β)
  证明: fun x =>
⟨mk _ fun n => Classical.choose hf x.coeff n,
    by ext n; simp only [mapFun, coeff_mk, comp_apply, Classical.choose_spec (hf (x.coeff n))]⟩
-/
theorem surjective (f : α -> β) (hf : Surjective f) : Surjective (mapFun f : 𝕎 α -> 𝕎 β) := fun x =>
⟨mk _ fun n => Classical.choose hf x.coeff n,
    by ext n; simp only [mapFun, coeff_mk, comp_apply, Classical.choose_spec (hf (x.coeff n))]⟩

/-- Auxiliary tactic for showing that `mapFun` respects the ring operations. -/
macro "map_fun_tac" : tactic => `(tactic| (
  -- TODO: the Lean 3 version of this tactic was more functional
  ext n
  simp only [mapFun, mk, comp_apply, zero_coeff, map_zero,
    -- the lemmas on the next line do not have the `simp` tag in mathlib4
    add_coeff, sub_coeff, mul_coeff, neg_coeff, nsmul_coeff, zsmul_coeff, pow_coeff,
    peval, map_aeval, algebraMap_int_eq, coe_eval₂Hom] <;>
  try { cases n <;> simp <;> done } <;> -- this line solves `one`
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl <;>
  ext ⟨i, k⟩ <;>
    fin_cases i <;> rfl))

variable [Fact p.Prime]
-- Porting note: using `(x y : 𝕎 R)` instead of `(x y : WittVector p R)` produced sorries.
variable (f : R ->+* S) (x y : WittVector p R)

-- and until `pow`.
-- We do not tag these lemmas as `@[simp]` because they will be bundled in `map` later on.
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: mapFun f (0 : 𝕎 R) = 0
  proof: by map_fun_tac

中文:
定理 zero
  结论: mapFun f (0 : 𝕎 R) = 0
  证明: by map_fun_tac

Depends on / 依赖: map_fun_tac
-/
theorem zero : mapFun f (0 : 𝕎 R) = 0 := by map_fun_tac

/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: mapFun f (1 : 𝕎 R) = 1
  proof: by map_fun_tac

中文:
定理 one
  结论: mapFun f (1 : 𝕎 R) = 1
  证明: by map_fun_tac

Depends on / 依赖: map_fun_tac
-/
theorem one : mapFun f (1 : 𝕎 R) = 1 := by map_fun_tac

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: mapFun f (x + y) = mapFun f x + mapFun f y
  proof: by map_fun_tac

中文:
定理 add
  结论: mapFun f (x + y) = mapFun f x + mapFun f y
  证明: by map_fun_tac

Depends on / 依赖: map_fun_tac
-/
theorem add : mapFun f (x + y) = mapFun f x + mapFun f y := by map_fun_tac

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: mapFun f (x - y) = mapFun f x - mapFun f y
  proof: by map_fun_tac

中文:
定理 sub
  结论: mapFun f (x - y) = mapFun f x - mapFun f y
  证明: by map_fun_tac

Depends on / 依赖: map_fun_tac
-/
theorem sub : mapFun f (x - y) = mapFun f x - mapFun f y := by map_fun_tac

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: mapFun f (x * y) = mapFun f x * mapFun f y
  proof: by map_fun_tac

中文:
定理 mul
  结论: mapFun f (x * y) = mapFun f x * mapFun f y
  证明: by map_fun_tac

Depends on / 依赖: map_fun_tac
-/
theorem mul : mapFun f (x * y) = mapFun f x * mapFun f y := by map_fun_tac

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  statement: mapFun f (-x) = -mapFun f x
  proof: by map_fun_tac

中文:
定理 neg
  结论: mapFun f (-x) = -mapFun f x
  证明: by map_fun_tac

Depends on / 依赖: map_fun_tac
-/
theorem neg : mapFun f (-x) = -mapFun f x := by map_fun_tac

/--
theorem `nsmul` / 定理 `nsmul`

English:
theorem nsmul
  given: (n : Nat) (x : WittVector p R)
  statement: mapFun f (n • x) = n • mapFun f x
  proof: by map_fun_tac

中文:
定理 nsmul
  条件: (n : 自然数) (x : Witt向量 p R)
  结论: mapFun f (n • x) = n • mapFun f x
  证明: by map_fun_tac

Depends on / 依赖: map_fun_tac
-/
theorem nsmul (n : Nat) (x : WittVector p R) : mapFun f (n • x) = n • mapFun f x := by map_fun_tac

/--
theorem `zsmul` / 定理 `zsmul`

English:
theorem zsmul
  given: (z : Int) (x : WittVector p R)
  statement: mapFun f (z • x) = z • mapFun f x
  proof: by map_fun_tac

中文:
定理 zsmul
  条件: (z : 整数) (x : Witt向量 p R)
  结论: mapFun f (z • x) = z • mapFun f x
  证明: by map_fun_tac

Depends on / 依赖: map_fun_tac
-/
theorem zsmul (z : Int) (x : WittVector p R) : mapFun f (z • x) = z • mapFun f x := by map_fun_tac

/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: (n : Nat)
  statement: mapFun f (x ^ n) = mapFun f x ^ n
  proof: by map_fun_tac

中文:
定理 pow
  条件: (n : 自然数)
  结论: mapFun f (x ^ n) = mapFun f x ^ n
  证明: by map_fun_tac

Depends on / 依赖: map_fun_tac
-/
theorem pow (n : Nat) : mapFun f (x ^ n) = mapFun f x ^ n := by map_fun_tac

/--
theorem `natCast` / 定理 `natCast`

English:
theorem natCast
  given: (n : Nat)
  statement: mapFun f (n : 𝕎 R) = n
  proof: show mapFun f n.unaryCast = (n : WittVector p S) by
    induction n <;> simp [*, Nat.unaryCast, add, one, zero] <;> rfl

中文:
定理 natCast
  条件: (n : 自然数)
  结论: mapFun f (n : 𝕎 R) = n
  证明: show mapFun f n.unaryCast = (n : WittVector p S) by
    induction n <;> simp [*, Nat.unaryCast, add, one, zero] <;> rfl

Depends on / 依赖: Nat.unaryCast, WittVector, mapFun, n.unaryCast, unaryCast
-/
theorem natCast (n : Nat) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.unaryCast = (n : WittVector p S) by
    induction n <;> simp [*, Nat.unaryCast, add, one, zero] <;> rfl

/--
theorem `intCast` / 定理 `intCast`

English:
theorem intCast
  given: (n : Int)
  statement: mapFun f (n : 𝕎 R) = n
  proof: show mapFun f n.castDef = (n : WittVector p S) by
    cases n <;> simp [*, Int.castDef, neg, natCast] <;> rfl

中文:
定理 intCast
  条件: (n : 整数)
  结论: mapFun f (n : 𝕎 R) = n
  证明: show mapFun f n.castDef = (n : WittVector p S) by
    cases n <;> simp [*, Int.castDef, neg, natCast] <;> rfl

Depends on / 依赖: Int.castDef, WittVector, castDef, mapFun, n.castDef, natCast
-/
theorem intCast (n : Int) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.castDef = (n : WittVector p S) by
    cases n <;> simp [*, Int.castDef, neg, natCast] <;> rfl

end mapFun

end WittVector

namespace WittVector

set_option backward.privateInPublic true in
/--
Definition of `ghostFun` / `ghostFun` 的定义

English:
definition ghostFun
  signature: : 𝕎 R -> Nat -> R
  body: fun x n => aeval x.coeff (W_ Int n)

中文:
定义 ghostFun
  签名: : 𝕎 R -> 自然数 -> R
  定义体: fun x n => aeval x.coeff (W_ Int n)
-/
private def ghostFun : 𝕎 R -> Nat -> R := fun x n => aeval x.coeff (W_ Int n)

section Tactic
open Lean Elab Tactic

/-- An auxiliary tactic for proving that `ghostFun` respects the ring operations. -/
elab "ghost_fun_tac " φ:term ", " fn:term : tactic => do
  evalTactic (← `(tactic| (
  ext n
have := congr_fun (congr_arg (@peval R _ _) (wittStructureInt_prop p $φ n)) fn
  simp only [wittZero, OfNat.ofNat, Zero.zero, wittOne, One.one,
    HAdd.hAdd, Add.add, HSub.hSub, Sub.sub, Neg.neg, HMul.hMul, Mul.mul, HPow.hPow, Pow.pow,
    wittNSMul, wittZSMul, HSMul.hSMul, SMul.smul]
  simpa +unfoldPartialApp [WittVector.ghostFun, aeval_rename, aeval_bind₁,
    comp, uncurry, peval, eval] using! this
  )))

end Tactic

section GhostFun

-- The following lemmas are not `@[simp]` because they will be bundled in `ghostMap` later on.

@[local simp]
/--
theorem `matrix_vecEmpty_coeff` / 定理 `matrix_vecEmpty_coeff`

English:
theorem matrix_vecEmpty_coeff
  given: {R} (i j)
  proof: by
  rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩

中文:
定理 matrix_vecEmpty_coeff
  条件: {R} (i j)
  证明: by
  rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩

Depends on / 依赖: i_val
-/
theorem matrix_vecEmpty_coeff {R} (i j) :
    @coeff p R (Matrix.vecEmpty i) j = (Matrix.vecEmpty i : Nat -> R) j := by
  rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩

variable [Fact p.Prime]
variable (x y : WittVector p R)

set_option backward.privateInPublic true in
/--
theorem `ghostFun_zero` / 定理 `ghostFun_zero`

English:
theorem ghostFun_zero
  statement: ghostFun (0 : 𝕎 R) = 0
  proof: by
  ghost_fun_tac 0, ![]

中文:
定理 ghostFun_zero
  结论: ghostFun (0 : 𝕎 R) = 0
  证明: by
  ghost_fun_tac 0, ![]
-/
private theorem ghostFun_zero : ghostFun (0 : 𝕎 R) = 0 := by
  ghost_fun_tac 0, ![]

set_option backward.privateInPublic true in
/--
theorem `ghostFun_one` / 定理 `ghostFun_one`

English:
theorem ghostFun_one
  statement: ghostFun (1 : 𝕎 R) = 1
  proof: by
  ghost_fun_tac 1, ![]

中文:
定理 ghostFun_one
  结论: ghostFun (1 : 𝕎 R) = 1
  证明: by
  ghost_fun_tac 1, ![]
-/
private theorem ghostFun_one : ghostFun (1 : 𝕎 R) = 1 := by
  ghost_fun_tac 1, ![]

set_option backward.privateInPublic true in
/--
theorem `ghostFun_add` / 定理 `ghostFun_add`

English:
theorem ghostFun_add
  statement: ghostFun (x + y) = ghostFun x + ghostFun y
  proof: by
  ghost_fun_tac X 0 + X 1, ![x.coeff, y.coeff]

中文:
定理 ghostFun_add
  结论: ghostFun (x + y) = ghostFun x + ghostFun y
  证明: by
  ghost_fun_tac X 0 + X 1, ![x.coeff, y.coeff]
-/
private theorem ghostFun_add : ghostFun (x + y) = ghostFun x + ghostFun y := by
  ghost_fun_tac X 0 + X 1, ![x.coeff, y.coeff]

/--
theorem `ghostFun_natCast` / 定理 `ghostFun_natCast`

English:
theorem ghostFun_natCast
  given: (i : Nat)
  statement: ghostFun (i : 𝕎 R) = i
  proof: show ghostFun i.unaryCast = _ by
    induction i <;> simp [*, Nat.unaryCast, ghostFun_zero, ghostFun_one, ghostFun_add]

中文:
定理 ghostFun_natCast
  条件: (i : 自然数)
  结论: ghostFun (i : 𝕎 R) = i
  证明: show ghostFun i.unaryCast = _ by
    induction i <;> simp [*, Nat.unaryCast, ghostFun_zero, ghostFun_one, ghostFun_add]
-/
private theorem ghostFun_natCast (i : Nat) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.unaryCast = _ by
    induction i <;> simp [*, Nat.unaryCast, ghostFun_zero, ghostFun_one, ghostFun_add]

/--
theorem `ghostFun_sub` / 定理 `ghostFun_sub`

English:
theorem ghostFun_sub
  statement: ghostFun (x - y) = ghostFun x - ghostFun y
  proof: by
  ghost_fun_tac X 0 - X 1, ![x.coeff, y.coeff]

中文:
定理 ghostFun_sub
  结论: ghostFun (x - y) = ghostFun x - ghostFun y
  证明: by
  ghost_fun_tac X 0 - X 1, ![x.coeff, y.coeff]
-/
private theorem ghostFun_sub : ghostFun (x - y) = ghostFun x - ghostFun y := by
  ghost_fun_tac X 0 - X 1, ![x.coeff, y.coeff]

set_option backward.privateInPublic true in
/--
theorem `ghostFun_mul` / 定理 `ghostFun_mul`

English:
theorem ghostFun_mul
  statement: ghostFun (x * y) = ghostFun x * ghostFun y
  proof: by
  ghost_fun_tac X 0 * X 1, ![x.coeff, y.coeff]

中文:
定理 ghostFun_mul
  结论: ghostFun (x * y) = ghostFun x * ghostFun y
  证明: by
  ghost_fun_tac X 0 * X 1, ![x.coeff, y.coeff]
-/
private theorem ghostFun_mul : ghostFun (x * y) = ghostFun x * ghostFun y := by
  ghost_fun_tac X 0 * X 1, ![x.coeff, y.coeff]

/--
theorem `ghostFun_neg` / 定理 `ghostFun_neg`

English:
theorem ghostFun_neg
  statement: ghostFun (-x) = -ghostFun x
  proof: by ghost_fun_tac -X 0, ![x.coeff]

中文:
定理 ghostFun_neg
  结论: ghostFun (-x) = -ghostFun x
  证明: by ghost_fun_tac -X 0, ![x.coeff]
-/
private theorem ghostFun_neg : ghostFun (-x) = -ghostFun x := by ghost_fun_tac -X 0, ![x.coeff]

/--
theorem `ghostFun_intCast` / 定理 `ghostFun_intCast`

English:
theorem ghostFun_intCast
  given: (i : Int)
  statement: ghostFun (i : 𝕎 R) = i
  proof: show ghostFun i.castDef = _ by
    cases i <;> simp [*, Int.castDef, ghostFun_natCast, ghostFun_neg]

中文:
定理 ghostFun_intCast
  条件: (i : 整数)
  结论: ghostFun (i : 𝕎 R) = i
  证明: show ghostFun i.castDef = _ by
    cases i <;> simp [*, Int.castDef, ghostFun_natCast, ghostFun_neg]
-/
private theorem ghostFun_intCast (i : Int) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.castDef = _ by
    cases i <;> simp [*, Int.castDef, ghostFun_natCast, ghostFun_neg]

/--
lemma `ghostFun_nsmul` / 引理 `ghostFun_nsmul`

English:
lemma ghostFun_nsmul
  given: (m : Nat) (x : WittVector p R)
  statement: ghostFun (m • x) = m • ghostFun x
  proof: by
  ghost_fun_tac m • (X 0), ![x.coeff]

中文:
引理 ghostFun_nsmul
  条件: (m : 自然数) (x : Witt向量 p R)
  结论: ghostFun (m • x) = m • ghostFun x
  证明: by
  ghost_fun_tac m • (X 0), ![x.coeff]
-/
private lemma ghostFun_nsmul (m : Nat) (x : WittVector p R) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • (X 0), ![x.coeff]

/--
lemma `ghostFun_zsmul` / 引理 `ghostFun_zsmul`

English:
lemma ghostFun_zsmul
  given: (m : Int) (x : WittVector p R)
  statement: ghostFun (m • x) = m • ghostFun x
  proof: by
  ghost_fun_tac m • (X 0), ![x.coeff]

中文:
引理 ghostFun_zsmul
  条件: (m : 整数) (x : Witt向量 p R)
  结论: ghostFun (m • x) = m • ghostFun x
  证明: by
  ghost_fun_tac m • (X 0), ![x.coeff]
-/
private lemma ghostFun_zsmul (m : Int) (x : WittVector p R) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • (X 0), ![x.coeff]

/--
theorem `ghostFun_pow` / 定理 `ghostFun_pow`

English:
theorem ghostFun_pow
  given: (m : Nat)
  statement: ghostFun (x ^ m) = ghostFun x ^ m
  proof: by
  ghost_fun_tac X 0 ^ m, ![x.coeff]

中文:
定理 ghostFun_pow
  条件: (m : 自然数)
  结论: ghostFun (x ^ m) = ghostFun x ^ m
  证明: by
  ghost_fun_tac X 0 ^ m, ![x.coeff]
-/
private theorem ghostFun_pow (m : Nat) : ghostFun (x ^ m) = ghostFun x ^ m := by
  ghost_fun_tac X 0 ^ m, ![x.coeff]

end GhostFun

variable (p) (R)

set_option backward.privateInPublic true in
/--
Definition of `ghostEquiv'` / `ghostEquiv'` 的定义

English:
definition ghostEquiv'
  signature: [Invertible (p : R)]
  body: ghostFun
  invFun x := mk p fun n => aeval x (xInTermsOfW p R n)
  left_inv := by
    intro x
    ext n
    have := bind₁_wittPolynomial_xInTermsOfW p R n
    apply_fun aeval x.coeff at this
    simpa +unfoldPartialApp only [aeval_bind₁, aeval_X, ghostFun,
      aeval_wittPolynomial]
  right_inv := 

中文:
定义 ghostEquiv'
  签名: [可逆 (p : R)]
  定义体: ghostFun
  invFun x := mk p fun n => aeval x (xInTermsOfW p R n)
  left_inv := by
    intro x
    ext n
    have := bind₁_wittPolynomial_xInTermsOfW p R n
    apply_fun aeval x.coeff at this
    simpa +unfoldPartialApp only [aeval_bind₁, aeval_X, ghostFun,
      aeval_wittPolynomial]
  right_inv := 
-/
private def ghostEquiv' [Invertible (p : R)] : 𝕎 R ≃ (Nat -> R) where
  toFun := ghostFun
  invFun x := mk p fun n => aeval x (xInTermsOfW p R n)
  left_inv := by
    intro x
    ext n
    have := bind₁_wittPolynomial_xInTermsOfW p R n
    apply_fun aeval x.coeff at this
    simpa +unfoldPartialApp only [aeval_bind₁, aeval_X, ghostFun,
      aeval_wittPolynomial]
  right_inv := by
    intro x
    ext n
    have := bind₁_xInTermsOfW_wittPolynomial p R n
    apply_fun aeval x at this
    simpa only [aeval_bind₁, aeval_X, ghostFun, aeval_wittPolynomial]

variable [Fact p.Prime]

private local instance comm_ring_aux₁ : CommRing (𝕎 (MvPolynomial R Rat)) :=
  (ghostEquiv' p (MvPolynomial R Rat)).injective.commRing ghostFun ghostFun_zero ghostFun_one
    ghostFun_add ghostFun_mul ghostFun_neg ghostFun_sub ghostFun_nsmul ghostFun_zsmul
    ghostFun_pow ghostFun_natCast ghostFun_intCast

set_option backward.privateInPublic true in
private local instance comm_ring_aux₂ : CommRing (𝕎 (MvPolynomial R Int)) :=
  (mapFun.injective _ <| map_injective (Int.castRingHom Rat) Int.cast_injective).commRing _
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.natCast _) (mapFun.intCast _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (𝕎 R)
  body: (mapFun.surjective _ <| counit_surjective _).commRing (mapFun <| MvPolynomial.counit _)
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.natCast _) (mapFun.intCast _)

中文:
实例 :
  签名: 交换环 (𝕎 R)
  定义体: (mapFun.surjective _ <| counit_surjective _).commRing (mapFun <| MvPolynomial.counit _)
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.natCast _) (mapFun.intCast _)

Depends on / 依赖: MvPolynomial, MvPolynomial.counit, commRing, counit, counit_surjective, intCast, mapFun, mapFun.add, mapFun.intCast, mapFun.mul, mapFun.natCast, mapFun.neg, mapFun.nsmul, mapFun.one, mapFun.pow, mapFun.sub, mapFun.surjective, mapFun.zero, mapFun.zsmul, natCast
-/
instance : CommRing (𝕎 R) :=
  (mapFun.surjective _ <| counit_surjective _).commRing (mapFun <| MvPolynomial.counit _)
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.natCast _) (mapFun.intCast _)

variable {p R}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S)
  body: mapFun f
  map_zero' := mapFun.zero f
  map_one' := mapFun.one f
  map_add' := mapFun.add f
  map_mul' := mapFun.mul f

中文:
定义 map
  签名: (f : R ->+* S)
  定义体: mapFun f
  map_zero' := mapFun.zero f
  map_one' := mapFun.one f
  map_add' := mapFun.add f
  map_mul' := mapFun.mul f

Depends on / 依赖: mapFun
-/
noncomputable def map (f : R ->+* S) : 𝕎 R ->+* 𝕎 S where
  toFun := mapFun f
  map_zero' := mapFun.zero f
  map_one' := mapFun.one f
  map_add' := mapFun.add f
  map_mul' := mapFun.mul f

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (f : R ->+* S) (hf : Injective f)
  statement: Injective (map f : 𝕎 R -> 𝕎 S)
  proof: mapFun.injective f hf

中文:
定理 map_injective
  条件: (f : R ->+* S) (hf : 单射 f)
  结论: 单射 (map f : 𝕎 R -> 𝕎 S)
  证明: mapFun.injective f hf

Depends on / 依赖: injective, mapFun, mapFun.injective
-/
theorem map_injective (f : R ->+* S) (hf : Injective f) : Injective (map f : 𝕎 R -> 𝕎 S) :=
  mapFun.injective f hf

/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: (f : R ->+* S) (hf : Surjective f)
  statement: Surjective (map f : 𝕎 R -> 𝕎 S)
  proof: mapFun.surjective f hf

@[simp]

中文:
定理 map_surjective
  条件: (f : R ->+* S) (hf : 满射 f)
  结论: 满射 (map f : 𝕎 R -> 𝕎 S)
  证明: mapFun.surjective f hf

@[simp]

Depends on / 依赖: mapFun, mapFun.surjective, surjective
-/
theorem map_surjective (f : R ->+* S) (hf : Surjective f) : Surjective (map f : 𝕎 R -> 𝕎 S) :=
  mapFun.surjective f hf

@[simp]
/--
theorem `map_coeff` / 定理 `map_coeff`

English:
theorem map_coeff
  given: (f : R ->+* S) (x : 𝕎 R) (n : Nat)
  statement: (map f x).coeff n = f (x.coeff n)
  proof: rfl

中文:
定理 map_coeff
  条件: (f : R ->+* S) (x : 𝕎 R) (n : 自然数)
  结论: (map f x).coeff n = f (x.coeff n)
  证明: rfl
-/
theorem map_coeff (f : R ->+* S) (x : 𝕎 R) (n : Nat) : (map f x).coeff n = f (x.coeff n) :=
  rfl

variable (R) in
@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: WittVector.map (RingHom.id R) = RingHom.id (𝕎 R)
  proof: by
  ext; simp

中文:
定理 map_id
  结论: Witt向量.map (环态射.id R) = 环态射.id (𝕎 R)
  证明: by
  ext; simp
-/
theorem map_id : WittVector.map (RingHom.id R) = RingHom.id (𝕎 R) := by
  ext; simp

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: (f : R ->+* S) {x : WittVector p R}
  proof: by
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · apply_fun (·.coeff n) at h
    simpa using h
  · ext n
    simpa using h n

中文:
定理 map_eq_zero_iff
  条件: (f : R ->+* S) {x : Witt向量 p R}
  证明: by
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · apply_fun (·.coeff n) at h
    simpa using h
  · ext n
    simpa using h n

Depends on / 依赖: apply_fun
-/
theorem map_eq_zero_iff (f : R ->+* S) {x : WittVector p R} :
    ((map f) x) = 0 ↔ forall n, f (x.coeff n) = 0 := by
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · apply_fun (·.coeff n) at h
    simpa using h
  · ext n
    simpa using h n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `ghostMap` / `ghostMap` 的定义

English:
definition ghostMap
  signature: : 𝕎 R ->+* Nat -> R where
  body: ghostFun
  map_zero' := ghostFun_zero
  map_one' := ghostFun_one
  map_add' := ghostFun_add
  map_mul' := ghostFun_mul

中文:
定义 ghostMap
  签名: : 𝕎 R ->+* 自然数 -> R where
  定义体: ghostFun
  map_zero' := ghostFun_zero
  map_one' := ghostFun_one
  map_add' := ghostFun_add
  map_mul' := ghostFun_mul

Depends on / 依赖: ghostFun
-/
def ghostMap : 𝕎 R ->+* Nat -> R where
  toFun := ghostFun
  map_zero' := ghostFun_zero
  map_one' := ghostFun_one
  map_add' := ghostFun_add
  map_mul' := ghostFun_mul

/--
Definition of `ghostComponent` / `ghostComponent` 的定义

English:
definition ghostComponent
  signature: (n : Nat)
  body: (Pi.evalRingHom _ n).comp ghostMap

中文:
定义 ghostComponent
  签名: (n : 自然数)
  定义体: (Pi.evalRingHom _ n).comp ghostMap

Depends on / 依赖: Pi.evalRingHom, evalRingHom, ghostMap
-/
def ghostComponent (n : Nat) : 𝕎 R ->+* R :=
  (Pi.evalRingHom _ n).comp ghostMap

/--
theorem `ghostComponent_apply` / 定理 `ghostComponent_apply`

English:
theorem ghostComponent_apply
  given: (n : Nat) (x : 𝕎 R)
  statement: ghostComponent n x = aeval x.coeff (W_ Int n)
  proof: rfl

中文:
定理 ghostComponent_apply
  条件: (n : 自然数) (x : 𝕎 R)
  结论: ghostComponent n x = aeval x.coeff (W_ 整数 n)
  证明: rfl
-/
theorem ghostComponent_apply (n : Nat) (x : 𝕎 R) : ghostComponent n x = aeval x.coeff (W_ Int n) :=
  rfl

/--
theorem `pow_dvd_ghostComponent_of_dvd_coeff` / 定理 `pow_dvd_ghostComponent_of_dvd_coeff`

English:
theorem pow_dvd_ghostComponent_of_dvd_coeff
  statement: {x : 𝕎 R} {n : Nat}
  proof: by
  rw [WittVector.ghostComponent_apply]; rw [wittPolynomial]; rw [MvPolynomial.aeval_sum]
  apply Finset.dvd_sum
  intro i hi
  simp only [Finset.mem_range] at hi
  have : (MvPolynomial.aeval x.coeff) ((MvPolynomial.monomial (R := Int)
      (Finsupp.single i (p ^ (n - i)))) (p ^ i)) = ((p : R) ^ 

中文:
定理 pow_dvd_ghostComponent_of_dvd_coeff
  结论: {x : 𝕎 R} {n : 自然数}
  证明: by
  rw [WittVector.ghostComponent_apply]; rw [wittPolynomial]; rw [MvPolynomial.aeval_sum]
  apply Finset.dvd_sum
  intro i hi
  simp only [Finset.mem_range] at hi
  have : (MvPolynomial.aeval x.coeff) ((MvPolynomial.monomial (R := Int)
      (Finsupp.single i (p ^ (n - i)))) (p ^ i)) = ((p : R) ^ 

Depends on / 依赖: Finset, Finset.dvd_sum, Finset.mem_range, Finsupp, Finsupp.single, MvPolynomial, MvPolynomial.aeval, MvPolynomial.aeval_monomial, MvPolynomial.aeval_sum, MvPolynomial.monomial, Nat.le_of_lt_succ, WittVector, WittVector.ghostComponent_apply, a.toFiberBundle, a.totalSpaceTopology, aeval_monomial, aeval_sum, dvd_sum, ghostComponent_apply, le_of_lt_succ
-/
theorem pow_dvd_ghostComponent_of_dvd_coeff {x : 𝕎 R} {n : Nat}
    (hx : forall i <= n, (p : R) ∣ x.coeff i) : (p : R) ^ (n + 1) ∣ ghostComponent n x := by
  rw [WittVector.ghostComponent_apply]; rw [wittPolynomial]; rw [MvPolynomial.aeval_sum]
  apply Finset.dvd_sum
  intro i hi
  simp only [Finset.mem_range] at hi
  have : (MvPolynomial.aeval x.coeff) ((MvPolynomial.monomial (R := Int)
      (Finsupp.single i (p ^ (n - i)))) (p ^ i)) = ((p : R) ^ i) * (x.coeff i) ^ (p ^ (n - i)) := by
    simp [MvPolynomial.aeval_monomial, map_pow]
  rw [this]; rw [show n + 1 = (n - i) + 1 + i by lia]; rw [pow_add]; rw [mul_comm]
  gcongr
  · exact hx i (Nat.le_of_lt_succ hi)
  · exact ((n - i).lt_two_pow_self).succ_le.trans
        (pow_left_mono (n - i) (Nat.Prime.two_le Fact.out))

@[simp]
/--
theorem `ghostMap_apply` / 定理 `ghostMap_apply`

English:
theorem ghostMap_apply
  given: (x : 𝕎 R) (n : Nat)
  statement: ghostMap x n = ghostComponent n x
  proof: rfl

中文:
定理 ghostMap_apply
  条件: (x : 𝕎 R) (n : 自然数)
  结论: ghostMap x n = ghostComponent n x
  证明: rfl
-/
theorem ghostMap_apply (x : 𝕎 R) (n : Nat) : ghostMap x n = ghostComponent n x :=
  rfl

section Invertible

variable (p R)
variable [Invertible (p : R)]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `ghostEquiv` / `ghostEquiv` 的定义

English:
definition ghostEquiv
  signature: : 𝕎 R ≃+* (Nat -> R)
  body: { (ghostMap : 𝕎 R ->+* Nat -> R), ghostEquiv' p R with }

@[simp]

中文:
定义 ghostEquiv
  签名: : 𝕎 R ≃+* (自然数 -> R)
  定义体: { (ghostMap : 𝕎 R ->+* Nat -> R), ghostEquiv' p R with }

@[simp]

Depends on / 依赖: ghostEquiv, ghostMap
-/
def ghostEquiv : 𝕎 R ≃+* (Nat -> R) :=
  { (ghostMap : 𝕎 R ->+* Nat -> R), ghostEquiv' p R with }

@[simp]
/--
theorem `ghostEquiv_coe` / 定理 `ghostEquiv_coe`

English:
theorem ghostEquiv_coe
  statement: (ghostEquiv p R : 𝕎 R ->+* Nat -> R) = ghostMap
  proof: rfl

中文:
定理 ghostEquiv_coe
  结论: (ghostEquiv p R : 𝕎 R ->+* 自然数 -> R) = ghostMap
  证明: rfl
-/
theorem ghostEquiv_coe : (ghostEquiv p R : 𝕎 R ->+* Nat -> R) = ghostMap :=
  rfl

/--
theorem `ghostMap.bijective_of_invertible` / 定理 `ghostMap.bijective_of_invertible`

English:
theorem ghostMap.bijective_of_invertible
  statement: Function.Bijective (ghostMap : 𝕎 R -> Nat -> R)
  proof: (ghostEquiv p R).bijective

中文:
定理 ghostMap.bijective_of_invertible
  结论: 函数.双射 (ghostMap : 𝕎 R -> 自然数 -> R)
  证明: (ghostEquiv p R).bijective

Depends on / 依赖: bijective, ghostEquiv
-/
theorem ghostMap.bijective_of_invertible : Function.Bijective (ghostMap : 𝕎 R -> Nat -> R) :=
  (ghostEquiv p R).bijective

end Invertible

/-- `WittVector.coeff x 0` as a `RingHom` -/
@[simps]
/--
Definition of `constantCoeff` / `constantCoeff` 的定义

English:
definition constantCoeff
  signature: : 𝕎 R ->+* R where
  body: x.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' := add_coeff_zero
  map_mul' := mul_coeff_zero

中文:
定义 constantCoeff
  签名: : 𝕎 R ->+* R where
  定义体: x.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' := add_coeff_zero
  map_mul' := mul_coeff_zero

Depends on / 依赖: x.coeff
-/
noncomputable def constantCoeff : 𝕎 R ->+* R where
  toFun x := x.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' := add_coeff_zero
  map_mul' := mul_coeff_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (𝕎 R)
  body: constantCoeff.domain_nontrivial

中文:
实例 [非平凡
  签名: R] : 非平凡 (𝕎 R)
  定义体: constantCoeff.domain_nontrivial

Depends on / 依赖: constantCoeff, constantCoeff.domain_nontrivial, domain_nontrivial
-/
instance [Nontrivial R] : Nontrivial (𝕎 R) :=
  constantCoeff.domain_nontrivial

end WittVector
