/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.WittVector.InitTail

/-!

# Truncated Witt vectors

The ring of truncated Witt vectors (of length `n`) is a quotient of the ring of Witt vectors.
It retains the first `n` coefficients of each Witt vector.
In this file, we set up the basic quotient API for this ring.

The ring of Witt vectors is the projective limit of all the rings of truncated Witt vectors.

## Main declarations

- `TruncatedWittVector`: the underlying type of the ring of truncated Witt vectors
- `TruncatedWittVector.instCommRing`: the ring structure on truncated Witt vectors
- `WittVector.truncate`: the quotient homomorphism that truncates a Witt vector,
  to obtain a truncated Witt vector
- `TruncatedWittVector.truncate`: the homomorphism that truncates
  a truncated Witt vector of length `n` to one of length `m` (for some `m ≤ n`)
- `WittVector.lift`: the unique ring homomorphism into the ring of Witt vectors
  that is compatible with a family of ring homomorphisms to the truncated Witt vectors:
  this realizes the ring of Witt vectors as projective limit of the rings of truncated Witt vectors

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


open Function (Injective Surjective)

noncomputable section

variable {p : Nat} (n : Nat) (R : Type*)

local notation "𝕎" => WittVector p -- type as `\bbW`

/-- A truncated Witt vector over `R` is a vector of elements of `R`,
i.e., the first `n` coefficients of a Witt vector.
We will define operations on this type that are compatible with the (untruncated) Witt
vector operations.

`TruncatedWittVector p n R` takes a parameter `p : ℕ` that is not used in the definition.
In practice, this number `p` is assumed to be a prime number,
and under this assumption we construct a ring structure on `TruncatedWittVector p n R`.
(`TruncatedWittVector p₁ n R` and `TruncatedWittVector p₂ n R` are definitionally
equal as types but will have different ring operations.)
-/
@[nolint unusedArguments]
/--
Definition of `TruncatedWittVector` / `TruncatedWittVector` 的定义

English:
definition TruncatedWittVector
  signature: (_ : Nat) (n : Nat) (R : Type*)
  body: Fin n -> R

中文:
定义 TruncatedWittVector
  签名: (_ : 自然数) (n : 自然数) (R : 类型)
  定义体: Fin n -> R
-/
def TruncatedWittVector (_ : Nat) (n : Nat) (R : Type*) :=
  Fin n -> R

instance (p n : Nat) (R : Type*) [Inhabited R] : Inhabited (TruncatedWittVector p n R) :=
  ⟨fun _ => default⟩

variable {n R}

namespace TruncatedWittVector

variable (p) in
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : Fin n -> R)
  body: x

中文:
定义 mk
  签名: (x : 有限集 n -> R)
  定义体: x
-/
def mk (x : Fin n -> R) : TruncatedWittVector p n R :=
  x

/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (i : Fin n) (x : TruncatedWittVector p n R)
  body: x i

@[ext]

中文:
定义 coeff
  签名: (i : 有限集 n) (x : TruncatedWittVector p n R)
  定义体: x i

@[ext]
-/
def coeff (i : Fin n) (x : TruncatedWittVector p n R) : R :=
  x i

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : TruncatedWittVector p n R} (h : forall i, x.coeff i = y.coeff i)
  statement: x = y
  proof: funext h

@[simp]

中文:
定理 ext
  条件: {x y : TruncatedWittVector p n R} (h : 对任意 i, x.coeff i = y.coeff i)
  结论: x = y
  证明: funext h

@[simp]
-/
theorem ext {x y : TruncatedWittVector p n R} (h : forall i, x.coeff i = y.coeff i) : x = y :=
  funext h

@[simp]
/--
theorem `coeff_mk` / 定理 `coeff_mk`

English:
theorem coeff_mk
  given: (x : Fin n -> R) (i : Fin n)
  statement: (mk p x).coeff i = x i
  proof: rfl

@[simp]

中文:
定理 coeff_mk
  条件: (x : 有限集 n -> R) (i : 有限集 n)
  结论: (mk p x).coeff i = x i
  证明: rfl

@[simp]
-/
theorem coeff_mk (x : Fin n -> R) (i : Fin n) : (mk p x).coeff i = x i :=
  rfl

@[simp]
/--
theorem `mk_coeff` / 定理 `mk_coeff`

English:
theorem mk_coeff
  given: (x : TruncatedWittVector p n R)
  statement: (mk p fun i => x.coeff i) = x
  proof: by
  ext i; rw [coeff_mk]

中文:
定理 mk_coeff
  条件: (x : TruncatedWittVector p n R)
  结论: (mk p fun i => x.coeff i) = x
  证明: by
  ext i; rw [coeff_mk]

Depends on / 依赖: coeff_mk
-/
theorem mk_coeff (x : TruncatedWittVector p n R) : (mk p fun i => x.coeff i) = x := by
  ext i; rw [coeff_mk]

variable [CommRing R]

/--
Definition of `out` / `out` 的定义

English:
definition out
  signature: (x : TruncatedWittVector p n R)
  body: @WittVector.mk' p _ fun i => if h : i < n then x.coeff ⟨i, h⟩ else 0

@[simp]

中文:
定义 out
  签名: (x : TruncatedWittVector p n R)
  定义体: @WittVector.mk' p _ fun i => if h : i < n then x.coeff ⟨i, h⟩ else 0

@[simp]

Depends on / 依赖: WittVector, WittVector.mk, x.coeff
-/
def out (x : TruncatedWittVector p n R) : 𝕎 R :=
  @WittVector.mk' p _ fun i => if h : i < n then x.coeff ⟨i, h⟩ else 0

@[simp]
/--
theorem `coeff_out` / 定理 `coeff_out`

English:
theorem coeff_out
  given: (x : TruncatedWittVector p n R) (i : Fin n)
  statement: x.out.coeff i = x.coeff i
  proof: by
  rw [out]; dsimp only; rw [dif_pos i.is_lt, Fin.eta]

中文:
定理 coeff_out
  条件: (x : TruncatedWittVector p n R) (i : 有限集 n)
  结论: x.out.coeff i = x.coeff i
  证明: by
  rw [out]; dsimp only; rw [dif_pos i.is_lt, Fin.eta]

Depends on / 依赖: Fin.eta, dif_pos, i.is_lt, is_lt
-/
theorem coeff_out (x : TruncatedWittVector p n R) (i : Fin n) : x.out.coeff i = x.coeff i := by
  rw [out]; dsimp only; rw [dif_pos i.is_lt, Fin.eta]

/--
theorem `out_injective` / 定理 `out_injective`

English:
theorem out_injective
  statement: Injective (@out p n R _)
  proof: by
  intro x y h
  ext i
  rw [WittVector.ext_iff] at h
  simpa only [coeff_out] using h ↑i

中文:
定理 out_injective
  结论: 单射 (@out p n R _)
  证明: by
  intro x y h
  ext i
  rw [WittVector.ext_iff] at h
  simpa only [coeff_out] using h ↑i

Depends on / 依赖: WittVector, WittVector.ext_iff, coeff_out, ext_iff
-/
theorem out_injective : Injective (@out p n R _) := by
  intro x y h
  ext i
  rw [WittVector.ext_iff] at h
  simpa only [coeff_out] using h ↑i

end TruncatedWittVector

namespace WittVector

variable (n)

section

/--
Definition of `truncateFun` / `truncateFun` 的定义

English:
definition truncateFun
  signature: (x : 𝕎 R)
  body: TruncatedWittVector.mk p fun i => x.coeff i

中文:
定义 truncateFun
  签名: (x : 𝕎 R)
  定义体: TruncatedWittVector.mk p fun i => x.coeff i

Depends on / 依赖: TruncatedWittVector, TruncatedWittVector.mk, x.coeff
-/
def truncateFun (x : 𝕎 R) : TruncatedWittVector p n R :=
  TruncatedWittVector.mk p fun i => x.coeff i

end

variable {n}

@[simp]
/--
theorem `coeff_truncateFun` / 定理 `coeff_truncateFun`

English:
theorem coeff_truncateFun
  given: (x : 𝕎 R) (i : Fin n)
  statement: (truncateFun n x).coeff i = x.coeff i
  proof: by
  rw [truncateFun]; rw [TruncatedWittVector.coeff_mk]

中文:
定理 coeff_truncateFun
  条件: (x : 𝕎 R) (i : 有限集 n)
  结论: (truncateFun n x).coeff i = x.coeff i
  证明: by
  rw [truncateFun]; rw [TruncatedWittVector.coeff_mk]

Depends on / 依赖: TruncatedWittVector, TruncatedWittVector.coeff_mk, coeff_mk, truncateFun
-/
theorem coeff_truncateFun (x : 𝕎 R) (i : Fin n) : (truncateFun n x).coeff i = x.coeff i := by
  rw [truncateFun]; rw [TruncatedWittVector.coeff_mk]

variable [CommRing R]

@[simp]
/--
theorem `out_truncateFun` / 定理 `out_truncateFun`

English:
theorem out_truncateFun
  given: (x : 𝕎 R)
  statement: (truncateFun n x).out = init n x
  proof: by
  ext i
  dsimp [TruncatedWittVector.out, init, select, coeff_mk]
  split_ifs with hi; swap; · rfl
  rw [coeff_truncateFun]; rw [Fin.val_mk]

中文:
定理 out_truncateFun
  条件: (x : 𝕎 R)
  结论: (truncateFun n x).out = init n x
  证明: by
  ext i
  dsimp [TruncatedWittVector.out, init, select, coeff_mk]
  split_ifs with hi; swap; · rfl
  rw [coeff_truncateFun]; rw [Fin.val_mk]

Depends on / 依赖: Fin.val_mk, TruncatedWittVector, TruncatedWittVector.out, coeff_mk, coeff_truncateFun, select, split_ifs, val_mk
-/
theorem out_truncateFun (x : 𝕎 R) : (truncateFun n x).out = init n x := by
  ext i
  dsimp [TruncatedWittVector.out, init, select, coeff_mk]
  split_ifs with hi; swap; · rfl
  rw [coeff_truncateFun]; rw [Fin.val_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRing R]

@[simp]
/--
theorem `truncateFun_out` / 定理 `truncateFun_out`

English:
theorem truncateFun_out
  given: (x : TruncatedWittVector p n R)
  statement: x.out.truncateFun n = x
  proof: by
  simp only [WittVector.truncateFun, coeff_out, mk_coeff]

中文:
定理 truncateFun_out
  条件: (x : TruncatedWittVector p n R)
  结论: x.out.truncateFun n = x
  证明: by
  simp only [WittVector.truncateFun, coeff_out, mk_coeff]

Depends on / 依赖: WittVector, WittVector.truncateFun, coeff_out, mk_coeff, truncateFun
-/
theorem truncateFun_out (x : TruncatedWittVector p n R) : x.out.truncateFun n = x := by
  simp only [WittVector.truncateFun, coeff_out, mk_coeff]

open WittVector

variable (p n R)
variable [Fact p.Prime]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (TruncatedWittVector p n R)
  body: ⟨truncateFun n 0⟩

中文:
实例 :
  签名: 零 (TruncatedWittVector p n R)
  定义体: ⟨truncateFun n 0⟩

Depends on / 依赖: truncateFun
-/
instance : Zero (TruncatedWittVector p n R) :=
  ⟨truncateFun n 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (TruncatedWittVector p n R)
  body: ⟨truncateFun n 1⟩

中文:
实例 :
  签名: 幺 (TruncatedWittVector p n R)
  定义体: ⟨truncateFun n 1⟩

Depends on / 依赖: truncateFun
-/
instance : One (TruncatedWittVector p n R) :=
  ⟨truncateFun n 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (TruncatedWittVector p n R)
  body: ⟨fun i => truncateFun n i⟩

中文:
实例 :
  签名: 自然数嵌入 (TruncatedWittVector p n R)
  定义体: ⟨fun i => truncateFun n i⟩

Depends on / 依赖: truncateFun
-/
instance : NatCast (TruncatedWittVector p n R) :=
  ⟨fun i => truncateFun n i⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (TruncatedWittVector p n R)
  body: ⟨fun i => truncateFun n i⟩

中文:
实例 :
  签名: 整数嵌入 (TruncatedWittVector p n R)
  定义体: ⟨fun i => truncateFun n i⟩

Depends on / 依赖: truncateFun
-/
instance : IntCast (TruncatedWittVector p n R) :=
  ⟨fun i => truncateFun n i⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (TruncatedWittVector p n R)
  body: ⟨fun x y => truncateFun n (x.out + y.out)⟩

中文:
实例 :
  签名: 加法 (TruncatedWittVector p n R)
  定义体: ⟨fun x y => truncateFun n (x.out + y.out)⟩

Depends on / 依赖: truncateFun, x.out, y.out
-/
instance : Add (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out + y.out)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (TruncatedWittVector p n R)
  body: ⟨fun x y => truncateFun n (x.out * y.out)⟩

中文:
实例 :
  签名: 乘法 (TruncatedWittVector p n R)
  定义体: ⟨fun x y => truncateFun n (x.out * y.out)⟩

Depends on / 依赖: truncateFun, x.out, y.out
-/
instance : Mul (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out * y.out)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (TruncatedWittVector p n R)
  body: ⟨fun x => truncateFun n (-x.out)⟩

中文:
实例 :
  签名: 取负 (TruncatedWittVector p n R)
  定义体: ⟨fun x => truncateFun n (-x.out)⟩

Depends on / 依赖: truncateFun, x.out
-/
instance : Neg (TruncatedWittVector p n R) :=
  ⟨fun x => truncateFun n (-x.out)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (TruncatedWittVector p n R)
  body: ⟨fun x y => truncateFun n (x.out - y.out)⟩

中文:
实例 :
  签名: 减法 (TruncatedWittVector p n R)
  定义体: ⟨fun x y => truncateFun n (x.out - y.out)⟩

Depends on / 依赖: truncateFun, x.out, y.out
-/
instance : Sub (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out - y.out)⟩

/--
Instance `hasNatScalar` / 实例 `hasNatScalar`

English:
instance hasNatScalar
  signature: : SMul Nat (TruncatedWittVector p n R)
  body: ⟨fun m x => truncateFun n (m • x.out)⟩

中文:
实例 has自然数Scalar
  签名: : 标量乘法 自然数 (TruncatedWittVector p n R)
  定义体: ⟨fun m x => truncateFun n (m • x.out)⟩

Depends on / 依赖: truncateFun, x.out
-/
instance hasNatScalar : SMul Nat (TruncatedWittVector p n R) :=
  ⟨fun m x => truncateFun n (m • x.out)⟩

/--
Instance `hasIntScalar` / 实例 `hasIntScalar`

English:
instance hasIntScalar
  signature: : SMul Int (TruncatedWittVector p n R)
  body: ⟨fun m x => truncateFun n (m • x.out)⟩

中文:
实例 has整数Scalar
  签名: : 标量乘法 整数 (TruncatedWittVector p n R)
  定义体: ⟨fun m x => truncateFun n (m • x.out)⟩

Depends on / 依赖: truncateFun, x.out
-/
instance hasIntScalar : SMul Int (TruncatedWittVector p n R) :=
  ⟨fun m x => truncateFun n (m • x.out)⟩

/--
Instance `hasNatPow` / 实例 `hasNatPow`

English:
instance hasNatPow
  signature: : Pow (TruncatedWittVector p n R) Nat
  body: ⟨fun x m => truncateFun n (x.out ^ m)⟩

@[simp]

中文:
实例 has自然数Pow
  签名: : 幂 (TruncatedWittVector p n R) 自然数
  定义体: ⟨fun x m => truncateFun n (x.out ^ m)⟩

@[simp]

Depends on / 依赖: truncateFun, x.out
-/
instance hasNatPow : Pow (TruncatedWittVector p n R) Nat :=
  ⟨fun x m => truncateFun n (x.out ^ m)⟩

@[simp]
/--
theorem `coeff_zero` / 定理 `coeff_zero`

English:
theorem coeff_zero
  given: (i : Fin n)
  statement: (0 : TruncatedWittVector p n R).coeff i = 0
  proof: by
  change coeff i (truncateFun _ 0 : TruncatedWittVector p n R) = 0
  rw [coeff_truncateFun]; rw [WittVector.zero_coeff]

中文:
定理 coeff_zero
  条件: (i : 有限集 n)
  结论: (0 : TruncatedWittVector p n R).coeff i = 0
  证明: by
  change coeff i (truncateFun _ 0 : TruncatedWittVector p n R) = 0
  rw [coeff_truncateFun]; rw [WittVector.zero_coeff]

Depends on / 依赖: TruncatedWittVector, WittVector, WittVector.zero_coeff, coeff_truncateFun, truncateFun, zero_coeff
-/
theorem coeff_zero (i : Fin n) : (0 : TruncatedWittVector p n R).coeff i = 0 := by
  change coeff i (truncateFun _ 0 : TruncatedWittVector p n R) = 0
  rw [coeff_truncateFun]; rw [WittVector.zero_coeff]

end TruncatedWittVector

/-- A macro tactic used to prove that `truncateFun` respects ring operations. -/
macro (name := witt_truncateFun_tac) "witt_truncateFun_tac" : tactic =>
  `(tactic|
    { change _ = WittVector.truncateFun n _
      apply TruncatedWittVector.out_injective
      iterate rw [WittVector.out_truncateFun]
      first
      | rw [WittVector.init_add]
      | rw [WittVector.init_mul]
      | rw [WittVector.init_neg]
      | rw [WittVector.init_sub]
      | rw [WittVector.init_nsmul]
      | rw [WittVector.init_zsmul]
      | rw [WittVector.init_pow]})

namespace WittVector

variable (p n R)
variable [CommRing R]

/--
theorem `truncateFun_surjective` / 定理 `truncateFun_surjective`

English:
theorem truncateFun_surjective
  statement: Surjective (@truncateFun p n R)
  proof: Function.RightInverse.surjective TruncatedWittVector.truncateFun_out

中文:
定理 truncateFun_surjective
  结论: 满射 (@truncateFun p n R)
  证明: Function.RightInverse.surjective TruncatedWittVector.truncateFun_out

Depends on / 依赖: Function, Function.RightInverse.surjective, RightInverse, TruncatedWittVector, TruncatedWittVector.truncateFun_out, surjective, truncateFun_out
-/
theorem truncateFun_surjective : Surjective (@truncateFun p n R) :=
  Function.RightInverse.surjective TruncatedWittVector.truncateFun_out

variable [Fact p.Prime]

@[simp]
/--
theorem `truncateFun_zero` / 定理 `truncateFun_zero`

English:
theorem truncateFun_zero
  statement: truncateFun n (0 : 𝕎 R) = 0
  proof: rfl

@[simp]

中文:
定理 truncateFun_zero
  结论: truncateFun n (0 : 𝕎 R) = 0
  证明: rfl

@[simp]
-/
theorem truncateFun_zero : truncateFun n (0 : 𝕎 R) = 0 := rfl

@[simp]
/--
theorem `truncateFun_one` / 定理 `truncateFun_one`

English:
theorem truncateFun_one
  statement: truncateFun n (1 : 𝕎 R) = 1
  proof: rfl

中文:
定理 truncateFun_one
  结论: truncateFun n (1 : 𝕎 R) = 1
  证明: rfl
-/
theorem truncateFun_one : truncateFun n (1 : 𝕎 R) = 1 := rfl

variable {p R}

@[simp]
/--
theorem `truncateFun_add` / 定理 `truncateFun_add`

English:
theorem truncateFun_add
  given: (x y : 𝕎 R)
  proof: by
  witt_truncateFun_tac

@[simp]

中文:
定理 truncateFun_add
  条件: (x y : 𝕎 R)
  证明: by
  witt_truncateFun_tac

@[simp]

Depends on / 依赖: witt_truncateFun_tac
-/
theorem truncateFun_add (x y : 𝕎 R) :
    truncateFun n (x + y) = truncateFun n x + truncateFun n y := by
  witt_truncateFun_tac

@[simp]
/--
theorem `truncateFun_mul` / 定理 `truncateFun_mul`

English:
theorem truncateFun_mul
  given: (x y : 𝕎 R)
  proof: by
  witt_truncateFun_tac

中文:
定理 truncateFun_mul
  条件: (x y : 𝕎 R)
  证明: by
  witt_truncateFun_tac

Depends on / 依赖: witt_truncateFun_tac
-/
theorem truncateFun_mul (x y : 𝕎 R) :
    truncateFun n (x * y) = truncateFun n x * truncateFun n y := by
  witt_truncateFun_tac

/--
theorem `truncateFun_neg` / 定理 `truncateFun_neg`

English:
theorem truncateFun_neg
  given: (x : 𝕎 R)
  statement: truncateFun n (-x) = -truncateFun n x
  proof: by
  witt_truncateFun_tac

中文:
定理 truncateFun_neg
  条件: (x : 𝕎 R)
  结论: truncateFun n (-x) = -truncateFun n x
  证明: by
  witt_truncateFun_tac

Depends on / 依赖: witt_truncateFun_tac
-/
theorem truncateFun_neg (x : 𝕎 R) : truncateFun n (-x) = -truncateFun n x := by
  witt_truncateFun_tac

/--
theorem `truncateFun_sub` / 定理 `truncateFun_sub`

English:
theorem truncateFun_sub
  given: (x y : 𝕎 R)
  proof: by
  witt_truncateFun_tac

中文:
定理 truncateFun_sub
  条件: (x y : 𝕎 R)
  证明: by
  witt_truncateFun_tac

Depends on / 依赖: witt_truncateFun_tac
-/
theorem truncateFun_sub (x y : 𝕎 R) :
    truncateFun n (x - y) = truncateFun n x - truncateFun n y := by
  witt_truncateFun_tac

/--
theorem `truncateFun_nsmul` / 定理 `truncateFun_nsmul`

English:
theorem truncateFun_nsmul
  given: (m : Nat) (x : 𝕎 R)
  statement: truncateFun n (m • x) = m • truncateFun n x
  proof: by
  witt_truncateFun_tac

中文:
定理 truncateFun_nsmul
  条件: (m : 自然数) (x : 𝕎 R)
  结论: truncateFun n (m • x) = m • truncateFun n x
  证明: by
  witt_truncateFun_tac

Depends on / 依赖: witt_truncateFun_tac
-/
theorem truncateFun_nsmul (m : Nat) (x : 𝕎 R) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncateFun_tac

/--
theorem `truncateFun_zsmul` / 定理 `truncateFun_zsmul`

English:
theorem truncateFun_zsmul
  given: (m : Int) (x : 𝕎 R)
  statement: truncateFun n (m • x) = m • truncateFun n x
  proof: by
  witt_truncateFun_tac

中文:
定理 truncateFun_zsmul
  条件: (m : 整数) (x : 𝕎 R)
  结论: truncateFun n (m • x) = m • truncateFun n x
  证明: by
  witt_truncateFun_tac

Depends on / 依赖: witt_truncateFun_tac
-/
theorem truncateFun_zsmul (m : Int) (x : 𝕎 R) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncateFun_tac

/--
theorem `truncateFun_pow` / 定理 `truncateFun_pow`

English:
theorem truncateFun_pow
  given: (x : 𝕎 R) (m : Nat)
  statement: truncateFun n (x ^ m) = truncateFun n x ^ m
  proof: by
  witt_truncateFun_tac

中文:
定理 truncateFun_pow
  条件: (x : 𝕎 R) (m : 自然数)
  结论: truncateFun n (x ^ m) = truncateFun n x ^ m
  证明: by
  witt_truncateFun_tac

Depends on / 依赖: witt_truncateFun_tac
-/
theorem truncateFun_pow (x : 𝕎 R) (m : Nat) : truncateFun n (x ^ m) = truncateFun n x ^ m := by
  witt_truncateFun_tac

/--
theorem `truncateFun_natCast` / 定理 `truncateFun_natCast`

English:
theorem truncateFun_natCast
  given: (m : Nat)
  statement: truncateFun n (m : 𝕎 R) = m
  proof: rfl

中文:
定理 truncateFun_natCast
  条件: (m : 自然数)
  结论: truncateFun n (m : 𝕎 R) = m
  证明: rfl
-/
theorem truncateFun_natCast (m : Nat) : truncateFun n (m : 𝕎 R) = m := rfl

/--
theorem `truncateFun_intCast` / 定理 `truncateFun_intCast`

English:
theorem truncateFun_intCast
  given: (m : Int)
  statement: truncateFun n (m : 𝕎 R) = m
  proof: rfl

中文:
定理 truncateFun_intCast
  条件: (m : 整数)
  结论: truncateFun n (m : 𝕎 R) = m
  证明: rfl
-/
theorem truncateFun_intCast (m : Int) : truncateFun n (m : 𝕎 R) = m := rfl

end WittVector

namespace TruncatedWittVector

open WittVector

variable (p n R)
variable [CommRing R]
variable [Fact p.Prime]

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing (TruncatedWittVector p n R)
  body: (truncateFun_surjective p n R).commRing _ (truncateFun_zero p n R) (truncateFun_one p n R)
    (truncateFun_add n) (truncateFun_mul n) (truncateFun_neg n) (truncateFun_sub n)
    (truncateFun_nsmul n) (truncateFun_zsmul n) (truncateFun_pow n) (truncateFun_natCast n)
    (truncateFun_intCast n)

中文:
实例 instCommRing
  签名: : 交换环 (TruncatedWittVector p n R)
  定义体: (truncateFun_surjective p n R).commRing _ (truncateFun_zero p n R) (truncateFun_one p n R)
    (truncateFun_add n) (truncateFun_mul n) (truncateFun_neg n) (truncateFun_sub n)
    (truncateFun_nsmul n) (truncateFun_zsmul n) (truncateFun_pow n) (truncateFun_natCast n)
    (truncateFun_intCast n)

Depends on / 依赖: commRing, truncateFun_add, truncateFun_intCast, truncateFun_mul, truncateFun_natCast, truncateFun_neg, truncateFun_nsmul, truncateFun_one, truncateFun_pow, truncateFun_sub, truncateFun_surjective, truncateFun_zero, truncateFun_zsmul
-/
instance instCommRing : CommRing (TruncatedWittVector p n R) :=
  (truncateFun_surjective p n R).commRing _ (truncateFun_zero p n R) (truncateFun_one p n R)
    (truncateFun_add n) (truncateFun_mul n) (truncateFun_neg n) (truncateFun_sub n)
    (truncateFun_nsmul n) (truncateFun_zsmul n) (truncateFun_pow n) (truncateFun_natCast n)
    (truncateFun_intCast n)

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector

variable (n)
variable [CommRing R]
variable [Fact p.Prime]

/--
Definition of `truncate` / `truncate` 的定义

English:
definition truncate
  signature: : 𝕎 R ->+* TruncatedWittVector p n R where
  body: truncateFun n
  map_zero' := truncateFun_zero p n R
  map_add' := truncateFun_add n
  map_one' := truncateFun_one p n R
  map_mul' := truncateFun_mul n

中文:
定义 truncate
  签名: : 𝕎 R ->+* TruncatedWittVector p n R where
  定义体: truncateFun n
  map_zero' := truncateFun_zero p n R
  map_add' := truncateFun_add n
  map_one' := truncateFun_one p n R
  map_mul' := truncateFun_mul n

Depends on / 依赖: truncateFun
-/
noncomputable def truncate : 𝕎 R ->+* TruncatedWittVector p n R where
  toFun := truncateFun n
  map_zero' := truncateFun_zero p n R
  map_add' := truncateFun_add n
  map_one' := truncateFun_one p n R
  map_mul' := truncateFun_mul n

variable (p R)

/--
theorem `truncate_surjective` / 定理 `truncate_surjective`

English:
theorem truncate_surjective
  statement: Surjective (truncate n : 𝕎 R -> TruncatedWittVector p n R)
  proof: truncateFun_surjective p n R

中文:
定理 truncate_surjective
  结论: 满射 (truncate n : 𝕎 R -> TruncatedWittVector p n R)
  证明: truncateFun_surjective p n R

Depends on / 依赖: truncateFun_surjective
-/
theorem truncate_surjective : Surjective (truncate n : 𝕎 R -> TruncatedWittVector p n R) :=
  truncateFun_surjective p n R

variable {p n R}

@[simp]
/--
theorem `coeff_truncate` / 定理 `coeff_truncate`

English:
theorem coeff_truncate
  given: (x : 𝕎 R) (i : Fin n)
  statement: (truncate n x).coeff i = x.coeff i
  proof: coeff_truncateFun _ _

中文:
定理 coeff_truncate
  条件: (x : 𝕎 R) (i : 有限集 n)
  结论: (truncate n x).coeff i = x.coeff i
  证明: coeff_truncateFun _ _

Depends on / 依赖: coeff_truncateFun
-/
theorem coeff_truncate (x : 𝕎 R) (i : Fin n) : (truncate n x).coeff i = x.coeff i :=
  coeff_truncateFun _ _

variable (n)

/--
theorem `mem_ker_truncate` / 定理 `mem_ker_truncate`

English:
theorem mem_ker_truncate
  given: (x : 𝕎 R)
  proof: by
  simp only [RingHom.mem_ker, truncate, RingHom.coe_mk, TruncatedWittVector.ext_iff,
    coeff_zero]
  exact Fin.forall_iff

中文:
定理 mem_ker_truncate
  条件: (x : 𝕎 R)
  证明: by
  simp only [RingHom.mem_ker, truncate, RingHom.coe_mk, TruncatedWittVector.ext_iff,
    coeff_zero]
  exact Fin.forall_iff

Depends on / 依赖: Fin.forall_iff, RingHom, RingHom.coe_mk, RingHom.mem_ker, TruncatedWittVector, TruncatedWittVector.ext_iff, coe_mk, coeff_zero, ext_iff, forall_iff, mem_ker, truncate, x.coeff
-/
theorem mem_ker_truncate (x : 𝕎 R) :
    x in RingHom.ker (truncate (p := p) n) ↔ forall i < n, x.coeff i = 0 := by
  simp only [RingHom.mem_ker, truncate, RingHom.coe_mk, TruncatedWittVector.ext_iff,
    coeff_zero]
  exact Fin.forall_iff

variable (p)

@[simp]
/--
theorem `truncate_mk'` / 定理 `truncate_mk'`

English:
theorem truncate_mk'
  given: (f : Nat -> R)
  proof: by
  ext i
  simp only [coeff_truncate, TruncatedWittVector.coeff_mk]

中文:
定理 truncate_mk'
  条件: (f : 自然数 -> R)
  证明: by
  ext i
  simp only [coeff_truncate, TruncatedWittVector.coeff_mk]

Depends on / 依赖: TruncatedWittVector, TruncatedWittVector.coeff_mk, coeff_mk, coeff_truncate
-/
theorem truncate_mk' (f : Nat -> R) :
    truncate n (@mk' p _ f) = TruncatedWittVector.mk _ fun k => f k := by
  ext i
  simp only [coeff_truncate, TruncatedWittVector.coeff_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRing R]

section
variable [Fact p.Prime]

/--
Definition of `truncate` / `truncate` 的定义

English:
definition truncate
  signature: {m : Nat} (hm : n <= m)
  body: RingHom.liftOfRightInverse (WittVector.truncate m) out truncateFun_out
    ⟨WittVector.truncate n, by
      intro x
      simp only [WittVector.mem_ker_truncate]
      intro h i hi
      exact h i (lt_of_lt_of_le hi hm)⟩

@[simp]

中文:
定义 truncate
  签名: {m : 自然数} (hm : n <= m)
  定义体: RingHom.liftOfRightInverse (WittVector.truncate m) out truncateFun_out
    ⟨WittVector.truncate n, by
      intro x
      simp only [WittVector.mem_ker_truncate]
      intro h i hi
      exact h i (lt_of_lt_of_le hi hm)⟩

@[simp]

Depends on / 依赖: RingHom, RingHom.liftOfRightInverse, WittVector, WittVector.mem_ker_truncate, WittVector.truncate, liftOfRightInverse, lt_of_lt_of_le, mem_ker_truncate, truncate, truncateFun_out
-/
def truncate {m : Nat} (hm : n <= m) : TruncatedWittVector p m R ->+* TruncatedWittVector p n R :=
  RingHom.liftOfRightInverse (WittVector.truncate m) out truncateFun_out
    ⟨WittVector.truncate n, by
      intro x
      simp only [WittVector.mem_ker_truncate]
      intro h i hi
      exact h i (lt_of_lt_of_le hi hm)⟩

@[simp]
/--
theorem `truncate_comp_wittVector_truncate` / 定理 `truncate_comp_wittVector_truncate`

English:
theorem truncate_comp_wittVector_truncate
  given: {m : Nat} (hm : n <= m)
  proof: RingHom.liftOfRightInverse_comp _ _ _ _

@[simp]

中文:
定理 truncate_comp_wittVector_truncate
  条件: {m : 自然数} (hm : n <= m)
  证明: RingHom.liftOfRightInverse_comp _ _ _ _

@[simp]

Depends on / 依赖: WittVector, WittVector.truncate, truncate
-/
theorem truncate_comp_wittVector_truncate {m : Nat} (hm : n <= m) :
    (truncate (p := p) (R := R) hm).comp (WittVector.truncate m) = WittVector.truncate n :=
  RingHom.liftOfRightInverse_comp _ _ _ _

@[simp]
/--
theorem `truncate_wittVector_truncate` / 定理 `truncate_wittVector_truncate`

English:
theorem truncate_wittVector_truncate
  given: {m : Nat} (hm : n <= m) (x : 𝕎 R)
  proof: RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

@[simp]

中文:
定理 truncate_wittVector_truncate
  条件: {m : 自然数} (hm : n <= m) (x : 𝕎 R)
  证明: RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

@[simp]

Depends on / 依赖: RingHom, RingHom.liftOfRightInverse_comp_apply, liftOfRightInverse_comp_apply
-/
theorem truncate_wittVector_truncate {m : Nat} (hm : n <= m) (x : 𝕎 R) :
    truncate hm (WittVector.truncate m x) = WittVector.truncate n x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

@[simp]
/--
theorem `truncate_truncate` / 定理 `truncate_truncate`

English:
theorem truncate_truncate
  statement: {n₁ n₂ n₃ : Nat} (h1 : n₁ <= n₂) (h2 : n₂ <= n₃)
  proof: by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) n₃ R x
  simp only [truncate_wittVector_truncate]

@[simp]

中文:
定理 truncate_truncate
  结论: {n₁ n₂ n₃ : 自然数} (h1 : n₁ <= n₂) (h2 : n₂ <= n₃)
  证明: by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) n₃ R x
  simp only [truncate_wittVector_truncate]

@[simp]

Depends on / 依赖: WittVector, WittVector.truncate_surjective, truncate_surjective, truncate_wittVector_truncate
-/
theorem truncate_truncate {n₁ n₂ n₃ : Nat} (h1 : n₁ <= n₂) (h2 : n₂ <= n₃)
    (x : TruncatedWittVector p n₃ R) :
    (truncate h1) (truncate h2 x) = truncate (h1.trans h2) x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) n₃ R x
  simp only [truncate_wittVector_truncate]

@[simp]
/--
theorem `truncate_comp` / 定理 `truncate_comp`

English:
theorem truncate_comp
  given: {n₁ n₂ n₃ : Nat} (h1 : n₁ <= n₂) (h2 : n₂ <= n₃)
  proof: by
  ext1 x; simp only [truncate_truncate, Function.comp_apply, RingHom.coe_comp]

中文:
定理 truncate_comp
  条件: {n₁ n₂ n₃ : 自然数} (h1 : n₁ <= n₂) (h2 : n₂ <= n₃)
  证明: by
  ext1 x; simp only [truncate_truncate, Function.comp_apply, RingHom.coe_comp]

Depends on / 依赖: Function, Function.comp_apply, RingHom, RingHom.coe_comp, coe_comp, comp_apply, h1.trans, truncate, truncate_truncate
-/
theorem truncate_comp {n₁ n₂ n₃ : Nat} (h1 : n₁ <= n₂) (h2 : n₂ <= n₃) :
    (truncate (p := p) (R := R) h1).comp (truncate h2) = truncate (h1.trans h2) := by
  ext1 x; simp only [truncate_truncate, Function.comp_apply, RingHom.coe_comp]

/--
theorem `truncate_surjective` / 定理 `truncate_surjective`

English:
theorem truncate_surjective
  given: {m : Nat} (hm : n <= m)
  statement: Surjective (truncate (p := p) (R := R) hm)
  proof: by
  intro x
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) _ R x
  exact ⟨WittVector.truncate _ x, truncate_wittVector_truncate _ _⟩

@[simp]

中文:
定理 truncate_surjective
  条件: {m : 自然数} (hm : n <= m)
  结论: 满射 (truncate (p := p) (R := R) hm)
  证明: by
  intro x
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) _ R x
  exact ⟨WittVector.truncate _ x, truncate_wittVector_truncate _ _⟩

@[simp]

Depends on / 依赖: WittVector, WittVector.truncate, WittVector.truncate_surjective, truncate, truncate_surjective, truncate_wittVector_truncate
-/
theorem truncate_surjective {m : Nat} (hm : n <= m) : Surjective (truncate (p := p) (R := R) hm) := by
  intro x
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) _ R x
  exact ⟨WittVector.truncate _ x, truncate_wittVector_truncate _ _⟩

@[simp]
/--
theorem `coeff_truncate` / 定理 `coeff_truncate`

English:
theorem coeff_truncate
  given: {m : Nat} (hm : n <= m) (i : Fin n) (x : TruncatedWittVector p m R)
  proof: by
  obtain ⟨y, rfl⟩ := @WittVector.truncate_surjective p _ _ _ _ x
  simp only [truncate_wittVector_truncate, WittVector.coeff_truncate, Fin.val_castLE]

中文:
定理 coeff_truncate
  条件: {m : 自然数} (hm : n <= m) (i : 有限集 n) (x : TruncatedWittVector p m R)
  证明: by
  obtain ⟨y, rfl⟩ := @WittVector.truncate_surjective p _ _ _ _ x
  simp only [truncate_wittVector_truncate, WittVector.coeff_truncate, Fin.val_castLE]

Depends on / 依赖: Fin.val_castLE, WittVector, WittVector.coeff_truncate, WittVector.truncate_surjective, coeff_truncate, truncate_surjective, truncate_wittVector_truncate, val_castLE
-/
theorem coeff_truncate {m : Nat} (hm : n <= m) (i : Fin n) (x : TruncatedWittVector p m R) :
    (truncate hm x).coeff i = x.coeff (Fin.castLE hm i) := by
  obtain ⟨y, rfl⟩ := @WittVector.truncate_surjective p _ _ _ _ x
  simp only [truncate_wittVector_truncate, WittVector.coeff_truncate, Fin.val_castLE]

end

section Fintype

instance {R : Type*} [Fintype R] : Fintype (TruncatedWittVector p n R) :=
  Pi.instFintype

variable (p n R)

/--
theorem `card` / 定理 `card`

English:
theorem card
  given: {R : Type*} [Fintype R]
  proof: by
  simp only [TruncatedWittVector, Fintype.card_fin, Fintype.card_fun]

中文:
定理 card
  条件: {R : 类型} [有限类型 R]
  证明: by
  simp only [TruncatedWittVector, Fintype.card_fin, Fintype.card_fun]

Depends on / 依赖: Fintype, Fintype.card_fin, Fintype.card_fun, TruncatedWittVector, card_fin, card_fun
-/
theorem card {R : Type*} [Fintype R] :
    Fintype.card (TruncatedWittVector p n R) = Fintype.card R ^ n := by
  simp only [TruncatedWittVector, Fintype.card_fin, Fintype.card_fun]

end Fintype

variable [Fact p.Prime]

/--
theorem `iInf_ker_truncate` / 定理 `iInf_ker_truncate`

English:
theorem iInf_ker_truncate
  statement: ⨅ i : Nat, RingHom.ker (WittVector.truncate (p := p) (R := R) i) = ⊥
  proof: by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext
  simp only [WittVector.mem_ker_truncate, Ideal.mem_iInf, WittVector.zero_coeff] at hx ⊢
  exact hx _ _ (Nat.lt_succ_self _)

中文:
定理 iInf_ker_truncate
  结论: ⨅ i : 自然数, 环态射.ker (Witt向量.truncate (p := p) (R := R) i) = ⊥
  证明: by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext
  simp only [WittVector.mem_ker_truncate, Ideal.mem_iInf, WittVector.zero_coeff] at hx ⊢
  exact hx _ _ (Nat.lt_succ_self _)

Depends on / 依赖: Ideal.mem_iInf, Nat.lt_succ_self, Submodule, Submodule.eq_bot_iff, WittVector, WittVector.mem_ker_truncate, WittVector.zero_coeff, eq_bot_iff, lt_succ_self, mem_iInf, mem_ker_truncate, zero_coeff
-/
theorem iInf_ker_truncate : ⨅ i : Nat, RingHom.ker (WittVector.truncate (p := p) (R := R) i) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext
  simp only [WittVector.mem_ker_truncate, Ideal.mem_iInf, WittVector.zero_coeff] at hx ⊢
  exact hx _ _ (Nat.lt_succ_self _)

end TruncatedWittVector

namespace WittVector

open TruncatedWittVector hiding truncate coeff

section lift

variable [CommRing R]
variable [Fact p.Prime]
variable {S : Type*} [Semiring S]
variable (f : forall k : Nat, S ->+* TruncatedWittVector p k R)
variable
  (f_compat : forall (k₁ k₂ : Nat) (hk : k₁ <= k₂), (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁)

variable (n)

/--
Definition of `liftFun` / `liftFun` 的定义

English:
definition liftFun
  signature: (s : S)
  body: @WittVector.mk' p _ fun k => TruncatedWittVector.coeff (Fin.last k) (f (k + 1) s)

中文:
定义 liftFun
  签名: (s : S)
  定义体: @WittVector.mk' p _ fun k => TruncatedWittVector.coeff (Fin.last k) (f (k + 1) s)

Depends on / 依赖: Fin.last, TruncatedWittVector, TruncatedWittVector.coeff, WittVector, WittVector.mk
-/
def liftFun (s : S) : 𝕎 R :=
  @WittVector.mk' p _ fun k => TruncatedWittVector.coeff (Fin.last k) (f (k + 1) s)

variable {f} in
include f_compat in
@[simp]
/--
theorem `truncate_liftFun` / 定理 `truncate_liftFun`

English:
theorem truncate_liftFun
  given: (s : S)
  statement: WittVector.truncate n (liftFun f s) = f n s
  proof: by
  ext i
  simp only [liftFun, TruncatedWittVector.coeff_mk, WittVector.truncate_mk']
  rw [← f_compat (i + 1) n i.is_lt]; rw [RingHom.comp_apply]; rw [TruncatedWittVector.coeff_truncate]
  congr 1 with _

中文:
定理 truncate_liftFun
  条件: (s : S)
  结论: Witt向量.truncate n (liftFun f s) = f n s
  证明: by
  ext i
  simp only [liftFun, TruncatedWittVector.coeff_mk, WittVector.truncate_mk']
  rw [← f_compat (i + 1) n i.is_lt]; rw [RingHom.comp_apply]; rw [TruncatedWittVector.coeff_truncate]
  congr 1 with _

Depends on / 依赖: RingHom, RingHom.comp_apply, TruncatedWittVector, TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_truncate, WittVector, WittVector.truncate_mk, coeff_mk, coeff_truncate, comp_apply, f_compat, i.is_lt, is_lt, liftFun, truncate_mk
-/
theorem truncate_liftFun (s : S) : WittVector.truncate n (liftFun f s) = f n s := by
  ext i
  simp only [liftFun, TruncatedWittVector.coeff_mk, WittVector.truncate_mk']
  rw [← f_compat (i + 1) n i.is_lt]; rw [RingHom.comp_apply]; rw [TruncatedWittVector.coeff_truncate]
  congr 1 with _

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : S ->+* 𝕎 R
  body: by
  refine { toFun := liftFun f
           map_zero' := ?_
           map_one' := ?_
           map_add' := ?_
           map_mul' := ?_ } <;>
  ( intros
    rw [← sub_eq_zero]; rw [← Ideal.mem_bot]; rw [← iInf_ker_truncate]; rw [Ideal.mem_iInf]
    simp [RingHom.mem_ker, f_compat])

中文:
定义 lift
  签名: : S ->+* 𝕎 R
  定义体: by
  refine { toFun := liftFun f
           map_zero' := ?_
           map_one' := ?_
           map_add' := ?_
           map_mul' := ?_ } <;>
  ( intros
    rw [← sub_eq_zero]; rw [← Ideal.mem_bot]; rw [← iInf_ker_truncate]; rw [Ideal.mem_iInf]
    simp [RingHom.mem_ker, f_compat])

Depends on / 依赖: Ideal.mem_bot, Ideal.mem_iInf, RingHom, RingHom.mem_ker, f_compat, iInf_ker_truncate, intros, liftFun, map_add, map_mul, map_one, map_zero, mem_bot, mem_iInf, mem_ker, sub_eq_zero
-/
def lift : S ->+* 𝕎 R := by
  refine { toFun := liftFun f
           map_zero' := ?_
           map_one' := ?_
           map_add' := ?_
           map_mul' := ?_ } <;>
  ( intros
    rw [← sub_eq_zero]; rw [← Ideal.mem_bot]; rw [← iInf_ker_truncate]; rw [Ideal.mem_iInf]
    simp [RingHom.mem_ker, f_compat])

variable {f}

@[simp]
/--
theorem `truncate_lift` / 定理 `truncate_lift`

English:
theorem truncate_lift
  given: (s : S)
  statement: WittVector.truncate n (lift _ f_compat s) = f n s
  proof: truncate_liftFun _ f_compat s

@[simp]

中文:
定理 truncate_lift
  条件: (s : S)
  结论: Witt向量.truncate n (lift _ f_compat s) = f n s
  证明: truncate_liftFun _ f_compat s

@[simp]

Depends on / 依赖: f_compat, truncate_liftFun
-/
theorem truncate_lift (s : S) : WittVector.truncate n (lift _ f_compat s) = f n s :=
  truncate_liftFun _ f_compat s

@[simp]
/--
theorem `truncate_comp_lift` / 定理 `truncate_comp_lift`

English:
theorem truncate_comp_lift
  statement: (WittVector.truncate n).comp (lift _ f_compat) = f n
  proof: by
  ext1; rw [RingHom.comp_apply, truncate_lift]

中文:
定理 truncate_comp_lift
  结论: (Witt向量.truncate n).comp (lift _ f_compat) = f n
  证明: by
  ext1; rw [RingHom.comp_apply, truncate_lift]

Depends on / 依赖: RingHom, RingHom.comp_apply, comp_apply, truncate_lift
-/
theorem truncate_comp_lift : (WittVector.truncate n).comp (lift _ f_compat) = f n := by
  ext1; rw [RingHom.comp_apply, truncate_lift]

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (g : S ->+* 𝕎 R) (g_compat : forall k, (WittVector.truncate k).comp g = f k)
  proof: by
  ext1 x
  rw [← sub_eq_zero]; rw [← Ideal.mem_bot]; rw [← iInf_ker_truncate]; rw [Ideal.mem_iInf]
  intro i
  simp only [RingHom.mem_ker, g_compat, ← RingHom.comp_apply, truncate_comp_lift, map_sub, sub_self]

中文:
定理 lift_unique
  条件: (g : S ->+* 𝕎 R) (g_compat : 对任意 k, (Witt向量.truncate k).comp g = f k)
  证明: by
  ext1 x
  rw [← sub_eq_zero]; rw [← Ideal.mem_bot]; rw [← iInf_ker_truncate]; rw [Ideal.mem_iInf]
  intro i
  simp only [RingHom.mem_ker, g_compat, ← RingHom.comp_apply, truncate_comp_lift, map_sub, sub_self]

Depends on / 依赖: Ideal.mem_bot, Ideal.mem_iInf, RingHom, RingHom.comp_apply, RingHom.mem_ker, comp_apply, g_compat, iInf_ker_truncate, map_sub, mem_bot, mem_iInf, mem_ker, sub_eq_zero, sub_self, truncate_comp_lift
-/
theorem lift_unique (g : S ->+* 𝕎 R) (g_compat : forall k, (WittVector.truncate k).comp g = f k) :
    lift _ f_compat = g := by
  ext1 x
  rw [← sub_eq_zero]; rw [← Ideal.mem_bot]; rw [← iInf_ker_truncate]; rw [Ideal.mem_iInf]
  intro i
  simp only [RingHom.mem_ker, g_compat, ← RingHom.comp_apply, truncate_comp_lift, map_sub, sub_self]

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simps]
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: : { f : forall k, S ->+* TruncatedWittVector p k R // forall (k₁ k₂) (hk : k₁ <= k₂),
  body: lift f.1 f.2
  invFun g :=
    ⟨fun k => (truncate k).comp g, by
      intro _ _ h
      simp only [← RingHom.comp_assoc, truncate_comp_wittVector_truncate]⟩
  left_inv := by rintro ⟨f, hf⟩; simp only [truncate_comp_lift]
  right_inv _ := lift_unique _ _ fun _ => rfl

中文:
定义 liftEquiv
  签名: : { f : 对任意 k, S ->+* TruncatedWittVector p k R // 对任意 (k₁ k₂) (hk : k₁ <= k₂),
  定义体: lift f.1 f.2
  invFun g :=
    ⟨fun k => (truncate k).comp g, by
      intro _ _ h
      simp only [← RingHom.comp_assoc, truncate_comp_wittVector_truncate]⟩
  left_inv := by rintro ⟨f, hf⟩; simp only [truncate_comp_lift]
  right_inv _ := lift_unique _ _ fun _ => rfl
-/
def liftEquiv : { f : forall k, S ->+* TruncatedWittVector p k R // forall (k₁ k₂) (hk : k₁ <= k₂),
    (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁ } ≃ (S ->+* 𝕎 R) where
  toFun f := lift f.1 f.2
  invFun g :=
    ⟨fun k => (truncate k).comp g, by
      intro _ _ h
      simp only [← RingHom.comp_assoc, truncate_comp_wittVector_truncate]⟩
  left_inv := by rintro ⟨f, hf⟩; simp only [truncate_comp_lift]
  right_inv _ := lift_unique _ _ fun _ => rfl

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: (g₁ g₂ : S ->+* 𝕎 R) (h : forall k, (truncate k).comp g₁ = (truncate k).comp g₂)
  proof: liftEquiv.symm.injective Subtype.ext funext h

中文:
定理 hom_ext
  条件: (g₁ g₂ : S ->+* 𝕎 R) (h : 对任意 k, (truncate k).comp g₁ = (truncate k).comp g₂)
  证明: liftEquiv.symm.injective Subtype.ext funext h

Depends on / 依赖: Subtype, Subtype.ext, injective, liftEquiv, liftEquiv.symm.injective
-/
theorem hom_ext (g₁ g₂ : S ->+* 𝕎 R) (h : forall k, (truncate k).comp g₁ = (truncate k).comp g₂) :
    g₁ = g₂ :=
liftEquiv.symm.injective Subtype.ext funext h

end lift

end WittVector
