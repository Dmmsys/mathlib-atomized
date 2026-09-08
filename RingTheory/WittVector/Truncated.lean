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

variable {p : ℕ} (n : ℕ) (R : Type*)

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
/-
**TruncatedWittVector** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TruncatedWittVector (_ : Nat) (n : Nat) (R : Type*)
参数：_ : Nat；n : Nat；R : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A truncated Witt vector over `R` is a vector of elements of `R`,
i.e., the first `n` coefficients of a Witt vector.
We will define operations on this type that are compatible with the (untruncated
) Witt
vector operations.

`TruncatedWittVector p n R` takes a parameter `p : ℕ` that is not used in the de
finition.
In practice, this number `p` is assumed to be a prime number,
and under this assumption we construct a ring structure on `TruncatedWittVector 
p n R`.
(`TruncatedWittVector p₁ n R` and `TruncatedWittVector p₂ n R` are definitionall
y
equal as types but will have different ring operations.)
-/
def TruncatedWittVector (_ : ℕ) (n : ℕ) (R : Type*) :=
  Fin n → R
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p n : ℕ) (R : Type*) [Inhabited R] : Inhabited (TruncatedWittVector p n R) :=
  ⟨fun _ => default⟩

variable {n R}

namespace TruncatedWittVector

variable (p) in
/-- Create a `TruncatedWittVector` from a vector `x`. -/
/-
**TruncatedWittVector.mk** 是 Mathlib 中的一个定义，位于命名空间 `TruncatedWittVector`。
形式化陈述：mk (x : Fin n -> R) : TruncatedWittVector p n R
参数：x : Fin n -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `TruncatedWittVector` from a vector `x`.
-/
def mk (x : Fin n → R) : TruncatedWittVector p n R :=
  x

/-- `x.coeff i` is the `i`th entry of `x`. -/
/-
**TruncatedWittVector.coeff** 是 Mathlib 中的一个定义，位于命名空间 `TruncatedWittVector`。
形式化陈述：coeff (i : Fin n) (x : TruncatedWittVector p n R) : R
参数：i : Fin n；x : TruncatedWittVector p n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x.coeff i` is the `i`th entry of `x`.
-/
def coeff (i : Fin n) (x : TruncatedWittVector p n R) : R :=
  x i

@[ext]
/-
**TruncatedWittVector.ext** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`。
形式化陈述：ext {x y : TruncatedWittVector p n R} (h : forall i, x.coeff i = y.coeff i
) : x = y
参数：h : forall i, x.coeff i = y.coeff i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {x y : TruncatedWittVector p n R} (h : ∀ i, x.coeff i = y.coeff i) : x = y :=
  funext h

@[simp]
/-
**TruncatedWittVector.coeff_mk** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`。
形式化陈述：coeff_mk (x : Fin n -> R) (i : Fin n) : (mk p x).coeff i = x i
参数：x : Fin n -> R；i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_mk (x : Fin n → R) (i : Fin n) : (mk p x).coeff i = x i :=
  rfl

@[simp]
/-
**TruncatedWittVector.mk_coeff** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`。
形式化陈述：mk_coeff (x : TruncatedWittVector p n R) : (mk p fun i => x.coeff i) = x
参数：x : TruncatedWittVector p n R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.ext`：ext {x y : TruncatedWittVector p n R} (h : fora
ll i, x.coeff i = y.coeff i) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TruncatedWittVector.coeff_mk`：coeff_mk (x : Fin n -> R) (i : Fin n) : (m
k p x).coeff i = x i
-/
theorem mk_coeff (x : TruncatedWittVector p n R) : (mk p fun i => x.coeff i) = x := by
  ext i; rw [coeff_mk]

variable [CommRing R]

/-- We can turn a truncated Witt vector `x` into a Witt vector
by setting all coefficients after `x` to be 0.
-/
/-
**TruncatedWittVector.out** 是 Mathlib 中的一个定义，位于命名空间 `TruncatedWittVector`。
形式化陈述：out (x : TruncatedWittVector p n R) : 𝕎 R
参数：x : TruncatedWittVector p n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can turn a truncated Witt vector `x` into a Witt vector
by setting all coefficients after `x` to be 0.
-/
def out (x : TruncatedWittVector p n R) : 𝕎 R :=
  @WittVector.mk' p _ fun i => if h : i < n then x.coeff ⟨i, h⟩ else 0

@[simp]
/-
**TruncatedWittVector.coeff_out** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`。
形式化陈述：coeff_out (x : TruncatedWittVector p n R) (i : Fin n) : x.out.coeff i = x.
coeff i
参数：x : TruncatedWittVector p n R；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TruncatedWittVector.out.eq_1`：∀ {p n : ℕ} {R : Type u_1} [inst : CommRin
g R] (x : TruncatedWittVector p n R),   x.out = { coeff := fun i => if h : i < n
 then TruncatedWit…
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Fin.eta`：∀ {n : ℕ} (a : Fin n) (h : ↑a < n), ⟨↑a, h⟩ = a
-/
theorem coeff_out (x : TruncatedWittVector p n R) (i : Fin n) : x.out.coeff i = x.coeff i := by
  rw [out]; dsimp only; rw [dif_pos i.is_lt, Fin.eta]
/-
**TruncatedWittVector.out_injective** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVect
or`。
形式化陈述：out_injective : Injective (@out p n R _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.ext`：ext {x y : TruncatedWittVector p n R} (h : fora
ll i, x.coeff i = y.coeff i) : x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TruncatedWittVector.coeff_out`：coeff_out (x : TruncatedWittVector p n R)
 (i : Fin n) : x.out.coeff i = x.coeff i
· 使用定理 `WittVector.ext_iff`：∀ {p : ℕ} {R : Type u_1} {x y : WittVector p R}, x =
 y ↔ ∀ (n : ℕ), x.coeff n = y.coeff n
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

/-- `truncateFun n x` uses the first `n` entries of `x` to construct a `TruncatedWittVector`,
which has the same base `p` as `x`.
This function is bundled into a ring homomorphism in `WittVector.truncate` -/
/-
**WittVector.truncateFun** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：truncateFun (x : 𝕎 R) : TruncatedWittVector p n R
参数：x : 𝕎 R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`truncateFun n x` uses the first `n` entries of `x` to construct a `TruncatedWit
tVector`,
which has the same base `p` as `x`.
This function is bundled into a ring homomorphism in `WittVector.truncate`
-/
def truncateFun (x : 𝕎 R) : TruncatedWittVector p n R :=
  TruncatedWittVector.mk p fun i => x.coeff i

end

variable {n}

@[simp]
/-
**WittVector.coeff_truncateFun** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_truncateFun (x : 𝕎 R) (i : Fin n) : (truncateFun n x).coeff i = x.co
eff i
参数：x : 𝕎 R；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.truncateFun.eq_1`：∀ {p : ℕ} (n : ℕ) {R : Type u_1} (x : WittV
ector p R),   WittVector.truncateFun n x = TruncatedWittVector.mk p fun i => x.c
oeff ↑i
· 使用定理 `TruncatedWittVector.coeff_mk`：coeff_mk (x : Fin n -> R) (i : Fin n) : (m
k p x).coeff i = x i
-/
theorem coeff_truncateFun (x : 𝕎 R) (i : Fin n) : (truncateFun n x).coeff i = x.coeff i := by
  rw [truncateFun, TruncatedWittVector.coeff_mk]

variable [CommRing R]

@[simp]
/-
**WittVector.out_truncateFun** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：out_truncateFun (x : 𝕎 R) : (truncateFun n x).out = init n x
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `WittVector.coeff_truncateFun`：coeff_truncateFun (x : 𝕎 R) (i : Fin n) : 
(truncateFun n x).coeff i = x.coeff i
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem out_truncateFun (x : 𝕎 R) : (truncateFun n x).out = init n x := by
  ext i
  dsimp [TruncatedWittVector.out, init, select, coeff_mk]
  split_ifs with hi; swap; · rfl
  rw [coeff_truncateFun, Fin.val_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRing R]

@[simp]
/-
**TruncatedWittVector.truncateFun_out** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVe
ctor`。
形式化陈述：truncateFun_out (x : TruncatedWittVector p n R) : x.out.truncateFun n = x
参数：x : TruncatedWittVector p n R。
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
· 使用定理 `TruncatedWittVector.coeff_out`：coeff_out (x : TruncatedWittVector p n R)
 (i : Fin n) : x.out.coeff i = x.coeff i
· 使用定理 `TruncatedWittVector.mk_coeff`：mk_coeff (x : TruncatedWittVector p n R) :
 (mk p fun i => x.coeff i) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem truncateFun_out (x : TruncatedWittVector p n R) : x.out.truncateFun n = x := by
  simp only [WittVector.truncateFun, coeff_out, mk_coeff]

open WittVector

variable (p n R)
variable [Fact p.Prime]
/-
**TruncatedWittVector.** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (TruncatedWittVector p n R) :=
  ⟨truncateFun n 0⟩
/-
**TruncatedWittVector.** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (TruncatedWittVector p n R) :=
  ⟨truncateFun n 1⟩
/-
**TruncatedWittVector.** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (TruncatedWittVector p n R) :=
  ⟨fun i => truncateFun n i⟩
/-
**TruncatedWittVector.** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (TruncatedWittVector p n R) :=
  ⟨fun i => truncateFun n i⟩
/-
**TruncatedWittVector.** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out + y.out)⟩
/-
**TruncatedWittVector.** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out * y.out)⟩
/-
**TruncatedWittVector.** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (TruncatedWittVector p n R) :=
  ⟨fun x => truncateFun n (-x.out)⟩
/-
**TruncatedWittVector.** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (TruncatedWittVector p n R) :=
  ⟨fun x y => truncateFun n (x.out - y.out)⟩
/-
**TruncatedWittVector.hasNatScalar** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVecto
r`。
形式化陈述：hasNatScalar : SMul Nat (TruncatedWittVector p n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNatScalar : SMul ℕ (TruncatedWittVector p n R) :=
  ⟨fun m x => truncateFun n (m • x.out)⟩
/-
**TruncatedWittVector.hasIntScalar** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVecto
r`。
形式化陈述：hasIntScalar : SMul Int (TruncatedWittVector p n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasIntScalar : SMul ℤ (TruncatedWittVector p n R) :=
  ⟨fun m x => truncateFun n (m • x.out)⟩
/-
**TruncatedWittVector.hasNatPow** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
形式化陈述：hasNatPow : Pow (TruncatedWittVector p n R) Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNatPow : Pow (TruncatedWittVector p n R) ℕ :=
  ⟨fun x m => truncateFun n (x.out ^ m)⟩

@[simp]
/-
**TruncatedWittVector.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`
。
形式化陈述：coeff_zero (i : Fin n) : (0 : TruncatedWittVector p n R).coeff i = 0
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.coeff_truncateFun`：coeff_truncateFun (x : 𝕎 R) (i : Fin n) : 
(truncateFun n x).coeff i = x.coeff i
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
-/
theorem coeff_zero (i : Fin n) : (0 : TruncatedWittVector p n R).coeff i = 0 := by
  change coeff i (truncateFun _ 0 : TruncatedWittVector p n R) = 0
  rw [coeff_truncateFun, WittVector.zero_coeff]

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

/-
**WittVector.truncateFun_surjective** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_surjective : Surjective (@truncateFun p n R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `TruncatedWittVector.truncateFun_out`：truncateFun_out (x : TruncatedWittV
ector p n R) : x.out.truncateFun n = x
-/
theorem truncateFun_surjective : Surjective (@truncateFun p n R) :=
  Function.RightInverse.surjective TruncatedWittVector.truncateFun_out

variable [Fact p.Prime]

@[simp]
/-
**WittVector.truncateFun_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_zero : truncateFun n (0 : 𝕎 R) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem truncateFun_zero : truncateFun n (0 : 𝕎 R) = 0 := rfl

@[simp]
/-
**WittVector.truncateFun_one** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_one : truncateFun n (1 : 𝕎 R) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem truncateFun_one : truncateFun n (1 : 𝕎 R) = 1 := rfl

variable {p R}

@[simp]
/-
**WittVector.truncateFun_add** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_add (x y : 𝕎 R) : truncateFun n (x + y) = truncateFun n x + tr
uncateFun n y
参数：x y : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.out_injective`：out_injective : Injective (@out p n R
 _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.out_truncateFun`：out_truncateFun (x : 𝕎 R) : (truncateFun n x
).out = init n x
· 使用定理 `WittVector.init_add`：init_add (x y : 𝕎 R) (n : Nat) : init n (x + y) = i
nit n (init n x + init n y)
-/
theorem truncateFun_add (x y : 𝕎 R) :
    truncateFun n (x + y) = truncateFun n x + truncateFun n y := by
  witt_truncateFun_tac

@[simp]
/-
**WittVector.truncateFun_mul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_mul (x y : 𝕎 R) : truncateFun n (x * y) = truncateFun n x * tr
uncateFun n y
参数：x y : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.out_injective`：out_injective : Injective (@out p n R
 _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.out_truncateFun`：out_truncateFun (x : 𝕎 R) : (truncateFun n x
).out = init n x
· 使用定理 `WittVector.init_mul`：init_mul (x y : 𝕎 R) (n : Nat) : init n (x * y) = i
nit n (init n x * init n y)
-/
theorem truncateFun_mul (x y : 𝕎 R) :
    truncateFun n (x * y) = truncateFun n x * truncateFun n y := by
  witt_truncateFun_tac
/-
**WittVector.truncateFun_neg** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_neg (x : 𝕎 R) : truncateFun n (-x) = -truncateFun n x
参数：x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.out_injective`：out_injective : Injective (@out p n R
 _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.out_truncateFun`：out_truncateFun (x : 𝕎 R) : (truncateFun n x
).out = init n x
· 使用定理 `WittVector.init_neg`：init_neg (x : 𝕎 R) (n : Nat) : init n (-x) = init n
 (-init n x)
-/
theorem truncateFun_neg (x : 𝕎 R) : truncateFun n (-x) = -truncateFun n x := by
  witt_truncateFun_tac
/-
**WittVector.truncateFun_sub** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_sub (x y : 𝕎 R) : truncateFun n (x - y) = truncateFun n x - tr
uncateFun n y
参数：x y : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.out_injective`：out_injective : Injective (@out p n R
 _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.out_truncateFun`：out_truncateFun (x : 𝕎 R) : (truncateFun n x
).out = init n x
· 使用定理 `WittVector.init_sub`：init_sub (x y : 𝕎 R) (n : Nat) : init n (x - y) = i
nit n (init n x - init n y)
-/
theorem truncateFun_sub (x y : 𝕎 R) :
    truncateFun n (x - y) = truncateFun n x - truncateFun n y := by
  witt_truncateFun_tac
/-
**WittVector.truncateFun_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_nsmul (m : Nat) (x : 𝕎 R) : truncateFun n (m • x) = m • trunca
teFun n x
参数：m : Nat；x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.out_injective`：out_injective : Injective (@out p n R
 _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.out_truncateFun`：out_truncateFun (x : 𝕎 R) : (truncateFun n x
).out = init n x
· 使用定理 `WittVector.init_nsmul`：init_nsmul (m : Nat) (x : 𝕎 R) (n : Nat) : init n
 (m • x) = init n (m • init n x)
-/
theorem truncateFun_nsmul (m : ℕ) (x : 𝕎 R) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncateFun_tac
/-
**WittVector.truncateFun_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_zsmul (m : Int) (x : 𝕎 R) : truncateFun n (m • x) = m • trunca
teFun n x
参数：m : Int；x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.out_injective`：out_injective : Injective (@out p n R
 _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.out_truncateFun`：out_truncateFun (x : 𝕎 R) : (truncateFun n x
).out = init n x
· 使用定理 `WittVector.init_zsmul`：init_zsmul (m : Int) (x : 𝕎 R) (n : Nat) : init n
 (m • x) = init n (m • init n x)
-/
theorem truncateFun_zsmul (m : ℤ) (x : 𝕎 R) : truncateFun n (m • x) = m • truncateFun n x := by
  witt_truncateFun_tac
/-
**WittVector.truncateFun_pow** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_pow (x : 𝕎 R) (m : Nat) : truncateFun n (x ^ m) = truncateFun 
n x ^ m
参数：x : 𝕎 R；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.out_injective`：out_injective : Injective (@out p n R
 _)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.out_truncateFun`：out_truncateFun (x : 𝕎 R) : (truncateFun n x
).out = init n x
· 使用定理 `WittVector.init_pow`：init_pow (m : Nat) (x : 𝕎 R) (n : Nat) : init n (x 
^ m) = init n (init n x ^ m)
-/
theorem truncateFun_pow (x : 𝕎 R) (m : ℕ) : truncateFun n (x ^ m) = truncateFun n x ^ m := by
  witt_truncateFun_tac
/-
**WittVector.truncateFun_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_natCast (m : Nat) : truncateFun n (m : 𝕎 R) = m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem truncateFun_natCast (m : ℕ) : truncateFun n (m : 𝕎 R) = m := rfl
/-
**WittVector.truncateFun_intCast** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncateFun_intCast (m : Int) : truncateFun n (m : 𝕎 R) = m
参数：m : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem truncateFun_intCast (m : ℤ) : truncateFun n (m : 𝕎 R) = m := rfl

end WittVector

namespace TruncatedWittVector

open WittVector

variable (p n R)
variable [CommRing R]
variable [Fact p.Prime]

/-
**TruncatedWittVector.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVecto
r`。
形式化陈述：instCommRing : CommRing (TruncatedWittVector p n R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.truncateFun_surjective`：truncateFun_surjective : Surjective (
@truncateFun p n R)
· 使用定理 `WittVector.truncateFun_zero`：truncateFun_zero : truncateFun n (0 : 𝕎 R) 
= 0
· 使用定理 `WittVector.truncateFun_one`：truncateFun_one : truncateFun n (1 : 𝕎 R) = 
1
· 使用定理 `WittVector.truncateFun_add`：truncateFun_add (x y : 𝕎 R) : truncateFun n 
(x + y) = truncateFun n x + truncateFun n y
· 使用定理 `WittVector.truncateFun_mul`：truncateFun_mul (x y : 𝕎 R) : truncateFun n 
(x * y) = truncateFun n x * truncateFun n y
· 使用定理 `WittVector.truncateFun_neg`：truncateFun_neg (x : 𝕎 R) : truncateFun n (-
x) = -truncateFun n x
· 使用定理 `WittVector.truncateFun_sub`：truncateFun_sub (x y : 𝕎 R) : truncateFun n 
(x - y) = truncateFun n x - truncateFun n y
· 使用定理 `WittVector.truncateFun_nsmul`：truncateFun_nsmul (m : Nat) (x : 𝕎 R) : tr
uncateFun n (m • x) = m • truncateFun n x
· 使用定理 `WittVector.truncateFun_zsmul`：truncateFun_zsmul (m : Int) (x : 𝕎 R) : tr
uncateFun n (m • x) = m • truncateFun n x
· 使用定理 `WittVector.truncateFun_pow`：truncateFun_pow (x : 𝕎 R) (m : Nat) : trunca
teFun n (x ^ m) = truncateFun n x ^ m
· 使用定理 `WittVector.truncateFun_natCast`：truncateFun_natCast (m : Nat) : truncate
Fun n (m : 𝕎 R) = m
· 使用定理 `WittVector.truncateFun_intCast`：truncateFun_intCast (m : Int) : truncate
Fun n (m : 𝕎 R) = m
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

/-- `truncate n` is a ring homomorphism that truncates `x` to its first `n` entries
to obtain a `TruncatedWittVector`, which has the same base `p` as `x`. -/
/-
**WittVector.truncate** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：truncate : 𝕎 R ->+* TruncatedWittVector p n R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.truncateFun_one`：truncateFun_one : truncateFun n (1 : 𝕎 R) = 
1
· 使用定理 `WittVector.truncateFun_mul`：truncateFun_mul (x y : 𝕎 R) : truncateFun n 
(x * y) = truncateFun n x * truncateFun n y
· 使用定理 `WittVector.truncateFun_zero`：truncateFun_zero : truncateFun n (0 : 𝕎 R) 
= 0
· 使用定理 `WittVector.truncateFun_add`：truncateFun_add (x y : 𝕎 R) : truncateFun n 
(x + y) = truncateFun n x + truncateFun n y

--- 原说明 ---
`truncate n` is a ring homomorphism that truncates `x` to its first `n` entries
to obtain a `TruncatedWittVector`, which has the same base `p` as `x`.
-/
noncomputable def truncate : 𝕎 R →+* TruncatedWittVector p n R where
  toFun := truncateFun n
  map_zero' := truncateFun_zero p n R
  map_add' := truncateFun_add n
  map_one' := truncateFun_one p n R
  map_mul' := truncateFun_mul n

variable (p R)
/-
**WittVector.truncate_surjective** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncate_surjective : Surjective (truncate n : 𝕎 R -> TruncatedWittVector 
p n R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.truncateFun_surjective`：truncateFun_surjective : Surjective (
@truncateFun p n R)
-/
theorem truncate_surjective : Surjective (truncate n : 𝕎 R → TruncatedWittVector p n R) :=
  truncateFun_surjective p n R

variable {p n R}

@[simp]
/-
**WittVector.coeff_truncate** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：coeff_truncate (x : 𝕎 R) (i : Fin n) : (truncate n x).coeff i = x.coeff i
参数：x : 𝕎 R；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.coeff_truncateFun`：coeff_truncateFun (x : 𝕎 R) (i : Fin n) : 
(truncateFun n x).coeff i = x.coeff i
-/
theorem coeff_truncate (x : 𝕎 R) (i : Fin n) : (truncate n x).coeff i = x.coeff i :=
  coeff_truncateFun _ _

variable (n)
/-
**WittVector.mem_ker_truncate** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：mem_ker_truncate (x : 𝕎 R) : x in RingHom.ker (truncate (p
参数：x : 𝕎 R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.truncateFun_one`：truncateFun_one : truncateFun n (1 : 𝕎 R) = 
1
· 使用定理 `WittVector.truncateFun_mul`：truncateFun_mul (x y : 𝕎 R) : truncateFun n 
(x * y) = truncateFun n x * truncateFun n y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.truncateFun_zero`：truncateFun_zero : truncateFun n (0 : 𝕎 R) 
= 0
· 使用定理 `WittVector.truncateFun_add`：truncateFun_add (x y : 𝕎 R) : truncateFun n 
(x + y) = truncateFun n x + truncateFun n y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `TruncatedWittVector.coeff_zero`：coeff_zero (i : Fin n) : (0 : TruncatedW
ittVector p n R).coeff i = 0
· 使用定理 `Fin.forall_iff`：∀ {n : ℕ} {p : Fin n → Prop}, (∀ (i : Fin n), p i) ↔ ∀ (
i : ℕ) (h : i < n), p ⟨i, h⟩
-/
theorem mem_ker_truncate (x : 𝕎 R) :
    x ∈ RingHom.ker (truncate (p := p) n) ↔ ∀ i < n, x.coeff i = 0 := by
  simp only [RingHom.mem_ker, truncate, RingHom.coe_mk, TruncatedWittVector.ext_iff,
    coeff_zero]
  exact Fin.forall_iff

variable (p)

@[simp]
/-
**WittVector.truncate_mk'** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncate_mk' (f : Nat -> R) : truncate n (@mk' p _ f) = TruncatedWittVecto
r.mk _ fun k => f k
参数：f : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.ext`：ext {x y : TruncatedWittVector p n R} (h : fora
ll i, x.coeff i = y.coeff i) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.coeff_truncate`：coeff_truncate (x : 𝕎 R) (i : Fin n) : (trunc
ate n x).coeff i = x.coeff i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem truncate_mk' (f : ℕ → R) :
    truncate n (@mk' p _ f) = TruncatedWittVector.mk _ fun k => f k := by
  ext i
  simp only [coeff_truncate, TruncatedWittVector.coeff_mk]

end WittVector

namespace TruncatedWittVector

variable [CommRing R]

section
variable [Fact p.Prime]

/-- A ring homomorphism that truncates a truncated Witt vector of length `m` to
a truncated Witt vector of length `n`, for `n ≤ m`.
-/
/-
**TruncatedWittVector.truncate** 是 Mathlib 中的一个定义，位于命名空间 `TruncatedWittVector`。
形式化陈述：truncate {m : Nat} (hm : n <= m) : TruncatedWittVector p m R ->+* Truncate
dWittVector p n R
参数：hm : n <= m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.truncateFun_out`：truncateFun_out (x : TruncatedWittV
ector p n R) : x.out.truncateFun n = x

--- 原说明 ---
A ring homomorphism that truncates a truncated Witt vector of length `m` to
a truncated Witt vector of length `n`, for `n ≤ m`.
-/
def truncate {m : ℕ} (hm : n ≤ m) : TruncatedWittVector p m R →+* TruncatedWittVector p n R :=
  RingHom.liftOfRightInverse (WittVector.truncate m) out truncateFun_out
    ⟨WittVector.truncate n, by
      intro x
      simp only [WittVector.mem_ker_truncate]
      intro h i hi
      exact h i (lt_of_lt_of_le hi hm)⟩

@[simp]
/-
**TruncatedWittVector.truncate_comp_wittVector_truncate** 是 Mathlib 中的一个定理，位于命名空
间 `TruncatedWittVector`。
形式化陈述：truncate_comp_wittVector_truncate {m : Nat} (hm : n <= m) : (truncate (p
参数：hm : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.liftOfRightInverse_comp`：liftOfRightInverse_comp (hf : Function.
RightInverse f_inv f) (g : { g : A ->+* C // RingHom.ker f <= RingHom.ker g }) :
 (f.liftOfRightInvers…
· 使用定理 `TruncatedWittVector.truncateFun_out`：truncateFun_out (x : TruncatedWittV
ector p n R) : x.out.truncateFun n = x
-/
theorem truncate_comp_wittVector_truncate {m : ℕ} (hm : n ≤ m) :
    (truncate (p := p) (R := R) hm).comp (WittVector.truncate m) = WittVector.truncate n :=
  RingHom.liftOfRightInverse_comp _ _ _ _

@[simp]
/-
**TruncatedWittVector.truncate_wittVector_truncate** 是 Mathlib 中的一个定理，位于命名空间 `Tr
uncatedWittVector`。
形式化陈述：truncate_wittVector_truncate {m : Nat} (hm : n <= m) (x : 𝕎 R) : truncate 
hm (WittVector.truncate m x) = WittVector.truncate n x
参数：hm : n <= m；x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.liftOfRightInverse_comp_apply`：liftOfRightInverse_comp_apply (hf
 : Function.RightInverse f_inv f) (g : { g : A ->+* C // RingHom.ker f <= RingHo
m.ker g }) (x : A) : (f.lif…
· 使用定理 `TruncatedWittVector.truncateFun_out`：truncateFun_out (x : TruncatedWittV
ector p n R) : x.out.truncateFun n = x
-/
theorem truncate_wittVector_truncate {m : ℕ} (hm : n ≤ m) (x : 𝕎 R) :
    truncate hm (WittVector.truncate m x) = WittVector.truncate n x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

@[simp]
/-
**TruncatedWittVector.truncate_truncate** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWitt
Vector`。
形式化陈述：truncate_truncate {n₁ n₂ n₃ : Nat} (h1 : n₁ <= n₂) (h2 : n₂ <= n₃) (x : Tr
uncatedWittVector p n₃ R) : (truncate h1) (truncate h2 x) = truncate (h1.trans h
2) x
参数：h1 : n₁ <= n₂；h2 : n₂ <= n₃；x : TruncatedWittVector p n₃ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `WittVector.truncate_surjective`：truncate_surjective : Surjective (trunca
te n : 𝕎 R -> TruncatedWittVector p n R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TruncatedWittVector.truncate_wittVector_truncate`：truncate_wittVector_tr
uncate {m : Nat} (hm : n <= m) (x : 𝕎 R) : truncate hm (WittVector.truncate m x)
 = WittVector.truncate n x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem truncate_truncate {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃)
    (x : TruncatedWittVector p n₃ R) :
    (truncate h1) (truncate h2 x) = truncate (h1.trans h2) x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) n₃ R x
  simp only [truncate_wittVector_truncate]

@[simp]
/-
**TruncatedWittVector.truncate_comp** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVect
or`。
形式化陈述：truncate_comp {n₁ n₂ n₃ : Nat} (h1 : n₁ <= n₂) (h2 : n₂ <= n₃) : (truncate
 (p
参数：h1 : n₁ <= n₂；h2 : n₂ <= n₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TruncatedWittVector.truncate_truncate`：truncate_truncate {n₁ n₂ n₃ : Nat
} (h1 : n₁ <= n₂) (h2 : n₂ <= n₃) (x : TruncatedWittVector p n₃ R) : (truncate h
1) (truncate h2 x) = trunca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem truncate_comp {n₁ n₂ n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) :
    (truncate (p := p) (R := R) h1).comp (truncate h2) = truncate (h1.trans h2) := by
  ext1 x; simp only [truncate_truncate, Function.comp_apply, RingHom.coe_comp]
/-
**TruncatedWittVector.truncate_surjective** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWi
ttVector`。
形式化陈述：truncate_surjective {m : Nat} (hm : n <= m) : Surjective (truncate (p
参数：hm : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.truncate_surjective`：truncate_surjective : Surjective (trunca
te n : 𝕎 R -> TruncatedWittVector p n R)
· 使用定理 `TruncatedWittVector.truncate_wittVector_truncate`：truncate_wittVector_tr
uncate {m : Nat} (hm : n <= m) (x : 𝕎 R) : truncate hm (WittVector.truncate m x)
 = WittVector.truncate n x
-/
theorem truncate_surjective {m : ℕ} (hm : n ≤ m) : Surjective (truncate (p := p) (R := R) hm) := by
  intro x
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective (p := p) _ R x
  exact ⟨WittVector.truncate _ x, truncate_wittVector_truncate _ _⟩

@[simp]
/-
**TruncatedWittVector.coeff_truncate** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVec
tor`。
形式化陈述：coeff_truncate {m : Nat} (hm : n <= m) (i : Fin n) (x : TruncatedWittVecto
r p m R) : (truncate hm x).coeff i = x.coeff (Fin.castLE hm i)
参数：hm : n <= m；i : Fin n；x : TruncatedWittVector p m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.truncate_surjective`：truncate_surjective : Surjective (trunca
te n : 𝕎 R -> TruncatedWittVector p n R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TruncatedWittVector.truncate_wittVector_truncate`：truncate_wittVector_tr
uncate {m : Nat} (hm : n <= m) (x : 𝕎 R) : truncate hm (WittVector.truncate m x)
 = WittVector.truncate n x
· 使用定理 `WittVector.coeff_truncate`：coeff_truncate (x : 𝕎 R) (i : Fin n) : (trunc
ate n x).coeff i = x.coeff i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_truncate {m : ℕ} (hm : n ≤ m) (i : Fin n) (x : TruncatedWittVector p m R) :
    (truncate hm x).coeff i = x.coeff (Fin.castLE hm i) := by
  obtain ⟨y, rfl⟩ := @WittVector.truncate_surjective p _ _ _ _ x
  simp only [truncate_wittVector_truncate, WittVector.coeff_truncate, Fin.val_castLE]

end

section Fintype

/-
**TruncatedWittVector.** 是 Mathlib 中的一个实例，位于命名空间 `TruncatedWittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [Fintype R] : Fintype (TruncatedWittVector p n R) :=
  Pi.instFintype

variable (p n R)
/-
**TruncatedWittVector.card** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWittVector`。
形式化陈述：card {R : Type*} [Fintype R] : Fintype.card (TruncatedWittVector p n R) = 
Fintype.card R ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fun`：Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype 
β] : Fintype.card (α -> β) = Fintype.card β ^ Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card {R : Type*} [Fintype R] :
    Fintype.card (TruncatedWittVector p n R) = Fintype.card R ^ n := by
  simp only [TruncatedWittVector, Fintype.card_fin, Fintype.card_fun]

end Fintype

variable [Fact p.Prime]

/-
**TruncatedWittVector.iInf_ker_truncate** 是 Mathlib 中的一个定理，位于命名空间 `TruncatedWitt
Vector`。
形式化陈述：iInf_ker_truncate : ⨅ i : Nat, RingHom.ker (WittVector.truncate (p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem iInf_ker_truncate : ⨅ i : ℕ, RingHom.ker (WittVector.truncate (p := p) (R := R) i) = ⊥ := by
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
variable (f : ∀ k : ℕ, S →+* TruncatedWittVector p k R)
variable
  (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁)

variable (n)

/-- Given a family `fₖ : S → TruncatedWittVector p k R` and `s : S`, we produce a Witt vector by
defining the `k`th entry to be the final entry of `fₖ s`.
-/
/-
**WittVector.liftFun** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：liftFun (s : S) : 𝕎 R
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family `fₖ : S → TruncatedWittVector p k R` and `s : S`, we produce a Wi
tt vector by
defining the `k`th entry to be the final entry of `fₖ s`.
-/
def liftFun (s : S) : 𝕎 R :=
  @WittVector.mk' p _ fun k => TruncatedWittVector.coeff (Fin.last k) (f (k + 1) s)

variable {f} in
include f_compat in
@[simp]
/-
**WittVector.truncate_liftFun** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncate_liftFun (s : S) : WittVector.truncate n (liftFun f s) = f n s
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TruncatedWittVector.ext`：ext {x y : TruncatedWittVector p n R} (h : fora
ll i, x.coeff i = y.coeff i) : x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.truncate_mk'`：truncate_mk' (f : Nat -> R) : truncate n (@mk' 
p _ f) = TruncatedWittVector.mk _ fun k => f k
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `TruncatedWittVector.coeff_truncate`：coeff_truncate {m : Nat} (hm : n <= 
m) (i : Fin n) (x : TruncatedWittVector p m R) : (truncate hm x).coeff i = x.coe
ff (Fin.castLE hm i)
-/
theorem truncate_liftFun (s : S) : WittVector.truncate n (liftFun f s) = f n s := by
  ext i
  simp only [liftFun, TruncatedWittVector.coeff_mk, WittVector.truncate_mk']
  rw [← f_compat (i + 1) n i.is_lt, RingHom.comp_apply, TruncatedWittVector.coeff_truncate]
  congr 1 with _

/--
Given compatible ring homs from `S` into `TruncatedWittVector n` for each `n`, we can lift these
to a ring hom `S → 𝕎 R`.

`lift` defines the universal property of `𝕎 R` as the inverse limit of `TruncatedWittVector n`.
-/
/-
**WittVector.lift** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：lift : S ->+* 𝕎 R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given compatible ring homs from `S` into `TruncatedWittVector n` for each `n`, w
e can lift these
to a ring hom `S → 𝕎 R`.

`lift` defines the universal property of `𝕎 R` as the inverse limit of `Truncate
dWittVector n`.
-/
def lift : S →+* 𝕎 R := by
  refine { toFun := liftFun f
           map_zero' := ?_
           map_one' := ?_
           map_add' := ?_
           map_mul' := ?_ } <;>
  ( intros
    rw [← sub_eq_zero, ← Ideal.mem_bot, ← iInf_ker_truncate, Ideal.mem_iInf]
    simp [RingHom.mem_ker, f_compat])

variable {f}

@[simp]
/-
**WittVector.truncate_lift** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncate_lift (s : S) : WittVector.truncate n (lift _ f_compat s) = f n s
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.truncate_liftFun`：truncate_liftFun (s : S) : WittVector.trunc
ate n (liftFun f s) = f n s
-/
theorem truncate_lift (s : S) : WittVector.truncate n (lift _ f_compat s) = f n s :=
  truncate_liftFun _ f_compat s

@[simp]
/-
**WittVector.truncate_comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：truncate_comp_lift : (WittVector.truncate n).comp (lift _ f_compat) = f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `WittVector.truncate_lift`：truncate_lift (s : S) : WittVector.truncate n 
(lift _ f_compat s) = f n s
-/
theorem truncate_comp_lift : (WittVector.truncate n).comp (lift _ f_compat) = f n := by
  ext1; rw [RingHom.comp_apply, truncate_lift]

/-- The uniqueness part of the universal property of `𝕎 R`. -/
/-
**WittVector.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：lift_unique (g : S ->+* 𝕎 R) (g_compat : forall k, (WittVector.truncate k)
.comp g = f k) : lift _ f_compat = g
参数：g : S ->+* 𝕎 R；g_compat : forall k, (WittVector.truncate k).comp g = f k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `TruncatedWittVector.iInf_ker_truncate`：iInf_ker_truncate : ⨅ i : Nat, Ri
ngHom.ker (WittVector.truncate (p
· 使用定理 `Ideal.mem_iInf`：mem_iInf {ι : Sort*} {I : ι -> Ideal R} {x : R} : x in i
Inf I ↔ forall i, x in I i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WittVector.truncate_comp_lift`：truncate_comp_lift : (WittVector.truncate
 n).comp (lift _ f_compat) = f n
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The uniqueness part of the universal property of `𝕎 R`.
-/
theorem lift_unique (g : S →+* 𝕎 R) (g_compat : ∀ k, (WittVector.truncate k).comp g = f k) :
    lift _ f_compat = g := by
  ext1 x
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← iInf_ker_truncate, Ideal.mem_iInf]
  intro i
  simp only [RingHom.mem_ker, g_compat, ← RingHom.comp_apply, truncate_comp_lift, map_sub, sub_self]

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simps]
/-
**WittVector.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：liftEquiv : { f : forall k, S ->+* TruncatedWittVector p k R // forall (k₁
 k₂) (hk : k₁ <= k₂), (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁ } ≃ (
S ->+* 𝕎 R) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of `𝕎 R` as projective limit of truncated Witt vector rin
gs.
-/
def liftEquiv : { f : ∀ k, S →+* TruncatedWittVector p k R // ∀ (k₁ k₂) (hk : k₁ ≤ k₂),
    (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁ } ≃ (S →+* 𝕎 R) where
  toFun f := lift f.1 f.2
  invFun g :=
    ⟨fun k => (truncate k).comp g, by
      intro _ _ h
      simp only [← RingHom.comp_assoc, truncate_comp_wittVector_truncate]⟩
  left_inv := by rintro ⟨f, hf⟩; simp only [truncate_comp_lift]
  right_inv _ := lift_unique _ _ fun _ => rfl
/-
**WittVector.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：hom_ext (g₁ g₂ : S ->+* 𝕎 R) (h : forall k, (truncate k).comp g₁ = (trunca
te k).comp g₂) : g₁ = g₂
参数：g₁ g₂ : S ->+* 𝕎 R；h : forall k, (truncate k).comp g₁ = (truncate k).comp g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem hom_ext (g₁ g₂ : S →+* 𝕎 R) (h : ∀ k, (truncate k).comp g₁ = (truncate k).comp g₂) :
    g₁ = g₂ :=
  liftEquiv.symm.injective <| Subtype.ext <| funext h

end lift

end WittVector

