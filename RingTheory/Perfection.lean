/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Pi
public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.Algebra.CharP.Subring
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Ring Perfection and Tilt

In this file we define the perfection of a ring of characteristic p, and the tilt of a field
given a valuation to `ℝ≥0`.

## TODO

Define the valuation on the tilt, and define a characteristic predicate for the tilt.

-/

@[expose] public section


universe u₁ u₂ u₃ u₄

open scoped NNReal

/-- The perfection of a monoid `α`, defined to be the projective limit of `α` using the `p`-th
power maps `α → α` indexed by the natural numbers, implemented as
`{ f : ℕ → M | ∀ n, f (n + 1) ^ p = f n }`.

If `α` is a ring with characteristic `p` and `p` is prime, `Perfection α p` is also a ring. -/
/-
**Perfection** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Perfection (α : Type u₁) [Pow α Nat] (p : Nat) : Type u₁
参数：α : Type u₁；p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The perfection of a monoid `α`, defined to be the projective limit of `α` using 
the `p`-th
power maps `α → α` indexed by the natural numbers, implemented as
`{ f : ℕ → M | ∀ n, f (n + 1) ^ p = f n }`.

If `α` is a ring with characteristic `p` and `p` is prime, `Perfection α p` is a
lso a ring.
-/
def Perfection (α : Type u₁) [Pow α ℕ] (p : ℕ) : Type u₁ :=
  { f : ℕ → α // ∀ n, f (n + 1) ^ p = f n }

@[deprecated (since := "2026-03-03")] alias Ring.Perfection := Perfection

namespace Perfection

section CommMonoid

/-- `Perfection M p` as a submonoid of `ℕ → M`. -/
/-
**Perfection.submonoid** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：submonoid (M : Type*) [CommMonoid M] (p : Nat) : Submonoid (Nat -> M) wher
e carrier
参数：M : Type*；p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Perfection M p` as a submonoid of `ℕ → M`.
-/
def submonoid (M : Type*) [CommMonoid M] (p : ℕ) : Submonoid (ℕ → M) where
  carrier := { f | ∀ n, f (n + 1) ^ p = f n }
  one_mem' _ := one_pow _
  mul_mem' hf hg n := (mul_pow _ _ _).trans congr($(hf n) * $(hg n))

@[deprecated (since := "2026-03-03")]
alias _root_.Monoid.perfection := submonoid
/-
**Perfection.** 是 Mathlib 中的一个实例，位于命名空间 `Perfection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Type*) [CommMonoid M] (p : ℕ) : CommMonoid (Perfection M p) :=
  inferInstanceAs <| CommMonoid (submonoid M p)

variable (M : Type*) [CommMonoid M] (p : ℕ)

/-- The `n`-th coefficient of an element of the perfection. -/
/-
**Perfection.coeffMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：coeffMonoidHom (n : Nat) : Perfection M p ->* M where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th coefficient of an element of the perfection.
-/
def coeffMonoidHom (n : ℕ) : Perfection M p →* M where
  toFun f := f.1 n
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The `p`-th root of an element of the perfection. -/
/-
**Perfection.pthRootMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：pthRootMonoidHom : Perfection M p ->* Perfection M p where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `p`-th root of an element of the perfection.
-/
def pthRootMonoidHom : Perfection M p →* Perfection M p where
  toFun f := ⟨fun n => coeffMonoidHom M p (n + 1) f, fun _ => f.2 _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {M p}

-- To prioritize `Perfection.ext` for the ring case.
@[ext low]
/-
**Perfection.extMonoid** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：extMonoid {f g : Perfection M p} (h : forall n, coeffMonoidHom M p n f = c
oeffMonoidHom M p n g) : f = g
参数：h : forall n, coeffMonoidHom M p n f = coeffMonoidHom M p n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem extMonoid {f g : Perfection M p}
    (h : ∀ n, coeffMonoidHom M p n f = coeffMonoidHom M p n g) :
    f = g :=
  Subtype.ext <| funext h

@[simp]
/-
**Perfection.coeffMonoidHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeffMonoidHom_mk (f : Nat -> M) (hf) (n : Nat) : coeffMonoidHom M p n ⟨f,
 hf⟩ = f n
参数：f : Nat -> M；hf；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeffMonoidHom_mk (f : ℕ → M) (hf) (n : ℕ) : coeffMonoidHom M p n ⟨f, hf⟩ = f n := rfl
/-
**Perfection.coeffMonoidHom_pthRootMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Perfecti
on`。
形式化陈述：coeffMonoidHom_pthRootMonoidHom (f : Perfection M p) (n : Nat) : coeffMono
idHom M p n (pthRootMonoidHom M p f) = coeffMonoidHom M p (n + 1) f
参数：f : Perfection M p；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeffMonoidHom_pthRootMonoidHom (f : Perfection M p) (n : ℕ) :
    coeffMonoidHom M p n (pthRootMonoidHom M p f) = coeffMonoidHom M p (n + 1) f := rfl
attribute [local simp] coeffMonoidHom_pthRootMonoidHom
/-
**Perfection.coeffMonoidHom_pow_p** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeffMonoidHom_pow_p (f : Perfection M p) (n : Nat) : coeffMonoidHom M p (
n + 1) (f ^ p) = coeffMonoidHom M p n f
参数：f : Perfection M p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coeffMonoidHom_pow_p (f : Perfection M p) (n : ℕ) :
    coeffMonoidHom M p (n + 1) (f ^ p) = coeffMonoidHom M p n f := by
  rw [map_pow]; exact f.2 n

@[simp]
/-
**Perfection.coeffMonoidHom_pow_p'** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeffMonoidHom_pow_p' (f : Perfection M p) (n : Nat) : coeffMonoidHom M p 
(n + 1) f ^ p = coeffMonoidHom M p n f
参数：f : Perfection M p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coeffMonoidHom_pow_p' (f : Perfection M p) (n : ℕ) :
    coeffMonoidHom M p (n + 1) f ^ p = coeffMonoidHom M p n f :=
  f.2 n
/-
**Perfection.** 是 Mathlib 中的一个实例，位于命名空间 `Perfection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PerfectRing (Perfection M p) p where
  bijective_frobenius := Function.bijective_iff_has_inverse.mpr
    ⟨pthRootMonoidHom M p, fun x ↦ by ext; simp, fun x ↦ by ext; simp⟩

@[simp]
/-
**Perfection.pthRootMonoidHom_eq_powMulEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Per
fection`。
形式化陈述：pthRootMonoidHom_eq_powMulEquiv_symm : pthRootMonoidHom M p = (powMulEquiv
 (Perfection M p) p).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulEquiv.eq_symm_apply`：eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x 
↔ e y = x
· 使用定理 `Perfection.extMonoid`：extMonoid {f g : Perfection M p} (h : forall n, co
effMonoidHom M p n f = coeffMonoidHom M p n g) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `powMulEquiv_apply`：∀ (M : Type u_1) (p : ℕ) [inst : CommMonoid M] [inst_
1 : PerfectRing M p] (a : M), (powMulEquiv M p) a = a ^ p
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Perfection.coeffMonoidHom_pow_p'`：coeffMonoidHom_pow_p' (f : Perfection 
M p) (n : Nat) : coeffMonoidHom M p (n + 1) f ^ p = coeffMonoidHom M p n f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pthRootMonoidHom_eq_powMulEquiv_symm :
    pthRootMonoidHom M p = (powMulEquiv (Perfection M p) p).symm :=
  MonoidHom.ext fun x ↦ (MulEquiv.eq_symm_apply _).mpr <| by ext; simp
/-
**Perfection.coe_pthRootMonoidHom_eq_powMulEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 
`Perfection`。
形式化陈述：coe_pthRootMonoidHom_eq_powMulEquiv_symm : ⇑(pthRootMonoidHom M p) = (powM
ulEquiv (Perfection M p) p).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Perfection.pthRootMonoidHom_eq_powMulEquiv_symm`：pthRootMonoidHom_eq_pow
MulEquiv_symm : pthRootMonoidHom M p = (powMulEquiv (Perfection M p) p).symm
-/
theorem coe_pthRootMonoidHom_eq_powMulEquiv_symm :
    ⇑(pthRootMonoidHom M p) = (powMulEquiv (Perfection M p) p).symm :=
  congr($pthRootMonoidHom_eq_powMulEquiv_symm)
/-
**Perfection.coeffMonoidHom_symm_powMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Perfecti
on`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {p : ℕ} (f : Perfection M p) (n : ℕ
),   (Perfection.coeffMonoidHom M p n) ((powMulEquiv (Perfection M p) p).symm f)
 =     (Perfection.coeffMonoidHom M p (n + 1)) f
参数：f : Perfection M p；n : ℕ；Perfection.coeffMonoidHom M p n；(powMulEquiv (Perfec
tion M p) p).symm f；Perfection.coeffMonoidHom M p (n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Perfection.coe_pthRootMonoidHom_eq_powMulEquiv_symm`：coe_pthRootMonoidHo
m_eq_powMulEquiv_symm : ⇑(pthRootMonoidHom M p) = (powMulEquiv (Perfection M p) 
p).symm
-/
@[simp] theorem coeffMonoidHom_symm_powMulEquiv (f : Perfection M p) (n : ℕ) :
    coeffMonoidHom M p n ((powMulEquiv _ p).symm f) = coeffMonoidHom M p (n + 1) f := by
  rw [← coe_pthRootMonoidHom_eq_powMulEquiv_symm]; rfl
/-
**Perfection.coeffMonoidHom_iterate_symm_powMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `
Perfection`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {p : ℕ} (f : Perfection M p) (n m :
 ℕ),   (Perfection.coeffMonoidHom M p n) ((⇑(powMulEquiv (Perfection M p) p).sym
m)^[m] f) =     (Perfection.coeffMonoidHom M p (n + m)) f
参数：f : Perfection M p；n m : ℕ；Perfection.coeffMonoidHom M p n；(⇑(powMulEquiv (Pe
rfection M p) p).symm)^[m] f；Perfection.coeffMonoidHom M p (n + m)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Perfection.coeffMonoidHom_symm_powMulEquiv`：∀ {M : Type u_1} [inst : Com
mMonoid M] {p : ℕ} (f : Perfection M p) (n : ℕ),   (Perfection.coeffMonoidHom M 
p n) ((powMulEquiv (Perfection M…
-/
@[simp] theorem coeffMonoidHom_iterate_symm_powMulEquiv (f : Perfection M p) (n m : ℕ) :
    coeffMonoidHom M p n ((powMulEquiv _ p).symm^[m] f) = coeffMonoidHom M p (n + m) f := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', coeffMonoidHom_symm_powMulEquiv, ih]
    grind
/-
**Perfection.coeffMonoidHom_pow_p_pow** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeffMonoidHom_pow_p_pow (f : Perfection M p) (m n : Nat) : coeffMonoidHom
 M p (m + n) (f ^ p ^ n) = coeffMonoidHom M p m f
参数：f : Perfection M p；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `Perfection.coeffMonoidHom_pow_p`：coeffMonoidHom_pow_p (f : Perfection M 
p) (n : Nat) : coeffMonoidHom M p (n + 1) (f ^ p) = coeffMonoidHom M p n f
-/
theorem coeffMonoidHom_pow_p_pow (f : Perfection M p) (m n : ℕ) :
    coeffMonoidHom M p (m + n) (f ^ p ^ n) = coeffMonoidHom M p m f :=
  n.recOn (by simp) fun n ih ↦ by rw [pow_succ, pow_mul, Nat.add_succ, coeffMonoidHom_pow_p, ih]

@[simp]
/-
**Perfection.coeffMonoidHom_pow_p_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeffMonoidHom_pow_p_pow' (f : Perfection M p) (m n : Nat) : coeffMonoidHo
m M p (m + n) f ^ p ^ n = coeffMonoidHom M p m f
参数：f : Perfection M p；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Perfection.coeffMonoidHom_pow_p_pow`：coeffMonoidHom_pow_p_pow (f : Perfe
ction M p) (m n : Nat) : coeffMonoidHom M p (m + n) (f ^ p ^ n) = coeffMonoidHom
 M p m f
-/
theorem coeffMonoidHom_pow_p_pow' (f : Perfection M p) (m n : ℕ) :
    coeffMonoidHom M p (m + n) f ^ p ^ n = coeffMonoidHom M p m f := by
  rw [← map_pow, coeffMonoidHom_pow_p_pow]

@[simp]
/-
**Perfection.coeffMonoidHom_pow_p_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Perfection
`。
形式化陈述：coeffMonoidHom_pow_p_pow_self (f : Perfection M p) (n : Nat) : coeffMonoid
Hom M p n f ^ p ^ n = coeffMonoidHom M p 0 f
参数：f : Perfection M p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Perfection.coeffMonoidHom_pow_p_pow'`：coeffMonoidHom_pow_p_pow' (f : Per
fection M p) (m n : Nat) : coeffMonoidHom M p (m + n) f ^ p ^ n = coeffMonoidHom
 M p m f
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem coeffMonoidHom_pow_p_pow_self (f : Perfection M p) (n : ℕ) :
    coeffMonoidHom M p n f ^ p ^ n = coeffMonoidHom M p 0 f := by
  rw [← coeffMonoidHom_pow_p_pow' _ 0 n, zero_add]
/-
**Perfection.coeffMonoidHom_powMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeffMonoidHom_powMonoidHom (f : Perfection M p) (n : Nat) : coeffMonoidHo
m M p (n + 1) (powMonoidHom p f) = coeffMonoidHom M p n f
参数：f : Perfection M p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeffMonoidHom_pow_p`：coeffMonoidHom_pow_p (f : Perfection M 
p) (n : Nat) : coeffMonoidHom M p (n + 1) (f ^ p) = coeffMonoidHom M p n f
-/
theorem coeffMonoidHom_powMonoidHom (f : Perfection M p) (n : ℕ) :
    coeffMonoidHom M p (n + 1) (powMonoidHom p f) = coeffMonoidHom M p n f :=
  coeffMonoidHom_pow_p f n
/-
**Perfection.coeffMonoidHom_iterate_powMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Perf
ection`。
形式化陈述：coeffMonoidHom_iterate_powMonoidHom (f : Perfection M p) (n m : Nat) : coe
ffMonoidHom M p (n + m) ((powMonoidHom p)^[m] f) = coeffMonoidHom M p n f
参数：f : Perfection M p；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `Perfection.coeffMonoidHom_powMonoidHom`：coeffMonoidHom_powMonoidHom (f :
 Perfection M p) (n : Nat) : coeffMonoidHom M p (n + 1) (powMonoidHom p f) = coe
ffMonoidHom M p n f
-/
theorem coeffMonoidHom_iterate_powMonoidHom (f : Perfection M p) (n m : ℕ) :
    coeffMonoidHom M p (n + m) ((powMonoidHom p)^[m] f) = coeffMonoidHom M p n f :=
  m.recOn rfl fun m ih ↦ by
    rw [Function.iterate_succ_apply', Nat.add_succ, coeffMonoidHom_powMonoidHom, ih]
/-
**Perfection.coeffMonoidHom_iterate_powMonoidHom'** 是 Mathlib 中的一个定理，位于命名空间 `Per
fection`。
形式化陈述：coeffMonoidHom_iterate_powMonoidHom' (f : Perfection M p) (n m : Nat) (hmn
 : m <= n) : coeffMonoidHom M p n ((powMonoidHom p)^[m] f) = coeffMonoidHom M p 
(n - m) f
参数：f : Perfection M p；n m : Nat；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Perfection.coeffMonoidHom_iterate_powMonoidHom`：coeffMonoidHom_iterate_p
owMonoidHom (f : Perfection M p) (n m : Nat) : coeffMonoidHom M p (n + m) ((powM
onoidHom p)^[m] f) = coeffMonoidHom …
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
theorem coeffMonoidHom_iterate_powMonoidHom' (f : Perfection M p) (n m : ℕ) (hmn : m ≤ n) :
    coeffMonoidHom M p n ((powMonoidHom p)^[m] f) = coeffMonoidHom M p (n - m) f := by
  rw [← coeffMonoidHom_iterate_powMonoidHom f (n - m) m, Nat.sub_add_cancel hmn]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given monoids `M` and `N`, with `M` being perfect,
any homomorphism `M →+* N` can be lifted uniquely to a homomorphism `M →* Perfection N p`. -/
@[simps! symm_apply]
/-
**Perfection.liftMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：liftMonoidHom (p : Nat) (M : Type*) [CommMonoid M] [PerfectRing M p] (N : 
Type*) [CommMonoid N] : (M ->* N) ≃* (M ->* Perfection N p) where toFun f
参数：p : Nat；M : Type*；N : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given monoids `M` and `N`, with `M` being perfect,
any homomorphism `M →+* N` can be lifted uniquely to a homomorphism `M →* Perfec
tion N p`.
-/
noncomputable def liftMonoidHom (p : ℕ) (M : Type*) [CommMonoid M] [PerfectRing M p]
    (N : Type*) [CommMonoid N] : (M →* N) ≃* (M →* Perfection N p) where
  toFun f :=
    { toFun r := ⟨fun n ↦ f ((powMulEquiv M (p ^ n)).symm r), fun n ↦ by
        rw [← map_pow, powMulEquiv_pow, pow_succ, MulAut.mul_def, MulEquiv.symm_trans_apply,
          powMulEquiv_symm_pow_p, ← powMulEquiv_pow]⟩
      map_one' := extMonoid fun _ ↦ by simp_rw [coeffMonoidHom_mk, map_one]
      map_mul' x y := extMonoid fun _ ↦ by simp_rw [map_mul, coeffMonoidHom_mk] }
  invFun := (coeffMonoidHom N p 0).comp
  left_inv f := by ext; simp
  right_inv f := by
    ext m n
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      coeffMonoidHom_mk]
    rw [← coeffMonoidHom_pow_p_pow _ 0 n, ← map_pow, powMulEquiv_symm_pow_p, zero_add]
  map_mul' _ _ := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**Perfection.coeffMonoidHom_zero_liftMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Perfec
tion`。
形式化陈述：∀ (p : ℕ) {M : Type u_2} {N : Type u_3} [inst : CommMonoid M] [inst_1 : Pe
rfectRing M p] [inst_2 : CommMonoid N]   (e : M →* N) (x : M), (Perfection.coeff
MonoidHom N p 0) (((Perfection.liftMonoidHom p M N) e) x) = e x
参数：p : ℕ；e : M →* N；x : M；Perfection.coeffMonoidHom N p 0；((Perfection.liftMonoi
dHom p M N) e) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `powMulEquiv.congr_simp`：∀ (M : Type u_1) (p p_1 : ℕ) (e_p : p = p_1) [in
st : CommMonoid M] [inst_1 : PerfectRing M p],   powMulEquiv M p = powMulEquiv M
 p_1
· 使用定理 `powMulEquiv_one`：∀ (M : Type u_1) [inst : CommMonoid M], powMulEquiv M 1
 = MulEquiv.refl M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coeffMonoidHom_zero_liftMonoidHom
    (p : ℕ) {M N : Type*} [CommMonoid M] [PerfectRing M p] [CommMonoid N] (e : M →* N) (x : M) :
    coeffMonoidHom N p 0 (liftMonoidHom p M N e x) = e x := by simp [liftMonoidHom]

set_option backward.isDefEq.respectTransparency.types false in
/-- A monoid homomorphism `M →* N` induces `Perfection M p →* Perfection N p`. -/
/-
**Perfection.mapMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：mapMonoidHom (p : Nat) {M N : Type*} [CommMonoid M] [CommMonoid N] (φ : M 
->* N) : Perfection M p ->* Perfection N p where toFun f
参数：p : Nat；φ : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoid homomorphism `M →* N` induces `Perfection M p →* Perfection N p`.
-/
def mapMonoidHom (p : ℕ) {M N : Type*} [CommMonoid M] [CommMonoid N] (φ : M →* N) :
    Perfection M p →* Perfection N p where
  toFun f := ⟨fun n ↦ φ (f.coeffMonoidHom M p n), fun n ↦ by rw [← map_pow, coeffMonoidHom_pow_p']⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
/-
**Perfection.coeffMonoidHom_mapMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeffMonoidHom_mapMonoidHom (p : Nat) {M N : Type*} [CommMonoid M] [CommMo
noid N] (φ : M ->* N) (f : Perfection M p) (n : Nat) : coeffMonoidHom N p n (map
MonoidHom p φ f) = φ (coeffMonoidHom M p n f)
参数：p : Nat；φ : M ->* N；f : Perfection M p；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeffMonoidHom_mapMonoidHom (p : ℕ) {M N : Type*} [CommMonoid M] [CommMonoid N]
    (φ : M →* N) (f : Perfection M p) (n : ℕ) :
    coeffMonoidHom N p n (mapMonoidHom p φ f) = φ (coeffMonoidHom M p n f) := rfl

end CommMonoid

section CommSemiring

/-- `Perfection R p` as a subsemiring of `ℕ → R`. -/
/-
**Perfection.subsemiring** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：subsemiring (R : Type*) [CommSemiring R] (p : Nat) [hp : Fact p.Prime] [Ch
arP R p] : Subsemiring (Nat -> R) where __
参数：R : Type*；p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Perfection R p` as a subsemiring of `ℕ → R`.
-/
def subsemiring (R : Type*) [CommSemiring R] (p : ℕ) [hp : Fact p.Prime] [CharP R p] :
    Subsemiring (ℕ → R) where
  __ := submonoid R p
  zero_mem' _ := zero_pow hp.1.ne_zero
  add_mem' hf hg n := (map_add (frobenius R p) _ _).trans congr($(hf n) + $(hg n))

@[deprecated (since := "2026-03-03")]
alias _root_.Ring.perfectionSubsemiring := subsemiring

variable (R : Type*) [CommSemiring R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
/-
**Perfection.** 是 Mathlib 中的一个实例，位于命名空间 `Perfection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring (Perfection R p) :=
  inferInstanceAs <| CommSemiring (subsemiring R p)
/-
**Perfection.** 是 Mathlib 中的一个实例，位于命名空间 `Perfection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CharP (Perfection R p) p :=
  CharP.subsemiring _ _ (subsemiring R p)

/-- The `n`-th coefficient of an element of the perfection. -/
/-
**Perfection.coeff** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：coeff (n : Nat) : Perfection R p ->+* R where __
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th coefficient of an element of the perfection.
-/
def coeff (n : ℕ) : Perfection R p →+* R where
  __ := coeffMonoidHom R p n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `p`-th root of an element of the perfection.

The preferred way to use this is `(frobeniusEquiv (Perfection R p) p).symm`. -/
/-
**Perfection.pthRoot** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：pthRoot : Perfection R p ->+* Perfection R p where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `p`-th root of an element of the perfection.

The preferred way to use this is `(frobeniusEquiv (Perfection R p) p).symm`.
-/
def pthRoot : Perfection R p →+* Perfection R p where
  __ := pthRootMonoidHom R p
  map_zero' := rfl
  map_add' _ _ := rfl

variable {R p}

@[ext]
/-
**Perfection.ext** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：ext {f g : Perfection R p} (h : forall n, coeff R p n f = coeff R p n g) :
 f = g
参数：h : forall n, coeff R p n f = coeff R p n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.extMonoid`：extMonoid {f g : Perfection M p} (h : forall n, co
effMonoidHom M p n f = coeffMonoidHom M p n g) : f = g
-/
theorem ext {f g : Perfection R p} (h : ∀ n, coeff R p n f = coeff R p n g) : f = g :=
  extMonoid h
/-
**Perfection.pthRoot_eq_symm_frobeniusEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Perfectio
n`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {p : ℕ} [hp : Fact (Nat.Prime p)]
 [inst_1 : CharP R p],   Perfection.pthRoot R p = ↑(frobeniusEquiv (Perfection R
 p) p).symm
参数：Nat.Prime p；frobeniusEquiv (Perfection R p) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Perfection.instCharP`：∀ (R : Type u_1) [inst : CommSemiring R] (p : ℕ) [
hp : Fact (Nat.Prime p)] [inst_1 : CharP R p],   CharP (Perfection R p) p
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frobeniusEquiv_apply`：∀ (R : Type u_1) (p : ℕ) [inst : CommSemiring R] [
inst_1 : ExpChar R p] [inst_2 : PerfectRing R p] (a : R),   (frobeniusEquiv R p)
 a = (frob…
· 使用定理 `Perfection.ext`：ext {f g : Perfection R p} (h : forall n, coeff R p n f 
= coeff R p n g) : f = g
· 使用定理 `Perfection.coeffMonoidHom_pow_p'`：coeffMonoidHom_pow_p' (f : Perfection 
M p) (n : Nat) : coeffMonoidHom M p (n + 1) f ^ p = coeffMonoidHom M p n f
-/
@[simp] lemma pthRoot_eq_symm_frobeniusEquiv :
    pthRoot R p = RingHomClass.toRingHom (frobeniusEquiv _ p).symm := by
  ext : 1
  simpa [RingEquiv.eq_symm_apply] using ext <| coeffMonoidHom_pow_p' _
/-
**Perfection.coe_pthRoot_eq_symm_frobeniusEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Perfe
ction`。
形式化陈述：coe_pthRoot_eq_symm_frobeniusEquiv : ⇑(pthRoot R p) = (frobeniusEquiv _ p)
.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.instCharP`：∀ (R : Type u_1) [inst : CommSemiring R] (p : ℕ) [
hp : Fact (Nat.Prime p)] [inst_1 : CharP R p],   CharP (Perfection R p) p
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Perfection.pthRoot_eq_symm_frobeniusEquiv`：∀ {R : Type u_1} [inst : Comm
Semiring R] {p : ℕ} [hp : Fact (Nat.Prime p)] [inst_1 : CharP R p],   Perfection
.pthRoot R p = ↑(frobeniusEquiv…
-/
lemma coe_pthRoot_eq_symm_frobeniusEquiv : ⇑(pthRoot R p) = (frobeniusEquiv _ p).symm :=
  congr($pthRoot_eq_symm_frobeniusEquiv)
/-
**Perfection.coeffMonoidHom_eq_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {p : ℕ} [hp : Fact (Nat.Prime p)]
 [inst_1 : CharP R p] (n : ℕ),   ⇑(Perfection.coeffMonoidHom R p n) = ⇑(Perfecti
on.coeff R p n)
参数：Nat.Prime p；n : ℕ；Perfection.coeffMonoidHom R p n；Perfection.coeff R p n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coeffMonoidHom_eq_coeff (n : ℕ) : ⇑(coeffMonoidHom R p n) = coeff R p n := rfl
/-
**Perfection.pthRootMonoidHom_eq_pthRoot** 是 Mathlib 中的一个引理，位于命名空间 `Perfection`。
形式化陈述：pthRootMonoidHom_eq_pthRoot : ⇑(pthRootMonoidHom R p) = pthRoot R p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pthRootMonoidHom_eq_pthRoot : ⇑(pthRootMonoidHom R p) = pthRoot R p := rfl
/-
**Perfection.pthRootMonoidHom_eq_symm_frobeniusEquiv** 是 Mathlib 中的一个引理，位于命名空间 `
Perfection`。
形式化陈述：pthRootMonoidHom_eq_symm_frobeniusEquiv : ⇑(pthRootMonoidHom R p) = RingHo
mClass.toRingHom (frobeniusEquiv _ p).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Perfection.instCharP`：∀ (R : Type u_1) [inst : CommSemiring R] (p : ℕ) [
hp : Fact (Nat.Prime p)] [inst_1 : CharP R p],   CharP (Perfection R p) p
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Perfection.pthRootMonoidHom_eq_powMulEquiv_symm`：pthRootMonoidHom_eq_pow
MulEquiv_symm : pthRootMonoidHom M p = (powMulEquiv (Perfection M p) p).symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pthRootMonoidHom_eq_symm_frobeniusEquiv :
    ⇑(pthRootMonoidHom R p) = RingHomClass.toRingHom (frobeniusEquiv _ p).symm := by
  simp
/-
**Perfection.coeff_toMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `Perfection`。
形式化陈述：coeff_toMonoidHom (n : Nat) : (coeff R p n).toMonoidHom = coeffMonoidHom R
 p n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_toMonoidHom (n : ℕ) : (coeff R p n).toMonoidHom = coeffMonoidHom R p n := rfl

@[simp]
/-
**Perfection.coeff_mk** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_mk (f : Nat -> R) (hf) (n : Nat) : coeff R p n ⟨f, hf⟩ = f n
参数：f : Nat -> R；hf；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_mk (f : ℕ → R) (hf) (n : ℕ) : coeff R p n ⟨f, hf⟩ = f n := rfl

@[simp]
/-
**Perfection.coeff_symm_frobeniusEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_symm_frobeniusEquiv (f : Perfection R p) (n : Nat) : coeff R p n ((f
robeniusEquiv _ p).symm f) = coeff R p (n + 1) f
参数：f : Perfection R p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeffMonoidHom_symm_powMulEquiv`：∀ {M : Type u_1} [inst : Com
mMonoid M] {p : ℕ} (f : Perfection M p) (n : ℕ),   (Perfection.coeffMonoidHom M 
p n) ((powMulEquiv (Perfection M…
-/
theorem coeff_symm_frobeniusEquiv (f : Perfection R p) (n : ℕ) :
    coeff R p n ((frobeniusEquiv _ p).symm f) = coeff R p (n + 1) f :=
  coeffMonoidHom_symm_powMulEquiv ..

@[simp]
/-
**Perfection.coeff_iterate_symm_frobeniusEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Perfec
tion`。
形式化陈述：coeff_iterate_symm_frobeniusEquiv (f : Perfection R p) (n m : Nat) : coeff
 R p n ((frobeniusEquiv _ p).symm^[m] f) = coeff R p (n + m) f
参数：f : Perfection R p；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeffMonoidHom_iterate_symm_powMulEquiv`：∀ {M : Type u_1} [in
st : CommMonoid M] {p : ℕ} (f : Perfection M p) (n m : ℕ),   (Perfection.coeffMo
noidHom M p n) ((⇑(powMulEquiv (Perfecti…
-/
theorem coeff_iterate_symm_frobeniusEquiv (f : Perfection R p) (n m : ℕ) :
    coeff R p n ((frobeniusEquiv _ p).symm^[m] f) = coeff R p (n + m) f :=
  coeffMonoidHom_iterate_symm_powMulEquiv ..
/-
**Perfection.coeff_pow_p** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_pow_p (f : Perfection R p) (n : Nat) : coeff R p (n + 1) (f ^ p) = c
oeff R p n f
参数：f : Perfection R p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeffMonoidHom_pow_p`：coeffMonoidHom_pow_p (f : Perfection M 
p) (n : Nat) : coeffMonoidHom M p (n + 1) (f ^ p) = coeffMonoidHom M p n f
-/
theorem coeff_pow_p (f : Perfection R p) (n : ℕ) :
    coeff R p (n + 1) (f ^ p) = coeff R p n f := coeffMonoidHom_pow_p f n

@[simp]
/-
**Perfection.coeff_pow_p'** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_pow_p' (f : Perfection R p) (n : Nat) : coeff R p (n + 1) f ^ p = co
eff R p n f
参数：f : Perfection R p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coeff_pow_p' (f : Perfection R p) (n : ℕ) : coeff R p (n + 1) f ^ p = coeff R p n f :=
  f.2 n

@[simp]
/-
**Perfection.coeff_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_frobenius (f : Perfection R p) (n : Nat) : coeff R p (n + 1) (froben
ius _ p f) = coeff R p n f
参数：f : Perfection R p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeffMonoidHom_powMonoidHom`：coeffMonoidHom_powMonoidHom (f :
 Perfection M p) (n : Nat) : coeffMonoidHom M p (n + 1) (powMonoidHom p f) = coe
ffMonoidHom M p n f
-/
theorem coeff_frobenius (f : Perfection R p) (n : ℕ) :
    coeff R p (n + 1) (frobenius _ p f) = coeff R p n f := coeffMonoidHom_powMonoidHom f n

@[simp]
/-
**Perfection.coeff_iterate_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_iterate_frobenius (f : Perfection R p) (n m : Nat) : coeff R p (n + 
m) ((frobenius _ p)^[m] f) = coeff R p n f
参数：f : Perfection R p；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeffMonoidHom_iterate_powMonoidHom`：coeffMonoidHom_iterate_p
owMonoidHom (f : Perfection M p) (n m : Nat) : coeffMonoidHom M p (n + m) ((powM
onoidHom p)^[m] f) = coeffMonoidHom …
-/
theorem coeff_iterate_frobenius (f : Perfection R p) (n m : ℕ) :
    coeff R p (n + m) ((frobenius _ p)^[m] f) = coeff R p n f :=
  coeffMonoidHom_iterate_powMonoidHom ..
/-
**Perfection.coeff_iterate_frobenius'** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_iterate_frobenius' (f : Perfection R p) (n m : Nat) (hmn : m <= n) :
 coeff R p n ((frobenius _ p)^[m] f) = coeff R p (n - m) f
参数：f : Perfection R p；n m : Nat；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeffMonoidHom_iterate_powMonoidHom'`：coeffMonoidHom_iterate_
powMonoidHom' (f : Perfection M p) (n m : Nat) (hmn : m <= n) : coeffMonoidHom M
 p n ((powMonoidHom p)^[m] f) = coeff…
-/
theorem coeff_iterate_frobenius' (f : Perfection R p) (n m : ℕ) (hmn : m ≤ n) :
    coeff R p n ((frobenius _ p)^[m] f) = coeff R p (n - m) f :=
  coeffMonoidHom_iterate_powMonoidHom' _ _ _ hmn
/-
**Perfection.pthRoot_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：pthRoot_frobenius : (pthRoot R p).comp (frobenius _ p) = RingHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Perfection.instCharP`：∀ (R : Type u_1) [inst : CommSemiring R] (p : ℕ) [
hp : Fact (Nat.Prime p)] [inst_1 : CharP R p],   CharP (Perfection R p) p
· 使用定理 `Perfection.ext`：ext {f g : Perfection R p} (h : forall n, coeff R p n f 
= coeff R p n g) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `Perfection.pthRoot_eq_symm_frobeniusEquiv`：∀ {R : Type u_1} [inst : Comm
Semiring R] {p : ℕ} [hp : Fact (Nat.Prime p)] [inst_1 : CharP R p],   Perfection
.pthRoot R p = ↑(frobeniusEquiv…
· 使用定理 `frobeniusEquiv_symm_comp_frobenius`：frobeniusEquiv_symm_comp_frobenius :
 ((frobeniusEquiv R p).symm : R ->+* R).comp (frobenius R p) = RingHom.id R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pthRoot_frobenius : (pthRoot R p).comp (frobenius _ p) = RingHom.id _ := by
  ext; simp
/-
**Perfection.frobenius_pthRoot** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：frobenius_pthRoot : (frobenius _ p).comp (pthRoot R p) = RingHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.pthRoot_frobenius`：pthRoot_frobenius : (pthRoot R p).comp (fr
obenius _ p) = RingHom.id _
-/
theorem frobenius_pthRoot : (frobenius _ p).comp (pthRoot R p) = RingHom.id _ := pthRoot_frobenius
/-
**Perfection.coeff_add_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_add_ne_zero {f : Perfection R p} {n : Nat} (hfn : coeff R p n f != 0
) (k : Nat) : coeff R p (n + k) f != 0
参数：hfn : coeff R p n f != 0；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Perfection.coeff_pow_p`：coeff_pow_p (f : Perfection R p) (n : Nat) : coe
ff R p (n + 1) (f ^ p) = coeff R p n f
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem coeff_add_ne_zero {f : Perfection R p} {n : ℕ} (hfn : coeff R p n f ≠ 0) (k : ℕ) :
    coeff R p (n + k) f ≠ 0 :=
  Nat.recOn k hfn fun k ih h => ih <| by
    rw [Nat.add_succ] at h
    rw [← coeff_pow_p, map_pow, h, zero_pow hp.1.ne_zero]
/-
**Perfection.coeff_ne_zero_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_ne_zero_of_le {f : Perfection R p} {m n : Nat} (hfm : coeff R p m f 
!= 0) (hmn : m <= n) : coeff R p n f != 0
参数：hfm : coeff R p m f != 0；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Perfection.coeff_add_ne_zero`：coeff_add_ne_zero {f : Perfection R p} {n 
: Nat} (hfn : coeff R p n f != 0) (k : Nat) : coeff R p (n + k) f != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coeff_ne_zero_of_le {f : Perfection R p} {m n : ℕ} (hfm : coeff R p m f ≠ 0)
    (hmn : m ≤ n) : coeff R p n f ≠ 0 :=
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  hk.symm ▸ coeff_add_ne_zero hfm k
/-
**Perfection.coeff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：coeff_surjective (h : Function.Surjective (frobenius R p)) (n : Nat) : Fun
ction.Surjective (Perfection.coeff R p n)
参数：h : Function.Surjective (frobenius R p)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `Nat.leRec_succ`：leRec_succ {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
· 使用引理 `Nat.leRec_self`：leRec_self {n} {motive : (m : Nat) -> n <= m -> Sort*} (
refl : motive n (Nat.le_refl _)) (le_succ_of_le : forall ⦃k⦄ (h : n <= k), motiv
e k …
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
-/
theorem coeff_surjective (h : Function.Surjective (frobenius R p)) (n : ℕ) :
    Function.Surjective (Perfection.coeff R p n) := by
  intro x
  refine ⟨⟨fun m ↦ if h : n ≤ m then ?_ else x ^ p ^ (n - m), ?_⟩, ?_⟩
  · induction h using Nat.leRec with
    | refl =>
      exact x
    | le_succ_of_le hle xk =>
      choose x hx using h xk
      use x
  · intro m
    obtain (h1 | h1 | h1) : n ≤ m ∨ n = m + 1 ∨ ¬ n ≤ m + 1 := by lia
    · have h1' : n ≤ m + 1 := by lia
      simp only [h1', ↓reduceDIte, h1, Nat.leRec_succ, ← frobenius_def]
      exact Classical.choose_spec (h _)
    · subst h1
      simp [← frobenius_def]
    · have h1' : ¬ n ≤ m := by lia
      have : n - m = (n - (m + 1)) + 1 := by lia
      simp [h1, h1', this, pow_succ, pow_mul]
  · simp

variable (R p)

/-- Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* Perfection S p`. -/
@[simps]
/-
**Perfection.lift** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：lift (R : Type u₁) [CommSemiring R] [CharP R p] [PerfectRing R p] (S : Typ
e u₂) [CommSemiring S] [CharP S p] : (R ->+* S) ≃ (R ->+* Perfection S p) where 
toFun f
参数：R : Type u₁；S : Type u₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* Perfection S p
`.
-/
noncomputable def lift (R : Type u₁) [CommSemiring R] [CharP R p] [PerfectRing R p]
    (S : Type u₂) [CommSemiring S] [CharP S p] : (R →+* S) ≃ (R →+* Perfection S p) where
  toFun f :=
    { toFun := fun r => ⟨fun n => f (((frobeniusEquiv R p).symm : R →+* R)^[n] r),
        fun n => by rw [← f.map_pow, Function.iterate_succ_apply', RingHom.coe_coe,
          frobeniusEquiv_symm_pow_p]⟩
      map_one' := ext fun _ => (congr_arg f <| iterate_map_one _ _).trans f.map_one
      map_mul' := fun _ _ =>
        ext fun _ => (congr_arg f <| iterate_map_mul _ _ _ _).trans <| f.map_mul _ _
      map_zero' := ext fun _ => (congr_arg f <| iterate_map_zero _ _).trans f.map_zero
      map_add' := fun _ _ =>
        ext fun _ => (congr_arg f <| iterate_map_add _ _ _ _).trans <| f.map_add _ _ }
  invFun := RingHom.comp <| coeff S p 0
  right_inv f := RingHom.ext fun r => ext fun n =>
    show coeff S p 0 (f (((frobeniusEquiv R p).symm)^[n] r)) = coeff S p n (f r) by
      rw [← coeff_iterate_frobenius _ 0 n, zero_add, ← RingHom.map_iterate_frobenius,
        Function.RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm R p) n]
/-
**Perfection.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：hom_ext {R : Type u₁} [CommSemiring R] [CharP R p] [PerfectRing R p] {S : 
Type u₂} [CommSemiring S] [CharP S p] {f g : R ->+* Perfection S p} (hfg : foral
l x, coeff S p 0 (f x) = coeff S p 0 (g x)) : f = g
参数：hfg : forall x, coeff S p 0 (f x) = coeff S p 0 (g x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem hom_ext {R : Type u₁} [CommSemiring R] [CharP R p] [PerfectRing R p] {S : Type u₂}
    [CommSemiring S] [CharP S p] {f g : R →+* Perfection S p}
    (hfg : ∀ x, coeff S p 0 (f x) = coeff S p 0 (g x)) : f = g :=
  (lift p R S).symm.injective <| RingHom.ext hfg

variable {R} {S : Type u₂} [CommSemiring S] [CharP S p]

/-- A ring homomorphism `R →+* S` induces `Perfection R p →+* Perfection S p`. -/
/-
**Perfection.map** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：map (φ : R ->+* S) : Perfection R p ->+* Perfection S p where __
参数：φ : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `R →+* S` induces `Perfection R p →+* Perfection S p`.
-/
def map (φ : R →+* S) : Perfection R p →+* Perfection S p where
  __ := mapMonoidHom p (φ : R →* S)
  map_zero' := Subtype.ext <| funext fun _ => φ.map_zero
  map_add' _ _ := Subtype.ext <| funext fun _ => φ.map_add _ _
/-
**Perfection.coeff_map** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (p : ℕ) [hp : Fact (Nat.Prime p)]
 [inst_1 : CharP R p] {S : Type u₂}   [inst_2 : CommSemiring S] [inst_3 : CharP 
S p] (φ : R →+* S) (f : Perfection R p) (n : ℕ),   (Perfection.coeff S p n) ((Pe
rfection.map p φ) f) = φ ((Perfection.coeff R p n) f)
参数：p : ℕ；Nat.Prime p；φ : R →+* S；f : Perfection R p；n : ℕ；Perfection.coeff S p n
；(Perfection.map p φ) f；(Perfection.coeff R p n) f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coeff_map (φ : R →+* S) (f : Perfection R p) (n : ℕ) :
    coeff S p n (map p φ f) = φ (coeff R p n f) := rfl

end CommSemiring

section CommRing

/-- `Perfection R p` as a semiring of `ℕ → R`. -/
/-
**Perfection.subring** 是 Mathlib 中的一个定义，位于命名空间 `Perfection`。
形式化陈述：subring (R : Type*) [CommRing R] (p : Nat) [hp : Fact p.Prime] [CharP R p]
 : Subring (Nat -> R) where __
参数：R : Type*；p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Perfection R p` as a semiring of `ℕ → R`.
-/
def subring (R : Type*) [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p] :
    Subring (ℕ → R) where
  __ := subsemiring R p
  neg_mem' hf n := (map_neg (frobenius R p) _).trans congr(-$(hf n))

@[deprecated (since := "2026-03-03")]
alias _root_.Ring.perfectionSubring := subring

variable (R : Type*) [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
/-
**Perfection.** 是 Mathlib 中的一个实例，位于命名空间 `Perfection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring (Perfection R p) :=
  inferInstanceAs <| Ring (subring R p)
/-
**Perfection.** 是 Mathlib 中的一个实例，位于命名空间 `Perfection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (Perfection R p) :=
  inferInstanceAs <| CommRing (subring R p)

end CommRing

section CommMonoid_CommRing

/-
**Perfection.coeff_mapMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Perfection`。
形式化陈述：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {M : Type u_1} {N : Type u_2} [inst_
1 : CommMonoid M] [inst_2 : CommRing N]   [inst_3 : CharP N p] (e : M →* N) (n :
 ℕ) (x : Perfection M p),   (Perfection.coeff N p n) ((Perfection.mapMonoidHom p
 e) x) = e ((Perfection.coeffMonoidHom M p n) x)
参数：Nat.Prime p；e : M →* N；n : ℕ；x : Perfection M p；Perfection.coeff N p n；(Perfe
ction.mapMonoidHom p e) x；(Perfection.coeffMonoidHom M p n) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coeff_mapMonoidHom {p : ℕ} [Fact p.Prime] {M N : Type*} [CommMonoid M] [CommRing N]
    [CharP N p] (e : M →* N) (n : ℕ) (x : Perfection M p) :
    coeff N p n (mapMonoidHom p e x) = e (coeffMonoidHom M p n x) := rfl

end CommMonoid_CommRing

end Perfection

/-- A perfection map to a ring of characteristic `p` is a map that is isomorphic
to its perfection. -/
/-
**PerfectionMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(p : ℕ) →   [Fact (Nat.Prime p)] →     {R : Type u₁} →       [inst : CommS
emiring R] →         [CharP R p] → {P : Type u₂} → [inst_2 : CommSemiring P] → [
CharP P p] → [PerfectRing P p] → (P →+* R) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A perfection map to a ring of characteristic `p` is a map that is isomorphic
to its perfection.
-/
structure PerfectionMap (p : ℕ) [Fact p.Prime] {R : Type u₁} [CommSemiring R] [CharP R p]
    {P : Type u₂} [CommSemiring P] [CharP P p] [PerfectRing P p] (π : P →+* R) : Prop where
  injective : ∀ ⦃x y : P⦄,
    (∀ n, π (((frobeniusEquiv P p).symm)^[n] x) = π (((frobeniusEquiv P p).symm)^[n] y)) → x = y
  surjective : ∀ f : ℕ → R, (∀ n, f (n + 1) ^ p = f n) → ∃ x : P, ∀ n,
    π (((frobeniusEquiv P p).symm)^[n] x) = f n

namespace PerfectionMap

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u₁} [CommSemiring R] [CharP R p]
variable {P : Type u₃} [CommSemiring P] [CharP P p] [PerfectRing P p]

/-- Create a `PerfectionMap` from an isomorphism to the perfection. -/
/-
**PerfectionMap.mk'** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：mk' {f : P ->+* R} (g : P ≃+* Perfection R p) (hfg : Perfection.lift p P R
 f = g) : PerfectionMap p f
参数：g : P ≃+* Perfection R p；hfg : Perfection.lift p P R f = g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
· 使用定理 `Perfection.ext`：ext {f g : Perfection R p} (h : forall n, coeff R p n f 
= coeff R p n g) : f = g
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Create a `PerfectionMap` from an isomorphism to the perfection.
-/
theorem mk' {f : P →+* R} (g : P ≃+* Perfection R p) (hfg : Perfection.lift p P R f = g) :
    PerfectionMap p f :=
  { injective := fun x y hxy =>
      g.injective <|
        (RingHom.ext_iff.1 hfg x).symm.trans <|
          Eq.symm <| (RingHom.ext_iff.1 hfg y).symm.trans <| Perfection.ext fun n => (hxy n).symm
    surjective := fun y hy =>
      let ⟨x, hx⟩ := g.surjective ⟨y, hy⟩
      ⟨x, fun n =>
        show Perfection.coeff R p n (Perfection.lift p P R f x) = Perfection.coeff R p n ⟨y, hy⟩ by
          simp [hfg, hx]⟩ }

variable (p R P)

/-- The canonical perfection map from the perfection of a ring. -/
/-
**PerfectionMap.of** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：of : PerfectionMap p (Perfection.coeff R p 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectionMap.mk'`：mk' {f : P ->+* R} (g : P ≃+* Perfection R p) (hfg : 
Perfection.lift p P R f = g) : PerfectionMap p f
· 使用定理 `Perfection.instCharP`：∀ (R : Type u_1) [inst : CommSemiring R] (p : ℕ) [
hp : Fact (Nat.Prime p)] [inst_1 : CharP R p],   CharP (Perfection R p) p
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x

--- 原说明 ---
The canonical perfection map from the perfection of a ring.
-/
theorem of : PerfectionMap p (Perfection.coeff R p 0) :=
  mk' (RingEquiv.refl _) <| (Equiv.eq_symm_apply _).1 rfl

/-- For a perfect ring, it itself is the perfection. -/
/-
**PerfectionMap.id** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：id [PerfectRing R p] : PerfectionMap p (RingHom.id R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `injective_pow_p`：injective_pow_p {x y : R} (h : x ^ p = y ^ p) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `frobeniusEquiv_symm_pow_p`：frobeniusEquiv_symm_pow_p (x : R) : ((frobeni
usEquiv R p).symm x) ^ p = x

--- 原说明 ---
For a perfect ring, it itself is the perfection.
-/
theorem id [PerfectRing R p] : PerfectionMap p (RingHom.id R) :=
  { injective := fun _ _ hxy => hxy 0
    surjective := fun f hf =>
      ⟨f 0, fun n =>
        show ((frobeniusEquiv R p).symm)^[n] (f 0) = f n from
          Nat.recOn n rfl fun n ih => injective_pow_p R p <| by
            rw [Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p, ih, hf]⟩ }

variable {p R P}

/-- A perfection map induces an isomorphism to the perfection. -/
/-
**PerfectionMap.equiv** 是 Mathlib 中的一个定义，位于命名空间 `PerfectionMap`。
形式化陈述：equiv {π : P ->+* R} (m : PerfectionMap p π) : P ≃+* Perfection R p
参数：m : PerfectionMap p π。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A perfection map induces an isomorphism to the perfection.
-/
noncomputable def equiv {π : P →+* R} (m : PerfectionMap p π) : P ≃+* Perfection R p :=
  RingEquiv.ofBijective (Perfection.lift p P R π)
    ⟨fun _ _ hxy => m.injective fun n => (congr_arg (Perfection.coeff R p n) hxy :), fun f =>
      let ⟨x, hx⟩ := m.surjective f.1 f.2
      ⟨x, Perfection.ext <| hx⟩⟩
/-
**PerfectionMap.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：equiv_apply {π : P ->+* R} (m : PerfectionMap p π) (x : P) : m.equiv x = P
erfection.lift p P R π x
参数：m : PerfectionMap p π；x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_apply {π : P →+* R} (m : PerfectionMap p π) (x : P) :
    m.equiv x = Perfection.lift p P R π x := rfl
/-
**PerfectionMap.comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：comp_equiv {π : P ->+* R} (m : PerfectionMap p π) (x : P) : Perfection.coe
ff R p 0 (m.equiv x) = π x
参数：m : PerfectionMap p π；x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_equiv {π : P →+* R} (m : PerfectionMap p π) (x : P) :
    Perfection.coeff R p 0 (m.equiv x) = π x := rfl
/-
**PerfectionMap.comp_equiv'** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：comp_equiv' {π : P ->+* R} (m : PerfectionMap p π) : (Perfection.coeff R p
 0).comp ↑m.equiv = π
参数：m : PerfectionMap p π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem comp_equiv' {π : P →+* R} (m : PerfectionMap p π) :
    (Perfection.coeff R p 0).comp ↑m.equiv = π :=
  RingHom.ext fun _ => rfl
/-
**PerfectionMap.comp_symm_equiv** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：comp_symm_equiv {π : P ->+* R} (m : PerfectionMap p π) (f : Perfection R p
) : π (m.equiv.symm f) = Perfection.coeff R p 0 f
参数：m : PerfectionMap p π；f : Perfection R p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PerfectionMap.comp_equiv`：comp_equiv {π : P ->+* R} (m : PerfectionMap p
 π) (x : P) : Perfection.coeff R p 0 (m.equiv x) = π x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
theorem comp_symm_equiv {π : P →+* R} (m : PerfectionMap p π) (f : Perfection R p) :
    π (m.equiv.symm f) = Perfection.coeff R p 0 f :=
  (m.comp_equiv _).symm.trans <| congr_arg _ <| m.equiv.apply_symm_apply f
/-
**PerfectionMap.comp_symm_equiv'** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：comp_symm_equiv' {π : P ->+* R} (m : PerfectionMap p π) : π.comp ↑m.equiv.
symm = Perfection.coeff R p 0
参数：m : PerfectionMap p π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `PerfectionMap.comp_symm_equiv`：comp_symm_equiv {π : P ->+* R} (m : Perfe
ctionMap p π) (f : Perfection R p) : π (m.equiv.symm f) = Perfection.coeff R p 0
 f
-/
theorem comp_symm_equiv' {π : P →+* R} (m : PerfectionMap p π) :
    π.comp ↑m.equiv.symm = Perfection.coeff R p 0 :=
  RingHom.ext m.comp_symm_equiv

variable (p R P)

/-- Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* P`,
where `P` is any perfection of `S`. -/
@[simps]
/-
**PerfectionMap.lift** 是 Mathlib 中的一个定义，位于命名空间 `PerfectionMap`。
形式化陈述：lift [PerfectRing R p] (S : Type u₂) [CommSemiring S] [CharP S p] (P : Typ
e u₃) [CommSemiring P] [CharP P p] [PerfectRing P p] (π : P ->+* S) (m : Perfect
ionMap p π) : (R ->+* S) ≃ (R ->+* P) where toFun f
参数：S : Type u₂；P : Type u₃；π : P ->+* S；m : PerfectionMap p π。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* P`,
where `P` is any perfection of `S`.
-/
noncomputable def lift [PerfectRing R p] (S : Type u₂) [CommSemiring S] [CharP S p] (P : Type u₃)
    [CommSemiring P] [CharP P p] [PerfectRing P p] (π : P →+* S) (m : PerfectionMap p π) :
    (R →+* S) ≃ (R →+* P) where
  toFun f := RingHom.comp ↑m.equiv.symm <| Perfection.lift p R S f
  invFun f := π.comp f
  left_inv f := by
    simp_rw [← RingHom.comp_assoc, comp_symm_equiv']
    exact (Perfection.lift p R S).symm_apply_apply f
  right_inv f := by
    exact RingHom.ext fun x => m.equiv.injective <| (m.equiv.apply_symm_apply _).trans
      <| show Perfection.lift p R S (π.comp f) x = RingHom.comp (↑m.equiv) f x from
        RingHom.ext_iff.1 (by rw [← Equiv.eq_symm_apply]; rfl) _

variable {R p}
/-
**PerfectionMap.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：hom_ext [PerfectRing R p] {S : Type u₂} [CommSemiring S] [CharP S p] {P : 
Type u₃} [CommSemiring P] [CharP P p] [PerfectRing P p] (π : P ->+* S) (m : Perf
ectionMap p π) {f g : R ->+* P} (hfg : forall x, π (f x) = π (g x)) : f = g
参数：π : P ->+* S；m : PerfectionMap p π；hfg : forall x, π (f x) = π (g x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem hom_ext [PerfectRing R p] {S : Type u₂} [CommSemiring S] [CharP S p] {P : Type u₃}
    [CommSemiring P] [CharP P p] [PerfectRing P p] (π : P →+* S) (m : PerfectionMap p π)
    {f g : R →+* P} (hfg : ∀ x, π (f x) = π (g x)) : f = g :=
  (lift p R S P π m).symm.injective <| RingHom.ext hfg

variable {P} (p)
variable {S : Type u₂} [CommSemiring S] [CharP S p]
variable {Q : Type u₄} [CommSemiring Q] [CharP Q p] [PerfectRing Q p]

/-- A ring homomorphism `R →+* S` induces `P →+* Q`, a map of the respective perfections. -/
@[nolint unusedArguments]
/-
**PerfectionMap.map** 是 Mathlib 中的一个定义，位于命名空间 `PerfectionMap`。
形式化陈述：map {π : P ->+* R} (_ : PerfectionMap p π) {σ : Q ->+* S} (n : PerfectionM
ap p σ) (φ : R ->+* S) : P ->+* Q
参数：_ : PerfectionMap p π；n : PerfectionMap p σ；φ : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `R →+* S` induces `P →+* Q`, a map of the respective perfect
ions.
-/
noncomputable def map {π : P →+* R} (_ : PerfectionMap p π) {σ : Q →+* S} (n : PerfectionMap p σ)
    (φ : R →+* S) : P →+* Q :=
  lift p P S Q σ n <| φ.comp π
/-
**PerfectionMap.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：comp_map {π : P ->+* R} (m : PerfectionMap p π) {σ : Q ->+* S} (n : Perfec
tionMap p σ) (φ : R ->+* S) : σ.comp (map p m n φ) = φ.comp π
参数：m : PerfectionMap p π；n : PerfectionMap p σ；φ : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem comp_map {π : P →+* R} (m : PerfectionMap p π) {σ : Q →+* S} (n : PerfectionMap p σ)
    (φ : R →+* S) : σ.comp (map p m n φ) = φ.comp π :=
  (lift p P S Q σ n).symm_apply_apply _
/-
**PerfectionMap.map_map** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：map_map {π : P ->+* R} (m : PerfectionMap p π) {σ : Q ->+* S} (n : Perfect
ionMap p σ) (φ : R ->+* S) (x : P) : σ (map p m n φ x) = φ (π x)
参数：m : PerfectionMap p π；n : PerfectionMap p σ；φ : R ->+* S；x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
· 使用定理 `PerfectionMap.comp_map`：comp_map {π : P ->+* R} (m : PerfectionMap p π) 
{σ : Q ->+* S} (n : PerfectionMap p σ) (φ : R ->+* S) : σ.comp (map p m n φ) = φ
.comp π
-/
theorem map_map {π : P →+* R} (m : PerfectionMap p π) {σ : Q →+* S} (n : PerfectionMap p σ)
    (φ : R →+* S) (x : P) : σ (map p m n φ x) = φ (π x) :=
  RingHom.ext_iff.1 (comp_map p m n φ) x
/-
**PerfectionMap.map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `PerfectionMap`。
形式化陈述：map_eq_map (φ : R ->+* S) : map p (of p R) (of p S) φ = Perfection.map p φ
参数：φ : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PerfectionMap.hom_ext`：hom_ext [PerfectRing R p] {S : Type u₂} [CommSemi
ring S] [CharP S p] {P : Type u₃} [CommSemiring P] [CharP P p] [PerfectRing P p]
 (π : P ->+…
· 使用定理 `Perfection.instCharP`：∀ (R : Type u_1) [inst : CommSemiring R] (p : ℕ) [
hp : Fact (Nat.Prime p)] [inst_1 : CharP R p],   CharP (Perfection R p) p
· 使用定理 `Perfection.instPerfectRing`：∀ {M : Type u_1} [inst : CommMonoid M] {p : 
ℕ}, PerfectRing (Perfection M p) p
· 使用定理 `PerfectionMap.of`：of : PerfectionMap p (Perfection.coeff R p 0)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PerfectionMap.map_map`：map_map {π : P ->+* R} (m : PerfectionMap p π) {σ
 : Q ->+* S} (n : PerfectionMap p σ) (φ : R ->+* S) (x : P) : σ (map p m n φ x) 
= φ (π x)
· 使用定理 `Perfection.coeff_map`：∀ {R : Type u_1} [inst : CommSemiring R] (p : ℕ) [
hp : Fact (Nat.Prime p)] [inst_1 : CharP R p] {S : Type u₂}   [inst_2 : CommSemi
ring S] [i…
-/
theorem map_eq_map (φ : R →+* S) : map p (of p R) (of p S) φ = Perfection.map p φ :=
  hom_ext _ (of p S) fun f => by rw [map_map, Perfection.coeff_map]

end PerfectionMap

section ModP

variable (O : Type u₂) [CommRing O] (p : ℕ)

/-- `O/(p)` for `O`, ring of integers of `K`. -/
/-
**ModP** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ModP
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`O/(p)` for `O`, ring of integers of `K`.
-/
abbrev ModP :=
  O ⧸ (Ideal.span {(p : O)} : Ideal O)

namespace ModP

/-
**ModP.** 是 Mathlib 中的一个实例，位于命名空间 `ModP`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fact p.Prime] [hvp : Fact (¬ IsUnit (p : O))] : CharP (ModP O p) p :=
  CharP.quotient O p <| hvp.1
/-
**ModP.** 是 Mathlib 中的一个实例，位于命名空间 `ModP`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hp : Fact p.Prime] [Fact (¬ IsUnit (p : O))] : Nontrivial (ModP O p) :=
  CharP.nontrivial_of_char_ne_one hp.1.ne_one

end ModP

end ModP

section Perfectoid

variable (K : Type u₁) [Field K] (v : Valuation K ℝ≥0)
variable (O : Type u₂) [CommRing O] [Algebra O K] (hv : v.Integers O)
variable (p : ℕ)

namespace ModP

section Classical

attribute [local instance] Classical.dec

/-- For a field `K` with valuation `v : K → ℝ≥0` and ring of integers `O`,
a function `O/(p) → ℝ≥0` that sends `0` to `0` and `x + (p)` to `v(x)` as long as `x ∉ (p)`. -/
/-
**ModP.preVal** 是 Mathlib 中的一个定义，位于命名空间 `ModP`。
形式化陈述：preVal (x : ModP O p) : Real>=0
参数：x : ModP O p。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a field `K` with valuation `v : K → ℝ≥0` and ring of integers `O`,
a function `O/(p) → ℝ≥0` that sends `0` to `0` and `x + (p)` to `v(x)` as long a
s `x ∉ (p)`.
-/
noncomputable def preVal (x : ModP O p) : ℝ≥0 :=
  if x = 0 then 0 else v (algebraMap O K x.out)

variable {K v O p}

@[simp]
/-
**ModP.preVal_zero** 是 Mathlib 中的一个定理，位于命名空间 `ModP`。
形式化陈述：preVal_zero : preVal K v O p 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem preVal_zero : preVal K v O p 0 = 0 :=
  if_pos rfl

include hv
/-
**ModP.preVal_mk** 是 Mathlib 中的一个定理，位于命名空间 `ModP`。
形式化陈述：preVal_mk {x : O} (hx : (Ideal.Quotient.mk _ x : ModP O p) != 0) : preVal 
K v O p (Ideal.Quotient.mk _ x) = v (algebraMap O K x)
参数：hx : (Ideal.Quotient.mk _ x : ModP O p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_singleton'`：mem_span_singleton' {x y : α} : x in span ({y
} : Set α) ↔ exists a, a * y = x
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `Quotient.mk_out'`：mk_out' (a : α) : s₁ (Quotient.mk'' a : Quotient s₁).o
ut a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Valuation.map_eq_of_sub_lt`：map_eq_of_sub_lt (h : v (y - x) < v x) : v y
 = v x
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Valuation.Integers.le_iff_dvd`：le_iff_dvd (hv : Integers v O) {x y : O} 
: v (algebraMap O F x) <= v (algebraMap O F y) ↔ y ∣ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `dvd_of_mul_left_dvd`：dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c
-/
theorem preVal_mk {x : O} (hx : (Ideal.Quotient.mk _ x : ModP O p) ≠ 0) :
    preVal K v O p (Ideal.Quotient.mk _ x) = v (algebraMap O K x) := by
  obtain ⟨r, hr⟩ : ∃ (a : O), a * (p : O) = (Ideal.Quotient.mk _ x).out - x :=
    Ideal.mem_span_singleton'.1 <| Ideal.Quotient.eq.1 <| Quotient.sound' <| Quotient.mk_out' _
  refine (if_neg hx).trans (v.map_eq_of_sub_lt <| lt_of_not_ge ?_)
  rw [← map_sub, ← hr, hv.le_iff_dvd]
  exact fun hprx =>
    hx (Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 <| dvd_of_mul_left_dvd hprx)
/-
**ModP.preVal_mul** 是 Mathlib 中的一个定理，位于命名空间 `ModP`。
形式化陈述：preVal_mul {x y : ModP O p} (hxy0 : x * y != 0) : preVal K v O p (x * y) =
 preVal K v O p x * preVal K v O p y
参数：hxy0 : x * y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `ModP.preVal_mk`：preVal_mk {x : O} (hx : (Ideal.Quotient.mk _ x : ModP O 
p) != 0) : preVal K v O p (Ideal.Quotient.mk _ x) = v (algebraMap O K x)
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
-/
theorem preVal_mul {x y : ModP O p} (hxy0 : x * y ≠ 0) :
    preVal K v O p (x * y) = preVal K v O p x * preVal K v O p y := by
  have hx0 : x ≠ 0 := mt (by rintro rfl; rw [zero_mul]) hxy0
  have hy0 : y ≠ 0 := mt (by rintro rfl; rw [mul_zero]) hxy0
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul (Ideal.Quotient.mk (Ideal.span {↑p})) r s] at hxy0 ⊢
  rw [preVal_mk hv hx0, preVal_mk hv hy0, preVal_mk hv hxy0, map_mul, v.map_mul]
/-
**ModP.preVal_add** 是 Mathlib 中的一个定理，位于命名空间 `ModP`。
形式化陈述：preVal_add (x y : ModP O p) : preVal K v O p (x + y) <= max (preVal K v O 
p x) (preVal K v O p y)
参数：x y : ModP O p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModP.preVal_zero`：preVal_zero : preVal K v O p 0 = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `ModP.preVal_mk`：preVal_mk {x : O} (hx : (Ideal.Quotient.mk _ x : ModP O 
p) != 0) : preVal K v O p (Ideal.Quotient.mk _ x) = v (algebraMap O K x)
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
-/
theorem preVal_add (x y : ModP O p) :
    preVal K v O p (x + y) ≤ max (preVal K v O p x) (preVal K v O p y) := by
  obtain rfl | hx0 := eq_or_ne x 0
  · simp
  obtain rfl | hy0 := eq_or_ne y 0
  · simp
  by_cases hxy0 : x + y = 0
  · simp [hxy0]
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_add (Ideal.Quotient.mk (Ideal.span {↑p})) r s] at hxy0 ⊢
  rw [preVal_mk hv hx0, preVal_mk hv hy0, preVal_mk hv hxy0, map_add]; exact v.map_add _ _
/-
**ModP.v_p_lt_preVal** 是 Mathlib 中的一个定理，位于命名空间 `ModP`。
形式化陈述：v_p_lt_preVal {x : ModP O p} : v p < preVal K v O p x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModP.preVal_zero`：preVal_zero : preVal K v O p 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Valuation.Integers.le_iff_dvd`：le_iff_dvd (hv : Integers v O) {x y : O} 
: v (algebraMap O F x) <= v (algebraMap O F y) ↔ y ∣ x
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `ModP.preVal_mk`：preVal_mk {x : O} (hx : (Ideal.Quotient.mk _ x : ModP O 
p) != 0) : preVal K v O p (Ideal.Quotient.mk _ x) = v (algebraMap O K x)
-/
theorem v_p_lt_preVal {x : ModP O p} : v p < preVal K v O p x ↔ x ≠ 0 := by
  refine ⟨by aesop, fun h => lt_of_not_ge fun hp => h ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [preVal_mk hv h, ← map_natCast (algebraMap O K) p, hv.le_iff_dvd] at hp
  · rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact hp
/-
**ModP.preVal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ModP`。
形式化陈述：preVal_eq_zero {x : ModP O p} : preVal K v O p x = 0 ↔ x = 0 where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ModP.v_p_lt_preVal`：v_p_lt_preVal {x : ModP O p} : v p < preVal K v O p 
x ↔ x != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModP.preVal_zero`：preVal_zero : preVal K v O p 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preVal_eq_zero {x : ModP O p} : preVal K v O p x = 0 ↔ x = 0 where
  mp h := by
    contrapose! h
    exact ((v_p_lt_preVal hv).2 h).ne_zero
  mpr hx := by simp [hx]
/-
**ModP.v_p_lt_val** 是 Mathlib 中的一个定理，位于命名空间 `ModP`。
形式化陈述：v_p_lt_val {x : O} : v p < v (algebraMap O K x) ↔ (Ideal.Quotient.mk _ x :
 ModP O p) != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Valuation.Integers.le_iff_dvd`：le_iff_dvd (hv : Integers v O) {x y : O} 
: v (algebraMap O F x) <= v (algebraMap O F y) ↔ y ∣ x
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem v_p_lt_val {x : O} :
    v p < v (algebraMap O K x) ↔ (Ideal.Quotient.mk _ x : ModP O p) ≠ 0 := by
  rw [lt_iff_not_ge, not_iff_not, ← map_natCast (algebraMap O K) p, hv.le_iff_dvd,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

open NNReal

variable [hp : Fact p.Prime]
/-
**ModP.mul_ne_zero_of_pow_p_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ModP`。
形式化陈述：mul_ne_zero_of_pow_p_ne_zero {x y : ModP O p} (hx : x ^ p != 0) (hy : y ^ 
p != 0) : x * y != 0
参数：hx : x ^ p != 0；hy : y ^ p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `ModP.v_p_lt_val`：v_p_lt_val {x : O} : v p < v (algebraMap O K x) ↔ (Idea
l.Quotient.mk _ x : ModP O p) != 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `NNReal.rpow_add`：rpow_add {x : Real>=0} (hx : x != 0) (y z : Real) : x ^
 (y + z) = x ^ y * x ^ z
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.rpow_le_rpow_of_exponent_ge`：rpow_le_rpow_of_exponent_ge {x : Rea
l>=0} {y z : Real} (hx0 : 0 < x) (hx1 : x <= 1) (hyz : z <= y) : x ^ y <= x ^ z
· 使用定理 `Valuation.Integers.map_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst : Comm
Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O :
 Type w} [inst_2 : …
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
（共 52 条，此处仅展示前 30 条）
-/
theorem mul_ne_zero_of_pow_p_ne_zero {x y : ModP O p} (hx : x ^ p ≠ 0) (hy : y ^ p ≠ 0) :
    x * y ≠ 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1p : (0 : ℝ) < 1 / p := one_div_pos.2 (Nat.cast_pos.2 hp.1.pos)
  rw [← (Ideal.Quotient.mk (Ideal.span {(p : O)})).map_mul]
  rw [← (Ideal.Quotient.mk (Ideal.span {(p : O)})).map_pow] at hx hy
  rw [← v_p_lt_val hv] at hx hy ⊢
  rw [map_pow, v.map_pow, ← rpow_lt_rpow_iff h1p, ← rpow_natCast, ← rpow_mul,
    mul_one_div_cancel (Nat.cast_ne_zero.2 hp.1.ne_zero : (p : ℝ) ≠ 0), rpow_one] at hx hy
  rw [map_mul, v.map_mul]; refine lt_of_le_of_lt ?_ (mul_lt_mul'' hx hy zero_le zero_le)
  by_cases hvp : v p = 0
  · rw [hvp]; exact zero_le
  replace hvp := zero_lt_iff.2 hvp
  conv_lhs => rw [← rpow_one (v p)]
  rw [← rpow_add (ne_of_gt hvp)]
  refine rpow_le_rpow_of_exponent_ge hvp (map_natCast (algebraMap O K) p ▸ hv.2 _) ?_
  rw [← add_div, div_le_one (Nat.cast_pos.2 hp.1.pos : 0 < (p : ℝ))]; exact mod_cast hp.1.two_le

end Classical

end ModP

/-- Perfection of `O/(p)` where `O` is the ring of integers of `K`. -/
/-
**PreTilt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PreTilt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Perfection of `O/(p)` where `O` is the ring of integers of `K`.
-/
def PreTilt :=
  Perfection (ModP O p) p

namespace PreTilt

variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]

/-
**PreTilt.** 是 Mathlib 中的一个实例，位于命名空间 `PreTilt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (PreTilt O p) :=
  inferInstanceAs <| CommRing <| Perfection _ _
/-
**PreTilt.** 是 Mathlib 中的一个实例，位于命名空间 `PreTilt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CharP (PreTilt O p) p :=
  inferInstanceAs <| CharP (Perfection _ _) _
/-
**PreTilt.** 是 Mathlib 中的一个实例，位于命名空间 `PreTilt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PerfectRing (PreTilt O p) p :=
  inferInstanceAs <| PerfectRing (Perfection _ _) p

section coeff

variable {O p}

/-- The `n`-th coefficient of an element of the perfection of `O/(p)`. -/
/-
**PreTilt.coeff** 是 Mathlib 中的一个定义，位于命名空间 `PreTilt`。
形式化陈述：coeff (n : Nat) : PreTilt O p ->+* ModP O p
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p

--- 原说明 ---
The `n`-th coefficient of an element of the perfection of `O/(p)`.
-/
def coeff (n : ℕ) : PreTilt O p →+* ModP O p := Perfection.coeff (ModP O p) p n
/-
**PreTilt.coeff_def** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：coeff_def (n : Nat) (x : PreTilt O p) : coeff n x = Perfection.coeff _ _ n
 x
参数：n : Nat；x : PreTilt O p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_def (n : ℕ) (x : PreTilt O p) : coeff n x = Perfection.coeff _ _ n x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PreTilt.coeff_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：coeff_frobenius (n : Nat) (x : PreTilt O p) : (coeff (n + 1) (frobenius _ 
p x)) = coeff n x
参数：n : Nat；x : PreTilt O p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PreTilt.instCharP`：∀ (O : Type u₂) [inst : CommRing O] (p : ℕ) [inst_1 :
 Fact (Nat.Prime p)] [inst_2 : Fact ¬IsUnit ↑p],   CharP (PreTilt O p) p
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Perfection.coeff_frobenius`：coeff_frobenius (f : Perfection R p) (n : Na
t) : coeff R p (n + 1) (frobenius _ p f) = coeff R p n f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_frobenius (n : ℕ) (x : PreTilt O p) :
    (coeff (n + 1) (frobenius _ p x)) = coeff n x := by
  simp [PreTilt, coeff]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PreTilt.coeff_iterate_frobenius** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：coeff_iterate_frobenius (m n : Nat) (x : PreTilt O p) : (coeff (m + n) ((f
robenius _ p)^[n] x)) = coeff m x
参数：m n : Nat；x : PreTilt O p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PreTilt.instCharP`：∀ (O : Type u₂) [inst : CommRing O] (p : ℕ) [inst_1 :
 Fact (Nat.Prime p)] [inst_2 : Fact ¬IsUnit ↑p],   CharP (PreTilt O p) p
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Perfection.coeff_iterate_frobenius`：coeff_iterate_frobenius (f : Perfect
ion R p) (n m : Nat) : coeff R p (n + m) ((frobenius _ p)^[m] f) = coeff R p n f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_iterate_frobenius (m n : ℕ) (x : PreTilt O p) :
    (coeff (m + n) ((frobenius _ p)^[n] x)) = coeff m x := by
  simp [PreTilt, coeff]

/-- A variant of `PreTilt.coeff_iterate_frobenius` using `m-n` and `n`. -/
/-
**PreTilt.coeff_iterate_frobenius'** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：coeff_iterate_frobenius' (x : PreTilt O p) {m n : Nat} (hmn : m <= n) : co
eff n ((frobenius _ p)^[m] x) = coeff (n - m) x
参数：x : PreTilt O p；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeff_iterate_frobenius'`：coeff_iterate_frobenius' (f : Perfe
ction R p) (n m : Nat) (hmn : m <= n) : coeff R p n ((frobenius _ p)^[m] f) = co
eff R p (n - m) f
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p

--- 原说明 ---
A variant of `PreTilt.coeff_iterate_frobenius` using `m-n` and `n`.
-/
theorem coeff_iterate_frobenius' (x : PreTilt O p) {m n : ℕ} (hmn : m ≤ n) :
    coeff n ((frobenius _ p)^[m] x) = coeff (n - m) x :=
  Perfection.coeff_iterate_frobenius' _ _ _ hmn

@[simp]
/-
**PreTilt.coeff_pow_p** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：coeff_pow_p (x : PreTilt O p) (n : Nat) : coeff (n + 1) x ^ p = coeff n x
参数：x : PreTilt O p；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeff_pow_p`：coeff_pow_p (f : Perfection R p) (n : Nat) : coe
ff R p (n + 1) (f ^ p) = coeff R p n f
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p
-/
theorem coeff_pow_p (x : PreTilt O p) (n : ℕ) : coeff (n + 1) x ^ p = coeff n x :=
  Perfection.coeff_pow_p x n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PreTilt.coeff_frobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：coeff_frobeniusEquiv_symm (n : Nat) (x : PreTilt O p) : (coeff n (((froben
iusEquiv _ p).symm) x)) = coeff (n + 1) x
参数：n : Nat；x : PreTilt O p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PreTilt.instCharP`：∀ (O : Type u₂) [inst : CommRing O] (p : ℕ) [inst_1 :
 Fact (Nat.Prime p)] [inst_2 : Fact ¬IsUnit ↑p],   CharP (PreTilt O p) p
· 使用定理 `PreTilt.instPerfectRing`：∀ (O : Type u₂) [inst : CommRing O] (p : ℕ) [in
st_1 : Fact (Nat.Prime p)] [inst_2 : Fact ¬IsUnit ↑p],   PerfectRing (PreTilt O 
p) p
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Perfection.coeff_symm_frobeniusEquiv`：coeff_symm_frobeniusEquiv (f : Per
fection R p) (n : Nat) : coeff R p n ((frobeniusEquiv _ p).symm f) = coeff R p (
n + 1) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_frobeniusEquiv_symm (n : ℕ) (x : PreTilt O p) :
    (coeff n (((frobeniusEquiv _ p).symm) x)) = coeff (n + 1) x := by
  simp [PreTilt, coeff]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PreTilt.coeff_iterate_frobeniusEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：coeff_iterate_frobeniusEquiv_symm (m n : Nat) (x : PreTilt O p) : (coeff m
 (((frobeniusEquiv _ p).symm^[n]) x)) = coeff (m + n) x
参数：m n : Nat；x : PreTilt O p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PreTilt.instCharP`：∀ (O : Type u₂) [inst : CommRing O] (p : ℕ) [inst_1 :
 Fact (Nat.Prime p)] [inst_2 : Fact ¬IsUnit ↑p],   CharP (PreTilt O p) p
· 使用定理 `PreTilt.instPerfectRing`：∀ (O : Type u₂) [inst : CommRing O] (p : ℕ) [in
st_1 : Fact (Nat.Prime p)] [inst_2 : Fact ¬IsUnit ↑p],   PerfectRing (PreTilt O 
p) p
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Perfection.coeff_iterate_symm_frobeniusEquiv`：coeff_iterate_symm_frobeni
usEquiv (f : Perfection R p) (n m : Nat) : coeff R p n ((frobeniusEquiv _ p).sym
m^[m] f) = coeff R p (n + m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_iterate_frobeniusEquiv_symm (m n : ℕ) (x : PreTilt O p) :
    (coeff m (((frobeniusEquiv _ p).symm^[n]) x)) = coeff (m + n) x := by
  simp [PreTilt, coeff]

end coeff

section Classical

open Perfection

open scoped Classical in
/-- The valuation `Perfection(O/(p)) → ℝ≥0` as a function.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `preVal(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`. -/
/-
**PreTilt.valAux** 是 Mathlib 中的一个定义，位于命名空间 `PreTilt`。
形式化陈述：valAux (f : PreTilt O p) : Real>=0
参数：f : PreTilt O p。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation `Perfection(O/(p)) → ℝ≥0` as a function.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `preVal(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`.
-/
noncomputable def valAux (f : PreTilt O p) : ℝ≥0 :=
  if h : ∃ n, coeff n f ≠ 0 then
    ModP.preVal K v O p (coeff (Nat.find h) f) ^ p ^ Nat.find h
  else 0

variable {K v O p}

open scoped Classical in
/-
**PreTilt.coeff_nat_find_add_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：coeff_nat_find_add_ne_zero {f : PreTilt O p} {h : exists n, coeff n f != 0
} (k : Nat) : coeff (Nat.find h + k) f != 0
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfection.coeff_add_ne_zero`：coeff_add_ne_zero {f : Perfection R p} {n 
: Nat} (hfn : coeff R p n f != 0) (k : Nat) : coeff R p (n + k) f != 0
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem coeff_nat_find_add_ne_zero {f : PreTilt O p} {h : ∃ n, coeff n f ≠ 0} (k : ℕ) :
    coeff (Nat.find h + k) f ≠ 0 :=
  coeff_add_ne_zero (Nat.find_spec h) k

@[simp]
/-
**PreTilt.valAux_zero** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：valAux_zero : valAux K v O p 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem valAux_zero : valAux K v O p 0 = 0 :=
  dif_neg fun ⟨_, hn⟩ => hn rfl

include hv
/-
**PreTilt.valAux_eq** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：valAux_eq {f : PreTilt O p} {n : Nat} (hfn : coeff n f != 0) : valAux K v 
O p f = ModP.preVal K v O p (coeff n f) ^ p ^ n
参数：hfn : coeff n f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PreTilt.valAux.eq_1`：∀ (K : Type u₁) [inst : Field K] (v : Valuation K N
NReal) (O : Type u₂) [inst_1 : CommRing O] [inst_2 : Algebra O K]   (p : ℕ) [ins
t_3 : Fac…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `PreTilt.coeff_pow_p`：coeff_pow_p (x : PreTilt O p) (n : Nat) : coeff (n 
+ 1) x ^ p = coeff n x
· 使用定理 `PreTilt.coeff_nat_find_add_ne_zero`：coeff_nat_find_add_ne_zero {f : PreT
ilt O p} {h : exists n, coeff n f != 0} (k : Nat) : coeff (Nat.find h + k) f != 
0
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `ModP.preVal_mk`：preVal_mk {x : O} (hx : (Ideal.Quotient.mk _ x : ModP O 
p) != 0) : preVal K v O p (Ideal.Quotient.mk _ x) = v (algebraMap O K x)
· 使用定理 `Valuation.map_pow`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x : R) (n : ℕ)
, v (x …
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem valAux_eq {f : PreTilt O p} {n : ℕ} (hfn : coeff n f ≠ 0) :
    valAux K v O p f = ModP.preVal K v O p (coeff n f) ^ p ^ n := by
  have h : ∃ n, coeff n f ≠ 0 := ⟨n, hfn⟩
  rw [valAux, dif_pos h]
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.find_min' h hfn)
  induction k with
  | zero => rfl
  | succ k ih => ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (coeff (Nat.find h + k + 1) f)
  have h1 : (Ideal.Quotient.mk _ x : ModP O p) ≠ 0 := hx.symm ▸ hfn
  have h2 : (Ideal.Quotient.mk _ (x ^ p) : ModP O p) ≠ 0 := by
    rw [map_pow, hx, coeff_pow_p]
    exact coeff_nat_find_add_ne_zero k
  rw [ih (coeff_nat_find_add_ne_zero k), ← add_assoc, ← hx, ← coeff_pow_p, ← hx, ← map_pow,
    ModP.preVal_mk hv h1, ModP.preVal_mk hv h2, map_pow, v.map_pow, ← pow_mul, pow_succ']
/-
**PreTilt.valAux_one** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：valAux_one : valAux K v O p 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PreTilt.valAux_eq`：valAux_eq {f : PreTilt O p} {n : Nat} (hfn : coeff n 
f != 0) : valAux K v O p f = ModP.preVal K v O p (coeff n f) ^ p ^ n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ModP.instNontrivialOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : C
ommRing O] (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact ¬IsUnit ↑p], Nontrivial (ModP
 O p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
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
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `ModP.preVal_mk`：preVal_mk {x : O} (hx : (Ideal.Quotient.mk _ x : ModP O 
p) != 0) : preVal K v O p (Ideal.Quotient.mk _ x) = v (algebraMap O K x)
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
-/
theorem valAux_one : valAux K v O p 1 = 1 :=
  (valAux_eq (hv := hv) <| show coeff 0 1 ≠ 0 from one_ne_zero).trans <| by
    rw [pow_zero, pow_one, map_one, ← (Ideal.Quotient.mk _).map_one, ModP.preVal_mk hv,
      map_one, v.map_one]
    change (1 : ModP O p) ≠ 0
    exact one_ne_zero
/-
**PreTilt.valAux_mul** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：valAux_mul (f g : PreTilt O p) : valAux K v O p (f * g) = valAux K v O p f
 * valAux K v O p g
参数：f g : PreTilt O p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PreTilt.valAux.congr_simp`：∀ (K : Type u₁) [inst : Field K] (v v_1 : Val
uation K NNReal),   v = v_1 →     ∀ (O : Type u₂) [inst_1 : CommRing O] [inst_2 
: Algebra O K] …
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `PreTilt.valAux_zero`：valAux_zero : valAux K v O p 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Perfection.ext`：ext {f g : Perfection R p} (h : forall n, coeff R p n f 
= coeff R p n g) : f = g
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p
· 使用定理 `Perfection.coeff_ne_zero_of_le`：coeff_ne_zero_of_le {f : Perfection R p}
 {m n : Nat} (hfm : coeff R p m f != 0) (hmn : m <= n) : coeff R p n f != 0
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `ModP.mul_ne_zero_of_pow_p_ne_zero`：mul_ne_zero_of_pow_p_ne_zero {x y : M
odP O p} (hx : x ^ p != 0) (hy : y ^ p != 0) : x * y != 0
· 使用定理 `PreTilt.coeff_pow_p`：coeff_pow_p (x : PreTilt O p) (n : Nat) : coeff (n 
+ 1) x ^ p = coeff n x
· 使用定理 `PreTilt.valAux_eq`：valAux_eq {f : PreTilt O p} {n : Nat} (hfn : coeff n 
f != 0) : valAux K v O p f = ModP.preVal K v O p (coeff n f) ^ p ^ n
· 使用定理 `Perfection.coeff_add_ne_zero`：coeff_add_ne_zero {f : Perfection R p} {n 
: Nat} (hfn : coeff R p n f != 0) (k : Nat) : coeff R p (n + k) f != 0
· 使用定理 `ModP.preVal_mul`：preVal_mul {x y : ModP O p} (hxy0 : x * y != 0) : preVa
l K v O p (x * y) = preVal K v O p x * preVal K v O p y
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
-/
theorem valAux_mul (f g : PreTilt O p) :
    valAux K v O p (f * g) = valAux K v O p f * valAux K v O p g := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  obtain rfl | hg := eq_or_ne g 0
  · simp
  obtain ⟨m, hm⟩ : ∃ n, coeff n f ≠ 0 := not_forall.1 fun h => hf <| Perfection.ext h
  obtain ⟨n, hn⟩ : ∃ n, coeff n g ≠ 0 := not_forall.1 fun h => hg <| Perfection.ext h
  replace hm := coeff_ne_zero_of_le hm (le_max_left m n)
  replace hn := coeff_ne_zero_of_le hn (le_max_right m n)
  have hfg : coeff (max m n + 1) (f * g) ≠ 0 := by
    rw [map_mul]
    refine ModP.mul_ne_zero_of_pow_p_ne_zero (hv := hv) ?_ ?_
    · rw [coeff_pow_p f]; assumption
    · rw [coeff_pow_p g]; assumption
  rw [valAux_eq hv (coeff_add_ne_zero hm 1),
      valAux_eq hv (coeff_add_ne_zero hn 1), valAux_eq hv hfg]
  rw [map_mul] at hfg ⊢; rw [ModP.preVal_mul hv hfg, mul_pow]
/-
**PreTilt.valAux_add** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：valAux_add (f g : PreTilt O p) : valAux K v O p (f + g) <= max (valAux K v
 O p f) (valAux K v O p g)
参数：f g : PreTilt O p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PreTilt.valAux.congr_simp`：∀ (K : Type u₁) [inst : Field K] (v v_1 : Val
uation K NNReal),   v = v_1 →     ∀ (O : Type u₂) [inst_1 : CommRing O] [inst_2 
: Algebra O K] …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PreTilt.valAux_zero`：valAux_zero : valAux K v O p 0 = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Perfection.ext`：ext {f g : Perfection R p} (h : forall n, coeff R p n f 
= coeff R p n g) : f = g
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p
· 使用定理 `Perfection.coeff_ne_zero_of_le`：coeff_ne_zero_of_le {f : Perfection R p}
 {m n : Nat} (hfm : coeff R p m f != 0) (hmn : m <= n) : coeff R p n f != 0
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `PreTilt.valAux_eq`：valAux_eq {f : PreTilt O p} {n : Nat} (hfn : coeff n 
f != 0) : valAux K v O p f = ModP.preVal K v O p (coeff n f) ^ p ^ n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `ModP.preVal_add`：preVal_add (x y : ModP O p) : preVal K v O p (x + y) <=
 max (preVal K v O p x) (preVal K v O p y)
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
（共 32 条，此处仅展示前 30 条）
-/
theorem valAux_add (f g : PreTilt O p) :
    valAux K v O p (f + g) ≤ max (valAux K v O p f) (valAux K v O p g) := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  obtain rfl | hg := eq_or_ne g 0
  · simp
  by_cases hfg : f + g = 0
  · simp [hfg]
  replace hf : ∃ n, coeff n f ≠ 0 := not_forall.1 fun h => hf <| Perfection.ext h
  replace hg : ∃ n, coeff n g ≠ 0 := not_forall.1 fun h => hg <| Perfection.ext h
  replace hfg : ∃ n, coeff n (f + g) ≠ 0 := not_forall.1 fun h => hfg <| Perfection.ext h
  obtain ⟨m, hm⟩ := hf; obtain ⟨n, hn⟩ := hg; obtain ⟨k, hk⟩ := hfg
  replace hm := coeff_ne_zero_of_le hm (le_trans (le_max_left m n) (le_max_left _ k))
  replace hn := coeff_ne_zero_of_le hn (le_trans (le_max_right m n) (le_max_left _ k))
  replace hk := coeff_ne_zero_of_le hk (le_max_right (max m n) k)
  rw [valAux_eq hv hm, valAux_eq hv hn, valAux_eq hv hk, map_add]
  rcases le_max_iff.1
      (ModP.preVal_add hv (coeff (max (max m n) k) f)
      (coeff (max (max m n) k) g)) with h | h
  · exact le_max_of_le_left (pow_le_pow_left' h _)
  · exact le_max_of_le_right (pow_le_pow_left' h _)

variable (K v O p)

/-- The valuation `Perfection(O/(p)) → ℝ≥0`.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `preVal(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`. -/
/-
**PreTilt.val** 是 Mathlib 中的一个定义，位于命名空间 `PreTilt`。
形式化陈述：val : Valuation (PreTilt O p) Real>=0 where toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PreTilt.valAux_zero`：valAux_zero : valAux K v O p 0 = 0
· 使用定理 `PreTilt.valAux_one`：valAux_one : valAux K v O p 1 = 1
· 使用定理 `PreTilt.valAux_mul`：valAux_mul (f g : PreTilt O p) : valAux K v O p (f *
 g) = valAux K v O p f * valAux K v O p g
· 使用定理 `PreTilt.valAux_add`：valAux_add (f g : PreTilt O p) : valAux K v O p (f +
 g) <= max (valAux K v O p f) (valAux K v O p g)

--- 原说明 ---
The valuation `Perfection(O/(p)) → ℝ≥0`.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `preVal(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`.
-/
noncomputable def val : Valuation (PreTilt O p) ℝ≥0 where
  toFun := valAux K v O p
  map_one' := valAux_one hv
  map_mul' := valAux_mul hv
  map_zero' := valAux_zero
  map_add_le_max' := valAux_add hv

variable {K v O p}
/-
**PreTilt.map_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：map_eq_zero {f : PreTilt O p} : val K v O hv p f = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Perfection.ext`：ext {f g : Perfection R p} (h : forall n, coeff R p n f 
= coeff R p n g) : f = g
· 使用定理 `ModP.instCharPOfPrimeOfFactNotIsUnitCast`：∀ (O : Type u₂) [inst : CommRi
ng O] (p : ℕ) [Fact (Nat.Prime p)] [hvp : Fact ¬IsUnit ↑p], CharP (ModP O p) p
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `PreTilt.valAux_eq`：valAux_eq {f : PreTilt O p} {n : Nat} (hfn : coeff n 
f != 0) : valAux K v O p f = ModP.preVal K v O p (coeff n f) ^ p ^ n
· 使用定理 `ModP.preVal_eq_zero`：preVal_eq_zero {x : ModP O p} : preVal K v O p x = 
0 ↔ x = 0 where mp h
-/
theorem map_eq_zero {f : PreTilt O p} : val K v O hv p f = 0 ↔ f = 0 := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact iff_of_true (Valuation.map_zero _) rfl
  obtain ⟨n, hn⟩ : ∃ n, coeff n f ≠ 0 := not_forall.1 fun h => hf0 <| Perfection.ext h
  change valAux K v O p f = 0 ↔ f = 0; refine iff_of_false (fun hvf => hn ?_) hf0
  rw [valAux_eq hv hn] at hvf
  replace hvf := eq_zero_of_pow_eq_zero hvf
  rwa [ModP.preVal_eq_zero hv] at hvf

end Classical

include hv

/-
**PreTilt.isDomain** 是 Mathlib 中的一个定理，位于命名空间 `PreTilt`。
形式化陈述：isDomain : IsDomain (PreTilt O p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用引理 `CharP.nontrivial_of_char_ne_one`：nontrivial_of_char_ne_one {v : Nat} (hv
 : v != 1) [hr : CharP R v] : Nontrivial R
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `PreTilt.instCharP`：∀ (O : Type u₂) [inst : CommRing O] (p : ℕ) [inst_1 :
 Fact (Nat.Prime p)] [inst_2 : Fact ¬IsUnit ↑p],   CharP (PreTilt O p) p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PreTilt.map_eq_zero`：map_eq_zero {f : PreTilt O p} : val K v O hv p f = 
0 ↔ f = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
-/
theorem isDomain : IsDomain (PreTilt O p) := by
  have hp : Nat.Prime p := Fact.out
  have : Nontrivial (PreTilt O p) := ⟨(CharP.nontrivial_of_char_ne_one hp.ne_one).1⟩
  have : NoZeroDivisors (PreTilt O p) :=
    ⟨fun hfg => by
      simp_rw [← map_eq_zero hv] at hfg ⊢; contrapose! hfg; rw [Valuation.map_mul]
      exact mul_ne_zero hfg.1 hfg.2⟩
  exact NoZeroDivisors.to_isDomain _

end PreTilt

/-- The tilt of a field, as defined in Perfectoid Spaces by Peter Scholze, as in
[scholze2011perfectoid]. Given a field `K` with valuation `K → ℝ≥0` and ring of integers `O`,
this is implemented as the fraction field of the perfection of `O/(p)`. -/
/-
**Tilt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Tilt [Fact p.Prime] [hvp : Fact (v p != 1)]
参数：v p != 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tilt of a field, as defined in Perfectoid Spaces by Peter Scholze, as in
[scholze2011perfectoid]. Given a field `K` with valuation `K → ℝ≥0` and ring of 
integers `O`,
this is implemented as the fraction field of the perfection of `O/(p)`.
-/
def Tilt [Fact p.Prime] [hvp : Fact (v p ≠ 1)] :=
  have _ := Fact.mk <| mt hv.one_of_isUnit <| (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  FractionRing (PreTilt O p)

namespace Tilt

/-
**Tilt.** 是 Mathlib 中的一个实例，位于命名空间 `Tilt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Fact p.Prime] [hvp : Fact (v p ≠ 1)] : Field (Tilt K v O hv p) :=
  #adaptation_note /-- This type ascription was not needed prior to nightly-2026-05-17. -/
  haveI : Fact ¬IsUnit (p : O) :=
    Fact.mk <| mt hv.one_of_isUnit <| (map_natCast (algebraMap O K) p).symm ▸ hvp.1
  haveI := PreTilt.isDomain K v O hv p
  inferInstanceAs <| Field (FractionRing (PreTilt O p))

end Tilt

end Perfectoid

