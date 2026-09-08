/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis

/-!
# Basic constructions for multiseries

## Main definitions

Let `[b₁, ..., bₙ]` be our basis.

* `const c` represents a constant multiseries `c • b₁⁰ ... bₙ⁰`.
  Then we define `zero` and `one` in terms of it.
* `monomial k` represents a monomial `bₖ`.
* `monomialRpow k r` represents a monomial `bₖʳ`.

For each construction, we provide two definitions: one for `Multiseries` and one for
`MultiseriesExpansion`. We then prove structural `simp`-lemmas describing their relationships with
`MultiseriesExpansion.seq` and `MultiseriesExpansion.toFun`. Finally, we prove that all
constructions are `Sorted` and `Approximates` their attached functions.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

open Filter Stream' Topology

mutual

/-- `Multiseries`-part of `MultiseriesExpansion.const`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const** 是 Mathlib 中
的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：(basis_hd : ℝ → ℝ) →   (basis_tl : Tactic.ComputeAsymptotics.Basis) →     
ℝ → Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiseries`-part of `MultiseriesExpansion.const`.
-/
def Multiseries.const (basis_hd : ℝ → ℝ) (basis_tl : Basis) (c : ℝ) :
    Multiseries basis_hd basis_tl :=
  .cons 0 (const basis_tl c) .nil

/-- Multiseries representing a constant. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.const** 是 Mathlib 中的一个定义，位于命名空间
 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：const (basis : Basis) (c : Real) : MultiseriesExpansion basis
参数：basis : Basis；c : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiseries representing a constant.
-/
def const (basis : Basis) (c : ℝ) : MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal c
  | List.cons basis_hd basis_tl => mk (Multiseries.const basis_hd basis_tl c) (fun _ ↦ c)

end

/-- Neutral element for addition. It is `0 : ℝ` for the empty basis and `[]` otherwise. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.zero** 是 Mathlib 中的一个定义，位于命名空间 
`Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：{basis : Tactic.ComputeAsymptotics.Basis} → Tactic.ComputeAsymptotics.Mult
iseriesExpansion basis
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Neutral element for addition. It is `0 : ℝ` for the empty basis and `[]` otherwi
se.
-/
def zero {basis : Basis} : MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal 0
  | List.cons _ _ => mk .nil (fun _ ↦ 0)

/-- This instance is needed to create an instance for `AddCommMonoid (MultiseriesExpansion basis)`,
which is necessary for using the `abel` tactic in our proofs. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.** 是 Mathlib 中的一个实例，位于命名空间 `Tac
tic.ComputeAsymptotics.MultiseriesExpansion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is needed to create an instance for `AddCommMonoid (MultiseriesExp
ansion basis)`,
which is necessary for using the `abel` tactic in our proofs.
-/
instance {basis : Basis} : Zero (MultiseriesExpansion basis) where
  zero := zero

/-- This instance is needed to create an instance for `AddCommMonoid (MultiseriesExpansion basis)`,
which is necessary for using the `abel` tactic in our proofs. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.** 是 Mathlib 中的一个实例，位于命名空间 `Tac
tic.ComputeAsymptotics.MultiseriesExpansion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is needed to create an instance for `AddCommMonoid (MultiseriesExp
ansion basis)`,
which is necessary for using the `abel` tactic in our proofs.
-/
instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Zero (Multiseries basis_hd basis_tl) where
  zero := .nil

/-- `Multiseries`-part of `MultiseriesExpansion.one`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.one** 是 Mathlib 中的一
个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：{basis_hd : ℝ → ℝ} →   {basis_tl : Tactic.ComputeAsymptotics.Basis} →     
Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiseries`-part of `MultiseriesExpansion.one`.
-/
def Multiseries.one {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Multiseries basis_hd basis_tl :=
  Multiseries.const _ _ 1

/-- Neutral element for multiplication. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.one** 是 Mathlib 中的一个定义，位于命名空间 `
Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：{basis : Tactic.ComputeAsymptotics.Basis} → Tactic.ComputeAsymptotics.Mult
iseriesExpansion basis
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Neutral element for multiplication.
-/
def one {basis : Basis} : MultiseriesExpansion basis :=
  const basis 1

mutual

/-- `Multiseries`-part of `MultiseriesExpansion.monomialRpow`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomialRpow** 是 Ma
thlib 中的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`
。
形式化陈述：(basis_hd : ℝ → ℝ) →   (basis_tl : Tactic.ComputeAsymptotics.Basis) →     
ℕ → ℝ → Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basi
s_tl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiseries`-part of `MultiseriesExpansion.monomialRpow`.
-/
noncomputable def Multiseries.monomialRpow (basis_hd : ℝ → ℝ) (basis_tl : Basis) (n : ℕ) (r : ℝ) :
    Multiseries basis_hd basis_tl :=
  match n with
  | 0 => .cons r one .nil
  | m + 1 => .cons 0 (monomialRpow _ m r) .nil

/-- Multiseries representing `basis[n] ^ r`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow** 是 Mathlib 中的一个定义
，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：(basis : Tactic.ComputeAsymptotics.Basis) → ℕ → ℝ → Tactic.ComputeAsymptot
ics.MultiseriesExpansion basis
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiseries representing `basis[n] ^ r`.
-/
noncomputable def monomialRpow (basis : Basis) (n : ℕ) (r : ℝ) : MultiseriesExpansion basis :=
  match basis with
  | [] => default
  | List.cons basis_hd basis_tl =>
    mk (Multiseries.monomialRpow _ _ n r) ((basis_hd :: basis_tl)[n]! ^ r)

end

/-- `Multiseries`-part of `MultiseriesExpansion.monomial`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomial** 是 Mathli
b 中的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：(basis_hd : ℝ → ℝ) →   (basis_tl : Tactic.ComputeAsymptotics.Basis) →     
ℕ → Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiseries`-part of `MultiseriesExpansion.monomial`.
-/
noncomputable def Multiseries.monomial (basis_hd : ℝ → ℝ) (basis_tl : Basis) (n : ℕ) :
    Multiseries basis_hd basis_tl :=
  Multiseries.monomialRpow _ _ n 1

/-- Multiseries representing `basis[n]`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial** 是 Mathlib 中的一个定义，位于命
名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：(basis : Tactic.ComputeAsymptotics.Basis) → ℕ → Tactic.ComputeAsymptotics.
MultiseriesExpansion basis
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiseries representing `basis[n]`.
-/
noncomputable def monomial (basis : Basis) (n : ℕ) : MultiseriesExpansion basis :=
  monomialRpow _ n 1
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.zero_def** 是 Mathlib 中的一个定理，位于命
名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)},   0 =     Tactic.ComputeAs
ymptotics.MultiseriesExpansion.mk Tactic.ComputeAsymptotics.MultiseriesExpansion
.Multiseries.nil       fun x => 0
参数：ℝ → ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_def {basis_hd basis_tl} :
    (0 : MultiseriesExpansion (basis_hd :: basis_tl)) = mk .nil (fun _ ↦ 0) :=
  rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.zero_def** 是 Mathli
b 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis},   0 = T
actic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.nil
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Multiseries.zero_def {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (0 : Multiseries basis_hd basis_tl) = .nil := rfl
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const_def** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} (c : ℝ),
   Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const basis_hd bas
is_tl c =     Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons 0 
      (Tactic.ComputeAsymptotics.MultiseriesExpansion.const basis_tl c)       Ta
ctic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.nil
参数：c : ℝ；Tactic.ComputeAsymptotics.MultiseriesExpansion.const basis_tl c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const.eq_1`：∀
 (basis_hd : ℝ → ℝ) (basis_tl : Tactic.ComputeAsymptotics.Basis) (c : ℝ),   Tact
ic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Multiseries.const_def {basis_hd basis_tl} (c : ℝ) :
    Multiseries.const basis_hd basis_tl c =
    Multiseries.cons 0 (MultiseriesExpansion.const basis_tl c) .nil := by
  simp [Multiseries.const]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.const_toFun'** 是 Mathlib 中的一个定理
，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis} {c : ℝ},   (Tactic.ComputeAsym
ptotics.MultiseriesExpansion.const basis c).toFun = fun x => c
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.const basis c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.const.eq_1`：∀ (c : ℝ),   
Tactic.ComputeAsymptotics.MultiseriesExpansion.const [] c = Tactic.ComputeAsympt
otics.MultiseriesExpansion.ofReal c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.const.eq_2`：∀ (c : ℝ) (ba
sis_hd : ℝ → ℝ) (basis_tl : List (ℝ → ℝ)),   Tactic.ComputeAsymptotics.Multiseri
esExpansion.const (basis_hd :: basis_tl) c =   …
-/
theorem const_toFun' {basis : Basis} {c : ℝ} : (const basis c).toFun = fun _ ↦ c := by
  match basis with
  | [] => simp [const, ofReal, toReal]
  | List.cons _ _ => simp [const]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.const_seq** 是 Mathlib 中的一个定理，位于
命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)} {c : ℝ},   (Tactic.ComputeA
symptotics.MultiseriesExpansion.const (basis_hd :: basis_tl) c).seq =     Tactic
.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const basis_hd basis_tl c
参数：ℝ → ℝ；Tactic.ComputeAsymptotics.MultiseriesExpansion.const (basis_hd :: basis
_tl) c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.const.eq_2`：∀ (c : ℝ) (ba
sis_hd : ℝ → ℝ) (basis_tl : List (ℝ → ℝ)),   Tactic.ComputeAsymptotics.Multiseri
esExpansion.const (basis_hd :: basis_tl) c =   …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const.eq_1`：∀
 (basis_hd : ℝ → ℝ) (basis_tl : Tactic.ComputeAsymptotics.Basis) (c : ℝ),   Tact
ic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem const_seq {basis_hd basis_tl} {c : ℝ} :
    (const (basis_hd :: basis_tl) c).seq = Multiseries.const basis_hd basis_tl c := by
  simp [const, Multiseries.const]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.zero_toFun** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis}, Tactic.ComputeAsymptotics.Mul
tiseriesExpansion.zero.toFun = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_toFun {basis : Basis} : (@zero basis).toFun = 0 := by
  match basis with
  | [] => rfl
  | List.cons _ _ => rfl
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.one_def** 是 Mathlib
 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis},   Tacti
c.ComputeAsymptotics.MultiseriesExpansion.Multiseries.one =     Tactic.ComputeAs
ymptotics.MultiseriesExpansion.Multiseries.cons 0 Tactic.ComputeAsymptotics.Mult
iseriesExpansion.one       Tactic.ComputeAsymptotics.MultiseriesExpansion.Multis
eries.nil
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const_def`：∀ 
{basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} (c : ℝ),   Tacti
c.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Multiseries.one_def {basis_hd basis_tl} :
    @Multiseries.one basis_hd basis_tl = Multiseries.cons 0 MultiseriesExpansion.one .nil := by
  simp [Multiseries.one, Multiseries.const_def, MultiseriesExpansion.one]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.one_toFun** 是 Mathlib 中的一个定理，位于
命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis}, Tactic.ComputeAsymptotics.Mul
tiseriesExpansion.one.toFun = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.const_toFun'`：∀ {basis : 
Tactic.ComputeAsymptotics.Basis} {c : ℝ},   (Tactic.ComputeAsymptotics.Multiseri
esExpansion.const basis c).toFun = fun x => c
-/
theorem one_toFun {basis : Basis} : (@one basis).toFun = 1 := by
  simp [one]
  rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.one_seq** 是 Mathlib 中的一个定理，位于命名
空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis},   Tacti
c.ComputeAsymptotics.MultiseriesExpansion.one.seq =     Tactic.ComputeAsymptotic
s.MultiseriesExpansion.Multiseries.one
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.const.eq_2`：∀ (c : ℝ) (ba
sis_hd : ℝ → ℝ) (basis_tl : List (ℝ → ℝ)),   Tactic.ComputeAsymptotics.Multiseri
esExpansion.const (basis_hd :: basis_tl) c =   …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (@one (basis_hd :: basis_tl)).seq = Multiseries.one := by
  simp [one, Multiseries.one, const]

mutual
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const_sorted** 是 Ma
thlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`
。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {c : ℝ},
   (Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const basis_hd ba
sis_tl c).Sorted
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const basis_hd bas
is_tl c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const_sorted.
_mutual`：∀ {c : ℝ} (x : (_ : ℝ → ℝ) ×' Tactic.ComputeAsymptotics.Basis ⊕' Tactic
.ComputeAsymptotics.Basis),   PSum.casesOn x (fun _x => (Tactic.Compu…
-/
theorem Multiseries.const_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} :
    (Multiseries.const basis_hd basis_tl c).Sorted := by
  simp only [Multiseries.const]
  exact const_sorted.cons_nil

/-- Constants are well-ordered. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.const_sorted** 是 Mathlib 中的一个定理
，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis} {c : ℝ},   (Tactic.ComputeAsym
ptotics.MultiseriesExpansion.const basis c).Sorted
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.const basis c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const_sorted.
_mutual`：∀ {c : ℝ} (x : (_ : ℝ → ℝ) ×' Tactic.ComputeAsymptotics.Basis ⊕' Tactic
.ComputeAsymptotics.Basis),   PSum.casesOn x (fun _x => (Tactic.Compu…

--- 原说明 ---
Constants are well-ordered.
-/
theorem const_sorted {basis : Basis} {c : ℝ} :
    (const basis c).Sorted := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [const, sorted_iff_seq_sorted, mk_seq] using Multiseries.const_sorted

end

/-- Zero is well-ordered. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.zero_sorted** 是 Mathlib 中的一个定理，
位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis}, Tactic.ComputeAsymptotics.Mul
tiseriesExpansion.Sorted 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted.nil`：nil (f : Real
 -> Real) : Sorted (basis

--- 原说明 ---
Zero is well-ordered.
-/
theorem zero_sorted {basis : Basis} : (0 : MultiseriesExpansion basis).Sorted := by
  cases basis with
  | nil => constructor
  | cons => apply Sorted.nil
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.one_sorted** 是 Math
lib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis},   Tacti
c.ComputeAsymptotics.MultiseriesExpansion.Multiseries.one.Sorted
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.const_sorted`
：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {c : ℝ},   (T
actic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.con…
-/
theorem Multiseries.one_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (Multiseries.one : Multiseries basis_hd basis_tl).Sorted :=
  Multiseries.const_sorted

/-- `one` is Sorted. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.one_sorted** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis}, Tactic.ComputeAsymptotics.Mul
tiseriesExpansion.one.Sorted
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.const_sorted`：∀ {basis : 
Tactic.ComputeAsymptotics.Basis} {c : ℝ},   (Tactic.ComputeAsymptotics.Multiseri
esExpansion.const basis c).Sorted

--- 原说明 ---
`one` is Sorted.
-/
theorem one_sorted {basis : Basis} : one.Sorted (basis := basis) :=
  const_sorted

/-- The constant multiseries approximates the constant function. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.const_approximates** 是 Mathlib 
中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {c : ℝ} {basis : Tactic.ComputeAsymptotics.Basis},   Tactic.ComputeAsymp
totics.WellFormedBasis basis →     (Tactic.ComputeAsymptotics.MultiseriesExpansi
on.const basis c).Approximates
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.const basis c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant multiseries approximates the constant function.
-/
theorem const_approximates {c : ℝ} {basis : Basis} (h_basis : WellFormedBasis basis) :
    (const basis c).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [const, Multiseries.const]
    apply (const_approximates h_basis.tail).cons _ (by simp)
    exact Majorized.const <| h_basis.tendsto_atTop (by simp)

/-- `zero` approximates the zero function. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.zero_approximates** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis}, Tactic.ComputeAsymptotics.Mul
tiseriesExpansion.zero.Approximates
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f

--- 原说明 ---
`zero` approximates the zero function.
-/
theorem zero_approximates {basis : Basis} :
    (@zero basis).Approximates := by
  cases basis with
  | nil => simp [zero]
  | cons => exact Approximates.nil (by rfl)

/-- `one` approximates the unit function. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.one_approximates** 是 Mathlib 中的
一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis},   Tactic.ComputeAsymptotics.W
ellFormedBasis basis → Tactic.ComputeAsymptotics.MultiseriesExpansion.one.Approx
imates
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.const_approximates`：∀ {c 
: ℝ} {basis : Tactic.ComputeAsymptotics.Basis},   Tactic.ComputeAsymptotics.Well
FormedBasis basis →     (Tactic.ComputeAsymptotics.Mult…

--- 原说明 ---
`one` approximates the unit function.
-/
theorem one_approximates {basis : Basis} (h_basis : WellFormedBasis basis) :
    (@one basis).Approximates :=
  const_approximates h_basis

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow_toFun** 是 Mathlib 
中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis} {n : Fin (List.length basis)} 
{r : ℝ},   (Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow basis (↑
n) r).toFun = basis[n] ^ r
参数：List.length basis；Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow
 basis (↑n) r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow.eq_2`：∀ (n :
 ℕ) (r : ℝ) (basis_hd : ℝ → ℝ) (basis_tl : List (ℝ → ℝ)),   Tactic.ComputeAsympt
otics.MultiseriesExpansion.monomialRpow (basis_hd :: b…
· 使用定理 `getElem!_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
-/
theorem monomialRpow_toFun {basis : Basis} {n : Fin (List.length basis)} {r : ℝ} :
    (monomialRpow basis n r).toFun = basis[n] ^ r := by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl => cases n using Fin.cases <;> simp [monomialRpow]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow_seq** 是 Mathlib 中的
一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {n : ℕ} 
{r : ℝ},   (Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow (basis_h
d :: basis_tl) n r).seq =     Tactic.ComputeAsymptotics.MultiseriesExpansion.Mul
tiseries.monomialRpow basis_hd basis_tl n r
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow (basis_hd :: basi
s_tl) n r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow.eq_2`：∀ (n :
 ℕ) (r : ℝ) (basis_hd : ℝ → ℝ) (basis_tl : List (ℝ → ℝ)),   Tactic.ComputeAsympt
otics.MultiseriesExpansion.monomialRpow (basis_hd :: b…
· 使用定理 `List.getElem!_eq_getElem?_getD`：∀ {α : Type u_1} [inst : Inhabited α] {l
 : List α} {i : ℕ}, l[i]! = l[i]?.getD default
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monomialRpow_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} {r : ℝ} :
    (monomialRpow (basis_hd :: basis_tl) n r).seq = Multiseries.monomialRpow _ _ n r := by
  simp [monomialRpow]

mutual
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomialRpow_sorted
** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multi
series`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {n : ℕ} 
{r : ℝ},   (Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomialR
pow basis_hd basis_tl n r).Sorted
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomialRpow basis
_hd basis_tl n r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomialRpow_
sorted._mutual`：∀ {r : ℝ} (x : (_ : ℝ → ℝ) ×' (_ : Tactic.ComputeAsymptotics.Bas
is) ×' ℕ ⊕' (_ : Tactic.ComputeAsymptotics.Basis) ×' ℕ),   PSum.casesOn x   …
-/
theorem Multiseries.monomialRpow_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} {r : ℝ} :
    (@Multiseries.monomialRpow basis_hd basis_tl n r).Sorted := by
  cases n with
  | zero =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil const_sorted
  | succ m =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil monomialRpow_sorted

/-- `monomial` is well-ordered. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow_sorted** 是 Mathlib
 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis} {n : ℕ} {r : ℝ},   (Tactic.Com
puteAsymptotics.MultiseriesExpansion.monomialRpow basis n r).Sorted
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow basis n r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomialRpow_
sorted._mutual`：∀ {r : ℝ} (x : (_ : ℝ → ℝ) ×' (_ : Tactic.ComputeAsymptotics.Bas
is) ×' ℕ ⊕' (_ : Tactic.ComputeAsymptotics.Basis) ×' ℕ),   PSum.casesOn x   …

--- 原说明 ---
`monomial` is well-ordered.
-/
theorem monomialRpow_sorted {basis : Basis} {n : ℕ} {r : ℝ} :
    (monomialRpow basis n r).Sorted := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [sorted_iff_seq_sorted, monomialRpow_seq] using Multiseries.monomialRpow_sorted

end

/-- `monomialRpow` approximates the monomial function. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow_approximates** 是 M
athlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis} {n : Fin (List.length basis)} 
{r : ℝ},   Tactic.ComputeAsymptotics.WellFormedBasis basis →     (Tactic.Compute
Asymptotics.MultiseriesExpansion.monomialRpow basis (↑n) r).Approximates
参数：List.length basis；Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow
 basis (↑n) r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`monomialRpow` approximates the monomial function.
-/
theorem monomialRpow_approximates {basis : Basis} {n : Fin (List.length basis)} {r : ℝ}
    (h_basis : WellFormedBasis basis) :
    (monomialRpow basis n r).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [List.length_cons, monomialRpow, Fin.is_lt, getElem!_pos]
    cases n using Fin.cases with
    | zero =>
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Multiseries.monomialRpow,
        List.getElem_cons_zero]
      apply (one_approximates h_basis.tail).cons _ (by simp)
      exact Majorized.self <| h_basis.tendsto_atTop (by simp)
    | succ m =>
      simp only [Fin.val_succ, Multiseries.monomialRpow, List.getElem_cons_succ]
      apply (monomialRpow_approximates h_basis.tail).cons _ (by simp)
      apply h_basis.tail_pow_majorized_head (by simp)

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial_toFun** 是 Mathlib 中的一个
定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis} {n : ℕ} (h : n < List.length b
asis),   (Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial basis n).toFun
 = basis[n]
参数：h : n < List.length basis；Tactic.ComputeAsymptotics.MultiseriesExpansion.mono
mial basis n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Real.pi_rpow_one`：pi_rpow_one {α : Type*} (f : α -> Real) : f ^ (1 : Rea
l) = f
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow_toFun`：∀ {ba
sis : Tactic.ComputeAsymptotics.Basis} {n : Fin (List.length basis)} {r : ℝ},   
(Tactic.ComputeAsymptotics.MultiseriesExpansion.monomia…
-/
theorem monomial_toFun {basis : Basis} {n : ℕ} (h : n < basis.length) :
    (monomial basis n).toFun = basis[n] := by
  let n' : Fin basis.length := ⟨n, h⟩
  conv_lhs => rw [show n = n'.val by simp [n']]
  convert! monomialRpow_toFun
  simp
  grind
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial_toFun'** 是 Mathlib 中的一
个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis} {n : Fin (List.length basis)},
   (Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial basis ↑n).toFun = ba
sis[n]
参数：List.length basis；Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial bas
is ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial_toFun`：∀ {basis 
: Tactic.ComputeAsymptotics.Basis} {n : ℕ} (h : n < List.length basis),   (Tacti
c.ComputeAsymptotics.MultiseriesExpansion.monomial …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem monomial_toFun' {basis : Basis} {n : Fin basis.length} :
    (monomial basis n).toFun = basis[n] := by
  simp

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial_seq** 是 Mathlib 中的一个定理
，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {n : ℕ},
   (Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial (basis_hd :: basis_t
l) n).seq =     Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monom
ial basis_hd basis_tl n
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial (basis_hd :: basis_tl
) n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow_seq`：∀ {basi
s_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {n : ℕ} {r : ℝ},   (T
actic.ComputeAsymptotics.MultiseriesExpansion.monomia…
-/
theorem monomial_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} :
    (monomial (basis_hd :: basis_tl) n).seq = Multiseries.monomial _ _ n :=
  monomialRpow_seq
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomial_sorted** 是
 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseri
es`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {n : ℕ},
   (Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomial basis_hd
 basis_tl n).Sorted
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomial basis_hd 
basis_tl n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.monomialRpow_
sorted`：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {n : ℕ
} {r : ℝ},   (Tactic.ComputeAsymptotics.MultiseriesExpansion.Multise…
-/
theorem Multiseries.monomial_sorted {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} :
    (@Multiseries.monomial basis_hd basis_tl n).Sorted :=
  Multiseries.monomialRpow_sorted

/-- `monomial` is well-ordered. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial_sorted** 是 Mathlib 中的一
个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis} {n : ℕ},   (Tactic.ComputeAsym
ptotics.MultiseriesExpansion.monomial basis n).Sorted
参数：Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial basis n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow_sorted`：∀ {b
asis : Tactic.ComputeAsymptotics.Basis} {n : ℕ} {r : ℝ},   (Tactic.ComputeAsympt
otics.MultiseriesExpansion.monomialRpow basis n r).Sorte…

--- 原说明 ---
`monomial` is well-ordered.
-/
theorem monomial_sorted {basis : Basis} {n : ℕ} : (monomial basis n).Sorted :=
  monomialRpow_sorted

/-- `monomial` approximates the monomial function. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial_approximates** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：∀ {basis : Tactic.ComputeAsymptotics.Basis} {n : Fin (List.length basis)},
   Tactic.ComputeAsymptotics.WellFormedBasis basis →     (Tactic.ComputeAsymptot
ics.MultiseriesExpansion.monomial basis ↑n).Approximates
参数：List.length basis；Tactic.ComputeAsymptotics.MultiseriesExpansion.monomial bas
is ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.monomialRpow_approximates
`：∀ {basis : Tactic.ComputeAsymptotics.Basis} {n : Fin (List.length basis)} {r :
 ℝ},   Tactic.ComputeAsymptotics.WellFormedBasis basis →     (…

--- 原说明 ---
`monomial` approximates the monomial function.
-/
theorem monomial_approximates {basis : Basis} {n : Fin (List.length basis)}
    (h_basis : WellFormedBasis basis) : (monomial basis n).Approximates :=
  monomialRpow_approximates h_basis

end MultiseriesExpansion

end Tactic.ComputeAsymptotics

