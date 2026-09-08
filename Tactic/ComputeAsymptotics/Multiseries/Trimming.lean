/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs

/-!
# Trimming of multiseries

A multiseries is *trimmed* when its leading coefficient (the head of its expansion) is itself
trimmed and non-zero. For a trimmed multiseries, the leading monomial captures the main
asymptotic behavior of the approximated function.

## Main definitions

* `IsZero`: a multiseries represents the zero function — it is either the real number `0`
  (for the empty basis) or has an empty underlying sequence (`.nil`).
* `Trimmed` and `Multiseries.Trimmed`: a multiseries is trimmed in the sense above. The former
  is defined inductively for `MultiseriesExpansion`, and the latter for `Multiseries` is
  derived from it.

We also prove structural lemmas relating these predicates to `seq` and to the `cons`/`nil`
constructors.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

open Filter Topology Stream'

/-- A multiseries is zero if it is the real constant `0` or has an empty sequence. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.IsZero** 是 Mathlib 中的一个归纳类型，位于命
名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：{basis : Tactic.ComputeAsymptotics.Basis} → Tactic.ComputeAsymptotics.Mult
iseriesExpansion basis → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiseries is zero if it is the real constant `0` or has an empty sequence.
-/
inductive IsZero : {basis : Basis} → MultiseriesExpansion basis → Prop
| const {c : MultiseriesExpansion []} (hc : c.toReal = 0) : IsZero c
| nil {basis_hd} {basis_tl} (f) : @IsZero (basis_hd :: basis_tl) (mk .nil f)

namespace IsZero

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.IsZero.const_iff** 是 Mathlib 中的
一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.IsZero`。
形式化陈述：const_iff {c : MultiseriesExpansion []} : IsZero c ↔ c.toReal = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_iff {c : MultiseriesExpansion []} : IsZero c ↔ c.toReal = 0 := by
  constructor <;> grind [IsZero]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.IsZero.iff_seq_eq_nil** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.IsZero`。
形式化陈述：iff_seq_eq_nil {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd ::
 basis_tl)} : IsZero ms ↔ ms.seq = .nil where mp h
参数：basis_hd :: basis_tl。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.mk_seq`：mk_seq {basis_hd 
basis_tl} (s : Multiseries basis_hd basis_tl) (f : Real -> Real) : (mk (basis_hd
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem iff_seq_eq_nil {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    IsZero ms ↔ ms.seq = .nil where
  mp h := by cases h; rw [mk_seq]
  mpr h := by
    convert IsZero.nil ms.toFun
    simp [h]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.IsZero.approximates_zero** 是 Ma
thlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.IsZero`。
形式化陈述：approximates_zero {basis : Basis} {ms : MultiseriesExpansion basis} (h_zer
o : IsZero ms) (h_approx : ms.Approximates) : ms.toFun =ᶠ[atTop] 0
参数：h_zero : IsZero ms；h_approx : ms.Approximates。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem approximates_zero {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_zero : IsZero ms) (h_approx : ms.Approximates) :
    ms.toFun =ᶠ[atTop] 0 := by
  cases h_zero with
  | const hc => simp [hc, Pi.zero_def]
  | nil => simpa using h_approx
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.IsZero.not_cons** 是 Mathlib 中的一
个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.IsZero`。
形式化陈述：not_cons {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion b
asis_tl} {tl : Multiseries basis_hd basis_tl} {f : Real -> Real} : ¬ @IsZero (ba
sis_hd :: basis_tl) (mk (.cons exp coef tl) f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} :
    ¬ @IsZero (basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  simp

end IsZero

/-- We call a multiseries `Trimmed` if it is either a constant, `.nil`, or `cons (exp, coef) tl`
where `coef` is trimmed and is not zero. Intuitively, when a multiseries is trimmed, its leading
monomial gives the main asymptotic behavior of the approximated function. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Trimmed** 是 Mathlib 中的一个归纳类型，位于
命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：{basis : Tactic.ComputeAsymptotics.Basis} → Tactic.ComputeAsymptotics.Mult
iseriesExpansion basis → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We call a multiseries `Trimmed` if it is either a constant, `.nil`, or `cons (ex
p, coef) tl`
where `coef` is trimmed and is not zero. Intuitively, when a multiseries is trim
med, its leading
monomial gives the main asymptotic behavior of the approximated function.
-/
inductive Trimmed : {basis : Basis} → MultiseriesExpansion basis → Prop
| const {c : ℝ} : @Trimmed [] c
| nil {basis_hd} {basis_tl} {f} : @Trimmed (basis_hd :: basis_tl) (mk .nil f)
| cons {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
  {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} (h_trimmed : coef.Trimmed)
  (h_ne_zero : ¬ IsZero coef) :
  @Trimmed (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)

/-- We call a `Multiseries` `Trimmed` if it is either `.nil` or `cons (exp, coef) tl` where `coef`
is trimmed and is not zero. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Trimmed** 是 Mathlib
 中的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：{basis_hd : ℝ → ℝ} →   {basis_tl : Tactic.ComputeAsymptotics.Basis} →     
Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl → P
rop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We call a `Multiseries` `Trimmed` if it is either `.nil` or `cons (exp, coef) tl
` where `coef`
is trimmed and is not zero.
-/
def Multiseries.Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : Multiseries basis_hd basis_tl) : Prop :=
  (mk ms 0).Trimmed
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.trimmed_iff_seq_trimmed** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：trimmed_iff_seq_trimmed {basis_hd : Real -> Real} {basis_tl : Basis} (ms :
 MultiseriesExpansion (basis_hd :: basis_tl)) : ms.Trimmed ↔ ms.seq.Trimmed wher
e mp h
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem trimmed_iff_seq_trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    ms.Trimmed ↔ ms.seq.Trimmed where
  mp h := by
    cases h <;> constructor <;> grind
  mpr h := by
    generalize hs : ms.seq = s at h
    cases h with
    | nil =>
      convert Trimmed.nil (f := ms.toFun)
      simp [hs]
    | @cons _ _ exp coef tl _ h_trimmed h_ne_zero =>
      convert Trimmed.cons h_trimmed h_ne_zero (exp := exp) (tl := tl) (f := ms.toFun)
      simp only [ms_eq_mk_iff, hs, and_true]

namespace Multiseries.Trimmed

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Trimmed.nil** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.T
rimmed`。
形式化陈述：nil {basis_hd} {basis_tl} : @Multiseries.Trimmed basis_hd basis_tl .nil
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nil {basis_hd} {basis_tl} :
    @Multiseries.Trimmed basis_hd basis_tl .nil := by
  constructor
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Trimmed.cons** 是 Ma
thlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.
Trimmed`。
形式化陈述：cons {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion basis
_tl} {tl : Multiseries basis_hd basis_tl} (h_coef : coef.Trimmed) (h_ne_zero : ¬
 IsZero coef) : Multiseries.Trimmed (cons exp coef tl)
参数：h_coef : coef.Trimmed；h_ne_zero : ¬ IsZero coef。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons {basis_hd} {basis_tl} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h_coef : coef.Trimmed) (h_ne_zero : ¬ IsZero coef) :
    Multiseries.Trimmed (cons exp coef tl) :=
  MultiseriesExpansion.Trimmed.cons h_coef h_ne_zero

/-- If `cons (exp, coef) tl` is trimmed, then `coef` is trimmed and is not zero. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Trimmed.elim_cons**
 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multise
ries.Trimmed`。
形式化陈述：elim_cons {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion 
basis_tl} {tl : Multiseries basis_hd basis_tl} (h : Multiseries.Trimmed (.cons e
xp coef tl)) : coef.Trimmed ∧ ¬ IsZero coef
参数：h : Multiseries.Trimmed (.cons exp coef tl)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `cons (exp, coef) tl` is trimmed, then `coef` is trimmed and is not zero.
-/
theorem elim_cons {basis_hd} {basis_tl} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : Multiseries.Trimmed (.cons exp coef tl)) :
    coef.Trimmed ∧ ¬ IsZero coef := by
  generalize h_ms : Multiseries.cons exp coef tl = ms at h
  cases h with
  | nil => simp at h_ms
  | cons h_trimmed h_ne_zero =>
    simp at h_ms
    grind

end Multiseries.Trimmed

/-- If `cons (exp, coef) tl` is trimmed, then `coef` is trimmed and is not zero. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.elim_cons** 是 Mathlib 中的一个定理，位于
命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：elim_cons {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion 
basis_tl} {tl : Multiseries basis_hd basis_tl} {f : Real -> Real} (h : Trimmed (
mk (.cons exp coef tl) f)) : coef.Trimmed ∧ ¬ IsZero coef
参数：h : Trimmed (mk (.cons exp coef tl) f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Trimmed.elim_
cons`：elim_cons {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion 
basis_tl} {tl : Multiseries basis_hd basis_tl} (h : Multiseries.Tr…

--- 原说明 ---
If `cons (exp, coef) tl` is trimmed, then `coef` is trimmed and is not zero.
-/
theorem elim_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ}
    (h : Trimmed (mk (.cons exp coef tl) f)) :
    coef.Trimmed ∧ ¬ IsZero coef := by
  simp only [trimmed_iff_seq_trimmed, mk_seq] at h
  exact h.elim_cons

end MultiseriesExpansion

end Tactic.ComputeAsymptotics

