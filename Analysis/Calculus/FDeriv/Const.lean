/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Fréchet derivative of constant functions

This file contains the usual formulas (and existence assertions) for the derivative of constant
functions, including various special cases such as the functions `0`, `1`, `Nat.cast n`,
`Int.cast z`, and other numerals.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Asymptotics Function Filter Set Metric
open scoped Topology NNReal ENNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f : E → F} {x : E} {s : Set E}

section Const

/-
**hasFDerivAtFilter_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_const (c : F) (L : Filter (E × E)) : HasFDerivAtFilter (
fun _ => c) (0 : E ->L[𝕜] F) L
参数：c : F；L : Filter (E × E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.congr_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E 
: Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCom
mGroup E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsLittleOTVS.zero`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasFDerivAtFilter_const (c : F) (L : Filter (E × E)) :
    HasFDerivAtFilter (fun _ => c) (0 : E →L[𝕜] F) L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun _ => by simp
/-
**hasFDerivAtFilter_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_zero (L : Filter (E × E)) : HasFDerivAtFilter (0 : E -> 
F) (0 : E ->L[𝕜] F) L
参数：L : Filter (E × E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasFDerivAtFilter_zero (L : Filter (E × E)) :
    HasFDerivAtFilter (0 : E → F) (0 : E →L[𝕜] F) L := hasFDerivAtFilter_const _ _
/-
**hasFDerivAtFilter_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_one [One F] (L : Filter (E × E)) : HasFDerivAtFilter (1 
: E -> F) (0 : E ->L[𝕜] F) L
参数：L : Filter (E × E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasFDerivAtFilter_one [One F] (L : Filter (E × E)) :
    HasFDerivAtFilter (1 : E → F) (0 : E →L[𝕜] F) L := hasFDerivAtFilter_const _ _
/-
**hasFDerivAtFilter_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_natCast [NatCast F] (n : Nat) (L : Filter (E × E)) : Has
FDerivAtFilter (n : E -> F) (0 : E ->L[𝕜] F) L
参数：n : Nat；L : Filter (E × E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasFDerivAtFilter_natCast [NatCast F] (n : ℕ) (L : Filter (E × E)) :
    HasFDerivAtFilter (n : E → F) (0 : E →L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _
/-
**hasFDerivAtFilter_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_intCast [IntCast F] (z : Int) (L : Filter (E × E)) : Has
FDerivAtFilter (z : E -> F) (0 : E ->L[𝕜] F) L
参数：z : Int；L : Filter (E × E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasFDerivAtFilter_intCast [IntCast F] (z : ℤ) (L : Filter (E × E)) :
    HasFDerivAtFilter (z : E → F) (0 : E →L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _
/-
**hasFDerivAtFilter_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_ofNat (n : Nat) [OfNat F n] (L : Filter (E × E)) : HasFD
erivAtFilter (ofNat(n) : E -> F) (0 : E ->L[𝕜] F) L
参数：n : Nat；L : Filter (E × E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasFDerivAtFilter_ofNat (n : ℕ) [OfNat F n] (L : Filter (E × E)) :
    HasFDerivAtFilter (ofNat(n) : E → F) (0 : E →L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _

@[fun_prop]
/-
**hasStrictFDerivAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_const (c : F) (x : E) : HasStrictFDerivAt (fun _ => c) (
0 : E ->L[𝕜] F) x
参数：c : F；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasStrictFDerivAt_const (c : F) (x : E) :
    HasStrictFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  hasFDerivAtFilter_const _ _

@[fun_prop]
/-
**hasStrictFDerivAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_zero (x : E) : HasStrictFDerivAt (0 : E -> F) (0 : E ->L
[𝕜] F) x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_const`：hasStrictFDerivAt_const (c : F) (x : E) : HasSt
rictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasStrictFDerivAt_zero (x : E) :
    HasStrictFDerivAt (0 : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/-
**hasStrictFDerivAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_one [One F] (x : E) : HasStrictFDerivAt (1 : E -> F) (0 
: E ->L[𝕜] F) x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_const`：hasStrictFDerivAt_const (c : F) (x : E) : HasSt
rictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasStrictFDerivAt_one [One F] (x : E) :
    HasStrictFDerivAt (1 : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/-
**hasStrictFDerivAt_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_natCast [NatCast F] (n : Nat) (x : E) : HasStrictFDerivA
t (n : E -> F) (0 : E ->L[𝕜] F) x
参数：n : Nat；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_const`：hasStrictFDerivAt_const (c : F) (x : E) : HasSt
rictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasStrictFDerivAt_natCast [NatCast F] (n : ℕ) (x : E) :
    HasStrictFDerivAt (n : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/-
**hasStrictFDerivAt_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_intCast [IntCast F] (z : Int) (x : E) : HasStrictFDerivA
t (z : E -> F) (0 : E ->L[𝕜] F) x
参数：z : Int；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_const`：hasStrictFDerivAt_const (c : F) (x : E) : HasSt
rictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasStrictFDerivAt_intCast [IntCast F] (z : ℤ) (x : E) :
    HasStrictFDerivAt (z : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/-
**hasStrictFDerivAt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_ofNat (n : Nat) [OfNat F n] (x : E) : HasStrictFDerivAt 
(ofNat(n) : E -> F) (0 : E ->L[𝕜] F) x
参数：n : Nat；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasStrictFDerivAt_const`：hasStrictFDerivAt_const (c : F) (x : E) : HasSt
rictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasStrictFDerivAt_ofNat (n : ℕ) [OfNat F n] (x : E) :
    HasStrictFDerivAt (ofNat(n) : E → F) (0 : E →L[𝕜] F) x := hasStrictFDerivAt_const _ _

@[fun_prop]
/-
**hasFDerivWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_const (c : F) (x : E) (s : Set E) : HasFDerivWithinAt (f
un _ => c) (0 : E ->L[𝕜] F) s x
参数：c : F；x : E；s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasFDerivWithinAt_const (c : F) (x : E) (s : Set E) :
    HasFDerivWithinAt (fun _ => c) (0 : E →L[𝕜] F) s x :=
  hasFDerivAtFilter_const _ _

@[fun_prop]
/-
**hasFDerivWithinAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_zero (x : E) (s : Set E) : HasFDerivWithinAt (0 : E -> F
) (0 : E ->L[𝕜] F) s x
参数：x : E；s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_const`：hasFDerivWithinAt_const (c : F) (x : E) (s : Se
t E) : HasFDerivWithinAt (fun _ => c) (0 : E ->L[𝕜] F) s x
-/
theorem hasFDerivWithinAt_zero (x : E) (s : Set E) :
    HasFDerivWithinAt (0 : E → F) (0 : E →L[𝕜] F) s x := hasFDerivWithinAt_const _ _ _

@[fun_prop]
/-
**hasFDerivWithinAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_one [One F] (x : E) (s : Set E) : HasFDerivWithinAt (1 :
 E -> F) (0 : E ->L[𝕜] F) s x
参数：x : E；s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_const`：hasFDerivWithinAt_const (c : F) (x : E) (s : Se
t E) : HasFDerivWithinAt (fun _ => c) (0 : E ->L[𝕜] F) s x
-/
theorem hasFDerivWithinAt_one [One F] (x : E) (s : Set E) :
    HasFDerivWithinAt (1 : E → F) (0 : E →L[𝕜] F) s x := hasFDerivWithinAt_const _ _ _

@[fun_prop]
/-
**hasFDerivWithinAt_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_natCast [NatCast F] (n : Nat) (x : E) (s : Set E) : HasF
DerivWithinAt (n : E -> F) (0 : E ->L[𝕜] F) s x
参数：n : Nat；x : E；s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_const`：hasFDerivWithinAt_const (c : F) (x : E) (s : Se
t E) : HasFDerivWithinAt (fun _ => c) (0 : E ->L[𝕜] F) s x
-/
theorem hasFDerivWithinAt_natCast [NatCast F] (n : ℕ) (x : E) (s : Set E) :
    HasFDerivWithinAt (n : E → F) (0 : E →L[𝕜] F) s x :=
  hasFDerivWithinAt_const _ _ _

@[fun_prop]
/-
**hasFDerivWithinAt_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_intCast [IntCast F] (z : Int) (x : E) (s : Set E) : HasF
DerivWithinAt (z : E -> F) (0 : E ->L[𝕜] F) s x
参数：z : Int；x : E；s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_const`：hasFDerivWithinAt_const (c : F) (x : E) (s : Se
t E) : HasFDerivWithinAt (fun _ => c) (0 : E ->L[𝕜] F) s x
-/
theorem hasFDerivWithinAt_intCast [IntCast F] (z : ℤ) (x : E) (s : Set E) :
    HasFDerivWithinAt (z : E → F) (0 : E →L[𝕜] F) s x :=
  hasFDerivWithinAt_const _ _ _

@[fun_prop]
/-
**hasFDerivWithinAt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_ofNat (n : Nat) [OfNat F n] (x : E) (s : Set E) : HasFDe
rivWithinAt (ofNat(n) : E -> F) (0 : E ->L[𝕜] F) s x
参数：n : Nat；x : E；s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivWithinAt_const`：hasFDerivWithinAt_const (c : F) (x : E) (s : Se
t E) : HasFDerivWithinAt (fun _ => c) (0 : E ->L[𝕜] F) s x
-/
theorem hasFDerivWithinAt_ofNat (n : ℕ) [OfNat F n] (x : E) (s : Set E) :
    HasFDerivWithinAt (ofNat(n) : E → F) (0 : E →L[𝕜] F) s x :=
  hasFDerivWithinAt_const _ _ _

@[fun_prop]
/-
**hasFDerivAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E ->L[𝕜]
 F) x
参数：c : F；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const`：hasFDerivAtFilter_const (c : F) (L : Filter (E 
× E)) : HasFDerivAtFilter (fun _ => c) (0 : E ->L[𝕜] F) L
-/
theorem hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  hasFDerivAtFilter_const _ _

@[fun_prop]
/-
**hasFDerivAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_zero (x : E) : HasFDerivAt (0 : E -> F) (0 : E ->L[𝕜] F) x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasFDerivAt_zero (x : E) :
    HasFDerivAt (0 : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
/-
**hasFDerivAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_one [One F] (x : E) : HasFDerivAt (1 : E -> F) (0 : E ->L[𝕜] F
) x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasFDerivAt_one [One F] (x : E) :
    HasFDerivAt (1 : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
/-
**hasFDerivAt_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_natCast [NatCast F] (n : Nat) (x : E) : HasFDerivAt (n : E -> 
F) (0 : E ->L[𝕜] F) x
参数：n : Nat；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasFDerivAt_natCast [NatCast F] (n : ℕ) (x : E) :
    HasFDerivAt (n : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
/-
**hasFDerivAt_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_intCast [IntCast F] (z : Int) (x : E) : HasFDerivAt (z : E -> 
F) (0 : E ->L[𝕜] F) x
参数：z : Int；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasFDerivAt_intCast [IntCast F] (z : ℤ) (x : E) :
    HasFDerivAt (z : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[fun_prop]
/-
**hasFDerivAt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_ofNat (n : Nat) [OfNat F n] (x : E) : HasFDerivAt (ofNat(n) : 
E -> F) (0 : E ->L[𝕜] F) x
参数：n : Nat；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasFDerivAt_ofNat (n : ℕ) [OfNat F n] (x : E) :
    HasFDerivAt (ofNat(n) : E → F) (0 : E →L[𝕜] F) x := hasFDerivAt_const _ _

@[simp, fun_prop]
/-
**differentiableAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_const (c : F) : DifferentiableAt 𝕜 (fun _ => c) x
参数：c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
-/
theorem differentiableAt_const (c : F) : DifferentiableAt 𝕜 (fun _ => c) x :=
  ⟨0, hasFDerivAt_const c x⟩

@[simp, fun_prop]
/-
**differentiableAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_zero (x : E) : DifferentiableAt 𝕜 (0 : E -> F) x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
-/
theorem differentiableAt_zero (x : E) :
    DifferentiableAt 𝕜 (0 : E → F) x := differentiableAt_const _

@[simp, fun_prop]
/-
**differentiableAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_one [One F] (x : E) : DifferentiableAt 𝕜 (1 : E -> F) x
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
-/
theorem differentiableAt_one [One F] (x : E) :
    DifferentiableAt 𝕜 (1 : E → F) x := differentiableAt_const _

@[simp, fun_prop]
/-
**differentiableAt_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_natCast [NatCast F] (n : Nat) (x : E) : DifferentiableAt 
𝕜 (n : E -> F) x
参数：n : Nat；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
-/
theorem differentiableAt_natCast [NatCast F] (n : ℕ) (x : E) :
    DifferentiableAt 𝕜 (n : E → F) x := differentiableAt_const _

@[simp, fun_prop]
/-
**differentiableAt_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_intCast [IntCast F] (z : Int) (x : E) : DifferentiableAt 
𝕜 (z : E -> F) x
参数：z : Int；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
-/
theorem differentiableAt_intCast [IntCast F] (z : ℤ) (x : E) :
    DifferentiableAt 𝕜 (z : E → F) x := differentiableAt_const _

@[simp low, fun_prop]
/-
**differentiableAt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_ofNat (n : Nat) [OfNat F n] (x : E) : DifferentiableAt 𝕜 
(ofNat(n) : E -> F) x
参数：n : Nat；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
-/
theorem differentiableAt_ofNat (n : ℕ) [OfNat F n] (x : E) :
    DifferentiableAt 𝕜 (ofNat(n) : E → F) x := differentiableAt_const _

@[fun_prop]
/-
**differentiableWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_const (c : F) : DifferentiableWithinAt 𝕜 (fun _ => 
c) s x
参数：c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
-/
theorem differentiableWithinAt_const (c : F) : DifferentiableWithinAt 𝕜 (fun _ => c) s x :=
  DifferentiableAt.differentiableWithinAt (differentiableAt_const _)

@[fun_prop]
/-
**differentiableWithinAt_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_zero : DifferentiableWithinAt 𝕜 (0 : E -> F) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_const`：differentiableWithinAt_const (c : F) : Dif
ferentiableWithinAt 𝕜 (fun _ => c) s x
-/
theorem differentiableWithinAt_zero :
    DifferentiableWithinAt 𝕜 (0 : E → F) s x := differentiableWithinAt_const _

@[fun_prop]
/-
**differentiableWithinAt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_one [One F] : DifferentiableWithinAt 𝕜 (1 : E -> F)
 s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_const`：differentiableWithinAt_const (c : F) : Dif
ferentiableWithinAt 𝕜 (fun _ => c) s x
-/
theorem differentiableWithinAt_one [One F] :
    DifferentiableWithinAt 𝕜 (1 : E → F) s x := differentiableWithinAt_const _

@[fun_prop]
/-
**differentiableWithinAt_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_natCast [NatCast F] (n : Nat) : DifferentiableWithi
nAt 𝕜 (n : E -> F) s x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_const`：differentiableWithinAt_const (c : F) : Dif
ferentiableWithinAt 𝕜 (fun _ => c) s x
-/
theorem differentiableWithinAt_natCast [NatCast F] (n : ℕ) :
    DifferentiableWithinAt 𝕜 (n : E → F) s x := differentiableWithinAt_const _

@[fun_prop]
/-
**differentiableWithinAt_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_intCast [IntCast F] (z : Int) : DifferentiableWithi
nAt 𝕜 (z : E -> F) s x
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_const`：differentiableWithinAt_const (c : F) : Dif
ferentiableWithinAt 𝕜 (fun _ => c) s x
-/
theorem differentiableWithinAt_intCast [IntCast F] (z : ℤ) :
    DifferentiableWithinAt 𝕜 (z : E → F) s x := differentiableWithinAt_const _

@[fun_prop]
/-
**differentiableWithinAt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_ofNat (n : Nat) [OfNat F n] : DifferentiableWithinA
t 𝕜 (ofNat(n) : E -> F) s x
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_const`：differentiableWithinAt_const (c : F) : Dif
ferentiableWithinAt 𝕜 (fun _ => c) s x
-/
theorem differentiableWithinAt_ofNat (n : ℕ) [OfNat F n] :
    DifferentiableWithinAt 𝕜 (ofNat(n) : E → F) s x := differentiableWithinAt_const _
/-
**fderivWithin_const_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_const_apply (c : F) : fderivWithin 𝕜 (fun _ => c) s x = 0
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `hasFDerivWithinAt_const`：hasFDerivWithinAt_const (c : F) (x : E) (s : Se
t E) : HasFDerivWithinAt (fun _ => c) (0 : E ->L[𝕜] F) s x
-/
theorem fderivWithin_const_apply (c : F) : fderivWithin 𝕜 (fun _ => c) s x = 0 := by
  rw [fderivWithin, if_pos]
  apply hasFDerivWithinAt_const

@[simp]
/-
**fderivWithin_fun_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fun_const (c : F) : fderivWithin 𝕜 (fun _ => c) s = 0
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_const_apply`：fderivWithin_const_apply (c : F) : fderivWithi
n 𝕜 (fun _ => c) s x = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
theorem fderivWithin_fun_const (c : F) : fderivWithin 𝕜 (fun _ ↦ c) s = 0 := by
  ext
  rw [fderivWithin_const_apply, Pi.zero_apply]

@[simp]
/-
**fderivWithin_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_const (c : F) : fderivWithin 𝕜 (Function.const E c) s = 0
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_fun_const`：fderivWithin_fun_const (c : F) : fderivWithin 𝕜 
(fun _ => c) s = 0
-/
theorem fderivWithin_const (c : F) : fderivWithin 𝕜 (Function.const E c) s = 0 :=
  fderivWithin_fun_const c

@[simp]
/-
**fderivWithin_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_zero : fderivWithin 𝕜 (0 : E -> F) s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_const`：fderivWithin_const (c : F) : fderivWithin 𝕜 (Functio
n.const E c) s = 0
-/
theorem fderivWithin_zero : fderivWithin 𝕜 (0 : E → F) s = 0 := fderivWithin_const _

@[simp]
/-
**fderivWithin_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_one [One F] : fderivWithin 𝕜 (1 : E -> F) s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_const`：fderivWithin_const (c : F) : fderivWithin 𝕜 (Functio
n.const E c) s = 0
-/
theorem fderivWithin_one [One F] : fderivWithin 𝕜 (1 : E → F) s = 0 := fderivWithin_const _

@[simp]
/-
**fderivWithin_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_natCast [NatCast F] (n : Nat) : fderivWithin 𝕜 (n : E -> F) s
 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_const`：fderivWithin_const (c : F) : fderivWithin 𝕜 (Functio
n.const E c) s = 0
-/
theorem fderivWithin_natCast [NatCast F] (n : ℕ) : fderivWithin 𝕜 (n : E → F) s = 0 :=
  fderivWithin_const _

@[simp]
/-
**fderivWithin_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_intCast [IntCast F] (z : Int) : fderivWithin 𝕜 (z : E -> F) s
 = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_const`：fderivWithin_const (c : F) : fderivWithin 𝕜 (Functio
n.const E c) s = 0
-/
theorem fderivWithin_intCast [IntCast F] (z : ℤ) : fderivWithin 𝕜 (z : E → F) s = 0 :=
  fderivWithin_const _

@[simp low]
/-
**fderivWithin_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_ofNat (n : Nat) [OfNat F n] : fderivWithin 𝕜 (ofNat(n) : E ->
 F) s = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_const`：fderivWithin_const (c : F) : fderivWithin 𝕜 (Functio
n.const E c) s = 0
-/
theorem fderivWithin_ofNat (n : ℕ) [OfNat F n] : fderivWithin 𝕜 (ofNat(n) : E → F) s = 0 :=
  fderivWithin_const _
/-
**fderiv_const_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_const_apply (c : F) : fderiv 𝕜 (fun _ => c) x = 0
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E : Typ
e u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Topolo
…
· 使用定理 `fderivWithin_const_apply`：fderivWithin_const_apply (c : F) : fderivWithi
n 𝕜 (fun _ => c) s x = 0
-/
theorem fderiv_const_apply (c : F) : fderiv 𝕜 (fun _ => c) x = 0 := by
  rw [fderiv, fderivWithin_const_apply]

@[simp]
/-
**fderiv_fun_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fun_const (c : F) : fderiv 𝕜 (fun _ : E => c) = 0
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `fderivWithin_fun_const`：fderivWithin_fun_const (c : F) : fderivWithin 𝕜 
(fun _ => c) s = 0
-/
theorem fderiv_fun_const (c : F) : fderiv 𝕜 (fun _ : E => c) = 0 := by
  rw [← fderivWithin_univ, fderivWithin_fun_const]

@[simp]
/-
**fderiv_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_const (c : F) : fderiv 𝕜 (Function.const E c) = 0
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_fun_const`：fderiv_fun_const (c : F) : fderiv 𝕜 (fun _ : E => c) =
 0
-/
theorem fderiv_const (c : F) : fderiv 𝕜 (Function.const E c) = 0 :=
  fderiv_fun_const c

@[simp]
/-
**fderiv_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_zero : fderiv 𝕜 (0 : E -> F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_const`：fderiv_const (c : F) : fderiv 𝕜 (Function.const E c) = 0
-/
theorem fderiv_zero : fderiv 𝕜 (0 : E → F) = 0 := fderiv_const _

@[simp]
/-
**fderiv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_one [One F] : fderiv 𝕜 (1 : E -> F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_const`：fderiv_const (c : F) : fderiv 𝕜 (Function.const E c) = 0
-/
theorem fderiv_one [One F] : fderiv 𝕜 (1 : E → F) = 0 := fderiv_const _

@[simp]
/-
**fderiv_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_natCast [NatCast F] (n : Nat) : fderiv 𝕜 (n : E -> F) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_const`：fderiv_const (c : F) : fderiv 𝕜 (Function.const E c) = 0
-/
theorem fderiv_natCast [NatCast F] (n : ℕ) : fderiv 𝕜 (n : E → F) = 0 := fderiv_const _

@[simp]
/-
**fderiv_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_intCast [IntCast F] (z : Int) : fderiv 𝕜 (z : E -> F) = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_const`：fderiv_const (c : F) : fderiv 𝕜 (Function.const E c) = 0
-/
theorem fderiv_intCast [IntCast F] (z : ℤ) : fderiv 𝕜 (z : E → F) = 0 := fderiv_const _

@[simp low]
/-
**fderiv_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_ofNat (n : Nat) [OfNat F n] : fderiv 𝕜 (ofNat(n) : E -> F) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_const`：fderiv_const (c : F) : fderiv 𝕜 (Function.const E c) = 0
-/
theorem fderiv_ofNat (n : ℕ) [OfNat F n] : fderiv 𝕜 (ofNat(n) : E → F) = 0 := fderiv_const _

@[simp, fun_prop]
/-
**differentiable_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_const (c : F) : Differentiable 𝕜 fun _ : E => c
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
-/
theorem differentiable_const (c : F) : Differentiable 𝕜 fun _ : E => c := fun _ =>
  differentiableAt_const _

@[simp, fun_prop]
/-
**differentiable_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_zero : Differentiable 𝕜 (0 : E -> F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
-/
theorem differentiable_zero :
    Differentiable 𝕜 (0 : E → F) := differentiable_const _

@[simp, fun_prop]
/-
**differentiable_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_one [One F] : Differentiable 𝕜 (1 : E -> F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
-/
theorem differentiable_one [One F] :
    Differentiable 𝕜 (1 : E → F) := differentiable_const _

@[simp, fun_prop]
/-
**differentiable_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_natCast [NatCast F] (n : Nat) : Differentiable 𝕜 (n : E -> 
F)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
-/
theorem differentiable_natCast [NatCast F] (n : ℕ) :
    Differentiable 𝕜 (n : E → F) := differentiable_const _

@[simp, fun_prop]
/-
**differentiable_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_intCast [IntCast F] (z : Int) : Differentiable 𝕜 (z : E -> 
F)
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
-/
theorem differentiable_intCast [IntCast F] (z : ℤ) :
    Differentiable 𝕜 (z : E → F) := differentiable_const _

@[simp low, fun_prop]
/-
**differentiable_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_ofNat (n : Nat) [OfNat F n] : Differentiable 𝕜 (ofNat(n) : 
E -> F)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
-/
theorem differentiable_ofNat (n : ℕ) [OfNat F n] :
    Differentiable 𝕜 (ofNat(n) : E → F) := differentiable_const _

@[simp, fun_prop]
/-
**differentiableOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_const (c : F) : DifferentiableOn 𝕜 (fun _ => c) s
参数：c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
-/
theorem differentiableOn_const (c : F) : DifferentiableOn 𝕜 (fun _ => c) s :=
  (differentiable_const _).differentiableOn

@[simp, fun_prop]
/-
**differentiableOn_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_zero : DifferentiableOn 𝕜 (0 : E -> F) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
-/
theorem differentiableOn_zero :
    DifferentiableOn 𝕜 (0 : E → F) s := differentiableOn_const _

@[simp, fun_prop]
/-
**differentiableOn_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_one [One F] : DifferentiableOn 𝕜 (1 : E -> F) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
-/
theorem differentiableOn_one [One F] :
    DifferentiableOn 𝕜 (1 : E → F) s := differentiableOn_const _

@[simp, fun_prop]
/-
**differentiableOn_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_natCast [NatCast F] (n : Nat) : DifferentiableOn 𝕜 (n : E
 -> F) s
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
-/
theorem differentiableOn_natCast [NatCast F] (n : ℕ) :
    DifferentiableOn 𝕜 (n : E → F) s := differentiableOn_const _

@[simp, fun_prop]
/-
**differentiableOn_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_intCast [IntCast F] (z : Int) : DifferentiableOn 𝕜 (z : E
 -> F) s
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
-/
theorem differentiableOn_intCast [IntCast F] (z : ℤ) :
    DifferentiableOn 𝕜 (z : E → F) s := differentiableOn_const _

@[simp low, fun_prop]
/-
**differentiableOn_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_ofNat (n : Nat) [OfNat F n] : DifferentiableOn 𝕜 (ofNat(n
) : E -> F) s
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
-/
theorem differentiableOn_ofNat (n : ℕ) [OfNat F n] :
    DifferentiableOn 𝕜 (ofNat(n) : E → F) s := differentiableOn_const _

@[fun_prop]
/-
**hasFDerivWithinAt_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_singleton (f : E -> F) (x : E) : HasFDerivWithinAt f (0 
: E ->L[𝕜] F) {x} x
参数：f : E -> F；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.of_not_accPt`：HasFDerivWithinAt.of_not_accPt (h : ¬Acc
Pt x (𝓟 s)) : HasFDerivWithinAt f f' s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `accPt_iff_clusterPt`：accPt_iff_clusterPt {x : X} {F : Filter X} : AccPt 
x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F)
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_singleton_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∉
 s → s ∩ {a} = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
theorem hasFDerivWithinAt_singleton (f : E → F) (x : E) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) {x} x := by
  refine .of_not_accPt ?_
  rw [accPt_iff_clusterPt, inf_principal]
  simp [ClusterPt]

@[fun_prop, nontriviality]
/-
**hasFDerivWithinAt_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_of_subsingleton [h : Subsingleton E] (f : E -> F) (s : S
et E) (x : E) : HasFDerivWithinAt f (0 : E ->L[𝕜] F) s x
参数：f : E -> F；s : Set E；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_singleton_of_subsingleton`：eq_empty_or_singleton_of_subs
ingleton [Subsingleton α] (s : Set α) : s = ∅ ∨ exists a, s = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFDerivWithinAt.singleton`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E]
 [inst_3 : Topolo…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.DiscreteTopology.metrizableSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] [DiscreteTopology X], TopologicalSpace.MetrizableSpace X
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
-/
theorem hasFDerivWithinAt_of_subsingleton [h : Subsingleton E] (f : E → F) (s : Set E) (x : E) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) s x := by
  obtain rfl | ⟨a, rfl⟩ := s.eq_empty_or_singleton_of_subsingleton
  · simp
  · exact HasFDerivWithinAt.singleton

@[fun_prop, nontriviality]
/-
**hasFDerivAt_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_of_subsingleton [h : Subsingleton E] (f : E -> F) (x : E) : Ha
sFDerivAt f (0 : E ->L[𝕜] F) x
参数：f : E -> F；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用定理 `Set.subsingleton_univ`：subsingleton_univ [Subsingleton α] : (univ : Set 
α).Subsingleton
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `hasFDerivWithinAt_singleton`：hasFDerivWithinAt_singleton (f : E -> F) (x
 : E) : HasFDerivWithinAt f (0 : E ->L[𝕜] F) {x} x
-/
theorem hasFDerivAt_of_subsingleton [h : Subsingleton E] (f : E → F) (x : E) :
    HasFDerivAt f (0 : E →L[𝕜] F) x := by
  rw [← hasFDerivWithinAt_univ, subsingleton_univ.eq_singleton_of_mem (mem_univ x)]
  exact hasFDerivWithinAt_singleton f x

@[nontriviality]
/-
**differentiable_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_of_subsingleton [Subsingleton E] {f : E -> F} : Differentia
ble 𝕜 f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasFDerivAt_of_subsingleton`：hasFDerivAt_of_subsingleton [h : Subsinglet
on E] (f : E -> F) (x : E) : HasFDerivAt f (0 : E ->L[𝕜] F) x
-/
theorem differentiable_of_subsingleton [Subsingleton E] {f : E → F} : Differentiable 𝕜 f :=
  fun x ↦ (hasFDerivAt_of_subsingleton f x (𝕜 := 𝕜)).differentiableAt

@[nontriviality]
/-
**differentiableWithinAt_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_of_subsingleton [Subsingleton E] : DifferentiableWi
thinAt 𝕜 f s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiable_of_subsingleton`：differentiable_of_subsingleton [Subsingl
eton E] {f : E -> F} : Differentiable 𝕜 f
-/
theorem differentiableWithinAt_of_subsingleton [Subsingleton E] :
    DifferentiableWithinAt 𝕜 f s x :=
  (differentiable_of_subsingleton x).differentiableWithinAt

@[fun_prop]
/-
**differentiableOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_singleton : DifferentiableOn 𝕜 f {x}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_eq`：∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∀ (a : α), a = a' 
→ p a) ↔ p a'
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `hasFDerivWithinAt_singleton`：hasFDerivWithinAt_singleton (f : E -> F) (x
 : E) : HasFDerivWithinAt f (0 : E ->L[𝕜] F) {x} x
-/
theorem differentiableOn_singleton : DifferentiableOn 𝕜 f {x} :=
  forall_eq.2 (hasFDerivWithinAt_singleton f x).differentiableWithinAt

@[fun_prop]
/-
**Set.Subsingleton.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.differentiableOn (hs : s.Subsingleton) : DifferentiableOn
 𝕜 f s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `differentiableOn_empty`：differentiableOn_empty : DifferentiableOn 𝕜 f ∅
· 使用定理 `differentiableOn_singleton`：differentiableOn_singleton : DifferentiableO
n 𝕜 f {x}
-/
theorem Set.Subsingleton.differentiableOn (hs : s.Subsingleton) : DifferentiableOn 𝕜 f s :=
  hs.induction_on differentiableOn_empty fun _ => differentiableOn_singleton
/-
**hasFDerivAt_zero_of_eventually_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_zero_of_eventually_const (c : F) (hf : f =ᶠ[𝓝 x] fun _ => c) :
 HasFDerivAt f (0 : E ->L[𝕜] F) x
参数：c : F；hf : f =ᶠ[𝓝 x] fun _ => c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.congr_of_eventuallyEq`：HasFDerivAt.congr_of_eventuallyEq (h 
: HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasFDerivAt f₁ f' x
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
-/
theorem hasFDerivAt_zero_of_eventually_const (c : F) (hf : f =ᶠ[𝓝 x] fun _ => c) :
    HasFDerivAt f (0 : E →L[𝕜] F) x :=
  (hasFDerivAt_const _ _).congr_of_eventuallyEq hf

end Const

/-- If `f : E → F` has injective differential within `s` at `x`,
it is differentiable within `s` at `x`. -/
/-
**differentiableWithinAt_of_fderivWithin_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_of_fderivWithin_injective (hf : Injective (fderivWi
thin 𝕜 f s x)) : DifferentiableWithinAt 𝕜 f s x
参数：hf : Injective (fderivWithin 𝕜 f s x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `Function.not_injective_const`：∀ {α : Type u_4} {β : Type u_5} [Nontrivia
l α] {b : β}, ¬Function.Injective fun x => b

--- 原说明 ---
If `f : E → F` has injective differential within `s` at `x`,
it is differentiable within `s` at `x`.
-/
lemma differentiableWithinAt_of_fderivWithin_injective (hf : Injective (fderivWithin 𝕜 f s x)) :
    DifferentiableWithinAt 𝕜 f s x := by
  nontriviality E
  contrapose hf
  rw [fderivWithin_zero_of_not_differentiableWithinAt hf]
  exact not_injective_const

/-- If `f : E → F` has injective differential at `x`, it is differentiable at `x`. -/
/-
**differentiableAt_of_fderiv_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_of_fderiv_injective (hf : Injective (fderiv 𝕜 f x)) : Dif
ferentiableAt 𝕜 f x
参数：hf : Injective (fderiv 𝕜 f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `differentiableWithinAt_of_fderivWithin_injective`：differentiableWithinAt
_of_fderivWithin_injective (hf : Injective (fderivWithin 𝕜 f s x)) : Differentia
bleWithinAt 𝕜 f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
If `f : E → F` has injective differential at `x`, it is differentiable at `x`.
-/
lemma differentiableAt_of_fderiv_injective (hf : Injective (fderiv 𝕜 f x)) :
    DifferentiableAt 𝕜 f x := by
  simp only [← differentiableWithinAt_univ, ← fderivWithin_univ] at hf ⊢
  exact differentiableWithinAt_of_fderivWithin_injective hf
/-
**differentiableWithinAt_of_isInvertible_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：differentiableWithinAt_of_isInvertible_fderivWithin (hf : (fderivWithin 𝕜 
f s x).IsInvertible) : DifferentiableWithinAt 𝕜 f s x
参数：hf : (fderivWithin 𝕜 f s x).IsInvertible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `differentiableWithinAt_of_fderivWithin_injective`：differentiableWithinAt
_of_fderivWithin_injective (hf : Injective (fderivWithin 𝕜 f s x)) : Differentia
bleWithinAt 𝕜 f s x
· 使用定理 `ContinuousLinearMap.IsInvertible.injective`：∀ {R : Type u_1} {M : Type u
_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂]  
 [inst_2 : Semiring R] [inst_3 :…
-/
theorem differentiableWithinAt_of_isInvertible_fderivWithin
    (hf : (fderivWithin 𝕜 f s x).IsInvertible) : DifferentiableWithinAt 𝕜 f s x :=
  differentiableWithinAt_of_fderivWithin_injective hf.injective
/-
**differentiableAt_of_isInvertible_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_of_isInvertible_fderiv (hf : (fderiv 𝕜 f x).IsInvertible)
 : DifferentiableAt 𝕜 f x
参数：hf : (fderiv 𝕜 f x).IsInvertible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `differentiableAt_of_fderiv_injective`：differentiableAt_of_fderiv_injecti
ve (hf : Injective (fderiv 𝕜 f x)) : DifferentiableAt 𝕜 f x
· 使用定理 `ContinuousLinearMap.IsInvertible.injective`：∀ {R : Type u_1} {M : Type u
_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂]  
 [inst_2 : Semiring R] [inst_3 :…
-/
theorem differentiableAt_of_isInvertible_fderiv
    (hf : (fderiv 𝕜 f x).IsInvertible) : DifferentiableAt 𝕜 f x :=
  differentiableAt_of_fderiv_injective hf.injective

/-! ### Support of derivatives -/

section Support
variable (𝕜)

/-
**HasStrictFDerivAt.of_notMem_tsupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasStrictFDeri
vAt f (0 : E ->L[𝕜] F) x
参数：h : x ∉ tsupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.congr_of_eventuallyEq`：HasStrictFDerivAt.congr_of_even
tuallyEq (h : HasStrictFDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt 
f₁ f' x
· 使用定理 `hasStrictFDerivAt_const`：hasStrictFDerivAt_const (c : F) (x : E) : HasSt
rictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `notMem_tsupport_iff_eventuallyEq`：∀ {α : Type u_2} {β : Type u_4} [inst 
: TopologicalSpace α] [inst_1 : Zero β] {f : α → β} {x : α},   x ∉ tsupport f ↔ 
f =ᶠ[nhds x] 0
-/
theorem HasStrictFDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) :
    HasStrictFDerivAt f (0 : E →L[𝕜] F) x := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictFDerivAt_const (0 : F) x).congr_of_eventuallyEq h.symm
/-
**HasFDerivAt.of_notMem_tsupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasFDerivAt f (0 : E
 ->L[𝕜] F) x
参数：h : x ∉ tsupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `HasStrictFDerivAt.of_notMem_tsupport`：HasStrictFDerivAt.of_notMem_tsuppo
rt (h : x ∉ tsupport f) : HasStrictFDerivAt f (0 : E ->L[𝕜] F) x
-/
theorem HasFDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) :
    HasFDerivAt f (0 : E →L[𝕜] F) x :=
  (HasStrictFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivAt
/-
**HasFDerivWithinAt.of_notMem_tsupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_notMem_tsupport {s : Set E} {x : E} (h : x ∉ tsupport
 f) : HasFDerivWithinAt f (0 : E ->L[𝕜] F) s x
参数：h : x ∉ tsupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `HasFDerivAt.of_notMem_tsupport`：HasFDerivAt.of_notMem_tsupport (h : x ∉ 
tsupport f) : HasFDerivAt f (0 : E ->L[𝕜] F) x
-/
theorem HasFDerivWithinAt.of_notMem_tsupport {s : Set E} {x : E} (h : x ∉ tsupport f) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) s x :=
  (HasFDerivAt.of_notMem_tsupport 𝕜 h).hasFDerivWithinAt
/-
**fderiv_of_notMem_tsupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_of_notMem_tsupport (h : x ∉ tsupport f) : fderiv 𝕜 f x = 0
参数：h : x ∉ tsupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.fderiv_eq`：Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[
𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x
· 使用定理 `notMem_tsupport_iff_eventuallyEq`：∀ {α : Type u_2} {β : Type u_4} [inst 
: TopologicalSpace α] [inst_1 : Zero β] {f : α → β} {x : α},   x ∉ tsupport f ↔ 
f =ᶠ[nhds x] 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderiv_zero`：fderiv_zero : fderiv 𝕜 (0 : E -> F) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_of_notMem_tsupport (h : x ∉ tsupport f) : fderiv 𝕜 f x = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.fderiv_eq]
/-
**support_fderiv_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：support_fderiv_subset : support (fderiv 𝕜 f) subseteq tsupport f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用定理 `fderiv_of_notMem_tsupport`：fderiv_of_notMem_tsupport (h : x ∉ tsupport f
) : fderiv 𝕜 f x = 0
-/
theorem support_fderiv_subset : support (fderiv 𝕜 f) ⊆ tsupport f := fun x ↦ by
  rw [← not_imp_not, notMem_support]
  exact fderiv_of_notMem_tsupport _
/-
**tsupport_fderiv_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsupport_fderiv_subset : tsupport (fderiv 𝕜 f) subseteq tsupport f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `support_fderiv_subset`：support_fderiv_subset : support (fderiv 𝕜 f) subs
eteq tsupport f
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem tsupport_fderiv_subset : tsupport (fderiv 𝕜 f) ⊆ tsupport f :=
  closure_minimal (support_fderiv_subset 𝕜) isClosed_closure
/-
**tsupport_fderiv_apply_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsupport_fderiv_apply_subset (v : E) : tsupport (fderiv 𝕜 f · v) subseteq 
tsupport f
参数：v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsupport_comp_subset`：∀ {X : Type u_1} {α : Type u_2} {β : Type u_4} [in
st : Zero α] [inst_1 : TopologicalSpace X] [inst_2 : Zero β]   {g : α → β}, g 0 
= 0 → ∀ (f…
· 使用定理 `tsupport_fderiv_subset`：tsupport_fderiv_subset : tsupport (fderiv 𝕜 f) s
ubseteq tsupport f
-/
theorem tsupport_fderiv_apply_subset (v : E) : tsupport (fderiv 𝕜 f · v) ⊆ tsupport f :=
  (tsupport_comp_subset (g := fun L : E →L[𝕜] F ↦ L v) rfl _).trans (tsupport_fderiv_subset 𝕜)
/-
**HasCompactSupport.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactSupport`。
形式化陈述：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F},   HasCompactSupport f → HasCompactSupport (fd
eriv 𝕜 f)
参数：𝕜 : Type u_1；fderiv 𝕜 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.mono'`：∀ {α : Type u_2} {β : Type u_4} {γ : Type u_5} 
[inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : Zero γ]   {f : α → β} {f
' : α → γ}, H…
· 使用定理 `support_fderiv_subset`：support_fderiv_subset : support (fderiv 𝕜 f) subs
eteq tsupport f
-/
protected theorem HasCompactSupport.fderiv (hf : HasCompactSupport f) :
    HasCompactSupport (fderiv 𝕜 f) :=
  hf.mono' <| support_fderiv_subset 𝕜
/-
**HasCompactSupport.fderiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactSupport`。
形式化陈述：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] {f : E → F},   HasCompactSupport f → ∀ (v : E), HasCompact
Support fun x => (fderiv 𝕜 f x) v
参数：𝕜 : Type u_1；v : E；fderiv 𝕜 f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst
_1 : TopologicalSpace X] (f : X → α), IsClosed (tsupport f)
· 使用定理 `tsupport_fderiv_apply_subset`：tsupport_fderiv_apply_subset (v : E) : tsu
pport (fderiv 𝕜 f · v) subseteq tsupport f
-/
protected theorem HasCompactSupport.fderiv_apply (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (fderiv 𝕜 f · v) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset 𝕜 v)

end Support


end

