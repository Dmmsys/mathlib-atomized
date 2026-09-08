/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.NumberTheory.Height.Basic

/-!
# Heights of points in projective space

We define the multiplicative (`Projectivization.mulHeight`) and the logarithmic
(`Projectivization.logHeight`) height of a point in a (finite-dimensional) projective space
over a field that has a `Height.AdmissibleAbsValues` instance.

The height is defined to be the height of any representative tuple; it does not depend
on which representative is chosen.
-/

public section

namespace Projectivization

open Height AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

/-
**Projectivization.mulHeight_aux** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    mulHeight a.val = mulHeight b.val :=
  have ht : t ≠ 0 := by
    contrapose! h
    simpa [h] using a.prop
  h ▸ mulHeight_smul_eq_mulHeight _ ht
/-
**Projectivization.logHeight_aux** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma logHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    logHeight a.val = logHeight b.val :=
  congrArg log <| mod_cast mulHeight_aux a b t h

-- We do not expose the bodies of these definitions so that we can keep the "_aux" lemmas
-- above private.

/-- The multiplicative height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
/-
**Projectivization.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：mulHeight (x : Projectivization K (ι -> K)) : Real
参数：x : Projectivization K (ι -> K)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.Height.Projectivization.0.Projectivization
.mulHeight_aux`：∀ {K : Type u_1} [inst : Field K] [inst_1 : Height.AdmissibleAbs
Values K] {ι : Type u_2} [Finite ι]   (a b : { v // v ≠ 0 }) (t : K), ↑a = t…

--- 原说明 ---
The multiplicative height of a point on a finite-dimensional projective space ov
er `K`
with a given basis.
-/
noncomputable def mulHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ Height.mulHeight r.val) mulHeight_aux

/-- The logarithmic height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
/-
**Projectivization.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：logHeight (x : Projectivization K (ι -> K)) : Real
参数：x : Projectivization K (ι -> K)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.Height.Projectivization.0.Projectivization
.logHeight_aux`：∀ {K : Type u_1} [inst : Field K] [inst_1 : Height.AdmissibleAbs
Values K] {ι : Type u_2} [Finite ι]   (a b : { v // v ≠ 0 }) (t : K), ↑a = t…

--- 原说明 ---
The logarithmic height of a point on a finite-dimensional projective space over 
`K`
with a given basis.
-/
noncomputable def logHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ Height.logHeight r.val) logHeight_aux
/-
**Projectivization.mulHeight_mk** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：mulHeight_mk {x : ι -> K} (hx : x != 0) : mulHeight (mk K x hx) = Height.m
ulHeight x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeight_mk {x : ι → K} (hx : x ≠ 0) : mulHeight (mk K x hx) = Height.mulHeight x := by
  rfl
/-
**Projectivization.logHeight_mk** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：logHeight_mk {x : ι -> K} (hx : x != 0) : logHeight (mk K x hx) = Height.l
ogHeight x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma logHeight_mk {x : ι → K} (hx : x ≠ 0) : logHeight (mk K x hx) = Height.logHeight x := by
  rfl
/-
**Projectivization.logHeight_eq_log_mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `Project
ivization`。
形式化陈述：logHeight_eq_log_mulHeight (x : Projectivization K (ι -> K)) : logHeight x
 = log (mulHeight x)
参数：x : Projectivization K (ι -> K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v
· 使用引理 `Projectivization.mulHeight_mk`：mulHeight_mk {x : ι -> K} (hx : x != 0) :
 mulHeight (mk K x hx) = Height.mulHeight x
· 使用引理 `Projectivization.logHeight_mk`：logHeight_mk {x : ι -> K} (hx : x != 0) :
 logHeight (mk K x hx) = Height.logHeight x
· 使用定理 `Height.logHeight.eq_1`：∀ {K : Type u_1} [inst : Field K] [inst_1 : Heigh
t.AdmissibleAbsValues K] {ι : Type u_2} (x : ι → K),   Height.logHeight x = Real
.log (Heigh…
-/
lemma logHeight_eq_log_mulHeight (x : Projectivization K (ι → K)) :
    logHeight x = log (mulHeight x) := by
  rw [← x.mk_rep, mulHeight_mk, logHeight_mk, Height.logHeight]
/-
**Projectivization.one_le_mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`
。
形式化陈述：one_le_mulHeight (x : Projectivization K (ι -> K)) : 1 <= mulHeight x
参数：x : Projectivization K (ι -> K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v
· 使用引理 `Projectivization.mulHeight_mk`：mulHeight_mk {x : ι -> K} (hx : x != 0) :
 mulHeight (mk K x hx) = Height.mulHeight x
· 使用引理 `Height.one_le_mulHeight`：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight 
x
-/
lemma one_le_mulHeight (x : Projectivization K (ι → K)) : 1 ≤ mulHeight x := by
  rw [← x.mk_rep, mulHeight_mk]
  exact Height.one_le_mulHeight _
/-
**Projectivization.mulHeight_pos** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：mulHeight_pos (x : Projectivization K (ι -> K)) : 0 < mulHeight x
参数：x : Projectivization K (ι -> K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Projectivization.one_le_mulHeight`：one_le_mulHeight (x : Projectivizatio
n K (ι -> K)) : 1 <= mulHeight x
-/
lemma mulHeight_pos (x : Projectivization K (ι → K)) : 0 < mulHeight x :=
  zero_lt_one.trans_le <| one_le_mulHeight x
/-
**Projectivization.mulHeight_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization
`。
形式化陈述：mulHeight_ne_zero (x : Projectivization K (ι -> K)) : mulHeight x != 0
参数：x : Projectivization K (ι -> K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Projectivization.mulHeight_pos`：mulHeight_pos (x : Projectivization K (ι
 -> K)) : 0 < mulHeight x
-/
lemma mulHeight_ne_zero (x : Projectivization K (ι → K)) : mulHeight x ≠ 0 :=
  (mulHeight_pos x).ne'
/-
**Projectivization.logHeight_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`
。
形式化陈述：logHeight_nonneg (x : Projectivization K (ι -> K)) : 0 <= logHeight x
参数：x : Projectivization K (ι -> K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.logHeight_eq_log_mulHeight`：logHeight_eq_log_mulHeight 
(x : Projectivization K (ι -> K)) : logHeight x = log (mulHeight x)
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
· 使用引理 `Projectivization.one_le_mulHeight`：one_le_mulHeight (x : Projectivizatio
n K (ι -> K)) : 1 <= mulHeight x
-/
lemma logHeight_nonneg (x : Projectivization K (ι → K)) : 0 ≤ logHeight x := by
  rw [logHeight_eq_log_mulHeight]
  exact log_nonneg <| x.one_le_mulHeight

end Projectivization

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Projectivization

/-- Extension for the `positivity` tactic: `Projectivization.mulHeight` is always positive. -/
@[positivity Projectivization.mulHeight _]
meta def evalProjMulHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@mulHeight $K $KF $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q(mulHeight_pos $a))
  | _, _, _ => throwError "not Projectivization.mulHeight"

/-- Extension for the `positivity` tactic: `Projectivization.logHeight` is always nonnegative. -/
@[positivity Projectivization.logHeight _]
meta def evalProjLogHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@logHeight $K $KF $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q(logHeight_nonneg $a))
  | _, _, _ => throwError "not Projectivization.logHeight"

end Mathlib.Meta.Positivity

