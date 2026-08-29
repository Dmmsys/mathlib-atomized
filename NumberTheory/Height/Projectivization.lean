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

/--
lemma `mulHeight_aux` / 引理 `mulHeight_aux`

English:
lemma mulHeight_aux
  given: (a b : { v : ι -> K // v != 0 }) (t : K) (h : a.val = t • b.val)
  proof: have ht : t != 0 := by
    contrapose! h
    simpa [h] using a.prop
  h ▸ mulHeight_smul_eq_mulHeight _ ht

中文:
引理 mulHeight_aux
  条件: (a b : { v : ι -> K // v != 0 }) (t : K) (h : a.val = t • b.val)
  证明: have ht : t != 0 := by
    contrapose! h
    simpa [h] using a.prop
  h ▸ mulHeight_smul_eq_mulHeight _ ht
-/
private lemma mulHeight_aux (a b : { v : ι -> K // v != 0 }) (t : K) (h : a.val = t • b.val) :
    mulHeight a.val = mulHeight b.val :=
  have ht : t != 0 := by
    contrapose! h
    simpa [h] using a.prop
  h ▸ mulHeight_smul_eq_mulHeight _ ht

/--
lemma `logHeight_aux` / 引理 `logHeight_aux`

English:
lemma logHeight_aux
  given: (a b : { v : ι -> K // v != 0 }) (t : K) (h : a.val = t • b.val)
  proof: congrArg log mod_cast mulHeight_aux a b t h

中文:
引理 logHeight_aux
  条件: (a b : { v : ι -> K // v != 0 }) (t : K) (h : a.val = t • b.val)
  证明: congrArg log mod_cast mulHeight_aux a b t h
-/
private lemma logHeight_aux (a b : { v : ι -> K // v != 0 }) (t : K) (h : a.val = t • b.val) :
    logHeight a.val = logHeight b.val :=
congrArg log mod_cast mulHeight_aux a b t h

-- We do not expose the bodies of these definitions so that we can keep the "_aux" lemmas
-- above private.

/--
Definition of `mulHeight` / `mulHeight` 的定义

English:
definition mulHeight
  signature: (x : Projectivization K (ι -> K))
  body: x.lift (fun r => Height.mulHeight r.val) mulHeight_aux

中文:
定义 mulHeight
  签名: (x : Projectivization K (ι -> K))
  定义体: x.lift (fun r => Height.mulHeight r.val) mulHeight_aux

Depends on / 依赖: Height, Height.mulHeight, mulHeight, mulHeight_aux, r.val, x.lift
-/
noncomputable def mulHeight (x : Projectivization K (ι -> K)) : Real :=
  x.lift (fun r => Height.mulHeight r.val) mulHeight_aux

/--
Definition of `logHeight` / `logHeight` 的定义

English:
definition logHeight
  signature: (x : Projectivization K (ι -> K))
  body: x.lift (fun r => Height.logHeight r.val) logHeight_aux

中文:
定义 logHeight
  签名: (x : Projectivization K (ι -> K))
  定义体: x.lift (fun r => Height.logHeight r.val) logHeight_aux

Depends on / 依赖: Height, Height.logHeight, logHeight, logHeight_aux, r.val, x.lift
-/
noncomputable def logHeight (x : Projectivization K (ι -> K)) : Real :=
  x.lift (fun r => Height.logHeight r.val) logHeight_aux

/--
lemma `mulHeight_mk` / 引理 `mulHeight_mk`

English:
lemma mulHeight_mk
  given: {x : ι -> K} (hx : x != 0)
  statement: mulHeight (mk K x hx) = Height.mulHeight x
  proof: by
  rfl

中文:
引理 mulHeight_mk
  条件: {x : ι -> K} (hx : x != 0)
  结论: mulHeight (mk K x hx) = Height.mulHeight x
  证明: by
  rfl
-/
lemma mulHeight_mk {x : ι -> K} (hx : x != 0) : mulHeight (mk K x hx) = Height.mulHeight x := by
  rfl

/--
lemma `logHeight_mk` / 引理 `logHeight_mk`

English:
lemma logHeight_mk
  given: {x : ι -> K} (hx : x != 0)
  statement: logHeight (mk K x hx) = Height.logHeight x
  proof: by
  rfl

中文:
引理 logHeight_mk
  条件: {x : ι -> K} (hx : x != 0)
  结论: logHeight (mk K x hx) = Height.logHeight x
  证明: by
  rfl
-/
lemma logHeight_mk {x : ι -> K} (hx : x != 0) : logHeight (mk K x hx) = Height.logHeight x := by
  rfl

/--
lemma `logHeight_eq_log_mulHeight` / 引理 `logHeight_eq_log_mulHeight`

English:
lemma logHeight_eq_log_mulHeight
  given: (x : Projectivization K (ι -> K))
  proof: by
  rw [← x.mk_rep]; rw [mulHeight_mk]; rw [logHeight_mk]; rw [Height.logHeight]

中文:
引理 logHeight_eq_log_mulHeight
  条件: (x : Projectivization K (ι -> K))
  证明: by
  rw [← x.mk_rep]; rw [mulHeight_mk]; rw [logHeight_mk]; rw [Height.logHeight]

Depends on / 依赖: Height, Height.logHeight, logHeight, logHeight_mk, mk_rep, mulHeight_mk, x.mk_rep
-/
lemma logHeight_eq_log_mulHeight (x : Projectivization K (ι -> K)) :
    logHeight x = log (mulHeight x) := by
  rw [← x.mk_rep]; rw [mulHeight_mk]; rw [logHeight_mk]; rw [Height.logHeight]

/--
lemma `one_le_mulHeight` / 引理 `one_le_mulHeight`

English:
lemma one_le_mulHeight
  given: (x : Projectivization K (ι -> K))
  statement: 1 <= mulHeight x
  proof: by
  rw [← x.mk_rep]; rw [mulHeight_mk]
  exact Height.one_le_mulHeight _

中文:
引理 one_le_mulHeight
  条件: (x : Projectivization K (ι -> K))
  结论: 1 <= mulHeight x
  证明: by
  rw [← x.mk_rep]; rw [mulHeight_mk]
  exact Height.one_le_mulHeight _

Depends on / 依赖: Height, Height.one_le_mulHeight, mk_rep, mulHeight_mk, one_le_mulHeight, x.mk_rep
-/
lemma one_le_mulHeight (x : Projectivization K (ι -> K)) : 1 <= mulHeight x := by
  rw [← x.mk_rep]; rw [mulHeight_mk]
  exact Height.one_le_mulHeight _

/--
lemma `mulHeight_pos` / 引理 `mulHeight_pos`

English:
lemma mulHeight_pos
  given: (x : Projectivization K (ι -> K))
  statement: 0 < mulHeight x
  proof: zero_lt_one.trans_le one_le_mulHeight x

中文:
引理 mulHeight_pos
  条件: (x : Projectivization K (ι -> K))
  结论: 0 < mulHeight x
  证明: zero_lt_one.trans_le one_le_mulHeight x

Depends on / 依赖: one_le_mulHeight, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma mulHeight_pos (x : Projectivization K (ι -> K)) : 0 < mulHeight x :=
zero_lt_one.trans_le one_le_mulHeight x

/--
lemma `mulHeight_ne_zero` / 引理 `mulHeight_ne_zero`

English:
lemma mulHeight_ne_zero
  given: (x : Projectivization K (ι -> K))
  statement: mulHeight x != 0
  proof: (mulHeight_pos x).ne'

中文:
引理 mulHeight_ne_zero
  条件: (x : Projectivization K (ι -> K))
  结论: mulHeight x != 0
  证明: (mulHeight_pos x).ne'

Depends on / 依赖: mulHeight_pos
-/
lemma mulHeight_ne_zero (x : Projectivization K (ι -> K)) : mulHeight x != 0 :=
  (mulHeight_pos x).ne'

/--
lemma `logHeight_nonneg` / 引理 `logHeight_nonneg`

English:
lemma logHeight_nonneg
  given: (x : Projectivization K (ι -> K))
  statement: 0 <= logHeight x
  proof: by
  rw [logHeight_eq_log_mulHeight]
exact log_nonneg x.one_le_mulHeight

中文:
引理 logHeight_nonneg
  条件: (x : Projectivization K (ι -> K))
  结论: 0 <= logHeight x
  证明: by
  rw [logHeight_eq_log_mulHeight]
exact log_nonneg x.one_le_mulHeight

Depends on / 依赖: logHeight_eq_log_mulHeight, log_nonneg, one_le_mulHeight, x.one_le_mulHeight
-/
lemma logHeight_nonneg (x : Projectivization K (ι -> K)) : 0 <= logHeight x := by
  rw [logHeight_eq_log_mulHeight]
exact log_nonneg x.one_le_mulHeight

end Projectivization

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Projectivization

/-- Extension for the `positivity` tactic: `Projectivization.mulHeight` is always positive. -/
@[positivity Projectivization.mulHeight _]
meta def evalProjMulHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@mulHeight $K $KF $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q(mulHeight_pos $a))
  | _, _, _ => throwError "not Projectivization.mulHeight"

/-- Extension for the `positivity` tactic: `Projectivization.logHeight` is always nonnegative. -/
@[positivity Projectivization.logHeight _]
meta def evalProjLogHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@logHeight $K $KF $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q(logHeight_nonneg $a))
  | _, _, _ => throwError "not Projectivization.logHeight"

end Mathlib.Meta.Positivity
