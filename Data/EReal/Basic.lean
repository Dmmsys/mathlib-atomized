/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Data.ENNReal.Operations

/-!
# The extended real numbers

This file defines `EReal`, `ℝ` with a top element `⊤` and a bottom element `⊥`, implemented as
`WithBot (WithTop ℝ)`.

`EReal` is a `CompleteLinearOrder`, deduced by typeclass inference from the fact that
`WithBot (WithTop L)` completes a conditionally complete linear order `L`.

Coercions from `ℝ` (called `coe` in lemmas) and from `ℝ≥0∞` (`coe_ennreal`) are registered
and their basic properties proved. The latter takes up most of the rest of this file.

## Tags

real, ereal, complete lattice
-/

@[expose] public section

open Function ENNReal NNReal Set

noncomputable section

/-- The type of extended real numbers `[-∞, ∞]`, constructed as `WithBot (WithTop ℝ)`. -/
@[wikidata Q2039387]
/--
Definition of `EReal` / `EReal` 的定义

English:
definition EReal
  body: WithBot (WithTop Real)
deriving Nontrivial,
  Zero, One, AddMonoid, AddCommMonoid, AddCommMonoidWithOne, CharZero,
  Top, Bot, SupSet, InfSet, PartialOrder, LinearOrder, CompleteLinearOrder, DenselyOrdered,
  ZeroLEOneClass, IsOrderedAddMonoid

中文:
定义 EReal
  定义体: WithBot (WithTop Real)
deriving Nontrivial,
  Zero, One, AddMonoid, AddCommMonoid, AddCommMonoidWithOne, CharZero,
  Top, Bot, SupSet, InfSet, PartialOrder, LinearOrder, CompleteLinearOrder, DenselyOrdered,
  ZeroLEOneClass, IsOrderedAddMonoid

Depends on / 依赖: WithBot, WithTop
-/
def EReal := WithBot (WithTop Real)
deriving Nontrivial,
  Zero, One, AddMonoid, AddCommMonoid, AddCommMonoidWithOne, CharZero,
  Top, Bot, SupSet, InfSet, PartialOrder, LinearOrder, CompleteLinearOrder, DenselyOrdered,
  ZeroLEOneClass, IsOrderedAddMonoid

/--
Definition of `Real.toEReal` / `Real.toEReal` 的定义

English:
definition Real.toEReal
  signature: : Real -> EReal
  body: WithBot.some ∘ WithTop.some

中文:
定义 Real.toEReal
  签名: : 实数 -> E实数
  定义体: WithBot.some ∘ WithTop.some
-/
@[coe] def Real.toEReal : Real -> EReal := WithBot.some ∘ WithTop.some

namespace EReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Real EReal
  body: ⟨Real.toEReal⟩

中文:
实例 :
  签名: Coe 实数 E实数
  定义体: ⟨Real.toEReal⟩

Depends on / 依赖: Real.toEReal, toEReal
-/
instance : Coe Real EReal := ⟨Real.toEReal⟩

/--
theorem `coe_strictMono` / 定理 `coe_strictMono`

English:
theorem coe_strictMono
  statement: StrictMono Real.toEReal
  proof: WithBot.coe_strictMono.comp WithTop.coe_strictMono

中文:
定理 coe_strictMono
  结论: StrictMono 实数.toE实数
  证明: WithBot.coe_strictMono.comp WithTop.coe_strictMono

Depends on / 依赖: WithBot, WithBot.coe_strictMono.comp, WithTop, WithTop.coe_strictMono, coe_strictMono
-/
theorem coe_strictMono : StrictMono Real.toEReal :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective Real.toEReal
  proof: coe_strictMono.injective

@[simp, norm_cast]

中文:
定理 coe_injective
  结论: Injective 实数.toE实数
  证明: coe_strictMono.injective

@[simp, norm_cast]

Depends on / 依赖: coe_strictMono, coe_strictMono.injective, injective
-/
theorem coe_injective : Injective Real.toEReal :=
  coe_strictMono.injective

@[simp, norm_cast]
/--
theorem `coe_le_coe_iff` / 定理 `coe_le_coe_iff`

English:
theorem coe_le_coe_iff
  given: {x y : Real}
  statement: (x : EReal) <= (y : EReal) ↔ x <= y
  proof: coe_strictMono.le_iff_le

@[gcongr] protected alias ⟨_, coe_le_coe⟩ := EReal.coe_le_coe_iff

@[simp, norm_cast]

中文:
定理 coe_le_coe_iff
  条件: {x y : 实数}
  结论: (x : E实数) <= (y : E实数) ↔ x <= y
  证明: coe_strictMono.le_iff_le

@[gcongr] protected alias ⟨_, coe_le_coe⟩ := EReal.coe_le_coe_iff

@[simp, norm_cast]
-/
protected theorem coe_le_coe_iff {x y : Real} : (x : EReal) <= (y : EReal) ↔ x <= y :=
  coe_strictMono.le_iff_le

@[gcongr] protected alias ⟨_, coe_le_coe⟩ := EReal.coe_le_coe_iff

@[simp, norm_cast]
/--
theorem `coe_lt_coe_iff` / 定理 `coe_lt_coe_iff`

English:
theorem coe_lt_coe_iff
  given: {x y : Real}
  statement: (x : EReal) < (y : EReal) ↔ x < y
  proof: coe_strictMono.lt_iff_lt

@[gcongr] protected alias ⟨_, coe_lt_coe⟩ := EReal.coe_lt_coe_iff

@[simp, norm_cast]

中文:
定理 coe_lt_coe_iff
  条件: {x y : 实数}
  结论: (x : E实数) < (y : E实数) ↔ x < y
  证明: coe_strictMono.lt_iff_lt

@[gcongr] protected alias ⟨_, coe_lt_coe⟩ := EReal.coe_lt_coe_iff

@[simp, norm_cast]
-/
protected theorem coe_lt_coe_iff {x y : Real} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[gcongr] protected alias ⟨_, coe_lt_coe⟩ := EReal.coe_lt_coe_iff

@[simp, norm_cast]
/--
theorem `coe_eq_coe_iff` / 定理 `coe_eq_coe_iff`

English:
theorem coe_eq_coe_iff
  given: {x y : Real}
  statement: (x : EReal) = (y : EReal) ↔ x = y
  proof: coe_injective.eq_iff

中文:
定理 coe_eq_coe_iff
  条件: {x y : 实数}
  结论: (x : E实数) = (y : E实数) ↔ x = y
  证明: coe_injective.eq_iff
-/
protected theorem coe_eq_coe_iff {x y : Real} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_injective.eq_iff

/--
theorem `coe_ne_coe_iff` / 定理 `coe_ne_coe_iff`

English:
theorem coe_ne_coe_iff
  given: {x y : Real}
  statement: (x : EReal) != (y : EReal) ↔ x != y
  proof: coe_injective.ne_iff

@[simp, norm_cast]

中文:
定理 coe_ne_coe_iff
  条件: {x y : 实数}
  结论: (x : E实数) != (y : E实数) ↔ x != y
  证明: coe_injective.ne_iff

@[simp, norm_cast]
-/
protected theorem coe_ne_coe_iff {x y : Real} : (x : EReal) != (y : EReal) ↔ x != y :=
  coe_injective.ne_iff

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: {n : Nat}
  statement: ((n : Real) : EReal) = n
  proof: rfl

中文:
定理 coe_natCast
  条件: {n : 自然数}
  结论: ((n : 实数) : E实数) = n
  证明: rfl
-/
protected theorem coe_natCast {n : Nat} : ((n : Real) : EReal) = n := rfl

/--
Definition of `orderEmbedding` / `orderEmbedding` 的定义

English:
definition orderEmbedding
  signature: : Real ↪o EReal where
  body: Real.toEReal
  inj' := EReal.coe_injective
  map_rel_iff' {x y} := by simp

中文:
定义 orderEmbedding
  签名: : 实数 ↪o E实数 where
  定义体: Real.toEReal
  inj' := EReal.coe_injective
  map_rel_iff' {x y} := by simp

Depends on / 依赖: Real.toEReal, toEReal
-/
def orderEmbedding : Real ↪o EReal where
  toFun := Real.toEReal
  inj' := EReal.coe_injective
  map_rel_iff' {x y} := by simp

/--
theorem `coe_orderEmbedding` / 定理 `coe_orderEmbedding`

English:
theorem coe_orderEmbedding
  statement: ⇑orderEmbedding = Real.toEReal
  proof: rfl

中文:
定理 coe_orderEmbedding
  结论: ⇑orderEmbedding = 实数.toE实数
  证明: rfl
-/
theorem coe_orderEmbedding : ⇑orderEmbedding = Real.toEReal := rfl

/--
Definition of `_root_.ENNReal.toEReal` / `_root_.ENNReal.toEReal` 的定义

English:
definition _root_.ENNReal.toEReal
  signature: : Real>=0∞ -> EReal

中文:
定义 _root_.ENNReal.toEReal
  签名: : 实数>=0∞ -> E实数
-/
@[coe] def _root_.ENNReal.toEReal : Real>=0∞ -> EReal
  | ⊤ => ⊤
  | .some x => x.1

/--
Instance `hasCoeENNReal` / 实例 `hasCoeENNReal`

English:
instance hasCoeENNReal
  signature: : Coe Real>=0∞ EReal
  body: ⟨ENNReal.toEReal⟩

中文:
实例 hasCoeENNReal
  签名: : Coe 实数>=0∞ E实数
  定义体: ⟨ENNReal.toEReal⟩

Depends on / 依赖: ENNReal, ENNReal.toEReal, toEReal
-/
instance hasCoeENNReal : Coe Real>=0∞ EReal :=
  ⟨ENNReal.toEReal⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited EReal
  body: ⟨0⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Inhabited E实数
  定义体: ⟨0⟩

@[simp, norm_cast]
-/
instance : Inhabited EReal := ⟨0⟩

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : Real) : EReal) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ((0 : 实数) : E实数) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ((0 : Real) : EReal) = 0 := rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : Real) : EReal) = 1
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : 实数) : E实数) = 1
  证明: rfl
-/
theorem coe_one : ((1 : Real) : EReal) = 1 := rfl

/-- A recursor for `EReal` in terms of the coercion.

When working in term mode, note that pattern matching can be used directly,
although this is prone to leaking the implementation details in terms of `Option`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {motive : EReal -> Sort*}

中文:
定义 rec
  签名: {motive : E实数 -> Sort*}
-/
protected def rec {motive : EReal -> Sort*}
    (bot : motive ⊥) (coe : forall a : Real, motive a) (top : motive ⊤) : forall a : EReal, motive a
  | ⊥ => bot
  | (a : Real) => coe a
  | ⊤ => top

/--
theorem `rec_bot` / 定理 `rec_bot`

English:
theorem rec_bot
  statement: {motive : EReal -> Sort*}
  proof: rfl

中文:
定理 rec_bot
  结论: {motive : E实数 -> Sort*}
  证明: rfl
-/
@[simp] theorem rec_bot {motive : EReal -> Sort*}
    (bot : motive ⊥) (coe : forall a : Real, motive a) (top : motive ⊤) : EReal.rec bot coe top ⊥ = bot :=
  rfl

/--
theorem `rec_top` / 定理 `rec_top`

English:
theorem rec_top
  statement: {motive : EReal -> Sort*}
  proof: rfl

中文:
定理 rec_top
  结论: {motive : E实数 -> Sort*}
  证明: rfl
-/
@[simp] theorem rec_top {motive : EReal -> Sort*}
    (bot : motive ⊥) (coe : forall a : Real, motive a) (top : motive ⊤) : EReal.rec bot coe top ⊤ = top :=
  rfl

/--
theorem `rec_coe` / 定理 `rec_coe`

English:
theorem rec_coe
  statement: {motive : EReal -> Sort*}
  proof: rfl

中文:
定理 rec_coe
  结论: {motive : E实数 -> Sort*}
  证明: rfl
-/
@[simp] theorem rec_coe {motive : EReal -> Sort*}
    (bot : motive ⊥) (coe : forall a : Real, motive a) (top : motive ⊤) (a : Real) :
    EReal.rec bot coe top a = coe a := rfl

/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : EReal -> Prop}
  statement: (forall r, p r) ↔ p ⊥ ∧ p ⊤ ∧ forall r : Real, p r where
  proof: ⟨h _, h _, fun _ => h _⟩
  mpr h := EReal.rec h.1 h.2.2 h.2.1

中文:
引理 «forall»
  条件: {p : E实数 -> 命题}
  结论: (对任意 r, p r) ↔ p ⊥ ∧ p ⊤ ∧ 对任意 r : 实数, p r where
  证明: ⟨h _, h _, fun _ => h _⟩
  mpr h := EReal.rec h.1 h.2.2 h.2.1
-/
protected lemma «forall» {p : EReal -> Prop} : (forall r, p r) ↔ p ⊥ ∧ p ⊤ ∧ forall r : Real, p r where
  mp h := ⟨h _, h _, fun _ => h _⟩
  mpr h := EReal.rec h.1 h.2.2 h.2.1

/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : EReal -> Prop}
  statement: (exists r, p r) ↔ p ⊥ ∨ p ⊤ ∨ exists r : Real, p r where
  proof: by rintro ⟨r, hr⟩; cases r <;> aesop
  mpr := by rintro (h | h | ⟨r, hr⟩) <;> exact ⟨_, ‹_›⟩

中文:
引理 «exists»
  条件: {p : E实数 -> 命题}
  结论: (存在 r, p r) ↔ p ⊥ ∨ p ⊤ ∨ 存在 r : 实数, p r where
  证明: by rintro ⟨r, hr⟩; cases r <;> aesop
  mpr := by rintro (h | h | ⟨r, hr⟩) <;> exact ⟨_, ‹_›⟩
-/
protected lemma «exists» {p : EReal -> Prop} : (exists r, p r) ↔ p ⊥ ∨ p ⊤ ∨ exists r : Real, p r where
  mp := by rintro ⟨r, hr⟩; cases r <;> aesop
  mpr := by rintro (h | h | ⟨r, hr⟩) <;> exact ⟨_, ‹_›⟩

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : EReal -> EReal -> EReal

中文:
定义 mul
  签名: : E实数 -> E实数 -> E实数
-/
protected def mul : EReal -> EReal -> EReal
  | ⊥, ⊥ => ⊤
  | ⊥, ⊤ => ⊥
  | ⊥, (y : Real) => if 0 < y then ⊥ else if y = 0 then 0 else ⊤
  | ⊤, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | ⊤, (y : Real) => if 0 < y then ⊤ else if y = 0 then 0 else ⊥
  | (x : Real), ⊤ => if 0 < x then ⊤ else if x = 0 then 0 else ⊥
  | (x : Real), ⊥ => if 0 < x then ⊥ else if x = 0 then 0 else ⊤
  | (x : Real), (y : Real) => (x * y : Real)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul EReal
  body: ⟨EReal.mul⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Mul E实数
  定义体: ⟨EReal.mul⟩

@[simp, norm_cast]

Depends on / 依赖: EReal.mul
-/
instance : Mul EReal := ⟨EReal.mul⟩

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : Real)
  statement: (↑(x * y) : EReal) = x * y
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : 实数)
  结论: (↑(x * y) : E实数) = x * y
  证明: rfl
-/
theorem coe_mul (x y : Real) : (↑(x * y) : EReal) = x * y :=
  rfl

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. -/
@[elab_as_elim]
/--
theorem `induction₂` / 定理 `induction₂`

English:
theorem induction₂
  statement: {P : EReal -> EReal -> Prop} (top_top : P ⊤ ⊤) (top_pos : forall x : Real, 0 < x -> P ⊤ x)

中文:
定理 induction₂
  结论: {P : E实数 -> E实数 -> 命题} (top_top : P ⊤ ⊤) (top_pos : 对任意 x : 实数, 0 < x -> P ⊤ x)
-/
theorem induction₂ {P : EReal -> EReal -> Prop} (top_top : P ⊤ ⊤) (top_pos : forall x : Real, 0 < x -> P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : forall x : Real, x < 0 -> P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_top : forall x : Real, 0 < x -> P x ⊤) (pos_bot : forall x : Real, 0 < x -> P x ⊥) (zero_top : P 0 ⊤)
    (coe_coe : forall x y : Real, P x y) (zero_bot : P 0 ⊥) (neg_top : forall x : Real, x < 0 -> P x ⊤)
    (neg_bot : forall x : Real, x < 0 -> P x ⊥) (bot_top : P ⊥ ⊤) (bot_pos : forall x : Real, 0 < x -> P ⊥ x)
    (bot_zero : P ⊥ 0) (bot_neg : forall x : Real, x < 0 -> P ⊥ x) (bot_bot : P ⊥ ⊥) : forall x y, P x y
  | ⊥, ⊥ => bot_bot
  | ⊥, (y : Real) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [bot_neg y hy, bot_zero, bot_pos y hy]
  | ⊥, ⊤ => bot_top
  | (x : Real), ⊥ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_bot x hx, zero_bot, pos_bot x hx]
  | (x : Real), (y : Real) => coe_coe _ _
  | (x : Real), ⊤ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_top x hx, zero_top, pos_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : Real) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [top_neg y hy, top_zero, top_pos y hy]
  | ⊤, ⊤ => top_top

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
/--
theorem `induction₂_symm` / 定理 `induction₂_symm`

English:
theorem induction₂_symm
  statement: {P : EReal -> EReal -> Prop} (symm : forall {x y}, P x y -> P y x)
  proof: @induction₂ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot

中文:
定理 induction₂_symm
  结论: {P : E实数 -> E实数 -> 命题} (symm : 对任意 {x y}, P x y -> P y x)
  证明: @induction₂ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot

Depends on / 依赖: bot_bot, coe_coe, neg_bot, pos_bot, top_bot, top_neg, top_pos, top_top, top_zero, zero_bot
-/
theorem induction₂_symm {P : EReal -> EReal -> Prop} (symm : forall {x y}, P x y -> P y x)
    (top_top : P ⊤ ⊤) (top_pos : forall x : Real, 0 < x -> P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : forall x : Real, x < 0 -> P ⊤ x) (top_bot : P ⊤ ⊥) (pos_bot : forall x : Real, 0 < x -> P x ⊥)
    (coe_coe : forall x y : Real, P x y) (zero_bot : P 0 ⊥) (neg_bot : forall x : Real, x < 0 -> P x ⊥)
    (bot_bot : P ⊥ ⊥) : forall x y, P x y :=
  @induction₂ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot

/--
theorem `mul_comm` / 定理 `mul_comm`

English:
theorem mul_comm
  given: (x y : EReal)
  statement: x * y = y * x
  proof: by
  induction x <;> induction y <;>
    try { rfl }
  rw [← coe_mul]; rw [← coe_mul]; rw [mul_comm]

中文:
定理 mul_comm
  条件: (x y : E实数)
  结论: x * y = y * x
  证明: by
  induction x <;> induction y <;>
    try { rfl }
  rw [← coe_mul]; rw [← coe_mul]; rw [mul_comm]
-/
protected theorem mul_comm (x y : EReal) : x * y = y * x := by
  induction x <;> induction y <;>
    try { rfl }
  rw [← coe_mul]; rw [← coe_mul]; rw [mul_comm]

/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  statement: forall x : EReal, 1 * x = x

中文:
定理 one_mul
  结论: 对任意 x : E实数, 1 * x = x
-/
protected theorem one_mul : forall x : EReal, 1 * x = x
  | ⊤ => if_pos one_pos
  | ⊥ => if_pos one_pos
  | (x : Real) => congr_arg Real.toEReal (one_mul x)

/--
theorem `zero_mul` / 定理 `zero_mul`

English:
theorem zero_mul
  statement: forall x : EReal, 0 * x = 0

中文:
定理 zero_mul
  结论: 对任意 x : E实数, 0 * x = 0
-/
protected theorem zero_mul : forall x : EReal, 0 * x = 0
  | ⊤ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
  | ⊥ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
  | (x : Real) => congr_arg Real.toEReal (zero_mul x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulZeroOneClass EReal
  body: EReal.one_mul
  mul_one := fun x => by rw [EReal.mul_comm, EReal.one_mul]
  zero_mul := EReal.zero_mul
  mul_zero := fun x => by rw [EReal.mul_comm, EReal.zero_mul]

中文:
实例 :
  签名: MulZeroOneClass E实数
  定义体: EReal.one_mul
  mul_one := fun x => by rw [EReal.mul_comm, EReal.one_mul]
  zero_mul := EReal.zero_mul
  mul_zero := fun x => by rw [EReal.mul_comm, EReal.zero_mul]

Depends on / 依赖: EReal.one_mul, one_mul
-/
instance : MulZeroOneClass EReal where
  one_mul := EReal.one_mul
  mul_one := fun x => by rw [EReal.mul_comm, EReal.one_mul]
  zero_mul := EReal.zero_mul
  mul_zero := fun x => by rw [EReal.mul_comm, EReal.zero_mul]


/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift EReal Real (↑) fun r => r != ⊤ ∧ r != ⊥ where
  body: by
    induction x
    · simp at hx
    · simp
    · simp at hx

中文:
实例 canLift
  签名: : CanLift E实数 实数 (↑) fun r => r != ⊤ ∧ r != ⊥ where
  定义体: by
    induction x
    · simp at hx
    · simp
    · simp at hx
-/
instance canLift : CanLift EReal Real (↑) fun r => r != ⊤ ∧ r != ⊥ where
  prf x hx := by
    induction x
    · simp at hx
    · simp
    · simp at hx

/--
Definition of `toReal` / `toReal` 的定义

English:
definition toReal
  signature: : EReal -> Real

中文:
定义 toReal
  签名: : E实数 -> 实数
-/
def toReal : EReal -> Real
  | ⊥ => 0
  | ⊤ => 0
  | (x : Real) => x

@[simp]
/--
theorem `toReal_top` / 定理 `toReal_top`

English:
theorem toReal_top
  statement: toReal ⊤ = 0
  proof: rfl

@[simp]

中文:
定理 toReal_top
  结论: to实数 ⊤ = 0
  证明: rfl

@[simp]
-/
theorem toReal_top : toReal ⊤ = 0 :=
  rfl

@[simp]
/--
theorem `toReal_bot` / 定理 `toReal_bot`

English:
theorem toReal_bot
  statement: toReal ⊥ = 0
  proof: rfl

@[simp]

中文:
定理 toReal_bot
  结论: to实数 ⊥ = 0
  证明: rfl

@[simp]
-/
theorem toReal_bot : toReal ⊥ = 0 :=
  rfl

@[simp]
/--
theorem `toReal_zero` / 定理 `toReal_zero`

English:
theorem toReal_zero
  statement: toReal 0 = 0
  proof: rfl

@[simp]

中文:
定理 toReal_zero
  结论: to实数 0 = 0
  证明: rfl

@[simp]
-/
theorem toReal_zero : toReal 0 = 0 :=
  rfl

@[simp]
/--
theorem `toReal_one` / 定理 `toReal_one`

English:
theorem toReal_one
  statement: toReal 1 = 1
  proof: rfl

@[simp]

中文:
定理 toReal_one
  结论: to实数 1 = 1
  证明: rfl

@[simp]
-/
theorem toReal_one : toReal 1 = 1 :=
  rfl

@[simp]
/--
theorem `toReal_coe` / 定理 `toReal_coe`

English:
theorem toReal_coe
  given: (x : Real)
  statement: toReal (x : EReal) = x
  proof: rfl

@[simp]

中文:
定理 toReal_coe
  条件: (x : 实数)
  结论: to实数 (x : E实数) = x
  证明: rfl

@[simp]
-/
theorem toReal_coe (x : Real) : toReal (x : EReal) = x :=
  rfl

@[simp]
/--
theorem `bot_lt_coe` / 定理 `bot_lt_coe`

English:
theorem bot_lt_coe
  given: (x : Real)
  statement: (⊥ : EReal) < x
  proof: WithBot.bot_lt_coe _

@[simp]

中文:
定理 bot_lt_coe
  条件: (x : 实数)
  结论: (⊥ : E实数) < x
  证明: WithBot.bot_lt_coe _

@[simp]

Depends on / 依赖: WithBot, WithBot.bot_lt_coe, bot_lt_coe
-/
theorem bot_lt_coe (x : Real) : (⊥ : EReal) < x :=
  WithBot.bot_lt_coe _

@[simp]
/--
theorem `coe_ne_bot` / 定理 `coe_ne_bot`

English:
theorem coe_ne_bot
  given: (x : Real)
  statement: (x : EReal) != ⊥
  proof: (bot_lt_coe x).ne'

@[simp]

中文:
定理 coe_ne_bot
  条件: (x : 实数)
  结论: (x : E实数) != ⊥
  证明: (bot_lt_coe x).ne'

@[simp]

Depends on / 依赖: bot_lt_coe
-/
theorem coe_ne_bot (x : Real) : (x : EReal) != ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
/--
theorem `bot_ne_coe` / 定理 `bot_ne_coe`

English:
theorem bot_ne_coe
  given: (x : Real)
  statement: (⊥ : EReal) != x
  proof: (bot_lt_coe x).ne

@[simp]

中文:
定理 bot_ne_coe
  条件: (x : 实数)
  结论: (⊥ : E实数) != x
  证明: (bot_lt_coe x).ne

@[simp]

Depends on / 依赖: bot_lt_coe
-/
theorem bot_ne_coe (x : Real) : (⊥ : EReal) != x :=
  (bot_lt_coe x).ne

@[simp]
/--
theorem `coe_lt_top` / 定理 `coe_lt_top`

English:
theorem coe_lt_top
  given: (x : Real)
  statement: (x : EReal) < ⊤
  proof: WithBot.coe_lt_coe.2 WithTop.coe_lt_top _

@[simp]

中文:
定理 coe_lt_top
  条件: (x : 实数)
  结论: (x : E实数) < ⊤
  证明: WithBot.coe_lt_coe.2 WithTop.coe_lt_top _

@[simp]

Depends on / 依赖: WithBot, WithBot.coe_lt_coe, WithTop, WithTop.coe_lt_top, coe_lt_coe, coe_lt_top
-/
theorem coe_lt_top (x : Real) : (x : EReal) < ⊤ :=
WithBot.coe_lt_coe.2 WithTop.coe_lt_top _

@[simp]
/--
theorem `coe_ne_top` / 定理 `coe_ne_top`

English:
theorem coe_ne_top
  given: (x : Real)
  statement: (x : EReal) != ⊤
  proof: (coe_lt_top x).ne

@[simp]

中文:
定理 coe_ne_top
  条件: (x : 实数)
  结论: (x : E实数) != ⊤
  证明: (coe_lt_top x).ne

@[simp]

Depends on / 依赖: coe_lt_top
-/
theorem coe_ne_top (x : Real) : (x : EReal) != ⊤ :=
  (coe_lt_top x).ne

@[simp]
/--
theorem `top_ne_coe` / 定理 `top_ne_coe`

English:
theorem top_ne_coe
  given: (x : Real)
  statement: (⊤ : EReal) != x
  proof: (coe_lt_top x).ne'

@[simp]

中文:
定理 top_ne_coe
  条件: (x : 实数)
  结论: (⊤ : E实数) != x
  证明: (coe_lt_top x).ne'

@[simp]

Depends on / 依赖: coe_lt_top
-/
theorem top_ne_coe (x : Real) : (⊤ : EReal) != x :=
  (coe_lt_top x).ne'

@[simp]
/--
theorem `bot_lt_zero` / 定理 `bot_lt_zero`

English:
theorem bot_lt_zero
  statement: (⊥ : EReal) < 0
  proof: bot_lt_coe 0

@[simp]

中文:
定理 bot_lt_zero
  结论: (⊥ : E实数) < 0
  证明: bot_lt_coe 0

@[simp]

Depends on / 依赖: bot_lt_coe
-/
theorem bot_lt_zero : (⊥ : EReal) < 0 :=
  bot_lt_coe 0

@[simp]
/--
theorem `bot_ne_zero` / 定理 `bot_ne_zero`

English:
theorem bot_ne_zero
  statement: (⊥ : EReal) != 0
  proof: (coe_ne_bot 0).symm

@[simp]

中文:
定理 bot_ne_zero
  结论: (⊥ : E实数) != 0
  证明: (coe_ne_bot 0).symm

@[simp]

Depends on / 依赖: coe_ne_bot
-/
theorem bot_ne_zero : (⊥ : EReal) != 0 :=
  (coe_ne_bot 0).symm

@[simp]
/--
theorem `zero_ne_bot` / 定理 `zero_ne_bot`

English:
theorem zero_ne_bot
  statement: (0 : EReal) != ⊥
  proof: coe_ne_bot 0

@[simp]

中文:
定理 zero_ne_bot
  结论: (0 : E实数) != ⊥
  证明: coe_ne_bot 0

@[simp]

Depends on / 依赖: coe_ne_bot
-/
theorem zero_ne_bot : (0 : EReal) != ⊥ :=
  coe_ne_bot 0

@[simp]
/--
theorem `zero_lt_top` / 定理 `zero_lt_top`

English:
theorem zero_lt_top
  statement: (0 : EReal) < ⊤
  proof: coe_lt_top 0

@[simp]

中文:
定理 zero_lt_top
  结论: (0 : E实数) < ⊤
  证明: coe_lt_top 0

@[simp]

Depends on / 依赖: coe_lt_top
-/
theorem zero_lt_top : (0 : EReal) < ⊤ :=
  coe_lt_top 0

@[simp]
/--
theorem `zero_ne_top` / 定理 `zero_ne_top`

English:
theorem zero_ne_top
  statement: (0 : EReal) != ⊤
  proof: coe_ne_top 0

@[simp]

中文:
定理 zero_ne_top
  结论: (0 : E实数) != ⊤
  证明: coe_ne_top 0

@[simp]

Depends on / 依赖: coe_ne_top
-/
theorem zero_ne_top : (0 : EReal) != ⊤ :=
  coe_ne_top 0

@[simp]
/--
theorem `top_ne_zero` / 定理 `top_ne_zero`

English:
theorem top_ne_zero
  statement: (⊤ : EReal) != 0
  proof: (coe_ne_top 0).symm

中文:
定理 top_ne_zero
  结论: (⊤ : E实数) != 0
  证明: (coe_ne_top 0).symm

Depends on / 依赖: coe_ne_top
-/
theorem top_ne_zero : (⊤ : EReal) != 0 :=
  (coe_ne_top 0).symm

/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  statement: range Real.toEReal = {⊥, ⊤}ᶜ
  proof: by
  ext x
  induction x <;> simp

中文:
定理 range_coe
  结论: range 实数.toE实数 = {⊥, ⊤}ᶜ
  证明: by
  ext x
  induction x <;> simp
-/
theorem range_coe : range Real.toEReal = {⊥, ⊤}ᶜ := by
  ext x
  induction x <;> simp

/--
theorem `range_coe_eq_Ioo` / 定理 `range_coe_eq_Ioo`

English:
theorem range_coe_eq_Ioo
  statement: range Real.toEReal = Ioo ⊥ ⊤
  proof: by
  ext x
  induction x <;> simp

@[simp, norm_cast]

中文:
定理 range_coe_eq_Ioo
  结论: range 实数.toE实数 = Ioo ⊥ ⊤
  证明: by
  ext x
  induction x <;> simp

@[simp, norm_cast]
-/
theorem range_coe_eq_Ioo : range Real.toEReal = Ioo ⊥ ⊤ := by
  ext x
  induction x <;> simp

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : Real)
  statement: (↑(x + y) : EReal) = x + y
  proof: rfl

中文:
定理 coe_add
  条件: (x y : 实数)
  结论: (↑(x + y) : E实数) = x + y
  证明: rfl
-/
theorem coe_add (x y : Real) : (↑(x + y) : EReal) = x + y :=
  rfl

-- `coe_mul` moved up

@[norm_cast]
/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  given: (n : Nat) (x : Real)
  statement: (↑(n • x) : EReal) = n • (x : EReal)
  proof: map_nsmul (⟨⟨Real.toEReal, coe_zero⟩, coe_add⟩ : Real ->+ EReal) _ _

@[simp, norm_cast]

中文:
定理 coe_nsmul
  条件: (n : 自然数) (x : 实数)
  结论: (↑(n • x) : E实数) = n • (x : E实数)
  证明: map_nsmul (⟨⟨Real.toEReal, coe_zero⟩, coe_add⟩ : Real ->+ EReal) _ _

@[simp, norm_cast]

Depends on / 依赖: Real.toEReal, coe_add, coe_zero, map_nsmul, toEReal
-/
theorem coe_nsmul (n : Nat) (x : Real) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_nsmul (⟨⟨Real.toEReal, coe_zero⟩, coe_add⟩ : Real ->+ EReal) _ _

@[simp, norm_cast]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: {x : Real}
  statement: (x : EReal) = 0 ↔ x = 0
  proof: EReal.coe_eq_coe_iff

@[simp, norm_cast]

中文:
定理 coe_eq_zero
  条件: {x : 实数}
  结论: (x : E实数) = 0 ↔ x = 0
  证明: EReal.coe_eq_coe_iff

@[simp, norm_cast]

Depends on / 依赖: EReal.coe_eq_coe_iff, coe_eq_coe_iff
-/
theorem coe_eq_zero {x : Real} : (x : EReal) = 0 ↔ x = 0 :=
  EReal.coe_eq_coe_iff

@[simp, norm_cast]
/--
theorem `coe_eq_one` / 定理 `coe_eq_one`

English:
theorem coe_eq_one
  given: {x : Real}
  statement: (x : EReal) = 1 ↔ x = 1
  proof: EReal.coe_eq_coe_iff

中文:
定理 coe_eq_one
  条件: {x : 实数}
  结论: (x : E实数) = 1 ↔ x = 1
  证明: EReal.coe_eq_coe_iff

Depends on / 依赖: EReal.coe_eq_coe_iff, coe_eq_coe_iff
-/
theorem coe_eq_one {x : Real} : (x : EReal) = 1 ↔ x = 1 :=
  EReal.coe_eq_coe_iff

/--
theorem `coe_ne_zero` / 定理 `coe_ne_zero`

English:
theorem coe_ne_zero
  given: {x : Real}
  statement: (x : EReal) != 0 ↔ x != 0
  proof: EReal.coe_ne_coe_iff

中文:
定理 coe_ne_zero
  条件: {x : 实数}
  结论: (x : E实数) != 0 ↔ x != 0
  证明: EReal.coe_ne_coe_iff

Depends on / 依赖: EReal.coe_ne_coe_iff, coe_ne_coe_iff
-/
theorem coe_ne_zero {x : Real} : (x : EReal) != 0 ↔ x != 0 :=
  EReal.coe_ne_coe_iff

/--
theorem `coe_ne_one` / 定理 `coe_ne_one`

English:
theorem coe_ne_one
  given: {x : Real}
  statement: (x : EReal) != 1 ↔ x != 1
  proof: EReal.coe_ne_coe_iff

@[simp, norm_cast]

中文:
定理 coe_ne_one
  条件: {x : 实数}
  结论: (x : E实数) != 1 ↔ x != 1
  证明: EReal.coe_ne_coe_iff

@[simp, norm_cast]

Depends on / 依赖: EReal.coe_ne_coe_iff, coe_ne_coe_iff
-/
theorem coe_ne_one {x : Real} : (x : EReal) != 1 ↔ x != 1 :=
  EReal.coe_ne_coe_iff

@[simp, norm_cast]
/--
theorem `coe_nonneg` / 定理 `coe_nonneg`

English:
theorem coe_nonneg
  given: {x : Real}
  statement: (0 : EReal) <= x ↔ 0 <= x
  proof: EReal.coe_le_coe_iff

@[simp, norm_cast]

中文:
定理 coe_nonneg
  条件: {x : 实数}
  结论: (0 : E实数) <= x ↔ 0 <= x
  证明: EReal.coe_le_coe_iff

@[simp, norm_cast]
-/
protected theorem coe_nonneg {x : Real} : (0 : EReal) <= x ↔ 0 <= x :=
  EReal.coe_le_coe_iff

@[simp, norm_cast]
/--
theorem `coe_nonpos` / 定理 `coe_nonpos`

English:
theorem coe_nonpos
  given: {x : Real}
  statement: (x : EReal) <= 0 ↔ x <= 0
  proof: EReal.coe_le_coe_iff

@[simp, norm_cast]

中文:
定理 coe_nonpos
  条件: {x : 实数}
  结论: (x : E实数) <= 0 ↔ x <= 0
  证明: EReal.coe_le_coe_iff

@[simp, norm_cast]
-/
protected theorem coe_nonpos {x : Real} : (x : EReal) <= 0 ↔ x <= 0 :=
  EReal.coe_le_coe_iff

@[simp, norm_cast]
/--
theorem `coe_pos` / 定理 `coe_pos`

English:
theorem coe_pos
  given: {x : Real}
  statement: (0 : EReal) < x ↔ 0 < x
  proof: EReal.coe_lt_coe_iff

@[simp, norm_cast]

中文:
定理 coe_pos
  条件: {x : 实数}
  结论: (0 : E实数) < x ↔ 0 < x
  证明: EReal.coe_lt_coe_iff

@[simp, norm_cast]
-/
protected theorem coe_pos {x : Real} : (0 : EReal) < x ↔ 0 < x :=
  EReal.coe_lt_coe_iff

@[simp, norm_cast]
/--
theorem `coe_neg'` / 定理 `coe_neg'`

English:
theorem coe_neg'
  given: {x : Real}
  statement: (x : EReal) < 0 ↔ x < 0
  proof: EReal.coe_lt_coe_iff

中文:
定理 coe_neg'
  条件: {x : 实数}
  结论: (x : E实数) < 0 ↔ x < 0
  证明: EReal.coe_lt_coe_iff
-/
protected theorem coe_neg' {x : Real} : (x : EReal) < 0 ↔ x < 0 :=
  EReal.coe_lt_coe_iff

/--
lemma `toReal_eq_zero_iff` / 引理 `toReal_eq_zero_iff`

English:
lemma toReal_eq_zero_iff
  given: {x : EReal}
  statement: x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥
  proof: by
  cases x <;> norm_num

中文:
引理 toReal_eq_zero_iff
  条件: {x : E实数}
  结论: x.to实数 = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥
  证明: by
  cases x <;> norm_num
-/
lemma toReal_eq_zero_iff {x : EReal} : x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥ := by
  cases x <;> norm_num

/--
lemma `toReal_ne_zero_iff` / 引理 `toReal_ne_zero_iff`

English:
lemma toReal_ne_zero_iff
  given: {x : EReal}
  statement: x.toReal != 0 ↔ x != 0 ∧ x != ⊤ ∧ x != ⊥
  proof: by
  simp only [ne_eq, toReal_eq_zero_iff, not_or]

中文:
引理 toReal_ne_zero_iff
  条件: {x : E实数}
  结论: x.to实数 != 0 ↔ x != 0 ∧ x != ⊤ ∧ x != ⊥
  证明: by
  simp only [ne_eq, toReal_eq_zero_iff, not_or]

Depends on / 依赖: ne_eq, not_or, toReal_eq_zero_iff
-/
lemma toReal_ne_zero_iff {x : EReal} : x.toReal != 0 ↔ x != 0 ∧ x != ⊤ ∧ x != ⊥ := by
  simp only [ne_eq, toReal_eq_zero_iff, not_or]

/--
lemma `toReal_eq_toReal` / 引理 `toReal_eq_toReal`

English:
lemma toReal_eq_toReal
  statement: {x y : EReal} (hx_top : x != ⊤) (hx_bot : x != ⊥)
  proof: by
  lift x to Real using ⟨hx_top, hx_bot⟩
  lift y to Real using ⟨hy_top, hy_bot⟩
  simp

中文:
引理 toReal_eq_toReal
  结论: {x y : E实数} (hx_top : x != ⊤) (hx_bot : x != ⊥)
  证明: by
  lift x to Real using ⟨hx_top, hx_bot⟩
  lift y to Real using ⟨hy_top, hy_bot⟩
  simp

Depends on / 依赖: hx_bot, hx_top, hy_bot, hy_top
-/
lemma toReal_eq_toReal {x y : EReal} (hx_top : x != ⊤) (hx_bot : x != ⊥)
    (hy_top : y != ⊤) (hy_bot : y != ⊥) :
    x.toReal = y.toReal ↔ x = y := by
  lift x to Real using ⟨hx_top, hx_bot⟩
  lift y to Real using ⟨hy_top, hy_bot⟩
  simp

/--
lemma `toReal_nonneg` / 引理 `toReal_nonneg`

English:
lemma toReal_nonneg
  given: {x : EReal} (hx : 0 <= x)
  statement: 0 <= x.toReal
  proof: by
  cases x
  · simp
  · exact toReal_coe _ ▸ EReal.coe_nonneg.mp hx
  · simp

中文:
引理 toReal_nonneg
  条件: {x : E实数} (hx : 0 <= x)
  结论: 0 <= x.to实数
  证明: by
  cases x
  · simp
  · exact toReal_coe _ ▸ EReal.coe_nonneg.mp hx
  · simp

Depends on / 依赖: EReal.coe_nonneg.mp, coe_nonneg, toReal_coe
-/
lemma toReal_nonneg {x : EReal} (hx : 0 <= x) : 0 <= x.toReal := by
  cases x
  · simp
  · exact toReal_coe _ ▸ EReal.coe_nonneg.mp hx
  · simp

/--
lemma `toReal_nonpos` / 引理 `toReal_nonpos`

English:
lemma toReal_nonpos
  given: {x : EReal} (hx : x <= 0)
  statement: x.toReal <= 0
  proof: by
  cases x
  · simp
  · exact toReal_coe _ ▸ EReal.coe_nonpos.mp hx
  · simp

中文:
引理 toReal_nonpos
  条件: {x : E实数} (hx : x <= 0)
  结论: x.to实数 <= 0
  证明: by
  cases x
  · simp
  · exact toReal_coe _ ▸ EReal.coe_nonpos.mp hx
  · simp

Depends on / 依赖: EReal.coe_nonpos.mp, coe_nonpos, toReal_coe
-/
lemma toReal_nonpos {x : EReal} (hx : x <= 0) : x.toReal <= 0 := by
  cases x
  · simp
  · exact toReal_coe _ ▸ EReal.coe_nonpos.mp hx
  · simp

/--
lemma `toReal_pos` / 引理 `toReal_pos`

English:
lemma toReal_pos
  given: {x : EReal} (hx : 0 < x) (h'x : x != ⊤)
  statement: 0 < x.toReal
  proof: by
  lift x to Real using by aesop
  simpa using hx

中文:
引理 toReal_pos
  条件: {x : E实数} (hx : 0 < x) (h'x : x != ⊤)
  结论: 0 < x.to实数
  证明: by
  lift x to Real using by aesop
  simpa using hx
-/
lemma toReal_pos {x : EReal} (hx : 0 < x) (h'x : x != ⊤) : 0 < x.toReal := by
  lift x to Real using by aesop
  simpa using hx

/--
lemma `toReal_neg` / 引理 `toReal_neg`

English:
lemma toReal_neg
  given: {x : EReal} (hx : x < 0) (h'x : x != ⊥)
  statement: x.toReal < 0
  proof: by
  lift x to Real using by aesop
  simpa using hx

中文:
引理 toReal_neg
  条件: {x : E实数} (hx : x < 0) (h'x : x != ⊥)
  结论: x.to实数 < 0
  证明: by
  lift x to Real using by aesop
  simpa using hx
-/
lemma toReal_neg {x : EReal} (hx : x < 0) (h'x : x != ⊥) : x.toReal < 0 := by
  lift x to Real using by aesop
  simpa using hx

/--
lemma `toReal_image_Ioo_zero_top` / 引理 `toReal_image_Ioo_zero_top`

English:
lemma toReal_image_Ioo_zero_top
  statement: toReal '' (Ioo 0 ⊤) = Ioi 0
  proof: by
  ext x
  constructor
  · rintro ⟨y, ⟨hy0, _⟩, rfl⟩
    lift y to Real using by aesop
    simpa using hy0
  · intro hx
    use (x : EReal)
    simpa using hx

中文:
引理 toReal_image_Ioo_zero_top
  结论: to实数 '' (Ioo 0 ⊤) = Ioi 0
  证明: by
  ext x
  constructor
  · rintro ⟨y, ⟨hy0, _⟩, rfl⟩
    lift y to Real using by aesop
    simpa using hy0
  · intro hx
    use (x : EReal)
    simpa using hx
-/
@[simp] lemma toReal_image_Ioo_zero_top : toReal '' (Ioo 0 ⊤) = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy0, _⟩, rfl⟩
    lift y to Real using by aesop
    simpa using hy0
  · intro hx
    use (x : EReal)
    simpa using hx

/--
lemma `toReal_image_Ioo_bot_zero` / 引理 `toReal_image_Ioo_bot_zero`

English:
lemma toReal_image_Ioo_bot_zero
  statement: toReal '' (Ioo ⊥ 0) = Iio 0
  proof: by
  ext x
  constructor
  · rintro ⟨y, ⟨_, hy0⟩, rfl⟩
    lift y to Real using by aesop
    simpa using hy0
  · intro hx
    use (x : EReal)
    simpa using hx

中文:
引理 toReal_image_Ioo_bot_zero
  结论: to实数 '' (Ioo ⊥ 0) = Iio 0
  证明: by
  ext x
  constructor
  · rintro ⟨y, ⟨_, hy0⟩, rfl⟩
    lift y to Real using by aesop
    simpa using hy0
  · intro hx
    use (x : EReal)
    simpa using hx
-/
@[simp] lemma toReal_image_Ioo_bot_zero : toReal '' (Ioo ⊥ 0) = Iio 0 := by
  ext x
  constructor
  · rintro ⟨y, ⟨_, hy0⟩, rfl⟩
    lift y to Real using by aesop
    simpa using hy0
  · intro hx
    use (x : EReal)
    simpa using hx

/--
theorem `toReal_le_toReal` / 定理 `toReal_le_toReal`

English:
theorem toReal_le_toReal
  given: {x y : EReal} (h : x <= y) (hx : x != ⊥) (hy : y != ⊤)
  proof: by
  lift x to Real using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to Real using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h

中文:
定理 toReal_le_toReal
  条件: {x y : E实数} (h : x <= y) (hx : x != ⊥) (hy : y != ⊤)
  证明: by
  lift x to Real using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to Real using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h

Depends on / 依赖: ne_bot_of_le_ne_bot, ne_top_of_le_ne_top
-/
theorem toReal_le_toReal {x y : EReal} (h : x <= y) (hx : x != ⊥) (hy : y != ⊤) :
    x.toReal <= y.toReal := by
  lift x to Real using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to Real using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h

/--
theorem `coe_toReal` / 定理 `coe_toReal`

English:
theorem coe_toReal
  given: {x : EReal} (hx : x != ⊤) (h'x : x != ⊥)
  statement: (x.toReal : EReal) = x
  proof: by
  lift x to Real using ⟨hx, h'x⟩
  rfl

中文:
定理 coe_toReal
  条件: {x : E实数} (hx : x != ⊤) (h'x : x != ⊥)
  结论: (x.to实数 : E实数) = x
  证明: by
  lift x to Real using ⟨hx, h'x⟩
  rfl
-/
theorem coe_toReal {x : EReal} (hx : x != ⊤) (h'x : x != ⊥) : (x.toReal : EReal) = x := by
  lift x to Real using ⟨hx, h'x⟩
  rfl

/--
theorem `le_coe_toReal` / 定理 `le_coe_toReal`

English:
theorem le_coe_toReal
  given: {x : EReal} (h : x != ⊤)
  statement: x <= x.toReal
  proof: by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_toReal h h']

中文:
定理 le_coe_toReal
  条件: {x : E实数} (h : x != ⊤)
  结论: x <= x.to实数
  证明: by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_toReal h h']

Depends on / 依赖: bot_le, coe_toReal, le_refl
-/
theorem le_coe_toReal {x : EReal} (h : x != ⊤) : x <= x.toReal := by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_toReal h h']

/--
theorem `coe_toReal_le` / 定理 `coe_toReal_le`

English:
theorem coe_toReal_le
  given: {x : EReal} (h : x != ⊥)
  statement: ↑x.toReal <= x
  proof: by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_toReal h' h]

中文:
定理 coe_toReal_le
  条件: {x : E实数} (h : x != ⊥)
  结论: ↑x.to实数 <= x
  证明: by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_toReal h' h]

Depends on / 依赖: coe_toReal, le_refl, le_top
-/
theorem coe_toReal_le {x : EReal} (h : x != ⊥) : ↑x.toReal <= x := by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_toReal h' h]

/--
theorem `eq_top_iff_forall_lt` / 定理 `eq_top_iff_forall_lt`

English:
theorem eq_top_iff_forall_lt
  given: (x : EReal)
  statement: x = ⊤ ↔ forall y : Real, (y : EReal) < x
  proof: by
  constructor
  · rintro rfl
    exact EReal.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toReal, le_coe_toReal h⟩

中文:
定理 eq_top_iff_forall_lt
  条件: (x : E实数)
  结论: x = ⊤ ↔ 对任意 y : 实数, (y : E实数) < x
  证明: by
  constructor
  · rintro rfl
    exact EReal.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toReal, le_coe_toReal h⟩

Depends on / 依赖: EReal.coe_lt_top, coe_lt_top, contrapose, le_coe_toReal, toReal, x.toReal
-/
theorem eq_top_iff_forall_lt (x : EReal) : x = ⊤ ↔ forall y : Real, (y : EReal) < x := by
  constructor
  · rintro rfl
    exact EReal.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toReal, le_coe_toReal h⟩

/--
theorem `eq_bot_iff_forall_lt` / 定理 `eq_bot_iff_forall_lt`

English:
theorem eq_bot_iff_forall_lt
  given: (x : EReal)
  statement: x = ⊥ ↔ forall y : Real, x < (y : EReal)
  proof: by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toReal, coe_toReal_le h⟩

中文:
定理 eq_bot_iff_forall_lt
  条件: (x : E实数)
  结论: x = ⊥ ↔ 对任意 y : 实数, x < (y : E实数)
  证明: by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toReal, coe_toReal_le h⟩

Depends on / 依赖: bot_lt_coe, coe_toReal_le, contrapose, toReal, x.toReal
-/
theorem eq_bot_iff_forall_lt (x : EReal) : x = ⊥ ↔ forall y : Real, x < (y : EReal) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toReal, coe_toReal_le h⟩


/--
lemma `exists_between_coe_real` / 引理 `exists_between_coe_real`

English:
lemma exists_between_coe_real
  given: {x z : EReal} (h : x < z)
  statement: exists y : Real, x < y ∧ y < z
  proof: by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction a with
  | bot => exact (not_lt_bot ha₁).elim
  | coe a₀ => exact ⟨a₀, ha₁, ha₂⟩
  | top => exact (not_top_lt ha₂).elim

@[simp]

中文:
引理 exists_between_coe_real
  条件: {x z : E实数} (h : x < z)
  结论: 存在 y : 实数, x < y ∧ y < z
  证明: by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction a with
  | bot => exact (not_lt_bot ha₁).elim
  | coe a₀ => exact ⟨a₀, ha₁, ha₂⟩
  | top => exact (not_top_lt ha₂).elim

@[simp]

Depends on / 依赖: exists_between, not_lt_bot, not_top_lt
-/
lemma exists_between_coe_real {x z : EReal} (h : x < z) : exists y : Real, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction a with
  | bot => exact (not_lt_bot ha₁).elim
  | coe a₀ => exact ⟨a₀, ha₁, ha₂⟩
  | top => exact (not_top_lt ha₂).elim

@[simp]
/--
lemma `image_coe_Icc` / 引理 `image_coe_Icc`

English:
lemma image_coe_Icc
  given: (x y : Real)
  statement: Real.toEReal '' Icc x y = Icc ↑x ↑y
  proof: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Icc]; rw [WithBot.image_coe_Icc]
  rfl

@[simp]

中文:
引理 image_coe_Icc
  条件: (x y : 实数)
  结论: 实数.toE实数 '' Icc x y = Icc ↑x ↑y
  证明: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Icc]; rw [WithBot.image_coe_Icc]
  rfl

@[simp]

Depends on / 依赖: WithBot, WithBot.image_coe_Icc, WithBot.some, WithTop, WithTop.image_coe_Icc, WithTop.some, image_coe_Icc, image_comp
-/
lemma image_coe_Icc (x y : Real) : Real.toEReal '' Icc x y = Icc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Icc]; rw [WithBot.image_coe_Icc]
  rfl

@[simp]
/--
lemma `image_coe_Ico` / 引理 `image_coe_Ico`

English:
lemma image_coe_Ico
  given: (x y : Real)
  statement: Real.toEReal '' Ico x y = Ico ↑x ↑y
  proof: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ico]; rw [WithBot.image_coe_Ico]
  rfl

@[simp]

中文:
引理 image_coe_Ico
  条件: (x y : 实数)
  结论: 实数.toE实数 '' Ico x y = Ico ↑x ↑y
  证明: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ico]; rw [WithBot.image_coe_Ico]
  rfl

@[simp]

Depends on / 依赖: WithBot, WithBot.image_coe_Ico, WithBot.some, WithTop, WithTop.image_coe_Ico, WithTop.some, image_coe_Ico, image_comp
-/
lemma image_coe_Ico (x y : Real) : Real.toEReal '' Ico x y = Ico ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ico]; rw [WithBot.image_coe_Ico]
  rfl

@[simp]
/--
lemma `image_coe_Ici` / 引理 `image_coe_Ici`

English:
lemma image_coe_Ici
  given: (x : Real)
  statement: Real.toEReal '' Ici x = Ico ↑x ⊤
  proof: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ici]; rw [WithBot.image_coe_Ico]
  rfl

@[simp]

中文:
引理 image_coe_Ici
  条件: (x : 实数)
  结论: 实数.toE实数 '' Ici x = Ico ↑x ⊤
  证明: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ici]; rw [WithBot.image_coe_Ico]
  rfl

@[simp]

Depends on / 依赖: WithBot, WithBot.image_coe_Ico, WithBot.some, WithTop, WithTop.image_coe_Ici, WithTop.some, image_coe_Ici, image_coe_Ico, image_comp
-/
lemma image_coe_Ici (x : Real) : Real.toEReal '' Ici x = Ico ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ici]; rw [WithBot.image_coe_Ico]
  rfl

@[simp]
/--
lemma `image_coe_Ioc` / 引理 `image_coe_Ioc`

English:
lemma image_coe_Ioc
  given: (x y : Real)
  statement: Real.toEReal '' Ioc x y = Ioc ↑x ↑y
  proof: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioc]; rw [WithBot.image_coe_Ioc]
  rfl

@[simp]

中文:
引理 image_coe_Ioc
  条件: (x y : 实数)
  结论: 实数.toE实数 '' Ioc x y = Ioc ↑x ↑y
  证明: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioc]; rw [WithBot.image_coe_Ioc]
  rfl

@[simp]

Depends on / 依赖: WithBot, WithBot.image_coe_Ioc, WithBot.some, WithTop, WithTop.image_coe_Ioc, WithTop.some, image_coe_Ioc, image_comp
-/
lemma image_coe_Ioc (x y : Real) : Real.toEReal '' Ioc x y = Ioc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioc]; rw [WithBot.image_coe_Ioc]
  rfl

@[simp]
/--
lemma `image_coe_Ioo` / 引理 `image_coe_Ioo`

English:
lemma image_coe_Ioo
  given: (x y : Real)
  statement: Real.toEReal '' Ioo x y = Ioo ↑x ↑y
  proof: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioo]; rw [WithBot.image_coe_Ioo]
  rfl

@[simp]

中文:
引理 image_coe_Ioo
  条件: (x y : 实数)
  结论: 实数.toE实数 '' Ioo x y = Ioo ↑x ↑y
  证明: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioo]; rw [WithBot.image_coe_Ioo]
  rfl

@[simp]

Depends on / 依赖: WithBot, WithBot.image_coe_Ioo, WithBot.some, WithTop, WithTop.image_coe_Ioo, WithTop.some, image_coe_Ioo, image_comp
-/
lemma image_coe_Ioo (x y : Real) : Real.toEReal '' Ioo x y = Ioo ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioo]; rw [WithBot.image_coe_Ioo]
  rfl

@[simp]
/--
lemma `image_coe_Ioi` / 引理 `image_coe_Ioi`

English:
lemma image_coe_Ioi
  given: (x : Real)
  statement: Real.toEReal '' Ioi x = Ioo ↑x ⊤
  proof: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioi]; rw [WithBot.image_coe_Ioo]
  rfl

@[simp]

中文:
引理 image_coe_Ioi
  条件: (x : 实数)
  结论: 实数.toE实数 '' Ioi x = Ioo ↑x ⊤
  证明: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioi]; rw [WithBot.image_coe_Ioo]
  rfl

@[simp]

Depends on / 依赖: WithBot, WithBot.image_coe_Ioo, WithBot.some, WithTop, WithTop.image_coe_Ioi, WithTop.some, image_coe_Ioi, image_coe_Ioo, image_comp
-/
lemma image_coe_Ioi (x : Real) : Real.toEReal '' Ioi x = Ioo ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioi]; rw [WithBot.image_coe_Ioo]
  rfl

@[simp]
/--
lemma `image_coe_Iic` / 引理 `image_coe_Iic`

English:
lemma image_coe_Iic
  given: (x : Real)
  statement: Real.toEReal '' Iic x = Ioc ⊥ ↑x
  proof: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iic]; rw [WithBot.image_coe_Iic]
  rfl

@[simp]

中文:
引理 image_coe_Iic
  条件: (x : 实数)
  结论: 实数.toE实数 '' Iic x = Ioc ⊥ ↑x
  证明: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iic]; rw [WithBot.image_coe_Iic]
  rfl

@[simp]

Depends on / 依赖: WithBot, WithBot.image_coe_Iic, WithBot.some, WithTop, WithTop.image_coe_Iic, WithTop.some, image_coe_Iic, image_comp
-/
lemma image_coe_Iic (x : Real) : Real.toEReal '' Iic x = Ioc ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iic]; rw [WithBot.image_coe_Iic]
  rfl

@[simp]
/--
lemma `image_coe_Iio` / 引理 `image_coe_Iio`

English:
lemma image_coe_Iio
  given: (x : Real)
  statement: Real.toEReal '' Iio x = Ioo ⊥ ↑x
  proof: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iio]; rw [WithBot.image_coe_Iio]
  rfl

@[simp]

中文:
引理 image_coe_Iio
  条件: (x : 实数)
  结论: 实数.toE实数 '' Iio x = Ioo ⊥ ↑x
  证明: by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iio]; rw [WithBot.image_coe_Iio]
  rfl

@[simp]

Depends on / 依赖: WithBot, WithBot.image_coe_Iio, WithBot.some, WithTop, WithTop.image_coe_Iio, WithTop.some, image_coe_Iio, image_comp
-/
lemma image_coe_Iio (x : Real) : Real.toEReal '' Iio x = Ioo ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iio]; rw [WithBot.image_coe_Iio]
  rfl

@[simp]
/--
lemma `preimage_coe_Ici` / 引理 `preimage_coe_Ici`

English:
lemma preimage_coe_Ici
  given: (x : Real)
  statement: Real.toEReal ⁻¹' Ici x = Ici x
  proof: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ici (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ici, WithTop.preimage_coe_Ici]

@[simp]

中文:
引理 preimage_coe_Ici
  条件: (x : 实数)
  结论: 实数.toE实数 ⁻¹' Ici x = Ici x
  证明: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ici (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ici, WithTop.preimage_coe_Ici]

@[simp]

Depends on / 依赖: WithBot, WithBot.preimage_coe_Ici, WithBot.some, WithTop, WithTop.preimage_coe_Ici, WithTop.some, preimage_coe_Ici, preimage_comp, preimage_comp.trans
-/
lemma preimage_coe_Ici (x : Real) : Real.toEReal ⁻¹' Ici x = Ici x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ici (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ici, WithTop.preimage_coe_Ici]

@[simp]
/--
lemma `preimage_coe_Ioi` / 引理 `preimage_coe_Ioi`

English:
lemma preimage_coe_Ioi
  given: (x : Real)
  statement: Real.toEReal ⁻¹' Ioi x = Ioi x
  proof: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi, WithTop.preimage_coe_Ioi]

@[simp]

中文:
引理 preimage_coe_Ioi
  条件: (x : 实数)
  结论: 实数.toE实数 ⁻¹' Ioi x = Ioi x
  证明: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi, WithTop.preimage_coe_Ioi]

@[simp]

Depends on / 依赖: WithBot, WithBot.preimage_coe_Ioi, WithBot.some, WithTop, WithTop.preimage_coe_Ioi, WithTop.some, preimage_coe_Ioi, preimage_comp, preimage_comp.trans
-/
lemma preimage_coe_Ioi (x : Real) : Real.toEReal ⁻¹' Ioi x = Ioi x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi, WithTop.preimage_coe_Ioi]

@[simp]
/--
lemma `preimage_coe_Ioi_bot` / 引理 `preimage_coe_Ioi_bot`

English:
lemma preimage_coe_Ioi_bot
  statement: Real.toEReal ⁻¹' Ioi ⊥ = univ
  proof: by
  change ((WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (⊥ : WithBot (WithTop Real))) : Set Real) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi_bot, preimage_univ]

@[simp]

中文:
引理 preimage_coe_Ioi_bot
  结论: 实数.toE实数 ⁻¹' Ioi ⊥ = univ
  证明: by
  change ((WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (⊥ : WithBot (WithTop Real))) : Set Real) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi_bot, preimage_univ]

@[simp]

Depends on / 依赖: WithBot, WithBot.preimage_coe_Ioi_bot, WithBot.some, WithTop, WithTop.some, preimage_coe_Ioi_bot, preimage_comp, preimage_comp.trans, preimage_univ
-/
lemma preimage_coe_Ioi_bot : Real.toEReal ⁻¹' Ioi ⊥ = univ := by
  change ((WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (⊥ : WithBot (WithTop Real))) : Set Real) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi_bot, preimage_univ]

@[simp]
/--
lemma `preimage_coe_Iic` / 引理 `preimage_coe_Iic`

English:
lemma preimage_coe_Iic
  given: (y : Real)
  statement: Real.toEReal ⁻¹' Iic y = Iic y
  proof: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iic (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iic, WithTop.preimage_coe_Iic]

@[simp]

中文:
引理 preimage_coe_Iic
  条件: (y : 实数)
  结论: 实数.toE实数 ⁻¹' Iic y = Iic y
  证明: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iic (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iic, WithTop.preimage_coe_Iic]

@[simp]

Depends on / 依赖: WithBot, WithBot.preimage_coe_Iic, WithBot.some, WithTop, WithTop.preimage_coe_Iic, WithTop.some, preimage_coe_Iic, preimage_comp, preimage_comp.trans
-/
lemma preimage_coe_Iic (y : Real) : Real.toEReal ⁻¹' Iic y = Iic y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iic (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iic, WithTop.preimage_coe_Iic]

@[simp]
/--
lemma `preimage_coe_Iio` / 引理 `preimage_coe_Iio`

English:
lemma preimage_coe_Iio
  given: (y : Real)
  statement: Real.toEReal ⁻¹' Iio y = Iio y
  proof: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio]

@[simp]

中文:
引理 preimage_coe_Iio
  条件: (y : 实数)
  结论: 实数.toE实数 ⁻¹' Iio y = Iio y
  证明: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio]

@[simp]

Depends on / 依赖: WithBot, WithBot.preimage_coe_Iio, WithBot.some, WithTop, WithTop.preimage_coe_Iio, WithTop.some, preimage_coe_Iio, preimage_comp, preimage_comp.trans
-/
lemma preimage_coe_Iio (y : Real) : Real.toEReal ⁻¹' Iio y = Iio y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio]

@[simp]
/--
lemma `preimage_coe_Iio_top` / 引理 `preimage_coe_Iio_top`

English:
lemma preimage_coe_Iio_top
  statement: Real.toEReal ⁻¹' Iio ⊤ = univ
  proof: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (⊤ : WithTop Real))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio_top]

@[simp]

中文:
引理 preimage_coe_Iio_top
  结论: 实数.toE实数 ⁻¹' Iio ⊤ = univ
  证明: by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (⊤ : WithTop Real))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio_top]

@[simp]

Depends on / 依赖: WithBot, WithBot.preimage_coe_Iio, WithBot.some, WithTop, WithTop.preimage_coe_Iio_top, WithTop.some, preimage_coe_Iio, preimage_coe_Iio_top, preimage_comp, preimage_comp.trans
-/
lemma preimage_coe_Iio_top : Real.toEReal ⁻¹' Iio ⊤ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (⊤ : WithTop Real))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio_top]

@[simp]
/--
lemma `preimage_coe_Icc` / 引理 `preimage_coe_Icc`

English:
lemma preimage_coe_Icc
  given: (x y : Real)
  statement: Real.toEReal ⁻¹' Icc x y = Icc x y
  proof: by
  simp_rw [← Ici_inter_Iic]
  simp

@[simp]

中文:
引理 preimage_coe_Icc
  条件: (x y : 实数)
  结论: 实数.toE实数 ⁻¹' Icc x y = Icc x y
  证明: by
  simp_rw [← Ici_inter_Iic]
  simp

@[simp]

Depends on / 依赖: Ici_inter_Iic, simp_rw
-/
lemma preimage_coe_Icc (x y : Real) : Real.toEReal ⁻¹' Icc x y = Icc x y := by
  simp_rw [← Ici_inter_Iic]
  simp

@[simp]
/--
lemma `preimage_coe_Ico` / 引理 `preimage_coe_Ico`

English:
lemma preimage_coe_Ico
  given: (x y : Real)
  statement: Real.toEReal ⁻¹' Ico x y = Ico x y
  proof: by
  simp_rw [← Ici_inter_Iio]
  simp

@[simp]

中文:
引理 preimage_coe_Ico
  条件: (x y : 实数)
  结论: 实数.toE实数 ⁻¹' Ico x y = Ico x y
  证明: by
  simp_rw [← Ici_inter_Iio]
  simp

@[simp]

Depends on / 依赖: Ici_inter_Iio, simp_rw
-/
lemma preimage_coe_Ico (x y : Real) : Real.toEReal ⁻¹' Ico x y = Ico x y := by
  simp_rw [← Ici_inter_Iio]
  simp

@[simp]
/--
lemma `preimage_coe_Ioc` / 引理 `preimage_coe_Ioc`

English:
lemma preimage_coe_Ioc
  given: (x y : Real)
  statement: Real.toEReal ⁻¹' Ioc x y = Ioc x y
  proof: by
  simp_rw [← Ioi_inter_Iic]
  simp

@[simp]

中文:
引理 preimage_coe_Ioc
  条件: (x y : 实数)
  结论: 实数.toE实数 ⁻¹' Ioc x y = Ioc x y
  证明: by
  simp_rw [← Ioi_inter_Iic]
  simp

@[simp]

Depends on / 依赖: Ioi_inter_Iic, simp_rw
-/
lemma preimage_coe_Ioc (x y : Real) : Real.toEReal ⁻¹' Ioc x y = Ioc x y := by
  simp_rw [← Ioi_inter_Iic]
  simp

@[simp]
/--
lemma `preimage_coe_Ioo` / 引理 `preimage_coe_Ioo`

English:
lemma preimage_coe_Ioo
  given: (x y : Real)
  statement: Real.toEReal ⁻¹' Ioo x y = Ioo x y
  proof: by
  simp_rw [← Ioi_inter_Iio]
  simp

@[simp]

中文:
引理 preimage_coe_Ioo
  条件: (x y : 实数)
  结论: 实数.toE实数 ⁻¹' Ioo x y = Ioo x y
  证明: by
  simp_rw [← Ioi_inter_Iio]
  simp

@[simp]

Depends on / 依赖: Ioi_inter_Iio, simp_rw
-/
lemma preimage_coe_Ioo (x y : Real) : Real.toEReal ⁻¹' Ioo x y = Ioo x y := by
  simp_rw [← Ioi_inter_Iio]
  simp

@[simp]
/--
lemma `preimage_coe_Ico_top` / 引理 `preimage_coe_Ico_top`

English:
lemma preimage_coe_Ico_top
  given: (x : Real)
  statement: Real.toEReal ⁻¹' Ico x ⊤ = Ici x
  proof: by
  rw [← Ici_inter_Iio]
  simp

@[simp]

中文:
引理 preimage_coe_Ico_top
  条件: (x : 实数)
  结论: 实数.toE实数 ⁻¹' Ico x ⊤ = Ici x
  证明: by
  rw [← Ici_inter_Iio]
  simp

@[simp]

Depends on / 依赖: Ici_inter_Iio
-/
lemma preimage_coe_Ico_top (x : Real) : Real.toEReal ⁻¹' Ico x ⊤ = Ici x := by
  rw [← Ici_inter_Iio]
  simp

@[simp]
/--
lemma `preimage_coe_Ioo_top` / 引理 `preimage_coe_Ioo_top`

English:
lemma preimage_coe_Ioo_top
  given: (x : Real)
  statement: Real.toEReal ⁻¹' Ioo x ⊤ = Ioi x
  proof: by
  rw [← Ioi_inter_Iio]
  simp

@[simp]

中文:
引理 preimage_coe_Ioo_top
  条件: (x : 实数)
  结论: 实数.toE实数 ⁻¹' Ioo x ⊤ = Ioi x
  证明: by
  rw [← Ioi_inter_Iio]
  simp

@[simp]

Depends on / 依赖: Ioi_inter_Iio
-/
lemma preimage_coe_Ioo_top (x : Real) : Real.toEReal ⁻¹' Ioo x ⊤ = Ioi x := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
/--
lemma `preimage_coe_Ioc_bot` / 引理 `preimage_coe_Ioc_bot`

English:
lemma preimage_coe_Ioc_bot
  given: (y : Real)
  statement: Real.toEReal ⁻¹' Ioc ⊥ y = Iic y
  proof: by
  rw [← Ioi_inter_Iic]
  simp

@[simp]

中文:
引理 preimage_coe_Ioc_bot
  条件: (y : 实数)
  结论: 实数.toE实数 ⁻¹' Ioc ⊥ y = Iic y
  证明: by
  rw [← Ioi_inter_Iic]
  simp

@[simp]

Depends on / 依赖: Ioi_inter_Iic
-/
lemma preimage_coe_Ioc_bot (y : Real) : Real.toEReal ⁻¹' Ioc ⊥ y = Iic y := by
  rw [← Ioi_inter_Iic]
  simp

@[simp]
/--
lemma `preimage_coe_Ioo_bot` / 引理 `preimage_coe_Ioo_bot`

English:
lemma preimage_coe_Ioo_bot
  given: (y : Real)
  statement: Real.toEReal ⁻¹' Ioo ⊥ y = Iio y
  proof: by
  rw [← Ioi_inter_Iio]
  simp

@[simp]

中文:
引理 preimage_coe_Ioo_bot
  条件: (y : 实数)
  结论: 实数.toE实数 ⁻¹' Ioo ⊥ y = Iio y
  证明: by
  rw [← Ioi_inter_Iio]
  simp

@[simp]

Depends on / 依赖: Ioi_inter_Iio
-/
lemma preimage_coe_Ioo_bot (y : Real) : Real.toEReal ⁻¹' Ioo ⊥ y = Iio y := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
/--
lemma `preimage_coe_Ioo_bot_top` / 引理 `preimage_coe_Ioo_bot_top`

English:
lemma preimage_coe_Ioo_bot_top
  statement: Real.toEReal ⁻¹' Ioo ⊥ ⊤ = univ
  proof: by
  rw [← Ioi_inter_Iio]
  simp

中文:
引理 preimage_coe_Ioo_bot_top
  结论: 实数.toE实数 ⁻¹' Ioo ⊥ ⊤ = univ
  证明: by
  rw [← Ioi_inter_Iio]
  simp

Depends on / 依赖: Ioi_inter_Iio
-/
lemma preimage_coe_Ioo_bot_top : Real.toEReal ⁻¹' Ioo ⊥ ⊤ = univ := by
  rw [← Ioi_inter_Iio]
  simp

/-! ### ennreal coercion -/

@[simp]
/--
theorem `toReal_coe_ennreal` / 定理 `toReal_coe_ennreal`

English:
theorem toReal_coe_ennreal
  statement: forall {x : Real>=0∞}, toReal (x : EReal) = ENNReal.toReal x

中文:
定理 toReal_coe_ennreal
  结论: 对任意 {x : 实数>=0∞}, to实数 (x : E实数) = ENN实数.to实数 x
-/
theorem toReal_coe_ennreal : forall {x : Real>=0∞}, toReal (x : EReal) = ENNReal.toReal x
  | ⊤ => rfl
  | .some _ => rfl

@[simp]
/--
theorem `coe_ennreal_ofReal` / 定理 `coe_ennreal_ofReal`

English:
theorem coe_ennreal_ofReal
  given: {x : Real}
  statement: (ENNReal.ofReal x : EReal) = max x 0
  proof: rfl

中文:
定理 coe_ennreal_ofReal
  条件: {x : 实数}
  结论: (ENN实数.of实数 x : E实数) = max x 0
  证明: rfl
-/
theorem coe_ennreal_ofReal {x : Real} : (ENNReal.ofReal x : EReal) = max x 0 :=
  rfl

/--
lemma `coe_ennreal_toReal` / 引理 `coe_ennreal_toReal`

English:
lemma coe_ennreal_toReal
  given: {x : Real>=0∞} (hx : x != ∞)
  statement: (x.toReal : EReal) = x
  proof: by
  lift x to Real>=0 using hx
  rfl

中文:
引理 coe_ennreal_toReal
  条件: {x : 实数>=0∞} (hx : x != ∞)
  结论: (x.to实数 : E实数) = x
  证明: by
  lift x to Real>=0 using hx
  rfl
-/
lemma coe_ennreal_toReal {x : Real>=0∞} (hx : x != ∞) : (x.toReal : EReal) = x := by
  lift x to Real>=0 using hx
  rfl

/--
theorem `coe_nnreal_eq_coe_real` / 定理 `coe_nnreal_eq_coe_real`

English:
theorem coe_nnreal_eq_coe_real
  given: (x : Real>=0)
  statement: ((x : Real>=0∞) : EReal) = (x : Real)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_nnreal_eq_coe_real
  条件: (x : 实数>=0)
  结论: ((x : 实数>=0∞) : E实数) = (x : 实数)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_nnreal_eq_coe_real (x : Real>=0) : ((x : Real>=0∞) : EReal) = (x : Real) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_ennreal_zero` / 定理 `coe_ennreal_zero`

English:
theorem coe_ennreal_zero
  statement: ((0 : Real>=0∞) : EReal) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_ennreal_zero
  结论: ((0 : 实数>=0∞) : E实数) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_ennreal_zero : ((0 : Real>=0∞) : EReal) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_ennreal_one` / 定理 `coe_ennreal_one`

English:
theorem coe_ennreal_one
  statement: ((1 : Real>=0∞) : EReal) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_ennreal_one
  结论: ((1 : 实数>=0∞) : E实数) = 1
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_ennreal_one : ((1 : Real>=0∞) : EReal) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_ennreal_top` / 定理 `coe_ennreal_top`

English:
theorem coe_ennreal_top
  statement: ((⊤ : Real>=0∞) : EReal) = ⊤
  proof: rfl

中文:
定理 coe_ennreal_top
  结论: ((⊤ : 实数>=0∞) : E实数) = ⊤
  证明: rfl
-/
theorem coe_ennreal_top : ((⊤ : Real>=0∞) : EReal) = ⊤ :=
  rfl

/--
theorem `coe_ennreal_strictMono` / 定理 `coe_ennreal_strictMono`

English:
theorem coe_ennreal_strictMono
  statement: StrictMono ((↑) : Real>=0∞ -> EReal)
  proof: WithTop.strictMono_iff.2 ⟨fun _ _ => EReal.coe_lt_coe_iff.2, fun _ => coe_lt_top _⟩

中文:
定理 coe_ennreal_strictMono
  结论: StrictMono ((↑) : 实数>=0∞ -> E实数)
  证明: WithTop.strictMono_iff.2 ⟨fun _ _ => EReal.coe_lt_coe_iff.2, fun _ => coe_lt_top _⟩

Depends on / 依赖: EReal.coe_lt_coe_iff, WithTop, WithTop.strictMono_iff, coe_lt_coe_iff, coe_lt_top, strictMono_iff
-/
theorem coe_ennreal_strictMono : StrictMono ((↑) : Real>=0∞ -> EReal) :=
  WithTop.strictMono_iff.2 ⟨fun _ _ => EReal.coe_lt_coe_iff.2, fun _ => coe_lt_top _⟩

/--
theorem `coe_ennreal_injective` / 定理 `coe_ennreal_injective`

English:
theorem coe_ennreal_injective
  statement: Injective ((↑) : Real>=0∞ -> EReal)
  proof: coe_ennreal_strictMono.injective

@[simp]

中文:
定理 coe_ennreal_injective
  结论: Injective ((↑) : 实数>=0∞ -> E实数)
  证明: coe_ennreal_strictMono.injective

@[simp]

Depends on / 依赖: coe_ennreal_strictMono, coe_ennreal_strictMono.injective, injective
-/
theorem coe_ennreal_injective : Injective ((↑) : Real>=0∞ -> EReal) :=
  coe_ennreal_strictMono.injective

@[simp]
/--
theorem `coe_ennreal_eq_top_iff` / 定理 `coe_ennreal_eq_top_iff`

English:
theorem coe_ennreal_eq_top_iff
  given: {x : Real>=0∞}
  statement: (x : EReal) = ⊤ ↔ x = ⊤
  proof: coe_ennreal_injective.eq_iff' rfl

中文:
定理 coe_ennreal_eq_top_iff
  条件: {x : 实数>=0∞}
  结论: (x : E实数) = ⊤ ↔ x = ⊤
  证明: coe_ennreal_injective.eq_iff' rfl

Depends on / 依赖: coe_ennreal_injective, coe_ennreal_injective.eq_iff, eq_iff
-/
theorem coe_ennreal_eq_top_iff {x : Real>=0∞} : (x : EReal) = ⊤ ↔ x = ⊤ :=
  coe_ennreal_injective.eq_iff' rfl

/--
theorem `coe_nnreal_ne_top` / 定理 `coe_nnreal_ne_top`

English:
theorem coe_nnreal_ne_top
  given: (x : Real>=0)
  statement: ((x : Real>=0∞) : EReal) != ⊤
  proof: coe_ne_top x

@[simp]

中文:
定理 coe_nnreal_ne_top
  条件: (x : 实数>=0)
  结论: ((x : 实数>=0∞) : E实数) != ⊤
  证明: coe_ne_top x

@[simp]

Depends on / 依赖: IsStablyFiniteRing, NonAssocSemiring, coe_ne_top
-/
theorem coe_nnreal_ne_top (x : Real>=0) : ((x : Real>=0∞) : EReal) != ⊤ := coe_ne_top x

@[simp]
/--
theorem `coe_nnreal_lt_top` / 定理 `coe_nnreal_lt_top`

English:
theorem coe_nnreal_lt_top
  given: (x : Real>=0)
  statement: ((x : Real>=0∞) : EReal) < ⊤
  proof: coe_lt_top x

@[simp, norm_cast]

中文:
定理 coe_nnreal_lt_top
  条件: (x : 实数>=0)
  结论: ((x : 实数>=0∞) : E实数) < ⊤
  证明: coe_lt_top x

@[simp, norm_cast]

Depends on / 依赖: coe_lt_top
-/
theorem coe_nnreal_lt_top (x : Real>=0) : ((x : Real>=0∞) : EReal) < ⊤ := coe_lt_top x

@[simp, norm_cast]
/--
theorem `coe_ennreal_le_coe_ennreal_iff` / 定理 `coe_ennreal_le_coe_ennreal_iff`

English:
theorem coe_ennreal_le_coe_ennreal_iff
  given: {x y : Real>=0∞}
  statement: (x : EReal) <= (y : EReal) ↔ x <= y
  proof: coe_ennreal_strictMono.le_iff_le

@[simp, norm_cast]

中文:
定理 coe_ennreal_le_coe_ennreal_iff
  条件: {x y : 实数>=0∞}
  结论: (x : E实数) <= (y : E实数) ↔ x <= y
  证明: coe_ennreal_strictMono.le_iff_le

@[simp, norm_cast]

Depends on / 依赖: coe_ennreal_strictMono, coe_ennreal_strictMono.le_iff_le, le_iff_le
-/
theorem coe_ennreal_le_coe_ennreal_iff {x y : Real>=0∞} : (x : EReal) <= (y : EReal) ↔ x <= y :=
  coe_ennreal_strictMono.le_iff_le

@[simp, norm_cast]
/--
theorem `coe_ennreal_lt_coe_ennreal_iff` / 定理 `coe_ennreal_lt_coe_ennreal_iff`

English:
theorem coe_ennreal_lt_coe_ennreal_iff
  given: {x y : Real>=0∞}
  statement: (x : EReal) < (y : EReal) ↔ x < y
  proof: coe_ennreal_strictMono.lt_iff_lt

@[simp, norm_cast]

中文:
定理 coe_ennreal_lt_coe_ennreal_iff
  条件: {x y : 实数>=0∞}
  结论: (x : E实数) < (y : E实数) ↔ x < y
  证明: coe_ennreal_strictMono.lt_iff_lt

@[simp, norm_cast]

Depends on / 依赖: IsStablyFiniteRing, SetLike, SubsemiringClass, coe_ennreal_strictMono, coe_ennreal_strictMono.lt_iff_lt, lt_iff_lt
-/
theorem coe_ennreal_lt_coe_ennreal_iff {x y : Real>=0∞} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_ennreal_strictMono.lt_iff_lt

@[simp, norm_cast]
/--
theorem `coe_ennreal_eq_coe_ennreal_iff` / 定理 `coe_ennreal_eq_coe_ennreal_iff`

English:
theorem coe_ennreal_eq_coe_ennreal_iff
  given: {x y : Real>=0∞}
  statement: (x : EReal) = (y : EReal) ↔ x = y
  proof: coe_ennreal_injective.eq_iff

中文:
定理 coe_ennreal_eq_coe_ennreal_iff
  条件: {x y : 实数>=0∞}
  结论: (x : E实数) = (y : E实数) ↔ x = y
  证明: coe_ennreal_injective.eq_iff

Depends on / 依赖: coe_ennreal_injective, coe_ennreal_injective.eq_iff, eq_iff
-/
theorem coe_ennreal_eq_coe_ennreal_iff {x y : Real>=0∞} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_ennreal_injective.eq_iff

/--
theorem `coe_ennreal_ne_coe_ennreal_iff` / 定理 `coe_ennreal_ne_coe_ennreal_iff`

English:
theorem coe_ennreal_ne_coe_ennreal_iff
  given: {x y : Real>=0∞}
  statement: (x : EReal) != (y : EReal) ↔ x != y
  proof: coe_ennreal_injective.ne_iff

@[simp, norm_cast]

中文:
定理 coe_ennreal_ne_coe_ennreal_iff
  条件: {x y : 实数>=0∞}
  结论: (x : E实数) != (y : E实数) ↔ x != y
  证明: coe_ennreal_injective.ne_iff

@[simp, norm_cast]

Depends on / 依赖: coe_ennreal_injective, coe_ennreal_injective.ne_iff, ne_iff
-/
theorem coe_ennreal_ne_coe_ennreal_iff {x y : Real>=0∞} : (x : EReal) != (y : EReal) ↔ x != y :=
  coe_ennreal_injective.ne_iff

@[simp, norm_cast]
/--
theorem `coe_ennreal_eq_zero` / 定理 `coe_ennreal_eq_zero`

English:
theorem coe_ennreal_eq_zero
  given: {x : Real>=0∞}
  statement: (x : EReal) = 0 ↔ x = 0
  proof: by
  rw [← coe_ennreal_eq_coe_ennreal_iff]; rw [coe_ennreal_zero]

@[simp, norm_cast]

中文:
定理 coe_ennreal_eq_zero
  条件: {x : 实数>=0∞}
  结论: (x : E实数) = 0 ↔ x = 0
  证明: by
  rw [← coe_ennreal_eq_coe_ennreal_iff]; rw [coe_ennreal_zero]

@[simp, norm_cast]

Depends on / 依赖: coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_zero
-/
theorem coe_ennreal_eq_zero {x : Real>=0∞} : (x : EReal) = 0 ↔ x = 0 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff]; rw [coe_ennreal_zero]

@[simp, norm_cast]
/--
theorem `coe_ennreal_eq_one` / 定理 `coe_ennreal_eq_one`

English:
theorem coe_ennreal_eq_one
  given: {x : Real>=0∞}
  statement: (x : EReal) = 1 ↔ x = 1
  proof: by
  rw [← coe_ennreal_eq_coe_ennreal_iff]; rw [coe_ennreal_one]

@[norm_cast]

中文:
定理 coe_ennreal_eq_one
  条件: {x : 实数>=0∞}
  结论: (x : E实数) = 1 ↔ x = 1
  证明: by
  rw [← coe_ennreal_eq_coe_ennreal_iff]; rw [coe_ennreal_one]

@[norm_cast]

Depends on / 依赖: coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_one
-/
theorem coe_ennreal_eq_one {x : Real>=0∞} : (x : EReal) = 1 ↔ x = 1 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff]; rw [coe_ennreal_one]

@[norm_cast]
/--
theorem `coe_ennreal_ne_zero` / 定理 `coe_ennreal_ne_zero`

English:
theorem coe_ennreal_ne_zero
  given: {x : Real>=0∞}
  statement: (x : EReal) != 0 ↔ x != 0
  proof: coe_ennreal_eq_zero.not

@[norm_cast]

中文:
定理 coe_ennreal_ne_zero
  条件: {x : 实数>=0∞}
  结论: (x : E实数) != 0 ↔ x != 0
  证明: coe_ennreal_eq_zero.not

@[norm_cast]

Depends on / 依赖: coe_ennreal_eq_zero, coe_ennreal_eq_zero.not
-/
theorem coe_ennreal_ne_zero {x : Real>=0∞} : (x : EReal) != 0 ↔ x != 0 :=
  coe_ennreal_eq_zero.not

@[norm_cast]
/--
theorem `coe_ennreal_ne_one` / 定理 `coe_ennreal_ne_one`

English:
theorem coe_ennreal_ne_one
  given: {x : Real>=0∞}
  statement: (x : EReal) != 1 ↔ x != 1
  proof: coe_ennreal_eq_one.not

中文:
定理 coe_ennreal_ne_one
  条件: {x : 实数>=0∞}
  结论: (x : E实数) != 1 ↔ x != 1
  证明: coe_ennreal_eq_one.not

Depends on / 依赖: coe_ennreal_eq_one, coe_ennreal_eq_one.not
-/
theorem coe_ennreal_ne_one {x : Real>=0∞} : (x : EReal) != 1 ↔ x != 1 :=
  coe_ennreal_eq_one.not

/--
theorem `coe_ennreal_nonneg` / 定理 `coe_ennreal_nonneg`

English:
theorem coe_ennreal_nonneg
  given: (x : Real>=0∞)
  statement: (0 : EReal) <= x
  proof: coe_ennreal_le_coe_ennreal_iff.2 zero_le

中文:
定理 coe_ennreal_nonneg
  条件: (x : 实数>=0∞)
  结论: (0 : E实数) <= x
  证明: coe_ennreal_le_coe_ennreal_iff.2 zero_le

Depends on / 依赖: coe_ennreal_le_coe_ennreal_iff, zero_le
-/
theorem coe_ennreal_nonneg (x : Real>=0∞) : (0 : EReal) <= x :=
  coe_ennreal_le_coe_ennreal_iff.2 zero_le

/--
theorem `range_coe_ennreal` / 定理 `range_coe_ennreal`

English:
theorem range_coe_ennreal
  statement: range ((↑) : Real>=0∞ -> EReal) = Set.Ici 0
  proof: Subset.antisymm (range_subset_iff.2 coe_ennreal_nonneg) fun x => match x with
    | ⊥ => fun h => absurd h bot_lt_zero.not_ge
    | ⊤ => fun _ => ⟨⊤, rfl⟩
    | (x : Real) => fun h => ⟨.some ⟨x, EReal.coe_nonneg.1 h⟩, rfl⟩

中文:
定理 range_coe_ennreal
  结论: range ((↑) : 实数>=0∞ -> E实数) = Set.Ici 0
  证明: Subset.antisymm (range_subset_iff.2 coe_ennreal_nonneg) fun x => match x with
    | ⊥ => fun h => absurd h bot_lt_zero.not_ge
    | ⊤ => fun _ => ⟨⊤, rfl⟩
    | (x : Real) => fun h => ⟨.some ⟨x, EReal.coe_nonneg.1 h⟩, rfl⟩
-/
@[simp] theorem range_coe_ennreal : range ((↑) : Real>=0∞ -> EReal) = Set.Ici 0 :=
  Subset.antisymm (range_subset_iff.2 coe_ennreal_nonneg) fun x => match x with
    | ⊥ => fun h => absurd h bot_lt_zero.not_ge
    | ⊤ => fun _ => ⟨⊤, rfl⟩
    | (x : Real) => fun h => ⟨.some ⟨x, EReal.coe_nonneg.1 h⟩, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift EReal Real>=0∞ (↑) (0 <= ·)
  body: ⟨range_coe_ennreal.ge⟩

@[simp, norm_cast]

中文:
实例 :
  签名: CanLift E实数 实数>=0∞ (↑) (0 <= ·)
  定义体: ⟨range_coe_ennreal.ge⟩

@[simp, norm_cast]

Depends on / 依赖: range_coe_ennreal, range_coe_ennreal.ge
-/
instance : CanLift EReal Real>=0∞ (↑) (0 <= ·) := ⟨range_coe_ennreal.ge⟩

@[simp, norm_cast]
/--
theorem `coe_ennreal_pos` / 定理 `coe_ennreal_pos`

English:
theorem coe_ennreal_pos
  given: {x : Real>=0∞}
  statement: (0 : EReal) < x ↔ 0 < x
  proof: by
  rw [← coe_ennreal_zero]; rw [coe_ennreal_lt_coe_ennreal_iff]

中文:
定理 coe_ennreal_pos
  条件: {x : 实数>=0∞}
  结论: (0 : E实数) < x ↔ 0 < x
  证明: by
  rw [← coe_ennreal_zero]; rw [coe_ennreal_lt_coe_ennreal_iff]

Depends on / 依赖: coe_ennreal_lt_coe_ennreal_iff, coe_ennreal_zero
-/
theorem coe_ennreal_pos {x : Real>=0∞} : (0 : EReal) < x ↔ 0 < x := by
  rw [← coe_ennreal_zero]; rw [coe_ennreal_lt_coe_ennreal_iff]

/--
theorem `coe_ennreal_pos_iff_ne_zero` / 定理 `coe_ennreal_pos_iff_ne_zero`

English:
theorem coe_ennreal_pos_iff_ne_zero
  given: {x : Real>=0∞}
  statement: (0 : EReal) < x ↔ x != 0
  proof: by
  rw [coe_ennreal_pos]; rw [pos_iff_ne_zero]

@[simp]

中文:
定理 coe_ennreal_pos_iff_ne_zero
  条件: {x : 实数>=0∞}
  结论: (0 : E实数) < x ↔ x != 0
  证明: by
  rw [coe_ennreal_pos]; rw [pos_iff_ne_zero]

@[simp]

Depends on / 依赖: coe_ennreal_pos, pos_iff_ne_zero
-/
theorem coe_ennreal_pos_iff_ne_zero {x : Real>=0∞} : (0 : EReal) < x ↔ x != 0 := by
  rw [coe_ennreal_pos]; rw [pos_iff_ne_zero]

@[simp]
/--
theorem `bot_lt_coe_ennreal` / 定理 `bot_lt_coe_ennreal`

English:
theorem bot_lt_coe_ennreal
  given: (x : Real>=0∞)
  statement: (⊥ : EReal) < x
  proof: (bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)

@[simp]

中文:
定理 bot_lt_coe_ennreal
  条件: (x : 实数>=0∞)
  结论: (⊥ : E实数) < x
  证明: (bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)

@[simp]

Depends on / 依赖: bot_lt_coe, coe_ennreal_nonneg, trans_le
-/
theorem bot_lt_coe_ennreal (x : Real>=0∞) : (⊥ : EReal) < x :=
  (bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)

@[simp]
/--
theorem `coe_ennreal_ne_bot` / 定理 `coe_ennreal_ne_bot`

English:
theorem coe_ennreal_ne_bot
  given: (x : Real>=0∞)
  statement: (x : EReal) != ⊥
  proof: (bot_lt_coe_ennreal x).ne'

@[simp, norm_cast]

中文:
定理 coe_ennreal_ne_bot
  条件: (x : 实数>=0∞)
  结论: (x : E实数) != ⊥
  证明: (bot_lt_coe_ennreal x).ne'

@[simp, norm_cast]

Depends on / 依赖: bot_lt_coe_ennreal
-/
theorem coe_ennreal_ne_bot (x : Real>=0∞) : (x : EReal) != ⊥ :=
  (bot_lt_coe_ennreal x).ne'

@[simp, norm_cast]
/--
theorem `coe_ennreal_add` / 定理 `coe_ennreal_add`

English:
theorem coe_ennreal_add
  given: (x y : ENNReal)
  statement: ((x + y : Real>=0∞) : EReal) = x + y
  proof: by
  cases x <;> cases y <;> rfl

中文:
定理 coe_ennreal_add
  条件: (x y : ENN实数)
  结论: ((x + y : 实数>=0∞) : E实数) = x + y
  证明: by
  cases x <;> cases y <;> rfl
-/
theorem coe_ennreal_add (x y : ENNReal) : ((x + y : Real>=0∞) : EReal) = x + y := by
  cases x <;> cases y <;> rfl

/--
theorem `coe_ennreal_top_mul` / 定理 `coe_ennreal_top_mul`

English:
theorem coe_ennreal_top_mul
  given: (x : Real>=0)
  statement: ((⊤ * x : Real>=0∞) : EReal) = ⊤ * x
  proof: by
  rcases eq_or_ne x 0 with (rfl | h0)
  · simp
  · rw [ENNReal.top_mul (ENNReal.coe_ne_zero.2 h0)]
exact Eq.symm if_pos NNReal.coe_pos.2 h0.bot_lt

@[simp, norm_cast]

中文:
定理 coe_ennreal_top_mul
  条件: (x : 实数>=0)
  结论: ((⊤ * x : 实数>=0∞) : E实数) = ⊤ * x
  证明: by
  rcases eq_or_ne x 0 with (rfl | h0)
  · simp
  · rw [ENNReal.top_mul (ENNReal.coe_ne_zero.2 h0)]
exact Eq.symm if_pos NNReal.coe_pos.2 h0.bot_lt

@[simp, norm_cast]
-/
private theorem coe_ennreal_top_mul (x : Real>=0) : ((⊤ * x : Real>=0∞) : EReal) = ⊤ * x := by
  rcases eq_or_ne x 0 with (rfl | h0)
  · simp
  · rw [ENNReal.top_mul (ENNReal.coe_ne_zero.2 h0)]
exact Eq.symm if_pos NNReal.coe_pos.2 h0.bot_lt

@[simp, norm_cast]
/--
theorem `coe_ennreal_mul` / 定理 `coe_ennreal_mul`

English:
theorem coe_ennreal_mul
  statement: forall x y : Real>=0∞, ((x * y : Real>=0∞) : EReal) = (x : EReal) * y

中文:
定理 coe_ennreal_mul
  结论: 对任意 x y : 实数>=0∞, ((x * y : 实数>=0∞) : E实数) = (x : E实数) * y
-/
theorem coe_ennreal_mul : forall x y : Real>=0∞, ((x * y : Real>=0∞) : EReal) = (x : EReal) * y
  | ⊤, ⊤ => rfl
  | ⊤, (y : Real>=0) => coe_ennreal_top_mul y
  | (x : Real>=0), ⊤ => by
    rw [mul_comm]; rw [coe_ennreal_top_mul]; rw [EReal.mul_comm]; rw [coe_ennreal_top]
  | (x : Real>=0), (y : Real>=0) => by
    simp only [← ENNReal.coe_mul, coe_nnreal_eq_coe_real, NNReal.coe_mul, EReal.coe_mul]

@[norm_cast]
/--
theorem `coe_ennreal_nsmul` / 定理 `coe_ennreal_nsmul`

English:
theorem coe_ennreal_nsmul
  given: (n : Nat) (x : Real>=0∞)
  statement: (↑(n • x) : EReal) = n • (x : EReal)
  proof: map_nsmul (⟨⟨(↑), coe_ennreal_zero⟩, coe_ennreal_add⟩ : Real>=0∞ ->+ EReal) _ _

中文:
定理 coe_ennreal_nsmul
  条件: (n : 自然数) (x : 实数>=0∞)
  结论: (↑(n • x) : E实数) = n • (x : E实数)
  证明: map_nsmul (⟨⟨(↑), coe_ennreal_zero⟩, coe_ennreal_add⟩ : Real>=0∞ ->+ EReal) _ _

Depends on / 依赖: coe_ennreal_add, coe_ennreal_zero, map_nsmul
-/
theorem coe_ennreal_nsmul (n : Nat) (x : Real>=0∞) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_nsmul (⟨⟨(↑), coe_ennreal_zero⟩, coe_ennreal_add⟩ : Real>=0∞ ->+ EReal) _ _

/-! ### toENNReal -/

/--
Definition of `toENNReal` / `toENNReal` 的定义

English:
definition toENNReal
  signature: (x : EReal)
  body: if x = ⊤ then ⊤
  else ENNReal.ofReal x.toReal

中文:
定义 toENNReal
  签名: (x : E实数)
  定义体: if x = ⊤ then ⊤
  else ENNReal.ofReal x.toReal

Depends on / 依赖: ENNReal, ENNReal.ofReal, ofReal, toReal, x.toReal
-/
noncomputable def toENNReal (x : EReal) : Real>=0∞ :=
  if x = ⊤ then ⊤
  else ENNReal.ofReal x.toReal

/--
lemma `toENNReal_top` / 引理 `toENNReal_top`

English:
lemma toENNReal_top
  statement: (⊤ : EReal).toENNReal = ⊤
  proof: rfl

@[simp]

中文:
引理 toENNReal_top
  结论: (⊤ : E实数).toENN实数 = ⊤
  证明: rfl

@[simp]
-/
@[simp] lemma toENNReal_top : (⊤ : EReal).toENNReal = ⊤ := rfl

@[simp]
/--
lemma `toENNReal_of_ne_top` / 引理 `toENNReal_of_ne_top`

English:
lemma toENNReal_of_ne_top
  given: {x : EReal} (hx : x != ⊤)
  statement: x.toENNReal = ENNReal.ofReal x.toReal
  proof: if_neg hx

@[simp]

中文:
引理 toENNReal_of_ne_top
  条件: {x : E实数} (hx : x != ⊤)
  结论: x.toENN实数 = ENN实数.of实数 x.to实数
  证明: if_neg hx

@[simp]

Depends on / 依赖: if_neg
-/
lemma toENNReal_of_ne_top {x : EReal} (hx : x != ⊤) : x.toENNReal = ENNReal.ofReal x.toReal :=
  if_neg hx

@[simp]
/--
lemma `toENNReal_eq_top_iff` / 引理 `toENNReal_eq_top_iff`

English:
lemma toENNReal_eq_top_iff
  given: {x : EReal}
  statement: x.toENNReal = ⊤ ↔ x = ⊤
  proof: by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toENNReal]

中文:
引理 toENNReal_eq_top_iff
  条件: {x : E实数}
  结论: x.toENN实数 = ⊤ ↔ x = ⊤
  证明: by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toENNReal]

Depends on / 依赖: toENNReal
-/
lemma toENNReal_eq_top_iff {x : EReal} : x.toENNReal = ⊤ ↔ x = ⊤ := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toENNReal]

/--
lemma `toENNReal_ne_top_iff` / 引理 `toENNReal_ne_top_iff`

English:
lemma toENNReal_ne_top_iff
  given: {x : EReal}
  statement: x.toENNReal != ⊤ ↔ x != ⊤
  proof: toENNReal_eq_top_iff.not

@[simp]

中文:
引理 toENNReal_ne_top_iff
  条件: {x : E实数}
  结论: x.toENN实数 != ⊤ ↔ x != ⊤
  证明: toENNReal_eq_top_iff.not

@[simp]

Depends on / 依赖: toENNReal_eq_top_iff, toENNReal_eq_top_iff.not
-/
lemma toENNReal_ne_top_iff {x : EReal} : x.toENNReal != ⊤ ↔ x != ⊤ := toENNReal_eq_top_iff.not

@[simp]
/--
lemma `toENNReal_of_nonpos` / 引理 `toENNReal_of_nonpos`

English:
lemma toENNReal_of_nonpos
  given: {x : EReal} (hx : x <= 0)
  statement: x.toENNReal = 0
  proof: by
  rw [toENNReal]; rw [if_neg (fun h => ?_)]
  · exact ENNReal.ofReal_of_nonpos (toReal_nonpos hx)
· exact zero_ne_top top_le_iff.mp h ▸ hx

中文:
引理 toENNReal_of_nonpos
  条件: {x : E实数} (hx : x <= 0)
  结论: x.toENN实数 = 0
  证明: by
  rw [toENNReal]; rw [if_neg (fun h => ?_)]
  · exact ENNReal.ofReal_of_nonpos (toReal_nonpos hx)
· exact zero_ne_top top_le_iff.mp h ▸ hx

Depends on / 依赖: ENNReal, ENNReal.ofReal_of_nonpos, if_neg, ofReal_of_nonpos, toENNReal, toReal_nonpos, top_le_iff, top_le_iff.mp, zero_ne_top
-/
lemma toENNReal_of_nonpos {x : EReal} (hx : x <= 0) : x.toENNReal = 0 := by
  rw [toENNReal]; rw [if_neg (fun h => ?_)]
  · exact ENNReal.ofReal_of_nonpos (toReal_nonpos hx)
· exact zero_ne_top top_le_iff.mp h ▸ hx

/--
lemma `toENNReal_bot` / 引理 `toENNReal_bot`

English:
lemma toENNReal_bot
  statement: (⊥ : EReal).toENNReal = 0
  proof: toENNReal_of_nonpos bot_le

中文:
引理 toENNReal_bot
  结论: (⊥ : E实数).toENN实数 = 0
  证明: toENNReal_of_nonpos bot_le

Depends on / 依赖: bot_le, toENNReal_of_nonpos
-/
lemma toENNReal_bot : (⊥ : EReal).toENNReal = 0 := toENNReal_of_nonpos bot_le
/--
lemma `toENNReal_zero` / 引理 `toENNReal_zero`

English:
lemma toENNReal_zero
  statement: (0 : EReal).toENNReal = 0
  proof: toENNReal_of_nonpos le_rfl

中文:
引理 toENNReal_zero
  结论: (0 : E实数).toENN实数 = 0
  证明: toENNReal_of_nonpos le_rfl

Depends on / 依赖: le_rfl, toENNReal_of_nonpos
-/
lemma toENNReal_zero : (0 : EReal).toENNReal = 0 := toENNReal_of_nonpos le_rfl

/--
lemma `toENNReal_eq_zero_iff` / 引理 `toENNReal_eq_zero_iff`

English:
lemma toENNReal_eq_zero_iff
  given: {x : EReal}
  statement: x.toENNReal = 0 ↔ x <= 0
  proof: by
  induction x <;> simp [toENNReal]

中文:
引理 toENNReal_eq_zero_iff
  条件: {x : E实数}
  结论: x.toENN实数 = 0 ↔ x <= 0
  证明: by
  induction x <;> simp [toENNReal]

Depends on / 依赖: toENNReal
-/
lemma toENNReal_eq_zero_iff {x : EReal} : x.toENNReal = 0 ↔ x <= 0 := by
  induction x <;> simp [toENNReal]

/--
lemma `toENNReal_ne_zero_iff` / 引理 `toENNReal_ne_zero_iff`

English:
lemma toENNReal_ne_zero_iff
  given: {x : EReal}
  statement: x.toENNReal != 0 ↔ 0 < x
  proof: by
  simp [toENNReal_eq_zero_iff.not]

@[simp]

中文:
引理 toENNReal_ne_zero_iff
  条件: {x : E实数}
  结论: x.toENN实数 != 0 ↔ 0 < x
  证明: by
  simp [toENNReal_eq_zero_iff.not]

@[simp]

Depends on / 依赖: toENNReal_eq_zero_iff, toENNReal_eq_zero_iff.not
-/
lemma toENNReal_ne_zero_iff {x : EReal} : x.toENNReal != 0 ↔ 0 < x := by
  simp [toENNReal_eq_zero_iff.not]

@[simp]
/--
lemma `toENNReal_pos_iff` / 引理 `toENNReal_pos_iff`

English:
lemma toENNReal_pos_iff
  given: {x : EReal}
  statement: 0 < x.toENNReal ↔ 0 < x
  proof: by
  rw [pos_iff_ne_zero]; rw [toENNReal_ne_zero_iff]

@[simp]

中文:
引理 toENNReal_pos_iff
  条件: {x : E实数}
  结论: 0 < x.toENN实数 ↔ 0 < x
  证明: by
  rw [pos_iff_ne_zero]; rw [toENNReal_ne_zero_iff]

@[simp]

Depends on / 依赖: pos_iff_ne_zero, toENNReal_ne_zero_iff
-/
lemma toENNReal_pos_iff {x : EReal} : 0 < x.toENNReal ↔ 0 < x := by
  rw [pos_iff_ne_zero]; rw [toENNReal_ne_zero_iff]

@[simp]
/--
lemma `coe_toENNReal` / 引理 `coe_toENNReal`

English:
lemma coe_toENNReal
  given: {x : EReal} (hx : 0 <= x)
  statement: (x.toENNReal : EReal) = x
  proof: by
  rw [toENNReal]
  by_cases h_top : x = ⊤
  · rw [if_pos h_top, h_top]
    rfl
  rw [if_neg h_top]
  simp only [coe_ennreal_ofReal, hx, toReal_nonneg, max_eq_left]
  exact coe_toReal h_top fun _ => by simp_all only [le_bot_iff, zero_ne_bot]

中文:
引理 coe_toENNReal
  条件: {x : E实数} (hx : 0 <= x)
  结论: (x.toENN实数 : E实数) = x
  证明: by
  rw [toENNReal]
  by_cases h_top : x = ⊤
  · rw [if_pos h_top, h_top]
    rfl
  rw [if_neg h_top]
  simp only [coe_ennreal_ofReal, hx, toReal_nonneg, max_eq_left]
  exact coe_toReal h_top fun _ => by simp_all only [le_bot_iff, zero_ne_bot]

Depends on / 依赖: coe_ennreal_ofReal, coe_toReal, h_top, if_neg, if_pos, le_bot_iff, max_eq_left, toENNReal, toReal_nonneg, zero_ne_bot
-/
lemma coe_toENNReal {x : EReal} (hx : 0 <= x) : (x.toENNReal : EReal) = x := by
  rw [toENNReal]
  by_cases h_top : x = ⊤
  · rw [if_pos h_top, h_top]
    rfl
  rw [if_neg h_top]
  simp only [coe_ennreal_ofReal, hx, toReal_nonneg, max_eq_left]
  exact coe_toReal h_top fun _ => by simp_all only [le_bot_iff, zero_ne_bot]

/--
lemma `coe_toENNReal_eq_max` / 引理 `coe_toENNReal_eq_max`

English:
lemma coe_toENNReal_eq_max
  given: {x : EReal}
  statement: x.toENNReal = max 0 x
  proof: by
  rcases le_total 0 x with (hx | hx)
  · rw [coe_toENNReal hx, max_eq_right hx]
  · rw [toENNReal_of_nonpos hx, max_eq_left hx, coe_ennreal_zero]

@[simp]

中文:
引理 coe_toENNReal_eq_max
  条件: {x : E实数}
  结论: x.toENN实数 = max 0 x
  证明: by
  rcases le_total 0 x with (hx | hx)
  · rw [coe_toENNReal hx, max_eq_right hx]
  · rw [toENNReal_of_nonpos hx, max_eq_left hx, coe_ennreal_zero]

@[simp]

Depends on / 依赖: coe_ennreal_zero, coe_toENNReal, le_total, max_eq_left, max_eq_right, toENNReal_of_nonpos
-/
lemma coe_toENNReal_eq_max {x : EReal} : x.toENNReal = max 0 x := by
  rcases le_total 0 x with (hx | hx)
  · rw [coe_toENNReal hx, max_eq_right hx]
  · rw [toENNReal_of_nonpos hx, max_eq_left hx, coe_ennreal_zero]

@[simp]
/--
lemma `toENNReal_coe` / 引理 `toENNReal_coe`

English:
lemma toENNReal_coe
  given: {x : Real>=0∞}
  statement: (x : EReal).toENNReal = x
  proof: by
  by_cases h_top : x = ⊤
  · rw [h_top, coe_ennreal_top, toENNReal_top]
  rwa [toENNReal, if_neg _, toReal_coe_ennreal, ENNReal.ofReal_toReal_eq_iff]
  simp [h_top]

中文:
引理 toENNReal_coe
  条件: {x : 实数>=0∞}
  结论: (x : E实数).toENN实数 = x
  证明: by
  by_cases h_top : x = ⊤
  · rw [h_top, coe_ennreal_top, toENNReal_top]
  rwa [toENNReal, if_neg _, toReal_coe_ennreal, ENNReal.ofReal_toReal_eq_iff]
  simp [h_top]

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal_eq_iff, coe_ennreal_top, h_top, if_neg, ofReal_toReal_eq_iff, toENNReal, toENNReal_top, toReal_coe_ennreal
-/
lemma toENNReal_coe {x : Real>=0∞} : (x : EReal).toENNReal = x := by
  by_cases h_top : x = ⊤
  · rw [h_top, coe_ennreal_top, toENNReal_top]
  rwa [toENNReal, if_neg _, toReal_coe_ennreal, ENNReal.ofReal_toReal_eq_iff]
  simp [h_top]

/--
lemma `real_coe_toENNReal` / 引理 `real_coe_toENNReal`

English:
lemma real_coe_toENNReal
  given: (x : Real)
  statement: (x : EReal).toENNReal = ENNReal.ofReal x
  proof: rfl

@[simp]

中文:
引理 real_coe_toENNReal
  条件: (x : 实数)
  结论: (x : E实数).toENN实数 = ENN实数.of实数 x
  证明: rfl

@[simp]
-/
@[simp] lemma real_coe_toENNReal (x : Real) : (x : EReal).toENNReal = ENNReal.ofReal x := rfl

@[simp]
/--
lemma `toReal_toENNReal` / 引理 `toReal_toENNReal`

English:
lemma toReal_toENNReal
  given: {x : EReal} (hx : 0 <= x)
  statement: x.toENNReal.toReal = x.toReal
  proof: by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toReal_nonneg hx]

中文:
引理 toReal_toENNReal
  条件: {x : E实数} (hx : 0 <= x)
  结论: x.toENN实数.to实数 = x.to实数
  证明: by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toReal_nonneg hx]

Depends on / 依赖: toReal_nonneg
-/
lemma toReal_toENNReal {x : EReal} (hx : 0 <= x) : x.toENNReal.toReal = x.toReal := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toReal_nonneg hx]

/--
lemma `toENNReal_eq_toENNReal` / 引理 `toENNReal_eq_toENNReal`

English:
lemma toENNReal_eq_toENNReal
  given: {x y : EReal} (hx : 0 <= x) (hy : 0 <= y)
  proof: by
  induction x <;> induction y <;> simp_all

中文:
引理 toENNReal_eq_toENNReal
  条件: {x y : E实数} (hx : 0 <= x) (hy : 0 <= y)
  证明: by
  induction x <;> induction y <;> simp_all
-/
lemma toENNReal_eq_toENNReal {x y : EReal} (hx : 0 <= x) (hy : 0 <= y) :
    x.toENNReal = y.toENNReal ↔ x = y := by
  induction x <;> induction y <;> simp_all

/--
lemma `toENNReal_le_toENNReal` / 引理 `toENNReal_le_toENNReal`

English:
lemma toENNReal_le_toENNReal
  given: {x y : EReal} (h : x <= y)
  statement: x.toENNReal <= y.toENNReal
  proof: by
  induction x
  · simp
  · by_cases hy_top : y = ⊤
    · simp [hy_top]
    simp only [toENNReal, coe_ne_top, ↓reduceIte, toReal_coe, hy_top]
exact ENNReal.ofReal_le_ofReal EReal.toReal_le_toReal h (coe_ne_bot _) hy_top
  · simp_all

中文:
引理 toENNReal_le_toENNReal
  条件: {x y : E实数} (h : x <= y)
  结论: x.toENN实数 <= y.toENN实数
  证明: by
  induction x
  · simp
  · by_cases hy_top : y = ⊤
    · simp [hy_top]
    simp only [toENNReal, coe_ne_top, ↓reduceIte, toReal_coe, hy_top]
exact ENNReal.ofReal_le_ofReal EReal.toReal_le_toReal h (coe_ne_bot _) hy_top
  · simp_all

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, EReal.toReal_le_toReal, coe_ne_bot, coe_ne_top, hy_top, ofReal_le_ofReal, reduceIte, toENNReal, toReal_coe, toReal_le_toReal
-/
lemma toENNReal_le_toENNReal {x y : EReal} (h : x <= y) : x.toENNReal <= y.toENNReal := by
  induction x
  · simp
  · by_cases hy_top : y = ⊤
    · simp [hy_top]
    simp only [toENNReal, coe_ne_top, ↓reduceIte, toReal_coe, hy_top]
exact ENNReal.ofReal_le_ofReal EReal.toReal_le_toReal h (coe_ne_bot _) hy_top
  · simp_all

/--
lemma `toENNReal_lt_toENNReal` / 引理 `toENNReal_lt_toENNReal`

English:
lemma toENNReal_lt_toENNReal
  given: {x y : EReal} (hx : 0 <= x) (hxy : x < y)
  proof: lt_of_le_of_ne (toENNReal_le_toENNReal hxy.le)
fun h => hxy.ne (toENNReal_eq_toENNReal hx (hx.trans_lt hxy).le).mp h

中文:
引理 toENNReal_lt_toENNReal
  条件: {x y : E实数} (hx : 0 <= x) (hxy : x < y)
  证明: lt_of_le_of_ne (toENNReal_le_toENNReal hxy.le)
fun h => hxy.ne (toENNReal_eq_toENNReal hx (hx.trans_lt hxy).le).mp h

Depends on / 依赖: hx.trans_lt, hxy.le, hxy.ne, lt_of_le_of_ne, toENNReal_eq_toENNReal, toENNReal_le_toENNReal, trans_lt
-/
lemma toENNReal_lt_toENNReal {x y : EReal} (hx : 0 <= x) (hxy : x < y) :
    x.toENNReal < y.toENNReal :=
  lt_of_le_of_ne (toENNReal_le_toENNReal hxy.le)
fun h => hxy.ne (toENNReal_eq_toENNReal hx (hx.trans_lt hxy).le).mp h


/--
theorem `coe_coe_eq_natCast` / 定理 `coe_coe_eq_natCast`

English:
theorem coe_coe_eq_natCast
  given: (n : Nat)
  statement: (n : Real) = (n : EReal)
  proof: rfl

中文:
定理 coe_coe_eq_natCast
  条件: (n : 自然数)
  结论: (n : 实数) = (n : E实数)
  证明: rfl
-/
theorem coe_coe_eq_natCast (n : Nat) : (n : Real) = (n : EReal) := rfl

/--
theorem `natCast_ne_bot` / 定理 `natCast_ne_bot`

English:
theorem natCast_ne_bot
  given: (n : Nat)
  statement: (n : EReal) != ⊥
  proof: Ne.symm (ne_of_beq_false rfl)

中文:
定理 natCast_ne_bot
  条件: (n : 自然数)
  结论: (n : E实数) != ⊥
  证明: Ne.symm (ne_of_beq_false rfl)

Depends on / 依赖: Ne.symm, ne_of_beq_false
-/
theorem natCast_ne_bot (n : Nat) : (n : EReal) != ⊥ := Ne.symm (ne_of_beq_false rfl)

/--
theorem `natCast_ne_top` / 定理 `natCast_ne_top`

English:
theorem natCast_ne_top
  given: (n : Nat)
  statement: (n : EReal) != ⊤
  proof: Ne.symm (ne_of_beq_false rfl)

@[norm_cast]

中文:
定理 natCast_ne_top
  条件: (n : 自然数)
  结论: (n : E实数) != ⊤
  证明: Ne.symm (ne_of_beq_false rfl)

@[norm_cast]

Depends on / 依赖: Ne.symm, ne_of_beq_false
-/
theorem natCast_ne_top (n : Nat) : (n : EReal) != ⊤ := Ne.symm (ne_of_beq_false rfl)

@[norm_cast]
/--
theorem `natCast_eq_iff` / 定理 `natCast_eq_iff`

English:
theorem natCast_eq_iff
  given: {m n : Nat}
  statement: (m : EReal) = (n : EReal) ↔ m = n
  proof: by
  rw [← coe_coe_eq_natCast n]; rw [← coe_coe_eq_natCast m]; rw [EReal.coe_eq_coe_iff]; rw [Nat.cast_inj]

中文:
定理 natCast_eq_iff
  条件: {m n : 自然数}
  结论: (m : E实数) = (n : E实数) ↔ m = n
  证明: by
  rw [← coe_coe_eq_natCast n]; rw [← coe_coe_eq_natCast m]; rw [EReal.coe_eq_coe_iff]; rw [Nat.cast_inj]

Depends on / 依赖: EReal.coe_eq_coe_iff, Nat.cast_inj, cast_inj, coe_coe_eq_natCast, coe_eq_coe_iff
-/
theorem natCast_eq_iff {m n : Nat} : (m : EReal) = (n : EReal) ↔ m = n := by
  rw [← coe_coe_eq_natCast n]; rw [← coe_coe_eq_natCast m]; rw [EReal.coe_eq_coe_iff]; rw [Nat.cast_inj]

/--
theorem `natCast_ne_iff` / 定理 `natCast_ne_iff`

English:
theorem natCast_ne_iff
  given: {m n : Nat}
  statement: (m : EReal) != (n : EReal) ↔ m != n
  proof: not_iff_not.2 natCast_eq_iff

@[norm_cast]

中文:
定理 natCast_ne_iff
  条件: {m n : 自然数}
  结论: (m : E实数) != (n : E实数) ↔ m != n
  证明: not_iff_not.2 natCast_eq_iff

@[norm_cast]

Depends on / 依赖: natCast_eq_iff, not_iff_not
-/
theorem natCast_ne_iff {m n : Nat} : (m : EReal) != (n : EReal) ↔ m != n :=
  not_iff_not.2 natCast_eq_iff

@[norm_cast]
/--
theorem `natCast_le_iff` / 定理 `natCast_le_iff`

English:
theorem natCast_le_iff
  given: {m n : Nat}
  statement: (m : EReal) <= (n : EReal) ↔ m <= n
  proof: by
  rw [← coe_coe_eq_natCast n]; rw [← coe_coe_eq_natCast m]; rw [EReal.coe_le_coe_iff]; rw [Nat.cast_le]

@[norm_cast]

中文:
定理 natCast_le_iff
  条件: {m n : 自然数}
  结论: (m : E实数) <= (n : E实数) ↔ m <= n
  证明: by
  rw [← coe_coe_eq_natCast n]; rw [← coe_coe_eq_natCast m]; rw [EReal.coe_le_coe_iff]; rw [Nat.cast_le]

@[norm_cast]

Depends on / 依赖: EReal.coe_le_coe_iff, Nat.cast_le, cast_le, coe_coe_eq_natCast, coe_le_coe_iff
-/
theorem natCast_le_iff {m n : Nat} : (m : EReal) <= (n : EReal) ↔ m <= n := by
  rw [← coe_coe_eq_natCast n]; rw [← coe_coe_eq_natCast m]; rw [EReal.coe_le_coe_iff]; rw [Nat.cast_le]

@[norm_cast]
/--
theorem `natCast_lt_iff` / 定理 `natCast_lt_iff`

English:
theorem natCast_lt_iff
  given: {m n : Nat}
  statement: (m : EReal) < (n : EReal) ↔ m < n
  proof: by
  rw [← coe_coe_eq_natCast n]; rw [← coe_coe_eq_natCast m]; rw [EReal.coe_lt_coe_iff]; rw [Nat.cast_lt]

@[simp, norm_cast]

中文:
定理 natCast_lt_iff
  条件: {m n : 自然数}
  结论: (m : E实数) < (n : E实数) ↔ m < n
  证明: by
  rw [← coe_coe_eq_natCast n]; rw [← coe_coe_eq_natCast m]; rw [EReal.coe_lt_coe_iff]; rw [Nat.cast_lt]

@[simp, norm_cast]

Depends on / 依赖: EReal.coe_lt_coe_iff, Nat.cast_lt, cast_lt, coe_coe_eq_natCast, coe_lt_coe_iff
-/
theorem natCast_lt_iff {m n : Nat} : (m : EReal) < (n : EReal) ↔ m < n := by
  rw [← coe_coe_eq_natCast n]; rw [← coe_coe_eq_natCast m]; rw [EReal.coe_lt_coe_iff]; rw [Nat.cast_lt]

@[simp, norm_cast]
/--
theorem `natCast_mul` / 定理 `natCast_mul`

English:
theorem natCast_mul
  given: (m n : Nat)
  proof: by
  rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [Nat.cast_mul]; rw [EReal.coe_mul]

中文:
定理 natCast_mul
  条件: (m n : 自然数)
  证明: by
  rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [Nat.cast_mul]; rw [EReal.coe_mul]

Depends on / 依赖: EReal.coe_mul, Nat.cast_mul, cast_mul, coe_coe_eq_natCast, coe_mul
-/
theorem natCast_mul (m n : Nat) :
    (m * n : Nat) = (m : EReal) * (n : EReal) := by
  rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [← coe_coe_eq_natCast]; rw [Nat.cast_mul]; rw [EReal.coe_mul]


/--
theorem `exists_rat_btwn_of_lt` / 定理 `exists_rat_btwn_of_lt`

English:
theorem exists_rat_btwn_of_lt
  proof: exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : Real), _ =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, _ => ⟨0, bot_lt_coe _, coe_lt_top _⟩

中文:
定理 exists_rat_btwn_of_lt
  证明: exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : Real), _ =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, _ => ⟨0, bot_lt_coe _, coe_lt_top _⟩

Depends on / 依赖: exists_rat_gt
-/
theorem exists_rat_btwn_of_lt :
    forall {a b : EReal}, a < b -> exists x : Rat, a < (x : Real) ∧ ((x : Real) : EReal) < b
  | ⊤, _, h => (not_top_lt h).elim
  | (a : Real), ⊥, h => (lt_irrefl _ ((bot_lt_coe a).trans h)).elim
  | (a : Real), (b : Real), h => by simp [exists_rat_btwn (EReal.coe_lt_coe_iff.1 h)]
  | (a : Real), ⊤, _ =>
    let ⟨b, hab⟩ := exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : Real), _ =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, _ => ⟨0, bot_lt_coe _, coe_lt_top _⟩

/--
theorem `lt_iff_exists_rat_btwn` / 定理 `lt_iff_exists_rat_btwn`

English:
theorem lt_iff_exists_rat_btwn
  given: {a b : EReal}
  proof: ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

中文:
定理 lt_iff_exists_rat_btwn
  条件: {a b : E实数}
  证明: ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

Depends on / 依赖: ax.trans, exists_rat_btwn_of_lt
-/
theorem lt_iff_exists_rat_btwn {a b : EReal} :
    a < b ↔ exists x : Rat, a < (x : Real) ∧ ((x : Real) : EReal) < b :=
  ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

/--
theorem `lt_iff_exists_real_btwn` / 定理 `lt_iff_exists_real_btwn`

English:
theorem lt_iff_exists_real_btwn
  given: {a b : EReal}
  statement: a < b ↔ exists x : Real, a < x ∧ (x : EReal) < b
  proof: ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : Real), ax, xb⟩,
    fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

中文:
定理 lt_iff_exists_real_btwn
  条件: {a b : E实数}
  结论: a < b ↔ 存在 x : 实数, a < x ∧ (x : E实数) < b
  证明: ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : Real), ax, xb⟩,
    fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

Depends on / 依赖: ax.trans, exists_rat_btwn_of_lt
-/
theorem lt_iff_exists_real_btwn {a b : EReal} : a < b ↔ exists x : Real, a < x ∧ (x : EReal) < b :=
  ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : Real), ax, xb⟩,
    fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

/--
Definition of `neTopBotEquivReal` / `neTopBotEquivReal` 的定义

English:
definition neTopBotEquivReal
  signature: : ({⊥, ⊤}ᶜ : Set EReal) ≃ Real where
  body: EReal.toReal x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
    lift x to Real
    · simpa [not_or, and_comm] using hx
    · simp
  right_inv x := by simp

中文:
定义 neTopBotEquivReal
  签名: : ({⊥, ⊤}ᶜ : Set E实数) ≃ 实数 where
  定义体: EReal.toReal x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
    lift x to Real
    · simpa [not_or, and_comm] using hx
    · simp
  right_inv x := by simp

Depends on / 依赖: EReal.toReal, toReal
-/
def neTopBotEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ Real where
  toFun x := EReal.toReal x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
    lift x to Real
    · simpa [not_or, and_comm] using hx
    · simp
  right_inv x := by simp

end EReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: cast from `ℝ` to `EReal`. -/
@[positivity Real.toEReal _]
meta def evalRealToEReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(EReal), ~q(Real.toEReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(EReal.coe_pos.2 $pa))
    | .nonnegative pa => pure (.nonnegative q(EReal.coe_nonneg.2 $pa))
    | .nonzero pa => pure (.nonzero q(EReal.coe_ne_zero.2 $pa))
    | _ => pure .none
  | _, _, _ => throwError "not Real.toEReal"

/-- Extension for the `positivity` tactic: cast from `ℝ≥0∞` to `EReal`. -/
@[positivity ENNReal.toEReal _]
meta def evalENNRealToEReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(EReal), ~q(ENNReal.toEReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(EReal.coe_ennreal_pos.2 $pa))
    | .nonzero pa => pure (.positive q(EReal.coe_ennreal_pos_iff_ne_zero.2 $pa))
    | _ => pure (.nonnegative q(EReal.coe_ennreal_nonneg $a))
  | _, _, _ => throwError "not ENNReal.toEReal"

/-- Extension for the `positivity` tactic: projection from `EReal` to `ℝ`.

We prove that `EReal.toReal x` is nonnegative whenever `x` is nonnegative.
Since `EReal.toReal ⊤ = 0`, we cannot prove a stronger statement,
at least without relying on a tactic like `finiteness`. -/
@[positivity EReal.toReal _]
meta def evalERealToReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(EReal.toReal $a) =>
    assertInstancesCommute
    match (← core q(inferInstance) (some q(inferInstance)) a).toNonneg with
    | .some pa => pure (.nonnegative q(EReal.toReal_nonneg $pa))
    | _ => pure .none
  | _, _, _ => throwError "not EReal.toReal"

/-- Extension for the `positivity` tactic: projection from `EReal` to `ℝ≥0∞`.

We show that `EReal.toENNReal x` is positive whenever `x` is positive,
and it is nonnegative otherwise.
We cannot deduce any corollaries from `x ≠ 0`, since `EReal.toENNReal x = 0` for `x < 0`.
-/
@[positivity EReal.toENNReal _]
meta def evalERealToENNReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ENNReal), ~q(EReal.toENNReal $a) =>
    assertInstancesCommute
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa => pure (.positive q(EReal.toENNReal_pos_iff.2 $pa))
    | _ => pure (.nonnegative q(zero_le (a := $e)))
  | _, _, _ => throwError "not EReal.toENNReal"

end Mathlib.Meta.Positivity
