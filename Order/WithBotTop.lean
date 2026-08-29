/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kevin Buzzard
-/
module

public import Mathlib.Order.WithBot

/-!
# Adding both `⊥` and `⊤` to a type

This files defines an abbreviation `WithBotTop ι` for `WithBot (WithTop ι)`.
We also introduce an abbreviation `EInt` for `WithBotTop ℤ`.
-/

@[expose] public section

variable {ι : Type*}

variable (ι) in
/-- The type obtained by adding both `⊥` and `⊤` to a type. -/
@[to_dual /-- The type obtained by adding both `⊤` and `⊥` to a type. -/]
/--
Definition of `WithBotTop` / `WithBotTop` 的定义

English:
abbreviation WithBotTop
  body: WithBot (WithTop ι)

中文:
缩写 WithBotTop
  定义体: WithBot (WithTop ι)

Depends on / 依赖: WithBot, WithTop
-/
abbrev WithBotTop := WithBot (WithTop ι)

/--
Definition of `WithBotTop.coe` / `WithBotTop.coe` 的定义

English:
definition WithBotTop.coe
  signature: : ι -> WithBotTop ι
  body: WithBot.some ∘ WithTop.some

中文:
定义 WithBotTop.coe
  签名: : ι -> WithBotTop ι
  定义体: WithBot.some ∘ WithTop.some

Depends on / 依赖: WithBot, WithBot.some, WithTop, WithTop.some
-/
def WithBotTop.coe : ι -> WithBotTop ι :=
  WithBot.some ∘ WithTop.some

namespace WithBotTop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe ι (WithBotTop ι)
  body: ⟨WithBotTop.coe⟩

中文:
实例 :
  签名: Coe ι (WithBotTop ι)
  定义体: ⟨WithBotTop.coe⟩

Depends on / 依赖: WithBotTop, WithBotTop.coe
-/
instance : Coe ι (WithBotTop ι) := ⟨WithBotTop.coe⟩

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective (WithBotTop.coe : ι -> _)
  proof: by rintro _ _ ⟨⟩; rfl

中文:
定理 coe_injective
  结论: Function.Injective (WithBotTop.coe : ι -> _)
  证明: by rintro _ _ ⟨⟩; rfl
-/
theorem coe_injective : Function.Injective (WithBotTop.coe : ι -> _) := by rintro _ _ ⟨⟩; rfl

/--
lemma `coe_ne_bot` / 引理 `coe_ne_bot`

English:
lemma coe_ne_bot
  given: (a : ι)
  statement: (a : WithBotTop ι) != ⊥
  proof: by rintro ⟨⟩

中文:
引理 coe_ne_bot
  条件: (a : ι)
  结论: (a : WithBotTop ι) != ⊥
  证明: by rintro ⟨⟩
-/
@[simp] lemma coe_ne_bot (a : ι) : (a : WithBotTop ι) != ⊥ := by rintro ⟨⟩
/--
lemma `coe_ne_top` / 引理 `coe_ne_top`

English:
lemma coe_ne_top
  given: (a : ι)
  statement: (a : WithBotTop ι) != ⊤
  proof: by rintro ⟨⟩

中文:
引理 coe_ne_top
  条件: (a : ι)
  结论: (a : WithBotTop ι) != ⊤
  证明: by rintro ⟨⟩
-/
@[simp] lemma coe_ne_top (a : ι) : (a : WithBotTop ι) != ⊤ := by rintro ⟨⟩
/--
lemma `top_ne_bot` / 引理 `top_ne_bot`

English:
lemma top_ne_bot
  statement: (⊤ : WithBotTop ι) != ⊥
  proof: by rintro ⟨⟩

中文:
引理 top_ne_bot
  结论: (⊤ : WithBotTop ι) != ⊥
  证明: by rintro ⟨⟩
-/
@[simp] lemma top_ne_bot : (⊤ : WithBotTop ι) != ⊥ := by rintro ⟨⟩

section

variable {motive : (WithBotTop ι) -> Sort*}
  (bot : motive ⊥) (coe : forall a : ι, motive a) (top : motive ⊤)

/-- A recursor for `WithBotTop` in terms of the coercion. -/
@[elab_as_elim]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: : forall a, motive a

中文:
定义 rec
  签名: : 对任意 a, motive a
-/
protected def rec : forall a, motive a
  | ⊥ => bot
  | (a : ι) => coe a
  | ⊤ => top

/--
lemma `rec_bot` / 引理 `rec_bot`

English:
lemma rec_bot
  statement: WithBotTop.rec (motive := motive) bot coe top ⊥ = bot
  proof: rfl

中文:
引理 rec_bot
  结论: WithBotTop.rec (motive := motive) bot coe top ⊥ = bot
  证明: rfl
-/
@[simp] lemma rec_bot : WithBotTop.rec (motive := motive) bot coe top ⊥ = bot := rfl
/--
lemma `rec_coe` / 引理 `rec_coe`

English:
lemma rec_coe
  given: (a : ι)
  statement: WithBotTop.rec (motive := motive) bot coe top a = coe a
  proof: rfl

中文:
引理 rec_coe
  条件: (a : ι)
  结论: WithBotTop.rec (motive := motive) bot coe top a = coe a
  证明: rfl
-/
@[simp] lemma rec_coe (a : ι) : WithBotTop.rec (motive := motive) bot coe top a = coe a := rfl
/--
lemma `rec_top` / 引理 `rec_top`

English:
lemma rec_top
  statement: WithBotTop.rec (motive := motive) bot coe top ⊤ = top
  proof: rfl

中文:
引理 rec_top
  结论: WithBotTop.rec (motive := motive) bot coe top ⊤ = top
  证明: rfl
-/
@[simp] lemma rec_top : WithBotTop.rec (motive := motive) bot coe top ⊤ = top := rfl

end

@[simp]
/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  given: [LE ι] {a b : ι}
  proof: by
  rw [← WithTop.coe_le_coe (α := ι)]
  exact WithBot.coe_le_coe

@[simp]

中文:
引理 coe_le_coe
  条件: [LE ι] {a b : ι}
  证明: by
  rw [← WithTop.coe_le_coe (α := ι)]
  exact WithBot.coe_le_coe

@[simp]

Depends on / 依赖: WithBot, WithBot.coe_le_coe, WithTop, WithTop.coe_le_coe, coe_le_coe
-/
lemma coe_le_coe [LE ι] {a b : ι} :
    (a : WithBotTop ι) <= b ↔ a <= b := by
  rw [← WithTop.coe_le_coe (α := ι)]
  exact WithBot.coe_le_coe

@[simp]
/--
lemma `coe_lt_coe` / 引理 `coe_lt_coe`

English:
lemma coe_lt_coe
  given: [LT ι] {a b : ι}
  proof: by
  rw [← WithTop.coe_lt_coe (α := ι)]
  exact WithBot.coe_lt_coe

@[simp]

中文:
引理 coe_lt_coe
  条件: [LT ι] {a b : ι}
  证明: by
  rw [← WithTop.coe_lt_coe (α := ι)]
  exact WithBot.coe_lt_coe

@[simp]

Depends on / 依赖: WithBot, WithBot.coe_lt_coe, WithTop, WithTop.coe_lt_coe, coe_lt_coe
-/
lemma coe_lt_coe [LT ι] {a b : ι} :
    (a : WithBotTop ι) < b ↔ a < b := by
  rw [← WithTop.coe_lt_coe (α := ι)]
  exact WithBot.coe_lt_coe

@[simp]
/--
theorem `coe_strictMono` / 定理 `coe_strictMono`

English:
theorem coe_strictMono
  given: [Preorder ι]
  statement: StrictMono (WithBotTop.coe : ι -> _)
  proof: WithBot.coe_strictMono.comp WithTop.coe_strictMono

中文:
定理 coe_strictMono
  条件: [Preorder ι]
  结论: StrictMono (WithBotTop.coe : ι -> _)
  证明: WithBot.coe_strictMono.comp WithTop.coe_strictMono

Depends on / 依赖: WithBot, WithBot.coe_strictMono.comp, WithTop, WithTop.coe_strictMono, coe_strictMono
-/
theorem coe_strictMono [Preorder ι] : StrictMono (WithBotTop.coe : ι -> _) :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

/--
lemma `coe_monotone` / 引理 `coe_monotone`

English:
lemma coe_monotone
  given: [Preorder ι]
  proof: fun _ _ _ => by simpa

中文:
引理 coe_monotone
  条件: [Preorder ι]
  证明: fun _ _ _ => by simpa
-/
lemma coe_monotone [Preorder ι] :
    Monotone (WithBotTop.coe : ι -> _) :=
  fun _ _ _ => by simpa

end WithBotTop

/--
Definition of `EInt` / `EInt` 的定义

English:
abbreviation EInt
  body: WithBotTop Int

中文:
缩写 EInt
  定义体: WithBotTop Int

Depends on / 依赖: WithBotTop
-/
abbrev EInt := WithBotTop Int
