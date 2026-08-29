/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Logic.Relation

/-!
# Game addition relation

This file defines, given relations `rα : α → α → Prop` and `rβ : β → β → Prop`, a relation
`Prod.GameAdd` on pairs, such that `GameAdd rα rβ x y` iff `x` can be reached from `y` by
decreasing either entry (with respect to `rα` and `rβ`). It is so called since it models the
subsequency relation on the addition of combinatorial games.

We also define `Sym2.GameAdd`, which is the unordered pair analog of `Prod.GameAdd`.

## Main definitions and results

- `Prod.GameAdd`: the game addition relation on ordered pairs.
- `WellFounded.prod_gameAdd`: formalizes induction on ordered pairs, where exactly one entry
  decreases at a time.

- `Sym2.GameAdd`: the game addition relation on unordered pairs.
- `WellFounded.sym2_gameAdd`: formalizes induction on unordered pairs, where exactly one entry
  decreases at a time.
-/

@[expose] public section

variable {α β : Type*} {rα : α -> α -> Prop} {rβ : β -> β -> Prop} {a : α} {b : β}

/-! ### `Prod.GameAdd` -/

namespace Prod

variable (rα rβ)

/--
Inductive type `GameAdd` / 归纳类型 `GameAdd`

English:
inductive GameAdd
  parameters: : α × β -> α × β -> Prop
  constructors (2):
    - fst: {a₁ a₂ b} : rα a₁ a₂ -> GameAdd (a₁, b) (a₂, b)
    - snd: {a b₁ b₂} : rβ b₁ b₂ -> GameAdd (a, b₁) (a, b₂)

中文:
归纳类型 GameAdd
  参数: : α × β -> α × β -> 命题
  构造子 (2 个):
    - fst: {a₁ a₂ b} : rα a₁ a₂ -> GameAdd (a₁, b) (a₂, b)
    - snd: {a b₁ b₂} : rβ b₁ b₂ -> GameAdd (a, b₁) (a, b₂)
-/
inductive GameAdd : α × β -> α × β -> Prop
  | fst {a₁ a₂ b} : rα a₁ a₂ -> GameAdd (a₁, b) (a₂, b)
  | snd {a b₁ b₂} : rβ b₁ b₂ -> GameAdd (a, b₁) (a, b₂)

/--
theorem `gameAdd_iff` / 定理 `gameAdd_iff`

English:
theorem gameAdd_iff
  given: {rα rβ} {x y : α × β}
  proof: by
  constructor
  · rintro (@⟨a₁, a₂, b, h⟩ | @⟨a, b₁, b₂, h⟩)
    exacts [Or.inl ⟨h, rfl⟩, Or.inr ⟨h, rfl⟩]
  · revert x y
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨h, rfl : b₁ = b₂⟩ | ⟨h, rfl : a₁ = a₂⟩)
    exacts [GameAdd.fst h, GameAdd.snd h]

中文:
定理 gameAdd_iff
  条件: {rα rβ} {x y : α × β}
  证明: by
  constructor
  · rintro (@⟨a₁, a₂, b, h⟩ | @⟨a, b₁, b₂, h⟩)
    exacts [Or.inl ⟨h, rfl⟩, Or.inr ⟨h, rfl⟩]
  · revert x y
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨h, rfl : b₁ = b₂⟩ | ⟨h, rfl : a₁ = a₂⟩)
    exacts [GameAdd.fst h, GameAdd.snd h]

Depends on / 依赖: GameAdd, GameAdd.fst, GameAdd.snd, Or.inl, Or.inr, exacts, revert
-/
theorem gameAdd_iff {rα rβ} {x y : α × β} :
    GameAdd rα rβ x y ↔ rα x.1 y.1 ∧ x.2 = y.2 ∨ rβ x.2 y.2 ∧ x.1 = y.1 := by
  constructor
  · rintro (@⟨a₁, a₂, b, h⟩ | @⟨a, b₁, b₂, h⟩)
    exacts [Or.inl ⟨h, rfl⟩, Or.inr ⟨h, rfl⟩]
  · revert x y
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨h, rfl : b₁ = b₂⟩ | ⟨h, rfl : a₁ = a₂⟩)
    exacts [GameAdd.fst h, GameAdd.snd h]

/--
theorem `gameAdd_mk_iff` / 定理 `gameAdd_mk_iff`

English:
theorem gameAdd_mk_iff
  given: {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β}
  proof: gameAdd_iff

@[simp]

中文:
定理 gameAdd_mk_iff
  条件: {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β}
  证明: gameAdd_iff

@[simp]

Depends on / 依赖: gameAdd_iff
-/
theorem gameAdd_mk_iff {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β} :
    GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ rα a₁ a₂ ∧ b₁ = b₂ ∨ rβ b₁ b₂ ∧ a₁ = a₂ :=
  gameAdd_iff

@[simp]
/--
theorem `gameAdd_swap_swap` / 定理 `gameAdd_swap_swap`

English:
theorem gameAdd_swap_swap
  statement: forall a b : α × β, GameAdd rβ rα a.swap b.swap ↔ GameAdd rα rβ a b
  proof: fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => by rw [Prod.swap, Prod.swap, gameAdd_mk_iff, gameAdd_mk_iff, or_comm]

中文:
定理 gameAdd_swap_swap
  结论: 对任意 a b : α × β, GameAdd rβ rα a.swap b.swap ↔ GameAdd rα rβ a b
  证明: fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => by rw [Prod.swap, Prod.swap, gameAdd_mk_iff, gameAdd_mk_iff, or_comm]

Depends on / 依赖: Prod.swap, gameAdd_mk_iff, or_comm
-/
theorem gameAdd_swap_swap : forall a b : α × β, GameAdd rβ rα a.swap b.swap ↔ GameAdd rα rβ a b :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => by rw [Prod.swap, Prod.swap, gameAdd_mk_iff, gameAdd_mk_iff, or_comm]

/--
theorem `gameAdd_swap_swap_mk` / 定理 `gameAdd_swap_swap_mk`

English:
theorem gameAdd_swap_swap_mk
  given: (a₁ a₂ : α) (b₁ b₂ : β)
  proof: gameAdd_swap_swap rβ rα (b₁, a₁) (b₂, a₂)

中文:
定理 gameAdd_swap_swap_mk
  条件: (a₁ a₂ : α) (b₁ b₂ : β)
  证明: gameAdd_swap_swap rβ rα (b₁, a₁) (b₂, a₂)

Depends on / 依赖: gameAdd_swap_swap
-/
theorem gameAdd_swap_swap_mk (a₁ a₂ : α) (b₁ b₂ : β) :
    GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ GameAdd rβ rα (b₁, a₁) (b₂, a₂) :=
  gameAdd_swap_swap rβ rα (b₁, a₁) (b₂, a₂)

/--
theorem `gameAdd_le_lex` / 定理 `gameAdd_le_lex`

English:
theorem gameAdd_le_lex
  statement: GameAdd rα rβ <= Prod.Lex rα rβ
  proof: fun _ _ h =>
  h.rec (Prod.Lex.left _ _) (Prod.Lex.right _)

中文:
定理 gameAdd_le_lex
  结论: GameAdd rα rβ <= Prod.Lex rα rβ
  证明: fun _ _ h =>
  h.rec (Prod.Lex.left _ _) (Prod.Lex.right _)
-/
theorem gameAdd_le_lex : GameAdd rα rβ <= Prod.Lex rα rβ := fun _ _ h =>
  h.rec (Prod.Lex.left _ _) (Prod.Lex.right _)

/--
theorem `rprod_le_transGen_gameAdd` / 定理 `rprod_le_transGen_gameAdd`

English:
theorem rprod_le_transGen_gameAdd
  statement: RProd rα rβ <= Relation.TransGen (GameAdd rα rβ)

中文:
定理 rprod_le_transGen_gameAdd
  结论: RProd rα rβ <= Relation.TransGen (GameAdd rα rβ)
-/
theorem rprod_le_transGen_gameAdd : RProd rα rβ <= Relation.TransGen (GameAdd rα rβ)
  | _, _, h => h.rec (by
      intro _ _ _ _ hα hβ
      exact Relation.TransGen.tail (Relation.TransGen.single <| GameAdd.fst hα) (GameAdd.snd hβ))

end Prod

/--
theorem `Acc.prod_gameAdd` / 定理 `Acc.prod_gameAdd`

English:
theorem Acc.prod_gameAdd
  given: (ha : Acc rα a) (hb : Acc rβ b)
  proof: by
  induction ha generalizing b with | _ a _ iha
  induction hb with | _ b hb ihb
  refine Acc.intro _ fun h => ?_
  rintro (⟨ra⟩ | ⟨rb⟩)
  exacts [iha _ ra (Acc.intro b hb), ihb _ rb]

中文:
定理 Acc.prod_gameAdd
  条件: (ha : Acc rα a) (hb : Acc rβ b)
  证明: by
  induction ha generalizing b with | _ a _ iha
  induction hb with | _ b hb ihb
  refine Acc.intro _ fun h => ?_
  rintro (⟨ra⟩ | ⟨rb⟩)
  exacts [iha _ ra (Acc.intro b hb), ihb _ rb]

Depends on / 依赖: Acc.intro, exacts, generalizing
-/
theorem Acc.prod_gameAdd (ha : Acc rα a) (hb : Acc rβ b) :
    Acc (Prod.GameAdd rα rβ) (a, b) := by
  induction ha generalizing b with | _ a _ iha
  induction hb with | _ b hb ihb
  refine Acc.intro _ fun h => ?_
  rintro (⟨ra⟩ | ⟨rb⟩)
  exacts [iha _ ra (Acc.intro b hb), ihb _ rb]

/--
theorem `WellFounded.prod_gameAdd` / 定理 `WellFounded.prod_gameAdd`

English:
theorem WellFounded.prod_gameAdd
  given: (hα : WellFounded rα) (hβ : WellFounded rβ)
  proof: ⟨fun ⟨a, b⟩ => (hα.apply a).prod_gameAdd (hβ.apply b)⟩

中文:
定理 WellFounded.prod_gameAdd
  条件: (hα : WellFounded rα) (hβ : WellFounded rβ)
  证明: ⟨fun ⟨a, b⟩ => (hα.apply a).prod_gameAdd (hβ.apply b)⟩

Depends on / 依赖: prod_gameAdd
-/
theorem WellFounded.prod_gameAdd (hα : WellFounded rα) (hβ : WellFounded rβ) :
    WellFounded (Prod.GameAdd rα rβ) :=
  ⟨fun ⟨a, b⟩ => (hα.apply a).prod_gameAdd (hβ.apply b)⟩

namespace Prod

/-- Recursion on the well-founded `Prod.GameAdd` relation.
  Note that it's strictly more general to recurse on the lexicographic order instead. -/
@[elab_as_elim]
/--
Definition of `GameAdd.recursion` / `GameAdd.recursion` 的定义

English:
definition GameAdd.recursion
  signature: {C : α -> β -> Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
  body: @WellFounded.fix (α × β) (fun x => C x.1 x.2) _ (hα.prod_gameAdd hβ)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) ⟨a, b⟩

@[deprecated (since := "2026-03-13")] alias GameAdd.fix := GameAdd.recursion

中文:
定义 GameAdd.recursion
  签名: {C : α -> β -> Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
  定义体: @WellFounded.fix (α × β) (fun x => C x.1 x.2) _ (hα.prod_gameAdd hβ)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) ⟨a, b⟩

@[deprecated (since := "2026-03-13")] alias GameAdd.fix := GameAdd.recursion

Depends on / 依赖: WellFounded, WellFounded.fix, prod_gameAdd
-/
def GameAdd.recursion {C : α -> β -> Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : forall a₁ b₁, (forall a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) -> C a₂ b₂) -> C a₁ b₁) (a : α) (b : β) :
    C a b :=
  @WellFounded.fix (α × β) (fun x => C x.1 x.2) _ (hα.prod_gameAdd hβ)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) ⟨a, b⟩

@[deprecated (since := "2026-03-13")] alias GameAdd.fix := GameAdd.recursion

/--
theorem `GameAdd.recursion_eq` / 定理 `GameAdd.recursion_eq`

English:
theorem GameAdd.recursion_eq
  statement: {C : α -> β -> Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
  proof: WellFounded.fix_eq _ _ _

@[deprecated (since := "2026-03-13")] alias GameAdd.fix_eq := GameAdd.recursion_eq

中文:
定理 GameAdd.recursion_eq
  结论: {C : α -> β -> Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
  证明: WellFounded.fix_eq _ _ _

@[deprecated (since := "2026-03-13")] alias GameAdd.fix_eq := GameAdd.recursion_eq

Depends on / 依赖: WellFounded, WellFounded.fix_eq, fix_eq
-/
theorem GameAdd.recursion_eq {C : α -> β -> Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : forall a₁ b₁, (forall a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) -> C a₂ b₂) -> C a₁ b₁) (a : α) (b : β) :
    GameAdd.recursion hα hβ IH a b = IH a b fun a' b' _ => GameAdd.recursion hα hβ IH a' b' :=
  WellFounded.fix_eq _ _ _

@[deprecated (since := "2026-03-13")] alias GameAdd.fix_eq := GameAdd.recursion_eq

/-- Induction on the well-founded `Prod.GameAdd` relation.
  Note that it's strictly more general to induct on the lexicographic order instead. -/
@[deprecated GameAdd.recursion (since := "2026-03-13")]
/--
theorem `GameAdd.induction` / 定理 `GameAdd.induction`

English:
theorem GameAdd.induction
  given: {C : α -> β -> Prop}
  proof: GameAdd.recursion

中文:
定理 GameAdd.induction
  条件: {C : α -> β -> 命题}
  证明: GameAdd.recursion

Depends on / 依赖: GameAdd, GameAdd.recursion, recursion
-/
theorem GameAdd.induction {C : α -> β -> Prop} :
    WellFounded rα ->
      WellFounded rβ ->
        (forall a₁ b₁, (forall a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) -> C a₂ b₂) -> C a₁ b₁) -> forall a b, C a b :=
  GameAdd.recursion

end Prod

/-! ### `Sym2.GameAdd` -/

namespace Sym2

/--
Definition of `GameAdd` / `GameAdd` 的定义

English:
definition GameAdd
  signature: (rα : α -> α -> Prop)
  body: Sym2.lift₂
    ⟨fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂),
      fun a₁ b₁ a₂ b₂ => by
        dsimp
        rw [Prod.gameAdd_swap_swap_mk _ _ b₁ b₂ a₁ a₂]; rw [Prod.gameAdd_swap_swap_mk _ _ a₁ b₂ b₁ a₂]
        simp [or_comm]⟩

中文:
定义 GameAdd
  签名: (rα : α -> α -> 命题)
  定义体: Sym2.lift₂
    ⟨fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂),
      fun a₁ b₁ a₂ b₂ => by
        dsimp
        rw [Prod.gameAdd_swap_swap_mk _ _ b₁ b₂ a₁ a₂]; rw [Prod.gameAdd_swap_swap_mk _ _ a₁ b₂ b₁ a₂]
        simp [or_comm]⟩

Depends on / 依赖: GameAdd, Prod.GameAdd, Prod.gameAdd_swap_swap_mk, Sym2.lift, gameAdd_swap_swap_mk, or_comm
-/
def GameAdd (rα : α -> α -> Prop) : Sym2 α -> Sym2 α -> Prop :=
  Sym2.lift₂
    ⟨fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂),
      fun a₁ b₁ a₂ b₂ => by
        dsimp
        rw [Prod.gameAdd_swap_swap_mk _ _ b₁ b₂ a₁ a₂]; rw [Prod.gameAdd_swap_swap_mk _ _ a₁ b₂ b₁ a₂]
        simp [or_comm]⟩

/--
theorem `gameAdd_iff` / 定理 `gameAdd_iff`

English:
theorem gameAdd_iff
  statement: forall {x y : α × α},
  proof: by
  rintro ⟨_, _⟩ ⟨_, _⟩
  rfl

中文:
定理 gameAdd_iff
  结论: 对任意 {x y : α × α},
  证明: by
  rintro ⟨_, _⟩ ⟨_, _⟩
  rfl
-/
theorem gameAdd_iff : forall {x y : α × α},
    GameAdd rα s(x.1, x.2) s(y.1, y.2) ↔ Prod.GameAdd rα rα x y ∨ Prod.GameAdd rα rα x.swap y := by
  rintro ⟨_, _⟩ ⟨_, _⟩
  rfl

/--
theorem `gameAdd_mk'_iff` / 定理 `gameAdd_mk'_iff`

English:
theorem gameAdd_mk'_iff
  given: {a₁ a₂ b₁ b₂ : α}
  proof: Iff.rfl

中文:
定理 gameAdd_mk'_iff
  条件: {a₁ a₂ b₁ b₂ : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem gameAdd_mk'_iff {a₁ a₂ b₁ b₂ : α} :
    GameAdd rα s(a₁, b₁) s(a₂, b₂) ↔
      Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂) :=
  Iff.rfl

/--
theorem `_root_.Prod.GameAdd.to_sym2` / 定理 `_root_.Prod.GameAdd.to_sym2`

English:
theorem _root_.Prod.GameAdd.to_sym2
  given: {a₁ a₂ b₁ b₂ : α} (h : Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂))
  proof: gameAdd_iff.2 Or.inl h

中文:
定理 _root_.Prod.GameAdd.to_sym2
  条件: {a₁ a₂ b₁ b₂ : α} (h : Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂))
  证明: gameAdd_iff.2 Or.inl h

Depends on / 依赖: Or.inl, gameAdd_iff
-/
theorem _root_.Prod.GameAdd.to_sym2 {a₁ a₂ b₁ b₂ : α} (h : Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂)) :
    Sym2.GameAdd rα s(a₁, b₁) s(a₂, b₂) :=
gameAdd_iff.2 Or.inl h

/--
theorem `GameAdd.fst` / 定理 `GameAdd.fst`

English:
theorem GameAdd.fst
  given: {a₁ a₂ b : α} (h : rα a₁ a₂)
  statement: GameAdd rα s(a₁, b) s(a₂, b)
  proof: (Prod.GameAdd.fst h).to_sym2

中文:
定理 GameAdd.fst
  条件: {a₁ a₂ b : α} (h : rα a₁ a₂)
  结论: GameAdd rα s(a₁, b) s(a₂, b)
  证明: (Prod.GameAdd.fst h).to_sym2

Depends on / 依赖: GameAdd, Prod.GameAdd.fst, to_sym2
-/
theorem GameAdd.fst {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα s(a₁, b) s(a₂, b) :=
  (Prod.GameAdd.fst h).to_sym2

/--
theorem `GameAdd.snd` / 定理 `GameAdd.snd`

English:
theorem GameAdd.snd
  given: {a b₁ b₂ : α} (h : rα b₁ b₂)
  statement: GameAdd rα s(a, b₁) s(a, b₂)
  proof: (Prod.GameAdd.snd h).to_sym2

中文:
定理 GameAdd.snd
  条件: {a b₁ b₂ : α} (h : rα b₁ b₂)
  结论: GameAdd rα s(a, b₁) s(a, b₂)
  证明: (Prod.GameAdd.snd h).to_sym2

Depends on / 依赖: GameAdd, Prod.GameAdd.snd, adicCompletion, to_sym2
-/
theorem GameAdd.snd {a b₁ b₂ : α} (h : rα b₁ b₂) : GameAdd rα s(a, b₁) s(a, b₂) :=
  (Prod.GameAdd.snd h).to_sym2

/--
theorem `GameAdd.fst_snd` / 定理 `GameAdd.fst_snd`

English:
theorem GameAdd.fst_snd
  given: {a₁ a₂ b : α} (h : rα a₁ a₂)
  statement: GameAdd rα s(a₁, b) s(b, a₂)
  proof: by
  rw [Sym2.eq_swap]
  exact GameAdd.snd h

中文:
定理 GameAdd.fst_snd
  条件: {a₁ a₂ b : α} (h : rα a₁ a₂)
  结论: GameAdd rα s(a₁, b) s(b, a₂)
  证明: by
  rw [Sym2.eq_swap]
  exact GameAdd.snd h

Depends on / 依赖: GameAdd, GameAdd.snd, Sym2.eq_swap, eq_swap
-/
theorem GameAdd.fst_snd {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα s(a₁, b) s(b, a₂) := by
  rw [Sym2.eq_swap]
  exact GameAdd.snd h

/--
theorem `GameAdd.snd_fst` / 定理 `GameAdd.snd_fst`

English:
theorem GameAdd.snd_fst
  given: {a₁ a₂ b : α} (h : rα a₁ a₂)
  statement: GameAdd rα s(b, a₁) s(a₂, b)
  proof: by
  rw [Sym2.eq_swap]
  exact GameAdd.fst h

中文:
定理 GameAdd.snd_fst
  条件: {a₁ a₂ b : α} (h : rα a₁ a₂)
  结论: GameAdd rα s(b, a₁) s(a₂, b)
  证明: by
  rw [Sym2.eq_swap]
  exact GameAdd.fst h

Depends on / 依赖: GameAdd, GameAdd.fst, Sym2.eq_swap, eq_swap
-/
theorem GameAdd.snd_fst {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα s(b, a₁) s(a₂, b) := by
  rw [Sym2.eq_swap]
  exact GameAdd.fst h

end Sym2

/--
theorem `Acc.sym2_gameAdd` / 定理 `Acc.sym2_gameAdd`

English:
theorem Acc.sym2_gameAdd
  given: {a b} (ha : Acc rα a) (hb : Acc rα b)
  proof: by
  induction ha generalizing b with | _ a _ iha
  induction hb with | _ b hb ihb
  refine Acc.intro _ fun s => ?_
  induction s with | _ c d
  rw [Sym2.GameAdd]
  dsimp
  rintro ((rc | rd) | (rd | rc))
  · exact iha c rc ⟨b, hb⟩
  · exact ihb d rd
  · rw [Sym2.eq_swap]
    exact iha d rd ⟨b, hb⟩
 

中文:
定理 Acc.sym2_gameAdd
  条件: {a b} (ha : Acc rα a) (hb : Acc rα b)
  证明: by
  induction ha generalizing b with | _ a _ iha
  induction hb with | _ b hb ihb
  refine Acc.intro _ fun s => ?_
  induction s with | _ c d
  rw [Sym2.GameAdd]
  dsimp
  rintro ((rc | rd) | (rd | rc))
  · exact iha c rc ⟨b, hb⟩
  · exact ihb d rd
  · rw [Sym2.eq_swap]
    exact iha d rd ⟨b, hb⟩
 

Depends on / 依赖: Acc.intro, GameAdd, Sym2.GameAdd, Sym2.eq_swap, eq_swap, generalizing
-/
theorem Acc.sym2_gameAdd {a b} (ha : Acc rα a) (hb : Acc rα b) :
    Acc (Sym2.GameAdd rα) s(a, b) := by
  induction ha generalizing b with | _ a _ iha
  induction hb with | _ b hb ihb
  refine Acc.intro _ fun s => ?_
  induction s with | _ c d
  rw [Sym2.GameAdd]
  dsimp
  rintro ((rc | rd) | (rd | rc))
  · exact iha c rc ⟨b, hb⟩
  · exact ihb d rd
  · rw [Sym2.eq_swap]
    exact iha d rd ⟨b, hb⟩
  · rw [Sym2.eq_swap]
    exact ihb c rc

/--
theorem `WellFounded.sym2_gameAdd` / 定理 `WellFounded.sym2_gameAdd`

English:
theorem WellFounded.sym2_gameAdd
  given: (h : WellFounded rα)
  statement: WellFounded (Sym2.GameAdd rα)
  proof: ⟨fun i => Sym2.inductionOn i fun x y => (h.apply x).sym2_gameAdd (h.apply y)⟩

中文:
定理 WellFounded.sym2_gameAdd
  条件: (h : WellFounded rα)
  结论: WellFounded (Sym2.GameAdd rα)
  证明: ⟨fun i => Sym2.inductionOn i fun x y => (h.apply x).sym2_gameAdd (h.apply y)⟩

Depends on / 依赖: Sym2.inductionOn, h.apply, inductionOn, sym2_gameAdd
-/
theorem WellFounded.sym2_gameAdd (h : WellFounded rα) : WellFounded (Sym2.GameAdd rα) :=
  ⟨fun i => Sym2.inductionOn i fun x y => (h.apply x).sym2_gameAdd (h.apply y)⟩

namespace Sym2

attribute [local instance] Sym2.Rel.setoid

/-- Recursion on the well-founded `Sym2.GameAdd` relation. -/
@[elab_as_elim]
/--
Definition of `GameAdd.recursion` / `GameAdd.recursion` 的定义

English:
definition GameAdd.recursion
  signature: {C : α -> α -> Sort*} (hr : WellFounded rα)
  body: @WellFounded.fix (α × α) (fun x => C x.1 x.2)
    (fun x y => Prod.GameAdd rα rα x y ∨ Prod.GameAdd rα rα x.swap y)
    (by simpa [← Sym2.gameAdd_iff] using hr.sym2_gameAdd.onFun)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) (a, b)

@[deprecated (since := "2026-03-13")] alias GameAdd

中文:
定义 GameAdd.recursion
  签名: {C : α -> α -> Sort*} (hr : WellFounded rα)
  定义体: @WellFounded.fix (α × α) (fun x => C x.1 x.2)
    (fun x y => Prod.GameAdd rα rα x y ∨ Prod.GameAdd rα rα x.swap y)
    (by simpa [← Sym2.gameAdd_iff] using hr.sym2_gameAdd.onFun)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) (a, b)

@[deprecated (since := "2026-03-13")] alias GameAdd
-/
def GameAdd.recursion {C : α -> α -> Sort*} (hr : WellFounded rα)
    (IH : forall a₁ b₁, (forall a₂ b₂, Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁) -> C a₂ b₂) -> C a₁ b₁) (a b : α) :
    C a b :=
  @WellFounded.fix (α × α) (fun x => C x.1 x.2)
    (fun x y => Prod.GameAdd rα rα x y ∨ Prod.GameAdd rα rα x.swap y)
    (by simpa [← Sym2.gameAdd_iff] using hr.sym2_gameAdd.onFun)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) (a, b)

@[deprecated (since := "2026-03-13")] alias GameAdd.fix := GameAdd.recursion

/--
theorem `GameAdd.recursion_eq` / 定理 `GameAdd.recursion_eq`

English:
theorem GameAdd.recursion_eq
  statement: {C : α -> α -> Sort*} (hr : WellFounded rα)
  proof: WellFounded.fix_eq ..

@[deprecated (since := "2026-03-13")] alias GameAdd.fix_eq := GameAdd.recursion_eq

中文:
定理 GameAdd.recursion_eq
  结论: {C : α -> α -> Sort*} (hr : WellFounded rα)
  证明: WellFounded.fix_eq ..

@[deprecated (since := "2026-03-13")] alias GameAdd.fix_eq := GameAdd.recursion_eq
-/
theorem GameAdd.recursion_eq {C : α -> α -> Sort*} (hr : WellFounded rα)
    (IH : forall a₁ b₁, (forall a₂ b₂, Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁) -> C a₂ b₂) -> C a₁ b₁) (a b : α) :
    GameAdd.recursion hr IH a b = IH a b fun a' b' _ => GameAdd.recursion hr IH a' b' :=
  WellFounded.fix_eq ..

@[deprecated (since := "2026-03-13")] alias GameAdd.fix_eq := GameAdd.recursion_eq

/-- Induction on the well-founded `Sym2.GameAdd` relation. -/
@[deprecated GameAdd.recursion (since := "2026-03-13")]
/--
theorem `GameAdd.induction` / 定理 `GameAdd.induction`

English:
theorem GameAdd.induction
  given: {C : α -> α -> Prop}
  proof: GameAdd.recursion

中文:
定理 GameAdd.induction
  条件: {C : α -> α -> 命题}
  证明: GameAdd.recursion
-/
theorem GameAdd.induction {C : α -> α -> Prop} :
    WellFounded rα ->
      (forall a₁ b₁, (forall a₂ b₂, Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁) -> C a₂ b₂) -> C a₁ b₁) ->
        forall a b, C a b :=
  GameAdd.recursion

end Sym2
