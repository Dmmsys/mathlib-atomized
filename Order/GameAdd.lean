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

variable {α β : Type*} {rα : α → α → Prop} {rβ : β → β → Prop} {a : α} {b : β}

/-! ### `Prod.GameAdd` -/

namespace Prod

variable (rα rβ)

/-- `Prod.GameAdd rα rβ x y` means that `x` can be reached from `y` by decreasing either entry with
  respect to the relations `rα` and `rβ`.

  It is so called, as it models game addition within combinatorial game theory. If `rα a₁ a₂` means
  that `a₂ ⟶ a₁` is a valid move in game `α`, and `rβ b₁ b₂` means that `b₂ ⟶ b₁` is a valid move
  in game `β`, then `GameAdd rα rβ` specifies the valid moves in the juxtaposition of `α` and `β`:
  the player is free to choose one of the games and make a move in it, while leaving the other game
  unchanged.

  See `Sym2.GameAdd` for the unordered pair analog. -/
/-
**Prod.GameAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 `Prod`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → α → Prop) → (β → β → Prop) → α × β 
→ α × β → Prop
参数：α → α → Prop；β → β → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.GameAdd rα rβ x y` means that `x` can be reached from `y` by decreasing ei
ther entry with
  respect to the relations `rα` and `rβ`.

  It is so called, as it models game addition within combinatorial game theory. 
If `rα a₁ a₂` means
  that `a₂ ⟶ a₁` is a valid move in game `α`, and `rβ b₁ b₂` means that `b₂ ⟶ b₁
` is a valid move
  in game `β`, then `GameAdd rα rβ` specifies the valid moves in the juxtapositi
on of `α` and `β`:
  the player is free to choose one of the games and make a move in it, while lea
ving the other game
  unchanged.

  See `Sym2.GameAdd` for the unordered pair analog.
-/
inductive GameAdd : α × β → α × β → Prop
  | fst {a₁ a₂ b} : rα a₁ a₂ → GameAdd (a₁, b) (a₂, b)
  | snd {a b₁ b₂} : rβ b₁ b₂ → GameAdd (a, b₁) (a, b₂)
/-
**Prod.gameAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：gameAdd_iff {rα rβ} {x y : α × β} : GameAdd rα rβ x y ↔ rα x.1 y.1 ∧ x.2 =
 y.2 ∨ rβ x.2 y.2 ∧ x.1 = y.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem gameAdd_iff {rα rβ} {x y : α × β} :
    GameAdd rα rβ x y ↔ rα x.1 y.1 ∧ x.2 = y.2 ∨ rβ x.2 y.2 ∧ x.1 = y.1 := by
  constructor
  · rintro (@⟨a₁, a₂, b, h⟩ | @⟨a, b₁, b₂, h⟩)
    exacts [Or.inl ⟨h, rfl⟩, Or.inr ⟨h, rfl⟩]
  · revert x y
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨h, rfl : b₁ = b₂⟩ | ⟨h, rfl : a₁ = a₂⟩)
    exacts [GameAdd.fst h, GameAdd.snd h]
/-
**Prod.gameAdd_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：gameAdd_mk_iff {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β} : GameAdd rα rβ (a₁, b₁) (a
₂, b₂) ↔ rα a₁ a₂ ∧ b₁ = b₂ ∨ rβ b₁ b₂ ∧ a₁ = a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.gameAdd_iff`：gameAdd_iff {rα rβ} {x y : α × β} : GameAdd rα rβ x y 
↔ rα x.1 y.1 ∧ x.2 = y.2 ∨ rβ x.2 y.2 ∧ x.1 = y.1
-/
theorem gameAdd_mk_iff {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β} :
    GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ rα a₁ a₂ ∧ b₁ = b₂ ∨ rβ b₁ b₂ ∧ a₁ = a₂ :=
  gameAdd_iff

@[simp]
/-
**Prod.gameAdd_swap_swap** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：gameAdd_swap_swap : forall a b : α × β, GameAdd rβ rα a.swap b.swap ↔ Game
Add rα rβ a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.swap.eq_1`：∀ {α : Type u_1} {β : Type u_2} (p : α × β), p.swap = (p
.2, p.1)
· 使用定理 `Prod.gameAdd_mk_iff`：gameAdd_mk_iff {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β} : Ga
meAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ rα a₁ a₂ ∧ b₁ = b₂ ∨ rβ b₁ b₂ ∧ a₁ = a₂
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem gameAdd_swap_swap : ∀ a b : α × β, GameAdd rβ rα a.swap b.swap ↔ GameAdd rα rβ a b :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => by rw [Prod.swap, Prod.swap, gameAdd_mk_iff, gameAdd_mk_iff, or_comm]
/-
**Prod.gameAdd_swap_swap_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：gameAdd_swap_swap_mk (a₁ a₂ : α) (b₁ b₂ : β) : GameAdd rα rβ (a₁, b₁) (a₂,
 b₂) ↔ GameAdd rβ rα (b₁, a₁) (b₂, a₂)
参数：a₁ a₂ : α；b₁ b₂ : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.gameAdd_swap_swap`：gameAdd_swap_swap : forall a b : α × β, GameAdd 
rβ rα a.swap b.swap ↔ GameAdd rα rβ a b
-/
theorem gameAdd_swap_swap_mk (a₁ a₂ : α) (b₁ b₂ : β) :
    GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ GameAdd rβ rα (b₁, a₁) (b₂, a₂) :=
  gameAdd_swap_swap rβ rα (b₁, a₁) (b₂, a₂)

/-- `Prod.GameAdd` is a subrelation of `Prod.Lex`. -/
/-
**Prod.gameAdd_le_lex** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：gameAdd_le_lex : GameAdd rα rβ <= Prod.Lex rα rβ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.GameAdd` is a subrelation of `Prod.Lex`.
-/
theorem gameAdd_le_lex : GameAdd rα rβ ≤ Prod.Lex rα rβ := fun _ _ h =>
  h.rec (Prod.Lex.left _ _) (Prod.Lex.right _)

/-- `Prod.RProd` is a subrelation of the transitive closure of `Prod.GameAdd`. -/
/-
**Prod.rprod_le_transGen_gameAdd** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (rα : α → α → Prop) (rβ : β → β → Prop),  
 Prod.RProd rα rβ ≤ Relation.TransGen (Prod.GameAdd rα rβ)
参数：rα : α → α → Prop；rβ : β → β → Prop；Prod.GameAdd rα rβ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.RProd` is a subrelation of the transitive closure of `Prod.GameAdd`.
-/
theorem rprod_le_transGen_gameAdd : RProd rα rβ ≤ Relation.TransGen (GameAdd rα rβ)
  | _, _, h => h.rec (by
      intro _ _ _ _ hα hβ
      exact Relation.TransGen.tail (Relation.TransGen.single <| GameAdd.fst hα) (GameAdd.snd hβ))

end Prod

/-- If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` is
  accessible under `Prod.GameAdd rα rβ`. Notice that `Prod.lexAccessible` requires the
  stronger condition `∀ b, Acc rβ b`. -/
/-
**Acc.prod_gameAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Acc.prod_gameAdd (ha : Acc rα a) (hb : Acc rβ b) : Acc (Prod.GameAdd rα rβ
) (a, b)
参数：ha : Acc rα a；hb : Acc rβ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` 
is
  accessible under `Prod.GameAdd rα rβ`. Notice that `Prod.lexAccessible` requir
es the
  stronger condition `∀ b, Acc rβ b`.
-/
theorem Acc.prod_gameAdd (ha : Acc rα a) (hb : Acc rβ b) :
    Acc (Prod.GameAdd rα rβ) (a, b) := by
  induction ha generalizing b with | _ a _ iha
  induction hb with | _ b hb ihb
  refine Acc.intro _ fun h => ?_
  rintro (⟨ra⟩ | ⟨rb⟩)
  exacts [iha _ ra (Acc.intro b hb), ihb _ rb]

/-- The `Prod.GameAdd` relation on well-founded inputs is well-founded.

  In particular, the sum of two well-founded games is well-founded. -/
/-
**WellFounded.prod_gameAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.prod_gameAdd (hα : WellFounded rα) (hβ : WellFounded rβ) : Wel
lFounded (Prod.GameAdd rα rβ)
参数：hα : WellFounded rα；hβ : WellFounded rβ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.prod_gameAdd`：Acc.prod_gameAdd (ha : Acc rα a) (hb : Acc rβ b) : Acc
 (Prod.GameAdd rα rβ) (a, b)
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a

--- 原说明 ---
The `Prod.GameAdd` relation on well-founded inputs is well-founded.

  In particular, the sum of two well-founded games is well-founded.
-/
theorem WellFounded.prod_gameAdd (hα : WellFounded rα) (hβ : WellFounded rβ) :
    WellFounded (Prod.GameAdd rα rβ) :=
  ⟨fun ⟨a, b⟩ => (hα.apply a).prod_gameAdd (hβ.apply b)⟩

namespace Prod

/-- Recursion on the well-founded `Prod.GameAdd` relation.
  Note that it's strictly more general to recurse on the lexicographic order instead. -/
@[elab_as_elim]
/-
**Prod.GameAdd.recursion** 是 Mathlib 中的一个定义，位于命名空间 `Prod.GameAdd`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {rα : α → α → Prop} →       {rβ : 
β → β → Prop} →         {C : α → β → Sort u_3} →           WellFounded rα →     
        WellFounded rβ →               ((a₁ : α) → (b₁ : β) → ((a₂ : α) → (b₂ : 
β) → Prod.GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) →               
  (a : α) → (b : β) → C a b
参数：(a₁ : α) → (b₁ : β) → ((a₂ : α) → (b₂ : β) → Prod.GameAdd rα rβ (a₂, b₂) (a₁,
 b₁) → C a₂ b₂) → C a₁ b₁；a : α；b : β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.prod_gameAdd`：WellFounded.prod_gameAdd (hα : WellFounded rα)
 (hβ : WellFounded rβ) : WellFounded (Prod.GameAdd rα rβ)

--- 原说明 ---
Recursion on the well-founded `Prod.GameAdd` relation.
  Note that it's strictly more general to recurse on the lexicographic order ins
tead.
-/
def GameAdd.recursion {C : α → β → Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
    C a b :=
  @WellFounded.fix (α × β) (fun x => C x.1 x.2) _ (hα.prod_gameAdd hβ)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) ⟨a, b⟩

@[deprecated (since := "2026-03-13")] alias GameAdd.fix := GameAdd.recursion
/-
**Prod.GameAdd.recursion_eq** 是 Mathlib 中的一个定理，位于命名空间 `Prod.GameAdd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {rα : α → α → Prop} {rβ : β → β → Prop} {C
 : α → β → Sort u_3} (hα : WellFounded rα)   (hβ : WellFounded rβ)   (IH : (a₁ :
 α) → (b₁ : β) → ((a₂ : α) → (b₂ : β) → Prod.GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C
 a₂ b₂) → C a₁ b₁) (a : α)   (b : β), Prod.GameAdd.recursion hα hβ IH a b = IH a
 b fun a' b' x => Prod.GameAdd.recursion hα hβ IH a' b'
参数：hα : WellFounded rα；hβ : WellFounded rβ；IH : (a₁ : α) → (b₁ : β) → ((a₂ : α) 
→ (b₂ : β) → Prod.GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁；a : α；b :
 β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.fix_eq`：∀ {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (
hwf : WellFounded r) (F : (x : α) → ((y : α) → r y x → C y) → C x)   (x : α), hw
f.fix F …
· 使用定理 `WellFounded.prod_gameAdd`：WellFounded.prod_gameAdd (hα : WellFounded rα)
 (hβ : WellFounded rβ) : WellFounded (Prod.GameAdd rα rβ)
-/
theorem GameAdd.recursion_eq {C : α → β → Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
    GameAdd.recursion hα hβ IH a b = IH a b fun a' b' _ => GameAdd.recursion hα hβ IH a' b' :=
  WellFounded.fix_eq _ _ _

@[deprecated (since := "2026-03-13")] alias GameAdd.fix_eq := GameAdd.recursion_eq

/-- Induction on the well-founded `Prod.GameAdd` relation.
  Note that it's strictly more general to induct on the lexicographic order instead. -/
@[deprecated GameAdd.recursion (since := "2026-03-13")]
/-
**Prod.GameAdd.induction** 是 Mathlib 中的一个定理，位于命名空间 `Prod.GameAdd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {rα : α → α → Prop} {rβ : β → β → Prop} {C
 : α → β → Prop},   WellFounded rα →     WellFounded rβ →       (∀ (a₁ : α) (b₁ 
: β), (∀ (a₂ : α) (b₂ : β), Prod.GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C 
a₁ b₁) →         ∀ (a : α) (b : β), C a b
参数：∀ (a₁ : α) (b₁ : β), (∀ (a₂ : α) (b₂ : β), Prod.GameAdd rα rβ (a₂, b₂) (a₁, b
₁) → C a₂ b₂) → C a₁ b₁；a : α；b : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction on the well-founded `Prod.GameAdd` relation.
  Note that it's strictly more general to induct on the lexicographic order inst
ead.
-/
theorem GameAdd.induction {C : α → β → Prop} :
    WellFounded rα →
      WellFounded rβ →
        (∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) → ∀ a b, C a b :=
  GameAdd.recursion

end Prod

/-! ### `Sym2.GameAdd` -/

namespace Sym2

/-- `Sym2.GameAdd rα x y` means that `x` can be reached from `y` by decreasing either entry with
  respect to the relation `rα`.

  See `Prod.GameAdd` for the ordered pair analog. -/
/-
**Sym2.GameAdd** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：GameAdd (rα : α -> α -> Prop) : Sym2 α -> Sym2 α -> Prop
参数：rα : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sym2.GameAdd rα x y` means that `x` can be reached from `y` by decreasing eithe
r entry with
  respect to the relation `rα`.

  See `Prod.GameAdd` for the ordered pair analog.
-/
def GameAdd (rα : α → α → Prop) : Sym2 α → Sym2 α → Prop :=
  Sym2.lift₂
    ⟨fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂),
      fun a₁ b₁ a₂ b₂ => by
        dsimp
        rw [Prod.gameAdd_swap_swap_mk _ _ b₁ b₂ a₁ a₂, Prod.gameAdd_swap_swap_mk _ _ a₁ b₂ b₁ a₂]
        simp [or_comm]⟩
/-
**Sym2.gameAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：gameAdd_iff : forall {x y : α × α}, GameAdd rα s(x.1, x.2) s(y.1, y.2) ↔ P
rod.GameAdd rα rα x y ∨ Prod.GameAdd rα rα x.swap y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem gameAdd_iff : ∀ {x y : α × α},
    GameAdd rα s(x.1, x.2) s(y.1, y.2) ↔ Prod.GameAdd rα rα x y ∨ Prod.GameAdd rα rα x.swap y := by
  rintro ⟨_, _⟩ ⟨_, _⟩
  rfl
/-
**Sym2.gameAdd_mk'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b₁ b₂ : α},   Sym2.GameAdd rα 
s(a₁, b₁) s(a₂, b₂) ↔ Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα 
(b₁, a₁) (a₂, b₂)
参数：a₁, b₁；a₂, b₂；a₁, b₁；a₂, b₂；b₁, a₁；a₂, b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem gameAdd_mk'_iff {a₁ a₂ b₁ b₂ : α} :
    GameAdd rα s(a₁, b₁) s(a₂, b₂) ↔
      Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂) :=
  Iff.rfl
/-
**Sym2._root_.Prod.GameAdd.to_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Prod.GameAdd.to_sym2 {a₁ a₂ b₁ b₂ : α} (h : Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂)) :
    Sym2.GameAdd rα s(a₁, b₁) s(a₂, b₂) :=
  gameAdd_iff.2 <| Or.inl <| h
/-
**Sym2.GameAdd.fst** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.GameAdd`。
形式化陈述：∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b : α}, rα a₁ a₂ → Sym2.GameAd
d rα s(a₁, b) s(a₂, b)
参数：a₁, b；a₂, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.GameAdd.to_sym2`：∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b₁ b₂ 
: α},   Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) → Sym2.GameAdd rα s(a₁, b₁) s(a₂, b
₂)
-/
theorem GameAdd.fst {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα s(a₁, b) s(a₂, b) :=
  (Prod.GameAdd.fst h).to_sym2
/-
**Sym2.GameAdd.snd** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.GameAdd`。
形式化陈述：∀ {α : Type u_1} {rα : α → α → Prop} {a b₁ b₂ : α}, rα b₁ b₂ → Sym2.GameAd
d rα s(a, b₁) s(a, b₂)
参数：a, b₁；a, b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.GameAdd.to_sym2`：∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b₁ b₂ 
: α},   Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) → Sym2.GameAdd rα s(a₁, b₁) s(a₂, b
₂)
-/
theorem GameAdd.snd {a b₁ b₂ : α} (h : rα b₁ b₂) : GameAdd rα s(a, b₁) s(a, b₂) :=
  (Prod.GameAdd.snd h).to_sym2
/-
**Sym2.GameAdd.fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.GameAdd`。
形式化陈述：∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b : α}, rα a₁ a₂ → Sym2.GameAd
d rα s(a₁, b) s(b, a₂)
参数：a₁, b；b, a₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `Sym2.GameAdd.snd`：∀ {α : Type u_1} {rα : α → α → Prop} {a b₁ b₂ : α}, rα
 b₁ b₂ → Sym2.GameAdd rα s(a, b₁) s(a, b₂)
-/
theorem GameAdd.fst_snd {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα s(a₁, b) s(b, a₂) := by
  rw [Sym2.eq_swap]
  exact GameAdd.snd h
/-
**Sym2.GameAdd.snd_fst** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.GameAdd`。
形式化陈述：∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b : α}, rα a₁ a₂ → Sym2.GameAd
d rα s(b, a₁) s(a₂, b)
参数：b, a₁；a₂, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `Sym2.GameAdd.fst`：∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b : α}, rα
 a₁ a₂ → Sym2.GameAdd rα s(a₁, b) s(a₂, b)
-/
theorem GameAdd.snd_fst {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα s(b, a₁) s(a₂, b) := by
  rw [Sym2.eq_swap]
  exact GameAdd.fst h

end Sym2

/-
**Acc.sym2_gameAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Acc.sym2_gameAdd {a b} (ha : Acc rα a) (hb : Acc rα b) : Acc (Sym2.GameAdd
 rα) s(a, b)
参数：ha : Acc rα a；hb : Acc rα b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.GameAdd.eq_1`：∀ {α : Type u_1} (rα : α → α → Prop),   Sym2.GameAdd 
rα =     Sym2.lift₂ ⟨fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ P
rod.Gam…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
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

/-- The `Sym2.GameAdd` relation on well-founded inputs is well-founded. -/
/-
**WellFounded.sym2_gameAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.sym2_gameAdd (h : WellFounded rα) : WellFounded (Sym2.GameAdd 
rα)
参数：h : WellFounded rα。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.inductionOn`：∀ {α : Type u_1} {f : Sym2 α → Prop} (i : Sym2 α), (∀ 
(x y : α), f s(x, y)) → f i
· 使用定理 `Acc.sym2_gameAdd`：Acc.sym2_gameAdd {a b} (ha : Acc rα a) (hb : Acc rα b)
 : Acc (Sym2.GameAdd rα) s(a, b)
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a

--- 原说明 ---
The `Sym2.GameAdd` relation on well-founded inputs is well-founded.
-/
theorem WellFounded.sym2_gameAdd (h : WellFounded rα) : WellFounded (Sym2.GameAdd rα) :=
  ⟨fun i => Sym2.inductionOn i fun x y => (h.apply x).sym2_gameAdd (h.apply y)⟩

namespace Sym2

attribute [local instance] Sym2.Rel.setoid

/-- Recursion on the well-founded `Sym2.GameAdd` relation. -/
@[elab_as_elim]
/-
**Sym2.GameAdd.recursion** 是 Mathlib 中的一个定义，位于命名空间 `Sym2.GameAdd`。
形式化陈述：{α : Type u_1} →   {rα : α → α → Prop} →     {C : α → α → Sort u_3} →     
  WellFounded rα →         ((a₁ b₁ : α) → ((a₂ b₂ : α) → Sym2.GameAdd rα s(a₂, b
₂) s(a₁, b₁) → C a₂ b₂) → C a₁ b₁) → (a b : α) → C a b
参数：(a₁ b₁ : α) → ((a₂ b₂ : α) → Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁) → C a₂ b₂) →
 C a₁ b₁；a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion on the well-founded `Sym2.GameAdd` relation.
-/
def GameAdd.recursion {C : α → α → Sort*} (hr : WellFounded rα)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a b : α) :
    C a b :=
  @WellFounded.fix (α × α) (fun x => C x.1 x.2)
    (fun x y ↦ Prod.GameAdd rα rα x y ∨ Prod.GameAdd rα rα x.swap y)
    (by simpa [← Sym2.gameAdd_iff] using hr.sym2_gameAdd.onFun)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) (a, b)

@[deprecated (since := "2026-03-13")] alias GameAdd.fix := GameAdd.recursion
/-
**Sym2.GameAdd.recursion_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.GameAdd`。
形式化陈述：∀ {α : Type u_1} {rα : α → α → Prop} {C : α → α → Sort u_3} (hr : WellFoun
ded rα)   (IH : (a₁ b₁ : α) → ((a₂ b₂ : α) → Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁)
 → C a₂ b₂) → C a₁ b₁) (a b : α),   Sym2.GameAdd.recursion hr IH a b = IH a b fu
n a' b' x => Sym2.GameAdd.recursion hr IH a' b'
参数：hr : WellFounded rα；IH : (a₁ b₁ : α) → ((a₂ b₂ : α) → Sym2.GameAdd rα s(a₂, b
₂) s(a₁, b₁) → C a₂ b₂) → C a₁ b₁；a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.fix_eq`：∀ {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (
hwf : WellFounded r) (F : (x : α) → ((y : α) → r y x → C y) → C x)   (x : α), hw
f.fix F …
-/
theorem GameAdd.recursion_eq {C : α → α → Sort*} (hr : WellFounded rα)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a b : α) :
    GameAdd.recursion hr IH a b = IH a b fun a' b' _ => GameAdd.recursion hr IH a' b' :=
  WellFounded.fix_eq ..

@[deprecated (since := "2026-03-13")] alias GameAdd.fix_eq := GameAdd.recursion_eq

/-- Induction on the well-founded `Sym2.GameAdd` relation. -/
@[deprecated GameAdd.recursion (since := "2026-03-13")]
/-
**Sym2.GameAdd.induction** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.GameAdd`。
形式化陈述：∀ {α : Type u_1} {rα C : α → α → Prop},   WellFounded rα →     (∀ (a₁ b₁ :
 α), (∀ (a₂ b₂ : α), Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁) → C a₂ b₂) → C a₁ b₁) →
 ∀ (a b : α), C a b
参数：∀ (a₁ b₁ : α), (∀ (a₂ b₂ : α), Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁) → C a₂ b₂)
 → C a₁ b₁；a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction on the well-founded `Sym2.GameAdd` relation.
-/
theorem GameAdd.induction {C : α → α → Prop} :
    WellFounded rα →
      (∀ a₁ b₁, (∀ a₂ b₂, Sym2.GameAdd rα s(a₂, b₂) s(a₁, b₁) → C a₂ b₂) → C a₁ b₁) →
        ∀ a b, C a b :=
  GameAdd.recursion

end Sym2

