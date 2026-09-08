/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.List.Chain
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Free groups

This file defines free groups over a type. Furthermore, it is shown that the free group construction
is an instance of a monad. For the result that `FreeGroup` is the left adjoint to the forgetful
functor from groups to types, see `Mathlib/Algebra/Category/Grp/Adjunctions.lean`.

## Main definitions

* `FreeGroup`/`FreeAddGroup`: the free group (resp. free additive group) associated to a type
  `α` defined as the words over `a : α × Bool` modulo the relation `a * x * x⁻¹ * b = a * b`.
* `FreeGroup.mk`/`FreeAddGroup.mk`: the canonical quotient map `List (α × Bool) → FreeGroup α`.
* `FreeGroup.of`/`FreeAddGroup.of`: the canonical injection `α → FreeGroup α`.
* `FreeGroup.lift f`/`FreeAddGroup.lift`: the canonical group homomorphism `FreeGroup α →* G`
  given a group `G` and a function `f : α → G`.

## Main statements

* `FreeGroup.Red.church_rosser`/`FreeAddGroup.Red.church_rosser`: The Church-Rosser theorem for word
  reduction (also known as Newman's diamond lemma).
* `FreeGroup.freeGroupUnitEquivInt`: The free group over the one-point type
  is isomorphic to the integers.
* The free group construction is an instance of a monad.

## Implementation details

First we introduce the one step reduction relation `FreeGroup.Red.Step`:
`w * x * x⁻¹ * v   ~>   w * v`, its reflexive transitive closure `FreeGroup.Red.trans`
and prove that its join is an equivalence relation. Then we introduce `FreeGroup α` as a quotient
over `FreeGroup.Red.Step`.

For the additive version we introduce the same relation under a different name so that we can
distinguish the quotient types more easily.


## Tags

free group, Newman's diamond lemma, Church-Rosser theorem
-/

@[expose] public section

open Relation
open scoped List

universe u v w

variable {α : Type u}

attribute [local simp] List.append_eq_has_append

/- Ensure that `@[to_additive]` uses the right namespace before the definition of `FreeGroup`. -/
insert_to_additive_translation FreeGroup FreeAddGroup

/-- Reduction step for the additive free group relation: `w + x + (-x) + v ~> w + v` -/
/-
**FreeAddGroup.Red.Step** 是 Mathlib 中的一个归纳类型，位于命名空间 `FreeAddGroup.Red`。
形式化陈述：{α : Type u} → List (α × Bool) → List (α × Bool) → Prop
参数：α × Bool；α × Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reduction step for the additive free group relation: `w + x + (-x) + v ~> w + v`
-/
inductive FreeAddGroup.Red.Step : List (α × Bool) → List (α × Bool) → Prop
  | not {L₁ L₂ x b} : FreeAddGroup.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)

attribute [simp] FreeAddGroup.Red.Step.not

/-- Reduction step for the multiplicative free group relation: `w * x * x⁻¹ * v ~> w * v` -/
@[to_additive]
/-
**FreeGroup.Red.Step** 是 Mathlib 中的一个归纳类型，位于命名空间 `FreeGroup.Red`。
形式化陈述：{α : Type u} → List (α × Bool) → List (α × Bool) → Prop
参数：α × Bool；α × Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reduction step for the multiplicative free group relation: `w * x * x⁻¹ * v ~> w
 * v`
-/
inductive FreeGroup.Red.Step : List (α × Bool) → List (α × Bool) → Prop
  | not {L₁ L₂ x b} : FreeGroup.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)

attribute [simp] FreeGroup.Red.Step.not

namespace FreeGroup

variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

/-- Reflexive-transitive closure of `Red.Step` -/
@[to_additive /-- Reflexive-transitive closure of `Red.Step` -/]
/-
**FreeGroup.Red** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：Red : List (α × Bool) -> List (α × Bool) -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reflexive-transitive closure of `Red.Step`
-/
def Red : List (α × Bool) → List (α × Bool) → Prop :=
  ReflTransGen Red.Step

@[to_additive (attr := refl)]
/-
**FreeGroup.Red.refl** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u} {L : List (α × Bool)}, FreeGroup.Red L L
参数：α × Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Red.refl : Red L L :=
  ReflTransGen.refl

@[to_additive (attr := trans)]
/-
**FreeGroup.Red.trans** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u} {L₁ L₂ L₃ : List (α × Bool)}, FreeGroup.Red L₁ L₂ → FreeGro
up.Red L₂ L₃ → FreeGroup.Red L₁ L₃
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.trans`：trans (hab : ReflTransGen r a b) (hbc : Ref
lTransGen r b c) : ReflTransGen r a c
-/
theorem Red.trans : Red L₁ L₂ → Red L₂ L₃ → Red L₁ L₃ :=
  ReflTransGen.trans

namespace Red

/-- Predicate asserting that the word `w₁` can be reduced to `w₂` in one step, i.e. there are words
`w₃ w₄` and letter `x` such that `w₁ = w₃xx⁻¹w₄` and `w₂ = w₃w₄` -/
@[to_additive /-- Predicate asserting that the word `w₁` can be reduced to `w₂` in one step, i.e.
there are words `w₃ w₄` and letter `x` such that `w₁ = w₃ + x + (-x) + w₄` and `w₂ = w₃w₄` -/]
/-
**FreeGroup.Red.Step.length** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup.Red.Step L₁ L₂ → L₂.le
ngth + 2 = L₁.length
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
-/
theorem Step.length : ∀ {L₁ L₂ : List (α × Bool)}, Step L₁ L₂ → L₂.length + 2 = L₁.length
  | _, _, @Red.Step.not _ L1 L2 x b => by rw [List.length_append, List.length_append]; rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.Red.Step.not_rev** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} {x : α} {b : Bool},   FreeGroup.R
ed.Step (L₁ ++ (x, !b) :: (x, b) :: L₂) (L₁ ++ L₂)
参数：α × Bool；L₁ ++ (x, !b) :: (x, b) :: L₂；L₁ ++ L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Step.not_rev {x b} : Step (L₁ ++ (x, !b) :: (x, b) :: L₂) (L₁ ++ L₂) := by
  cases b <;> exact Step.not

@[to_additive (attr := simp)]
/-
**FreeGroup.Red.Step.cons_not** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L : List (α × Bool)} {x : α} {b : Bool}, FreeGroup.Red.Ste
p ((x, b) :: (x, !b) :: L) L
参数：α × Bool；(x, b) :: (x, !b) :: L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Step.cons_not {x b} : Red.Step ((x, b) :: (x, !b) :: L) L :=
  @Step.not _ [] _ _ _

@[to_additive (attr := simp)]
/-
**FreeGroup.Red.Step.cons_not_rev** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`
。
形式化陈述：∀ {α : Type u} {L : List (α × Bool)} {x : α} {b : Bool}, FreeGroup.Red.Ste
p ((x, !b) :: (x, b) :: L) L
参数：α × Bool；(x, !b) :: (x, b) :: L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.Step.not_rev`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} {x 
: α} {b : Bool},   FreeGroup.Red.Step (L₁ ++ (x, !b) :: (x, b) :: L₂) (L₁ ++ L₂)
-/
theorem Step.cons_not_rev {x b} : Red.Step ((x, !b) :: (x, b) :: L) L :=
  @Red.Step.not_rev _ [] _ _ _

@[to_additive]
/-
**FreeGroup.Red.Step.append_left** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ L₃ : List (α × Bool)}, FreeGroup.Red.Step L₂ L₃ → Fr
eeGroup.Red.Step (L₁ ++ L₂) (L₁ ++ L₃)
参数：α × Bool；L₁ ++ L₂；L₁ ++ L₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
-/
theorem Step.append_left : ∀ {L₁ L₂ L₃ : List (α × Bool)}, Step L₂ L₃ → Step (L₁ ++ L₂) (L₁ ++ L₃)
  | _, _, _, Red.Step.not => by rw [← List.append_assoc, ← List.append_assoc]; constructor

@[to_additive]
/-
**FreeGroup.Red.Step.cons** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} {x : α × Bool},   FreeGroup.Red.S
tep L₁ L₂ → FreeGroup.Red.Step (x :: L₁) (x :: L₂)
参数：α × Bool；x :: L₁；x :: L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.Step.append_left`：∀ {α : Type u} {L₁ L₂ L₃ : List (α × Boo
l)}, FreeGroup.Red.Step L₂ L₃ → FreeGroup.Red.Step (L₁ ++ L₂) (L₁ ++ L₃)
-/
theorem Step.cons {x} (H : Red.Step L₁ L₂) : Red.Step (x :: L₁) (x :: L₂) :=
  @Step.append_left _ [x] _ _ H

@[to_additive]
/-
**FreeGroup.Red.Step.append_right** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`
。
形式化陈述：∀ {α : Type u} {L₁ L₂ L₃ : List (α × Bool)}, FreeGroup.Red.Step L₁ L₂ → Fr
eeGroup.Red.Step (L₁ ++ L₃) (L₂ ++ L₃)
参数：α × Bool；L₁ ++ L₃；L₂ ++ L₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
-/
theorem Step.append_right : ∀ {L₁ L₂ L₃ : List (α × Bool)}, Step L₁ L₂ → Step (L₁ ++ L₃) (L₂ ++ L₃)
  | _, _, _, Red.Step.not => by simp

@[to_additive]
/-
**FreeGroup.Red.not_step_nil** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：not_step_nil : ¬Step [] L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem not_step_nil : ¬Step [] L := by
  generalize h' : [] = L'
  intro h
  rcases h with - | ⟨L₁, L₂⟩
  simp at h'

@[to_additive]
/-
**FreeGroup.Red.Step.cons_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step
`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} {a : α} {b : Bool},   FreeGroup.R
ed.Step ((a, b) :: L₁) L₂ ↔ (∃ L, FreeGroup.Red.Step L₁ L ∧ L₂ = (a, b) :: L) ∨ 
L₁ = (a, !b) :: L₂
参数：α × Bool；(a, b) :: L₁；∃ L, FreeGroup.Red.Step L₁ L ∧ L₂ = (a, b) :: L；a, !b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.Red.Step.cons`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} {x : α
 × Bool},   FreeGroup.Red.Step L₁ L₂ → FreeGroup.Red.Step (x :: L₁) (x :: L₂)
· 使用定理 `FreeGroup.Red.Step.cons_not`：∀ {α : Type u} {L : List (α × Bool)} {x : α
} {b : Bool}, FreeGroup.Red.Step ((x, b) :: (x, !b) :: L) L
-/
theorem Step.cons_left_iff {a : α} {b : Bool} :
    Step ((a, b) :: L₁) L₂ ↔ (∃ L, Step L₁ L ∧ L₂ = (a, b) :: L) ∨ L₁ = (a, ! b) :: L₂ := by
  constructor
  · generalize hL : ((a, b) :: L₁ : List _) = L
    rintro @⟨_ | ⟨p, s'⟩, e, a', b'⟩ <;> simp_all
  · rintro (⟨L, h, rfl⟩ | rfl)
    · exact Step.cons h
    · exact Step.cons_not

@[to_additive]
/-
**FreeGroup.Red.not_step_singleton** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u} {L : List (α × Bool)} {p : α × Bool}, ¬FreeGroup.Red.Step [
p] L
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_step_singleton : ∀ {p : α × Bool}, ¬Step [p] L
  | (a, b) => by simp [Step.cons_left_iff, not_step_nil]

@[to_additive]
/-
**FreeGroup.Red.Step.cons_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step
`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} {p : α × Bool},   FreeGroup.Red.S
tep (p :: L₁) (p :: L₂) ↔ FreeGroup.Red.Step L₁ L₂
参数：α × Bool；p :: L₁；p :: L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem Step.cons_cons_iff : ∀ {p : α × Bool}, Step (p :: L₁) (p :: L₂) ↔ Step L₁ L₂ := by
  simp +contextual [Step.cons_left_iff, iff_def, or_imp]

@[to_additive]
/-
**FreeGroup.Red.Step.append_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.St
ep`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} (L : List (α × Bool)),   FreeGrou
p.Red.Step (L ++ L₁) (L ++ L₂) ↔ FreeGroup.Red.Step L₁ L₂
参数：α × Bool；L : List (α × Bool)；L ++ L₁；L ++ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Step.append_left_iff : ∀ L, Step (L ++ L₁) (L ++ L₂) ↔ Step L₁ L₂
  | [] => by simp
  | p :: l => by simp [Step.append_left_iff l, Step.cons_cons_iff]

@[to_additive]
/-
**FreeGroup.Red.Step.diamond_aux** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ L₃ L₄ : List (α × Bool)} {x1 : α} {b1 : Bool} {x2 : 
α} {b2 : Bool},   L₁ ++ (x1, b1) :: (x1, !b1) :: L₂ = L₃ ++ (x2, b2) :: (x2, !b2
) :: L₄ →     L₁ ++ L₂ = L₃ ++ L₄ ∨ ∃ L₅, FreeGroup.Red.Step (L₁ ++ L₂) L₅ ∧ Fre
eGroup.Red.Step (L₃ ++ L₄) L₅
参数：α × Bool；x1, b1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Step.diamond_aux :
    ∀ {L₁ L₂ L₃ L₄ : List (α × Bool)} {x1 b1 x2 b2},
      L₁ ++ (x1, b1) :: (x1, !b1) :: L₂ = L₃ ++ (x2, b2) :: (x2, !b2) :: L₄ →
        L₁ ++ L₂ = L₃ ++ L₄ ∨ ∃ L₅, Red.Step (L₁ ++ L₂) L₅ ∧ Red.Step (L₃ ++ L₄) L₅
  | [], _, [], _, _, _, _, _, H => by injections; subst_vars; simp
  | [], _, [(x3, b3)], _, _, _, _, _, H => by injections; subst_vars; simp
  | [(x3, b3)], _, [], _, _, _, _, _, H => by injections; subst_vars; simp
  | [], _, (x3, b3) :: (x4, b4) :: tl, _, _, _, _, _, H => by
    injections; subst_vars; right; exact ⟨_, Red.Step.not, Red.Step.cons_not⟩
  | (x3, b3) :: (x4, b4) :: tl, _, [], _, _, _, _, _, H => by
    injections; subst_vars; right; simpa using ⟨_, Red.Step.cons_not, Red.Step.not⟩
  | (x3, b3) :: tl, _, (x4, b4) :: tl2, _, _, _, _, _, H =>
    let ⟨H1, H2⟩ := List.cons.inj H
    match Step.diamond_aux H2 with
    | Or.inl H3 => Or.inl <| by simp [H1, H3]
    | Or.inr ⟨L₅, H3, H4⟩ => Or.inr ⟨_, Step.cons H3, by simpa [H1] using Step.cons H4⟩

@[to_additive]
/-
**FreeGroup.Red.Step.diamond** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ L₃ L₄ : List (α × Bool)},   FreeGroup.Red.Step L₁ L₃
 →     FreeGroup.Red.Step L₂ L₄ → L₁ = L₂ → L₃ = L₄ ∨ ∃ L₅, FreeGroup.Red.Step L
₃ L₅ ∧ FreeGroup.Red.Step L₄ L₅
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.Step.diamond_aux`：∀ {α : Type u} {L₁ L₂ L₃ L₄ : List (α × 
Bool)} {x1 : α} {b1 : Bool} {x2 : α} {b2 : Bool},   L₁ ++ (x1, b1) :: (x1, !b1) 
:: L₂ = L₃ ++ (x2, b…
-/
theorem Step.diamond :
    ∀ {L₁ L₂ L₃ L₄ : List (α × Bool)},
      Red.Step L₁ L₃ → Red.Step L₂ L₄ → L₁ = L₂ → L₃ = L₄ ∨ ∃ L₅, Red.Step L₃ L₅ ∧ Red.Step L₄ L₅
  | _, _, _, _, Red.Step.not, Red.Step.not, H => Step.diamond_aux H

@[to_additive]
/-
**FreeGroup.Red.Step.to_red** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup.Red.Step L₁ L₂ → FreeG
roup.Red L₁ L₂
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
-/
theorem Step.to_red : Step L₁ L₂ → Red L₁ L₂ :=
  ReflTransGen.single

/-- **Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
respectively. This is also known as Newman's diamond lemma. -/
@[to_additive
  /-- **Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
  to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
  respectively. This is also known as Newman's diamond lemma. -/]
/-
**FreeGroup.Red.church_rosser** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：church_rosser : Red L₁ L₂ -> Red L₁ L₃ -> Join Red L₂ L₃
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.church_rosser`：church_rosser (h : forall a b c, r a b -> r a c 
-> exists d, ReflGen r b d ∧ ReflTransGen r c d) (hab : ReflTransGen r a b) (hac
 : ReflTrans…
· 使用定理 `FreeGroup.Red.Step.diamond`：∀ {α : Type u} {L₁ L₂ L₃ L₄ : List (α × Bool
)},   FreeGroup.Red.Step L₁ L₃ →     FreeGroup.Red.Step L₂ L₄ → L₁ = L₂ → L₃ = L
₄ ∨ ∃ L₅, FreeGr…
· 使用定理 `FreeGroup.Red.Step.to_red`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, Fre
eGroup.Red.Step L₁ L₂ → FreeGroup.Red L₁ L₂
-/
theorem church_rosser : Red L₁ L₂ → Red L₁ L₃ → Join Red L₂ L₃ :=
  Relation.church_rosser fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, hcd.to_red⟩

@[to_additive]
/-
**FreeGroup.Red.cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：cons_cons {p} : Red L₁ L₂ -> Red (p :: L₁) (p :: L₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.ReflT
ransGen r ≤ Func…
· 使用定理 `FreeGroup.Red.Step.cons`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} {x : α
 × Bool},   FreeGroup.Red.Step L₁ L₂ → FreeGroup.Red.Step (x :: L₁) (x :: L₂)
-/
theorem cons_cons {p} : Red L₁ L₂ → Red (p :: L₁) (p :: L₂) :=
  ReflTransGen.lift (List.cons p) (fun _ _ => Step.cons) L₁ L₂

@[to_additive]
/-
**FreeGroup.Red.cons_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：cons_cons_iff (p) : Red (p :: L₁) (p :: L₂) ↔ Red L₁ L₂
参数：p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.head_induction_on`：head_induction_on {motive : for
all a : α, ReflTransGen r a b -> Prop} {a : α} (h : ReflTransGen r a b) (refl : 
motive b refl) (head : forall…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.Red.Step.cons_left_iff`：∀ {α : Type u} {L₁ L₂ : List (α × Bool
)} {a : α} {b : Bool},   FreeGroup.Red.Step ((a, b) :: L₁) L₂ ↔ (∃ L, FreeGroup.
Red.Step L₁ L ∧ L₂ = (…
· 使用定理 `Relation.ReflTransGen.head`：head (hab : r a b) (hbc : ReflTransGen r b c
) : ReflTransGen r a c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.Red.cons_cons`：cons_cons {p} : Red L₁ L₂ -> Red (p :: L₁) (p :
: L₂)
· 使用定理 `FreeGroup.Red.Step.cons_not_rev`：∀ {α : Type u} {L : List (α × Bool)} {x
 : α} {b : Bool}, FreeGroup.Red.Step ((x, !b) :: (x, b) :: L) L
-/
theorem cons_cons_iff (p) : Red (p :: L₁) (p :: L₂) ↔ Red L₁ L₂ :=
  Iff.intro
    (by
      generalize eq₁ : (p :: L₁ : List _) = LL₁
      generalize eq₂ : (p :: L₂ : List _) = LL₂
      intro h
      induction h using Relation.ReflTransGen.head_induction_on generalizing L₁ L₂ with
      | refl =>
        subst_vars
        cases eq₂
        constructor
      | head h₁₂ h ih =>
        subst_vars
        obtain ⟨a, b⟩ := p
        rw [Step.cons_left_iff] at h₁₂
        rcases h₁₂ with (⟨L, h₁₂, rfl⟩ | rfl)
        · exact (ih rfl rfl).head h₁₂
        · exact (cons_cons h).tail Step.cons_not_rev)
    cons_cons

@[to_additive]
/-
**FreeGroup.Red.append_append_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`
。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} (L : List (α × Bool)), FreeGroup.
Red (L ++ L₁) (L ++ L₂) ↔ FreeGroup.Red L₁ L₂
参数：α × Bool；L : List (α × Bool)；L ++ L₁；L ++ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append_append_left_iff : ∀ L, Red (L ++ L₁) (L ++ L₂) ↔ Red L₁ L₂
  | [] => Iff.rfl
  | p :: L => by simp [append_append_left_iff L, cons_cons_iff]

@[to_additive]
/-
**FreeGroup.Red.append_append** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：append_append (h₁ : Red L₁ L₃) (h₂ : Red L₂ L₄) : Red (L₁ ++ L₂) (L₃ ++ L₄
)
参数：h₁ : Red L₁ L₃；h₂ : Red L₂ L₄。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.trans`：trans (hab : ReflTransGen r a b) (hbc : Ref
lTransGen r b c) : ReflTransGen r a c
· 使用定理 `Relation.ReflTransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.ReflT
ransGen r ≤ Func…
· 使用定理 `FreeGroup.Red.Step.append_right`：∀ {α : Type u} {L₁ L₂ L₃ : List (α × Bo
ol)}, FreeGroup.Red.Step L₁ L₂ → FreeGroup.Red.Step (L₁ ++ L₃) (L₂ ++ L₃)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FreeGroup.Red.append_append_left_iff`：∀ {α : Type u} {L₁ L₂ : List (α × 
Bool)} (L : List (α × Bool)), FreeGroup.Red (L ++ L₁) (L ++ L₂) ↔ FreeGroup.Red 
L₁ L₂
-/
theorem append_append (h₁ : Red L₁ L₃) (h₂ : Red L₂ L₄) : Red (L₁ ++ L₂) (L₃ ++ L₄) :=
  (h₁.lift (fun L => L ++ L₂) fun _ _ => Step.append_right).trans ((append_append_left_iff _).2 h₂)

@[to_additive]
/-
**FreeGroup.Red.to_append_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：to_append_iff : Red L (L₁ ++ L₂) ↔ exists L₃ L₄, L = L₃ ++ L₄ ∧ Red L₃ L₁ 
∧ Red L₄ L₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.Red.refl`：∀ {α : Type u} {L : List (α × Bool)}, FreeGroup.Red 
L L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.append_eq_append_iff`：∀ {α : Type u_1} {ws xs ys zs : List α},   ws
 ++ xs = ys ++ zs ↔ (∃ as, ys = ws ++ as ∧ xs = as ++ zs) ∨ ∃ bs, ws = ys ++ bs 
∧ zs = bs ++ xs
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FreeGroup.Red.append_append`：append_append (h₁ : Red L₁ L₃) (h₂ : Red L₂
 L₄) : Red (L₁ ++ L₂) (L₃ ++ L₄)
-/
theorem to_append_iff : Red L (L₁ ++ L₂) ↔ ∃ L₃ L₄, L = L₃ ++ L₄ ∧ Red L₃ L₁ ∧ Red L₄ L₂ :=
  Iff.intro
    (by
      generalize eq : L₁ ++ L₂ = L₁₂
      intro h
      induction h generalizing L₁ L₂ with
      | refl => exact ⟨_, _, eq.symm, by rfl, by rfl⟩
      | tail hLL' h ih =>
        obtain @⟨s, e, a, b⟩ := h
        rcases List.append_eq_append_iff.1 eq with (⟨s', rfl, rfl⟩ | ⟨e', rfl, rfl⟩)
        · have : L₁ ++ (s' ++ (a, b) :: (a, not b) :: e) =
            L₁ ++ s' ++ (a, b) :: (a, not b) :: e := by simp
          rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩
          exact ⟨w₁, w₂, rfl, h₁, h₂.tail Step.not⟩
        · have : s ++ (a, b) :: (a, not b) :: e' ++ L₂ =
            s ++ (a, b) :: (a, not b) :: (e' ++ L₂) := by simp
          rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩
          exact ⟨w₁, w₂, rfl, h₁.tail Step.not, h₂⟩)
    fun ⟨_, _, Eq, h₃, h₄⟩ => Eq.symm ▸ append_append h₃ h₄

/-- The empty word `[]` only reduces to itself. -/
@[to_additive /-- The empty word `[]` only reduces to itself. -/]
/-
**FreeGroup.Red.nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：nil_iff : Red [] L ↔ L = []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.reflTransGen_iff_eq`：reflTransGen_iff_eq (h : forall b, ¬r a b)
 : ReflTransGen r a b ↔ b = a
· 使用定理 `FreeGroup.Red.not_step_nil`：not_step_nil : ¬Step [] L

--- 原说明 ---
The empty word `[]` only reduces to itself.
-/
theorem nil_iff : Red [] L ↔ L = [] :=
  reflTransGen_iff_eq fun _ => Red.not_step_nil

/-- A letter only reduces to itself. -/
@[to_additive /-- A letter only reduces to itself. -/]
/-
**FreeGroup.Red.singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：singleton_iff {x} : Red [x] L₁ ↔ L₁ = [x]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.reflTransGen_iff_eq`：reflTransGen_iff_eq (h : forall b, ¬r a b)
 : ReflTransGen r a b ↔ b = a
· 使用定理 `FreeGroup.Red.not_step_singleton`：∀ {α : Type u} {L : List (α × Bool)} {
p : α × Bool}, ¬FreeGroup.Red.Step [p] L

--- 原说明 ---
A letter only reduces to itself.
-/
theorem singleton_iff {x} : Red [x] L₁ ↔ L₁ = [x] :=
  reflTransGen_iff_eq fun _ => not_step_singleton

/-- If `x` is a letter and `w` is a word such that `xw` reduces to the empty word, then `w` reduces
to `x⁻¹` -/
@[to_additive
  /-- If `x` is a letter and `w` is a word such that `x + w` reduces to the empty word, then `w`
  reduces to `-x`. -/]
/-
**FreeGroup.Red.cons_nil_iff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`
。
形式化陈述：cons_nil_iff_singleton {x b} : Red ((x, b) :: L) [] ↔ Red L [(x, not b)]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.cons_cons`：cons_cons {p} : Red L₁ L₂ -> Red (p :: L₁) (p :
: L₂)
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
· 使用定理 `FreeGroup.Red.Step.cons_not_rev`：∀ {α : Type u} {L : List (α × Bool)} {x
 : α} {b : Bool}, FreeGroup.Red.Step ((x, !b) :: (x, b) :: L) L
· 使用定理 `FreeGroup.Red.church_rosser`：church_rosser : Red L₁ L₂ -> Red L₁ L₃ -> J
oin Red L₂ L₃
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.Red.singleton_iff`：singleton_iff {x} : Red [x] L₁ ↔ L₁ = [x]
· 使用定理 `FreeGroup.Red.Step.cons_not`：∀ {α : Type u} {L : List (α × Bool)} {x : α
} {b : Bool}, FreeGroup.Red.Step ((x, b) :: (x, !b) :: L) L
-/
theorem cons_nil_iff_singleton {x b} : Red ((x, b) :: L) [] ↔ Red L [(x, not b)] :=
  Iff.intro
    (fun h => by
      have h₁ : Red ((x, not b) :: (x, b) :: L) [(x, not b)] := cons_cons h
      have h₂ : Red ((x, not b) :: (x, b) :: L) L := ReflTransGen.single Step.cons_not_rev
      let ⟨L', h₁, h₂⟩ := church_rosser h₁ h₂
      rw [singleton_iff] at h₁
      subst L'
      assumption)
    fun h => (cons_cons h).tail Step.cons_not

@[to_additive]
/-
**FreeGroup.Red.red_iff_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：red_iff_irreducible {x1 b1 x2 b2} (h : (x1, b1) != (x2, b2)) : Red [(x1, !
b1), (x2, b2)] L ↔ L = [(x1, !b1), (x2, b2)]
参数：h : (x1, b1) != (x2, b2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.reflTransGen_iff_eq`：reflTransGen_iff_eq (h : forall b, ¬r a b)
 : ReflTransGen r a b ↔ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem red_iff_irreducible {x1 b1 x2 b2} (h : (x1, b1) ≠ (x2, b2)) :
    Red [(x1, !b1), (x2, b2)] L ↔ L = [(x1, !b1), (x2, b2)] := by
  apply reflTransGen_iff_eq
  generalize eq : [(x1, not b1), (x2, b2)] = L'
  intro L h'
  cases h'
  simp only [List.cons_eq_append_iff, List.cons.injEq, Prod.mk.injEq, and_false,
    List.nil_eq_append_iff, exists_const, or_self, or_false, List.cons_ne_nil] at eq
  rcases eq with ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  simp at h

/-- If `x` and `y` are distinct letters and `w₁ w₂` are words such that `xw₁` reduces to `yw₂`, then
`w₁` reduces to `x⁻¹yw₂`. -/
@[to_additive /-- If `x` and `y` are distinct letters and `w₁ w₂` are words such that `x + w₁`
reduces to `y + w₂`, then `w₁` reduces to `-x + y + w₂`. -/]
/-
**FreeGroup.Red.inv_of_red_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：inv_of_red_of_ne {x1 b1 x2 b2} (H1 : (x1, b1) != (x2, b2)) (H2 : Red ((x1,
 b1) :: L₁) ((x2, b2) :: L₂)) : Red L₁ ((x1, not b1) :: (x2, b2) :: L₂)
参数：H1 : (x1, b1) != (x2, b2)；H2 : Red ((x1, b1) :: L₁) ((x2, b2) :: L₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FreeGroup.Red.to_append_iff`：to_append_iff : Red L (L₁ ++ L₂) ↔ exists L
₃ L₄, L = L₃ ++ L₄ ∧ Red L₃ L₁ ∧ Red L₄ L₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FreeGroup.Red.append_append`：append_append (h₁ : Red L₁ L₃) (h₂ : Red L₂
 L₄) : Red (L₁ ++ L₂) (L₃ ++ L₄)
· 使用定理 `FreeGroup.Red.cons_cons`：cons_cons {p} : Red L₁ L₂ -> Red (p :: L₁) (p :
: L₂)
· 使用定理 `FreeGroup.Red.Step.to_red`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, Fre
eGroup.Red.Step L₁ L₂ → FreeGroup.Red L₁ L₂
· 使用定理 `FreeGroup.Red.Step.cons_not_rev`：∀ {α : Type u} {L : List (α × Bool)} {x
 : α} {b : Bool}, FreeGroup.Red.Step ((x, !b) :: (x, b) :: L) L
· 使用定理 `FreeGroup.Red.church_rosser`：church_rosser : Red L₁ L₂ -> Red L₁ L₃ -> J
oin Red L₂ L₃
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.Red.red_iff_irreducible`：red_iff_irreducible {x1 b1 x2 b2} (h 
: (x1, b1) != (x2, b2)) : Red [(x1, !b1), (x2, b2)] L ↔ L = [(x1, !b1), (x2, b2)
]
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inv_of_red_of_ne {x1 b1 x2 b2} (H1 : (x1, b1) ≠ (x2, b2))
    (H2 : Red ((x1, b1) :: L₁) ((x2, b2) :: L₂)) : Red L₁ ((x1, not b1) :: (x2, b2) :: L₂) := by
  have : Red ((x1, b1) :: L₁) ([(x2, b2)] ++ L₂) := H2
  rcases to_append_iff.1 this with ⟨_ | ⟨p, L₃⟩, L₄, eq, h₁, h₂⟩
  · simp [nil_iff] at h₁
  · cases eq
    change Red (L₃ ++ L₄) ([(x1, not b1), (x2, b2)] ++ L₂)
    apply append_append _ h₂
    have h₁ : Red ((x1, not b1) :: (x1, b1) :: L₃) [(x1, not b1), (x2, b2)] := cons_cons h₁
    have h₂ : Red ((x1, not b1) :: (x1, b1) :: L₃) L₃ := Step.cons_not_rev.to_red
    rcases church_rosser h₁ h₂ with ⟨L', h₁, h₂⟩
    rw [red_iff_irreducible H1] at h₁
    rwa [h₁] at h₂

open List -- for <+ notation

@[to_additive]
/-
**FreeGroup.Red.Step.sublist** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup.Red.Step L₁ L₂ → L₂.Su
blist L₁
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Step.sublist (H : Red.Step L₁ L₂) : L₂ <+ L₁ := by
  cases H; simp

/-- If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/
@[to_additive
/-- If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/]
/-
**FreeGroup.Red.sublist** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup.Red L₁ L₂ → L₂.Sublist
 L₁
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.reflTransGen_le_of_le`：reflTransGen_le_of_le {r' : α -> α -> Pr
op} [Std.Refl r] [IsTrans α r] (h : r' <= r) : ReflTransGen r' <= r
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `FreeGroup.Red.Step.sublist`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, Fr
eeGroup.Red.Step L₁ L₂ → L₂.Sublist L₁
-/
protected theorem sublist : Red L₁ L₂ → L₂ <+ L₁ :=
  @reflTransGen_le_of_le _ (fun a b => b <+ a) _ ⟨List.Sublist.refl⟩
    ⟨fun _a _b _c hab hbc => List.Sublist.trans hbc hab⟩ (fun _ _ => Red.Step.sublist) L₁ L₂

@[to_additive]
/-
**FreeGroup.Red.length_le** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：length_le (h : Red L₁ L₂) : L₂.length <= L₁.length
参数：h : Red L₁ L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂
 → l₁.length ≤ l₂.length
· 使用定理 `FreeGroup.Red.sublist`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGro
up.Red L₁ L₂ → L₂.Sublist L₁
-/
theorem length_le (h : Red L₁ L₂) : L₂.length ≤ L₁.length :=
  h.sublist.length_le

@[to_additive (attr := deprecated "Should not be needed." (since := "2026-04-10"))]
/-
**FreeGroup.Red.sizeof_of_step** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup.Red.Step L₁ L₂ → sizeO
f L₂ < sizeOf L₁
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `List.cons.sizeOf_spec`：∀ {α : Type u} [inst : SizeOf α] (head : α) (tail
 : List α), sizeOf (head :: tail) = 1 + sizeOf head + sizeOf tail
· 使用定理 `Nat.add_lt_add_left`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), k + n < k + m
-/
theorem sizeof_of_step : ∀ {L₁ L₂ : List (α × Bool)},
    Step L₁ L₂ → sizeOf L₂ < sizeOf L₁
  | _, _, @Step.not _ L1 L2 x b => by
    induction L1 with
    | nil =>
      rw [nil_append, nil_append, cons.sizeOf_spec, cons.sizeOf_spec]
      lia
    | cons hd tl ih =>
      dsimp
      exact Nat.add_lt_add_left ih _

@[to_additive]
/-
**FreeGroup.Red.length** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：length (h : Red L₁ L₂) : exists n, L₁.length = L₂.length + 2 * n
参数：h : Red L₁ L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.Red.Step.length`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, Fre
eGroup.Red.Step L₁ L₂ → L₂.length + 2 = L₁.length
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.mul_add`：∀ (n m k : ℕ), n * (m + k) = n * m + n * k
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length (h : Red L₁ L₂) : ∃ n, L₁.length = L₂.length + 2 * n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _h₁₂ h₂₃ ih =>
    rcases ih with ⟨n, eq⟩
    exists 1 + n
    simp [Nat.mul_add, eq, (Step.length h₂₃).symm, add_assoc]

@[to_additive]
/-
**FreeGroup.Red.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：antisymm (h₁₂ : Red L₁ L₂) (h₂₁ : Red L₂ L₁) : L₁ = L₂
参数：h₁₂ : Red L₁ L₂；h₂₁ : Red L₂ L₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.antisymm`：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₂.Sublist l₁ → l₁ = l₂
· 使用定理 `FreeGroup.Red.sublist`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGro
up.Red L₁ L₂ → L₂.Sublist L₁
-/
theorem antisymm (h₁₂ : Red L₁ L₂) (h₂₁ : Red L₂ L₁) : L₁ = L₂ :=
  h₂₁.sublist.antisymm h₁₂.sublist

end Red

@[to_additive]
/-
**FreeGroup.equivalence_join_red** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：equivalence_join_red : Equivalence (Join (@Red α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.equivalence_join_reflTransGen`：equivalence_join_reflTransGen (h
 : forall a b c, r a b -> r a c -> exists d, ReflGen r b d ∧ ReflTransGen r c d)
 : Equivalence (Join (ReflTr…
· 使用定理 `FreeGroup.Red.Step.diamond`：∀ {α : Type u} {L₁ L₂ L₃ L₄ : List (α × Bool
)},   FreeGroup.Red.Step L₁ L₃ →     FreeGroup.Red.Step L₂ L₄ → L₁ = L₂ → L₃ = L
₄ ∨ ∃ L₅, FreeGr…
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
-/
theorem equivalence_join_red : Equivalence (Join (@Red α)) :=
  equivalence_join_reflTransGen fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, ReflTransGen.single hcd⟩

@[to_additive]
/-
**FreeGroup.join_red_of_step** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：join_red_of_step (h : Red.Step L₁ L₂) : Join Red L₁ L₂
参数：h : Red.Step L₁ L₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.le_join_of_refl`：le_join_of_refl [Std.Refl r] : r <= Join r
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `Relation.instIsPreorderReflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}
, IsPreorder α (Relation.ReflTransGen r)
· 使用定理 `FreeGroup.Red.Step.to_red`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, Fre
eGroup.Red.Step L₁ L₂ → FreeGroup.Red L₁ L₂
-/
theorem join_red_of_step (h : Red.Step L₁ L₂) : Join Red L₁ L₂ := by
  unfold Red
  exact le_join_of_refl L₁ L₂ h.to_red

@[to_additive]
/-
**FreeGroup.eqvGen_step_iff_join_red** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：eqvGen_step_iff_join_red : EqvGen Red.Step L₁ L₂ ↔ Join Red L₁ L₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.EqvGen.mono`：mono {r p : α -> α -> Prop} (hrp : r <= p) : EqvGe
n r <= EqvGen p
· 使用定理 `FreeGroup.join_red_of_step`：join_red_of_step (h : Red.Step L₁ L₂) : Join
 Red L₁ L₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equivalence.eqvGen_iff`：Equivalence.eqvGen_iff (h : Equivalence r) : Eqv
Gen r a b ↔ r a b
· 使用定理 `FreeGroup.equivalence_join_red`：equivalence_join_red : Equivalence (Join
 (@Red α))
· 使用定理 `Relation.join_le_of_equivalence_of_le`：join_le_of_equivalence_of_le {r' 
: α -> α -> Prop} (hr : Equivalence r) (h : r' <= r) : Join r' <= r
· 使用定理 `Relation.EqvGen.is_equivalence`：is_equivalence : Equivalence (@EqvGen α 
r)
· 使用定理 `Relation.reflTransGen_le_of_equivalence_of_le`：reflTransGen_le_of_equiva
lence_of_le {r' : α -> α -> Prop} (hr : Equivalence r) : r' <= r -> ReflTransGen
 r' <= r
-/
theorem eqvGen_step_iff_join_red : EqvGen Red.Step L₁ L₂ ↔ Join Red L₁ L₂ :=
  Iff.intro
    (fun h =>
      have : EqvGen (Join Red) L₁ L₂ := h.mono fun _ _ => join_red_of_step
      equivalence_join_red.eqvGen_iff.1 this)
    (join_le_of_equivalence_of_le (Relation.EqvGen.is_equivalence _)
      (reflTransGen_le_of_equivalence_of_le (Relation.EqvGen.is_equivalence _) EqvGen.rel) L₁ L₂)

/-! ### Reduced words -/

/-- Predicate asserting that the word `L` admits no reduction steps, i.e., no two neighboring
elements of the word cancel. -/
@[to_additive /-- Predicate asserting the word `L` admits no reduction steps,
i.e., no two neighboring elements of the word cancel. -/]
/-
**FreeGroup.IsReduced** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：IsReduced (L : List (α × Bool)) : Prop
参数：L : List (α × Bool)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsReduced (L : List (α × Bool)) : Prop := L.IsChain fun a b ↦ a.1 = b.1 → a.2 = b.2

section IsReduced

open List

@[to_additive (attr := simp)]
/-
**FreeGroup.IsReduced.nil** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.IsReduced`。
形式化陈述：∀ {α : Type u}, FreeGroup.IsReduced []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isChain_nil`：isChain_nil : IsChain R []
-/
theorem IsReduced.nil : IsReduced ([] : List (α × Bool)) := isChain_nil

@[to_additive (attr := simp)]
/-
**FreeGroup.IsReduced.singleton** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.IsReduced`。
形式化陈述：∀ {α : Type u} {a : α × Bool}, FreeGroup.IsReduced [a]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isChain_singleton`：isChain_singleton (a : α) : IsChain R [a]
-/
theorem IsReduced.singleton {a : α × Bool} : IsReduced [a] := isChain_singleton a

@[to_additive (attr := simp)]
/-
**FreeGroup.isReduced_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：isReduced_cons_cons {a b : (α × Bool)} : IsReduced (a :: b :: L) ↔ (a.1 = 
b.1 -> a.2 = b.2) ∧ IsReduced (b :: L)
参数：α × Bool。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
-/
theorem isReduced_cons_cons {a b : (α × Bool)} :
    IsReduced (a :: b :: L) ↔ (a.1 = b.1 → a.2 = b.2) ∧ IsReduced (b :: L) := isChain_cons_cons

@[to_additive]
/-
**FreeGroup.IsReduced.not_step** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.IsReduced`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup.IsReduced L₁ → ¬FreeGr
oup.Red.Step L₁ L₂
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem IsReduced.not_step (h : IsReduced L₁) : ¬ Red.Step L₁ L₂ := fun step ↦ by
  induction step
  simp [IsReduced] at h

@[to_additive]
/-
**FreeGroup.IsReduced.of_forall_not_step** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Is
Reduced`。
形式化陈述：∀ {α : Type u} {L₁ : List (α × Bool)}, (∀ (L₂ : List (α × Bool)), ¬FreeGro
up.Red.Step L₁ L₂) → FreeGroup.IsReduced L₁
参数：α × Bool；∀ (L₂ : List (α × Bool)), ¬FreeGroup.Red.Step L₁ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsReduced.of_forall_not_step :
    ∀ {L₁ : List (α × Bool)}, (∀ L₂, ¬ Red.Step L₁ L₂) → IsReduced L₁
  | [], _ => .nil
  | [a], _ => .singleton
  | (a₁, b₁) :: (a₂, b₂) :: L₁, hL₁ => by
    rw [isReduced_cons_cons]
    refine ⟨?_, .of_forall_not_step fun L₂ step ↦ hL₁ _ step.cons⟩
    rintro rfl
    symm
    rw [← Bool.ne_not]
    rintro rfl
    exact hL₁ L₁ <| .not (L₁ := [])

@[to_additive]
/-
**FreeGroup.isReduced_iff_not_step** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：isReduced_iff_not_step : IsReduced L₁ ↔ forall L₂, ¬ Red.Step L₁ L₂ where 
mp h _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.IsReduced.not_step`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, 
FreeGroup.IsReduced L₁ → ¬FreeGroup.Red.Step L₁ L₂
· 使用定理 `FreeGroup.IsReduced.of_forall_not_step`：∀ {α : Type u} {L₁ : List (α × B
ool)}, (∀ (L₂ : List (α × Bool)), ¬FreeGroup.Red.Step L₁ L₂) → FreeGroup.IsReduc
ed L₁
-/
theorem isReduced_iff_not_step : IsReduced L₁ ↔ ∀ L₂, ¬ Red.Step L₁ L₂ where
  mp h _ := h.not_step
  mpr := .of_forall_not_step

@[to_additive]
/-
**FreeGroup.IsReduced.red_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.IsReduced`
。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup.IsReduced L₁ → (FreeGr
oup.Red L₁ L₂ ↔ L₂ = L₁)
参数：α × Bool；FreeGroup.Red L₁ L₂ ↔ L₂ = L₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.reflTransGen_iff_eq`：reflTransGen_iff_eq (h : forall b, ¬r a b)
 : ReflTransGen r a b ↔ b = a
· 使用定理 `FreeGroup.IsReduced.not_step`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, 
FreeGroup.IsReduced L₁ → ¬FreeGroup.Red.Step L₁ L₂
-/
theorem IsReduced.red_iff_eq (h : IsReduced L₁) : Red L₁ L₂ ↔ L₂ = L₁ :=
  Relation.reflTransGen_iff_eq fun _ => h.not_step

@[to_additive]
/-
**FreeGroup.IsReduced.append_overlap** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.IsRedu
ced`。
形式化陈述：∀ {α : Type u} {L₁ L₂ L₃ : List (α × Bool)},   FreeGroup.IsReduced (L₁ ++ 
L₂) → FreeGroup.IsReduced (L₂ ++ L₃) → L₂ ≠ [] → FreeGroup.IsReduced (L₁ ++ L₂ +
+ L₃)
参数：α × Bool；L₁ ++ L₂；L₂ ++ L₃；L₁ ++ L₂ ++ L₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.append_overlap`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ 
l₃ : List α},   List.IsChain R (l₁ ++ l₂) → List.IsChain R (l₂ ++ l₃) → l₂ ≠ [] 
→ List.IsChain R …
-/
theorem IsReduced.append_overlap {L₁ L₂ L₃ : List (α × Bool)} (h₁ : IsReduced (L₁ ++ L₂))
    (h₂ : IsReduced (L₂ ++ L₃)) (hn : L₂ ≠ []) : IsReduced (L₁ ++ L₂ ++ L₃) :=
  IsChain.append_overlap h₁ h₂ hn

@[to_additive]
/-
**FreeGroup.IsReduced.infix** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.IsReduced`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup.IsReduced L₂ → L₁ <:+:
 L₂ → FreeGroup.IsReduced L₁
参数：α × Bool。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.infix`：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α},
 List.IsChain R l → l₁ <:+: l → List.IsChain R l₁
-/
theorem IsReduced.infix (h : IsReduced L₂) (h' : L₁ <:+: L₂) : IsReduced L₁ := IsChain.infix h h'

end IsReduced
end FreeGroup

set_option linter.translateOverwrite false in
/--
If `α` is a type, then `FreeGroup α` is the free group generated by `α`.
This is a group equipped with a function `FreeGroup.of : α → FreeGroup α` which has
the following universal property: if `G` is any group, and `f : α → G` is any function,
then this function is the composite of `FreeGroup.of` and a unique group homomorphism
`FreeGroup.lift f : FreeGroup α →* G`.

A typical element of `FreeGroup α` is a formal product of
elements of `α` and their formal inverses, quotient by reduction.
For example if `x` and `y` are terms of type `α` then `x⁻¹ * y * y * x * y⁻¹` is a
"typical" element of `FreeGroup α`. In particular if `α` is empty
then `FreeGroup α` is isomorphic to the trivial group, and if `α` has one term
then `FreeGroup α` is isomorphic to `Multiplicative ℤ`.
If `α` has two or more terms then `FreeGroup α` is not commutative.
-/
@[to_additive (attr := wikidata Q431078)
/-- If `α` is a type, then `FreeAddGroup α` is the free additive group generated by `α`.
This is a group equipped with a function `FreeAddGroup.of : α → FreeAddGroup α` which has
the following universal property: if `G` is any group, and `f : α → G` is any function,
then this function is the composite of `FreeAddGroup.of` and a unique group homomorphism
`FreeAddGroup.lift f : FreeAddGroup α →+ G`.

A typical element of `FreeAddGroup α` is a formal sum of
elements of `α` and their formal inverses, quotient by reduction.
For example if `x` and `y` are terms of type `α` then `-x + y + y + x + -y` is a
"typical" element of `FreeAddGroup α`. In particular if `α` is empty
then `FreeAddGroup α` is isomorphic to the trivial group, and if `α` has one term
then `FreeAddGroup α` is isomorphic to `ℤ`.
If `α` has two or more terms then `FreeAddGroup α` is not commutative. -/]
/-
**FreeGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FreeGroup (α : Type u) : Type u
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def FreeGroup (α : Type u) : Type u :=
  Quot <| @FreeGroup.Red.Step α

namespace FreeGroup

variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

/-- The canonical map from `List (α × Bool)` to the free group on `α`. -/
@[to_additive /-- The canonical map from `List (α × Bool)` to the free additive group on `α`. -/]
/-
**FreeGroup.mk** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：mk (L : List (α × Bool)) : FreeGroup α
参数：L : List (α × Bool)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `List (α × Bool)` to the free group on `α`.
-/
def mk (L : List (α × Bool)) : FreeGroup α :=
  Quot.mk Red.Step L

@[to_additive (attr := simp)]
/-
**FreeGroup.quot_mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：quot_mk_eq_mk : Quot.mk Red.Step L = mk L
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_mk : Quot.mk Red.Step L = mk L :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.quot_lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：quot_lift_mk (β : Type v) (f : List (α × Bool) -> β) (H : forall L₁ L₂, Re
d.Step L₁ L₂ -> f L₁ = f L₂) : Quot.lift f H (mk L) = f L
参数：β : Type v；f : List (α × Bool) -> β；H : forall L₁ L₂, Red.Step L₁ L₂ -> f L₁ 
= f L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_lift_mk (β : Type v) (f : List (α × Bool) → β)
    (H : ∀ L₁ L₂, Red.Step L₁ L₂ → f L₁ = f L₂) : Quot.lift f H (mk L) = f L :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.quot_liftOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：quot_liftOn_mk (β : Type v) (f : List (α × Bool) -> β) (H : forall L₁ L₂, 
Red.Step L₁ L₂ -> f L₁ = f L₂) : Quot.liftOn (mk L) f H = f L
参数：β : Type v；f : List (α × Bool) -> β；H : forall L₁ L₂, Red.Step L₁ L₂ -> f L₁ 
= f L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_liftOn_mk (β : Type v) (f : List (α × Bool) → β)
    (H : ∀ L₁ L₂, Red.Step L₁ L₂ → f L₁ = f L₂) : Quot.liftOn (mk L) f H = f L :=
  rfl

open scoped Relator in
@[to_additive (attr := simp)]
/-
**FreeGroup.quot_map_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：quot_map_mk (β : Type v) (f : List (α × Bool) -> List (β × Bool)) (H : (Re
d.Step ⇒ Red.Step) f f) : Quot.map f H (mk L) = mk (f L)
参数：β : Type v；f : List (α × Bool) -> List (β × Bool)；H : (Red.Step ⇒ Red.Step) f
 f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_map_mk (β : Type v) (f : List (α × Bool) → List (β × Bool))
    (H : (Red.Step ⇒ Red.Step) f f) : Quot.map f H (mk L) = mk (f L) :=
  rfl

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (FreeGroup α) :=
  ⟨mk []⟩

@[to_additive]
/-
**FreeGroup.one_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：one_eq_mk : (1 : FreeGroup α) = mk []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_eq_mk : (1 : FreeGroup α) = mk [] :=
  rfl

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (FreeGroup α) :=
  ⟨1⟩

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (FreeGroup α) := inferInstanceAs <| Unique (Quot _)

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (FreeGroup α) :=
  ⟨fun x y =>
    Quot.liftOn x
      (fun L₁ =>
        Quot.liftOn y (fun L₂ => mk <| L₁ ++ L₂) fun _L₂ _L₃ H =>
          Quot.sound <| Red.Step.append_left H)
      fun _L₁ _L₂ H => Quot.inductionOn y fun _L₃ => Quot.sound <| Red.Step.append_right H⟩

@[to_additive (attr := simp)]
/-
**FreeGroup.mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂) :=
  rfl

/-- Transform a word representing a free group element into a word representing its inverse. -/
@[to_additive /-- Transform a word representing a free group element into a word representing its
  negative. -/]
/-
**FreeGroup.invRev** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：invRev (w : List (α × Bool)) : List (α × Bool)
参数：w : List (α × Bool)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def invRev (w : List (α × Bool)) : List (α × Bool) :=
  (List.map (fun g : α × Bool => (g.1, not g.2)) w).reverse

@[to_additive (attr := simp)]
/-
**FreeGroup.invRev_length** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：invRev_length : (invRev L₁).length = L₁.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invRev_length : (invRev L₁).length = L₁.length := by simp [invRev]

@[to_additive (attr := simp)]
/-
**FreeGroup.invRev_invRev** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：invRev_invRev : invRev (invRev L₁) = L₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invRev_invRev : invRev (invRev L₁) = L₁ := by
  simp [invRev, List.map_reverse, Function.comp_def]

@[to_additive (attr := simp)]
/-
**FreeGroup.invRev_empty** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：invRev_empty : invRev ([] : List (α × Bool)) = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invRev_empty : invRev ([] : List (α × Bool)) = [] :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.invRev_append** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：invRev_append : invRev (L₁ ++ L₂) = invRev L₂ ++ invRev L₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invRev_append : invRev (L₁ ++ L₂) = invRev L₂ ++ invRev L₁ := by simp [invRev]

@[to_additive]
/-
**FreeGroup.invRev_cons** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：invRev_cons {a : (α × Bool)} : invRev (a :: L) = invRev L ++ invRev [a]
参数：α × Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invRev_cons {a : (α × Bool)} : invRev (a :: L) = invRev L ++ invRev [a] := by
  simp [invRev]

@[to_additive]
/-
**FreeGroup.invRev_involutive** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：invRev_involutive : Function.Involutive (@invRev α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.invRev_invRev`：invRev_invRev : invRev (invRev L₁) = L₁
-/
theorem invRev_involutive : Function.Involutive (@invRev α) := fun _ => invRev_invRev

@[to_additive]
/-
**FreeGroup.invRev_injective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：invRev_injective : Function.Injective (@invRev α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `FreeGroup.invRev_involutive`：invRev_involutive : Function.Involutive (@i
nvRev α)
-/
theorem invRev_injective : Function.Injective (@invRev α) :=
  invRev_involutive.injective

@[to_additive]
/-
**FreeGroup.invRev_surjective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：invRev_surjective : Function.Surjective (@invRev α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `FreeGroup.invRev_involutive`：invRev_involutive : Function.Involutive (@i
nvRev α)
-/
theorem invRev_surjective : Function.Surjective (@invRev α) :=
  invRev_involutive.surjective

@[to_additive]
/-
**FreeGroup.invRev_bijective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：invRev_bijective : Function.Bijective (@invRev α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `FreeGroup.invRev_involutive`：invRev_involutive : Function.Involutive (@i
nvRev α)
-/
theorem invRev_bijective : Function.Bijective (@invRev α) :=
  invRev_involutive.bijective

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (FreeGroup α) :=
  ⟨Quot.map invRev
      (by
        intro a b h
        cases h
        simp [invRev])⟩

@[to_additive (attr := simp)]
/-
**FreeGroup.inv_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：inv_mk : (mk L)⁻¹ = mk (invRev L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_mk : (mk L)⁻¹ = mk (invRev L) :=
  rfl

@[to_additive]
/-
**FreeGroup.Red.Step.invRev** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)},   FreeGroup.Red.Step L₁ L₂ → Fre
eGroup.Red.Step (FreeGroup.invRev L₁) (FreeGroup.invRev L₂)
参数：α × Bool；FreeGroup.invRev L₁；FreeGroup.invRev L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Red.Step.invRev {L₁ L₂ : List (α × Bool)} (h : Red.Step L₁ L₂) :
    Red.Step (FreeGroup.invRev L₁) (FreeGroup.invRev L₂) := by
  obtain ⟨a, b, x, y⟩ := h
  simp [FreeGroup.invRev]

@[to_additive]
/-
**FreeGroup.Red.invRev** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)},   FreeGroup.Red L₁ L₂ → FreeGrou
p.Red (FreeGroup.invRev L₁) (FreeGroup.invRev L₂)
参数：α × Bool；FreeGroup.invRev L₁；FreeGroup.invRev L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.ReflT
ransGen r ≤ Func…
· 使用定理 `FreeGroup.Red.Step.invRev`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)},   F
reeGroup.Red.Step L₁ L₂ → FreeGroup.Red.Step (FreeGroup.invRev L₁) (FreeGroup.in
vRev L₂)
-/
theorem Red.invRev {L₁ L₂ : List (α × Bool)} (h : Red L₁ L₂) : Red (invRev L₁) (invRev L₂) :=
  Relation.ReflTransGen.lift FreeGroup.invRev (fun _a _b => Red.Step.invRev) L₁ L₂ h

@[to_additive (attr := simp)]
/-
**FreeGroup.Red.step_invRev_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)},   FreeGroup.Red.Step (FreeGroup.
invRev L₁) (FreeGroup.invRev L₂) ↔ FreeGroup.Red.Step L₁ L₂
参数：α × Bool；FreeGroup.invRev L₁；FreeGroup.invRev L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.invRev_invRev`：invRev_invRev : invRev (invRev L₁) = L₁
· 使用定理 `FreeGroup.Red.Step.invRev`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)},   F
reeGroup.Red.Step L₁ L₂ → FreeGroup.Red.Step (FreeGroup.invRev L₁) (FreeGroup.in
vRev L₂)
-/
theorem Red.step_invRev_iff :
    Red.Step (FreeGroup.invRev L₁) (FreeGroup.invRev L₂) ↔ Red.Step L₁ L₂ :=
  ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive (attr := simp)]
/-
**FreeGroup.red_invRev_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：red_invRev_iff : Red (invRev L₁) (invRev L₂) ↔ Red L₁ L₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.invRev_invRev`：invRev_invRev : invRev (invRev L₁) = L₁
· 使用定理 `FreeGroup.Red.invRev`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)},   FreeGr
oup.Red L₁ L₂ → FreeGroup.Red (FreeGroup.invRev L₁) (FreeGroup.invRev L₂)
-/
theorem red_invRev_iff : Red (invRev L₁) (invRev L₂) ↔ Red L₁ L₂ :=
  ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (FreeGroup α) where
  mul_assoc := by rintro ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩; simp
  one_mul := by rintro ⟨L⟩; rfl
  mul_one := by rintro ⟨L⟩; simp [one_eq_mk]
  inv_mul_cancel := by
    rintro ⟨L⟩
    exact
      List.recOn L rfl fun ⟨x, b⟩ tl ih =>
          Eq.trans (Quot.sound <| by simp [invRev]) ih

@[to_additive (attr := simp)]
/-
**FreeGroup.pow_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：pow_mk (n : Nat) : mk L ^ n = mk (List.flatten <| List.replicate n L)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_mk (n : ℕ) : mk L ^ n = mk (List.flatten <| List.replicate n L) :=
  match n with
  | 0 => rfl
  | n + 1 => by rw [pow_succ', pow_mk, mul_mk, List.replicate_succ, List.flatten_cons]

/-- `of` is the canonical injection from the type to the free group over that type by sending each
element to the equivalence class of the letter that is the element. -/
@[to_additive /-- `of` is the canonical injection from the type to the free group over that type
  by sending each element to the equivalence class of the letter that is the element. -/]
/-
**FreeGroup.of** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：of (x : α) : FreeGroup α
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def of (x : α) : FreeGroup α :=
  mk [(x, true)]

@[to_additive (attr := elab_as_elim, induction_eliminator)]
/-
**FreeGroup.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：∀ {α : Type u} {C : FreeGroup α → Prop} (z : FreeGroup α),   C 1 →     (∀ 
(x : α), C (FreeGroup.of x)) →       (∀ (x : α), C (FreeGroup.of x) → C (FreeGro
up.of x)⁻¹) → (∀ (x y : FreeGroup α), C x → C y → C (x * y)) → C z
参数：z : FreeGroup α；∀ (x : α), C (FreeGroup.of x)；∀ (x : α), C (FreeGroup.of x) →
 C (FreeGroup.of x)⁻¹；∀ (x y : FreeGroup α), C x → C y → C (x * y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
-/
protected lemma induction_on {C : FreeGroup α → Prop} (z : FreeGroup α) (C1 : C 1)
    (of : ∀ x, C <| of x) (inv_of : ∀ x, C (.of x) → C (.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  Quot.inductionOn z fun L ↦ L.recOn C1 fun ⟨x, b⟩ _tl ih ↦
    b.recOn (mul _ _ (inv_of _ <| of x) ih) (mul _ _ (of x) ih)

/-- Two homomorphisms out of a free group are equal if they are equal on generators.

See note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext) /-- Two homomorphisms out of a free additive group are equal if they are
  equal on generators. See note [partially-applied ext lemmas]. -/]
/-
**FreeGroup.ext_hom** 是 Mathlib 中的一个引理，位于命名空间 `FreeGroup`。
形式化陈述：ext_hom {M : Type*} [Monoid M] (f g : FreeGroup α ->* M) (h : forall a, f 
(of a) = g (of a)) : f = g
参数：f g : FreeGroup α ->* M；h : forall a, f (of a) = g (of a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `FreeGroup.induction_on`：∀ {α : Type u} {C : FreeGroup α → Prop} (z : Fre
eGroup α),   C 1 →     (∀ (x : α), C (FreeGroup.of x)) →       (∀ (x : α), C (Fr
eeGroup.of x…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
lemma ext_hom {M : Type*} [Monoid M] (f g : FreeGroup α →* M) (h : ∀ a, f (of a) = g (of a)) :
    f = g := by
  ext x
  have this (x) : f (of x)⁻¹ = g (of x)⁻¹ := by
    trans f (of x)⁻¹ * f (of x) * g (of x)⁻¹
    · simp_rw [mul_assoc, h, ← _root_.map_mul, mul_inv_cancel, _root_.map_one, mul_one]
    · simp_rw [← _root_.map_mul, inv_mul_cancel, _root_.map_one, one_mul]
  induction x <;> simp [*]

@[to_additive]
/-
**FreeGroup.Red.exact** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup.mk L₁ = FreeGroup.mk L
₂ ↔ Relation.Join FreeGroup.Red L₁ L₂
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.eqvGen_exact`：Quot.eqvGen_exact (H : Quot.mk r a = Quot.mk r b) : E
qvGen r a b
· 使用定理 `Quot.eqvGen_sound`：Quot.eqvGen_sound (H : EqvGen r a b) : Quot.mk r a = 
Quot.mk r b
· 使用定理 `FreeGroup.eqvGen_step_iff_join_red`：eqvGen_step_iff_join_red : EqvGen Re
d.Step L₁ L₂ ↔ Join Red L₁ L₂
-/
theorem Red.exact : mk L₁ = mk L₂ ↔ Join Red L₁ L₂ :=
  calc
    mk L₁ = mk L₂ ↔ EqvGen Red.Step L₁ L₂ := Iff.intro Quot.eqvGen_exact Quot.eqvGen_sound
    _ ↔ Join Red L₁ L₂ := eqvGen_step_iff_join_red

/-- The canonical map from the type to the free group is an injection. -/
@[to_additive /-- The canonical map from the type to the additive free group is an injection. -/]
/-
**FreeGroup.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：of_injective : Function.Injective (@of α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FreeGroup.Red.exact`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, FreeGroup
.mk L₁ = FreeGroup.mk L₂ ↔ Relation.Join FreeGroup.Red L₁ L₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
The canonical map from the type to the free group is an injection.
-/
theorem of_injective : Function.Injective (@of α) := fun _ _ H => by
  let ⟨L₁, hx, hy⟩ := Red.exact.1 H
  simp [Red.singleton_iff] at hx hy; simp_all

section lift

variable {β : Type v} [Group β] (f : α → β) {x y : FreeGroup α}

/-- Given `f : α → β` with `β` a group, the canonical map `List (α × Bool) → β` -/
@[to_additive /-- Given `f : α → β` with `β` an additive group, the canonical map
  `List (α × Bool) → β` -/]
/-
**FreeGroup.Lift.aux** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup.Lift`。
形式化陈述：{α : Type u} → {β : Type v} → [Group β] → (α → β) → List (α × Bool) → β
参数：α → β；α × Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Lift.aux : List (α × Bool) → β := fun L =>
  List.prod <| L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹

@[to_additive]
/-
**FreeGroup.Red.Step.lift** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.Red.Step`。
形式化陈述：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} {β : Type v} [inst : Group β] {f 
: α → β},   FreeGroup.Red.Step L₁ L₂ → FreeGroup.Lift.aux f L₁ = FreeGroup.Lift.
aux f L₂
参数：α × Bool。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem Red.Step.lift {f : α → β} (H : Red.Step L₁ L₂) : Lift.aux f L₁ = Lift.aux f L₂ := by
  obtain @⟨_, _, _, b⟩ := H; cases b <;> simp [Lift.aux, List.prod_append]

set_option backward.isDefEq.respectTransparency false in
/-- If `β` is a group, then any function from `α` to `β` extends uniquely to a group homomorphism
from the free group over `α` to `β` -/
@[to_additive (attr := simps symm_apply)
  /-- If `β` is an additive group, then any function from `α` to `β` extends uniquely to an
  additive group homomorphism from the free additive group over `α` to `β` -/]
/-
**FreeGroup.lift** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：lift : (α -> β) ≃ (FreeGroup α ->* β) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.Red.Step.lift`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)} {β : T
ype v} [inst : Group β] {f : α → β},   FreeGroup.Red.Step L₁ L₂ → FreeGroup.Lift
.aux f L₁ = F…
-/
def lift : (α → β) ≃ (FreeGroup α →* β) where
  toFun f :=
    MonoidHom.mk' (Quot.lift (Lift.aux f) fun _ _ => Red.Step.lift) <| by
      rintro ⟨L₁⟩ ⟨L₂⟩; simp [Lift.aux, List.prod_append]
  invFun g := g ∘ of
  left_inv f := by ext; simp [of, Lift.aux]
  right_inv g := by ext; simp [of, Lift.aux]

variable {f}

@[to_additive (attr := simp)]
/-
**FreeGroup.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：lift_mk : lift f (mk L) = List.prod (L.map fun x => cond x.2 (f x.1) (f x.
1)⁻¹)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk : lift f (mk L) = List.prod (L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹) :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.lift_apply_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：lift_apply_of {x} : lift f (of x) = f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_apply_of {x} : lift f (of x) = f x := by simp [of]

@[to_additive]
/-
**FreeGroup.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：lift_unique (g : FreeGroup α ->* β) (hg : forall x, g (FreeGroup.of x) = f
 x) {x} : g x = FreeGroup.lift f x
参数：g : FreeGroup α ->* β；hg : forall x, g (FreeGroup.of x) = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem lift_unique (g : FreeGroup α →* β) (hg : ∀ x, g (FreeGroup.of x) = f x) {x} :
    g x = FreeGroup.lift f x :=
  DFunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ FreeGroup.of = f)) x

@[to_additive]
/-
**FreeGroup.lift_of_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：lift_of_eq_id (α) : lift of = MonoidHom.id (FreeGroup α)
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem lift_of_eq_id (α) : lift of = MonoidHom.id (FreeGroup α) :=
  lift.apply_symm_apply (MonoidHom.id _)

@[to_additive]
/-
**FreeGroup.lift_of_apply** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：lift_of_apply (x : FreeGroup α) : lift FreeGroup.of x = x
参数：x : FreeGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `FreeGroup.lift_of_eq_id`：lift_of_eq_id (α) : lift of = MonoidHom.id (Fre
eGroup α)
-/
theorem lift_of_apply (x : FreeGroup α) : lift FreeGroup.of x = x :=
  DFunLike.congr_fun (lift_of_eq_id α) x

@[to_additive]
/-
**FreeGroup.range_lift_le** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：range_lift_le {s : Subgroup β} (H : Set.range f subseteq s) : (lift f).ran
ge <= s
参数：H : Set.range f subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
-/
theorem range_lift_le {s : Subgroup β} (H : Set.range f ⊆ s) : (lift f).range ≤ s := by
  rintro _ ⟨⟨L⟩, rfl⟩
  exact List.recOn L s.one_mem fun ⟨x, b⟩ tl ih ↦
    Bool.recOn b (by simpa using s.mul_mem (s.inv_mem <| H ⟨x, rfl⟩) ih)
      (by simpa using s.mul_mem (H ⟨x, rfl⟩) ih)

@[to_additive]
/-
**FreeGroup.range_lift_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：range_lift_eq_closure : (lift f).range = Subgroup.closure (Set.range f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `FreeGroup.range_lift_le`：range_lift_le {s : Subgroup β} (H : Set.range f
 subseteq s) : (lift f).range <= s
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FreeGroup.lift_apply_of`：lift_apply_of {x} : lift f (of x) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_lift_eq_closure : (lift f).range = Subgroup.closure (Set.range f) := by
  apply le_antisymm (range_lift_le Subgroup.subset_closure)
  rw [Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨FreeGroup.of a, by simp only [lift_apply_of]⟩

@[to_additive]
/-
**FreeGroup.lift_surjective_iff_closure_range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `
FreeGroup`。
形式化陈述：lift_surjective_iff_closure_range_eq_top : Function.Surjective (lift f) ↔ 
Subgroup.closure (Set.range f) = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `FreeGroup.range_lift_eq_closure`：range_lift_eq_closure : (lift f).range 
= Subgroup.closure (Set.range f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_surjective_iff_closure_range_eq_top :
    Function.Surjective (lift f) ↔ Subgroup.closure (Set.range f) = ⊤ := by
  rw [← MonoidHom.range_eq_top, range_lift_eq_closure]

@[to_additive]
/-
**FreeGroup.closure_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：closure_eq_range (s : Set β) : Subgroup.closure s = (lift ((↑) : s -> β)).
range
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.range_lift_eq_closure`：range_lift_eq_closure : (lift f).range 
= Subgroup.closure (Set.range f)
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem closure_eq_range (s : Set β) : Subgroup.closure s = (lift ((↑) : s → β)).range := by
  rw [FreeGroup.range_lift_eq_closure, Subtype.range_coe]

/-- The generators of `FreeGroup α` generate `FreeGroup α`. That is, the subgroup closure of the
set of generators equals `⊤`. -/
@[to_additive (attr := simp)]
/-
**FreeGroup.closure_range_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：closure_range_of (α) : Subgroup.closure (Set.range (FreeGroup.of : α -> Fr
eeGroup α)) = ⊤
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.range_lift_eq_closure`：range_lift_eq_closure : (lift f).range 
= Subgroup.closure (Set.range f)
· 使用定理 `FreeGroup.lift_of_eq_id`：lift_of_eq_id (α) : lift of = MonoidHom.id (Fre
eGroup α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id

--- 原说明 ---
The generators of `FreeGroup α` generate `FreeGroup α`. That is, the subgroup cl
osure of the
set of generators equals `⊤`.
-/
theorem closure_range_of (α) :
    Subgroup.closure (Set.range (FreeGroup.of : α → FreeGroup α)) = ⊤ := by
  rw [← range_lift_eq_closure, lift_of_eq_id]
  exact MonoidHom.range_eq_top.2 Function.surjective_id

@[to_additive]
/-
**FreeGroup.lift_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：lift_surjective_of_surjective (hf : Function.Surjective f) : Function.Surj
ective (lift f)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `FreeGroup.range_lift_eq_closure`：range_lift_eq_closure : (lift f).range 
= Subgroup.closure (Set.range f)
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Subgroup.closure_univ`：closure_univ : closure (univ : Set G) = ⊤
-/
theorem lift_surjective_of_surjective (hf : Function.Surjective f) :
    Function.Surjective (lift f) := by
  rw [← MonoidHom.range_eq_top, range_lift_eq_closure, hf.range_eq, Subgroup.closure_univ]

end lift

section Map

variable {β : Type v} (f : α → β) {x y : FreeGroup α}

set_option backward.isDefEq.respectTransparency false in
/-- Any function from `α` to `β` extends uniquely to a group homomorphism from the free group over
  `α` to the free group over `β`. -/
@[to_additive /-- Any function from `α` to `β` extends uniquely to an additive group homomorphism
from the additive free group over `α` to the additive free group over `β`. -/]
/-
**FreeGroup.map** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：map : FreeGroup α ->* FreeGroup β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map : FreeGroup α →* FreeGroup β :=
  MonoidHom.mk'
    (Quot.map (List.map fun x => (f x.1, x.2)) fun L₁ L₂ H => by cases H; simp)
    (by rintro ⟨L₁⟩ ⟨L₂⟩; simp)

variable {f}

@[to_additive (attr := simp)]
/-
**FreeGroup.map.mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.map`。
形式化陈述：∀ {α : Type u} {L : List (α × Bool)} {β : Type v} {f : α → β},   (FreeGrou
p.map f) (FreeGroup.mk L) = FreeGroup.mk (List.map (fun x => (f x.1, x.2)) L)
参数：α × Bool；FreeGroup.map f；FreeGroup.mk L；List.map (fun x => (f x.1, x.2)) L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map.mk : map f (mk L) = mk (L.map fun x => (f x.1, x.2)) :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.map.id** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.map`。
形式化陈述：∀ {α : Type u} (x : FreeGroup α), (FreeGroup.map id) x = x
参数：x : FreeGroup α；FreeGroup.map id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `List.map_id'`：∀ {α : Type u_1} (l : List α), List.map (fun a => a) l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map.id (x : FreeGroup α) : map id x = x := by rcases x with ⟨L⟩; simp [List.map_id']

@[to_additive (attr := simp)]
/-
**FreeGroup.map.id'** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.map`。
形式化陈述：∀ {α : Type u} (x : FreeGroup α), (FreeGroup.map fun z => z) x = x
参数：x : FreeGroup α；FreeGroup.map fun z => z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.map.id`：∀ {α : Type u} (x : FreeGroup α), (FreeGroup.map id) x
 = x
-/
theorem map.id' (x : FreeGroup α) : map (fun z => z) x = x :=
  map.id x

@[to_additive]
/-
**FreeGroup.map.comp** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.map`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ) (x : Free
Group α),   (FreeGroup.map g) ((FreeGroup.map f) x) = (FreeGroup.map (g ∘ f)) x
参数：f : α → β；g : β → γ；x : FreeGroup α；FreeGroup.map g；(FreeGroup.map f) x；FreeG
roup.map (g ∘ f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map.comp {γ : Type w} (f : α → β) (g : β → γ) (x) :
    map g (map f x) = map (g ∘ f) x := by
  rcases x with ⟨L⟩; simp [Function.comp_def]

@[to_additive (attr := simp)]
/-
**FreeGroup.map.of** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.map`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {x : α}, (FreeGroup.map f) (FreeGr
oup.of x) = FreeGroup.of (f x)
参数：FreeGroup.map f；FreeGroup.of x；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map.of {x} : map f (of x) = of (f x) :=
  rfl

@[to_additive]
/-
**FreeGroup.map.unique** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.map`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} (g : FreeGroup α →* FreeGroup β), 
  (∀ (x : α), g (FreeGroup.of x) = FreeGroup.of (f x)) → ∀ {x : FreeGroup α}, g 
x = (FreeGroup.map f) x
参数：g : FreeGroup α →* FreeGroup β；∀ (x : α), g (FreeGroup.of x) = FreeGroup.of (
f x)；FreeGroup.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map.unique (g : FreeGroup α →* FreeGroup β)
    (hg : ∀ x, g (FreeGroup.of x) = FreeGroup.of (f x)) :
    ∀ {x}, g x = map f x := by
  rintro ⟨L⟩
  exact List.recOn L g.map_one fun ⟨x, b⟩ t (ih : g (FreeGroup.mk t) = map f (FreeGroup.mk t)) =>
    Bool.recOn b
      (show g ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) =
          FreeGroup.map f ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) by
        simp [g.map_mul, g.map_inv, hg, ih])
      (show g (FreeGroup.of x * FreeGroup.mk t) =
          FreeGroup.map f (FreeGroup.of x * FreeGroup.mk t) by simp [g.map_mul, hg, ih])

@[to_additive]
/-
**FreeGroup.map_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：map_eq_lift : map f = lift (of ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FreeGroup.ext_hom`：ext_hom {M : Type*} [Monoid M] (f g : FreeGroup α ->*
 M) (h : forall a, f (of a) = g (of a)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.lift_apply_of`：lift_apply_of {x} : lift f (of x) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_eq_lift : map f = lift (of ∘ f) := by
  ext; simp

@[to_additive]
/-
**FreeGroup.range_map** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：range_map : (map f).range = Subgroup.closure (of '' Set.range f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.map_eq_lift`：map_eq_lift : map f = lift (of ∘ f)
· 使用定理 `FreeGroup.range_lift_eq_closure`：range_lift_eq_closure : (lift f).range 
= Subgroup.closure (Set.range f)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem range_map : (map f).range = Subgroup.closure (of '' Set.range f) := by
  rw [map_eq_lift, range_lift_eq_closure, Set.range_comp]

/-- If `α` and `β` are arbitrary types and there is a surjection between them,
then the induced map on their free groups is also surjective. -/
@[to_additive /-- If `α` and `β` are arbitrary types and there is a surjection between them,
then the induced map on their additive free groups is also surjective. -/]
/-
**FreeGroup.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：map_surjective (hf : Function.Surjective f) : Function.Surjective (map f)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `FreeGroup.range_map`：range_map : (map f).range = Subgroup.closure (of ''
 Set.range f)
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `FreeGroup.closure_range_of`：closure_range_of (α) : Subgroup.closure (Set
.range (FreeGroup.of : α -> FreeGroup α)) = ⊤
-/
theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) := by
  rw [← MonoidHom.range_eq_top, range_map, hf.range_eq, Set.image_univ, closure_range_of]

/-- If `α` and `β` are arbitrary types and there is an injection between them,
then the induced map on their free groups is also injective. -/
@[to_additive /-- If `α` and `β` are arbitrary types and there is an injection between them,
then the induced map on their additive free groups is also injective. -/]
/-
**FreeGroup.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：map_injective (hf : Function.Injective f) : Function.Injective (map f)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.injective_iff_hasLeftInverse`：injective_iff_hasLeftInverse : In
jective f ↔ HasLeftInverse f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FreeGroup.map.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} (f : α → β)
 (g : β → γ) (x : FreeGroup α),   (FreeGroup.map g) ((FreeGroup.map f) x) = (Fre
eGroup.m…
· 使用定理 `Function.invFun_comp`：invFun_comp (hf : Injective f) : invFun f ∘ f = id
· 使用定理 `FreeGroup.map.id`：∀ {α : Type u} (x : FreeGroup α), (FreeGroup.map id) x
 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) := by
  by_cases! h : IsEmpty α
  · exact Function.injective_of_subsingleton _
  · rw [Function.injective_iff_hasLeftInverse]
    use map (Function.invFun f)
    simp [Function.LeftInverse, map.comp, Function.invFun_comp hf]

/-- If `α` and `β` are arbitrary types and there is a bijection between them,
then the induced map on their free groups is also bijective. -/
@[to_additive /-- If `α` and `β` are arbitrary types and there is a bijection between them,
then the induced map on their additive free groups is also bijective. -/]
/-
**FreeGroup.map_bijective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：map_bijective (hf : Function.Bijective f) : Function.Bijective (map f)
参数：hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.map_injective`：map_injective (hf : Function.Injective f) : Fun
ction.Injective (map f)
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `FreeGroup.map_surjective`：map_surjective (hf : Function.Surjective f) : 
Function.Surjective (map f)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
-/
theorem map_bijective (hf : Function.Bijective f) : Function.Bijective (map f) := by
  exact ⟨map_injective hf.injective, map_surjective hf.surjective⟩

/-- Equivalent types give rise to multiplicatively equivalent free groups.

The converse can be found in `Mathlib/GroupTheory/FreeGroup/GeneratorEquiv.lean`, as
`Equiv.ofFreeGroupEquiv`. -/
@[to_additive (attr := simps apply)
  /-- Equivalent types give rise to additively equivalent additive free groups. -/]
/-
**FreeGroup.freeGroupCongr** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：freeGroupCongr {α β} (e : α ≃ β) : FreeGroup α ≃* FreeGroup β where toFun
参数：e : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def freeGroupCongr {α β} (e : α ≃ β) : FreeGroup α ≃* FreeGroup β where
  toFun := map e
  invFun := map e.symm
  left_inv x := by simp [map.comp]
  right_inv x := by simp [map.comp]
  map_mul' := map_mul _

@[to_additive (attr := simp)]
/-
**FreeGroup.freeGroupCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：freeGroupCongr_refl : freeGroupCongr (Equiv.refl α) = MulEquiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `FreeGroup.map.id`：∀ {α : Type u} (x : FreeGroup α), (FreeGroup.map id) x
 = x
-/
theorem freeGroupCongr_refl : freeGroupCongr (Equiv.refl α) = MulEquiv.refl _ :=
  MulEquiv.ext map.id

@[to_additive (attr := simp)]
/-
**FreeGroup.freeGroupCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：freeGroupCongr_symm {α β} (e : α ≃ β) : (freeGroupCongr e).symm = freeGrou
pCongr e.symm
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem freeGroupCongr_symm {α β} (e : α ≃ β) : (freeGroupCongr e).symm = freeGroupCongr e.symm :=
  rfl

@[to_additive]
/-
**FreeGroup.freeGroupCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：freeGroupCongr_trans {α β γ} (e : α ≃ β) (f : β ≃ γ) : (freeGroupCongr e).
trans (freeGroupCongr f) = freeGroupCongr (e.trans f)
参数：e : α ≃ β；f : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `FreeGroup.map.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} (f : α → β)
 (g : β → γ) (x : FreeGroup α),   (FreeGroup.map g) ((FreeGroup.map f) x) = (Fre
eGroup.m…
-/
theorem freeGroupCongr_trans {α β γ} (e : α ≃ β) (f : β ≃ γ) :
    (freeGroupCongr e).trans (freeGroupCongr f) = freeGroupCongr (e.trans f) :=
  MulEquiv.ext <| map.comp _ _

end Map

section Prod

variable [Group α] (x y : FreeGroup α)

/-- If `α` is a group, then any function from `α` to `α` extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the multiplicative version of `FreeGroup.sum`. -/
@[to_additive /-- If `α` is an additive group, then any function from `α` to `α` extends uniquely
  to an additive homomorphism from the additive free group over `α` to `α`. -/]
/-
**FreeGroup.prod** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：prod : FreeGroup α ->* α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prod : FreeGroup α →* α :=
  lift id

variable {x y}

@[to_additive (attr := simp)]
/-
**FreeGroup.prod_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：prod_mk : prod (mk L) = List.prod (L.map fun x => cond x.2 x.1 x.1⁻¹)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_mk : prod (mk L) = List.prod (L.map fun x => cond x.2 x.1 x.1⁻¹) :=
  rfl

@[to_additive (attr := simp)]
/-
**FreeGroup.prod.of** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.prod`。
形式化陈述：∀ {α : Type u} [inst : Group α] {x : α}, FreeGroup.prod (FreeGroup.of x) =
 x
参数：FreeGroup.of x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.lift_apply_of`：lift_apply_of {x} : lift f (of x) = f x
-/
theorem prod.of {x : α} : prod (of x) = x :=
  lift_apply_of

@[to_additive]
/-
**FreeGroup.prod.unique** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.prod`。
形式化陈述：∀ {α : Type u} [inst : Group α] (g : FreeGroup α →* α),   (∀ (x : α), g (F
reeGroup.of x) = x) → ∀ {x : FreeGroup α}, g x = FreeGroup.prod x
参数：g : FreeGroup α →* α；∀ (x : α), g (FreeGroup.of x) = x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.lift_unique`：lift_unique (g : FreeGroup α ->* β) (hg : forall 
x, g (FreeGroup.of x) = f x) {x} : g x = FreeGroup.lift f x
-/
theorem prod.unique (g : FreeGroup α →* α) (hg : ∀ x, g (FreeGroup.of x) = x) {x} : g x = prod x :=
  lift_unique g hg

@[to_additive]
/-
**FreeGroup.prod_surjective** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：prod_surjective : Function.Surjective (prod : FreeGroup α ->* α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.lift_surjective_of_surjective`：lift_surjective_of_surjective (
hf : Function.Surjective f) : Function.Surjective (lift f)
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
theorem prod_surjective : Function.Surjective (prod : FreeGroup α →* α) :=
  FreeGroup.lift_surjective_of_surjective Function.surjective_id

end Prod

@[to_additive]
/-
**FreeGroup.lift_eq_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：lift_eq_prod_map {β : Type v} [Group β] {f : α -> β} {x} : lift f x = prod
 (map f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.lift_unique`：lift_unique (g : FreeGroup α ->* β) (hg : forall 
x, g (FreeGroup.of x) = f x) {x} : g x = FreeGroup.lift f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FreeGroup.prod.of`：∀ {α : Type u} [inst : Group α] {x : α}, FreeGroup.pr
od (FreeGroup.of x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MonoidHom.coe_comp`：MonoidHom.coe_comp [MulOne M] [MulOne N] [MulOne P] 
(g : N ->* P) (f : M ->* N) : ↑(g.comp f) = g ∘ f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem lift_eq_prod_map {β : Type v} [Group β] {f : α → β} {x} : lift f x = prod (map f x) := by
  rw [← lift_unique (prod.comp (map f)) (by simp), MonoidHom.coe_comp, Function.comp_apply]

section Sum

variable [AddGroup α] (x y : FreeGroup α)

/-- If `α` is a group, then any function from `α` to `α` extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the additive version of `Prod`. -/
/-
**FreeGroup.sum** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：sum : α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a group, then any function from `α` to `α` extends uniquely to a homom
orphism from the
free group over `α` to `α`. This is the additive version of `Prod`.
-/
def sum : α :=
  @prod (Multiplicative _) _ x

variable {x y}

@[simp]
/-
**FreeGroup.sum_mk** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：sum_mk : sum (mk L) = List.sum (L.map fun x => cond x.2 x.1 (-x.1))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_mk : sum (mk L) = List.sum (L.map fun x => cond x.2 x.1 (-x.1)) :=
  rfl

@[simp]
/-
**FreeGroup.sum.of** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.sum`。
形式化陈述：∀ {α : Type u} [inst : AddGroup α] {x : α}, (FreeGroup.of x).sum = x
参数：FreeGroup.of x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.prod.of`：∀ {α : Type u} [inst : Group α] {x : α}, FreeGroup.pr
od (FreeGroup.of x) = x
-/
theorem sum.of {x : α} : sum (of x) = x :=
  @prod.of _ (_) _

-- note: there are no bundled homs with different notation in the domain and codomain, so we copy
-- these manually
@[simp]
/-
**FreeGroup.sum.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.sum`。
形式化陈述：∀ {α : Type u} [inst : AddGroup α] {x y : FreeGroup α}, (x * y).sum = x.su
m + y.sum
参数：x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
theorem sum.map_mul : sum (x * y) = sum x + sum y :=
  (@prod (Multiplicative _) _).map_mul _ _

@[simp]
/-
**FreeGroup.sum.map_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.sum`。
形式化陈述：∀ {α : Type u} [inst : AddGroup α], FreeGroup.sum 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
theorem sum.map_one : sum (1 : FreeGroup α) = 0 :=
  (@prod (Multiplicative _) _).map_one

@[simp]
/-
**FreeGroup.sum.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.sum`。
形式化陈述：∀ {α : Type u} [inst : AddGroup α] {x : FreeGroup α}, x⁻¹.sum = -x.sum
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
-/
theorem sum.map_inv : sum x⁻¹ = -sum x :=
  (prod : FreeGroup (Multiplicative α) →* Multiplicative α).map_inv _

end Sum

/-- The bijection between the free group on the empty type, and a type with one element. -/
@[to_additive
  (attr := deprecated "Use `Equiv.ofUnique (FreeGroup Empty) Unit` instead,
or `MulEquiv.ofUnique (FreeGroup Empty) Unit` for the multiplicative version instead."
(since := "2026-02-11"))
  /-- The bijection between the additive free group on the empty type,
  and a type with one element. -/]
/-
**FreeGroup.freeGroupEmptyEquivUnit** 是 Mathlib 中的一个缩写定义，位于命名空间 `FreeGroup`。
形式化陈述：freeGroupEmptyEquivUnit : FreeGroup Empty ≃ Unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev freeGroupEmptyEquivUnit : FreeGroup Empty ≃ Unit :=
  Equiv.ofUnique (FreeGroup Empty) Unit

/-- The bijection between the free group on a singleton, and the integers. -/
/-
**FreeGroup.freeGroupUnitEquivInt** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：freeGroupUnitEquivInt : FreeGroup Unit ≃ Int where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between the free group on a singleton, and the integers.
-/
def freeGroupUnitEquivInt : FreeGroup Unit ≃ ℤ where
  toFun x := sum (by
    revert x
    exact ↑(map fun _ => (1 : ℤ)))
  invFun x := of () ^ x
  left_inv := by
    rintro ⟨L⟩
    simp only [quot_mk_eq_mk, map.mk, sum_mk, List.map_map]
    exact List.recOn L
     rfl
     (fun ⟨⟨⟩, b⟩ tl ih => by
        cases b <;> simp [zpow_add, ih] <;> rfl)
  right_inv x :=
    Int.induction_on x (by simp)
      (fun i ih => by
        simp only [zpow_natCast, map_pow, map.of] at ih
        simp [zpow_add, ih])
      (fun i ih => by
        simp only [zpow_neg, zpow_natCast, map_inv, map_pow, map.of, sum.map_inv, neg_inj] at ih
        simp [zpow_add, ih, sub_eq_add_neg])

/-- The bijection between the free group on a unique type and the integers. -/
/-
**FreeGroup.equivIntOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：equivIntOfUnique [Unique α] : FreeGroup α ≃ Int where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between the free group on a unique type and the integers.
-/
def equivIntOfUnique [Unique α] : FreeGroup α ≃ ℤ where
  toFun x := sum (map 1 x)
  invFun x := of default ^ x
  left_inv x := by
    induction x with
    | C1 => simp
    | of x => simp [Unique.default_eq x]
    | inv_of x hx => simp [Unique.default_eq x]
    | mul x y hx hy => simp [zpow_add, hx, hy]
  right_inv x := by
    induction x with
    | zero => simp
    | succ x hx => simpa [zpow_add_one] using hx
    | pred x hx => simpa [zpow_sub_one, ← sub_eq_add_neg] using hx

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between the free group on a unique type and the integers. -/
/-
**FreeGroup.mulEquivIntOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：mulEquivIntOfUnique [Unique α] : FreeGroup α ≃* Multiplicative Int where t
oFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The isomorphism between the free group on a unique type and the integers.
-/
def mulEquivIntOfUnique [Unique α] : FreeGroup α ≃* Multiplicative ℤ where
  toFun := Multiplicative.ofAdd ∘ equivIntOfUnique
  invFun := equivIntOfUnique.symm ∘ Multiplicative.toAdd
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by simp [equivIntOfUnique]

/-- A free group over one generator is an instance of a cyclic group. -/
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A free group over one generator is an instance of a cyclic group.
-/
instance [Unique α] : IsCyclic (FreeGroup α) :=
  ⟨of default, fun x => ⟨equivIntOfUnique x, equivIntOfUnique.left_inv x⟩⟩

/-- The isomorphism between the free additive group on a unique type and the integers. -/
/-
**FreeGroup._root_.FreeAddGroup.addEquivIntOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `F
reeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the free additive group on a unique type and the integer
s.
-/
def _root_.FreeAddGroup.addEquivIntOfUnique [Unique α] : FreeAddGroup α ≃+ ℤ where
  toFun x := FreeAddGroup.sum (FreeAddGroup.map 1 x)
  invFun x := x • FreeAddGroup.of default
  left_inv x := by
    induction x with
    | C1 => simp
    | of x => simp [Unique.default_eq x]
    | neg_of x hx => simp [Unique.default_eq x]
    | add x y hx hy => simp [add_zsmul, hx, hy]
  right_inv x := by induction x <;> simp
  map_add' x y := by simp

/-- A free additive group over one generator is an instance of a cyclic group. -/
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A free additive group over one generator is an instance of a cyclic group.
-/
instance [Unique α] : IsAddCyclic (FreeAddGroup α) :=
  ⟨FreeAddGroup.of default, fun x =>
  ⟨_root_.FreeAddGroup.addEquivIntOfUnique x, _root_.FreeAddGroup.addEquivIntOfUnique.left_inv x⟩⟩

section Category

variable {β : Type u}

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad FreeGroup.{u} where
  pure {_α} := of
  map {_α _β f} := map f
  bind {_α _β x f} := lift f x

@[to_additive]
/-
**FreeGroup.map_pure** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：map_pure (f : α -> β) (x : α) : f < > (pure x : FreeGroup α) = pure (f x)
参数：f : α -> β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.map.of`：∀ {α : Type u} {β : Type v} {f : α → β} {x : α}, (Free
Group.map f) (FreeGroup.of x) = FreeGroup.of (f x)
-/
theorem map_pure (f : α → β) (x : α) : f <$> (pure x : FreeGroup α) = pure (f x) :=
  map.of

@[to_additive (attr := simp)]
/-
**FreeGroup.map_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：map_one (f : α -> β) : f < > (1 : FreeGroup α) = 1
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
theorem map_one (f : α → β) : f <$> (1 : FreeGroup α) = 1 :=
  (map f).map_one

@[to_additive (attr := simp)]
/-
**FreeGroup.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：map_mul (f : α -> β) (x y : FreeGroup α) : f < > (x * y) = f < > x * f < >
 y
参数：f : α -> β；x y : FreeGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
theorem map_mul (f : α → β) (x y : FreeGroup α) : f <$> (x * y) = f <$> x * f <$> y :=
  (map f).map_mul x y

@[to_additive (attr := simp)]
/-
**FreeGroup.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：map_inv (f : α -> β) (x : FreeGroup α) : f < > x⁻¹ = (f <$> x)⁻¹
参数：f : α -> β；x : FreeGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
-/
theorem map_inv (f : α → β) (x : FreeGroup α) : f <$> x⁻¹ = (f <$> x)⁻¹ :=
  (map f).map_inv x

@[to_additive]
/-
**FreeGroup.pure_bind** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：pure_bind (f : α -> FreeGroup β) (x) : pure x >>= f = f x
参数：f : α -> FreeGroup β；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.lift_apply_of`：lift_apply_of {x} : lift f (of x) = f x
-/
theorem pure_bind (f : α → FreeGroup β) (x) : pure x >>= f = f x :=
  lift_apply_of

@[to_additive (attr := simp)]
/-
**FreeGroup.one_bind** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：one_bind (f : α -> FreeGroup β) : 1 >>= f = 1
参数：f : α -> FreeGroup β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
theorem one_bind (f : α → FreeGroup β) : 1 >>= f = 1 :=
  (lift f).map_one

@[to_additive (attr := simp)]
/-
**FreeGroup.mul_bind** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：mul_bind (f : α -> FreeGroup β) (x y : FreeGroup α) : x * y >>= f = (x >>=
 f) * (y >>= f)
参数：f : α -> FreeGroup β；x y : FreeGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
theorem mul_bind (f : α → FreeGroup β) (x y : FreeGroup α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  (lift f).map_mul _ _

@[to_additive (attr := simp)]
/-
**FreeGroup.inv_bind** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：inv_bind (f : α -> FreeGroup β) (x : FreeGroup α) : x⁻¹ >>= f = (x >>= f)⁻
¹
参数：f : α -> FreeGroup β；x : FreeGroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
-/
theorem inv_bind (f : α → FreeGroup β) (x : FreeGroup α) : x⁻¹ >>= f = (x >>= f)⁻¹ :=
  (lift f).map_inv _

@[to_additive]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad FreeGroup.{u} := LawfulMonad.mk'
  (id_map := fun x =>
    FreeGroup.induction_on x (map_one id) (fun x => map_pure id x) (fun x ih => by rw [map_inv, ih])
      fun x y ihx ihy => by rw [map_mul, ihx, ihy])
  (pure_bind := fun x f => pure_bind f x)
  (bind_assoc := fun x => by
    refine FreeGroup.induction_on x ?_ ?_ ?_ ?_ <;> simp +instances +contextual [instMonad])
  (bind_pure_comp := fun f x => by
    refine FreeGroup.induction_on x ?_ ?_ ?_ ?_ <;> simp +instances +contextual [instMonad])

end Category

end FreeGroup

