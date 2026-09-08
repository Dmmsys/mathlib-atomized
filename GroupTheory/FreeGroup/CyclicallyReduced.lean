/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amir Livne Bar-on, Bernhard Reinke
-/
module

public import Mathlib.Data.List.Induction
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Tactic.Group

/-!
This file defines some extra lemmas for free groups, in particular about cyclically reduced words.
We show that free groups are (strongly) torsion-free in the sense of `IsMulTorsionFree`, i.e.,
taking powers by every non-zero element `n : ℕ` is injective.

## Main declarations

* `FreeGroup.IsCyclicallyReduced`: the predicate for cyclically reduced words

-/

@[expose] public section
open List

universe u

variable {α : Type u}
namespace FreeGroup

variable {L L₁ L₂ L₃ : List (α × Bool)}

/-- Predicate asserting that the word `L` is cyclically reduced, i.e., it is reduced and furthermore
the first and the last letter of the word do not cancel. The empty word is by convention also
cyclically reduced. -/
@[to_additive /-- Predicate asserting that the word `L` is cyclically reduced, i.e., it is reduced
and furthermore the first and the last letter of the word do not cancel. The empty word is by
convention also cyclically reduced. -/]
/-
**FreeGroup.IsCyclicallyReduced** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：IsCyclicallyReduced (L : List (α × Bool)) : Prop
参数：L : List (α × Bool)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsCyclicallyReduced (L : List (α × Bool)) : Prop :=
  IsReduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?, a.1 = b.1 → a.2 = b.2

@[to_additive]
/-
**FreeGroup.isCyclicallyReduced_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup`。
形式化陈述：isCyclicallyReduced_iff : IsCyclicallyReduced L ↔ IsReduced L ∧ forall a i
n L.getLast?, forall b in L.head?, a.1 = b.1 -> a.2 = b.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCyclicallyReduced_iff :
    IsCyclicallyReduced L ↔
    IsReduced L ∧ ∀ a ∈ L.getLast?, ∀ b ∈ L.head?, a.1 = b.1 → a.2 = b.2 := Iff.rfl

@[to_additive]
/-
**FreeGroup.isCyclicallyReduced_cons_append_iff** 是 Mathlib 中的一个定理，位于命名空间 `FreeG
roup`。
形式化陈述：isCyclicallyReduced_cons_append_iff {a b : α × Bool} : IsCyclicallyReduced
 (b :: L ++ [a]) ↔ IsReduced (b :: L ++ [a]) ∧ (a.1 = b.1 -> a.2 = b.2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.isCyclicallyReduced_iff`：isCyclicallyReduced_iff : IsCyclicall
yReduced L ↔ IsReduced L ∧ forall a in L.getLast?, forall b in L.head?, a.1 = b.
1 -> a.2 = b.2
· 使用定理 `List.getLast?_concat`：∀ {α : Type u_1} {l : List α} {a : α}, (l ++ [a]).
getLast? = some a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCyclicallyReduced_cons_append_iff {a b : α × Bool} :
    IsCyclicallyReduced (b :: L ++ [a]) ↔
    IsReduced (b :: L ++ [a]) ∧ (a.1 = b.1 → a.2 = b.2) := by
  rw [isCyclicallyReduced_iff, List.getLast?_concat]
  simp

namespace IsCyclicallyReduced

@[to_additive (attr := simp)]
/-
**FreeGroup.IsCyclicallyReduced.nil** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.IsCycli
callyReduced`。
形式化陈述：∀ {α : Type u}, FreeGroup.IsCyclicallyReduced []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
protected theorem nil : IsCyclicallyReduced ([] : List (α × Bool)) := by
  simp [IsCyclicallyReduced]

@[to_additive (attr := simp)]
/-
**FreeGroup.IsCyclicallyReduced.singleton** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.I
sCyclicallyReduced`。
形式化陈述：∀ {α : Type u} {x : α × Bool}, FreeGroup.IsCyclicallyReduced [x]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
protected theorem singleton {x : (α × Bool)} : IsCyclicallyReduced [x] := by
  simp [IsCyclicallyReduced]


@[to_additive]
/-
**FreeGroup.IsCyclicallyReduced.isReduced** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.I
sCyclicallyReduced`。
形式化陈述：isReduced (h : IsCyclicallyReduced L) : IsReduced L
参数：h : IsCyclicallyReduced L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isReduced (h : IsCyclicallyReduced L) : IsReduced L := h.1

@[to_additive]
/-
**FreeGroup.IsCyclicallyReduced.flatten_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Fre
eGroup.IsCyclicallyReduced`。
形式化陈述：flatten_replicate (h : IsCyclicallyReduced L) (n : Nat) : IsCyclicallyRedu
ced (List.replicate n L).flatten
参数：h : IsCyclicallyReduced L；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatten_replicate_nil`：∀ {n : ℕ} {α : Type u_1}, (List.replicate n 
[]).flatten = []
· 使用定理 `FreeGroup.isCyclicallyReduced_iff`：isCyclicallyReduced_iff : IsCyclicall
yReduced L ↔ IsReduced L ∧ forall a in L.getLast?, forall b in L.head?, a.1 = b.
1 -> a.2 = b.2
· 使用定理 `FreeGroup.IsReduced.eq_1`：∀ {α : Type u} (L : List (α × Bool)), FreeGrou
p.IsReduced L = List.IsChain (fun a b => a.1 = b.1 → a.2 = b.2) L
· 使用定理 `List.isChain_flatten`：∀ {α : Type u_1} {R : α → α → Prop} {L : List (Lis
t α)},   [] ∉ L →     (List.IsChain R L.flatten ↔       (∀ l ∈ L, List.IsChain R
 l) ∧ List…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `FreeGroup.IsCyclicallyReduced.isReduced`：isReduced (h : IsCyclicallyRedu
ced L) : IsReduced L
· 使用定理 `List.isChain_replicate_of_rel`：isChain_replicate_of_rel (n : Nat) {a : α
} (h : r a a) : IsChain r (replicate n a)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.getLast?_flatten_replicate`：∀ {α : Type u} {n : ℕ}, n ≠ 0 → ∀ (l : 
List α), (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Option.mem_def`：∀ {α : Type u_1} {a : α} {b : Option α}, a ∈ b ↔ b = som
e a
· 使用定理 `List.head?_flatten_replicate`：∀ {α : Type u} {n : ℕ}, n ≠ 0 → ∀ (l : Lis
t α), (List.replicate n l).flatten.head? = l.head?
-/
theorem flatten_replicate (h : IsCyclicallyReduced L) (n : ℕ) :
    IsCyclicallyReduced (List.replicate n L).flatten := by match n, L with
  | 0, _ => simp
  | n + 1, [] => simp
  | n + 1, (head :: tail) =>
    rw [isCyclicallyReduced_iff, IsReduced, List.isChain_flatten (by simp)]
    refine ⟨⟨by simpa [IsReduced] using h.isReduced, List.isChain_replicate_of_rel _ h.2⟩,
      fun _ ha _ hb ↦ ?_⟩
    rw [Option.mem_def, List.getLast?_flatten_replicate (h := by simp +arith)] at ha
    rw [Option.mem_def, List.head?_flatten_replicate (h := by simp +arith)] at hb
    exact h.2 _ ha _ hb

end IsCyclicallyReduced

@[to_additive]
/-
**FreeGroup.IsReduced.append_flatten_replicate_append** 是 Mathlib 中的一个定理，位于命名空间 
`FreeGroup.IsReduced`。
形式化陈述：∀ {α : Type u} {L₁ L₂ L₃ : List (α × Bool)},   FreeGroup.IsCyclicallyReduc
ed L₂ →     FreeGroup.IsReduced (L₁ ++ L₂ ++ L₃) →       ∀ {n : ℕ}, n ≠ 0 → Free
Group.IsReduced (L₁ ++ (List.replicate n L₂).flatten ++ L₃)
参数：α × Bool；L₁ ++ L₂ ++ L₃；L₁ ++ (List.replicate n L₂).flatten ++ L₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.flatten_replicate_nil`：∀ {n : ℕ} {α : Type u_1}, (List.replicate n 
[]).flatten = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `FreeGroup.IsReduced.append_overlap`：∀ {α : Type u} {L₁ L₂ L₃ : List (α ×
 Bool)},   FreeGroup.IsReduced (L₁ ++ L₂) → FreeGroup.IsReduced (L₂ ++ L₃) → L₂ 
≠ [] → FreeGroup.IsReduc…
· 使用定理 `List.replicate_succ`：∀ {α : Type u} {a : α} {n : ℕ}, List.replicate (n +
 1) a = a :: List.replicate n a
· 使用定理 `List.flatten_cons`：∀ {α : Type u_1} {l : List α} {L : List (List α)}, (l
 :: L).flatten = l ++ L.flatten
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `FreeGroup.IsReduced.infix`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, Fre
eGroup.IsReduced L₂ → L₁ <:+: L₂ → FreeGroup.IsReduced L₁
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FreeGroup.IsCyclicallyReduced.isReduced`：isReduced (h : IsCyclicallyRedu
ced L) : IsReduced L
· 使用定理 `FreeGroup.IsCyclicallyReduced.flatten_replicate`：flatten_replicate (h : 
IsCyclicallyReduced L) (n : Nat) : IsCyclicallyReduced (List.replicate n L).flat
ten
· 使用定理 `List.replicate_succ'`：∀ {n : ℕ} {α : Type u_1} {a : α}, List.replicate (
n + 1) a = List.replicate n a ++ [a]
· 使用定理 `List.flatten_concat`：∀ {α : Type u_1} {L : List (List α)} {l : List α}, 
(L ++ [l]).flatten = L.flatten ++ l
-/
theorem IsReduced.append_flatten_replicate_append (h₁ : IsCyclicallyReduced L₂)
    (h₂ : IsReduced (L₁ ++ L₂ ++ L₃)) {n : ℕ} (hn : n ≠ 0) :
  IsReduced (L₁ ++ (List.replicate n L₂).flatten ++ L₃) := by
  match n with
  | 0 => contradiction
  | n + 1 =>
    if h : L₂ = [] then simp_all else
    have h' : (replicate (n + 1) L₂).flatten ≠ [] := by simp [h]
    refine IsReduced.append_overlap ?_ ?_ (hn := h')
    · rw [replicate_succ, flatten_cons, ← append_assoc]
      refine IsReduced.append_overlap (h₂.infix ⟨[], L₃, by simp⟩) ?_ h
      rw [← flatten_cons, ← replicate_succ]
      exact (h₁.flatten_replicate _).isReduced
    · rw [replicate_succ', flatten_concat]
      refine IsReduced.append_overlap ?_ (h₂.infix ⟨L₁, [], by simp⟩) h
      rw [← flatten_concat, ← replicate_succ']
      exact (h₁.flatten_replicate _).isReduced

/-- This function produces a subword of a word `L` by cancelling the first and last letters of `L`
as long as possible. If `L` is reduced, the resulting word will be cyclically reduced. -/
@[to_additive /-- This function produces a subword of a word `L` by cancelling the first and last
letters of `L` as long as possible. If `L` is reduced, the resulting word will be cyclically
reduced. -/]
/-
**FreeGroup.reduceCyclically** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup`。
形式化陈述：reduceCyclically [DecidableEq α] : List (α × Bool) -> List (α × Bool)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def reduceCyclically [DecidableEq α] : List (α × Bool) → List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun x => [x])
    (cons_append := fun a L b rC => if b.1 = a.1 ∧ (!b.2) = a.2 then rC else a :: L ++ [b])

namespace reduceCyclically
variable [DecidableEq α]

@[to_additive (attr := simp)]
/-
**FreeGroup.reduceCyclically.nil** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.reduceCycl
ically`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α], FreeGroup.reduceCyclically [] = []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `List.bidirectionalRec_nil`：bidirectionalRec_nil {motive : List α -> Sort
*} (nil : motive []) (singleton : forall a : α, motive [a]) (cons_append : foral
l (a : α) (l : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem nil : reduceCyclically ([] : List (α × Bool)) = [] := by simp [reduceCyclically]

@[to_additive (attr := simp)]
/-
**FreeGroup.reduceCyclically.singleton** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.redu
ceCyclically`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] {a : α × Bool}, FreeGroup.reduceCycl
ically [a] = [a]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `List.bidirectionalRec_singleton`：bidirectionalRec_singleton {motive : Li
st α -> Sort*} (nil : motive []) (singleton : forall a : α, motive [a]) (cons_ap
pend : forall (a : α)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem singleton {a : α × Bool} : reduceCyclically [a] = [a] := by
  simp [reduceCyclically]

@[to_additive]
/-
**FreeGroup.reduceCyclically.cons_append** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup.re
duceCyclically`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] {a b : α × Bool} (L : List (α × Bool
)),   FreeGroup.reduceCyclically (a :: (L ++ [b])) =     if b.1 = a.1 ∧ (!b.2) =
 a.2 then FreeGroup.reduceCyclically L else a :: L ++ [b]
参数：L : List (α × Bool)；a :: (L ++ [b])；!b.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `List.bidirectionalRec_cons_append`：bidirectionalRec_cons_append {motive 
: List α -> Sort*} (nil : motive []) (singleton : forall a : α, motive [a]) (con
s_append : forall (a : …
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem cons_append {a b : α × Bool} (L : List (α × Bool)) :
    reduceCyclically (a :: (L ++ [b])) =
    if b.1 = a.1 ∧ (!b.2) = a.2 then reduceCyclically L else a :: L ++ [b] := by
  simp [reduceCyclically]


@[to_additive]
/-
**FreeGroup.reduceCyclically.isCyclicallyReduced** 是 Mathlib 中的一个定理，位于命名空间 `Free
Group.reduceCyclically`。
形式化陈述：isCyclicallyReduced (h : IsReduced L) : IsCyclicallyReduced (reduceCyclica
lly L)
参数：h : IsReduced L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeGroup.reduceCyclically.nil`：∀ {α : Type u} [inst : DecidableEq α], F
reeGroup.reduceCyclically [] = []
· 使用定理 `FreeGroup.reduceCyclically.singleton`：∀ {α : Type u} [inst : DecidableEq
 α] {a : α × Bool}, FreeGroup.reduceCyclically [a] = [a]
· 使用定理 `FreeGroup.reduceCyclically.cons_append`：∀ {α : Type u} [inst : Decidable
Eq α] {a b : α × Bool} (L : List (α × Bool)),   FreeGroup.reduceCyclically (a ::
 (L ++ [b])) =     if b.1 = …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `FreeGroup.isCyclicallyReduced_cons_append_iff`：isCyclicallyReduced_cons_
append_iff {a b : α × Bool} : IsCyclicallyReduced (b :: L ++ [a]) ↔ IsReduced (b
 :: L ++ [a]) ∧ (a.1 = b.1 -> a.2 =…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `FreeGroup.IsReduced.infix`：∀ {α : Type u} {L₁ L₂ : List (α × Bool)}, Fre
eGroup.IsReduced L₂ → L₁ <:+: L₂ → FreeGroup.IsReduced L₁
-/
theorem isCyclicallyReduced (h : IsReduced L) : IsCyclicallyReduced (reduceCyclically L) := by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b ih =>
    rw [reduceCyclically.cons_append]
    split
    case isTrue => exact ih (h.infix ⟨[a], [b], rfl⟩)
    case isFalse h' =>
      rw [isCyclicallyReduced_cons_append_iff]
      exact ⟨h, by simpa using h'⟩

/-- Partner function to `reduceCyclically`.
See `reduceCyclically.conj_conjugator_reduceCyclically`. -/
@[to_additive /-- Partner function to `reduceCyclically`.
See `reduceCyclically.conj_conjugator_reduceCyclically`. -/]
/-
**FreeGroup.reduceCyclically.conjugator** 是 Mathlib 中的一个定义，位于命名空间 `FreeGroup.red
uceCyclically`。
形式化陈述：conjugator : List (α × Bool) -> List (α × Bool)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def conjugator : List (α × Bool) → List (α × Bool) :=
  List.bidirectionalRec
    (nil := [])
    (singleton := fun _ => [])
    (cons_append := fun a _ b rCC => if b.1 = a.1 ∧ (!b.2) = a.2 then a :: rCC else [] )

@[to_additive (attr := simp)]
/-
**FreeGroup.reduceCyclically.conjugator.nil** 是 Mathlib 中的一个定理，位于命名空间 `FreeGroup
.reduceCyclically.conjugator`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α], FreeGroup.reduceCyclically.conjugat
or [] = []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `List.bidirectionalRec_nil`：bidirectionalRec_nil {motive : List α -> Sort
*} (nil : motive []) (singleton : forall a : α, motive [a]) (cons_append : foral
l (a : α) (l : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem conjugator.nil : conjugator ([] : List (α × Bool)) = [] := by simp [conjugator]

@[to_additive (attr := simp)]
/-
**FreeGroup.reduceCyclically.conjugator.singleton** 是 Mathlib 中的一个定理，位于命名空间 `Fre
eGroup.reduceCyclically.conjugator`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] {a : α × Bool}, FreeGroup.reduceCycl
ically.conjugator [a] = []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `List.bidirectionalRec_singleton`：bidirectionalRec_singleton {motive : Li
st α -> Sort*} (nil : motive []) (singleton : forall a : α, motive [a]) (cons_ap
pend : forall (a : α)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem conjugator.singleton {a : α × Bool} : conjugator [a] = [] := by simp [conjugator]

@[to_additive]
/-
**FreeGroup.reduceCyclically.conjugator.cons_append** 是 Mathlib 中的一个定理，位于命名空间 `F
reeGroup.reduceCyclically.conjugator`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] {a b : α × Bool} (L : List (α × Bool
)),   FreeGroup.reduceCyclically.conjugator (a :: (L ++ [b])) =     if b.1 = a.1
 ∧ (!b.2) = a.2 then a :: FreeGroup.reduceCyclically.conjugator L else []
参数：L : List (α × Bool)；a :: (L ++ [b])；!b.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `List.bidirectionalRec_cons_append`：bidirectionalRec_cons_append {motive 
: List α -> Sort*} (nil : motive []) (singleton : forall a : α, motive [a]) (con
s_append : forall (a : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem conjugator.cons_append {a b : α × Bool} (L : List (α × Bool)) :
    conjugator (a :: (L ++ [b])) = if b.1 = a.1 ∧ (!b.2) = a.2 then a :: conjugator L else [] := by
  simp [conjugator]

@[to_additive]
/-
**FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically** 是 Mathlib 中的一个定理
，位于命名空间 `FreeGroup.reduceCyclically`。
形式化陈述：conj_conjugator_reduceCyclically (L : List (α × Bool)) : conjugator L ++ r
educeCyclically L ++ invRev (conjugator L) = L
参数：L : List (α × Bool)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FreeGroup.reduceCyclically.conjugator.nil`：∀ {α : Type u} [inst : Decida
bleEq α], FreeGroup.reduceCyclically.conjugator [] = []
· 使用定理 `FreeGroup.reduceCyclically.nil`：∀ {α : Type u} [inst : DecidableEq α], F
reeGroup.reduceCyclically [] = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FreeGroup.reduceCyclically.conjugator.singleton`：∀ {α : Type u} [inst : 
DecidableEq α] {a : α × Bool}, FreeGroup.reduceCyclically.conjugator [a] = []
· 使用定理 `FreeGroup.reduceCyclically.singleton`：∀ {α : Type u} [inst : DecidableEq
 α] {a : α × Bool}, FreeGroup.reduceCyclically [a] = [a]
· 使用定理 `FreeGroup.reduceCyclically.cons_append`：∀ {α : Type u} [inst : Decidable
Eq α] {a b : α × Bool} (L : List (α × Bool)),   FreeGroup.reduceCyclically (a ::
 (L ++ [b])) =     if b.1 = …
· 使用定理 `FreeGroup.reduceCyclically.conjugator.cons_append`：∀ {α : Type u} [inst 
: DecidableEq α] {a b : α × Bool} (L : List (α × Bool)),   FreeGroup.reduceCycli
cally.conjugator (a :: (L ++ [b])) =   …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Bool.not_not`：∀ (b : Bool), (!!b) = b
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
-/
theorem conj_conjugator_reduceCyclically (L : List (α × Bool)) :
    conjugator L ++ reduceCyclically L ++ invRev (conjugator L) = L := by
  induction L using List.bidirectionalRec
  case nil => simp
  case singleton => simp
  case cons_append a l b eq =>
    rw [reduceCyclically.cons_append, conjugator.cons_append]
    split
    case isTrue h =>
      nth_rw 4 [← eq]
      simp [invRev, h.1.symm, h.2.symm]
    case isFalse => simp

@[to_additive]
/-
**FreeGroup.reduceCyclically.reduce_flatten_replicate_succ** 是 Mathlib 中的一个定理，位于
命名空间 `FreeGroup.reduceCyclically`。
形式化陈述：reduce_flatten_replicate_succ (h : IsReduced L) (n : Nat) : reduce (List.r
eplicate (n + 1) L).flatten = conjugator L ++ (List.replicate (n + 1) (reduceCyc
lically L)).flatten ++ invRev (conjugator L)
参数：h : IsReduced L；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically`：conj_conjug
ator_reduceCyclically (L : List (α × Bool)) : conjugator L ++ reduceCyclically L
 ++ invRev (conjugator L) = L
· 使用定理 `List.replicate_succ`：∀ {α : Type u} {a : α} {n : ℕ}, List.replicate (n +
 1) a = a :: List.replicate n a
· 使用定理 `List.flatten_cons`：∀ {α : Type u_1} {l : List α} {L : List (List α)}, (l
 :: L).flatten = l ++ L.flatten
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeGroup.reduce_append_reduce_reduce`：reduce_append_reduce_reduce : red
uce (reduce L₁ ++ reduce L₂) = reduce (L₁ ++ L₂)
· 使用定理 `FreeGroup.IsReduced.reduce_eq`：∀ {α : Type u_1} {L : List (α × Bool)} [i
nst : DecidableEq α], FreeGroup.IsReduced L → FreeGroup.reduce L = L
· 使用定理 `FreeGroup.reduce.sound`：∀ {α : Type u_1} {L₁ L₂ : List (α × Bool)} [inst
 : DecidableEq α],   FreeGroup.mk L₁ = FreeGroup.mk L₂ → FreeGroup.reduce L₁ = F
reeGroup.red…
· 使用定理 `FreeGroup.mul_mk`：mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂)
· 使用定理 `FreeGroup.inv_mk`：inv_mk : (mk L)⁻¹ = mk (invRev L)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Group._zpow_trick_one'`：_zpow_trick_one' {G : Type*} [Gro
up G] (a b : G) (n : Int) : a * b ^ n * b = a * b ^ (n + 1)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FreeGroup.isReduced_iff_reduce_eq`：isReduced_iff_reduce_eq : IsReduced L
 ↔ reduce L = L where mp h
· 使用定理 `FreeGroup.IsReduced.append_flatten_replicate_append`：∀ {α : Type u} {L₁ 
L₂ L₃ : List (α × Bool)},   FreeGroup.IsCyclicallyReduced L₂ →     FreeGroup.IsR
educed (L₁ ++ L₂ ++ L₃) →       ∀ {n : ℕ}…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FreeGroup.reduceCyclically.isCyclicallyReduced`：isCyclicallyReduced (h :
 IsReduced L) : IsCyclicallyReduced (reduceCyclically L)
-/
theorem reduce_flatten_replicate_succ (h : IsReduced L) (n : ℕ) :
    reduce (List.replicate (n + 1) L).flatten = conjugator L ++
    (List.replicate (n + 1) (reduceCyclically L)).flatten ++ invRev (conjugator L) := by
  induction n
  case zero =>
    simpa [← append_assoc, conj_conjugator_reduceCyclically, ← isReduced_iff_reduce_eq]
  case succ n ih =>
    rw [replicate_succ, flatten_cons, ← reduce_append_reduce_reduce, ih, h.reduce_eq]
    nth_rewrite 1 [← conj_conjugator_reduceCyclically L]
    have {L₁ L₂ L₃ L₄ L₅ : List (α × Bool)} : reduce (L₁ ++ L₂ ++ invRev L₃ ++ (L₃ ++ L₄ ++ L₅)) =
        reduce (L₁ ++ (L₂ ++ L₄) ++ L₅) := by
      apply reduce.sound
      repeat rw [← mul_mk]
      rw [← inv_mk]
      group
    rw [this, ← flatten_cons, ← replicate_succ, ← isReduced_iff_reduce_eq]
    apply IsReduced.append_flatten_replicate_append (hn := by simp)
    · exact isCyclicallyReduced h
    · rwa [conj_conjugator_reduceCyclically]

@[to_additive]
/-
**FreeGroup.reduceCyclically.reduce_flatten_replicate** 是 Mathlib 中的一个定理，位于命名空间 
`FreeGroup.reduceCyclically`。
形式化陈述：reduce_flatten_replicate (h : IsReduced L) (n : Nat) : reduce (List.replic
ate n L).flatten = if n = 0 then [] else conjugator L ++ (List.replicate n (redu
ceCyclically L)).flatten ++ invRev (conjugator L)
参数：h : IsReduced L；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FreeGroup.reduceCyclically.reduce_flatten_replicate_succ`：reduce_flatten
_replicate_succ (h : IsReduced L) (n : Nat) : reduce (List.replicate (n + 1) L).
flatten = conjugator L ++ (List.replicate (n +…
-/
theorem reduce_flatten_replicate (h : IsReduced L) (n : ℕ) :
    reduce (List.replicate n L).flatten = if n = 0 then [] else conjugator L ++
    (List.replicate n (reduceCyclically L)).flatten ++ invRev (conjugator L) :=
  match n with
  | 0 => by simp
  | n + 1 => reduce_flatten_replicate_succ h n

end reduceCyclically

section IsMulTorsionFree
open reduceCyclically

/-- Free groups are torsion-free, i.e., taking powers is injective. Our proof idea is as follows:
if `x ^ n = y ^ n`, then also `x ^ (2 * n) = y ^ (2 * n)`. We then compare the reduced words
representing the powers in terms of the cyclic reductions of `x.toWord` and `y.toWord` using
`reduce_flatten_replicate`. We conclude that the cyclic reductions of `x.toWord` and `y.toWord` must
have the same length, and in fact they have to agree. -/
@[to_additive /-- Free additive groups are torsion free, i.e., scalar multiplication by every
non-zero element `n : ℕ` is injective. See the instance for free groups for an overview over the
proof. -/]
/-
**FreeGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMulTorsionFree (FreeGroup α) where
  pow_left_injective n hn x y heq := by
    classical
    let f (a : FreeGroup α) (n : ℕ) : ℕ :=
        (conjugator a.toWord).length + (n * (reduceCyclically a.toWord).length +
          (conjugator a.toWord).length)
    let g (a : FreeGroup α) (k : ℕ) : List (α × Bool) :=
        conjugator a.toWord ++ ((replicate k (reduceCyclically a.toWord)).flatten ++
          invRev (conjugator a.toWord))
    have heq₂ : x ^ (2 * n) = y ^ (2 * n) := by simp_rw [mul_comm, pow_mul, heq]
    replace heq : g x n = g y n := by
      simpa [toWord_pow, reduce_flatten_replicate, isReduced_toWord, hn] using congr_arg toWord heq
    replace heq₂ : g x (2 * n) = g y (2 * n) := by
      simpa [toWord_pow, reduce_flatten_replicate, isReduced_toWord, hn] using congr_arg toWord heq₂
    have leq : f x n = f y n := by simpa [g] using congr_arg List.length heq
    have leq₂ : f x (2 * n) = f y (2 * n) := by simpa [g] using congr_arg List.length heq₂
    obtain ⟨hc, heq'⟩ := List.append_inj heq (by grind)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    have hm : reduceCyclically x.toWord = reduceCyclically y.toWord := by
      simp only [replicate_succ, flatten_cons, append_assoc] at heq'
      exact (List.append_inj heq' <| mul_left_cancel₀ hn <| by grind).1
    have := congr_arg mk <| (conj_conjugator_reduceCyclically x.toWord).symm
    rwa [hc, hm, conj_conjugator_reduceCyclically, mk_toWord, mk_toWord] at this

end IsMulTorsionFree
end FreeGroup

