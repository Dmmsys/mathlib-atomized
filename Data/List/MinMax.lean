/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes, Mantas Bakšys
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Data.List.Induction
public import Mathlib.Order.MinMax
public import Mathlib.Order.WithBot

/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f [] = none`

`minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/

@[expose] public section

namespace List

variable {α β : Type*}

section ArgAux

variable (r : α → α → Prop) [DecidableRel r] {l : List α} {o : Option α} {a : α}

/-- Auxiliary definition for `argmax` and `argmin`. -/
/-
**List.argAux** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：argAux (a : Option α) (b : α) : Option α
参数：a : Option α；b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `argmax` and `argmin`.
-/
def argAux (a : Option α) (b : α) : Option α :=
  Option.casesOn a (some b) fun c => if r b c then some b else some c

@[simp]
/-
**List.foldl_argAux_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_argAux_eq_none : l.foldl (argAux r) o = none ↔ l = [] ∧ o = none
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem foldl_argAux_eq_none : l.foldl (argAux r) o = none ↔ l = [] ∧ o = none :=
  List.reverseRecOn l (by simp) fun tl hd => by
    simp only [foldl_append, foldl_cons, argAux, foldl_nil, append_eq_nil_iff]
    cases foldl (argAux r) o tl
    · simp
    · simp only
      split_ifs <;> simp
/-
**List.foldl_argAux_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem foldl_argAux_mem (l) : ∀ a m : α, m ∈ foldl (argAux r) (some a) l → m ∈ a :: l :=
  List.reverseRecOn l (by simp [eq_comm]) <| by
    intro _ _ _ _
    simp only [foldl_append, foldl_cons, foldl_nil, argAux]
    cases _ : foldl _ _ _ <;> grind

@[simp]
/-
**List.argAux_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：argAux_self (hr₀ : Std.Irrefl r) (a : α) : argAux r (some a) a = a
参数：hr₀ : Std.Irrefl r；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Std.Irrefl.irrefl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Irrefl 
r] (a : α), ¬r a a
-/
theorem argAux_self (hr₀ : Std.Irrefl r) (a : α) : argAux r (some a) a = a :=
  if_neg <| hr₀.irrefl _
/-
**List.not_of_mem_foldl_argAux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_of_mem_foldl_argAux (hr₀ : Std.Irrefl r) (hr₁ : IsTrans α r) : forall 
{a m : α} {o : Option α}, a in l -> m in foldl (argAux r) o l -> ¬r a m
参数：hr₀ : Std.Irrefl r；hr₁ : IsTrans α r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.foldl_argAux_eq_none`：foldl_argAux_eq_none : l.foldl (argAux r) o =
 none ↔ l = [] ∧ o = none
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `List.argAux.eq_1`：∀ {α : Type u_1} (r : α → α → Prop) [inst : DecidableR
el r] (a : Option α) (b : α),   List.argAux r a b = Option.casesOn a (some b) fu
n c =>…
· 使用定理 `List.foldl_nil`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → α} {b : α},
 List.foldl f b [] = b
· 使用定理 `List.foldl_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : β
 → α → β} {b : β},   List.foldl f b (a :: l) = List.foldl f (f b a) l
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Std.Irrefl.irrefl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Irrefl 
r] (a : α), ¬r a a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Option.mem_def`：∀ {α : Type u_1} {a : α} {b : Option α}, a ∈ b ↔ b = som
e a
-/
theorem not_of_mem_foldl_argAux (hr₀ : Std.Irrefl r) (hr₁ : IsTrans α r) :
    ∀ {a m : α} {o : Option α}, a ∈ l → m ∈ foldl (argAux r) o l → ¬r a m := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton tl a ih => ?_
  intro b m o hb ho
  rw [foldl_append, foldl_cons, foldl_nil, argAux] at ho
  rcases hf : foldl (argAux r) o tl with - | c
  · rw [hf] at ho
    rw [foldl_argAux_eq_none] at hf
    simp_all [hf.1, hf.2, hr₀.irrefl _]
  rw [hf, Option.mem_def] at ho
  grind +splitIndPred

end ArgAux

section Preorder

variable [Preorder β] [DecidableLT β] {f : α → β} {l : List α} {a m : α}

/-- `argmax f l` returns `some a`, where `f a` is maximal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f a < f b`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmax f [] = none`. -/
@[to_dual
/-- `argmin f l` returns `some a`, where `f a` is minimal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f b < f a`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmin f [] = none`. -/]
/-
**List.argmax** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：argmax (f : α -> β) (l : List α) : Option α
参数：f : α -> β；l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def argmax (f : α → β) (l : List α) : Option α :=
  l.foldl (argAux fun b c => f c < f b) none

@[to_dual (attr := simp)]
/-
**List.argmax_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：argmax_nil (f : α -> β) : argmax f [] = none
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem argmax_nil (f : α → β) : argmax f [] = none :=
  rfl

@[to_dual (attr := simp)]
/-
**List.argmax_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：argmax_singleton {f : α -> β} {a : α} : argmax f [a] = a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem argmax_singleton {f : α → β} {a : α} : argmax f [a] = a :=
  rfl

@[to_dual]
/-
**List.not_lt_of_mem_argmax** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_lt_of_mem_argmax : a in l -> m in argmax f l -> ¬f m < f a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_of_mem_foldl_argAux`：not_of_mem_foldl_argAux (hr₀ : Std.Irrefl 
r) (hr₁ : IsTrans α r) : forall {a m : α} {o : Option α}, a in l -> m in foldl (
argAux r) o l -> ¬…
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
theorem not_lt_of_mem_argmax : a ∈ l → m ∈ argmax f l → ¬f m < f a :=
  not_of_mem_foldl_argAux _ ⟨fun x h => lt_irrefl (f x) h⟩
    ⟨fun _ _ z hxy hyz => lt_trans (a := f z) hyz hxy⟩

@[to_dual]
/-
**List.argmax_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：argmax_concat (f : α -> β) (a : α) (l : List α) : argmax f (l ++ [a]) = Op
tion.casesOn (argmax f l) (some a) fun c => if f c < f a then some a else some c
参数：f : α -> β；a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.argmax.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder β] [i
nst_1 : DecidableLT β] (f : α → β) (l : List α),   List.argmax f l = List.foldl 
(List.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem argmax_concat (f : α → β) (a : α) (l : List α) :
    argmax f (l ++ [a]) =
      Option.casesOn (argmax f l) (some a) fun c => if f c < f a then some a else some c := by
  rw [argmax, argmax]; simp [argAux]

@[to_dual]
/-
**List.argmax_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder β] [inst_1 : DecidableLT 
β] {f : α → β} {l : List α} {m : α},   m ∈ List.argmax f l → m ∈ l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `_private.Mathlib.Data.List.MinMax.0.List.foldl_argAux_mem`：∀ {α : Type u
_1} (r : α → α → Prop) [inst : DecidableRel r] (l : List α) (a m : α),   m ∈ Lis
t.foldl (List.argAux r) (some a) l → m ∈ a :: l
-/
theorem argmax_mem : ∀ {l : List α} {m : α}, m ∈ argmax f l → m ∈ l
  | [], m => by simp
  | hd :: tl, m => by simpa [argmax, argAux] using foldl_argAux_mem _ tl hd m

@[to_dual (attr := simp)]
/-
**List.argmax_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：argmax_eq_none : l.argmax f = none ↔ l = []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem argmax_eq_none : l.argmax f = none ↔ l = [] := by simp [argmax]

end Preorder

section LinearOrder

variable [LinearOrder β] {f : α → β} {l : List α} {a m : α}

@[to_dual]
/-
**List.le_of_mem_argmax** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：le_of_mem_argmax : a in l -> m in argmax f l -> f a <= f m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `List.not_lt_of_mem_argmax`：not_lt_of_mem_argmax : a in l -> m in argmax 
f l -> ¬f m < f a
-/
theorem le_of_mem_argmax : a ∈ l → m ∈ argmax f l → f a ≤ f m := fun ha hm =>
  le_of_not_gt <| not_lt_of_mem_argmax ha hm

@[to_dual]
/-
**List.argmax_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：argmax_cons (f : α -> β) (a : α) (l : List α) : argmax f (a :: l) = Option
.casesOn (argmax f l) (some a) fun c => if f a < f c then some c else some a
参数：f : α -> β；a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `List.argmax_concat`：argmax_concat (f : α -> β) (a : α) (l : List α) : ar
gmax f (l ++ [a]) = Option.casesOn (argmax f l) (some a) fun c => if f c < f a t
hen some…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Lean.Grind.em`：∀ (p : Prop), Grind.alreadyNorm p ∨ Grind.alreadyNorm ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Lean.Grind.Order.le_lt_trans`：∀ {α : Type u_1} [inst : LE α] [inst_1 : L
T α] [Std.LawfulOrderLT α] [Std.IsPreorder α] {a b c : α},   a ≤ b → b < c → a <
 c
· 使用定理 `instLawfulOrderLT_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.Law
fulOrderLT α
· 使用定理 `instIsPreorder_mathlib`：∀ {α : Type u_1} [inst : Preorder α], Std.IsPreo
rder α
· 使用定理 `Lean.Grind.Order.le_of_eq_1`：∀ {α : Type u_1} [inst : LE α] [Std.IsPreor
der α] {a b : α}, a = b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Lean.Grind.Order.lt_le_trans`：∀ {α : Type u_1} [inst : LE α] [inst_1 : L
T α] [Std.LawfulOrderLT α] [Std.IsPreorder α] {a b c : α},   a < b → b ≤ c → a <
 c
· 使用定理 `Lean.Grind.Order.lt_eq_false_of_le`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] {a b : α},   a ≤ b → (b < a)
 = False
· 使用定理 `Lean.Grind.Order.le_trans`：∀ {α : Type u_1} [inst : LE α] [Std.IsPreorde
r α] {a b c : α}, a ≤ b → b ≤ c → a ≤ c
· 使用定理 `Lean.Grind.Order.le_of_eq_2`：∀ {α : Type u_1} [inst : LE α] [Std.IsPreor
der α] {a b : α}, a = b → b ≤ a
· 使用定理 `Lean.Grind.Order.le_of_not_lt`：∀ {α : Type u_1} [inst : LE α] [inst_1 : 
LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] {a b : α}, ¬a < b → b ≤ a
· 使用定理 `Std.IsLinearOrder.toIsLinearPreorder`：∀ {α : Type u} [inst : LE α] [self
 : Std.IsLinearOrder α], Std.IsLinearPreorder α
· 使用定理 `instIsLinearOrder_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], Std.
IsLinearOrder α
· 使用定理 `Lean.Grind.Order.lt_eq_false_of_lt`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] {a b : α},   a < b → (b < a)
 = False
-/
theorem argmax_cons (f : α → β) (a : α) (l : List α) :
    argmax f (a :: l) =
      Option.casesOn (argmax f l) (some a) fun c => if f a < f c then some c else some a :=
  List.reverseRecOn l rfl fun hd tl ih => by
    rw [← cons_append, argmax_concat, ih, argmax_concat]
    rcases h : argmax f hd with - | m
    · simp
    dsimp
    rw [← apply_ite, ← apply_ite]
    grind -abstractProof -- Without `-abstractProof`, `to_dual` gives an error.

variable [DecidableEq α]

@[to_dual]
/-
**List.index_of_argmax** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：index_of_argmax : forall {l : List α} {m : α}, m in argmax f l -> forall {
a}, a in l -> f m <= f a -> l.idxOf m <= l.idxOf a | [], m, _, _, _, _ => by sim
p | hd :: tl, m, hm, a, ha, ham => by simp only [idxOf_cons, argmax_cons, Option
.mem_def] at hm ⊢ cases h : argmax f tl · rw [h] at hm simp_all rw [h] at hm dsi
mp only at hm simp only [cond_eq_ite, beq_iff_eq] obtain ha | ha
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem index_of_argmax :
    ∀ {l : List α} {m : α}, m ∈ argmax f l → ∀ {a}, a ∈ l → f m ≤ f a → l.idxOf m ≤ l.idxOf a
  | [], m, _, _, _, _ => by simp
  | hd :: tl, m, hm, a, ha, ham => by
    simp only [idxOf_cons, argmax_cons, Option.mem_def] at hm ⊢
    cases h : argmax f tl
    · rw [h] at hm
      simp_all
    rw [h] at hm
    dsimp only at hm
    simp only [cond_eq_ite, beq_iff_eq]
    obtain ha | ha := ha <;> split_ifs at hm <;> injection hm with hm <;> subst hm
    · cases not_le_of_gt ‹_› ‹_›
    · rw [if_pos rfl]
    · rw [if_neg, if_neg]
      · exact Nat.succ_le_succ (index_of_argmax h (by assumption) ham)
      · exact ne_of_apply_ne f (lt_of_lt_of_le ‹_› ‹_›).ne
      · exact ne_of_apply_ne _ ‹f hd < f _›.ne
    · rw [if_pos rfl]
      exact Nat.zero_le _

@[to_dual]
/-
**List.mem_argmax_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_argmax_iff : m in argmax f l ↔ m in l ∧ (forall a in l, f a <= f m) ∧ 
forall a in l, f m <= f a -> l.idxOf m <= l.idxOf a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.argmax_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder β] [in
st_1 : DecidableLT β] {f : α → β} {l : List α} {m : α},   m ∈ List.argmax f l → 
m ∈ l
· 使用定理 `List.le_of_mem_argmax`：le_of_mem_argmax : a in l -> m in argmax f l -> f
 a <= f m
· 使用定理 `List.index_of_argmax`：index_of_argmax : forall {l : List α} {m : α}, m i
n argmax f l -> forall {a}, a in l -> f m <= f a -> l.idxOf m <= l.idxOf a | [],
 m, _, _, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_antisymm`：∀ {n m : ℕ}, n ≤ m → m ≤ n → n = m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.idxOf_inj`：idxOf_inj [BEq α] [LawfulBEq α] {l : List α} {x y : α} (
hx : x in l) : idxOf x l = idxOf y l ↔ x = y
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Option.mem_def`：∀ {α : Type u_1} {a : α} {b : Option α}, a ∈ b ↔ b = som
e a
-/
theorem mem_argmax_iff :
    m ∈ argmax f l ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.idxOf m ≤ l.idxOf a :=
  ⟨fun hm => ⟨argmax_mem hm, fun _ ha => le_of_mem_argmax ha hm, fun _ => index_of_argmax hm⟩,
    by
      rintro ⟨hml, ham, hma⟩
      rcases harg : argmax f l with - | n
      · simp_all
      · have :=
          Nat.le_antisymm (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
            (index_of_argmax harg hml (ham _ (argmax_mem harg)))
        rw [(idxOf_inj hml).1 this, Option.mem_def]⟩

@[to_dual]
/-
**List.argmax_eq_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：argmax_eq_some_iff : argmax f l = some m ↔ m in l ∧ (forall a in l, f a <=
 f m) ∧ forall a in l, f m <= f a -> l.idxOf m <= l.idxOf a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_argmax_iff`：mem_argmax_iff : m in argmax f l ↔ m in l ∧ (forall
 a in l, f a <= f m) ∧ forall a in l, f m <= f a -> l.idxOf m <= l.idxOf a
-/
theorem argmax_eq_some_iff :
    argmax f l = some m ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.idxOf m ≤ l.idxOf a :=
  mem_argmax_iff

end LinearOrder

section MaximumMinimum

section Preorder

variable [Preorder α] [DecidableLT α] {l : List α} {a m : α}

/-- `maximum l` returns a `WithBot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]` -/
@[to_dual
/-- `minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]` -/]
/-
**List.maximum** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：maximum (l : List α) : WithBot α
参数：l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def maximum (l : List α) : WithBot α :=
  argmax id l

@[to_dual (attr := simp)]
/-
**List.maximum_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_nil : maximum ([] : List α) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem maximum_nil : maximum ([] : List α) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/-
**List.maximum_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_singleton (a : α) : maximum [a] = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem maximum_singleton (a : α) : maximum [a] = a :=
  rfl

@[to_dual]
/-
**List.maximum_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m -> m in l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.argmax_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder β] [in
st_1 : DecidableLT β] {f : α → β} {l : List α} {m : α},   m ∈ List.argmax f l → 
m ∈ l
-/
theorem maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m → m ∈ l :=
  argmax_mem

@[to_dual (attr := simp)]
/-
**List.maximum_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_eq_bot {l : List α} : l.maximum = ⊥ ↔ l = []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.argmax_eq_none`：argmax_eq_none : l.argmax f = none ↔ l = []
-/
theorem maximum_eq_bot {l : List α} : l.maximum = ⊥ ↔ l = [] :=
  argmax_eq_none

@[to_dual not_lt_minimum_of_mem]
/-
**List.not_maximum_lt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_maximum_lt_of_mem : a in l -> (maximum l : WithBot α) = m -> ¬m < a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_lt_of_mem_argmax`：not_lt_of_mem_argmax : a in l -> m in argmax 
f l -> ¬f m < f a
-/
theorem not_maximum_lt_of_mem : a ∈ l → (maximum l : WithBot α) = m → ¬m < a :=
  not_lt_of_mem_argmax

@[to_dual not_lt_minimum_of_mem']
/-
**List.not_maximum_lt_of_mem'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_maximum_lt_of_mem' (ha : a in l) : ¬maximum l < (a : WithBot α)
参数：ha : a in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `List.not_maximum_lt_of_mem`：not_maximum_lt_of_mem : a in l -> (maximum l
 : WithBot α) = m -> ¬m < a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_maximum_lt_of_mem' (ha : a ∈ l) : ¬maximum l < (a : WithBot α) := by
  cases h : l.maximum <;> simp_all [not_maximum_lt_of_mem ha]

end Preorder

section LinearOrder

variable [LinearOrder α] {l : List α} {a m : α}

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
/-
**List.maximum_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l)
 a
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.argmax_concat`：argmax_concat (f : α -> β) (a : α) (l : List α) : ar
gmax f (l ++ [a]) = Option.casesOn (argmax f l) (some a) fun c => if f c < f a t
hen some…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `max_def_lt`：max_def_lt (a b : α) : max a b = if a < b then b else a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) a := by
  simp only [maximum, argmax_concat, id]
  cases argmax id l
  · exact (max_eq_right bot_le).symm
  · simp [WithBot.some_eq_coe, max_def_lt, WithBot.coe_lt_coe]

@[to_dual minimum_le_of_mem]
/-
**List.le_maximum_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：le_maximum_of_mem : a in l -> (maximum l : WithBot α) = m -> a <= m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.le_of_mem_argmax`：le_of_mem_argmax : a in l -> m in argmax f l -> f
 a <= f m
-/
theorem le_maximum_of_mem : a ∈ l → (maximum l : WithBot α) = m → a ≤ m :=
  le_of_mem_argmax

@[to_dual minimum_le_of_mem']
/-
**List.le_maximum_of_mem'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：le_maximum_of_mem' (ha : a in l) : (a : WithBot α) <= maximum l
参数：ha : a in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `List.not_maximum_lt_of_mem'`：not_maximum_lt_of_mem' (ha : a in l) : ¬max
imum l < (a : WithBot α)
-/
theorem le_maximum_of_mem' (ha : a ∈ l) : (a : WithBot α) ≤ maximum l :=
  le_of_not_gt <| not_maximum_lt_of_mem' ha

@[to_dual]
/-
**List.maximum_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_cons (a : α) (l : List α) : maximum (a :: l) = max ↑a (maximum l)
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `List.maximum_concat`：maximum_concat (a : α) (l : List α) : maximum (l ++
 [a]) = max (maximum l) a
· 使用定理 `max_assoc`：∀ {α : Type u_1} [inst : LinearOrder α] (a b c : α), max (max
 a b) c = max a (max b c)
-/
theorem maximum_cons (a : α) (l : List α) : maximum (a :: l) = max ↑a (maximum l) :=
  List.reverseRecOn l (by simp) fun tl hd ih => by
    rw [← cons_append, maximum_concat, ih, maximum_concat, max_assoc]

@[to_dual]
/-
**List.maximum_append** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：maximum_append (l₁ l₂ : List α) : (l₁ ++ l₂).maximum = max l₁.maximum l₂.m
aximum
参数：l₁ l₂ : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.maximum_cons`：maximum_cons (a : α) (l : List α) : maximum (a :: l) 
= max ↑a (maximum l)
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_assoc`：∀ {α : Type u_1} [inst : LinearOrder α] (a b c : α), max (max
 a b) c = max a (max b c)
-/
lemma maximum_append (l₁ l₂ : List α) : (l₁ ++ l₂).maximum = max l₁.maximum l₂.maximum := by
  induction l₁ with
  | nil => simp
  | cons _ _ ih => rw [maximum_cons, cons_append, maximum_cons, ih, ← max_assoc]

@[to_dual le_minimum_of_forall_le]
/-
**List.maximum_le_of_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_le_of_forall_le {b : WithBot α} (h : forall a in l, a <= b) : l.ma
ximum <= b
参数：h : forall a in l, a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.maximum_cons`：maximum_cons (a : α) (l : List α) : maximum (a :: l) 
= max ↑a (maximum l)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
-/
theorem maximum_le_of_forall_le {b : WithBot α} (h : ∀ a ∈ l, a ≤ b) : l.maximum ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [maximum_cons, max_le_iff]
    exact ⟨h a (by simp), ih fun a w => h a (mem_cons.mpr (Or.inr w))⟩

@[to_dual minimum_anti]
/-
**List.maximum_mono** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_mono {l₁ l₂ : List α} (h : l₁ subseteq l₂) : l₁.maximum <= l₂.maxi
mum
参数：h : l₁ subseteq l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.maximum_le_of_forall_le`：maximum_le_of_forall_le {b : WithBot α} (h
 : forall a in l, a <= b) : l.maximum <= b
· 使用定理 `List.le_maximum_of_mem'`：le_maximum_of_mem' (ha : a in l) : (a : WithBot
 α) <= maximum l
-/
theorem maximum_mono {l₁ l₂ : List α} (h : l₁ ⊆ l₂) : l₁.maximum ≤ l₂.maximum :=
  maximum_le_of_forall_le fun _ ↦ (le_maximum_of_mem' <| h ·)

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
/-
**List.maximum_eq_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_eq_coe_iff : maximum l = m ↔ m in l ∧ forall a in l, a <= m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.maximum.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Decida
bleLT α] (l : List α), l.maximum = List.argmax id l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.some_eq_coe`：some_eq_coe (a : α) : (Option.some a : WithBot α) =
 (↑a : WithBot α)
· 使用定理 `List.argmax_eq_some_iff`：argmax_eq_some_iff : argmax f l = some m ↔ m in
 l ∧ (forall a in l, f a <= f m) ∧ forall a in l, f m <= f a -> l.idxOf m <= l.i
dxOf a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem maximum_eq_coe_iff : maximum l = m ↔ m ∈ l ∧ ∀ a ∈ l, a ≤ m := by
  rw [maximum, ← WithBot.some_eq_coe, argmax_eq_some_iff]
  simp only [id_eq, and_congr_right_iff, and_iff_left_iff_imp]
  intro _ h a hal hma
  rw [_root_.le_antisymm hma (h a hal)]

@[to_dual minimum_le_coe_iff]
/-
**List.coe_le_maximum_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：coe_le_maximum_iff : a <= l.maximum ↔ exists b, b in l ∧ a <= b
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.maximum_cons`：maximum_cons (a : α) (l : List α) : maximum (a :: l) 
= max ↑a (maximum l)
-/
theorem coe_le_maximum_iff : a ≤ l.maximum ↔ ∃ b, b ∈ l ∧ a ≤ b := by
  induction l <;> simp [maximum_cons, *]

@[to_dual]
/-
**List.maximum_ne_bot_of_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_ne_bot_of_ne_nil (h : l != []) : l.maximum != ⊥
参数：h : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.maximum_cons`：maximum_cons (a : α) (l : List α) : maximum (a :: l) 
= max ↑a (maximum l)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem maximum_ne_bot_of_ne_nil (h : l ≠ []) : l.maximum ≠ ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]

@[to_dual]
/-
**List.maximum_ne_bot_of_length_pos** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_ne_bot_of_length_pos (h : 0 < l.length) : l.maximum != ⊥
参数：h : 0 < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.maximum_cons`：maximum_cons (a : α) (l : List α) : maximum (a :: l) 
= max ↑a (maximum l)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem maximum_ne_bot_of_length_pos (h : 0 < l.length) : l.maximum ≠ ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]

/-- The maximum value in a non-empty `List`. -/
@[to_dual /-- The minimum value in a non-empty `List`. -/]
/-
**List.maximum_of_length_pos** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：maximum_of_length_pos (h : 0 < l.length) : α
参数：h : 0 < l.length。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.maximum_ne_bot_of_length_pos`：maximum_ne_bot_of_length_pos (h : 0 <
 l.length) : l.maximum != ⊥

--- 原说明 ---
The maximum value in a non-empty `List`.
-/
def maximum_of_length_pos (h : 0 < l.length) : α :=
  WithBot.unbot l.maximum (maximum_ne_bot_of_length_pos h)

@[to_dual (attr := simp)]
/-
**List.coe_maximum_of_length_pos** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：coe_maximum_of_length_pos (h : 0 < l.length) : (l.maximum_of_length_pos h 
: α) = l.maximum
参数：h : 0 < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
· 使用定理 `List.maximum_ne_bot_of_length_pos`：maximum_ne_bot_of_length_pos (h : 0 <
 l.length) : l.maximum != ⊥
-/
lemma coe_maximum_of_length_pos (h : 0 < l.length) :
    (l.maximum_of_length_pos h : α) = l.maximum :=
  WithBot.coe_unbot _ _

@[to_dual (attr := simp) minimum_of_length_pos_le_iff]
/-
**List.le_maximum_of_length_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：le_maximum_of_length_pos_iff {b : α} (h : 0 < l.length) : b <= maximum_of_
length_pos h ↔ b <= l.maximum
参数：h : 0 < l.length。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.le_unbot_iff`：le_unbot_iff (hx : x != ⊥) : a <= unbot x hx ↔ a <
= x
· 使用定理 `List.maximum_ne_bot_of_length_pos`：maximum_ne_bot_of_length_pos (h : 0 <
 l.length) : l.maximum != ⊥
-/
theorem le_maximum_of_length_pos_iff {b : α} (h : 0 < l.length) :
    b ≤ maximum_of_length_pos h ↔ b ≤ l.maximum :=
  WithBot.le_unbot_iff _

@[to_dual]
/-
**List.maximum_of_length_pos_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：maximum_of_length_pos_mem (h : 0 < l.length) : maximum_of_length_pos h in 
l
参数：h : 0 < l.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.maximum_mem`：maximum_mem {l : List α} {m : α} : (maximum l : WithTo
p α) = m -> m in l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.coe_maximum_of_length_pos`：coe_maximum_of_length_pos (h : 0 < l.len
gth) : (l.maximum_of_length_pos h : α) = l.maximum
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem maximum_of_length_pos_mem (h : 0 < l.length) :
    maximum_of_length_pos h ∈ l := by
  apply maximum_mem
  simp only [coe_maximum_of_length_pos]

@[to_dual minimum_of_length_pos_le_of_mem]
/-
**List.le_maximum_of_length_pos_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：le_maximum_of_length_pos_of_mem (h : a in l) (w : 0 < l.length) : a <= l.m
aximum_of_length_pos w
参数：h : a in l；w : 0 < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.le_maximum_of_mem'`：le_maximum_of_mem' (ha : a in l) : (a : WithBot
 α) <= maximum l
-/
theorem le_maximum_of_length_pos_of_mem (h : a ∈ l) (w : 0 < l.length) :
    a ≤ l.maximum_of_length_pos w := by
  simp only [le_maximum_of_length_pos_iff]
  exact le_maximum_of_mem' h

@[to_dual minimum_of_length_pos_le_getElem]
/-
**List.getElem_le_maximum_of_length_pos** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_le_maximum_of_length_pos {i : Nat} (w : i < l.length) (h
参数：w : i < l.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.le_maximum_of_length_pos_of_mem`：le_maximum_of_length_pos_of_mem (h
 : a in l) (w : 0 < l.length) : a <= l.maximum_of_length_pos w
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
-/
theorem getElem_le_maximum_of_length_pos {i : ℕ} (w : i < l.length) (h := (Nat.zero_lt_of_lt w)) :
    l[i] ≤ l.maximum_of_length_pos h := by
  apply le_maximum_of_length_pos_of_mem
  exact getElem_mem _

@[to_dual]
/-
**List.Perm.maximum_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {l l' : List α}, l.Perm l' → l.max
imum = l'.maximum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Perm.maximum_eq {l l' : List α} (h : l ~ l') :
    l.maximum = l'.maximum := by
  induction h with grind [maximum_cons]


@[to_dual]
/-
**List.getD_max** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：getD_max?_eq_unbotD_maximum (l : List α) (d : α) : l.max?.getD d = l.maxim
um.unbotD d
参数：l : List α；d : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma getD_max?_eq_unbotD_maximum (l : List α) (d : α) : l.max?.getD d = l.maximum.unbotD d := by
  cases hy : l.maximum with
  | bot => simp [List.maximum_eq_bot.mp hy]
  | coe y =>
    rw [List.maximum_eq_coe_iff] at hy
    simp only [WithBot.unbotD_coe]
    cases hz : l.max? with
    | none => simp [List.max?_eq_none_iff.mp hz] at hy
    | some z =>
      have : Std.Antisymm (α := α) (· ≤ ·) := ⟨fun _ _ => _root_.le_antisymm⟩
      rw [List.max?_eq_some_iff] at hz
      · rw [Option.getD_some]
        exact _root_.le_antisymm (hy.right _ hz.left) (hz.right _ hy.left)

end LinearOrder

end MaximumMinimum

section Fold

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {l : List α}

@[to_dual (attr := simp)]
/-
**List.foldr_max_of_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_max_of_ne_nil (h : l != []) : ↑(l.foldr max ⊥) = l.maximum
参数：h : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.maximum_cons`：maximum_cons (a : α) (l : List α) : maximum (a :: l) 
= max ↑a (maximum l)
· 使用定理 `List.foldr.eq_2`：∀ {α : Type u} {β : Type v} (f : α → β → β) (init : β) 
(a : α) (as : List α),   List.foldr f init (a :: as) = f a (List.foldr f init as
)
· 使用引理 `WithBot.coe_max`：coe_max (a b : α) : ↑(max a b) = max (a : WithBot α) b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem foldr_max_of_ne_nil (h : l ≠ []) : ↑(l.foldr max ⊥) = l.maximum := by
  induction l with
  | nil => contradiction
  | cons hd tl IH =>
    rw [maximum_cons, foldr, WithBot.coe_max]
    by_cases h : tl = []
    · simp [h]
    · simp [IH h]

@[to_dual le_min_of_forall_le]
/-
**List.max_le_of_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：max_le_of_forall_le (l : List α) (a : α) (h : forall x in l, x <= a) : l.f
oldr max ⊥ <= a
参数：l : List α；a : α；h : forall x in l, x <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
theorem max_le_of_forall_le (l : List α) (a : α) (h : ∀ x ∈ l, x ≤ a) : l.foldr max ⊥ ≤ a := by
  induction l with
  | nil => simp
  | cons y l IH => simpa [h y mem_cons_self] using IH fun x hx => h x <| mem_cons_of_mem _ hx

@[to_dual min_le_of_le]
/-
**List.le_max_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：le_max_of_le {l : List α} {a x : α} (hx : x in l) (h : a <= x) : a <= l.fo
ldr max ⊥
参数：hx : x in l；h : a <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
-/
theorem le_max_of_le {l : List α} {a x : α} (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max ⊥ := by
  induction l with
  | nil => exact absurd hx not_mem_nil
  | cons y l IH =>
    obtain hl | hl := hx
    · simp only [foldr]
      exact le_max_of_le_left h
    · exact le_max_of_le_right (IH (by assumption))

end OrderBot

/-- If `a ≤ x` for some `x` in the list `l`, and `b : α`, then `a ≤ l.foldr max b`. -/
@[to_dual min_le_of_le']
/-
**List.le_max_of_le'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：le_max_of_le' {l : List α} {a x : α} (b : α) (hx : x in l) (h : a <= x) : 
a <= l.foldr max b
参数：b : α；hx : x in l；h : a <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c

--- 原说明 ---
If `a ≤ x` for some `x` in the list `l`, and `b : α`, then `a ≤ l.foldr max b`.
-/
theorem le_max_of_le' {l : List α} {a x : α} (b : α) (hx : x ∈ l) (h : a ≤ x) :
    a ≤ l.foldr max b := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y l IH =>
    simp only [List.foldr]
    obtain rfl | hl := mem_cons.mp hx
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (IH hl)

end Fold

end List

