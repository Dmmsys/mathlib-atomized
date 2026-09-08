/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Common
public import Mathlib.Util.CompileInductive

/-! ### Induction principles for lists -/

@[expose] public section

variable {α : Type*}

namespace List

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_elim]
/-
**List.reverseRec** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} →   {motive : List α → Sort u_2} →     motive [] → ((l : Li
st α) → (a : α) → motive l → motive (l ++ [a])) → (l : List α) → motive l
参数：(l : List α) → (a : α) → motive l → motive (l ++ [a])；l : List α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []

--- 原说明 ---
Induction principle from the right for lists: if a property holds for the empty 
list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle i
s given for
a `Sort`-valued predicate, i.e., it can also be used to construct data.
-/
def reverseRec {motive : List α → Sort*} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : ∀ l, motive l
  | [] => nil
  | a :: l => (dropLast_concat_getLast (cons_ne_nil a l)) ▸
    append_singleton _ _ ((a :: l).dropLast.reverseRec nil append_singleton)
  termination_by l => l.length

@[simp]
/-
**List.reverseRec_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverseRec_nil {motive : List α -> Sort*} (nil : motive []) (append_single
ton : forall (l : List α) (a : α), motive l -> motive (l ++ [a])) : [].reverseRe
c nil append_singleton = nil
参数：nil : motive []；append_singleton : forall (l : List α) (a : α), motive l -> m
otive (l ++ [a])。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverseRec_nil {motive : List α → Sort*} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    [].reverseRec nil append_singleton = nil := by grind [reverseRec]

@[simp]
/-
**List.reverseRec_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverseRec_concat {motive : List α -> Sort*} (x : α) (xs : List α) (nil : 
motive []) (append_singleton : forall (l : List α) (a : α), motive l -> motive (
l ++ [a])) : (xs ++ [x]).reverseRec nil append_singleton = append_singleton xs x
 (xs.reverseRec nil append_singleton)
参数：x : α；xs : List α；nil : motive []；append_singleton : forall (l : List α) (a :
 α), motive l -> motive (l ++ [a])。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reverseRec_concat {motive : List α → Sort*} (x : α) (xs : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    (xs ++ [x]).reverseRec nil append_singleton =
    append_singleton xs x (xs.reverseRec nil append_singleton) := by
  grind [reverseRec, cases List]

/-- Like `reverseRec`, but with the list parameter placed first. -/
@[elab_as_elim]
/-
**List.reverseRecOn** 是 Mathlib 中的一个缩写定义，位于命名空间 `List`。
形式化陈述：reverseRecOn {motive : List α -> Sort*} (l : List α) (nil : motive []) (ap
pend_singleton : forall (l : List α) (a : α), motive l -> motive (l ++ [a])) : m
otive l
参数：l : List α；nil : motive []；append_singleton : forall (l : List α) (a : α), mo
tive l -> motive (l ++ [a])。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Like `reverseRec`, but with the list parameter placed first.
-/
abbrev reverseRecOn {motive : List α → Sort*} (l : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : motive l :=
  reverseRec nil append_singleton l
/-
**List.reverseRecOn_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverseRecOn_nil {motive : List α -> Sort*} (nil : motive []) (append_sing
leton : forall (l : List α) (a : α), motive l -> motive (l ++ [a])) : reverseRec
On [] nil append_singleton = nil
参数：nil : motive []；append_singleton : forall (l : List α) (a : α), motive l -> m
otive (l ++ [a])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverseRec_nil`：reverseRec_nil {motive : List α -> Sort*} (nil : mo
tive []) (append_singleton : forall (l : List α) (a : α), motive l -> motive (l 
++ [a])) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverseRecOn_nil {motive : List α → Sort*} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    reverseRecOn [] nil append_singleton = nil := by simp
/-
**List.reverseRecOn_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：reverseRecOn_concat {motive : List α -> Sort*} (x : α) (xs : List α) (nil 
: motive []) (append_singleton : forall (l : List α) (a : α), motive l -> motive
 (l ++ [a])) : (xs ++ [x]).reverseRecOn nil append_singleton = append_singleton 
xs x (reverseRecOn xs nil append_singleton)
参数：x : α；xs : List α；nil : motive []；append_singleton : forall (l : List α) (a :
 α), motive l -> motive (l ++ [a])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverseRec_concat`：reverseRec_concat {motive : List α -> Sort*} (x 
: α) (xs : List α) (nil : motive []) (append_singleton : forall (l : List α) (a 
: α), motive…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverseRecOn_concat {motive : List α → Sort*} (x : α) (xs : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    (xs ++ [x]).reverseRecOn nil append_singleton =
      append_singleton xs x (reverseRecOn xs nil append_singleton) := by simp

/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
@[elab_as_elim]
/-
**List.bidirectionalRec** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} →   {motive : List α → Sort u_2} →     motive [] →       ((
a : α) → motive [a]) →         ((a : α) → (l : List α) → (b : α) → motive l → mo
tive (a :: (l ++ [b]))) → (l : List α) → motive l
参数：(a : α) → motive [a]；(a : α) → (l : List α) → (b : α) → motive l → motive (a 
:: (l ++ [b]))；l : List α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []

--- 原说明 ---
Bidirectional induction principle for lists: if a property holds for the empty l
ist, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. Thi
s can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued p
redicate, i.e., it
can also be used to construct data.
-/
def bidirectionalRec {motive : List α → Sort*} (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) :
    ∀ l, motive l
  | [] => nil
  | [a] => singleton a
  | a :: b :: l =>
    (dropLast_concat_getLast (cons_ne_nil b l)) ▸
    cons_append a ((b :: l).dropLast) ((b :: l).getLast (cons_ne_nil _ _))
    ((b :: l).dropLast.bidirectionalRec nil singleton cons_append)
termination_by l => l.length

@[simp]
/-
**List.bidirectionalRec_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bidirectionalRec_nil {motive : List α -> Sort*} (nil : motive []) (singlet
on : forall a : α, motive [a]) (cons_append : forall (a : α) (l : List α) (b : α
), motive l -> motive (a :: (l ++ [b]))) : bidirectionalRec nil singleton cons_a
ppend [] = nil
参数：nil : motive []；singleton : forall a : α, motive [a]；cons_append : forall (a 
: α) (l : List α) (b : α), motive l -> motive (a :: (l ++ [b]))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bidirectionalRec_nil {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) :
    bidirectionalRec nil singleton cons_append [] = nil := by grind [bidirectionalRec]


@[simp]
/-
**List.bidirectionalRec_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bidirectionalRec_singleton {motive : List α -> Sort*} (nil : motive []) (s
ingleton : forall a : α, motive [a]) (cons_append : forall (a : α) (l : List α) 
(b : α), motive l -> motive (a :: (l ++ [b]))) (a : α) : bidirectionalRec nil si
ngleton cons_append [a] = singleton a
参数：nil : motive []；singleton : forall a : α, motive [a]；cons_append : forall (a 
: α) (l : List α) (b : α), motive l -> motive (a :: (l ++ [b]))；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bidirectionalRec_singleton {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) (a : α) :
    bidirectionalRec nil singleton cons_append [a] = singleton a := by
  grind [bidirectionalRec]

@[simp]
/-
**List.bidirectionalRec_cons_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bidirectionalRec_cons_append {motive : List α -> Sort*} (nil : motive []) 
(singleton : forall a : α, motive [a]) (cons_append : forall (a : α) (l : List α
) (b : α), motive l -> motive (a :: (l ++ [b]))) (a : α) (l : List α) (b : α) : 
bidirectionalRec nil singleton cons_append (a :: (l ++ [b])) = cons_append a l b
 (bidirectionalRec nil singleton cons_append l)
参数：nil : motive []；singleton : forall a : α, motive [a]；cons_append : forall (a 
: α) (l : List α) (b : α), motive l -> motive (a :: (l ++ [b]))；a : α；l : List α
；b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bidirectionalRec_cons_append {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b])))
    (a : α) (l : List α) (b : α) :
    bidirectionalRec nil singleton cons_append (a :: (l ++ [b])) =
      cons_append a l b (bidirectionalRec nil singleton cons_append l) := by
  grind [bidirectionalRec, cases List]

/-- Like `bidirectionalRec`, but with the list parameter placed first. -/
@[elab_as_elim]
/-
**List.bidirectionalRecOn** 是 Mathlib 中的一个缩写定义，位于命名空间 `List`。
形式化陈述：bidirectionalRecOn {C : List α -> Sort*} (l : List α) (H0 : C []) (H1 : fo
rall a : α, C [a]) (Hn : forall (a : α) (l : List α) (b : α), C l -> C (a :: (l 
++ [b]))) : C l
参数：l : List α；H0 : C []；H1 : forall a : α, C [a]；Hn : forall (a : α) (l : List α
) (b : α), C l -> C (a :: (l ++ [b]))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Like `bidirectionalRec`, but with the list parameter placed first.
-/
abbrev bidirectionalRecOn {C : List α → Sort*} (l : List α) (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : C l :=
  bidirectionalRec H0 H1 Hn l

/--
A dependent recursion principle for nonempty lists. Useful for dealing with
operations like `List.head` which are not defined on the empty list.
-/
@[elab_as_elim]
/-
**List.recNeNil** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：recNeNil {motive : (l : List α) -> l != [] -> Sort*} (singleton : forall x
, motive [x] (cons_ne_nil x [])) (cons : forall x xs h, motive xs h -> motive (x
 :: xs) (cons_ne_nil x xs)) (l : List α) (h : l != []) : motive l h
参数：l : List α；singleton : forall x, motive [x] (cons_ne_nil x [])；cons : forall 
x xs h, motive xs h -> motive (x :: xs) (cons_ne_nil x xs)；l : List α；h : l != [
]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []

--- 原说明 ---
A dependent recursion principle for nonempty lists. Useful for dealing with
operations like `List.head` which are not defined on the empty list.
-/
def recNeNil {motive : (l : List α) → l ≠ [] → Sort*}
    (singleton : ∀ x, motive [x] (cons_ne_nil x []))
    (cons : ∀ x xs h, motive xs h → motive (x :: xs) (cons_ne_nil x xs))
    (l : List α) (h : l ≠ []) : motive l h :=
  match l with
  | [x] => singleton x
  | x :: y :: xs =>
    cons x (y :: xs) (cons_ne_nil y xs) (recNeNil singleton cons (y :: xs) (cons_ne_nil y xs))

@[simp]
/-
**List.recNeNil_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：recNeNil_singleton {motive : (l : List α) -> l != [] -> Sort*} (x : α) (si
ngleton : forall x, motive [x] (cons_ne_nil x [])) (cons : forall x xs h, motive
 xs h -> motive (x :: xs) (cons_ne_nil x xs)) : recNeNil singleton cons [x] (con
s_ne_nil x []) = singleton x
参数：l : List α；x : α；singleton : forall x, motive [x] (cons_ne_nil x [])；cons : f
orall x xs h, motive xs h -> motive (x :: xs) (cons_ne_nil x xs)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
-/
theorem recNeNil_singleton {motive : (l : List α) → l ≠ [] → Sort*} (x : α)
    (singleton : ∀ x, motive [x] (cons_ne_nil x []))
    (cons : ∀ x xs h, motive xs h → motive (x :: xs) (cons_ne_nil x xs)) :
    recNeNil singleton cons [x] (cons_ne_nil x []) = singleton x := rfl

@[simp]
/-
**List.recNeNil_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：recNeNil_cons {motive : (l : List α) -> l != [] -> Sort*} (x : α) (xs : Li
st α) (h : xs != []) (singleton : forall x, motive [x] (cons_ne_nil x [])) (cons
 : forall x xs h, motive xs h -> motive (x :: xs) (cons_ne_nil x xs)) : recNeNil
 singleton cons (x :: xs) (cons_ne_nil x xs) = cons x xs h (recNeNil singleton c
ons xs h)
参数：l : List α；x : α；xs : List α；h : xs != []；singleton : forall x, motive [x] (c
ons_ne_nil x [])；cons : forall x xs h, motive xs h -> motive (x :: xs) (cons_ne_
nil x xs)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
-/
theorem recNeNil_cons {motive : (l : List α) → l ≠ [] → Sort*} (x : α) (xs : List α) (h : xs ≠ [])
    (singleton : ∀ x, motive [x] (cons_ne_nil x []))
    (cons : ∀ x xs h, motive xs h → motive (x :: xs) (cons_ne_nil x xs)) :
    recNeNil singleton cons (x :: xs) (cons_ne_nil x xs) =
      cons x xs h (recNeNil singleton cons xs h) :=
  match xs with
  | _ :: _ => rfl

/--
A dependent recursion principle for nonempty lists. Useful for dealing with
operations like `List.head` which are not defined on the empty list.
Same as `List.recNeNil`, with a more convenient argument order.
-/
@[elab_as_elim, simp]
/-
**List.recOnNeNil** 是 Mathlib 中的一个缩写定义，位于命名空间 `List`。
形式化陈述：recOnNeNil {motive : (l : List α) -> l != [] -> Sort*} (l : List α) (h : l
 != []) (singleton : forall x, motive [x] (cons_ne_nil x [])) (cons : forall x x
s h, motive xs h -> motive (x :: xs) (cons_ne_nil x xs)) : motive l h
参数：l : List α；l : List α；h : l != []；singleton : forall x, motive [x] (cons_ne_n
il x [])；cons : forall x xs h, motive xs h -> motive (x :: xs) (cons_ne_nil x xs
)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []

--- 原说明 ---
A dependent recursion principle for nonempty lists. Useful for dealing with
operations like `List.head` which are not defined on the empty list.
Same as `List.recNeNil`, with a more convenient argument order.
-/
abbrev recOnNeNil {motive : (l : List α) → l ≠ [] → Sort*} (l : List α) (h : l ≠ [])
    (singleton : ∀ x, motive [x] (cons_ne_nil x []))
    (cons : ∀ x xs h, motive xs h → motive (x :: xs) (cons_ne_nil x xs)) :
    motive l h := recNeNil singleton cons l h

/--
A recursion principle for lists which separates the singleton case.
-/
@[elab_as_elim]
/-
**List.twoStepInduction** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：twoStepInduction {motive : (l : List α) -> Sort*} (nil : motive []) (singl
eton : forall x, motive [x]) (cons_cons : forall x y xs, motive xs -> (forall y,
 motive (y :: xs)) -> motive (x :: y :: xs)) (l : List α) : motive l
参数：l : List α；nil : motive []；singleton : forall x, motive [x]；cons_cons : foral
l x y xs, motive xs -> (forall y, motive (y :: xs)) -> motive (x :: y :: xs)；l :
 List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursion principle for lists which separates the singleton case.
-/
def twoStepInduction {motive : (l : List α) → Sort*} (nil : motive [])
    (singleton : ∀ x, motive [x])
    (cons_cons : ∀ x y xs, motive xs → (∀ y, motive (y :: xs)) → motive (x :: y :: xs))
    (l : List α) : motive l := match l with
  | [] => nil
  | [x] => singleton x
  | x :: y :: xs =>
    cons_cons x y xs
    (twoStepInduction nil singleton cons_cons xs)
    (fun y => twoStepInduction nil singleton cons_cons (y :: xs))

@[simp]
/-
**List.twoStepInduction_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：twoStepInduction_nil {motive : (l : List α) -> Sort*} (nil : motive []) (s
ingleton : forall x, motive [x]) (cons_cons : forall x y xs, motive xs -> (foral
l y, motive (y :: xs)) -> motive (x :: y :: xs)) : twoStepInduction nil singleto
n cons_cons [] = nil
参数：l : List α；nil : motive []；singleton : forall x, motive [x]；cons_cons : foral
l x y xs, motive xs -> (forall y, motive (y :: xs)) -> motive (x :: y :: xs)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.twoStepInduction.eq_1`：∀ {α : Type u_1} {motive : List α → Sort u_2
} (nil : motive []) (singleton : (x : α) → motive [x])   (cons_cons : (x y : α) 
→ (xs : List α) …
-/
theorem twoStepInduction_nil {motive : (l : List α) → Sort*} (nil : motive [])
    (singleton : ∀ x, motive [x])
    (cons_cons : ∀ x y xs, motive xs → (∀ y, motive (y :: xs)) → motive (x :: y :: xs)) :
    twoStepInduction nil singleton cons_cons [] = nil := twoStepInduction.eq_1 ..

@[simp]
/-
**List.twoStepInduction_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：twoStepInduction_singleton {motive : (l : List α) -> Sort*} (x : α) (nil :
 motive []) (singleton : forall x, motive [x]) (cons_cons : forall x y xs, motiv
e xs -> (forall y, motive (y :: xs)) -> motive (x :: y :: xs)) : twoStepInductio
n nil singleton cons_cons [x] = singleton x
参数：l : List α；x : α；nil : motive []；singleton : forall x, motive [x]；cons_cons :
 forall x y xs, motive xs -> (forall y, motive (y :: xs)) -> motive (x :: y :: x
s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.twoStepInduction.eq_2`：∀ {α : Type u_1} {motive : List α → Sort u_2
} (nil : motive []) (singleton : (x : α) → motive [x])   (cons_cons : (x y : α) 
→ (xs : List α) …
-/
theorem twoStepInduction_singleton {motive : (l : List α) → Sort*} (x : α) (nil : motive [])
    (singleton : ∀ x, motive [x])
    (cons_cons : ∀ x y xs, motive xs → (∀ y, motive (y :: xs)) → motive (x :: y :: xs)) :
    twoStepInduction nil singleton cons_cons [x] = singleton x := twoStepInduction.eq_2 ..

@[simp]
/-
**List.twoStepInduction_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：twoStepInduction_cons_cons {motive : (l : List α) -> Sort*} (x y : α) (xs 
: List α) (nil : motive []) (singleton : forall x, motive [x]) (cons_cons : fora
ll x y xs, motive xs -> (forall y, motive (y :: xs)) -> motive (x :: y :: xs)) :
 twoStepInduction nil singleton cons_cons (x :: y :: xs) = cons_cons x y xs (two
StepInduction nil singleton cons_cons xs) (fun y => twoStepInduction nil singlet
on cons_cons (y :: xs))
参数：l : List α；x y : α；xs : List α；nil : motive []；singleton : forall x, motive [
x]；cons_cons : forall x y xs, motive xs -> (forall y, motive (y :: xs)) -> motiv
e (x :: y :: xs)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.twoStepInduction.eq_3`：∀ {α : Type u_1} {motive : List α → Sort u_2
} (nil : motive []) (singleton : (x : α) → motive [x])   (cons_cons : (x y : α) 
→ (xs : List α) …
-/
theorem twoStepInduction_cons_cons {motive : (l : List α) → Sort*} (x y : α) (xs : List α)
    (nil : motive []) (singleton : ∀ x, motive [x])
    (cons_cons : ∀ x y xs, motive xs → (∀ y, motive (y :: xs)) → motive (x :: y :: xs)) :
    twoStepInduction nil singleton cons_cons (x :: y :: xs) =
    cons_cons x y xs
    (twoStepInduction nil singleton cons_cons xs)
    (fun y => twoStepInduction nil singleton cons_cons (y :: xs)) := twoStepInduction.eq_3 ..

end List

