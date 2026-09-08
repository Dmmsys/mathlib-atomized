/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Multivariate.Basic

/-!
# The W construction as a multivariate polynomial functor.

W types are well-founded tree-like structures. They are defined
as the least fixpoint of a polynomial functor.

## Main definitions

* `W_mk`     - constructor
* `W_dest`   - destructor
* `W_rec`    - recursor: basis for defining functions by structural recursion on `P.W α`
* `W_rec_eq` - defining equation for `W_rec`
* `W_ind`    - induction principle for `P.W α`

## Implementation notes

Three views of M-types:

* `wp`: polynomial functor
* `W`: data type inductively defined by a triple:
     shape of the root, data in the root and children of the root
* `W`: least fixed point of a polynomial functor

Specifically, we define the polynomial functor `wp` as:

* A := a tree-like structure without information in the nodes
* B := given the tree-like structure `t`, `B t` is a valid path
  (specified inductively by `W_path`) from the root of `t` to any given node.

As a result `wp α` is made of a dataless tree and a function from
its valid paths to values of `α`

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

@[expose] public section


universe u v

namespace MvPFunctor

open TypeVec

open MvFunctor

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

/-- A path from the root of a tree to one of its node -/
/-
**MvPFunctor.WPath** 是 Mathlib 中的一个归纳类型，位于命名空间 `MvPFunctor`。
形式化陈述：{n : ℕ} → (P : MvPFunctor.{u} (n + 1)) → P.last.W → Fin2 n → Type u
参数：P : MvPFunctor.{u} (n + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path from the root of a tree to one of its node
-/
inductive WPath : P.last.W → Fin2 n → Type u
  | root (a : P.A) (f : P.last.B a → P.last.W) (i : Fin2 n) (c : P.drop.B a i) : WPath ⟨a, f⟩ i
  | child (a : P.A) (f : P.last.B a → P.last.W) (i : Fin2 n) (j : P.last.B a)
    (c : WPath (f j) i) : WPath ⟨a, f⟩ i
/-
**MvPFunctor.WPath.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.WPath`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} (n + 1)) →     (x : P.last.W) → {i : Fin2 
n} → [I : Inhabited (P.drop.B x.head i)] → Inhabited (P.WPath x i)
参数：P : MvPFunctor.{u} (n + 1)；x : P.last.W；P.drop.B x.head i；P.WPath x i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WPath.inhabited (x : P.last.W) {i : Fin2 n} [I : Inhabited (P.drop.B x.head i)] :
    Inhabited (WPath P x i) :=
  ⟨match x, I with
    | ⟨a, f⟩, I => WPath.root a f i (@default _ I)⟩

/-- Specialized destructor on `WPath` -/
/-
**MvPFunctor.wPathCasesOn** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W} (g' : 
P.drop.B a ⟹ α) (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) : P.WPath ⟨a, f⟩ 
⟹ α
参数：g' : P.drop.B a ⟹ α；g : forall j : P.last.B a, P.WPath (f j) ⟹ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Specialized destructor on `WPath`
-/
def wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W} (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) : P.WPath ⟨a, f⟩ ⟹ α := by
  intro i x
  match x with
  | WPath.root _ _ i c => exact g' i c
  | WPath.child _ _ i j c => exact g j i c

/-- Specialized destructor on `WPath` -/
/-
**MvPFunctor.wPathDestLeft** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wPathDestLeft {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W} (h : 
P.WPath ⟨a, f⟩ ⟹ α) : P.drop.B a ⟹ α
参数：h : P.WPath ⟨a, f⟩ ⟹ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Specialized destructor on `WPath`
-/
def wPathDestLeft {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.drop.B a ⟹ α := fun i c => h i (WPath.root a f i c)

/-- Specialized destructor on `WPath` -/
/-
**MvPFunctor.wPathDestRight** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wPathDestRight {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W} (h :
 P.WPath ⟨a, f⟩ ⟹ α) : forall j : P.last.B a, P.WPath (f j) ⟹ α
参数：h : P.WPath ⟨a, f⟩ ⟹ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Specialized destructor on `WPath`
-/
def wPathDestRight {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : ∀ j : P.last.B a, P.WPath (f j) ⟹ α := fun j i c =>
  h i (WPath.child a f i j c)
/-
**MvPFunctor.wPathDestLeft_wPathCasesOn** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：wPathDestLeft_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.
last.W} (g' : P.drop.B a ⟹ α) (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) : P
.wPathDestLeft (P.wPathCasesOn g' g) = g'
参数：g' : P.drop.B a ⟹ α；g : forall j : P.last.B a, P.WPath (f j) ⟹ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wPathDestLeft_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) :
    P.wPathDestLeft (P.wPathCasesOn g' g) = g' := rfl
/-
**MvPFunctor.wPathDestRight_wPathCasesOn** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：wPathDestRight_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a -> P
.last.W} (g' : P.drop.B a ⟹ α) (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) : 
P.wPathDestRight (P.wPathCasesOn g' g) = g
参数：g' : P.drop.B a ⟹ α；g : forall j : P.last.B a, P.WPath (f j) ⟹ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wPathDestRight_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) :
    P.wPathDestRight (P.wPathCasesOn g' g) = g := rfl
/-
**MvPFunctor.wPathCasesOn_eta** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：wPathCasesOn_eta {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W} (h
 : P.WPath ⟨a, f⟩ ⟹ α) : P.wPathCasesOn (P.wPathDestLeft h) (P.wPathDestRight h)
 = h
参数：h : P.WPath ⟨a, f⟩ ⟹ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem wPathCasesOn_eta {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.wPathCasesOn (P.wPathDestLeft h) (P.wPathDestRight h) = h := by
  ext i x; cases x <;> rfl
/-
**MvPFunctor.comp_wPathCasesOn** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：comp_wPathCasesOn {α β : TypeVec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a 
-> P.last.W} (g' : P.drop.B a ⟹ α) (g : forall j : P.last.B a, P.WPath (f j) ⟹ α
) : h ⊚ P.wPathCasesOn g' g = P.wPathCasesOn (h ⊚ g') fun i => h ⊚ g i
参数：h : α ⟹ β；g' : P.drop.B a ⟹ α；g : forall j : P.last.B a, P.WPath (f j) ⟹ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem comp_wPathCasesOn {α β : TypeVec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) :
    h ⊚ P.wPathCasesOn g' g = P.wPathCasesOn (h ⊚ g') fun i => h ⊚ g i := by
  ext i x; cases x <;> rfl

/-- Polynomial functor for the W-type of `P`. `A` is a data-less well-founded
tree whereas, for a given `a : A`, `B a` is a valid path in tree `a` so
that `Wp.obj α` is made of a tree and a function from its valid paths to
the values it contains -/
/-
**MvPFunctor.wp** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wp : MvPFunctor n where A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Polynomial functor for the W-type of `P`. `A` is a data-less well-founded
tree whereas, for a given `a : A`, `B a` is a valid path in tree `a` so
that `Wp.obj α` is made of a tree and a function from its valid paths to
the values it contains
-/
def wp : MvPFunctor n where
  A := P.last.W
  B := P.WPath

/-- W-type of `P` -/
/-
**MvPFunctor.W** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：W (α : TypeVec n) : Type _
参数：α : TypeVec n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
W-type of `P`
-/
def W (α : TypeVec n) : Type _ :=
  P.wp α
/-
**MvPFunctor.mvfunctorW** 是 Mathlib 中的一个实例，位于命名空间 `MvPFunctor`。
形式化陈述：mvfunctorW : MvFunctor P.W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mvfunctorW : MvFunctor P.W := by delta MvPFunctor.W; infer_instance

/-!
First, describe operations on `W` as a polynomial functor.
-/


/-- Constructor for `wp` -/
/-
**MvPFunctor.wpMk** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wpMk {α : TypeVec n} (a : P.A) (f : P.last.B a -> P.last.W) (f' : P.WPath 
⟨a, f⟩ ⟹ α) : P.W α
参数：a : P.A；f : P.last.B a -> P.last.W；f' : P.WPath ⟨a, f⟩ ⟹ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `wp`
-/
def wpMk {α : TypeVec n} (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.W α :=
  ⟨⟨a, f⟩, f'⟩
/-
**MvPFunctor.wpRec** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} (n + 1)) →     {α : TypeVec.{u_2} n} →    
   {C : Sort u_1} →         ((a : P.A) → (f : P.last.B a → P.last.W) → TypeVec.A
rrow (P.WPath (WType.mk a f)) α → (P.last.B a → C) → C) →           (x : P.last.
W) → TypeVec.Arrow (P.WPath x) α → C
参数：P : MvPFunctor.{u} (n + 1)；(a : P.A) → (f : P.last.B a → P.last.W) → TypeVec.
Arrow (P.WPath (WType.mk a f)) α → (P.last.B a → C) → C；x : P.last.W；P.WPath x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def wpRec {α : TypeVec n} {C : Sort*}
    (g : ∀ (a : P.A) (f : P.last.B a → P.last.W), P.WPath ⟨a, f⟩ ⟹ α → (P.last.B a → C) → C) :
    ∀ (x : P.last.W) (_ : P.WPath x ⟹ α), C
  | ⟨a, f⟩, f' => g a f f' fun i => wpRec g (f i) (P.wPathDestRight f' i)
/-
**MvPFunctor.wpRec_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：wpRec_eq {α : TypeVec n} {C : Sort*} (g : forall (a : P.A) (f : P.last.B a
 -> P.last.W), P.WPath ⟨a, f⟩ ⟹ α -> (P.last.B a -> C) -> C) (a : P.A) (f : P.la
st.B a -> P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) : P.wpRec g ⟨a, f⟩ f' = g a f f' f
un i => P.wpRec g (f i) (P.wPathDestRight f' i)
参数：g : forall (a : P.A) (f : P.last.B a -> P.last.W), P.WPath ⟨a, f⟩ ⟹ α -> (P.l
ast.B a -> C) -> C；a : P.A；f : P.last.B a -> P.last.W；f' : P.WPath ⟨a, f⟩ ⟹ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wpRec_eq {α : TypeVec n} {C : Sort*}
    (g : ∀ (a : P.A) (f : P.last.B a → P.last.W), P.WPath ⟨a, f⟩ ⟹ α → (P.last.B a → C) → C)
    (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.wpRec g ⟨a, f⟩ f' = g a f f' fun i => P.wpRec g (f i) (P.wPathDestRight f' i) := rfl

/-- Induction principle for an unfolded `W` -/
@[elab_as_elim]
/-
**MvPFunctor.wpInd** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} (n + 1)) →     {α : TypeVec.{u_1} n} →    
   {C : (x : P.last.W) → TypeVec.Arrow (P.WPath x) α → Sort v} →         ((a : P
.A) →             (f : P.last.B a → P.last.W) →               (f' : TypeVec.Arro
w (P.WPath (WType.mk a f)) α) →                 ((i : P.last.B a) → C (f i) (P.w
PathDestRight f' i)) → C (WType.mk a f) f') →           (x : P.last.W) → (f' : T
ypeVec.Arrow (P.WPath x) α) → C x f'
参数：P : MvPFunctor.{u} (n + 1)；x : P.last.W；P.WPath x；(a : P.A) →             (f 
: P.last.B a → P.last.W) →               (f' : TypeVec.Arrow (P.WPath (WType.mk 
a f)) α) →                 ((i : P.last.B a) → C (f i) (P.wPathDestRight f' i)) 
→ C (WType.mk a f) f'；x : P.last.W；f' : TypeVec.Arrow (P.WPath x) α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction principle for an unfolded `W`
-/
def wpInd {α : TypeVec n} {C : ∀ x : P.last.W, P.WPath x ⟹ α → Sort v}
    (ih : ∀ (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α),
        (∀ i : P.last.B a, C (f i) (P.wPathDestRight f' i)) → C ⟨a, f⟩ f') :
    ∀ (x : P.last.W) (f' : P.WPath x ⟹ α), C x f'
  | ⟨a, f⟩, f' => ih a f f' fun _i => wpInd ih _ _

@[deprecated (since := "2026-03-20")] alias wp_ind := wpInd

/-!
Now think of W as defined inductively by the data ⟨a, f', f⟩ where
- `a  : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f  : P.last.B a → P.last.W` are the subtrees
-/


/-- Constructor for `W` -/
/-
**MvPFunctor.wMk** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wMk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W
 α) : P.W α
参数：a : P.A；f' : P.drop.B a ⟹ α；f : P.last.B a -> P.W α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `W`
-/
def wMk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) : P.W α :=
  let g : P.last.B a → P.last.W := fun i => (f i).fst
  let g' : P.WPath ⟨a, g⟩ ⟹ α := P.wPathCasesOn f' fun i => (f i).snd
  ⟨⟨a, g⟩, g'⟩

/-- Recursor for `W` -/
/-
**MvPFunctor.wRec** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wRec {α : TypeVec n} {C : Sort*} (g : forall a : P.A, P.drop.B a ⟹ α -> (P
.last.B a -> P.W α) -> (P.last.B a -> C) -> C) : P.W α -> C | ⟨a, f'⟩ => let g' 
(a : P.A) (f : P.last.B a -> P.last.W) (h : P.WPath ⟨a, f⟩ ⟹ α) (h' : P.last.B a
 -> C) : C
参数：g : forall a : P.A, P.drop.B a ⟹ α -> (P.last.B a -> P.W α) -> (P.last.B a ->
 C) -> C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursor for `W`
-/
def wRec {α : TypeVec n} {C : Sort*}
    (g : ∀ a : P.A, P.drop.B a ⟹ α → (P.last.B a → P.W α) → (P.last.B a → C) → C) : P.W α → C
  | ⟨a, f'⟩ =>
    let g' (a : P.A) (f : P.last.B a → P.last.W) (h : P.WPath ⟨a, f⟩ ⟹ α)
      (h' : P.last.B a → C) : C :=
      g a (P.wPathDestLeft h) (fun i => ⟨f i, P.wPathDestRight h i⟩) h'
    P.wpRec g' a f'

/-- Defining equation for the recursor of `W` -/
/-
**MvPFunctor.wRec_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：wRec_eq {α : TypeVec n} {C : Sort*} (g : forall a : P.A, P.drop.B a ⟹ α ->
 (P.last.B a -> P.W α) -> (P.last.B a -> C) -> C) (a : P.A) (f' : P.drop.B a ⟹ α
) (f : P.last.B a -> P.W α) : P.wRec g (P.wMk a f' f) = g a f' f fun i => P.wRec
 g (f i)
参数：g : forall a : P.A, P.drop.B a ⟹ α -> (P.last.B a -> P.W α) -> (P.last.B a ->
 C) -> C；a : P.A；f' : P.drop.B a ⟹ α；f : P.last.B a -> P.W α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defining equation for the recursor of `W`
-/
theorem wRec_eq {α : TypeVec n} {C : Sort*}
    (g : ∀ a : P.A, P.drop.B a ⟹ α → (P.last.B a → P.W α) → (P.last.B a → C) → C) (a : P.A)
    (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
    P.wRec g (P.wMk a f' f) = g a f' f fun i => P.wRec g (f i) := rfl

/-- Induction principle for `W` -/
@[elab_as_elim]
/-
**MvPFunctor.wInd** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wInd {α : TypeVec n} {C : P.W α -> Sort v} (ih : forall (a : P.A) (f' : P.
drop.B a ⟹ α) (f : P.last.B a -> P.W α), (forall i, C (f i)) -> C (P.wMk a f' f)
) : forall x, C x
参数：ih : forall (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α), (foral
l i, C (f i)) -> C (P.wMk a f' f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction principle for `W`
-/
def wInd {α : TypeVec n} {C : P.W α → Sort v}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α),
        (∀ i, C (f i)) → C (P.wMk a f' f)) :
    ∀ x, C x := fun ⟨hd, ch⟩ =>
  wpInd P (fun head f f' ih' =>
    cast
      (congr rfl <| Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq <| wPathCasesOn_eta P f'⟩)
      <| ih head (P.wPathDestLeft f') (fun i => ⟨f i, P.wPathDestRight f' i⟩) ih') hd ch

@[deprecated (since := "2026-03-20")] alias w_ind := wInd

@[simp]
/-
**MvPFunctor.wInd_wMk** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：wInd_wMk {α : TypeVec n} {C : P.W α -> Sort v} (ih : forall (a : P.A) (f' 
: P.drop.B a ⟹ α) (f : P.last.B a -> P.W α), (forall i, C (f i)) -> C (P.wMk a f
' f)) {a : P.drop.A} {f' : P.drop.B a ⟹ α} {f : P.last.B a -> P.W α} : wInd P ih
 (wMk P a f' f) = ih a f' f (fun i => wInd P ih (f i))
参数：ih : forall (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α), (foral
l i, C (f i)) -> C (P.wMk a f' f)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wInd_wMk {α : TypeVec n} {C : P.W α → Sort v}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α),
        (∀ i, C (f i)) → C (P.wMk a f' f))
    {a : P.drop.A} {f' : P.drop.B a ⟹ α} {f : P.last.B a → P.W α}
    : wInd P ih (wMk P a f' f) = ih a f' f (fun i => wInd P ih (f i)) := rfl

/-- Cases lemma for `W` types -/
@[elab_as_elim]
/-
**MvPFunctor.wCases** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wCases {α : TypeVec n} {C : P.W α -> Sort v} (ih : forall (a : P.A) (f' : 
P.drop.B a ⟹ α) (f : P.last.B a -> P.W α), C (P.wMk a f' f)) : forall x, C x
参数：ih : forall (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α), C (P.w
Mk a f' f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cases lemma for `W` types
-/
def wCases {α : TypeVec n} {C : P.W α → Sort v}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α), C (P.wMk a f' f)) :
    ∀ x, C x := P.wInd fun a f' f _ih' => ih a f' f

@[deprecated (since := "2026-03-20")] alias w_cases := wCases

/-- W-types are functorial -/
/-
**MvPFunctor.wMap** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wMap {α β : TypeVec n} (g : α ⟹ β) : P.W α -> P.W β
参数：g : α ⟹ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
W-types are functorial
-/
def wMap {α β : TypeVec n} (g : α ⟹ β) : P.W α → P.W β := fun x => g <$$> x
/-
**MvPFunctor.wMk_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：wMk_eq {α : TypeVec n} (a : P.A) (f : P.last.B a -> P.last.W) (g' : P.drop
.B a ⟹ α) (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) : (P.wMk a g' fun i => 
⟨f i, g i⟩) = ⟨⟨a, f⟩, P.wPathCasesOn g' g⟩
参数：a : P.A；f : P.last.B a -> P.last.W；g' : P.drop.B a ⟹ α；g : forall j : P.last.
B a, P.WPath (f j) ⟹ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wMk_eq {α : TypeVec n} (a : P.A) (f : P.last.B a → P.last.W) (g' : P.drop.B a ⟹ α)
    (g : ∀ j : P.last.B a, P.WPath (f j) ⟹ α) :
    (P.wMk a g' fun i => ⟨f i, g i⟩) = ⟨⟨a, f⟩, P.wPathCasesOn g' g⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.w_map_wMk** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：w_map_wMk {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f' : P.drop.B a ⟹ α) (f
 : P.last.B a -> P.W α) : g < > P.wMk a f' f = P.wMk a (g ⊚ f') fun i => g < > f
 i
参数：g : α ⟹ β；a : P.A；f' : P.drop.B a ⟹ α；f : P.last.B a -> P.W α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPFunctor.wMk_eq`：wMk_eq {α : TypeVec n} (a : P.A) (f : P.last.B a -> P
.last.W) (g' : P.drop.B a ⟹ α) (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) : 
(P.wMk …
· 使用定理 `MvPFunctor.map_eq`：map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P
.B a ⟹ α) : @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩
· 使用定理 `MvPFunctor.comp_wPathCasesOn`：comp_wPathCasesOn {α β : TypeVec n} (h : α
 ⟹ β) {a : P.A} {f : P.last.B a -> P.last.W} (g' : P.drop.B a ⟹ α) (g : forall j
 : P.last.B a, P.W…
-/
theorem w_map_wMk {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → P.W α) : g <$$> P.wMk a f' f = P.wMk a (g ⊚ f') fun i => g <$$> f i := by
  change _ = P.wMk a (g ⊚ f') (MvFunctor.map g ∘ f)
  have : MvFunctor.map g ∘ f = fun i => ⟨(f i).fst, g ⊚ (f i).snd⟩ := by
    ext i : 1
    dsimp [Function.comp_def]
    cases f i
    rfl
  rw [this]
  have : f = fun i => ⟨(f i).fst, (f i).snd⟩ := by
    ext1 x
    cases f x
    rfl
  rw [this]
  dsimp
  rw [wMk_eq, wMk_eq]
  have h := MvPFunctor.map_eq P.wp g
  rw [h, comp_wPathCasesOn]

-- TODO: this technical theorem is used in one place in constructing the initial algebra.
-- Can it be avoided?
/-- Constructor of a value of `P.obj (α ::: β)` from components.
Useful to avoid complicated type annotation -/
/-
**MvPFunctor.objAppend1** 是 Mathlib 中的一个缩写定义，位于命名空间 `MvPFunctor`。
形式化陈述：objAppend1 {α : TypeVec n} {β : Type u} (a : P.A) (f' : P.drop.B a ⟹ α) (f
 : P.last.B a -> β) : P (α ::: β)
参数：a : P.A；f' : P.drop.B a ⟹ α；f : P.last.B a -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor of a value of `P.obj (α ::: β)` from components.
Useful to avoid complicated type annotation
-/
abbrev objAppend1 {α : TypeVec n} {β : Type u} (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → β) : P (α ::: β) :=
  ⟨a, splitFun f' f⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.map_objAppend1** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：map_objAppend1 {α γ : TypeVec n} (g : α ⟹ γ) (a : P.A) (f' : P.drop.B a ⟹ 
α) (f : P.last.B a -> P.W α) : appendFun g (P.wMap g) < > P.objAppend1 a f' f = 
P.objAppend1 a (g ⊚ f') fun x => P.wMap g (f x)
参数：g : α ⟹ γ；a : P.A；f' : P.drop.B a ⟹ α；f : P.last.B a -> P.W α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPFunctor.objAppend1.eq_1`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : 
TypeVec.{u} n} {β : Type u} (a : P.A) (f' : (P.drop.B a).Arrow α)   (f : P.last.
B a → β), P.objA…
· 使用定理 `MvPFunctor.map_eq`：map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P
.B a ⟹ α) : @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩
· 使用定理 `TypeVec.appendFun.eq_1`：∀ {n : ℕ} {α : TypeVec.{u_1} n} {α' : TypeVec.{u
_2} n} {β : Type u_1} {β' : Type u_2} (f : α.Arrow α') (g : β → β'),   (f ::: g)
 = TypeVec.s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TypeVec.splitFun_comp`：splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : 
drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂) (g₀ : last α₀ -> last α₁) (g₁ : last
 α₁ -> last…
-/
theorem map_objAppend1 {α γ : TypeVec n} (g : α ⟹ γ) (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → P.W α) :
    appendFun g (P.wMap g) <$$> P.objAppend1 a f' f =
      P.objAppend1 a (g ⊚ f') fun x => P.wMap g (f x) := by
  rw [objAppend1, objAppend1, map_eq, appendFun, ← splitFun_comp]; rfl

/-!
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/


/-- Constructor for the W-type of `P` -/
/-
**MvPFunctor.wMk'** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：{n : ℕ} → (P : MvPFunctor.{u} (n + 1)) → {α : TypeVec.{u} n} → ↑P (α ::: P
.W α) → P.W α
参数：P : MvPFunctor.{u} (n + 1)；α ::: P.W α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for the W-type of `P`
-/
def wMk' {α : TypeVec n} : P (α ::: P.W α) → P.W α
  | ⟨a, f⟩ => P.wMk a (dropFun f) (lastFun f)

/-- Destructor for the W-type of `P` -/
/-
**MvPFunctor.wDest'** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：wDest' {α : TypeVec.{u} n} : P.W α -> P (α.append1 (P.W α))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destructor for the W-type of `P`
-/
def wDest' {α : TypeVec.{u} n} : P.W α → P (α.append1 (P.W α)) :=
  P.wRec fun a f' f _ => ⟨a, splitFun f' f⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.wDest'_wMk** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} (a : P.A) (f' :
 (P.drop.B a).Arrow α)   (f : P.last.B a → P.W α), P.wDest' (P.wMk a f' f) = ⟨a,
 TypeVec.splitFun f' f⟩
参数：P : MvPFunctor.{u} (n + 1)；a : P.A；f' : (P.drop.B a).Arrow α；f : P.last.B a →
 P.W α；P.wMk a f' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPFunctor.wDest'.eq_1`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : Type
Vec.{u} n}, P.wDest' = P.wRec fun a f' f x => ⟨a, TypeVec.splitFun f' f⟩
· 使用定理 `MvPFunctor.wRec_eq`：wRec_eq {α : TypeVec n} {C : Sort*} (g : forall a : 
P.A, P.drop.B a ⟹ α -> (P.last.B a -> P.W α) -> (P.last.B a -> C) -> C) (a : P.A
) (f' : …
-/
theorem wDest'_wMk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
    P.wDest' (P.wMk a f' f) = ⟨a, splitFun f' f⟩ := by rw [wDest', wRec_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.wDest'_wMk'** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} (x : ↑P (α ::: 
P.W α)), P.wDest' (P.wMk' x) = x
参数：P : MvPFunctor.{u} (n + 1)；x : ↑P (α ::: P.W α)；P.wMk' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPFunctor.wMk'.eq_1`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVe
c.{u} n} (a : P.A) (f : (P.B a).Arrow (α ::: P.W α)),   P.wMk' ⟨a, f⟩ = P.wMk a 
(TypeVec.d…
· 使用定理 `MvPFunctor.wDest'_wMk`：∀ {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeV
ec.{u} n} (a : P.A) (f' : (P.drop.B a).Arrow α)   (f : P.last.B a → P.W α), P.wD
est' (P.wMk…
· 使用定理 `TypeVec.split_dropFun_lastFun`：split_dropFun_lastFun {α α' : TypeVec (n 
+ 1)} (f : α ⟹ α') : splitFun (dropFun f) (lastFun f) = f
-/
theorem wDest'_wMk' {α : TypeVec n} (x : P (α.append1 (P.W α))) : P.wDest' (P.wMk' x) = x := by
  obtain ⟨a, f⟩ := x; rw [wMk', wDest'_wMk, split_dropFun_lastFun]

end MvPFunctor

