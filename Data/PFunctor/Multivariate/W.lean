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

* `W_mk` - constructor
* `W_dest` - destructor
* `W_rec` - recursor: basis for defining functions by structural recursion on `P.W α`
* `W_rec_eq` - defining equation for `W_rec`
* `W_ind` - induction principle for `P.W α`

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

variable {n : Nat} (P : MvPFunctor.{u} (n + 1))

/--
Inductive type `WPath` / 归纳类型 `WPath`

English:
inductive WPath
  parameters: : P.last.W -> Fin2 n -> Type u
  constructors (2):
    - root: (a : P.A) (f : P.last.B a -> P.last.W) (i : Fin2 n) (c : P.drop.B a i) : WPath ⟨a, f⟩ i
    - child: (a : P.A) (f : P.last.B a -> P.last.W) (i : Fin2 n) (j : P.last.B a) (c : WPath (f j) i) : WPath ⟨a, f⟩ i

中文:
归纳类型 WPath
  参数: : P.last.W -> Fin2 n -> 类型u
  构造子 (2 个):
    - root: (a : P.A) (f : P.last.B a -> P.last.W) (i : Fin2 n) (c : P.drop.B a i) : WPath ⟨a, f⟩ i
    - child: (a : P.A) (f : P.last.B a -> P.last.W) (i : Fin2 n) (j : P.last.B a) (c : WPath (f j) i) : WPath ⟨a, f⟩ i
-/
inductive WPath : P.last.W -> Fin2 n -> Type u
  | root (a : P.A) (f : P.last.B a -> P.last.W) (i : Fin2 n) (c : P.drop.B a i) : WPath ⟨a, f⟩ i
  | child (a : P.A) (f : P.last.B a -> P.last.W) (i : Fin2 n) (j : P.last.B a)
    (c : WPath (f j) i) : WPath ⟨a, f⟩ i

/--
Instance `WPath.inhabited` / 实例 `WPath.inhabited`

English:
instance WPath.inhabited
  signature: (x : P.last.W) {i : Fin2 n} [I : Inhabited (P.drop.B x.head i)]
  body: ⟨match x, I with
    | ⟨a, f⟩, I => WPath.root a f i (@default _ I)⟩

中文:
实例 WPath.inhabited
  签名: (x : P.last.W) {i : Fin2 n} [I : 可居 (P.drop.B x.head i)]
  定义体: ⟨match x, I with
    | ⟨a, f⟩, I => WPath.root a f i (@default _ I)⟩

Depends on / 依赖: WPath.root
-/
instance WPath.inhabited (x : P.last.W) {i : Fin2 n} [I : Inhabited (P.drop.B x.head i)] :
    Inhabited (WPath P x i) :=
  ⟨match x, I with
    | ⟨a, f⟩, I => WPath.root a f i (@default _ I)⟩

/--
Definition of `wPathCasesOn` / `wPathCasesOn` 的定义

English:
definition wPathCasesOn
  signature: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W} (g' : P.drop.B a ⟹ α)
  body: by
  intro i x
  match x with
  | WPath.root _ _ i c => exact g' i c
  | WPath.child _ _ i j c => exact g j i c

中文:
定义 wPathCasesOn
  签名: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W} (g' : P.drop.B a ⟹ α)
  定义体: by
  intro i x
  match x with
  | WPath.root _ _ i c => exact g' i c
  | WPath.child _ _ i j c => exact g j i c

Depends on / 依赖: WPath.child, WPath.root
-/
def wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W} (g' : P.drop.B a ⟹ α)
    (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) : P.WPath ⟨a, f⟩ ⟹ α := by
  intro i x
  match x with
  | WPath.root _ _ i c => exact g' i c
  | WPath.child _ _ i j c => exact g j i c

/--
Definition of `wPathDestLeft` / `wPathDestLeft` 的定义

English:
definition wPathDestLeft
  signature: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  body: fun i c => h i (WPath.root a f i c)

中文:
定义 wPathDestLeft
  签名: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  定义体: fun i c => h i (WPath.root a f i c)

Depends on / 依赖: WPath.root
-/
def wPathDestLeft {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.drop.B a ⟹ α := fun i c => h i (WPath.root a f i c)

/--
Definition of `wPathDestRight` / `wPathDestRight` 的定义

English:
definition wPathDestRight
  signature: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  body: fun j i c =>
  h i (WPath.child a f i j c)

中文:
定义 wPathDestRight
  签名: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  定义体: fun j i c =>
  h i (WPath.child a f i j c)
-/
def wPathDestRight {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : forall j : P.last.B a, P.WPath (f j) ⟹ α := fun j i c =>
  h i (WPath.child a f i j c)

/--
theorem `wPathDestLeft_wPathCasesOn` / 定理 `wPathDestLeft_wPathCasesOn`

English:
theorem wPathDestLeft_wPathCasesOn
  statement: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  proof: rfl

中文:
定理 wPathDestLeft_wPathCasesOn
  结论: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  证明: rfl
-/
theorem wPathDestLeft_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
    (g' : P.drop.B a ⟹ α) (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) :
    P.wPathDestLeft (P.wPathCasesOn g' g) = g' := rfl

/--
theorem `wPathDestRight_wPathCasesOn` / 定理 `wPathDestRight_wPathCasesOn`

English:
theorem wPathDestRight_wPathCasesOn
  statement: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  proof: rfl

中文:
定理 wPathDestRight_wPathCasesOn
  结论: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  证明: rfl
-/
theorem wPathDestRight_wPathCasesOn {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
    (g' : P.drop.B a ⟹ α) (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) :
    P.wPathDestRight (P.wPathCasesOn g' g) = g := rfl

/--
theorem `wPathCasesOn_eta` / 定理 `wPathCasesOn_eta`

English:
theorem wPathCasesOn_eta
  statement: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  proof: by
  ext i x; cases x <;> rfl

中文:
定理 wPathCasesOn_eta
  结论: {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
  证明: by
  ext i x; cases x <;> rfl
-/
theorem wPathCasesOn_eta {α : TypeVec n} {a : P.A} {f : P.last.B a -> P.last.W}
    (h : P.WPath ⟨a, f⟩ ⟹ α) : P.wPathCasesOn (P.wPathDestLeft h) (P.wPathDestRight h) = h := by
  ext i x; cases x <;> rfl

/--
theorem `comp_wPathCasesOn` / 定理 `comp_wPathCasesOn`

English:
theorem comp_wPathCasesOn
  statement: {α β : TypeVec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a -> P.last.W}
  proof: by
  ext i x; cases x <;> rfl

中文:
定理 comp_wPathCasesOn
  结论: {α β : TypeVec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a -> P.last.W}
  证明: by
  ext i x; cases x <;> rfl
-/
theorem comp_wPathCasesOn {α β : TypeVec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a -> P.last.W}
    (g' : P.drop.B a ⟹ α) (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) :
    h ⊚ P.wPathCasesOn g' g = P.wPathCasesOn (h ⊚ g') fun i => h ⊚ g i := by
  ext i x; cases x <;> rfl

/--
Definition of `wp` / `wp` 的定义

English:
definition wp
  signature: : MvPFunctor n where
  body: P.last.W
  B := P.WPath

中文:
定义 wp
  签名: : MvP函子 n where
  定义体: P.last.W
  B := P.WPath

Depends on / 依赖: P.last.W
-/
def wp : MvPFunctor n where
  A := P.last.W
  B := P.WPath

/--
Definition of `W` / `W` 的定义

English:
definition W
  signature: (α : TypeVec n)
  body: P.wp α

中文:
定义 W
  签名: (α : TypeVec n)
  定义体: P.wp α

Depends on / 依赖: P.wp
-/
def W (α : TypeVec n) : Type _ :=
  P.wp α

/--
Instance `mvfunctorW` / 实例 `mvfunctorW`

English:
instance mvfunctorW
  signature: : MvFunctor P.W
  body: by delta MvPFunctor.W; infer_instance

中文:
实例 mvfunctorW
  签名: : Mv函子 P.W
  定义体: by delta MvPFunctor.W; infer_instance

Depends on / 依赖: MvPFunctor, MvPFunctor.W, infer_instance
-/
instance mvfunctorW : MvFunctor P.W := by delta MvPFunctor.W; infer_instance

/-!
First, describe operations on `W` as a polynomial functor.
-/


/--
Definition of `wpMk` / `wpMk` 的定义

English:
definition wpMk
  signature: {α : TypeVec n} (a : P.A) (f : P.last.B a -> P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α)
  body: ⟨⟨a, f⟩, f'⟩

中文:
定义 wpMk
  签名: {α : TypeVec n} (a : P.A) (f : P.last.B a -> P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α)
  定义体: ⟨⟨a, f⟩, f'⟩
-/
def wpMk {α : TypeVec n} (a : P.A) (f : P.last.B a -> P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.W α :=
  ⟨⟨a, f⟩, f'⟩

/--
Definition of `wpRec` / `wpRec` 的定义

English:
definition wpRec
  signature: {α : TypeVec n} {C : Sort*}

中文:
定义 wpRec
  签名: {α : TypeVec n} {C : 类型层*}
-/
def wpRec {α : TypeVec n} {C : Sort*}
    (g : forall (a : P.A) (f : P.last.B a -> P.last.W), P.WPath ⟨a, f⟩ ⟹ α -> (P.last.B a -> C) -> C) :
    forall (x : P.last.W) (_ : P.WPath x ⟹ α), C
  | ⟨a, f⟩, f' => g a f f' fun i => wpRec g (f i) (P.wPathDestRight f' i)

/--
theorem `wpRec_eq` / 定理 `wpRec_eq`

English:
theorem wpRec_eq
  statement: {α : TypeVec n} {C : Sort*}
  proof: rfl

中文:
定理 wpRec_eq
  结论: {α : TypeVec n} {C : 类型层*}
  证明: rfl
-/
theorem wpRec_eq {α : TypeVec n} {C : Sort*}
    (g : forall (a : P.A) (f : P.last.B a -> P.last.W), P.WPath ⟨a, f⟩ ⟹ α -> (P.last.B a -> C) -> C)
    (a : P.A) (f : P.last.B a -> P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α) :
    P.wpRec g ⟨a, f⟩ f' = g a f f' fun i => P.wpRec g (f i) (P.wPathDestRight f' i) := rfl

/-- Induction principle for an unfolded `W` -/
@[elab_as_elim]
/--
Definition of `wpInd` / `wpInd` 的定义

English:
definition wpInd
  signature: {α : TypeVec n} {C : forall x : P.last.W, P.WPath x ⟹ α -> Sort v}
  body: wpInd

中文:
定义 wpInd
  签名: {α : TypeVec n} {C : 对任意 x : P.last.W, P.WPath x ⟹ α -> 类型层 v}
  定义体: wpInd
-/
def wpInd {α : TypeVec n} {C : forall x : P.last.W, P.WPath x ⟹ α -> Sort v}
    (ih : forall (a : P.A) (f : P.last.B a -> P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α),
        (forall i : P.last.B a, C (f i) (P.wPathDestRight f' i)) -> C ⟨a, f⟩ f') :
    forall (x : P.last.W) (f' : P.WPath x ⟹ α), C x f'
  | ⟨a, f⟩, f' => ih a f f' fun _i => wpInd ih _ _

@[deprecated (since := "2026-03-20")] alias wp_ind := wpInd

/-!
Now think of W as defined inductively by the data ⟨a, f', f⟩ where
- `a : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f : P.last.B a → P.last.W` are the subtrees
-/


/--
Definition of `wMk` / `wMk` 的定义

English:
definition wMk
  signature: {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α)
  body: let g : P.last.B a -> P.last.W := fun i => (f i).fst
  let g' : P.WPath ⟨a, g⟩ ⟹ α := P.wPathCasesOn f' fun i => (f i).snd
  ⟨⟨a, g⟩, g'⟩

中文:
定义 wMk
  签名: {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α)
  定义体: let g : P.last.B a -> P.last.W := fun i => (f i).fst
  let g' : P.WPath ⟨a, g⟩ ⟹ α := P.wPathCasesOn f' fun i => (f i).snd
  ⟨⟨a, g⟩, g'⟩

Depends on / 依赖: P.WPath, P.last.B, P.last.W, P.wPathCasesOn, wPathCasesOn
-/
def wMk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α) : P.W α :=
  let g : P.last.B a -> P.last.W := fun i => (f i).fst
  let g' : P.WPath ⟨a, g⟩ ⟹ α := P.wPathCasesOn f' fun i => (f i).snd
  ⟨⟨a, g⟩, g'⟩

/--
Definition of `wRec` / `wRec` 的定义

English:
definition wRec
  signature: {α : TypeVec n} {C : Sort*}
  body: g a (P.wPathDestLeft h) (fun i => ⟨f i, P.wPathDestRight h i⟩) h'
    P.wpRec g' a f'

中文:
定义 wRec
  签名: {α : TypeVec n} {C : 类型层*}
  定义体: g a (P.wPathDestLeft h) (fun i => ⟨f i, P.wPathDestRight h i⟩) h'
    P.wpRec g' a f'

Depends on / 依赖: P.wPathDestLeft, P.wPathDestRight, P.wpRec, wPathDestLeft, wPathDestRight
-/
def wRec {α : TypeVec n} {C : Sort*}
    (g : forall a : P.A, P.drop.B a ⟹ α -> (P.last.B a -> P.W α) -> (P.last.B a -> C) -> C) : P.W α -> C
  | ⟨a, f'⟩ =>
    let g' (a : P.A) (f : P.last.B a -> P.last.W) (h : P.WPath ⟨a, f⟩ ⟹ α)
      (h' : P.last.B a -> C) : C :=
      g a (P.wPathDestLeft h) (fun i => ⟨f i, P.wPathDestRight h i⟩) h'
    P.wpRec g' a f'

/--
theorem `wRec_eq` / 定理 `wRec_eq`

English:
theorem wRec_eq
  statement: {α : TypeVec n} {C : Sort*}
  proof: rfl

中文:
定理 wRec_eq
  结论: {α : TypeVec n} {C : 类型层*}
  证明: rfl
-/
theorem wRec_eq {α : TypeVec n} {C : Sort*}
    (g : forall a : P.A, P.drop.B a ⟹ α -> (P.last.B a -> P.W α) -> (P.last.B a -> C) -> C) (a : P.A)
    (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α) :
    P.wRec g (P.wMk a f' f) = g a f' f fun i => P.wRec g (f i) := rfl

/-- Induction principle for `W` -/
@[elab_as_elim]
/--
Definition of `wInd` / `wInd` 的定义

English:
definition wInd
  signature: {α : TypeVec n} {C : P.W α -> Sort v}
  body: fun ⟨hd, ch⟩ =>
  wpInd P (fun head f f' ih' =>
    cast
      (congr rfl <| Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq <| wPathCasesOn_eta P f'⟩)
 ih head (P.wPathDestLeft f') (fun i => ⟨f i, P.wPathDestRight f' i⟩) ih') hd ch

@[deprecated (since := "2026-03-20")] alias w_ind := wInd

@[simp]

中文:
定义 wInd
  签名: {α : TypeVec n} {C : P.W α -> 类型层 v}
  定义体: fun ⟨hd, ch⟩ =>
  wpInd P (fun head f f' ih' =>
    cast
      (congr rfl <| Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq <| wPathCasesOn_eta P f'⟩)
 ih head (P.wPathDestLeft f') (fun i => ⟨f i, P.wPathDestRight f' i⟩) ih') hd ch

@[deprecated (since := "2026-03-20")] alias w_ind := wInd

@[simp]
-/
def wInd {α : TypeVec n} {C : P.W α -> Sort v}
    (ih : forall (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α),
        (forall i, C (f i)) -> C (P.wMk a f' f)) :
    forall x, C x := fun ⟨hd, ch⟩ =>
  wpInd P (fun head f f' ih' =>
    cast
      (congr rfl <| Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq <| wPathCasesOn_eta P f'⟩)
 ih head (P.wPathDestLeft f') (fun i => ⟨f i, P.wPathDestRight f' i⟩) ih') hd ch

@[deprecated (since := "2026-03-20")] alias w_ind := wInd

@[simp]
/--
theorem `wInd_wMk` / 定理 `wInd_wMk`

English:
theorem wInd_wMk
  statement: {α : TypeVec n} {C : P.W α -> Sort v}
  proof: rfl

中文:
定理 wInd_wMk
  结论: {α : TypeVec n} {C : P.W α -> 类型层 v}
  证明: rfl
-/
theorem wInd_wMk {α : TypeVec n} {C : P.W α -> Sort v}
    (ih : forall (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α),
        (forall i, C (f i)) -> C (P.wMk a f' f))
    {a : P.drop.A} {f' : P.drop.B a ⟹ α} {f : P.last.B a -> P.W α}
    : wInd P ih (wMk P a f' f) = ih a f' f (fun i => wInd P ih (f i)) := rfl

/-- Cases lemma for `W` types -/
@[elab_as_elim]
/--
Definition of `wCases` / `wCases` 的定义

English:
definition wCases
  signature: {α : TypeVec n} {C : P.W α -> Sort v}
  body: P.wInd fun a f' f _ih' => ih a f' f

@[deprecated (since := "2026-03-20")] alias w_cases := wCases

中文:
定义 wCases
  签名: {α : TypeVec n} {C : P.W α -> 类型层 v}
  定义体: P.wInd fun a f' f _ih' => ih a f' f

@[deprecated (since := "2026-03-20")] alias w_cases := wCases

Depends on / 依赖: P.wInd
-/
def wCases {α : TypeVec n} {C : P.W α -> Sort v}
    (ih : forall (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α), C (P.wMk a f' f)) :
    forall x, C x := P.wInd fun a f' f _ih' => ih a f' f

@[deprecated (since := "2026-03-20")] alias w_cases := wCases

/--
Definition of `wMap` / `wMap` 的定义

English:
definition wMap
  signature: {α β : TypeVec n} (g : α ⟹ β)
  body: fun x => g < > x

中文:
定义 wMap
  签名: {α β : TypeVec n} (g : α ⟹ β)
  定义体: fun x => g < > x
-/
def wMap {α β : TypeVec n} (g : α ⟹ β) : P.W α -> P.W β := fun x => g < > x

/--
theorem `wMk_eq` / 定理 `wMk_eq`

English:
theorem wMk_eq
  statement: {α : TypeVec n} (a : P.A) (f : P.last.B a -> P.last.W) (g' : P.drop.B a ⟹ α)
  proof: rfl

中文:
定理 wMk_eq
  结论: {α : TypeVec n} (a : P.A) (f : P.last.B a -> P.last.W) (g' : P.drop.B a ⟹ α)
  证明: rfl
-/
theorem wMk_eq {α : TypeVec n} (a : P.A) (f : P.last.B a -> P.last.W) (g' : P.drop.B a ⟹ α)
    (g : forall j : P.last.B a, P.WPath (f j) ⟹ α) :
    (P.wMk a g' fun i => ⟨f i, g i⟩) = ⟨⟨a, f⟩, P.wPathCasesOn g' g⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `w_map_wMk` / 定理 `w_map_wMk`

English:
theorem w_map_wMk
  statement: {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f' : P.drop.B a ⟹ α)
  proof: by
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
  rw [wMk_eq]; rw [wMk_eq]
  have h := MvPFunctor.map_eq P.wp g
  rw [h]; rw [comp_wPathCasesOn]

中文:
定理 w_map_wMk
  结论: {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f' : P.drop.B a ⟹ α)
  证明: by
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
  rw [wMk_eq]; rw [wMk_eq]
  have h := MvPFunctor.map_eq P.wp g
  rw [h]; rw [comp_wPathCasesOn]

Depends on / 依赖: Function, Function.comp_def, MvFunctor, MvFunctor.map, MvPFunctor, MvPFunctor.map_eq, P.wMk, P.wp, comp_def, comp_wPathCasesOn, map_eq, wMk_eq
-/
theorem w_map_wMk {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f' : P.drop.B a ⟹ α)
(f : P.last.B a -> P.W α) : g < > P.wMk a f' f = P.wMk a (g ⊚ f') fun i => g < > f i := by
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
  rw [wMk_eq]; rw [wMk_eq]
  have h := MvPFunctor.map_eq P.wp g
  rw [h]; rw [comp_wPathCasesOn]

-- TODO: this technical theorem is used in one place in constructing the initial algebra.
-- Can it be avoided?
/--
Definition of `objAppend1` / `objAppend1` 的定义

English:
abbreviation objAppend1
  signature: {α : TypeVec n} {β : Type u} (a : P.A) (f' : P.drop.B a ⟹ α)
  body: ⟨a, splitFun f' f⟩

中文:
缩写 objAppend1
  签名: {α : TypeVec n} {β : 类型u} (a : P.A) (f' : P.drop.B a ⟹ α)
  定义体: ⟨a, splitFun f' f⟩

Depends on / 依赖: splitFun
-/
abbrev objAppend1 {α : TypeVec n} {β : Type u} (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.last.B a -> β) : P (α ::: β) :=
  ⟨a, splitFun f' f⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_objAppend1` / 定理 `map_objAppend1`

English:
theorem map_objAppend1
  statement: {α γ : TypeVec n} (g : α ⟹ γ) (a : P.A) (f' : P.drop.B a ⟹ α)
  proof: by
  rw [objAppend1]; rw [objAppend1]; rw [map_eq]; rw [appendFun]; rw [← splitFun_comp]; rfl

中文:
定理 map_objAppend1
  结论: {α γ : TypeVec n} (g : α ⟹ γ) (a : P.A) (f' : P.drop.B a ⟹ α)
  证明: by
  rw [objAppend1]; rw [objAppend1]; rw [map_eq]; rw [appendFun]; rw [← splitFun_comp]; rfl

Depends on / 依赖: appendFun, map_eq, objAppend1, splitFun_comp
-/
theorem map_objAppend1 {α γ : TypeVec n} (g : α ⟹ γ) (a : P.A) (f' : P.drop.B a ⟹ α)
    (f : P.last.B a -> P.W α) :
appendFun g (P.wMap g) < > P.objAppend1 a f' f =
      P.objAppend1 a (g ⊚ f') fun x => P.wMap g (f x) := by
  rw [objAppend1]; rw [objAppend1]; rw [map_eq]; rw [appendFun]; rw [← splitFun_comp]; rfl

/-!
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/


/--
Definition of `wMk'` / `wMk'` 的定义

English:
definition wMk'
  signature: {α : TypeVec n}

中文:
定义 wMk'
  签名: {α : TypeVec n}
-/
def wMk' {α : TypeVec n} : P (α ::: P.W α) -> P.W α
  | ⟨a, f⟩ => P.wMk a (dropFun f) (lastFun f)

/--
Definition of `wDest'` / `wDest'` 的定义

English:
definition wDest'
  signature: {α : TypeVec.{u} n}
  body: P.wRec fun a f' f _ => ⟨a, splitFun f' f⟩

中文:
定义 wDest'
  签名: {α : TypeVec.{u} n}
  定义体: P.wRec fun a f' f _ => ⟨a, splitFun f' f⟩

Depends on / 依赖: P.wRec, splitFun
-/
def wDest' {α : TypeVec.{u} n} : P.W α -> P (α.append1 (P.W α)) :=
  P.wRec fun a f' f _ => ⟨a, splitFun f' f⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wDest'_wMk` / 定理 `wDest'_wMk`

English:
theorem wDest'_wMk
  given: {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α)
  proof: by rw [wDest', wRec_eq]

中文:
定理 wDest'_wMk
  条件: {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α)
  证明: by rw [wDest', wRec_eq]
-/
theorem wDest'_wMk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a -> P.W α) :
    P.wDest' (P.wMk a f' f) = ⟨a, splitFun f' f⟩ := by rw [wDest', wRec_eq]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wDest'_wMk'` / 定理 `wDest'_wMk'`

English:
theorem wDest'_wMk'
  given: {α : TypeVec n} (x : P (α.append1 (P.W α)))
  statement: P.wDest' (P.wMk' x) = x
  proof: by
  obtain ⟨a, f⟩ := x; rw [wMk', wDest'_wMk, split_dropFun_lastFun]

中文:
定理 wDest'_wMk'
  条件: {α : TypeVec n} (x : P (α.append1 (P.W α)))
  结论: P.wDest' (P.wMk' x) = x
  证明: by
  obtain ⟨a, f⟩ := x; rw [wMk', wDest'_wMk, split_dropFun_lastFun]
-/
theorem wDest'_wMk' {α : TypeVec n} (x : P (α.append1 (P.W α))) : P.wDest' (P.wMk' x) = x := by
  obtain ⟨a, f⟩ := x; rw [wMk', wDest'_wMk, split_dropFun_lastFun]

end MvPFunctor
