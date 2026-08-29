/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# M-types

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.
-/

@[expose] public section


universe u uA uB v w

open Nat Function

open List

variable (F : PFunctor.{uA, uB})

namespace PFunctor

namespace Approx

/--
Inductive type `CofixA` / 归纳类型 `CofixA`

English:
inductive CofixA
  parameters: : Nat -> Type (max uA uB)
  constructors (2):
    - continue: CofixA 0
    - intro: {n} : forall a, (F.B a -> CofixA n) -> CofixA (succ n)

中文:
归纳类型 余fixA
  参数: : 自然数 -> 类型 (最大值 uA uB)
  构造子 (2 个):
    - continue: 余fixA 0
    - intro: {n} : 对任意 a, (F.B a -> 余fixA n) -> 余fixA (succ n)
-/
inductive CofixA : Nat -> Type (max uA uB)
  | continue : CofixA 0
  | intro {n} : forall a, (F.B a -> CofixA n) -> CofixA (succ n)

/--
Definition of `CofixA.default` / `CofixA.default` 的定义

English:
definition CofixA.default
  signature: [Inhabited F.A]

中文:
定义 余fixA.default
  签名: [可居 F.A]
-/
protected def CofixA.default [Inhabited F.A] : forall n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro default fun _ => CofixA.default n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: F.A] {n} : Inhabited (CofixA F n)
  body: ⟨CofixA.default F n⟩

中文:
实例 [可居
  签名: F.A] {n} : 可居 (余fixA F n)
  定义体: ⟨CofixA.default F n⟩

Depends on / 依赖: CofixA, CofixA.default
-/
instance [Inhabited F.A] {n} : Inhabited (CofixA F n) :=
  ⟨CofixA.default F n⟩

/--
theorem `cofixA_eq_zero` / 定理 `cofixA_eq_zero`

English:
theorem cofixA_eq_zero
  statement: forall x y : CofixA F 0, x = y

中文:
定理 cofixA_eq_zero
  结论: 对任意 x y : 余fixA F 0, x = y
-/
theorem cofixA_eq_zero : forall x y : CofixA F 0, x = y
  | CofixA.continue, CofixA.continue => rfl

variable {F}

/--
Definition of `head'` / `head'` 的定义

English:
definition head'
  signature: : forall {n}, CofixA F (succ n) -> F.A

中文:
定义 head'
  签名: : 对任意 {n}, 余fixA F (succ n) -> F.A
-/
def head' : forall {n}, CofixA F (succ n) -> F.A
  | _, CofixA.intro i _ => i

/--
Definition of `children'` / `children'` 的定义

English:
definition children'
  signature: : forall {n} (x : CofixA F (succ n)), F.B (head' x) -> CofixA F n

中文:
定义 children'
  签名: : 对任意 {n} (x : 余fixA F (succ n)), F.B (head' x) -> 余fixA F n
-/
def children' : forall {n} (x : CofixA F (succ n)), F.B (head' x) -> CofixA F n
  | _, CofixA.intro _ f => f

/--
theorem `approx_eta` / 定理 `approx_eta`

English:
theorem approx_eta
  given: {n : Nat} (x : CofixA F (n + 1))
  statement: x = CofixA.intro (head' x) (children' x)
  proof: by
  cases x; rfl

中文:
定理 approx_eta
  条件: {n : 自然数} (x : 余fixA F (n + 1))
  结论: x = 余fixA.intro (head' x) (children' x)
  证明: by
  cases x; rfl
-/
theorem approx_eta {n : Nat} (x : CofixA F (n + 1)) : x = CofixA.intro (head' x) (children' x) := by
  cases x; rfl

/--
Inductive type `Agree` / 归纳类型 `Agree`

English:
inductive Agree
  parameters: : forall {n : Nat}, CofixA F n -> CofixA F (n + 1) -> Prop
  constructors (2):
    - continu: (x : CofixA F 0) (y : CofixA F 1) : Agree x y
    - intro: {n} {a} (x : F.B a -> CofixA F n) (x' : F.B a -> CofixA F (n + 1)) : (forall i : F.B a, Agree (x i) (x' i)) -> Agree (CofixA.intro a x) (CofixA.intro a x')

中文:
归纳类型 Agree
  参数: : 对任意 {n : 自然数}, 余fixA F n -> 余fixA F (n + 1) -> 命题
  构造子 (2 个):
    - continu: (x : 余fixA F 0) (y : 余fixA F 1) : Agree x y
    - intro: {n} {a} (x : F.B a -> 余fixA F n) (x' : F.B a -> 余fixA F (n + 1)) : (对任意 i : F.B a, Agree (x i) (x' i)) -> Agree (余fixA.intro a x) (余fixA.intro a x')
-/
inductive Agree : forall {n : Nat}, CofixA F n -> CofixA F (n + 1) -> Prop
  | continu (x : CofixA F 0) (y : CofixA F 1) : Agree x y
  | intro {n} {a} (x : F.B a -> CofixA F n) (x' : F.B a -> CofixA F (n + 1)) :
    (forall i : F.B a, Agree (x i) (x' i)) -> Agree (CofixA.intro a x) (CofixA.intro a x')

/--
Definition of `AllAgree` / `AllAgree` 的定义

English:
definition AllAgree
  signature: (x : forall n, CofixA F n)
  body: forall n, Agree (x n) (x (succ n))

@[simp]

中文:
定义 AllAgree
  签名: (x : 对任意 n, 余fixA F n)
  定义体: forall n, Agree (x n) (x (succ n))

@[simp]
-/
def AllAgree (x : forall n, CofixA F n) :=
  forall n, Agree (x n) (x (succ n))

@[simp]
/--
theorem `agree_trivial` / 定理 `agree_trivial`

English:
theorem agree_trivial
  given: {x : CofixA F 0} {y : CofixA F 1}
  statement: Agree x y
  proof: by constructor

中文:
定理 agree_trivial
  条件: {x : 余fixA F 0} {y : 余fixA F 1}
  结论: Agree x y
  证明: by constructor
-/
theorem agree_trivial {x : CofixA F 0} {y : CofixA F 1} : Agree x y := by constructor

/--
theorem `agree_children` / 定理 `agree_children`

English:
theorem agree_children
  statement: {n : Nat} (x : CofixA F (succ n)) (y : CofixA F (succ n + 1)) {i j}
  proof: by
  obtain - | ⟨_, _, hagree⟩ := h₁; cases h₀
  apply hagree

中文:
定理 agree_children
  结论: {n : 自然数} (x : 余fixA F (succ n)) (y : 余fixA F (succ n + 1)) {i j}
  证明: by
  obtain - | ⟨_, _, hagree⟩ := h₁; cases h₀
  apply hagree

Depends on / 依赖: hagree
-/
theorem agree_children {n : Nat} (x : CofixA F (succ n)) (y : CofixA F (succ n + 1)) {i j}
    (h₀ : i ≍ j) (h₁ : Agree x y) : Agree (children' x i) (children' y j) := by
  obtain - | ⟨_, _, hagree⟩ := h₁; cases h₀
  apply hagree

/--
Definition of `truncate` / `truncate` 的定义

English:
definition truncate
  signature: : forall {n : Nat}, CofixA F (n + 1) -> CofixA F n

中文:
定义 truncate
  签名: : 对任意 {n : 自然数}, 余fixA F (n + 1) -> 余fixA F n
-/
def truncate : forall {n : Nat}, CofixA F (n + 1) -> CofixA F n
  | 0, CofixA.intro _ _ => CofixA.continue
| succ _, CofixA.intro i f => CofixA.intro i truncate ∘ f

/--
theorem `truncate_eq_of_agree` / 定理 `truncate_eq_of_agree`

English:
theorem truncate_eq_of_agree
  given: {n : Nat} (x : CofixA F n) (y : CofixA F (succ n)) (h : Agree x y)
  proof: by
  induction n with
  | zero =>
    cases x
    cases y
    rfl
  | succ n n_ih =>
    cases h with | intro f y h₁ =>
    simp only [truncate, Function.comp_def]
    congr with y
    exact n_ih _ _ (h₁ y)

中文:
定理 truncate_eq_of_agree
  条件: {n : 自然数} (x : 余fixA F n) (y : 余fixA F (succ n)) (h : Agree x y)
  证明: by
  induction n with
  | zero =>
    cases x
    cases y
    rfl
  | succ n n_ih =>
    cases h with | intro f y h₁ =>
    simp only [truncate, Function.comp_def]
    congr with y
    exact n_ih _ _ (h₁ y)

Depends on / 依赖: Function, Function.comp_def, comp_def, n_ih, truncate
-/
theorem truncate_eq_of_agree {n : Nat} (x : CofixA F n) (y : CofixA F (succ n)) (h : Agree x y) :
    truncate y = x := by
  induction n with
  | zero =>
    cases x
    cases y
    rfl
  | succ n n_ih =>
    cases h with | intro f y h₁ =>
    simp only [truncate, Function.comp_def]
    congr with y
    exact n_ih _ _ (h₁ y)

variable {X : Type w}
variable (f : X -> F X)

/--
Definition of `sCorec` / `sCorec` 的定义

English:
definition sCorec
  signature: : X -> forall n, CofixA F n

中文:
定义 sCorec
  签名: : X -> 对任意 n, 余fixA F n
-/
def sCorec : X -> forall n, CofixA F n
  | _, 0 => CofixA.continue
  | j, succ _ => CofixA.intro (f j).1 fun i => sCorec ((f j).2 i) _

/--
theorem `P_corec` / 定理 `P_corec`

English:
theorem P_corec
  given: (i : X) (n : Nat)
  statement: Agree (sCorec f i n) (sCorec f i (succ n))
  proof: by
  induction n generalizing i with
  | zero => constructor
  | succ n n_ih => exact .intro _ _ fun _ => n_ih _

中文:
定理 P_corec
  条件: (i : X) (n : 自然数)
  结论: Agree (sCorec f i n) (sCorec f i (succ n))
  证明: by
  induction n generalizing i with
  | zero => constructor
  | succ n n_ih => exact .intro _ _ fun _ => n_ih _

Depends on / 依赖: generalizing, n_ih
-/
theorem P_corec (i : X) (n : Nat) : Agree (sCorec f i n) (sCorec f i (succ n)) := by
  induction n generalizing i with
  | zero => constructor
  | succ n n_ih => exact .intro _ _ fun _ => n_ih _

/--
Definition of `Path` / `Path` 的定义

English:
definition Path
  signature: (F : PFunctor.{uA, uB})
  body: List F.Idx

中文:
定义 道路
  签名: (F : P函子.{uA, uB})
  定义体: List F.Idx

Depends on / 依赖: F.Idx
-/
def Path (F : PFunctor.{uA, uB}) :=
  List F.Idx

/--
Instance `Path.inhabited` / 实例 `Path.inhabited`

English:
instance Path.inhabited
  signature: : Inhabited (Path F)
  body: ⟨[]⟩

中文:
实例 道路.inhabited
  签名: : 可居 (道路 F)
  定义体: ⟨[]⟩
-/
instance Path.inhabited : Inhabited (Path F) :=
  ⟨[]⟩

/--
Instance `CofixA.instSubsingleton` / 实例 `CofixA.instSubsingleton`

English:
instance CofixA.instSubsingleton
  signature: : Subsingleton (CofixA F 0)
  body: ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

中文:
实例 余fixA.instSubsingleton
  签名: : 子单例 (余fixA F 0)
  定义体: ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
-/
instance CofixA.instSubsingleton : Subsingleton (CofixA F 0) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

/--
theorem `head_succ'` / 定理 `head_succ'`

English:
theorem head_succ'
  given: (n m : Nat) (x : forall n, CofixA F n) (Hconsistent : AllAgree x)
  proof: by
  suffices forall n, head' (x (succ n)) = head' (x 1) by simp [this]
  intro n
  induction n with
  | zero => grind
  | succ n n_ih => grind +splitIndPred [Hconsistent (succ n), head']

中文:
定理 head_succ'
  条件: (n m : 自然数) (x : 对任意 n, 余fixA F n) (Hconsistent : AllAgree x)
  证明: by
  suffices forall n, head' (x (succ n)) = head' (x 1) by simp [this]
  intro n
  induction n with
  | zero => grind
  | succ n n_ih => grind +splitIndPred [Hconsistent (succ n), head']

Depends on / 依赖: Hconsistent, n_ih, splitIndPred
-/
theorem head_succ' (n m : Nat) (x : forall n, CofixA F n) (Hconsistent : AllAgree x) :
    head' (x (succ n)) = head' (x (succ m)) := by
  suffices forall n, head' (x (succ n)) = head' (x 1) by simp [this]
  intro n
  induction n with
  | zero => grind
  | succ n n_ih => grind +splitIndPred [Hconsistent (succ n), head']

end Approx

open Approx

/--
Definition of `MIntl` / `MIntl` 的定义

English:
structure MIntl
  parameters: where
  axioms and operations (2):
    - approx : forall n, CofixA F n
    - consistent : AllAgree approx

中文:
结构 M整数l
  参数: where
  公理与运算 (2 个):
    - approx : 对任意 n, 余fixA F n
    - consistent : AllAgree approx
-/
structure MIntl where
  /-- An `n`-th level approximation, for each depth `n` -/
  approx : forall n, CofixA F n
  /-- Each approximation agrees with the next -/
  consistent : AllAgree approx

/--
Definition of `M` / `M` 的定义

English:
definition M
  body: MIntl F

中文:
定义 M
  定义体: MIntl F
-/
def M :=
  MIntl F

/--
theorem `M.default_consistent` / 定理 `M.default_consistent`

English:
theorem M.default_consistent
  given: [Inhabited F.A]
  statement: forall n, Agree (default : CofixA F n) default

中文:
定理 M.default_consistent
  条件: [可居 F.A]
  结论: 对任意 n, Agree (default : 余fixA F n) default
-/
theorem M.default_consistent [Inhabited F.A] : forall n, Agree (default : CofixA F n) default
  | 0 => Agree.continu _ _
  | succ n => Agree.intro _ _ fun _ => M.default_consistent n

/--
Instance `MIntl.inhabited` / 实例 `MIntl.inhabited`

English:
instance MIntl.inhabited
  signature: [Inhabited F.A]
  body: ⟨{ approx := default
      consistent := M.default_consistent _ }⟩

中文:
实例 M整数l.inhabited
  签名: [可居 F.A]
  定义体: ⟨{ approx := default
      consistent := M.default_consistent _ }⟩

Depends on / 依赖: M.default_consistent, approx, consistent, default_consistent
-/
instance MIntl.inhabited [Inhabited F.A] : Inhabited (MIntl F) :=
  ⟨{ approx := default
      consistent := M.default_consistent _ }⟩

/--
Instance `M.inhabited` / 实例 `M.inhabited`

English:
instance M.inhabited
  signature: [Inhabited F.A]
  body: inferInstanceAs Inhabited (MIntl F)

中文:
实例 M.inhabited
  签名: [可居 F.A]
  定义体: inferInstanceAs Inhabited (MIntl F)

Depends on / 依赖: Inhabited
-/
instance M.inhabited [Inhabited F.A] : Inhabited (M F) :=
inferInstanceAs Inhabited (MIntl F)

namespace M

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: (x y : M F) (H : forall i : Nat, x.approx i = y.approx i)
  statement: x = y
  proof: by
  cases x
  cases y
  congr with n
  apply H

中文:
定理 ext'
  条件: (x y : M F) (H : 对任意 i : 自然数, x.approx i = y.approx i)
  结论: x = y
  证明: by
  cases x
  cases y
  congr with n
  apply H
-/
theorem ext' (x y : M F) (H : forall i : Nat, x.approx i = y.approx i) : x = y := by
  cases x
  cases y
  congr with n
  apply H

variable {X : Type*}
variable (f : X -> F X)
variable {F}

/--
Definition of `corec` / `corec` 的定义

English:
definition corec
  signature: (i : X)
  body: sCorec f i
  consistent := P_corec _ _

中文:
定义 corec
  签名: (i : X)
  定义体: sCorec f i
  consistent := P_corec _ _
-/
protected def corec (i : X) : M F where
  approx := sCorec f i
  consistent := P_corec _ _

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: (x : M F)
  body: head' (x.1 1)

中文:
定义 head
  签名: (x : M F)
  定义体: head' (x.1 1)
-/
def head (x : M F) :=
  head' (x.1 1)

/--
Definition of `children` / `children` 的定义

English:
definition children
  signature: (x : M F) (i : F.B (head x))
  body: have H := fun n : Nat => @head_succ' _ n 0 x.1 x.2
  { approx := fun n => children' (x.1 _) (cast (congr_arg _ <| by simp only [head, H]) i)
    consistent := by
      intro n
      have P' := x.2 (succ n)
      apply agree_children _ _ _ P'
      trans i
      · apply cast_heq
      symm
      appl

中文:
定义 children
  签名: (x : M F) (i : F.B (head x))
  定义体: have H := fun n : Nat => @head_succ' _ n 0 x.1 x.2
  { approx := fun n => children' (x.1 _) (cast (congr_arg _ <| by simp only [head, H]) i)
    consistent := by
      intro n
      have P' := x.2 (succ n)
      apply agree_children _ _ _ P'
      trans i
      · apply cast_heq
      symm
      appl

Depends on / 依赖: agree_children, approx, cast_heq, children, congr_arg, consistent, head_succ
-/
def children (x : M F) (i : F.B (head x)) : M F :=
  have H := fun n : Nat => @head_succ' _ n 0 x.1 x.2
  { approx := fun n => children' (x.1 _) (cast (congr_arg _ <| by simp only [head, H]) i)
    consistent := by
      intro n
      have P' := x.2 (succ n)
      apply agree_children _ _ _ P'
      trans i
      · apply cast_heq
      symm
      apply cast_heq }

/--
Definition of `ichildren` / `ichildren` 的定义

English:
definition ichildren
  signature: [Inhabited (M F)] [DecidableEq F.A] (i : F.Idx) (x : M F)
  body: if H' : i.1 = head x then children x (cast (congr_arg _ <| by simp only [head, H']) i.2)
  else default

中文:
定义 ichildren
  签名: [可居 (M F)] [DecidableEq F.A] (i : F.Idx) (x : M F)
  定义体: if H' : i.1 = head x then children x (cast (congr_arg _ <| by simp only [head, H']) i.2)
  else default

Depends on / 依赖: children, congr_arg
-/
def ichildren [Inhabited (M F)] [DecidableEq F.A] (i : F.Idx) (x : M F) : M F :=
  if H' : i.1 = head x then children x (cast (congr_arg _ <| by simp only [head, H']) i.2)
  else default

/--
theorem `head_succ` / 定理 `head_succ`

English:
theorem head_succ
  given: (n m : Nat) (x : M F)
  statement: head' (x.approx (succ n)) = head' (x.approx (succ m))
  proof: head_succ' n m _ x.consistent

中文:
定理 head_succ
  条件: (n m : 自然数) (x : M F)
  结论: head' (x.approx (succ n)) = head' (x.approx (succ m))
  证明: head_succ' n m _ x.consistent

Depends on / 依赖: consistent, head_succ, x.consistent
-/
theorem head_succ (n m : Nat) (x : M F) : head' (x.approx (succ n)) = head' (x.approx (succ m)) :=
  head_succ' n m _ x.consistent

/--
theorem `head_eq_head'` / 定理 `head_eq_head'`

English:
theorem head_eq_head'
  statement: forall (x : M F) (n : Nat), head x = head' (x.approx <| n + 1)

中文:
定理 head_eq_head'
  结论: 对任意 (x : M F) (n : 自然数), head x = head' (x.approx <| n + 1)
-/
theorem head_eq_head' : forall (x : M F) (n : Nat), head x = head' (x.approx <| n + 1)
  | ⟨_, h⟩, _ => head_succ' _ _ _ h

/--
theorem `head'_eq_head` / 定理 `head'_eq_head`

English:
theorem head'_eq_head
  statement: forall (x : M F) (n : Nat), head' (x.approx <| n + 1) = head x

中文:
定理 head'_eq_head
  结论: 对任意 (x : M F) (n : 自然数), head' (x.approx <| n + 1) = head x
-/
theorem head'_eq_head : forall (x : M F) (n : Nat), head' (x.approx <| n + 1) = head x
  | ⟨_, h⟩, _ => head_succ' _ _ _ h

/--
theorem `truncate_approx` / 定理 `truncate_approx`

English:
theorem truncate_approx
  given: (x : M F) (n : Nat)
  statement: truncate (x.approx <| n + 1) = x.approx n
  proof: truncate_eq_of_agree _ _ (x.consistent _)

中文:
定理 truncate_approx
  条件: (x : M F) (n : 自然数)
  结论: truncate (x.approx <| n + 1) = x.approx n
  证明: truncate_eq_of_agree _ _ (x.consistent _)

Depends on / 依赖: consistent, truncate_eq_of_agree, x.consistent
-/
theorem truncate_approx (x : M F) (n : Nat) : truncate (x.approx <| n + 1) = x.approx n :=
  truncate_eq_of_agree _ _ (x.consistent _)

/--
Definition of `dest` / `dest` 的定义

English:
definition dest
  signature: : M F -> F (M F)

中文:
定义 dest
  签名: : M F -> F (M F)
-/
def dest : M F -> F (M F)
  | x => ⟨head x, fun i => children x i⟩

namespace Approx

/--
Definition of `sMk` / `sMk` 的定义

English:
definition sMk
  signature: (x : F (M F))

中文:
定义 sMk
  签名: (x : F (M F))
-/
protected def sMk (x : F (M F)) : forall n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro x.1 fun i => (x.2 i).approx n

/--
theorem `P_mk` / 定理 `P_mk`

English:
theorem P_mk
  given: (x : F (M F))
  statement: AllAgree (Approx.sMk x)

中文:
定理 P_mk
  条件: (x : F (M F))
  结论: AllAgree (Approx.sMk x)
-/
protected theorem P_mk (x : F (M F)) : AllAgree (Approx.sMk x)
  | 0 => by constructor
  | succ n => by
    constructor
    introv
    apply (x.2 i).consistent

end Approx

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : F (M F))
  body: Approx.sMk x
  consistent := Approx.P_mk x

中文:
定义 mk
  签名: (x : F (M F))
  定义体: Approx.sMk x
  consistent := Approx.P_mk x
-/
protected def mk (x : F (M F)) : M F where
  approx := Approx.sMk x
  consistent := Approx.P_mk x

/--
Inductive type `Agree'` / 归纳类型 `Agree'`

English:
inductive Agree'
  parameters: : Nat -> M F -> M F -> Prop
  constructors (2):
    - trivial: (x y : M F) : Agree' 0 x y
    - step: {n : Nat} {a} (x y : F.B a -> M F) {x' y'} : x' = M.mk ⟨a, x⟩ -> y' = M.mk ⟨a, y⟩ -> (forall i, Agree' n (x i) (y i)) -> Agree' (succ n) x' y'

中文:
归纳类型 Agree'
  参数: : 自然数 -> M F -> M F -> 命题
  构造子 (2 个):
    - trivial: (x y : M F) : Agree' 0 x y
    - step: {n : 自然数} {a} (x y : F.B a -> M F) {x' y'} : x' = M.mk ⟨a, x⟩ -> y' = M.mk ⟨a, y⟩ -> (对任意 i, Agree' n (x i) (y i)) -> Agree' (succ n) x' y'
-/
inductive Agree' : Nat -> M F -> M F -> Prop
  | trivial (x y : M F) : Agree' 0 x y
  | step {n : Nat} {a} (x y : F.B a -> M F) {x' y'} :
      x' = M.mk ⟨a, x⟩ -> y' = M.mk ⟨a, y⟩ -> (forall i, Agree' n (x i) (y i)) -> Agree' (succ n) x' y'

@[simp]
/--
theorem `dest_mk` / 定理 `dest_mk`

English:
theorem dest_mk
  given: (x : F (M F))
  statement: dest (M.mk x) = x
  proof: rfl

中文:
定理 dest_mk
  条件: (x : F (M F))
  结论: dest (M.mk x) = x
  证明: rfl
-/
theorem dest_mk (x : F (M F)) : dest (M.mk x) = x := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mk_dest` / 定理 `mk_dest`

English:
theorem mk_dest
  given: (x : M F)
  statement: M.mk (dest x) = x
  proof: by
  apply ext'
  intro n
  dsimp only [M.mk]
  induction n with
  | zero => apply @Subsingleton.elim _ CofixA.instSubsingleton
  | succ n => ?_
  dsimp only [Approx.sMk, dest, head]
  rcases h : x.approx (succ n) with - | ⟨hd, ch⟩
  have h' : hd = head' (x.approx 1) := by
    rw [← head_succ' n]; r

中文:
定理 mk_dest
  条件: (x : M F)
  结论: M.mk (dest x) = x
  证明: by
  apply ext'
  intro n
  dsimp only [M.mk]
  induction n with
  | zero => apply @Subsingleton.elim _ CofixA.instSubsingleton
  | succ n => ?_
  dsimp only [Approx.sMk, dest, head]
  rcases h : x.approx (succ n) with - | ⟨hd, ch⟩
  have h' : hd = head' (x.approx 1) := by
    rw [← head_succ' n]; r

Depends on / 依赖: Approx, Approx.sMk, CofixA, CofixA.instSubsingleton, M.mk, Subsingleton, Subsingleton.elim, approx, cast_eq_iff_heq, children, consistent, generalize, head_succ, instSubsingleton, revert, x.approx, x.consistent
-/
theorem mk_dest (x : M F) : M.mk (dest x) = x := by
  apply ext'
  intro n
  dsimp only [M.mk]
  induction n with
  | zero => apply @Subsingleton.elim _ CofixA.instSubsingleton
  | succ n => ?_
  dsimp only [Approx.sMk, dest, head]
  rcases h : x.approx (succ n) with - | ⟨hd, ch⟩
  have h' : hd = head' (x.approx 1) := by
    rw [← head_succ' n]; rw [h]; rw [head']
    apply x.consistent
  revert ch
  rw [h']
  intro ch h
  congr
  ext a
  dsimp only [children]
  generalize hh : cast _ a = a''
  rw [cast_eq_iff_heq] at hh
  revert a''
  rw [h]
  intro _ hh
  cases hh
  rfl

/--
theorem `mk_inj` / 定理 `mk_inj`

English:
theorem mk_inj
  given: {x y : F (M F)} (h : M.mk x = M.mk y)
  statement: x = y
  proof: by rw [← dest_mk x, h, dest_mk]

中文:
定理 mk_inj
  条件: {x y : F (M F)} (h : M.mk x = M.mk y)
  结论: x = y
  证明: by rw [← dest_mk x, h, dest_mk]

Depends on / 依赖: dest_mk
-/
theorem mk_inj {x y : F (M F)} (h : M.mk x = M.mk y) : x = y := by rw [← dest_mk x, h, dest_mk]

/--
Definition of `cases` / `cases` 的定义

English:
definition cases
  signature: {r : M F -> Sort w} (f : forall x : F (M F), r (M.mk x)) (x : M F)
  body: suffices r (M.mk (dest x)) by
    rw [← mk_dest x]
    exact this
  f _

中文:
定义 cases
  签名: {r : M F -> 类型层 w} (f : 对任意 x : F (M F), r (M.mk x)) (x : M F)
  定义体: suffices r (M.mk (dest x)) by
    rw [← mk_dest x]
    exact this
  f _
-/
protected def cases {r : M F -> Sort w} (f : forall x : F (M F), r (M.mk x)) (x : M F) : r x :=
  suffices r (M.mk (dest x)) by
    rw [← mk_dest x]
    exact this
  f _

/--
Definition of `casesOn` / `casesOn` 的定义

English:
definition casesOn
  signature: {r : M F -> Sort w} (x : M F) (f : forall x : F (M F), r (M.mk x))
  body: M.cases f x

中文:
定义 casesOn
  签名: {r : M F -> 类型层 w} (x : M F) (f : 对任意 x : F (M F), r (M.mk x))
  定义体: M.cases f x
-/
protected def casesOn {r : M F -> Sort w} (x : M F) (f : forall x : F (M F), r (M.mk x)) : r x :=
  M.cases f x

/--
Definition of `casesOn'` / `casesOn'` 的定义

English:
definition casesOn'
  signature: {r : M F -> Sort w} (x : M F) (f : forall a f, r (M.mk ⟨a, f⟩))
  body: M.casesOn x (fun ⟨a, g⟩ => f a g)

中文:
定义 casesOn'
  签名: {r : M F -> 类型层 w} (x : M F) (f : 对任意 a f, r (M.mk ⟨a, f⟩))
  定义体: M.casesOn x (fun ⟨a, g⟩ => f a g)
-/
protected def casesOn' {r : M F -> Sort w} (x : M F) (f : forall a f, r (M.mk ⟨a, f⟩)) : r x :=
  M.casesOn x (fun ⟨a, g⟩ => f a g)

/--
theorem `approx_mk` / 定理 `approx_mk`

English:
theorem approx_mk
  given: (a : F.A) (f : F.B a -> M F) (i : Nat)
  proof: rfl

@[simp]

中文:
定理 approx_mk
  条件: (a : F.A) (f : F.B a -> M F) (i : 自然数)
  证明: rfl

@[simp]
-/
theorem approx_mk (a : F.A) (f : F.B a -> M F) (i : Nat) :
    (M.mk ⟨a, f⟩).approx (succ i) = CofixA.intro a fun j => (f j).approx i :=
  rfl

@[simp]
/--
theorem `agree'_refl` / 定理 `agree'_refl`

English:
theorem agree'_refl
  given: {n : Nat} (x : M F)
  statement: Agree' n x x
  proof: by
  induction n generalizing x with | zero => ?_ | succ _ n_ih => ?_ <;>
  induction x using PFunctor.M.casesOn' <;> constructor <;> try rfl
  intro; apply n_ih

中文:
定理 agree'_refl
  条件: {n : 自然数} (x : M F)
  结论: Agree' n x x
  证明: by
  induction n generalizing x with | zero => ?_ | succ _ n_ih => ?_ <;>
  induction x using PFunctor.M.casesOn' <;> constructor <;> try rfl
  intro; apply n_ih

Depends on / 依赖: PFunctor, PFunctor.M.casesOn, casesOn, generalizing, n_ih
-/
theorem agree'_refl {n : Nat} (x : M F) : Agree' n x x := by
  induction n generalizing x with | zero => ?_ | succ _ n_ih => ?_ <;>
  induction x using PFunctor.M.casesOn' <;> constructor <;> try rfl
  intro; apply n_ih

/--
theorem `agree_iff_agree'` / 定理 `agree_iff_agree'`

English:
theorem agree_iff_agree'
  given: {n : Nat} (x y : M F)
  proof: by
  constructor <;> intro h
  · induction n generalizing x y with
    | zero => constructor
    | succ _ n_ih =>
      induction x using PFunctor.M.casesOn'
      induction y using PFunctor.M.casesOn'
      simp only [approx_mk] at h
      obtain - | ⟨_, _, hagree⟩ := h
      constructor <;> try rf

中文:
定理 agree_iff_agree'
  条件: {n : 自然数} (x y : M F)
  证明: by
  constructor <;> intro h
  · induction n generalizing x y with
    | zero => constructor
    | succ _ n_ih =>
      induction x using PFunctor.M.casesOn'
      induction y using PFunctor.M.casesOn'
      simp only [approx_mk] at h
      obtain - | ⟨_, _, hagree⟩ := h
      constructor <;> try rf

Depends on / 依赖: PFunctor, PFunctor.M.casesOn, approx_mk, casesOn, generalizing, hagree, n_ih
-/
theorem agree_iff_agree' {n : Nat} (x y : M F) :
    Agree (x.approx n) (y.approx <| n + 1) ↔ Agree' n x y := by
  constructor <;> intro h
  · induction n generalizing x y with
    | zero => constructor
    | succ _ n_ih =>
      induction x using PFunctor.M.casesOn'
      induction y using PFunctor.M.casesOn'
      simp only [approx_mk] at h
      obtain - | ⟨_, _, hagree⟩ := h
      constructor <;> try rfl
      intro i
      apply n_ih
      apply hagree
  · induction n generalizing x y with
    | zero => constructor
    | succ _ n_ih =>
      obtain - | @⟨_, a, x', y'⟩ := h
      induction x using PFunctor.M.casesOn' with | _ x_a x_f
      induction y using PFunctor.M.casesOn' with | _ y_a y_f
      simp only [approx_mk]
      have h_a_1 := mk_inj ‹M.mk ⟨x_a, x_f⟩ = M.mk ⟨a, x'⟩›
      cases h_a_1
      replace h_a_2 := mk_inj ‹M.mk ⟨y_a, y_f⟩ = M.mk ⟨a, y'⟩›
      cases h_a_2
      constructor
      intro i
      apply n_ih
      simp [*]

@[simp]
/--
theorem `cases_mk` / 定理 `cases_mk`

English:
theorem cases_mk
  given: {r : M F -> Sort*} (x : F (M F)) (f : forall x : F (M F), r (M.mk x))
  proof: rfl

@[simp]

中文:
定理 cases_mk
  条件: {r : M F -> 类型层*} (x : F (M F)) (f : 对任意 x : F (M F), r (M.mk x))
  证明: rfl

@[simp]
-/
theorem cases_mk {r : M F -> Sort*} (x : F (M F)) (f : forall x : F (M F), r (M.mk x)) :
    PFunctor.M.cases f (M.mk x) = f x := rfl

@[simp]
/--
theorem `casesOn_mk` / 定理 `casesOn_mk`

English:
theorem casesOn_mk
  given: {r : M F -> Sort*} (x : F (M F)) (f : forall x : F (M F), r (M.mk x))
  proof: cases_mk x f

@[simp]

中文:
定理 casesOn_mk
  条件: {r : M F -> 类型层*} (x : F (M F)) (f : 对任意 x : F (M F), r (M.mk x))
  证明: cases_mk x f

@[simp]

Depends on / 依赖: cases_mk
-/
theorem casesOn_mk {r : M F -> Sort*} (x : F (M F)) (f : forall x : F (M F), r (M.mk x)) :
    PFunctor.M.casesOn (M.mk x) f = f x :=
  cases_mk x f

@[simp]
/--
theorem `casesOn_mk'` / 定理 `casesOn_mk'`

English:
theorem casesOn_mk'
  statement: {r : M F -> Sort*} {a} (x : F.B a -> M F)
  proof: @cases_mk F r ⟨a, x⟩ (fun ⟨a, g⟩ => f a g)

中文:
定理 casesOn_mk'
  结论: {r : M F -> 类型层*} {a} (x : F.B a -> M F)
  证明: @cases_mk F r ⟨a, x⟩ (fun ⟨a, g⟩ => f a g)

Depends on / 依赖: cases_mk
-/
theorem casesOn_mk' {r : M F -> Sort*} {a} (x : F.B a -> M F)
    (f : forall (a) (f : F.B a -> M F), r (M.mk ⟨a, f⟩)) :
    PFunctor.M.casesOn' (M.mk ⟨a, x⟩) f = f a x :=
  @cases_mk F r ⟨a, x⟩ (fun ⟨a, g⟩ => f a g)

/--
Inductive type `IsPath` / 归纳类型 `IsPath`

English:
inductive IsPath
  parameters: : Path F -> M F -> Prop
  constructors (2):
    - nil: (x : M F) : IsPath [] x
    - cons: (xs : Path F) {a} (x : M F) (f : F.B a -> M F) (i : F.B a) : x = M.mk ⟨a, f⟩ -> IsPath xs (f i) -> IsPath (⟨a, i⟩ :: xs) x

中文:
归纳类型 是道路
  参数: : 道路 F -> M F -> 命题
  构造子 (2 个):
    - nil: (x : M F) : 是道路 [] x
    - cons: (xs : 道路 F) {a} (x : M F) (f : F.B a -> M F) (i : F.B a) : x = M.mk ⟨a, f⟩ -> 是道路 xs (f i) -> 是道路 (⟨a, i⟩ :: xs) x
-/
inductive IsPath : Path F -> M F -> Prop
  | nil (x : M F) : IsPath [] x
  | cons (xs : Path F) {a} (x : M F) (f : F.B a -> M F) (i : F.B a) :
    x = M.mk ⟨a, f⟩ -> IsPath xs (f i) -> IsPath (⟨a, i⟩ :: xs) x

/--
theorem `isPath_cons` / 定理 `isPath_cons`

English:
theorem isPath_cons
  given: {xs : Path F} {a a'} {f : F.B a -> M F} {i : F.B a'}
  proof: by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, _⟩)
  cases mk_inj h
  rfl

中文:
定理 isPath_cons
  条件: {xs : 道路 F} {a a'} {f : F.B a -> M F} {i : F.B a'}
  证明: by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, _⟩)
  cases mk_inj h
  rfl

Depends on / 依赖: M.mk, generalize, mk_inj
-/
theorem isPath_cons {xs : Path F} {a a'} {f : F.B a -> M F} {i : F.B a'} :
    IsPath (⟨a', i⟩ :: xs) (M.mk ⟨a, f⟩) -> a = a' := by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, _⟩)
  cases mk_inj h
  rfl

/--
theorem `isPath_cons'` / 定理 `isPath_cons'`

English:
theorem isPath_cons'
  given: {xs : Path F} {a} {f : F.B a -> M F} {i : F.B a}
  proof: by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, hp⟩)
  cases mk_inj h
  exact hp

中文:
定理 isPath_cons'
  条件: {xs : 道路 F} {a} {f : F.B a -> M F} {i : F.B a}
  证明: by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, hp⟩)
  cases mk_inj h
  exact hp

Depends on / 依赖: M.mk, generalize, mk_inj
-/
theorem isPath_cons' {xs : Path F} {a} {f : F.B a -> M F} {i : F.B a} :
    IsPath (⟨a, i⟩ :: xs) (M.mk ⟨a, f⟩) -> IsPath xs (f i) := by
  generalize h : M.mk ⟨a, f⟩ = x
  rintro (_ | ⟨_, _, _, _, rfl, hp⟩)
  cases mk_inj h
  exact hp

/--
Definition of `isubtree` / `isubtree` 的定义

English:
definition isubtree
  signature: [DecidableEq F.A] [Inhabited (M F)]

中文:
定义 isubtree
  签名: [DecidableEq F.A] [可居 (M F)]
-/
def isubtree [DecidableEq F.A] [Inhabited (M F)] : Path F -> M F -> M F
  | [], x => x
  | ⟨a, i⟩ :: ps, x =>
    PFunctor.M.casesOn' (r := fun _ => M F) x (fun a' f =>
      if h : a = a' then
        isubtree ps (f <| cast (by rw [h]) i)
      else
        default (α := M F))

/--
Definition of `iselect` / `iselect` 的定义

English:
definition iselect
  signature: [DecidableEq F.A] [Inhabited (M F)] (ps : Path F)
  body: fun x : M F =>
head isubtree ps x

中文:
定义 iselect
  签名: [DecidableEq F.A] [可居 (M F)] (ps : 道路 F)
  定义体: fun x : M F =>
head isubtree ps x
-/
def iselect [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) : M F -> F.A := fun x : M F =>
head isubtree ps x

/--
theorem `iselect_eq_default` / 定理 `iselect_eq_default`

English:
theorem iselect_eq_default
  statement: [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) (x : M F)
  proof: by
  induction ps generalizing x with
  | nil =>
    exfalso
    apply h
    constructor
  | cons ps_hd ps_tail ps_ih =>
    obtain ⟨a, i⟩ := ps_hd
    induction x using PFunctor.M.casesOn' with | _ x_a x_f
    simp only [iselect, isubtree] at ps_ih ⊢
    by_cases h'' : a = x_a
    · subst x_a
     

中文:
定理 iselect_eq_default
  结论: [DecidableEq F.A] [可居 (M F)] (ps : 道路 F) (x : M F)
  证明: by
  induction ps generalizing x with
  | nil =>
    exfalso
    apply h
    constructor
  | cons ps_hd ps_tail ps_ih =>
    obtain ⟨a, i⟩ := ps_hd
    induction x using PFunctor.M.casesOn' with | _ x_a x_f
    simp only [iselect, isubtree] at ps_ih ⊢
    by_cases h'' : a = x_a
    · subst x_a
     

Depends on / 依赖: PFunctor, PFunctor.M.casesOn, casesOn, casesOn_mk, dif_pos, generalizing, iselect, isubtree, ps_hd, ps_ih, ps_tail
-/
theorem iselect_eq_default [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) (x : M F)
    (h : ¬IsPath ps x) : iselect ps x = head default := by
  induction ps generalizing x with
  | nil =>
    exfalso
    apply h
    constructor
  | cons ps_hd ps_tail ps_ih =>
    obtain ⟨a, i⟩ := ps_hd
    induction x using PFunctor.M.casesOn' with | _ x_a x_f
    simp only [iselect, isubtree] at ps_ih ⊢
    by_cases h'' : a = x_a
    · subst x_a
      simp only [dif_pos, casesOn_mk']
      rw [ps_ih]
      intro h'
      apply h
      constructor <;> try rfl
      apply h'
    · simp [*]

@[simp]
/--
theorem `head_mk` / 定理 `head_mk`

English:
theorem head_mk
  given: (x : F (M F))
  statement: head (M.mk x) = x.1
  proof: Eq.symm
    calc
      x.1 = (dest (M.mk x)).1 := by rw [dest_mk]
      _ = head (M.mk x) := rfl

中文:
定理 head_mk
  条件: (x : F (M F))
  结论: head (M.mk x) = x.1
  证明: Eq.symm
    calc
      x.1 = (dest (M.mk x)).1 := by rw [dest_mk]
      _ = head (M.mk x) := rfl

Depends on / 依赖: Eq.symm, M.mk, dest_mk
-/
theorem head_mk (x : F (M F)) : head (M.mk x) = x.1 :=
Eq.symm
    calc
      x.1 = (dest (M.mk x)).1 := by rw [dest_mk]
      _ = head (M.mk x) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `children_mk` / 定理 `children_mk`

English:
theorem children_mk
  given: {a} (x : F.B a -> M F) (i : F.B (head (M.mk ⟨a, x⟩)))
  proof: by apply ext'; intro n; rfl

@[simp]

中文:
定理 children_mk
  条件: {a} (x : F.B a -> M F) (i : F.B (head (M.mk ⟨a, x⟩)))
  证明: by apply ext'; intro n; rfl

@[simp]
-/
theorem children_mk {a} (x : F.B a -> M F) (i : F.B (head (M.mk ⟨a, x⟩))) :
    children (M.mk ⟨a, x⟩) i = x (cast (by rw [head_mk]) i) := by apply ext'; intro n; rfl

@[simp]
/--
theorem `ichildren_mk` / 定理 `ichildren_mk`

English:
theorem ichildren_mk
  given: [DecidableEq F.A] [Inhabited (M F)] (x : F (M F)) (i : F.Idx)
  proof: by
  dsimp only [ichildren, PFunctor.Obj.iget]
  congr with h

@[simp]

中文:
定理 ichildren_mk
  条件: [DecidableEq F.A] [可居 (M F)] (x : F (M F)) (i : F.Idx)
  证明: by
  dsimp only [ichildren, PFunctor.Obj.iget]
  congr with h

@[simp]

Depends on / 依赖: PFunctor, PFunctor.Obj.iget, ichildren
-/
theorem ichildren_mk [DecidableEq F.A] [Inhabited (M F)] (x : F (M F)) (i : F.Idx) :
    ichildren i (M.mk x) = x.iget i := by
  dsimp only [ichildren, PFunctor.Obj.iget]
  congr with h

@[simp]
/--
theorem `isubtree_cons` / 定理 `isubtree_cons`

English:
theorem isubtree_cons
  statement: [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a -> M F)
  proof: by
  simp only [isubtree, dif_pos, isubtree, M.casesOn_mk']; rfl

@[simp]

中文:
定理 isubtree_cons
  结论: [DecidableEq F.A] [可居 (M F)] (ps : 道路 F) {a} (f : F.B a -> M F)
  证明: by
  simp only [isubtree, dif_pos, isubtree, M.casesOn_mk']; rfl

@[simp]

Depends on / 依赖: M.casesOn_mk, casesOn_mk, dif_pos, isubtree
-/
theorem isubtree_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a -> M F)
    {i : F.B a} : isubtree (⟨_, i⟩ :: ps) (M.mk ⟨a, f⟩) = isubtree ps (f i) := by
  simp only [isubtree, dif_pos, isubtree, M.casesOn_mk']; rfl

@[simp]
/--
theorem `iselect_nil` / 定理 `iselect_nil`

English:
theorem iselect_nil
  given: [DecidableEq F.A] [Inhabited (M F)] {a} (f : F.B a -> M F)
  proof: rfl

@[simp]

中文:
定理 iselect_nil
  条件: [DecidableEq F.A] [可居 (M F)] {a} (f : F.B a -> M F)
  证明: rfl

@[simp]
-/
theorem iselect_nil [DecidableEq F.A] [Inhabited (M F)] {a} (f : F.B a -> M F) :
    iselect nil (M.mk ⟨a, f⟩) = a := rfl

@[simp]
/--
theorem `iselect_cons` / 定理 `iselect_cons`

English:
theorem iselect_cons
  given: [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a -> M F) {i}
  proof: by simp only [iselect, isubtree_cons]

中文:
定理 iselect_cons
  条件: [DecidableEq F.A] [可居 (M F)] (ps : 道路 F) {a} (f : F.B a -> M F) {i}
  证明: by simp only [iselect, isubtree_cons]

Depends on / 依赖: iselect, isubtree_cons
-/
theorem iselect_cons [DecidableEq F.A] [Inhabited (M F)] (ps : Path F) {a} (f : F.B a -> M F) {i} :
    iselect (⟨a, i⟩ :: ps) (M.mk ⟨a, f⟩) = iselect ps (f i) := by simp only [iselect, isubtree_cons]

/--
theorem `corec_def` / 定理 `corec_def`

English:
theorem corec_def
  given: {X} (f : X -> F X) (x₀ : X)
  statement: M.corec f x₀ = M.mk (F.map (M.corec f) (f x₀))
  proof: by
  dsimp only [M.corec, M.mk]
  congr with n
  rcases n with - | n
  · dsimp only [sCorec, Approx.sMk]
  · dsimp only [sCorec, Approx.sMk]
    cases f x₀
    dsimp only [PFunctor.map]
    congr

中文:
定理 corec_def
  条件: {X} (f : X -> F X) (x₀ : X)
  结论: M.corec f x₀ = M.mk (F.map (M.corec f) (f x₀))
  证明: by
  dsimp only [M.corec, M.mk]
  congr with n
  rcases n with - | n
  · dsimp only [sCorec, Approx.sMk]
  · dsimp only [sCorec, Approx.sMk]
    cases f x₀
    dsimp only [PFunctor.map]
    congr

Depends on / 依赖: Approx, Approx.sMk, M.corec, M.mk, PFunctor, PFunctor.map, sCorec
-/
theorem corec_def {X} (f : X -> F X) (x₀ : X) : M.corec f x₀ = M.mk (F.map (M.corec f) (f x₀)) := by
  dsimp only [M.corec, M.mk]
  congr with n
  rcases n with - | n
  · dsimp only [sCorec, Approx.sMk]
  · dsimp only [sCorec, Approx.sMk]
    cases f x₀
    dsimp only [PFunctor.map]
    congr

/--
theorem `ext_aux` / 定理 `ext_aux`

English:
theorem ext_aux
  statement: [Inhabited (M F)] [DecidableEq F.A] {n : Nat} (x y z : M F) (hx : Agree' n z x)
  proof: by
  induction n generalizing x y z with
  | zero =>
    specialize hrec [] rfl
    induction x using PFunctor.M.casesOn'
    induction y using PFunctor.M.casesOn'
    simp only [iselect_nil] at hrec
    subst hrec
    simp only [approx_mk, heq_iff_eq, CofixA.intro.injEq,
      eq_iff_true_of_subsin

中文:
定理 ext_aux
  结论: [可居 (M F)] [DecidableEq F.A] {n : 自然数} (x y z : M F) (hx : Agree' n z x)
  证明: by
  induction n generalizing x y z with
  | zero =>
    specialize hrec [] rfl
    induction x using PFunctor.M.casesOn'
    induction y using PFunctor.M.casesOn'
    simp only [iselect_nil] at hrec
    subst hrec
    simp only [approx_mk, heq_iff_eq, CofixA.intro.injEq,
      eq_iff_true_of_subsin

Depends on / 依赖: CofixA, CofixA.intro.injEq, PFunctor, PFunctor.M.casesOn, and_self, approx_mk, casesOn, eq_iff_true_of_subsingleton, generalizing, heq_iff_eq, iselect_nil, iterate, mk_inj, n_ih, rename_i, specialize
-/
theorem ext_aux [Inhabited (M F)] [DecidableEq F.A] {n : Nat} (x y z : M F) (hx : Agree' n z x)
    (hy : Agree' n z y) (hrec : forall ps : Path F, n = ps.length -> iselect ps x = iselect ps y) :
    x.approx (n + 1) = y.approx (n + 1) := by
  induction n generalizing x y z with
  | zero =>
    specialize hrec [] rfl
    induction x using PFunctor.M.casesOn'
    induction y using PFunctor.M.casesOn'
    simp only [iselect_nil] at hrec
    subst hrec
    simp only [approx_mk, heq_iff_eq, CofixA.intro.injEq,
      eq_iff_true_of_subsingleton, and_self]
  | succ n n_ih =>
    cases hx
    cases hy
    induction x using PFunctor.M.casesOn'
    induction y using PFunctor.M.casesOn'
    subst z
    iterate 3 (have := mk_inj ‹_›; cases this)
    rename_i n_ih a f₃ f₂ hAgree₂ _ _ h₂ _ _ f₁ h₁ hAgree₁ clr
    simp only [approx_mk]
    have := mk_inj h₁
    cases this; clear h₁
    have := mk_inj h₂
    cases this; clear h₂
    congr
    ext i
    apply n_ih
    · solve_by_elim
    · solve_by_elim
    introv h
    specialize hrec (⟨_, i⟩ :: ps) (congr_arg _ h)
    simp only [iselect_cons] at hrec
    exact hrec

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: [Inhabited (M F)] [DecidableEq F.A] (x y : M F)
  proof: by
  apply ext'; intro i
  induction i with
  | zero => subsingleton
  | succ i i_ih =>
    apply ext_aux x y x
    · rw [← agree_iff_agree']
      apply x.consistent
    · rw [← agree_iff_agree', i_ih]
      apply y.consistent
    introv H'
    dsimp only [iselect] at H
    cases H'
    apply H ps

中文:
定理 ext
  结论: [可居 (M F)] [DecidableEq F.A] (x y : M F)
  证明: by
  apply ext'; intro i
  induction i with
  | zero => subsingleton
  | succ i i_ih =>
    apply ext_aux x y x
    · rw [← agree_iff_agree']
      apply x.consistent
    · rw [← agree_iff_agree', i_ih]
      apply y.consistent
    introv H'
    dsimp only [iselect] at H
    cases H'
    apply H ps

Depends on / 依赖: agree_iff_agree, consistent, ext_aux, i_ih, introv, iselect, subsingleton, x.consistent, y.consistent
-/
theorem ext [Inhabited (M F)] [DecidableEq F.A] (x y : M F)
    (H : forall ps : Path F, iselect ps x = iselect ps y) :
    x = y := by
  apply ext'; intro i
  induction i with
  | zero => subsingleton
  | succ i i_ih =>
    apply ext_aux x y x
    · rw [← agree_iff_agree']
      apply x.consistent
    · rw [← agree_iff_agree', i_ih]
      apply y.consistent
    introv H'
    dsimp only [iselect] at H
    cases H'
    apply H ps

section Bisim

variable (R : M F -> M F -> Prop)

local infixl:50 " ~ " => R

/--
Definition of `IsBisimulation` / `IsBisimulation` 的定义

English:
structure IsBisimulation
  parameters: : Prop where
  axioms and operations (2):
    - head : forall {a a'} {f f'}, M.mk ⟨a, f⟩ ~ M.mk ⟨a', f'⟩ -> a = a'
    - tail : forall {a} {f f' : F.B a -> M F}, M.mk ⟨a, f⟩ ~ M.mk ⟨a, f'⟩ -> forall i : F.B a, f i ~ f' i

中文:
结构 是Bisimulation
  参数: : 命题 where
  公理与运算 (2 个):
    - head : 对任意 {a a'} {f f'}, M.mk ⟨a, f⟩ ~ M.mk ⟨a', f'⟩ -> a = a'
    - tail : 对任意 {a} {f f' : F.B a -> M F}, M.mk ⟨a, f⟩ ~ M.mk ⟨a, f'⟩ -> 对任意 i : F.B a, f i ~ f' i
-/
structure IsBisimulation : Prop where
  /-- The head of the trees are equal -/
  head : forall {a a'} {f f'}, M.mk ⟨a, f⟩ ~ M.mk ⟨a', f'⟩ -> a = a'
  /-- The tails are equal -/
  tail : forall {a} {f f' : F.B a -> M F}, M.mk ⟨a, f⟩ ~ M.mk ⟨a, f'⟩ -> forall i : F.B a, f i ~ f' i

set_option backward.isDefEq.respectTransparency false in
/--
theorem `nth_of_bisim` / 定理 `nth_of_bisim`

English:
theorem nth_of_bisim
  statement: [Inhabited (M F)] [DecidableEq F.A]
  proof: by
  intro h₀ hh
  induction s₁ using PFunctor.M.casesOn' with | _ a f
  induction s₂ using PFunctor.M.casesOn' with | _ a' f'
  obtain rfl : a = a' := bisim.head h₀
  induction ps generalizing a f f' with
  | nil =>
    exists rfl, a, f, f', rfl, rfl
    apply bisim.tail h₀
  | cons i ps ps_ih => ?

中文:
定理 nth_of_bisim
  结论: [可居 (M F)] [DecidableEq F.A]
  证明: by
  intro h₀ hh
  induction s₁ using PFunctor.M.casesOn' with | _ a f
  induction s₂ using PFunctor.M.casesOn' with | _ a' f'
  obtain rfl : a = a' := bisim.head h₀
  induction ps generalizing a f f' with
  | nil =>
    exists rfl, a, f, f', rfl, rfl
    apply bisim.tail h₀
  | cons i ps ps_ih => ?

Depends on / 依赖: PFunctor, PFunctor.M.casesOn, bisim.head, bisim.tail, casesOn, generalizing, isPath_cons, iselect, ps_ih
-/
theorem nth_of_bisim [Inhabited (M F)] [DecidableEq F.A]
    (bisim : IsBisimulation R) (s₁ s₂) (ps : Path F) :
    (R s₁ s₂) ->
      IsPath ps s₁ ∨ IsPath ps s₂ ->
        iselect ps s₁ = iselect ps s₂ ∧
          exists (a : _) (f f' : F.B a -> M F),
            isubtree ps s₁ = M.mk ⟨a, f⟩ ∧
              isubtree ps s₂ = M.mk ⟨a, f'⟩ ∧ forall i : F.B a, f i ~ f' i := by
  intro h₀ hh
  induction s₁ using PFunctor.M.casesOn' with | _ a f
  induction s₂ using PFunctor.M.casesOn' with | _ a' f'
  obtain rfl : a = a' := bisim.head h₀
  induction ps generalizing a f f' with
  | nil =>
    exists rfl, a, f, f', rfl, rfl
    apply bisim.tail h₀
  | cons i ps ps_ih => ?_
  obtain ⟨a', i⟩ := i
  obtain rfl : a = a' := by rcases hh with hh | hh <;> cases isPath_cons hh <;> rfl
  dsimp only [iselect] at ps_ih ⊢
  have h₁ := bisim.tail h₀ i
  induction h : f i using PFunctor.M.casesOn' with | _ a₀ f₀
  induction h' : f' i using PFunctor.M.casesOn' with | _ a₁ f₁
  simp only [h, h', isubtree_cons] at ps_ih ⊢
  rw [h]; rw [h'] at h₁
  obtain rfl : a₀ = a₁ := bisim.head h₁
  apply ps_ih _ _ _ h₁
  rw [← h]; rw [← h']
  apply Or.imp isPath_cons' isPath_cons' hh

/--
theorem `eq_of_bisim` / 定理 `eq_of_bisim`

English:
theorem eq_of_bisim
  given: [Nonempty (M F)] (bisim : IsBisimulation R)
  statement: forall s₁ s₂, R s₁ s₂ -> s₁ = s₂
  proof: by
  inhabit M F
  classical
  introv Hr; apply ext
  introv
  by_cases h : IsPath ps s₁ ∨ IsPath ps s₂
  · have H := nth_of_bisim R bisim _ _ ps Hr h
    exact H.left
  · rw [not_or] at h
    obtain ⟨h₀, h₁⟩ := h
    simp only [iselect_eq_default, *, not_false_iff]

中文:
定理 eq_of_bisim
  条件: [非空 (M F)] (bisim : 是Bisimulation R)
  结论: 对任意 s₁ s₂, R s₁ s₂ -> s₁ = s₂
  证明: by
  inhabit M F
  classical
  introv Hr; apply ext
  introv
  by_cases h : IsPath ps s₁ ∨ IsPath ps s₂
  · have H := nth_of_bisim R bisim _ _ ps Hr h
    exact H.left
  · rw [not_or] at h
    obtain ⟨h₀, h₁⟩ := h
    simp only [iselect_eq_default, *, not_false_iff]

Depends on / 依赖: H.left, IsPath, classical, inhabit, introv, iselect_eq_default, not_false_iff, not_or, nth_of_bisim
-/
theorem eq_of_bisim [Nonempty (M F)] (bisim : IsBisimulation R) : forall s₁ s₂, R s₁ s₂ -> s₁ = s₂ := by
  inhabit M F
  classical
  introv Hr; apply ext
  introv
  by_cases h : IsPath ps s₁ ∨ IsPath ps s₂
  · have H := nth_of_bisim R bisim _ _ ps Hr h
    exact H.left
  · rw [not_or] at h
    obtain ⟨h₀, h₁⟩ := h
    simp only [iselect_eq_default, *, not_false_iff]

end Bisim

universe u' v'

/--
Definition of `corecOn` / `corecOn` 的定义

English:
definition corecOn
  signature: {X : Type*} (x₀ : X) (f : X -> F X)
  body: M.corec f x₀

中文:
定义 corecOn
  签名: {X : 类型} (x₀ : X) (f : X -> F X)
  定义体: M.corec f x₀

Depends on / 依赖: M.corec
-/
def corecOn {X : Type*} (x₀ : X) (f : X -> F X) : M F :=
  M.corec f x₀

variable {P : PFunctor.{uA, uB}} {α : Type*}

/--
theorem `dest_corec` / 定理 `dest_corec`

English:
theorem dest_corec
  given: (g : α -> P α) (x : α)
  statement: M.dest (M.corec g x) = P.map (M.corec g) (g x)
  proof: by
  rw [corec_def]; rw [dest_mk]

中文:
定理 dest_corec
  条件: (g : α -> P α) (x : α)
  结论: M.dest (M.corec g x) = P.map (M.corec g) (g x)
  证明: by
  rw [corec_def]; rw [dest_mk]

Depends on / 依赖: corec_def, dest_mk
-/
theorem dest_corec (g : α -> P α) (x : α) : M.dest (M.corec g x) = P.map (M.corec g) (g x) := by
  rw [corec_def]; rw [dest_mk]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `bisim` / 定理 `bisim`

English:
theorem bisim
  statement: (R : M P -> M P -> Prop)
  proof: by
  introv h'
  have := Inhabited.mk x.head
  apply eq_of_bisim R _ _ _ h'; clear h' x y
  constructor <;> introv ih <;> rcases h _ _ ih with ⟨a'', g, g', h₀, h₁, h₂⟩ <;> clear h
  · replace h₀ := congr_arg Sigma.fst h₀
    replace h₁ := congr_arg Sigma.fst h₁
    simp only [dest_mk] at h₀ h₁
    r

中文:
定理 bisim
  结论: (R : M P -> M P -> 命题)
  证明: by
  introv h'
  have := Inhabited.mk x.head
  apply eq_of_bisim R _ _ _ h'; clear h' x y
  constructor <;> introv ih <;> rcases h _ _ ih with ⟨a'', g, g', h₀, h₁, h₂⟩ <;> clear h
  · replace h₀ := congr_arg Sigma.fst h₀
    replace h₁ := congr_arg Sigma.fst h₁
    simp only [dest_mk] at h₀ h₁
    r

Depends on / 依赖: Inhabited, Inhabited.mk, Sigma.fst, congr_arg, dest_mk, eq_of_bisim, introv, replace, x.head
-/
theorem bisim (R : M P -> M P -> Prop)
    (h : forall x y, R x y -> exists a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ forall i, R (f i) (f' i)) :
    forall x y, R x y -> x = y := by
  introv h'
  have := Inhabited.mk x.head
  apply eq_of_bisim R _ _ _ h'; clear h' x y
  constructor <;> introv ih <;> rcases h _ _ ih with ⟨a'', g, g', h₀, h₁, h₂⟩ <;> clear h
  · replace h₀ := congr_arg Sigma.fst h₀
    replace h₁ := congr_arg Sigma.fst h₁
    simp only [dest_mk] at h₀ h₁
    rw [h₀]; rw [h₁]
  · simp only [dest_mk] at h₀ h₁
    cases h₀
    cases h₁
    apply h₂

/--
theorem `bisim'` / 定理 `bisim'`

English:
theorem bisim'
  statement: {α : Type*} (Q : α -> Prop) (u v : α -> M P)
  proof: fun x Qx =>
  let R := fun w z : M P => exists x', Q x' ∧ w = u x' ∧ z = v x'
  @M.bisim P R
    (fun _ _ ⟨x', Qx', xeq, yeq⟩ =>
      let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx'
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩

中文:
定理 bisim'
  结论: {α : 类型} (Q : α -> 命题) (u v : α -> M P)
  证明: fun x Qx =>
  let R := fun w z : M P => exists x', Q x' ∧ w = u x' ∧ z = v x'
  @M.bisim P R
    (fun _ _ ⟨x', Qx', xeq, yeq⟩ =>
      let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx'
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩
-/
theorem bisim' {α : Type*} (Q : α -> Prop) (u v : α -> M P)
    (h : forall x, Q x -> exists a f f',
          M.dest (u x) = ⟨a, f⟩
          ∧ M.dest (v x) = ⟨a, f'⟩
          ∧ forall i, exists x', Q x' ∧ f i = u x' ∧ f' i = v x') :
    forall x, Q x -> u x = v x := fun x Qx =>
  let R := fun w z : M P => exists x', Q x' ∧ w = u x' ∧ z = v x'
  @M.bisim P R
    (fun _ _ ⟨x', Qx', xeq, yeq⟩ =>
      let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx'
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩

-- for the record, show M_bisim follows from _bisim'
/--
theorem `bisim_equiv` / 定理 `bisim_equiv`

English:
theorem bisim_equiv
  statement: (R : M P -> M P -> Prop)
  proof: fun x y Rxy =>
  let Q : M P × M P -> Prop := fun p => R p.fst p.snd
  bisim' Q Prod.fst Prod.snd
    (fun p Qp =>
      let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp
      ⟨a, f, f', hx, hy, fun i => ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
    ⟨x, y⟩ Rxy

中文:
定理 bisim_equiv
  结论: (R : M P -> M P -> 命题)
  证明: fun x y Rxy =>
  let Q : M P × M P -> Prop := fun p => R p.fst p.snd
  bisim' Q Prod.fst Prod.snd
    (fun p Qp =>
      let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp
      ⟨a, f, f', hx, hy, fun i => ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
    ⟨x, y⟩ Rxy
-/
theorem bisim_equiv (R : M P -> M P -> Prop)
    (h : forall x y, R x y -> exists a f f', M.dest x = ⟨a, f⟩ ∧ M.dest y = ⟨a, f'⟩ ∧ forall i, R (f i) (f' i)) :
    forall x y, R x y -> x = y := fun x y Rxy =>
  let Q : M P × M P -> Prop := fun p => R p.fst p.snd
  bisim' Q Prod.fst Prod.snd
    (fun p Qp =>
      let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp
      ⟨a, f, f', hx, hy, fun i => ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
    ⟨x, y⟩ Rxy

/--
theorem `corec_unique` / 定理 `corec_unique`

English:
theorem corec_unique
  given: (g : α -> P α) (f : α -> M P) (hyp : forall x, M.dest (f x) = P.map f (g x))
  proof: by
  ext x
  apply bisim' (fun _ => True) _ _ _ _ trivial
  clear x
  intro x _
  rcases gxeq : g x with ⟨a, f'⟩
  have h₀ : M.dest (f x) = ⟨a, f ∘ f'⟩ := by rw [hyp, gxeq, PFunctor.map_eq]
  have h₁ : M.dest (M.corec g x) = ⟨a, M.corec g ∘ f'⟩ := by rw [dest_corec, gxeq, PFunctor.map_eq]
  refine ⟨

中文:
定理 corec_unique
  条件: (g : α -> P α) (f : α -> M P) (hyp : 对任意 x, M.dest (f x) = P.map f (g x))
  证明: by
  ext x
  apply bisim' (fun _ => True) _ _ _ _ trivial
  clear x
  intro x _
  rcases gxeq : g x with ⟨a, f'⟩
  have h₀ : M.dest (f x) = ⟨a, f ∘ f'⟩ := by rw [hyp, gxeq, PFunctor.map_eq]
  have h₁ : M.dest (M.corec g x) = ⟨a, M.corec g ∘ f'⟩ := by rw [dest_corec, gxeq, PFunctor.map_eq]
  refine ⟨

Depends on / 依赖: M.corec, M.dest, PFunctor, PFunctor.map_eq, dest_corec, map_eq
-/
theorem corec_unique (g : α -> P α) (f : α -> M P) (hyp : forall x, M.dest (f x) = P.map f (g x)) :
    f = M.corec g := by
  ext x
  apply bisim' (fun _ => True) _ _ _ _ trivial
  clear x
  intro x _
  rcases gxeq : g x with ⟨a, f'⟩
  have h₀ : M.dest (f x) = ⟨a, f ∘ f'⟩ := by rw [hyp, gxeq, PFunctor.map_eq]
  have h₁ : M.dest (M.corec g x) = ⟨a, M.corec g ∘ f'⟩ := by rw [dest_corec, gxeq, PFunctor.map_eq]
  refine ⟨_, _, _, h₀, h₁, ?_⟩
  intro i
  exact ⟨f' i, trivial, rfl, rfl⟩

/--
Definition of `corec₁` / `corec₁` 的定义

English:
definition corec₁
  signature: {α : Type u} (F : forall X, (α -> X) -> α -> P X)
  body: M.corec (F _ id)

中文:
定义 corec₁
  签名: {α : 类型u} (F : 对任意 X, (α -> X) -> α -> P X)
  定义体: M.corec (F _ id)

Depends on / 依赖: M.corec
-/
def corec₁ {α : Type u} (F : forall X, (α -> X) -> α -> P X) : α -> M P :=
  M.corec (F _ id)

/--
Definition of `corec'` / `corec'` 的定义

English:
definition corec'
  signature: {α : Type u} (F : forall {X : Type (max u uA uB)}, (α -> X) -> α -> M P oplus P X) (x : α)
  body: corec₁
    (fun _ rec (a : M P oplus α) =>
      let y := Sum.bind a (F (rec ∘ Sum.inr))
      match y with
      | Sum.inr y => y
      | Sum.inl y => P.map (rec ∘ Sum.inl) (M.dest y))
    (@Sum.inr (M P) _ x)

中文:
定义 corec'
  签名: {α : 类型u} (F : 对任意 {X : 类型 (最大值 u uA uB)}, (α -> X) -> α -> M P oplus P X) (x : α)
  定义体: corec₁
    (fun _ rec (a : M P oplus α) =>
      let y := Sum.bind a (F (rec ∘ Sum.inr))
      match y with
      | Sum.inr y => y
      | Sum.inl y => P.map (rec ∘ Sum.inl) (M.dest y))
    (@Sum.inr (M P) _ x)

Depends on / 依赖: M.dest, P.map, Sum.bind, Sum.inl, Sum.inr
-/
def corec' {α : Type u} (F : forall {X : Type (max u uA uB)}, (α -> X) -> α -> M P oplus P X) (x : α) : M P :=
  corec₁
    (fun _ rec (a : M P oplus α) =>
      let y := Sum.bind a (F (rec ∘ Sum.inr))
      match y with
      | Sum.inr y => y
      | Sum.inl y => P.map (rec ∘ Sum.inl) (M.dest y))
    (@Sum.inr (M P) _ x)

end M

end PFunctor
