/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.M

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

* `M.mk` - constructor
* `M.dest` - destructor
* `M.corec` - corecursor: useful for formulating infinite, productive computations
* `M.bisim` - bisimulation: proof technique to show the equality of infinite objects

## Implementation notes

Dual view of M-types:

* `mp`: polynomial functor
* `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `mp` as:

* A := a possibly infinite tree-like structure without information in the nodes
* B := given the tree-like structure `t`, `B t` is a valid path
  from the root of `t` to any given node.

As a result `mp α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

@[expose] public section



universe u v

open MvFunctor

namespace MvPFunctor

open TypeVec

variable {n : Nat} (P : MvPFunctor.{u} (n + 1))

/--
Inductive type `M.Path` / 归纳类型 `M.Path`

English:
inductive M.Path
  parameters: : P.last.M -> Fin2 n -> Type u
  constructors (2):
    - root: (x : P.last.M) (a : P.A) (f : P.last.B a -> P.last.M) (h : PFunctor.M.dest x = ⟨a, f⟩) (i : Fin2 n) (c : P.drop.B a i) : M.Path x i
    - child: (x : P.last.M) (a : P.A) (f : P.last.B a -> P.last.M) (h : PFunctor.M.dest x = ⟨a, f⟩) (j : P.last.B a) (i : Fin2 n) (c : M.Path (f j) i) : M.Path x i

中文:
归纳类型 M.道路
  参数: : P.last.M -> Fin2 n -> 类型u
  构造子 (2 个):
    - root: (x : P.last.M) (a : P.A) (f : P.last.B a -> P.last.M) (h : P函子.M.dest x = ⟨a, f⟩) (i : Fin2 n) (c : P.drop.B a i) : M.道路 x i
    - child: (x : P.last.M) (a : P.A) (f : P.last.B a -> P.last.M) (h : P函子.M.dest x = ⟨a, f⟩) (j : P.last.B a) (i : Fin2 n) (c : M.道路 (f j) i) : M.道路 x i
-/
inductive M.Path : P.last.M -> Fin2 n -> Type u
  | root (x : P.last.M)
          (a : P.A)
          (f : P.last.B a -> P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (i : Fin2 n)
          (c : P.drop.B a i) : M.Path x i
  | child (x : P.last.M)
          (a : P.A)
          (f : P.last.B a -> P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (j : P.last.B a)
          (i : Fin2 n)
          (c : M.Path (f j) i) : M.Path x i

/--
Instance `M.Path.inhabited` / 实例 `M.Path.inhabited`

English:
instance M.Path.inhabited
  signature: (x : P.last.M) {i} [Inhabited (P.drop.B x.head i)]
  body: let a := PFunctor.M.head x
  let f := PFunctor.M.children x
  ⟨M.Path.root _ a f
      (PFunctor.M.casesOn' x
        (r := fun _ => PFunctor.M.dest x = ⟨a, f⟩)
 by
        intros; simp [a]; rfl)
      _ default⟩

中文:
实例 M.道路.inhabited
  签名: (x : P.last.M) {i} [可居 (P.drop.B x.head i)]
  定义体: let a := PFunctor.M.head x
  let f := PFunctor.M.children x
  ⟨M.Path.root _ a f
      (PFunctor.M.casesOn' x
        (r := fun _ => PFunctor.M.dest x = ⟨a, f⟩)
 by
        intros; simp [a]; rfl)
      _ default⟩

Depends on / 依赖: M.Path.root, PFunctor, PFunctor.M.casesOn, PFunctor.M.children, PFunctor.M.dest, PFunctor.M.head, casesOn, children, intros
-/
instance M.Path.inhabited (x : P.last.M) {i} [Inhabited (P.drop.B x.head i)] :
    Inhabited (M.Path P x i) :=
  let a := PFunctor.M.head x
  let f := PFunctor.M.children x
  ⟨M.Path.root _ a f
      (PFunctor.M.casesOn' x
        (r := fun _ => PFunctor.M.dest x = ⟨a, f⟩)
 by
        intros; simp [a]; rfl)
      _ default⟩

/--
Definition of `mp` / `mp` 的定义

English:
definition mp
  signature: : MvPFunctor n where
  body: P.last.M
  B := M.Path P

中文:
定义 mp
  签名: : MvP函子 n where
  定义体: P.last.M
  B := M.Path P

Depends on / 依赖: P.last.M
-/
def mp : MvPFunctor n where
  A := P.last.M
  B := M.Path P

/--
Definition of `M` / `M` 的定义

English:
definition M
  signature: (α : TypeVec n)
  body: P.mp α

中文:
定义 M
  签名: (α : TypeVec n)
  定义体: P.mp α

Depends on / 依赖: P.mp
-/
def M (α : TypeVec n) : Type _ :=
  P.mp α

/--
Instance `mvfunctorM` / 实例 `mvfunctorM`

English:
instance mvfunctorM
  signature: : MvFunctor P.M
  body: by delta M; infer_instance

中文:
实例 mvfunctorM
  签名: : Mv函子 P.M
  定义体: by delta M; infer_instance

Depends on / 依赖: infer_instance
-/
instance mvfunctorM : MvFunctor P.M := by delta M; infer_instance

/--
Instance `inhabitedM` / 实例 `inhabitedM`

English:
instance inhabitedM
  signature: {α : TypeVec _} [I : Inhabited P.A] [forall i : Fin2 n, Inhabited (α i)]
  body: @Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.last I) _

中文:
实例 inhabitedM
  签名: {α : TypeVec _} [I : 可居 P.A] [对任意 i : Fin2 n, 可居 (α i)]
  定义体: @Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.last I) _

Depends on / 依赖: Obj.inhabited, P.last, PFunctor, PFunctor.M.inhabited, inhabited
-/
instance inhabitedM {α : TypeVec _} [I : Inhabited P.A] [forall i : Fin2 n, Inhabited (α i)] :
    Inhabited (P.M α) :=
  @Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.last I) _

/--
Definition of `M.corecShape` / `M.corecShape` 的定义

English:
definition M.corecShape
  signature: {β : Type v} (g₀ : β -> P.A) (g₂ : forall b : β, P.last.B (g₀ b) -> β)
  body: PFunctor.M.corec fun b => ⟨g₀ b, g₂ b⟩

中文:
定义 M.corecShape
  签名: {β : 类型v} (g₀ : β -> P.A) (g₂ : 对任意 b : β, P.last.B (g₀ b) -> β)
  定义体: PFunctor.M.corec fun b => ⟨g₀ b, g₂ b⟩

Depends on / 依赖: PFunctor, PFunctor.M.corec
-/
def M.corecShape {β : Type v} (g₀ : β -> P.A) (g₂ : forall b : β, P.last.B (g₀ b) -> β) :
    β -> P.last.M :=
  PFunctor.M.corec fun b => ⟨g₀ b, g₂ b⟩

/--
Definition of `castDropB` / `castDropB` 的定义

English:
definition castDropB
  signature: {a a' : P.A} (h : a = a')
  body: fun _i b => Eq.recOn h b

中文:
定义 castDropB
  签名: {a a' : P.A} (h : a = a')
  定义体: fun _i b => Eq.recOn h b

Depends on / 依赖: Eq.recOn
-/
def castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' := fun _i b => Eq.recOn h b

/--
Definition of `castLastB` / `castLastB` 的定义

English:
definition castLastB
  signature: {a a' : P.A} (h : a = a')
  body: fun b => Eq.recOn h b

中文:
定义 castLastB
  签名: {a a' : P.A} (h : a = a')
  定义体: fun b => Eq.recOn h b

Depends on / 依赖: Eq.recOn
-/
def castLastB {a a' : P.A} (h : a = a') : P.last.B a -> P.last.B a' := fun b => Eq.recOn h b

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `M.corecContents` / `M.corecContents` 的定义

English:
definition M.corecContents
  signature: {α : TypeVec.{u} n}
  body: by
      rw [h]; rw [M.corecShape]; rw [PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    g₁ b i (P.castDropB this i c)
  | _, M.Path.child x a f h' j i c =>
    have h₀ : a = g₀ b := by
      rw [h]; rw [M.corecShape]; rw [PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    have h₁ : 

中文:
定义 M.corecContents
  签名: {α : TypeVec.{u} n}
  定义体: by
      rw [h]; rw [M.corecShape]; rw [PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    g₁ b i (P.castDropB this i c)
  | _, M.Path.child x a f h' j i c =>
    have h₀ : a = g₀ b := by
      rw [h]; rw [M.corecShape]; rw [PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    have h₁ : 

Depends on / 依赖: M.Path.child, M.corecContents, M.corecShape, P.castDropB, P.castLastB, PFunctor, PFunctor.M.dest_corec, castDropB, castLastB, corecContents, corecShape, dest_corec
-/
def M.corecContents {α : TypeVec.{u} n}
    {β : Type v}
    (g₀ : β -> P.A)
    (g₁ : forall b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : forall b : β, P.last.B (g₀ b) -> β)
    (x : _)
    (b : β)
    (h : x = M.corecShape P g₀ g₂ b) :
    M.Path P x ⟹ α
  | _, M.Path.root x a f h' i c =>
    have : a = g₀ b := by
      rw [h]; rw [M.corecShape]; rw [PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    g₁ b i (P.castDropB this i c)
  | _, M.Path.child x a f h' j i c =>
    have h₀ : a = g₀ b := by
      rw [h]; rw [M.corecShape]; rw [PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    have h₁ : f j = M.corecShape P g₀ g₂ (g₂ b (castLastB P h₀ j)) := by
      rw [h]; rw [M.corecShape]; rw [PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    M.corecContents g₀ g₁ g₂ (f j) (g₂ b (P.castLastB h₀ j)) h₁ i c

/--
Definition of `M.corec'` / `M.corec'` 的定义

English:
definition M.corec'
  signature: {α : TypeVec n} {β : Type v} (g₀ : β -> P.A) (g₁ : forall b : β, P.drop.B (g₀ b) ⟹ α)
  body: fun b =>
  ⟨M.corecShape P g₀ g₂ b, M.corecContents P g₀ g₁ g₂ _ _ rfl⟩

中文:
定义 M.corec'
  签名: {α : TypeVec n} {β : 类型v} (g₀ : β -> P.A) (g₁ : 对任意 b : β, P.drop.B (g₀ b) ⟹ α)
  定义体: fun b =>
  ⟨M.corecShape P g₀ g₂ b, M.corecContents P g₀ g₁ g₂ _ _ rfl⟩
-/
def M.corec' {α : TypeVec n} {β : Type v} (g₀ : β -> P.A) (g₁ : forall b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : forall b : β, P.last.B (g₀ b) -> β) : β -> P.M α := fun b =>
  ⟨M.corecShape P g₀ g₂ b, M.corecContents P g₀ g₁ g₂ _ _ rfl⟩

/--
Definition of `M.corec` / `M.corec` 的定义

English:
definition M.corec
  signature: {α : TypeVec n} {β : Type u} (g : β -> P (α.append1 β))
  body: M.corec' P (fun b => (g b).fst) (fun b => dropFun (g b).snd) fun b => lastFun (g b).snd

中文:
定义 M.corec
  签名: {α : TypeVec n} {β : 类型u} (g : β -> P (α.append1 β))
  定义体: M.corec' P (fun b => (g b).fst) (fun b => dropFun (g b).snd) fun b => lastFun (g b).snd

Depends on / 依赖: M.corec, dropFun, lastFun
-/
def M.corec {α : TypeVec n} {β : Type u} (g : β -> P (α.append1 β)) : β -> P.M α :=
  M.corec' P (fun b => (g b).fst) (fun b => dropFun (g b).snd) fun b => lastFun (g b).snd

/--
Definition of `M.pathDestLeft` / `M.pathDestLeft` 的定义

English:
definition M.pathDestLeft
  signature: {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a -> P.last.M}
  body: fun i c =>
  f' i (M.Path.root x a f h i c)

中文:
定义 M.pathDestLeft
  签名: {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a -> P.last.M}
  定义体: fun i c =>
  f' i (M.Path.root x a f h i c)
-/
def M.pathDestLeft {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a -> P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P.drop.B a ⟹ α := fun i c =>
  f' i (M.Path.root x a f h i c)

/--
Definition of `M.pathDestRight` / `M.pathDestRight` 的定义

English:
definition M.pathDestRight
  signature: {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a -> P.last.M}
  body: fun j i c => f' i (M.Path.child x a f h j i c)

中文:
定义 M.pathDestRight
  签名: {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a -> P.last.M}
  定义体: fun j i c => f' i (M.Path.child x a f h j i c)

Depends on / 依赖: M.Path.child
-/
def M.pathDestRight {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a -> P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    forall j : P.last.B a, M.Path P (f j) ⟹ α := fun j i c => f' i (M.Path.child x a f h j i c)

/--
Definition of `M.dest'` / `M.dest'` 的定义

English:
definition M.dest'
  signature: {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a -> P.last.M}
  body: ⟨a, splitFun (M.pathDestLeft P h f') fun x => ⟨f x, M.pathDestRight P h f' x⟩⟩

中文:
定义 M.dest'
  签名: {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a -> P.last.M}
  定义体: ⟨a, splitFun (M.pathDestLeft P h f') fun x => ⟨f x, M.pathDestRight P h f' x⟩⟩

Depends on / 依赖: M.pathDestLeft, M.pathDestRight, pathDestLeft, pathDestRight, splitFun
-/
def M.dest' {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a -> P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P (α.append1 (P.M α)) :=
  ⟨a, splitFun (M.pathDestLeft P h f') fun x => ⟨f x, M.pathDestRight P h f' x⟩⟩

/--
Definition of `M.dest` / `M.dest` 的定义

English:
definition M.dest
  signature: {α : TypeVec n} (x : P.M α)
  body: M.dest' P (Sigma.eta <| PFunctor.M.dest x.fst).symm x.snd

中文:
定义 M.dest
  签名: {α : TypeVec n} (x : P.M α)
  定义体: M.dest' P (Sigma.eta <| PFunctor.M.dest x.fst).symm x.snd

Depends on / 依赖: M.dest, PFunctor, PFunctor.M.dest, Sigma.eta, x.fst, x.snd
-/
def M.dest {α : TypeVec n} (x : P.M α) : P (α ::: P.M α) :=
  M.dest' P (Sigma.eta <| PFunctor.M.dest x.fst).symm x.snd

/--
Definition of `M.mk` / `M.mk` 的定义

English:
definition M.mk
  signature: {α : TypeVec n}
  body: M.corec _ fun i => appendFun id (M.dest P) < > i

中文:
定义 M.mk
  签名: {α : TypeVec n}
  定义体: M.corec _ fun i => appendFun id (M.dest P) < > i
-/
def M.mk {α : TypeVec n} : P (α.append1 (P.M α)) -> P.M α :=
M.corec _ fun i => appendFun id (M.dest P) < > i

/--
theorem `M.dest'_eq_dest'` / 定理 `M.dest'_eq_dest'`

English:
theorem M.dest'_eq_dest'
  statement: {α : TypeVec n} {x : P.last.M} {a₁ : P.A}
  proof: by cases h₁.symm.trans h₂; rfl

中文:
定理 M.dest'_eq_dest'
  结论: {α : TypeVec n} {x : P.last.M} {a₁ : P.A}
  证明: by cases h₁.symm.trans h₂; rfl
-/
theorem M.dest'_eq_dest' {α : TypeVec n} {x : P.last.M} {a₁ : P.A}
    {f₁ : P.last.B a₁ -> P.last.M} (h₁ : PFunctor.M.dest x = ⟨a₁, f₁⟩) {a₂ : P.A}
    {f₂ : P.last.B a₂ -> P.last.M} (h₂ : PFunctor.M.dest x = ⟨a₂, f₂⟩) (f' : M.Path P x ⟹ α) :
    M.dest' P h₁ f' = M.dest' P h₂ f' := by cases h₁.symm.trans h₂; rfl

/--
theorem `M.dest_eq_dest'` / 定理 `M.dest_eq_dest'`

English:
theorem M.dest_eq_dest'
  statement: {α : TypeVec n} {x : P.last.M} {a : P.A}
  proof: M.dest'_eq_dest' _ _ _ _

中文:
定理 M.dest_eq_dest'
  结论: {α : TypeVec n} {x : P.last.M} {a : P.A}
  证明: M.dest'_eq_dest' _ _ _ _

Depends on / 依赖: M.dest, _eq_dest
-/
theorem M.dest_eq_dest' {α : TypeVec n} {x : P.last.M} {a : P.A}
    {f : P.last.B a -> P.last.M} (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    M.dest P ⟨x, f'⟩ = M.dest' P h f' :=
  M.dest'_eq_dest' _ _ _ _

/--
theorem `M.dest_corec'` / 定理 `M.dest_corec'`

English:
theorem M.dest_corec'
  statement: {α : TypeVec.{u} n} {β : Type v} (g₀ : β -> P.A)
  proof: rfl

中文:
定理 M.dest_corec'
  结论: {α : TypeVec.{u} n} {β : 类型v} (g₀ : β -> P.A)
  证明: rfl
-/
theorem M.dest_corec' {α : TypeVec.{u} n} {β : Type v} (g₀ : β -> P.A)
    (g₁ : forall b : β, P.drop.B (g₀ b) ⟹ α) (g₂ : forall b : β, P.last.B (g₀ b) -> β) (x : β) :
    M.dest P (M.corec' P g₀ g₁ g₂ x) = ⟨g₀ x, splitFun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `M.dest_corec` / 定理 `M.dest_corec`

English:
theorem M.dest_corec
  given: {α : TypeVec n} {β : Type u} (g : β -> P (α.append1 β)) (x : β)
  proof: by
  trans
  · apply M.dest_corec'
  obtain ⟨a, f⟩ := g x; dsimp
  rw [MvPFunctor.map_eq]; congr
  conv_rhs => rw [← split_dropFun_lastFun f, appendFun_comp_splitFun]
  rfl

中文:
定理 M.dest_corec
  条件: {α : TypeVec n} {β : 类型u} (g : β -> P (α.append1 β)) (x : β)
  证明: by
  trans
  · apply M.dest_corec'
  obtain ⟨a, f⟩ := g x; dsimp
  rw [MvPFunctor.map_eq]; congr
  conv_rhs => rw [← split_dropFun_lastFun f, appendFun_comp_splitFun]
  rfl

Depends on / 依赖: M.dest_corec, MvPFunctor, MvPFunctor.map_eq, appendFun_comp_splitFun, conv_rhs, dest_corec, map_eq, split_dropFun_lastFun
-/
theorem M.dest_corec {α : TypeVec n} {β : Type u} (g : β -> P (α.append1 β)) (x : β) :
M.dest P (M.corec P g x) = appendFun id (M.corec P g) < > g x := by
  trans
  · apply M.dest_corec'
  obtain ⟨a, f⟩ := g x; dsimp
  rw [MvPFunctor.map_eq]; congr
  conv_rhs => rw [← split_dropFun_lastFun f, appendFun_comp_splitFun]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `M.bisim_lemma` / 定理 `M.bisim_lemma`

English:
theorem M.bisim_lemma
  statement: {α : TypeVec n} {a₁ : (mp P).A} {f₁ : (mp P).B a₁ ⟹ α} {a' : P.A}
  proof: by
  generalize ef : @splitFun n _ (append1 α (M P α)) f' f₁' = ff at e₁
  let he₁' := PFunctor.M.dest a₁
  rcases e₁' : he₁' with ⟨a₁', g₁'⟩
  rw [M.dest_eq_dest' _ e₁'] at e₁
  cases e₁; exact ⟨_, e₁', splitFun_inj ef⟩

中文:
定理 M.bisim_lemma
  结论: {α : TypeVec n} {a₁ : (mp P).A} {f₁ : (mp P).B a₁ ⟹ α} {a' : P.A}
  证明: by
  generalize ef : @splitFun n _ (append1 α (M P α)) f' f₁' = ff at e₁
  let he₁' := PFunctor.M.dest a₁
  rcases e₁' : he₁' with ⟨a₁', g₁'⟩
  rw [M.dest_eq_dest' _ e₁'] at e₁
  cases e₁; exact ⟨_, e₁', splitFun_inj ef⟩

Depends on / 依赖: M.dest_eq_dest, PFunctor, PFunctor.M.dest, append1, dest_eq_dest, generalize, splitFun, splitFun_inj
-/
theorem M.bisim_lemma {α : TypeVec n} {a₁ : (mp P).A} {f₁ : (mp P).B a₁ ⟹ α} {a' : P.A}
    {f' : (P.B a').drop ⟹ α} {f₁' : (P.B a').last -> M P α}
    (e₁ : M.dest P ⟨a₁, f₁⟩ = ⟨a', splitFun f' f₁'⟩) :
    exists (g₁' : _) (e₁' : PFunctor.M.dest a₁ = ⟨a', g₁'⟩),
      f' = M.pathDestLeft P e₁' f₁ ∧
        f₁' = fun x : (last P).B a' => ⟨g₁' x, M.pathDestRight P e₁' f₁ x⟩ := by
  generalize ef : @splitFun n _ (append1 α (M P α)) f' f₁' = ff at e₁
  let he₁' := PFunctor.M.dest a₁
  rcases e₁' : he₁' with ⟨a₁', g₁'⟩
  rw [M.dest_eq_dest' _ e₁'] at e₁
  cases e₁; exact ⟨_, e₁', splitFun_inj ef⟩

/--
theorem `M.bisim` / 定理 `M.bisim`

English:
theorem M.bisim
  statement: {α : TypeVec n} (R : P.M α -> P.M α -> Prop)
  proof: by
  obtain ⟨a₁, f₁⟩ := x
  obtain ⟨a₂, f₂⟩ := y
  dsimp [mp] at *
  have : a₁ = a₂ := by
    refine
      PFunctor.M.bisim (fun a₁ a₂ => exists x y, R x y ∧ x.1 = a₁ ∧ y.1 = a₂) ?_ _ _
        ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rcases h _ _ r with

中文:
定理 M.bisim
  结论: {α : TypeVec n} (R : P.M α -> P.M α -> 命题)
  证明: by
  obtain ⟨a₁, f₁⟩ := x
  obtain ⟨a₂, f₂⟩ := y
  dsimp [mp] at *
  have : a₁ = a₂ := by
    refine
      PFunctor.M.bisim (fun a₁ a₂ => exists x y, R x y ∧ x.1 = a₁ ∧ y.1 = a₂) ?_ _ _
        ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rcases h _ _ r with

Depends on / 依赖: M.bisim_lemma, PFunctor, PFunctor.M.bisim, bisim_lemma
-/
theorem M.bisim {α : TypeVec n} (R : P.M α -> P.M α -> Prop)
    (h :
      forall x y,
        R x y ->
          exists a f f₁ f₂,
            M.dest P x = ⟨a, splitFun f f₁⟩ ∧
              M.dest P y = ⟨a, splitFun f f₂⟩ ∧ forall i, R (f₁ i) (f₂ i))
    (x y) (r : R x y) : x = y := by
  obtain ⟨a₁, f₁⟩ := x
  obtain ⟨a₂, f₂⟩ := y
  dsimp [mp] at *
  have : a₁ = a₂ := by
    refine
      PFunctor.M.bisim (fun a₁ a₂ => exists x y, R x y ∧ x.1 = a₁ ∧ y.1 = a₂) ?_ _ _
        ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h'⟩
    rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩
    rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩
    rw [e₁']; rw [e₂']
    exact ⟨_, _, _, rfl, rfl, fun b => ⟨_, _, h' b, rfl, rfl⟩⟩
  subst this
  congr with (i p)
  induction p with (
    obtain ⟨a', f', f₁', f₂', e₁, e₂, h''⟩ := h _ _ r
    obtain ⟨g₁', e₁', rfl, rfl⟩ := M.bisim_lemma P e₁
    obtain ⟨g₂', e₂', e₃, rfl⟩ := M.bisim_lemma P e₂
    cases h'.symm.trans e₁'
    cases h'.symm.trans e₂')
  | root x a f h' i c =>
    exact congr_fun (congr_fun e₃ i) c
  | child x a f h' i c p IH =>
    exact IH _ _ (h'' _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `M.bisim₀` / 定理 `M.bisim₀`

English:
theorem M.bisim₀
  statement: {α : TypeVec n} (R : P.M α -> P.M α -> Prop) (h₀ : Equivalence R)
  proof: by
  apply M.bisim P R _ _ _ r
  clear r x y
  introv Hr
  specialize h _ _ Hr
  clear Hr
  revert h
  rcases M.dest P x with ⟨ax, fx⟩
  rcases M.dest P y with ⟨ay, fy⟩
  intro h
  rw [map_eq]; rw [map_eq] at h
  injection h with h₀ h₁
  subst ay
  simp only [heq_eq_eq] at h₁
  have Hdrop : dropFun 

中文:
定理 M.bisim₀
  结论: {α : TypeVec n} (R : P.M α -> P.M α -> 命题) (h₀ : 等价 R)
  证明: by
  apply M.bisim P R _ _ _ r
  clear r x y
  introv Hr
  specialize h _ _ Hr
  clear Hr
  revert h
  rcases M.dest P x with ⟨ax, fx⟩
  rcases M.dest P y with ⟨ay, fy⟩
  intro h
  rw [map_eq]; rw [map_eq] at h
  injection h with h₀ h₁
  subst ay
  simp only [heq_eq_eq] at h₁
  have Hdrop : dropFun 

Depends on / 依赖: M.bisim, M.dest, congr_arg, dropFun, heq_eq_eq, injection, introv, lastFun, map_eq, replace, revert, specialize, split_dropFun_lastFun, true_and
-/
theorem M.bisim₀ {α : TypeVec n} (R : P.M α -> P.M α -> Prop) (h₀ : Equivalence R)
    (h : forall x y, R x y -> (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y)
    (x y) (r : R x y) : x = y := by
  apply M.bisim P R _ _ _ r
  clear r x y
  introv Hr
  specialize h _ _ Hr
  clear Hr
  revert h
  rcases M.dest P x with ⟨ax, fx⟩
  rcases M.dest P y with ⟨ay, fy⟩
  intro h
  rw [map_eq]; rw [map_eq] at h
  injection h with h₀ h₁
  subst ay
  simp only [heq_eq_eq] at h₁
  have Hdrop : dropFun fx = dropFun fy := by
    replace h₁ := congr_arg dropFun h₁
    simpa using! h₁
  exists ax, dropFun fx, lastFun fx, lastFun fy
  rw [split_dropFun_lastFun]; rw [Hdrop]; rw [split_dropFun_lastFun]
  simp only [true_and]
  intro i
  replace h₁ := congr_fun (congr_fun h₁ Fin2.fz) i
  simp only [TypeVec.comp, appendFun, splitFun] at h₁
  replace h₁ := Quot.eqvGen_exact h₁
  rw [h₀.eqvGen_iff] at h₁
  exact h₁

/--
theorem `M.bisim'` / 定理 `M.bisim'`

English:
theorem M.bisim'
  statement: {α : TypeVec n} (R : P.M α -> P.M α -> Prop)
  proof: by
  have := M.bisim₀ P (Relation.EqvGen R) ?_ ?_
  · solve_by_elim [Relation.EqvGen.rel]
  · apply Relation.EqvGen.is_equivalence
  · clear r x y
    introv Hr
    have : forall x y, R x y -> Relation.EqvGen R x y := @Relation.EqvGen.rel _ R
    induction Hr
    · rw [← Quot.factor_mk_eq R (Relatio

中文:
定理 M.bisim'
  结论: {α : TypeVec n} (R : P.M α -> P.M α -> 命题)
  证明: by
  have := M.bisim₀ P (Relation.EqvGen R) ?_ ?_
  · solve_by_elim [Relation.EqvGen.rel]
  · apply Relation.EqvGen.is_equivalence
  · clear r x y
    introv Hr
    have : forall x y, R x y -> Relation.EqvGen R x y := @Relation.EqvGen.rel _ R
    induction Hr
    · rw [← Quot.factor_mk_eq R (Relatio

Depends on / 依赖: EqvGen, M.bisim, MvFunctor, MvFunctor.map_map, Quot.factor_mk_eq, Relation, Relation.EqvGen, Relation.EqvGen.is_equivalence, Relation.EqvGen.rel, all_goals, appendFun_comp_id, factor_mk_eq, introv, is_equivalence, map_map, solve_by_elim
-/
theorem M.bisim' {α : TypeVec n} (R : P.M α -> P.M α -> Prop)
    (h : forall x y, R x y -> (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y)
    (x y) (r : R x y) : x = y := by
  have := M.bisim₀ P (Relation.EqvGen R) ?_ ?_
  · solve_by_elim [Relation.EqvGen.rel]
  · apply Relation.EqvGen.is_equivalence
  · clear r x y
    introv Hr
    have : forall x y, R x y -> Relation.EqvGen R x y := @Relation.EqvGen.rel _ R
    induction Hr
    · rw [← Quot.factor_mk_eq R (Relation.EqvGen R) this]
      rwa [appendFun_comp_id, ← MvFunctor.map_map, ← MvFunctor.map_map, h]
    all_goals simp_all

set_option backward.isDefEq.respectTransparency false in
/--
theorem `M.dest_map` / 定理 `M.dest_map`

English:
theorem M.dest_map
  given: {α β : TypeVec n} (g : α ⟹ β) (x : P.M α)
  proof: by
  obtain ⟨a, f⟩ := x
  rw [map_eq]
  conv =>
    rhs
    rw [M.dest]; rw [M.dest']; rw [map_eq]; rw [appendFun_comp_splitFun]
  rfl

中文:
定理 M.dest_map
  条件: {α β : TypeVec n} (g : α ⟹ β) (x : P.M α)
  证明: by
  obtain ⟨a, f⟩ := x
  rw [map_eq]
  conv =>
    rhs
    rw [M.dest]; rw [M.dest']; rw [map_eq]; rw [appendFun_comp_splitFun]
  rfl

Depends on / 依赖: M.dest, appendFun_comp_splitFun, map_eq
-/
theorem M.dest_map {α β : TypeVec n} (g : α ⟹ β) (x : P.M α) :
M.dest P (g <$$> x) = (appendFun g fun x => g <$$> x) < > M.dest P x := by
  obtain ⟨a, f⟩ := x
  rw [map_eq]
  conv =>
    rhs
    rw [M.dest]; rw [M.dest']; rw [map_eq]; rw [appendFun_comp_splitFun]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `M.map_dest` / 定理 `M.map_dest`

English:
theorem M.map_dest
  statement: {α β : TypeVec n} (g : (α ::: P.M α) ⟹ (β ::: P.M β)) (x : P.M α)
  proof: by
  rw [M.dest_map]; congr
  apply eq_of_drop_last_eq (by simp)
  simp only [lastFun_appendFun]
  ext1; apply h

中文:
定理 M.map_dest
  结论: {α β : TypeVec n} (g : (α ::: P.M α) ⟹ (β ::: P.M β)) (x : P.M α)
  证明: by
  rw [M.dest_map]; congr
  apply eq_of_drop_last_eq (by simp)
  simp only [lastFun_appendFun]
  ext1; apply h

Depends on / 依赖: M.dest_map, dest_map, eq_of_drop_last_eq, lastFun_appendFun
-/
theorem M.map_dest {α β : TypeVec n} (g : (α ::: P.M α) ⟹ (β ::: P.M β)) (x : P.M α)
    (h : forall x : P.M α, lastFun g x = (dropFun g <$$> x : P.M β)) :
g < > M.dest P x = M.dest P (dropFun g <$$> x) := by
  rw [M.dest_map]; congr
  apply eq_of_drop_last_eq (by simp)
  simp only [lastFun_appendFun]
  ext1; apply h

end MvPFunctor
