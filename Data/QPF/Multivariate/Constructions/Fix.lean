/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Multivariate.W
public import Mathlib.Data.QPF.Multivariate.Basic

/-!
# The initial algebra of a multivariate qpf is again a qpf.

For an `(n+1)`-ary QPF `F (α₀,..,αₙ)`, we take the least fixed point of `F` with
regards to its last argument `αₙ`. The result is an `n`-ary functor: `Fix F (α₀,..,αₙ₋₁)`.
Making `Fix F` into a functor allows us to take the fixed point, compose with other functors
and take a fixed point again.

## Main definitions

* `Fix.mk` - constructor
* `Fix.dest` - destructor
* `Fix.rec` - recursor: basis for defining functions by structural recursion on `Fix F α`
* `Fix.drec` - dependent recursor: generalization of `Fix.rec` where
                  the result type of the function is allowed to depend on the `Fix F α` value
* `Fix.rec_eq` - defining equation for `recursor`
* `Fix.ind` - induction principle for `Fix F α`

## Implementation notes

For `F` a `QPF`, we define `Fix F α` in terms of the W-type of the polynomial functor `P` of `F`.
We define the relation `WEquiv` and take its quotient as the definition of `Fix F α`.

See [avigad-carneiro-hudon2019] for more details.

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

@[expose] public section


universe u v

namespace MvQPF

open TypeVec

open MvFunctor (LiftP LiftR)

open MvFunctor

variable {n : Nat} {F : TypeVec.{u} (n + 1) -> Type u} [q : MvQPF F]


/--
Definition of `recF` / `recF` 的定义

English:
definition recF
  signature: {α : TypeVec n} {β : Type u} (g : F (α.append1 β) -> β)
  body: q.P.wRec fun a f' _f rec => g (abs ⟨a, splitFun f' rec⟩)

中文:
定义 recF
  签名: {α : TypeVec n} {β : 类型u} (g : F (α.append1 β) -> β)
  定义体: q.P.wRec fun a f' _f rec => g (abs ⟨a, splitFun f' rec⟩)

Depends on / 依赖: q.P.wRec, splitFun
-/
def recF {α : TypeVec n} {β : Type u} (g : F (α.append1 β) -> β) : q.P.W α -> β :=
  q.P.wRec fun a f' _f rec => g (abs ⟨a, splitFun f' rec⟩)

/--
theorem `recF_eq` / 定理 `recF_eq`

English:
theorem recF_eq
  statement: {α : TypeVec n} {β : Type u} (g : F (α.append1 β) -> β) (a : q.P.A)
  proof: by
  rw [recF]; rw [MvPFunctor.wRec_eq]; rfl

中文:
定理 recF_eq
  结论: {α : TypeVec n} {β : 类型u} (g : F (α.append1 β) -> β) (a : q.P.A)
  证明: by
  rw [recF]; rw [MvPFunctor.wRec_eq]; rfl

Depends on / 依赖: MvPFunctor, MvPFunctor.wRec_eq, wRec_eq
-/
theorem recF_eq {α : TypeVec n} {β : Type u} (g : F (α.append1 β) -> β) (a : q.P.A)
    (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a -> q.P.W α) :
    recF g (q.P.wMk a f' f) = g (abs ⟨a, splitFun f' (recF g ∘ f)⟩) := by
  rw [recF]; rw [MvPFunctor.wRec_eq]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `recF_eq'` / 定理 `recF_eq'`

English:
theorem recF_eq'
  given: {α : TypeVec n} {β : Type u} (g : F (α.append1 β) -> β) (x : q.P.W α)
  proof: by
  induction x using q.P.wCases
  case ih a f' f =>
    rw [recF_eq]; rw [q.P.wDest'_wMk]; rw [MvPFunctor.map_eq]; rw [appendFun_comp_splitFun]; rw [TypeVec.id_comp]

中文:
定理 recF_eq'
  条件: {α : TypeVec n} {β : 类型u} (g : F (α.append1 β) -> β) (x : q.P.W α)
  证明: by
  induction x using q.P.wCases
  case ih a f' f =>
    rw [recF_eq]; rw [q.P.wDest'_wMk]; rw [MvPFunctor.map_eq]; rw [appendFun_comp_splitFun]; rw [TypeVec.id_comp]

Depends on / 依赖: MvPFunctor, MvPFunctor.map_eq, TypeVec, TypeVec.id_comp, _wMk, appendFun_comp_splitFun, id_comp, map_eq, q.P.wCases, q.P.wDest, recF_eq, wCases
-/
theorem recF_eq' {α : TypeVec n} {β : Type u} (g : F (α.append1 β) -> β) (x : q.P.W α) :
    recF g x = g (abs (appendFun id (recF g) <$$> q.P.wDest' x)) := by
  induction x using q.P.wCases
  case ih a f' f =>
    rw [recF_eq]; rw [q.P.wDest'_wMk]; rw [MvPFunctor.map_eq]; rw [appendFun_comp_splitFun]; rw [TypeVec.id_comp]

/--
Inductive type `WEquiv` / 归纳类型 `WEquiv`

English:
inductive WEquiv
  parameters: {α : TypeVec n}
  constructors (3):
    - ind: (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f₀ f₁ : q.P.last.B a -> q.P.W α) : (forall x, WEquiv (f₀ x) (f₁ x)) -> WEquiv (q.P.wMk a f' f₀) (q.P.wMk a f' f₁)
    - abs: (a₀ : q.P.A) (f'₀ : q.P.drop.B a₀ ⟹ α) (f₀ : q.P.last.B a₀ -> q.P.W α) (a₁ : q.P.A) (f'₁ : q.P.drop.B a₁ ⟹ α) (f₁ : q.P.last.B a₁ -> q.P.W α) : abs ⟨a₀, q.P.appendContents f'₀ f₀⟩ = abs ⟨a₁, q.P.appendContents f'₁ f₁⟩ -> WEquiv (q.P.wMk a₀ f'₀ f₀) (q.P.wMk a₁ f'₁ f₁)
    - trans: (u v w : q.P.W α) : WEquiv u v -> WEquiv v w -> WEquiv u w

中文:
归纳类型 W等价
  参数: {α : TypeVec n}
  构造子 (3 个):
    - ind: (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f₀ f₁ : q.P.last.B a -> q.P.W α) : (对任意 x, W等价 (f₀ x) (f₁ x)) -> W等价 (q.P.wMk a f' f₀) (q.P.wMk a f' f₁)
    - abs: (a₀ : q.P.A) (f'₀ : q.P.drop.B a₀ ⟹ α) (f₀ : q.P.last.B a₀ -> q.P.W α) (a₁ : q.P.A) (f'₁ : q.P.drop.B a₁ ⟹ α) (f₁ : q.P.last.B a₁ -> q.P.W α) : abs ⟨a₀, q.P.appendContents f'₀ f₀⟩ = abs ⟨a₁, q.P.appendContents f'₁ f₁⟩ -> W等价 (q.P.wMk a₀ f'₀ f₀) (q.P.wMk a₁ f'₁ f₁)
    - trans: (u v w : q.P.W α) : W等价 u v -> W等价 v w -> W等价 u w
-/
inductive WEquiv {α : TypeVec n} : q.P.W α -> q.P.W α -> Prop
  | ind (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f₀ f₁ : q.P.last.B a -> q.P.W α) :
    (forall x, WEquiv (f₀ x) (f₁ x)) -> WEquiv (q.P.wMk a f' f₀) (q.P.wMk a f' f₁)
  | abs (a₀ : q.P.A) (f'₀ : q.P.drop.B a₀ ⟹ α) (f₀ : q.P.last.B a₀ -> q.P.W α) (a₁ : q.P.A)
    (f'₁ : q.P.drop.B a₁ ⟹ α) (f₁ : q.P.last.B a₁ -> q.P.W α) :
    abs ⟨a₀, q.P.appendContents f'₀ f₀⟩ = abs ⟨a₁, q.P.appendContents f'₁ f₁⟩ ->
      WEquiv (q.P.wMk a₀ f'₀ f₀) (q.P.wMk a₁ f'₁ f₁)
  | trans (u v w : q.P.W α) : WEquiv u v -> WEquiv v w -> WEquiv u w

set_option backward.isDefEq.respectTransparency false in
/--
theorem `recF_eq_of_wEquiv` / 定理 `recF_eq_of_wEquiv`

English:
theorem recF_eq_of_wEquiv
  given: (α : TypeVec n) {β : Type u} (u : F (α.append1 β) -> β) (x y : q.P.W α)
  proof: by
  induction x using q.P.wCases
  case ih a₀ f'₀ f₀ =>
    induction y using q.P.wCases
    case ih a₁ f'₁ f₁ =>
      intro h
      -- Porting note: induction on h doesn't work.
      refine @WEquiv.recOn _ _ _ _ (fun a a' _ => recF u a = recF u a') _ _ h ?_ ?_ ?_
      · intro a f' f₀ f₁ _h ih; simp only [recF_eq]
        congr 4; funext; apply ih
      · intro a₀ f'₀ f₀ a₁ f'₁ f₁ h; simp only [recF_eq', abs_map, MvPFunctor.wDest'_wMk, h]
      · intro x y z _e₁ _e₂ ih₁ ih₂; exact Eq.trans ih₁ ih₂

中文:
定理 recF_eq_of_wEquiv
  条件: (α : TypeVec n) {β : 类型u} (u : F (α.append1 β) -> β) (x y : q.P.W α)
  证明: by
  induction x using q.P.wCases
  case ih a₀ f'₀ f₀ =>
    induction y using q.P.wCases
    case ih a₁ f'₁ f₁ =>
      intro h
      -- Porting note: induction on h doesn't work.
      refine @WEquiv.recOn _ _ _ _ (fun a a' _ => recF u a = recF u a') _ _ h ?_ ?_ ?_
      · intro a f' f₀ f₁ _h ih; simp only [recF_eq]
        congr 4; funext; apply ih
      · intro a₀ f'₀ f₀ a₁ f'₁ f₁ h; simp only [recF_eq', abs_map, MvPFunctor.wDest'_wMk, h]
      · intro x y z _e₁ _e₂ ih₁ ih₂; exact Eq.trans ih₁ ih₂

Depends on / 依赖: q.P.wCases, wCases
-/
theorem recF_eq_of_wEquiv (α : TypeVec n) {β : Type u} (u : F (α.append1 β) -> β) (x y : q.P.W α) :
    WEquiv x y -> recF u x = recF u y := by
  induction x using q.P.wCases
  case ih a₀ f'₀ f₀ =>
    induction y using q.P.wCases
    case ih a₁ f'₁ f₁ =>
      intro h
      -- Porting note: induction on h doesn't work.
      refine @WEquiv.recOn _ _ _ _ (fun a a' _ => recF u a = recF u a') _ _ h ?_ ?_ ?_
      · intro a f' f₀ f₁ _h ih; simp only [recF_eq]
        congr 4; funext; apply ih
      · intro a₀ f'₀ f₀ a₁ f'₁ f₁ h; simp only [recF_eq', abs_map, MvPFunctor.wDest'_wMk, h]
      · intro x y z _e₁ _e₂ ih₁ ih₂; exact Eq.trans ih₁ ih₂

/--
theorem `wEquiv.abs'` / 定理 `wEquiv.abs'`

English:
theorem wEquiv.abs'
  statement: {α : TypeVec n} (x y : q.P.W α)
  proof: by
  revert h
  induction x using q.P.wCases
  case ih a₀ f'₀ f₀ =>
    induction y using q.P.wCases
    apply WEquiv.abs

中文:
定理 wEquiv.abs'
  结论: {α : TypeVec n} (x y : q.P.W α)
  证明: by
  revert h
  induction x using q.P.wCases
  case ih a₀ f'₀ f₀ =>
    induction y using q.P.wCases
    apply WEquiv.abs

Depends on / 依赖: WEquiv, WEquiv.abs, q.P.wCases, revert, wCases
-/
theorem wEquiv.abs' {α : TypeVec n} (x y : q.P.W α)
    (h : MvQPF.abs (q.P.wDest' x) = MvQPF.abs (q.P.wDest' y)) :
    WEquiv x y := by
  revert h
  induction x using q.P.wCases
  case ih a₀ f'₀ f₀ =>
    induction y using q.P.wCases
    apply WEquiv.abs

/--
theorem `wEquiv.refl` / 定理 `wEquiv.refl`

English:
theorem wEquiv.refl
  given: {α : TypeVec n} (x : q.P.W α)
  statement: WEquiv x x
  proof: abs' x x rfl

中文:
定理 wEquiv.refl
  条件: {α : TypeVec n} (x : q.P.W α)
  结论: W等价 x x
  证明: abs' x x rfl
-/
theorem wEquiv.refl {α : TypeVec n} (x : q.P.W α) : WEquiv x x := abs' x x rfl

/--
theorem `wEquiv.symm` / 定理 `wEquiv.symm`

English:
theorem wEquiv.symm
  given: {α : TypeVec n} (x y : q.P.W α)
  statement: WEquiv x y -> WEquiv y x
  proof: by
  intro h; induction h with
  | ind a f' f₀ f₁ _h ih => exact WEquiv.ind _ _ _ _ ih
  | abs a₀ f'₀ f₀ a₁ f'₁ f₁ h => exact WEquiv.abs _ _ _ _ _ _ h.symm
  | trans x y z _e₁ _e₂ ih₁ ih₂ => exact MvQPF.WEquiv.trans _ _ _ ih₂ ih₁

中文:
定理 wEquiv.symm
  条件: {α : TypeVec n} (x y : q.P.W α)
  结论: W等价 x y -> W等价 y x
  证明: by
  intro h; induction h with
  | ind a f' f₀ f₁ _h ih => exact WEquiv.ind _ _ _ _ ih
  | abs a₀ f'₀ f₀ a₁ f'₁ f₁ h => exact WEquiv.abs _ _ _ _ _ _ h.symm
  | trans x y z _e₁ _e₂ ih₁ ih₂ => exact MvQPF.WEquiv.trans _ _ _ ih₂ ih₁

Depends on / 依赖: MvQPF.WEquiv.trans, WEquiv, WEquiv.abs, WEquiv.ind, h.symm
-/
theorem wEquiv.symm {α : TypeVec n} (x y : q.P.W α) : WEquiv x y -> WEquiv y x := by
  intro h; induction h with
  | ind a f' f₀ f₁ _h ih => exact WEquiv.ind _ _ _ _ ih
  | abs a₀ f'₀ f₀ a₁ f'₁ f₁ h => exact WEquiv.abs _ _ _ _ _ _ h.symm
  | trans x y z _e₁ _e₂ ih₁ ih₂ => exact MvQPF.WEquiv.trans _ _ _ ih₂ ih₁

/--
Definition of `wrepr` / `wrepr` 的定义

English:
definition wrepr
  signature: {α : TypeVec n}
  body: recF (q.P.wMk' ∘ repr)

中文:
定义 wrepr
  签名: {α : TypeVec n}
  定义体: recF (q.P.wMk' ∘ repr)

Depends on / 依赖: q.P.wMk
-/
def wrepr {α : TypeVec n} : q.P.W α -> q.P.W α :=
  recF (q.P.wMk' ∘ repr)

/--
theorem `wrepr_wMk` / 定理 `wrepr_wMk`

English:
theorem wrepr_wMk
  statement: {α : TypeVec n} (a : q.P.A) (f' : q.P.drop.B a ⟹ α)
  proof: by
  rw [wrepr]; rw [recF_eq']; rw [q.P.wDest'_wMk]; rfl

中文:
定理 wrepr_wMk
  结论: {α : TypeVec n} (a : q.P.A) (f' : q.P.drop.B a ⟹ α)
  证明: by
  rw [wrepr]; rw [recF_eq']; rw [q.P.wDest'_wMk]; rfl

Depends on / 依赖: _wMk, q.P.wDest, recF_eq
-/
theorem wrepr_wMk {α : TypeVec n} (a : q.P.A) (f' : q.P.drop.B a ⟹ α)
    (f : q.P.last.B a -> q.P.W α) :
    wrepr (q.P.wMk a f' f) =
      q.P.wMk' (repr (abs (appendFun id wrepr <$$> ⟨a, q.P.appendContents f' f⟩))) := by
  rw [wrepr]; rw [recF_eq']; rw [q.P.wDest'_wMk]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wrepr_equiv` / 定理 `wrepr_equiv`

English:
theorem wrepr_equiv
  given: {α : TypeVec n} (x : q.P.W α)
  statement: WEquiv (wrepr x) x
  proof: by
  induction x using q.P.wInd
  case ih a f' f ih =>
    apply WEquiv.trans _ (q.P.wMk' (appendFun id wrepr <$$> ⟨a, q.P.appendContents f' f⟩))
    · apply wEquiv.abs'
      rw [wrepr_wMk]; rw [q.P.wDest'_wMk']; rw [q.P.wDest'_wMk']; rw [abs_repr]
    rw [q.P.map_eq]; rw [MvPFunctor.wMk']; rw [appendFun_comp_splitFun]; rw [id_comp]
    apply WEquiv.ind; exact ih

中文:
定理 wrepr_equiv
  条件: {α : TypeVec n} (x : q.P.W α)
  结论: W等价 (wrepr x) x
  证明: by
  induction x using q.P.wInd
  case ih a f' f ih =>
    apply WEquiv.trans _ (q.P.wMk' (appendFun id wrepr <$$> ⟨a, q.P.appendContents f' f⟩))
    · apply wEquiv.abs'
      rw [wrepr_wMk]; rw [q.P.wDest'_wMk']; rw [q.P.wDest'_wMk']; rw [abs_repr]
    rw [q.P.map_eq]; rw [MvPFunctor.wMk']; rw [appendFun_comp_splitFun]; rw [id_comp]
    apply WEquiv.ind; exact ih

Depends on / 依赖: MvPFunctor, MvPFunctor.wMk, WEquiv, WEquiv.ind, WEquiv.trans, _wMk, abs_repr, appendContents, appendFun, appendFun_comp_splitFun, id_comp, map_eq, q.P.appendContents, q.P.map_eq, q.P.wDest, q.P.wInd, q.P.wMk, wEquiv, wEquiv.abs, wrepr_wMk
-/
theorem wrepr_equiv {α : TypeVec n} (x : q.P.W α) : WEquiv (wrepr x) x := by
  induction x using q.P.wInd
  case ih a f' f ih =>
    apply WEquiv.trans _ (q.P.wMk' (appendFun id wrepr <$$> ⟨a, q.P.appendContents f' f⟩))
    · apply wEquiv.abs'
      rw [wrepr_wMk]; rw [q.P.wDest'_wMk']; rw [q.P.wDest'_wMk']; rw [abs_repr]
    rw [q.P.map_eq]; rw [MvPFunctor.wMk']; rw [appendFun_comp_splitFun]; rw [id_comp]
    apply WEquiv.ind; exact ih

/--
theorem `wEquiv_map` / 定理 `wEquiv_map`

English:
theorem wEquiv_map
  given: {α β : TypeVec n} (g : α ⟹ β) (x y : q.P.W α)
  proof: by
  intro h; induction h with
  | ind a f' f₀ f₁ h ih => rw [q.P.w_map_wMk, q.P.w_map_wMk]; apply WEquiv.ind; exact ih
  | abs a₀ f'₀ f₀ a₁ f'₁ f₁ h =>
    rw [q.P.w_map_wMk]; rw [q.P.w_map_wMk]; apply WEquiv.abs
    change
      abs (q.P.objAppend1 a₀ (g ⊚ f'₀) fun x => q.P.wMap g (f₀ x)) =
        abs (q.P.objAppend1 a₁ (g ⊚ f'₁) fun x => q.P.wMap g (f₁ x))
    rw [← q.P.map_objAppend1]; rw [← q.P.map_objAppend1]; rw [abs_map]; rw [abs_map]; rw [h]
  | trans x y z _ _ ih₁ ih₂ =>
    apply MvQPF.WEquiv.trans
    · apply ih₁
    · apply ih₂

中文:
定理 wEquiv_map
  条件: {α β : TypeVec n} (g : α ⟹ β) (x y : q.P.W α)
  证明: by
  intro h; induction h with
  | ind a f' f₀ f₁ h ih => rw [q.P.w_map_wMk, q.P.w_map_wMk]; apply WEquiv.ind; exact ih
  | abs a₀ f'₀ f₀ a₁ f'₁ f₁ h =>
    rw [q.P.w_map_wMk]; rw [q.P.w_map_wMk]; apply WEquiv.abs
    change
      abs (q.P.objAppend1 a₀ (g ⊚ f'₀) fun x => q.P.wMap g (f₀ x)) =
        abs (q.P.objAppend1 a₁ (g ⊚ f'₁) fun x => q.P.wMap g (f₁ x))
    rw [← q.P.map_objAppend1]; rw [← q.P.map_objAppend1]; rw [abs_map]; rw [abs_map]; rw [h]
  | trans x y z _ _ ih₁ ih₂ =>
    apply MvQPF.WEquiv.trans
    · apply ih₁
    · apply ih₂

Depends on / 依赖: MvQPF.WEquiv.trans, WEquiv, WEquiv.abs, WEquiv.ind, abs_map, map_objAppend1, objAppend1, q.P.map_objAppend1, q.P.objAppend1, q.P.wMap, q.P.w_map_wMk, w_map_wMk
-/
theorem wEquiv_map {α β : TypeVec n} (g : α ⟹ β) (x y : q.P.W α) :
    WEquiv x y -> WEquiv (g <$$> x) (g <$$> y) := by
  intro h; induction h with
  | ind a f' f₀ f₁ h ih => rw [q.P.w_map_wMk, q.P.w_map_wMk]; apply WEquiv.ind; exact ih
  | abs a₀ f'₀ f₀ a₁ f'₁ f₁ h =>
    rw [q.P.w_map_wMk]; rw [q.P.w_map_wMk]; apply WEquiv.abs
    change
      abs (q.P.objAppend1 a₀ (g ⊚ f'₀) fun x => q.P.wMap g (f₀ x)) =
        abs (q.P.objAppend1 a₁ (g ⊚ f'₁) fun x => q.P.wMap g (f₁ x))
    rw [← q.P.map_objAppend1]; rw [← q.P.map_objAppend1]; rw [abs_map]; rw [abs_map]; rw [h]
  | trans x y z _ _ ih₁ ih₂ =>
    apply MvQPF.WEquiv.trans
    · apply ih₁
    · apply ih₂

/-- Define the fixed point as the quotient of trees under the equivalence relation.
-/
@[instance_reducible]
/--
Definition of `wSetoid` / `wSetoid` 的定义

English:
definition wSetoid
  signature: (α : TypeVec n)
  body: ⟨WEquiv, wEquiv.refl, wEquiv.symm _ _, WEquiv.trans _ _ _⟩

中文:
定义 wSetoid
  签名: (α : TypeVec n)
  定义体: ⟨WEquiv, wEquiv.refl, wEquiv.symm _ _, WEquiv.trans _ _ _⟩

Depends on / 依赖: WEquiv, WEquiv.trans, wEquiv, wEquiv.refl, wEquiv.symm
-/
def wSetoid (α : TypeVec n) : Setoid (q.P.W α) :=
  ⟨WEquiv, wEquiv.refl, wEquiv.symm _ _, WEquiv.trans _ _ _⟩

attribute [local instance] wSetoid

/--
Definition of `Fix` / `Fix` 的定义

English:
definition Fix
  signature: {n : Nat} (F : TypeVec (n + 1) -> Type*) [q : MvQPF F] (α : TypeVec n)
  body: Quotient (wSetoid α : Setoid (q.P.W α))

中文:
定义 Fix
  签名: {n : 自然数} (F : TypeVec (n + 1) -> 类型) [q : MvQPF F] (α : TypeVec n)
  定义体: Quotient (wSetoid α : Setoid (q.P.W α))

Depends on / 依赖: Quotient, Setoid, q.P.W, wSetoid
-/
def Fix {n : Nat} (F : TypeVec (n + 1) -> Type*) [q : MvQPF F] (α : TypeVec n) :=
  Quotient (wSetoid α : Setoid (q.P.W α))

/--
Definition of `Fix.map` / `Fix.map` 的定义

English:
definition Fix.map
  signature: {α β : TypeVec n} (g : α ⟹ β)
  body: Quotient.lift (fun x : q.P.W α => ⟦q.P.wMap g x⟧) fun _a _b h => Quot.sound (wEquiv_map _ _ _ h)

中文:
定义 Fix.map
  签名: {α β : TypeVec n} (g : α ⟹ β)
  定义体: Quotient.lift (fun x : q.P.W α => ⟦q.P.wMap g x⟧) fun _a _b h => Quot.sound (wEquiv_map _ _ _ h)

Depends on / 依赖: Quot.sound, Quotient, Quotient.lift, q.P.W, q.P.wMap, wEquiv_map
-/
def Fix.map {α β : TypeVec n} (g : α ⟹ β) : Fix F α -> Fix F β :=
  Quotient.lift (fun x : q.P.W α => ⟦q.P.wMap g x⟧) fun _a _b h => Quot.sound (wEquiv_map _ _ _ h)

/--
Instance `Fix.mvfunctor` / 实例 `Fix.mvfunctor`

English:
instance Fix.mvfunctor
  signature: : MvFunctor (Fix F) where map
  body: Fix.map

中文:
实例 Fix.mvfunctor
  签名: : Mv函子 (Fix F) where map
  定义体: Fix.map

Depends on / 依赖: Fix.map
-/
instance Fix.mvfunctor : MvFunctor (Fix F) where map := Fix.map

variable {α : TypeVec.{u} n}

/--
Definition of `Fix.rec` / `Fix.rec` 的定义

English:
definition Fix.rec
  signature: {β : Type u} (g : F (α ::: β) -> β)
  body: Quot.lift (recF g) (recF_eq_of_wEquiv α g)

中文:
定义 Fix.rec
  签名: {β : 类型u} (g : F (α ::: β) -> β)
  定义体: Quot.lift (recF g) (recF_eq_of_wEquiv α g)

Depends on / 依赖: Quot.lift, recF_eq_of_wEquiv
-/
def Fix.rec {β : Type u} (g : F (α ::: β) -> β) : Fix F α -> β :=
  Quot.lift (recF g) (recF_eq_of_wEquiv α g)

/--
Definition of `fixToW` / `fixToW` 的定义

English:
definition fixToW
  signature: : Fix F α -> q.P.W α
  body: Quotient.lift wrepr (recF_eq_of_wEquiv α fun x => q.P.wMk' (repr x))

中文:
定义 fixToW
  签名: : Fix F α -> q.P.W α
  定义体: Quotient.lift wrepr (recF_eq_of_wEquiv α fun x => q.P.wMk' (repr x))

Depends on / 依赖: Quotient, Quotient.lift, q.P.wMk, recF_eq_of_wEquiv
-/
def fixToW : Fix F α -> q.P.W α :=
  Quotient.lift wrepr (recF_eq_of_wEquiv α fun x => q.P.wMk' (repr x))

/--
Definition of `Fix.mk` / `Fix.mk` 的定义

English:
definition Fix.mk
  signature: (x : F (append1 α (Fix F α)))
  body: Quot.mk _ (q.P.wMk' (appendFun id fixToW <$$> repr x))

中文:
定义 Fix.mk
  签名: (x : F (append1 α (Fix F α)))
  定义体: Quot.mk _ (q.P.wMk' (appendFun id fixToW <$$> repr x))

Depends on / 依赖: Quot.mk, appendFun, fixToW, q.P.wMk
-/
def Fix.mk (x : F (append1 α (Fix F α))) : Fix F α :=
  Quot.mk _ (q.P.wMk' (appendFun id fixToW <$$> repr x))

/--
Definition of `Fix.dest` / `Fix.dest` 的定义

English:
definition Fix.dest
  signature: : Fix F α -> F (append1 α (Fix F α))
  body: Fix.rec (MvFunctor.map (appendFun id Fix.mk))

中文:
定义 Fix.dest
  签名: : Fix F α -> F (append1 α (Fix F α))
  定义体: Fix.rec (MvFunctor.map (appendFun id Fix.mk))

Depends on / 依赖: Fix.mk, Fix.rec, MvFunctor, MvFunctor.map, appendFun
-/
def Fix.dest : Fix F α -> F (append1 α (Fix F α)) :=
  Fix.rec (MvFunctor.map (appendFun id Fix.mk))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Fix.rec_eq` / 定理 `Fix.rec_eq`

English:
theorem Fix.rec_eq
  given: {β : Type u} (g : F (append1 α β) -> β) (x : F (append1 α (Fix F α)))
  proof: by
  have : recF g ∘ fixToW = Fix.rec g := by
    apply funext
    apply Quotient.ind
    intro x
    apply recF_eq_of_wEquiv
    apply wrepr_equiv
  conv =>
    lhs
    rw [Fix.rec]; rw [Fix.mk]
    dsimp
  rcases h : repr x with ⟨a, f⟩
  rw [MvPFunctor.map_eq]; rw [recF_eq']; rw [← MvPFunctor.map_eq]; rw [MvPFunctor.wDest'_wMk']
  rw [← MvPFunctor.comp_map]; rw [abs_map]; rw [← h]; rw [abs_repr]; rw [← appendFun_comp]; rw [id_comp]; rw [this]

中文:
定理 Fix.rec_eq
  条件: {β : 类型u} (g : F (append1 α β) -> β) (x : F (append1 α (Fix F α)))
  证明: by
  have : recF g ∘ fixToW = Fix.rec g := by
    apply funext
    apply Quotient.ind
    intro x
    apply recF_eq_of_wEquiv
    apply wrepr_equiv
  conv =>
    lhs
    rw [Fix.rec]; rw [Fix.mk]
    dsimp
  rcases h : repr x with ⟨a, f⟩
  rw [MvPFunctor.map_eq]; rw [recF_eq']; rw [← MvPFunctor.map_eq]; rw [MvPFunctor.wDest'_wMk']
  rw [← MvPFunctor.comp_map]; rw [abs_map]; rw [← h]; rw [abs_repr]; rw [← appendFun_comp]; rw [id_comp]; rw [this]

Depends on / 依赖: Fix.mk, Fix.rec, MvPFunctor, MvPFunctor.comp_map, MvPFunctor.map_eq, MvPFunctor.wDest, Quotient, Quotient.ind, _wMk, abs_map, abs_repr, appendFun_comp, comp_map, fixToW, id_comp, map_eq, recF_eq, recF_eq_of_wEquiv, wrepr_equiv
-/
theorem Fix.rec_eq {β : Type u} (g : F (append1 α β) -> β) (x : F (append1 α (Fix F α))) :
    Fix.rec g (Fix.mk x) = g (appendFun id (Fix.rec g) <$$> x) := by
  have : recF g ∘ fixToW = Fix.rec g := by
    apply funext
    apply Quotient.ind
    intro x
    apply recF_eq_of_wEquiv
    apply wrepr_equiv
  conv =>
    lhs
    rw [Fix.rec]; rw [Fix.mk]
    dsimp
  rcases h : repr x with ⟨a, f⟩
  rw [MvPFunctor.map_eq]; rw [recF_eq']; rw [← MvPFunctor.map_eq]; rw [MvPFunctor.wDest'_wMk']
  rw [← MvPFunctor.comp_map]; rw [abs_map]; rw [← h]; rw [abs_repr]; rw [← appendFun_comp]; rw [id_comp]; rw [this]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Fix.ind_aux` / 定理 `Fix.ind_aux`

English:
theorem Fix.ind_aux
  given: (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a -> q.P.W α)
  proof: by
  have : Fix.mk (abs ⟨a, q.P.appendContents f' fun x => ⟦f x⟧⟩) = ⟦wrepr (q.P.wMk a f' f)⟧ := by
    apply Quot.sound; apply wEquiv.abs'
    rw [MvPFunctor.wDest'_wMk']; rw [abs_map]; rw [abs_repr]; rw [← abs_map]; rw [MvPFunctor.map_eq]
    conv =>
      rhs
      rw [wrepr_wMk]; rw [q.P.wDest'_wMk']; rw [abs_repr]; rw [MvPFunctor.map_eq]
    congr 2; rw [MvPFunctor.appendContents, MvPFunctor.appendContents]
    rw [appendFun]; rw [appendFun]; rw [← splitFun_comp]; rw [← splitFun_comp]
    rfl
  rw [this]
  apply Quot.sound
  apply wrepr_equiv

中文:
定理 Fix.ind_aux
  条件: (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a -> q.P.W α)
  证明: by
  have : Fix.mk (abs ⟨a, q.P.appendContents f' fun x => ⟦f x⟧⟩) = ⟦wrepr (q.P.wMk a f' f)⟧ := by
    apply Quot.sound; apply wEquiv.abs'
    rw [MvPFunctor.wDest'_wMk']; rw [abs_map]; rw [abs_repr]; rw [← abs_map]; rw [MvPFunctor.map_eq]
    conv =>
      rhs
      rw [wrepr_wMk]; rw [q.P.wDest'_wMk']; rw [abs_repr]; rw [MvPFunctor.map_eq]
    congr 2; rw [MvPFunctor.appendContents, MvPFunctor.appendContents]
    rw [appendFun]; rw [appendFun]; rw [← splitFun_comp]; rw [← splitFun_comp]
    rfl
  rw [this]
  apply Quot.sound
  apply wrepr_equiv

Depends on / 依赖: Fix.mk, MvPFunctor, MvPFunctor.appendContents, MvPFunctor.map_eq, MvPFunctor.wDest, Quot.sound, _wMk, abs_map, abs_repr, appendContents, appendFun, map_eq, q.P.appendContents, q.P.wDest, q.P.wMk, splitFun_comp, wEquiv, wEquiv.abs, wrepr_wMk
-/
theorem Fix.ind_aux (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a -> q.P.W α) :
    Fix.mk (abs ⟨a, q.P.appendContents f' fun x => ⟦f x⟧⟩) = ⟦q.P.wMk a f' f⟧ := by
  have : Fix.mk (abs ⟨a, q.P.appendContents f' fun x => ⟦f x⟧⟩) = ⟦wrepr (q.P.wMk a f' f)⟧ := by
    apply Quot.sound; apply wEquiv.abs'
    rw [MvPFunctor.wDest'_wMk']; rw [abs_map]; rw [abs_repr]; rw [← abs_map]; rw [MvPFunctor.map_eq]
    conv =>
      rhs
      rw [wrepr_wMk]; rw [q.P.wDest'_wMk']; rw [abs_repr]; rw [MvPFunctor.map_eq]
    congr 2; rw [MvPFunctor.appendContents, MvPFunctor.appendContents]
    rw [appendFun]; rw [appendFun]; rw [← splitFun_comp]; rw [← splitFun_comp]
    rfl
  rw [this]
  apply Quot.sound
  apply wrepr_equiv

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Fix.ind_rec` / 定理 `Fix.ind_rec`

English:
theorem Fix.ind_rec
  statement: {β : Type u} (g₁ g₂ : Fix F α -> β)
  proof: by
  apply Quot.ind
  intro x
  induction x using q.P.wInd
  case ih a f' f ih =>
    change g₁ ⟦q.P.wMk a f' f⟧ = g₂ ⟦q.P.wMk a f' f⟧
    rw [← Fix.ind_aux a f' f]
    apply h
    rw [← abs_map]; rw [← abs_map]; rw [MvPFunctor.map_eq]; rw [MvPFunctor.map_eq]
    congr 2
    rw [MvPFunctor.appendContents]; rw [appendFun]; rw [appendFun]; rw [← splitFun_comp]; rw [← splitFun_comp]
    have : (g₁ ∘ fun x => ⟦f x⟧) = g₂ ∘ fun x => ⟦f x⟧ := by
      ext x
      exact ih x
    rw [this]

中文:
定理 Fix.ind_rec
  结论: {β : 类型u} (g₁ g₂ : Fix F α -> β)
  证明: by
  apply Quot.ind
  intro x
  induction x using q.P.wInd
  case ih a f' f ih =>
    change g₁ ⟦q.P.wMk a f' f⟧ = g₂ ⟦q.P.wMk a f' f⟧
    rw [← Fix.ind_aux a f' f]
    apply h
    rw [← abs_map]; rw [← abs_map]; rw [MvPFunctor.map_eq]; rw [MvPFunctor.map_eq]
    congr 2
    rw [MvPFunctor.appendContents]; rw [appendFun]; rw [appendFun]; rw [← splitFun_comp]; rw [← splitFun_comp]
    have : (g₁ ∘ fun x => ⟦f x⟧) = g₂ ∘ fun x => ⟦f x⟧ := by
      ext x
      exact ih x
    rw [this]

Depends on / 依赖: Fix.ind_aux, MvPFunctor, MvPFunctor.appendContents, MvPFunctor.map_eq, Quot.ind, abs_map, appendContents, appendFun, ind_aux, map_eq, q.P.wInd, q.P.wMk, splitFun_comp
-/
theorem Fix.ind_rec {β : Type u} (g₁ g₂ : Fix F α -> β)
    (h :
      forall x : F (append1 α (Fix F α)),
appendFun id g₁ < > x = appendFun id g₂ < > x -> g₁ (Fix.mk x) = g₂ (Fix.mk x)) :
    forall x, g₁ x = g₂ x := by
  apply Quot.ind
  intro x
  induction x using q.P.wInd
  case ih a f' f ih =>
    change g₁ ⟦q.P.wMk a f' f⟧ = g₂ ⟦q.P.wMk a f' f⟧
    rw [← Fix.ind_aux a f' f]
    apply h
    rw [← abs_map]; rw [← abs_map]; rw [MvPFunctor.map_eq]; rw [MvPFunctor.map_eq]
    congr 2
    rw [MvPFunctor.appendContents]; rw [appendFun]; rw [appendFun]; rw [← splitFun_comp]; rw [← splitFun_comp]
    have : (g₁ ∘ fun x => ⟦f x⟧) = g₂ ∘ fun x => ⟦f x⟧ := by
      ext x
      exact ih x
    rw [this]

/--
theorem `Fix.rec_unique` / 定理 `Fix.rec_unique`

English:
theorem Fix.rec_unique
  statement: {β : Type u} (g : F (append1 α β) -> β) (h : Fix F α -> β)
  proof: by
  ext x
  apply Fix.ind_rec
  intro x hyp'
  rw [hyp]; rw [← hyp']; rw [Fix.rec_eq]

中文:
定理 Fix.rec_unique
  结论: {β : 类型u} (g : F (append1 α β) -> β) (h : Fix F α -> β)
  证明: by
  ext x
  apply Fix.ind_rec
  intro x hyp'
  rw [hyp]; rw [← hyp']; rw [Fix.rec_eq]

Depends on / 依赖: Fix.ind_rec, Fix.rec_eq, ind_rec, rec_eq
-/
theorem Fix.rec_unique {β : Type u} (g : F (append1 α β) -> β) (h : Fix F α -> β)
    (hyp : forall x, h (Fix.mk x) = g (appendFun id h <$$> x)) : Fix.rec g = h := by
  ext x
  apply Fix.ind_rec
  intro x hyp'
  rw [hyp]; rw [← hyp']; rw [Fix.rec_eq]

/--
theorem `Fix.mk_dest` / 定理 `Fix.mk_dest`

English:
theorem Fix.mk_dest
  given: (x : Fix F α)
  statement: Fix.mk (Fix.dest x) = x
  proof: by
  change (Fix.mk ∘ Fix.dest) x = x
  apply Fix.ind_rec
  intro x; dsimp
  rw [Fix.dest]; rw [Fix.rec_eq]; rw [← comp_map]; rw [← appendFun_comp]; rw [id_comp]
  intro h; rw [h]
  change Fix.mk (appendFun id id <$$> x) = Fix.mk x
  rw [appendFun_id_id]; rw [MvFunctor.id_map]

中文:
定理 Fix.mk_dest
  条件: (x : Fix F α)
  结论: Fix.mk (Fix.dest x) = x
  证明: by
  change (Fix.mk ∘ Fix.dest) x = x
  apply Fix.ind_rec
  intro x; dsimp
  rw [Fix.dest]; rw [Fix.rec_eq]; rw [← comp_map]; rw [← appendFun_comp]; rw [id_comp]
  intro h; rw [h]
  change Fix.mk (appendFun id id <$$> x) = Fix.mk x
  rw [appendFun_id_id]; rw [MvFunctor.id_map]

Depends on / 依赖: Fix.dest, Fix.ind_rec, Fix.mk, Fix.rec_eq, MvFunctor, MvFunctor.id_map, appendFun, appendFun_comp, appendFun_id_id, comp_map, id_comp, id_map, ind_rec, rec_eq
-/
theorem Fix.mk_dest (x : Fix F α) : Fix.mk (Fix.dest x) = x := by
  change (Fix.mk ∘ Fix.dest) x = x
  apply Fix.ind_rec
  intro x; dsimp
  rw [Fix.dest]; rw [Fix.rec_eq]; rw [← comp_map]; rw [← appendFun_comp]; rw [id_comp]
  intro h; rw [h]
  change Fix.mk (appendFun id id <$$> x) = Fix.mk x
  rw [appendFun_id_id]; rw [MvFunctor.id_map]

/--
theorem `Fix.dest_mk` / 定理 `Fix.dest_mk`

English:
theorem Fix.dest_mk
  given: (x : F (append1 α (Fix F α)))
  statement: Fix.dest (Fix.mk x) = x
  proof: by
  unfold Fix.dest
  rw [Fix.rec_eq]; rw [← Fix.dest]; rw [← comp_map]
  conv =>
    rhs
    rw [← MvFunctor.id_map x]
  rw [← appendFun_comp]; rw [id_comp]
  have : Fix.mk ∘ Fix.dest (F := F) (α := α) = _root_.id := by
    ext (x : Fix F α)
    apply Fix.mk_dest
  rw [this]; rw [appendFun_id_id]

中文:
定理 Fix.dest_mk
  条件: (x : F (append1 α (Fix F α)))
  结论: Fix.dest (Fix.mk x) = x
  证明: by
  unfold Fix.dest
  rw [Fix.rec_eq]; rw [← Fix.dest]; rw [← comp_map]
  conv =>
    rhs
    rw [← MvFunctor.id_map x]
  rw [← appendFun_comp]; rw [id_comp]
  have : Fix.mk ∘ Fix.dest (F := F) (α := α) = _root_.id := by
    ext (x : Fix F α)
    apply Fix.mk_dest
  rw [this]; rw [appendFun_id_id]

Depends on / 依赖: Fix.dest, Fix.mk, Fix.mk_dest, Fix.rec_eq, MvFunctor, MvFunctor.id_map, _root_, _root_.id, appendFun_comp, appendFun_id_id, comp_map, id_comp, id_map, mk_dest, rec_eq
-/
theorem Fix.dest_mk (x : F (append1 α (Fix F α))) : Fix.dest (Fix.mk x) = x := by
  unfold Fix.dest
  rw [Fix.rec_eq]; rw [← Fix.dest]; rw [← comp_map]
  conv =>
    rhs
    rw [← MvFunctor.id_map x]
  rw [← appendFun_comp]; rw [id_comp]
  have : Fix.mk ∘ Fix.dest (F := F) (α := α) = _root_.id := by
    ext (x : Fix F α)
    apply Fix.mk_dest
  rw [this]; rw [appendFun_id_id]

/--
theorem `Fix.ind` / 定理 `Fix.ind`

English:
theorem Fix.ind
  statement: {α : TypeVec n} (p : Fix F α -> Prop)
  proof: by
  apply Quot.ind
  intro x
  induction x using q.P.wInd
  case ih a f' f ih =>
    change p ⟦q.P.wMk a f' f⟧
    rw [← Fix.ind_aux a f' f]
    apply h
    rw [MvQPF.liftP_iff]
    refine ⟨_, _, rfl, ?_⟩
    intro i j
    cases i
    · apply ih
    · trivial

中文:
定理 Fix.ind
  结论: {α : TypeVec n} (p : Fix F α -> 命题)
  证明: by
  apply Quot.ind
  intro x
  induction x using q.P.wInd
  case ih a f' f ih =>
    change p ⟦q.P.wMk a f' f⟧
    rw [← Fix.ind_aux a f' f]
    apply h
    rw [MvQPF.liftP_iff]
    refine ⟨_, _, rfl, ?_⟩
    intro i j
    cases i
    · apply ih
    · trivial

Depends on / 依赖: Fix.ind_aux, MvQPF.liftP_iff, Quot.ind, ind_aux, liftP_iff, q.P.wInd, q.P.wMk
-/
theorem Fix.ind {α : TypeVec n} (p : Fix F α -> Prop)
    (h : forall x : F (α.append1 (Fix F α)), LiftP (PredLast α p) x -> p (Fix.mk x)) : forall x, p x := by
  apply Quot.ind
  intro x
  induction x using q.P.wInd
  case ih a f' f ih =>
    change p ⟦q.P.wMk a f' f⟧
    rw [← Fix.ind_aux a f' f]
    apply h
    rw [MvQPF.liftP_iff]
    refine ⟨_, _, rfl, ?_⟩
    intro i j
    cases i
    · apply ih
    · trivial

/--
Instance `mvqpfFix` / 实例 `mvqpfFix`

English:
instance mvqpfFix
  signature: : MvQPF (Fix F) where
  body: q.P.wp
  abs α := Quot.mk WEquiv α
  repr α := fixToW α
  abs_repr := by
    intro α
    apply Quot.ind
    intro a
    apply Quot.sound
    apply wrepr_equiv
  abs_map := by
    intro α β g x
    conv =>
      rhs
      dsimp [MvFunctor.map]
    rfl

中文:
实例 mvqpfFix
  签名: : MvQPF (Fix F) where
  定义体: q.P.wp
  abs α := Quot.mk WEquiv α
  repr α := fixToW α
  abs_repr := by
    intro α
    apply Quot.ind
    intro a
    apply Quot.sound
    apply wrepr_equiv
  abs_map := by
    intro α β g x
    conv =>
      rhs
      dsimp [MvFunctor.map]
    rfl

Depends on / 依赖: q.P.wp
-/
instance mvqpfFix : MvQPF (Fix F) where
  P := q.P.wp
  abs α := Quot.mk WEquiv α
  repr α := fixToW α
  abs_repr := by
    intro α
    apply Quot.ind
    intro a
    apply Quot.sound
    apply wrepr_equiv
  abs_map := by
    intro α β g x
    conv =>
      rhs
      dsimp [MvFunctor.map]
    rfl

/--
Definition of `Fix.drec` / `Fix.drec` 的定义

English:
definition Fix.drec
  signature: {β : Fix F α -> Type u}
  body: let y := @Fix.rec _ F _ α (Sigma β) (fun i => ⟨_, g i⟩) x
  have : x = y.1 := by
    symm
    dsimp [y]
    apply Fix.ind_rec _ id _ x
    intro x' ih
    rw [Fix.rec_eq]
    dsimp
    simp only [appendFun_id_id, MvFunctor.id_map] at ih
    congr
    conv =>
      rhs
      rw [← ih]
    rw [MvFunctor.map_map]; rw [← appendFun_comp]; rw [id_comp]
    simp only [Function.comp_def]
  cast (by rw [this]) y.2

中文:
定义 Fix.drec
  签名: {β : Fix F α -> 类型u}
  定义体: let y := @Fix.rec _ F _ α (Sigma β) (fun i => ⟨_, g i⟩) x
  have : x = y.1 := by
    symm
    dsimp [y]
    apply Fix.ind_rec _ id _ x
    intro x' ih
    rw [Fix.rec_eq]
    dsimp
    simp only [appendFun_id_id, MvFunctor.id_map] at ih
    congr
    conv =>
      rhs
      rw [← ih]
    rw [MvFunctor.map_map]; rw [← appendFun_comp]; rw [id_comp]
    simp only [Function.comp_def]
  cast (by rw [this]) y.2

Depends on / 依赖: Fix.ind_rec, Fix.rec, Fix.rec_eq, Function, Function.comp_def, MvFunctor, MvFunctor.id_map, MvFunctor.map_map, appendFun_comp, appendFun_id_id, comp_def, id_comp, id_map, ind_rec, map_map, rec_eq
-/
def Fix.drec {β : Fix F α -> Type u}
    (g : forall x : F (α ::: Sigma β), β (Fix.mk <| (id ::: Sigma.fst) <$$> x)) (x : Fix F α) : β x :=
  let y := @Fix.rec _ F _ α (Sigma β) (fun i => ⟨_, g i⟩) x
  have : x = y.1 := by
    symm
    dsimp [y]
    apply Fix.ind_rec _ id _ x
    intro x' ih
    rw [Fix.rec_eq]
    dsimp
    simp only [appendFun_id_id, MvFunctor.id_map] at ih
    congr
    conv =>
      rhs
      rw [← ih]
    rw [MvFunctor.map_map]; rw [← appendFun_comp]; rw [id_comp]
    simp only [Function.comp_def]
  cast (by rw [this]) y.2

end MvQPF
