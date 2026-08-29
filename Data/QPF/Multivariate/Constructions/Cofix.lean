/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Control.Functor.Multivariate
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Multivariate.M
public import Mathlib.Data.QPF.Multivariate.Basic

/-!
# The final co-algebra of a multivariate qpf is again a qpf.

For a `(n+1)`-ary QPF `F (α₀,..,αₙ)`, we take the least fixed point of `F` with
regards to its last argument `αₙ`. The result is an `n`-ary functor: `Fix F (α₀,..,αₙ₋₁)`.
Making `Fix F` into a functor allows us to take the fixed point, compose with other functors
and take a fixed point again.

## Main definitions

* `Cofix.mk` - constructor
* `Cofix.dest` - destructor
* `Cofix.corec` - corecursor: useful for formulating infinite, productive computations
* `Cofix.bisim` - bisimulation: proof technique to show the equality of possibly infinite values
                    of `Cofix F α`

## Implementation notes

For `F` a QPF, we define `Cofix F α` in terms of the M-type of the polynomial functor `P` of `F`.
We define the relation `Mcongr` and take its quotient as the definition of `Cofix F α`.

`Mcongr` is taken as the weakest bisimulation on M-type. See
[avigad-carneiro-hudon2019] for more details.

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

@[expose] public section


universe u

open MvFunctor

namespace MvQPF

open TypeVec MvPFunctor

open MvFunctor (LiftP LiftR)

variable {n : Nat} {F : TypeVec.{u} (n + 1) -> Type u} [q : MvQPF F]

/--
Definition of `corecF` / `corecF` 的定义

English:
definition corecF
  signature: {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 β))
  body: M.corec _ fun x => repr (g x)

中文:
定义 corecF
  签名: {α : TypeVec n} {β : 类型u} (g : β -> F (α.append1 β))
  定义体: M.corec _ fun x => repr (g x)

Depends on / 依赖: M.corec
-/
def corecF {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 β)) : β -> q.P.M α :=
  M.corec _ fun x => repr (g x)

/--
theorem `corecF_eq` / 定理 `corecF_eq`

English:
theorem corecF_eq
  given: {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 β)) (x : β)
  proof: by
  rw [corecF]; rw [M.dest_corec]

中文:
定理 corecF_eq
  条件: {α : TypeVec n} {β : 类型u} (g : β -> F (α.append1 β)) (x : β)
  证明: by
  rw [corecF]; rw [M.dest_corec]

Depends on / 依赖: M.dest_corec, corecF, dest_corec
-/
theorem corecF_eq {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 β)) (x : β) :
M.dest q.P (corecF g x) = appendFun id (corecF g) < > repr (g x) := by
  rw [corecF]; rw [M.dest_corec]

/--
Definition of `IsPrecongr` / `IsPrecongr` 的定义

English:
definition IsPrecongr
  signature: {α : TypeVec n} (r : q.P.M α -> q.P.M α -> Prop)
  body: forall ⦃x y⦄,
    r x y ->
      abs (appendFun id (Quot.mk r) <$$> M.dest q.P x) =
        abs (appendFun id (Quot.mk r) <$$> M.dest q.P y)

中文:
定义 IsPrecongr
  签名: {α : TypeVec n} (r : q.P.M α -> q.P.M α -> 命题)
  定义体: forall ⦃x y⦄,
    r x y ->
      abs (appendFun id (Quot.mk r) <$$> M.dest q.P x) =
        abs (appendFun id (Quot.mk r) <$$> M.dest q.P y)

Depends on / 依赖: M.dest, Quot.mk, appendFun
-/
def IsPrecongr {α : TypeVec n} (r : q.P.M α -> q.P.M α -> Prop) : Prop :=
  forall ⦃x y⦄,
    r x y ->
      abs (appendFun id (Quot.mk r) <$$> M.dest q.P x) =
        abs (appendFun id (Quot.mk r) <$$> M.dest q.P y)

/--
Definition of `Mcongr` / `Mcongr` 的定义

English:
definition Mcongr
  signature: {α : TypeVec n} (x y : q.P.M α)
  body: exists r, IsPrecongr r ∧ r x y

中文:
定义 Mcongr
  签名: {α : TypeVec n} (x y : q.P.M α)
  定义体: exists r, IsPrecongr r ∧ r x y

Depends on / 依赖: IsPrecongr
-/
def Mcongr {α : TypeVec n} (x y : q.P.M α) : Prop :=
  exists r, IsPrecongr r ∧ r x y

/--
Definition of `Cofix` / `Cofix` 的定义

English:
definition Cofix
  signature: (F : TypeVec (n + 1) -> Type u) [MvQPF F] (α : TypeVec n)
  body: Quot (@Mcongr _ F _ α)

中文:
定义 Cofix
  签名: (F : TypeVec (n + 1) -> 类型u) [MvQPF F] (α : TypeVec n)
  定义体: Quot (@Mcongr _ F _ α)

Depends on / 依赖: Mcongr
-/
def Cofix (F : TypeVec (n + 1) -> Type u) [MvQPF F] (α : TypeVec n) :=
  Quot (@Mcongr _ F _ α)

instance {α : TypeVec n} [Inhabited q.P.A] [forall i : Fin2 n, Inhabited (α i)] :
    Inhabited (Cofix F α) :=
  ⟨Quot.mk _ default⟩

/--
Definition of `mRepr` / `mRepr` 的定义

English:
definition mRepr
  signature: {α : TypeVec n}
  body: corecF (abs ∘ M.dest q.P)

中文:
定义 mRepr
  签名: {α : TypeVec n}
  定义体: corecF (abs ∘ M.dest q.P)

Depends on / 依赖: M.dest, corecF
-/
def mRepr {α : TypeVec n} : q.P.M α -> q.P.M α :=
  corecF (abs ∘ M.dest q.P)

/--
Definition of `Cofix.map` / `Cofix.map` 的定义

English:
definition Cofix.map
  signature: {α β : TypeVec n} (g : α ⟹ β)
  body: Quot.lift (fun x : q.P.M α => Quot.mk Mcongr (g <$$> x))
    (by
      rintro aa₁ aa₂ ⟨r, pr, ra₁a₂⟩; apply Quot.sound
let r' b₁ b₂ := exists a₁ a₂ : q.P.M α, r a₁ a₂ ∧ b₁ = g < > a₁ ∧ b₂ = g < > a₂
      use r'; constructor
      · show IsPrecongr r'
        rintro b₁ b₂ ⟨a₁, a₂, ra₁a₂, b₁eq, b₂eq⟩

中文:
定义 Cofix.map
  签名: {α β : TypeVec n} (g : α ⟹ β)
  定义体: Quot.lift (fun x : q.P.M α => Quot.mk Mcongr (g <$$> x))
    (by
      rintro aa₁ aa₂ ⟨r, pr, ra₁a₂⟩; apply Quot.sound
let r' b₁ b₂ := exists a₁ a₂ : q.P.M α, r a₁ a₂ ∧ b₁ = g < > a₁ ∧ b₂ = g < > a₂
      use r'; constructor
      · show IsPrecongr r'
        rintro b₁ b₂ ⟨a₁, a₂, ra₁a₂, b₁eq, b₂eq⟩

Depends on / 依赖: IsPrecongr, Mcongr, Quot.lift, Quot.mk, Quot.sound, q.P.M
-/
def Cofix.map {α β : TypeVec n} (g : α ⟹ β) : Cofix F α -> Cofix F β :=
  Quot.lift (fun x : q.P.M α => Quot.mk Mcongr (g <$$> x))
    (by
      rintro aa₁ aa₂ ⟨r, pr, ra₁a₂⟩; apply Quot.sound
let r' b₁ b₂ := exists a₁ a₂ : q.P.M α, r a₁ a₂ ∧ b₁ = g < > a₁ ∧ b₂ = g < > a₂
      use r'; constructor
      · show IsPrecongr r'
        rintro b₁ b₂ ⟨a₁, a₂, ra₁a₂, b₁eq, b₂eq⟩
        let u : Quot r -> Quot r' :=
          Quot.lift (fun x : q.P.M α => Quot.mk r' (g <$$> x))
            (by
              intro a₁ a₂ ra₁a₂
              apply Quot.sound
              exact ⟨a₁, a₂, ra₁a₂, rfl, rfl⟩)
        have hu : (Quot.mk r' ∘ fun x : q.P.M α => g <$$> x) = u ∘ Quot.mk r := by
          ext x
          rfl
        rw [b₁eq]; rw [b₂eq]; rw [M.dest_map]; rw [M.dest_map]; rw [← q.P.comp_map]; rw [← q.P.comp_map]
        rw [← appendFun_comp]; rw [id_comp]; rw [hu]; rw [← comp_id g]; rw [appendFun_comp]
        rw [q.P.comp_map]; rw [q.P.comp_map]; rw [abs_map]; rw [pr ra₁a₂]; rw [← abs_map]
      show r' (g <$$> aa₁) (g <$$> aa₂); exact ⟨aa₁, aa₂, ra₁a₂, rfl, rfl⟩)

/--
Instance `Cofix.mvfunctor` / 实例 `Cofix.mvfunctor`

English:
instance Cofix.mvfunctor
  signature: : MvFunctor (Cofix F) where map
  body: @Cofix.map _ _ _

中文:
实例 Cofix.mvfunctor
  签名: : MvFunctor (Cofix F) where map
  定义体: @Cofix.map _ _ _

Depends on / 依赖: Cofix.map
-/
instance Cofix.mvfunctor : MvFunctor (Cofix F) where map := @Cofix.map _ _ _

/--
Definition of `Cofix.corec` / `Cofix.corec` 的定义

English:
definition Cofix.corec
  signature: {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 β))
  body: fun x =>
  Quot.mk _ (corecF g x)

中文:
定义 Cofix.corec
  签名: {α : TypeVec n} {β : 类型u} (g : β -> F (α.append1 β))
  定义体: fun x =>
  Quot.mk _ (corecF g x)
-/
def Cofix.corec {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 β)) : β -> Cofix F α := fun x =>
  Quot.mk _ (corecF g x)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Cofix.dest` / `Cofix.dest` 的定义

English:
definition Cofix.dest
  signature: {α : TypeVec n}
  body: Quot.lift (fun x => appendFun id (Quot.mk Mcongr) <$$> abs (M.dest q.P x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      have : forall x y, r x y -> Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      conv =>
        lhs
        rw [appendFun_com

中文:
定义 Cofix.dest
  签名: {α : TypeVec n}
  定义体: Quot.lift (fun x => appendFun id (Quot.mk Mcongr) <$$> abs (M.dest q.P x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      have : forall x y, r x y -> Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      conv =>
        lhs
        rw [appendFun_com

Depends on / 依赖: M.dest, Mcongr, Quot.factor_mk_eq, Quot.lift, Quot.mk, abs_map, appendFun, appendFun_comp_id, comp_map, factor_mk_eq
-/
def Cofix.dest {α : TypeVec n} : Cofix F α -> F (α.append1 (Cofix F α)) :=
  Quot.lift (fun x => appendFun id (Quot.mk Mcongr) <$$> abs (M.dest q.P x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      have : forall x y, r x y -> Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      conv =>
        lhs
        rw [appendFun_comp_id]; rw [comp_map]; rw [← abs_map]; rw [pr rxy]; rw [abs_map]; rw [← comp_map]; rw [← appendFun_comp_id])

/--
Definition of `Cofix.abs` / `Cofix.abs` 的定义

English:
definition Cofix.abs
  signature: {α}
  body: Quot.mk _

中文:
定义 Cofix.abs
  签名: {α}
  定义体: Quot.mk _

Depends on / 依赖: Quot.mk
-/
def Cofix.abs {α} : q.P.M α -> Cofix F α :=
  Quot.mk _

/--
Definition of `Cofix.repr` / `Cofix.repr` 的定义

English:
definition Cofix.repr
  signature: {α}
  body: M.corec _ q.repr ∘ Cofix.dest

中文:
定义 Cofix.repr
  签名: {α}
  定义体: M.corec _ q.repr ∘ Cofix.dest

Depends on / 依赖: Cofix.dest, M.corec, q.repr
-/
def Cofix.repr {α} : Cofix F α -> q.P.M α :=
M.corec _ q.repr ∘ Cofix.dest

/--
Definition of `Cofix.corec'₁` / `Cofix.corec'₁` 的定义

English:
definition Cofix.corec'₁
  signature: {α : TypeVec n} {β : Type u} (g : forall {X}, (β -> X) -> F (α.append1 X)) (x : β)
  body: Cofix.corec (fun _ => g id) x

中文:
定义 Cofix.corec'₁
  签名: {α : TypeVec n} {β : 类型u} (g : 对任意 {X}, (β -> X) -> F (α.append1 X)) (x : β)
  定义体: Cofix.corec (fun _ => g id) x

Depends on / 依赖: Cofix.corec
-/
def Cofix.corec'₁ {α : TypeVec n} {β : Type u} (g : forall {X}, (β -> X) -> F (α.append1 X)) (x : β) :
    Cofix F α :=
  Cofix.corec (fun _ => g id) x

/--
Definition of `Cofix.corec'` / `Cofix.corec'` 的定义

English:
definition Cofix.corec'
  signature: {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 (Cofix F α oplus β))) (x : β)
  body: let f : (α ::: Cofix F α) ⟹ (α ::: (Cofix F α oplus β)) := id ::: Sum.inl
  Cofix.corec (Sum.elim (MvFunctor.map f ∘ Cofix.dest) g) (Sum.inr x : Cofix F α oplus β)

中文:
定义 Cofix.corec'
  签名: {α : TypeVec n} {β : 类型u} (g : β -> F (α.append1 (Cofix F α oplus β))) (x : β)
  定义体: let f : (α ::: Cofix F α) ⟹ (α ::: (Cofix F α oplus β)) := id ::: Sum.inl
  Cofix.corec (Sum.elim (MvFunctor.map f ∘ Cofix.dest) g) (Sum.inr x : Cofix F α oplus β)
-/
def Cofix.corec' {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 (Cofix F α oplus β))) (x : β) :
    Cofix F α :=
  let f : (α ::: Cofix F α) ⟹ (α ::: (Cofix F α oplus β)) := id ::: Sum.inl
  Cofix.corec (Sum.elim (MvFunctor.map f ∘ Cofix.dest) g) (Sum.inr x : Cofix F α oplus β)

/--
Definition of `Cofix.corec₁` / `Cofix.corec₁` 的定义

English:
definition Cofix.corec₁
  signature: {α : TypeVec n} {β : Type u}
  body: Cofix.corec' (fun x => g Sum.inl Sum.inr x) x

中文:
定义 Cofix.corec₁
  签名: {α : TypeVec n} {β : 类型u}
  定义体: Cofix.corec' (fun x => g Sum.inl Sum.inr x) x

Depends on / 依赖: Cofix.corec, Sum.inl, Sum.inr
-/
def Cofix.corec₁ {α : TypeVec n} {β : Type u}
    (g : forall {X}, (Cofix F α -> X) -> (β -> X) -> β -> F (α ::: X)) (x : β) : Cofix F α :=
  Cofix.corec' (fun x => g Sum.inl Sum.inr x) x

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Cofix.dest_corec` / 定理 `Cofix.dest_corec`

English:
theorem Cofix.dest_corec
  given: {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 β)) (x : β)
  proof: by
  conv =>
    lhs
    rw [Cofix.dest]; rw [Cofix.corec]
  dsimp
  rw [corecF_eq]; rw [abs_map]; rw [abs_repr]; rw [← comp_map]; rw [← appendFun_comp]; rfl

中文:
定理 Cofix.dest_corec
  条件: {α : TypeVec n} {β : 类型u} (g : β -> F (α.append1 β)) (x : β)
  证明: by
  conv =>
    lhs
    rw [Cofix.dest]; rw [Cofix.corec]
  dsimp
  rw [corecF_eq]; rw [abs_map]; rw [abs_repr]; rw [← comp_map]; rw [← appendFun_comp]; rfl

Depends on / 依赖: Cofix.corec, Cofix.dest, abs_map, abs_repr, appendFun_comp, comp_map, corecF_eq
-/
theorem Cofix.dest_corec {α : TypeVec n} {β : Type u} (g : β -> F (α.append1 β)) (x : β) :
Cofix.dest (Cofix.corec g x) = appendFun id (Cofix.corec g) < > g x := by
  conv =>
    lhs
    rw [Cofix.dest]; rw [Cofix.corec]
  dsimp
  rw [corecF_eq]; rw [abs_map]; rw [abs_repr]; rw [← comp_map]; rw [← appendFun_comp]; rfl

/--
Definition of `Cofix.mk` / `Cofix.mk` 的定义

English:
definition Cofix.mk
  signature: {α : TypeVec n}
  body: Cofix.corec fun x => (appendFun id fun i : Cofix F α => Cofix.dest.{u} i) < > x

中文:
定义 Cofix.mk
  签名: {α : TypeVec n}
  定义体: Cofix.corec fun x => (appendFun id fun i : Cofix F α => Cofix.dest.{u} i) < > x

Depends on / 依赖: Cofix.corec, Cofix.dest, appendFun
-/
def Cofix.mk {α : TypeVec n} : F (α.append1 <| Cofix F α) -> Cofix F α :=
Cofix.corec fun x => (appendFun id fun i : Cofix F α => Cofix.dest.{u} i) < > x

/-!
## Bisimulation principles for `Cofix F`

The following theorems are bisimulation principles. The general idea
is to use a bisimulation relation to prove the equality between
specific values of type `Cofix F α`.

A bisimulation relation `R` for values `x y : Cofix F α`:

* holds for `x y`: `R x y`
* for any values `x y` that satisfy `R`, their root has the same shape
  and their children can be paired in such a way that they satisfy `R`.

-/


set_option backward.isDefEq.respectTransparency false in
/--
theorem `Cofix.bisim_aux` / 定理 `Cofix.bisim_aux`

English:
theorem Cofix.bisim_aux
  statement: {α : TypeVec n} (r : Cofix F α -> Cofix F α -> Prop) (h' : forall x, r x x)
  proof: by
  intro x
  rcases x; clear x; rename M (P F) α => x
  intro y
  rcases y; clear y; rename M (P F) α => y
  intro rxy
  apply Quot.sound
  let r' := fun x y => r (Quot.mk _ x) (Quot.mk _ y)
  have hr' : r' = fun x y => r (Quot.mk _ x) (Quot.mk _ y) := rfl
  have : IsPrecongr r' := by
    intro a 

中文:
定理 Cofix.bisim_aux
  结论: {α : TypeVec n} (r : Cofix F α -> Cofix F α -> 命题) (h' : 对任意 x, r x x)
  证明: by
  intro x
  rcases x; clear x; rename M (P F) α => x
  intro y
  rcases y; clear y; rename M (P F) α => y
  intro rxy
  apply Quot.sound
  let r' := fun x y => r (Quot.mk _ x) (Quot.mk _ y)
  have hr' : r' = fun x y => r (Quot.mk _ x) (Quot.mk _ y) := rfl
  have : IsPrecongr r' := by
    intro a 
-/
private theorem Cofix.bisim_aux {α : TypeVec n} (r : Cofix F α -> Cofix F α -> Prop) (h' : forall x, r x x)
    (h : forall x y, r x y ->
appendFun id (Quot.mk r) < > Cofix.dest x = appendFun id (Quot.mk r) < > Cofix.dest y) :
    forall x y, r x y -> x = y := by
  intro x
  rcases x; clear x; rename M (P F) α => x
  intro y
  rcases y; clear y; rename M (P F) α => y
  intro rxy
  apply Quot.sound
  let r' := fun x y => r (Quot.mk _ x) (Quot.mk _ y)
  have hr' : r' = fun x y => r (Quot.mk _ x) (Quot.mk _ y) := rfl
  have : IsPrecongr r' := by
    intro a b r'ab
    have h₀ :
appendFun id (Quot.mk r ∘ Quot.mk Mcongr) < > MvQPF.abs (M.dest q.P a) =
appendFun id (Quot.mk r ∘ Quot.mk Mcongr) < > MvQPF.abs (M.dest q.P b) := by
      rw [appendFun_comp_id]; rw [comp_map]; rw [comp_map]; exact h _ _ r'ab
    have h₁ : forall u v : q.P.M α, Mcongr u v -> Quot.mk r' u = Quot.mk r' v := by
      intro u v cuv
      apply Quot.sound
      dsimp [r', hr']
      rw [Quot.sound cuv]
      apply h'
    let f : Quot r -> Quot r' :=
      Quot.lift (Quot.lift (Quot.mk r') h₁)
        (by
          intro c
          apply Quot.inductionOn
            (motive := fun c =>
              forall b, r c b -> Quot.lift (Quot.mk r') h₁ c = Quot.lift (Quot.mk r') h₁ b) c
          clear c
          intro c d
          apply Quot.inductionOn
            (motive := fun d => r (Quot.mk Mcongr c) d ->
              Quot.lift (Quot.mk r') h₁ (Quot.mk Mcongr c) = Quot.lift (Quot.mk r') h₁ d) d
          clear d
          intro d rcd; apply Quot.sound; apply rcd)
    have : f ∘ Quot.mk r ∘ Quot.mk Mcongr = Quot.mk r' := rfl
    rw [← this]; rw [appendFun_comp_id]; rw [q.P.comp_map]; rw [q.P.comp_map]; rw [abs_map]; rw [abs_map]; rw [abs_map]; rw [abs_map]; rw [h₀]
  exact ⟨r', this, rxy⟩

/--
theorem `Cofix.bisim_rel` / 定理 `Cofix.bisim_rel`

English:
theorem Cofix.bisim_rel
  statement: {α : TypeVec n} (r : Cofix F α -> Cofix F α -> Prop)
  proof: by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply Cofix.bisim_aux r'
  · intro x
    left
    rfl
  · intro x y r'xy
    cases r'xy with
    | inl h =>
      rw [h]
    | inr r'xy =>
      have : forall x y, r x y -> r' x y := fun x y h => Or.inr h
      rw [← Quot.factor_mk_eq _ _ this]
  

中文:
定理 Cofix.bisim_rel
  结论: {α : TypeVec n} (r : Cofix F α -> Cofix F α -> 命题)
  证明: by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply Cofix.bisim_aux r'
  · intro x
    left
    rfl
  · intro x y r'xy
    cases r'xy with
    | inl h =>
      rw [h]
    | inr r'xy =>
      have : forall x y, r x y -> r' x y := fun x y h => Or.inr h
      rw [← Quot.factor_mk_eq _ _ this]
  

Depends on / 依赖: Cofix.bisim_aux, Or.inr, Quot.factor_mk_eq, Quot.mk, appendFun, appendFun_comp_id, bisim_aux, comp_map, factor_mk_eq
-/
theorem Cofix.bisim_rel {α : TypeVec n} (r : Cofix F α -> Cofix F α -> Prop)
    (h : forall x y, r x y ->
appendFun id (Quot.mk r) < > Cofix.dest x = appendFun id (Quot.mk r) < > Cofix.dest y) :
    forall x y, r x y -> x = y := by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply Cofix.bisim_aux r'
  · intro x
    left
    rfl
  · intro x y r'xy
    cases r'xy with
    | inl h =>
      rw [h]
    | inr r'xy =>
      have : forall x y, r x y -> r' x y := fun x y h => Or.inr h
      rw [← Quot.factor_mk_eq _ _ this]
      dsimp [r']
      rw [appendFun_comp_id]
      rw [@comp_map _ _ q _ _ _ (appendFun id (Quot.mk r))]; rw [@comp_map _ _ q _ _ _ (appendFun id (Quot.mk r))]
      rw [h _ _ r'xy]
  right; exact rxy

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Cofix.bisim` / 定理 `Cofix.bisim`

English:
theorem Cofix.bisim
  statement: {α : TypeVec n} (r : Cofix F α -> Cofix F α -> Prop)
  proof: by
  apply Cofix.bisim_rel
  intro x y rxy
  rcases (liftR_iff (fun a b => RelLast α r b) (dest x) (dest y)).mp (h x y rxy)
    with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq]; rw [dyeq]; rw [← abs_map]; rw [← abs_map]; rw [MvPFunctor.map_eq]; rw [MvPFunctor.map_eq]
  rw [← split_dropFun_lastFun f₀]; r

中文:
定理 Cofix.bisim
  结论: {α : TypeVec n} (r : Cofix F α -> Cofix F α -> 命题)
  证明: by
  apply Cofix.bisim_rel
  intro x y rxy
  rcases (liftR_iff (fun a b => RelLast α r b) (dest x) (dest y)).mp (h x y rxy)
    with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq]; rw [dyeq]; rw [← abs_map]; rw [← abs_map]; rw [MvPFunctor.map_eq]; rw [MvPFunctor.map_eq]
  rw [← split_dropFun_lastFun f₀]; r

Depends on / 依赖: Cofix.bisim_rel, MvPFunctor, MvPFunctor.map_eq, Quot.sound, RelLast, abs_map, appendFun_comp_splitFun, bisim_rel, id_comp, liftR_iff, map_eq, split_dropFun_lastFun
-/
theorem Cofix.bisim {α : TypeVec n} (r : Cofix F α -> Cofix F α -> Prop)
    (h : forall x y, r x y -> LiftR (RelLast α r) (Cofix.dest x) (Cofix.dest y)) :
    forall x y, r x y -> x = y := by
  apply Cofix.bisim_rel
  intro x y rxy
  rcases (liftR_iff (fun a b => RelLast α r b) (dest x) (dest y)).mp (h x y rxy)
    with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq]; rw [dyeq]; rw [← abs_map]; rw [← abs_map]; rw [MvPFunctor.map_eq]; rw [MvPFunctor.map_eq]
  rw [← split_dropFun_lastFun f₀]; rw [← split_dropFun_lastFun f₁]
  rw [appendFun_comp_splitFun]; rw [appendFun_comp_splitFun]
  rw [id_comp]; rw [id_comp]
  congr 2 with (i j); rcases i with - | i
  · apply Quot.sound
    apply h' _ j
  · change f₀ _ j = f₁ _ j
    apply h' _ j

/--
theorem `Cofix.bisim₂` / 定理 `Cofix.bisim₂`

English:
theorem Cofix.bisim₂
  statement: {α : TypeVec n} (r : Cofix F α -> Cofix F α -> Prop)
  proof: Cofix.bisim r by intros; rw [← LiftR_RelLast_iff]; apply h; assumption

中文:
定理 Cofix.bisim₂
  结论: {α : TypeVec n} (r : Cofix F α -> Cofix F α -> 命题)
  证明: Cofix.bisim r by intros; rw [← LiftR_RelLast_iff]; apply h; assumption

Depends on / 依赖: Cofix.bisim, LiftR_RelLast_iff, intros
-/
theorem Cofix.bisim₂ {α : TypeVec n} (r : Cofix F α -> Cofix F α -> Prop)
    (h : forall x y, r x y -> LiftR' (RelLast' α r) (Cofix.dest x) (Cofix.dest y)) :
    forall x y, r x y -> x = y :=
Cofix.bisim r by intros; rw [← LiftR_RelLast_iff]; apply h; assumption

/--
theorem `Cofix.bisim'` / 定理 `Cofix.bisim'`

English:
theorem Cofix.bisim'
  statement: {α : TypeVec n} {β : Type*} (Q : β -> Prop) (u v : β -> Cofix F α)
  proof: fun x Qx =>
  let R := fun w z : Cofix F α => exists x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f', f₀, f₁, ux'eq, vx'eq, h'⟩
      rw [liftR_iff]
      refine
        ⟨a, q.P.appendContents f' f₀, q.P.appendContents f' f₁, xe

中文:
定理 Cofix.bisim'
  结论: {α : TypeVec n} {β : 类型} (Q : β -> 命题) (u v : β -> Cofix F α)
  证明: fun x Qx =>
  let R := fun w z : Cofix F α => exists x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f', f₀, f₁, ux'eq, vx'eq, h'⟩
      rw [liftR_iff]
      refine
        ⟨a, q.P.appendContents f' f₀, q.P.appendContents f' f₁, xe
-/
theorem Cofix.bisim' {α : TypeVec n} {β : Type*} (Q : β -> Prop) (u v : β -> Cofix F α)
    (h : forall x, Q x -> exists a f' f₀ f₁,
      Cofix.dest (u x) = q.abs ⟨a, q.P.appendContents f' f₀⟩ ∧
        Cofix.dest (v x) = q.abs ⟨a, q.P.appendContents f' f₁⟩ ∧
          forall i, exists x', Q x' ∧ f₀ i = u x' ∧ f₁ i = v x') :
    forall x, Q x -> u x = v x := fun x Qx =>
  let R := fun w z : Cofix F α => exists x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f', f₀, f₁, ux'eq, vx'eq, h'⟩
      rw [liftR_iff]
      refine
        ⟨a, q.P.appendContents f' f₀, q.P.appendContents f' f₁, xeq.symm ▸ ux'eq,
          yeq.symm ▸ vx'eq, ?_⟩
      intro i; cases i
      · apply h'
      · intro j
        apply Eq.refl)
    _ _ ⟨x, Qx, rfl, rfl⟩

/--
theorem `Cofix.mk_dest` / 定理 `Cofix.mk_dest`

English:
theorem Cofix.mk_dest
  given: {α : TypeVec n} (x : Cofix F α)
  statement: Cofix.mk (Cofix.dest x) = x
  proof: by
  apply Cofix.bisim_rel (fun x y : Cofix F α => x = Cofix.mk (Cofix.dest y)) _ _ _ rfl
  intro x y h
  rw [h]
  conv =>
    lhs
    congr
    rfl
    rw [Cofix.mk]
    rw [Cofix.dest_corec]
  rw [← comp_map]; rw [← appendFun_comp]; rw [id_comp]
  rw [← comp_map]; rw [← appendFun_comp]; rw [id_com

中文:
定理 Cofix.mk_dest
  条件: {α : TypeVec n} (x : Cofix F α)
  结论: Cofix.mk (Cofix.dest x) = x
  证明: by
  apply Cofix.bisim_rel (fun x y : Cofix F α => x = Cofix.mk (Cofix.dest y)) _ _ _ rfl
  intro x y h
  rw [h]
  conv =>
    lhs
    congr
    rfl
    rw [Cofix.mk]
    rw [Cofix.dest_corec]
  rw [← comp_map]; rw [← appendFun_comp]; rw [id_comp]
  rw [← comp_map]; rw [← appendFun_comp]; rw [id_com

Depends on / 依赖: Cofix.bisim_rel, Cofix.dest, Cofix.dest_corec, Cofix.mk, Quot.sound, appendFun_comp, bisim_rel, comp_map, dest_corec, id_comp
-/
theorem Cofix.mk_dest {α : TypeVec n} (x : Cofix F α) : Cofix.mk (Cofix.dest x) = x := by
  apply Cofix.bisim_rel (fun x y : Cofix F α => x = Cofix.mk (Cofix.dest y)) _ _ _ rfl
  intro x y h
  rw [h]
  conv =>
    lhs
    congr
    rfl
    rw [Cofix.mk]
    rw [Cofix.dest_corec]
  rw [← comp_map]; rw [← appendFun_comp]; rw [id_comp]
  rw [← comp_map]; rw [← appendFun_comp]; rw [id_comp]; rw [← Cofix.mk]
  congr 1
  apply congrArg
  funext x
  apply Quot.sound
  rfl

/--
theorem `Cofix.dest_mk` / 定理 `Cofix.dest_mk`

English:
theorem Cofix.dest_mk
  given: {α : TypeVec n} (x : F (α.append1 <| Cofix F α))
  proof: by
  have : Cofix.mk ∘ Cofix.dest = @_root_.id (Cofix F α) := funext Cofix.mk_dest
  rw [Cofix.mk]; rw [Cofix.dest_corec]; rw [← comp_map]; rw [← Cofix.mk]; rw [← appendFun_comp]; rw [this]; rw [id_comp]; rw [appendFun_id_id]; rw [MvFunctor.id_map]

中文:
定理 Cofix.dest_mk
  条件: {α : TypeVec n} (x : F (α.append1 <| Cofix F α))
  证明: by
  have : Cofix.mk ∘ Cofix.dest = @_root_.id (Cofix F α) := funext Cofix.mk_dest
  rw [Cofix.mk]; rw [Cofix.dest_corec]; rw [← comp_map]; rw [← Cofix.mk]; rw [← appendFun_comp]; rw [this]; rw [id_comp]; rw [appendFun_id_id]; rw [MvFunctor.id_map]

Depends on / 依赖: Cofix.dest, Cofix.dest_corec, Cofix.mk, Cofix.mk_dest, MvFunctor, MvFunctor.id_map, _root_, _root_.id, appendFun_comp, appendFun_id_id, comp_map, dest_corec, id_comp, id_map, mk_dest
-/
theorem Cofix.dest_mk {α : TypeVec n} (x : F (α.append1 <| Cofix F α)) :
    Cofix.dest (Cofix.mk x) = x := by
  have : Cofix.mk ∘ Cofix.dest = @_root_.id (Cofix F α) := funext Cofix.mk_dest
  rw [Cofix.mk]; rw [Cofix.dest_corec]; rw [← comp_map]; rw [← Cofix.mk]; rw [← appendFun_comp]; rw [this]; rw [id_comp]; rw [appendFun_id_id]; rw [MvFunctor.id_map]

/--
theorem `Cofix.ext` / 定理 `Cofix.ext`

English:
theorem Cofix.ext
  given: {α : TypeVec n} (x y : Cofix F α) (h : x.dest = y.dest)
  statement: x = y
  proof: by
  rw [← Cofix.mk_dest x]; rw [h]; rw [Cofix.mk_dest]

中文:
定理 Cofix.ext
  条件: {α : TypeVec n} (x y : Cofix F α) (h : x.dest = y.dest)
  结论: x = y
  证明: by
  rw [← Cofix.mk_dest x]; rw [h]; rw [Cofix.mk_dest]

Depends on / 依赖: Cofix.mk_dest, mk_dest
-/
theorem Cofix.ext {α : TypeVec n} (x y : Cofix F α) (h : x.dest = y.dest) : x = y := by
  rw [← Cofix.mk_dest x]; rw [h]; rw [Cofix.mk_dest]

/--
theorem `Cofix.ext_mk` / 定理 `Cofix.ext_mk`

English:
theorem Cofix.ext_mk
  given: {α : TypeVec n} (x y : F (α ::: Cofix F α)) (h : Cofix.mk x = Cofix.mk y)
  proof: by rw [← Cofix.dest_mk x, h, Cofix.dest_mk]

中文:
定理 Cofix.ext_mk
  条件: {α : TypeVec n} (x y : F (α ::: Cofix F α)) (h : Cofix.mk x = Cofix.mk y)
  证明: by rw [← Cofix.dest_mk x, h, Cofix.dest_mk]

Depends on / 依赖: Cofix.dest_mk, dest_mk
-/
theorem Cofix.ext_mk {α : TypeVec n} (x y : F (α ::: Cofix F α)) (h : Cofix.mk x = Cofix.mk y) :
    x = y := by rw [← Cofix.dest_mk x, h, Cofix.dest_mk]

/-!
`liftR_map`, `liftR_map_last` and `liftR_map_last'` are useful for reasoning about
the induction step in bisimulation proofs.
-/


section LiftRMap

/--
theorem `liftR_map` / 定理 `liftR_map`

English:
theorem liftR_map
  statement: {α β : TypeVec n} {F' : TypeVec n -> Type u} [MvFunctor F'] [LawfulMvFunctor F']
  proof: by
  rw [LiftR_def]
exists h < > x
  rw [MvFunctor.map_map]; rw [comp_assoc]; rw [hh]; rw [← comp_assoc]; rw [fst_prod_mk]; rw [comp_assoc]; rw [fst_diag]
  rw [MvFunctor.map_map]; rw [comp_assoc]; rw [hh]; rw [← comp_assoc]; rw [snd_prod_mk]; rw [comp_assoc]; rw [snd_diag]
  dsimp [LiftR']; constru

中文:
定理 liftR_map
  结论: {α β : TypeVec n} {F' : TypeVec n -> 类型u} [MvFunctor F'] [LawfulMvFunctor F']
  证明: by
  rw [LiftR_def]
exists h < > x
  rw [MvFunctor.map_map]; rw [comp_assoc]; rw [hh]; rw [← comp_assoc]; rw [fst_prod_mk]; rw [comp_assoc]; rw [fst_diag]
  rw [MvFunctor.map_map]; rw [comp_assoc]; rw [hh]; rw [← comp_assoc]; rw [snd_prod_mk]; rw [comp_assoc]; rw [snd_diag]
  dsimp [LiftR']; constru

Depends on / 依赖: LiftR_def, MvFunctor, MvFunctor.map_map, comp_assoc, fst_diag, fst_prod_mk, map_map, snd_diag, snd_prod_mk
-/
theorem liftR_map {α β : TypeVec n} {F' : TypeVec n -> Type u} [MvFunctor F'] [LawfulMvFunctor F']
    (R : β otimes β ⟹ «repeat» n Prop) (x : F' α) (f g : α ⟹ β) (h : α ⟹ Subtype_ R)
    (hh : subtypeVal _ ⊚ h = (f otimes' g) ⊚ prod.diag) : LiftR' R (f <$$> x) (g <$$> x) := by
  rw [LiftR_def]
exists h < > x
  rw [MvFunctor.map_map]; rw [comp_assoc]; rw [hh]; rw [← comp_assoc]; rw [fst_prod_mk]; rw [comp_assoc]; rw [fst_diag]
  rw [MvFunctor.map_map]; rw [comp_assoc]; rw [hh]; rw [← comp_assoc]; rw [snd_prod_mk]; rw [comp_assoc]; rw [snd_diag]
  dsimp [LiftR']; constructor <;> rfl

open Function

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftR_map_last` / 定理 `liftR_map_last`

English:
theorem liftR_map_last
  statement: [lawful : LawfulMvFunctor F]
  proof: let h : ι -> { x : ι' × ι' // uncurry R x } := fun x => ⟨(f x, g x), hh x⟩
  let b : (α ::: ι) ⟹ _ := @diagSub n α ::: h
  let c :
    (Subtype_ α.repeatEq ::: { x // uncurry R x }) ⟹
      ((fun i : Fin2 n => { x // ofRepeat (α.RelLast' R i.fs x) }) ::: Subtype (uncurry R)) :=
    ofSubtype _ ::: i

中文:
定理 liftR_map_last
  结论: [lawful : LawfulMvFunctor F]
  证明: let h : ι -> { x : ι' × ι' // uncurry R x } := fun x => ⟨(f x, g x), hh x⟩
  let b : (α ::: ι) ⟹ _ := @diagSub n α ::: h
  let c :
    (Subtype_ α.repeatEq ::: { x // uncurry R x }) ⟹
      ((fun i : Fin2 n => { x // ofRepeat (α.RelLast' R i.fs x) }) ::: Subtype (uncurry R)) :=
    ofSubtype _ ::: i

Depends on / 依赖: RelLast, Subtype, Subtype_, TypeVec, TypeVec.id_comp, diagSub, eq_of_drop_last_eq, fromAppend1DropLast, i.fs, id_comp, ofRepeat, ofSubtype, otimes, prod.diag, prod_map_id, repeatEq, subtypeVal, toSubtyp, toSubtype, uncurry
-/
theorem liftR_map_last [lawful : LawfulMvFunctor F]
    {α : TypeVec n} {ι ι'} (R : ι' -> ι' -> Prop)
    (x : F (α ::: ι)) (f g : ι -> ι') (hh : forall x : ι, R (f x) (g x)) :
    LiftR' (RelLast' _ R) ((id ::: f) <$$> x) ((id ::: g) <$$> x) :=
  let h : ι -> { x : ι' × ι' // uncurry R x } := fun x => ⟨(f x, g x), hh x⟩
  let b : (α ::: ι) ⟹ _ := @diagSub n α ::: h
  let c :
    (Subtype_ α.repeatEq ::: { x // uncurry R x }) ⟹
      ((fun i : Fin2 n => { x // ofRepeat (α.RelLast' R i.fs x) }) ::: Subtype (uncurry R)) :=
    ofSubtype _ ::: id
  have hh :
    subtypeVal _ ⊚ toSubtype _ ⊚ fromAppend1DropLast ⊚ c ⊚ b =
      ((id ::: f) otimes' (id ::: g)) ⊚ prod.diag := by
    dsimp [b]
    apply eq_of_drop_last_eq
    · dsimp
      simp only [prod_map_id, TypeVec.id_comp]
      erw [toSubtype_of_subtype_assoc, TypeVec.id_comp]
      clear liftR_map_last q lawful F x R f g hh h b c
      ext (i x) : 2
      induction i with
      | fz => rfl
      | fs _ ih =>
        apply ih
    simp only [lastFun_from_append1_drop_last, lastFun_toSubtype, lastFun_appendFun,
      lastFun_subtypeVal, Function.id_comp, lastFun_comp, lastFun_prod]
    ext1
    rfl
  liftR_map _ _ _ _ (toSubtype _ ⊚ fromAppend1DropLast ⊚ c ⊚ b) hh

/--
theorem `liftR_map_last'` / 定理 `liftR_map_last'`

English:
theorem liftR_map_last'
  statement: [LawfulMvFunctor F] {α : TypeVec n} {ι} (R : ι -> ι -> Prop) (x : F (α ::: ι))
  proof: by
  have := liftR_map_last R x f id hh
  rwa [appendFun_id_id, MvFunctor.id_map] at this

中文:
定理 liftR_map_last'
  结论: [LawfulMvFunctor F] {α : TypeVec n} {ι} (R : ι -> ι -> 命题) (x : F (α ::: ι))
  证明: by
  have := liftR_map_last R x f id hh
  rwa [appendFun_id_id, MvFunctor.id_map] at this

Depends on / 依赖: MvFunctor, MvFunctor.id_map, appendFun_id_id, id_map, liftR_map_last
-/
theorem liftR_map_last' [LawfulMvFunctor F] {α : TypeVec n} {ι} (R : ι -> ι -> Prop) (x : F (α ::: ι))
    (f : ι -> ι) (hh : forall x : ι, R (f x) x) : LiftR' (RelLast' _ R) ((id ::: f) <$$> x) x := by
  have := liftR_map_last R x f id hh
  rwa [appendFun_id_id, MvFunctor.id_map] at this

end LiftRMap

variable {F : TypeVec (n + 1) -> Type u} [q : MvQPF F]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Cofix.abs_repr` / 定理 `Cofix.abs_repr`

English:
theorem Cofix.abs_repr
  given: {α} (x : Cofix F α)
  statement: Quot.mk _ (Cofix.repr x) = x
  proof: by
  let R := fun x y : Cofix F α => abs (repr y) = x
  refine Cofix.bisim₂ R ?_ _ _ rfl
  clear x
  rintro x y h
  subst h
  dsimp [Cofix.dest, Cofix.abs]
  induction y using Quot.ind
  simp only [Cofix.repr, M.dest_corec, abs_map, MvQPF.abs_repr, Function.comp]
  conv => congr; rfl; rw [Cofix.dest

中文:
定理 Cofix.abs_repr
  条件: {α} (x : Cofix F α)
  结论: Quot.mk _ (Cofix.repr x) = x
  证明: by
  let R := fun x y : Cofix F α => abs (repr y) = x
  refine Cofix.bisim₂ R ?_ _ _ rfl
  clear x
  rintro x y h
  subst h
  dsimp [Cofix.dest, Cofix.abs]
  induction y using Quot.ind
  simp only [Cofix.repr, M.dest_corec, abs_map, MvQPF.abs_repr, Function.comp]
  conv => congr; rfl; rw [Cofix.dest

Depends on / 依赖: Cofix.abs, Cofix.bisim, Cofix.dest, Cofix.repr, Function, Function.comp, M.dest_corec, MvFunctor, MvFunctor.map_map, MvQPF.abs_repr, Quot.ind, abs_map, abs_repr, appendFun_comp_id, dest_corec, intros, liftR_map_last, map_map
-/
theorem Cofix.abs_repr {α} (x : Cofix F α) : Quot.mk _ (Cofix.repr x) = x := by
  let R := fun x y : Cofix F α => abs (repr y) = x
  refine Cofix.bisim₂ R ?_ _ _ rfl
  clear x
  rintro x y h
  subst h
  dsimp [Cofix.dest, Cofix.abs]
  induction y using Quot.ind
  simp only [Cofix.repr, M.dest_corec, abs_map, MvQPF.abs_repr, Function.comp]
  conv => congr; rfl; rw [Cofix.dest]
  rw [MvFunctor.map_map]; rw [MvFunctor.map_map]; rw [← appendFun_comp_id]; rw [← appendFun_comp_id]
  apply liftR_map_last
  intros
  rfl

end MvQPF

namespace Mathlib.Tactic.MvBisim

open Lean Expr Elab Term Tactic Meta Qq

/-- tactic for proof by bisimulation -/
syntax "mv_bisim" (ppSpace colGt term) (" with" (ppSpace colGt binderIdent)+)? : tactic

elab_rules : tactic
  | `(tactic| mv_bisim $e $[ with $ids:binderIdent*]?) => do
    let ids : TSyntaxArray `Lean.binderIdent := ids.getD #[]
    let idsn (n : Nat) : Name :=
      match ids[n]? with
      | some s =>
        match s with
        | `(binderIdent| $n:ident) => n.getId
        | `(binderIdent| _) => `_
        | _ => unreachable!
      | none => `_
    let idss (n : Nat) : TacticM (TSyntax `rcasesPat) := do
      match ids[n]? with
      | some s =>
        match s with
        | `(binderIdent| $n:ident) => `(rcasesPat| $n)
        | `(binderIdent| _%$b) => `(rcasesPat| _%$b)
        | _ => unreachable!
      | none => `(rcasesPat| _)
    withMainContext do
      let e ← Tactic.elabTerm e none
      let f ← liftMetaTacticAux fun g => do
        let (#[fv], g) ← g.generalize #[{ expr := e }] | unreachable!
        return (mkFVar fv, [g])
      withMainContext do
        let some (t, l, r) ← matchEq? (← getMainTarget) | throwError "goal is not an equality"
        let ex ←
          withLocalDecl (idsn 1) .default t fun v₀ =>
            withLocalDecl (idsn 2) .default t fun v₁ => do
              let x₀ ← mkEq v₀ l
              let x₁ ← mkEq v₁ r
              let xx ← mkAppM ``And #[x₀, x₁]
              let ex₁ ← mkLambdaFVars #[f] xx
              let ex₂ ← mkAppM ``Exists #[ex₁]
              mkLambdaFVars #[v₀, v₁] ex₂
        let R ← liftMetaTacticAux fun g => do
          let g₁ ← g.define (idsn 0) (← mkArrow t (← mkArrow t (mkSort .zero))) ex
          let (Rv, g₂) ← g₁.intro1P
          return (mkFVar Rv, [g₂])
        withMainContext do
          ids[0]?.forM fun s => addLocalVarInfoForBinderIdent R s
          let sR ← exprToSyntax R
evalTactic ← `(tactic|
refine MvQPF.Cofix.bisim₂ sR ?_ _ _ ⟨_, rfl, rfl⟩;
rintro (← idss 1) (← idss 2) ⟨ (← idss 3), (← idss 4), (← idss 5)⟩)
          liftMetaTactic fun g => return [← g.clear f.fvarId!]
    for h : n in [6 : ids.size] do
      let name := ids[n]
      logWarningAt name m!"unused name: {name}"

end Mathlib.Tactic.MvBisim

namespace MvQPF

open TypeVec MvPFunctor

open MvFunctor (LiftP LiftR)

variable {n : Nat} {F : TypeVec.{u} (n + 1) -> Type u} [q : MvQPF F]

/--
theorem `corec_roll` / 定理 `corec_roll`

English:
theorem corec_roll
  given: {α : TypeVec n} {X Y} {x₀ : X} (f : X -> Y) (g : Y -> F (α ::: X))
  proof: by
  mv_bisim x₀ with R a b x Ha Hb
  rw [Ha]; rw [Hb]; rw [Cofix.dest_corec]; rw [Cofix.dest_corec]; rw [Function.comp_apply]; rw [Function.comp_apply]
  rw [MvFunctor.map_map]; rw [← appendFun_comp_id]
  refine liftR_map_last _ _ _ _ ?_
  intro a; refine ⟨a, rfl, rfl⟩

中文:
定理 corec_roll
  条件: {α : TypeVec n} {X Y} {x₀ : X} (f : X -> Y) (g : Y -> F (α ::: X))
  证明: by
  mv_bisim x₀ with R a b x Ha Hb
  rw [Ha]; rw [Hb]; rw [Cofix.dest_corec]; rw [Cofix.dest_corec]; rw [Function.comp_apply]; rw [Function.comp_apply]
  rw [MvFunctor.map_map]; rw [← appendFun_comp_id]
  refine liftR_map_last _ _ _ _ ?_
  intro a; refine ⟨a, rfl, rfl⟩

Depends on / 依赖: Cofix.dest_corec, Function, Function.comp_apply, MvFunctor, MvFunctor.map_map, appendFun_comp_id, comp_apply, dest_corec, liftR_map_last, map_map, mv_bisim
-/
theorem corec_roll {α : TypeVec n} {X Y} {x₀ : X} (f : X -> Y) (g : Y -> F (α ::: X)) :
    Cofix.corec (g ∘ f) x₀ = Cofix.corec (MvFunctor.map (id ::: f) ∘ g) (f x₀) := by
  mv_bisim x₀ with R a b x Ha Hb
  rw [Ha]; rw [Hb]; rw [Cofix.dest_corec]; rw [Cofix.dest_corec]; rw [Function.comp_apply]; rw [Function.comp_apply]
  rw [MvFunctor.map_map]; rw [← appendFun_comp_id]
  refine liftR_map_last _ _ _ _ ?_
  intro a; refine ⟨a, rfl, rfl⟩

/--
theorem `Cofix.dest_corec'` / 定理 `Cofix.dest_corec'`

English:
theorem Cofix.dest_corec'
  statement: {α : TypeVec.{u} n} {β : Type u}
  proof: by
  rw [Cofix.corec']; rw [Cofix.dest_corec]; dsimp
  congr!; ext (i | i) <;> erw [corec_roll] <;> dsimp [Cofix.corec']
  · mv_bisim i with R a b x Ha Hb
    rw [Ha]; rw [Hb]; rw [Cofix.dest_corec]
    dsimp [Function.comp_def]
    repeat rw [MvFunctor.map_map, ← appendFun_comp_id]
    apply liftR_

中文:
定理 Cofix.dest_corec'
  结论: {α : TypeVec.{u} n} {β : 类型u}
  证明: by
  rw [Cofix.corec']; rw [Cofix.dest_corec]; dsimp
  congr!; ext (i | i) <;> erw [corec_roll] <;> dsimp [Cofix.corec']
  · mv_bisim i with R a b x Ha Hb
    rw [Ha]; rw [Hb]; rw [Cofix.dest_corec]
    dsimp [Function.comp_def]
    repeat rw [MvFunctor.map_map, ← appendFun_comp_id]
    apply liftR_

Depends on / 依赖: Cofix.corec, Cofix.dest_corec, Function, Function.comp_def, MvFunctor, MvFunctor.id_map, MvFunctor.map_map, Sum.elim, appendFun_comp_id, appendFun_id_id, comp_def, corec_roll, dest_corec, id_map, intros, liftR_map_last, map_map, mv_bisim, repeat
-/
theorem Cofix.dest_corec' {α : TypeVec.{u} n} {β : Type u}
    (g : β -> F (α.append1 (Cofix F α oplus β))) (x : β) :
    Cofix.dest (Cofix.corec' g x) =
appendFun id (Sum.elim _root_.id (Cofix.corec' g)) < > g x := by
  rw [Cofix.corec']; rw [Cofix.dest_corec]; dsimp
  congr!; ext (i | i) <;> erw [corec_roll] <;> dsimp [Cofix.corec']
  · mv_bisim i with R a b x Ha Hb
    rw [Ha]; rw [Hb]; rw [Cofix.dest_corec]
    dsimp [Function.comp_def]
    repeat rw [MvFunctor.map_map, ← appendFun_comp_id]
    apply liftR_map_last'
    dsimp [Function.comp_def]
    intros
    exact ⟨_, rfl, rfl⟩
  · congr 1 with y
    erw [appendFun_id_id]
    simp [MvFunctor.id_map, Sum.elim]

/--
theorem `Cofix.dest_corec₁` / 定理 `Cofix.dest_corec₁`

English:
theorem Cofix.dest_corec₁
  statement: {α : TypeVec n} {β : Type u}
  proof: by
  rw [Cofix.corec₁]; rw [Cofix.dest_corec']; rw [← h]; rfl

中文:
定理 Cofix.dest_corec₁
  结论: {α : TypeVec n} {β : 类型u}
  证明: by
  rw [Cofix.corec₁]; rw [Cofix.dest_corec']; rw [← h]; rfl

Depends on / 依赖: Cofix.corec, Cofix.dest_corec, dest_corec
-/
theorem Cofix.dest_corec₁ {α : TypeVec n} {β : Type u}
    (g : forall {X}, (Cofix F α -> X) -> (β -> X) -> β -> F (α.append1 X)) (x : β)
    (h : forall (X Y) (f : Cofix F α -> X) (f' : β -> X) (k : X -> Y),
g (k ∘ f) (k ∘ f') x = (id ::: k) < > g f f' x) :
    Cofix.dest (Cofix.corec₁ (@g) x) = g id (Cofix.corec₁ @g) x := by
  rw [Cofix.corec₁]; rw [Cofix.dest_corec']; rw [← h]; rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Instance `mvqpfCofix` / 实例 `mvqpfCofix`

English:
instance mvqpfCofix
  signature: : MvQPF (Cofix F) where
  body: q.P.mp
  abs := Quot.mk Mcongr
  repr := Cofix.repr
  abs_repr := Cofix.abs_repr
  abs_map := by intros; rfl

中文:
实例 mvqpfCofix
  签名: : MvQPF (Cofix F) where
  定义体: q.P.mp
  abs := Quot.mk Mcongr
  repr := Cofix.repr
  abs_repr := Cofix.abs_repr
  abs_map := by intros; rfl

Depends on / 依赖: q.P.mp
-/
instance mvqpfCofix : MvQPF (Cofix F) where
  P := q.P.mp
  abs := Quot.mk Mcongr
  repr := Cofix.repr
  abs_repr := Cofix.abs_repr
  abs_map := by intros; rfl

end MvQPF
