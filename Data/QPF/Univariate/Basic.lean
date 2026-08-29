/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.PFunctor.Univariate.M

/-!

# Quotients of Polynomial Functors

We assume the following:

* `P`: a polynomial functor
* `W`: its W-type
* `M`: its M-type
* `F`: a functor

We define:

* `q`: `QPF` data, representing `F` as a quotient of `P`

The main goal is to construct:

* `Fix`: the initial algebra with structure map `F Fix → Fix`.
* `Cofix`: the final coalgebra with structure map `Cofix → F Cofix`

We also show that the composition of qpfs is a qpf, and that the quotient of a qpf
is a qpf.

The present theory focuses on the univariate case for qpfs

## References

* [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial
  Functors*][avigad-carneiro-hudon2019]

-/

@[expose] public section


universe u u' v

/--
Definition of `QPF` / `QPF` 的定义

English:
class QPF
  parameters: (F : Type u -> Type v)
  extends: Functor F
  axioms and operations (4):
    - P : PFunctor.{u, u'}
    - abs : forall {α}, P α -> F α
    - repr : forall {α}, F α -> P α
    - abs_repr : forall {α} (x : F α), abs (repr x) = x

中文:
类 QPF
  参数: (F : 类型u -> 类型v)
  继承: Functor F
  公理与运算 (4 个):
    - P : PFunctor.{u, u'}
    - abs : 对任意 {α}, P α -> F α
    - repr : 对任意 {α}, F α -> P α
    - abs_repr : 对任意 {α} (x : F α), abs (repr x) = x
-/
class QPF (F : Type u -> Type v) extends Functor F where
  P : PFunctor.{u, u'}
  abs : forall {α}, P α -> F α
  repr : forall {α}, F α -> P α
  abs_repr : forall {α} (x : F α), abs (repr x) = x
abs_map : forall {α β} (f : α -> β) (p : P α), abs (P.map f p) = f < > abs p

namespace QPF

variable {F : Type u -> Type v} [q : QPF F]

open Functor (Liftp Liftr)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `id_map` / 定理 `id_map`

English:
theorem id_map
  given: {α : Type _} (x : F α)
  statement: id < > x = x
  proof: by
  rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x
  rw [← abs_map]
  rfl

中文:
定理 id_map
  条件: {α : Type _} (x : F α)
  结论: id < > x = x
  证明: by
  rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x
  rw [← abs_map]
  rfl

Depends on / 依赖: abs_map, abs_repr
-/
theorem id_map {α : Type _} (x : F α) : id < > x = x := by
  rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x
  rw [← abs_map]
  rfl

/--
theorem `comp_map` / 定理 `comp_map`

English:
theorem comp_map
  given: {α β γ : Type _} (f : α -> β) (g : β -> γ) (x : F α)
  proof: by
  rw [← abs_repr x]
  rw [← abs_map]; rw [← abs_map]; rw [← abs_map]
  rfl

中文:
定理 comp_map
  条件: {α β γ : Type _} (f : α -> β) (g : β -> γ) (x : F α)
  证明: by
  rw [← abs_repr x]
  rw [← abs_map]; rw [← abs_map]; rw [← abs_map]
  rfl

Depends on / 依赖: abs_map, abs_repr
-/
theorem comp_map {α β γ : Type _} (f : α -> β) (g : β -> γ) (x : F α) :
(g ∘ f) < > x = g < > f < > x := by
  rw [← abs_repr x]
  rw [← abs_map]; rw [← abs_map]; rw [← abs_map]
  rfl

/--
theorem `lawfulFunctor` / 定理 `lawfulFunctor`

English:
theorem lawfulFunctor
  proof: { map_const := @h
    id_map := @id_map F _
    comp_map := @comp_map F _ }

中文:
定理 lawfulFunctor
  证明: { map_const := @h
    id_map := @id_map F _
    comp_map := @comp_map F _ }

Depends on / 依赖: comp_map, id_map, map_const
-/
theorem lawfulFunctor
    (h : forall α β : Type u, @Functor.mapConst F _ α _ = Functor.map ∘ Function.const β) :
    LawfulFunctor F :=
  { map_const := @h
    id_map := @id_map F _
    comp_map := @comp_map F _ }

/-
Lifting predicates and relations
-/
section

open Functor

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftp_iff` / 定理 `liftp_iff`

English:
theorem liftp_iff
  given: {α : Type u} (p : α -> Prop) (x : F α)
  proof: by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use a, fun i => (f i).val
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨a, f, h₀, h₁⟩
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map]; rw [h₀]; rfl

中文:
定理 liftp_iff
  条件: {α : 类型u} (p : α -> 命题) (x : F α)
  证明: by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use a, fun i => (f i).val
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨a, f, h₀, h₁⟩
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map]; rw [h₀]; rfl

Depends on / 依赖: abs_map, abs_repr, property
-/
theorem liftp_iff {α : Type u} (p : α -> Prop) (x : F α) :
    Liftp p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i, p (f i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use a, fun i => (f i).val
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨a, f, h₀, h₁⟩
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map]; rw [h₀]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftp_iff'` / 定理 `liftp_iff'`

English:
theorem liftp_iff'
  given: {α : Type u} (p : α -> Prop) (x : F α)
  proof: by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use ⟨a, fun i => (f i).val⟩
    dsimp
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨⟨a, f⟩, h₀, h₁⟩; dsimp at *
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [←

中文:
定理 liftp_iff'
  条件: {α : 类型u} (p : α -> 命题) (x : F α)
  证明: by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use ⟨a, fun i => (f i).val⟩
    dsimp
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨⟨a, f⟩, h₀, h₁⟩; dsimp at *
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [←

Depends on / 依赖: abs_map, abs_repr, property
-/
theorem liftp_iff' {α : Type u} (p : α -> Prop) (x : F α) :
    Liftp p x ↔ exists u : q.P α, abs u = x ∧ forall i, p (u.snd i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use ⟨a, fun i => (f i).val⟩
    dsimp
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨⟨a, f⟩, h₀, h₁⟩; dsimp at *
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map]; rw [← h₀]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftr_iff` / 定理 `liftr_iff`

English:
theorem liftr_iff
  given: {α : Type u} (r : α -> α -> Prop) (x y : F α)
  proof: by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : repr u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]
      rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]
      rfl
    intro i
    exact (f

中文:
定理 liftr_iff
  条件: {α : 类型u} (r : α -> α -> 命题) (x y : F α)
  证明: by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : repr u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]
      rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]
      rfl
    intro i
    exact (f

Depends on / 依赖: abs_map, abs_repr, property, val.fst, val.snd
-/
theorem liftr_iff {α : Type u} (r : α -> α -> Prop) (x y : F α) :
    Liftr r x y ↔ exists a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ forall i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : repr u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]
      rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use abs ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  constructor
  · rw [xeq, ← abs_map]
    rfl
  rw [yeq]; rw [← abs_map]; rfl

end

/-
Think of trees in the `W` type corresponding to `P` as representatives of elements of the
least fixed point of `F`, and assign a canonical representative to each equivalence class
of trees.
-/
/--
Definition of `recF` / `recF` 的定义

English:
definition recF
  signature: {α : Type _} (g : F α -> α)

中文:
定义 recF
  签名: {α : Type _} (g : F α -> α)
-/
def recF {α : Type _} (g : F α -> α) : q.P.W -> α
  | ⟨a, f⟩ => g (abs ⟨a, fun x => recF g (f x)⟩)

/--
theorem `recF_eq` / 定理 `recF_eq`

English:
theorem recF_eq
  given: {α : Type _} (g : F α -> α) (x : q.P.W)
  proof: by
  cases x
  rfl

中文:
定理 recF_eq
  条件: {α : Type _} (g : F α -> α) (x : q.P.W)
  证明: by
  cases x
  rfl
-/
theorem recF_eq {α : Type _} (g : F α -> α) (x : q.P.W) :
    recF g x = g (abs (q.P.map (recF g) x.dest)) := by
  cases x
  rfl

/--
theorem `recF_eq'` / 定理 `recF_eq'`

English:
theorem recF_eq'
  given: {α : Type _} (g : F α -> α) (a : q.P.A) (f : q.P.B a -> q.P.W)
  proof: rfl

中文:
定理 recF_eq'
  条件: {α : Type _} (g : F α -> α) (a : q.P.A) (f : q.P.B a -> q.P.W)
  证明: rfl
-/
theorem recF_eq' {α : Type _} (g : F α -> α) (a : q.P.A) (f : q.P.B a -> q.P.W) :
    recF g ⟨a, f⟩ = g (abs (q.P.map (recF g) ⟨a, f⟩)) :=
  rfl

/--
Inductive type `Wequiv` / 归纳类型 `Wequiv`

English:
inductive Wequiv
  parameters: : q.P.W -> q.P.W -> Prop
  constructors (3):
    - ind: (a : q.P.A) (f f' : q.P.B a -> q.P.W) : (forall x, Wequiv (f x) (f' x)) -> Wequiv ⟨a, f⟩ ⟨a, f'⟩
    - abs: (a : q.P.A) (f : q.P.B a -> q.P.W) (a' : q.P.A) (f' : q.P.B a' -> q.P.W) : abs ⟨a, f⟩ = abs ⟨a', f'⟩ -> Wequiv ⟨a, f⟩ ⟨a', f'⟩
    - trans: (u v w : q.P.W) : Wequiv u v -> Wequiv v w -> Wequiv u w

中文:
归纳类型 Wequiv
  参数: : q.P.W -> q.P.W -> 命题
  构造子 (3 个):
    - ind: (a : q.P.A) (f f' : q.P.B a -> q.P.W) : (对任意 x, Wequiv (f x) (f' x)) -> Wequiv ⟨a, f⟩ ⟨a, f'⟩
    - abs: (a : q.P.A) (f : q.P.B a -> q.P.W) (a' : q.P.A) (f' : q.P.B a' -> q.P.W) : abs ⟨a, f⟩ = abs ⟨a', f'⟩ -> Wequiv ⟨a, f⟩ ⟨a', f'⟩
    - trans: (u v w : q.P.W) : Wequiv u v -> Wequiv v w -> Wequiv u w
-/
inductive Wequiv : q.P.W -> q.P.W -> Prop
  | ind (a : q.P.A) (f f' : q.P.B a -> q.P.W) : (forall x, Wequiv (f x) (f' x)) -> Wequiv ⟨a, f⟩ ⟨a, f'⟩
  | abs (a : q.P.A) (f : q.P.B a -> q.P.W) (a' : q.P.A) (f' : q.P.B a' -> q.P.W) :
      abs ⟨a, f⟩ = abs ⟨a', f'⟩ -> Wequiv ⟨a, f⟩ ⟨a', f'⟩
  | trans (u v w : q.P.W) : Wequiv u v -> Wequiv v w -> Wequiv u w

set_option backward.isDefEq.respectTransparency false in
/--
theorem `recF_eq_of_Wequiv` / 定理 `recF_eq_of_Wequiv`

English:
theorem recF_eq_of_Wequiv
  given: {α : Type u} (u : F α -> α) (x y : q.P.W)
  proof: by
  intro h
  induction h with
  | ind a f f' _ ih => simp only [recF_eq', PFunctor.map_eq, Function.comp_def, ih]
  | abs a f a' f' h => simp only [recF_eq', abs_map, h]
  | trans x y z _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂

中文:
定理 recF_eq_of_Wequiv
  条件: {α : 类型u} (u : F α -> α) (x y : q.P.W)
  证明: by
  intro h
  induction h with
  | ind a f f' _ ih => simp only [recF_eq', PFunctor.map_eq, Function.comp_def, ih]
  | abs a f a' f' h => simp only [recF_eq', abs_map, h]
  | trans x y z _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂

Depends on / 依赖: Eq.trans, Function, Function.comp_def, PFunctor, PFunctor.map_eq, abs_map, comp_def, map_eq, recF_eq
-/
theorem recF_eq_of_Wequiv {α : Type u} (u : F α -> α) (x y : q.P.W) :
    Wequiv x y -> recF u x = recF u y := by
  intro h
  induction h with
  | ind a f f' _ ih => simp only [recF_eq', PFunctor.map_eq, Function.comp_def, ih]
  | abs a f a' f' h => simp only [recF_eq', abs_map, h]
  | trans x y z _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂

/--
theorem `Wequiv.abs'` / 定理 `Wequiv.abs'`

English:
theorem Wequiv.abs'
  given: (x y : q.P.W) (h : QPF.abs x.dest = QPF.abs y.dest)
  statement: Wequiv x y
  proof: by
  cases x
  cases y
  apply Wequiv.abs
  apply h

中文:
定理 Wequiv.abs'
  条件: (x y : q.P.W) (h : QPF.abs x.dest = QPF.abs y.dest)
  结论: Wequiv x y
  证明: by
  cases x
  cases y
  apply Wequiv.abs
  apply h

Depends on / 依赖: Wequiv, Wequiv.abs
-/
theorem Wequiv.abs' (x y : q.P.W) (h : QPF.abs x.dest = QPF.abs y.dest) : Wequiv x y := by
  cases x
  cases y
  apply Wequiv.abs
  apply h

/--
theorem `Wequiv.refl` / 定理 `Wequiv.refl`

English:
theorem Wequiv.refl
  given: (x : q.P.W)
  statement: Wequiv x x
  proof: by
  obtain ⟨a, f⟩ := x
  exact Wequiv.abs a f a f rfl

中文:
定理 Wequiv.refl
  条件: (x : q.P.W)
  结论: Wequiv x x
  证明: by
  obtain ⟨a, f⟩ := x
  exact Wequiv.abs a f a f rfl

Depends on / 依赖: Wequiv, Wequiv.abs
-/
theorem Wequiv.refl (x : q.P.W) : Wequiv x x := by
  obtain ⟨a, f⟩ := x
  exact Wequiv.abs a f a f rfl

/--
theorem `Wequiv.symm` / 定理 `Wequiv.symm`

English:
theorem Wequiv.symm
  given: (x y : q.P.W)
  statement: Wequiv x y -> Wequiv y x
  proof: by
  intro h
  induction h with
  | ind a f f' _ ih => exact Wequiv.ind _ _ _ ih
  | abs a f a' f' h => exact Wequiv.abs _ _ _ _ h.symm
  | trans x y z _ _ ih₁ ih₂ => exact QPF.Wequiv.trans _ _ _ ih₂ ih₁

中文:
定理 Wequiv.symm
  条件: (x y : q.P.W)
  结论: Wequiv x y -> Wequiv y x
  证明: by
  intro h
  induction h with
  | ind a f f' _ ih => exact Wequiv.ind _ _ _ ih
  | abs a f a' f' h => exact Wequiv.abs _ _ _ _ h.symm
  | trans x y z _ _ ih₁ ih₂ => exact QPF.Wequiv.trans _ _ _ ih₂ ih₁

Depends on / 依赖: QPF.Wequiv.trans, Wequiv, Wequiv.abs, Wequiv.ind, h.symm
-/
theorem Wequiv.symm (x y : q.P.W) : Wequiv x y -> Wequiv y x := by
  intro h
  induction h with
  | ind a f f' _ ih => exact Wequiv.ind _ _ _ ih
  | abs a f a' f' h => exact Wequiv.abs _ _ _ _ h.symm
  | trans x y z _ _ ih₁ ih₂ => exact QPF.Wequiv.trans _ _ _ ih₂ ih₁

/--
Definition of `Wrepr` / `Wrepr` 的定义

English:
definition Wrepr
  signature: : q.P.W -> q.P.W
  body: recF (PFunctor.W.mk ∘ repr)

中文:
定义 Wrepr
  签名: : q.P.W -> q.P.W
  定义体: recF (PFunctor.W.mk ∘ repr)

Depends on / 依赖: PFunctor, PFunctor.W.mk
-/
def Wrepr : q.P.W -> q.P.W :=
  recF (PFunctor.W.mk ∘ repr)

/--
theorem `Wrepr_equiv` / 定理 `Wrepr_equiv`

English:
theorem Wrepr_equiv
  given: (x : q.P.W)
  statement: Wequiv (Wrepr x) x
  proof: by
  induction x with | _ a f ih
  apply Wequiv.trans (v := PFunctor.W.mk (q.P.map Wrepr ⟨a, f⟩))
  · apply Wequiv.abs'
    have : Wrepr ⟨a, f⟩ = PFunctor.W.mk (repr (abs (q.P.map Wrepr ⟨a, f⟩))) := rfl
    rw [this]; rw [PFunctor.W.dest_mk]; rw [abs_repr]
    rfl
  apply Wequiv.ind; exact ih

中文:
定理 Wrepr_equiv
  条件: (x : q.P.W)
  结论: Wequiv (Wrepr x) x
  证明: by
  induction x with | _ a f ih
  apply Wequiv.trans (v := PFunctor.W.mk (q.P.map Wrepr ⟨a, f⟩))
  · apply Wequiv.abs'
    have : Wrepr ⟨a, f⟩ = PFunctor.W.mk (repr (abs (q.P.map Wrepr ⟨a, f⟩))) := rfl
    rw [this]; rw [PFunctor.W.dest_mk]; rw [abs_repr]
    rfl
  apply Wequiv.ind; exact ih

Depends on / 依赖: PFunctor, PFunctor.W.dest_mk, PFunctor.W.mk, Wequiv, Wequiv.abs, Wequiv.ind, Wequiv.trans, abs_repr, dest_mk, q.P.map
-/
theorem Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x := by
  induction x with | _ a f ih
  apply Wequiv.trans (v := PFunctor.W.mk (q.P.map Wrepr ⟨a, f⟩))
  · apply Wequiv.abs'
    have : Wrepr ⟨a, f⟩ = PFunctor.W.mk (repr (abs (q.P.map Wrepr ⟨a, f⟩))) := rfl
    rw [this]; rw [PFunctor.W.dest_mk]; rw [abs_repr]
    rfl
  apply Wequiv.ind; exact ih

/-- Define the fixed point as the quotient of trees under the equivalence relation `Wequiv`. -/
@[instance_reducible]
/--
Definition of `Wsetoid` / `Wsetoid` 的定义

English:
definition Wsetoid
  signature: : Setoid q.P.W
  body: ⟨Wequiv, @Wequiv.refl _ _, @Wequiv.symm _ _, @Wequiv.trans _ _⟩

中文:
定义 Wsetoid
  签名: : Setoid q.P.W
  定义体: ⟨Wequiv, @Wequiv.refl _ _, @Wequiv.symm _ _, @Wequiv.trans _ _⟩

Depends on / 依赖: Wequiv, Wequiv.refl, Wequiv.symm, Wequiv.trans
-/
def Wsetoid : Setoid q.P.W :=
  ⟨Wequiv, @Wequiv.refl _ _, @Wequiv.symm _ _, @Wequiv.trans _ _⟩

attribute [local instance] Wsetoid

/--
Definition of `Fix` / `Fix` 的定义

English:
definition Fix
  signature: (F : Type u -> Type u) [q : QPF F]
  body: Quotient (Wsetoid : Setoid q.P.W)

中文:
定义 Fix
  签名: (F : 类型u -> 类型u) [q : QPF F]
  定义体: Quotient (Wsetoid : Setoid q.P.W)

Depends on / 依赖: Quotient, Setoid, Wsetoid, q.P.W
-/
def Fix (F : Type u -> Type u) [q : QPF F] :=
  Quotient (Wsetoid : Setoid q.P.W)

variable {F : Type u -> Type u} [q : QPF F]

/--
Definition of `Fix.rec` / `Fix.rec` 的定义

English:
definition Fix.rec
  signature: {α : Type _} (g : F α -> α)
  body: Quot.lift (recF g) (recF_eq_of_Wequiv g)

中文:
定义 Fix.rec
  签名: {α : Type _} (g : F α -> α)
  定义体: Quot.lift (recF g) (recF_eq_of_Wequiv g)
-/
def Fix.rec {α : Type _} (g : F α -> α) : Fix F -> α :=
  Quot.lift (recF g) (recF_eq_of_Wequiv g)

/--
Definition of `fixToW` / `fixToW` 的定义

English:
definition fixToW
  signature: : Fix F -> q.P.W
  body: Quotient.lift Wrepr (recF_eq_of_Wequiv fun x => @PFunctor.W.mk q.P (repr x))

中文:
定义 fixToW
  签名: : Fix F -> q.P.W
  定义体: Quotient.lift Wrepr (recF_eq_of_Wequiv fun x => @PFunctor.W.mk q.P (repr x))

Depends on / 依赖: PFunctor, PFunctor.W.mk, Quotient, Quotient.lift, recF_eq_of_Wequiv
-/
def fixToW : Fix F -> q.P.W :=
  Quotient.lift Wrepr (recF_eq_of_Wequiv fun x => @PFunctor.W.mk q.P (repr x))

/--
Definition of `Fix.mk` / `Fix.mk` 的定义

English:
definition Fix.mk
  signature: (x : F (Fix F))
  body: Quot.mk _ (PFunctor.W.mk (q.P.map fixToW (repr x)))

中文:
定义 Fix.mk
  签名: (x : F (Fix F))
  定义体: Quot.mk _ (PFunctor.W.mk (q.P.map fixToW (repr x)))
-/
def Fix.mk (x : F (Fix F)) : Fix F :=
  Quot.mk _ (PFunctor.W.mk (q.P.map fixToW (repr x)))

/--
Definition of `Fix.dest` / `Fix.dest` 的定义

English:
definition Fix.dest
  signature: : Fix F -> F (Fix F)
  body: Fix.rec (Functor.map Fix.mk)

中文:
定义 Fix.dest
  签名: : Fix F -> F (Fix F)
  定义体: Fix.rec (Functor.map Fix.mk)
-/
def Fix.dest : Fix F -> F (Fix F) :=
  Fix.rec (Functor.map Fix.mk)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Fix.rec_eq` / 定理 `Fix.rec_eq`

English:
theorem Fix.rec_eq
  given: {α : Type _} (g : F α -> α) (x : F (Fix F))
  proof: by
  have : recF g ∘ fixToW = Fix.rec g := by
    ext ⟨x⟩
    apply recF_eq_of_Wequiv
    rw [fixToW]
    apply Wrepr_equiv
  conv =>
    lhs
    rw [Fix.rec]; rw [Fix.mk]
    dsimp
  rcases h : repr x with ⟨a, f⟩
  rw [PFunctor.map_eq]; rw [recF_eq]; rw [← PFunctor.map_eq]; rw [PFunctor.W.dest_mk];

中文:
定理 Fix.rec_eq
  条件: {α : Type _} (g : F α -> α) (x : F (Fix F))
  证明: by
  have : recF g ∘ fixToW = Fix.rec g := by
    ext ⟨x⟩
    apply recF_eq_of_Wequiv
    rw [fixToW]
    apply Wrepr_equiv
  conv =>
    lhs
    rw [Fix.rec]; rw [Fix.mk]
    dsimp
  rcases h : repr x with ⟨a, f⟩
  rw [PFunctor.map_eq]; rw [recF_eq]; rw [← PFunctor.map_eq]; rw [PFunctor.W.dest_mk];
-/
theorem Fix.rec_eq {α : Type _} (g : F α -> α) (x : F (Fix F)) :
    Fix.rec g (Fix.mk x) = g (Fix.rec g <$> x) := by
  have : recF g ∘ fixToW = Fix.rec g := by
    ext ⟨x⟩
    apply recF_eq_of_Wequiv
    rw [fixToW]
    apply Wrepr_equiv
  conv =>
    lhs
    rw [Fix.rec]; rw [Fix.mk]
    dsimp
  rcases h : repr x with ⟨a, f⟩
  rw [PFunctor.map_eq]; rw [recF_eq]; rw [← PFunctor.map_eq]; rw [PFunctor.W.dest_mk]; rw [PFunctor.map_map]; rw [abs_map]; rw [← h]; rw [abs_repr]; rw [this]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Fix.ind_aux` / 定理 `Fix.ind_aux`

English:
theorem Fix.ind_aux
  given: (a : q.P.A) (f : q.P.B a -> q.P.W)
  proof: by
  have : Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦Wrepr ⟨a, f⟩⟧ := by
    apply Quot.sound; apply Wequiv.abs'
    rw [PFunctor.W.dest_mk]; rw [abs_map]; rw [abs_repr]; rw [← abs_map]; rw [PFunctor.map_eq]
    simp only [Wrepr, recF_eq, PFunctor.W.dest_mk, abs_repr, Function.comp]
    rfl
  rw [this]
 

中文:
定理 Fix.ind_aux
  条件: (a : q.P.A) (f : q.P.B a -> q.P.W)
  证明: by
  have : Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦Wrepr ⟨a, f⟩⟧ := by
    apply Quot.sound; apply Wequiv.abs'
    rw [PFunctor.W.dest_mk]; rw [abs_map]; rw [abs_repr]; rw [← abs_map]; rw [PFunctor.map_eq]
    simp only [Wrepr, recF_eq, PFunctor.W.dest_mk, abs_repr, Function.comp]
    rfl
  rw [this]
 
-/
theorem Fix.ind_aux (a : q.P.A) (f : q.P.B a -> q.P.W) :
    Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦⟨a, f⟩⟧ := by
  have : Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦Wrepr ⟨a, f⟩⟧ := by
    apply Quot.sound; apply Wequiv.abs'
    rw [PFunctor.W.dest_mk]; rw [abs_map]; rw [abs_repr]; rw [← abs_map]; rw [PFunctor.map_eq]
    simp only [Wrepr, recF_eq, PFunctor.W.dest_mk, abs_repr, Function.comp]
    rfl
  rw [this]
  apply Quot.sound
  apply Wrepr_equiv

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Fix.ind_rec` / 定理 `Fix.ind_rec`

English:
theorem Fix.ind_rec
  statement: {α : Type u} (g₁ g₂ : Fix F -> α)
  proof: by
  rintro ⟨x⟩
  induction x with | _ a f ih
  change g₁ ⟦⟨a, f⟩⟧ = g₂ ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]; apply h
  rw [← abs_map]; rw [← abs_map]; rw [PFunctor.map_eq]; rw [PFunctor.map_eq]
  congr 2 with x
  apply ih

中文:
定理 Fix.ind_rec
  结论: {α : 类型u} (g₁ g₂ : Fix F -> α)
  证明: by
  rintro ⟨x⟩
  induction x with | _ a f ih
  change g₁ ⟦⟨a, f⟩⟧ = g₂ ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]; apply h
  rw [← abs_map]; rw [← abs_map]; rw [PFunctor.map_eq]; rw [PFunctor.map_eq]
  congr 2 with x
  apply ih
-/
theorem Fix.ind_rec {α : Type u} (g₁ g₂ : Fix F -> α)
    (h : forall x : F (Fix F), g₁ <$> x = g₂ <$> x -> g₁ (Fix.mk x) = g₂ (Fix.mk x)) :
    forall x, g₁ x = g₂ x := by
  rintro ⟨x⟩
  induction x with | _ a f ih
  change g₁ ⟦⟨a, f⟩⟧ = g₂ ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]; apply h
  rw [← abs_map]; rw [← abs_map]; rw [PFunctor.map_eq]; rw [PFunctor.map_eq]
  congr 2 with x
  apply ih

/--
theorem `Fix.rec_unique` / 定理 `Fix.rec_unique`

English:
theorem Fix.rec_unique
  statement: {α : Type u} (g : F α -> α) (h : Fix F -> α)
  proof: by
  ext x
  apply Fix.ind_rec
  intro x hyp'
  rw [hyp]; rw [← hyp']; rw [Fix.rec_eq]

中文:
定理 Fix.rec_unique
  结论: {α : 类型u} (g : F α -> α) (h : Fix F -> α)
  证明: by
  ext x
  apply Fix.ind_rec
  intro x hyp'
  rw [hyp]; rw [← hyp']; rw [Fix.rec_eq]
-/
theorem Fix.rec_unique {α : Type u} (g : F α -> α) (h : Fix F -> α)
    (hyp : forall x, h (Fix.mk x) = g (h <$> x)) : Fix.rec g = h := by
  ext x
  apply Fix.ind_rec
  intro x hyp'
  rw [hyp]; rw [← hyp']; rw [Fix.rec_eq]

/--
theorem `Fix.mk_dest` / 定理 `Fix.mk_dest`

English:
theorem Fix.mk_dest
  given: (x : Fix F)
  statement: Fix.mk (Fix.dest x) = x
  proof: by
  change (Fix.mk ∘ Fix.dest) x = id x
  apply Fix.ind_rec (mk ∘ dest) id
  intro x
  rw [Function.comp_apply]; rw [id_eq]; rw [Fix.dest]; rw [Fix.rec_eq]; rw [id_map]; rw [comp_map]
  intro h
  rw [h]

中文:
定理 Fix.mk_dest
  条件: (x : Fix F)
  结论: Fix.mk (Fix.dest x) = x
  证明: by
  change (Fix.mk ∘ Fix.dest) x = id x
  apply Fix.ind_rec (mk ∘ dest) id
  intro x
  rw [Function.comp_apply]; rw [id_eq]; rw [Fix.dest]; rw [Fix.rec_eq]; rw [id_map]; rw [comp_map]
  intro h
  rw [h]
-/
theorem Fix.mk_dest (x : Fix F) : Fix.mk (Fix.dest x) = x := by
  change (Fix.mk ∘ Fix.dest) x = id x
  apply Fix.ind_rec (mk ∘ dest) id
  intro x
  rw [Function.comp_apply]; rw [id_eq]; rw [Fix.dest]; rw [Fix.rec_eq]; rw [id_map]; rw [comp_map]
  intro h
  rw [h]

/--
theorem `Fix.dest_mk` / 定理 `Fix.dest_mk`

English:
theorem Fix.dest_mk
  given: (x : F (Fix F))
  statement: Fix.dest (Fix.mk x) = x
  proof: by
  unfold Fix.dest; rw [Fix.rec_eq, ← Fix.dest, ← comp_map]
  conv =>
    rhs
    rw [← id_map x]
  congr with x
  apply Fix.mk_dest

中文:
定理 Fix.dest_mk
  条件: (x : F (Fix F))
  结论: Fix.dest (Fix.mk x) = x
  证明: by
  unfold Fix.dest; rw [Fix.rec_eq, ← Fix.dest, ← comp_map]
  conv =>
    rhs
    rw [← id_map x]
  congr with x
  apply Fix.mk_dest
-/
theorem Fix.dest_mk (x : F (Fix F)) : Fix.dest (Fix.mk x) = x := by
  unfold Fix.dest; rw [Fix.rec_eq, ← Fix.dest, ← comp_map]
  conv =>
    rhs
    rw [← id_map x]
  congr with x
  apply Fix.mk_dest

/--
theorem `Fix.ind` / 定理 `Fix.ind`

English:
theorem Fix.ind
  given: (p : Fix F -> Prop) (h : forall x : F (Fix F), Liftp p x -> p (Fix.mk x))
  statement: forall x, p x
  proof: by
  rintro ⟨x⟩
  induction x with | _ a f ih
  change p ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]
  apply h
  rw [liftp_iff]
  refine ⟨_, _, rfl, ?_⟩
  convert! ih

中文:
定理 Fix.ind
  条件: (p : Fix F -> 命题) (h : 对任意 x : F (Fix F), Liftp p x -> p (Fix.mk x))
  结论: 对任意 x, p x
  证明: by
  rintro ⟨x⟩
  induction x with | _ a f ih
  change p ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]
  apply h
  rw [liftp_iff]
  refine ⟨_, _, rfl, ?_⟩
  convert! ih
-/
theorem Fix.ind (p : Fix F -> Prop) (h : forall x : F (Fix F), Liftp p x -> p (Fix.mk x)) : forall x, p x := by
  rintro ⟨x⟩
  induction x with | _ a f ih
  change p ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]
  apply h
  rw [liftp_iff]
  refine ⟨_, _, rfl, ?_⟩
  convert! ih

end QPF

/-
Construct the final coalgebra to a qpf.
-/
namespace QPF

variable {F : Type u -> Type u} [q : QPF F]

open Functor (Liftp Liftr)

/--
Definition of `corecF` / `corecF` 的定义

English:
definition corecF
  signature: {α : Type _} (g : α -> F α)
  body: PFunctor.M.corec fun x => repr (g x)

中文:
定义 corecF
  签名: {α : Type _} (g : α -> F α)
  定义体: PFunctor.M.corec fun x => repr (g x)

Depends on / 依赖: PFunctor, PFunctor.M.corec
-/
def corecF {α : Type _} (g : α -> F α) : α -> q.P.M :=
  PFunctor.M.corec fun x => repr (g x)

/--
theorem `corecF_eq` / 定理 `corecF_eq`

English:
theorem corecF_eq
  given: {α : Type _} (g : α -> F α) (x : α)
  proof: by
  rw [corecF]; rw [PFunctor.M.dest_corec]

中文:
定理 corecF_eq
  条件: {α : Type _} (g : α -> F α) (x : α)
  证明: by
  rw [corecF]; rw [PFunctor.M.dest_corec]

Depends on / 依赖: PFunctor, PFunctor.M.dest_corec, corecF, dest_corec
-/
theorem corecF_eq {α : Type _} (g : α -> F α) (x : α) :
    PFunctor.M.dest (corecF g x) = q.P.map (corecF g) (repr (g x)) := by
  rw [corecF]; rw [PFunctor.M.dest_corec]

-- Equivalence
/--
Definition of `IsPrecongr` / `IsPrecongr` 的定义

English:
definition IsPrecongr
  signature: (r : q.P.M -> q.P.M -> Prop)
  body: forall ⦃x y⦄, r x y ->
    abs (q.P.map (Quot.mk r) (PFunctor.M.dest x)) = abs (q.P.map (Quot.mk r) (PFunctor.M.dest y))

中文:
定义 IsPrecongr
  签名: (r : q.P.M -> q.P.M -> 命题)
  定义体: forall ⦃x y⦄, r x y ->
    abs (q.P.map (Quot.mk r) (PFunctor.M.dest x)) = abs (q.P.map (Quot.mk r) (PFunctor.M.dest y))

Depends on / 依赖: PFunctor, PFunctor.M.dest, Quot.mk, q.P.map
-/
def IsPrecongr (r : q.P.M -> q.P.M -> Prop) : Prop :=
  forall ⦃x y⦄, r x y ->
    abs (q.P.map (Quot.mk r) (PFunctor.M.dest x)) = abs (q.P.map (Quot.mk r) (PFunctor.M.dest y))

/--
Definition of `Mcongr` / `Mcongr` 的定义

English:
definition Mcongr
  signature: : q.P.M -> q.P.M -> Prop
  body: fun x y => exists r, IsPrecongr r ∧ r x y

中文:
定义 Mcongr
  签名: : q.P.M -> q.P.M -> 命题
  定义体: fun x y => exists r, IsPrecongr r ∧ r x y

Depends on / 依赖: IsPrecongr
-/
def Mcongr : q.P.M -> q.P.M -> Prop := fun x y => exists r, IsPrecongr r ∧ r x y

/--
Definition of `Cofix` / `Cofix` 的定义

English:
definition Cofix
  signature: (F : Type u -> Type u) [q : QPF F]
  body: Quot (@Mcongr F q)

中文:
定义 Cofix
  签名: (F : 类型u -> 类型u) [q : QPF F]
  定义体: Quot (@Mcongr F q)

Depends on / 依赖: Mcongr
-/
def Cofix (F : Type u -> Type u) [q : QPF F] :=
  Quot (@Mcongr F q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: q.P.A] : Inhabited (Cofix F)
  body: ⟨Quot.mk _ default⟩

中文:
实例 [Inhabited
  签名: q.P.A] : Inhabited (Cofix F)
  定义体: ⟨Quot.mk _ default⟩

Depends on / 依赖: Quot.mk
-/
instance [Inhabited q.P.A] : Inhabited (Cofix F) :=
  ⟨Quot.mk _ default⟩

/--
Definition of `Cofix.corec` / `Cofix.corec` 的定义

English:
definition Cofix.corec
  signature: {α : Type _} (g : α -> F α) (x : α)
  body: Quot.mk _ (corecF g x)

中文:
定义 Cofix.corec
  签名: {α : Type _} (g : α -> F α) (x : α)
  定义体: Quot.mk _ (corecF g x)
-/
def Cofix.corec {α : Type _} (g : α -> F α) (x : α) : Cofix F :=
  Quot.mk _ (corecF g x)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Cofix.dest` / `Cofix.dest` 的定义

English:
definition Cofix.dest
  signature: : Cofix F -> F (Cofix F)
  body: Quot.lift (fun x => Quot.mk Mcongr <$> abs (PFunctor.M.dest x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      have : forall x y, r x y -> Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      conv =>
        lhs
        rw [comp_map]; rw [← abs_map

中文:
定义 Cofix.dest
  签名: : Cofix F -> F (Cofix F)
  定义体: Quot.lift (fun x => Quot.mk Mcongr <$> abs (PFunctor.M.dest x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      have : forall x y, r x y -> Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      conv =>
        lhs
        rw [comp_map]; rw [← abs_map
-/
def Cofix.dest : Cofix F -> F (Cofix F) :=
  Quot.lift (fun x => Quot.mk Mcongr <$> abs (PFunctor.M.dest x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      have : forall x y, r x y -> Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      conv =>
        lhs
        rw [comp_map]; rw [← abs_map]; rw [pr rxy]; rw [abs_map]; rw [← comp_map])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Cofix.dest_corec` / 定理 `Cofix.dest_corec`

English:
theorem Cofix.dest_corec
  given: {α : Type u} (g : α -> F α) (x : α)
  proof: by
  conv =>
    lhs
    rw [Cofix.dest]; rw [Cofix.corec]
  dsimp
  rw [corecF_eq]; rw [abs_map]; rw [abs_repr]; rw [← comp_map]; rfl

中文:
定理 Cofix.dest_corec
  条件: {α : 类型u} (g : α -> F α) (x : α)
  证明: by
  conv =>
    lhs
    rw [Cofix.dest]; rw [Cofix.corec]
  dsimp
  rw [corecF_eq]; rw [abs_map]; rw [abs_repr]; rw [← comp_map]; rfl
-/
theorem Cofix.dest_corec {α : Type u} (g : α -> F α) (x : α) :
Cofix.dest (Cofix.corec g x) = Cofix.corec g < > g x := by
  conv =>
    lhs
    rw [Cofix.dest]; rw [Cofix.corec]
  dsimp
  rw [corecF_eq]; rw [abs_map]; rw [abs_repr]; rw [← comp_map]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Cofix.bisim_aux` / 定理 `Cofix.bisim_aux`

English:
theorem Cofix.bisim_aux
  statement: (r : Cofix F -> Cofix F -> Prop) (h' : forall x, r x x)
  proof: by
  rintro ⟨x⟩ ⟨y⟩ rxy
  apply Quot.sound
  let r' x y := r (Quot.mk _ x) (Quot.mk _ y)
  have : IsPrecongr r' := by
    intro a b r'ab
    have h₀ :
Quot.mk r < > Quot.mk Mcongr < > abs (PFunctor.M.dest a) =
Quot.mk r < > Quot.mk Mcongr < > abs (PFunctor.M.dest b) :=
      h _ _ r'ab
    have h₁ :

中文:
定理 Cofix.bisim_aux
  结论: (r : Cofix F -> Cofix F -> 命题) (h' : 对任意 x, r x x)
  证明: by
  rintro ⟨x⟩ ⟨y⟩ rxy
  apply Quot.sound
  let r' x y := r (Quot.mk _ x) (Quot.mk _ y)
  have : IsPrecongr r' := by
    intro a b r'ab
    have h₀ :
Quot.mk r < > Quot.mk Mcongr < > abs (PFunctor.M.dest a) =
Quot.mk r < > Quot.mk Mcongr < > abs (PFunctor.M.dest b) :=
      h _ _ r'ab
    have h₁ :
-/
private theorem Cofix.bisim_aux (r : Cofix F -> Cofix F -> Prop) (h' : forall x, r x x)
    (h : forall x y, r x y -> Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
    forall x y, r x y -> x = y := by
  rintro ⟨x⟩ ⟨y⟩ rxy
  apply Quot.sound
  let r' x y := r (Quot.mk _ x) (Quot.mk _ y)
  have : IsPrecongr r' := by
    intro a b r'ab
    have h₀ :
Quot.mk r < > Quot.mk Mcongr < > abs (PFunctor.M.dest a) =
Quot.mk r < > Quot.mk Mcongr < > abs (PFunctor.M.dest b) :=
      h _ _ r'ab
    have h₁ : forall u v : q.P.M, Mcongr u v -> Quot.mk r' u = Quot.mk r' v := by
      intro u v cuv
      apply Quot.sound
      simp only [r']
      rw [Quot.sound cuv]
      apply h'
    let f : Quot r -> Quot r' :=
Quot.lift (Quot.lift (Quot.mk r') h₁) by
        rintro ⟨c⟩ ⟨d⟩ rcd
        exact Quot.sound rcd
    have : f ∘ Quot.mk r ∘ Quot.mk Mcongr = Quot.mk r' := rfl
    rw [← this]; rw [← PFunctor.map_map _ _ f]; rw [← PFunctor.map_map _ _ (Quot.mk r)]; rw [abs_map]; rw [abs_map]; rw [abs_map]; rw [h₀]
    rw [← PFunctor.map_map _ _ f]; rw [← PFunctor.map_map _ _ (Quot.mk r)]; rw [abs_map]; rw [abs_map]; rw [abs_map]
  exact ⟨r', this, rxy⟩

/--
theorem `Cofix.bisim_rel` / 定理 `Cofix.bisim_rel`

English:
theorem Cofix.bisim_rel
  statement: (r : Cofix F -> Cofix F -> Prop)
  proof: by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply Cofix.bisim_aux r'
  · intro x
    left
    rfl
  · intro x y r'xy
    rcases r'xy with r'xy | r'xy
    · rw [r'xy]
    have : forall x y, r x y -> r' x y := fun x y h => Or.inr h
    rw [← Quot.factor_mk_eq _ _ this]
    dsimp [r']
    rw [

中文:
定理 Cofix.bisim_rel
  结论: (r : Cofix F -> Cofix F -> 命题)
  证明: by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply Cofix.bisim_aux r'
  · intro x
    left
    rfl
  · intro x y r'xy
    rcases r'xy with r'xy | r'xy
    · rw [r'xy]
    have : forall x y, r x y -> r' x y := fun x y h => Or.inr h
    rw [← Quot.factor_mk_eq _ _ this]
    dsimp [r']
    rw [
-/
theorem Cofix.bisim_rel (r : Cofix F -> Cofix F -> Prop)
    (h : forall x y, r x y -> Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
    forall x y, r x y -> x = y := by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply Cofix.bisim_aux r'
  · intro x
    left
    rfl
  · intro x y r'xy
    rcases r'xy with r'xy | r'xy
    · rw [r'xy]
    have : forall x y, r x y -> r' x y := fun x y h => Or.inr h
    rw [← Quot.factor_mk_eq _ _ this]
    dsimp [r']
    rw [@comp_map _ q _ _ _ (Quot.mk r)]; rw [@comp_map _ q _ _ _ (Quot.mk r)]
    rw [h _ _ r'xy]
  right; exact rxy

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Cofix.bisim` / 定理 `Cofix.bisim`

English:
theorem Cofix.bisim
  statement: (r : Cofix F -> Cofix F -> Prop)
  proof: by
  apply Cofix.bisim_rel
  intro x y rxy
  rcases (liftr_iff r _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq]; rw [dyeq]; rw [← abs_map]; rw [← abs_map]; rw [PFunctor.map_eq]; rw [PFunctor.map_eq]
  congr 2 with i
  apply Quot.sound
  apply h'

中文:
定理 Cofix.bisim
  结论: (r : Cofix F -> Cofix F -> 命题)
  证明: by
  apply Cofix.bisim_rel
  intro x y rxy
  rcases (liftr_iff r _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq]; rw [dyeq]; rw [← abs_map]; rw [← abs_map]; rw [PFunctor.map_eq]; rw [PFunctor.map_eq]
  congr 2 with i
  apply Quot.sound
  apply h'
-/
theorem Cofix.bisim (r : Cofix F -> Cofix F -> Prop)
    (h : forall x y, r x y -> Liftr r (Cofix.dest x) (Cofix.dest y)) : forall x y, r x y -> x = y := by
  apply Cofix.bisim_rel
  intro x y rxy
  rcases (liftr_iff r _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq]; rw [dyeq]; rw [← abs_map]; rw [← abs_map]; rw [PFunctor.map_eq]; rw [PFunctor.map_eq]
  congr 2 with i
  apply Quot.sound
  apply h'

/--
theorem `Cofix.bisim'` / 定理 `Cofix.bisim'`

English:
theorem Cofix.bisim'
  statement: {α : Type*} (Q : α -> Prop) (u v : α -> Cofix F)
  proof: fun x Qx =>
  let R := fun w z : Cofix F => exists x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f, f', ux'eq, vx'eq, h'⟩
      rw [liftr_iff]
      exact ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, r

中文:
定理 Cofix.bisim'
  结论: {α : 类型} (Q : α -> 命题) (u v : α -> Cofix F)
  证明: fun x Qx =>
  let R := fun w z : Cofix F => exists x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f, f', ux'eq, vx'eq, h'⟩
      rw [liftr_iff]
      exact ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, r
-/
theorem Cofix.bisim' {α : Type*} (Q : α -> Prop) (u v : α -> Cofix F)
    (h : forall x, Q x -> exists a f f', Cofix.dest (u x) = abs ⟨a, f⟩ ∧ Cofix.dest (v x) = abs ⟨a, f'⟩ ∧
      forall i, exists x', Q x' ∧ f i = u x' ∧ f' i = v x') :
    forall x, Q x -> u x = v x := fun x Qx =>
  let R := fun w z : Cofix F => exists x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f, f', ux'eq, vx'eq, h'⟩
      rw [liftr_iff]
      exact ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩

end QPF

/-
Composition of qpfs.
-/
namespace QPF

variable {F₂ : Type u -> Type u} [q₂ : QPF F₂]
variable {F₁ : Type u -> Type u} [q₁ : QPF F₁]

set_option backward.isDefEq.respectTransparency false in
/-- composition of qpfs gives another qpf -/
@[instance_reducible]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : QPF (Functor.Comp F₂ F₁) where
  body: PFunctor.comp q₂.P q₁.P
  abs {α} := by
    dsimp [Functor.Comp]
    intro p
    exact abs ⟨p.1.1, fun x => abs ⟨p.1.2 x, fun y => p.2 ⟨x, y⟩⟩⟩
  repr {α} := by
    dsimp [Functor.Comp]
    intro y
    refine ⟨⟨(repr y).1, fun u => (repr ((repr y).2 u)).1⟩, ?_⟩
    dsimp [PFunctor.comp]
    intro x


中文:
定义 comp
  签名: : QPF (Functor.Comp F₂ F₁) where
  定义体: PFunctor.comp q₂.P q₁.P
  abs {α} := by
    dsimp [Functor.Comp]
    intro p
    exact abs ⟨p.1.1, fun x => abs ⟨p.1.2 x, fun y => p.2 ⟨x, y⟩⟩⟩
  repr {α} := by
    dsimp [Functor.Comp]
    intro y
    refine ⟨⟨(repr y).1, fun u => (repr ((repr y).2 u)).1⟩, ?_⟩
    dsimp [PFunctor.comp]
    intro x


Depends on / 依赖: PFunctor, PFunctor.comp
-/
def comp : QPF (Functor.Comp F₂ F₁) where
  P := PFunctor.comp q₂.P q₁.P
  abs {α} := by
    dsimp [Functor.Comp]
    intro p
    exact abs ⟨p.1.1, fun x => abs ⟨p.1.2 x, fun y => p.2 ⟨x, y⟩⟩⟩
  repr {α} := by
    dsimp [Functor.Comp]
    intro y
    refine ⟨⟨(repr y).1, fun u => (repr ((repr y).2 u)).1⟩, ?_⟩
    dsimp [PFunctor.comp]
    intro x
    exact (repr ((repr y).2 x.1)).snd x.2
  abs_repr {α} := by
    dsimp [Functor.Comp]
    intro x
    conv =>
      rhs
      rw [← abs_repr x]
    obtain ⟨a, f⟩ := repr x
    dsimp
    congr with x
    rcases h' : repr (f x) with ⟨b, g⟩
    dsimp; rw [← h', abs_repr]
  abs_map {α β} f := by
    dsimp +unfoldPartialApp [Functor.Comp, PFunctor.comp]
    intro p
    obtain ⟨a, g⟩ := p; dsimp
    obtain ⟨b, h⟩ := a; dsimp
    symm
    trans
    · symm
      apply abs_map
    congr
    rw [PFunctor.map_eq]
    dsimp [Function.comp_def]
    congr
    ext x
    rw [← abs_map]
    rfl

end QPF

/-
Quotients.

We show that if `F` is a qpf and `G` is a suitable quotient of `F`, then `G` is a qpf.
-/
namespace QPF

variable {F : Type u -> Type u} [q : QPF F]
variable {G : Type u -> Type u} [Functor G]
variable {FG_abs : forall {α}, F α -> G α}
variable {FG_repr : forall {α}, G α -> F α}

/-- Given a qpf `F` and a well-behaved surjection `FG_abs` from `F α` to
functor `G α`, `G` is a qpf. We can consider `G` a quotient on `F` where
elements `x y : F α` are in the same equivalence class if
`FG_abs x = FG_abs y`. -/
@[instance_reducible]
/--
Definition of `quotientQPF` / `quotientQPF` 的定义

English:
definition quotientQPF
  signature: (FG_abs_repr : forall {α} (x : G α), FG_abs (FG_repr x) = x)
  body: q.P
  abs {_} p := FG_abs (abs p)
  repr {_} x := repr (FG_repr x)
  abs_repr {α} x := by rw [abs_repr, FG_abs_repr]
  abs_map {α β} f x := by rw [abs_map, FG_abs_map]

中文:
定义 quotientQPF
  签名: (FG_abs_repr : 对任意 {α} (x : G α), FG_abs (FG_repr x) = x)
  定义体: q.P
  abs {_} p := FG_abs (abs p)
  repr {_} x := repr (FG_repr x)
  abs_repr {α} x := by rw [abs_repr, FG_abs_repr]
  abs_map {α β} f x := by rw [abs_map, FG_abs_map]
-/
def quotientQPF (FG_abs_repr : forall {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : forall {α β} (f : α -> β) (x : F α), FG_abs (f <$> x) = f <$> FG_abs x) : QPF G where
  P := q.P
  abs {_} p := FG_abs (abs p)
  repr {_} x := repr (FG_repr x)
  abs_repr {α} x := by rw [abs_repr, FG_abs_repr]
  abs_map {α β} f x := by rw [abs_map, FG_abs_map]

end QPF

/-
Support.
-/
namespace QPF

variable {F : Type u -> Type u} [q : QPF F]

open Functor (Liftp Liftr supp)

open Set

/--
theorem `mem_supp` / 定理 `mem_supp`

English:
theorem mem_supp
  given: {α : Type u} (x : F α) (u : α)
  proof: by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : Liftp (fun u => u in f '' univ) x := by
      rw [liftp_iff]
      exact ⟨a, f, haf.symm, fun i => mem_image_of_mem _ (mem_univ _)⟩
    exact h this
  intro h p; rw [liftp_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i,

中文:
定理 mem_supp
  条件: {α : 类型u} (x : F α) (u : α)
  证明: by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : Liftp (fun u => u in f '' univ) x := by
      rw [liftp_iff]
      exact ⟨a, f, haf.symm, fun i => mem_image_of_mem _ (mem_univ _)⟩
    exact h this
  intro h p; rw [liftp_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i,

Depends on / 依赖: haf.symm, liftp_iff, mem_image_of_mem, mem_univ, xeq.symm
-/
theorem mem_supp {α : Type u} (x : F α) (u : α) :
    u in supp x ↔ forall a f, abs ⟨a, f⟩ = x -> u in f '' univ := by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : Liftp (fun u => u in f '' univ) x := by
      rw [liftp_iff]
      exact ⟨a, f, haf.symm, fun i => mem_image_of_mem _ (mem_univ _)⟩
    exact h this
  intro h p; rw [liftp_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  rw [← hi]; apply h'

/--
theorem `supp_eq` / 定理 `supp_eq`

English:
theorem supp_eq
  given: {α : Type u} (x : F α)
  proof: by
  ext
  apply mem_supp

中文:
定理 supp_eq
  条件: {α : 类型u} (x : F α)
  证明: by
  ext
  apply mem_supp

Depends on / 依赖: mem_supp
-/
theorem supp_eq {α : Type u} (x : F α) :
    supp x = { u | forall a f, abs ⟨a, f⟩ = x -> u in f '' univ } := by
  ext
  apply mem_supp

/--
theorem `has_good_supp_iff` / 定理 `has_good_supp_iff`

English:
theorem has_good_supp_iff
  given: {α : Type u} (x : F α)
  proof: by
  constructor
  · intro h
    have : Liftp (· in supp x) x := by rw [h]; intro u; exact id
    rw [liftp_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine ⟨a, f, xeq.symm, ?_⟩
    intro a' f' h''
    rintro u ⟨i, _, hfi⟩
    have : u in supp x := by rw [← hfi]; apply h'
    exact (mem_

中文:
定理 has_good_supp_iff
  条件: {α : 类型u} (x : F α)
  证明: by
  constructor
  · intro h
    have : Liftp (· in supp x) x := by rw [h]; intro u; exact id
    rw [liftp_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine ⟨a, f, xeq.symm, ?_⟩
    intro a' f' h''
    rintro u ⟨i, _, hfi⟩
    have : u in supp x := by rw [← hfi]; apply h'
    exact (mem_

Depends on / 依赖: liftp_iff, mem_supp, usuppx, xeq.symm
-/
theorem has_good_supp_iff {α : Type u} (x : F α) :
    (forall p, Liftp p x ↔ forall u in supp x, p u) ↔
      exists a f, abs ⟨a, f⟩ = x ∧ forall a' f', abs ⟨a', f'⟩ = x -> f '' univ subseteq f' '' univ := by
  constructor
  · intro h
    have : Liftp (· in supp x) x := by rw [h]; intro u; exact id
    rw [liftp_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine ⟨a, f, xeq.symm, ?_⟩
    intro a' f' h''
    rintro u ⟨i, _, hfi⟩
    have : u in supp x := by rw [← hfi]; apply h'
    exact (mem_supp x u).mp this _ _ h''
  rintro ⟨a, f, xeq, h⟩ p; rw [liftp_iff]; constructor
  · rintro ⟨a', f', xeq', h'⟩ u usuppx
    rcases (mem_supp x u).mp usuppx a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    rw [← f'ieq]
    apply h'
  intro h'
  refine ⟨a, f, xeq.symm, ?_⟩; intro i
  apply h'; rw [mem_supp]
  intro a' f' xeq'
  apply h a' f' xeq'
  apply mem_image_of_mem _ (mem_univ _)

/--
Definition of `IsUniform` / `IsUniform` 的定义

English:
definition IsUniform
  signature: : Prop
  body: forall ⦃α : Type u⦄ (a a' : q.P.A) (f : q.P.B a -> α) (f' : q.P.B a' -> α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ -> f '' univ = f' '' univ

中文:
定义 IsUniform
  签名: : 命题
  定义体: forall ⦃α : Type u⦄ (a a' : q.P.A) (f : q.P.B a -> α) (f' : q.P.B a' -> α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ -> f '' univ = f' '' univ

Depends on / 依赖: q.P.A, q.P.B
-/
def IsUniform : Prop :=
  forall ⦃α : Type u⦄ (a a' : q.P.A) (f : q.P.B a -> α) (f' : q.P.B a' -> α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ -> f '' univ = f' '' univ

/--
Definition of `LiftpPreservation` / `LiftpPreservation` 的定义

English:
definition LiftpPreservation
  signature: : Prop
  body: forall ⦃α⦄ (p : α -> Prop) (x : q.P α), Liftp p (abs x) ↔ Liftp p x

中文:
定义 LiftpPreservation
  签名: : 命题
  定义体: forall ⦃α⦄ (p : α -> Prop) (x : q.P α), Liftp p (abs x) ↔ Liftp p x
-/
def LiftpPreservation : Prop :=
  forall ⦃α⦄ (p : α -> Prop) (x : q.P α), Liftp p (abs x) ↔ Liftp p x

/--
Definition of `SuppPreservation` / `SuppPreservation` 的定义

English:
definition SuppPreservation
  signature: : Prop
  body: forall ⦃α⦄ (x : q.P α), supp (abs x) = supp x

中文:
定义 SuppPreservation
  签名: : 命题
  定义体: forall ⦃α⦄ (x : q.P α), supp (abs x) = supp x
-/
def SuppPreservation : Prop :=
  forall ⦃α⦄ (x : q.P α), supp (abs x) = supp x

/--
theorem `supp_eq_of_isUniform` / 定理 `supp_eq_of_isUniform`

English:
theorem supp_eq_of_isUniform
  given: (h : q.IsUniform) {α : Type u} (a : q.P.A) (f : q.P.B a -> α)
  proof: by
  ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'

中文:
定理 supp_eq_of_isUniform
  条件: (h : q.IsUniform) {α : 类型u} (a : q.P.A) (f : q.P.B a -> α)
  证明: by
  ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'

Depends on / 依赖: e.symm, mem_supp
-/
theorem supp_eq_of_isUniform (h : q.IsUniform) {α : Type u} (a : q.P.A) (f : q.P.B a -> α) :
    supp (abs ⟨a, f⟩) = f '' univ := by
  ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'

/--
theorem `liftp_iff_of_isUniform` / 定理 `liftp_iff_of_isUniform`

English:
theorem liftp_iff_of_isUniform
  given: (h : q.IsUniform) {α : Type u} (x : F α) (p : α -> Prop)
  proof: by
  rw [liftp_iff]; rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h]; rw [h _ _ _ _ abseq]
    rintro ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine ⟨a, f, rfl, fun i => h' _ ?_⟩
  rw [supp_eq_of_isUniform h]
  exac

中文:
定理 liftp_iff_of_isUniform
  条件: (h : q.IsUniform) {α : 类型u} (x : F α) (p : α -> 命题)
  证明: by
  rw [liftp_iff]; rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h]; rw [h _ _ _ _ abseq]
    rintro ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine ⟨a, f, rfl, fun i => h' _ ?_⟩
  rw [supp_eq_of_isUniform h]
  exac

Depends on / 依赖: abs_repr, liftp_iff, mem_univ, supp_eq_of_isUniform
-/
theorem liftp_iff_of_isUniform (h : q.IsUniform) {α : Type u} (x : F α) (p : α -> Prop) :
    Liftp p x ↔ forall u in supp x, p u := by
  rw [liftp_iff]; rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h]; rw [h _ _ _ _ abseq]
    rintro ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine ⟨a, f, rfl, fun i => h' _ ?_⟩
  rw [supp_eq_of_isUniform h]
  exact ⟨i, mem_univ i, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `supp_map` / 定理 `supp_map`

English:
theorem supp_map
  given: (h : q.IsUniform) {α β : Type u} (g : α -> β) (x : F α)
  proof: by
  rw [← abs_repr x]; obtain ⟨a, f⟩ := repr x; rw [← abs_map, PFunctor.map_eq]
  rw [supp_eq_of_isUniform h]; rw [supp_eq_of_isUniform h]; rw [image_comp]

中文:
定理 supp_map
  条件: (h : q.IsUniform) {α β : 类型u} (g : α -> β) (x : F α)
  证明: by
  rw [← abs_repr x]; obtain ⟨a, f⟩ := repr x; rw [← abs_map, PFunctor.map_eq]
  rw [supp_eq_of_isUniform h]; rw [supp_eq_of_isUniform h]; rw [image_comp]

Depends on / 依赖: PFunctor, PFunctor.map_eq, abs_map, abs_repr, image_comp, map_eq, supp_eq_of_isUniform
-/
theorem supp_map (h : q.IsUniform) {α β : Type u} (g : α -> β) (x : F α) :
    supp (g <$> x) = g '' supp x := by
  rw [← abs_repr x]; obtain ⟨a, f⟩ := repr x; rw [← abs_map, PFunctor.map_eq]
  rw [supp_eq_of_isUniform h]; rw [supp_eq_of_isUniform h]; rw [image_comp]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `suppPreservation_iff_uniform` / 定理 `suppPreservation_iff_uniform`

English:
theorem suppPreservation_iff_uniform
  statement: q.SuppPreservation ↔ q.IsUniform
  proof: by
  constructor
  · intro h α a a' f f' h'
    rw [← PFunctor.supp_eq]; rw [← PFunctor.supp_eq]; rw [← h]; rw [h']; rw [h]
  · rintro h α ⟨a, f⟩
    rwa [supp_eq_of_isUniform, PFunctor.supp_eq]

中文:
定理 suppPreservation_iff_uniform
  结论: q.SuppPreservation ↔ q.IsUniform
  证明: by
  constructor
  · intro h α a a' f f' h'
    rw [← PFunctor.supp_eq]; rw [← PFunctor.supp_eq]; rw [← h]; rw [h']; rw [h]
  · rintro h α ⟨a, f⟩
    rwa [supp_eq_of_isUniform, PFunctor.supp_eq]

Depends on / 依赖: PFunctor, PFunctor.supp_eq, supp_eq, supp_eq_of_isUniform
-/
theorem suppPreservation_iff_uniform : q.SuppPreservation ↔ q.IsUniform := by
  constructor
  · intro h α a a' f f' h'
    rw [← PFunctor.supp_eq]; rw [← PFunctor.supp_eq]; rw [← h]; rw [h']; rw [h]
  · rintro h α ⟨a, f⟩
    rwa [supp_eq_of_isUniform, PFunctor.supp_eq]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `suppPreservation_iff_liftpPreservation` / 定理 `suppPreservation_iff_liftpPreservation`

English:
theorem suppPreservation_iff_liftpPreservation
  statement: q.SuppPreservation ↔ q.LiftpPreservation
  proof: by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [suppPreservation_iff_uniform] at h'
    dsimp only [SuppPreservation, supp] at h
    rw [liftp_iff_of_isUniform h']; rw [supp_eq_of_isUniform h']; rw [PFunctor.liftp_iff']
    simp
  · rintro α ⟨a, f⟩
    simp only [LiftpPre

中文:
定理 suppPreservation_iff_liftpPreservation
  结论: q.SuppPreservation ↔ q.LiftpPreservation
  证明: by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [suppPreservation_iff_uniform] at h'
    dsimp only [SuppPreservation, supp] at h
    rw [liftp_iff_of_isUniform h']; rw [supp_eq_of_isUniform h']; rw [PFunctor.liftp_iff']
    simp
  · rintro α ⟨a, f⟩
    simp only [LiftpPre

Depends on / 依赖: LiftpPreservation, PFunctor, PFunctor.liftp_iff, SuppPreservation, liftp_iff, liftp_iff_of_isUniform, suppPreservation_iff_uniform, supp_eq_of_isUniform
-/
theorem suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftpPreservation := by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [suppPreservation_iff_uniform] at h'
    dsimp only [SuppPreservation, supp] at h
    rw [liftp_iff_of_isUniform h']; rw [supp_eq_of_isUniform h']; rw [PFunctor.liftp_iff']
    simp
  · rintro α ⟨a, f⟩
    simp only [LiftpPreservation] at h
    simp only [supp, h]

/--
theorem `liftpPreservation_iff_uniform` / 定理 `liftpPreservation_iff_uniform`

English:
theorem liftpPreservation_iff_uniform
  statement: q.LiftpPreservation ↔ q.IsUniform
  proof: by
  rw [← suppPreservation_iff_liftpPreservation]; rw [suppPreservation_iff_uniform]

中文:
定理 liftpPreservation_iff_uniform
  结论: q.LiftpPreservation ↔ q.IsUniform
  证明: by
  rw [← suppPreservation_iff_liftpPreservation]; rw [suppPreservation_iff_uniform]

Depends on / 依赖: suppPreservation_iff_liftpPreservation, suppPreservation_iff_uniform
-/
theorem liftpPreservation_iff_uniform : q.LiftpPreservation ↔ q.IsUniform := by
  rw [← suppPreservation_iff_liftpPreservation]; rw [suppPreservation_iff_uniform]

end QPF
