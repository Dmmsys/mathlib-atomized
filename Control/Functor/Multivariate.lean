/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import Mathlib.Data.Fin.Fin2
public import Mathlib.Data.TypeVec
public import Mathlib.Logic.Equiv.Defs

/-!

# Functors between the category of tuples of types, and the category Type

Features:

* `MvFunctor n` : the type class of multivariate functors
* `f <$$> x` : notation for map

-/

@[expose] public section


universe u v w

open MvFunctor

/--
Definition of `MvFunctor` / `MvFunctor` 的定义

English:
class MvFunctor
  parameters: {n : Nat} (F : TypeVec n -> Type*)
  axioms and operations (1):
    - map : forall {α β : TypeVec n}, α ⟹ β -> F α -> F β

中文:
类 MvFunctor
  参数: {n : 自然数} (F : TypeVec n -> 类型)
  公理与运算 (1 个):
    - map : 对任意 {α β : TypeVec n}, α ⟹ β -> F α -> F β
-/
class MvFunctor {n : Nat} (F : TypeVec n -> Type*) where
  /-- Multivariate map, if `f : α ⟹ β` and `x : F α` then `f <$$> x : F β`. -/
  map : forall {α β : TypeVec n}, α ⟹ β -> F α -> F β

/-- Multivariate map, if `f : α ⟹ β` and `x : F α` then `f <$$> x : F β` -/
scoped[MvFunctor] infixr:100 " < > " => MvFunctor.map

variable {n : Nat}

namespace MvFunctor

variable {α β : TypeVec.{u} n} {F : TypeVec.{u} n -> Type v} [MvFunctor F]

/--
Definition of `LiftP` / `LiftP` 的定义

English:
definition LiftP
  signature: {α : TypeVec n} (P : forall i, α i -> Prop) (x : F α)
  body: exists u : F (fun i => Subtype (P i)), (fun i => @Subtype.val _ (P i)) < > u = x

中文:
定义 LiftP
  签名: {α : TypeVec n} (P : 对任意 i, α i -> 命题) (x : F α)
  定义体: exists u : F (fun i => Subtype (P i)), (fun i => @Subtype.val _ (P i)) < > u = x

Depends on / 依赖: Subtype, Subtype.val
-/
def LiftP {α : TypeVec n} (P : forall i, α i -> Prop) (x : F α) : Prop :=
exists u : F (fun i => Subtype (P i)), (fun i => @Subtype.val _ (P i)) < > u = x

/--
Definition of `LiftR` / `LiftR` 的定义

English:
definition LiftR
  signature: {α : TypeVec n} (R : forall ⦃i⦄, α i -> α i -> Prop) (x y : F α)
  body: exists u : F (fun i => { p : α i × α i // R p.fst p.snd }),
(fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.fst) < > u = x ∧
(fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.snd) < > u = y

中文:
定义 LiftR
  签名: {α : TypeVec n} (R : 对任意 ⦃i⦄, α i -> α i -> 命题) (x y : F α)
  定义体: exists u : F (fun i => { p : α i × α i // R p.fst p.snd }),
(fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.fst) < > u = x ∧
(fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.snd) < > u = y

Depends on / 依赖: p.fst, p.snd, t.val.fst, t.val.snd
-/
def LiftR {α : TypeVec n} (R : forall ⦃i⦄, α i -> α i -> Prop) (x y : F α) : Prop :=
  exists u : F (fun i => { p : α i × α i // R p.fst p.snd }),
(fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.fst) < > u = x ∧
(fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.snd) < > u = y

/--
Definition of `supp` / `supp` 的定义

English:
definition supp
  signature: {α : TypeVec n} (x : F α) (i : Fin2 n)
  body: { y : α i | forall ⦃P⦄, LiftP P x -> P i y }

中文:
定义 supp
  签名: {α : TypeVec n} (x : F α) (i : Fin2 n)
  定义体: { y : α i | forall ⦃P⦄, LiftP P x -> P i y }
-/
def supp {α : TypeVec n} (x : F α) (i : Fin2 n) : Set (α i) :=
  { y : α i | forall ⦃P⦄, LiftP P x -> P i y }

/--
theorem `of_mem_supp` / 定理 `of_mem_supp`

English:
theorem of_mem_supp
  given: {α : TypeVec n} {x : F α} {P : forall ⦃i⦄, α i -> Prop} (h : LiftP P x) (i : Fin2 n)
  proof: fun _y hy => hy h

中文:
定理 of_mem_supp
  条件: {α : TypeVec n} {x : F α} {P : 对任意 ⦃i⦄, α i -> 命题} (h : LiftP P x) (i : Fin2 n)
  证明: fun _y hy => hy h
-/
theorem of_mem_supp {α : TypeVec n} {x : F α} {P : forall ⦃i⦄, α i -> Prop} (h : LiftP P x) (i : Fin2 n) :
    forall y in supp x i, P y := fun _y hy => hy h

end MvFunctor



/--
Definition of `LawfulMvFunctor` / `LawfulMvFunctor` 的定义

English:
class LawfulMvFunctor
  parameters: {n : Nat} (F : TypeVec n -> Type*) [MvFunctor F]
  axioms and operations (2):
    - id_map : forall {α : TypeVec n} (x : F α), TypeVec.id < > x = x comp_map :
    - forall : {α β γ : TypeVec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α), (h ⊚ g) < > x = h < > g < > x

中文:
类 LawfulMvFunctor
  参数: {n : 自然数} (F : TypeVec n -> 类型) [MvFunctor F]
  公理与运算 (2 个):
    - id_map : 对任意 {α : TypeVec n} (x : F α), TypeVec.id < > x = x comp_map :
    - forall : {α β γ : TypeVec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α), (h ⊚ g) < > x = h < > g < > x
-/
class LawfulMvFunctor {n : Nat} (F : TypeVec n -> Type*) [MvFunctor F] : Prop where
  /-- `map` preserved identities, i.e., maps identity on `α` to identity on `F α` -/
id_map : forall {α : TypeVec n} (x : F α), TypeVec.id < > x = x
  /-- `map` preserves compositions -/
  comp_map :
forall {α β γ : TypeVec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α), (h ⊚ g) < > x = h < > g < > x

open Nat TypeVec

namespace MvFunctor

export LawfulMvFunctor (comp_map)

open LawfulMvFunctor

variable {α β γ : TypeVec.{u} n}
variable {F : TypeVec.{u} n -> Type v} [MvFunctor F]
variable (P : α ⟹ «repeat» n Prop) (R : α otimes α ⟹ «repeat» n Prop)

/--
Definition of `LiftP'` / `LiftP'` 的定义

English:
definition LiftP'
  signature: : F α -> Prop
  body: MvFunctor.LiftP fun i x => ofRepeat P i x

中文:
定义 LiftP'
  签名: : F α -> 命题
  定义体: MvFunctor.LiftP fun i x => ofRepeat P i x

Depends on / 依赖: MvFunctor, MvFunctor.LiftP, ofRepeat
-/
def LiftP' : F α -> Prop :=
MvFunctor.LiftP fun i x => ofRepeat P i x


/--
Definition of `LiftR'` / `LiftR'` 的定义

English:
definition LiftR'
  signature: : F α -> F α -> Prop
  body: MvFunctor.LiftR @fun i x y => ofRepeat R i TypeVec.prod.mk _ x y

中文:
定义 LiftR'
  签名: : F α -> F α -> 命题
  定义体: MvFunctor.LiftR @fun i x y => ofRepeat R i TypeVec.prod.mk _ x y

Depends on / 依赖: MvFunctor, MvFunctor.LiftR, TypeVec, TypeVec.prod.mk, ofRepeat
-/
def LiftR' : F α -> F α -> Prop :=
MvFunctor.LiftR @fun i x y => ofRepeat R i TypeVec.prod.mk _ x y

variable [LawfulMvFunctor F]

@[simp]
/--
theorem `id_map` / 定理 `id_map`

English:
theorem id_map
  given: (x : F α)
  statement: TypeVec.id < > x = x
  proof: LawfulMvFunctor.id_map x

@[simp]

中文:
定理 id_map
  条件: (x : F α)
  结论: TypeVec.id < > x = x
  证明: LawfulMvFunctor.id_map x

@[simp]

Depends on / 依赖: LawfulMvFunctor, LawfulMvFunctor.id_map, id_map
-/
theorem id_map (x : F α) : TypeVec.id < > x = x :=
  LawfulMvFunctor.id_map x

@[simp]
/--
theorem `id_map'` / 定理 `id_map'`

English:
theorem id_map'
  given: (x : F α)
  statement: (fun _i a => a) < > x = x
  proof: id_map x

中文:
定理 id_map'
  条件: (x : F α)
  结论: (fun _i a => a) < > x = x
  证明: id_map x

Depends on / 依赖: id_map
-/
theorem id_map' (x : F α) : (fun _i a => a) < > x = x :=
  id_map x

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : α ⟹ β) (h : β ⟹ γ) (x : F α)
  statement: h < > g < > x = (h ⊚ g) < > x
  proof: Eq.symm comp_map _ _ _

中文:
定理 map_map
  条件: (g : α ⟹ β) (h : β ⟹ γ) (x : F α)
  结论: h < > g < > x = (h ⊚ g) < > x
  证明: Eq.symm comp_map _ _ _

Depends on / 依赖: Eq.symm, comp_map
-/
theorem map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h < > g < > x = (h ⊚ g) < > x :=
Eq.symm comp_map _ _ _

section LiftP'

variable (F) in
/--
theorem `exists_iff_exists_of_mono` / 定理 `exists_iff_exists_of_mono`

English:
theorem exists_iff_exists_of_mono
  statement: {P : F α -> Prop} {q : F β -> Prop}
  proof: by
  constructor <;> rintro ⟨u, h₂⟩
· refine ⟨f < > u, ?_⟩
    apply (h₁ u).mp h₂
· refine ⟨g < > u, ?_⟩
    rw [h₁]
    simp only [MvFunctor.map_map, h₀, LawfulMvFunctor.id_map, h₂]

中文:
定理 exists_iff_exists_of_mono
  结论: {P : F α -> 命题} {q : F β -> 命题}
  证明: by
  constructor <;> rintro ⟨u, h₂⟩
· refine ⟨f < > u, ?_⟩
    apply (h₁ u).mp h₂
· refine ⟨g < > u, ?_⟩
    rw [h₁]
    simp only [MvFunctor.map_map, h₀, LawfulMvFunctor.id_map, h₂]

Depends on / 依赖: LawfulMvFunctor, LawfulMvFunctor.id_map, MvFunctor, MvFunctor.map_map, id_map, map_map
-/
theorem exists_iff_exists_of_mono {P : F α -> Prop} {q : F β -> Prop}
    (f : α ⟹ β) (g : β ⟹ α)
    (h₀ : f ⊚ g = TypeVec.id)
    (h₁ : forall u : F α, P u ↔ q (f <$$> u)) :
    (exists u : F α, P u) ↔ exists u : F β, q u := by
  constructor <;> rintro ⟨u, h₂⟩
· refine ⟨f < > u, ?_⟩
    apply (h₁ u).mp h₂
· refine ⟨g < > u, ?_⟩
    rw [h₁]
    simp only [MvFunctor.map_map, h₀, LawfulMvFunctor.id_map, h₂]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LiftP_def` / 定理 `LiftP_def`

English:
theorem LiftP_def
  given: (x : F α)
  statement: LiftP' P x ↔ exists u : F (Subtype_ P), subtypeVal P < > u = x
  proof: exists_iff_exists_of_mono F _ _ (toSubtype_of_subtype P) (by simp [MvFunctor.map_map])

中文:
定理 LiftP_def
  条件: (x : F α)
  结论: LiftP' P x ↔ 存在 u : F (Subtype_ P), subtypeVal P < > u = x
  证明: exists_iff_exists_of_mono F _ _ (toSubtype_of_subtype P) (by simp [MvFunctor.map_map])

Depends on / 依赖: MvFunctor, MvFunctor.map_map, exists_iff_exists_of_mono, map_map, toSubtype_of_subtype
-/
theorem LiftP_def (x : F α) : LiftP' P x ↔ exists u : F (Subtype_ P), subtypeVal P < > u = x :=
  exists_iff_exists_of_mono F _ _ (toSubtype_of_subtype P) (by simp [MvFunctor.map_map])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LiftR_def` / 定理 `LiftR_def`

English:
theorem LiftR_def
  given: (x y : F α)
  proof: exists_iff_exists_of_mono _ _ _ (toSubtype'_of_subtype' R) (by
    simp only [map_map, comp_assoc, subtypeVal_toSubtype']
    simp +unfoldPartialApp [comp])

中文:
定理 LiftR_def
  条件: (x y : F α)
  证明: exists_iff_exists_of_mono _ _ _ (toSubtype'_of_subtype' R) (by
    simp only [map_map, comp_assoc, subtypeVal_toSubtype']
    simp +unfoldPartialApp [comp])

Depends on / 依赖: _of_subtype, comp_assoc, exists_iff_exists_of_mono, map_map, subtypeVal_toSubtype, toSubtype, unfoldPartialApp
-/
theorem LiftR_def (x y : F α) :
    LiftR' R x y ↔
      exists u : F (Subtype_ R),
(TypeVec.prod.fst ⊚ subtypeVal R) < > u = x ∧
(TypeVec.prod.snd ⊚ subtypeVal R) < > u = y :=
  exists_iff_exists_of_mono _ _ _ (toSubtype'_of_subtype' R) (by
    simp only [map_map, comp_assoc, subtypeVal_toSubtype']
    simp +unfoldPartialApp [comp])

end LiftP'

end MvFunctor

namespace MvFunctor

section LiftPLastPredIff

variable {F : TypeVec.{u} (n + 1) -> Type*} [MvFunctor F] [LawfulMvFunctor F] {α : TypeVec.{u} n}

variable {β : Type u}
variable (pp : β -> Prop)

/--
Definition of `f` / `f` 的定义

English:
definition f
  signature: :

中文:
定义 f
  签名: :
-/
private def f :
    forall n α,
      (fun i : Fin2 (n + 1) => { p_1 // ofRepeat (PredLast' α pp i p_1) }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 : (α ::: β) i // PredLast α pp p_1 }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by grind [PredLast]) x.property⟩
  | _, _, Fin2.fz, x => ⟨x.val, x.property⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `g` / `g` 的定义

English:
definition g
  signature: :

中文:
定义 g
  签名: :
-/
private def g :
    forall n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i // PredLast α pp p_1 }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 // ofRepeat (PredLast' α pp i p_1) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [PredLast]; erw [const_iff_true]) x.property⟩
  | _, _, Fin2.fz, x => ⟨x.val, x.property⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LiftP_PredLast_iff` / 定理 `LiftP_PredLast_iff`

English:
theorem LiftP_PredLast_iff
  given: {β} (P : β -> Prop) (x : F (α ::: β))
  proof: by
  dsimp only [LiftP, LiftP']
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α)
  · ext i ⟨x, _⟩
    cases i <;> rfl
  · intros
    rw [MvFunctor.map_map]
    dsimp +unfoldPartialApp [(· ⊚ ·)]
    suffices (fun i => Subtype.val) = (fun i x => (MvFunctor.f P n α i x).val) by rw [this]
    ext

中文:
定理 LiftP_PredLast_iff
  条件: {β} (P : β -> 命题) (x : F (α ::: β))
  证明: by
  dsimp only [LiftP, LiftP']
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α)
  · ext i ⟨x, _⟩
    cases i <;> rfl
  · intros
    rw [MvFunctor.map_map]
    dsimp +unfoldPartialApp [(· ⊚ ·)]
    suffices (fun i => Subtype.val) = (fun i x => (MvFunctor.f P n α i x).val) by rw [this]
    ext

Depends on / 依赖: MvFunctor, MvFunctor.f, MvFunctor.map_map, Subtype, Subtype.val, exists_iff_exists_of_mono, intros, map_map, unfoldPartialApp
-/
theorem LiftP_PredLast_iff {β} (P : β -> Prop) (x : F (α ::: β)) :
    LiftP' (PredLast' _ P) x ↔ LiftP (PredLast _ P) x := by
  dsimp only [LiftP, LiftP']
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α)
  · ext i ⟨x, _⟩
    cases i <;> rfl
  · intros
    rw [MvFunctor.map_map]
    dsimp +unfoldPartialApp [(· ⊚ ·)]
    suffices (fun i => Subtype.val) = (fun i x => (MvFunctor.f P n α i x).val) by rw [this]
    ext i ⟨x, _⟩
    cases i <;> rfl

variable (rr : β -> β -> Prop)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `f'` / `f'` 的定义

English:
definition f'
  signature: :

中文:
定义 f'
  签名: :
-/
private def f' :
    forall n α,
      (fun i : Fin2 (n + 1) =>
          { p_1 : _ × _ // ofRepeat (RelLast' α rr i (TypeVec.prod.mk _ p_1.fst p_1.snd)) }) ⟹
        fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [RelLast]; erw [repeatEq_iff_eq]) x.property⟩
  | _, _, Fin2.fz, x => ⟨x.val, x.property⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `g'` / `g'` 的定义

English:
definition g'
  signature: :

中文:
定义 g'
  签名: :
-/
private def g' :
    forall n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }) ⟹
        fun i : Fin2 (n + 1) =>
        { p_1 : _ × _ // ofRepeat (RelLast' α rr i (TypeVec.prod.mk _ p_1.1 p_1.2)) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [RelLast]; erw [repeatEq_iff_eq]) x.property⟩
  | _, _, Fin2.fz, x => ⟨x.val, x.property⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LiftR_RelLast_iff` / 定理 `LiftR_RelLast_iff`

English:
theorem LiftR_RelLast_iff
  given: (x y : F (α ::: β))
  proof: by
  dsimp only [LiftR, LiftR']
  apply exists_iff_exists_of_mono F (f' rr _ _) (g' rr _ _)
  · ext i ⟨x, _⟩ : 2
    cases i <;> rfl
  · intros
    simp +unfoldPartialApp only [map_map, TypeVec.comp]
    apply iff_of_eq -- Switch to `eq` so we can use `ext`
    congr <;> ext i ⟨x, _⟩ <;> cases i <;>

中文:
定理 LiftR_RelLast_iff
  条件: (x y : F (α ::: β))
  证明: by
  dsimp only [LiftR, LiftR']
  apply exists_iff_exists_of_mono F (f' rr _ _) (g' rr _ _)
  · ext i ⟨x, _⟩ : 2
    cases i <;> rfl
  · intros
    simp +unfoldPartialApp only [map_map, TypeVec.comp]
    apply iff_of_eq -- Switch to `eq` so we can use `ext`
    congr <;> ext i ⟨x, _⟩ <;> cases i <;>

Depends on / 依赖: Switch, TypeVec, TypeVec.comp, exists_iff_exists_of_mono, iff_of_eq, intros, map_map, unfoldPartialApp
-/
theorem LiftR_RelLast_iff (x y : F (α ::: β)) :
    LiftR' (RelLast' _ rr) x y ↔ LiftR (RelLast _ rr) x y := by
  dsimp only [LiftR, LiftR']
  apply exists_iff_exists_of_mono F (f' rr _ _) (g' rr _ _)
  · ext i ⟨x, _⟩ : 2
    cases i <;> rfl
  · intros
    simp +unfoldPartialApp only [map_map, TypeVec.comp]
    apply iff_of_eq -- Switch to `eq` so we can use `ext`
    congr <;> ext i ⟨x, _⟩ <;> cases i <;> rfl

end LiftPLastPredIff

/-- Any type function that is (extensionally) equivalent to a functor, is itself a functor -/
@[instance_reducible]
/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: {F F' : TypeVec.{u} n -> Type*} [MvFunctor F'] (eqv : forall α, F α ≃ F' α)
  body: (eqv _).symm f < > eqv _ x

中文:
定义 ofEquiv
  签名: {F F' : TypeVec.{u} n -> 类型} [MvFunctor F'] (eqv : 对任意 α, F α ≃ F' α)
  定义体: (eqv _).symm f < > eqv _ x
-/
def ofEquiv {F F' : TypeVec.{u} n -> Type*} [MvFunctor F'] (eqv : forall α, F α ≃ F' α) :
    MvFunctor F where
map f x := (eqv _).symm f < > eqv _ x

end MvFunctor
