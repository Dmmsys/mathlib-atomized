/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.W.Basic

/-!
# Polynomial Functors

This file defines polynomial functors and the W-type construction as a polynomial functor.
(For the M-type construction, see `Mathlib/Data/PFunctor/Univariate/M.lean`.)
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ v₁ v₂ v₃

-- Note: `set_option linter.checkUnivs` should not apply here,
-- we really do want two separate universe levels
set_option linter.checkUnivs false in
/-- A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/
@[pp_with_univ]
/--
Definition of `PFunctor` / `PFunctor` 的定义

English:
structure PFunctor
  parameters: where
  axioms and operations (2):
    - A : Type uA
    - B : A -> Type uB

中文:
结构 PFunctor
  参数: where
  公理与运算 (2 个):
    - A : 类型uA
    - B : A -> 类型uB
-/
structure PFunctor where
  /-- The head type -/
  A : Type uA
  /-- The child family of types -/
  B : A -> Type uB

namespace PFunctor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited PFunctor
  body: ⟨⟨default, default⟩⟩

中文:
实例 :
  签名: Inhabited PFunctor
  定义体: ⟨⟨default, default⟩⟩
-/
instance : Inhabited PFunctor :=
  ⟨⟨default, default⟩⟩

variable (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} {γ : Type v₃}

/-- Applying `P` to an object of `Type` -/
@[coe]
/--
Definition of `Obj` / `Obj` 的定义

English:
definition Obj
  signature: (α : Type v)
  body: Σ x : P.A, P.B x -> α

中文:
定义 Obj
  签名: (α : 类型v)
  定义体: Σ x : P.A, P.B x -> α
-/
def Obj (α : Type v) : Type (max v uA uB) :=
  Σ x : P.A, P.B x -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun PFunctor.{uA, uB} (fun _ => Type v -> Type (max v uA uB))
  body: Obj

中文:
实例 :
  签名: CoeFun PFunctor.{uA, uB} (fun _ => 类型v -> Type (max v uA uB))
  定义体: Obj
-/
instance : CoeFun PFunctor.{uA, uB} (fun _ => Type v -> Type (max v uA uB)) where
  coe := Obj

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: fun ⟨a, g⟩ => ⟨a, f ∘ g⟩

中文:
定义 map
  签名: (f : α -> β)
  定义体: fun ⟨a, g⟩ => ⟨a, f ∘ g⟩
-/
def map (f : α -> β) : P α -> P β :=
  fun ⟨a, g⟩ => ⟨a, f ∘ g⟩

/--
Instance `Obj.inhabited` / 实例 `Obj.inhabited`

English:
instance Obj.inhabited
  signature: [Inhabited P.A] [Inhabited α]
  body: ⟨⟨default, default⟩⟩

中文:
实例 Obj.inhabited
  签名: [Inhabited P.A] [Inhabited α]
  定义体: ⟨⟨default, default⟩⟩
-/
instance Obj.inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P α) :=
  ⟨⟨default, default⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor P.Obj
  body: @map P

中文:
实例 :
  签名: Functor P.Obj
  定义体: @map P
-/
instance : Functor P.Obj where map := @map P

/-- We prefer `PFunctor.map` to `Functor.map` because it is universe-polymorphic. -/
@[simp]
/--
theorem `map_eq_map` / 定理 `map_eq_map`

English:
theorem map_eq_map
  given: {α β : Type v} (f : α -> β) (x : P α)
  statement: f < > x = P.map f x
  proof: rfl

@[simp]

中文:
定理 map_eq_map
  条件: {α β : 类型v} (f : α -> β) (x : P α)
  结论: f < > x = P.map f x
  证明: rfl

@[simp]
-/
theorem map_eq_map {α β : Type v} (f : α -> β) (x : P α) : f < > x = P.map f x :=
  rfl

@[simp]
/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: (f : α -> β) (a : P.A) (g : P.B a -> α)
  proof: rfl

@[simp]

中文:
定理 map_eq
  条件: (f : α -> β) (a : P.A) (g : P.B a -> α)
  证明: rfl

@[simp]
-/
protected theorem map_eq (f : α -> β) (a : P.A) (g : P.B a -> α) :
    P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
  rfl

@[simp]
/--
theorem `id_map` / 定理 `id_map`

English:
theorem id_map
  statement: forall x : P α, P.map id x = x
  proof: fun ⟨_, _⟩ => rfl

@[simp]

中文:
定理 id_map
  结论: 对任意 x : P α, P.map id x = x
  证明: fun ⟨_, _⟩ => rfl

@[simp]
-/
protected theorem id_map : forall x : P α, P.map id x = x := fun ⟨_, _⟩ => rfl

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (f : α -> β) (g : β -> γ)
  proof: fun ⟨_, _⟩ => rfl

中文:
定理 map_map
  条件: (f : α -> β) (g : β -> γ)
  证明: fun ⟨_, _⟩ => rfl
-/
protected theorem map_map (f : α -> β) (g : β -> γ) :
    forall x : P α, P.map g (P.map f x) = P.map (g ∘ f) x := fun ⟨_, _⟩ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor (Obj.{v} P)
  body: rfl
  id_map x := P.id_map x
.symm comp_map f g x := P.map_map f g x

中文:
实例 :
  签名: LawfulFunctor (Obj.{v} P)
  定义体: rfl
  id_map x := P.id_map x
.symm comp_map f g x := P.map_map f g x
-/
instance : LawfulFunctor (Obj.{v} P) where
  map_const := rfl
  id_map x := P.id_map x
.symm comp_map f g x := P.map_map f g x

/--
Definition of `W` / `W` 的定义

English:
definition W
  signature: : Type (max uA uB)
  body: WType P.B

中文:
定义 W
  签名: : Type (max uA uB)
  定义体: WType P.B
-/
def W : Type (max uA uB) :=
  WType P.B

/- Inhabitants of W types is awkward to encode as an instance assumption because there needs to be a
value `a : P.A` such that `P.B a` is empty to yield a finite tree. -/

variable {P}

/--
Definition of `W.head` / `W.head` 的定义

English:
definition W.head
  signature: : W P -> P.A

中文:
定义 W.head
  签名: : W P -> P.A
-/
def W.head : W P -> P.A
  | ⟨a, _f⟩ => a

/--
Definition of `W.children` / `W.children` 的定义

English:
definition W.children
  signature: : forall x : W P, P.B (W.head x) -> W P

中文:
定义 W.children
  签名: : 对任意 x : W P, P.B (W.head x) -> W P
-/
def W.children : forall x : W P, P.B (W.head x) -> W P
  | ⟨_a, f⟩ => f

/--
Definition of `W.dest` / `W.dest` 的定义

English:
definition W.dest
  signature: : W P -> P (W P)

中文:
定义 W.dest
  签名: : W P -> P (W P)
-/
def W.dest : W P -> P (W P)
  | ⟨a, f⟩ => ⟨a, f⟩

/--
Definition of `W.mk` / `W.mk` 的定义

English:
definition W.mk
  signature: : P (W P) -> W P

中文:
定义 W.mk
  签名: : P (W P) -> W P
-/
def W.mk : P (W P) -> W P
  | ⟨a, f⟩ => ⟨a, f⟩

@[simp]
/--
theorem `W.dest_mk` / 定理 `W.dest_mk`

English:
theorem W.dest_mk
  given: (p : P (W P))
  statement: W.dest (W.mk p) = p
  proof: by cases p; rfl

@[simp]

中文:
定理 W.dest_mk
  条件: (p : P (W P))
  结论: W.dest (W.mk p) = p
  证明: by cases p; rfl

@[simp]
-/
theorem W.dest_mk (p : P (W P)) : W.dest (W.mk p) = p := by cases p; rfl

@[simp]
/--
theorem `W.mk_dest` / 定理 `W.mk_dest`

English:
theorem W.mk_dest
  given: (p : W P)
  statement: W.mk (W.dest p) = p
  proof: by cases p; rfl

中文:
定理 W.mk_dest
  条件: (p : W P)
  结论: W.mk (W.dest p) = p
  证明: by cases p; rfl
-/
theorem W.mk_dest (p : W P) : W.mk (W.dest p) = p := by cases p; rfl

variable (P)

/--
Definition of `Idx` / `Idx` 的定义

English:
definition Idx
  signature: : Type (max uA uB)
  body: Σ x : P.A, P.B x

中文:
定义 Idx
  签名: : Type (max uA uB)
  定义体: Σ x : P.A, P.B x
-/
def Idx : Type (max uA uB) :=
  Σ x : P.A, P.B x

/--
Instance `Idx.inhabited` / 实例 `Idx.inhabited`

English:
instance Idx.inhabited
  signature: [Inhabited P.A] [Inhabited (P.B default)]
  body: ⟨⟨default, default⟩⟩

中文:
实例 Idx.inhabited
  签名: [Inhabited P.A] [Inhabited (P.B default)]
  定义体: ⟨⟨default, default⟩⟩
-/
instance Idx.inhabited [Inhabited P.A] [Inhabited (P.B default)] : Inhabited P.Idx :=
  ⟨⟨default, default⟩⟩

variable {P}

/--
Definition of `Obj.iget` / `Obj.iget` 的定义

English:
definition Obj.iget
  signature: [DecidableEq P.A] {α} [Inhabited α] (x : P α) (i : P.Idx)
  body: if h : i.1 = x.1 then x.2 (cast (congr_arg _ h) i.2) else default

@[simp]

中文:
定义 Obj.iget
  签名: [DecidableEq P.A] {α} [Inhabited α] (x : P α) (i : P.Idx)
  定义体: if h : i.1 = x.1 then x.2 (cast (congr_arg _ h) i.2) else default

@[simp]

Depends on / 依赖: congr_arg
-/
def Obj.iget [DecidableEq P.A] {α} [Inhabited α] (x : P α) (i : P.Idx) : α :=
  if h : i.1 = x.1 then x.2 (cast (congr_arg _ h) i.2) else default

@[simp]
/--
theorem `fst_map` / 定理 `fst_map`

English:
theorem fst_map
  given: (x : P α) (f : α -> β)
  statement: (P.map f x).1 = x.1
  proof: by cases x; rfl

@[simp]

中文:
定理 fst_map
  条件: (x : P α) (f : α -> β)
  结论: (P.map f x).1 = x.1
  证明: by cases x; rfl

@[simp]
-/
theorem fst_map (x : P α) (f : α -> β) : (P.map f x).1 = x.1 := by cases x; rfl

@[simp]
/--
theorem `iget_map` / 定理 `iget_map`

English:
theorem iget_map
  statement: [DecidableEq P.A] [Inhabited α] [Inhabited β] (x : P α)
  proof: by
  simp only [Obj.iget, fst_map, *, dif_pos]
  cases x
  rfl

中文:
定理 iget_map
  结论: [DecidableEq P.A] [Inhabited α] [Inhabited β] (x : P α)
  证明: by
  simp only [Obj.iget, fst_map, *, dif_pos]
  cases x
  rfl

Depends on / 依赖: Obj.iget, dif_pos, fst_map
-/
theorem iget_map [DecidableEq P.A] [Inhabited α] [Inhabited β] (x : P α)
    (f : α -> β) (i : P.Idx) (h : i.1 = x.1) : (P.map f x).iget i = f (x.iget i) := by
  simp only [Obj.iget, fst_map, *, dif_pos]
  cases x
  rfl

end PFunctor

/-
Composition of polynomial functors.
-/
namespace PFunctor

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁})
  body: ⟨Σ a₂ : P₂.1, P₂.2 a₂ -> P₁.1, fun a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u)⟩

中文:
定义 comp
  签名: (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁})
  定义体: ⟨Σ a₂ : P₂.1, P₂.2 a₂ -> P₁.1, fun a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u)⟩
-/
def comp (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) :
    PFunctor.{max uA₁ uA₂ uB₂, max uB₁ uB₂} :=
  ⟨Σ a₂ : P₂.1, P₂.2 a₂ -> P₁.1, fun a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u)⟩

/--
Definition of `comp.mk` / `comp.mk` 的定义

English:
definition comp.mk
  signature: (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : P₂ (P₁ α))
  body: ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2⟩

中文:
定义 comp.mk
  签名: (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : 类型v} (x : P₂ (P₁ α))
  定义体: ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2⟩
-/
def comp.mk (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : P₂ (P₁ α)) :
    comp P₂ P₁ α :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2⟩

/--
Definition of `comp.get` / `comp.get` 的定义

English:
definition comp.get
  signature: (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : comp P₂ P₁ α)
  body: ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩

中文:
定义 comp.get
  签名: (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : 类型v} (x : comp P₂ P₁ α)
  定义体: ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩
-/
def comp.get (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : comp P₂ P₁ α) :
    P₂ (P₁ α) :=
  ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩

end PFunctor

/-
Lifting predicates and relations.
-/
namespace PFunctor

variable {P : PFunctor.{uA, uB}}

open Functor

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftp_iff` / 定理 `liftp_iff`

English:
theorem liftp_iff
  given: {α : Type u} (p : α -> Prop) (x : P α)
  proof: by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i => (f i).val, ?_, fun i => (f i).property⟩
    rw [← hy]; rw [h]; rw [map_eq_map]; rw [PFunctor.map_eq]
    congr
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i => ⟨f i, pf i⟩⟩
  rw [xeq]; rfl

中文:
定理 liftp_iff
  条件: {α : 类型u} (p : α -> 命题) (x : P α)
  证明: by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i => (f i).val, ?_, fun i => (f i).property⟩
    rw [← hy]; rw [h]; rw [map_eq_map]; rw [PFunctor.map_eq]
    congr
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i => ⟨f i, pf i⟩⟩
  rw [xeq]; rfl

Depends on / 依赖: PFunctor, PFunctor.map_eq, map_eq, map_eq_map, property
-/
theorem liftp_iff {α : Type u} (p : α -> Prop) (x : P α) :
    Liftp p x ↔ exists a f, x = ⟨a, f⟩ ∧ forall i, p (f i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i => (f i).val, ?_, fun i => (f i).property⟩
    rw [← hy]; rw [h]; rw [map_eq_map]; rw [PFunctor.map_eq]
    congr
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i => ⟨f i, pf i⟩⟩
  rw [xeq]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftp_iff'` / 定理 `liftp_iff'`

English:
theorem liftp_iff'
  given: {α : Type u} (p : α -> Prop) (a : P.A) (f : P.B a -> α)
  proof: by
  simp only [liftp_iff]; constructor <;> intro h
  · rcases h with ⟨a', f', heq, h'⟩
    cases heq
    assumption
  repeat' first | constructor | assumption

中文:
定理 liftp_iff'
  条件: {α : 类型u} (p : α -> 命题) (a : P.A) (f : P.B a -> α)
  证明: by
  simp only [liftp_iff]; constructor <;> intro h
  · rcases h with ⟨a', f', heq, h'⟩
    cases heq
    assumption
  repeat' first | constructor | assumption

Depends on / 依赖: liftp_iff, repeat
-/
theorem liftp_iff' {α : Type u} (p : α -> Prop) (a : P.A) (f : P.B a -> α) :
    @Liftp.{u} P.Obj _ α p ⟨a, f⟩ ↔ forall i, p (f i) := by
  simp only [liftp_iff]; constructor <;> intro h
  · rcases h with ⟨a', f', heq, h'⟩
    cases heq
    assumption
  repeat' first | constructor | assumption

/--
theorem `liftr_iff` / 定理 `liftr_iff`

English:
theorem liftr_iff
  given: {α : Type u} (r : α -> α -> Prop) (x y : P α)
  proof: by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use ⟨a

中文:
定理 liftr_iff
  条件: {α : 类型u} (r : α -> α -> 命题) (x y : P α)
  证明: by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use ⟨a

Depends on / 依赖: property, val.fst, val.snd
-/
theorem liftr_iff {α : Type u} (r : α -> α -> Prop) (x y : P α) :
    Liftr r x y ↔ exists a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ forall i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  constructor
  · rw [xeq]
    rfl
  rw [yeq]; rfl

open Set

/--
theorem `supp_eq` / 定理 `supp_eq`

English:
theorem supp_eq
  given: {α : Type u} (a : P.A) (f : P.B a -> α)
  proof: by
  ext x; simp only [supp, image_univ, mem_range, mem_ofPred_eq]
  constructor <;> intro h
  · apply @h fun x => exists y : P.B a, f y = x
    rw [liftp_iff']
    intro
    exact ⟨_, rfl⟩
  · simp only [liftp_iff']
    cases h
    subst x
    tauto

中文:
定理 supp_eq
  条件: {α : 类型u} (a : P.A) (f : P.B a -> α)
  证明: by
  ext x; simp only [supp, image_univ, mem_range, mem_ofPred_eq]
  constructor <;> intro h
  · apply @h fun x => exists y : P.B a, f y = x
    rw [liftp_iff']
    intro
    exact ⟨_, rfl⟩
  · simp only [liftp_iff']
    cases h
    subst x
    tauto

Depends on / 依赖: image_univ, liftp_iff, mem_ofPred_eq, mem_range
-/
theorem supp_eq {α : Type u} (a : P.A) (f : P.B a -> α) :
    @supp.{u} P.Obj _ α (⟨a, f⟩ : P α) = f '' univ := by
  ext x; simp only [supp, image_univ, mem_range, mem_ofPred_eq]
  constructor <;> intro h
  · apply @h fun x => exists y : P.B a, f y = x
    rw [liftp_iff']
    intro
    exact ⟨_, rfl⟩
  · simp only [liftp_iff']
    cases h
    subst x
    tauto

end PFunctor
