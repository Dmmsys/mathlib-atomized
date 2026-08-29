/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Control.Functor.Multivariate
public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Multivariate polynomial functors.

Multivariate polynomial functors are used for defining M-types and W-types.
They map a type vector `α` to the type `Σ a : A, B a ⟹ α`, with `A : Type` and
`B : A → TypeVec n`. They interact well with Lean's inductive definitions because
they guarantee that occurrences of `α` are positive.
-/

@[expose] public section


universe u v

open MvFunctor

/-- multivariate polynomial functors
-/
@[pp_with_univ]
/--
Definition of `MvPFunctor` / `MvPFunctor` 的定义

English:
structure MvPFunctor
  parameters: (n : Nat)
  axioms and operations (2):
    - A : Type u
    - B : A -> TypeVec.{u} n

中文:
结构 MvP函子
  参数: (n : 自然数)
  公理与运算 (2 个):
    - A : 类型u
    - B : A -> TypeVec.{u} n
-/
structure MvPFunctor (n : Nat) where
  /-- The head type -/
  A : Type u
  /-- The child family of types -/
  B : A -> TypeVec.{u} n

namespace MvPFunctor

open MvFunctor (LiftP LiftR)

variable {n m : Nat} (P : MvPFunctor.{u} n)

/-- Applying `P` to an object of `Type` -/
@[coe]
/--
Definition of `Obj` / `Obj` 的定义

English:
definition Obj
  signature: (α : TypeVec.{u} n)
  body: Σ a : P.A, P.B a ⟹ α

中文:
定义 Obj
  签名: (α : TypeVec.{u} n)
  定义体: Σ a : P.A, P.B a ⟹ α
-/
def Obj (α : TypeVec.{u} n) : Type u :=
  Σ a : P.A, P.B a ⟹ α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (MvPFunctor.{u} n) (fun _ => TypeVec.{u} n -> Type u)
  body: Obj

中文:
实例 :
  签名: CoeFun (MvP函子.{u} n) (fun _ => TypeVec.{u} n -> 类型u)
  定义体: Obj
-/
instance : CoeFun (MvPFunctor.{u} n) (fun _ => TypeVec.{u} n -> Type u) where
  coe := Obj

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {α β : TypeVec n} (f : α ⟹ β)
  body: fun ⟨a, g⟩ => ⟨a, TypeVec.comp f g⟩

中文:
定义 map
  签名: {α β : TypeVec n} (f : α ⟹ β)
  定义体: fun ⟨a, g⟩ => ⟨a, TypeVec.comp f g⟩

Depends on / 依赖: TypeVec, TypeVec.comp
-/
def map {α β : TypeVec n} (f : α ⟹ β) : P α -> P β := fun ⟨a, g⟩ => ⟨a, TypeVec.comp f g⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (MvPFunctor n)
  body: ⟨⟨default, default⟩⟩

中文:
实例 :
  签名: 可居 (MvP函子 n)
  定义体: ⟨⟨default, default⟩⟩
-/
instance : Inhabited (MvPFunctor n) :=
  ⟨⟨default, default⟩⟩

/--
Instance `Obj.inhabited` / 实例 `Obj.inhabited`

English:
instance Obj.inhabited
  signature: {α : TypeVec n} [Inhabited P.A] [forall i, Inhabited (α i)]
  body: ⟨⟨default, fun _ _ => default⟩⟩

中文:
实例 Obj.inhabited
  签名: {α : TypeVec n} [可居 P.A] [对任意 i, 可居 (α i)]
  定义体: ⟨⟨default, fun _ _ => default⟩⟩
-/
instance Obj.inhabited {α : TypeVec n} [Inhabited P.A] [forall i, Inhabited (α i)] :
    Inhabited (P α) :=
  ⟨⟨default, fun _ _ => default⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MvFunctor.{u} P.Obj
  body: ⟨@MvPFunctor.map n P⟩

中文:
实例 :
  签名: Mv函子.{u} P.Obj
  定义体: ⟨@MvPFunctor.map n P⟩

Depends on / 依赖: MvPFunctor, MvPFunctor.map
-/
instance : MvFunctor.{u} P.Obj :=
  ⟨@MvPFunctor.map n P⟩

/--
theorem `map_eq` / 定理 `map_eq`

English:
theorem map_eq
  given: {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α)
  proof: rfl

中文:
定理 map_eq
  条件: {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α)
  证明: rfl
-/
theorem map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
    @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
  rfl

/--
theorem `id_map` / 定理 `id_map`

English:
theorem id_map
  given: {α : TypeVec n}
  statement: forall x : P α, TypeVec.id < > x = x

中文:
定理 id_map
  条件: {α : TypeVec n}
  结论: 对任意 x : P α, TypeVec.id < > x = x
-/
theorem id_map {α : TypeVec n} : forall x : P α, TypeVec.id < > x = x
  | ⟨_, _⟩ => rfl

/--
theorem `comp_map` / 定理 `comp_map`

English:
theorem comp_map
  given: {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ)

中文:
定理 comp_map
  条件: {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ)
-/
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) :
forall x : P α, (g ⊚ f) < > x = g < > f < > x
  | ⟨_, _⟩ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMvFunctor.{u} P.Obj
  body: @id_map _ P
  comp_map := @comp_map _ P

中文:
实例 :
  签名: LawfulMv函子.{u} P.Obj
  定义体: @id_map _ P
  comp_map := @comp_map _ P

Depends on / 依赖: id_map
-/
instance : LawfulMvFunctor.{u} P.Obj where
  id_map := @id_map _ P
  comp_map := @comp_map _ P

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (n : Nat) (A : Type u)
  body: { A
    B := fun _ _ => PEmpty }

中文:
定义 const
  签名: (n : 自然数) (A : 类型u)
  定义体: { A
    B := fun _ _ => PEmpty }

Depends on / 依赖: PEmpty
-/
def const (n : Nat) (A : Type u) : MvPFunctor n :=
  { A
    B := fun _ _ => PEmpty }

section Const

variable (n) {A : Type u} {α β : TypeVec.{u} n}

/--
Definition of `const.mk` / `const.mk` 的定义

English:
definition const.mk
  signature: (x : A) {α}
  body: ⟨x, fun _ a => PEmpty.elim a⟩

中文:
定义 const.mk
  签名: (x : A) {α}
  定义体: ⟨x, fun _ a => PEmpty.elim a⟩

Depends on / 依赖: PEmpty, PEmpty.elim
-/
def const.mk (x : A) {α} : const n A α :=
  ⟨x, fun _ a => PEmpty.elim a⟩

variable {n}

/--
Definition of `const.get` / `const.get` 的定义

English:
definition const.get
  signature: (x : const n A α)
  body: x.1

@[simp]

中文:
定义 const.get
  签名: (x : const n A α)
  定义体: x.1

@[simp]
-/
def const.get (x : const n A α) : A :=
  x.1

@[simp]
/--
theorem `const.get_map` / 定理 `const.get_map`

English:
theorem const.get_map
  given: (f : α ⟹ β) (x : const n A α)
  statement: const.get (f <$$> x) = const.get x
  proof: by
  cases x
  rfl

@[simp]

中文:
定理 const.get_map
  条件: (f : α ⟹ β) (x : const n A α)
  结论: const.get (f <$$> x) = const.get x
  证明: by
  cases x
  rfl

@[simp]
-/
theorem const.get_map (f : α ⟹ β) (x : const n A α) : const.get (f <$$> x) = const.get x := by
  cases x
  rfl

@[simp]
/--
theorem `const.get_mk` / 定理 `const.get_mk`

English:
theorem const.get_mk
  given: (x : A)
  statement: const.get (const.mk n x : const n A α) = x
  proof: rfl

@[simp]

中文:
定理 const.get_mk
  条件: (x : A)
  结论: const.get (const.mk n x : const n A α) = x
  证明: rfl

@[simp]
-/
theorem const.get_mk (x : A) : const.get (const.mk n x : const n A α) = x := rfl

@[simp]
/--
theorem `const.mk_get` / 定理 `const.mk_get`

English:
theorem const.mk_get
  given: (x : const n A α)
  statement: const.mk n (const.get x) = x
  proof: by
  cases x
  dsimp [const.get, const.mk]
  congr with (_⟨⟩)

中文:
定理 const.mk_get
  条件: (x : const n A α)
  结论: const.mk n (const.get x) = x
  证明: by
  cases x
  dsimp [const.get, const.mk]
  congr with (_⟨⟩)

Depends on / 依赖: const.get, const.mk
-/
theorem const.mk_get (x : const n A α) : const.mk n (const.get x) = x := by
  cases x
  dsimp [const.get, const.mk]
  congr with (_⟨⟩)

end Const

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (P : MvPFunctor.{u} n) (Q : Fin2 n -> MvPFunctor.{u} m)
  body: Σ a₂ : P.1, forall i, P.2 a₂ i -> (Q i).1
  B a i := Σ (j : _) (b : P.2 a.1 j), (Q j).2 (a.snd j b) i

中文:
定义 comp
  签名: (P : MvP函子.{u} n) (Q : Fin2 n -> MvP函子.{u} m)
  定义体: Σ a₂ : P.1, forall i, P.2 a₂ i -> (Q i).1
  B a i := Σ (j : _) (b : P.2 a.1 j), (Q j).2 (a.snd j b) i
-/
def comp (P : MvPFunctor.{u} n) (Q : Fin2 n -> MvPFunctor.{u} m) : MvPFunctor m where
  A := Σ a₂ : P.1, forall i, P.2 a₂ i -> (Q i).1
  B a i := Σ (j : _) (b : P.2 a.1 j), (Q j).2 (a.snd j b) i

variable {P} {Q : Fin2 n -> MvPFunctor.{u} m} {α β : TypeVec.{u} m}

/--
Definition of `comp.mk` / `comp.mk` 的定义

English:
definition comp.mk
  signature: (x : P (fun i => Q i α))
  body: ⟨⟨x.1, fun _ a => (x.2 _ a).1⟩, fun i a => (x.snd a.fst a.snd.fst).snd i a.snd.snd⟩

中文:
定义 comp.mk
  签名: (x : P (fun i => Q i α))
  定义体: ⟨⟨x.1, fun _ a => (x.2 _ a).1⟩, fun i a => (x.snd a.fst a.snd.fst).snd i a.snd.snd⟩

Depends on / 依赖: a.fst, a.snd.fst, a.snd.snd, x.snd
-/
def comp.mk (x : P (fun i => Q i α)) : comp P Q α :=
  ⟨⟨x.1, fun _ a => (x.2 _ a).1⟩, fun i a => (x.snd a.fst a.snd.fst).snd i a.snd.snd⟩

/--
Definition of `comp.get` / `comp.get` 的定义

English:
definition comp.get
  signature: (x : comp P Q α)
  body: ⟨x.1.1, fun i a => ⟨x.fst.snd i a, fun (j : Fin2 m) (b : (Q i).B _ j) => x.snd j ⟨i, ⟨a, b⟩⟩⟩⟩

中文:
定义 comp.get
  签名: (x : comp P Q α)
  定义体: ⟨x.1.1, fun i a => ⟨x.fst.snd i a, fun (j : Fin2 m) (b : (Q i).B _ j) => x.snd j ⟨i, ⟨a, b⟩⟩⟩⟩

Depends on / 依赖: x.fst.snd, x.snd
-/
def comp.get (x : comp P Q α) : P (fun i => Q i α) :=
  ⟨x.1.1, fun i a => ⟨x.fst.snd i a, fun (j : Fin2 m) (b : (Q i).B _ j) => x.snd j ⟨i, ⟨a, b⟩⟩⟩⟩

/--
theorem `comp.get_map` / 定理 `comp.get_map`

English:
theorem comp.get_map
  given: (f : α ⟹ β) (x : comp P Q α)
  proof: by
  rfl

@[simp]

中文:
定理 comp.get_map
  条件: (f : α ⟹ β) (x : comp P Q α)
  证明: by
  rfl

@[simp]
-/
theorem comp.get_map (f : α ⟹ β) (x : comp P Q α) :
comp.get (f <$$> x) = (fun i (x : Q i α) => f <$$> x) < > comp.get x := by
  rfl

@[simp]
/--
theorem `comp.get_mk` / 定理 `comp.get_mk`

English:
theorem comp.get_mk
  given: (x : P (fun i => Q i α))
  statement: comp.get (comp.mk x) = x
  proof: by
  rfl

@[simp]

中文:
定理 comp.get_mk
  条件: (x : P (fun i => Q i α))
  结论: comp.get (comp.mk x) = x
  证明: by
  rfl

@[simp]
-/
theorem comp.get_mk (x : P (fun i => Q i α)) : comp.get (comp.mk x) = x := by
  rfl

@[simp]
/--
theorem `comp.mk_get` / 定理 `comp.mk_get`

English:
theorem comp.mk_get
  given: (x : comp P Q α)
  statement: comp.mk (comp.get x) = x
  proof: by
  rfl

中文:
定理 comp.mk_get
  条件: (x : comp P Q α)
  结论: comp.mk (comp.get x) = x
  证明: by
  rfl
-/
theorem comp.mk_get (x : comp P Q α) : comp.mk (comp.get x) = x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftP_iff` / 定理 `liftP_iff`

English:
theorem liftP_iff
  given: {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop) (x : P α)
  proof: by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i j => (f i j).val, ?_, fun i j => (f i j).property⟩
    rw [← hy]; rw [h]; rw [map_eq]
    rfl
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i j => ⟨f i j, pf i j⟩⟩
  rw [xeq]; rfl

中文:
定理 liftP_iff
  条件: {α : TypeVec n} (p : 对任意 ⦃i⦄, α i -> 命题) (x : P α)
  证明: by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i j => (f i j).val, ?_, fun i j => (f i j).property⟩
    rw [← hy]; rw [h]; rw [map_eq]
    rfl
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i j => ⟨f i j, pf i j⟩⟩
  rw [xeq]; rfl

Depends on / 依赖: map_eq, property
-/
theorem liftP_iff {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop) (x : P α) :
    LiftP p x ↔ exists a f, x = ⟨a, f⟩ ∧ forall i j, p (f i j) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i j => (f i j).val, ?_, fun i j => (f i j).property⟩
    rw [← hy]; rw [h]; rw [map_eq]
    rfl
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i j => ⟨f i j, pf i j⟩⟩
  rw [xeq]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `liftP_iff'` / 定理 `liftP_iff'`

English:
theorem liftP_iff'
  given: {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop) (a : P.A) (f : P.B a ⟹ α)
  proof: by
  simp only [liftP_iff]; constructor
  · rintro ⟨_, _, ⟨⟩, _⟩
    assumption
  · intro
    repeat' first | constructor | assumption

中文:
定理 liftP_iff'
  条件: {α : TypeVec n} (p : 对任意 ⦃i⦄, α i -> 命题) (a : P.A) (f : P.B a ⟹ α)
  证明: by
  simp only [liftP_iff]; constructor
  · rintro ⟨_, _, ⟨⟩, _⟩
    assumption
  · intro
    repeat' first | constructor | assumption

Depends on / 依赖: liftP_iff, repeat
-/
theorem liftP_iff' {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop) (a : P.A) (f : P.B a ⟹ α) :
    @LiftP.{u} _ P.Obj _ α p ⟨a, f⟩ ↔ forall i x, p (f i x) := by
  simp only [liftP_iff]; constructor
  · rintro ⟨_, _, ⟨⟩, _⟩
    assumption
  · intro
    repeat' first | constructor | assumption

/--
theorem `liftR_iff` / 定理 `liftR_iff`

English:
theorem liftR_iff
  given: {α : TypeVec n} (r : forall ⦃i⦄, α i -> α i -> Prop) (x y : P α)
  proof: by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i j
    exact (f i j).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  exact ⟨⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩, xeq.symm, yeq.symm⟩

中文:
定理 liftR_iff
  条件: {α : TypeVec n} (r : 对任意 ⦃i⦄, α i -> α i -> 命题) (x y : P α)
  证明: by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i j
    exact (f i j).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  exact ⟨⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩, xeq.symm, yeq.symm⟩

Depends on / 依赖: property, val.fst, val.snd, xeq.symm, yeq.symm
-/
theorem liftR_iff {α : TypeVec n} (r : forall ⦃i⦄, α i -> α i -> Prop) (x y : P α) :
    LiftR @r x y ↔ exists a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ forall i j, r (f₀ i j) (f₁ i j) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i j
    exact (f i j).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  exact ⟨⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩, xeq.symm, yeq.symm⟩

open Set

/--
theorem `supp_eq` / 定理 `supp_eq`

English:
theorem supp_eq
  given: {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i)
  proof: by
  ext x; simp only [supp, image_univ, mem_range, mem_ofPred_eq]
  constructor <;> intro h
  · apply @h fun i x => exists y : P.B a i, f i y = x
    rw [liftP_iff']
    intros
    exact ⟨_, rfl⟩
  · simp only [liftP_iff']
    cases h
    subst x
    tauto

中文:
定理 supp_eq
  条件: {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i)
  证明: by
  ext x; simp only [supp, image_univ, mem_range, mem_ofPred_eq]
  constructor <;> intro h
  · apply @h fun i x => exists y : P.B a i, f i y = x
    rw [liftP_iff']
    intros
    exact ⟨_, rfl⟩
  · simp only [liftP_iff']
    cases h
    subst x
    tauto

Depends on / 依赖: image_univ, intros, liftP_iff, mem_ofPred_eq, mem_range
-/
theorem supp_eq {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i) :
    @supp.{u} _ P.Obj _ α (⟨a, f⟩ : P α) i = f i '' univ := by
  ext x; simp only [supp, image_univ, mem_range, mem_ofPred_eq]
  constructor <;> intro h
  · apply @h fun i x => exists y : P.B a i, f i y = x
    rw [liftP_iff']
    intros
    exact ⟨_, rfl⟩
  · simp only [liftP_iff']
    cases h
    subst x
    tauto

end MvPFunctor

/-
Decomposing an n+1-ary pfunctor.
-/
namespace MvPFunctor

open TypeVec

variable {n : Nat} (P : MvPFunctor.{u} (n + 1))

/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: : MvPFunctor n where
  body: P.A
  B a := (P.B a).drop

中文:
定义 drop
  签名: : MvP函子 n where
  定义体: P.A
  B a := (P.B a).drop
-/
def drop : MvPFunctor n where
  A := P.A
  B a := (P.B a).drop

/--
Definition of `last` / `last` 的定义

English:
definition last
  signature: : PFunctor where
  body: P.A
  B a := (P.B a).last

中文:
定义 last
  签名: : P函子 where
  定义体: P.A
  B a := (P.B a).last
-/
def last : PFunctor where
  A := P.A
  B a := (P.B a).last

/--
Definition of `appendContents` / `appendContents` 的定义

English:
abbreviation appendContents
  signature: {α : TypeVec n} {β : Type*} {a : P.A} (f' : P.drop.B a ⟹ α)
  body: splitFun f' f

中文:
缩写 appendContents
  签名: {α : TypeVec n} {β : 类型} {a : P.A} (f' : P.drop.B a ⟹ α)
  定义体: splitFun f' f

Depends on / 依赖: splitFun
-/
abbrev appendContents {α : TypeVec n} {β : Type*} {a : P.A} (f' : P.drop.B a ⟹ α)
    (f : P.last.B a -> β) : P.B a ⟹ (α ::: β) :=
  splitFun f' f

end MvPFunctor
