/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Defs

/-!
# A type for VM-erased data

This file defines a type `Erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `Erased α` is
represented as `0`, just like types and proofs.
-/

@[expose] public section


universe u

/--
Definition of `Erased` / `Erased` 的定义

English:
definition Erased
  signature: (α : Sort u)
  body: { s : α -> Prop // exists a, (a = ·) = s }

中文:
定义 Erased
  签名: (α : 类型层 u)
  定义体: { s : α -> Prop // exists a, (a = ·) = s }
-/
def Erased (α : Sort u) : Sort max 1 u :=
  { s : α -> Prop // exists a, (a = ·) = s }

namespace Erased

/-- Erase a value. -/
@[macro_inline]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {α} (a : α)
  body: ⟨fun b => a = b, a, rfl⟩

中文:
定义 mk
  签名: {α} (a : α)
  定义体: ⟨fun b => a = b, a, rfl⟩
-/
def mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

/--
Definition of `out` / `out` 的定义

English:
definition out
  signature: {α}

中文:
定义 out
  签名: {α}
-/
noncomputable def out {α} : Erased α -> α
  | ⟨_, h⟩ => Classical.choose h

/--
Definition of `OutType` / `OutType` 的定义

English:
abbreviation OutType
  signature: (a : Erased (Sort u))
  body: out a

中文:
缩写 OutType
  签名: (a : Erased (类型层 u))
  定义体: out a
-/
abbrev OutType (a : Erased (Sort u)) : Sort u :=
  out a

/--
theorem `out_proof` / 定理 `out_proof`

English:
theorem out_proof
  given: {p : Prop} (a : Erased p)
  statement: p
  proof: out a

@[simp]

中文:
定理 out_proof
  条件: {p : 命题} (a : Erased p)
  结论: p
  证明: out a

@[simp]
-/
theorem out_proof {p : Prop} (a : Erased p) : p :=
  out a

@[simp]
/--
theorem `out_mk` / 定理 `out_mk`

English:
theorem out_mk
  given: {α} (a : α)
  statement: (mk a).out = a
  proof: by
  let h := (mk a).2; change Classical.choose h = a
  have := Classical.choose_spec h
  exact cast (congr_fun this a).symm rfl

@[simp]

中文:
定理 out_mk
  条件: {α} (a : α)
  结论: (mk a).out = a
  证明: by
  let h := (mk a).2; change Classical.choose h = a
  have := Classical.choose_spec h
  exact cast (congr_fun this a).symm rfl

@[simp]

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec, congr_fun
-/
theorem out_mk {α} (a : α) : (mk a).out = a := by
  let h := (mk a).2; change Classical.choose h = a
  have := Classical.choose_spec h
  exact cast (congr_fun this a).symm rfl

@[simp]
/--
theorem `mk_out` / 定理 `mk_out`

English:
theorem mk_out
  given: {α}
  statement: forall a : Erased α, mk (out a) = a

中文:
定理 mk_out
  条件: {α}
  结论: 对任意 a : Erased α, mk (out a) = a
-/
theorem mk_out {α} : forall a : Erased α, mk (out a) = a
  | ⟨s, h⟩ => by simp only [mk]; congr; exact Classical.choose_spec h

@[ext]
/--
theorem `out_inj` / 定理 `out_inj`

English:
theorem out_inj
  given: {α} (a b : Erased α) (h : a.out = b.out)
  statement: a = b
  proof: by simpa using congr_arg mk h

中文:
定理 out_inj
  条件: {α} (a b : Erased α) (h : a.out = b.out)
  结论: a = b
  证明: by simpa using congr_arg mk h

Depends on / 依赖: congr_arg
-/
theorem out_inj {α} (a b : Erased α) (h : a.out = b.out) : a = b := by simpa using congr_arg mk h

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: (α)
  body: ⟨out, mk, mk_out, out_mk⟩

中文:
定义 equiv
  签名: (α)
  定义体: ⟨out, mk, mk_out, out_mk⟩

Depends on / 依赖: mk_out, out_mk
-/
noncomputable def equiv (α) : Erased α ≃ α :=
  ⟨out, mk, mk_out, out_mk⟩

instance (α : Type u) : Repr (Erased α) :=
  ⟨fun _ _ => "Erased"⟩

instance (α : Type u) : ToString (Erased α) :=
  ⟨fun _ => "Erased"⟩

/--
Definition of `choice` / `choice` 的定义

English:
definition choice
  signature: {α} (h : Nonempty α)
  body: mk (Classical.choice h)

@[simp]

中文:
定义 choice
  签名: {α} (h : 非空 α)
  定义体: mk (Classical.choice h)

@[simp]

Depends on / 依赖: Classical, Classical.choice, choice
-/
def choice {α} (h : Nonempty α) : Erased α :=
  mk (Classical.choice h)

@[simp]
/--
theorem `nonempty_iff` / 定理 `nonempty_iff`

English:
theorem nonempty_iff
  given: {α}
  statement: Nonempty (Erased α) ↔ Nonempty α
  proof: ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩

中文:
定理 nonempty_iff
  条件: {α}
  结论: 非空 (Erased α) ↔ 非空 α
  证明: ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩

Depends on / 依赖: a.out
-/
theorem nonempty_iff {α} : Nonempty (Erased α) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩

instance {α} [h : Nonempty α] : Inhabited (Erased α) :=
  ⟨choice h⟩

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: {α β} (a : Erased α) (f : α -> Erased β)
  body: ⟨fun b => (f a.out).1 b, (f a.out).2⟩

@[simp]

中文:
定义 bind
  签名: {α β} (a : Erased α) (f : α -> Erased β)
  定义体: ⟨fun b => (f a.out).1 b, (f a.out).2⟩

@[simp]

Depends on / 依赖: a.out
-/
def bind {α β} (a : Erased α) (f : α -> Erased β) : Erased β :=
  ⟨fun b => (f a.out).1 b, (f a.out).2⟩

@[simp]
/--
theorem `bind_eq_out` / 定理 `bind_eq_out`

English:
theorem bind_eq_out
  given: {α β} (a f)
  statement: @bind α β a f = f a.out
  proof: rfl

中文:
定理 bind_eq_out
  条件: {α β} (a f)
  结论: @bind α β a f = f a.out
  证明: rfl
-/
theorem bind_eq_out {α β} (a f) : @bind α β a f = f a.out := rfl

/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: {α} (a : Erased (Erased α))
  body: bind a id

@[simp]

中文:
定义 join
  签名: {α} (a : Erased (Erased α))
  定义体: bind a id

@[simp]
-/
def join {α} (a : Erased (Erased α)) : Erased α :=
  bind a id

@[simp]
/--
theorem `join_eq_out` / 定理 `join_eq_out`

English:
theorem join_eq_out
  given: {α} (a)
  statement: @join α a = a.out
  proof: rfl

中文:
定理 join_eq_out
  条件: {α} (a)
  结论: @join α a = a.out
  证明: rfl
-/
theorem join_eq_out {α} (a) : @join α a = a.out :=
  rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {α β} (f : α -> β) (a : Erased α)
  body: bind a (mk ∘ f)

@[simp]

中文:
定义 map
  签名: {α β} (f : α -> β) (a : Erased α)
  定义体: bind a (mk ∘ f)

@[simp]
-/
def map {α β} (f : α -> β) (a : Erased α) : Erased β :=
  bind a (mk ∘ f)

@[simp]
/--
theorem `map_out` / 定理 `map_out`

English:
theorem map_out
  given: {α β} {f : α -> β} (a : Erased α)
  statement: (a.map f).out = f a.out
  proof: by simp [map]

中文:
定理 map_out
  条件: {α β} {f : α -> β} (a : Erased α)
  结论: (a.map f).out = f a.out
  证明: by simp [map]
-/
theorem map_out {α β} {f : α -> β} (a : Erased α) : (a.map f).out = f a.out := by simp [map]

/--
Instance `Monad` / 实例 `Monad`

English:
instance Monad
  signature: : Monad Erased where
  body: @mk
  bind := @bind
  map := @map

@[simp]

中文:
实例 单子
  签名: : 单子 Erased where
  定义体: @mk
  bind := @bind
  map := @map

@[simp]
-/
protected instance Monad : Monad Erased where
  pure := @mk
  bind := @bind
  map := @map

@[simp]
/--
theorem `pure_def` / 定理 `pure_def`

English:
theorem pure_def
  given: {α}
  statement: (pure : α -> Erased α) = @mk _
  proof: rfl

@[simp]

中文:
定理 pure_def
  条件: {α}
  结论: (pure : α -> Erased α) = @mk _
  证明: rfl

@[simp]
-/
theorem pure_def {α} : (pure : α -> Erased α) = @mk _ :=
  rfl

@[simp]
/--
theorem `bind_def` / 定理 `bind_def`

English:
theorem bind_def
  given: {α β}
  statement: ((· >>= ·) : Erased α -> (α -> Erased β) -> Erased β) = @bind _ _
  proof: rfl

@[simp]

中文:
定理 bind_def
  条件: {α β}
  结论: ((· >>= ·) : Erased α -> (α -> Erased β) -> Erased β) = @bind _ _
  证明: rfl

@[simp]
-/
theorem bind_def {α β} : ((· >>= ·) : Erased α -> (α -> Erased β) -> Erased β) = @bind _ _ :=
  rfl

@[simp]
/--
theorem `map_def` / 定理 `map_def`

English:
theorem map_def
  given: {α β}
  statement: ((· <$> ·) : (α -> β) -> Erased α -> Erased β) = @map _ _
  proof: rfl

中文:
定理 map_def
  条件: {α β}
  结论: ((· <$> ·) : (α -> β) -> Erased α -> Erased β) = @map _ _
  证明: rfl
-/
theorem map_def {α β} : ((· <$> ·) : (α -> β) -> Erased α -> Erased β) = @map _ _ :=
  rfl

/--
Instance `instLawfulMonad` / 实例 `instLawfulMonad`

English:
instance instLawfulMonad
  signature: : LawfulMonad Erased
  body: { id_map := by intros; ext; simp
    map_const := by intros; ext; simp [Functor.mapConst]
    pure_bind := by intros; ext; simp
    bind_assoc := by intros; ext; simp
    bind_pure_comp := by intros; ext; simp
    bind_map := by intros; ext; simp [Seq.seq]
    seqLeft_eq := by intros; ext; simp [Seq.seq, SeqLeft.seqLeft]
    seqRight_eq := by intros; ext; simp [Seq.seq, SeqRight.seqRight]
    pure_seq := by intros; ext; simp [Seq.seq] }

中文:
实例 instLawfulMonad
  签名: : 合法单子 Erased
  定义体: { id_map := by intros; ext; simp
    map_const := by intros; ext; simp [Functor.mapConst]
    pure_bind := by intros; ext; simp
    bind_assoc := by intros; ext; simp
    bind_pure_comp := by intros; ext; simp
    bind_map := by intros; ext; simp [Seq.seq]
    seqLeft_eq := by intros; ext; simp [Seq.seq, SeqLeft.seqLeft]
    seqRight_eq := by intros; ext; simp [Seq.seq, SeqRight.seqRight]
    pure_seq := by intros; ext; simp [Seq.seq] }
-/
protected instance instLawfulMonad : LawfulMonad Erased :=
  { id_map := by intros; ext; simp
    map_const := by intros; ext; simp [Functor.mapConst]
    pure_bind := by intros; ext; simp
    bind_assoc := by intros; ext; simp
    bind_pure_comp := by intros; ext; simp
    bind_map := by intros; ext; simp [Seq.seq]
    seqLeft_eq := by intros; ext; simp [Seq.seq, SeqLeft.seqLeft]
    seqRight_eq := by intros; ext; simp [Seq.seq, SeqRight.seqRight]
    pure_seq := by intros; ext; simp [Seq.seq] }

end Erased
