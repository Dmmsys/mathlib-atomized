/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Functor

/-!
# Finiteness of the Set monad operations

## Tags

finite sets
-/

@[expose] public section

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

section monad
attribute [local instance] Set.monad

/-- If `s : Set α` is a set with `Fintype` instance and `f : α → Set β` is a function such that
each `f a`, `a ∈ s`, has a `Fintype` structure, then `s >>= f` has a `Fintype` structure. -/
@[instance_reducible]
/--
Definition of `fintypeBind` / `fintypeBind` 的定义

English:
definition fintypeBind
  signature: {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α -> Set β)
  body: Set.fintypeBiUnion s f H

中文:
定义 fintypeBind
  签名: {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α -> Set β)
  定义体: Set.fintypeBiUnion s f H

Depends on / 依赖: Set.fintypeBiUnion, fintypeBiUnion
-/
def fintypeBind {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α -> Set β)
    (H : forall a in s, Fintype (f a)) : Fintype (s >>= f) :=
  Set.fintypeBiUnion s f H

/--
Instance `fintypeBind'` / 实例 `fintypeBind'`

English:
instance fintypeBind'
  signature: {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α -> Set β)
  body: Set.fintypeBiUnion' s f

中文:
实例 fintypeBind'
  签名: {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α -> Set β)
  定义体: Set.fintypeBiUnion' s f

Depends on / 依赖: Set.fintypeBiUnion, fintypeBiUnion
-/
instance fintypeBind' {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α -> Set β)
    [forall a, Fintype (f a)] : Fintype (s >>= f) :=
  Set.fintypeBiUnion' s f

end monad

/--
Instance `fintypePure` / 实例 `fintypePure`

English:
instance fintypePure
  signature: : forall a : α, Fintype (pure a : Set α)
  body: Set.fintypeSingleton

中文:
实例 fintypePure
  签名: : 对任意 a : α, Fintype (pure a : Set α)
  定义体: Set.fintypeSingleton

Depends on / 依赖: Set.fintypeSingleton, fintypeSingleton
-/
instance fintypePure : forall a : α, Fintype (pure a : Set α) :=
  Set.fintypeSingleton

/--
Instance `fintypeSeq` / 实例 `fintypeSeq`

English:
instance fintypeSeq
  signature: [DecidableEq β] (f : Set (α -> β)) (s : Set α) [Fintype f] [Fintype s]
  body: by
  rw [seq_def]
  apply Set.fintypeBiUnion'

中文:
实例 fintypeSeq
  签名: [DecidableEq β] (f : Set (α -> β)) (s : Set α) [Fintype f] [Fintype s]
  定义体: by
  rw [seq_def]
  apply Set.fintypeBiUnion'

Depends on / 依赖: Set.fintypeBiUnion, fintypeBiUnion, seq_def
-/
instance fintypeSeq [DecidableEq β] (f : Set (α -> β)) (s : Set α) [Fintype f] [Fintype s] :
    Fintype (f.seq s) := by
  rw [seq_def]
  apply Set.fintypeBiUnion'

/--
Instance `fintypeSeq'` / 实例 `fintypeSeq'`

English:
instance fintypeSeq'
  signature: {α β : Type u} [DecidableEq β] (f : Set (α -> β)) (s : Set α) [Fintype f]
  body: Set.fintypeSeq f s

中文:
实例 fintypeSeq'
  签名: {α β : 类型u} [DecidableEq β] (f : Set (α -> β)) (s : Set α) [Fintype f]
  定义体: Set.fintypeSeq f s

Depends on / 依赖: Set.fintypeSeq, fintypeSeq
-/
instance fintypeSeq' {α β : Type u} [DecidableEq β] (f : Set (α -> β)) (s : Set α) [Fintype f]
    [Fintype s] : Fintype (f <*> s) :=
  Set.fintypeSeq f s

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

/--
theorem `finite_pure` / 定理 `finite_pure`

English:
theorem finite_pure
  given: (a : α)
  statement: (pure a : Set α).Finite
  proof: toFinite _

中文:
定理 finite_pure
  条件: (a : α)
  结论: (pure a : Set α).Finite
  证明: toFinite _

Depends on / 依赖: toFinite
-/
theorem finite_pure (a : α) : (pure a : Set α).Finite :=
  toFinite _

/--
Instance `finite_seq` / 实例 `finite_seq`

English:
instance finite_seq
  signature: (f : Set (α -> β)) (s : Set α) [Finite f] [Finite s]
  body: by
  rw [seq_def]
  infer_instance

中文:
实例 finite_seq
  签名: (f : Set (α -> β)) (s : Set α) [Finite f] [Finite s]
  定义体: by
  rw [seq_def]
  infer_instance

Depends on / 依赖: infer_instance, seq_def
-/
instance finite_seq (f : Set (α -> β)) (s : Set α) [Finite f] [Finite s] : Finite (f.seq s) := by
  rw [seq_def]
  infer_instance

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

section monad
attribute [local instance] Set.monad

/--
theorem `Finite.bind` / 定理 `Finite.bind`

English:
theorem Finite.bind
  given: {α β} {s : Set α} {f : α -> Set β} (h : s.Finite) (hf : forall a in s, (f a).Finite)
  proof: h.biUnion hf

中文:
定理 Finite.bind
  条件: {α β} {s : Set α} {f : α -> Set β} (h : s.Finite) (hf : 对任意 a in s, (f a).Finite)
  证明: h.biUnion hf

Depends on / 依赖: biUnion, h.biUnion
-/
theorem Finite.bind {α β} {s : Set α} {f : α -> Set β} (h : s.Finite) (hf : forall a in s, (f a).Finite) :
    (s >>= f).Finite :=
  h.biUnion hf

end monad

/--
theorem `Finite.seq` / 定理 `Finite.seq`

English:
theorem Finite.seq
  given: {f : Set (α -> β)} {s : Set α} (hf : f.Finite) (hs : s.Finite)
  proof: hf.image2 _ hs

中文:
定理 Finite.seq
  条件: {f : Set (α -> β)} {s : Set α} (hf : f.Finite) (hs : s.Finite)
  证明: hf.image2 _ hs

Depends on / 依赖: hf.image2, image2
-/
theorem Finite.seq {f : Set (α -> β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f.seq s).Finite :=
  hf.image2 _ hs

/--
theorem `Finite.seq'` / 定理 `Finite.seq'`

English:
theorem Finite.seq'
  given: {α β : Type u} {f : Set (α -> β)} {s : Set α} (hf : f.Finite) (hs : s.Finite)
  proof: hf.seq hs

中文:
定理 Finite.seq'
  条件: {α β : 类型u} {f : Set (α -> β)} {s : Set α} (hf : f.Finite) (hs : s.Finite)
  证明: hf.seq hs

Depends on / 依赖: hf.seq
-/
theorem Finite.seq' {α β : Type u} {f : Set (α -> β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f <*> s).Finite :=
  hf.seq hs

end SetFiniteConstructors

end Set
