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
/-
**Set.fintypeBind** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：fintypeBind {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α -> Set β)
 (H : forall a in s, Fintype (f a)) : Fintype (s >>= f)
参数：s : Set α；f : α -> Set β；H : forall a in s, Fintype (f a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s : Set α` is a set with `Fintype` instance and `f : α → Set β` is a functio
n such that
each `f a`, `a ∈ s`, has a `Fintype` structure, then `s >>= f` has a `Fintype` s
tructure.
-/
def fintypeBind {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    (H : ∀ a ∈ s, Fintype (f a)) : Fintype (s >>= f) :=
  Set.fintypeBiUnion s f H
/-
**Set.fintypeBind'** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeBind' {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α -> Set β
) [forall a, Fintype (f a)] : Fintype (s >>= f)
参数：s : Set α；f : α -> Set β；f a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeBind' {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    [∀ a, Fintype (f a)] : Fintype (s >>= f) :=
  Set.fintypeBiUnion' s f

end monad

/-
**Set.fintypePure** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypePure : forall a : α, Fintype (pure a : Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypePure : ∀ a : α, Fintype (pure a : Set α) :=
  Set.fintypeSingleton
/-
**Set.fintypeSeq** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeSeq [DecidableEq β] (f : Set (α -> β)) (s : Set α) [Fintype f] [Fin
type s] : Fintype (f.seq s)
参数：f : Set (α -> β)；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSeq [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f] [Fintype s] :
    Fintype (f.seq s) := by
  rw [seq_def]
  apply Set.fintypeBiUnion'
/-
**Set.fintypeSeq'** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeSeq' {α β : Type u} [DecidableEq β] (f : Set (α -> β)) (s : Set α) 
[Fintype f] [Fintype s] : Fintype (f <*> s)
参数：f : Set (α -> β)；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSeq' {α β : Type u} [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f]
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

/-
**Finite.Set.finite_pure** 是 Mathlib 中的一个定理，位于命名空间 `Finite.Set`。
形式化陈述：finite_pure (a : α) : (pure a : Set α).Finite
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem finite_pure (a : α) : (pure a : Set α).Finite :=
  toFinite _
/-
**Finite.Set.finite_seq** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_seq (f : Set (α -> β)) (s : Set α) [Finite f] [Finite s] : Finite (
f.seq s)
参数：f : Set (α -> β)；s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.seq_def`：seq_def {s : Set (α -> β)} {t : Set α} : seq s t = ⋃ f in s
, f '' t
-/
instance finite_seq (f : Set (α → β)) (s : Set α) [Finite f] [Finite s] : Finite (f.seq s) := by
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

/-
**Set.Finite.bind** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α β : Type u_1} {s : Set α} {f : α → Set β}, s.Finite → (∀ a ∈ s, (f a)
.Finite) → (s >>= f).Finite
参数：∀ a ∈ s, (f a).Finite；s >>= f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.biUnion`：∀ {α : Type u} {ι : Type u_1} {s : Set ι}, s.Finite 
→ ∀ {t : ι → Set α}, (∀ i ∈ s, (t i).Finite) → (⋃ i ∈ s, t i).Finite
-/
theorem Finite.bind {α β} {s : Set α} {f : α → Set β} (h : s.Finite) (hf : ∀ a ∈ s, (f a).Finite) :
    (s >>= f).Finite :=
  h.biUnion hf

end monad

/-
**Set.Finite.seq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : Set (α → β)} {s : Set α}, f.Finite → s.Fi
nite → (f.seq s).Finite
参数：α → β；f.seq s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : S
et α} {t : Set β} (f : α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Fi
nite
-/
theorem Finite.seq {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f.seq s).Finite :=
  hf.image2 _ hs
/-
**Set.Finite.seq'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α β : Type u} {f : Set (α → β)} {s : Set α}, f.Finite → s.Finite → (f <
*> s).Finite
参数：α → β；f <*> s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.seq`：∀ {α : Type u} {β : Type v} {f : Set (α → β)} {s : Set α
}, f.Finite → s.Finite → (f.seq s).Finite
-/
theorem Finite.seq' {α β : Type u} {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f <*> s).Finite :=
  hf.seq hs

end SetFiniteConstructors

end Set

