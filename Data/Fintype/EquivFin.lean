/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.NodupEquivFin

/-!
# Equivalences between `Fintype`, `Fin` and `Finite`

This file defines the bijection between a `Fintype α` and `Fin (Fintype.card α)`, and uses this to
relate `Fintype` with `Finite`. From that we can derive properties of `Finite` and `Infinite`,
and show some instances of `Infinite`.

## Main declarations

* `Fintype.truncEquivFin`: A fintype `α` is computably equivalent to `Fin (card α)`. The
  `Trunc`-free, noncomputable version is `Fintype.equivFin`.
* `Fintype.truncEquivOfCardEq` `Fintype.equivOfCardEq`: Two fintypes of same cardinality are
  equivalent. See above.
* `Fin.equiv_iff_eq`: `Fin m ≃ Fin n` iff `m = n`.
* `Infinite.natEmbedding`: An embedding of `ℕ` into an infinite type.

Types which have an injection from/a surjection to an `Infinite` type are themselves `Infinite`.
See `Infinite.of_injective` and `Infinite.of_surjective`.

## Instances

We provide `Infinite` instances for
* specific types: `ℕ`, `ℤ`, `String`
* type constructors: `Multiset α`, `List α`

-/

@[expose] public section

assert_not_exists Monoid

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

/-- There is (computably) an equivalence between `α` and `Fin (card α)`.

Since it is not unique and depends on which permutation
of the universe list is used, the equivalence is wrapped in `Trunc` to
preserve computability.

See `Fintype.equivFin` for the noncomputable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq`
for an equiv `α ≃ Fin n` given `Fintype.card α = n`.

See `Fintype.truncFinBijection` for a version without `[DecidableEq α]`.
-/
/-
**Fintype.truncEquivFin** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：truncEquivFin (α) [DecidableEq α] [Fintype α] : Trunc (α ≃ Fin (card α))
参数：α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.mem_univ_val`：mem_univ_val : forall x, x in (univ : Finset α).1

--- 原说明 ---
There is (computably) an equivalence between `α` and `Fin (card α)`.

Since it is not unique and depends on which permutation
of the universe list is used, the equivalence is wrapped in `Trunc` to
preserve computability.

See `Fintype.equivFin` for the noncomputable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq`
for an equiv `α ≃ Fin n` given `Fintype.card α = n`.

See `Fintype.truncFinBijection` for a version without `[DecidableEq α]`.
-/
def truncEquivFin (α) [DecidableEq α] [Fintype α] : Trunc (α ≃ Fin (card α)) := by
  unfold card Finset.card
  exact
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (∀ x : α, x ∈ s) → s.Nodup → Trunc (α ≃ Fin (Multiset.card s)))
      univ.val
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getEquivOfForallMemList _ h).symm)
      mem_univ_val univ.2

/-- There is (noncomputably) an equivalence between `α` and `Fin (card α)`.

See `Fintype.truncEquivFin` for the computable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq`
for an equiv `α ≃ Fin n` given `Fintype.card α = n`.
-/
/-
**Fintype.equivFin** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：equivFin (α) [Fintype α] : α ≃ Fin (card α)
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is (noncomputably) an equivalence between `α` and `Fin (card α)`.

See `Fintype.truncEquivFin` for the computable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq`
for an equiv `α ≃ Fin n` given `Fintype.card α = n`.
-/
noncomputable def equivFin (α) [Fintype α] : α ≃ Fin (card α) :=
  letI := Classical.decEq α
  (truncEquivFin α).out

/-- There is (computably) a bijection between `Fin (card α)` and `α`.

Since it is not unique and depends on which permutation
of the universe list is used, the bijection is wrapped in `Trunc` to
preserve computability.

See `Fintype.truncEquivFin` for a version that gives an equivalence
given `[DecidableEq α]`.
-/
/-
**Fintype.truncFinBijection** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：truncFinBijection (α) [Fintype α] : Trunc { f : Fin (card α) -> α // Bijec
tive f }
参数：α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ_val`：mem_univ_val : forall x, x in (univ : Finset α).1

--- 原说明 ---
There is (computably) a bijection between `Fin (card α)` and `α`.

Since it is not unique and depends on which permutation
of the universe list is used, the bijection is wrapped in `Trunc` to
preserve computability.

See `Fintype.truncEquivFin` for a version that gives an equivalence
given `[DecidableEq α]`.
-/
def truncFinBijection (α) [Fintype α] : Trunc { f : Fin (card α) → α // Bijective f } := by
  unfold card Finset.card
  refine
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (∀ x : α, x ∈ s) → s.Nodup → Trunc {f : Fin (Multiset.card s) → α // Bijective f})
      univ.val
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getBijectionOfForallMemList _ h))
      mem_univ_val univ.2

end Fintype

namespace Fintype

section

variable [Fintype α] [Fintype β]

/-- If the cardinality of `α` is `n`, there is computably a bijection between `α` and `Fin n`.

See `Fintype.equivFinOfCardEq` for the noncomputable definition,
and `Fintype.truncEquivFin` and `Fintype.equivFin` for the bijection `α ≃ Fin (card α)`.
-/
/-
**Fintype.truncEquivFinOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：truncEquivFinOfCardEq [DecidableEq α] {n : Nat} (h : Fintype.card α = n) :
 Trunc (α ≃ Fin n)
参数：h : Fintype.card α = n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If the cardinality of `α` is `n`, there is computably a bijection between `α` an
d `Fin n`.

See `Fintype.equivFinOfCardEq` for the noncomputable definition,
and `Fintype.truncEquivFin` and `Fintype.equivFin` for the bijection `α ≃ Fin (c
ard α)`.
-/
def truncEquivFinOfCardEq [DecidableEq α] {n : ℕ} (h : Fintype.card α = n) : Trunc (α ≃ Fin n) :=
  (truncEquivFin α).map fun e => e.trans (finCongr h)

/-- If the cardinality of `α` is `n`, there is noncomputably a bijection between `α` and `Fin n`.

See `Fintype.truncEquivFinOfCardEq` for the computable definition,
and `Fintype.truncEquivFin` and `Fintype.equivFin` for the bijection `α ≃ Fin (card α)`.
-/
/-
**Fintype.equivFinOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：equivFinOfCardEq {n : Nat} (h : Fintype.card α = n) : α ≃ Fin n
参数：h : Fintype.card α = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the cardinality of `α` is `n`, there is noncomputably a bijection between `α`
 and `Fin n`.

See `Fintype.truncEquivFinOfCardEq` for the computable definition,
and `Fintype.truncEquivFin` and `Fintype.equivFin` for the bijection `α ≃ Fin (c
ard α)`.
-/
noncomputable def equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n :=
  letI := Classical.decEq α
  (truncEquivFinOfCardEq h).out

/-- Two `Fintype`s with the same cardinality are (computably) in bijection.

See `Fintype.equivOfCardEq` for the noncomputable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq` for
the specialization to `Fin`.
-/
/-
**Fintype.truncEquivOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：truncEquivOfCardEq [DecidableEq α] [DecidableEq β] (h : card α = card β) :
 Trunc (α ≃ β)
参数：h : card α = card β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Two `Fintype`s with the same cardinality are (computably) in bijection.

See `Fintype.equivOfCardEq` for the noncomputable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq` for
the specialization to `Fin`.
-/
def truncEquivOfCardEq [DecidableEq α] [DecidableEq β] (h : card α = card β) : Trunc (α ≃ β) :=
  (truncEquivFinOfCardEq h).bind fun e => (truncEquivFin β).map fun e' => e.trans e'.symm

/-- Two `Fintype`s with the same cardinality are (noncomputably) in bijection.

See `Fintype.truncEquivOfCardEq` for the computable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq` for
the specialization to `Fin`.
-/
/-
**Fintype.equivOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：equivOfCardEq (h : card α = card β) : α ≃ β
参数：h : card α = card β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two `Fintype`s with the same cardinality are (noncomputably) in bijection.

See `Fintype.truncEquivOfCardEq` for the computable version,
and `Fintype.truncEquivFinOfCardEq` and `Fintype.equivFinOfCardEq` for
the specialization to `Fin`.
-/
noncomputable def equivOfCardEq (h : card α = card β) : α ≃ β := by
  letI := Classical.decEq α
  letI := Classical.decEq β
  exact (truncEquivOfCardEq h).out

end

/-
**Fintype.card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card α = card β ↔ Nonemp
ty (α ≃ β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.nonempty`：∀ {α : Sort u_1} (q : Trunc α), Nonempty α
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card α = card β ↔ Nonempty (α ≃ β) :=
  ⟨fun h =>
    haveI := Classical.propDecidable
    (truncEquivOfCardEq h).nonempty,
    fun ⟨f⟩ => card_congr f⟩

end Fintype

/-!
### Relation to `Finite`

In this section we prove that `α : Type*` is `Finite` if and only if `Fintype α` is nonempty.
-/

/-
**Fintype.finite** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {α : Type u_4} (_inst : Fintype α), Finite α
参数：_inst : Fintype α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Relation to `Finite`

In this section we prove that `α : Type*` is `Finite` if and only if `Fintype α`
 is nonempty.
-/
protected theorem Fintype.finite {α : Type*} (_inst : Fintype α) : Finite α :=
  ⟨Fintype.equivFin α⟩

set_option linter.unusedFintypeInType false in
/-- For efficiency reasons, we want `Finite` instances to have higher
priority than ones coming from `Fintype` instances. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For efficiency reasons, we want `Finite` instances to have higher
priority than ones coming from `Fintype` instances.
-/
instance (priority := 900) Finite.of_fintype (α : Type*) [Fintype α] : Finite α :=
  Fintype.finite ‹_›
/-
**finite_iff_nonempty_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_iff_nonempty_fintype (α : Type*) : Finite α ↔ Nonempty (Fintype α)
参数：α : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem finite_iff_nonempty_fintype (α : Type*) : Finite α ↔ Nonempty (Fintype α) :=
  ⟨fun _ => nonempty_fintype α, fun ⟨_⟩ => inferInstance⟩

/-- Noncomputably get a `Fintype` instance from a `Finite` instance. This is not an
/-
**because** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance because we want `Fintype` instances to be useful for computations. -/
@[instance_reducible]
/-
**Fintype.ofFinite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fintype.ofFinite (α : Type*) [Finite α] : Fintype α
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)

--- 原说明 ---
Noncomputably get a `Fintype` instance from a `Finite` instance. This is not an
instance because we want `Fintype` instances to be useful for computations.
-/
noncomputable def Fintype.ofFinite (α : Type*) [Finite α] : Fintype α :=
  (nonempty_fintype α).some
/-
**Finite.of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.of_injective {α β : Sort*} [Finite β] (f : α -> β) (H : Injective f
) : Finite α
参数：f : α -> β；H : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_equiv_fin`：Finite.exists_equiv_fin (α : Sort*) [h : Finite
 α] : exists n : Nat, Nonempty (α ≃ Fin n)
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem Finite.of_injective {α β : Sort*} [Finite β] (f : α → β) (H : Injective f) : Finite α := by
  rcases Finite.exists_equiv_fin β with ⟨n, ⟨e⟩⟩
  classical exact .of_equiv (Set.range (e ∘ f)) (Equiv.ofInjective _ (e.injective.comp H)).symm

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Finite.of_subsingleton {α : Sort*} [Subsingleton α] : Finite α :=
  Finite.of_injective (Function.const α ()) <| Function.injective_of_subsingleton _

-- Higher priority for `Prop`s
/-
**instFiniteProp** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instFiniteProp (p : Prop) : Finite p
参数：p : Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
-/
instance instFiniteProp (p : Prop) : Finite p :=
  Finite.of_subsingleton

/-- This instance also provides `[Finite s]` for `s : Set α`. -/
/-
**Subtype.finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.finite {α : Sort*} [Finite α] {p : α -> Prop} : Finite { x // p x 
}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))

--- 原说明 ---
This instance also provides `[Finite s]` for `s : Set α`.
-/
instance Subtype.finite {α : Sort*} [Finite α] {p : α → Prop} : Finite { x // p x } :=
  Finite.of_injective Subtype.val Subtype.coe_injective
/-
**Finite.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.of_surjective {α β : Sort*} [Finite α] (f : α -> β) (H : Surjective
 f) : Finite β
参数：f : α -> β；H : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
-/
theorem Finite.of_surjective {α β : Sort*} [Finite α] (f : α → β) (H : Surjective f) : Finite β :=
  Finite.of_injective _ <| injective_surjInv H
/-
**Quot.finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quot.finite {α : Sort*} [Finite α] (r : α -> α -> Prop) : Finite (Quot r)
参数：r : α -> α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
instance Quot.finite {α : Sort*} [Finite α] (r : α → α → Prop) : Finite (Quot r) :=
  Finite.of_surjective _ Quot.mk_surjective
/-
**Quotient.finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.finite {α : Sort*} [Finite α] (s : Setoid α) : Finite (Quotient s
)
参数：s : Setoid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Quotient.finite {α : Sort*} [Finite α] (s : Setoid α) : Finite (Quotient s) :=
  Quot.finite _

namespace Fintype

variable [Fintype α] [Fintype β]

/-
**Fintype.card_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_eq_one_iff : card α = 1 ↔ exists x : α, forall y, y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_unit`：Fintype.card_unit : Fintype.card Unit = 1
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem card_eq_one_iff : card α = 1 ↔ ∃ x : α, ∀ y, y = x := by
  rw [← card_unit, card_eq]
  exact
    ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.injective (Subsingleton.elim _ _)⟩,
     fun ⟨x, hx⟩ =>
      ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ =>
          Subsingleton.elim _ _⟩⟩⟩
/-
**Fintype.card_eq_one_iff_nonempty_unique** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_eq_one_iff`：card_eq_one_iff : card α = 1 ↔ exists x : α, fo
rall y, y = x
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
-/
theorem card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
    ⟨{  default := d
        uniq := h }⟩,
    fun ⟨_h⟩ => Fintype.card_unique⟩
/-
**Fintype.card_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_le_one_iff : card α <= 1 ↔ forall a b : α, a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Fintype.card_eq_one_iff`：card_eq_one_iff : card α = 1 ↔ exists x : α, fo
rall y, y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Fintype.card_unit`：Fintype.card_unit : Fintype.card Unit = 1
-/
theorem card_le_one_iff : card α ≤ 1 ↔ ∀ a b : α, a = b :=
  let n := card α
  have hn : n = card α := rfl
  match n, hn with
  | 0, ha =>
    ⟨fun _h => fun a => (card_eq_zero_iff.1 ha.symm).elim a, fun _ => ha ▸ Nat.le_succ _⟩
  | 1, ha =>
    ⟨fun _h => fun a b => by
      let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm
      rw [hx a, hx b], fun _ => ha ▸ le_rfl⟩
  | n + 2, ha =>
    ⟨fun h => False.elim <| by rw [← ha] at h; cases h with | step h => cases h; , fun h =>
      card_unit ▸ card_le_of_injective (fun _ => ()) fun _ _ _ => h _ _⟩
/-
**Fintype.card_le_one_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_le_one_iff_subsingleton : card α <= 1 ↔ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Fintype.card_le_one_iff`：card_le_one_iff : card α <= 1 ↔ forall a b : α,
 a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `subsingleton_iff`：subsingleton_iff : Subsingleton α ↔ forall x y : α, x 
= y
-/
theorem card_le_one_iff_subsingleton : card α ≤ 1 ↔ Subsingleton α :=
  card_le_one_iff.trans subsingleton_iff.symm
/-
**Fintype.one_lt_card_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：one_lt_card_iff_nontrivial : 1 < card α ↔ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton : car
d α <= 1 ↔ Subsingleton α
-/
theorem one_lt_card_iff_nontrivial : 1 < card α ↔ Nontrivial α := by
  contrapose!; exact card_le_one_iff_subsingleton
/-
**Fintype.exists_ne_of_one_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : exists b : α, b != a
参数：h : 1 < card α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
-/
theorem exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : ∃ b : α, b ≠ a :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_ne a
/-
**Fintype.exists_pair_of_one_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：exists_pair_of_one_lt_card (h : 1 < card α) : exists a b : α, a != b
参数：h : 1 < card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
-/
theorem exists_pair_of_one_lt_card (h : 1 < card α) : ∃ a b : α, a ≠ b :=
  haveI : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exists_pair_ne α
/-
**Fintype.card_eq_one_of_forall_eq** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：card_eq_one_of_forall_eq {i : α} (h : forall j, j = i) : card α = 1
参数：h : forall j, j = i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq_one_iff`：card_eq_one_iff : card α = 1 ↔ exists x : α, fo
rall y, y = x
-/
theorem card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1 :=
  Fintype.card_eq_one_iff.2 ⟨i, h⟩
/-
**Fintype.one_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
-/
theorem one_lt_card [h : Nontrivial α] : 1 < Fintype.card α :=
  Fintype.one_lt_card_iff_nontrivial.mpr h
/-
**Fintype.one_lt_card_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：one_lt_card_iff : 1 < card α ↔ exists a b : α, a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
-/
theorem one_lt_card_iff : 1 < card α ↔ ∃ a b : α, a ≠ b :=
  one_lt_card_iff_nontrivial.trans nontrivial_iff

end Fintype

namespace Fintype

variable [Fintype α] [Fintype β]

/-
**Fintype.bijective_iff_injective_and_card** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：bijective_iff_injective_and_card (f : α -> β) : Bijective f ↔ Injective f 
∧ card α = card β
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Fintype.card_of_bijective`：card_of_bijective {f : α -> β} (hf : Bijectiv
e f) : card α = card β
· 使用定理 `Function.Injective.surjective_of_finite`：∀ {α : Type u_1} {β : Type u_2}
 [Finite α] {f : α → β} (e : α ≃ β), Function.Injective f → Function.Surjective 
f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem bijective_iff_injective_and_card (f : α → β) :
    Bijective f ↔ Injective f ∧ card α = card β :=
  ⟨fun h => ⟨h.1, card_of_bijective h⟩, fun h =>
    ⟨h.1, h.1.surjective_of_finite <| equivOfCardEq h.2⟩⟩
/-
**Fintype.bijective_iff_surjective_and_card** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：bijective_iff_surjective_and_card (f : α -> β) : Bijective f ↔ Surjective 
f ∧ card α = card β
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Fintype.card_of_bijective`：card_of_bijective {f : α -> β} (hf : Bijectiv
e f) : card α = card β
· 使用定理 `Function.Surjective.injective_of_finite`：∀ {α : Type u_1} {β : Type u_2}
 [Finite α] {f : α → β} (e : α ≃ β), Function.Surjective f → Function.Injective 
f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem bijective_iff_surjective_and_card (f : α → β) :
    Bijective f ↔ Surjective f ∧ card α = card β :=
  ⟨fun h => ⟨h.2, card_of_bijective h⟩, fun h =>
    ⟨h.1.injective_of_finite <| equivOfCardEq h.2, h.1⟩⟩
/-
**Fintype._root_.Function.LeftInverse.rightInverse_of_card_le** 是 Mathlib 中的一个定理
，位于命名空间 `Fintype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.LeftInverse.rightInverse_of_card_le {f : α → β} {g : β → α}
    (hfg : LeftInverse f g) (hcard : card α ≤ card β) : RightInverse f g :=
  have hsurj : Surjective f := surjective_iff_hasRightInverse.2 ⟨g, hfg⟩
  rightInverse_of_injective_of_leftInverse
    ((bijective_iff_surjective_and_card _).2
        ⟨hsurj, le_antisymm hcard (card_le_of_surjective f hsurj)⟩).1
    hfg
/-
**Fintype._root_.Function.RightInverse.leftInverse_of_card_le** 是 Mathlib 中的一个定理
，位于命名空间 `Fintype`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.RightInverse.leftInverse_of_card_le {f : α → β} {g : β → α}
    (hfg : RightInverse f g) (hcard : card β ≤ card α) : LeftInverse f g :=
  Function.LeftInverse.rightInverse_of_card_le hfg hcard

end Fintype

namespace Equiv

variable [Fintype α] [Fintype β]

open Fintype

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
/-
**Equiv.ofLeftInverseOfCardLE** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ofLeftInverseOfCardLE (hβα : card β <= card α) (f : α -> β) (g : β -> α) (
h : LeftInverse g f) : α ≃ β where toFun
参数：hβα : card β <= card α；f : α -> β；g : β -> α；h : LeftInverse g f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.rightInverse_of_card_le`：∀ {α : Type u_1} {β : Type
 u_2} [inst : Fintype α] [inst_1 : Fintype β] {f : α → β} {g : β → α},   Functio
n.LeftInverse f g → Fintype.card α…

--- 原说明 ---
Construct an equivalence from functions that are inverse to each other.
-/
def ofLeftInverseOfCardLE (hβα : card β ≤ card α) (f : α → β) (g : β → α) (h : LeftInverse g f) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv := h
  right_inv := h.rightInverse_of_card_le hβα

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
/-
**Equiv.ofRightInverseOfCardLE** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：ofRightInverseOfCardLE (hαβ : card α <= card β) (f : α -> β) (g : β -> α) 
(h : RightInverse g f) : α ≃ β where toFun
参数：hαβ : card α <= card β；f : α -> β；g : β -> α；h : RightInverse g f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.leftInverse_of_card_le`：∀ {α : Type u_1} {β : Type
 u_2} [inst : Fintype α] [inst_1 : Fintype β] {f : α → β} {g : β → α},   Functio
n.RightInverse f g → Fintype.card …

--- 原说明 ---
Construct an equivalence from functions that are inverse to each other.
-/
def ofRightInverseOfCardLE (hαβ : card α ≤ card β) (f : α → β) (g : β → α) (h : RightInverse g f) :
    α ≃ β where
  toFun := f
  invFun := g
  left_inv := h.leftInverse_of_card_le hαβ
  right_inv := h

end Equiv

/-- Noncomputable equivalence between a finset `s` coerced to a type and `Fin #s`. -/
/-
**Finset.equivFin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finset.equivFin (s : Finset α) : s ≃ Fin #s
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputable equivalence between a finset `s` coerced to a type and `Fin #s`.
-/
noncomputable def Finset.equivFin (s : Finset α) : s ≃ Fin #s :=
  Fintype.equivFinOfCardEq (Fintype.card_coe _)

/-- Noncomputable equivalence between a finset `s` as a fintype and `Fin n`, when there is a
proof that `#s = n`. -/
/-
**Finset.equivFinOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finset.equivFinOfCardEq {s : Finset α} {n : Nat} (h : #s = n) : s ≃ Fin n
参数：h : #s = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputable equivalence between a finset `s` as a fintype and `Fin n`, when th
ere is a
proof that `#s = n`.
-/
noncomputable def Finset.equivFinOfCardEq {s : Finset α} {n : ℕ} (h : #s = n) : s ≃ Fin n :=
  Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h)
/-
**Finset.card_eq_of_equiv_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_eq_of_equiv_fin {s : Finset α} {n : Nat} (i : s ≃ Fin n) : #s 
= n
参数：i : s ≃ Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.equiv_iff_eq`：equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Finset.card_eq_of_equiv_fin {s : Finset α} {n : ℕ} (i : s ≃ Fin n) : #s = n :=
  Fin.equiv_iff_eq.1 ⟨s.equivFin.symm.trans i⟩
/-
**Finset.card_eq_of_equiv_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_eq_of_equiv_fintype {s : Finset α} [Fintype β] (i : s ≃ β) : #
s = Fintype.card β
参数：i : s ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_eq_of_equiv_fin`：Finset.card_eq_of_equiv_fin {s : Finset α} 
{n : Nat} (i : s ≃ Fin n) : #s = n
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem Finset.card_eq_of_equiv_fintype {s : Finset α} [Fintype β] (i : s ≃ β) :
    #s = Fintype.card β := card_eq_of_equiv_fin <| i.trans <| Fintype.equivFin β

/-- Noncomputable equivalence between two finsets `s` and `t` as fintypes when there is a proof
that `#s = #t`. -/
/-
**Finset.equivOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finset.equivOfCardEq {s : Finset α} {t : Finset β} (h : #s = #t) : s ≃ t
参数：h : #s = #t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputable equivalence between two finsets `s` and `t` as fintypes when there
 is a proof
that `#s = #t`.
-/
noncomputable def Finset.equivOfCardEq {s : Finset α} {t : Finset β} (h : #s = #t) :
    s ≃ t := Fintype.equivOfCardEq ((Fintype.card_coe _).trans (h.trans (Fintype.card_coe _).symm))
/-
**Finset.card_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.card_eq_of_equiv {s : Finset α} {t : Finset β} (i : s ≃ t) : #s = #
t
参数：i : s ≃ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_eq_of_equiv_fintype`：Finset.card_eq_of_equiv_fintype {s : Fi
nset α} [Fintype β] (i : s ≃ β) : #s = Fintype.card β
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
-/
theorem Finset.card_eq_of_equiv {s : Finset α} {t : Finset β} (i : s ≃ t) : #s = #t :=
  (card_eq_of_equiv_fintype i).trans (Fintype.card_coe _)

namespace Function.Embedding

/-- An embedding from a `Fintype` to itself can be promoted to an equivalence. -/
/-
**Function.Embedding.equivOfFiniteSelfEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Funct
ion.Embedding`。
形式化陈述：equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) : α ≃ α
参数：e : α ↪ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding from a `Fintype` to itself can be promoted to an equivalence.
-/
noncomputable def equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) : α ≃ α :=
  Equiv.ofBijective e e.2.bijective_of_finite

@[simp]
/-
**Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding** 是 Mathlib 中的一个定理，位
于命名空间 `Function.Embedding`。
形式化陈述：toEmbedding_equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) : e.equivOfF
initeSelfEmbedding.toEmbedding = e
参数：e : α ↪ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
-/
theorem toEmbedding_equivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) :
    e.equivOfFiniteSelfEmbedding.toEmbedding = e := by
  ext
  rfl

/-- On a finite type, equivalence between the self-embeddings and the bijections. -/
/-
**Function.Embedding._root_.Equiv.embeddingEquivOfFinite** 是 Mathlib 中的一个定义，位于命名
空间 `Function.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On a finite type, equivalence between the self-embeddings and the bijections.
-/
@[simps] noncomputable def _root_.Equiv.embeddingEquivOfFinite (α : Type*) [Finite α] :
    (α ↪ α) ≃ (α ≃ α) where
  toFun e := e.equivOfFiniteSelfEmbedding
  invFun e := e.toEmbedding

/-- A constructive embedding of a fintype `α` in another fintype `β` when `card α ≤ card β`. -/
/-
**Function.Embedding.truncOfCardLE** 是 Mathlib 中的一个定义，位于命名空间 `Function.Embedding
`。
形式化陈述：truncOfCardLE [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (h :
 Fintype.card α <= Fintype.card β) : Trunc (α ↪ β)
参数：h : Fintype.card α <= Fintype.card β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A constructive embedding of a fintype `α` in another fintype `β` when `card α ≤ 
card β`.
-/
def truncOfCardLE [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (h : Fintype.card α ≤ Fintype.card β) : Trunc (α ↪ β) :=
  (Fintype.truncEquivFin α).bind fun ea =>
    (Fintype.truncEquivFin β).map fun eb =>
      ea.toEmbedding.trans ((Fin.castLEEmb h).trans eb.symm.toEmbedding)
/-
**Function.Embedding.nonempty_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Function.Emb
edding`。
形式化陈述：nonempty_of_card_le [Fintype α] [Fintype β] (h : Fintype.card α <= Fintype
.card β) : Nonempty (α ↪ β)
参数：h : Fintype.card α <= Fintype.card β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Trunc.nonempty`：∀ {α : Sort u_1} (q : Trunc α), Nonempty α
-/
theorem nonempty_of_card_le [Fintype α] [Fintype β] (h : Fintype.card α ≤ Fintype.card β) :
    Nonempty (α ↪ β) := by classical exact (truncOfCardLE h).nonempty
/-
**Function.Embedding.nonempty_iff_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Function.Em
bedding`。
形式化陈述：nonempty_iff_card_le [Fintype α] [Fintype β] : Nonempty (α ↪ β) ↔ Fintype.
card α <= Fintype.card β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β
· 使用定理 `Function.Embedding.nonempty_of_card_le`：nonempty_of_card_le [Fintype α] 
[Fintype β] (h : Fintype.card α <= Fintype.card β) : Nonempty (α ↪ β)
-/
theorem nonempty_iff_card_le [Fintype α] [Fintype β] :
    Nonempty (α ↪ β) ↔ Fintype.card α ≤ Fintype.card β :=
  ⟨fun ⟨e⟩ => Fintype.card_le_of_embedding e, nonempty_of_card_le⟩
/-
**Function.Embedding.exists_of_card_le_finset** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n.Embedding`。
形式化陈述：exists_of_card_le_finset [Fintype α] {s : Finset β} (h : Fintype.card α <=
 #s) : exists f : α ↪ β, Set.range f subseteq s
参数：h : Fintype.card α <= #s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.nonempty_of_card_le`：nonempty_of_card_le [Fintype α] 
[Fintype β] (h : Fintype.card α <= Fintype.card β) : Nonempty (α ↪ β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem exists_of_card_le_finset [Fintype α] {s : Finset β} (h : Fintype.card α ≤ #s) :
    ∃ f : α ↪ β, Set.range f ⊆ s := by
  rw [← Fintype.card_coe] at h
  rcases nonempty_of_card_le h with ⟨f⟩
  exact ⟨f.trans (Embedding.subtype _), by simp [Set.range_subset_iff]⟩
/-
**Function.Embedding.exists_of_card_eq_finset** 是 Mathlib 中的一个引理，位于命名空间 `Functio
n.Embedding`。
形式化陈述：exists_of_card_eq_finset [Fintype α] {s : Finset β} (hsn : Fintype.card α 
= s.card) : exists f : α ↪ β, Finset.univ.map f = s
参数：hsn : Fintype.card α = s.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.exists_of_card_le_finset`：exists_of_card_le_finset [F
intype α] {s : Finset β} (h : Fintype.card α <= #s) : exists f : α ↪ β, Set.rang
e f subseteq s
· 使用定理 `Nat.le_of_eq`：∀ {n m : ℕ}, n = m → n ≤ m
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
lemma exists_of_card_eq_finset [Fintype α] {s : Finset β} (hsn : Fintype.card α = s.card) :
    ∃ f : α ↪ β, Finset.univ.map f = s := by
  obtain ⟨f : α ↪ β, hf⟩ := exists_of_card_le_finset (Nat.le_of_eq hsn)
  use f
  apply Finset.eq_of_subset_of_card_le
  · simp [← coe_subset, hf]
  · simp [← hsn]

end Function.Embedding

@[simp]
/-
**Finset.univ_map_embedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.univ_map_embedding {α : Type*} [Fintype α] (e : α ↪ α) : univ.map e
 = univ
参数：e : α ↪ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding`：toEmbedding_e
quivOfFiniteSelfEmbedding [Finite α] (e : α ↪ α) : e.equivOfFiniteSelfEmbedding.
toEmbedding = e
· 使用定理 `Finset.univ_map_equiv_to_embedding`：univ_map_equiv_to_embedding {α β : T
ype*} [Fintype α] [Fintype β] (e : α ≃ β) : univ.map e.toEmbedding = univ
-/
theorem Finset.univ_map_embedding {α : Type*} [Fintype α] (e : α ↪ α) : univ.map e = univ := by
  rw [← e.toEmbedding_equivOfFiniteSelfEmbedding, univ_map_equiv_to_embedding]

namespace Fintype

/-
**Fintype.card_lt_of_surjective_not_injective** 是 Mathlib 中的一个定理，位于命名空间 `Fintype
`。
形式化陈述：card_lt_of_surjective_not_injective [Fintype α] [Fintype β] (f : α -> β) (
h : Function.Surjective f) (h' : ¬Function.Injective f) : card β < card α
参数：f : α -> β；h : Function.Surjective f；h' : ¬Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_lt_of_injective_not_surjective`：card_lt_of_injective_not_su
rjective (f : α -> β) (h : Function.Injective f) (h' : ¬Function.Surjective f) :
 card α < card β
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)
· 使用定理 `Function.Surjective.injective_of_finite`：∀ {α : Type u_1} {β : Type u_2}
 [Finite α] {f : α → β} (e : α ≃ β), Function.Surjective f → Function.Injective 
f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem card_lt_of_surjective_not_injective [Fintype α] [Fintype β] (f : α → β)
    (h : Function.Surjective f) (h' : ¬Function.Injective f) : card β < card α :=
  card_lt_of_injective_not_surjective _ (Function.injective_surjInv h) fun hg =>
    have w : Function.Bijective (Function.surjInv h) := ⟨Function.injective_surjInv h, hg⟩
    h' <| h.injective_of_finite (Equiv.ofBijective _ w).symm

end Fintype

/-
**Fintype.false** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {α : Type u_1} [Infinite α] (_h : Fintype α), False
参数：_h : Fintype α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_finite`：not_finite (α : Sort*) [Infinite α] [Finite α] : False
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
protected theorem Fintype.false [Infinite α] (_h : Fintype α) : False :=
  not_finite α

@[simp]
/-
**isEmpty_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_fintype {α : Type*} : IsEmpty (Fintype α) ↔ Infinite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Fintype.finite`：∀ {α : Type u_4} (_inst : Fintype α), Finite α
-/
theorem isEmpty_fintype {α : Type*} : IsEmpty (Fintype α) ↔ Infinite α :=
  ⟨fun ⟨h⟩ => ⟨fun h' => (@nonempty_fintype α h').elim h⟩, fun ⟨h⟩ => ⟨fun h' => h h'.finite⟩⟩

/-- A non-infinite type is a fintype. -/
@[instance_reducible]
/-
**fintypeOfNotInfinite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fintypeOfNotInfinite {α : Type*} (h : ¬Infinite α) : Fintype α
参数：h : ¬Infinite α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-infinite type is a fintype.
-/
noncomputable def fintypeOfNotInfinite {α : Type*} (h : ¬Infinite α) : Fintype α :=
  @Fintype.ofFinite _ (not_infinite_iff_finite.mp h)

section

open scoped Classical in
/-- Any type is (classically) either a `Fintype`, or `Infinite`.

One can obtain the relevant typeclasses via `cases fintypeOrInfinite α`.
-/
/-
**fintypeOrInfinite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fintypeOrInfinite (α : Type*) : Fintype α oplus' Infinite α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type is (classically) either a `Fintype`, or `Infinite`.

One can obtain the relevant typeclasses via `cases fintypeOrInfinite α`.
-/
noncomputable def fintypeOrInfinite (α : Type*) : Fintype α ⊕' Infinite α :=
  if h : Infinite α then PSum.inr h else PSum.inl (fintypeOfNotInfinite h)

end

namespace Infinite

/-
**Infinite.of_not_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：of_not_fintype (h : Fintype α -> False) : Infinite α
参数：h : Fintype α -> False。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isEmpty_fintype`：isEmpty_fintype {α : Type*} : IsEmpty (Fintype α) ↔ Inf
inite α
-/
theorem of_not_fintype (h : Fintype α → False) : Infinite α :=
  isEmpty_fintype.mp ⟨h⟩

/-- If `s : Set α` is a proper subset of `α` and `f : α → s` is injective, then `α` is infinite. -/
/-
**Infinite.of_injective_to_set** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：of_injective_to_set {s : Set α} (hs : s != Set.univ) {f : α -> s} (hf : In
jective f) : Infinite α
参数：hs : s != Set.univ；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_not_fintype`：of_not_fintype (h : Fintype α -> False) : Infin
ite α
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_ssubset_univ`：toFinset_ssubset_univ [Fintype α] {s : Set α}
 [Fintype s] : s.toFinset ⊂ Finset.univ ↔ s ⊂ univ
· 使用定理 `Set.ssubset_univ_iff`：ssubset_univ_iff : s ⊂ univ ↔ s != univ

--- 原说明 ---
If `s : Set α` is a proper subset of `α` and `f : α → s` is injective, then `α` 
is infinite.
-/
theorem of_injective_to_set {s : Set α} (hs : s ≠ Set.univ) {f : α → s} (hf : Injective f) :
    Infinite α :=
  of_not_fintype fun h => by
    classical
      refine lt_irrefl (Fintype.card α) ?_
      calc
        Fintype.card α ≤ Fintype.card s := Fintype.card_le_of_injective f hf
        _ = #s.toFinset := s.toFinset_card.symm
        _ < Fintype.card α :=
          Finset.card_lt_card <| by rwa [Set.toFinset_ssubset_univ, Set.ssubset_univ_iff]

/-- If `s : Set α` is a proper subset of `α` and `f : s → α` is surjective, then `α` is infinite. -/
/-
**Infinite.of_surjective_from_set** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：of_surjective_from_set {s : Set α} (hs : s != Set.univ) {f : s -> α} (hf :
 Surjective f) : Infinite α
参数：hs : s != Set.univ；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective_to_set`：of_injective_to_set {s : Set α} (hs : s !=
 Set.univ) {f : α -> s} (hf : Injective f) : Infinite α
· 使用定理 `Function.injective_surjInv`：injective_surjInv (h : Surjective f) : Injec
tive (surjInv h)

--- 原说明 ---
If `s : Set α` is a proper subset of `α` and `f : s → α` is surjective, then `α`
 is infinite.
-/
theorem of_surjective_from_set {s : Set α} (hs : s ≠ Set.univ) {f : s → α} (hf : Surjective f) :
    Infinite α :=
  of_injective_to_set hs (injective_surjInv hf)
/-
**Infinite.exists_notMem_finset** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：exists_notMem_finset [Infinite α] (s : Finset α) : exists x, x ∉ s
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Fintype.false`：∀ {α : Type u_1} [Infinite α] (_h : Fintype α), False
-/
theorem exists_notMem_finset [Infinite α] (s : Finset α) : ∃ x, x ∉ s :=
  not_forall.1 fun h => Fintype.false ⟨s, h⟩

-- see Note [lower instance priority]
/-
**Infinite.** 是 Mathlib 中的一个实例，位于命名空间 `Infinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (α : Type*) [Infinite α] : Nontrivial α :=
  ⟨let ⟨x, _hx⟩ := exists_notMem_finset (∅ : Finset α)
    let ⟨y, hy⟩ := exists_notMem_finset ({x} : Finset α)
    ⟨y, x, by simpa only [mem_singleton] using hy⟩⟩
/-
**Infinite.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：∀ (α : Type u_4) [Infinite α], Nonempty α
参数：α : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
-/
protected theorem nonempty (α : Type*) [Infinite α] : Nonempty α := by infer_instance
/-
**Infinite.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：of_injective {α β} [Infinite β] (f : β -> α) (hf : Injective f) : Infinite
 α
参数：f : β -> α；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.false`：∀ {α : Sort u_1} [Infinite α], Finite α → False
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
-/
theorem of_injective {α β} [Infinite β] (f : β → α) (hf : Injective f) : Infinite α :=
  ⟨fun _I => (Finite.of_injective f hf).false⟩
/-
**Infinite.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：of_surjective {α β} [Infinite β] (f : α -> β) (hf : Surjective f) : Infini
te α
参数：f : α -> β；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.false`：∀ {α : Sort u_1} [Infinite α], Finite α → False
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
-/
theorem of_surjective {α β} [Infinite β] (f : α → β) (hf : Surjective f) : Infinite α :=
  ⟨fun _I => (Finite.of_surjective f hf).false⟩
/-
**Infinite.** 是 Mathlib 中的一个实例，位于命名空间 `Infinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : α → Type*} [Infinite α] [∀ a, Nonempty (β a)] : Infinite ((a : α) × β a) :=
  Infinite.of_surjective Sigma.fst Sigma.fst_surjective
/-
**Infinite.sigma_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：sigma_of_right {β : α -> Type*} {a : α} [Infinite (β a)] : Infinite ((a : 
α) × β a)
参数：β a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem sigma_of_right {β : α → Type*} {a : α} [Infinite (β a)] :
    Infinite ((a : α) × β a) :=
  Infinite.of_injective (f := fun x ↦ ⟨a,x⟩) fun _ _ ↦ by simp
/-
**Infinite.** 是 Mathlib 中的一个实例，位于命名空间 `Infinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : α → Type*} [Nonempty α] [∀ a, Infinite (β a)] : Infinite ((a : α) × β a) :=
  Infinite.sigma_of_right (a := Classical.arbitrary α)

end Infinite

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Infinite ℕ :=
  Infinite.of_not_fintype <| by
    intro h
    exact (Finset.range _).card_le_univ.not_gt ((Nat.lt_succ_self _).trans_eq (card_range _).symm)
/-
**Int.infinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.infinite : Infinite Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Int.ofNat.inj`：∀ {a a_1 : ℕ}, Int.ofNat a = Int.ofNat a_1 → a = a_1
-/
instance Int.infinite : Infinite ℤ :=
  Infinite.of_injective Int.ofNat fun _ _ => Int.ofNat.inj
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Infinite (Multiset α) :=
  let ⟨x⟩ := ‹Nonempty α›
  Infinite.of_injective (fun n => Multiset.replicate n x) (Multiset.replicate_left_injective _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Infinite (List α) :=
  Infinite.of_surjective ((↑) : List α → Multiset α) Quot.mk_surjective
/-
**String.infinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：String.infinite : Infinite String
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `instInfiniteListOfNonempty`：∀ {α : Type u_1} [Nonempty α], Infinite (Lis
t α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `String.ofList_injective`：∀ {l₁ l₂ : List Char}, String.ofList l₁ = Strin
g.ofList l₂ → l₁ = l₂
-/
instance String.infinite : Infinite String :=
  Infinite.of_injective String.ofList (fun _ _ => String.ofList_injective)
/-
**Infinite.set** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Infinite.set [Infinite α] : Infinite (Set α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `Set.singleton_injective`：singleton_injective : Injective (singleton : α 
-> Set α)
-/
instance Infinite.set [Infinite α] : Infinite (Set α) :=
  Infinite.of_injective singleton Set.singleton_injective
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Infinite α] : Infinite (Finset α) :=
  Infinite.of_injective singleton Finset.singleton_injective
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Infinite α] : Infinite (Option α) :=
  Infinite.of_injective some (Option.some_injective α)
/-
**Sum.infinite_of_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.infinite_of_left [Infinite α] : Infinite (α oplus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
instance Sum.infinite_of_left [Infinite α] : Infinite (α ⊕ β) :=
  Infinite.of_injective Sum.inl Sum.inl_injective
/-
**Sum.infinite_of_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.infinite_of_right [Infinite β] : Infinite (α oplus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
instance Sum.infinite_of_right [Infinite β] : Infinite (α ⊕ β) :=
  Infinite.of_injective Sum.inr Sum.inr_injective
/-
**Prod.infinite_of_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.infinite_of_right [Nonempty α] [Infinite β] : Infinite (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_surjective`：of_surjective {α β} [Infinite β] (f : α -> β) (h
f : Surjective f) : Infinite α
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
-/
instance Prod.infinite_of_right [Nonempty α] [Infinite β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.snd Prod.snd_surjective
/-
**Prod.infinite_of_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.infinite_of_left [Infinite α] [Nonempty β] : Infinite (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_surjective`：of_surjective {α β} [Infinite β] (f : α -> β) (h
f : Surjective f) : Infinite α
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
-/
instance Prod.infinite_of_left [Infinite α] [Nonempty β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.fst Prod.fst_surjective
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Infinite α] : Infinite (Equiv.Perm α) := by
  classical
  obtain ⟨a : α⟩ := Nontrivial.to_nonempty (α := α)
  exact Infinite.of_injective _ (Equiv.swap_injective_of_left a)

namespace Infinite

set_option backward.privateInPublic true in
/-
**Infinite.natEmbeddingAux** 是 Mathlib 中的一个定义，位于命名空间 `Infinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def natEmbeddingAux (α : Type*) [Infinite α] : ℕ → α
  | n =>
    letI := Classical.decEq α
    Classical.choose
      (exists_notMem_finset
        ((Multiset.range n).pmap (fun m (_ : m < n) => natEmbeddingAux _ m) fun _ =>
            Multiset.mem_range.1).toFinset)

set_option backward.privateInPublic true in
/-
**Infinite.natEmbeddingAux_injective** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem natEmbeddingAux_injective (α : Type*) [Infinite α] :
    Function.Injective (natEmbeddingAux α) := by
  rintro m n h
  let := Classical.decEq α
  wlog hmlen : m ≤ n generalizing m n
  · exact (this h.symm <| le_of_not_ge hmlen).symm
  by_contra hmn
  have hmn : m < n := lt_of_le_of_ne hmlen hmn
  refine (Classical.choose_spec (exists_notMem_finset
    ((Multiset.range n).pmap (fun m (_ : m < n) ↦ natEmbeddingAux α m)
      (fun _ ↦ Multiset.mem_range.1)).toFinset)) ?_
  refine Multiset.mem_toFinset.2 (Multiset.mem_pmap.2 ⟨m, Multiset.mem_range.2 hmn, ?_⟩)
  rw [h, natEmbeddingAux]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Embedding of `ℕ` into an infinite type. -/
/-
**Infinite.natEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Infinite`。
形式化陈述：natEmbedding (α : Type*) [Infinite α] : Nat ↪ α
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.Fintype.EquivFin.0.Infinite.natEmbeddingAux_inject
ive`：∀ (α : Type u_4) [inst : Infinite α], Function.Injective (Infinite.natEmbed
dingAux✝ α)

--- 原说明 ---
Embedding of `ℕ` into an infinite type.
-/
noncomputable def natEmbedding (α : Type*) [Infinite α] : ℕ ↪ α :=
  ⟨_, natEmbeddingAux_injective α⟩

/-- See `Infinite.exists_superset_card_eq` for a version that, for an `s : Finset α`,
provides a superset `t : Finset α`, `s ⊆ t` such that `#t` is fixed. -/
/-
**Infinite.exists_subset_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：exists_subset_card_eq (α : Type*) [Infinite α] (n : Nat) : exists s : Fins
et α, #s = n
参数：α : Type*；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n

--- 原说明 ---
See `Infinite.exists_superset_card_eq` for a version that, for an `s : Finset α`
,
provides a superset `t : Finset α`, `s ⊆ t` such that `#t` is fixed.
-/
theorem exists_subset_card_eq (α : Type*) [Infinite α] (n : ℕ) : ∃ s : Finset α, #s = n :=
  ⟨(range n).map (natEmbedding α), by rw [card_map, card_range]⟩

/-- See `Infinite.exists_subset_card_eq` for a version that provides an arbitrary
`s : Finset α` for any cardinality. -/
/-
**Infinite.exists_superset_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Infinite`。
形式化陈述：exists_superset_card_eq [Infinite α] (s : Finset α) (n : Nat) (hn : #s <= 
n) : exists t : Finset α, s subseteq t ∧ #t = n
参数：s : Finset α；n : Nat；hn : #s <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Infinite.exists_notMem_finset`：exists_notMem_finset [Infinite α] (s : Fi
nset α) : exists x, x ∉ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.subset_cons`：subset_cons (h : a ∉ s) : s subseteq s.cons a h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See `Infinite.exists_subset_card_eq` for a version that provides an arbitrary
`s : Finset α` for any cardinality.
-/
theorem exists_superset_card_eq [Infinite α] (s : Finset α) (n : ℕ) (hn : #s ≤ n) :
    ∃ t : Finset α, s ⊆ t ∧ #t = n := by
  induction n generalizing s with
  | zero => exact ⟨s, subset_rfl, Nat.eq_zero_of_le_zero hn⟩
  | succ n IH =>
    rcases hn.eq_or_lt with hn' | hn'
    · exact ⟨s, subset_rfl, hn'⟩
    obtain ⟨t, hs, ht⟩ := IH _ (Nat.le_of_lt_succ hn')
    obtain ⟨x, hx⟩ := exists_notMem_finset t
    refine ⟨Finset.cons x t hx, hs.trans (Finset.subset_cons _), ?_⟩
    simp [ht]

end Infinite

/-- If every finset in a type has bounded cardinality, that type is finite. -/
@[instance_reducible]
/-
**fintypeOfFinsetCardLe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fintypeOfFinsetCardLe {ι : Type*} (n : Nat) (w : forall s : Finset ι, #s <
= n) : Fintype ι
参数：n : Nat；w : forall s : Finset ι, #s <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If every finset in a type has bounded cardinality, that type is finite.
-/
noncomputable def fintypeOfFinsetCardLe {ι : Type*} (n : ℕ) (w : ∀ s : Finset ι, #s ≤ n) :
    Fintype ι := by
  apply fintypeOfNotInfinite
  intro i
  obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  specialize w s
  rw [c] at w
  exact Nat.not_succ_le_self n w
/-
**not_injective_infinite_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_injective_infinite_finite {α β} [Infinite α] [Finite β] (f : α -> β) :
 ¬Injective f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.false`：∀ {α : Sort u_1} [Infinite α], Finite α → False
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
-/
theorem not_injective_infinite_finite {α β} [Infinite α] [Finite β] (f : α → β) : ¬Injective f :=
  fun hf => (Finite.of_injective f hf).false
/-
**Function.Embedding.is_empty** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.Embedding.is_empty {α β} [Infinite α] [Finite β] : IsEmpty (α ↪ β
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `not_injective_infinite_finite`：not_injective_infinite_finite {α β} [Infi
nite α] [Finite β] (f : α -> β) : ¬Injective f
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
instance Function.Embedding.is_empty {α β} [Infinite α] [Finite β] : IsEmpty (α ↪ β) :=
  ⟨fun f => not_injective_infinite_finite f f.2⟩
/-
**not_surjective_finite_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_surjective_finite_infinite {α β} [Finite α] [Infinite β] (f : α -> β) 
: ¬Surjective f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.not_finite`：∀ {α : Sort u_3} [self : Infinite α], ¬Finite α
· 使用定理 `Infinite.of_surjective`：of_surjective {α β} [Infinite β] (f : α -> β) (h
f : Surjective f) : Infinite α
-/
theorem not_surjective_finite_infinite {α β} [Finite α] [Infinite β] (f : α → β) : ¬Surjective f :=
  fun hf => (Infinite.of_surjective f hf).not_finite ‹_›
