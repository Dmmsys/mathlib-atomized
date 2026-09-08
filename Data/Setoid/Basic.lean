/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Equivalence relations

This file defines the complete lattice of equivalence relations on a type, results about the
inductively defined equivalence closure of a binary relation, and the analogues of some isomorphism
theorems for quotients of arbitrary types.

## Implementation notes

The complete lattice instance for equivalence relations could have been defined by lifting
the Galois insertion of equivalence relations on α into binary relations on α, and then using
`CompleteLattice.copy` to define a complete lattice instance with more appropriate
definitional equalities (a similar example is `Filter.CompleteLattice` in
`Mathlib/Order/Filter/Basic.lean`). This does not save space, however, and is less clear.

Partitions are not defined as a separate structure here; users are encouraged to
reason about them using the existing `Setoid` and its infrastructure.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation
-/

@[expose] public section

attribute [refl, simp] Setoid.refl
attribute [symm] Setoid.symm
attribute [trans] Setoid.trans

variable {α β γ : Type*}

namespace Setoid

attribute [ext] ext

/-- Two equivalence relations are equal iff their underlying binary operations are equal. -/
/-
**Setoid.eq_iff_rel_eq** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eq_iff_rel_eq {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ ⇑r₁ = ⇑r₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two equivalence relations are equal iff their underlying binary operations are e
qual.
-/
theorem eq_iff_rel_eq {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ ⇑r₁ = ⇑r₂ :=
  ⟨fun h => h ▸ rfl, fun h => Setoid.ext fun _ _ => h ▸ Iff.rfl⟩

/-- Defining `≤` for equivalence relations. -/
/-
**Setoid.** 是 Mathlib 中的一个实例，位于命名空间 `Setoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defining `≤` for equivalence relations.
-/
instance : LE (Setoid α) :=
  ⟨fun r s => ∀ ⦃x y⦄, r x y → s x y⟩
/-
**Setoid.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：le_def {r s : Setoid α} : r <= s ↔ forall {x y}, r x y -> s x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {r s : Setoid α} : r ≤ s ↔ ∀ {x y}, r x y → s x y :=
  Iff.rfl
/-
**Setoid.le_iff_rel_le** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：le_iff_rel_le {r₁ r₂ : Setoid α} : r₁ <= r₂ ↔ ⇑r₁ <= ⇑r₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff_rel_le {r₁ r₂ : Setoid α} : r₁ ≤ r₂ ↔ ⇑r₁ ≤ ⇑r₂ := Iff.rfl

@[refl]
/-
**Setoid.refl'** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：refl' (r : Setoid α) (x) : r x x
参数：r : Setoid α；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `Setoid.iseqv`：∀ {α : Sort u} [self : Setoid α], Equivalence ⇑self
-/
theorem refl' (r : Setoid α) (x) : r x x := r.iseqv.refl x

@[symm]
/-
**Setoid.symm'** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
参数：r : Setoid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
· 使用定理 `Setoid.iseqv`：∀ {α : Sort u} [self : Setoid α], Equivalence ⇑self
-/
theorem symm' (r : Setoid α) : ∀ {x y}, r x y → r y x := r.iseqv.symm

@[trans]
/-
**Setoid.trans'** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z -> r x z
参数：r : Setoid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
· 使用定理 `Setoid.iseqv`：∀ {α : Sort u} [self : Setoid α], Equivalence ⇑self
-/
theorem trans' (r : Setoid α) : ∀ {x y z}, r x y → r y z → r x z := r.iseqv.trans
/-
**Setoid.comm'** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comm' (s : Setoid α) {x y} : s x y ↔ s y x
参数：s : Setoid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
-/
theorem comm' (s : Setoid α) {x y} : s x y ↔ s y x :=
  ⟨s.symm', s.symm'⟩
/-
**Setoid.comm** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comm [Setoid α] {x y : α} : x ≈ y ↔ y ≈ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
-/
theorem comm [Setoid α] {x y : α} : x ≈ y ↔ y ≈ x :=
  ⟨Setoid.symm, Setoid.symm⟩

open scoped Function -- required for scoped `on` notation

/-- The kernel of a function is an equivalence relation. -/
@[instance_reducible]
/-
**Setoid.ker** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：ker (f : α -> β) : Setoid α
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a function is an equivalence relation.
-/
def ker (f : α → β) : Setoid α :=
  ⟨(· = ·) on f, eq_equivalence.comap f⟩

/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp]
/-
**Setoid.ker_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：ker_mk_eq (r : Setoid α) : ker (@Quotient.mk'' _ r) = r
参数：r : Setoid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y

--- 原说明 ---
The kernel of the quotient map induced by an equivalence relation r equals r.
-/
theorem ker_mk_eq (r : Setoid α) : ker (@Quotient.mk'' _ r) = r :=
  ext fun _ _ => Quotient.eq
/-
**Setoid.ker_apply_mk_out** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：ker_apply_mk_out {f : α -> β} (a : α) : f (⟦a⟧ : Quotient (Setoid.ker f)).
out = f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_out`：Quotient.mk_out {s : Setoid α} (a : α) : s (⟦a⟧ : Quoti
ent s).out a
-/
theorem ker_apply_mk_out {f : α → β} (a : α) : f (⟦a⟧ : Quotient (Setoid.ker f)).out = f a :=
  @Quotient.mk_out _ (Setoid.ker f) a

@[simp]
/-
**Setoid.ker_def** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：ker_def {f : α -> β} {x y : α} : ker f x y ↔ f x = f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_def {f : α → β} {x y : α} : ker f x y ↔ f x = f y :=
  Iff.rfl

/-- Given types `α`, `β`, the product of two equivalence relations `r` on `α` and `s` on `β`:
`(x₁, x₂), (y₁, y₂) ∈ α × β` are related by `r.prod s` iff `x₁` is related to `y₁`
by `r` and `x₂` is related to `y₂` by `s`. -/
@[instance_reducible]
/-
**Setoid.prod** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Setoid α → Setoid β → Setoid (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given types `α`, `β`, the product of two equivalence relations `r` on `α` and `s
` on `β`:
`(x₁, x₂), (y₁, y₂) ∈ α × β` are related by `r.prod s` iff `x₁` is related to `y
₁`
by `r` and `x₂` is related to `y₂` by `s`.
-/
protected def prod (r : Setoid α) (s : Setoid β) :
    Setoid (α × β) where
  r x y := r x.1 y.1 ∧ s x.2 y.2
  iseqv :=
    ⟨fun x => ⟨r.refl' x.1, s.refl' x.2⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩,
      fun h₁ h₂ => ⟨r.trans' h₁.1 h₂.1, s.trans' h₁.2 h₂.2⟩⟩
/-
**Setoid.prod_apply** 是 Mathlib 中的一个引理，位于命名空间 `Setoid`。
形式化陈述：prod_apply {r : Setoid α} {s : Setoid β} {x₁ x₂ : α} {y₁ y₂ : β} : @Setoid
.r _ (r.prod s) (x₁, y₁) (x₂, y₂) ↔ (@Setoid.r _ r x₁ x₂ ∧ @Setoid.r _ s y₁ y₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma prod_apply {r : Setoid α} {s : Setoid β} {x₁ x₂ : α} {y₁ y₂ : β} :
    @Setoid.r _ (r.prod s) (x₁, y₁) (x₂, y₂) ↔ (@Setoid.r _ r x₁ x₂ ∧ @Setoid.r _ s y₁ y₂) :=
  Iff.rfl
/-
**Setoid.piSetoid_apply** 是 Mathlib 中的一个引理，位于命名空间 `Setoid`。
形式化陈述：piSetoid_apply {ι : Sort*} {α : ι -> Sort*} {r : forall i, Setoid (α i)} {
x y : forall i, α i} : @Setoid.r _ (@piSetoid _ _ r) x y ↔ forall i, @Setoid.r _
 (r i) (x i) (y i)
参数：α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma piSetoid_apply {ι : Sort*} {α : ι → Sort*} {r : ∀ i, Setoid (α i)} {x y : ∀ i, α i} :
    @Setoid.r _ (@piSetoid _ _ r) x y ↔ ∀ i, @Setoid.r _ (r i) (x i) (y i) :=
  Iff.rfl

/-- A bijection between the product of two quotients and the quotient by the product of the
equivalence relations. -/
@[simps]
/-
**Setoid.prodQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：prodQuotientEquiv (r : Setoid α) (s : Setoid β) : Quotient r × Quotient s 
≃ Quotient (r.prod s) where toFun | (x, y) => Quotient.map₂ Prod.mk (fun _ _ hx 
_ _ hy => ⟨hx, hy⟩) x y invFun q
参数：r : Setoid α；s : Setoid β。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
A bijection between the product of two quotients and the quotient by the product
 of the
equivalence relations.
-/
def prodQuotientEquiv (r : Setoid α) (s : Setoid β) :
    Quotient r × Quotient s ≃ Quotient (r.prod s) where
  toFun | (x, y) => Quotient.map₂ Prod.mk (fun _ _ hx _ _ hy ↦ ⟨hx, hy⟩) x y
  invFun q := Quotient.liftOn' q (fun xy ↦ (Quotient.mk'' xy.1, Quotient.mk'' xy.2))
    fun x y hxy ↦ Prod.ext (by simpa [Quotient.eq] using hxy.1) (by simpa [Quotient.eq] using hxy.2)
  left_inv q := by
    rcases q with ⟨qa, qb⟩
    induction qa, qb using Quotient.inductionOn₂'
    rfl
  right_inv q := by induction q using Quotient.inductionOn'; rfl

/-- A bijection between an indexed product of quotients and the quotient by the product of the
equivalence relations. -/
@[simps]
/-
**Setoid.piQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：piQuotientEquiv {ι : Sort*} {α : ι -> Sort*} (r : forall i, Setoid (α i)) 
: (forall i, Quotient (r i)) ≃ Quotient (@piSetoid _ _ r) where toFun x
参数：r : forall i, Setoid (α i)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
A bijection between an indexed product of quotients and the quotient by the prod
uct of the
equivalence relations.
-/
noncomputable def piQuotientEquiv {ι : Sort*} {α : ι → Sort*} (r : ∀ i, Setoid (α i)) :
    (∀ i, Quotient (r i)) ≃ Quotient (@piSetoid _ _ r) where
  toFun x := Quotient.mk'' fun i ↦ (x i).out
  invFun q := Quotient.liftOn' q (fun x i ↦ Quotient.mk'' (x i)) fun x y hxy ↦ by
    ext i
    simpa [Quotient.eq] using hxy i
  left_inv q := by
    ext i
    simp
  right_inv q := by
    induction q using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'', Quotient.eq'']
    intro i
    change Setoid.r _ _
    rw [← Quotient.eq'']
    simp

/-- The infimum of two equivalence relations. -/
/-
**Setoid.** 是 Mathlib 中的一个实例，位于命名空间 `Setoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of two equivalence relations.
-/
instance : Min (Setoid α) :=
  ⟨fun r s =>
    ⟨fun x y => r x y ∧ s x y,
      ⟨fun x => ⟨r.refl' x, s.refl' x⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩, fun h1 h2 =>
        ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

/-- The infimum of 2 equivalence relations r and s is the same relation as the infimum
of the underlying binary operations. -/
/-
**Setoid.inf_def** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：inf_def {r s : Setoid α} : ⇑(r ⊓ s) = ⇑r ⊓ ⇑s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of 2 equivalence relations r and s is the same relation as the infim
um
of the underlying binary operations.
-/
theorem inf_def {r s : Setoid α} : ⇑(r ⊓ s) = ⇑r ⊓ ⇑s :=
  rfl
/-
**Setoid.inf_iff_and** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：inf_iff_and {r s : Setoid α} {x y} : (r ⊓ s) x y ↔ r x y ∧ s x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inf_iff_and {r s : Setoid α} {x y} : (r ⊓ s) x y ↔ r x y ∧ s x y :=
  Iff.rfl

/-- The infimum of a set of equivalence relations. -/
/-
**Setoid.** 是 Mathlib 中的一个实例，位于命名空间 `Setoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of a set of equivalence relations.
-/
instance : InfSet (Setoid α) :=
  ⟨fun S =>
    { r := fun x y => ∀ r ∈ S, r x y
      iseqv := ⟨fun x r _ => r.refl' x, fun h r hr => r.symm' <| h r hr, fun h1 h2 r hr =>
        r.trans' (h1 r hr) <| h2 r hr⟩ }⟩

/-- The underlying binary operation of the infimum of a set of equivalence relations
is the infimum of the set's image under the map to the underlying binary operation. -/
/-
**Setoid.sInf_def** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：sInf_def {s : Set (Setoid α)} : ⇑(sInf s) = sInf ((⇑) '' s)
参数：Setoid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The underlying binary operation of the infimum of a set of equivalence relations
is the infimum of the set's image under the map to the underlying binary operati
on.
-/
theorem sInf_def {s : Set (Setoid α)} : ⇑(sInf s) = sInf ((⇑) '' s) := by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl
/-
**Setoid.** 是 Mathlib 中的一个实例，位于命名空间 `Setoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Setoid α) where
  lt r s := r ≤ s ∧ ¬s ≤ r
  le_refl _ _ _ := id
  le_trans _ _ _ hr hs _ _ h := hs <| hr h
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm _ _ h1 h2 := Setoid.ext fun _ _ => ⟨fun h => h1 h, fun h => h2 h⟩

/-- The complete lattice of equivalence relations on a type, with bottom element `=`
and top element the trivial equivalence relation. -/
/-
**Setoid.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `Setoid`。
形式化陈述：completeLattice : CompleteLattice (Setoid α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
The complete lattice of equivalence relations on a type, with bottom element `=`
and top element the trivial equivalence relation.
-/
instance completeLattice : CompleteLattice (Setoid α) :=
  { (completeLatticeOfInf (Setoid α)) fun _ =>
      ⟨fun _ hr _ _ h => h _ hr, fun _ hr _ _ h _ hr' => hr hr' h⟩ with
    inf := Min.min
    inf_le_left := fun _ _ _ _ h => h.1
    inf_le_right := fun _ _ _ _ h => h.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 h, h2 h⟩
    top := ⟨fun _ _ => True, ⟨fun _ => trivial, fun h => h, fun h1 _ => h1⟩⟩
    le_top := fun _ _ _ _ => trivial
    bot := ⟨(· = ·), ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
    bot_le := fun r x _ h => h ▸ r.2.1 x }

@[simp, grind =]
/-
**Setoid.top_def** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：top_def : ⇑(⊤ : Setoid α) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_def : ⇑(⊤ : Setoid α) = ⊤ :=
  rfl

@[simp, grind =]
/-
**Setoid.bot_def** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：bot_def : ⇑(⊥ : Setoid α) = (· = ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_def : ⇑(⊥ : Setoid α) = (· = ·) :=
  rfl
/-
**Setoid.mk_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (iseqv : Equivalence r), { r := r, ise
qv := iseqv } = ⊤ ↔ r = ⊤
参数：iseqv : Equivalence r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mk_eq_top {r : α → α → Prop} (iseqv) : mk r iseqv = ⊤ ↔ r = ⊤ := by
  simp [eq_iff_rel_eq]
/-
**Setoid.mk_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (iseqv : Equivalence r), { r := r, ise
qv := iseqv } = ⊥ ↔ r = fun x1 x2 => x1 = x2
参数：iseqv : Equivalence r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mk_eq_bot {r : α → α → Prop} (iseqv) : mk r iseqv = ⊥ ↔ r = (· = ·) := by
  simp [eq_iff_rel_eq]
/-
**Setoid.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eq_top_iff {s : Setoid α} : s = (⊤ : Setoid α) ↔ forall x y : α, s x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Setoid.le_def`：le_def {r s : Setoid α} : r <= s ↔ forall {x y}, r x y ->
 s x y
· 使用定理 `Setoid.top_def`：top_def : ⇑(⊤ : Setoid α) = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_top_iff {s : Setoid α} : s = (⊤ : Setoid α) ↔ ∀ x y : α, s x y := by
  rw [_root_.eq_top_iff, Setoid.le_def, Setoid.top_def]
  simp only [Pi.top_apply, Prop.top_eq_true, forall_true_left]

@[simp]
/-
**Setoid.ker_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：ker_eq_bot_iff {f : α -> β} : ker f = ⊥ ↔ f.Injective
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
theorem ker_eq_bot_iff {f : α → β} : ker f = ⊥ ↔ f.Injective := le_bot_iff.symm
/-
**Setoid.sInf_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Setoid`。
形式化陈述：sInf_equiv {S : Set (Setoid α)} {x y : α} : letI
参数：Setoid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sInf_equiv {S : Set (Setoid α)} {x y : α} :
    letI := sInf S
    x ≈ y ↔ ∀ s ∈ S, s x y := Iff.rfl
/-
**Setoid.sInf_iff** 是 Mathlib 中的一个引理，位于命名空间 `Setoid`。
形式化陈述：sInf_iff {S : Set (Setoid α)} {x y : α} : sInf S x y ↔ forall s in S, s x 
y
参数：Setoid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sInf_iff {S : Set (Setoid α)} {x y : α} :
    sInf S x y ↔ ∀ s ∈ S, s x y := Iff.rfl
/-
**Setoid.quotient_mk_sInf_eq** 是 Mathlib 中的一个引理，位于命名空间 `Setoid`。
形式化陈述：quotient_mk_sInf_eq {S : Set (Setoid α)} {x y : α} : Quotient.mk (sInf S) 
x = Quotient.mk (sInf S) y ↔ forall s in S, s x y
参数：Setoid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma quotient_mk_sInf_eq {S : Set (Setoid α)} {x y : α} :
    Quotient.mk (sInf S) x = Quotient.mk (sInf S) y ↔ ∀ s ∈ S, s x y := by
  simp [sInf_iff, Quotient.eq]

/-- The map induced between quotients by a setoid inequality. -/
/-
**Setoid.map_of_le** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：map_of_le {s t : Setoid α} (h : s <= t) : Quotient s -> Quotient t
参数：h : s <= t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
The map induced between quotients by a setoid inequality.
-/
def map_of_le {s t : Setoid α} (h : s ≤ t) : Quotient s → Quotient t :=
  Quotient.map' id h

/-- The map from the quotient of the infimum of a set of setoids into the quotient
by an element of this set. -/
/-
**Setoid.map_sInf** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：map_sInf {S : Set (Setoid α)} {s : Setoid α} (h : s in S) : Quotient (sInf
 S) -> Quotient s
参数：Setoid α；h : s in S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the quotient of the infimum of a set of setoids into the quotient
by an element of this set.
-/
def map_sInf {S : Set (Setoid α)} {s : Setoid α} (h : s ∈ S) :
    Quotient (sInf S) → Quotient s :=
  Setoid.map_of_le fun _ _ a ↦ a s h

/-- The quotient by the trivial relation is equivalent to the original space. -/
/-
**Setoid.quotientBotEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：quotientBotEquiv : Quotient (⊥ : Setoid α) ≃ α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The quotient by the trivial relation is equivalent to the original space.
-/
def quotientBotEquiv :
    Quotient (⊥ : Setoid α) ≃ α where
  toFun := Quotient.lift id (fun _ _ ↦ id)
  invFun := Quotient.mk''
  left_inv := Quotient.ind fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

section EqvGen

open Relation

/-- The inductively defined equivalence closure of a binary relation r is the infimum
of the set of all equivalence relations containing r. -/
/-
**Setoid.eqvGen_eq** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eqvGen_eq (r : α -> α -> Prop) : EqvGen.setoid r = sInf { s : Setoid α | f
orall ⦃x y⦄, r x y -> s x y }
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
The inductively defined equivalence closure of a binary relation r is the infimu
m
of the set of all equivalence relations containing r.
-/
theorem eqvGen_eq (r : α → α → Prop) :
    EqvGen.setoid r = sInf { s : Setoid α | ∀ ⦃x y⦄, r x y → s x y } :=
  le_antisymm
    (fun _ _ H =>
      EqvGen.rec (fun _ _ h _ hs => hs h) (refl' _) (fun _ _ _ => symm' _)
        (fun _ _ _ _ _ => trans' _) H)
    (sInf_le fun _ _ h => EqvGen.rel _ _ h)

/-- The supremum of two equivalence relations r and s is the equivalence closure of the binary
relation `x is related to y by r or s`. -/
/-
**Setoid.sup_eq_eqvGen** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：sup_eq_eqvGen (r s : Setoid α) : r ⊔ s = EqvGen.setoid fun x y => r x y ∨ 
s x y
参数：r s : Setoid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.eqvGen_eq`：eqvGen_eq (r : α -> α -> Prop) : EqvGen.setoid r = sIn
f { s : Setoid α | forall ⦃x y⦄, r x y -> s x y }
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The supremum of two equivalence relations r and s is the equivalence closure of 
the binary
relation `x is related to y by r or s`.
-/
theorem sup_eq_eqvGen (r s : Setoid α) :
    r ⊔ s = EqvGen.setoid fun x y => r x y ∨ s x y := by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [le_def, or_imp, ← forall_and]

/-- The supremum of 2 equivalence relations r and s is the equivalence closure of the
supremum of the underlying binary operations. -/
/-
**Setoid.sup_def** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：sup_def {r s : Setoid α} : r ⊔ s = EqvGen.setoid (⇑r ⊔ ⇑s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.sup_eq_eqvGen`：sup_eq_eqvGen (r s : Setoid α) : r ⊔ s = EqvGen.se
toid fun x y => r x y ∨ s x y

--- 原说明 ---
The supremum of 2 equivalence relations r and s is the equivalence closure of th
e
supremum of the underlying binary operations.
-/
theorem sup_def {r s : Setoid α} : r ⊔ s = EqvGen.setoid (⇑r ⊔ ⇑s) := by
  rw [sup_eq_eqvGen]; rfl

/-- The supremum of a set S of equivalence relations is the equivalence closure of the binary
relation `there exists r ∈ S relating x and y`. -/
/-
**Setoid.sSup_eq_eqvGen** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：sSup_eq_eqvGen (S : Set (Setoid α)) : sSup S = EqvGen.setoid fun x y => ex
ists r : Setoid α, r in S ∧ r x y
参数：S : Set (Setoid α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.eqvGen_eq`：eqvGen_eq (r : α -> α -> Prop) : EqvGen.setoid r = sIn
f { s : Setoid α | forall ⦃x y⦄, r x y -> s x y }
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b

--- 原说明 ---
The supremum of a set S of equivalence relations is the equivalence closure of t
he binary
relation `there exists r ∈ S relating x and y`.
-/
theorem sSup_eq_eqvGen (S : Set (Setoid α)) :
    sSup S = EqvGen.setoid fun x y => ∃ r : Setoid α, r ∈ S ∧ r x y := by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [upperBounds, le_def, and_imp, exists_imp]
  ext
  exact ⟨fun H x y r hr => H hr, fun H r hr x y => H r hr⟩

/-- The supremum of a set of equivalence relations is the equivalence closure of the
supremum of the set's image under the map to the underlying binary operation. -/
/-
**Setoid.sSup_def** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：sSup_def {s : Set (Setoid α)} : sSup s = EqvGen.setoid (sSup ((⇑) '' s))
参数：Setoid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.sSup_eq_eqvGen`：sSup_eq_eqvGen (S : Set (Setoid α)) : sSup S = Eq
vGen.setoid fun x y => exists r : Setoid α, r in S ∧ r x y
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The supremum of a set of equivalence relations is the equivalence closure of the
supremum of the set's image under the map to the underlying binary operation.
-/
theorem sSup_def {s : Set (Setoid α)} : sSup s = EqvGen.setoid (sSup ((⇑) '' s)) := by
  rw [sSup_eq_eqvGen, sSup_image]
  congr with (x y)
  simp only [iSup_apply, iSup_Prop_eq, exists_prop]

/-- The equivalence closure of an equivalence relation r is r. -/
@[simp]
/-
**Setoid.eqvGen_of_setoid** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eqvGen_of_setoid (r : Setoid α) : EqvGen.setoid r.r = r
参数：r : Setoid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.eqvGen_eq`：eqvGen_eq (r : α -> α -> Prop) : EqvGen.setoid r = sIn
f { s : Setoid α | forall ⦃x y⦄, r x y -> s x y }
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
The equivalence closure of an equivalence relation r is r.
-/
theorem eqvGen_of_setoid (r : Setoid α) : EqvGen.setoid r.r = r :=
  le_antisymm (by rw [eqvGen_eq]; exact sInf_le fun _ _ => id) EqvGen.rel

/-- Equivalence closure is idempotent. -/
/-
**Setoid.eqvGen_idem** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eqvGen_idem (r : α -> α -> Prop) : EqvGen.setoid (EqvGen.setoid r) = EqvGe
n.setoid r
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.eqvGen_of_setoid`：eqvGen_of_setoid (r : Setoid α) : EqvGen.setoid
 r.r = r

--- 原说明 ---
Equivalence closure is idempotent.
-/
theorem eqvGen_idem (r : α → α → Prop) : EqvGen.setoid (EqvGen.setoid r) = EqvGen.setoid r :=
  eqvGen_of_setoid _

/-- The equivalence closure of a binary relation r is contained in any equivalence
relation containing r. -/
/-
**Setoid.eqvGen_le** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eqvGen_le {r : α -> α -> Prop} {s : Setoid α} (h : forall x y, r x y -> s 
x y) : EqvGen.setoid r <= s
参数：h : forall x y, r x y -> s x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.eqvGen_eq`：eqvGen_eq (r : α -> α -> Prop) : EqvGen.setoid r = sIn
f { s : Setoid α | forall ⦃x y⦄, r x y -> s x y }
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
The equivalence closure of a binary relation r is contained in any equivalence
relation containing r.
-/
theorem eqvGen_le {r : α → α → Prop} {s : Setoid α} (h : ∀ x y, r x y → s x y) :
    EqvGen.setoid r ≤ s := by rw [eqvGen_eq]; exact sInf_le h

/-- Equivalence closure of binary relations is monotone. -/
/-
**Setoid.eqvGen_mono** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eqvGen_mono {r s : α -> α -> Prop} (h : forall x y, r x y -> s x y) : EqvG
en.setoid r <= EqvGen.setoid s
参数：h : forall x y, r x y -> s x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.eqvGen_le`：eqvGen_le {r : α -> α -> Prop} {s : Setoid α} (h : for
all x y, r x y -> s x y) : EqvGen.setoid r <= s

--- 原说明 ---
Equivalence closure of binary relations is monotone.
-/
theorem eqvGen_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) :
    EqvGen.setoid r ≤ EqvGen.setoid s :=
  eqvGen_le fun _ _ hr => EqvGen.rel _ _ <| h _ _ hr

/-- There is a Galois insertion of equivalence relations on α into binary relations
on α, with equivalence closure the lower adjoint. -/
/-
**Setoid.gi** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：gi : @GaloisInsertion (α -> α -> Prop) (Setoid α) _ _ EqvGen.setoid (⇑) wh
ere choice r _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a Galois insertion of equivalence relations on α into binary relations
on α, with equivalence closure the lower adjoint.
-/
def gi : @GaloisInsertion (α → α → Prop) (Setoid α) _ _ EqvGen.setoid (⇑) where
  choice r _ := EqvGen.setoid r
  gc _ s := ⟨fun H _ _ h => H <| EqvGen.rel _ _ h, fun H => eqvGen_of_setoid s ▸ eqvGen_mono H⟩
  le_l_u x := (eqvGen_of_setoid x).symm ▸ le_refl x
  choice_eq _ _ := rfl

end EqvGen

open Function

/-- A function from α to β is injective iff its kernel is the bottom element of the complete lattice
of equivalence relations on α. -/
/-
**Setoid.injective_iff_ker_bot** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：injective_iff_ker_bot (f : α -> β) : Injective f ↔ ker f = ⊥
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥

--- 原说明 ---
A function from α to β is injective iff its kernel is the bottom element of the 
complete lattice
of equivalence relations on α.
-/
theorem injective_iff_ker_bot (f : α → β) : Injective f ↔ ker f = ⊥ :=
  (@eq_bot_iff (Setoid α) _ _ (ker f)).symm

/-- The elements related to x ∈ α by the kernel of f are those in the preimage of f(x) under f. -/
/-
**Setoid.ker_iff_mem_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：ker_iff_mem_preimage {f : α -> β} {x y} : ker f x y ↔ x in f ⁻¹' {f y}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The elements related to x ∈ α by the kernel of f are those in the preimage of f(
x) under f.
-/
theorem ker_iff_mem_preimage {f : α → β} {x y} : ker f x y ↔ x ∈ f ⁻¹' {f y} :=
  Iff.rfl

/-- Equivalence between functions `α → β` such that `r x y → f x = f y` and functions
`quotient r → β`. -/
/-
**Setoid.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：liftEquiv (r : Setoid α) : { f : α -> β // r <= ker f } ≃ (Quotient r -> β
) where toFun f
参数：r : Setoid α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Equivalence between functions `α → β` such that `r x y → f x = f y` and function
s
`quotient r → β`.
-/
def liftEquiv (r : Setoid α) : { f : α → β // r ≤ ker f } ≃ (Quotient r → β) where
  toFun f := Quotient.lift (f : α → β) f.2
  invFun f := ⟨f ∘ Quotient.mk'', fun x y h => by simp [ker_def, Quotient.sound' h]⟩
  right_inv _ := funext fun x => Quotient.inductionOn' x fun _ => rfl

/-- The uniqueness part of the universal property for quotients of an arbitrary type. -/
/-
**Setoid.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：lift_unique {r : Setoid α} {f : α -> β} (H : r <= ker f) (g : Quotient r -
> β) (Hg : f = g ∘ Quotient.mk'') : Quotient.lift f H = g
参数：H : r <= ker f；g : Quotient r -> β；Hg : f = g ∘ Quotient.mk''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.mk.eq_1`：∀ {α : Sort u} (s : Setoid α) (a : α), ⟦a⟧ = Quot.mk (
⇑s) a
· 使用定理 `Quotient.lift_mk`：Quotient.lift_mk {s : Setoid α} (f : α -> β) (h : fora
ll a b : α, a ≈ b -> f a = f b) (x : α) : Quotient.lift f h (Quotient.mk s x) = 
f x
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Quotient.mk''_eq_mk`：∀ {α : Sort u_1} {s : Setoid α}, Quotient.mk'' = Qu
otient.mk s

--- 原说明 ---
The uniqueness part of the universal property for quotients of an arbitrary type
.
-/
theorem lift_unique {r : Setoid α} {f : α → β} (H : r ≤ ker f) (g : Quotient r → β)
    (Hg : f = g ∘ Quotient.mk'') : Quotient.lift f H = g := by
  ext ⟨x⟩
  rw [← Quotient.mk, Quotient.lift_mk f H, Hg, Function.comp_apply, Quotient.mk''_eq_mk]

/-- Given a function `f`, lift it to the quotient by its kernel. -/
/-
**Setoid.kerLift** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：kerLift (f : α -> β) : Quotient (ker f) -> β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f`, lift it to the quotient by its kernel.
-/
def kerLift (f : α → β) : Quotient (ker f) → β :=
  Quotient.lift f fun _ _ ↦ id

@[simp]
/-
**Setoid.kerLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：kerLift_mk (f : α -> β) (x : α) : kerLift f ⟦x⟧ = f x
参数：f : α -> β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem kerLift_mk (f : α → β) (x : α) : kerLift f ⟦x⟧ = f x :=
  rfl

/-- Given a map f from α to β, the natural map from the quotient of α by the kernel of f is
injective. -/
/-
**Setoid.kerLift_injective** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：kerLift_injective (f : α -> β) : Injective kerLift f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b

--- 原说明 ---
Given a map f from α to β, the natural map from the quotient of α by the kernel 
of f is
injective.
-/
theorem kerLift_injective (f : α → β) : Injective <| kerLift f :=
  fun x y => Quotient.inductionOn₂' x y fun _ _ h => Quotient.sound' h

/-- Given a map f from α to β, the kernel of f is the unique equivalence relation on α whose
induced map from the quotient of α to β is injective. -/
/-
**Setoid.ker_eq_lift_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：ker_eq_lift_of_injective {r : Setoid α} (f : α -> β) (H : r <= ker f) (h :
 Injective (Quotient.lift f H)) : ker f = r
参数：f : α -> β；H : r <= ker f；h : Injective (Quotient.lift f H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b

--- 原说明 ---
Given a map f from α to β, the kernel of f is the unique equivalence relation on
 α whose
induced map from the quotient of α to β is injective.
-/
theorem ker_eq_lift_of_injective {r : Setoid α} (f : α → β) (H : r ≤ ker f)
    (h : Injective (Quotient.lift f H)) : ker f = r :=
  le_antisymm
    (fun x y hk =>
      Quotient.exact <| h <| show Quotient.lift f H ⟦x⟧ = Quotient.lift f H ⟦y⟧ from hk)
    H
/-
**Setoid.lift_injective_iff_ker_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：lift_injective_iff_ker_eq_of_le {r : Setoid α} {f : α -> β} (hle : r <= ke
r f) : Injective (Quotient.lift f hle) ↔ ker f = r
参数：hle : r <= ker f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ker_eq_lift_of_injective`：ker_eq_lift_of_injective {r : Setoid α}
 (f : α -> β) (H : r <= ker f) (h : Injective (Quotient.lift f H)) : ker f = r
· 使用定理 `Setoid.kerLift_injective`：kerLift_injective (f : α -> β) : Injective ker
Lift f
-/
theorem lift_injective_iff_ker_eq_of_le {r : Setoid α} {f : α → β}
    (hle : r ≤ ker f) : Injective (Quotient.lift f hle) ↔ ker f = r :=
  ⟨ker_eq_lift_of_injective f hle, fun h ↦ h ▸ kerLift_injective _⟩

variable (r : Setoid α) (f : α → β)

/-- The image of `f` lifted to the quotient by its kernel is equal to the image of `f` itself. -/
/-
**Setoid.range_kerLift_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β), Set.range (Setoid.kerLift f) 
= Set.range f
参数：f : α → β；Setoid.kerLift f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_quotient_lift`：range_quotient_lift [s : Setoid ι] (hf) : range
 (Quotient.lift f hf : Quotient s -> α) = range f

--- 原说明 ---
The image of `f` lifted to the quotient by its kernel is equal to the image of `
f` itself.
-/
@[simp] theorem range_kerLift_eq_range : Set.range (kerLift f) = Set.range f :=
  Set.range_quotient_lift (s := ker f) _

/-- The quotient of `α` by the kernel of a function `f`
bijects with the image of `f` lifted to the quotient. -/
/-
**Setoid.quotientKerEquivRangeKerLift** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：quotientKerEquivRangeKerLift : Quotient (ker f) ≃ Set.range (kerLift f)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.kerLift_injective`：kerLift_injective (f : α -> β) : Injective ker
Lift f

--- 原说明 ---
The quotient of `α` by the kernel of a function `f`
bijects with the image of `f` lifted to the quotient.
-/
noncomputable def quotientKerEquivRangeKerLift : Quotient (ker f) ≃ Set.range (kerLift f) :=
  .ofInjective _ <| kerLift_injective _

/-- The first isomorphism theorem for sets: the quotient of α by the kernel of a function f
bijects with f's image. -/
/-
**Setoid.quotientKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：quotientKerEquivRange : Quotient (ker f) ≃ Set.range f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Setoid.range_kerLift_eq_range`：∀ {α : Type u_1} {β : Type u_2} (f : α → 
β), Set.range (Setoid.kerLift f) = Set.range f

--- 原说明 ---
The first isomorphism theorem for sets: the quotient of α by the kernel of a fun
ction f
bijects with f's image.
-/
noncomputable def quotientKerEquivRange : Quotient (ker f) ≃ Set.range f :=
  quotientKerEquivRangeKerLift _ |>.trans <| .setCongr <| range_kerLift_eq_range _

/-- If `f` has a computable right-inverse, then the quotient by its kernel is equivalent to its
domain. -/
@[simps]
/-
**Setoid.quotientKerEquivOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：quotientKerEquivOfRightInverse (g : β -> α) (hf : Function.RightInverse g 
f) : Quotient (ker f) ≃ β where toFun
参数：g : β -> α；hf : Function.RightInverse g f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
If `f` has a computable right-inverse, then the quotient by its kernel is equiva
lent to its
domain.
-/
def quotientKerEquivOfRightInverse (g : β → α) (hf : Function.RightInverse g f) :
    Quotient (ker f) ≃ β where
  toFun := kerLift f
  invFun b := Quotient.mk'' (g b)
  left_inv a := Quotient.inductionOn' a fun a => Quotient.sound' <| hf (f a)
  right_inv := hf

/-- The quotient of α by the kernel of a surjective function f bijects with f's codomain.

If a specific right-inverse of `f` is known, `Setoid.quotientKerEquivOfRightInverse` can be
definitionally more useful. -/
/-
**Setoid.quotientKerEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：quotientKerEquivOfSurjective (hf : Surjective f) : Quotient (ker f) ≃ β
参数：hf : Surjective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f

--- 原说明 ---
The quotient of α by the kernel of a surjective function f bijects with f's codo
main.

If a specific right-inverse of `f` is known, `Setoid.quotientKerEquivOfRightInve
rse` can be
definitionally more useful.
-/
noncomputable def quotientKerEquivOfSurjective (hf : Surjective f) : Quotient (ker f) ≃ β :=
  quotientKerEquivOfRightInverse _ (Function.surjInv hf) (rightInverse_surjInv hf)

variable {r f}

/-- Given a function `f : α → β` and equivalence relation `r` on `α`, the equivalence
closure of the relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are
related to the elements of `f⁻¹(y)` by `r`.' -/
@[instance_reducible]
/-
**Setoid.map** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：map (r : Setoid α) (f : α -> β) : Setoid β
参数：r : Setoid α；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : α → β` and equivalence relation `r` on `α`, the equivalenc
e
closure of the relation on `f`'s image defined by '`x ≈ y` iff the elements of `
f⁻¹(x)` are
related to the elements of `f⁻¹(y)` by `r`.'
-/
def map (r : Setoid α) (f : α → β) : Setoid β :=
  Relation.EqvGen.setoid (Relation.Map r f f)
/-
**Setoid.coe_map_of_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：coe_map_of_ker_le (r : Setoid α) (f : α -> β) (hf : ker f <= r) : ⇑(map r 
f) = Relation.Map r f f ⊔ (· = ·)
参数：r : Setoid α；f : α -> β；hf : ker f <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `Std.Symm.map`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [Std.Sy
mm r] (f : α → β), Std.Symm (Relation.Map r f f)
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Quotient.instIsEquivEquiv`：∀ {α : Type u_4} [inst : Setoid α], IsEquiv α
 fun x1 x2 => x1 ≈ x2
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `IsTrans.map`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [IsTrans
 α r] {f : α → β},   (∀ (x y : α), f x = f y → r x y) → IsTrans β (Relation.Map 
r…
· 使用定理 `Equivalence.isTrans`：Equivalence.isTrans (h : Equivalence r) : IsTrans α
 r
· 使用定理 `Setoid.iseqv`：∀ {α : Sort u} [self : Setoid α], Equivalence ⇑self
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem coe_map_of_ker_le (r : Setoid α) (f : α → β) (hf : ker f ≤ r) :
    ⇑(map r f) = Relation.Map r f f ⊔ (· = ·) := by
  refine le_antisymm ?_ (sup_le Relation.EqvGen.rel (by rintro _ _ rfl; exact .refl _))
  rintro _ _ hxy
  induction hxy with
  | rel _ _ hab => exact .inl hab
  | refl _ => exact .inr rfl
  | symm _ _ _ ih => exact ih.imp (Std.Symm.symm _ _) (Std.Symm.symm _ _)
  | trans _ _ _ _ _ ih1 ih2 =>
    rcases ih1 with ih1 | rfl
    · rcases ih2 with ih2 | rfl
      · exact .inl <| r.iseqv.isTrans.map hf |>.trans _ _ _ ih1 ih2
      · exact .inl ih1
    · exact ih2

/-- Given a surjective function f whose kernel is contained in an equivalence relation r, the
equivalence relation on f's codomain defined by x ≈ y ↔ the elements of f⁻¹(x) are related to
the elements of f⁻¹(y) by r. -/
@[instance_reducible]
/-
**Setoid.mapOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：mapOfSurjective (r : Setoid α) (f : α -> β) (h : ker f <= r) (hf : Surject
ive f) : Setoid β
参数：r : Setoid α；f : α -> β；h : ker f <= r；hf : Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a surjective function f whose kernel is contained in an equivalence relati
on r, the
equivalence relation on f's codomain defined by x ≈ y ↔ the elements of f⁻¹(x) a
re related to
the elements of f⁻¹(y) by r.
-/
def mapOfSurjective (r : Setoid α) (f : α → β) (h : ker f ≤ r) (hf : Surjective f) : Setoid β :=
  ⟨Relation.Map r f f, Relation.map_equivalence r.iseqv f hf h⟩

/-- A special case of the equivalence closure of an equivalence relation r equaling r. -/
/-
**Setoid.mapOfSurjective_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：mapOfSurjective_eq_map (h : ker f <= r) (hf : Surjective f) : map r f = ma
pOfSurjective r f h hf
参数：h : ker f <= r；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Setoid.eqvGen_of_setoid`：eqvGen_of_setoid (r : Setoid α) : EqvGen.setoid
 r.r = r

--- 原说明 ---
A special case of the equivalence closure of an equivalence relation r equaling 
r.
-/
theorem mapOfSurjective_eq_map (h : ker f ≤ r) (hf : Surjective f) :
    map r f = mapOfSurjective r f h hf := by
  rw [← eqvGen_of_setoid (mapOfSurjective r f h hf)]; rfl

/-- Given a function `f : α → β`, an equivalence relation `r` on `β` induces an equivalence
relation on `α` defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `r`'.

See note [reducible non-instances]. -/
/-
**Setoid.comap** 是 Mathlib 中的一个缩写定义，位于命名空间 `Setoid`。
形式化陈述：comap (f : α -> β) (r : Setoid β) : Setoid α
参数：f : α -> β；r : Setoid β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f : α → β`, an equivalence relation `r` on `β` induces an equi
valence
relation on `α` defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `r`'.

See note [reducible non-instances].
-/
abbrev comap (f : α → β) (r : Setoid β) : Setoid α :=
  ⟨r on f, r.iseqv.comap _⟩
/-
**Setoid.comap_rel_eq** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comap_rel_eq (f : α -> β) (r : Setoid β) : ⇑(comap f r) = (⇑r on f)
参数：f : α -> β；r : Setoid β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_rel_eq (f : α → β) (r : Setoid β) : ⇑(comap f r) = (⇑r on f) :=
  rfl
/-
**Setoid.comap_rel** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comap_rel (f : α -> β) (r : Setoid β) (x y : α) : comap f r x y ↔ r (f x) 
(f y)
参数：f : α -> β；r : Setoid β；x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_rel (f : α → β) (r : Setoid β) (x y : α) : comap f r x y ↔ r (f x) (f y) :=
  Iff.rfl

/-- Given a map `f : N → M` and an equivalence relation `r` on `β`, the equivalence relation
induced on `α` by `f` equals the kernel of `r`'s quotient map composed with `f`. -/
/-
**Setoid.comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comap_eq {f : α -> β} {r : Setoid β} : comap f r = ker (@Quotient.mk'' _ r
 ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given a map `f : N → M` and an equivalence relation `r` on `β`, the equivalence 
relation
induced on `α` by `f` equals the kernel of `r`'s quotient map composed with `f`.
-/
theorem comap_eq {f : α → β} {r : Setoid β} : comap f r = ker (@Quotient.mk'' _ r ∘ f) :=
  ext fun x y => show _ ↔ ⟦_⟧ = ⟦_⟧ by rw [Quotient.eq]; rfl

@[simp]
/-
**Setoid.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comap_id (c : Setoid α) : c.comap id = c
参数：c : Setoid α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id (c : Setoid α) : c.comap id = c := rfl

@[simp]
/-
**Setoid.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comap_comp (c : Setoid γ) (g : β -> γ) (f : α -> β) : c.comap (g ∘ f) = (c
.comap g).comap f
参数：c : Setoid γ；g : β -> γ；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp (c : Setoid γ) (g : β → γ) (f : α → β) : c.comap (g ∘ f) = (c.comap g).comap f :=
  rfl
/-
**Setoid.comap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comap_injective (f : α -> β) (hf : Function.Surjective f) : Function.Injec
tive (comap f)
参数：f : α -> β；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₂`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f → ∀ {p : β → β → Prop}, (∀ (y₁ y₂ : β), p y₁ y₂) ↔ ∀ (
x₁ x₂ : α), p (f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Setoid.ext_iff`：∀ {α : Sort u_3} {s t : Setoid α}, s = t ↔ ∀ (a b : α), 
s a b ↔ t a b
-/
theorem comap_injective (f : α → β) (hf : Function.Surjective f) :
    Function.Injective (comap f) :=
  fun _ _ h => ext <| hf.forall₂.2 <| Setoid.ext_iff.1 h
/-
**Setoid.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：le_comap_map {r : Setoid α} {f : α -> β} : r <= comap f (r.map f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_comap_map {r : Setoid α} {f : α → β} : r ≤ comap f (r.map f) :=
  fun _ _ h => Relation.EqvGen.rel _ _ ⟨_, _, h, rfl, rfl⟩
/-
**Setoid.comap_map_of_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comap_map_of_ker_le (f : α -> β) (r : Setoid α) (hf : ker f <= r) : comap 
f (r.map f) = r
参数：f : α -> β；r : Setoid α；hf : ker f <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.le_iff_rel_le`：le_iff_rel_le {r₁ r₂ : Setoid α} : r₁ <= r₂ ↔ ⇑r₁ 
<= ⇑r₂
· 使用定理 `Setoid.comap_rel_eq`：comap_rel_eq (f : α -> β) (r : Setoid β) : ⇑(comap 
f r) = (⇑r on f)
· 使用定理 `Setoid.coe_map_of_ker_le`：coe_map_of_ker_le (r : Setoid α) (f : α -> β) 
(hf : ker f <= r) : ⇑(map r f) = Relation.Map r f f ⊔ (· = ·)
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `Setoid.le_comap_map`：le_comap_map {r : Setoid α} {f : α -> β} : r <= com
ap f (r.map f)
-/
theorem comap_map_of_ker_le (f : α → β) (r : Setoid α) (hf : ker f ≤ r) :
    comap f (r.map f) = r := by
  apply le_antisymm _ le_comap_map
  rw [le_iff_rel_le, comap_rel_eq, coe_map_of_ker_le _ _ hf]
  rintro x y (⟨a, b, h, ha, hb⟩ | h)
  · replace ha := hf ha
    replace hb := hf hb
    exact trans (symm ha) (trans h hb)
  · exact hf h
/-
**Setoid.comap_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comap_map_eq (f : α -> β) (r : Setoid α) (hf : f.Injective) : comap f (r.m
ap f) = r
参数：f : α -> β；r : Setoid α；hf : f.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.comap_map_of_ker_le`：comap_map_of_ker_le (f : α -> β) (r : Setoid
 α) (hf : ker f <= r) : comap f (r.map f) = r
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Setoid.ker_eq_bot_iff`：ker_eq_bot_iff {f : α -> β} : ker f = ⊥ ↔ f.Injec
tive
-/
theorem comap_map_eq (f : α → β) (r : Setoid α) (hf : f.Injective) : comap f (r.map f) = r :=
  comap_map_of_ker_le f r <| ker_eq_bot_iff.2 hf ▸ bot_le
/-
**Setoid.comap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：comap_surjective (f : α -> β) (hf : Function.Injective f) : Function.Surje
ctive (Setoid.comap f)
参数：f : α -> β；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.comap_map_eq`：comap_map_eq (f : α -> β) (r : Setoid α) (hf : f.In
jective) : comap f (r.map f) = r
-/
theorem comap_surjective (f : α → β) (hf : Function.Injective f) :
    Function.Surjective (Setoid.comap f) :=
  fun r => ⟨_, comap_map_eq f r hf⟩

/-- The second isomorphism theorem for sets. -/
/-
**Setoid.comapQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：comapQuotientEquiv (f : α -> β) (r : Setoid β) : Quotient (comap f r) ≃ Se
t.range (@Quotient.mk'' _ r ∘ f)
参数：f : α -> β；r : Setoid β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The second isomorphism theorem for sets.
-/
noncomputable def comapQuotientEquiv (f : α → β) (r : Setoid β) :
    Quotient (comap f r) ≃ Set.range (@Quotient.mk'' _ r ∘ f) :=
  (Quotient.congrRight <| Setoid.ext_iff.1 comap_eq).trans <| quotientKerEquivRange <|
    Quotient.mk'' ∘ f

variable (r f)

/-- The third isomorphism theorem for sets. -/
/-
**Setoid.quotientQuotientEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：quotientQuotientEquivQuotient (s : Setoid α) (h : r <= s) : Quotient (ker 
(Quot.mapRight h)) ≃ Quotient s where toFun x
参数：s : Setoid α；h : r <= s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The third isomorphism theorem for sets.
-/
def quotientQuotientEquivQuotient (s : Setoid α) (h : r ≤ s) :
    Quotient (ker (Quot.mapRight h)) ≃ Quotient s where
  toFun x :=
    (Quotient.liftOn' x fun w =>
        (Quotient.liftOn' w (@Quotient.mk'' _ s)) fun _ _ H => Quotient.sound <| h H)
      fun x y => Quotient.inductionOn₂' x y fun _ _ H => show @Quot.mk _ _ _ = @Quot.mk _ _ _ from H
  invFun x :=
    (Quotient.liftOn' x fun w => @Quotient.mk'' _ (ker <| Quot.mapRight h) <| @Quotient.mk'' _ r w)
      fun _ _ H => Quotient.sound' <| show @Quot.mk _ _ _ = @Quot.mk _ _ _ from Quotient.sound H
  left_inv x :=
    Quotient.inductionOn' x fun y => Quotient.inductionOn' y fun w => by change ⟦_⟧ = _; rfl
  right_inv x := Quotient.inductionOn' x fun y => by change ⟦_⟧ = _; rfl

variable {r f}

open Quotient

/-- Given an equivalence relation `r` on `α`, the order-preserving bijection between the set of
equivalence relations containing `r` and the equivalence relations on the quotient of `α` by `r`. -/
/-
**Setoid.correspondence** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：correspondence (r : Setoid α) : { s // r <= s } ≃o Setoid (Quotient r) whe
re toFun s
参数：r : Setoid α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)

--- 原说明 ---
Given an equivalence relation `r` on `α`, the order-preserving bijection between
 the set of
equivalence relations containing `r` and the equivalence relations on the quotie
nt of `α` by `r`.
-/
def correspondence (r : Setoid α) : { s // r ≤ s } ≃o Setoid (Quotient r) where
  toFun s := ⟨Quotient.lift₂ s.1.1 fun _ _ _ _ h₁ h₂ ↦ Eq.propIntro
      (fun h ↦ s.1.trans' (s.1.trans' (s.1.symm' (s.2 h₁)) h) (s.2 h₂))
      (fun h ↦ s.1.trans' (s.1.trans' (s.2 h₁) h) (s.1.symm' (s.2 h₂))),
    ⟨Quotient.ind s.1.2.1, fun {x y} ↦ Quotient.inductionOn₂ x y fun _ _ ↦ s.1.2.2,
      fun {x y z} ↦ Quotient.inductionOn₃ x y z fun _ _ _ ↦ s.1.2.3⟩⟩
  invFun s := ⟨comap Quotient.mk' s, fun x y h => by rw [comap_rel, Quotient.eq'.2 h]⟩
  right_inv _ := ext fun x y ↦ Quotient.inductionOn₂ x y fun _ _ ↦ Iff.rfl
  map_rel_iff' :=
    ⟨fun h x y hs ↦ @h ⟦x⟧ ⟦y⟧ hs, fun h x y ↦ Quotient.inductionOn₂ x y fun _ _ hs ↦ h hs⟩

/-- Given two equivalence relations with `r ≤ s`, a bijection between the sum of the quotients by
`r` on each equivalence class by `s` and the quotient by `r`. -/
/-
**Setoid.sigmaQuotientEquivOfLe** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：sigmaQuotientEquivOfLe {r s : Setoid α} (hle : r <= s) : (Σ q : Quotient s
, Quotient (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} -> α))) ≃ Quotient r
参数：hle : r <= s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given two equivalence relations with `r ≤ s`, a bijection between the sum of the
 quotients by
`r` on each equivalence class by `s` and the quotient by `r`.
-/
def sigmaQuotientEquivOfLe {r s : Setoid α} (hle : r ≤ s) :
    (Σ q : Quotient s, Quotient (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} → α))) ≃
      Quotient r :=
  .trans (.symm <| .sigmaCongrRight fun _ ↦ .subtypeQuotientEquivQuotientSubtype
      (s₁ := r) (s₂ := r.comap Subtype.val) _ _ (fun _ ↦ Iff.rfl) fun _ _ ↦ Iff.rfl)
    (.sigmaFiberEquiv fun a ↦ a.lift (Quotient.mk s) fun _ _ h ↦ Quotient.sound <| hle h)

end Setoid

@[simp]
/-
**Quotient.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quotient.subsingleton_iff {s : Setoid α} : Subsingleton (Quotient s) ↔ s =
 ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Quotient.mk'_surjective`：∀ {α : Sort u_1} [s : Setoid α], Function.Surje
ctive Quotient.mk'
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Quotient.subsingleton_iff {s : Setoid α} : Subsingleton (Quotient s) ↔ s = ⊤ := by
  simp only [_root_.subsingleton_iff, eq_top_iff, Setoid.le_def, Setoid.top_def, Pi.top_apply]
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quotient.mk'_surjective.forall.trans (forall_congr' fun b => ?_)
  simp_rw [Prop.top_eq_true, true_implies, Quotient.eq']
/-
**Quot.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quot.subsingleton_iff (r : α -> α -> Prop) : Subsingleton (Quot r) ↔ Relat
ion.EqvGen r = ⊤
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Quot.eq`：Quot.eq {α : Type*} {r : α -> α -> Prop} {x y : α} : Quot.mk r 
x = Quot.mk r y ↔ Relation.EqvGen r x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Quot.subsingleton_iff (r : α → α → Prop) :
    Subsingleton (Quot r) ↔ Relation.EqvGen r = ⊤ := by
  simp only [_root_.subsingleton_iff, _root_.eq_top_iff, Pi.le_def, Pi.top_apply]
  refine Quot.mk_surjective.forall.trans (forall_congr' fun a => ?_)
  refine Quot.mk_surjective.forall.trans (forall_congr' fun b => ?_)
  rw [Quot.eq]
  simp
