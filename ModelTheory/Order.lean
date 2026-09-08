/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Finset.Sort
public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Fraisse
public import Mathlib.Order.CountableDenseLinearOrder

/-!
# Ordered First-Ordered Structures

This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions

- `FirstOrder.Language.order` is the language consisting of a single relation representing `≤`.
- `FirstOrder.Language.IsOrdered` points out a specific symbol in a language as representing `≤`.
- `FirstOrder.Language.OrderedStructure` indicates that the `≤` symbol in an ordered language
  is interpreted as the actual relation `≤` in a particular structure.
- `FirstOrder.Language.linearOrderTheory` and similar define the theories of preorders,
  partial orders, and linear orders.
- `FirstOrder.Language.dlo` defines the theory of dense linear orders without endpoints, a
  particularly useful example in model theory.
- `FirstOrder.Language.orderStructure` is the structure on an ordered type, assigning the symbol
  representing `≤` to the actual relation `≤`.
- Conversely, `FirstOrder.Language.LEOfStructure`, `FirstOrder.Language.preorderOfModels`,
  `FirstOrder.Language.partialOrderOfModels`, and `FirstOrder.Language.linearOrderOfModels`
  are the orders induced by first-order structures modelling the relevant theory.

## Main Results

- `PartialOrder`s model the theory of partial orders, `LinearOrder`s model the theory of
  linear orders, and dense linear orders without endpoints model `Language.dlo`.
- Under `L.orderedStructure` assumptions, elements of any `L.HomClass M N` are monotone, and
  strictly monotone if injective.
- Under `Language.order.orderedStructure` assumptions, any `OrderHomClass` has an instance of
  `L.HomClass M N`, while `M ↪o N` and any `OrderIsoClass` have an instance of
  `L.StrongHomClass M N`.
- `FirstOrder.Language.isFraisseLimit_of_countable_nonempty_dlo` shows that any countable nonempty
  model of the theory of linear orders is a Fraïssé limit of the class of finite models of the
  theory of linear orders.
- `FirstOrder.Language.isFraisse_finite_linear_order` shows that the class of finite models of the
  theory of linear orders is Fraïssé.
- `FirstOrder.Language.aleph0_categorical_dlo` shows that the theory of dense linear orders is
  `ℵ₀`-categorical, and thus complete.

-/

@[expose] public section


universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder Structure

variable {L : Language.{u, v}} {α : Type w} {M : Type w'} {n : ℕ}

/-- The type of relations for the language of orders, consisting of a single binary relation `le`.
-/
/-
**FirstOrder.Language.orderRel** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Language`
。
形式化陈述：orderRel : Nat -> Type | le : orderRel 2 deriving DecidableEq  /-- The rel
ational language consisting of a single relation representing `≤`. -/ protected 
def order : Language
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of relations for the language of orders, consisting of a single binary 
relation `le`.
-/
inductive orderRel : ℕ → Type
  | le : orderRel 2
  deriving DecidableEq

/-- The relational language consisting of a single relation representing `≤`. -/
/-
**FirstOrder.Language.order** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：FirstOrder.Language
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relational language consisting of a single relation representing `≤`.
-/
protected def order : Language := ⟨fun _ => Empty, orderRel⟩
  deriving IsRelational

namespace order

@[simp]
/-
**FirstOrder.Language.order.forall_relations** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrd
er.Language.order`。
形式化陈述：forall_relations {P : forall (n) (_ : Language.order.Relations n), Prop} :
 (forall {n} (R), P n R) ↔ P 2 .le
参数：n；_ : Language.order.Relations n。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forall_relations {P : ∀ (n) (_ : Language.order.Relations n), Prop} :
    (∀ {n} (R), P n R) ↔ P 2 .le := ⟨fun h => h _, fun h n R =>
      match n, R with
      | 2, .le => h⟩
/-
**FirstOrder.Language.order.instSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrd
er.Language.order`。
形式化陈述：instSubsingleton : Subsingleton (Language.order.Relations n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance instSubsingleton : Subsingleton (Language.order.Relations n) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
/-
**FirstOrder.Language.order.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.orde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEmpty (Language.order.Relations 0) := ⟨fun x => by cases x⟩
/-
**FirstOrder.Language.order.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.orde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (Σ n, Language.order.Relations n) :=
  ⟨⟨⟨2, .le⟩⟩, fun ⟨n, R⟩ =>
      match n, R with
      | 2, .le => rfl⟩
/-
**FirstOrder.Language.order.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.orde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique Language.order.Symbols := ⟨⟨Sum.inr default⟩, by
  have : IsEmpty (Σ n, Language.order.Functions n) := isEmpty_sigma.2 inferInstance
  simp only [Symbols, Sum.forall, reduceCtorEq, Sum.inr.injEq, IsEmpty.forall_iff, true_and]
  exact Unique.eq_default⟩

@[simp]
/-
**FirstOrder.Language.order.card_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.La
nguage.order`。
形式化陈述：card_eq_one : Language.order.card = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_eq_one : Language.order.card = 1 := by simp [card]

end order

/-- A language is ordered if it has a symbol representing `≤`. -/
/-
**FirstOrder.Language.IsOrdered** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Language
`。
形式化陈述：FirstOrder.Language → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language is ordered if it has a symbol representing `≤`.
-/
class IsOrdered (L : Language.{u, v}) where
  /-- The relation symbol representing `≤`. -/
  leSymb : L.Relations 2

export IsOrdered (leSymb)
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrdered Language.order :=
  ⟨.le⟩
/-
**FirstOrder.Language.order.relation_eq_leSymb** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.order`。
形式化陈述：∀ (R : FirstOrder.Language.order.Relations 2), R = FirstOrder.Language.leS
ymb
参数：R : FirstOrder.Language.order.Relations 2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma order.relation_eq_leSymb : (R : Language.order.Relations 2) → R = leSymb
  | .le => rfl

section IsOrdered

variable [IsOrdered L]

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ ≤ t₂`. -/
/-
**FirstOrder.Language.Term.le** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.Ter
m`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type w} → {n : ℕ} → [L.IsOrdered] → L.T
erm (α ⊕ Fin n) → L.Term (α ⊕ Fin n) → L.BoundedFormula α n
参数：α ⊕ Fin n；α ⊕ Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Joins two terms `t₁, t₂` in a formula representing `t₁ ≤ t₂`.
-/
def Term.le (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  leSymb.boundedFormula₂ t₁ t₂

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ < t₂`. -/
/-
**FirstOrder.Language.Term.lt** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.Ter
m`。
形式化陈述：{L : FirstOrder.Language} →   {α : Type w} → {n : ℕ} → [L.IsOrdered] → L.T
erm (α ⊕ Fin n) → L.Term (α ⊕ Fin n) → L.BoundedFormula α n
参数：α ⊕ Fin n；α ⊕ Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Joins two terms `t₁, t₂` in a formula representing `t₁ < t₂`.
-/
def Term.lt (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  t₁.le t₂ ⊓ ∼(t₂.le t₁)

variable (L)

/-- The language homomorphism sending the unique symbol `≤` of `Language.order` to `≤` in an ordered
language. -/
/-
**FirstOrder.Language.orderLHom** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：(L : FirstOrder.Language) → [L.IsOrdered] → FirstOrder.Language.order →ᴸ L
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsRelationalOrder`：FirstOrder.Language.order.IsR
elational

--- 原说明 ---
The language homomorphism sending the unique symbol `≤` of `Language.order` to `
≤` in an ordered
language.
-/
@[simps] def orderLHom : Language.order →ᴸ L where
  onRelation | _, .le => leSymb

@[simp]
/-
**FirstOrder.Language.orderLHom_leSymb** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage`。
形式化陈述：orderLHom_leSymb : (orderLHom L).onRelation leSymb = (leSymb : L.Relations
 2)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderLHom_leSymb :
    (orderLHom L).onRelation leSymb = (leSymb : L.Relations 2) :=
  rfl

@[simp]
/-
**FirstOrder.Language.orderLHom_order** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage`。
形式化陈述：orderLHom_order : orderLHom Language.order = LHom.id Language.order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.LHom.funext`：∀ {L : FirstOrder.Language} {L' : First
Order.Language} {F G : L →ᴸ L'},   F.onFunction = G.onFunction → F.onRelation = 
G.onRelation → F = G
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `FirstOrder.Language.instIsRelationalOrder`：FirstOrder.Language.order.IsR
elational
-/
theorem orderLHom_order : orderLHom Language.order = LHom.id Language.order :=
  LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- The theory of preorders. -/
/-
**FirstOrder.Language.preorderTheory** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：preorderTheory : L.Theory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The theory of preorders.
-/
def preorderTheory : L.Theory :=
  {leSymb.reflexive, leSymb.transitive}
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Theory.IsUniversal L.preorderTheory := ⟨by
  simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_transitive⟩⟩

/-- The theory of partial orders. -/
/-
**FirstOrder.Language.partialOrderTheory** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：partialOrderTheory : L.Theory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The theory of partial orders.
-/
def partialOrderTheory : L.Theory :=
  insert leSymb.antisymmetric L.preorderTheory
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Theory.IsUniversal L.partialOrderTheory :=
  Theory.IsUniversal.insert leSymb.isUniversal_antisymmetric

/-- The theory of linear orders. -/
/-
**FirstOrder.Language.linearOrderTheory** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage`。
形式化陈述：linearOrderTheory : L.Theory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The theory of linear orders.
-/
def linearOrderTheory : L.Theory :=
  insert leSymb.total L.partialOrderTheory
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Theory.IsUniversal L.linearOrderTheory :=
  Theory.IsUniversal.insert leSymb.isUniversal_total
/-
**FirstOrder.Language.** 是 Mathlib 中的一个示例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [L.Structure M] [M ⊨ L.linearOrderTheory] (S : L.Substructure M) :
    S ⊨ L.linearOrderTheory := inferInstance

/-- A sentence indicating that an order has no top element:
$\forall x, \exists y, \neg y \le x$. -/
/-
**FirstOrder.Language.noTopOrderSentence** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：noTopOrderSentence : L.Sentence
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sentence indicating that an order has no top element:
$\forall x, \exists y, \neg y \le x$.
-/
def noTopOrderSentence : L.Sentence :=
  ∀' ∃' ∼((&1).le &0)

/-- A sentence indicating that an order has no bottom element:
$\forall x, \exists y, \neg x \le y$. -/
/-
**FirstOrder.Language.noBotOrderSentence** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：noBotOrderSentence : L.Sentence
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sentence indicating that an order has no bottom element:
$\forall x, \exists y, \neg x \le y$.
-/
def noBotOrderSentence : L.Sentence :=
  ∀' ∃' ∼((&0).le &1)

/-- A sentence indicating that an order is dense:
$\forall x, \forall y, x < y \to \exists z, x < z \wedge z < y$. -/
/-
**FirstOrder.Language.denselyOrderedSentence** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：denselyOrderedSentence : L.Sentence
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sentence indicating that an order is dense:
$\forall x, \forall y, x < y \to \exists z, x < z \wedge z < y$.
-/
def denselyOrderedSentence : L.Sentence :=
  ∀' ∀' ((&0).lt &1 ⟹ ∃' ((&0).lt &2 ⊓ (&2).lt &1))

/-- The theory of dense linear orders without endpoints. -/
/-
**FirstOrder.Language.dlo** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：dlo : L.Theory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The theory of dense linear orders without endpoints.
-/
def dlo : L.Theory :=
  L.linearOrderTheory ∪ {L.noTopOrderSentence, L.noBotOrderSentence, L.denselyOrderedSentence}

variable [L.Structure M]
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : M ⊨ L.dlo] : M ⊨ L.linearOrderTheory := h.mono Set.subset_union_left
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : M ⊨ L.linearOrderTheory] : M ⊨ L.partialOrderTheory := h.mono (Set.subset_insert _ _)
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : M ⊨ L.partialOrderTheory] : M ⊨ L.preorderTheory := h.mono (Set.subset_insert _ _)

end IsOrdered

/-
**FirstOrder.Language.sum.instIsOrdered** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.sum`。
形式化陈述：{L : FirstOrder.Language} → (L.sum FirstOrder.Language.order).IsOrdered
参数：L.sum FirstOrder.Language.order。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sum.instIsOrdered : IsOrdered (L.sum Language.order) :=
  ⟨Sum.inr IsOrdered.leSymb⟩

variable (L M)

/-- Any linearly-ordered type is naturally a structure in the language `Language.order`.
This is not an instance, because sometimes the `Language.order.Structure` is defined first. -/
@[instance_reducible]
/-
**FirstOrder.Language.orderStructure** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：(M : Type w') → [LE M] → FirstOrder.Language.order.Structure M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsRelationalOrder`：FirstOrder.Language.order.IsR
elational

--- 原说明 ---
Any linearly-ordered type is naturally a structure in the language `Language.ord
er`.
This is not an instance, because sometimes the `Language.order.Structure` is def
ined first.
-/
def orderStructure [LE M] : Language.order.Structure M where
  RelMap | .le => (fun x => x 0 ≤ x 1)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is `≤`. -/
/-
**FirstOrder.Language.OrderedStructure** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：(L : FirstOrder.Language) → (M : Type w') → [L.IsOrdered] → [LE M] → [L.St
ructure M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure is ordered if its language has a `≤` symbol whose interpretation is 
`≤`.
-/
class OrderedStructure [L.IsOrdered] [LE M] [L.Structure M] : Prop where
  relMap_leSymb : ∀ (x : Fin 2 → M), RelMap (leSymb : L.Relations 2) x ↔ (x 0 ≤ x 1)

export OrderedStructure (relMap_leSymb)

attribute [simp] relMap_leSymb

variable {L M}

section order_to_structure

variable [IsOrdered L] [L.Structure M]

section LE

variable [LE M]

/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Language.order.Structure M] [Language.order.OrderedStructure M]
    [(orderLHom L).IsExpansionOn M] : L.OrderedStructure M where
  relMap_leSymb x := by
    rw [← orderLHom_leSymb L, LHom.IsExpansionOn.map_onRelation, relMap_leSymb]

variable [L.OrderedStructure M]

set_option backward.isDefEq.respectTransparency.types false in
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Language.order.Structure M] [Language.order.OrderedStructure M] :
    LHom.IsExpansionOn (orderLHom L) M where
  map_onRelation := by simp [order.relation_eq_leSymb]
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : L.Substructure M) : L.OrderedStructure S := ⟨fun x => relMap_leSymb (S.subtype ∘ x)⟩

@[simp]
/-
**FirstOrder.Language.Term.realize_le** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Term`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type w} {M : Type w'} {n : ℕ} [inst : L.I
sOrdered] [inst_1 : L.Structure M]   [inst_2 : LE M] [L.OrderedStructure M] {t₁ 
t₂ : L.Term (α ⊕ Fin n)} {v : α → M} {xs : Fin n → M},   (t₁.le t₂).Realize v xs
 ↔     FirstOrder.Language.Term.realize (Sum.elim v xs) t₁ ≤ FirstOrder.Language
.Term.realize (Sum.elim v xs) t₂
参数：α ⊕ Fin n；t₁.le t₂；Sum.elim v xs；Sum.elim v xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Term.realize_le {t₁ t₂ : L.Term (α ⊕ (Fin n))} {v : α → M}
    {xs : Fin n → M} :
    (t₁.le t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) ≤ t₂.realize (Sum.elim v xs) := by
  simp [Term.le]
/-
**FirstOrder.Language.realize_noTopOrder_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：realize_noTopOrder_iff : M ⊨ L.noTopOrderSentence ↔ NoTopOrder M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NoTopOrder.exists_not_le`：∀ {α : Type u_3} {inst : LE α} [self : NoTopOr
der α] (a : α), ∃ b, ¬b ≤ a
-/
theorem realize_noTopOrder_iff : M ⊨ L.noTopOrderSentence ↔ NoTopOrder M := by
  simp only [noTopOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize_le]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_le a
/-
**FirstOrder.Language.realize_noBotOrder_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：realize_noBotOrder_iff : M ⊨ L.noBotOrderSentence ↔ NoBotOrder M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NoBotOrder.exists_not_ge`：∀ {α : Type u_3} {inst : LE α} [self : NoBotOr
der α] (a : α), ∃ b, ¬a ≤ b
-/
theorem realize_noBotOrder_iff : M ⊨ L.noBotOrderSentence ↔ NoBotOrder M := by
  simp only [noBotOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize_le]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_ge a

variable (L M)

@[simp]
/-
**FirstOrder.Language.realize_noTopOrder** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：realize_noTopOrder [h : NoTopOrder M] : M ⊨ L.noTopOrderSentence
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.realize_noTopOrder_iff`：realize_noTopOrder_iff : M ⊨
 L.noTopOrderSentence ↔ NoTopOrder M
-/
theorem realize_noTopOrder [h : NoTopOrder M] : M ⊨ L.noTopOrderSentence :=
  realize_noTopOrder_iff.2 h

@[simp]
/-
**FirstOrder.Language.realize_noBotOrder** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：realize_noBotOrder [h : NoBotOrder M] : M ⊨ L.noBotOrderSentence
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.realize_noBotOrder_iff`：realize_noBotOrder_iff : M ⊨
 L.noBotOrderSentence ↔ NoBotOrder M
-/
theorem realize_noBotOrder [h : NoBotOrder M] : M ⊨ L.noBotOrderSentence :=
  realize_noBotOrder_iff.2 h
/-
**FirstOrder.Language.noTopOrder_of_dlo** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage`。
形式化陈述：noTopOrder_of_dlo [M ⊨ L.dlo] : NoTopOrder M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.realize_noTopOrder_iff`：realize_noTopOrder_iff : M ⊨
 L.noTopOrderSentence ↔ NoTopOrder M
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem noTopOrder_of_dlo [M ⊨ L.dlo] : NoTopOrder M :=
  realize_noTopOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or]))
/-
**FirstOrder.Language.noBotOrder_of_dlo** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage`。
形式化陈述：noBotOrder_of_dlo [M ⊨ L.dlo] : NoBotOrder M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.realize_noBotOrder_iff`：realize_noBotOrder_iff : M ⊨
 L.noBotOrderSentence ↔ NoBotOrder M
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem noBotOrder_of_dlo [M ⊨ L.dlo] : NoBotOrder M :=
  realize_noBotOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))

end LE

@[simp]
/-
**FirstOrder.Language.orderedStructure_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language`。
形式化陈述：orderedStructure_iff [LE M] [Language.order.Structure M] [Language.order.O
rderedStructure M] : L.OrderedStructure M ↔ LHom.IsExpansionOn (orderLHom L) M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsExpansionOnOrderLHomOfOrderedStructureOrder`：∀
 {L : FirstOrder.Language} {M : Type w'} [inst : L.IsOrdered] [inst_1 : L.Struct
ure M] [inst_2 : LE M]   [L.OrderedStructure M] [inst_4 : F…
· 使用定理 `FirstOrder.Language.instOrderedStructureOfOrderOfIsExpansionOnOrderLHom`
：∀ {L : FirstOrder.Language} {M : Type w'} [inst : L.IsOrdered] [inst_1 : L.Stru
cture M] [inst_2 : LE M]   [inst_3 : FirstOrder.Language.orde…
-/
theorem orderedStructure_iff
    [LE M] [Language.order.Structure M] [Language.order.OrderedStructure M] :
    L.OrderedStructure M ↔ LHom.IsExpansionOn (orderLHom L) M :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

section Preorder

variable [Preorder M] [L.OrderedStructure M]

/-
**FirstOrder.Language.model_preorder** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：model_preorder : M ⊨ L.preorderTheory
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
instance model_preorder : M ⊨ L.preorderTheory := by
  simp only [preorderTheory, Theory.model_insert_iff, Relations.realize_reflexive, relMap_leSymb,
    Theory.model_singleton_iff, Relations.realize_transitive, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact ⟨inferInstance, inferInstance⟩

@[simp]
/-
**FirstOrder.Language.Term.realize_lt** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Term`。
形式化陈述：∀ {L : FirstOrder.Language} {α : Type w} {M : Type w'} {n : ℕ} [inst : L.I
sOrdered] [inst_1 : L.Structure M]   [inst_2 : Preorder M] [L.OrderedStructure M
] {t₁ t₂ : L.Term (α ⊕ Fin n)} {v : α → M} {xs : Fin n → M},   (t₁.lt t₂).Realiz
e v xs ↔     FirstOrder.Language.Term.realize (Sum.elim v xs) t₁ < FirstOrder.La
nguage.Term.realize (Sum.elim v xs) t₂
参数：α ⊕ Fin n；t₁.lt t₂；Sum.elim v xs；Sum.elim v xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Term.realize_lt {t₁ t₂ : L.Term (α ⊕ (Fin n))}
    {v : α → M} {xs : Fin n → M} :
    (t₁.lt t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [Term.lt, lt_iff_le_not_ge]
/-
**FirstOrder.Language.realize_denselyOrdered_iff** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language`。
形式化陈述：realize_denselyOrdered_iff : M ⊨ L.denselyOrderedSentence ↔ DenselyOrdered
 M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
-/
theorem realize_denselyOrdered_iff :
    M ⊨ L.denselyOrderedSentence ↔ DenselyOrdered M := by
  simp only [denselyOrderedSentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, Term.realize_lt,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  refine ⟨fun h => ⟨fun a b ab => h a b ab⟩, ?_⟩
  intro h a b ab
  exact exists_between ab

@[simp]
/-
**FirstOrder.Language.realize_denselyOrdered** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：realize_denselyOrdered [h : DenselyOrdered M] : M ⊨ L.denselyOrderedSenten
ce
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.realize_denselyOrdered_iff`：realize_denselyOrdered_i
ff : M ⊨ L.denselyOrderedSentence ↔ DenselyOrdered M
-/
theorem realize_denselyOrdered [h : DenselyOrdered M] :
    M ⊨ L.denselyOrderedSentence :=
  realize_denselyOrdered_iff.2 h

variable (L) (M)
/-
**FirstOrder.Language.denselyOrdered_of_dlo** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language`。
形式化陈述：denselyOrdered_of_dlo [M ⊨ L.dlo] : DenselyOrdered M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.realize_denselyOrdered_iff`：realize_denselyOrdered_i
ff : M ⊨ L.denselyOrderedSentence ↔ DenselyOrdered M
· 使用定理 `FirstOrder.Language.Theory.realize_sentence_of_mem`：∀ {L : FirstOrder.La
nguage} {M : Type w} [inst : L.Structure M] (T : L.Theory) [M ⊨ T] {φ : L.Senten
ce}, φ ∈ T → M ⊨ φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem denselyOrdered_of_dlo [M ⊨ L.dlo] : DenselyOrdered M :=
  realize_denselyOrdered_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]))

end Preorder

/-
**FirstOrder.Language.model_partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：model_partialOrder [PartialOrder M] [L.OrderedStructure M] : M ⊨ L.partial
OrderTheory
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
instance model_partialOrder [PartialOrder M] [L.OrderedStructure M] :
    M ⊨ L.partialOrderTheory := by
  simp only [partialOrderTheory, Theory.model_insert_iff, Relations.realize_antisymmetric,
    relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    model_preorder, and_true]
  infer_instance

section LinearOrder

variable [LinearOrder M] [L.OrderedStructure M]

/-
**FirstOrder.Language.model_linearOrder** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.La
nguage`。
形式化陈述：model_linearOrder : M ⊨ L.linearOrderTheory
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
instance model_linearOrder : M ⊨ L.linearOrderTheory := by
  simp only [linearOrderTheory, Theory.model_insert_iff, Relations.realize_total, relMap_leSymb,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, model_partialOrder,
    and_true]
  infer_instance
/-
**FirstOrder.Language.model_dlo** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
形式化陈述：model_dlo [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M] : M ⊨ L.dlo
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_insert`：union_insert : s union insert a t = insert a (s union 
t)
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance model_dlo [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M] :
    M ⊨ L.dlo := by
  simp [dlo, model_linearOrder, Theory.model_insert_iff]

end LinearOrder

end order_to_structure

section structure_to_order

variable (L) [IsOrdered L] (M) [L.Structure M]

/-- Any structure in an ordered language can be ordered correspondingly. -/
@[instance_reducible]
/-
**FirstOrder.Language.leOfStructure** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langua
ge`。
形式化陈述：leOfStructure : LE M where le a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any structure in an ordered language can be ordered correspondingly.
-/
def leOfStructure : LE M where
  le a b := Structure.RelMap (leSymb : L.Relations 2) ![a, b]
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @OrderedStructure L M _ (L.leOfStructure M) _ := by
  let := L.leOfStructure M
  constructor
  simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
  intros
  rfl

/-- The order structure on an ordered language is decidable. -/
-- This should not be a global instance,
-- because it will match with any `LE` typeclass search
@[instance_reducible, local instance]
/-
**FirstOrder.Language.decidableLEOfStructure** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：decidableLEOfStructure [h : DecidableRel (fun (a b : M) => Structure.RelMa
p (leSymb : L.Relations 2) ![a, b])] : letI
参数：fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a, b]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def decidableLEOfStructure
    [h : DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a, b])] :
    letI := L.leOfStructure M
    DecidableLE M := h

/-- Any model of a theory of preorders is a preorder. -/
@[instance_reducible]
/-
**FirstOrder.Language.preorderOfModels** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lan
guage`。
形式化陈述：preorderOfModels [h : M ⊨ L.preorderTheory] : Preorder M where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any model of a theory of preorders is a preorder.
-/
def preorderOfModels [h : M ⊨ L.preorderTheory] : Preorder M where
  __ := L.leOfStructure M
  le_refl := (Relations.realize_reflexive.mp <|
    Theory.model_iff _ |>.mp h _ <| by simp [preorderTheory]).refl
  le_trans := (Relations.realize_transitive.mp <|
    Theory.model_iff _ |>.mp h _ <| by simp [preorderTheory]).trans

/-- Any model of a theory of partial orders is a partial order. -/
@[instance_reducible]
/-
**FirstOrder.Language.partialOrderOfModels** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language`。
形式化陈述：partialOrderOfModels [h : M ⊨ L.partialOrderTheory] : PartialOrder M where
 __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instModelPreorderTheoryOfPartialOrderTheory`：∀ (L : 
FirstOrder.Language) {M : Type w'} [inst : L.IsOrdered] [inst_1 : L.Structure M]
 [h : M ⊨ L.partialOrderTheory],   M ⊨ L.preorderTheo…

--- 原说明 ---
Any model of a theory of partial orders is a partial order.
-/
def partialOrderOfModels [h : M ⊨ L.partialOrderTheory] : PartialOrder M where
  __ := L.preorderOfModels M
  le_antisymm := (Relations.realize_antisymmetric.mp <|
    Theory.model_iff _ |>.mp h _ <| by simp [partialOrderTheory]).antisymm

/-- Any model of a theory of linear orders is a linear order. -/
@[instance_reducible]
/-
**FirstOrder.Language.linearOrderOfModels** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.
Language`。
形式化陈述：linearOrderOfModels [h : M ⊨ L.linearOrderTheory] [DecidableRel (fun (a b 
: M) => Structure.RelMap (leSymb : L.Relations 2) ![a, b])] : LinearOrder M wher
e __
参数：fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a, b]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instModelPartialOrderTheoryOfLinearOrderTheory`：∀ (L
 : FirstOrder.Language) {M : Type w'} [inst : L.IsOrdered] [inst_1 : L.Structure
 M] [h : M ⊨ L.linearOrderTheory],   M ⊨ L.partialOrderT…

--- 原说明 ---
Any model of a theory of linear orders is a linear order.
-/
def linearOrderOfModels [h : M ⊨ L.linearOrderTheory]
    [DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a, b])] :
    LinearOrder M where
  __ := L.partialOrderOfModels M
  le_total := (Relations.realize_total.mp <|
    Theory.model_iff _ |>.mp h _ <| by simp [linearOrderTheory]).total
  toDecidableLE := inferInstance

end structure_to_order

namespace order

variable [Language.order.Structure M] [LE M] [Language.order.OrderedStructure M]
  {N : Type*} [Language.order.Structure N] [LE N] [Language.order.OrderedStructure N]
  {F : Type*}

set_option backward.isDefEq.respectTransparency.types false in
/-
**FirstOrder.Language.order.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.orde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FunLike F M N] [OrderHomClass F M N] : Language.order.HomClass F M N :=
  ⟨fun _ => isEmptyElim, by
    simp only [forall_relations, relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply]
    exact fun φ x => map_rel φ⟩

-- If `OrderEmbeddingClass` or `RelEmbeddingClass` is defined, this should be generalized.
set_option backward.isDefEq.respectTransparency.types false in
/-
**FirstOrder.Language.order.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.orde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Language.order.StrongHomClass (M ↪o N) M N :=
  ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
    Function.comp_apply, RelEmbedding.map_rel_iff, implies_true]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**FirstOrder.Language.order.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.orde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EquivLike F M N] [OrderIsoClass F M N] : Language.order.StrongHomClass F M N :=
  ⟨fun _ => isEmptyElim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
      Function.comp_apply, map_le_map_iff, implies_true]⟩

end order

namespace HomClass

variable [L.IsOrdered] [L.Structure M] {N : Type*} [L.Structure N]
  {F : Type*} [FunLike F M N] [L.HomClass F M N]

/-
**FirstOrder.Language.HomClass.monotone** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.La
nguage.HomClass`。
形式化陈述：monotone [Preorder M] [L.OrderedStructure M] [Preorder N] [L.OrderedStruct
ure N] (f : F) : Monotone f
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_rel`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma monotone [Preorder M] [L.OrderedStructure M] [Preorder N] [L.OrderedStructure N] (f : F) :
    Monotone f := fun a b => by
  have h := HomClass.map_rel f leSymb ![a, b]
  simp only [relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.comp_apply] at h
  exact h
/-
**FirstOrder.Language.HomClass.strictMono** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.
Language.HomClass`。
形式化陈述：strictMono [EmbeddingLike F M N] [PartialOrder M] [L.OrderedStructure M] [
PartialOrder N] [L.OrderedStructure N] (f : F) : StrictMono f
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用引理 `FirstOrder.Language.HomClass.monotone`：monotone [Preorder M] [L.OrderedS
tructure M] [Preorder N] [L.OrderedStructure N] (f : F) : Monotone f
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
-/
lemma strictMono [EmbeddingLike F M N] [PartialOrder M] [L.OrderedStructure M]
    [PartialOrder N] [L.OrderedStructure N] (f : F) :
    StrictMono f :=
  (HomClass.monotone f).strictMono_of_injective (EmbeddingLike.injective f)

end HomClass

/-- This is not an instance because it would form a loop with
`FirstOrder.Language.order.instStrongHomClassOfOrderIsoClass`.
As both types are `Prop`s, it would only cause a slowdown. -/
/-
**FirstOrder.Language.StrongHomClass.toOrderIsoClass** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.StrongHomClass`。
形式化陈述：∀ (L : FirstOrder.Language) [inst : L.IsOrdered] (M : Type u_1) [inst_1 : 
L.Structure M] [inst_2 : LE M]   [L.OrderedStructure M] (N : Type u_2) [inst_4 :
 L.Structure N] [inst_5 : LE N] [L.OrderedStructure N] (F : Type u_3)   [inst : 
EquivLike F M N] [L.StrongHomClass F M N], OrderIsoClass F M N
参数：L : FirstOrder.Language；M : Type u_1；N : Type u_2；F : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.StrongHomClass.map_rel`：∀ {L : outParam FirstOrder.L
anguage} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {i
nst : FunLike F M N} {inst_1 : L…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
This is not an instance because it would form a loop with
`FirstOrder.Language.order.instStrongHomClassOfOrderIsoClass`.
As both types are `Prop`s, it would only cause a slowdown.
-/
lemma StrongHomClass.toOrderIsoClass
    (L : Language) [L.IsOrdered] (M : Type*) [L.Structure M] [LE M] [L.OrderedStructure M]
    (N : Type*) [L.Structure N] [LE N] [L.OrderedStructure N]
    (F : Type*) [EquivLike F M N] [L.StrongHomClass F M N] :
    OrderIsoClass F M N where
  map_le_map_iff f a b := by
    have h := StrongHomClass.map_rel f leSymb ![a, b]
    simp only [relMap_leSymb, Fin.isValue, Function.comp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    exact h

section Fraisse

variable (M)

/-
**FirstOrder.Language.dlo_isExtensionPair** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.
Language`。
形式化陈述：dlo_isExtensionPair (M : Type w) [Language.order.Structure M] [M ⊨ Languag
e.order.linearOrderTheory] (N : Type w') [Language.order.Structure N] [N ⊨ Langu
age.order.dlo] [Nonempty N] : Language.order.IsExtensionPair M N
参数：M : Type w；N : Type w'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.isExtensionPair_iff_exists_embedding_closure_singlet
on_sup`：isExtensionPair_iff_exists_embedding_closure_singleton_sup : L.IsExtensi
onPair M N ↔ forall (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] N)…
· 使用定理 `FirstOrder.Language.instModelLinearOrderTheoryOfDlo`：∀ (L : FirstOrder.L
anguage) {M : Type w'} [inst : L.IsOrdered] [inst_1 : L.Structure M] [h : M ⊨ L.
dlo],   M ⊨ L.linearOrderTheory
· 使用定理 `FirstOrder.Language.denselyOrdered_of_dlo`：denselyOrdered_of_dlo [M ⊨ L.
dlo] : DenselyOrdered M
· 使用定理 `FirstOrder.Language.instOrderedStructure`：∀ (L : FirstOrder.Language) (M
 : Type w') [inst : L.IsOrdered] [inst_1 : L.Structure M], L.OrderedStructure M
· 使用定理 `FirstOrder.Language.noBotOrder_of_dlo`：noBotOrder_of_dlo [M ⊨ L.dlo] : N
oBotOrder M
· 使用定理 `FirstOrder.Language.noTopOrder_of_dlo`：noTopOrder_of_dlo [M ⊨ L.dlo] : N
oTopOrder M
· 使用定理 `NoBotOrder.to_noMinOrder`：NoBotOrder.to_noMinOrder (α : Type*) [LinearOr
der α] [NoBotOrder α] : NoMinOrder α
· 使用定理 `NoTopOrder.to_noMaxOrder`：∀ (α : Type u_3) [inst : LinearOrder α] [NoTop
Order α], NoMaxOrder α
· 使用定理 `FirstOrder.Language.Structure.FG.finite`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] [L.IsRelational],   FirstOrder.Language.Struc
ture.FG L M → Finite M
· 使用定理 `FirstOrder.Language.instIsRelationalOrder`：FirstOrder.Language.order.IsR
elational
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_iff_structure_fg`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (S : L.Substructure M),   S.FG ↔
 FirstOrder.Language.Structure.FG L ↥S
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用引理 `FirstOrder.Language.HomClass.strictMono`：strictMono [EmbeddingLike F M N
] [PartialOrder M] [L.OrderedStructure M] [PartialOrder N] [L.OrderedStructure N
] (f : F) : StrictMono f
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
· 使用定理 `FirstOrder.Language.instOrderedStructureSubtypeMemSubstructure`：∀ {L : F
irstOrder.Language} {M : Type w'} [inst : L.IsOrdered] [inst_1 : L.Structure M] 
[inst_2 : LE M]   [L.OrderedStructure M] (S : L.Subs…
· 使用引理 `Order.exists_orderEmbedding_insert`：exists_orderEmbedding_insert [Densel
yOrdered β] [NoMinOrder β] [NoMaxOrder β] [nonem : Nonempty β] (S : Finset α) (f
 : S ↪o β) (a : α) : exi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `FirstOrder.Language.Substructure.closure_insert`：closure_insert (s : Set
 M) (m : M) : closure L (insert m s) = closure L {m} ⊔ closure L s
· 使用定理 `FirstOrder.Language.Substructure.closure_eq`：closure_eq : closure L (S :
 Set M) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LowerAdjoint.closure_eq_self_of_mem_closed`：closure_eq_self_of_mem_close
d {x : α} (h : x in l.closed) : u (l x) = x
· 使用引理 `FirstOrder.Language.Substructure.mem_closed_of_isRelational`：mem_closed_
of_isRelational [L.IsRelational] (s : Set M) : s in (closure L).closed
（共 35 条，此处仅展示前 30 条）
-/
lemma dlo_isExtensionPair
    (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.linearOrderTheory]
    (N : Type w') [Language.order.Structure N] [N ⊨ Language.order.dlo] [Nonempty N] :
    Language.order.IsExtensionPair M N := by
  classical
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro S S_fg f m
  let := Language.order.linearOrderOfModels M
  let := Language.order.linearOrderOfModels N
  have := Language.order.denselyOrdered_of_dlo N
  have := Language.order.noBotOrder_of_dlo N
  have := Language.order.noTopOrder_of_dlo N
  have := NoBotOrder.to_noMinOrder N
  have := NoTopOrder.to_noMaxOrder N
  have hS : Set.Finite (S : Set M) := (S.fg_iff_structure_fg.1 S_fg).finite
  obtain ⟨g, hg⟩ := Order.exists_orderEmbedding_insert hS.toFinset
    ((OrderIso.setCongr hS.toFinset (S : Set M) hS.coe_toFinset).toOrderEmbedding.trans
      (OrderEmbedding.ofStrictMono f (HomClass.strictMono f))) m
  let g' :
    ((Substructure.closure Language.order).toFun {m} ⊔ S : Language.order.Substructure M) ↪o N :=
    ((OrderIso.setCongr _ _ (by
      convert!
        LowerAdjoint.closure_eq_self_of_mem_closed _
          (Substructure.mem_closed_of_isRelational Language.order
            ((insert m hS.toFinset : Finset M) : Set M))
      simp only [Finset.coe_insert, Set.Finite.coe_toFinset, Substructure.closure_insert,
        Substructure.closure_eq])).toOrderEmbedding.trans g)
  use StrongHomClass.toEmbedding g'
  ext ⟨x, xS⟩
  refine congr_fun hg.symm ⟨x, (?_ : x ∈ hS.toFinset)⟩
  simp only [Set.Finite.mem_toFinset, SetLike.mem_coe, xS]

set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Type w) [Language.order.Structure M] [M ⊨ Language.order.dlo] [Nonempty M] :
    Infinite M := by
  let := orderStructure ℚ
  obtain ⟨f, _⟩ := embedding_from_cg cg_of_countable default (dlo_isExtensionPair ℚ M)
  exact Infinite.of_injective f f.injective
/-
**FirstOrder.Language.dlo_age** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrder.Language`。
形式化陈述：dlo_age [Language.order.Structure M] [Mdlo : M ⊨ Language.order.dlo] [None
mpty M] : Language.order.age M = {M : CategoryTheory.Bundled.{w'} Language.order
.Structure | Finite M ∧ M ⊨ Language.order.linearOrderTheory}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.age.eq_1`：∀ (L : FirstOrder.Language) (M : Type w) [
inst : L.Structure M],   L.age M = {N | FirstOrder.Language.Structure.FG L ↑N ∧ 
Nonempty (L.Embedd…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `FirstOrder.Language.Structure.FG.finite`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] [L.IsRelational],   FirstOrder.Language.Struc
ture.FG L M → Finite M
· 使用定理 `FirstOrder.Language.instIsRelationalOrder`：FirstOrder.Language.order.IsR
elational
· 使用定理 `FirstOrder.Language.Theory.IsUniversal.models_of_embedding`：∀ {L : First
Order.Language} {M : Type w} [inst : L.Structure M] {T : L.Theory} [hT : T.IsUni
versal] {N : Type u_1}   [inst_1 : L.Structure N…
· 使用定理 `FirstOrder.Language.instIsUniversalLinearOrderTheory`：∀ (L : FirstOrder.
Language) [inst : L.IsOrdered], L.linearOrderTheory.IsUniversal
· 使用定理 `FirstOrder.Language.instModelLinearOrderTheoryOfDlo`：∀ (L : FirstOrder.L
anguage) {M : Type w'} [inst : L.IsOrdered] [inst_1 : L.Structure M] [h : M ⊨ L.
dlo],   M ⊨ L.linearOrderTheory
· 使用定理 `FirstOrder.Language.Structure.FG.of_finite`：∀ {L : FirstOrder.Language} 
{M : Type u_1} [inst : L.Structure M] [Finite M], FirstOrder.Language.Structure.
FG L M
· 使用定理 `RelEmbedding.instEmbeddingLike`：∀ {α : Type u_1} {β : Type u_2} {r : α →
 α → Prop} {s : β → β → Prop}, EmbeddingLike (r ↪r s) α β
· 使用定理 `FirstOrder.Language.order.instStrongHomClassOrderEmbedding`：∀ {M : Type 
w'} [inst : FirstOrder.Language.order.Structure M] [inst_1 : LE M]   [FirstOrder
.Language.order.OrderedStructure M] {N : Type u_…
· 使用定理 `FirstOrder.Language.instOrderedStructure`：∀ (L : FirstOrder.Language) (M
 : Type w') [inst : L.IsOrdered] [inst_1 : L.Structure M], L.OrderedStructure M
· 使用引理 `nonempty_orderEmbedding_of_finite_infinite`：nonempty_orderEmbedding_of_f
inite_infinite (α : Type*) [LinearOrder α] [hα : Finite α] (β : Type*) [LinearOr
der β] [hβ : Infinite β] : Nonem…
· 使用定理 `FirstOrder.Language.instInfiniteOfModelDloOrderOfNonempty`：∀ (M : Type w
) [inst : FirstOrder.Language.order.Structure M] [M ⊨ FirstOrder.Language.order.
dlo] [Nonempty M],   Infinite M
-/
lemma dlo_age [Language.order.Structure M] [Mdlo : M ⊨ Language.order.dlo] [Nonempty M] :
    Language.order.age M = {M : CategoryTheory.Bundled.{w'} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} := by
  classical
  rw [age]
  ext N
  refine ⟨fun ⟨hF, h⟩ => ⟨hF.finite, Theory.IsUniversal.models_of_embedding h.some⟩,
    fun ⟨hF, h⟩ => ⟨FG.of_finite, ?_⟩⟩
  let := Language.order.linearOrderOfModels M
  let := Language.order.linearOrderOfModels N
  exact ⟨StrongHomClass.toEmbedding (nonempty_orderEmbedding_of_finite_infinite N M).some⟩

/-- Any countable nonempty model of the theory of dense linear orders is a Fraïssé limit of the
/-
**FirstOrder.Language.of** 是 Mathlib 中的一个类，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class of finite models of the theory of linear orders. -/
/-
**FirstOrder.Language.isFraisseLimit_of_countable_nonempty_dlo** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language`。
形式化陈述：isFraisseLimit_of_countable_nonempty_dlo (M : Type w) [Language.order.Stru
cture M] [Countable M] [Nonempty M] [M ⊨ Language.order.dlo] : IsFraisseLimit {M
 : CategoryTheory.Bundled.{w} Language.order.Structure | Finite M ∧ M ⊨ Language
.order.linearOrderTheory} M
参数：M : Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Countable.countable_functions`：∀ {L : FirstOrder.Lan
guage} [h : Countable L.Symbols], Countable ((l : ℕ) × L.Functions l)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.isUltrahomogeneous_iff_IsExtensionPair`：isUltrahomog
eneous_iff_IsExtensionPair (M_CG : CG L M) : L.IsUltrahomogeneous M ↔ L.IsExtens
ionPair M M
· 使用定理 `FirstOrder.Language.Structure.cg_of_countable`：cg_of_countable [Countabl
e M] : CG L M
· 使用引理 `FirstOrder.Language.dlo_isExtensionPair`：dlo_isExtensionPair (M : Type w
) [Language.order.Structure M] [M ⊨ Language.order.linearOrderTheory] (N : Type 
w') [Language.order.Structure…
· 使用定理 `FirstOrder.Language.instModelLinearOrderTheoryOfDlo`：∀ (L : FirstOrder.L
anguage) {M : Type w'} [inst : L.IsOrdered] [inst_1 : L.Structure M] [h : M ⊨ L.
dlo],   M ⊨ L.linearOrderTheory
· 使用引理 `FirstOrder.Language.dlo_age`：dlo_age [Language.order.Structure M] [Mdlo 
: M ⊨ Language.order.dlo] [Nonempty M] : Language.order.age M = {M : CategoryThe
ory.Bundled.{w'} …

--- 原说明 ---
Any countable nonempty model of the theory of dense linear orders is a Fraïssé l
imit of the
class of finite models of the theory of linear orders.
-/
theorem isFraisseLimit_of_countable_nonempty_dlo (M : Type w)
    [Language.order.Structure M] [Countable M] [Nonempty M] [M ⊨ Language.order.dlo] :
    IsFraisseLimit {M : CategoryTheory.Bundled.{w} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} M :=
  ⟨(isUltrahomogeneous_iff_IsExtensionPair cg_of_countable).2 (dlo_isExtensionPair M M), dlo_age M⟩

set_option backward.isDefEq.respectTransparency false in
/-- The class of finite models of the theory of linear orders is Fraïssé. -/
/-
**FirstOrder.Language.isFraisse_finite_linear_order** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language`。
形式化陈述：isFraisse_finite_linear_order : IsFraisse {M : CategoryTheory.Bundled.{0} 
Language.order.Structure | Finite M ∧ M ⊨ Language.order.linearOrderTheory}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.IsFraisseLimit.isFraisse`：isFraisse [Countable (Σ l,
 L.Functions l)] [Countable M] (h : IsFraisseLimit K M) : IsFraisse K
· 使用定理 `FirstOrder.Language.Countable.countable_functions`：∀ {L : FirstOrder.Lan
guage} [h : Countable L.Symbols], Countable ((l : ℕ) × L.Functions l)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `FirstOrder.Language.isFraisseLimit_of_countable_nonempty_dlo`：isFraisseL
imit_of_countable_nonempty_dlo (M : Type w) [Language.order.Structure M] [Counta
ble M] [Nonempty M] [M ⊨ Language.order.dlo] : IsF…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `FirstOrder.Language.instOrderedStructure`：∀ (L : FirstOrder.Language) (M
 : Type w') [inst : L.IsOrdered] [inst_1 : L.Structure M], L.OrderedStructure M
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R

--- 原说明 ---
The class of finite models of the theory of linear orders is Fraïssé.
-/
theorem isFraisse_finite_linear_order :
    IsFraisse {M : CategoryTheory.Bundled.{0} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} := by
  let : Language.order.Structure ℚ := orderStructure _
  exact (isFraisseLimit_of_countable_nonempty_dlo ℚ).isFraisse

open Cardinal

/-- The theory of dense linear orders is `ℵ₀`-categorical. -/
/-
**FirstOrder.Language.aleph0_categorical_dlo** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：aleph0_categorical_dlo : (ℵ₀).Categorical Language.order.dlo
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.denumerable_iff`：denumerable_iff {α : Type u} : Nonempty (Denum
erable α) ↔ #α = ℵ₀
· 使用定理 `FirstOrder.Language.IsFraisseLimit.nonempty_equiv`：nonempty_equiv : None
mpty (M ≃[L] N)
· 使用定理 `FirstOrder.Language.Countable.countable_functions`：∀ {L : FirstOrder.Lan
guage} [h : Countable L.Symbols], Countable ((l : ℕ) × L.Functions l)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `FirstOrder.Language.isFraisseLimit_of_countable_nonempty_dlo`：isFraisseL
imit_of_countable_nonempty_dlo (M : Type w) [Language.order.Structure M] [Counta
ble M] [Nonempty M] [M ⊨ Language.order.dlo] : IsF…
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T

--- 原说明 ---
The theory of dense linear orders is `ℵ₀`-categorical.
-/
theorem aleph0_categorical_dlo : (ℵ₀).Categorical Language.order.dlo := fun M₁ M₂ h₁ h₂ => by
  obtain ⟨_⟩ := denumerable_iff.2 h₁
  obtain ⟨_⟩ := denumerable_iff.2 h₂
  exact (isFraisseLimit_of_countable_nonempty_dlo M₁).nonempty_equiv
    (isFraisseLimit_of_countable_nonempty_dlo M₂)

set_option backward.isDefEq.respectTransparency false in
/-- The theory of dense linear orders is `ℵ₀`-complete. -/
/-
**FirstOrder.Language.dlo_isComplete** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：dlo_isComplete : Language.order.dlo.IsComplete
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.Categorical.isComplete`：∀ {L : FirstOrder.Language} (κ : Cardin
al.{w}) (T : L.Theory),   κ.Categorical T →     Cardinal.aleph0 ≤ κ →       Card
inal.lift.{w, max u v…
· 使用定理 `FirstOrder.Language.aleph0_categorical_dlo`：aleph0_categorical_dlo : (ℵ₀
).Categorical Language.order.dlo
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FirstOrder.Language.order.card_eq_one`：card_eq_one : Language.order.card
 = 1
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `FirstOrder.Language.instOrderedStructure`：∀ (L : FirstOrder.Language) (M
 : Type w') [inst : L.IsOrdered] [inst_1 : L.Structure M], L.OrderedStructure M
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `FirstOrder.Language.instInfiniteOfModelDloOrderOfNonempty`：∀ (M : Type w
) [inst : FirstOrder.Language.order.Structure M] [M ⊨ FirstOrder.Language.order.
dlo] [Nonempty M],   Infinite M
· 使用定理 `FirstOrder.Language.Theory.ModelType.is_model`：∀ {L : FirstOrder.Languag
e} {T : L.Theory} (self : T.ModelType), ↑self ⊨ T
· 使用定理 `FirstOrder.Language.Theory.ModelType.nonempty'`：∀ {L : FirstOrder.Langua
ge} {T : L.Theory} (self : T.ModelType), Nonempty ↑self

--- 原说明 ---
The theory of dense linear orders is `ℵ₀`-complete.
-/
theorem dlo_isComplete : Language.order.dlo.IsComplete :=
  aleph0_categorical_dlo.{0}.isComplete ℵ₀ _ le_rfl (by simp [one_le_aleph0])
    ⟨by
      letI : Language.order.Structure ℚ := orderStructure ℚ
      exact Theory.ModelType.of _ ℚ⟩
    fun _ => inferInstance

end Fraisse

end Language

end FirstOrder

namespace Order

open FirstOrder FirstOrder.Language

set_option backward.isDefEq.respectTransparency false in
/-- A model-theoretic adaptation of the proof of `Order.iso_of_countable_dense`: two countable,
  dense, nonempty linear orders without endpoints are order isomorphic. -/
/-
**Order.** 是 Mathlib 中的一个示例，位于命名空间 `Order`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A model-theoretic adaptation of the proof of `Order.iso_of_countable_dense`: two
 countable,
  dense, nonempty linear orders without endpoints are order isomorphic.
-/
example (α β : Type w') [LinearOrder α] [LinearOrder β]
    [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    [Nonempty α] [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) := by
  let := orderStructure α
  let := orderStructure β
  let := StrongHomClass.toOrderIsoClass Language.order α β (α ≃[Language.order] β)
  exact ⟨(IsFraisseLimit.nonempty_equiv (isFraisseLimit_of_countable_nonempty_dlo α)
    (isFraisseLimit_of_countable_nonempty_dlo β)).some⟩

end Order

