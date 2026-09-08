/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.ULift

/-!
# (Semi-)lattices

Semilattices are partially ordered sets with join (least upper bound, or `sup`) or meet (greatest
lower bound, or `inf`) operations. Lattices are posets that are both join-semilattices and
meet-semilattices.

Distributive lattices are lattices which satisfy any of four equivalent distributivity properties,
of `sup` over `inf`, on the left or on the right.

## Main declarations

* `SemilatticeSup`: a type class for join semilattices
* `SemilatticeSup.mk'`: an alternative constructor for `SemilatticeSup` via proofs that `⊔` is
  commutative, associative and idempotent.
* `SemilatticeInf`: a type class for meet semilattices
* `SemilatticeSup.mk'`: an alternative constructor for `SemilatticeInf` via proofs that `⊓` is
  commutative, associative and idempotent.

* `Lattice`: a type class for lattices
* `Lattice.mk'`: an alternative constructor for `Lattice` via proofs that `⊔` and `⊓` are
  commutative, associative and satisfy a pair of "absorption laws".

* `DistribLattice`: a type class for distributive lattices.

## Notation

* `a ⊔ b`: the supremum or join of `a` and `b`
* `a ⊓ b`: the infimum or meet of `a` and `b`

## TODO

* (Semi-)lattice homomorphisms
* Alternative constructors for distributive lattices from the other distributive properties

## Tags

semilattice, lattice

-/

@[expose] public section

universe u v w

variable {α : Type u} {β : Type v}

/-!
### Join-semilattices
-/

/-- A `SemilatticeSup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
/-
**SemilatticeSup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SemilatticeSup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors.
-/
class SemilatticeSup (α : Type u) extends PartialOrder α where
  /-- The binary supremum, used to derive `Max α` -/
  sup : α → α → α
  /-- The supremum is an upper bound on the first argument -/
  protected le_sup_left : ∀ a b : α, a ≤ sup a b
  /-- The supremum is an upper bound on the second argument -/
  protected le_sup_right : ∀ a b : α, b ≤ sup a b
  /-- The supremum is the *least* upper bound -/
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → sup a b ≤ c

/-- A `SemilatticeInf` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors. -/
@[to_dual]
/-
**SemilatticeInf** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SemilatticeInf` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors.
-/
class SemilatticeInf (α : Type u) extends PartialOrder α where
  /-- The binary infimum, used to derive `Min α` -/
  inf : α → α → α
  /-- The infimum is a lower bound on the first argument -/
  protected inf_le_left : ∀ a b : α, inf a b ≤ a
  /-- The infimum is a lower bound on the second argument -/
  protected inf_le_right : ∀ a b : α, inf a b ≤ b
  /-- The infimum is the *greatest* lower bound -/
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ inf b c

attribute [to_dual existing] SemilatticeSup.casesOn

@[to_dual]
/-
**SemilatticeSup.toMax** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SemilatticeSup.toMax [SemilatticeSup α] : Max α where max a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SemilatticeSup.toMax [SemilatticeSup α] : Max α where max a b := SemilatticeSup.sup a b

-- Note: it is not possible for `to_dual` to translate `le a b := a ⊔ b = b` consistently.
/--
A type with a commutative, associative and idempotent binary `sup` operation has the structure of a
join-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
@[instance_reducible]
/-
**SemilatticeSup.mk'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SemilatticeSup.mk' {α : Type*} [Max α] (sup_comm : forall a b : α, a ⊔ b =
 b ⊔ a) (sup_assoc : forall a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (sup_idem : fora
ll a : α, a ⊔ a = a) : SemilatticeSup α where sup
参数：sup_comm : forall a b : α, a ⊔ b = b ⊔ a；sup_assoc : forall a b c : α, a ⊔ b 
⊔ c = a ⊔ (b ⊔ c)；sup_idem : forall a : α, a ⊔ a = a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type with a commutative, associative and idempotent binary `sup` operation has
 the structure of a
join-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq
_right`.
-/
def SemilatticeSup.mk' {α : Type*} [Max α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (sup_idem : ∀ a : α, a ⊔ a = a) :
    SemilatticeSup α where
  sup := (· ⊔ ·)
  le a b := a ⊔ b = b
  le_refl := sup_idem
  le_trans a b c hab hbc := by rw [← hbc, ← sup_assoc, hab]
  le_antisymm a b hab hba := by rwa [← hba, sup_comm]
  le_sup_left a b := by rw [← sup_assoc, sup_idem]
  le_sup_right a b := by rw [sup_comm, sup_assoc, sup_idem]
  sup_le a b c hac hbc := by rwa [sup_assoc, hbc]

/--
A type with a commutative, associative and idempotent binary `inf` operation has the structure of a
meet-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `b ⊓ a = a`; cf. `inf_eq_right`.
-/
@[instance_reducible]
/-
**SemilatticeInf.mk'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SemilatticeInf.mk' {α : Type*} [Min α] (inf_comm : forall a b : α, a ⊓ b =
 b ⊓ a) (inf_assoc : forall a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : fora
ll a : α, a ⊓ a = a) : SemilatticeInf α where inf
参数：inf_comm : forall a b : α, a ⊓ b = b ⊓ a；inf_assoc : forall a b c : α, a ⊓ b 
⊓ c = a ⊓ (b ⊓ c)；inf_idem : forall a : α, a ⊓ a = a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type with a commutative, associative and idempotent binary `inf` operation has
 the structure of a
meet-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `b ⊓ a = a`; cf. `inf_eq
_right`.
-/
def SemilatticeInf.mk' {α : Type*} [Min α] (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a) :
    SemilatticeInf α where
  inf := (· ⊓ ·)
  le b a := a ⊓ b = b
  le_refl := inf_idem
  le_trans c b a hbc hab := by rw [← hbc, ← inf_assoc, hab]
  le_antisymm a b hba hab := by rwa [← hba, inf_comm]
  inf_le_left a b := by rw [← inf_assoc, inf_idem]
  inf_le_right a b := by rw [inf_comm, inf_assoc, inf_idem]
  le_inf a b c hac hbc := by rwa [inf_assoc, hbc]

section SemilatticeSup

variable [SemilatticeSup α] {a b c d : α}

@[to_dual (attr := simp) inf_le_left]
/-
**le_sup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sup_left : a <= a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.le_sup_left`：∀ {α : Type u} [self : SemilatticeSup α] (a 
b : α), a ≤ SemilatticeSup.sup a b
-/
theorem le_sup_left : a ≤ a ⊔ b :=
  SemilatticeSup.le_sup_left a b

@[to_dual (attr := simp) inf_le_right]
/-
**le_sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sup_right : b <= a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.le_sup_right`：∀ {α : Type u} [self : SemilatticeSup α] (a
 b : α), b ≤ SemilatticeSup.sup a b
-/
theorem le_sup_right : b ≤ a ⊔ b :=
  SemilatticeSup.le_sup_right a b

@[to_dual (reorder := a b c) le_inf]
/-
**sup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_le : a <= c -> b <= c -> a ⊔ b <= c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.sup_le`：∀ {α : Type u} [self : SemilatticeSup α] (a b c :
 α), a ≤ c → b ≤ c → SemilatticeSup.sup a b ≤ c
-/
theorem sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
  SemilatticeSup.sup_le a b c

@[to_dual inf_le_of_left_le]
/-
**le_sup_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
参数：h : c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem le_sup_of_le_left (h : c ≤ a) : c ≤ a ⊔ b :=
  le_trans h le_sup_left

@[to_dual inf_le_of_right_le]
/-
**le_sup_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
参数：h : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem le_sup_of_le_right (h : c ≤ b) : c ≤ a ⊔ b :=
  le_trans h le_sup_right

@[to_dual inf_lt_of_left_lt]
/-
**lt_sup_of_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_sup_of_lt_left (h : c < a) : c < a ⊔ b
参数：h : c < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem lt_sup_of_lt_left (h : c < a) : c < a ⊔ b :=
  h.trans_le le_sup_left

@[to_dual inf_lt_of_right_lt]
/-
**lt_sup_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_sup_of_lt_right (h : c < b) : c < a ⊔ b
参数：h : c < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem lt_sup_of_lt_right (h : c < b) : c < a ⊔ b :=
  h.trans_le le_sup_right

@[to_dual (attr := simp) (reorder := a b c) le_inf_iff]
/-
**sup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem sup_le_iff : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h : a ⊔ b ≤ c => ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
   fun ⟨h₁, h₂⟩ => sup_le h₁ h₂⟩

@[to_dual (attr := simp)]
/-
**sup_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_left : a ⊔ b = a ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_eq_left : a ⊔ b = a ↔ b ≤ a :=
  le_antisymm_iff.trans <| by simp

@[to_dual (attr := simp)]
/-
**sup_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_right : a ⊔ b = b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_eq_right : a ⊔ b = b ↔ a ≤ b :=
  le_antisymm_iff.trans <| by simp

@[to_dual (attr := simp)]
/-
**left_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_eq_sup : a = a ⊔ b ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
-/
theorem left_eq_sup : a = a ⊔ b ↔ b ≤ a :=
  eq_comm.trans sup_eq_left

@[to_dual (attr := simp)]
/-
**right_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_eq_sup : b = a ⊔ b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
theorem right_eq_sup : b = a ⊔ b ↔ a ≤ b :=
  eq_comm.trans sup_eq_right

alias ⟨le_of_sup_eq', sup_of_le_left⟩ := sup_eq_left

alias ⟨le_of_sup_eq, sup_of_le_right⟩ := sup_eq_right

attribute [to_dual (attr := simp)] sup_of_le_left sup_of_le_right
attribute [to_dual le_of_inf_eq'] le_of_sup_eq
attribute [to_dual le_of_inf_eq] le_of_sup_eq'

@[to_dual (attr := simp) inf_lt_left]
/-
**left_lt_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_lt_sup : a < a ⊔ b ↔ ¬b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `left_eq_sup`：left_eq_sup : a = a ⊔ b ↔ b <= a
-/
theorem left_lt_sup : a < a ⊔ b ↔ ¬b ≤ a :=
  le_sup_left.lt_iff_ne.trans <| not_congr left_eq_sup

@[to_dual (attr := simp) inf_lt_right]
/-
**right_lt_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_lt_sup : b < a ⊔ b ↔ ¬a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `right_eq_sup`：right_eq_sup : b = a ⊔ b ↔ a <= b
-/
theorem right_lt_sup : b < a ⊔ b ↔ ¬a ≤ b :=
  le_sup_right.lt_iff_ne.trans <| not_congr right_eq_sup

@[to_dual inf_lt_left_or_right]
/-
**left_or_right_lt_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_or_right_lt_sup (h : a != b) : a < a ⊔ b ∨ b < a ⊔ b
参数：h : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `left_lt_sup`：left_lt_sup : a < a ⊔ b ↔ ¬b <= a
· 使用定理 `right_lt_sup`：right_lt_sup : b < a ⊔ b ↔ ¬a <= b
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Ne.not_le_or_not_ge`：Ne.not_le_or_not_ge (h : a != b) : ¬a <= b ∨ ¬b <= 
a
-/
theorem left_or_right_lt_sup (h : a ≠ b) : a < a ⊔ b ∨ b < a ⊔ b :=
  h.not_le_or_not_ge.symm.imp left_lt_sup.2 right_lt_sup.2

@[to_dual]
/-
**le_iff_exists_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_exists_sup : a <= b ↔ exists c, b = a ⊔ c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem le_iff_exists_sup : a ≤ b ↔ ∃ c, b = a ⊔ c := by
  constructor
  · intro h
    exact ⟨b, (sup_eq_right.mpr h).symm⟩
  · rintro ⟨c, rfl : _ = _ ⊔ _⟩
    exact le_sup_left

@[to_dual (attr := gcongr)]
/-
**sup_le_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
参数：h₁ : a <= b；h₂ : c <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
-/
theorem sup_le_sup (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
  sup_le (le_sup_of_le_left h₁) (le_sup_of_le_right h₂)

-- FIXME: these theorems use the wrong `left`/`right` naming convention.
-- FIXME: the fact that the following theorems use `(reorder := h₁ c)` is not good.
-- Instead, we should use a consistent argument ordering.
@[to_dual (reorder := h₁ c)]
/-
**sup_le_sup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
参数：h₁ : a <= b；c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem sup_le_sup_left (h₁ : a ≤ b) (c) : c ⊔ a ≤ c ⊔ b :=
  sup_le_sup le_rfl h₁

@[to_dual (reorder := h₁ c)]
/-
**sup_le_sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
参数：h₁ : a <= b；c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem sup_le_sup_right (h₁ : a ≤ b) (c) : a ⊔ c ≤ b ⊔ c :=
  sup_le_sup h₁ le_rfl

@[to_dual]
/-
**sup_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_idem (a : α) : a ⊔ a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_idem (a : α) : a ⊔ a = a := by simp

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.IdempotentOp (α := α) (· ⊔ ·) := ⟨sup_idem⟩

@[to_dual]
/-
**sup_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_comm (a b : α) : a ⊔ b = b ⊔ a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by apply le_antisymm <;> simp

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Commutative (α := α) (· ⊔ ·) := ⟨sup_comm⟩

@[to_dual]
/-
**sup_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
  eq_of_forall_ge_iff fun x => by simp only [sup_le_iff]; rw [and_assoc]

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Associative (α := α) (· ⊔ ·) := ⟨sup_assoc⟩

@[to_dual]
/-
**sup_left_right_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_left_right_swap (a b c : α) : a ⊔ b ⊔ c = c ⊔ b ⊔ a
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
-/
theorem sup_left_right_swap (a b c : α) : a ⊔ b ⊔ c = c ⊔ b ⊔ a := by
  rw [sup_comm, sup_comm a, sup_assoc]

@[to_dual]
/-
**sup_left_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_left_idem (a b : α) : a ⊔ (a ⊔ b) = a ⊔ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_left_idem (a b : α) : a ⊔ (a ⊔ b) = a ⊔ b := by simp

@[to_dual]
/-
**sup_right_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_right_idem (a b : α) : a ⊔ b ⊔ b = a ⊔ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_right_idem (a b : α) : a ⊔ b ⊔ b = a ⊔ b := by simp

@[to_dual]
/-
**sup_left_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) := by
  rw [← sup_assoc, ← sup_assoc, @sup_comm α _ a]

@[to_dual]
/-
**sup_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b := by
  rw [sup_assoc, sup_assoc, sup_comm b]

@[to_dual]
/-
**sup_sup_sup_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (b ⊔ d)
参数：a b c d : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `sup_left_comm`：sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (b ⊔ d) := by
  rw [sup_assoc, sup_left_comm b, ← sup_assoc]

@[to_dual]
/-
**sup_rotate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_rotate (a b c : α) : a ⊔ b ⊔ c = b ⊔ c ⊔ a
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem sup_rotate (a b c : α) : a ⊔ b ⊔ c = b ⊔ c ⊔ a := by
  rw [sup_assoc, sup_comm]

@[to_dual]
/-
**sup_rotate'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_rotate' (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (c ⊔ a)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
-/
theorem sup_rotate' (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (c ⊔ a) := by
  rw [sup_comm, sup_assoc]

@[to_dual]
/-
**sup_sup_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sup_distrib_left (a b c : α) : a ⊔ (b ⊔ c) = a ⊔ b ⊔ (a ⊔ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
theorem sup_sup_distrib_left (a b c : α) : a ⊔ (b ⊔ c) = a ⊔ b ⊔ (a ⊔ c) := by
  rw [sup_sup_sup_comm, sup_idem]

@[to_dual]
/-
**sup_sup_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ (b ⊔ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
theorem sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ (b ⊔ c) := by
  rw [sup_sup_sup_comm, sup_idem]

-- FIXME: These theorems use the wrong `left`/`right` naming convention.
@[to_dual]
/-
**sup_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_congr_left (hb : b <= a ⊔ c) (hc : c <= a ⊔ b) : a ⊔ b = a ⊔ c
参数：hb : b <= a ⊔ c；hc : c <= a ⊔ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem sup_congr_left (hb : b ≤ a ⊔ c) (hc : c ≤ a ⊔ b) : a ⊔ b = a ⊔ c :=
  (sup_le le_sup_left hb).antisymm <| sup_le le_sup_left hc

@[to_dual]
/-
**sup_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_congr_right (ha : a <= b ⊔ c) (hb : b <= a ⊔ c) : a ⊔ c = b ⊔ c
参数：ha : a <= b ⊔ c；hb : b <= a ⊔ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem sup_congr_right (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ⊔ c = b ⊔ c :=
  (sup_le ha le_sup_right).antisymm <| sup_le hb le_sup_right

@[to_dual]
/-
**sup_eq_sup_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_sup_iff_left : a ⊔ b = a ⊔ c ↔ b <= a ⊔ c ∧ c <= a ⊔ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_congr_left`：sup_congr_left (hb : b <= a ⊔ c) (hc : c <= a ⊔ b) : a ⊔
 b = a ⊔ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sup_eq_sup_iff_left : a ⊔ b = a ⊔ c ↔ b ≤ a ⊔ c ∧ c ≤ a ⊔ b :=
  ⟨fun h => ⟨h ▸ le_sup_right, h.symm ▸ le_sup_right⟩, fun h => sup_congr_left h.1 h.2⟩

@[to_dual]
/-
**sup_eq_sup_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_sup_iff_right : a ⊔ c = b ⊔ c ↔ a <= b ⊔ c ∧ b <= a ⊔ c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_congr_right`：sup_congr_right (ha : a <= b ⊔ c) (hb : b <= a ⊔ c) : a
 ⊔ c = b ⊔ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sup_eq_sup_iff_right : a ⊔ c = b ⊔ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c :=
  ⟨fun h => ⟨h ▸ le_sup_left, h.symm ▸ le_sup_left⟩, fun h => sup_congr_right h.1 h.2⟩

@[to_dual inf_lt_or_inf_lt]
/-
**Ne.lt_sup_or_lt_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ne.lt_sup_or_lt_sup (hab : a != b) : a < a ⊔ b ∨ b < a ⊔ b
参数：hab : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `left_lt_sup`：left_lt_sup : a < a ⊔ b ↔ ¬b <= a
· 使用定理 `right_lt_sup`：right_lt_sup : b < a ⊔ b ↔ ¬a <= b
· 使用定理 `Ne.not_le_or_not_ge`：Ne.not_le_or_not_ge (h : a != b) : ¬a <= b ∨ ¬b <= 
a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem Ne.lt_sup_or_lt_sup (hab : a ≠ b) : a < a ⊔ b ∨ b < a ⊔ b :=
  hab.symm.not_le_or_not_ge.imp left_lt_sup.2 right_lt_sup.2

@[to_dual inf_le_ite]
/-
**ite_le_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_le_sup (a b : α) (P : Prop) [Decidable P] : ite P a b <= a ⊔ b
参数：a b : α；P : Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem ite_le_sup (a b : α) (P : Prop) [Decidable P] : ite P a b ≤ a ⊔ b :=
  if h : P then (if_pos h).trans_le le_sup_left else (if_neg h).trans_le le_sup_right

@[to_dual (reorder := H (x y))]
/-
**SemilatticeSup.ext_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemilatticeSup.ext_sup {α} {A B : SemilatticeSup α} (H : forall x y : α, (
haveI
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem SemilatticeSup.ext_sup {α} {A B : SemilatticeSup α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y)
    (x y : α) :
    (haveI := A; x ⊔ y) = x ⊔ y :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff]; rw [← H, @sup_le_iff α A, H, H]

@[to_dual (reorder := H (x y))]
/-
**SemilatticeSup.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemilatticeSup.ext {α} {A B : SemilatticeSup α} (H : forall x y : α, (have
I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PartialOrder.ext`：PartialOrder.ext {A B : PartialOrder α} (H : forall x 
y : α, (haveI
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemilatticeSup.ext_sup`：SemilatticeSup.ext_sup {α} {A B : SemilatticeSup
 α} (H : forall x y : α, (haveI
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem SemilatticeSup.ext {α} {A B : SemilatticeSup α}
    (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by
  cases A
  cases B
  cases PartialOrder.ext H
  congr
  ext; apply SemilatticeSup.ext_sup H

@[to_dual]
/-
**OrderDual.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instSemilatticeSup (α) [h : SemilatticeInf α] : SemilatticeSup α
ᵒᵈ where sup a b
参数：α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeInf.inf_le_left`：∀ {α : Type u} [self : SemilatticeInf α] (a 
b : α), SemilatticeInf.inf a b ≤ a
· 使用定理 `SemilatticeInf.inf_le_right`：∀ {α : Type u} [self : SemilatticeInf α] (a
 b : α), SemilatticeInf.inf a b ≤ b
· 使用定理 `SemilatticeInf.le_inf`：∀ {α : Type u} [self : SemilatticeInf α] (a b c :
 α), a ≤ b → a ≤ c → a ≤ SemilatticeInf.inf b c
-/
instance OrderDual.instSemilatticeSup (α) [h : SemilatticeInf α] : SemilatticeSup αᵒᵈ where
  sup a b := h.inf a b
  le_sup_left := h.inf_le_left
  le_sup_right := h.inf_le_right
  sup_le _ _ _ := h.le_inf _ _ _

@[to_dual]
/-
**SemilatticeSup.dual_dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemilatticeSup.dual_dual (α : Type*) [H : SemilatticeSup α] : OrderDual.in
stSemilatticeSup αᵒᵈ = H
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.ext`：SemilatticeSup.ext {α} {A B : SemilatticeSup α} (H :
 forall x y : α, (haveI
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem SemilatticeSup.dual_dual (α : Type*) [H : SemilatticeSup α] :
    OrderDual.instSemilatticeSup αᵒᵈ = H :=
  SemilatticeSup.ext fun _ _ => Iff.rfl

end SemilatticeSup

/-!
### Lattices
-/


/-- A lattice is a join-semilattice which is also a meet-semilattice. -/
/-
**Lattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lattice is a join-semilattice which is also a meet-semilattice.
-/
class Lattice (α : Type u) extends SemilatticeSup α, SemilatticeInf α

attribute [to_dual existing] Lattice.toSemilatticeInf
/-
**OrderDual.instLattice** 是 Mathlib 中的一个定义，位于命名空间 `OrderDual`。
形式化陈述：(α : Type u_1) → [Lattice α] → Lattice αᵒᵈ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.instLattice (α) [Lattice α] : Lattice αᵒᵈ where

/-- The partial orders from `SemilatticeSup_mk'` and `SemilatticeInf_mk'` agree
if `sup` and `inf` satisfy the lattice absorption laws `sup_inf_self` (`a ⊔ a ⊓ b = a`)
and `inf_sup_self` (`a ⊓ (a ⊔ b) = a`). -/
/-
**semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Max α] [inst_1 : Min α] (sup_comm : ∀ (a b : α), 
a ⊔ b = b ⊔ a)   (sup_assoc : ∀ (a b c : α), a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (sup_idem 
: ∀ (a : α), a ⊔ a = a)   (inf_comm : ∀ (a b : α), a ⊓ b = b ⊓ a) (inf_assoc : ∀
 (a b c : α), a ⊓ b ⊓ c = a ⊓ (b ⊓ c))   (inf_idem : ∀ (a : α), a ⊓ a = a),   (∀
 (a b : α), a ⊔ a ⊓ b = a) →     (∀ (a b : α), a ⊓ (a ⊔ b) = a) →       (Semilat
ticeSup.mk' sup_comm sup_assoc sup_idem).toPartialOrder =         (SemilatticeIn
f.mk' inf_comm inf_assoc inf_idem).toPartialOrder
参数：sup_comm : ∀ (a b : α), a ⊔ b = b ⊔ a；sup_assoc : ∀ (a b c : α), a ⊔ b ⊔ c = 
a ⊔ (b ⊔ c)；sup_idem : ∀ (a : α), a ⊔ a = a；inf_comm : ∀ (a b : α), a ⊓ b = b ⊓ 
a；inf_assoc : ∀ (a b c : α), a ⊓ b ⊓ c = a ⊓ (b ⊓ c)；inf_idem : ∀ (a : α), a ⊓ a
 = a；∀ (a b : α), a ⊔ a ⊓ b = a；∀ (a b : α), a ⊓ (a ⊔ b) = a；SemilatticeSup.mk' 
sup_comm sup_assoc sup_idem；SemilatticeInf.mk' inf_comm inf_assoc inf_idem。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PartialOrder.ext`：PartialOrder.ext {A B : PartialOrder α} (H : forall x 
y : α, (haveI
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The partial orders from `SemilatticeSup_mk'` and `SemilatticeInf_mk'` agree
if `sup` and `inf` satisfy the lattice absorption laws `sup_inf_self` (`a ⊔ a ⊓ 
b = a`)
and `inf_sup_self` (`a ⊓ (a ⊔ b) = a`).
-/
theorem semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder
    {α : Type*} [Max α] [Min α]
    (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a) (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c))
    (sup_idem : ∀ a : α, a ⊔ a = a) (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (inf_idem : ∀ a : α, a ⊓ a = a)
    (sup_inf_self : ∀ a b : α, a ⊔ a ⊓ b = a) (inf_sup_self : ∀ a b : α, a ⊓ (a ⊔ b) = a) :
    @SemilatticeSup.toPartialOrder _ (SemilatticeSup.mk' sup_comm sup_assoc sup_idem) =
      @SemilatticeInf.toPartialOrder _ (SemilatticeInf.mk' inf_comm inf_assoc inf_idem) :=
  PartialOrder.ext fun a b =>
    show a ⊔ b = b ↔ b ⊓ a = a from
      ⟨fun h => by rw [← h, inf_comm, inf_sup_self], fun h => by rw [← h, sup_comm, sup_inf_self]⟩

/-- A type with a pair of commutative and associative binary operations which satisfy two absorption
laws relating the two operations has the structure of a lattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
@[instance_reducible]
/-
**Lattice.mk'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Lattice.mk' {α : Type*} [Max α] [Min α] (sup_comm : forall a b : α, a ⊔ b 
= b ⊔ a) (sup_assoc : forall a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (inf_comm : for
all a b : α, a ⊓ b = b ⊓ a) (inf_assoc : forall a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ 
c)) (sup_inf_self : forall a b : α, a ⊔ a ⊓ b = a) (inf_sup_self : forall a b : 
α, a ⊓ (a ⊔ b) = a) : Lattice α
参数：sup_comm : forall a b : α, a ⊔ b = b ⊔ a；sup_assoc : forall a b c : α, a ⊔ b 
⊔ c = a ⊔ (b ⊔ c)；inf_comm : forall a b : α, a ⊓ b = b ⊓ a；inf_assoc : forall a 
b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)；sup_inf_self : forall a b : α, a ⊔ a ⊓ b = a；in
f_sup_self : forall a b : α, a ⊓ (a ⊔ b) = a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder`：∀ {α
 : Type u_1} [inst : Max α] [inst_1 : Min α] (sup_comm : ∀ (a b : α), a ⊔ b = b 
⊔ a)   (sup_assoc : ∀ (a b c : α), a ⊔ b ⊔ c = a ⊔ (b ⊔ …

--- 原说明 ---
A type with a pair of commutative and associative binary operations which satisf
y two absorption
laws relating the two operations has the structure of a lattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq
_right`.
-/
def Lattice.mk' {α : Type*} [Max α] [Min α] (sup_comm : ∀ a b : α, a ⊔ b = b ⊔ a)
    (sup_assoc : ∀ a b c : α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c)) (inf_comm : ∀ a b : α, a ⊓ b = b ⊓ a)
    (inf_assoc : ∀ a b c : α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c)) (sup_inf_self : ∀ a b : α, a ⊔ a ⊓ b = a)
    (inf_sup_self : ∀ a b : α, a ⊓ (a ⊔ b) = a) : Lattice α :=
  have sup_idem : ∀ b : α, b ⊔ b = b := fun b =>
    calc
      b ⊔ b = b ⊔ b ⊓ (b ⊔ b) := by rw [inf_sup_self]
      _ = b := by rw [sup_inf_self]
  have inf_idem : ∀ b : α, b ⊓ b = b := fun b =>
    calc
      b ⊓ b = b ⊓ (b ⊔ b ⊓ b) := by rw [sup_inf_self]
      _ = b := by rw [inf_sup_self]
  let semilatt_inf_inst := SemilatticeInf.mk' inf_comm inf_assoc inf_idem
  let semilatt_sup_inst := SemilatticeSup.mk' sup_comm sup_assoc sup_idem
  have partial_order_eq : @SemilatticeSup.toPartialOrder _ semilatt_sup_inst =
                          @SemilatticeInf.toPartialOrder _ semilatt_inf_inst :=
    semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder _ _ _ _ _ _
      sup_inf_self inf_sup_self
  { semilatt_sup_inst, semilatt_inf_inst with
    inf_le_left := fun a b => by
      rw [partial_order_eq]
      apply inf_le_left,
    inf_le_right := fun a b => by
      rw [partial_order_eq]
      apply inf_le_right,
    le_inf := fun a b c => by
      rw [partial_order_eq]
      apply le_inf }

section Lattice

variable [Lattice α] {a b c : α}

/-
**inf_le_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_le_sup : a ⊓ b <= a ⊔ b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem inf_le_sup : a ⊓ b ≤ a ⊔ b :=
  inf_le_left.trans le_sup_left
/-
**sup_le_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_le_inf : a ⊔ b <= a ⊓ b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_le_inf : a ⊔ b ≤ a ⊓ b ↔ a = b := by simp [le_antisymm_iff, and_comm]

@[to_dual (attr := simp)]
/-
**inf_eq_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_eq_sup : a ⊓ b = a ⊔ b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
· 使用定理 `sup_le_inf`：sup_le_inf : a ⊔ b <= a ⊓ b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inf_eq_sup : a ⊓ b = a ⊔ b ↔ a = b := by rw [← inf_le_sup.ge_iff_eq, sup_le_inf]
/-
**inf_lt_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Lattice α] {a b : α}, a ⊓ b < a ⊔ b ↔ a ≠ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `inf_eq_sup`：inf_eq_sup : a ⊓ b = a ⊔ b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma inf_lt_sup : a ⊓ b < a ⊔ b ↔ a ≠ b := by rw [inf_le_sup.lt_iff_ne, Ne, inf_eq_sup]

@[to_dual (attr := simp) inf_right_le_sup_left]
/-
**inf_left_le_sup_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_left_le_sup_right : (a ⊓ b) <= (b ⊔ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma inf_left_le_sup_right : (a ⊓ b) ≤ (b ⊔ c) := le_trans inf_le_right le_sup_left

@[simp, to_dual self]
/-
**inf_right_le_sup_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_right_le_sup_right : (b ⊓ a) <= (b ⊔ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma inf_right_le_sup_right : (b ⊓ a) ≤ (b ⊔ c) := le_trans inf_le_left le_sup_left

@[simp, to_dual self]
/-
**inf_left_le_sup_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_left_le_sup_left : (a ⊓ b) <= (c ⊔ b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma inf_left_le_sup_left : (a ⊓ b) ≤ (c ⊔ b) := le_trans inf_le_right le_sup_right

@[to_dual]
/-
**inf_eq_and_sup_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_eq_and_sup_eq_iff : a ⊓ b = c ∧ a ⊔ b = c ↔ a = c ∧ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_eq_inf`：∀ {α : Type u} [inst : Lattice α] {a b : α}, a ⊔ b = a ⊓ b ↔
 a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
lemma inf_eq_and_sup_eq_iff : a ⊓ b = c ∧ a ⊔ b = c ↔ a = c ∧ b = c := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain rfl := sup_eq_inf.1 (h.2.trans h.1.symm)
    simpa using h
  · rintro ⟨rfl, rfl⟩
    exact ⟨inf_idem _, sup_idem _⟩

/-!
#### Distributivity laws
-/


-- TODO: better names?
@[to_dual le_inf_sup]
/-
**sup_inf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_inf_le : a ⊔ b ⊓ c <= (a ⊔ b) ⊓ (a ⊔ c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem sup_inf_le : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
  le_inf (sup_le_sup_left inf_le_left _) (sup_le_sup_left inf_le_right _)

@[to_dual]
/-
**inf_sup_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sup_self : a ⊓ (a ⊔ b) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inf_sup_self : a ⊓ (a ⊔ b) = a := by simp

@[to_dual]
/-
**sup_eq_iff_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_iff_inf_eq : a ⊔ b = b ↔ a ⊓ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sup_eq_iff_inf_eq : a ⊔ b = b ↔ a ⊓ b = a := by rw [sup_eq_right, ← inf_eq_left]

@[to_dual self]
/-
**Lattice.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Lattice.ext {α} {A B : Lattice α} (H : forall x y : α, (haveI
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.ext`：SemilatticeSup.ext {α} {A B : SemilatticeSup α} (H :
 forall x y : α, (haveI
· 使用定理 `SemilatticeInf.ext`：∀ {α : Type u_1} {A B : SemilatticeInf α}, (∀ (y x :
 α), y ≤ x ↔ y ≤ x) → A = B
· 使用定理 `Lattice.inf_le_left`：∀ {α : Type u} [self : Lattice α] (a b : α), Lattic
e.inf a b ≤ a
· 使用定理 `Lattice.inf_le_right`：∀ {α : Type u} [self : Lattice α] (a b : α), Latti
ce.inf a b ≤ b
· 使用定理 `Lattice.le_inf`：∀ {α : Type u} [self : Lattice α] (a b c : α), a ≤ b → a
 ≤ c → a ≤ Lattice.inf b c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem Lattice.ext {α} {A B : Lattice α} (H : ∀ x y : α, (haveI := A; x ≤ y) ↔ x ≤ y) :
    A = B := by
  cases A
  cases B
  cases SemilatticeSup.ext H
  cases SemilatticeInf.ext H
  congr

end Lattice

/-!
### Distributive lattices
-/


/-- A distributive lattice is a lattice that satisfies any of four
equivalent distributive properties (of `sup` over `inf` or `inf` over `sup`,
on the left or right).

The definition here chooses `le_sup_inf`: `(x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)`. To prove distributivity
from the dual law, use `DistribLattice.of_inf_sup_le`.

A classic example of a distributive lattice
is the lattice of subsets of a set, and in fact this example is
generic in the sense that every distributive lattice is realizable
as a sublattice of a powerset lattice. -/
/-
**DistribLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A distributive lattice is a lattice that satisfies any of four
equivalent distributive properties (of `sup` over `inf` or `inf` over `sup`,
on the left or right).

The definition here chooses `le_sup_inf`: `(x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)`. To 
prove distributivity
from the dual law, use `DistribLattice.of_inf_sup_le`.

A classic example of a distributive lattice
is the lattice of subsets of a set, and in fact this example is
generic in the sense that every distributive lattice is realizable
as a sublattice of a powerset lattice.
-/
class DistribLattice (α) extends Lattice α where
  /-- The infimum distributes over the supremum -/
  protected le_sup_inf : ∀ x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z

section DistribLattice

variable [DistribLattice α] {x y z : α}

/-
**le_sup_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sup_inf {x y z : α} : (x ⊔ y) ⊓ (x ⊔ z) <= x ⊔ y ⊓ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribLattice.le_sup_inf`：∀ {α : Type u_1} [self : DistribLattice α] (x
 y z : α), (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z
-/
theorem le_sup_inf {x y z : α} : (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z :=
  DistribLattice.le_sup_inf x y z
/-
**sup_inf_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_inf_le`：sup_inf_le : a ⊔ b ⊓ c <= (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `le_sup_inf`：le_sup_inf {x y z : α} : (x ⊔ y) ⊓ (x ⊔ z) <= x ⊔ y ⊓ z
-/
theorem sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  le_antisymm sup_inf_le le_sup_inf
/-
**sup_inf_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) := by
  simp only [sup_inf_left, sup_comm _ c]

@[to_dual existing]
/-
**inf_sup_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_sup_self`：inf_sup_self : a ⊓ (a ⊔ b) = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_inf_self`：∀ {α : Type u} [inst : Lattice α] {a b : α}, a ⊔ a ⊓ b = a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
-/
theorem inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c :=
  calc
    a ⊓ (b ⊔ c) = a ⊓ (a ⊔ c) ⊓ (b ⊔ c) := by rw [inf_sup_self]
    _ = a ⊓ (a ⊓ b ⊔ c) := by simp only [inf_assoc, sup_inf_right]
    _ = (a ⊔ a ⊓ b) ⊓ (a ⊓ b ⊔ c) := by rw [sup_inf_self]
    _ = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm]
    _ = a ⊓ b ⊔ a ⊓ c := by rw [sup_inf_left]

@[to_dual existing le_sup_inf]
/-
**inf_sup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sup_le {x y z : α} : x ⊓ (y ⊔ z) <= (x ⊓ y) ⊔ (x ⊓ z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem inf_sup_le {x y z : α} : x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z) := by
  rw [inf_sup_left]
/-
**OrderDual.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.instDistribLattice (α : Type*) [DistribLattice α] : DistribLatti
ce αᵒᵈ where le_sup_inf _ _ _
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sup_le`：inf_sup_le {x y z : α} : x ⊓ (y ⊔ z) <= (x ⊓ y) ⊔ (x ⊓ z)
-/
instance OrderDual.instDistribLattice (α : Type*) [DistribLattice α] : DistribLattice αᵒᵈ where
  le_sup_inf _ _ _ := inf_sup_le

@[to_dual existing]
/-
**inf_sup_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c := by
  simp only [inf_sup_left, inf_comm _ c]

@[to_dual self (reorder := x y, h₁ h₂)]
/-
**le_of_inf_le_sup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_inf_le_sup_le (h₁ : x ⊓ z <= y ⊓ z) (h₂ : x ⊔ z <= y ⊔ z) : x <= y
参数：h₁ : x ⊓ z <= y ⊓ z；h₂ : x ⊔ z <= y ⊔ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem le_of_inf_le_sup_le (h₁ : x ⊓ z ≤ y ⊓ z) (h₂ : x ⊔ z ≤ y ⊔ z) : x ≤ y :=
  calc
    x ≤ y ⊓ z ⊔ x := le_sup_right
    _ = (y ⊔ x) ⊓ (x ⊔ z) := by rw [sup_inf_right, sup_comm x]
    _ ≤ (y ⊔ x) ⊓ (y ⊔ z) := inf_le_inf_left _ h₂
    _ = y ⊔ x ⊓ z := by rw [← sup_inf_left]
    _ ≤ y ⊔ y ⊓ z := sup_le_sup_left h₁ _
    _ ≤ _ := sup_le (le_refl y) inf_le_left

@[to_dual self (reorder := h₁ h₂)]
/-
**eq_of_inf_eq_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_inf_eq_sup_eq {a b c : α} (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) 
: b = c
参数：h₁ : b ⊓ a = c ⊓ a；h₂ : b ⊔ a = c ⊔ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_inf_le_sup_le`：le_of_inf_le_sup_le (h₁ : x ⊓ z <= y ⊓ z) (h₂ : x ⊔
 z <= y ⊔ z) : x <= y
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_inf_eq_sup_eq {a b c : α} (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
  le_antisymm (le_of_inf_le_sup_le (le_of_eq h₁) (le_of_eq h₂))
    (le_of_inf_le_sup_le (le_of_eq h₁.symm) (le_of_eq h₂.symm))

end DistribLattice

-- See note [reducible non-instances]
/-- Prove distributivity of an existing lattice from the dual distributive law. -/
@[to_dual existing mk]
/-
**DistribLattice.ofInfSupLe** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DistribLattice.ofInfSupLe [Lattice α] (inf_sup_le : forall a b c : α, a ⊓ 
(b ⊔ c) <= a ⊓ b ⊔ a ⊓ c) : DistribLattice α where le_sup_inf
参数：inf_sup_le : forall a b c : α, a ⊓ (b ⊔ c) <= a ⊓ b ⊔ a ⊓ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prove distributivity of an existing lattice from the dual distributive law.
-/
abbrev DistribLattice.ofInfSupLe
    [Lattice α] (inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c) : DistribLattice α where
  le_sup_inf := (@OrderDual.instDistribLattice αᵒᵈ { (inferInstance : Lattice αᵒᵈ) with
      le_sup_inf := inf_sup_le }).le_sup_inf

/-!
### Lattices derived from linear orders
-/

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrder.toLattice {α : Type u} [LinearOrder α] : Lattice α where
  sup := max
  inf := min
  le_sup_left := le_max_left; le_sup_right := le_max_right; sup_le _ _ _ := max_le
  inf_le_left := min_le_left; inf_le_right := min_le_right; le_inf _ _ _ := le_min

section LinearOrder

variable [LinearOrder α] {a b c d : α}

@[to_dual]
/-
**sup_ind** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_ind (a b : α) {p : α -> Prop} (ha : p a) (hb : p b) : p (a ⊔ b)
参数：a b : α；ha : p a；hb : p b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
-/
theorem sup_ind (a b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊔ b) :=
  (Std.Total.total a b).elim (fun h : a ≤ b => by rwa [sup_eq_right.2 h]) fun h => by
  rwa [sup_eq_left.2 h]

@[to_dual (attr := simp) inf_le_iff]
/-
**le_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sup_iff : a <= b ⊔ c ↔ a <= b ∨ a <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_sup_iff : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c := by
  grind

@[to_dual (attr := simp) inf_lt_iff]
/-
**lt_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c := by
  grind

@[to_dual (attr := simp) lt_inf_iff]
/-
**sup_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `sup_ind`：sup_ind (a b : α) {p : α -> Prop} (ha : p a) (hb : p b) : p (a 
⊔ b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a :=
  ⟨fun h => ⟨le_sup_left.trans_lt h, le_sup_right.trans_lt h⟩,
   fun h => sup_ind (p := (· < a)) b c h.1 h.2⟩

variable (a b c d)

@[to_dual]
/-
**max_max_max_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_max_max_comm : max (max a b) (max c d) = max (max a c) (max b d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
-/
theorem max_max_max_comm : max (max a b) (max c d) = max (max a c) (max b d) :=
  sup_sup_sup_comm _ _ _ _

end LinearOrder

/-
**sup_eq_maxDefault** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sup_eq_maxDefault [SemilatticeSup α] [DecidableLE α] [@Std.Total α (· <= ·
)] : (· ⊔ ·) = (maxDefault : α -> α -> α)
参数：· <= ·。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
-/
theorem sup_eq_maxDefault [SemilatticeSup α] [DecidableLE α] [@Std.Total α (· ≤ ·)] :
    (· ⊔ ·) = (maxDefault : α → α → α) := by
  ext x y
  unfold maxDefault
  split_ifs with h'
  exacts [sup_of_le_right h', sup_of_le_left <| (total_of (· ≤ ·) x y).resolve_left h']
/-
**inf_eq_minDefault** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_eq_minDefault [SemilatticeInf α] [DecidableLE α] [@Std.Total α (· <= ·
)] : (· ⊓ ·) = (minDefault : α -> α -> α)
参数：· <= ·。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
-/
theorem inf_eq_minDefault [SemilatticeInf α] [DecidableLE α] [@Std.Total α (· ≤ ·)] :
    (· ⊓ ·) = (minDefault : α → α → α) := by
  ext x y
  unfold minDefault
  split_ifs with h'
  exacts [inf_of_le_left h', inf_of_le_right <| (total_of (· ≤ ·) x y).resolve_left h']

/-- A lattice with total order is a linear order.

See note [reducible non-instances]. -/
/-
**Lattice.toLinearOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Lattice.toLinearOrder (α : Type u) [Lattice α] [DecidableEq α] [DecidableL
E α] [DecidableLT α] [@Std.Total α (· <= ·)] : LinearOrder α where toDecidableLE
参数：α : Type u；· <= ·。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lattice with total order is a linear order.

See note [reducible non-instances].
-/
abbrev Lattice.toLinearOrder (α : Type u) [Lattice α] [DecidableEq α]
    [DecidableLE α] [DecidableLT α] [@Std.Total α (· ≤ ·)] : LinearOrder α where
  toDecidableLE := ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total := total_of (· ≤ ·)
  max_def := by exact congr_fun₂ sup_eq_maxDefault
  min_def := by exact congr_fun₂ inf_eq_minDefault

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {α : Type u} [LinearOrder α] : DistribLattice α where
  le_sup_inf _ b c :=
    match le_total b c with
    | Or.inl h => inf_le_of_left_le <| sup_le_sup_left (le_inf (le_refl b) h) _
    | Or.inr h => inf_le_of_right_le <| sup_le_sup_left (le_inf h (le_refl c)) _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribLattice ℕ := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice ℤ := inferInstance

/-! ### Dual order -/


open OrderDual

@[to_dual (attr := simp)]
/-
**ofDual_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_sup [Min α] (a b : αᵒᵈ) : ofDual (a ⊔ b) = ofDual a ⊓ ofDual b
参数：a b : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_sup [Min α] (a b : αᵒᵈ) : ofDual (a ⊔ b) = ofDual a ⊓ ofDual b :=
  rfl

@[to_dual (attr := simp)]
/-
**toDual_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_sup [Max α] (a b : α) : toDual (a ⊔ b) = toDual a ⊓ toDual b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_sup [Max α] (a b : α) : toDual (a ⊔ b) = toDual a ⊓ toDual b :=
  rfl

section LinearOrder

variable [LinearOrder α]

/-
**ofDual_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : LinearOrder α] (a b : αᵒᵈ),   OrderDual.ofDual (max
 a b) = min (OrderDual.ofDual a) (OrderDual.ofDual b)
参数：a b : αᵒᵈ；max a b；OrderDual.ofDual a；OrderDual.ofDual b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] theorem ofDual_max (a b : αᵒᵈ) : ofDual (max a b) = min (ofDual a) (ofDual b) :=
  rfl
/-
**toDual_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : LinearOrder α] (a b : α),   OrderDual.toDual (max a
 b) = min (OrderDual.toDual a) (OrderDual.toDual b)
参数：a b : α；max a b；OrderDual.toDual a；OrderDual.toDual b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] theorem toDual_max (a b : α) : toDual (max a b) = min (toDual a) (toDual b) :=
  rfl

end LinearOrder

/-! ### Function lattices -/


namespace Pi

variable {ι : Type*} {α' : ι → Type*}

@[to_dual]
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Max (α' i)] : Max (∀ i, α' i) :=
  ⟨fun f g i => f i ⊔ g i⟩

@[to_dual (attr := simp)]
/-
**Pi.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：sup_apply [forall i, Max (α' i)] (f g : forall i, α' i) (i : ι) : (f ⊔ g) 
i = f i ⊔ g i
参数：α' i；f g : forall i, α' i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply [∀ i, Max (α' i)] (f g : ∀ i, α' i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  rfl

@[to_dual (attr := push ←)]
/-
**Pi.sup_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：sup_def [forall i, Max (α' i)] (f g : forall i, α' i) : f ⊔ g = fun i => f
 i ⊔ g i
参数：α' i；f g : forall i, α' i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_def [∀ i, Max (α' i)] (f g : ∀ i, α' i) : f ⊔ g = fun i => f i ⊔ g i :=
  rfl

@[to_dual]
/-
**Pi.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instSemilatticeSup [forall i, SemilatticeSup (α' i)] : SemilatticeSup (for
all i, α' i) where sup x y i
参数：α' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeSup [∀ i, SemilatticeSup (α' i)] : SemilatticeSup (∀ i, α' i) where
  sup x y i := x i ⊔ y i
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ ac bc i := sup_le (ac i) (bc i)
/-
**Pi.instLattice** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：{ι : Type u_1} → {α' : ι → Type u_2} → [(i : ι) → Lattice (α' i)] → Lattic
e ((i : ι) → α' i)
参数：i : ι；α' i；(i : ι) → α' i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLattice [∀ i, Lattice (α' i)] : Lattice (∀ i, α' i) where
/-
**Pi.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instDistribLattice [forall i, DistribLattice (α' i)] : DistribLattice (for
all i, α' i) where le_sup_inf _ _ _ _
参数：α' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribLattice [∀ i, DistribLattice (α' i)] : DistribLattice (∀ i, α' i) where
  le_sup_inf _ _ _ _ := le_sup_inf

end Pi

namespace Function

variable {ι : Type*} {π : ι → Type*} [DecidableEq ι]

-- Porting note: Dot notation on `Function.update` broke
@[to_dual]
/-
**Function.update_sup** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_sup [forall i, SemilatticeSup (π i)] (f : forall i, π i) (i : ι) (a
 b : π i) : update f i (a ⊔ b) = update f i a ⊔ update f i b
参数：π i；f : forall i, π i；i : ι；a b : π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
theorem update_sup [∀ i, SemilatticeSup (π i)] (f : ∀ i, π i) (i : ι) (a b : π i) :
    update f i (a ⊔ b) = update f i a ⊔ update f i b :=
  funext fun j => by obtain rfl | hji := eq_or_ne j i <;> simp [update_of_ne, *]

end Function

/-!
### Monotone functions and lattices
-/


namespace Monotone

/-- Pointwise supremum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise infimum of two monotone functions is a monotone function. -/]
/-
**Monotone.sup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : SemilatticeSup β
] {f g : α → β},   Monotone f → Monotone g → Monotone (f ⊔ g)
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d

--- 原说明 ---
Pointwise supremum of two monotone functions is a monotone function.
-/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone (f ⊔ g) := fun _ _ h => sup_le_sup (hf h) (hg h)

/-- Pointwise maximum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise minimum of two monotone functions is a monotone function. -/]
/-
**Monotone.max** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : LinearOrder β] {
f g : α → β},   Monotone f → Monotone g → Monotone fun x => max (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.sup`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : 
SemilatticeSup β] {f g : α → β},   Monotone f → Monotone g → Monotone (f ⊔ g)

--- 原说明 ---
Pointwise maximum of two monotone functions is a monotone function.
-/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} (hf : Monotone f)
    (hg : Monotone g) :
    Monotone fun x => max (f x) (g x) :=
  hf.sup hg

@[to_dual map_inf_le]
/-
**Monotone.le_map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α -> β} (h : Monoton
e f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
参数：h : Monotone f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α → β} (h : Monotone f) (x y : α) :
    f x ⊔ f y ≤ f (x ⊔ y) :=
  sup_le (h le_sup_left) (h le_sup_right)

@[to_dual of_map_inf_le_left]
/-
**Monotone.of_left_le_map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：of_left_le_map_sup [SemilatticeSup α] [Preorder β] {f : α -> β} (h : foral
l x y, f x <= f (x ⊔ y)) : Monotone f
参数：h : forall x y, f x <= f (x ⊔ y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
theorem of_left_le_map_sup [SemilatticeSup α] [Preorder β] {f : α → β}
    (h : ∀ x y, f x ≤ f (x ⊔ y)) : Monotone f := by
  intro x y hxy
  rw [← sup_eq_right.2 hxy]
  apply h

@[to_dual of_map_inf_le]
/-
**Monotone.of_le_map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：of_le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α -> β} (h : fora
ll x y, f x ⊔ f y <= f (x ⊔ y)) : Monotone f
参数：h : forall x y, f x ⊔ f y <= f (x ⊔ y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.of_left_le_map_sup`：of_left_le_map_sup [SemilatticeSup α] [Preo
rder β] {f : α -> β} (h : forall x y, f x <= f (x ⊔ y)) : Monotone f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem of_le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α → β}
    (h : ∀ x y, f x ⊔ f y ≤ f (x ⊔ y)) : Monotone f :=
  of_left_le_map_sup fun x y ↦ le_sup_left.trans (h x y)

@[to_dual]
/-
**Monotone.of_map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：of_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α -> β} (h : forall 
x y, f (x ⊔ y) = f x ⊔ f y) : Monotone f
参数：h : forall x y, f (x ⊔ y) = f x ⊔ f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.of_le_map_sup`：of_le_map_sup [SemilatticeSup α] [SemilatticeSup
 β] {f : α -> β} (h : forall x y, f x ⊔ f y <= f (x ⊔ y)) : Monotone f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem of_map_sup [SemilatticeSup α] [SemilatticeSup β] {f : α → β}
    (h : ∀ x y, f (x ⊔ y) = f x ⊔ f y) : Monotone f :=
  of_le_map_sup fun x y ↦ (h x y).ge

variable [LinearOrder α]

@[to_dual]
/-
**Monotone.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：map_sup [SemilatticeSup β] {f : α -> β} (hf : Monotone f) (x y : α) : f (x
 ⊔ y) = f x ⊔ f y
参数：hf : Monotone f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
theorem map_sup [SemilatticeSup β] {f : α → β} (hf : Monotone f) (x y : α) :
    f (x ⊔ y) = f x ⊔ f y :=
  (Std.Total.total x y).elim (fun h : x ≤ y => by simp only [h, hf h, sup_of_le_right]) fun h => by
    simp only [h, hf h, sup_of_le_left]

end Monotone

/-
**exists_ge_and_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ge_and_iff_exists [SemilatticeSup α] {P : α -> Prop} {x₀ : α} (hP :
 Monotone P) : (exists x, x₀ <= x ∧ P x) ↔ exists x, P x
参数：hP : Monotone P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem exists_ge_and_iff_exists [SemilatticeSup α] {P : α → Prop} {x₀ : α} (hP : Monotone P) :
    (∃ x, x₀ ≤ x ∧ P x) ↔ ∃ x, P x :=
  ⟨fun h => h.imp fun _ h => h.2, fun ⟨x, hx⟩ => ⟨x ⊔ x₀, le_sup_right, hP le_sup_left hx⟩⟩
/-
**exists_and_iff_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_and_iff_of_monotone [SemilatticeSup α] {P Q : α -> Prop} (hP : Mono
tone P) (hQ : Monotone Q) : ((exists x, P x) ∧ exists x, Q x) ↔ (exists x, P x ∧
 Q x)
参数：hP : Monotone P；hQ : Monotone Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem exists_and_iff_of_monotone [SemilatticeSup α] {P Q : α → Prop}
    (hP : Monotone P) (hQ : Monotone Q) :
    ((∃ x, P x) ∧ ∃ x, Q x) ↔ (∃ x, P x ∧ Q x) :=
  ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ ↦ ⟨x ⊔ y, ⟨hP le_sup_left hPx, hQ le_sup_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ ↦ ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

namespace MonotoneOn
variable {f : α → β} {s : Set α} {x y : α}

/-- Pointwise supremum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise infimum of two monotone functions is a monotone function. -/]
/-
**MonotoneOn.sup** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : SemilatticeSup β
] {f g : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn g s → MonotoneOn (f ⊔
 g) s
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d

--- 原说明 ---
Pointwise supremum of two monotone functions is a monotone function.
-/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} {s : Set α}
    (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (f ⊔ g) s :=
  fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)

/-- Pointwise maximum of two monotone functions is a monotone function. -/
@[to_dual /-- Pointwise minimum of two monotone functions is a monotone function. -/]
/-
**MonotoneOn.max** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : LinearOrder β] {
f g : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn g s → MonotoneOn (fun x 
=> max (f x) (g x)) s
参数：fun x => max (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.sup`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: SemilatticeSup β] {f g : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn g s
 → M…

--- 原说明 ---
Pointwise maximum of two monotone functions is a monotone function.
-/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => max (f x) (g x)) s :=
  hf.sup hg

@[to_dual]
/-
**MonotoneOn.of_map_sup** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：of_map_sup [SemilatticeSup α] [SemilatticeSup β] (h : forall x in s, foral
l y in s, f (x ⊔ y) = f x ⊔ f y) : MonotoneOn f s
参数：h : forall x in s, forall y in s, f (x ⊔ y) = f x ⊔ f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem of_map_sup [SemilatticeSup α] [SemilatticeSup β]
    (h : ∀ x ∈ s, ∀ y ∈ s, f (x ⊔ y) = f x ⊔ f y) : MonotoneOn f s := fun x hx y hy hxy =>
  sup_eq_right.1 <| by rw [← h _ hx _ hy, sup_eq_right.2 hxy]

variable [LinearOrder α]

@[to_dual]
/-
**MonotoneOn.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：map_sup [SemilatticeSup β] (hf : MonotoneOn f s) (hx : x in s) (hy : y in 
s) : f (x ⊔ y) = f x ⊔ f y
参数：hf : MonotoneOn f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
theorem map_sup [SemilatticeSup β] (hf : MonotoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    f (x ⊔ y) = f x ⊔ f y := by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right]

end MonotoneOn

namespace Antitone

/-- Pointwise supremum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise infimum of two antitone functions is an antitone function. -/]
/-
**Antitone.sup** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : SemilatticeSup β
] {f g : α → β},   Antitone f → Antitone g → Antitone (f ⊔ g)
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d

--- 原说明 ---
Pointwise supremum of two antitone functions is an antitone function.
-/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone (f ⊔ g) := fun _ _ h => sup_le_sup (hf h) (hg h)

/-- Pointwise maximum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise minimum of two antitone functions is an antitone function. -/]
/-
**Antitone.max** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : LinearOrder β] {
f g : α → β},   Antitone f → Antitone g → Antitone fun x => max (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.sup`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : 
SemilatticeSup β] {f g : α → β},   Antitone f → Antitone g → Antitone (f ⊔ g)

--- 原说明 ---
Pointwise maximum of two antitone functions is an antitone function.
-/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} (hf : Antitone f)
    (hg : Antitone g) :
    Antitone fun x => max (f x) (g x) :=
  hf.sup hg

@[to_dual le_map_inf]
/-
**Antitone.map_sup_le** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：map_sup_le [SemilatticeSup α] [SemilatticeInf β] {f : α -> β} (h : Antiton
e f) (x y : α) : f (x ⊔ y) <= f x ⊓ f y
参数：h : Antitone f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_sup`：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f
 : α -> β} (h : Monotone f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem map_sup_le [SemilatticeSup α] [SemilatticeInf β] {f : α → β} (h : Antitone f) (x y : α) :
    f (x ⊔ y) ≤ f x ⊓ f y :=
  h.dual_right.le_map_sup x y

variable [LinearOrder α]

@[to_dual]
/-
**Antitone.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：map_sup [SemilatticeInf β] {f : α -> β} (hf : Antitone f) (x y : α) : f (x
 ⊔ y) = f x ⊓ f y
参数：hf : Antitone f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_sup`：map_sup [SemilatticeSup β] {f : α -> β} (hf : Monotone
 f) (x y : α) : f (x ⊔ y) = f x ⊔ f y
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem map_sup [SemilatticeInf β] {f : α → β} (hf : Antitone f) (x y : α) :
    f (x ⊔ y) = f x ⊓ f y :=
  hf.dual_right.map_sup x y

end Antitone

/-
**exists_le_and_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_le_and_iff_exists [SemilatticeInf α] {P : α -> Prop} {x₀ : α} (hP :
 Antitone P) : (exists x, x <= x₀ ∧ P x) ↔ exists x, P x
参数：hP : Antitone P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ge_and_iff_exists`：exists_ge_and_iff_exists [SemilatticeSup α] {P
 : α -> Prop} {x₀ : α} (hP : Monotone P) : (exists x, x₀ <= x ∧ P x) ↔ exists x,
 P x
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem exists_le_and_iff_exists [SemilatticeInf α] {P : α → Prop} {x₀ : α} (hP : Antitone P) :
    (∃ x, x ≤ x₀ ∧ P x) ↔ ∃ x, P x :=
  exists_ge_and_iff_exists <| hP.dual_left
/-
**exists_and_iff_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_and_iff_of_antitone [SemilatticeInf α] {P Q : α -> Prop} (hP : Anti
tone P) (hQ : Antitone Q) : ((exists x, P x) ∧ exists x, Q x) ↔ (exists x, P x ∧
 Q x)
参数：hP : Antitone P；hQ : Antitone Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem exists_and_iff_of_antitone [SemilatticeInf α] {P Q : α → Prop}
    (hP : Antitone P) (hQ : Antitone Q) : ((∃ x, P x) ∧ ∃ x, Q x) ↔ (∃ x, P x ∧ Q x) :=
  ⟨fun ⟨⟨x, hPx⟩, ⟨y, hQx⟩⟩ ↦ ⟨x ⊓ y, ⟨hP inf_le_left hPx, hQ inf_le_right hQx⟩⟩,
    fun ⟨x, hPx, hQx⟩ ↦ ⟨⟨x, hPx⟩, ⟨x, hQx⟩⟩⟩

namespace AntitoneOn
variable {f : α → β} {s : Set α} {x y : α}

/-- Pointwise supremum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise infimum of two antitone functions is an antitone function. -/]
/-
**AntitoneOn.sup** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : SemilatticeSup β
] {f g : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn g s → AntitoneOn (f ⊔
 g) s
参数：f ⊔ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d

--- 原说明 ---
Pointwise supremum of two antitone functions is an antitone function.
-/
protected theorem sup [Preorder α] [SemilatticeSup β] {f g : α → β} {s : Set α}
    (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (f ⊔ g) s :=
  fun _ hx _ hy h => sup_le_sup (hf hx hy h) (hg hx hy h)

/-- Pointwise maximum of two antitone functions is an antitone function. -/
@[to_dual /-- Pointwise minimum of two antitone functions is an antitone function. -/]
/-
**AntitoneOn.max** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : LinearOrder β] {
f g : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn g s → AntitoneOn (fun x 
=> max (f x) (g x)) s
参数：fun x => max (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.sup`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: SemilatticeSup β] {f g : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn g s
 → A…

--- 原说明 ---
Pointwise maximum of two antitone functions is an antitone function.
-/
protected theorem max [Preorder α] [LinearOrder β] {f g : α → β} {s : Set α} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => max (f x) (g x)) s :=
  hf.sup hg

@[to_dual]
/-
**AntitoneOn.of_map_inf** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：of_map_inf [SemilatticeInf α] [SemilatticeSup β] (h : forall x in s, foral
l y in s, f (x ⊓ y) = f x ⊔ f y) : AntitoneOn f s
参数：h : forall x in s, forall y in s, f (x ⊓ y) = f x ⊔ f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
-/
theorem of_map_inf [SemilatticeInf α] [SemilatticeSup β]
    (h : ∀ x ∈ s, ∀ y ∈ s, f (x ⊓ y) = f x ⊔ f y) : AntitoneOn f s := fun x hx y hy hxy =>
  sup_eq_left.1 <| by rw [← h _ hx _ hy, inf_eq_left.2 hxy]

variable [LinearOrder α]

@[to_dual]
/-
**AntitoneOn.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：map_sup [SemilatticeInf β] (hf : AntitoneOn f s) (hx : x in s) (hy : y in 
s) : f (x ⊔ y) = f x ⊓ f y
参数：hf : AntitoneOn f s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
-/
theorem map_sup [SemilatticeInf β] (hf : AntitoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    f (x ⊔ y) = f x ⊓ f y := by
  cases le_total x y <;> have := hf ?_ ?_ ‹_› <;>
    first
    | assumption
    | simp only [*, sup_of_le_left, sup_of_le_right, inf_of_le_left, inf_of_le_right]

end AntitoneOn

/-!
### Products of (semi-)lattices
-/


namespace Prod

variable (α β)

@[to_dual]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Max α] [Max β] : Max (α × β) :=
  ⟨fun p q => ⟨p.1 ⊔ q.1, p.2 ⊔ q.2⟩⟩

@[to_dual (attr := simp)]
/-
**Prod.mk_sup_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_sup_mk [Max α] [Max β] (a₁ a₂ : α) (b₁ b₂ : β) : (a₁, b₁) ⊔ (a₂, b₂) = 
(a₁ ⊔ a₂, b₁ ⊔ b₂)
参数：a₁ a₂ : α；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_sup_mk [Max α] [Max β] (a₁ a₂ : α) (b₁ b₂ : β) :
    (a₁, b₁) ⊔ (a₂, b₂) = (a₁ ⊔ a₂, b₁ ⊔ b₂) :=
  rfl

@[to_dual (attr := simp)]
/-
**Prod.fst_sup** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).fst = p.fst ⊔ q.fst
参数：p q : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).fst = p.fst ⊔ q.fst :=
  rfl

@[to_dual (attr := simp)]
/-
**Prod.snd_sup** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).snd = p.snd ⊔ q.snd
参数：p q : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).snd = p.snd ⊔ q.snd :=
  rfl

@[to_dual (attr := simp)]
/-
**Prod.swap_sup** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).swap = p.swap ⊔ q.swap
参数：p q : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_sup [Max α] [Max β] (p q : α × β) : (p ⊔ q).swap = p.swap ⊔ q.swap :=
  rfl

@[to_dual]
/-
**Prod.sup_def** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：sup_def [Max α] [Max β] (p q : α × β) : p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.
snd)
参数：p q : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_def [Max α] [Max β] (p q : α × β) : p ⊔ q = (p.fst ⊔ q.fst, p.snd ⊔ q.snd) :=
  rfl

@[to_dual]
/-
**Prod.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instSemilatticeSup [SemilatticeSup α] [SemilatticeSup β] : SemilatticeSup 
(α × β) where sup a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeSup [SemilatticeSup α] [SemilatticeSup β] : SemilatticeSup (α × β) where
  sup a b := ⟨a.1 ⊔ b.1, a.2 ⊔ b.2⟩
  sup_le _ _ _ h₁ h₂ := ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩
/-
**Prod.instLattice** 是 Mathlib 中的一个定义，位于命名空间 `Prod`。
形式化陈述：(α : Type u) → (β : Type v) → [Lattice α] → [Lattice β] → Lattice (α × β)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLattice [Lattice α] [Lattice β] : Lattice (α × β) where
/-
**Prod.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instDistribLattice [DistribLattice α] [DistribLattice β] : DistribLattice 
(α × β) where le_sup_inf _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribLattice [DistribLattice α] [DistribLattice β] : DistribLattice (α × β) where
  le_sup_inf _ _ _ := ⟨le_sup_inf, le_sup_inf⟩

end Prod

/-!
### Subtypes of (semi-)lattices
-/


namespace Subtype

/-- A subtype forms a `⊔`-semilattice if `⊔` preserves the property.
See note [reducible non-instances]. -/
@[to_dual (rename := Psup → Pinf)
/-- A subtype forms a `⊓`-semilattice if `⊓` preserves the property.
See note [reducible non-instances]. -/]
/-
**Subtype.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：Subtype.semilatticeSup (p : Nat -> Prop) : SemilatticeSup (Subtype p)
参数：p : Nat -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev semilatticeSup [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) :
    SemilatticeSup { x : α // P x } where
  sup x y := ⟨x.1 ⊔ y.1, Psup x.2 y.2⟩
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le _ _ _ h1 h2 := sup_le h1 h2

/-- A subtype forms a lattice if `⊔` and `⊓` preserve the property.
See note [reducible non-instances]. -/
/-
**Subtype.lattice** 是 Mathlib 中的一个定义，位于命名空间 `Subtype`。
形式化陈述：{α : Type u} →   [inst : Lattice α] →     {P : α → Prop} → (∀ ⦃x y : α⦄, P
 x → P y → P (x ⊔ y)) → (∀ ⦃x y : α⦄, P x → P y → P (x ⊓ y)) → Lattice { x // P 
x }
参数：∀ ⦃x y : α⦄, P x → P y → P (x ⊔ y)；∀ ⦃x y : α⦄, P x → P y → P (x ⊓ y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype forms a lattice if `⊔` and `⊓` preserve the property.
See note [reducible non-instances].
-/
protected abbrev lattice [Lattice α] {P : α → Prop} (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y))
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) : Lattice { x : α // P x } where
  __ := Subtype.semilatticeInf Pinf
  __ := Subtype.semilatticeSup Psup

@[to_dual (attr := simp, norm_cast) (rename := Psup → Pinf)]
/-
**Subtype.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_sup [SemilatticeSup α] {P : α -> Prop} (Psup : forall ⦃x y⦄, P x -> P 
y -> P (x ⊔ y)) (x y : Subtype P) : (haveI
参数：Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)；x y : Subtype P。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (x y : Subtype P) :
    (haveI := Subtype.semilatticeSup Psup; (x ⊔ y : Subtype P) : α) = (x ⊔ y : α) :=
  rfl

@[to_dual (attr := simp) (rename := Psup → Pinf)]
/-
**Subtype.mk_sup_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：mk_sup_mk [SemilatticeSup α] {P : α -> Prop} (Psup : forall ⦃x y⦄, P x -> 
P y -> P (x ⊔ y)) {x y : α} (hx : P x) (hy : P y) : (haveI
参数：Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)；hx : P x；hy : P y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_sup_mk [SemilatticeSup α] {P : α → Prop}
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) {x y : α} (hx : P x) (hy : P y) :
    (haveI := Subtype.semilatticeSup Psup; (⟨x, hx⟩ ⊔ ⟨y, hy⟩ : Subtype P)) =
      ⟨x ⊔ y, Psup hx hy⟩ :=
  rfl

end Subtype

section lift

/-- A type endowed with `⊔` is a `SemilatticeSup`, if it admits an injective map that
preserves `⊔` to a `SemilatticeSup`.
See note [reducible non-instances]. -/
@[to_dual /-- A type endowed with `⊓` is a `SemilatticeInf`, if it admits an injective map that
preserves `⊓` to a `SemilatticeInf`.
See note [reducible non-instances]. -/]
/-
**Function.Injective.semilatticeSup** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injectiv
e`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : Max α] →       [inst_1 : LE α]
 →         [inst_2 : LT α] →           [inst_3 : SemilatticeSup β] →            
 (f : α → β) →               Function.Injective f →                 (∀ {x y : α}
, f x ≤ f y ↔ x ≤ y) →                   (∀ {x y : α}, f x < f y ↔ x < y) → (∀ (
a b : α), f (a ⊔ b) = f a ⊔ f b) → SemilatticeSup α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Injective.semilatticeSup [Max α] [LE α] [LT α] [SemilatticeSup β]
    (f : α → β) (hf_inj : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) :
    SemilatticeSup α where
  __ := hf_inj.partialOrder f le lt
  sup a b := max a b
  le_sup_left a b := by
    rw [← le, map_sup]
    exact le_sup_left
  le_sup_right a b := by
    rw [← le, map_sup]
    exact le_sup_right
  sup_le a b c ha hb := by
    rw [← le] at *
    rw [map_sup]
    exact sup_le ha hb

/-- A type endowed with `⊔` and `⊓` is a `Lattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `Lattice`.
See note [reducible non-instances]. -/
@[to_dual self (reorder := 3 4, le (x y), lt (x y), map_inf map_sup)]
/-
**Function.Injective.lattice** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : Max α] →       [inst_1 : Min α
] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 : 
Lattice β] →               (f : α → β) →                 Function.Injective f → 
                  (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →                     (∀ {x y
 : α}, f x < f y ↔ x < y) →                       (∀ (a b : α), f (a ⊔ b) = f a 
⊔ f b) → (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) → Lattice α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeInf.inf_le_left`：∀ {α : Type u} [self : SemilatticeInf α] (a 
b : α), SemilatticeInf.inf a b ≤ a
· 使用定理 `SemilatticeInf.inf_le_right`：∀ {α : Type u} [self : SemilatticeInf α] (a
 b : α), SemilatticeInf.inf a b ≤ b
· 使用定理 `SemilatticeInf.le_inf`：∀ {α : Type u} [self : SemilatticeInf α] (a b c :
 α), a ≤ b → a ≤ c → a ≤ SemilatticeInf.inf b c

--- 原说明 ---
A type endowed with `⊔` and `⊓` is a `Lattice`, if it admits an injective map th
at
preserves `⊔` and `⊓` to a `Lattice`.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.lattice [Max α] [Min α] [LE α] [LT α] [Lattice β]
    (f : α → β) (hf_inj : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    Lattice α where
  __ := hf_inj.semilatticeSup f le lt map_sup
  __ := hf_inj.semilatticeInf f le lt map_inf

/-- A type endowed with `⊔` and `⊓` is a `DistribLattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `DistribLattice`.
See note [reducible non-instances]. -/
@[to_dual self (reorder := 3 4, le (x y), lt (x y), map_inf map_sup)]
/-
**Function.Injective.distribLattice** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injectiv
e`。
形式化陈述：{α : Type u} →   {β : Type v} →     [inst : Max α] →       [inst_1 : Min α
] →         [inst_2 : LE α] →           [inst_3 : LT α] →             [inst_4 : 
DistribLattice β] →               (f : α → β) →                 Function.Injecti
ve f →                   (∀ {x y : α}, f x ≤ f y ↔ x ≤ y) →                     
(∀ {x y : α}, f x < f y ↔ x < y) →                       (∀ (a b : α), f (a ⊔ b)
 = f a ⊔ f b) → (∀ (a b : α), f (a ⊓ b) = f a ⊓ f b) → DistribLattice α
参数：f : α → β；∀ {x y : α}, f x ≤ f y ↔ x ≤ y；∀ {x y : α}, f x < f y ↔ x < y；∀ (a 
b : α), f (a ⊔ b) = f a ⊔ f b；∀ (a b : α), f (a ⊓ b) = f a ⊓ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type endowed with `⊔` and `⊓` is a `DistribLattice`, if it admits an injective
 map that
preserves `⊔` and `⊓` to a `DistribLattice`.
See note [reducible non-instances].
-/
protected abbrev Function.Injective.distribLattice [Max α] [Min α] [LE α] [LT α] [DistribLattice β]
    (f : α → β) (hf_inj : Function.Injective f)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    DistribLattice α where
  __ := hf_inj.lattice f le lt map_sup map_inf
  le_sup_inf a b c := by
    rw [← le, map_inf, map_sup, map_sup, map_sup, map_inf]
    exact le_sup_inf

/-- A subtype forms a distributive lattice if `⊔` and `⊓` preserve the property.
See note [reducible non-instances]. -/
/-
**Subtype.distribLattice** 是 Mathlib 中的一个实例，位于命名空间 `IsLprojection`。
形式化陈述：Subtype.distribLattice [FaithfulSMul M X] : DistribLattice { P : M // IsLp
rojection X P } where le_sup_inf P Q R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))

--- 原说明 ---
A subtype forms a distributive lattice if `⊔` and `⊓` preserve the property.
See note [reducible non-instances].
-/
protected abbrev Subtype.distribLattice [DistribLattice α] {P : α → Prop}
    (Psup : ∀ ⦃s t : α⦄, P s → P t → P (s ⊔ t)) (Pinf : ∀ ⦃s t : α⦄, P s → P t → P (s ⊓ t)) :
    DistribLattice (Subtype P) :=
  letI := Subtype.lattice Psup Pinf
  Subtype.coe_injective.distribLattice _ coe_le_coe coe_lt_coe (coe_sup Psup) (coe_inf Pinf)

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `Preorder` across an `Equiv`. -/
/-
**Equiv.preorder** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [Preorder β] → Preorder α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `Preorder` across an `Equiv`.
-/
protected abbrev preorder [Preorder β] : Preorder α := by
  let le := e.le
  let lt := e.lt
  apply Function.Injective.preorder e <;> intros <;> rfl

/-- Transfer `PartialOrder` across an `Equiv`. -/
/-
**Equiv.partialOrder** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [PartialOrder β] → PartialOrder α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `PartialOrder` across an `Equiv`.
-/
protected abbrev partialOrder [PartialOrder β] : PartialOrder α := by
  let preorder := e.preorder
  apply e.injective.partialOrder <;> intros <;> rfl

/-- Transfer `LinearOrder` across an `Equiv`. -/
/-
**Equiv.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [LinearOrder β] → [DecidableEq α] → 
LinearOrder α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `LinearOrder` across an `Equiv`.
-/
protected abbrev linearOrder [LinearOrder β] [DecidableEq α] : LinearOrder α := by
  let max := e.max
  let min := e.min
  let preorder := e.preorder
  let compare := e.ord
  apply e.injective.linearOrder <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `SemilatticeSup` across an `Equiv`. -/
/-
**Equiv.semilatticeSup** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [SemilatticeSup β] → SemilatticeSup 
α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `SemilatticeSup` across an `Equiv`.
-/
protected abbrev semilatticeSup [SemilatticeSup β] : SemilatticeSup α := by
  let max := e.max
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeSup <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `SemilatticeInf` across an `Equiv`. -/
/-
**Equiv.semilatticeInf** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [SemilatticeInf β] → SemilatticeInf 
α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `SemilatticeInf` across an `Equiv`.
-/
protected abbrev semilatticeInf [SemilatticeInf β] : SemilatticeInf α := by
  let min := e.min
  let partialOrder := e.partialOrder
  apply e.injective.semilatticeInf <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `Lattice` across an `Equiv`. -/
/-
**Equiv.lattice** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [Lattice β] → Lattice α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `Lattice` across an `Equiv`.
-/
protected abbrev lattice [Lattice β] : Lattice α := by
  let semilatticeSup := e.semilatticeSup
  let semilatticeInf := e.semilatticeInf
  apply e.injective.lattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `DistribLattice` across an `Equiv`. -/
/-
**Equiv.distribLattice** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u} → {β : Type v} → α ≃ β → [DistribLattice β] → DistribLattice 
α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `DistribLattice` across an `Equiv`.
-/
protected abbrev distribLattice [DistribLattice β] : DistribLattice α := by
  let lattice := e.lattice
  apply e.injective.distribLattice <;> intros <;> first | rfl | exact e.apply_symm_apply _

end Equiv

end lift

namespace ULift

@[to_dual]
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemilatticeSup α] : SemilatticeSup (ULift.{v} α) :=
  ULift.down_injective.semilatticeSup _ .rfl .rfl down_sup
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Lattice α] : Lattice (ULift.{v} α) where
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribLattice α] : DistribLattice (ULift.{v} α) :=
  ULift.down_injective.distribLattice _ .rfl .rfl down_sup down_inf
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder α] : LinearOrder (ULift.{v} α) :=
  ULift.down_injective.linearOrder _ down_le down_lt down_inf down_sup down_compare

end ULift

--To avoid noncomputability poisoning from `Bool.completeBooleanAlgebra`
/-
**Bool.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.instPartialOrder : PartialOrder Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bool.instPartialOrder : PartialOrder Bool := inferInstance
/-
**Bool.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.instDistribLattice : DistribLattice Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bool.instDistribLattice : DistribLattice Bool := inferInstance

variable [LinearOrder α] {p : α → α → Prop}
/-
**pairwise_iff_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pairwise_iff_lt [Std.Symm p] : Pairwise p ↔ forall ⦃a b⦄, a < b -> p a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
lemma pairwise_iff_lt [Std.Symm p] : Pairwise p ↔ ∀ ⦃a b⦄, a < b → p a b := by
  simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab ↦ symm <| h _ _ hab
/-
**pairwise_iff_gt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pairwise_iff_gt [Std.Symm p] : Pairwise p ↔ forall ⦃a b⦄, b < a -> p a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
lemma pairwise_iff_gt [Std.Symm p] : Pairwise p ↔ ∀ ⦃a b⦄, b < a → p a b := by
  simpa [Pairwise, ← lt_or_lt_iff_ne, or_imp, forall_and] using fun h a b hab ↦ symm <| h _ _ hab

alias ⟨_, Pairwise.of_lt⟩ := pairwise_iff_lt
alias ⟨_, Pairwise.of_gt⟩ := pairwise_iff_gt
