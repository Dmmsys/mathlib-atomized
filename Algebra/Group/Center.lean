/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Data.Set.Basic
public import Mathlib.Util.Delaborators

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Set.addCenter`: the center of an additive magma
* `Set.centralizer`: the centralizer of a subset of a magma
* `Set.addCentralizer`: the centralizer of a subset of an additive magma

## See also

See `Mathlib/GroupTheory/Subsemigroup/Center.lean` for the definition of the center as a
subsemigroup:
* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

See `Mathlib/GroupTheory/Subsemigroup/Centralizer.lean` for the definition of the centralizer
as a subsemigroup:
* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/

@[expose] public section

assert_not_exists HeytingAlgebra RelIso Finset MonoidWithZero Subsemigroup

variable {M : Type*} {S T : Set M}

/-- Conditions for an element to be additively central -/
/-
**IsAddCentral** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{M : Type u_1} → [Add M] → M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditions for an element to be additively central
-/
structure IsAddCentral [Add M] (z : M) : Prop where
  /-- addition commutes -/
  comm (a : M) : AddCommute z a
  /-- associative property for left addition -/
  left_assoc (b c : M) : z + (b + c) = (z + b) + c
  /-- associative property for right addition -/
  right_assoc (a b : M) : (a + b) + z = a + (b + z)

/-- Conditions for an element to be multiplicatively central -/
@[to_additive]
/-
**IsMulCentral** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{M : Type u_1} → [Mul M] → M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditions for an element to be multiplicatively central
-/
structure IsMulCentral [Mul M] (z : M) : Prop where
  /-- multiplication commutes -/
  comm (a : M) : Commute z a
  /-- associative property for left multiplication -/
  left_assoc (b c : M) : z * (b * c) = (z * b) * c
  /-- associative property for right multiplication -/
  right_assoc (a b : M) : (a * b) * z = a * (b * z)

attribute [mk_iff] IsMulCentral IsAddCentral
attribute [to_additive existing] isMulCentral_iff

namespace IsMulCentral

variable {a c : M} [Mul M]

@[to_additive]
/-
**IsMulCentral.mid_assoc** 是 Mathlib 中的一个定理，位于命名空间 `IsMulCentral`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral z → ∀ (a c : M), a *
 z * c = a * (z * c)
参数：a c : M；z * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMulCentral.right_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMul
Central z → ∀ (a b : M), a * b * z = a * (b * z)
· 使用定理 `IsMulCentral.left_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulC
entral z → ∀ (b c : M), z * (b * c) = z * b * c
-/
protected theorem mid_assoc {z : M} (h : IsMulCentral z) (a c) : a * z * c = a * (z * c) := by
  rw [h.comm, ← h.right_assoc, ← h.comm, ← h.left_assoc, h.comm]

-- cf. `Commute.left_comm`
@[to_additive]
/-
**IsMulCentral.left_comm** 是 Mathlib 中的一个定理，位于命名空间 `IsMulCentral`。
形式化陈述：∀ {M : Type u_1} {a : M} [inst : Mul M], IsMulCentral a → ∀ (b c : M), a *
 (b * c) = b * (a * c)
参数：b c : M；b * c；a * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `IsMulCentral.right_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMul
Central z → ∀ (a b : M), a * b * z = a * (b * z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem left_comm (h : IsMulCentral a) (b c) : a * (b * c) = b * (a * c) := by
  simp only [(h.comm _).eq, h.right_assoc]

-- cf. `Commute.right_comm`
@[to_additive]
/-
**IsMulCentral.right_comm** 是 Mathlib 中的一个定理，位于命名空间 `IsMulCentral`。
形式化陈述：∀ {M : Type u_1} {c : M} [inst : Mul M], IsMulCentral c → ∀ (a b : M), a *
 b * c = a * c * b
参数：a b : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMulCentral.right_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMul
Central z → ∀ (a b : M), a * b * z = a * (b * z)
· 使用定理 `IsMulCentral.mid_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCe
ntral z → ∀ (a c : M), a * z * c = a * (z * c)
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  simp only [h.right_assoc, h.mid_assoc, (h.comm _).eq]

end IsMulCentral

namespace Set

/-! ### Center -/

section Mul
variable [Mul M]

variable (M) in
/-- The center of a magma. -/
@[to_additive addCenter /-- The center of an additive magma. -/]
/-
**Set.center** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：center : Set M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a magma.
-/
def center : Set M :=
  { z | IsMulCentral z }

variable (S) in
/-- The centralizer of a subset of a magma. -/
@[to_additive addCentralizer /-- The centralizer of a subset of an additive magma. -/]
/-
**Set.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：centralizer : Set M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centralizer of a subset of a magma.
-/
def centralizer : Set M := {c | ∀ m ∈ S, m * c = c * m}

@[to_additive mem_addCenter_iff]
/-
**Set.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_center_iff {z : M} : z in center M ↔ IsMulCentral z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_center_iff {z : M} : z ∈ center M ↔ IsMulCentral z :=
  Iff.rfl

@[to_additive mem_addCentralizer]
/-
**Set.mem_centralizer_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_centralizer_iff {c : M} : c in centralizer S ↔ forall m in S, m * c = 
c * m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_centralizer_iff {c : M} : c ∈ centralizer S ↔ ∀ m ∈ S, m * c = c * m := Iff.rfl

@[to_additive (attr := simp) add_mem_addCenter]
/-
**Set.mul_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mul_mem_center {z₁ z₂ : M} (hz₁ : z₁ in Set.center M) (hz₂ : z₂ in Set.cen
ter M) : z₁ * z₂ in Set.center M
参数：hz₁ : z₁ in Set.center M；hz₂ : z₂ in Set.center M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem mul_mem_center {z₁ z₂ : M} (hz₁ : z₁ ∈ Set.center M) (hz₂ : z₂ ∈ Set.center M) :
    z₁ * z₂ ∈ Set.center M := by
  simp only [commute_iff_eq, mem_center_iff, isMulCentral_iff] at *
  grind

@[to_additive addCenter_subset_addCentralizer]
/-
**Set.center_subset_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：center_subset_centralizer (S : Set M) : Set.center M subseteq S.centralize
r
参数：S : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
-/
lemma center_subset_centralizer (S : Set M) : Set.center M ⊆ S.centralizer :=
  fun _ hx m _ ↦ (hx.comm m).symm

@[to_additive addCentralizer_union]
/-
**Set.centralizer_union** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：centralizer_union : centralizer (S union T) = centralizer S inter centrali
zer T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma centralizer_union : centralizer (S ∪ T) = centralizer S ∩ centralizer T := by
  simp [centralizer, or_imp, forall_and, ofPred_and]

@[to_additive (attr := gcongr) addCentralizer_subset]
/-
**Set.centralizer_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：centralizer_subset (h : S subseteq T) : centralizer T subseteq centralizer
 S
参数：h : S subseteq T。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma centralizer_subset (h : S ⊆ T) : centralizer T ⊆ centralizer S := fun _ ht s hs ↦ ht s (h hs)

@[to_additive subset_addCentralizer_addCentralizer]
/-
**Set.subset_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_centralizer_centralizer : S subseteq S.centralizer.centralizer
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma subset_centralizer_centralizer : S ⊆ S.centralizer.centralizer :=
  fun x hx _ hy ↦ (hy x hx).symm

@[to_additive (attr := simp) addCentralizer_addCentralizer_addCentralizer]
/-
**Set.centralizer_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：centralizer_centralizer_centralizer (S : Set M) : S.centralizer.centralize
r.centralizer = S.centralizer
参数：S : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma centralizer_centralizer_centralizer (S : Set M) :
    S.centralizer.centralizer.centralizer = S.centralizer := by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
  exact fun x hx y hy ↦ hx y <| Set.subset_centralizer_centralizer hy

@[to_additive decidableMemAddCentralizer]
/-
**Set.decidableMemCentralizer** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemCentralizer [forall a : M, Decidable <| forall b in S, b * a =
 a * b] : DecidablePred (· in centralizer S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mem_centralizer_iff`：mem_centralizer_iff {c : M} : c in centralizer 
S ↔ forall m in S, m * c = c * m
-/
instance decidableMemCentralizer [∀ a : M, Decidable <| ∀ b ∈ S, b * a = a * b] :
    DecidablePred (· ∈ centralizer S) := fun _ ↦ decidable_of_iff' _ mem_centralizer_iff

@[to_additive addCentralizer_addCentralizer_comm_of_comm]
/-
**Set.centralizer_centralizer_comm_of_comm** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：centralizer_centralizer_comm_of_comm (h_comm : forall x in S, forall y in 
S, x * y = y * x) : forall x in S.centralizer.centralizer, forall y in S.central
izer.centralizer, x * y = y * x
参数：h_comm : forall x in S, forall y in S, x * y = y * x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma centralizer_centralizer_comm_of_comm (h_comm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ S.centralizer.centralizer, ∀ y ∈ S.centralizer.centralizer, x * y = y * x :=
  fun _ h₁ _ h₂ ↦ h₂ _ fun _ h₃ ↦ h₁ _ fun _ h₄ ↦ h_comm _ h₄ _ h₃

@[to_additive (attr := simp) addCentralizer_empty]
/-
**Set.centralizer_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：centralizer_empty : (∅ : Set M).centralizer = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem centralizer_empty : (∅ : Set M).centralizer = ⊤ := by simp [centralizer]

/-- The centralizer of the product of non-empty sets is equal to the product of the centralizers. -/
@[to_additive addCentralizer_prod]
/-
**Set.centralizer_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：centralizer_prod {N : Type*} [Mul N] {S : Set M} {T : Set N} (hS : S.Nonem
pty) (hT : T.Nonempty) : (S ×ˢ T).centralizer = S.centralizer ×ˢ T.centralizer
参数：hS : S.Nonempty；hT : T.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
The centralizer of the product of non-empty sets is equal to the product of the 
centralizers.
-/
theorem centralizer_prod {N : Type*} [Mul N] {S : Set M} {T : Set N}
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (S ×ˢ T).centralizer = S.centralizer ×ˢ T.centralizer := by
  ext
  simp only [mem_prod, mem_centralizer_iff, Prod.forall, Prod.mul_def]
  grind [Set.Nonempty]

@[to_additive prod_addCentralizer_subset_addCentralizer_prod]
/-
**Set.prod_centralizer_subset_centralizer_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_centralizer_subset_centralizer_prod {N : Type*} [Mul N] (S : Set M) (
T : Set N) : S.centralizer ×ˢ T.centralizer subseteq (S ×ˢ T).centralizer
参数：S : Set M；T : Set N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_centralizer_subset_centralizer_prod {N : Type*} [Mul N] (S : Set M) (T : Set N) :
    S.centralizer ×ˢ T.centralizer ⊆ (S ×ˢ T).centralizer := by
  simp_all [subset_def, mem_centralizer_iff]

@[to_additive addCenter_prod]
/-
**Set.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 : Mul N], Set.cente
r (M × N) = Set.center M ×ˢ Set.center N
参数：M × N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
protected theorem center_prod {N : Type*} [Mul N] :
    center (M × N) = center M ×ˢ center N := by
  aesop (add simp [forall_and, commute_iff_eq, isMulCentral_iff, mem_center_iff])

open Function in
@[to_additive addCenter_pi]
/-
**Set.center_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {ι : Type u_2} {A : ι → Type u_3} [inst : (i : ι) → Mul (A i)],   Set.ce
nter ((i : ι) → A i) = Set.univ.pi fun i => Set.center (A i)
参数：i : ι；A i；(i : ι) → A i；A i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
protected theorem center_pi {ι : Type*} {A : ι → Type*} [Π i, Mul (A i)] :
    center (Π i, A i) = univ.pi fun i ↦ center (A i) := by
  classical
  ext x
  simp only [mem_pi, mem_center_iff, isMulCentral_iff, mem_univ, forall_true_left,
    commute_iff_eq, funext_iff, Pi.mul_def]
  refine ⟨fun ⟨h1, h2, h3⟩ i ↦ ?_, by grind⟩
  exact ⟨fun a ↦ by simpa using h1 (update x i a) i,
    fun b c ↦ by simpa using h2 (update x i b) (update x i c) i,
    fun a b ↦ by simpa using h3 (update x i a) (update x i b) i⟩

end Mul

section Semigroup
variable [Semigroup M] {a b : M}

@[to_additive]
/-
**Set._root_.Semigroup.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Semigroup.mem_center_iff {z : M} :
    z ∈ Set.center M ↔ ∀ g, g * z = z * g := ⟨fun a g ↦ by rw [IsMulCentral.comm a g],
  fun h ↦ ⟨fun _ ↦ (h _).symm, fun _ _ ↦ (mul_assoc z _ _).symm, fun _ _ ↦ mul_assoc _ _ z⟩ ⟩

@[to_additive (attr := simp) add_mem_addCentralizer]
/-
**Set.mul_mem_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mul_mem_centralizer (ha : a in centralizer S) (hb : b in centralizer S) : 
a * b in centralizer S
参数：ha : a in centralizer S；hb : b in centralizer S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mul_mem_centralizer (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a * b ∈ centralizer S := fun g hg ↦ by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]

@[to_additive (attr := simp) addCentralizer_eq_top_iff_subset]
/-
**Set.centralizer_eq_top_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：centralizer_eq_top_iff_subset : centralizer S = Set.univ ↔ S subseteq cent
er M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trivial`：True
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
-/
theorem centralizer_eq_top_iff_subset : centralizer S = Set.univ ↔ S ⊆ center M :=
  eq_top_iff.trans <| ⟨
    fun h _ hx ↦ Semigroup.mem_center_iff.mpr fun _ ↦ by rw [h trivial _ hx],
    fun h _ _ _ hm ↦ (h hm).comm _⟩

variable (M) in
@[to_additive (attr := simp) addCentralizer_univ]
/-
**Set.centralizer_univ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：centralizer_univ : centralizer univ = center M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
-/
lemma centralizer_univ : centralizer univ = center M :=
  Subset.antisymm (fun _ ha ↦ Semigroup.mem_center_iff.mpr fun b ↦ ha b (Set.mem_univ b))
  fun _ ha b _ ↦ (ha.comm b).symm

-- TODO Add `instance : Decidable (IsMulCentral a)` for `instance decidableMemCenter [Mul M]`
@[to_additive decidableMemAddCenter]
/-
**Set.decidableMemCenter** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemCenter [forall a : M, Decidable <| forall b : M, b * a = a * b
] : DecidablePred (· in center M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
-/
instance decidableMemCenter [∀ a : M, Decidable <| ∀ b : M, b * a = a * b] :
    DecidablePred (· ∈ center M) := fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)

end Semigroup

section CommSemigroup
variable [CommSemigroup M]

variable (M)

@[to_additive (attr := simp) addCenter_eq_univ]
/-
**Set.center_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：center_eq_univ : center M = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem center_eq_univ : center M = univ :=
  (Subset.antisymm (subset_univ _)) fun _ _ => Semigroup.mem_center_iff.mpr (fun _ => mul_comm _ _)

@[to_additive (attr := simp) addCentralizer_eq_univ]
/-
**Set.centralizer_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：centralizer_eq_univ : centralizer S = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma centralizer_eq_univ : centralizer S = univ :=
  eq_univ_of_forall fun _ _ _ ↦ mul_comm _ _

end CommSemigroup

section MulOneClass
variable [MulOneClass M]

@[to_additive (attr := simp) zero_mem_addCenter]
/-
**Set.one_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：one_mem_center : (1 : M) in Set.center M where comm _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem one_mem_center : (1 : M) ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]

@[to_additive (attr := simp) zero_mem_addCentralizer]
/-
**Set.one_mem_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：one_mem_centralizer : (1 : M) in centralizer S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma one_mem_centralizer : (1 : M) ∈ centralizer S := by simp [mem_centralizer_iff]

end MulOneClass

section Monoid
variable [Monoid M]

@[to_additive subset_addCenter_add_units]
/-
**Set.subset_center_units** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_center_units : ((↑) : Mˣ -> M) ⁻¹' center M subseteq Set.center Mˣ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
-/
theorem subset_center_units : ((↑) : Mˣ → M) ⁻¹' center M ⊆ Set.center Mˣ :=
  fun _ ha => by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← Units.val_inj, Units.val_mul, Units.val_mul, ha.comm]

@[to_additive (attr := simp)]
/-
**Set.units_inv_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：units_inv_mem_center {a : Mˣ} (ha : ↑a in Set.center M) : ↑a⁻¹ in Set.cent
er M
参数：ha : ↑a in Set.center M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `Commute.units_inv_right`：units_inv_right : Commute a u -> Commute a ↑u⁻¹
-/
theorem units_inv_mem_center {a : Mˣ} (ha : ↑a ∈ Set.center M) : ↑a⁻¹ ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.units_inv_right <| ha ·)

@[simp]
/-
**Set.invOf_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：invOf_mem_center {a : M} [Invertible a] (ha : a in Set.center M) : ⅟a in S
et.center M
参数：ha : a in Set.center M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `Commute.invOf_right`：Commute.invOf_right [Monoid α] {a b : α} [Invertibl
e b] (h : Commute a b) : Commute a (⅟b)
-/
theorem invOf_mem_center {a : M} [Invertible a] (ha : a ∈ Set.center M) : ⅟a ∈ Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

end Monoid

section DivisionMonoid
variable [DivisionMonoid M] {a b : M}

@[to_additive (attr := simp) neg_mem_addCenter]
/-
**Set.inv_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inv_mem_center (ha : a in Set.center M) : a⁻¹ in Set.center M
参数：ha : a in Set.center M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
-/
theorem inv_mem_center (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← inv_inj, mul_inv_rev, inv_inv, ha.comm, mul_inv_rev, inv_inv]

@[to_additive (attr := simp) sub_mem_addCenter]
/-
**Set.div_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：div_mem_center (ha : a in Set.center M) (hb : b in Set.center M) : a / b i
n Set.center M
参数：ha : a in Set.center M；hb : b in Set.center M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Set.mul_mem_center`：mul_mem_center {z₁ z₂ : M} (hz₁ : z₁ in Set.center M
) (hz₂ : z₂ in Set.center M) : z₁ * z₂ in Set.center M
· 使用定理 `Set.inv_mem_center`：inv_mem_center (ha : a in Set.center M) : a⁻¹ in Set
.center M
-/
theorem div_mem_center (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)

end DivisionMonoid

section Group
variable [Group M] {a b : M}

@[to_additive (attr := simp) neg_mem_addCentralizer]
/-
**Set.inv_mem_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_mem_centralizer (ha : a in centralizer S) : a⁻¹ in centralizer S
参数：ha : a in centralizer S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
-/
lemma inv_mem_centralizer (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
  fun g hg ↦ by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

@[to_additive (attr := simp) sub_mem_addCentralizer]
/-
**Set.div_mem_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：div_mem_centralizer (ha : a in centralizer S) (hb : b in centralizer S) : 
a / b in centralizer S
参数：ha : a in centralizer S；hb : b in centralizer S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `Set.mul_mem_centralizer`：mul_mem_centralizer (ha : a in centralizer S) (
hb : b in centralizer S) : a * b in centralizer S
· 使用引理 `Set.inv_mem_centralizer`：inv_mem_centralizer (ha : a in centralizer S) :
 a⁻¹ in centralizer S
-/
lemma div_mem_centralizer (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer hb)

end Group
end Set

