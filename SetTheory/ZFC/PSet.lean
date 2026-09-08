/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Set.Lattice

/-!
# Pre-sets

A pre-set is inductively defined by its indexing type and its members, which are themselves
pre-sets.

After defining pre-sets we define extensional equality over them, also inductively. We construct a
`Setoid` instance from it, and in `Mathlib/SetTheory/ZFC/Basic.lean` we define ZFC sets as the
quotient of pre-sets by extensional equality.

## Main definitions

* `PSet`: Pre-set.
* `PSet.Type`: Underlying type of a pre-set.
* `PSet.Func`: Underlying family of pre-sets of a pre-set.
* `PSet.Equiv`: Extensional equivalence of pre-sets. Defined inductively.
* `PSet.omega`: The von Neumann ordinal `ω` as a `PSet`.
-/

@[expose] public section


universe u v

/-- The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality. -/
@[pp_with_univ, use_set_notation_for_order]
/-
**PSet** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality.
-/
inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α → PSet) : PSet

namespace PSet

/-- The underlying type of a pre-set -/
/-
**PSet.** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying type of a pre-set
-/
def «Type» : PSet → Type u
  | ⟨α, _⟩ => α

/-- The underlying pre-set family of a pre-set -/
/-
**PSet.Func** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：(x : PSet.{u_1}) → x.Type → PSet.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying pre-set family of a pre-set
-/
def Func : ∀ x : PSet, x.Type → PSet
  | ⟨_, A⟩ => A

@[simp]
/-
**PSet.mk_type** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mk_type (α A) : «Type» ⟨α, A⟩ = α
参数：α A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_type (α A) : «Type» ⟨α, A⟩ = α :=
  rfl

@[simp]
/-
**PSet.mk_func** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mk_func (α A) : Func ⟨α, A⟩ = A
参数：α A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_func (α A) : Func ⟨α, A⟩ = A :=
  rfl

@[simp]
/-
**PSet.eta** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ (x : PSet.{u_1}), PSet.mk x.Type x.Func = x
参数：x : PSet.{u_1}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eta : ∀ x : PSet, mk x.Type x.Func = x
  | ⟨_, _⟩ => rfl

/-- Two pre-sets are extensionally equivalent if every element of the first family is extensionally
equivalent to some element of the second family and vice-versa. -/
/-
**PSet.Equiv** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：PSet.{u_1} → PSet.{u_2} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two pre-sets are extensionally equivalent if every element of the first family i
s extensionally
equivalent to some element of the second family and vice-versa.
-/
def Equiv : PSet → PSet → Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b))
/-
**PSet.equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ {x : PSet.{u_1}} {y : PSet.{u_2}},   x.Equiv y ↔ (∀ (i : x.Type), ∃ j, (
x.Func i).Equiv (y.Func j)) ∧ ∀ (j : y.Type), ∃ i, (x.Func i).Equiv (y.Func j)
参数：∀ (i : x.Type), ∃ j, (x.Func i).Equiv (y.Func j)；j : y.Type；x.Func i；y.Func j
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem equiv_iff :
    ∀ {x y : PSet},
      Equiv x y ↔ (∀ i, ∃ j, Equiv (x.Func i) (y.Func j)) ∧ ∀ j, ∃ i, Equiv (x.Func i) (y.Func j)
  | ⟨_, _⟩, ⟨_, _⟩ => Iff.rfl
/-
**PSet.Equiv.exists_left** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → ∀ (i : x.Type), ∃ j, (x.F
unc i).Equiv (y.Func j)
参数：i : x.Type；x.Func i；y.Func j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PSet.equiv_iff`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}},   x.Equiv y ↔ (∀ (i
 : x.Type), ∃ j, (x.Func i).Equiv (y.Func j)) ∧ ∀ (j : y.Type), ∃ i, (x.Func i).
Equi…
-/
theorem Equiv.exists_left {x y : PSet} (h : Equiv x y) : ∀ i, ∃ j, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).1
/-
**PSet.Equiv.exists_right** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → ∀ (j : y.Type), ∃ i, (x.F
unc i).Equiv (y.Func j)
参数：j : y.Type；x.Func i；y.Func j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PSet.equiv_iff`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}},   x.Equiv y ↔ (∀ (i
 : x.Type), ∃ j, (x.Func i).Equiv (y.Func j)) ∧ ∀ (j : y.Type), ∃ i, (x.Func i).
Equi…
-/
theorem Equiv.exists_right {x y : PSet} (h : Equiv x y) : ∀ j, ∃ i, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).2

@[refl]
/-
**PSet.Equiv.refl** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ (x : PSet.{u_1}), x.Equiv x
参数：x : PSet.{u_1}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Equiv.refl : ∀ x, Equiv x x
  | ⟨_, _⟩ => ⟨fun a => ⟨a, Equiv.refl _⟩, fun a => ⟨a, Equiv.refl _⟩⟩
/-
**PSet.Equiv.rfl** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ {x : PSet.{u_1}}, x.Equiv x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.refl`：∀ (x : PSet.{u_1}), x.Equiv x
-/
protected theorem Equiv.rfl {x} : Equiv x x :=
  Equiv.refl x
/-
**PSet.Equiv.euc** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, x.Equiv y → z.Equiv 
y → x.Equiv z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Equiv.euc : ∀ {x y z}, Equiv x y → Equiv z y → Equiv x z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩, ⟨γβ, βγ⟩ =>
    ⟨ fun a =>
        let ⟨b, ab⟩ := αβ a
        let ⟨c, bc⟩ := βγ b
        ⟨c, Equiv.euc ab bc⟩,
      fun c =>
        let ⟨b, cb⟩ := γβ c
        let ⟨a, ba⟩ := βα b
        ⟨a, Equiv.euc ba cb⟩ ⟩

@[symm]
/-
**PSet.Equiv.symm** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equiv x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.euc`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, x.
Equiv y → z.Equiv y → x.Equiv z
· 使用定理 `PSet.Equiv.refl`：∀ (x : PSet.{u_1}), x.Equiv x
-/
protected theorem Equiv.symm {x y} : Equiv x y → Equiv y x :=
  (Equiv.refl y).euc
/-
**PSet.Equiv.comm** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y ↔ y.Equiv x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
-/
protected theorem Equiv.comm {x y} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩

@[trans]
/-
**PSet.Equiv.trans** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, x.Equiv y → y.Equiv 
z → x.Equiv z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.euc`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, x.
Equiv y → z.Equiv y → x.Equiv z
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
-/
protected theorem Equiv.trans {x y z} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  h1.euc h2.symm
/-
**PSet.equiv_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ (x : PSet.{u_1}) (y : PSet.{u_2}) [IsEmpty x.Type] [IsEmpty y.Type], x.E
quiv y
参数：x : PSet.{u_1}；y : PSet.{u_2}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.equiv_iff`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}},   x.Equiv y ↔ (∀ (i
 : x.Type), ∃ j, (x.Func i).Equiv (y.Func j)) ∧ ∀ (j : y.Type), ∃ i, (x.Func i).
Equi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
protected theorem equiv_of_isEmpty (x y : PSet) [IsEmpty x.Type] [IsEmpty y.Type] : Equiv x y :=
  equiv_iff.2 <| by simp
/-
**PSet.setoid** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
形式化陈述：setoid : Setoid PSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance setoid : Setoid PSet :=
  ⟨PSet.Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

/-- A pre-set is a subset of another pre-set if every element of the first family is extensionally
equivalent to some element of the second family. -/
/-
**PSet.Subset** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：PSet.{u_1} → PSet.{u_2} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pre-set is a subset of another pre-set if every element of the first family is
 extensionally
equivalent to some element of the second family.
-/
protected def Subset (x y : PSet) : Prop :=
  ∀ a, ∃ b, Equiv (x.Func a) (y.Func b)
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE PSet :=
  ⟨PSet.Subset⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder PSet where
  le_refl _ a := ⟨a, Equiv.refl _⟩
  le_trans x y z hxy hyz a := by
    obtain ⟨b, hb⟩ := hxy a
    obtain ⟨c, hc⟩ := hyz b
    exact ⟨c, hb.trans hc⟩
/-
**PSet.Equiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ (x y : PSet.{u_1}), x.Equiv y ↔ x ⊆ y ∧ y ⊆ x
参数：x y : PSet.{u_1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
-/
theorem Equiv.ext : ∀ x y : PSet, Equiv x y ↔ x ⊆ y ∧ y ⊆ x
  | ⟨_, _⟩, ⟨_, _⟩ =>
    ⟨fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩,
      fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩⟩
/-
**PSet.Subset.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Subset`。
形式化陈述：∀ {x y z : PSet.{u_1}}, x.Equiv y → (x ⊆ z ↔ y ⊆ z)
参数：x ⊆ z ↔ y ⊆ z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.trans`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, 
x.Equiv y → y.Equiv z → x.Equiv z
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
-/
theorem Subset.congr_left : ∀ {x y z : PSet}, Equiv x y → (x ⊆ z ↔ y ⊆ z)
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ =>
    ⟨fun αγ b =>
      let ⟨a, ba⟩ := βα b
      let ⟨c, ac⟩ := αγ a
      ⟨c, (Equiv.symm ba).trans ac⟩,
      fun βγ a =>
      let ⟨b, ab⟩ := αβ a
      let ⟨c, bc⟩ := βγ b
      ⟨c, Equiv.trans ab bc⟩⟩
/-
**PSet.Subset.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Subset`。
形式化陈述：∀ {x y z : PSet.{u_1}}, x.Equiv y → (z ⊆ x ↔ z ⊆ y)
参数：z ⊆ x ↔ z ⊆ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.trans`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, 
x.Equiv y → y.Equiv z → x.Equiv z
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
-/
theorem Subset.congr_right : ∀ {x y z : PSet}, Equiv x y → (z ⊆ x ↔ z ⊆ y)
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ =>
    ⟨fun γα c =>
      let ⟨a, ca⟩ := γα c
      let ⟨b, ab⟩ := αβ a
      ⟨b, ca.trans ab⟩,
      fun γβ c =>
      let ⟨b, cb⟩ := γβ c
      let ⟨a, ab⟩ := βα b
      ⟨a, cb.trans (Equiv.symm ab)⟩⟩

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
/-
**PSet.le_def** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：le_def (x y : PSet) : x <= y ↔ x subseteq y
参数：x y : PSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def (x y : PSet) : x ≤ y ↔ x ⊆ y :=
  Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
/-
**PSet.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：lt_def (x y : PSet) : x < y ↔ x ⊂ y
参数：x y : PSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_def (x y : PSet) : x < y ↔ x ⊂ y :=
  Iff.rfl

/-- `x ∈ y` as pre-sets if `x` is extensionally equivalent to a member of the family `y`. -/
/-
**PSet.Mem** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：PSet.{u} → PSet.{u} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x ∈ y` as pre-sets if `x` is extensionally equivalent to a member of the family
 `y`.
-/
protected def Mem (y x : PSet.{u}) : Prop :=
  ∃ b, Equiv x (y.Func b)
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership PSet PSet :=
  ⟨PSet.Mem⟩
/-
**PSet.mem_def** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_def {x y : PSet} : x in y ↔ exists b, Equiv x (y.Func b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_def {x y : PSet} : x ∈ y ↔ ∃ b, Equiv x (y.Func b) :=
  Iff.rfl
/-
**PSet.Mem.mk** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Mem`。
形式化陈述：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α A
参数：A : α → PSet.{u}；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.refl`：∀ (x : PSet.{u_1}), x.Equiv x
-/
theorem Mem.mk {α : Type u} (A : α → PSet) (a : α) : A a ∈ mk α A :=
  ⟨a, Equiv.refl (A a)⟩
/-
**PSet.func_mem** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：func_mem (x : PSet) (i : x.Type) : x.Func i in x
参数：x : PSet；i : x.Type。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Mem.mk`：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α 
A
-/
theorem func_mem (x : PSet) (i : x.Type) : x.Func i ∈ x := Mem.mk _ _
/-
**PSet.Mem.ext** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Mem`。
形式化陈述：∀ {x y : PSet.{u}}, (∀ (w : PSet.{u}), w ∈ x ↔ w ∈ y) → x.Equiv y
参数：∀ (w : PSet.{u}), w ∈ x ↔ w ∈ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PSet.Mem.mk`：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α 
A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
-/
theorem Mem.ext : ∀ {x y : PSet.{u}}, (∀ w : PSet.{u}, w ∈ x ↔ w ∈ y) → Equiv x y
  | ⟨_, A⟩, ⟨_, B⟩, h =>
    ⟨fun a => (h (A a)).1 (Mem.mk A a), fun b =>
      let ⟨a, ha⟩ := (h (B b)).2 (Mem.mk B b)
      ⟨a, ha.symm⟩⟩
/-
**PSet.Mem.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Mem`。
形式化陈述：∀ {x y : PSet.{u}}, x.Equiv y → ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.trans`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, 
x.Equiv y → y.Equiv z → x.Equiv z
· 使用定理 `PSet.Equiv.euc`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, x.
Equiv y → z.Equiv y → x.Equiv z
-/
theorem Mem.congr_right : ∀ {x y : PSet.{u}}, Equiv x y → ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩, _ =>
    ⟨fun ⟨a, ha⟩ =>
      let ⟨b, hb⟩ := αβ a
      ⟨b, ha.trans hb⟩,
      fun ⟨b, hb⟩ =>
      let ⟨a, ha⟩ := βα b
      ⟨a, hb.euc ha⟩⟩
/-
**PSet.equiv_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：equiv_iff_mem {x y : PSet.{u}} : Equiv x y ↔ forall {w : PSet.{u}}, w in x
 ↔ w in y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Mem.congr_right`：∀ {x y : PSet.{u}}, x.Equiv y → ∀ {w : PSet.{u}}, 
w ∈ x ↔ w ∈ y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PSet.Mem.mk`：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α 
A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
-/
theorem equiv_iff_mem {x y : PSet.{u}} : Equiv x y ↔ ∀ {w : PSet.{u}}, w ∈ x ↔ w ∈ y :=
  ⟨Mem.congr_right,
    match x, y with
    | ⟨_, A⟩, ⟨_, B⟩ => fun h =>
      ⟨fun a => h.1 (Mem.mk A a), fun b =>
        let ⟨a, h⟩ := h.2 (Mem.mk B b)
        ⟨a, h.symm⟩⟩⟩
/-
**PSet.Mem.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Mem`。
形式化陈述：∀ {x y : PSet.{u}}, x.Equiv y → ∀ {w : PSet.{u}}, x ∈ w ↔ y ∈ w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.trans`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, 
x.Equiv y → y.Equiv z → x.Equiv z
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
-/
theorem Mem.congr_left : ∀ {x y : PSet.{u}}, Equiv x y → ∀ {w : PSet.{u}}, x ∈ w ↔ y ∈ w
  | _, _, h, ⟨_, _⟩ => ⟨fun ⟨a, ha⟩ => ⟨a, h.symm.trans ha⟩, fun ⟨a, ha⟩ => ⟨a, h.trans ha⟩⟩
/-
**PSet.mem_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ {x y z : PSet.{u_1}}, x ⊆ y → z ∈ x → z ∈ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `PSet.Equiv.trans`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, 
x.Equiv y → y.Equiv z → x.Equiv z
-/
theorem mem_of_subset {x y z : PSet} : x ⊆ y → z ∈ x → z ∈ y
  | h₁, ⟨a, h₂⟩ => (h₁ a).elim fun b h₃ => ⟨b, h₂.trans h₃⟩
/-
**PSet.subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：subset_iff {x y : PSet} : x subseteq y ↔ forall ⦃z⦄, z in x -> z in y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.mem_of_subset`：∀ {x y z : PSet.{u_1}}, x ⊆ y → z ∈ x → z ∈ y
· 使用定理 `PSet.Mem.mk`：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α 
A
-/
theorem subset_iff {x y : PSet} : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y :=
  ⟨fun h _ => mem_of_subset h, fun h a => h (Mem.mk _ a)⟩
/-
**PSet.mem_wf_aux** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mem_wf_aux : ∀ {x y : PSet.{u}}, Equiv x y → Acc (· ∈ ·) y
  | ⟨α, A⟩, ⟨β, B⟩, H =>
    ⟨_, by
      rintro ⟨γ, C⟩ ⟨b, hc⟩
      obtain ⟨a, ha⟩ := H.exists_right b
      have H := ha.trans hc.symm
      rw [mk_func] at H
      exact mem_wf_aux H⟩
/-
**PSet.mem_wf** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_wf : @WellFounded PSet (· in ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.SetTheory.ZFC.PSet.0.PSet.mem_wf_aux`：∀ {x y : PSet.{u}
}, x.Equiv y → Acc (fun x1 x2 => x1 ∈ x2) y
· 使用定理 `PSet.Equiv.refl`：∀ (x : PSet.{u_1}), x.Equiv x
-/
theorem mem_wf : @WellFounded PSet (· ∈ ·) :=
  ⟨fun x => mem_wf_aux <| Equiv.refl x⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsWellFounded PSet (· ∈ ·) :=
  ⟨mem_wf⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation PSet :=
  ⟨_, mem_wf⟩
/-
**PSet.mem_asymm** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_asymm {x y : PSet} : x in y -> y ∉ x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `asymm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Asymm r], r
 a b → ¬r b a
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `PSet.instIsWellFoundedMem`：IsWellFounded PSet.{u_1} fun x1 x2 => x1 ∈ x2
-/
theorem mem_asymm {x y : PSet} : x ∈ y → y ∉ x :=
  asymm_of (· ∈ ·)
/-
**PSet.mem_irrefl** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_irrefl (x : PSet) : x ∉ x
参数：x : PSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
· 使用定理 `Function.instIrreflSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Ir
refl r], Std.Irrefl (Function.swap r)
· 使用定理 `Std.instIrreflOfAsymm`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asymm r]
, Std.Irrefl r
· 使用定理 `Function.instAsymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asy
mm r], Std.Asymm (Function.swap r)
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `PSet.instIsWellFoundedMem`：IsWellFounded PSet.{u_1} fun x1 x2 => x1 ∈ x2
-/
theorem mem_irrefl (x : PSet) : x ∉ x :=
  irrefl_of (· ∈ ·) x
/-
**PSet.not_subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：not_subset_of_mem {x y : PSet} (h : x in y) : ¬ y subseteq x
参数：h : x in y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.mem_irrefl`：mem_irrefl (x : PSet) : x ∉ x
· 使用定理 `PSet.mem_of_subset`：∀ {x y z : PSet.{u_1}}, x ⊆ y → z ∈ x → z ∈ y
-/
theorem not_subset_of_mem {x y : PSet} (h : x ∈ y) : ¬ y ⊆ x :=
  fun h' ↦ mem_irrefl _ <| mem_of_subset h' h
/-
**PSet.notMem_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：notMem_of_subset {x y : PSet} (h : x subseteq y) : y ∉ x
参数：h : x subseteq y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `PSet.not_subset_of_mem`：not_subset_of_mem {x y : PSet} (h : x in y) : ¬ 
y subseteq x
-/
theorem notMem_of_subset {x y : PSet} (h : x ⊆ y) : y ∉ x :=
  imp_not_comm.2 not_subset_of_mem h

/-- Convert a pre-set to a `Set` of pre-sets. -/
/-
**PSet.toSet** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：toSet (u : PSet.{u}) : Set PSet.{u}
参数：u : PSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a pre-set to a `Set` of pre-sets.
-/
def toSet (u : PSet.{u}) : Set PSet.{u} :=
  { x | x ∈ u }

@[simp]
/-
**PSet.mem_toSet** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_toSet (a u : PSet.{u}) : a in u.toSet ↔ a in u
参数：a u : PSet.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSet (a u : PSet.{u}) : a ∈ u.toSet ↔ a ∈ u :=
  Iff.rfl

/-- A nonempty set is one that contains some element. -/
/-
**PSet.Nonempty** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：PSet.{u_1} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonempty set is one that contains some element.
-/
protected def Nonempty (u : PSet) : Prop :=
  u.toSet.Nonempty
/-
**PSet.nonempty_def** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：nonempty_def (u : PSet) : u.Nonempty ↔ exists x, x in u
参数：u : PSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_def (u : PSet) : u.Nonempty ↔ ∃ x, x ∈ u :=
  Iff.rfl
/-
**PSet.nonempty_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：nonempty_of_mem {x u : PSet} (h : x in u) : u.Nonempty
参数：h : x in u。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_of_mem {x u : PSet} (h : x ∈ u) : u.Nonempty :=
  ⟨x, h⟩

@[simp]
/-
**PSet.nonempty_toSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：nonempty_toSet_iff {u : PSet} : u.toSet.Nonempty ↔ u.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_toSet_iff {u : PSet} : u.toSet.Nonempty ↔ u.Nonempty :=
  Iff.rfl
/-
**PSet.nonempty_type_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：nonempty_type_iff_nonempty {x : PSet} : Nonempty x.Type ↔ PSet.Nonempty x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.func_mem`：func_mem (x : PSet) (i : x.Type) : x.Func i in x
-/
theorem nonempty_type_iff_nonempty {x : PSet} : Nonempty x.Type ↔ PSet.Nonempty x :=
  ⟨fun ⟨i⟩ => ⟨_, func_mem _ i⟩, fun ⟨_, j, _⟩ => ⟨j⟩⟩
/-
**PSet.nonempty_of_nonempty_type** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：nonempty_of_nonempty_type (x : PSet) [h : Nonempty x.Type] : PSet.Nonempty
 x
参数：x : PSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PSet.nonempty_type_iff_nonempty`：nonempty_type_iff_nonempty {x : PSet} :
 Nonempty x.Type ↔ PSet.Nonempty x
-/
theorem nonempty_of_nonempty_type (x : PSet) [h : Nonempty x.Type] : PSet.Nonempty x :=
  nonempty_type_iff_nonempty.1 h

/-- Two pre-sets are equivalent iff they have the same members. -/
/-
**PSet.Equiv.eq** 是 Mathlib 中的一个定理，位于命名空间 `PSet.Equiv`。
形式化陈述：∀ {x y : PSet.{u_1}}, x.Equiv y ↔ x.toSet = y.toSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PSet.equiv_iff_mem`：equiv_iff_mem {x y : PSet.{u}} : Equiv x y ↔ forall 
{w : PSet.{u}}, w in x ↔ w in y
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b

--- 原说明 ---
Two pre-sets are equivalent iff they have the same members.
-/
theorem Equiv.eq {x y : PSet} : Equiv x y ↔ toSet x = toSet y :=
  equiv_iff_mem.trans <| .symm Set.ext_iff
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe PSet (Set PSet) :=
  ⟨toSet⟩

/-- The empty pre-set -/
/-
**PSet.empty** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：PSet.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty pre-set
-/
protected def empty : PSet :=
  ⟨_, PEmpty.elim⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EmptyCollection PSet :=
  ⟨PSet.empty⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited PSet :=
  ⟨∅⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEmpty («Type» ∅) :=
  ⟨PEmpty.elim⟩
/-
**PSet.empty_def** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：empty_def : (∅ : PSet) = ⟨_, PEmpty.elim⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem empty_def : (∅ : PSet) = ⟨_, PEmpty.elim⟩ := by
  simp [EmptyCollection.emptyCollection, PSet.empty]

@[simp]
/-
**PSet.notMem_empty** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：notMem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u})
参数：x : PSet.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsEmpty.exists_iff`：exists_iff {p : α -> Prop} : (exists a, p a) ↔ False
· 使用定理 `PSet.instIsEmptyTypeEmptyCollection`：IsEmpty ∅.Type
-/
theorem notMem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u}) :=
  IsEmpty.exists_iff.1

@[simp]
/-
**PSet.toSet_empty** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：toSet_empty : toSet ∅ = ∅
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSet_empty : toSet ∅ = ∅ := by simp [toSet]

@[simp]
/-
**PSet.empty_subset** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：empty_subset (x : PSet.{u}) : (∅ : PSet) subseteq x
参数：x : PSet.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_subset (x : PSet.{u}) : (∅ : PSet) ⊆ x := fun x => x.elim

@[simp]
/-
**PSet.not_nonempty_empty** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：not_nonempty_empty : ¬PSet.Nonempty ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PSet.toSet_empty`：toSet_empty : toSet ∅ = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_nonempty_empty : ¬PSet.Nonempty ∅ := by simp [PSet.Nonempty]
/-
**PSet.equiv_empty** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ (x : PSet.{u_1}) [IsEmpty x.Type], x.Equiv ∅
参数：x : PSet.{u_1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.equiv_of_isEmpty`：∀ (x : PSet.{u_1}) (y : PSet.{u_2}) [IsEmpty x.Ty
pe] [IsEmpty y.Type], x.Equiv y
· 使用定理 `PSet.instIsEmptyTypeEmptyCollection`：IsEmpty ∅.Type
-/
protected theorem equiv_empty (x : PSet) [IsEmpty x.Type] : Equiv x ∅ :=
  PSet.equiv_of_isEmpty x _

/-- Insert an element into a pre-set -/
/-
**PSet.insert** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：PSet.{u_1} → PSet.{u_1} → PSet.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Insert an element into a pre-set
-/
protected def insert (x y : PSet) : PSet :=
  ⟨Option y.Type, fun o => Option.casesOn o x y.Func⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Insert PSet PSet :=
  ⟨PSet.insert⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Singleton PSet PSet :=
  ⟨fun s => insert s ∅⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulSingleton PSet PSet :=
  ⟨fun _ => rfl⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x y : PSet) : Inhabited (insert x y).Type :=
  inferInstanceAs (Inhabited <| Option y.Type)

@[simp]
/-
**PSet.mem_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ {x y z : PSet.{u}}, x ∈ insert y z ↔ x.Equiv y ∨ x ∈ z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_insert_iff : ∀ {x y z : PSet.{u}}, x ∈ insert y z ↔ Equiv x y ∨ x ∈ z
  | x, y, ⟨α, A⟩ =>
    show (x ∈ PSet.mk (Option α) fun o => Option.rec y A o) ↔ Equiv x y ∨ x ∈ PSet.mk α A from
      ⟨fun m =>
        match m with
        | ⟨some a, ha⟩ => Or.inr ⟨a, ha⟩
        | ⟨none, h⟩ => Or.inl h,
        fun m =>
        match m with
        | Or.inr ⟨a, ha⟩ => ⟨some a, ha⟩
        | Or.inl h => ⟨none, h⟩⟩
/-
**PSet.mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_insert (x y : PSet) : x in insert x y
参数：x y : PSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.mem_insert_iff`：∀ {x y z : PSet.{u}}, x ∈ insert y z ↔ x.Equiv y ∨ 
x ∈ z
· 使用定理 `PSet.Equiv.rfl`：∀ {x : PSet.{u_1}}, x.Equiv x
-/
theorem mem_insert (x y : PSet) : x ∈ insert x y :=
  mem_insert_iff.2 <| Or.inl Equiv.rfl
/-
**PSet.mem_insert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_insert_of_mem {y z : PSet} (x) (h : z in y) : z in insert x y
参数：x；h : z in y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.mem_insert_iff`：∀ {x y z : PSet.{u}}, x ∈ insert y z ↔ x.Equiv y ∨ 
x ∈ z
-/
theorem mem_insert_of_mem {y z : PSet} (x) (h : z ∈ y) : z ∈ insert x y :=
  mem_insert_iff.2 <| Or.inr h

@[simp]
/-
**PSet.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_singleton {x y : PSet} : x in ({y} : PSet) ↔ Equiv x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PSet.mem_insert_iff`：∀ {x y z : PSet.{u}}, x ∈ insert y z ↔ x.Equiv y ∨ 
x ∈ z
· 使用定理 `PSet.notMem_empty`：notMem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u})
-/
theorem mem_singleton {x y : PSet} : x ∈ ({y} : PSet) ↔ Equiv x y :=
  mem_insert_iff.trans
    ⟨fun o => Or.rec id (fun n => absurd n (notMem_empty _)) o, Or.inl⟩
/-
**PSet.mem_pair** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_pair {x y z : PSet} : x in ({y, z} : PSet) ↔ Equiv x y ∨ Equiv x z
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
theorem mem_pair {x y z : PSet} : x ∈ ({y, z} : PSet) ↔ Equiv x y ∨ Equiv x z := by
  simp

/-- The n-th von Neumann ordinal -/
/-
**PSet.ofNat** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：ℕ → PSet.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The n-th von Neumann ordinal
-/
def ofNat : ℕ → PSet
  | 0 => ∅
  | n + 1 => insert (ofNat n) (ofNat n)

/-- The von Neumann ordinal ω -/
/-
**PSet.omega** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：omega : PSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The von Neumann ordinal ω
-/
def omega : PSet :=
  ⟨ULift ℕ, fun n => ofNat n.down⟩

/-- The pre-set separation operation `{x ∈ a | p x}` -/
/-
**PSet.sep** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：(PSet.{u_1} → Prop) → PSet.{u_1} → PSet.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-set separation operation `{x ∈ a | p x}`
-/
protected def sep (p : PSet → Prop) (x : PSet) : PSet :=
  ⟨{ a // p (x.Func a) }, fun y => x.Func y.1⟩
/-
**PSet.** 是 Mathlib 中的一个实例，位于命名空间 `PSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sep PSet PSet :=
  ⟨PSet.sep⟩
/-
**PSet.mem_sep** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ {p : PSet.{u_1} → Prop},   (∀ (x y : PSet.{u_1}), x.Equiv y → p x → p y)
 → ∀ {x y : PSet.{u_1}}, y ∈ PSet.sep p x ↔ y ∈ x ∧ p y
参数：∀ (x y : PSet.{u_1}), x.Equiv y → p x → p y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
-/
theorem mem_sep {p : PSet → Prop} (H : ∀ x y, Equiv x y → p x → p y) :
    ∀ {x y : PSet}, y ∈ PSet.sep p x ↔ y ∈ x ∧ p y
  | ⟨_, _⟩, _ =>
    ⟨fun ⟨⟨a, pa⟩, h⟩ => ⟨⟨a, h⟩, H _ _ h.symm pa⟩, fun ⟨⟨a, h⟩, pa⟩ =>
      ⟨⟨a, H _ _ h pa⟩, h⟩⟩

/-- The pre-set powerset operator -/
/-
**PSet.powerset** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：powerset (x : PSet) : PSet
参数：x : PSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-set powerset operator
-/
def powerset (x : PSet) : PSet :=
  ⟨Set x.Type, fun p => ⟨p, fun y => x.Func y.1⟩⟩

@[simp]
/-
**PSet.mem_powerset** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_powerset : forall {x y : PSet}, y in powerset x ↔ y subseteq x | ⟨_, A
⟩, ⟨_, B⟩ => ⟨fun ⟨_, e⟩ => (Subset.congr_left e).2 fun ⟨a, _⟩ => ⟨a, Equiv.refl
 (A a)⟩, fun βα => ⟨{ a | exists b, Equiv (B b) (A a) }, fun b => let ⟨a, ba⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.Subset.congr_left`：∀ {x y z : PSet.{u_1}}, x.Equiv y → (x ⊆ z ↔ y ⊆
 z)
· 使用定理 `PSet.Equiv.refl`：∀ (x : PSet.{u_1}), x.Equiv x
-/
theorem mem_powerset : ∀ {x y : PSet}, y ∈ powerset x ↔ y ⊆ x
  | ⟨_, A⟩, ⟨_, B⟩ =>
    ⟨fun ⟨_, e⟩ => (Subset.congr_left e).2 fun ⟨a, _⟩ => ⟨a, Equiv.refl (A a)⟩, fun βα =>
      ⟨{ a | ∃ b, Equiv (B b) (A a) }, fun b =>
        let ⟨a, ba⟩ := βα b
        ⟨⟨a, b, ba⟩, ba⟩,
        fun ⟨_, b, ba⟩ => ⟨b, ba⟩⟩⟩

/-- The pre-set union operator -/
/-
**PSet.sUnion** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：sUnion (a : PSet) : PSet
参数：a : PSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-set union operator
-/
def sUnion (a : PSet) : PSet :=
  ⟨Σ x, (a.Func x).Type, fun ⟨x, y⟩ => (a.Func x).Func y⟩

@[inherit_doc]
prefix:110 "⋃₀ " => sUnion

@[simp]
/-
**PSet.mem_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：mem_sUnion : forall {x y : PSet.{u}}, y in ⋃₀ x ↔ exists z in x, y in z | 
⟨α, A⟩, y => ⟨fun ⟨⟨a, c⟩, (e : Equiv y ((A a).Func c))⟩ => have : Func (A a) c 
in mk (A a).Type (A a).Func
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Mem.mk`：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α 
A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PSet.Mem.congr_left`：∀ {x y : PSet.{u}}, x.Equiv y → ∀ {w : PSet.{u}}, x
 ∈ w ↔ y ∈ w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PSet.eta`：∀ (x : PSet.{u_1}), PSet.mk x.Type x.Func = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PSet.Equiv.trans`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, 
x.Equiv y → y.Equiv z → x.Equiv z
-/
theorem mem_sUnion : ∀ {x y : PSet.{u}}, y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z
  | ⟨α, A⟩, y =>
    ⟨fun ⟨⟨a, c⟩, (e : Equiv y ((A a).Func c))⟩ =>
      have : Func (A a) c ∈ mk (A a).Type (A a).Func := Mem.mk (A a).Func c
      ⟨_, Mem.mk _ _, (Mem.congr_left e).2 (by rwa [eta] at this)⟩,
      fun ⟨⟨β, B⟩, ⟨a, (e : Equiv (mk β B) (A a))⟩, ⟨b, yb⟩⟩ => by
      rw [← eta (A a)] at e
      exact
        let ⟨βt, _⟩ := e
        let ⟨c, bc⟩ := βt b
        ⟨⟨a, c⟩, yb.trans bc⟩⟩

@[simp]
/-
**PSet.toSet_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：toSet_sUnion (x : PSet.{u}) : (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet)
参数：x : PSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toSet_sUnion (x : PSet.{u}) : (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet) := by
  ext
  simp

/-- The image of a function from pre-sets to pre-sets. -/
/-
**PSet.image** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：image (f : PSet.{u} -> PSet.{u}) (x : PSet.{u}) : PSet
参数：f : PSet.{u} -> PSet.{u}；x : PSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a function from pre-sets to pre-sets.
-/
def image (f : PSet.{u} → PSet.{u}) (x : PSet.{u}) : PSet :=
  ⟨x.Type, f ∘ x.Func⟩
/-
**PSet.mem_image** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：∀ {f : PSet.{u} → PSet.{u}},   (∀ (x y : PSet.{u}), x.Equiv y → (f x).Equi
v (f y)) → ∀ {x y : PSet.{u}}, y ∈ PSet.image f x ↔ ∃ z ∈ x, y.Equiv (f z)
参数：∀ (x y : PSet.{u}), x.Equiv y → (f x).Equiv (f y)；f z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Mem.mk`：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α 
A
· 使用定理 `PSet.Equiv.trans`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, 
x.Equiv y → y.Equiv z → x.Equiv z
-/
theorem mem_image {f : PSet.{u} → PSet.{u}} (H : ∀ x y, Equiv x y → Equiv (f x) (f y)) :
    ∀ {x y : PSet.{u}}, y ∈ image f x ↔ ∃ z ∈ x, Equiv y (f z)
  | ⟨_, A⟩, _ =>
    ⟨fun ⟨a, ya⟩ => ⟨A a, Mem.mk A a, ya⟩, fun ⟨_, ⟨a, za⟩, yz⟩ => ⟨a, yz.trans <| H _ _ za⟩⟩

/-- Universe lift operation -/
/-
**PSet.Lift** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：PSet.{u} → PSet.{max u v}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universe lift operation
-/
protected def Lift : PSet.{u} → PSet.{max u v}
  | ⟨α, A⟩ => ⟨ULift.{v, u} α, fun ⟨x⟩ => PSet.Lift (A x)⟩

-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/-- Embedding of one universe in another -/
/-
**PSet.embed** 是 Mathlib 中的一个定义，位于命名空间 `PSet`。
形式化陈述：embed : PSet.{max (u + 1) v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of one universe in another
-/
def embed : PSet.{max (u + 1) v} :=
  ⟨ULift.{v, u + 1} PSet, fun ⟨x⟩ => PSet.Lift.{u, max (u + 1) v} x⟩
/-
**PSet.lift_mem_embed** 是 Mathlib 中的一个定理，位于命名空间 `PSet`。
形式化陈述：lift_mem_embed : forall x : PSet.{u}, PSet.Lift.{u, max (u + 1) v} x in em
bed.{u, v}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.rfl`：∀ {x : PSet.{u_1}}, x.Equiv x
-/
theorem lift_mem_embed : ∀ x : PSet.{u}, PSet.Lift.{u, max (u + 1) v} x ∈ embed.{u, v} := fun x =>
  ⟨⟨x⟩, Equiv.rfl⟩

end PSet

