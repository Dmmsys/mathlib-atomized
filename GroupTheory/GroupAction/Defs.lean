/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Data.Set.BooleanAlgebra
public meta import Mathlib.Tactic.ToDual

/-!
# Definition of `orbit`, `fixedPoints` and `stabilizer`

This file defines orbits, stabilizers, and other objects defined in terms of actions.

## Main definitions

* `MulAction.orbit`
* `MulAction.fixedPoints`
* `MulAction.fixedBy`
* `MulAction.stabilizer`

-/

@[expose] public section

assert_not_exists MonoidWithZero DistribMulAction

universe u v

open scoped Pointwise

open Function

namespace MulAction

variable (M γ α : Type*) [SMul γ α] [Monoid M] [MulAction M α]

section Orbit

variable {α}

/-- The orbit of an element under an action. -/
@[to_additive /-- The orbit of an element under an action. -/]
/-
**MulAction.orbit** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：orbit (a : α)
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orbit of an element under an action.
-/
def orbit (a : α) :=
  Set.range fun m : γ => m • a

variable {γ}

@[to_additive]
/-
**MulAction.mem_orbit_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_orbit_iff {a₁ a₂ : α} : a₂ in orbit γ a₁ ↔ exists x : γ, x • a₁ = a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_orbit_iff {a₁ a₂ : α} : a₂ ∈ orbit γ a₁ ↔ ∃ x : γ, x • a₁ = a₂ :=
  Iff.rfl

@[to_additive (attr := simp)]
/-
**MulAction.mem_orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
参数：a : α；m : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_orbit (a : α) (m : γ) : m • a ∈ orbit γ a :=
  ⟨m, rfl⟩

variable {M}

@[to_additive]
/-
**MulAction.mem_orbit_of_mem_orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_orbit_of_mem_orbit {a₁ a₂ : α} (m : M) (h : a₂ in orbit M a₁) : m • a₂
 in orbit M a₁
参数：m : M；h : a₂ in orbit M a₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.mem_orbit_iff`：mem_orbit_iff {a₁ a₂ : α} : a₂ in orbit γ a₁ ↔ 
exists x : γ, x • a₁ = a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
theorem mem_orbit_of_mem_orbit {a₁ a₂ : α} (m : M) (h : a₂ ∈ orbit M a₁) :
    m • a₂ ∈ orbit M a₁ := by
  obtain ⟨x, rfl⟩ := mem_orbit_iff.mp h
  simp [smul_smul]

@[to_additive (attr := simp)]
/-
**MulAction.mem_orbit_self** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_orbit_self (a : α) : a in orbit M a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_orbit_self (a : α) : a ∈ orbit M a :=
  ⟨1, by simp⟩

@[to_additive]
/-
**MulAction.nonempty_orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：nonempty_orbit (a : α) : Set.Nonempty (orbit M a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
theorem nonempty_orbit (a : α) : Set.Nonempty (orbit M a) :=
  Set.range_nonempty _

@[to_additive]
/-
**MulAction.mapsTo_smul_orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mapsTo_smul_orbit (m : M) (a : α) : Set.MapsTo (m • ·) (orbit M a) (orbit 
M a)
参数：m : M；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_iff_subset_preimage`：mapsTo_iff_subset_preimage : MapsTo f s 
t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem mapsTo_smul_orbit (m : M) (a : α) : Set.MapsTo (m • ·) (orbit M a) (orbit M a) :=
  Set.mapsTo_iff_subset_preimage.mpr <| Set.range_subset_iff.mpr fun m' => ⟨m * m', mul_smul _ _ _⟩

@[to_additive]
/-
**MulAction.smul_orbit_subset** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：smul_orbit_subset (m : M) (a : α) : m • orbit M a subseteq orbit M a
参数：m : M；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `MulAction.mapsTo_smul_orbit`：mapsTo_smul_orbit (m : M) (a : α) : Set.Map
sTo (m • ·) (orbit M a) (orbit M a)
-/
theorem smul_orbit_subset (m : M) (a : α) : m • orbit M a ⊆ orbit M a :=
  (mapsTo_smul_orbit m a).image_subset

@[to_additive]
/-
**MulAction.orbit_smul_subset** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：orbit_smul_subset (m : M) (a : α) : orbit M (m • a) subseteq orbit M a
参数：m : M；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem orbit_smul_subset (m : M) (a : α) : orbit M (m • a) ⊆ orbit M a :=
  Set.range_subset_iff.2 fun m' => mul_smul m' m a ▸ mem_orbit _ _

@[to_additive]
/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : α} : MulAction M (orbit M a) where
  smul m := (mapsTo_smul_orbit m a).restrict _ _ _
  one_smul m := Subtype.ext (one_smul M (m : α))
  mul_smul m m' a' := Subtype.ext (mul_smul m m' (a' : α))

@[to_additive (attr := simp)]
/-
**MulAction.orbit.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.orbit`。
形式化陈述：∀ {M : Type u_1} {α : Type u_3} [inst : Monoid M] [inst_1 : MulAction M α]
 {a : α} {m : M}   {a' : ↑(MulAction.orbit M a)}, ↑(m • a') = m • ↑a'
参数：MulAction.orbit M a；m • a'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orbit.coe_smul {a : α} {m : M} {a' : orbit M a} : ↑(m • a') = m • (a' : α) :=
  rfl

@[to_additive]
/-
**MulAction.orbit_submonoid_subset** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：orbit_submonoid_subset (S : Submonoid M) (a : α) : orbit S a subseteq orbi
t M a
参数：S : Submonoid M；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
-/
lemma orbit_submonoid_subset (S : Submonoid M) (a : α) : orbit S a ⊆ orbit M a := by
  rintro b ⟨g, rfl⟩
  exact mem_orbit _ _

@[to_additive]
/-
**MulAction.mem_orbit_of_mem_orbit_submonoid** 是 Mathlib 中的一个引理，位于命名空间 `MulActio
n`。
形式化陈述：mem_orbit_of_mem_orbit_submonoid {S : Submonoid M} {a b : α} (h : a in orb
it S b) : a in orbit M b
参数：h : a in orbit S b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.orbit_submonoid_subset`：orbit_submonoid_subset (S : Submonoid 
M) (a : α) : orbit S a subseteq orbit M a
-/
lemma mem_orbit_of_mem_orbit_submonoid {S : Submonoid M} {a b : α} (h : a ∈ orbit S b) :
    a ∈ orbit M b :=
  orbit_submonoid_subset S _ h

end Orbit

section FixedPoints

/-- The set of elements fixed under the whole action. -/
@[to_additive /-- The set of elements fixed under the whole action. -/]
/-
**MulAction.fixedPoints** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：fixedPoints : Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of elements fixed under the whole action.
-/
def fixedPoints : Set α :=
  { a : α | ∀ m : M, m • a = a }

variable {M} in
/-- `fixedBy m` is the set of elements fixed by `m`. -/
@[to_additive /-- `fixedBy m` is the set of elements fixed by `m`. -/]
/-
**MulAction.fixedBy** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：fixedBy (m : M) : Set α
参数：m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fixedBy m` is the set of elements fixed by `m`.
-/
def fixedBy (m : M) : Set α :=
  { x | m • x = x }

@[to_additive]
/-
**MulAction.fixed_eq_iInter_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：fixed_eq_iInter_fixedBy : fixedPoints M α = ⋂ m : M, fixedBy α m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem fixed_eq_iInter_fixedBy : fixedPoints M α = ⋂ m : M, fixedBy α m :=
  Set.ext fun _ =>
    ⟨fun hx => Set.mem_iInter.2 fun m => hx m, fun hx m => (Set.mem_iInter.1 hx m :)⟩

variable {M α}

@[to_additive (attr := simp)]
/-
**MulAction.mem_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_fixedPoints {a : α} : a in fixedPoints M α ↔ forall m : M, m • a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fixedPoints {a : α} : a ∈ fixedPoints M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

@[to_additive (attr := simp, grind =)]
/-
**MulAction.mem_fixedBy** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_fixedBy {m : M} {a : α} : a in fixedBy α m ↔ m • a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fixedBy {m : M} {a : α} : a ∈ fixedBy α m ↔ m • a = a :=
  Iff.rfl

@[to_additive]
/-
**MulAction.mem_fixedPoints'** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_fixedPoints' {a : α} : a in fixedPoints M α ↔ forall a', a' in orbit M
 a -> a' = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.mem_orbit_iff`：mem_orbit_iff {a₁ a₂ : α} : a₂ in orbit γ a₁ ↔ 
exists x : γ, x • a₁ = a₂
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
-/
theorem mem_fixedPoints' {a : α} : a ∈ fixedPoints M α ↔ ∀ a', a' ∈ orbit M a → a' = a :=
  ⟨fun h _ h₁ =>
    let ⟨m, hm⟩ := mem_orbit_iff.1 h₁
    hm ▸ h m,
    fun h _ => h _ (mem_orbit _ _)⟩

end FixedPoints

section Stabilizers

variable {α}

/-- The stabilizer of a point `a` as a submonoid of `M`. -/
@[to_additive /-- The stabilizer of a point `a` as an additive submonoid of `M`. -/]
/-
**MulAction.stabilizerSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：stabilizerSubmonoid (a : α) : Submonoid M where carrier
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The stabilizer of a point `a` as a submonoid of `M`.
-/
def stabilizerSubmonoid (a : α) : Submonoid M where
  carrier := { m | m • a = a }
  one_mem' := one_smul _ a
  mul_mem' {m m'} (ha : m • a = a) (hb : m' • a = a) :=
    show (m * m') • a = a by rw [← smul_smul, hb, ha]

variable {M}

@[to_additive]
/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] (a : α) : DecidablePred (· ∈ stabilizerSubmonoid M a) :=
  fun _ => inferInstanceAs <| Decidable (_ = _)

@[to_additive (attr := simp)]
/-
**MulAction.mem_stabilizerSubmonoid_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_stabilizerSubmonoid_iff {a : α} {m : M} : m in stabilizerSubmonoid M a
 ↔ m • a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_stabilizerSubmonoid_iff {a : α} {m : M} : m ∈ stabilizerSubmonoid M a ↔ m • a = a :=
  Iff.rfl

end Stabilizers

end MulAction

section FixedPoints

variable (M : Type u) (α : Type v) [Monoid M]

section Monoid

variable [Monoid α] [MulDistribMulAction M α]

/-- The submonoid of elements fixed under the whole action. -/
/-
**FixedPoints.submonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FixedPoints.submonoid : Submonoid α where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulAction.smul_one`：∀ {M : Type u_9} {N : Type u_10} {inst : M
onoid M} {inst_1 : Monoid N} [self : MulDistribMulAction M N] (r : M),   r • 1 =
 1

--- 原说明 ---
The submonoid of elements fixed under the whole action.
-/
def FixedPoints.submonoid : Submonoid α where
  carrier := MulAction.fixedPoints M α
  one_mem' := smul_one
  mul_mem' ha hb _ := by rw [smul_mul', ha, hb]

@[simp]
/-
**FixedPoints.mem_submonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FixedPoints.mem_submonoid (a : α) : a in submonoid M α ↔ forall m : M, m •
 a = a
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma FixedPoints.mem_submonoid (a : α) : a ∈ submonoid M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass M (FixedPoints.submonoid M α) α where
  smul_comm g x y := by simp_rw [Submonoid.smul_def, smul_eq_mul, smul_mul', x.2 g]

end Monoid

section Group
namespace FixedPoints
variable [Group α] [MulDistribMulAction M α]

/-- The subgroup of elements fixed under the whole action. -/
/-
**FixedPoints.subgroup** 是 Mathlib 中的一个定义，位于命名空间 `FixedPoints`。
形式化陈述：subgroup : Subgroup α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of elements fixed under the whole action.
-/
def subgroup : Subgroup α where
  __ := submonoid M α
  inv_mem' ha _ := by rw [smul_inv', ha]

@[simp]
/-
**FixedPoints.mem_subgroup** 是 Mathlib 中的一个引理，位于命名空间 `FixedPoints`。
形式化陈述：mem_subgroup (a : α) : a in FixedPoints.subgroup M α ↔ forall m : M, m • a
 = a
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_subgroup (a : α) : a ∈ FixedPoints.subgroup M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl
/-
**FixedPoints.** 是 Mathlib 中的一个实例，位于命名空间 `FixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass M (FixedPoints.subgroup M α) α :=
  inferInstanceAs (SMulCommClass M (FixedPoints.submonoid M α) α)

@[simp]
/-
**FixedPoints.subgroup_toSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `FixedPoints`。
形式化陈述：subgroup_toSubmonoid : (FixedPoints.subgroup M α).toSubmonoid = submonoid 
M α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subgroup_toSubmonoid : (FixedPoints.subgroup M α).toSubmonoid = submonoid M α :=
  rfl

end FixedPoints
end Group
end FixedPoints

namespace MulAction
variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

section Orbit

@[to_additive (attr := simp)]
/-
**MulAction.orbit_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：orbit_smul (g : G) (a : α) : orbit G (g • a) = orbit G a
参数：g : G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MulAction.orbit_smul_subset`：orbit_smul_subset (m : M) (a : α) : orbit M
 (m • a) subseteq orbit M a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem orbit_smul (g : G) (a : α) : orbit G (g • a) = orbit G a :=
  (orbit_smul_subset g a).antisymm <|
    calc
      orbit G a = orbit G (g⁻¹ • g • a) := by rw [inv_smul_smul]
      _ ⊆ orbit G (g • a) := orbit_smul_subset _ _

@[to_additive]
/-
**MulAction.orbit_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：orbit_eq_iff {a b : α} : orbit G a = orbit G b ↔ a in orbit G b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.mem_orbit_self`：mem_orbit_self (a : α) : a in orbit M a
· 使用定理 `MulAction.orbit_smul`：orbit_smul (g : G) (a : α) : orbit G (g • a) = orb
it G a
-/
theorem orbit_eq_iff {a b : α} : orbit G a = orbit G b ↔ a ∈ orbit G b :=
  ⟨fun h => h ▸ mem_orbit_self _, fun ⟨_, hc⟩ => hc ▸ orbit_smul _ _⟩

@[to_additive]
/-
**MulAction.mem_orbit_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_orbit_smul (g : G) (a : α) : a in orbit G (g • a)
参数：g : G；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.orbit_smul`：orbit_smul (g : G) (a : α) : orbit G (g • a) = orb
it G a
-/
theorem mem_orbit_smul (g : G) (a : α) : a ∈ orbit G (g • a) := by
  simp only [orbit_smul, mem_orbit_self]

@[to_additive]
/-
**MulAction.smul_mem_orbit_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：smul_mem_orbit_smul (g h : G) (a : α) : g • a in orbit G (h • a)
参数：g h : G；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.orbit_smul`：orbit_smul (g : G) (a : α) : orbit G (g • a) = orb
it G a
-/
theorem smul_mem_orbit_smul (g h : G) (a : α) : g • a ∈ orbit G (h • a) := by
  simp only [orbit_smul, mem_orbit]

@[to_additive]
/-
**MulAction.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
形式化陈述：instMulAction (H : Subgroup G) : MulAction H α
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction (H : Subgroup G) : MulAction H α :=
  inferInstanceAs (MulAction H.toSubmonoid α)

@[to_additive]
/-
**MulAction.subgroup_smul_def** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：subgroup_smul_def {H : Subgroup G} (a : H) (b : α) : a • b = (a : G) • b
参数：a : H；b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subgroup_smul_def {H : Subgroup G} (a : H) (b : α) : a • b = (a : G) • b := rfl

@[to_additive]
/-
**MulAction.orbit_subgroup_subset** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：orbit_subgroup_subset (H : Subgroup G) (a : α) : orbit H a subseteq orbit 
G a
参数：H : Subgroup G；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.orbit_submonoid_subset`：orbit_submonoid_subset (S : Submonoid 
M) (a : α) : orbit S a subseteq orbit M a
-/
lemma orbit_subgroup_subset (H : Subgroup G) (a : α) : orbit H a ⊆ orbit G a :=
  orbit_submonoid_subset H.toSubmonoid a

@[to_additive]
/-
**MulAction.mem_orbit_of_mem_orbit_subgroup** 是 Mathlib 中的一个引理，位于命名空间 `MulAction
`。
形式化陈述：mem_orbit_of_mem_orbit_subgroup {H : Subgroup G} {a b : α} (h : a in orbit
 H b) : a in orbit G b
参数：h : a in orbit H b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.orbit_subgroup_subset`：orbit_subgroup_subset (H : Subgroup G) 
(a : α) : orbit H a subseteq orbit G a
-/
lemma mem_orbit_of_mem_orbit_subgroup {H : Subgroup G} {a b : α} (h : a ∈ orbit H b) :
    a ∈ orbit G b :=
  orbit_subgroup_subset H _ h

@[to_additive]
/-
**MulAction.mem_orbit_symm** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：mem_orbit_symm {a₁ a₂ : α} : a₁ in orbit G a₂ ↔ a₂ in orbit G a₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_orbit_symm {a₁ a₂ : α} : a₁ ∈ orbit G a₂ ↔ a₂ ∈ orbit G a₁ := by
  simp_rw [← orbit_eq_iff, eq_comm]

@[to_additive]
/-
**MulAction.mem_subgroup_orbit_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：mem_subgroup_orbit_iff {H : Subgroup G} {x : α} {a b : orbit G x} : a in M
ulAction.orbit H b ↔ (a : α) in MulAction.orbit H (b : α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `MulAction.orbit.coe_smul`：∀ {M : Type u_1} {α : Type u_3} [inst : Monoid
 M] [inst_1 : MulAction M α] {a : α} {m : M}   {a' : ↑(MulAction.orbit M a)}, ↑(
m • a') = m • …
· 使用引理 `MulAction.subgroup_smul_def`：subgroup_smul_def {H : Subgroup G} (a : H) 
(b : α) : a • b = (a : G) • b
-/
lemma mem_subgroup_orbit_iff {H : Subgroup G} {x : α} {a b : orbit G x} :
    a ∈ MulAction.orbit H b ↔ (a : α) ∈ MulAction.orbit H (b : α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨g, rfl⟩
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def, ← orbit.coe_smul, ← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g

variable (G α)

/-- The relation 'in the same orbit'. -/
@[to_additive /-- The relation 'in the same orbit'. -/]
/-
**MulAction.orbitRel** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：orbitRel : Setoid α where r a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation 'in the same orbit'.
-/
def orbitRel : Setoid α where
  r a b := a ∈ orbit G b
  iseqv := ⟨mem_orbit_self, mem_orbit_symm.mp, by grind [orbit_eq_iff]⟩

variable {G α}

@[to_additive]
/-
**MulAction.orbitRel_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：orbitRel_apply {a b : α} : orbitRel G α a b ↔ a in orbit G b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem orbitRel_apply {a b : α} : orbitRel G α a b ↔ a ∈ orbit G b :=
  Iff.rfl

/-- When you take a set `U` in `α`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `G`. -/
@[to_additive
/-- When you take a set `U` in `α`, push it down to the quotient, and pull back, you get the union
of the orbit of `U` under `G`. -/]
/-
**MulAction.quotient_preimage_image_eq_union_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulA
ction`。
形式化陈述：quotient_preimage_image_eq_union_mul (U : Set α) : letI
参数：U : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem quotient_preimage_image_eq_union_mul (U : Set α) :
    letI := orbitRel G α
    Quotient.mk' ⁻¹' Quotient.mk' '' U = ⋃ g : G, (g • ·) '' U := by
  let := orbitRel G α
  set f : α → Quotient (MulAction.orbitRel G α) := Quotient.mk'
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    obtain ⟨g, rfl⟩ := Quotient.exact hab
    rw [Set.mem_iUnion]
    exact ⟨g⁻¹, g • a, hb, inv_smul_smul g a⟩
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨g, u, hu₁, hu₂⟩ := hx
    rw [Set.mem_preimage, Set.mem_image]
    refine ⟨g⁻¹ • a, ?_, by simp +instances [f, orbitRel, Quotient.eq']⟩
    rw [← hu₂]
    convert! hu₁
    simp only [inv_smul_smul]

@[to_additive]
/-
**MulAction.disjoint_image_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：disjoint_image_image_iff {U V : Set α} : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem disjoint_image_image_iff {U V : Set α} :
    letI := orbitRel G α
    Disjoint (Quotient.mk' '' U) (Quotient.mk' '' V) ↔ ∀ x ∈ U, ∀ g : G, g • x ∉ V := by
  let := orbitRel G α
  set f : α → Quotient (MulAction.orbitRel G α) := Quotient.mk'
  refine
    ⟨fun h a a_in_U g g_in_V =>
      h.le_bot ⟨⟨a, a_in_U, Quotient.sound ⟨g⁻¹, ?_⟩⟩, ⟨g • a, g_in_V, rfl⟩⟩, ?_⟩
  · simp
  · intro h
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb₁, hb₂⟩ ⟨c, hc₁, hc₂⟩
    obtain ⟨g, rfl⟩ := Quotient.exact (hc₂.trans hb₂.symm)
    exact h b hb₁ g hc₁

@[to_additive]
/-
**MulAction.image_inter_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：image_inter_image_iff (U V : Set α) : letI
参数：U V : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `MulAction.disjoint_image_image_iff`：disjoint_image_image_iff {U V : Set 
α} : letI
-/
theorem image_inter_image_iff (U V : Set α) :
    letI := orbitRel G α
    Quotient.mk' '' U ∩ Quotient.mk' '' V = ∅ ↔ ∀ x ∈ U, ∀ g : G, g • x ∉ V :=
  Set.disjoint_iff_inter_eq_empty.symm.trans disjoint_image_image_iff

variable (G α)

/-- The quotient by `MulAction.orbitRel`, given a name to enable dot notation. -/
@[to_additive
    /-- The quotient by `AddAction.orbitRel`, given a name to enable dot notation. -/]
/-
**MulAction.orbitRel.Quotient** 是 Mathlib 中的一个定义，位于命名空间 `MulAction.orbitRel`。
形式化陈述：(G : Type u_1) → (α : Type u_2) → [inst : Group G] → [MulAction G α] → Typ
e u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev orbitRel.Quotient : Type _ :=
  _root_.Quotient <| orbitRel G α

variable {G α}

@[to_additive (attr := simp)]
/-
**MulAction.orbitRel.Quotient.quotient_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulAct
ion.orbitRel.Quotient`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{g : G} {a : α}, ⟦g • a⟧ = ⟦a⟧
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
lemma orbitRel.Quotient.quotient_smul_eq {g : G} {a : α} :
    ⟦g • a⟧ = (⟦a⟧ : orbitRel.Quotient G α) := Quotient.eq.mpr ⟨g, rfl⟩

/-- The orbit corresponding to an element of the quotient by `MulAction.orbitRel` -/
@[to_additive /-- The orbit corresponding to an element of the quotient by `AddAction.orbitRel` -/]
nonrec def orbitRel.Quotient.orbit (x : orbitRel.Quotient G α) : Set α :=
  Quotient.liftOn' x (orbit G) fun _ _ => MulAction.orbit_eq_iff.2

@[to_additive (attr := simp)]
/-
**MulAction.orbitRel.Quotient.orbit_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.orbi
tRel.Quotient`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
(a : α),   MulAction.orbitRel.Quotient.orbit (Quotient.mk'' a) = MulAction.orbit
 G a
参数：a : α；Quotient.mk'' a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem orbitRel.Quotient.orbit_mk (a : α) :
    orbitRel.Quotient.orbit (Quotient.mk'' a : orbitRel.Quotient G α) = MulAction.orbit G a :=
  rfl

@[to_additive]
/-
**MulAction.orbitRel.Quotient.mem_orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.orb
itRel.Quotient`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{a : α} {x : MulAction.orbitRel.Quotient G α},   a ∈ x.orbit ↔ Quotient.mk'' a =
 x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem orbitRel.Quotient.mem_orbit {a : α} {x : orbitRel.Quotient G α} :
    a ∈ x.orbit ↔ Quotient.mk'' a = x := by
  induction x using Quotient.inductionOn'
  rw [Quotient.eq'']
  rfl

/-- Note that `hφ = Quotient.out_eq'` is a useful choice here. -/
@[to_additive /-- Note that `hφ = Quotient.out_eq'` is a useful choice here. -/]
/-
**MulAction.orbitRel.Quotient.orbit_eq_orbit_out** 是 Mathlib 中的一个定理，位于命名空间 `MulA
ction.orbitRel.Quotient`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
(x : MulAction.orbitRel.Quotient G α)   {φ : MulAction.orbitRel.Quotient G α → α
}, Function.RightInverse φ Quotient.mk' → x.orbit = MulAction.orbit G (φ x)
参数：x : MulAction.orbitRel.Quotient G α；φ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Note that `hφ = Quotient.out_eq'` is a useful choice here.
-/
theorem orbitRel.Quotient.orbit_eq_orbit_out (x : orbitRel.Quotient G α)
    {φ : orbitRel.Quotient G α → α} (hφ : letI := orbitRel G α; RightInverse φ Quotient.mk') :
    orbitRel.Quotient.orbit x = MulAction.orbit G (φ x) := by
  conv_lhs => rw [← hφ x]
  rfl

@[to_additive]
/-
**MulAction.orbitRel.Quotient.orbit_injective** 是 Mathlib 中的一个定理，位于命名空间 `MulActi
on.orbitRel.Quotient`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α],
   Function.Injective MulAction.orbitRel.Quotient.orbit
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `MulAction.orbitRel.Quotient.orbit_eq_orbit_out`：∀ {G : Type u_1} {α : Ty
pe u_2} [inst : Group G] [inst_1 : MulAction G α] (x : MulAction.orbitRel.Quotie
nt G α)   {φ : MulAction.orbitRel.Qu…
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
lemma orbitRel.Quotient.orbit_injective :
    Injective (orbitRel.Quotient.orbit : orbitRel.Quotient G α → Set α) := by
  intro x y h
  simp_rw [orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq', orbit_eq_iff,
    ← orbitRel_apply] at h
  simpa [← Quotient.eq''] using h

@[to_additive (attr := simp)]
/-
**MulAction.orbitRel.Quotient.orbit_inj** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.orb
itRel.Quotient`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{x y : MulAction.orbitRel.Quotient G α},   x.orbit = y.orbit ↔ x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulAction.orbitRel.Quotient.orbit_injective`：∀ {G : Type u_1} {α : Type 
u_2} [inst : Group G] [inst_1 : MulAction G α],   Function.Injective MulAction.o
rbitRel.Quotient.orbit
-/
lemma orbitRel.Quotient.orbit_inj {x y : orbitRel.Quotient G α} : x.orbit = y.orbit ↔ x = y :=
  orbitRel.Quotient.orbit_injective.eq_iff

@[to_additive]
/-
**MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq** 是 Mathlib 中的一个定理，位于命名
空间 `MulAction.orbitRel`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{H : Subgroup G} {a b : α},   ⟦a⟧ = ⟦b⟧ → ⟦a⟧ = ⟦b⟧
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用引理 `MulAction.mem_orbit_of_mem_orbit_subgroup`：mem_orbit_of_mem_orbit_subgro
up {H : Subgroup G} {a b : α} (h : a in orbit H b) : a in orbit G b
-/
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq {H : Subgroup G} {a b : α}
    (h : (⟦a⟧ : orbitRel.Quotient H α) = ⟦b⟧) : (⟦a⟧ : orbitRel.Quotient G α) = ⟦b⟧ := by
  rw [@Quotient.eq] at h ⊢
  exact mem_orbit_of_mem_orbit_subgroup h

@[to_additive]
/-
**MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq'** 是 Mathlib 中的一个定理，位于命
名空间 `MulAction.orbitRel`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{H : Subgroup G} {a b : α},   Quotient.mk'' a = Quotient.mk'' b → Quotient.mk'' 
a = Quotient.mk'' b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq`：∀ {G : Type u_1}
 {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] {H : Subgroup G} {a b 
: α},   ⟦a⟧ = ⟦b⟧ → ⟦a⟧ = ⟦b⟧
-/
lemma orbitRel.quotient_eq_of_quotient_subgroup_eq' {H : Subgroup G} {a b : α}
    (h : (Quotient.mk'' a : orbitRel.Quotient H α) = Quotient.mk'' b) :
    (Quotient.mk'' a : orbitRel.Quotient G α) = Quotient.mk'' b :=
  orbitRel.quotient_eq_of_quotient_subgroup_eq h

@[to_additive]
nonrec lemma orbitRel.Quotient.nonempty_orbit (x : orbitRel.Quotient G α) :
    Set.Nonempty x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact nonempty_orbit _

@[to_additive]
nonrec lemma orbitRel.Quotient.mapsTo_smul_orbit (g : G) (x : orbitRel.Quotient G α) :
    Set.MapsTo (g • ·) x.orbit x.orbit := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out x Quotient.out_eq']
  exact mapsTo_smul_orbit g x.out

@[to_additive]
/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : orbitRel.Quotient G α) : MulAction G x.orbit where
  smul g := (orbitRel.Quotient.mapsTo_smul_orbit g x).restrict _ _ _
  one_smul a := Subtype.ext (one_smul G (a : α))
  mul_smul g g' a' := Subtype.ext (mul_smul g g' (a' : α))

@[to_additive (attr := simp)]
/-
**MulAction.orbitRel.Quotient.orbit.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulActio
n.orbitRel.Quotient.orbit`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{g : G} {x : MulAction.orbitRel.Quotient G α}   {a : ↑x.orbit}, ↑(g • a) = g • ↑
a
参数：g • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orbitRel.Quotient.orbit.coe_smul {g : G} {x : orbitRel.Quotient G α} {a : x.orbit} :
    ↑(g • a) = g • (a : α) :=
  rfl

@[to_additive (attr := norm_cast, simp)]
/-
**MulAction.orbitRel.Quotient.mem_subgroup_orbit_iff** 是 Mathlib 中的一个定理，位于命名空间 `
MulAction.orbitRel.Quotient`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{H : Subgroup G}   {x : MulAction.orbitRel.Quotient G α} {a b : ↑x.orbit}, ↑a ∈ 
MulAction.orbit ↥H ↑b ↔ a ∈ MulAction.orbit (↥H) b
参数：↥H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.mem_orbit`：mem_orbit (a : α) (m : γ) : m • a in orbit γ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `MulAction.orbitRel.Quotient.orbit.coe_smul`：∀ {G : Type u_1} {α : Type u
_2} [inst : Group G] [inst_1 : MulAction G α] {g : G} {x : MulAction.orbitRel.Qu
otient G α}   {a : ↑x.orbit}, ↑(…
· 使用引理 `MulAction.subgroup_smul_def`：subgroup_smul_def {H : Subgroup G} (a : H) 
(b : α) : a • b = (a : G) • b
-/
lemma orbitRel.Quotient.mem_subgroup_orbit_iff {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} : (a : α) ∈ MulAction.orbit H (b : α) ↔ a ∈ MulAction.orbit H b := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with ⟨g, h⟩
    dsimp at h
    rw [subgroup_smul_def, ← orbit.coe_smul, ← Subtype.ext_iff] at h
    subst h
    exact MulAction.mem_orbit _ g
  · rcases h with ⟨g, rfl⟩
    exact MulAction.mem_orbit _ g

@[to_additive]
/-
**MulAction.orbitRel.Quotient.subgroup_quotient_eq_iff** 是 Mathlib 中的一个定理，位于命名空间
 `MulAction.orbitRel.Quotient`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{H : Subgroup G}   {x : MulAction.orbitRel.Quotient G α} {a b : ↑x.orbit}, ⟦a⟧ =
 ⟦b⟧ ↔ ⟦↑a⟧ = ⟦↑b⟧
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MulAction.orbitRel.Quotient.mem_subgroup_orbit_iff`：∀ {G : Type u_1} {α 
: Type u_2} [inst : Group G] [inst_1 : MulAction G α] {H : Subgroup G}   {x : Mu
lAction.orbitRel.Quotient G α} {a b : ↑x…
-/
lemma orbitRel.Quotient.subgroup_quotient_eq_iff {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} : (⟦a⟧ : orbitRel.Quotient H x.orbit) = ⟦b⟧ ↔
      (⟦↑a⟧ : orbitRel.Quotient H α) = ⟦↑b⟧ := by
  simp_rw [← @Quotient.mk''_eq_mk, Quotient.eq'']
  exact orbitRel.Quotient.mem_subgroup_orbit_iff.symm

@[to_additive]
/-
**MulAction.orbitRel.Quotient.mem_subgroup_orbit_iff'** 是 Mathlib 中的一个定理，位于命名空间 
`MulAction.orbitRel.Quotient`。
形式化陈述：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [inst_1 : MulAction G α] 
{H : Subgroup G}   {x : MulAction.orbitRel.Quotient G α} {a b : ↑x.orbit} {c : α
},   ⟦a⟧ = ⟦b⟧ → (↑a ∈ MulAction.orbit (↥H) c ↔ ↑b ∈ MulAction.orbit (↥H) c)
参数：↑a ∈ MulAction.orbit (↥H) c ↔ ↑b ∈ MulAction.orbit (↥H) c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.mem_orbit_symm`：mem_orbit_symm {a₁ a₂ : α} : a₁ in orbit G a₂ 
↔ a₂ in orbit G a₁
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.orbit_eq_iff`：orbit_eq_iff {a b : α} : orbit G a = orbit G b ↔
 a in orbit G b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `MulAction.orbitRel.Quotient.mem_orbit`：∀ {G : Type u_1} {α : Type u_2} [
inst : Group G] [inst_1 : MulAction G α] {a : α} {x : MulAction.orbitRel.Quotien
t G α},   a ∈ x.orbit ↔ Quo…
· 使用定理 `Quotient.mk''_eq_mk`：∀ {α : Sort u_1} {s : Setoid α}, Quotient.mk'' = Qu
otient.mk s
· 使用定理 `MulAction.orbitRel.Quotient.mem_subgroup_orbit_iff`：∀ {G : Type u_1} {α 
: Type u_2} [inst : Group G] [inst_1 : MulAction G α] {H : Subgroup G}   {x : Mu
lAction.orbitRel.Quotient G α} {a b : ↑x…
· 使用定理 `MulAction.orbitRel_apply`：orbitRel_apply {a b : α} : orbitRel G α a b ↔ 
a in orbit G b
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
· 使用定理 `MulAction.orbitRel.Quotient.orbit_eq_orbit_out`：∀ {G : Type u_1} {α : Ty
pe u_2} [inst : Group G] [inst_1 : MulAction G α] (x : MulAction.orbitRel.Quotie
nt G α)   {φ : MulAction.orbitRel.Qu…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma orbitRel.Quotient.mem_subgroup_orbit_iff' {H : Subgroup G} {x : orbitRel.Quotient G α}
    {a b : x.orbit} {c : α} (h : (⟦a⟧ : orbitRel.Quotient H x.orbit) = ⟦b⟧) :
    (a : α) ∈ MulAction.orbit H c ↔ (b : α) ∈ MulAction.orbit H c := by
  simp_rw [mem_orbit_symm (a₂ := c)]
  convert! Iff.rfl using 2
  rw [orbit_eq_iff]
  suffices hb : ↑b ∈ orbitRel.Quotient.orbit (⟦a⟧ : orbitRel.Quotient H x.orbit) by
    rw [orbitRel.Quotient.orbit_eq_orbit_out (⟦a⟧ : orbitRel.Quotient H x.orbit) Quotient.out_eq']
       at hb
    rw [orbitRel.Quotient.mem_subgroup_orbit_iff]
    convert! hb using 1
    rw [orbit_eq_iff, ← orbitRel_apply, ← Quotient.eq'', Quotient.out_eq', @Quotient.mk''_eq_mk]
  rw [orbitRel.Quotient.mem_orbit, h, @Quotient.mk''_eq_mk]

variable (G) (α)

local notation "Ω" => orbitRel.Quotient G α

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.

This version is expressed in terms of `MulAction.orbitRel.Quotient.orbit` instead of
`MulAction.orbit`, to avoid mentioning `Quotient.out`. -/
@[to_additive
  /-- Decomposition of a type `X` as a disjoint union of its orbits under an additive group action.

  This version is expressed in terms of `AddAction.orbitRel.Quotient.orbit` instead of
  `AddAction.orbit`, to avoid mentioning `Quotient.out`. -/]
/-
**MulAction.selfEquivSigmaOrbits'** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：selfEquivSigmaOrbits' : α ≃ Σ ω : Ω, ω.orbit
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def selfEquivSigmaOrbits' : α ≃ Σ ω : Ω, ω.orbit :=
  letI := orbitRel G α
  calc
    α ≃ Σ ω : Ω, { a // Quotient.mk' a = ω } := (Equiv.sigmaFiberEquiv Quotient.mk').symm
    _ ≃ Σ ω : Ω, ω.orbit :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.subtypeEquivRight fun _ => orbitRel.Quotient.mem_orbit.symm

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive /-- Decomposition of a type `X` as a disjoint union of its orbits under an additive
group action. -/]
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MulAction.selfEquivSigmaOrbits** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：selfEquivSigmaOrbits : α ≃ Σ ω : Ω, orbit G ω.out
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
noncomputable def selfEquivSigmaOrbits : α ≃ Σ ω : Ω, orbit G ω.out :=
  (selfEquivSigmaOrbits' G α).trans <|
    Equiv.sigmaCongrRight fun _ =>
      Equiv.setCongr <| orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.
Phrased as a set union. See `MulAction.selfEquivSigmaOrbits` for the type isomorphism. -/
@[to_additive /-- Decomposition of a type `X` as a disjoint union of its orbits under an additive
group action. Phrased as a set union. See `AddAction.selfEquivSigmaOrbits` for the type
isomorphism. -/]
/-
**MulAction.univ_eq_iUnion_orbit** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：univ_eq_iUnion_orbit : Set.univ (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma univ_eq_iUnion_orbit :
    Set.univ (α := α) = ⋃ x : Ω, x.orbit := by
  ext x
  simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
  exact ⟨Quotient.mk'' x, by simp⟩

end Orbit

section Stabilizer

variable (G) in
/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive /-- The stabilizer of an element under an action, i.e. what sends the element to
itself. An additive subgroup. -/]
/-
**MulAction.stabilizer** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：stabilizer (a : α) : Subgroup G
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def stabilizer (a : α) : Subgroup G :=
  { stabilizerSubmonoid G a with
    inv_mem' := fun {m} (ha : m • a = a) => show m⁻¹ • a = a by rw [inv_smul_eq_iff, ha] }

@[to_additive]
/-
**MulAction.** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] (a : α) : DecidablePred (· ∈ stabilizer G a) :=
  fun _ => inferInstanceAs <| Decidable (_ = _)

@[to_additive (attr := simp)]
/-
**MulAction.mem_stabilizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：mem_stabilizer_iff {a : α} {g : G} : g in stabilizer G a ↔ g • a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_stabilizer_iff {a : α} {g : G} : g ∈ stabilizer G a ↔ g • a = a :=
  Iff.rfl

@[to_additive]
/-
**MulAction.le_stabilizer_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：le_stabilizer_smul_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β) :
 stabilizer G a <= stabilizer G (a • b)
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma le_stabilizer_smul_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β) :
    stabilizer G a ≤ stabilizer G (a • b) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, ← smul_assoc]; rintro a h; rw [h]

-- This lemma does not need `MulAction G α`, only `SMul G α`.
-- We use `G'` instead of `G` to locally reduce the typeclass assumptions.
@[to_additive]
/-
**MulAction.le_stabilizer_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：le_stabilizer_smul_right {G'} [Group G'] [SMul α β] [MulAction G' β] [SMul
CommClass G' α β] (a : α) (b : β) : stabilizer G' b <= stabilizer G' (a • b)
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
lemma le_stabilizer_smul_right {G'} [Group G'] [SMul α β] [MulAction G' β]
    [SMulCommClass G' α β] (a : α) (b : β) :
    stabilizer G' b ≤ stabilizer G' (a • b) := by
  simp_rw [SetLike.le_def, mem_stabilizer_iff, smul_comm]; rintro a h; rw [h]

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_smul_eq_left** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_smul_eq_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β) (
h : Injective (· • b : α -> β)) : stabilizer G (a • b) = stabilizer G a
参数：a : α；b : β；h : Injective (· • b : α -> β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用引理 `MulAction.le_stabilizer_smul_left`：le_stabilizer_smul_left [SMul α β] [I
sScalarTower G α β] (a : α) (b : β) : stabilizer G a <= stabilizer G (a • b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
lemma stabilizer_smul_eq_left [SMul α β] [IsScalarTower G α β] (a : α) (b : β)
    (h : Injective (· • b : α → β)) : stabilizer G (a • b) = stabilizer G a := by
  refine (le_stabilizer_smul_left _ _).antisymm' fun a ha ↦ ?_
  simpa only [mem_stabilizer_iff, ← smul_assoc, h.eq_iff] using ha

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_smul_eq_right** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_smul_eq_right {α} [Group α] [MulAction α β] [SMulCommClass G α 
β] (a : α) (b : β) : stabilizer G (a • b) = stabilizer G b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用引理 `MulAction.le_stabilizer_smul_right`：le_stabilizer_smul_right {G'} [Group
 G'] [SMul α β] [MulAction G' β] [SMulCommClass G' α β] (a : α) (b : β) : stabil
izer G' b <= stabilizer …
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
lemma stabilizer_smul_eq_right {α} [Group α] [MulAction α β] [SMulCommClass G α β] (a : α) (b : β) :
    stabilizer G (a • b) = stabilizer G b :=
  (le_stabilizer_smul_right _ _).antisymm' <| (le_stabilizer_smul_right a⁻¹ _).trans_eq <| by
    rw [inv_smul_smul]

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_mul_eq_left** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_mul_eq_left [Group α] [IsScalarTower G α α] (a b : α) : stabili
zer G (a * b) = stabilizer G a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.stabilizer_smul_eq_left`：stabilizer_smul_eq_left [SMul α β] [I
sScalarTower G α β] (a : α) (b : β) (h : Injective (· • b : α -> β)) : stabilize
r G (a • b) = stabilize…
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
-/
lemma stabilizer_mul_eq_left [Group α] [IsScalarTower G α α] (a b : α) :
    stabilizer G (a * b) = stabilizer G a := stabilizer_smul_eq_left a _ <| mul_left_injective _

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_mul_eq_right** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_mul_eq_right [Group α] [SMulCommClass G α α] (a b : α) : stabil
izer G (a * b) = stabilizer G b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.stabilizer_smul_eq_right`：stabilizer_smul_eq_right {α} [Group 
α] [MulAction α β] [SMulCommClass G α β] (a : α) (b : β) : stabilizer G (a • b) 
= stabilizer G b
-/
lemma stabilizer_mul_eq_right [Group α] [SMulCommClass G α α] (a b : α) :
    stabilizer G (a * b) = stabilizer G b := stabilizer_smul_eq_right a _

end Stabilizer

end MulAction

