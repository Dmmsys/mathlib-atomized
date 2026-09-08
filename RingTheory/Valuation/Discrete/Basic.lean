/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.Order.Group.Cyclic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ`, a valuation `v : A → Γ` on a ring `A` is
*discrete*, if there is an element `γ : Γˣ` that is `< 1` and generated the range of `v`,
implemented as `MonoidWithZeroHom.valueGroup v`. When `Γ := ℤₘ₀` (defined in
`Multiplicative.termℤₘ₀`), `γ = ofAdd (-1)` and the condition of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.

Note that this definition of discrete implies that the valuation is nontrivial and of rank one, as
is commonly assumed in number theory. To avoid potential confusion with other definitions of
discrete, we use the name `IsRankOneDiscrete` to refer to discrete valuations in this setting.

## Main Definitions
* `Valuation.IsRankOneDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if there is
  an element `γ : Γˣ` that is `< 1` and generates the range of `v`.
* `Valuation.IsUniformizer`: Given a `Γ`-valued valuation `v` on a ring `R`, an element `π : R` is
  a uniformizer if `v π` is a generator of the value group that is `<1`.
* `Valuation.Uniformizer`: A structure bundling an element of a ring and a proof that it is a
  uniformizer.

## Main Results
* `Valuation.IsUniformizer.of_associated`: An element associated to a uniformizer is itself a
  uniformizer.
* `Valuation.associated_of_isUniformizer`: If two elements are uniformizers, they are associated.
* `Valuation.IsUniformizer.is_generator` A generator of the maximal ideal is a uniformizer when
  the valuation is discrete.
* `Valuation.IsRankOneDiscrete.mk'`: if the `valueGroup` of the valuation `v` is cyclic and
  nontrivial, then `v` is discrete.
* `Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`: If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then there exists a uniformizer for `v`.
* `Valuation.isUniformizer_of_maximalIdeal_eq_span`: Given a discrete valuation `v` on a field `K`,
  a generator of the maximal ideal of `v.valuationSubring` is a uniformizer for `v`.
* `Valuation.valuationSubring_isDiscreteValuationRing` : If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then `v.valuationSubring` is a discrete
  valuation ring. This instance is the formalization of Chapter I, Section 1, Proposition 1 in
  [serre1968].


## TODO
* Relate discrete valuations and discrete valuation rings (contained in the project
  <https://github.com/mariainesdff/LocalClassFieldTheory>)
-/

@[expose] public section

namespace Valuation

open LinearOrderedCommGroup MonoidWithZeroHom Set Subgroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
/-
**Valuation.IsRankOneDiscrete** 是 Mathlib 中的一个归纳类型，位于命名空间 `Valuation`。
形式化陈述：{Γ : Type u_1} → [inst : LinearOrderedCommGroupWithZero Γ] → {A : Type u_2
} → [inst_1 : Ring A] → Valuation A Γ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation
.
-/
class IsRankOneDiscrete : Prop where
  exists_generator_lt_one' : ∃ (γ : Γˣ), zpowers γ = (valueGroup (.ofClass v)) ∧ γ < 1

namespace IsRankOneDiscrete

variable [IsRankOneDiscrete v]

/-
**Valuation.IsRankOneDiscrete.exists_generator_lt_one** 是 Mathlib 中的一个引理，位于命名空间 
`Valuation.IsRankOneDiscrete`。
形式化陈述：exists_generator_lt_one : exists (γ : Γˣ), zpowers γ = valueGroup (.ofClas
s v) ∧ γ < 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsRankOneDiscrete.exists_generator_lt_one'`：∀ {Γ : Type u_1} {
inst : LinearOrderedCommGroupWithZero Γ} {A : Type u_2} {inst_1 : Ring A} {v : V
aluation A Γ}   [self : v.IsRankOneDiscret…
-/
lemma exists_generator_lt_one : ∃ (γ : Γˣ), zpowers γ = valueGroup (.ofClass v) ∧ γ < 1 :=
  exists_generator_lt_one'

/-- Given a discrete valuation `v`, `Valuation.IsRankOneDiscrete.generator` is an element of `Γ`
which is a generator of the value group that is `< 1`. -/
/-
**Valuation.IsRankOneDiscrete.generator** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.IsR
ankOneDiscrete`。
形式化陈述：generator : Γˣ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.IsRankOneDiscrete.exists_generator_lt_one`：exists_generator_lt
_one : exists (γ : Γˣ), zpowers γ = valueGroup (.ofClass v) ∧ γ < 1

--- 原说明 ---
Given a discrete valuation `v`, `Valuation.IsRankOneDiscrete.generator` is an el
ement of `Γ`
which is a generator of the value group that is `< 1`.
-/
noncomputable def generator : Γˣ := (exists_generator_lt_one v).choose
/-
**Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup** 是 Mathlib 中的一个引理
，位于命名空间 `Valuation.IsRankOneDiscrete`。
形式化陈述：generator_zpowers_eq_valueGroup : zpowers (generator v) = valueGroup (.ofC
lass v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.IsRankOneDiscrete.exists_generator_lt_one`：exists_generator_lt
_one : exists (γ : Γˣ), zpowers γ = valueGroup (.ofClass v) ∧ γ < 1
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma generator_zpowers_eq_valueGroup :
    zpowers (generator v) = valueGroup (.ofClass v) :=
  (exists_generator_lt_one v).choose_spec.1
/-
**Valuation.IsRankOneDiscrete.generator_mem_valueGroup** 是 Mathlib 中的一个引理，位于命名空间
 `Valuation.IsRankOneDiscrete`。
形式化陈述：generator_mem_valueGroup : (IsRankOneDiscrete.generator v) in valueGroup (
.ofClass v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup`：generator_z
powers_eq_valueGroup : zpowers (generator v) = valueGroup (.ofClass v)
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g
-/
lemma generator_mem_valueGroup :
    (IsRankOneDiscrete.generator v) ∈ valueGroup (.ofClass v) := by
  rw [← IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  exact mem_zpowers (IsRankOneDiscrete.generator v)
/-
**Valuation.IsRankOneDiscrete.generator_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuat
ion.IsRankOneDiscrete`。
形式化陈述：generator_lt_one : generator v < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.IsRankOneDiscrete.exists_generator_lt_one`：exists_generator_lt
_one : exists (γ : Γˣ), zpowers γ = valueGroup (.ofClass v) ∧ γ < 1
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma generator_lt_one : generator v < 1 :=
  (exists_generator_lt_one v).choose_spec.2
/-
**Valuation.IsRankOneDiscrete.generator_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuat
ion.IsRankOneDiscrete`。
形式化陈述：generator_ne_one : generator v != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `Valuation.IsRankOneDiscrete.generator_lt_one`：generator_lt_one : generat
or v < 1
-/
lemma generator_ne_one : generator v ≠ 1 :=
  ne_of_lt <| generator_lt_one v
/-
**Valuation.IsRankOneDiscrete.generator_zpowers_eq_range** 是 Mathlib 中的一个引理，位于命名
空间 `Valuation.IsRankOneDiscrete`。
形式化陈述：generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRa
nkOneDiscrete w] : Units.val '' (zpowers (generator w)) = range w \ {0}
参数：K : Type*；w : Valuation K Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup`：generator_z
powers_eq_valueGroup : zpowers (generator v) = valueGroup (.ofClass v)
· 使用引理 `MonoidWithZeroHom.valueGroup_eq_range`：valueGroup_eq_range : Units.val '
' (valueGroup f) = (range f \ {0})
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    Units.val '' (zpowers (generator w)) = range w \ {0} := by
  simp [generator_zpowers_eq_valueGroup, valueGroup_eq_range]
/-
**Valuation.IsRankOneDiscrete.generator_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `Val
uation.IsRankOneDiscrete`。
形式化陈述：generator_mem_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDi
screte w] : ↑(generator w) in range w
参数：K : Type*；w : Valuation K Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.IsRankOneDiscrete.generator_zpowers_eq_range`：generator_zpower
s_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] : Uni
ts.val '' (zpowers (generator w)) = range w …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma generator_mem_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    ↑(generator w) ∈ range w := by
  apply sdiff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩
/-
**Valuation.IsRankOneDiscrete.generator_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valua
tion.IsRankOneDiscrete`。
形式化陈述：generator_ne_zero : (generator v : Γ) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma generator_ne_zero : (generator v : Γ) ≠ 0 := by simp

/-- Given a discrete valuation `v`, `Valuation.IsRankOneDiscrete.generator` is a generator of
the value group that is `< 1`, as an element of `valueGroup v`. -/
/-
**Valuation.IsRankOneDiscrete.generator'** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.Is
RankOneDiscrete`。
形式化陈述：generator' : valueGroup (.ofClass v)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.IsRankOneDiscrete.generator_mem_valueGroup`：generator_mem_valu
eGroup : (IsRankOneDiscrete.generator v) in valueGroup (.ofClass v)

--- 原说明 ---
Given a discrete valuation `v`, `Valuation.IsRankOneDiscrete.generator` is a gen
erator of
the value group that is `< 1`, as an element of `valueGroup v`.
-/
noncomputable def generator' : valueGroup (.ofClass v) := ⟨generator v, generator_mem_valueGroup v⟩

@[simp]
/-
**Valuation.IsRankOneDiscrete.embedding_generator'** 是 Mathlib 中的一个引理，位于命名空间 `Va
luation.IsRankOneDiscrete`。
形式化陈述：embedding_generator' : ValueGroup₀.embedding (f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
lemma embedding_generator' :
    ValueGroup₀.embedding (f := .ofClass v) (generator' v) = generator v := rfl
/-
**Valuation.IsRankOneDiscrete.generator'_zpowers_eq_top** 是 Mathlib 中的一个定理，位于命名空
间 `Valuation.IsRankOneDiscrete`。
形式化陈述：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {A : Type u_2} 
[inst_1 : Ring A] (v : Valuation A Γ)   [inst_2 : v.IsRankOneDiscrete], Subgroup
.zpowers (Valuation.IsRankOneDiscrete.generator' v) = ⊤
参数：v : Valuation A Γ；Valuation.IsRankOneDiscrete.generator' v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_subtype_inj`：map_subtype_inj {H : Subgroup G} {K L : Subgro
up H} : K.map H.subtype = L.map H.subtype ↔ K = L
· 使用定理 `MonoidHom.map_zpowers`：MonoidHom.map_zpowers (f : G ->* N) (x : G) : (Su
bgroup.zpowers x).map f = Subgroup.zpowers (f x)
· 使用引理 `Subgroup.subtype_apply`：subtype_apply {s : Subgroup G} (x : s) : s.subty
pe x = x
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.subtype_range`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用引理 `Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup`：generator_z
powers_eq_valueGroup : zpowers (generator v) = valueGroup (.ofClass v)
-/
lemma generator'_zpowers_eq_top : (zpowers (generator' v)) = ⊤ := by
  rw [← map_subtype_inj, MonoidHom.map_zpowers,
    subtype_apply, ← MonoidHom.range_eq_map, Subgroup.subtype_range]
  apply generator_zpowers_eq_valueGroup
/-
**Valuation.IsRankOneDiscrete.generator'_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Valua
tion.IsRankOneDiscrete`。
形式化陈述：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {A : Type u_2} 
[inst_1 : Ring A] (v : Valuation A Γ)   [inst_2 : v.IsRankOneDiscrete], Valuatio
n.IsRankOneDiscrete.generator' v < 1
参数：v : Valuation A Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.IsRankOneDiscrete.exists_generator_lt_one`：exists_generator_lt
_one : exists (γ : Γˣ), zpowers γ = valueGroup (.ofClass v) ∧ γ < 1
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma generator'_lt_one : generator' v < 1 :=
  (exists_generator_lt_one v).choose_spec.2
/-
**Valuation.IsRankOneDiscrete.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation.IsRankOneDis
crete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCyclic <| valueGroup (.ofClass v) := by
  rw [← generator_zpowers_eq_valueGroup]
  exact isCyclic_zpowers (generator v)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Valuation.IsRankOneDiscrete.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation.IsRankOneDis
crete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : v.IsNontrivial := by
  apply IsNontrivial.mk
  by_contra! h1
  have hvalueGroup : valueGroup (.ofClass v) = ⊥ := by
    simp only [valueGroup, valueMonoid, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      closure_eq_bot_iff, subset_singleton_iff, mem_preimage, mem_range, forall_exists_index,
      Units.ext_iff]
    intro y x
    specialize h1 x
    aesop
  aesop (add safe forward [generator_lt_one, generator_zpowers_eq_valueGroup])
/-
**Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator** 是 Mathlib 中的一个引
理，位于命名空间 `Valuation.IsRankOneDiscrete`。
形式化陈述：valueGroup_genLTOne_eq_generator : (valueGroup (.ofClass v)).genLTOne = ge
nerator v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `Valuation.IsRankOneDiscrete.instIsNontrivial`：∀ {Γ : Type u_1} [inst : L
inearOrderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation
 A Γ)   [v.IsRankOneDiscrete], v.I…
· 使用定理 `Valuation.IsRankOneDiscrete.instIsCyclicSubtypeUnitsMemSubgroupValueGrou
pOfClass`：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {A : Type u
_2} [inst_1 : Ring A] (v : Valuation A Γ)   [v.IsRankOneDiscrete], IsC…
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_unique`：genLTOne_unique {g : G}
 (hg : g < 1) (hH : Subgroup.zpowers g = H) : g = H.genLTOne
· 使用引理 `Valuation.IsRankOneDiscrete.generator_lt_one`：generator_lt_one : generat
or v < 1
· 使用引理 `Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup`：generator_z
powers_eq_valueGroup : zpowers (generator v) = valueGroup (.ofClass v)
-/
lemma valueGroup_genLTOne_eq_generator : (valueGroup (.ofClass v)).genLTOne = generator v :=
  ((valueGroup (.ofClass v)).genLTOne_unique (generator_lt_one v)
      (generator_zpowers_eq_valueGroup v)).symm

section WithZeroMulInt

open WithZero

variable {v : Valuation A ℤᵐ⁰} [hv : v.IsRankOneDiscrete]

/--
The generator of a discrete valuation in `ℤᵐ⁰` that contains `exp (-1)` in its range
is equal to `exp (-1)`. -/
/-
**Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range** 是 Mathlib 
中的一个定理，位于命名空间 `Valuation.IsRankOneDiscrete`。
形式化陈述：generator_eq_exp_neg_one_of_mem_range (hπ : exp (-1) in Set.range v) : hv.
generator = Units.mk0 (exp (-1 : Int) : Intᵐ⁰) (by simp)
参数：hπ : exp (-1) in Set.range v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `Valuation.IsRankOneDiscrete.instIsNontrivial`：∀ {Γ : Type u_1} [inst : L
inearOrderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation
 A Γ)   [v.IsRankOneDiscrete], v.I…
· 使用定理 `Valuation.IsRankOneDiscrete.instIsCyclicSubtypeUnitsMemSubgroupValueGrou
pOfClass`：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {A : Type u
_2} [inst_1 : Ring A] (v : Valuation A Γ)   [v.IsRankOneDiscrete], IsC…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator`：valueGroup
_genLTOne_eq_generator : (valueGroup (.ofClass v)).genLTOne = generator v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_unique`：genLTOne_unique {g : G}
 (hg : g < 1) (hH : Subgroup.zpowers g = H) : g = H.genLTOne
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `compareOfLessAndEq_eq_lt`：∀ {α : Type u} [inst : LT α] [LE α] [inst_2 : 
DecidableLT α] [inst_3 : DecidableEq α] {x y : α},   compareOfLessAndEq x y = Or
dering.lt ↔ x …
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The generator of a discrete valuation in `ℤᵐ⁰` that contains `exp (-1)` in its r
ange
is equal to `exp (-1)`.
-/
theorem generator_eq_exp_neg_one_of_mem_range (hπ : exp (-1) ∈ Set.range v) :
    hv.generator = Units.mk0 (exp (-1 : ℤ) : ℤᵐ⁰) (by simp) := by
  rw [← Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator]
  suffices Units.mk0 (exp (-1)) (by simp) = (Subgroup.genLTOne (valueGroup (.ofClass v))) by
    simp [← this]
  apply Subgroup.genLTOne_unique
  · exact compareOfLessAndEq_eq_lt.mp rfl
  · ext n
    simp_all only [Int.reduceNeg, exp_neg, Subgroup.mem_zpowers_iff, mem_valueGroup_iff_of_comm,
      ne_eq]
    refine ⟨fun ⟨k, h⟩ ↦ ?_ , fun _ ↦ ⟨-WithZero.log n, by aesop⟩⟩
    rw [← h]
    have ⟨π, hπ⟩ := hπ
    cases k with
    | ofNat n => refine ⟨1, ?_, π ^ n, ?_⟩ <;> simp [hπ]
    | negSucc n => refine ⟨π ^ (n + 1), ?_, 1, ?_⟩ <;> simp [hπ, Int.negSucc_eq, mul_assoc]

/--
The generator of a surjective discrete valuation in `ℤᵐ⁰` is equal to `exp (-1)`. -/
/-
**Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective** 是 Mathlib
 中的一个引理，位于命名空间 `Valuation.IsRankOneDiscrete`。
形式化陈述：generator_eq_exp_neg_one_of_surjective (hsurj : Function.Surjective v) : h
v.generator = Units.mk0 (exp (-1 : Int) : Intᵐ⁰) (by simp)
参数：hsurj : Function.Surjective v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range`：gener
ator_eq_exp_neg_one_of_mem_range (hπ : exp (-1) in Set.range v) : hv.generator =
 Units.mk0 (exp (-1 : Int) : Intᵐ⁰) (by simp)

--- 原说明 ---
The generator of a surjective discrete valuation in `ℤᵐ⁰` is equal to `exp (-1)`
.
-/
lemma generator_eq_exp_neg_one_of_surjective (hsurj : Function.Surjective v) :
    hv.generator = Units.mk0 (exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
  generator_eq_exp_neg_one_of_mem_range (by aesop)

@[deprecated generator_eq_exp_neg_one_of_surjective (since := "2026-04-01")]
/-
**Valuation.IsRankOneDiscrete.generator_eq_neg_exp_one_of_surjective** 是 Mathlib
 中的一个引理，位于命名空间 `Valuation.IsRankOneDiscrete`。
形式化陈述：generator_eq_neg_exp_one_of_surjective (hsurj : Function.Surjective v) : h
v.generator = Units.mk0 (exp (-1 : Int) : Intᵐ⁰) (by simp)
参数：hsurj : Function.Surjective v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用引理 `Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective`：gene
rator_eq_exp_neg_one_of_surjective (hsurj : Function.Surjective v) : hv.generato
r = Units.mk0 (exp (-1 : Int) : Intᵐ⁰) (by simp)
-/
lemma generator_eq_neg_exp_one_of_surjective (hsurj : Function.Surjective v) :
    hv.generator = Units.mk0 (exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
  generator_eq_exp_neg_one_of_surjective hsurj

end WithZeroMulInt

end IsRankOneDiscrete

section IsRankOneDiscrete

variable [hv : IsRankOneDiscrete v]

/-- An element `π : A` is a uniformizer if `v π` is a generator of the value group that is `< 1`. -/
/-
**Valuation.IsUniformizer** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：IsUniformizer (π : A) : Prop
参数：π : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `π : A` is a uniformizer if `v π` is a generator of the value group t
hat is `< 1`.
-/
def IsUniformizer (π : A) : Prop := v π = hv.generator

variable {v} {π : A}

namespace IsUniformizer

/-
**Valuation.IsUniformizer.iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsUniformizer
`。
形式化陈述：iff : v.IsUniformizer π ↔ v π = hv.generator
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
theorem iff : v.IsUniformizer π ↔ v π = hv.generator := refl _
/-
**Valuation.IsUniformizer.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsUniform
izer`。
形式化陈述：ne_zero (hπ : IsUniformizer v π) : π != 0
参数：hπ : IsUniformizer v π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsUniformizer.eq_1`：∀ {Γ : Type u_1} [inst : LinearOrderedComm
GroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation A Γ)   [hv : v.
IsRankOneDiscrete]…
-/
theorem ne_zero (hπ : IsUniformizer v π) : π ≠ 0 := by
  intro h0
  rw [h0, IsUniformizer, map_zero] at hπ
  exact (Units.ne_zero _).symm hπ

@[simp]
/-
**Valuation.IsUniformizer.val** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsUniformizer
`。
形式化陈述：val (hπ : v.IsUniformizer π) : v π = hv.generator
参数：hπ : v.IsUniformizer π。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val (hπ : v.IsUniformizer π) : v π = hv.generator := hπ
/-
**Valuation.IsUniformizer.val_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsUnif
ormizer`。
形式化陈述：val_lt_one (hπ : v.IsUniformizer π) : v π < 1
参数：hπ : v.IsUniformizer π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.IsRankOneDiscrete.generator_lt_one`：generator_lt_one : generat
or v < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma val_lt_one (hπ : v.IsUniformizer π) : v π < 1 := hπ ▸ hv.generator_lt_one
/-
**Valuation.IsUniformizer.val_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsUni
formizer`。
形式化陈述：val_ne_zero (hπ : v.IsUniformizer π) : v π != 0
参数：hπ : v.IsUniformizer π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma val_ne_zero (hπ : v.IsUniformizer π) : v π ≠ 0 := by
  by_contra h0
  simp only [IsUniformizer, h0] at hπ
  exact (Units.ne_zero _).symm hπ
/-
**Valuation.IsUniformizer.val_pos** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsUniform
izer`。
形式化陈述：val_pos (hπ : IsUniformizer v π) : 0 < v π
参数：hπ : IsUniformizer v π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.IsUniformizer.iff`：iff : v.IsUniformizer π ↔ v π = hv.generato
r
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem val_pos (hπ : IsUniformizer v π) : 0 < v π := by
  rw [IsUniformizer.iff] at hπ; simp [zero_lt_iff, ne_eq, hπ]
/-
**Valuation.IsUniformizer.zpowers_eq_valueGroup** 是 Mathlib 中的一个引理，位于命名空间 `Valua
tion.IsUniformizer`。
形式化陈述：zpowers_eq_valueGroup (hπ : v.IsUniformizer π) : valueGroup (.ofClass v) =
 zpowers (Units.mk0 (v π) hπ.val_ne_zero)
参数：hπ : v.IsUniformizer π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.IsUniformizer.val_ne_zero`：val_ne_zero (hπ : v.IsUniformizer π
) : v π != 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `Valuation.IsRankOneDiscrete.instIsNontrivial`：∀ {Γ : Type u_1} [inst : L
inearOrderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation
 A Γ)   [v.IsRankOneDiscrete], v.I…
· 使用定理 `Valuation.IsRankOneDiscrete.instIsCyclicSubtypeUnitsMemSubgroupValueGrou
pOfClass`：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {A : Type u
_2} [inst_1 : Ring A] (v : Valuation A Γ)   [v.IsRankOneDiscrete], IsC…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_zpowers_eq_top`：genLTOne_zpower
s_eq_top : Subgroup.zpowers H.genLTOne = H
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Valuation.IsUniformizer.val`：val (hπ : v.IsUniformizer π) : v π = hv.gen
erator
· 使用定理 `Units.mk0.congr_simp`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] (a a_1
 : G₀) (e_a : a = a_1) (ha : a ≠ 0), Units.mk0 a ha = Units.mk0 a_1 ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用引理 `Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator`：valueGroup
_genLTOne_eq_generator : (valueGroup (.ofClass v)).genLTOne = generator v
-/
lemma zpowers_eq_valueGroup (hπ : v.IsUniformizer π) :
    valueGroup (.ofClass v) = zpowers (Units.mk0 (v π) hπ.val_ne_zero) := by
  rw [← (valueGroup (.ofClass v)).genLTOne_zpowers_eq_top]
  congr
  simp only [val, Units.mk0_val, hπ]
  exact IsRankOneDiscrete.valueGroup_genLTOne_eq_generator v

end IsUniformizer

variable (v) in
/-- The structure `Uniformizer` bundles together the term in the ring and a proof that it is a
  uniformizer. -/
@[ext]
/-
**Valuation.Uniformizer** 是 Mathlib 中的一个归纳类型，位于命名空间 `Valuation`。
形式化陈述：{Γ : Type u_1} →   [inst : LinearOrderedCommGroupWithZero Γ] →     {A : Ty
pe u_2} → [inst_1 : Ring A] → (v : Valuation A Γ) → [hv : v.IsRankOneDiscrete] →
 Type u_2
参数：v : Valuation A Γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure `Uniformizer` bundles together the term in the ring and a proof th
at it is a
  uniformizer.
-/
structure Uniformizer where
  /-- The integer underlying a `Uniformizer` -/
  val : v.integer
  valuation_gt_one : v.IsUniformizer val

namespace Uniformizer

/-- A constructor for `Uniformizer`. -/
/-
**Valuation.Uniformizer.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.Uniformizer`。
形式化陈述：mk' {x : A} (hx : v.IsUniformizer x) : v.Uniformizer where val
参数：hx : v.IsUniformizer x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for `Uniformizer`.
-/
def mk' {x : A} (hx : v.IsUniformizer x) : v.Uniformizer where
  val := ⟨x, le_of_lt hx.val_lt_one⟩
  valuation_gt_one := hx

@[simp]
/-
**Valuation.Uniformizer.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation.Uniformizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe v.Uniformizer v.integer := ⟨fun π ↦ π.val⟩
/-
**Valuation.Uniformizer.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Uniformizer
`。
形式化陈述：ne_zero (π : Uniformizer v) : π.1.1 != 0
参数：π : Uniformizer v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsUniformizer.ne_zero`：ne_zero (hπ : IsUniformizer v π) : π !=
 0
· 使用定理 `Valuation.Uniformizer.valuation_gt_one`：∀ {Γ : Type u_1} [inst : LinearO
rderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] {v : Valuation A Γ} 
  [hv : v.IsRankOneDiscrete]…
-/
theorem ne_zero (π : Uniformizer v) : π.1.1 ≠ 0 := π.2.ne_zero

end Uniformizer

end IsRankOneDiscrete

end Ring

section CommRing

variable {R : Type*} [CommRing R] {v : Valuation R Γ} [hv : IsRankOneDiscrete v]

/-
**Valuation.IsUniformizer.not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsUnif
ormizer`。
形式化陈述：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {R : Type u_2} 
[inst_1 : CommRing R] {v : Valuation R Γ}   [hv : v.IsRankOneDiscrete] {π : ↥v.i
nteger}, v.IsUniformizer ↑π → ¬IsUnit π
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Valuation.IsUniformizer.val_lt_one`：val_lt_one (hπ : v.IsUniformizer π) 
: v π < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.Integers.one_of_isUnit`：one_of_isUnit (hv : Integers v O) {x :
 O} (hx : IsUnit x) : v (algebraMap O R x) = 1
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
theorem IsUniformizer.not_isUnit {π : v.integer} (hπ : IsUniformizer v π) : ¬ IsUnit π :=
  fun h ↦ ne_of_gt hπ.val_lt_one (Integers.one_of_isUnit (integer.integers v) h).symm

end CommRing

section Ring

variable {R : Type*} [Ring R] (v : Valuation R Γ) [IsCyclic (valueGroup (.ofClass v))]
  [Nontrivial (valueGroup (.ofClass v))]

/-
**Valuation.IsRankOneDiscrete.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsRankOne
Discrete`。
形式化陈述：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {R : Type u_2} 
[inst_1 : Ring R] (v : Valuation R Γ)   [IsCyclic ↥(MonoidWithZeroHom.ofClass v)
.valueGroup] [Nontrivial ↥(MonoidWithZeroHom.ofClass v).valueGroup],   v.IsRankO
neDiscrete
参数：v : Valuation R Γ；MonoidWithZeroHom.ofClass v；MonoidWithZeroHom.ofClass v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_zpowers_eq_top`：genLTOne_zpower
s_eq_top : Subgroup.zpowers H.genLTOne = H
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_lt_one`：genLTOne_lt_one : H.gen
LTOne < 1
-/
instance IsRankOneDiscrete.mk' : IsRankOneDiscrete v :=
  ⟨(valueGroup (.ofClass v)).genLTOne, ⟨(valueGroup (.ofClass v)).genLTOne_zpowers_eq_top,
    (valueGroup (.ofClass v)).genLTOne_lt_one⟩⟩

end Ring

section Field

open Ideal IsLocalRing Valuation.IsRankOneDiscrete

variable {K : Type*} [Field K] (v : Valuation K Γ)

/- When the valuation is defined over a field instead that simply on a (commutative) ring, we use
the notion of `valuationSubring` instead of the weaker one of `integer` to access the
corresponding API. -/
local notation "K₀" => v.valuationSubring

section IsNontrivial

variable [IsCyclic (valueGroup (.ofClass v))] [Nontrivial (valueGroup (.ofClass v))]

/-
**Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial** 是 Mathlib 中的一个定理，位于
命名空间 `Valuation`。
形式化陈述：exists_isUniformizer_of_isCyclic_of_nontrivial : exists π : K₀, IsUniformi
zer v (π : K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsRankOneDiscrete.mk'`：∀ {Γ : Type u_1} [inst : LinearOrderedC
ommGroupWithZero Γ] {R : Type u_2} [inst_1 : Ring R] (v : Valuation R Γ)   [IsCy
clic ↥(MonoidWithZero…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.valueGroup_eq_range`：valueGroup_eq_range : Units.val '
' (valueGroup f) = (range f \ {0})
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_mem`：genLTOne_mem : H.genLTOne 
in H
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `LinearOrderedCommGroup.Subgroup.genLTOne_lt_one`：genLTOne_lt_one : H.gen
LTOne < 1
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `Valuation.IsRankOneDiscrete.instIsNontrivial`：∀ {Γ : Type u_1} [inst : L
inearOrderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation
 A Γ)   [v.IsRankOneDiscrete], v.I…
· 使用定理 `Valuation.IsRankOneDiscrete.instIsCyclicSubtypeUnitsMemSubgroupValueGrou
pOfClass`：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {A : Type u
_2} [inst_1 : Ring A] (v : Valuation A Γ)   [v.IsRankOneDiscrete], IsC…
· 使用引理 `Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator`：valueGroup
_genLTOne_eq_generator : (valueGroup (.ofClass v)).genLTOne = generator v
-/
theorem exists_isUniformizer_of_isCyclic_of_nontrivial : ∃ π : K₀, IsUniformizer v (π : K) := by
  simp only [IsUniformizer.iff, Subtype.exists, mem_valuationSubring_iff, exists_prop]
  set g := (valueGroup (.ofClass v)).genLTOne with hg
  obtain ⟨⟨π, hπ⟩, hγ0⟩ : g.1 ∈ ((range (MonoidWithZeroHom.ofClass v)) \ {0}) := by
    rw [← valueGroup_eq_range, hg]
    exact mem_image_of_mem Units.val (valueGroup (.ofClass v)).genLTOne_mem
  use π
  simp only [MonoidWithZeroHom.coe_ofClass] at hπ
  rw [hπ, hg]
  exact ⟨le_of_lt (valueGroup (.ofClass v)).genLTOne_lt_one,
    by rw [valueGroup_genLTOne_eq_generator]⟩
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (Uniformizer v) :=
  ⟨⟨(exists_isUniformizer_of_isCyclic_of_nontrivial v).choose,
    (exists_isUniformizer_of_isCyclic_of_nontrivial v).choose_spec⟩⟩

end IsNontrivial

section IsRankOneDiscrete

section Uniformizer

variable {v} [hv : v.IsRankOneDiscrete]

/-- An element associated to a uniformizer is itself a uniformizer. -/
/-
**Valuation.IsUniformizer.of_associated** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsU
niformizer`。
形式化陈述：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {K : Type u_2} 
[inst_1 : Field K] {v : Valuation K Γ}   [hv : v.IsRankOneDiscrete] {π₁ π₂ : ↥v.
valuationSubring}, v.IsUniformizer ↑π₁ → Associated π₁ π₂ → v.IsUniformizer ↑π₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Valuation.Integers.isUnit_iff_valuation_eq_one`：isUnit_iff_valuation_eq_
one (hv : Integers v O) {x : O} : IsUnit x ↔ v (algebraMap O F x) = 1
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.IsUniformizer.iff`：iff : v.IsUniformizer π ↔ v π = hv.generato
r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subring.coe_mul`：coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
An element associated to a uniformizer is itself a uniformizer.
-/
theorem IsUniformizer.of_associated {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
    (H : Associated π₁ π₂) : IsUniformizer v π₂ := by
  obtain ⟨u, hu⟩ := H
  have : v (u.1 : K) = 1 := (Integers.isUnit_iff_valuation_eq_one <| integer.integers v).mp u.isUnit
  rwa [IsUniformizer.iff, ← hu, Subring.coe_mul, map_mul, this, mul_one, ← IsUniformizer.iff]

set_option backward.isDefEq.respectTransparency.types false in
/-- If two elements of `K₀` are uniformizers, then they are associated. -/
/-
**Valuation.associated_of_isUniformizer** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：associated_of_isUniformizer {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁) (h2 : I
sUniformizer v π₂) : Associated π₁ π₂
参数：h1 : IsUniformizer v π₁；h2 : IsUniformizer v π₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valuation.IsUniformizer.iff`：iff : v.IsUniformizer π ↔ v π = hv.generato
r
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valuation.mem_integer_iff`：mem_integer_iff (r : R) : r in v.integer ↔ v 
r <= 1
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用引理 `Valuation.Integers.isUnit_iff_valuation_eq_one`：isUnit_iff_valuation_eq_
one (hv : Integers v O) {x : O} : IsUnit x ↔ v (algebraMap O F x) = 1
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Valuation.IsUniformizer.ne_zero`：ne_zero (hπ : IsUniformizer v π) : π !=
 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
If two elements of `K₀` are uniformizers, then they are associated.
-/
theorem associated_of_isUniformizer {π₁ π₂ : K₀} (h1 : IsUniformizer v π₁)
    (h2 : IsUniformizer v π₂) : Associated π₁ π₂ := by
  have hval : v ((π₁ : K)⁻¹ * π₂) = 1 := by
    simp [IsUniformizer.iff.mp h1, IsUniformizer.iff.mp h2]
  set p : v.integer := ⟨(π₁.1 : K)⁻¹ * π₂.1, (v.mem_integer_iff _).mpr (le_of_eq hval)⟩ with hp
  use ((Integers.isUnit_iff_valuation_eq_one (x := p) <| integer.integers v).mpr hval).unit
  apply_fun ((↑) : K₀ → K) using Subtype.val_injective
  simp [hp, ← mul_assoc, mul_inv_cancel₀ h1.ne_zero]
/-
**Valuation.exists_pow_Uniformizer** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：exists_pow_Uniformizer {r : K₀} (hr : r != 0) (π : Uniformizer v) : exists
 n : Nat, exists u : K₀ˣ, r = (π.1 ^ n).1 * u.1
参数：hr : r != 0；π : Uniformizer v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Valuation.zero_iff`：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K
} : v x = 0 ↔ x = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subring.coe_eq_zero_iff`：coe_eq_zero_iff {x : s} : (x : R) = 0 ↔ x = 0
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `MonoidWithZeroHom.mem_valueGroup`：mem_valueGroup {b : Bˣ} (hb : b.1 in r
ange f) : b in valueGroup f
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用引理 `Valuation.IsUniformizer.val_ne_zero`：val_ne_zero (hπ : v.IsUniformizer π
) : v π != 0
· 使用定理 `Valuation.Uniformizer.valuation_gt_one`：∀ {Γ : Type u_1} [inst : LinearO
rderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] {v : Valuation A Γ} 
  [hv : v.IsRankOneDiscrete]…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
· 使用引理 `Valuation.IsUniformizer.zpowers_eq_valueGroup`：zpowers_eq_valueGroup (hπ
 : v.IsUniformizer π) : valueGroup (.ofClass v) = zpowers (Units.mk0 (v π) hπ.va
l_ne_zero)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Units.val_zpow_eq_zpow_val`：val_zpow_eq_zpow_val : forall (u : αˣ) (n : 
Int), ((u ^ n : αˣ) : α) = (u : α) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_le_one_iff_right_of_lt_one₀`：∀ {G₀ : Type u_3} [inst : GroupWithZer
o G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G
₀]   {n : ℤ}, 0 < a → …
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 66 条，此处仅展示前 30 条）
-/
theorem exists_pow_Uniformizer {r : K₀} (hr : r ≠ 0) (π : Uniformizer v) :
    ∃ n : ℕ, ∃ u : K₀ˣ, r = (π.1 ^ n).1 * u.1 := by
  have hr₀ : v r ≠ 0 := by rw [ne_eq, zero_iff, Subring.coe_eq_zero_iff]; exact hr
  set vr : Γˣ := Units.mk0 (v r) hr₀ with hvr_def
  have hvr : vr ∈ (valueGroup (.ofClass v)) := by
    apply mem_valueGroup
    rw [hvr_def, Units.val_mk0 hr₀]
    exact mem_range_self _
  rw [π.2.zpowers_eq_valueGroup, mem_zpowers_iff] at hvr
  obtain ⟨m, hm⟩ := hvr
  have hm' : v π.val ^ m = v r := by
    rw [hvr_def] at hm
    rw [← Units.val_mk0 hr₀, ← hm]
    simp [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have hm₀ : 0 ≤ m := by
    rw [← zpow_le_one_iff_right_of_lt_one₀ π.2.val_pos π.2.val_lt_one, hm']
    exact r.2
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm₀
  use n
  have hpow : v (π.1.1 ^ (-m) * r) = 1 := by
    rw [map_mul, map_zpow₀, ← hm', zpow_neg, hm', inv_mul_cancel₀ hr₀]
  set a : K₀ := ⟨π.1.1 ^ (-m) * r, by apply le_of_eq hpow⟩ with ha
  have ha₀ : (↑a : K) ≠ 0 := by
    simp only [zpow_neg, ne_eq, mul_eq_zero, inv_eq_zero, ZeroMemClass.coe_eq_zero, not_or, ha]
    refine ⟨?_, hr⟩
    rw [hn, zpow_natCast, pow_eq_zero_iff', not_and_or]
    exact Or.inl π.ne_zero
  have h_unit_a : IsUnit a :=
    Integers.isUnit_of_one (integer.integers v) (isUnit_iff_ne_zero.mpr ha₀) hpow
  use h_unit_a.unit
  rw [IsUnit.unit_spec, Subring.coe_pow, ha, ← mul_assoc, zpow_neg, hn, zpow_natCast,
    mul_inv_cancel₀ (pow_ne_zero _ π.ne_zero), one_mul]

set_option backward.isDefEq.respectTransparency false in
/-
**Valuation.Uniformizer.is_generator** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Unifor
mizer`。
形式化陈述：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {K : Type u_2} 
[inst_1 : Field K] {v : Valuation K Γ}   [hv : v.IsRankOneDiscrete] (π : v.Unifo
rmizer), IsLocalRing.maximalIdeal ↥v.valuationSubring = Ideal.span {π.val}
参数：π : v.Uniformizer。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Valuation.IsUniformizer.not_isUnit`：∀ {Γ : Type u_1} [inst : LinearOrder
edCommGroupWithZero Γ] {R : Type u_2} [inst_1 : CommRing R] {v : Valuation R Γ} 
  [hv : v.IsRankOneDiscr…
· 使用定理 `Valuation.Uniformizer.valuation_gt_one`：∀ {Γ : Type u_1} [inst : LinearO
rderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] {v : Valuation A Γ} 
  [hv : v.IsRankOneDiscrete]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_singleton_eq_top`：span_singleton_eq_top {x} : span ({x} : Set
 α) = ⊤ ↔ IsUnit x
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Valuation.exists_pow_Uniformizer`：exists_pow_Uniformizer {r : K₀} (hr : 
r != 0) (π : Uniformizer v) : exists n : Nat, exists u : K₀ˣ, r = (π.1 ^ n).1 * 
u.1
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subring.coe_mul`：coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
-/
theorem Uniformizer.is_generator (π : Uniformizer v) :
    maximalIdeal v.valuationSubring = Ideal.span {π.1} := by
  apply (maximalIdeal.isMaximal _).eq_of_le
  · intro h
    rw [Ideal.span_singleton_eq_top] at h
    apply π.2.not_isUnit h
  · intro x hx
    by_cases hx₀ : x = 0
    · simp [hx₀]
    · obtain ⟨n, ⟨u, hu⟩⟩ := exists_pow_Uniformizer hx₀ π
      rw [← Subring.coe_mul, Subtype.coe_inj] at hu
      have hn : Not (IsUnit x) := fun h ↦
        (maximalIdeal.isMaximal _).ne_top (eq_top_of_isUnit_mem _ hx h)
      replace hn : n ≠ 0 := fun h ↦ by
        simp only [hu, h, pow_zero, one_mul, Units.isUnit, not_true] at hn
      simp [Ideal.mem_span_singleton, hu, dvd_pow_self _ hn]
/-
**Valuation.IsUniformizer.is_generator** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsUn
iformizer`。
形式化陈述：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {K : Type u_2} 
[inst_1 : Field K] {v : Valuation K Γ}   [hv : v.IsRankOneDiscrete] {π : ↥v.valu
ationSubring},   v.IsUniformizer ↑π → IsLocalRing.maximalIdeal ↥v.valuationSubri
ng = Ideal.span {π}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Uniformizer.is_generator`：∀ {Γ : Type u_1} [inst : LinearOrder
edCommGroupWithZero Γ] {K : Type u_2} [inst_1 : Field K] {v : Valuation K Γ}   [
hv : v.IsRankOneDiscrete…
-/
theorem IsUniformizer.is_generator {π : v.valuationSubring} (hπ : IsUniformizer v π) :
    maximalIdeal v.valuationSubring = Ideal.span {π} :=
  Uniformizer.is_generator ⟨π, hπ⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Valuation.pow_Uniformizer_is_pow_generator** 是 Mathlib 中的一个定理，位于命名空间 `Valuatio
n`。
形式化陈述：pow_Uniformizer_is_pow_generator (π : Uniformizer v) (n : Nat) : maximalId
eal v.valuationSubring ^ n = Ideal.span {π.1 ^ n}
参数：π : Uniformizer v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Valuation.Uniformizer.is_generator`：∀ {Γ : Type u_1} [inst : LinearOrder
edCommGroupWithZero Γ] {K : Type u_2} [inst_1 : Field K] {v : Valuation K Γ}   [
hv : v.IsRankOneDiscrete…
-/
theorem pow_Uniformizer_is_pow_generator (π : Uniformizer v) (n : ℕ) :
    maximalIdeal v.valuationSubring ^ n = Ideal.span {π.1 ^ n} := by
  rw [← Ideal.span_singleton_pow, Uniformizer.is_generator]

end Uniformizer

end IsRankOneDiscrete

/-
**Valuation.valuationSubring_not_isField** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：valuationSubring_not_isField [Nontrivial (valueGroup (.ofClass v))] [IsCyc
lic (valueGroup (.ofClass v))] : ¬ IsField K₀
参数：valueGroup (.ofClass v)；valueGroup (.ofClass v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsRankOneDiscrete.mk'`：∀ {Γ : Type u_1} [inst : LinearOrderedC
ommGroupWithZero Γ] {R : Type u_2} [inst_1 : Ring R] (v : Valuation R Γ)   [IsCy
clic ↥(MonoidWithZero…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`：exists_isUnifo
rmizer_of_isCyclic_of_nontrivial : exists π : K₀, IsUniformizer v (π : K)
· 使用定理 `Valuation.IsUniformizer.ne_zero`：ne_zero (hπ : IsUniformizer v π) : π !=
 0
· 使用定理 `Valuation.IsUniformizer.not_isUnit`：∀ {Γ : Type u_1} [inst : LinearOrder
edCommGroupWithZero Γ] {R : Type u_2} [inst_1 : CommRing R] {v : Valuation R Γ} 
  [hv : v.IsRankOneDiscr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `SubmonoidClass.instIsDedekindFiniteMonoidSubtypeMem`：∀ {M : Type u_1} {A
 : Type u_3} [inst : MulOneClass M] [inst_1 : SetLike A M] [hA : SubmonoidClass 
A M] (S : A)   [IsDedekindFiniteMonoid M]…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem valuationSubring_not_isField [Nontrivial (valueGroup (.ofClass v))]
    [IsCyclic (valueGroup (.ofClass v))] : ¬ IsField K₀ := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  rintro ⟨-, -, h⟩
  have := hπ.ne_zero
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact hπ.not_isUnit h

set_option backward.isDefEq.respectTransparency false in
/-
**Valuation.isUniformizer_of_maximalIdeal_eq_span** 是 Mathlib 中的一个定理，位于命名空间 `Val
uation`。
形式化陈述：isUniformizer_of_maximalIdeal_eq_span [v.IsRankOneDiscrete] {r : K₀} (hr :
 maximalIdeal v.valuationSubring = Ideal.span {r}) : IsUniformizer v r
参数：hr : maximalIdeal v.valuationSubring = Ideal.span {r}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Ring.ne_bot_of_isMaximal_of_not_isField`：ne_bot_of_isMaximal_of_not_isFi
eld [Nontrivial R] {M : Ideal R} (max : M.IsMaximal) (not_field : ¬IsField R) : 
M != ⊥
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Valuation.valuationSubring_not_isField`：valuationSubring_not_isField [No
ntrivial (valueGroup (.ofClass v))] [IsCyclic (valueGroup (.ofClass v))] : ¬ IsF
ield K₀
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `Valuation.IsRankOneDiscrete.instIsNontrivial`：∀ {Γ : Type u_1} [inst : L
inearOrderedCommGroupWithZero Γ] {A : Type u_2} [inst_1 : Ring A] (v : Valuation
 A Γ)   [v.IsRankOneDiscrete], v.I…
· 使用定理 `Valuation.IsRankOneDiscrete.instIsCyclicSubtypeUnitsMemSubgroupValueGrou
pOfClass`：∀ {Γ : Type u_1} [inst : LinearOrderedCommGroupWithZero Γ] {A : Type u
_2} [inst_1 : Ring A] (v : Valuation A Γ)   [v.IsRankOneDiscrete], IsC…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_zero`：span_zero : span (0 : Set α) = ⊥
· 使用定理 `Set.singleton_zero`：∀ {α : Type u_2} [inst : Zero α], {0} = 0
· 使用定理 `Valuation.IsRankOneDiscrete.mk'`：∀ {Γ : Type u_1} [inst : LinearOrderedC
ommGroupWithZero Γ] {R : Type u_2} [inst_1 : Ring R] (v : Valuation R Γ)   [IsCy
clic ↥(MonoidWithZero…
· 使用定理 `Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`：exists_isUnifo
rmizer_of_isCyclic_of_nontrivial : exists π : K₀, IsUniformizer v (π : K)
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Valuation.exists_pow_Uniformizer`：exists_pow_Uniformizer {r : K₀} (hr : 
r != 0) (π : Uniformizer v) : exists n : Nat, exists u : K₀ˣ, r = (π.1 ^ n).1 * 
u.1
· 使用定理 `Valuation.IsUniformizer.of_associated`：∀ {Γ : Type u_1} [inst : LinearOr
deredCommGroupWithZero Γ] {K : Type u_2} [inst_1 : Field K] {v : Valuation K Γ} 
  [hv : v.IsRankOneDiscrete…
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Valuation.Uniformizer.is_generator`：∀ {Γ : Type u_1} [inst : LinearOrder
edCommGroupWithZero Γ] {K : Type u_2} [inst_1 : Field K] {v : Valuation K Γ}   [
hv : v.IsRankOneDiscrete…
-/
theorem isUniformizer_of_maximalIdeal_eq_span [v.IsRankOneDiscrete] {r : K₀}
    (hr : maximalIdeal v.valuationSubring = Ideal.span {r}) :
    IsUniformizer v r := by
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, Set.singleton_zero, span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (valuationSubring_not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨n, u, hu⟩ := exists_pow_Uniformizer hr₀ ⟨π, hπ⟩
  rw [Uniformizer.is_generator ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr
  exact hπ.of_associated hr

set_option backward.isDefEq.respectTransparency false in
/-
**Valuation.ideal_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：ideal_isPrincipal [IsCyclic (valueGroup (.ofClass v))] [Nontrivial (valueG
roup (.ofClass v))] (I : Ideal K₀) : I.IsPrincipal
参数：valueGroup (.ofClass v)；valueGroup (.ofClass v)；I : Ideal K₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.IsRankOneDiscrete.mk'`：∀ {Γ : Type u_1} [inst : LinearOrderedC
ommGroupWithZero Γ] {R : Type u_2} [inst_1 : Ring R] (v : Valuation R Γ)   [IsCy
clic ↥(MonoidWithZero…
· 使用定理 `Valuation.instNonemptyUniformizer`：∀ {Γ : Type u_1} [inst : LinearOrdere
dCommGroupWithZero Γ] {K : Type u_2} [inst_1 : Field K] (v : Valuation K Γ)   [i
nst_2 : IsCyclic ↥(Mono…
· 使用定理 `Submodule.exists_mem_ne_zero_of_ne_bot`：exists_mem_ne_zero_of_ne_bot {p 
: Submodule R M} (h : p != ⊥) : exists b : M, b in p ∧ b != 0
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Valuation.exists_pow_Uniformizer`：exists_pow_Uniformizer {r : K₀} (hr : 
r != 0) (π : Uniformizer v) : exists n : Nat, exists u : K₀ˣ, r = (π.1 ^ n).1 * 
u.1
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subring.coe_mul`：coe_mul (x y : s) : (↑(x * y) : R) = ↑x * ↑y
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ideal.IsPrime.pow_mem_iff_mem`：∀ {α : Type u} [inst : Semiring α] {I : I
deal α}, I.IsPrime → ∀ {r : α} (n : ℕ), 0 < n → (r ^ n ∈ I ↔ r ∈ I)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Ideal.mul_unit_mem_iff_mem`：mul_unit_mem_iff_mem {x y : α} (hy : IsUnit 
y) : x * y in I ↔ x in I
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Valuation.Uniformizer.is_generator`：∀ {Γ : Type u_1} [inst : LinearOrder
edCommGroupWithZero Γ] {K : Type u_2} [inst_1 : Field K] {v : Valuation K Γ}   [
hv : v.IsRankOneDiscrete…
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
（共 32 条，此处仅展示前 30 条）
-/
theorem ideal_isPrincipal [IsCyclic (valueGroup (.ofClass v))]
    [Nontrivial (valueGroup (.ofClass v))] (I : Ideal K₀) : I.IsPrincipal := by
  suffices ∀ P : Ideal K₀, P.IsPrime → Submodule.IsPrincipal P by
    exact (IsPrincipalIdealRing.of_prime this).principal I
  intro P hP
  by_cases h_ne_bot : P = ⊥
  · rw [h_ne_bot]; exact bot_isPrincipal
  · let π : Uniformizer v := Nonempty.some (by infer_instance)
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    obtain ⟨n, ⟨u, hu⟩⟩ := exists_pow_Uniformizer hx₀ π
    by_cases hn : n = 0
    · rw [← Subring.coe_mul, hn, pow_zero, one_mul, SetLike.coe_eq_coe] at hu
      refine (hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx_mem ?_)).elim
      simp only [hu, Units.isUnit]
    · rw [← Subring.coe_mul, SetLike.coe_eq_coe] at hu
      rw [hu, Ideal.mul_unit_mem_iff_mem P u.isUnit,
        IsPrime.pow_mem_iff_mem hP _ (pos_iff_ne_zero.mpr hn),
        ← Ideal.span_singleton_le_iff_mem] at hx_mem
      replace hx_mem := π.is_generator ▸ hx_mem
      rw [← Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal K₀) hP.ne_top hx_mem]
      exact ⟨π.1, π.is_generator⟩
/-
**Valuation.valuationSubring_isPrincipalIdealRing** 是 Mathlib 中的一个定理，位于命名空间 `Val
uation`。
形式化陈述：valuationSubring_isPrincipalIdealRing [IsCyclic (valueGroup (.ofClass v))]
 [Nontrivial (valueGroup (.ofClass v))] : IsPrincipalIdealRing K₀
参数：valueGroup (.ofClass v)；valueGroup (.ofClass v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Valuation.ideal_isPrincipal`：ideal_isPrincipal [IsCyclic (valueGroup (.o
fClass v))] [Nontrivial (valueGroup (.ofClass v))] (I : Ideal K₀) : I.IsPrincipa
l
-/
theorem valuationSubring_isPrincipalIdealRing [IsCyclic (valueGroup (.ofClass v))]
    [Nontrivial (valueGroup (.ofClass v))] : IsPrincipalIdealRing K₀ :=
  ⟨(ideal_isPrincipal v ·)⟩

/-- This is Chapter I, Section 1, Proposition 1 in Serre's Local Fields -/
/-
**Valuation.valuationSubring_isDiscreteValuationRing** 是 Mathlib 中的一个实例，位于命名空间 `
Valuation`。
形式化陈述：valuationSubring_isDiscreteValuationRing [IsCyclic (valueGroup (.ofClass v
))] [Nontrivial (valueGroup (.ofClass v))] : IsDiscreteValuationRing K₀ where to
IsPrincipalIdealRing
参数：valueGroup (.ofClass v)；valueGroup (.ofClass v)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.valuationSubring_isPrincipalIdealRing`：valuationSubring_isPrin
cipalIdealRing [IsCyclic (valueGroup (.ofClass v))] [Nontrivial (valueGroup (.of
Class v))] : IsPrincipalIdealRing K₀
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.isField_iff_maximalIdeal_eq`：isField_iff_maximalIdeal_eq : I
sField R ↔ maximalIdeal R = ⊥
· 使用定理 `Valuation.valuationSubring_not_isField`：valuationSubring_not_isField [No
ntrivial (valueGroup (.ofClass v))] [IsCyclic (valueGroup (.ofClass v))] : ¬ IsF
ield K₀

--- 原说明 ---
This is Chapter I, Section 1, Proposition 1 in Serre's Local Fields
-/
instance valuationSubring_isDiscreteValuationRing [IsCyclic (valueGroup (.ofClass v))]
    [Nontrivial (valueGroup (.ofClass v))] : IsDiscreteValuationRing K₀ where
  toIsPrincipalIdealRing := valuationSubring_isPrincipalIdealRing v
  toIsLocalRing := inferInstance
  not_a_field' := by rw [ne_eq, ← isField_iff_maximalIdeal_eq]; exact valuationSubring_not_isField v

end Field

end Valuation

