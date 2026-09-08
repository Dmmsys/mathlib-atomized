/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
module

public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public meta import Mathlib.Lean.Expr.ExtraRecognizers

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `LinearIndependent R v` as `Function.Injective (Finsupp.linearCombination R v)`. Here
`Finsupp.linearCombination` is the linear map sending a function `f : ι →₀ R` with finite support to
the linear combination of vectors from `v` with these coefficients.

The goal of this file is to define linear independence and to prove that several other
statements are equivalent to this one, including `ker (Finsupp.linearCombination R v) = ⊥` and
some versions with explicitly written linear combinations.

## Main definitions
All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `LinearIndependent R v` states that the elements of the family `v` are linearly independent.

* `LinearIndepOn R v s` states that the elements of the family `v` indexed by the members
  of the set `s : Set ι` are linearly independent.

* `LinearIndependent.repr hv x` returns the linear combination representing `x : span R (range v)`
  on the linearly independent vectors `v`, given `hv : LinearIndependent R v`
  (using classical choice). `LinearIndependent.repr hv` is provided as a linear map.

* `LinearIndependent.Maximal` states that there exists no linear independent family that strictly
  includes the given one.

## Main results

* `Fintype.linearIndependent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : Finset ι`;

## Implementation notes

We use families instead of sets in `LinearIndependent` because it allows us to say that two
identical vectors are linearly dependent.

If you want to use sets, use `LinearIndepOn id s` given a set `s : Set M`. The lemmas
`LinearIndependent.linearIndepOn_id` and `LinearIndependent.of_linearIndepOn_id_range` connect those
two worlds.

In this file we prove some variants of results on different kinds of (semi)rings. We distinguish
them by using suffixes in their names, e.g. `linearIndependent_iffₛ` for semirings,
`linearIndependent_iffₒₛ` for (canonically) ordered semirings, and `linearIndependent_iff` (without
suffix) for rings.

## TODO

This file contains much more than definitions.

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

@[expose] public section

assert_not_exists Cardinal

noncomputable section

open Function Module Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι → M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)
/-- `LinearIndependent R v` states the family of vectors `v` is linearly independent over `R`. -/
/-
**LinearIndependent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearIndependent : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearIndependent R v` states the family of vectors `v` is linearly independent
 over `R`.
-/
def LinearIndependent : Prop :=
  Injective (Finsupp.linearCombination R v)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `LinearIndependent` that suggests pretty printing with type hints
in case the family of vectors is over a `Set`.

Type hints look like `LinearIndependent fun (v : ↑s) => ↑v` or `LinearIndependent (ι := ↑s) f`,
depending on whether the family is a lambda expression or not. -/
@[app_delab LinearIndependent]
meta def delabLinearIndependent : Delab :=
  whenPPOption getPPNotation <|
  whenNotPPOption getPPAnalysisSkip <|
  withOptionAtCurrPos `pp.analysis.skip true do
    let e ← getExpr
    guard <| e.isAppOfArity ``LinearIndependent 7
    let some _ := (e.getArg! 0).coeTypeSet? | failure
    let optionsPerPos ← if (e.getArg! 3).isLambda then
      withNaryArg 3 do return (← read).optionsPerPos.setBool (← getPos) pp.funBinderTypes.name true
    else
      withNaryArg 0 do return (← read).optionsPerPos.setBool (← getPos) `pp.analysis.namedArg true
    withTheReader Context ({· with optionsPerPos}) delab

/-- `LinearIndepOn R v s` states that the vectors in the family `v` that are indexed
by the elements of `s` are linearly independent over `R`. -/
/-
**LinearIndepOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearIndepOn (s : Set ι) : Prop
参数：s : Set ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearIndepOn R v s` states that the vectors in the family `v` that are indexed
by the elements of `s` are linearly independent over `R`.
-/
def LinearIndepOn (s : Set ι) : Prop := LinearIndependent R (fun x : s ↦ v x)

variable {R v}
/-
**LinearIndepOn.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.linearIndependent {s : Set ι} (h : LinearIndepOn R v s) : Li
nearIndependent R (fun x : s => v x)
参数：h : LinearIndepOn R v s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearIndepOn.linearIndependent {s : Set ι} (h : LinearIndepOn R v s) :
    LinearIndependent R (fun x : s ↦ v x) := h
/-
**linearIndependent_iff_injective_finsuppLinearCombination** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：linearIndependent_iff_injective_finsuppLinearCombination : LinearIndepende
nt R v ↔ Injective (Finsupp.linearCombination R v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_iff_injective_finsuppLinearCombination :
    LinearIndependent R v ↔ Injective (Finsupp.linearCombination R v) := Iff.rfl

alias ⟨LinearIndependent.finsuppLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_finsuppLinearCombination
/-
**linearIndependent_iff_injective_fintypeLinearCombination** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：linearIndependent_iff_injective_fintypeLinearCombination [Fintype ι] : Lin
earIndependent R v ↔ Injective (Fintype.linearCombination R v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem linearIndependent_iff_injective_fintypeLinearCombination [Fintype ι] :
    LinearIndependent R v ↔ Injective (Fintype.linearCombination R v) := by
  simp [← Finsupp.linearCombination_eq_fintype_linearCombination, LinearIndependent]

alias ⟨LinearIndependent.fintypeLinearCombination_injective, _⟩ :=
  linearIndependent_iff_injective_fintypeLinearCombination
/-
**LinearIndependent.injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.injective [Nontrivial R] (hv : LinearIndependent R v) : 
Injective v
参数：hv : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Finsupp.single_left_injective`：single_left_injective (h : b != 0) : Func
tion.Injective fun a : α => single a b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem LinearIndependent.injective [Nontrivial R] (hv : LinearIndependent R v) : Injective v := by
  simpa [comp_def]
    using Injective.comp hv (Finsupp.single_left_injective one_ne_zero)
/-
**LinearIndepOn.injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.injOn [Nontrivial R] (hv : LinearIndepOn R v s) : InjOn v s
参数：hv : LinearIndepOn R v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
-/
theorem LinearIndepOn.injOn [Nontrivial R] (hv : LinearIndepOn R v s) : InjOn v s :=
  injOn_iff_injective.2 <| LinearIndependent.injective hv
/-
**LinearIndependent.smul_left_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.smul_left_injective (hv : LinearIndependent R v) (i : ι)
 : Injective fun r : R => r • v i
参数：hv : LinearIndependent R v；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
-/
theorem LinearIndependent.smul_left_injective (hv : LinearIndependent R v) (i : ι) :
    Injective fun r : R ↦ r • v i := by convert! hv.comp (Finsupp.single_injective i); simp
/-
**LinearIndependent.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.ne_zero [Nontrivial R] (i : ι) (hv : LinearIndependent R
 v) : v i != 0
参数：i : ι；hv : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem LinearIndependent.ne_zero [Nontrivial R] (i : ι) (hv : LinearIndependent R v) :
    v i ≠ 0 := by
  intro h
  have := @hv (Finsupp.single i 1 : ι →₀ R) 0 (by simpa using h)
  simp at this
/-
**LinearIndepOn.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.ne_zero [Nontrivial R] {i : ι} (hv : LinearIndepOn R v s) (h
i : i in s) : v i != 0
参数：hv : LinearIndepOn R v s；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
-/
theorem LinearIndepOn.ne_zero [Nontrivial R] {i : ι} (hv : LinearIndepOn R v s) (hi : i ∈ s) :
    v i ≠ 0 :=
  LinearIndependent.ne_zero ⟨i, hi⟩ hv
/-
**LinearIndepOn.zero_notMem_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.zero_notMem_image [Nontrivial R] (hs : LinearIndepOn R v s) 
: 0 ∉ v '' s
参数：hs : LinearIndepOn R v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.ne_zero`：LinearIndepOn.ne_zero [Nontrivial R] {i : ι} (hv 
: LinearIndepOn R v s) (hi : i in s) : v i != 0
-/
theorem LinearIndepOn.zero_notMem_image [Nontrivial R] (hs : LinearIndepOn R v s) : 0 ∉ v '' s :=
  fun ⟨_, hi, h0⟩ ↦ hs.ne_zero hi h0
/-
**linearIndependent_empty_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_empty_type [IsEmpty ι] : LinearIndependent R v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
-/
theorem linearIndependent_empty_type [IsEmpty ι] : LinearIndependent R v :=
  injective_of_subsingleton _

@[simp]
/-
**linearIndependent_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_zero_iff [Nontrivial R] : LinearIndependent R (0 : ι -> 
M) ↔ IsEmpty ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `linearIndependent_empty_type`：linearIndependent_empty_type [IsEmpty ι] :
 LinearIndependent R v
-/
theorem linearIndependent_zero_iff [Nontrivial R] : LinearIndependent R (0 : ι → M) ↔ IsEmpty ι :=
  ⟨fun h ↦ not_nonempty_iff.1 fun ⟨i⟩ ↦ (h.ne_zero i rfl).elim,
    fun _ ↦ linearIndependent_empty_type⟩

@[simp]
/-
**linearIndepOn_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_zero_iff [Nontrivial R] : LinearIndepOn R (0 : ι -> M) s ↔ s
 = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `linearIndependent_zero_iff`：linearIndependent_zero_iff [Nontrivial R] : 
LinearIndependent R (0 : ι -> M) ↔ IsEmpty ι
· 使用定理 `Set.isEmpty_coe_sort`：isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = 
∅
-/
theorem linearIndepOn_zero_iff [Nontrivial R] : LinearIndepOn R (0 : ι → M) s ↔ s = ∅ :=
  linearIndependent_zero_iff.trans isEmpty_coe_sort

@[simp]
/-
**linearIndependent_subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_subsingleton_iff [Nontrivial R] [Subsingleton M] (f : ι 
-> M) : LinearIndependent R f ↔ IsEmpty ι
参数：f : ι -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `linearIndependent_zero_iff`：linearIndependent_zero_iff [Nontrivial R] : 
LinearIndependent R (0 : ι -> M) ↔ IsEmpty ι
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_subsingleton_iff [Nontrivial R] [Subsingleton M] (f : ι → M) :
    LinearIndependent R f ↔ IsEmpty ι := by
  rw [Subsingleton.elim f 0, linearIndependent_zero_iff]

variable (R M) in
/-
**linearIndependent_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_empty : LinearIndependent R (fun x => x : (∅ : Set M) ->
 M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_empty_type`：linearIndependent_empty_type [IsEmpty ι] :
 LinearIndependent R v
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
theorem linearIndependent_empty : LinearIndependent R (fun x => x : (∅ : Set M) → M) :=
  linearIndependent_empty_type

variable (R v) in
@[simp]
/-
**linearIndepOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_empty : LinearIndepOn R v ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_empty_type`：linearIndependent_empty_type [IsEmpty ι] :
 LinearIndependent R v
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
theorem linearIndepOn_empty : LinearIndepOn R v ∅ :=
  linearIndependent_empty_type ..
/-
**linearIndependent_set_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_set_coe_iff : LinearIndependent R (fun x : s => v x) ↔ L
inearIndepOn R v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_set_coe_iff :
    LinearIndependent R (fun x : s ↦ v x) ↔ LinearIndepOn R v s := Iff.rfl
/-
**linearIndependent_subtype_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_subtype_iff {s : Set M} : LinearIndependent R (Subtype.v
al : s -> M) ↔ LinearIndepOn R id s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_subtype_iff {s : Set M} :
    LinearIndependent R (Subtype.val : s → M) ↔ LinearIndepOn R id s := Iff.rfl
/-
**linearIndependent_comp_subtype_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_comp_subtype_iff : LinearIndependent R (v ∘ Subtype.val 
: s -> M) ↔ LinearIndepOn R v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_comp_subtype_iff :
    LinearIndependent R (v ∘ Subtype.val : s → M) ↔ LinearIndepOn R v s := Iff.rfl

/-- A subfamily of a linearly independent family (i.e., a composition with an injective map) is a
linearly independent family. -/
/-
**LinearIndependent.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.comp (h : LinearIndependent R v) (f : ι' -> ι) (hf : Inj
ective f) : LinearIndependent R (v ∘ f)
参数：h : LinearIndependent R v；f : ι' -> ι；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.linearCombination_mapDomain`：linearCombination_mapDomain (f : α 
-> α') (l : α ->₀ R) : (linearCombination R v') (mapDomain f l) = (linearCombina
tion R (v' ∘ f)) l
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)

--- 原说明 ---
A subfamily of a linearly independent family (i.e., a composition with an inject
ive map) is a
linearly independent family.
-/
theorem LinearIndependent.comp (h : LinearIndependent R v) (f : ι' → ι) (hf : Injective f) :
    LinearIndependent R (v ∘ f) := by
  simpa [comp_def] using! Injective.comp h (Finsupp.mapDomain_injective hf)
/-
**LinearIndepOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn R v s) (h : t subsete
q s) : LinearIndepOn R v t
参数：hs : LinearIndepOn R v s；h : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
lemma LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn R v s) (h : t ⊆ s) :
    LinearIndepOn R v t := hs.comp _ <| Set.inclusion_injective h

-- This version makes `l₁` and `l₂` explicit.
/-
**linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff : LinearIndependent R v ↔ forall l, Finsupp.linearCo
mbination R v l = 0 -> l = 0
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
theorem linearIndependent_iffₛ :
    LinearIndependent R v ↔
      ∀ l₁ l₂, Finsupp.linearCombination R v l₁ = Finsupp.linearCombination R v l₂ → l₁ = l₂ :=
  Iff.rfl

open Finset in
/-
**linearIndependent_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff'ₛ : LinearIndependent R v ↔ forall s : Finset ι, for
all f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i • v i -> forall i in s, f 
i = g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'ₛ`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} {
v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mod
ule R M],   L…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem linearIndependent_iff'ₛ :
    LinearIndependent R v ↔
      ∀ s : Finset ι, ∀ f g : ι → R, ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i → ∀ i ∈ s, f i = g i :=
  linearIndependent_iffₛ.trans
    ⟨fun hv s f g eq i his ↦ by
      have h :=
        hv (∑ i ∈ s, Finsupp.single i (f i)) (∑ i ∈ s, Finsupp.single i (g i)) <| by
          simpa only [map_sum, Finsupp.linearCombination_single] using eq
      have (f : ι → R) : f i = (∑ j ∈ s, Finsupp.single j (f j)) i :=
        calc
          f i = (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single i (f i)) := by
            { rw [Finsupp.lapply_apply, Finsupp.single_eq_same] }
          _ = ∑ j ∈ s, (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single j (f j)) :=
            Eq.symm <|
              Finset.sum_eq_single i
                (fun j _hjs hji => by rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne' hji])
                fun hnis => hnis.elim his
          _ = (∑ j ∈ s, Finsupp.single j (f j)) i := (map_sum ..).symm
      rw [this f, this g, h],
      fun hv f g hl ↦
      Finsupp.ext fun _ ↦ by
        classical
        refine _root_.by_contradiction fun hni ↦ hni <| hv (f.support ∪ g.support) f g ?_ _ ?_
        · rwa [← sum_subset subset_union_left, ← sum_subset subset_union_right] <;>
            rintro i - hi <;> rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
        · contrapose hni
          simp_rw [notMem_union, Finsupp.notMem_support_iff] at hni
          rw [hni.1, hni.2]⟩
/-
**linearIndependent_iff''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff''ₛ : LinearIndependent R v ↔ forall (s : Finset ι) (
f g : ι -> R), (forall i ∉ s, f i = g i) -> ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> forall i, f i = g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_extend_by_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M),   (∑ i ∈ s, if 
i ∈ s then f i …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearIndependent_iff''ₛ :
    LinearIndependent R v ↔
      ∀ (s : Finset ι) (f g : ι → R), (∀ i ∉ s, f i = g i) →
        ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i → ∀ i, f i = g i := by
  classical
  exact linearIndependent_iff'ₛ.trans
    ⟨fun H s f g eq hv i ↦ if his : i ∈ s then H s f g hv i his else eq i his,
      fun H s f g eq i hi ↦ by
      convert!
        H s (fun j ↦ if j ∈ s then f j else 0) (fun j ↦ if j ∈ s then g j else 0)
          (fun j hj ↦ (if_neg hj).trans (if_neg hj).symm)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, eq]) i <;>
      exact (if_pos hi).symm⟩
/-
**not_linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_linearIndependent_iff : ¬LinearIndependent R v ↔ exists s : Finset ι, 
exists g : ι -> R, ∑ i in s, g i • v i = 0 ∧ exists i in s, g i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_linearIndependent_iffₛ :
    ¬LinearIndependent R v ↔ ∃ s : Finset ι,
      ∃ f g : ι → R, ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i ∧ ∃ i ∈ s, f i ≠ g i := by
  rw [linearIndependent_iff'ₛ]
  simp only [exists_prop, not_forall]
/-
**Fintype.linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.linearIndependent_iff [Fintype ι] : LinearIndependent R v ↔ forall
 g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff''`：linearIndependent_iff''ₛ : LinearIndependent R 
v ↔ forall (s : Finset ι) (f g : ι -> R), (forall i ∉ s, f i = g i) -> ∑ i in s,
 f i • v i = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem Fintype.linearIndependent_iffₛ [Fintype ι] :
    LinearIndependent R v ↔ ∀ f g : ι → R, ∑ i, f i • v i = ∑ i, g i • v i → ∀ i, f i = g i := by
  simp_rw [linearIndependent_iff_injective_fintypeLinearCombination,
    Injective, Fintype.linearCombination_apply, funext_iff]
/-
**Fintype.not_linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.not_linearIndependent_iff [Fintype ι] : ¬LinearIndependent R v ↔ e
xists g : ι -> R, ∑ i, g i • v i = 0 ∧ exists i, g i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
-/
theorem Fintype.not_linearIndependent_iffₛ [Fintype ι] :
    ¬LinearIndependent R v ↔ ∃ f g : ι → R, ∑ i, f i • v i = ∑ i, g i • v i ∧ ∃ i, f i ≠ g i := by
  simpa using not_iff_not.2 Fintype.linearIndependent_iffₛ
/-
**linearIndepOn_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndepOn_finset_iff {s : Finset ι} : LinearIndepOn R v s ↔ forall f :
 ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) 
[inst_1 : Decidable p] (a : α) (b : p → β) (c : ¬p → β),   (if h : p then b h e…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
lemma linearIndepOn_finset_iffₛ {s : Finset ι} :
    LinearIndepOn R v s ↔ ∀ f g : ι → R,
      ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i → ∀ i ∈ s, f i = g i := by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iffₛ]
  constructor
  · rintro hv f g hfg i hi
    simp_rw [← s.sum_attach] at hfg
    exact hv (f ∘ Subtype.val) (g ∘ Subtype.val) hfg ⟨i, hi⟩
  · rintro hv f g hfg i
    simpa using hv (fun j ↦ if hj : j ∈ s then f ⟨j, hj⟩ else 0)
      (fun j ↦ if hj : j ∈ s then g ⟨j, hj⟩ else 0) (by simpa +contextual [← s.sum_attach]) i
/-
**not_linearIndepOn_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_linearIndepOn_finset_iff {s : Finset ι} : ¬LinearIndepOn R v s ↔ exist
s f : ι -> R, ∑ i in s, f i • v i = 0 ∧ exists i in s, f i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `linearIndepOn_finset_iff`：linearIndepOn_finset_iff {s : Finset ι} : Line
arIndepOn R v s ↔ forall f : ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f
 i = 0
-/
lemma not_linearIndepOn_finset_iffₛ {s : Finset ι} :
    ¬LinearIndepOn R v s ↔ ∃ f g : ι → R,
      ∑ i ∈ s, f i • v i = ∑ i ∈ s, g i • v i ∧ ∃ i ∈ s, f i ≠ g i := by
  simpa using linearIndepOn_finset_iffₛ.not

/-- A family is linearly independent if and only if all of its finite subfamily is
linearly independent. -/
/-
**linearIndependent_iff_finset_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff_finset_linearIndependent : LinearIndependent R v ↔ f
orall (s : Finset ι), LinearIndependent R (v ∘ (Subtype.val : s -> ι))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff'ₛ`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} {
v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mod
ule R M],   L…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.linearIndependent_iffₛ`：Fintype.linearIndependent_iffₛ [Fintype 
ι] : LinearIndependent R v ↔ forall f g : ι -> R, ∑ i, f i • v i = ∑ i, g i • v 
i -> forall i, f i =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i

--- 原说明 ---
A family is linearly independent if and only if all of its finite subfamily is
linearly independent.
-/
theorem linearIndependent_iff_finset_linearIndependent :
    LinearIndependent R v ↔ ∀ (s : Finset ι), LinearIndependent R (v ∘ (Subtype.val : s → ι)) :=
  ⟨fun H _ ↦ H.comp _ Subtype.val_injective, fun H ↦ linearIndependent_iff'ₛ.2 fun s f g eq i hi ↦
    Fintype.linearIndependent_iffₛ.1 (H s) (f ∘ Subtype.val) (g ∘ Subtype.val)
      (by simpa only [← s.sum_coe_sort] using! eq) ⟨i, hi⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**linearIndepOn_iff_linearIndepOn_finset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff_linearIndepOn_finset : LinearIndepOn R v s ↔ forall t : 
Finset ι, ↑t subseteq s -> LinearIndepOn R v t where mp hv t hts
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndepOn.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v : ι
 → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] (s :…
· 使用定理 `linearIndependent_iff_finset_linearIndependent`：linearIndependent_iff_fi
nset_linearIndependent : LinearIndependent R v ↔ forall (s : Finset ι), LinearIn
dependent R (v ∘ (Subtype.val : s ->…
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Finset.mem_map_of_mem`：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a
 in s -> f a in s.map f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
lemma linearIndepOn_iff_linearIndepOn_finset :
    LinearIndepOn R v s ↔ ∀ t : Finset ι, ↑t ⊆ s → LinearIndepOn R v t where
  mp hv t hts := hv.mono hts
  mpr hv := by
    rw [LinearIndepOn, linearIndependent_iff_finset_linearIndependent]
    exact fun t ↦ (hv (t.map <| .subtype _) (by simp)).comp (ι' := t)
      (fun x ↦ ⟨x, Finset.mem_map_of_mem (.subtype _) x.2⟩) fun x ↦ by aesop

/-- If the image of a family of vectors under a linear map is linearly independent, then so is
the original family. -/
/-
**LinearIndependent.of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.of_comp (f : M ->ₗ[R] M') (hfv : LinearIndependent R (f 
∘ v)) : LinearIndependent R v
参数：f : M ->ₗ[R] M'；hfv : LinearIndependent R (f ∘ v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Finsupp.linearCombination_linear_comp`：linearCombination_linear_comp (f 
: M ->ₗ[R] M') : linearCombination R (f ∘ v) = f ∘ₗ linearCombination R v
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…

--- 原说明 ---
If the image of a family of vectors under a linear map is linearly independent, 
then so is
the original family.
-/
theorem LinearIndependent.of_comp (f : M →ₗ[R] M') (hfv : LinearIndependent R (f ∘ v)) :
    LinearIndependent R v := by
  rw [LinearIndependent, Finsupp.linearCombination_linear_comp, LinearMap.coe_comp] at hfv
  exact hfv.of_comp
/-
**LinearIndepOn.of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.of_comp (f : M ->ₗ[R] M') (hfv : LinearIndepOn R (f ∘ v) s) 
: LinearIndepOn R v s
参数：f : M ->ₗ[R] M'；hfv : LinearIndepOn R (f ∘ v) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
-/
theorem LinearIndepOn.of_comp (f : M →ₗ[R] M') (hfv : LinearIndepOn R (f ∘ v) s) :
    LinearIndepOn R v s :=
  LinearIndependent.of_comp f hfv
/-
**LinearIndependent.of_linearIndependent_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.of_linearIndependent_subset (s : Set ι') {v : ι -> ι' ->
 R} (hv : LinearIndependent R fun (i : ι) (j : s) => v i j) : LinearIndependent 
R v
参数：s : Set ι'；hv : LinearIndependent R fun (i : ι) (j : s) => v i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
-/
lemma LinearIndependent.of_linearIndependent_subset (s : Set ι') {v : ι → ι' → R}
    (hv : LinearIndependent R fun (i : ι) (j : s) ↦ v i j) :
    LinearIndependent R v :=
  hv.of_comp ⟨⟨s.domRestrict, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩

/-- If `f` is a linear map injective on the span of the range of `v`, then the family `f ∘ v`
is linearly independent if and only if the family `v` is linearly independent.
See `LinearMap.linearIndependent_iff_of_disjoint` for the version with `Set.InjOn` replaced
by `Disjoint` when working over a ring. -/
/-
**LinearMap.linearIndependent_iff_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} {M' : Type u_5} {v : ι → M} 
[inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [in
st_3 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M'),   Set.
InjOn ⇑f ↑(Submodule.span R (Set.range v)) → (LinearIndependent R (⇑f ∘ v) ↔ Lin
earIndependent R v)
参数：f : M →ₗ[R] M'；Submodule.span R (Set.range v)；LinearIndependent R (⇑f ∘ v) ↔ 
LinearIndependent R v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_linear_comp`：linearCombination_linear_comp (f 
: M ->ₗ[R] M') : linearCombination R (f ∘ v) = f ∘ₗ linearCombination R v
· 使用定理 `Set.InjOn.injective_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : α → β} {g : β → γ} (s : Set β),   Set.InjOn g s → Set.range f ⊆ s → (Functi
on.Injective …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `f` is a linear map injective on the span of the range of `v`, then the famil
y `f ∘ v`
is linearly independent if and only if the family `v` is linearly independent.
See `LinearMap.linearIndependent_iff_of_disjoint` for the version with `Set.InjO
n` replaced
by `Disjoint` when working over a ring.
-/
protected theorem LinearMap.linearIndependent_iff_of_injOn (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (Set.range v))) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v := by
  simp_rw [LinearIndependent, Finsupp.linearCombination_linear_comp, coe_comp]
  rw [hf_inj.injective_iff]
  rw [← Finsupp.range_linearCombination, LinearMap.coe_range]
/-
**LinearMap.linearIndepOn_iff_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {ι : Type u'} {R : Type u_2} {s : Set ι} {M : Type u_4} {M' : Type u_5} 
{v : ι → M} [inst : Semiring R]   [inst_1 : AddCommMonoid M] [inst_2 : AddCommMo
noid M'] [inst_3 : _root_.Module R M] [inst_4 : _root_.Module R M']   (f : M →ₗ[
R] M'), Set.InjOn ⇑f ↑(Submodule.span R (v '' s)) → (LinearIndepOn R (⇑f ∘ v) s 
↔ LinearIndepOn R v s)
参数：f : M →ₗ[R] M'；Submodule.span R (v '' s)；LinearIndepOn R (⇑f ∘ v) s ↔ LinearI
ndepOn R v s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
-/
protected theorem LinearMap.linearIndepOn_iff_of_injOn (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) :
    LinearIndepOn R (f ∘ v) s ↔ LinearIndepOn R v s :=
  f.linearIndependent_iff_of_injOn (by rwa [← image_eq_range]) (v := fun i : s ↦ v i)

-- TODO : Rename this `LinearIndependent.of_subsingleton`.
@[nontriviality]
/-
**linearIndependent_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_of_subsingleton [Subsingleton R] : LinearIndependent R v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iffₛ`：linearIndependent_iffₛ : LinearIndependent R v ↔
 forall l₁ l₂, Finsupp.linearCombination R v l₁ = Finsupp.linearCombination R v 
l₂ -> l₁ = l…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem linearIndependent_of_subsingleton [Subsingleton R] : LinearIndependent R v :=
  linearIndependent_iffₛ.2 fun _l _l' _hl => Subsingleton.elim _ _

@[nontriviality]
/-
**LinearIndepOn.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.of_subsingleton [Subsingleton R] : LinearIndepOn R v s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_of_subsingleton`：linearIndependent_of_subsingleton [Su
bsingleton R] : LinearIndependent R v
-/
theorem LinearIndepOn.of_subsingleton [Subsingleton R] : LinearIndepOn R v s :=
  linearIndependent_of_subsingleton
/-
**linearIndependent_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_equiv (e : ι ≃ ι') {f : ι' -> M} : LinearIndependent R (
f ∘ e) ↔ LinearIndependent R f
参数：e : ι ≃ ι'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
-/
theorem linearIndependent_equiv (e : ι ≃ ι') {f : ι' → M} :
    LinearIndependent R (f ∘ e) ↔ LinearIndependent R f :=
  ⟨fun h ↦ comp_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
    fun h ↦ h.comp _ e.injective⟩
/-
**linearIndependent_equiv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_equiv' (e : ι ≃ ι') {f : ι' -> M} {g : ι -> M} (h : f ∘ 
e = g) : LinearIndependent R g ↔ LinearIndependent R f
参数：e : ι ≃ ι'；h : f ∘ e = g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
-/
theorem linearIndependent_equiv' (e : ι ≃ ι') {f : ι' → M} {g : ι → M} (h : f ∘ e = g) :
    LinearIndependent R g ↔ LinearIndependent R f :=
  h ▸ linearIndependent_equiv e
/-
**linearIndepOn_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_equiv (e : ι ≃ ι') {f : ι' -> M} {s : Set ι} : LinearIndepOn
 R (f ∘ e) s ↔ LinearIndepOn R f (e '' s)
参数：e : ι ≃ ι'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_equiv'`：linearIndependent_equiv' (e : ι ≃ ι') {f : ι' 
-> M} {g : ι -> M} (h : f ∘ e = g) : LinearIndependent R g ↔ LinearIndependent R
 f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.image_apply_coe`：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) (s : 
Set α) (x : ↑s), ↑((e.image s) x) = e ↑x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem linearIndepOn_equiv (e : ι ≃ ι') {f : ι' → M} {s : Set ι} :
    LinearIndepOn R (f ∘ e) s ↔ LinearIndepOn R f (e '' s) :=
  linearIndependent_equiv' (e.image s) <| by simp [funext_iff]

@[simp]
/-
**linearIndepOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_univ_iff : LinearIndepOn R v univ ↔ LinearIndependent R v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_equiv'`：linearIndependent_equiv' (e : ι ≃ ι') {f : ι' 
-> M} {g : ι -> M} (h : f ∘ e = g) : LinearIndependent R g ↔ LinearIndependent R
 f
-/
theorem linearIndepOn_univ_iff : LinearIndepOn R v univ ↔ LinearIndependent R v :=
  linearIndependent_equiv' (Equiv.Set.univ ι) rfl

@[deprecated (since := "2026-02-24")] alias linearIndepOn_univ := linearIndepOn_univ_iff

alias ⟨_, LinearIndependent.linearIndepOn_univ⟩ := linearIndepOn_univ_iff
/-
**LinearIndependent.linearIndepOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.linearIndepOn (h : LinearIndependent R v) (s : Set ι) : 
LinearIndepOn R v s
参数：h : LinearIndependent R v；s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `LinearIndependent.linearIndepOn_univ`：∀ {ι : Type u'} {R : Type u_2} {M 
: Type u_4} {v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2
 : _root_.Module R M], Lin…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma LinearIndependent.linearIndepOn (h : LinearIndependent R v) (s : Set ι) :
    LinearIndepOn R v s :=
  h.linearIndepOn_univ.mono s.subset_univ
/-
**linearIndepOn_iff_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff_image {ι} {s : Set ι} {f : ι -> M} (hf : Set.InjOn f s) 
: LinearIndepOn R f s ↔ LinearIndepOn R id (f '' s)
参数：hf : Set.InjOn f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_equiv'`：linearIndependent_equiv' (e : ι ≃ ι') {f : ι' 
-> M} {g : ι -> M} (h : f ∘ e = g) : LinearIndependent R g ↔ LinearIndependent R
 f
-/
theorem linearIndepOn_iff_image {ι} {s : Set ι} {f : ι → M} (hf : Set.InjOn f s) :
    LinearIndepOn R f s ↔ LinearIndepOn R id (f '' s) :=
  linearIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl
/-
**linearIndepOn_range_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_range_iff {ι} {f : ι -> ι'} (hf : Injective f) (g : ι' -> M)
 : LinearIndepOn R g (range f) ↔ LinearIndependent R (g ∘ f)
参数：hf : Injective f；g : ι' -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `linearIndependent_equiv'`：linearIndependent_equiv' (e : ι ≃ ι') {f : ι' 
-> M} {g : ι -> M} (h : f ∘ e = g) : LinearIndependent R g ↔ LinearIndependent R
 f
-/
theorem linearIndepOn_range_iff {ι} {f : ι → ι'} (hf : Injective f) (g : ι' → M) :
    LinearIndepOn R g (range f) ↔ LinearIndependent R (g ∘ f) :=
  Iff.symm <| linearIndependent_equiv' (Equiv.ofInjective f hf) rfl

alias ⟨LinearIndependent.of_linearIndepOn_range, _⟩ := linearIndepOn_range_iff
/-
**linearIndepOn_id_range_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_id_range_iff {ι} {f : ι -> M} (hf : Injective f) : LinearInd
epOn R id (range f) ↔ LinearIndependent R f
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndepOn_range_iff`：linearIndepOn_range_iff {ι} {f : ι -> ι'} (hf :
 Injective f) (g : ι' -> M) : LinearIndepOn R g (range f) ↔ LinearIndependent R 
(g ∘ f)
-/
theorem linearIndepOn_id_range_iff {ι} {f : ι → M} (hf : Injective f) :
    LinearIndepOn R id (range f) ↔ LinearIndependent R f :=
  linearIndepOn_range_iff hf id

alias ⟨LinearIndependent.of_linearIndepOn_id_range, _⟩ := linearIndepOn_id_range_iff
/-
**LinearIndependent.linearIndepOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.linearIndepOn_id (i : LinearIndependent R v) : LinearInd
epOn R id (range v)
参数：i : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.comp_rangeSplitting`：comp_rangeSplitting (f : α -> β) : f ∘ rangeSpl
itting f = Subtype.val
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Set.rangeSplitting_injective`：rangeSplitting_injective (f : α -> β) : In
jective (rangeSplitting f)
-/
theorem LinearIndependent.linearIndepOn_id (i : LinearIndependent R v) :
    LinearIndepOn R id (range v) := by
  simpa using! i.comp _ (rangeSplitting_injective v)

/-- A version of `LinearIndependent.linearIndepOn_id` with the set range equality as a hypothesis.
-/
/-
**LinearIndependent.linearIndepOn_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.linearIndepOn_id' (hv : LinearIndependent R v) {t : Set 
M} (ht : Set.range v = t) : LinearIndepOn R id t
参数：hv : LinearIndependent R v；ht : Set.range v = t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)

--- 原说明 ---
A version of `LinearIndependent.linearIndepOn_id` with the set range equality as
 a hypothesis.
-/
theorem LinearIndependent.linearIndepOn_id' (hv : LinearIndependent R v) {t : Set M}
    (ht : Set.range v = t) : LinearIndepOn R id t :=
  ht ▸ hv.linearIndepOn_id

section Indexed

/-
**linearIndepOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff : LinearIndepOn R v s ↔ forall l in Finsupp.supported R 
R s, (Finsupp.linearCombination R v) l = 0 -> l = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `linearIndepOn_iffₛ`：linearIndepOn_iffₛ : LinearIndepOn R v s ↔ forall f 
in Finsupp.supported R R s, forall g in Finsupp.supported R R s, Finsupp.linearC
ombinati…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem linearIndepOn_iffₛ : LinearIndepOn R v s ↔
      ∀ f ∈ Finsupp.supported R R s, ∀ g ∈ Finsupp.supported R R s,
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g → f = g := by
  simp only [LinearIndepOn, linearIndependent_iffₛ, Finsupp.mem_supported,
    Finsupp.linearCombination_apply, Set.subset_def, Finset.mem_coe]
  refine ⟨fun h l₁ h₁ l₂ h₂ eq ↦ (Finsupp.subtypeDomain_eq_iff h₁ h₂).1 <| h _ _ <|
    (Finsupp.sum_subtypeDomain_index h₁).trans eq ▸ (Finsupp.sum_subtypeDomain_index h₂).symm,
    fun h l₁ l₂ eq ↦ ?_⟩
  refine Finsupp.embDomain_injective (Embedding.subtype (· ∈ s)) <| h _ ?_ _ ?_ ?_
  iterate 2 simpa using fun _ h _ ↦ h
  simp_rw [Finsupp.embDomain_eq_mapDomain]
  rwa [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index] <;>
    intros <;> simp only [zero_smul, add_smul]

/-- An indexed set of vectors is linearly dependent iff there are two distinct
`Finsupp.LinearCombination`s of the vectors with the same value. -/
/-
**linearDepOn_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearDepOn_iff'ₛ : ¬LinearIndepOn R v s ↔ exists f g : ι ->₀ R, f in Fins
upp.supported R R s ∧ g in Finsupp.supported R R s ∧ Finsupp.linearCombination R
 v f = Finsupp.linearCombination R v g ∧ f != g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An indexed set of vectors is linearly dependent iff there are two distinct
`Finsupp.LinearCombination`s of the vectors with the same value.
-/
theorem linearDepOn_iff'ₛ : ¬LinearIndepOn R v s ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g ∧ f ≠ g := by
  simp [linearIndepOn_iffₛ]

/-- A version of `linearDepOn_iff'ₛ` with `Finsupp.linearCombination` unfolded. -/
/-
**linearDepOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearDepOn_iff : ¬LinearIndepOn R v s ↔ exists f : ι ->₀ R, f in Finsupp.
supported R R s ∧ ∑ i in f.support, f i • v i = 0 ∧ f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearDepOn_iff'`：linearDepOn_iff'ₛ : ¬LinearIndepOn R v s ↔ exists f g 
: ι ->₀ R, f in Finsupp.supported R R s ∧ g in Finsupp.supported R R s ∧ Finsupp
.linea…

--- 原说明 ---
A version of `linearDepOn_iff'ₛ` with `Finsupp.linearCombination` unfolded.
-/
theorem linearDepOn_iffₛ : ¬LinearIndepOn R v s ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        ∑ i ∈ f.support, f i • v i = ∑ i ∈ g.support, g i • v i ∧ f ≠ g :=
  linearDepOn_iff'ₛ
/-
**linearIndependent_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_restrict_iff : LinearIndependent R (s.domRestrict v) ↔ L
inearIndepOn R v s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_restrict_iff :
    LinearIndependent R (s.domRestrict v) ↔ LinearIndepOn R v s := Iff.rfl
/-
**LinearIndepOn.linearIndependent_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.linearIndependent_restrict (hs : LinearIndepOn R v s) : Line
arIndependent R (s.domRestrict v)
参数：hs : LinearIndepOn R v s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearIndepOn.linearIndependent_restrict (hs : LinearIndepOn R v s) :
    LinearIndependent R (s.domRestrict v) :=
  hs
/-
**linearIndepOn_iff_linearCombinationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff_linearCombinationOn : LinearIndepOn R v s ↔ (LinearMap.k
er <| Finsupp.linearCombinationOn ι M R v s) = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `linearIndepOn_iff_linearCombinationOnₛ`：linearIndepOn_iff_linearCombinat
ionOnₛ : LinearIndepOn R v s ↔ Injective (Finsupp.linearCombinationOn ι M R v s)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
-/
theorem linearIndepOn_iff_linearCombinationOnₛ :
    LinearIndepOn R v s ↔ Injective (Finsupp.linearCombinationOn ι M R v s) := by
  rw [← linearIndependent_restrict_iff]
  simp [LinearIndependent, Finsupp.linearCombination_restrict]

end Indexed

section repr

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
@[simps (rhsMd := default) apply_coe symm_apply]
/-
**LinearIndependent.linearCombinationEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearIndependent.linearCombinationEquiv (hv : LinearIndependent R v) : (ι
 ->₀ R) ≃ₗ[R] span R (range v)
参数：hv : LinearIndependent R v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical isomorphism between linear combinations and the span of linearly indep
endent vectors.
-/
def LinearIndependent.linearCombinationEquiv (hv : LinearIndependent R v) :
    (ι →₀ R) ≃ₗ[R] span R (range v) := by
  refine LinearEquiv.ofBijective (LinearMap.codRestrict (span R (range v))
    (Finsupp.linearCombination R v) ?_) ⟨hv.codRestrict _, ?_⟩
  · simp_rw [← Finsupp.range_linearCombination]; exact fun c ↦ ⟨c, rfl⟩
  rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, LinearMap.map_codRestrict,
    ← LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top,
    Finsupp.range_linearCombination]

/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `LinearIndependent.linearCombinationEquiv`. -/
/-
**LinearIndependent.repr** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearIndependent.repr (hv : LinearIndependent R v) : span R (range v) ->ₗ
[R] ι ->₀ R
参数：hv : LinearIndependent R v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear combination representing a vector in the span of linearly independent vec
tors.

Given a family of linearly independent vectors, we can represent any vector in t
heir span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `LinearIndependent.linearCombinationEquiv`.
-/
def LinearIndependent.repr (hv : LinearIndependent R v) : span R (range v) →ₗ[R] ι →₀ R :=
  hv.linearCombinationEquiv.symm

variable (hv : LinearIndependent R v) {i : ι}

@[simp]
/-
**LinearIndependent.linearCombination_repr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.linearCombination_repr (x) : Finsupp.linearCombination R
 v (hv.repr x) = x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem LinearIndependent.linearCombination_repr (x) :
    Finsupp.linearCombination R v (hv.repr x) = x :=
  Subtype.ext_iff.1 (LinearEquiv.apply_symm_apply hv.linearCombinationEquiv x)
/-
**LinearIndependent.linearCombination_comp_repr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.linearCombination_comp_repr : (Finsupp.linearCombination
 R v).comp hv.repr = Submodule.subtype _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearIndependent.linearCombination_repr`：LinearIndependent.linearCombin
ation_repr (x) : Finsupp.linearCombination R v (hv.repr x) = x
-/
theorem LinearIndependent.linearCombination_comp_repr :
    (Finsupp.linearCombination R v).comp hv.repr = Submodule.subtype _ :=
  LinearMap.ext <| hv.linearCombination_repr
/-
**LinearIndependent.repr_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.repr_ker : LinearMap.ker hv.repr = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.repr.eq_1`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_
4} {v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_
.Module R M] (hv …
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
-/
theorem LinearIndependent.repr_ker : LinearMap.ker hv.repr = ⊥ := by
  rw [LinearIndependent.repr, LinearEquiv.ker]
/-
**LinearIndependent.repr_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.repr_range : LinearMap.range hv.repr = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.repr.eq_1`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_
4} {v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_
.Module R M] (hv …
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
-/
theorem LinearIndependent.repr_range : LinearMap.range hv.repr = ⊤ := by
  rw [LinearIndependent.repr, LinearEquiv.range]
/-
**LinearIndependent.repr_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.repr_eq {l : ι ->₀ R} {x : span R (range v)} (eq : Finsu
pp.linearCombination R v l = ↑x) : hv.repr x = l
参数：range v；eq : Finsupp.linearCombination R v l = ↑x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem LinearIndependent.repr_eq {l : ι →₀ R} {x : span R (range v)}
    (eq : Finsupp.linearCombination R v l = ↑x) : hv.repr x = l := by
  have :
    ↑((LinearIndependent.linearCombinationEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l) =
      Finsupp.linearCombination R v l :=
    rfl
  have : (LinearIndependent.linearCombinationEquiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l = x := by
    rw [eq] at this
    exact Subtype.ext_iff.2 this
  rw [← LinearEquiv.symm_apply_apply hv.linearCombinationEquiv l]
  rw [← this]
  rfl
/-
**LinearIndependent.repr_eq_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.repr_eq_single (i) (x : span R (range v)) (hx : ↑x = v i
) : hv.repr x = Finsupp.single i 1
参数：i；x : span R (range v)；hx : ↑x = v i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.repr_eq`：LinearIndependent.repr_eq {l : ι ->₀ R} {x : 
span R (range v)} (eq : Finsupp.linearCombination R v l = ↑x) : hv.repr x = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearIndependent.repr_eq_single (i) (x : span R (range v)) (hx : ↑x = v i) :
    hv.repr x = Finsupp.single i 1 := by
  apply hv.repr_eq
  simp [Finsupp.linearCombination_single, hx]
/-
**LinearIndependent.span_repr_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.span_repr_eq [Nontrivial R] (x) : Span.repr R (Set.range
 v) x = (hv.repr x).equivMapDomain (Equiv.ofInjective _ hv.injective)
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.linearCombinationEquiv_apply_coe`：∀ {ι : Type u'} {R :
 Type u_2} {M : Type u_4} {v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoi
d M]   [inst_2 : _root_.Module R M] (hv …
· 使用定理 `Finsupp.linearCombination_equivMapDomain`：linearCombination_equivMapDoma
in (f : α ≃ α') (l : α ->₀ R) : (linearCombination R v') (equivMapDomain f l) = 
(linearCombination R (v' ∘ f))…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.self_comp_ofInjective_symm`：self_comp_ofInjective_symm {α β} {f : 
α -> β} (hf : Injective f) : f ∘ (ofInjective f hf).symm = Subtype.val
· 使用定理 `Span.finsupp_linearCombination_repr`：Span.finsupp_linearCombination_repr
 {w : Set M} (x : span R w) : Finsupp.linearCombination R ((↑) : w -> M) (Span.r
epr R w x) = x
· 使用定理 `LinearIndependent.linearCombination_repr`：LinearIndependent.linearCombin
ation_repr (x) : Finsupp.linearCombination R v (hv.repr x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.ofInjective_symm_apply`：ofInjective_symm_apply {α β} {f : α -> β} 
(hf : Injective f) (a : α) : (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a
· 使用定理 `Equiv.ofInjective_apply`：∀ {α : Sort u_3} {β : Type u_4} (f : α → β) (hf
 : Function.Injective f) (a : α), (Equiv.ofInjective f hf) a = ⟨f a, ⋯⟩
-/
theorem LinearIndependent.span_repr_eq [Nontrivial R] (x) :
    Span.repr R (Set.range v) x =
      (hv.repr x).equivMapDomain (Equiv.ofInjective _ hv.injective) := by
  have p :
    (Span.repr R (Set.range v) x).equivMapDomain (Equiv.ofInjective _ hv.injective).symm =
      hv.repr x := by
    apply (LinearIndependent.linearCombinationEquiv hv).injective
    ext
    simp only [LinearIndependent.linearCombinationEquiv_apply_coe, Equiv.self_comp_ofInjective_symm,
      LinearIndependent.linearCombination_repr, Finsupp.linearCombination_equivMapDomain,
      Span.finsupp_linearCombination_repr]
  ext ⟨_, ⟨i, rfl⟩⟩
  simp [← p]
/-
**LinearIndependent.eq_zero_of_smul_mem_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.eq_zero_of_smul_mem_span (hv : LinearIndependent R v) (i
 : ι) (a : R) (ha : a • v i in span R (v '' (univ \ {i}))) : a = 0
参数：hv : LinearIndependent R v；i : ι；a : R；ha : a • v i in span R (v '' (univ \ {
i}))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `Finsupp.span_image_eq_map_linearCombination`：span_image_eq_map_linearCom
bination (s : Set α) : span R (v '' s) = Submodule.map (linearCombination R v) (
supported R R s)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.notMem_of_mem_sdiff`：notMem_of_mem_sdiff {s t : Set α} {x : α} (h : 
x in s \ t) : x ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_iffₛ`：linearIndependent_iffₛ : LinearIndependent R v ↔
 forall l₁ l₂, Finsupp.linearCombination R v l₁ = Finsupp.linearCombination R v 
l₂ -> l₁ = l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem LinearIndependent.eq_zero_of_smul_mem_span (hv : LinearIndependent R v) (i : ι) (a : R)
    (ha : a • v i ∈ span R (v '' (univ \ {i}))) : a = 0 := by
  rw [Finsupp.span_image_eq_map_linearCombination, mem_map] at ha
  rcases ha with ⟨l, hl, e⟩
  rw [linearIndependent_iffₛ.1 hv l (Finsupp.single i a) (by simp [e])] at hl
  by_contra hn
  exact (notMem_of_mem_sdiff (hl <| by simp [hn])) (mem_singleton _)

nonrec lemma LinearIndepOn.eq_zero_of_smul_mem_span (hv : LinearIndepOn R v s) (hi : i ∈ s) (a : R)
    (ha : a • v i ∈ span R (v '' (s \ {i}))) : a = 0 :=
  hv.eq_zero_of_smul_mem_span ⟨i, hi⟩ _ <| by
    simpa [← comp_def, image_comp, image_sdiff Subtype.val_injective]

variable [Nontrivial R]
/-
**LinearIndependent.notMem_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.notMem_span (hv : LinearIndependent R v) (i : ι) : v i ∉
 span R (v '' {i}ᶜ)
参数：hv : LinearIndependent R v；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `LinearIndependent.eq_zero_of_smul_mem_span`：LinearIndependent.eq_zero_of
_smul_mem_span (hv : LinearIndependent R v) (i : ι) (a : R) (ha : a • v i in spa
n R (v '' (univ \ {i}))) : a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
-/
lemma LinearIndependent.notMem_span (hv : LinearIndependent R v) (i : ι) :
    v i ∉ span R (v '' {i}ᶜ) := fun hi ↦
  one_ne_zero <| hv.eq_zero_of_smul_mem_span i 1 <| by simpa [Set.compl_eq_univ_sdiff] using hi
/-
**LinearIndepOn.notMem_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndepOn.notMem_span (hv : LinearIndepOn R v s) (hi : i in s) : v i ∉
 span R (v '' (s \ {i}))
参数：hv : LinearIndepOn R v s；hi : i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `LinearIndepOn.eq_zero_of_smul_mem_span`：∀ {ι : Type u'} {R : Type u_2} {
s : Set ι} {M : Type u_4} {v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoi
d M]   [inst_2 : _root_.Modu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma LinearIndepOn.notMem_span (hv : LinearIndepOn R v s) (hi : i ∈ s) :
    v i ∉ span R (v '' (s \ {i})) := fun hi' ↦
  one_ne_zero <| hv.eq_zero_of_smul_mem_span hi 1 <| by simpa [Set.compl_eq_univ_sdiff] using hi'
/-
**LinearIndepOn.notMem_span_of_insert** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndepOn.notMem_span_of_insert (hv : LinearIndepOn R v (insert i s)) 
(hi : i ∉ s) : v i ∉ span R (v '' s)
参数：hv : LinearIndepOn R v (insert i s)；hi : i ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `LinearIndepOn.notMem_span`：LinearIndepOn.notMem_span (hv : LinearIndepOn
 R v s) (hi : i in s) : v i ∉ span R (v '' (s \ {i}))
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
lemma LinearIndepOn.notMem_span_of_insert (hv : LinearIndepOn R v (insert i s)) (hi : i ∉ s) :
    v i ∉ span R (v '' s) := by simpa [hi] using hv.notMem_span <| mem_insert ..

end repr

section Maximal

universe v w

/--
A linearly independent family is maximal if there is no strictly larger linearly independent family.
-/
@[nolint unusedArguments]
/-
**LinearIndependent.Maximal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearIndependent.Maximal {ι : Type w} {R : Type u} [Semiring R] {M : Type
 v} [AddCommMonoid M] [Module R M] {v : ι -> M} (_i : LinearIndependent R v) : P
rop
参数：_i : LinearIndependent R v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linearly independent family is maximal if there is no strictly larger linearly
 independent family.
-/
def LinearIndependent.Maximal {ι : Type w} {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M]
    [Module R M] {v : ι → M} (_i : LinearIndependent R v) : Prop :=
  ∀ (s : Set M) (_i' : LinearIndependent R ((↑) : s → M)) (_h : range v ≤ s), range v = s

/-- An alternative characterization of a maximal linearly independent family,
quantifying over types (in the same universe as `M`) into which the indexing family injects.
-/
/-
**LinearIndependent.maximal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.maximal_iff {ι : Type w} {R : Type u} [Semiring R] [Nont
rivial R] {M : Type v} [AddCommMonoid M] [Module R M] {v : ι -> M} (i : LinearIn
dependent R v) : i.Maximal ↔ forall (κ : Type v) (w : κ -> M) (_i' : LinearIndep
endent R w) (j : ι -> κ) (_h : w ∘ j = v), Surjective j
参数：i : LinearIndependent R v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s

--- 原说明 ---
An alternative characterization of a maximal linearly independent family,
quantifying over types (in the same universe as `M`) into which the indexing fam
ily injects.
-/
theorem LinearIndependent.maximal_iff {ι : Type w} {R : Type u} [Semiring R] [Nontrivial R]
    {M : Type v} [AddCommMonoid M] [Module R M] {v : ι → M} (i : LinearIndependent R v) :
    i.Maximal ↔
      ∀ (κ : Type v) (w : κ → M) (_i' : LinearIndependent R w) (j : ι → κ) (_h : w ∘ j = v),
        Surjective j := by
  constructor
  · rintro p κ w i' j rfl
    specialize p (range w) i'.linearIndepOn_id (range_comp_subset_range _ _)
    rw [range_comp, ← image_univ (f := w)] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p w i' h
    specialize
      p w ((↑) : w → M) i' (fun i => ⟨v i, range_subset_iff.mp h i⟩)
        (by
          ext
          simp)
    have q := congr_arg (fun s => ((↑) : w → M) '' s) p.range_eq
    rw [← image_univ, image_image] at q
    simpa using q

end Maximal

/-!
### Properties which require `LinearOrder R` and `CanonicallyOrderedAdd R`

If the semiring `R` is linearly and canonically ordered (e.g. `R = ℕ`), `LinearIndependent` can be
proved from linear combination over two disjoint sets.
-/

section LinearlyCanonicallyOrdered

variable [LinearOrder R] [CanonicallyOrderedAdd R] [AddRightReflectLE R] [IsCancelAdd M]

/-
**linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff : LinearIndependent R v ↔ forall l, Finsupp.linearCo
mbination R v l = 0 -> l = 0
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
theorem linearIndependent_iffₒₛ :
    LinearIndependent R v ↔
      ∀ (s t : Finset ι) (f : ι → R), Disjoint s t →
        ∑ i ∈ s, f i • v i = ∑ i ∈ t, f i • v i → (∀ i ∈ s, f i = 0) ∧ ∀ i ∈ t, f i = 0 := by
  classical
  let : Sub R := CanonicallyOrderedAdd.toSub
  have : OrderedSub R := CanonicallyOrderedAdd.toOrderedSub
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s t f hst heq => ?_, fun h s f g heq => ?_⟩
  · specialize h (s ∪ t) (fun i => if i ∈ s then f i else 0) (fun i => if i ∈ t then f i else 0) ?_
    · simpa
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simpa [hi, hst.notMem_of_mem_left_finset hi] using h i (Finset.mem_union_left _ hi)
    · simpa [hi, hst.notMem_of_mem_right_finset hi] using (h i (Finset.mem_union_right _ hi)).symm
  · specialize h { i ∈ s | g i ≤ f i } { i ∈ s | f i < g i }
      (fun i => if g i ≤ f i then f i - g i else g i - f i) ?_ ?_
    · simp_rw [Finset.disjoint_left, Finset.mem_filter]
      exact fun i ⟨_, hi⟩ ⟨_, hi'⟩ => hi.not_gt hi'
    · rw [← add_right_cancel_iff
        (a := ∑ i ∈ s with g i ≤ f i, g i • v i + ∑ i ∈ s with f i < g i, f i • v i)]
      conv_lhs => rw [← add_assoc, ← Finset.sum_add_distrib]
      conv_rhs => rw [add_left_comm, ← Finset.sum_add_distrib]
      convert! heq
        <;> simp_rw [← Finset.sum_filter_add_sum_filter_not s (fun i => g i ≤ f i), not_le]
        <;> congr! 2 with i hi
        <;> simp only [Finset.mem_filter] at hi
      · simp [hi.2, ← add_smul, tsub_add_cancel_of_le hi.2]
      · simp [hi.2.not_ge, ← add_smul, tsub_add_cancel_of_le hi.2.le]
    simp only [Finset.mem_filter] at h
    intro i hi
    by_cases hi' : g i ≤ f i
    · apply hi'.antisymm'
      simpa [hi', tsub_eq_zero_iff_le] using h.1 i ⟨hi, hi'⟩
    · apply (not_le.1 hi').le.antisymm
      simpa [hi', tsub_eq_zero_iff_le] using h.2 i ⟨hi, not_le.1 hi'⟩
/-
**not_linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_linearIndependent_iff : ¬LinearIndependent R v ↔ exists s : Finset ι, 
exists g : ι -> R, ∑ i in s, g i • v i = 0 ∧ exists i in s, g i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_linearIndependent_iffₒₛ :
    ¬ LinearIndependent R v ↔
      ∃ (s t : Finset ι) (f : ι → R),
        Disjoint s t ∧ ∑ i ∈ s, f i • v i = ∑ i ∈ t, f i • v i ∧ ∃ i ∈ s, 0 < f i := by
  simp only [linearIndependent_iffₒₛ, pos_iff_ne_zero]
  push +distrib Not
  refine ⟨fun ⟨s, t, f, hst, heq, h⟩ => ?_,
    fun ⟨s, t, f, hst, heq, hi⟩ => ⟨s, t, f, hst, heq, .inl hi⟩⟩
  rcases h with ⟨i, hi, hfi⟩ | ⟨i, hi, hgi⟩
  · exact ⟨s, t, f, hst, heq, i, hi, hfi⟩
  · exact ⟨t, s, f, hst.symm, heq.symm, i, hi, hgi⟩

nonrec theorem Fintype.linearIndependent_iffₒₛ [DecidableEq ι] [Fintype ι] :
    LinearIndependent R v ↔ ∀ t, ∀ (f : ι → R),
      ∑ i ∈ t, f i • v i = ∑ i ∉ t, f i • v i → ∀ i, f i = 0 := by
  rw [linearIndependent_iffₒₛ]
  refine ⟨fun h t f heq i => ?_, fun h t₁ t₂ f ht₁t₂ heq => ?_⟩
  · specialize h t tᶜ f disjoint_compl_right heq
    by_cases hi : i ∈ t
    · exact h.1 i hi
    · exact h.2 i (Finset.mem_compl.2 hi)
  · specialize h t₁ (fun i => if i ∈ t₁ ∨ i ∈ t₂ then f i else 0) ?_
    · rw [← Finset.sum_subset ht₁t₂.le_compl_left]
      · convert! heq using 2 with i hi i hi <;> simp [hi]
      · intro i hi hi'
        simp [Finset.mem_compl.1 hi, hi']
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;> simpa [hi] using h i
/-
**Fintype.not_linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.not_linearIndependent_iff [Fintype ι] : ¬LinearIndependent R v ↔ e
xists g : ι -> R, ∑ i, g i • v i = 0 ∧ exists i, g i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
-/
theorem Fintype.not_linearIndependent_iffₒₛ [DecidableEq ι] [Fintype ι] :
    ¬ LinearIndependent R v ↔ ∃ t, ∃ (f : ι → R),
      ∑ i ∈ t, f i • v i = ∑ i ∉ t, f i • v i ∧ ∃ i ∈ t, 0 < f i := by
  simp only [linearIndependent_iffₒₛ, not_forall, pos_iff_ne_zero]
  refine ⟨fun ⟨t, f, heq, i, hfi⟩ => ?_, fun ⟨t, f, heq, i, hi, hfi⟩ =>
    ⟨t, f, heq, i, hfi⟩⟩
  by_cases hi' : i ∈ t
  · exact ⟨t, f, heq, i, hi', hfi⟩
  · refine ⟨tᶜ, f, ?_, i, Finset.mem_compl.2 hi', hfi⟩
    simp [heq]

set_option backward.isDefEq.respectTransparency false in
/-
**linearIndepOn_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndepOn_finset_iff {s : Finset ι} : LinearIndepOn R v s ↔ forall f :
 ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) 
[inst_1 : Decidable p] (a : α) (b : p → β) (c : ¬p → β),   (if h : p then b h e…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
lemma linearIndepOn_finset_iffₒₛ [DecidableEq ι] {s : Finset ι} :
    LinearIndepOn R v s ↔ ∀ t ⊆ s, ∀ (f : ι → R),
      ∑ i ∈ t, f i • v i = ∑ i ∈ s \ t, f i • v i → ∀ i ∈ s, f i = 0 := by
  rw [LinearIndepOn, Fintype.linearIndependent_iffₒₛ]
  refine ⟨fun h t ht f heq i hi => h { i | i.1 ∈ t } (f ∘ Subtype.val) ?_ ⟨i, hi⟩,
    fun h t f heq i => ?_⟩
  · simp only [Finset.compl_filter, Finset.sum_filter, Function.comp_apply, Finset.coe_sort_coe]
    rw [Finset.sum_coe_sort s fun i => if i ∈ t then f i • v i else 0,
      Finset.sum_coe_sort s fun i => if i ∉ t then f i • v i else 0]
    simpa [Finset.inter_eq_right.2 ht, Finset.sum_ite, Finset.filter_notMem_eq_sdiff]
  · specialize h (t.map (Embedding.subtype _)) (Finset.map_subtype_subset _)
      (fun i => if h : i ∈ s then f ⟨i, h⟩ else 0) ?_ i i.2
    · conv =>
        enter [2, 1, 1]
        rw [← s.subtype_map_of_mem (fun x hx => hx), Finset.subtype_eq_univ.2 (fun x hx => hx)]
        change Finset.map (Embedding.subtype (· ∈ (s : Set ι))) _
      rw [← Finset.map_sdiff]
      simpa [Embedding.subtype, ← Finset.compl_eq_univ_sdiff]
    simpa using h
/-
**not_linearIndepOn_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_linearIndepOn_finset_iff {s : Finset ι} : ¬LinearIndepOn R v s ↔ exist
s f : ι -> R, ∑ i in s, f i • v i = 0 ∧ exists i in s, f i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `linearIndepOn_finset_iff`：linearIndepOn_finset_iff {s : Finset ι} : Line
arIndepOn R v s ↔ forall f : ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f
 i = 0
-/
lemma not_linearIndepOn_finset_iffₒₛ [DecidableEq ι] {s : Finset ι} :
    ¬LinearIndepOn R v s ↔ ∃ t ⊆ s, ∃ (f : ι → R),
      ∑ i ∈ t, f i • v i = ∑ i ∈ s \ t, f i • v i ∧ ∃ i ∈ t, 0 < f i := by
  simp only [linearIndepOn_finset_iffₒₛ, not_forall, pos_iff_ne_zero]
  refine ⟨fun ⟨t, hst, f, heq, i, hi, hfi⟩ => ?_,
    fun ⟨t, hst, f, heq, i, hi, hfi⟩ => ⟨t, hst, f, heq, i, hst hi, hfi⟩⟩
  by_cases hi' : i ∈ t
  · exact ⟨t, hst, f, heq, i, hi', hfi⟩
  · refine ⟨s \ t, Finset.sdiff_subset, f, ?_, i, Finset.mem_sdiff.2 ⟨hi, hi'⟩, hfi⟩
    simpa [Finset.sdiff_sdiff_eq_self hst] using heq.symm

end LinearlyCanonicallyOrdered

end Semiring

/-! ### Properties which require `Ring R` -/

section Module

variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']
variable {v : ι → M} {i : ι}

/-
**LinearIndependent.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.neg (hv : LinearIndependent R v) : LinearIndependent R (
-v)
参数：hv : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Finsupp.sum_neg`：∀ {α : Type u_1} {M : Type u_8} {G : Type u_12} [inst :
 Zero M] [inst_1 : AddCommGroup G] {f : α →₀ M} {h : α → M → G},   (f.sum fun a 
b => …
-/
theorem LinearIndependent.neg (hv : LinearIndependent R v) : LinearIndependent R (-v) := by
  intro f g h
  simp only [Finsupp.linearCombination_apply, Pi.neg_apply, smul_neg, Finsupp.sum_neg, neg_inj] at h
  ext m
  exact DFunLike.congr_fun (hv h) m
/-
**linearIndependent_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} [inst : Ring R] [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {v : ι → M}, LinearIndependent R (-
v) ↔ LinearIndependent R v
参数：-v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `LinearIndependent.neg`：LinearIndependent.neg (hv : LinearIndependent R v
) : LinearIndependent R (-v)
-/
@[simp] theorem linearIndependent_neg_iff :
    LinearIndependent R (-v) ↔ LinearIndependent R v := by
  refine ⟨fun h ↦ ?_, LinearIndependent.neg⟩
  simpa using h.neg
/-
**linearIndependent_iff_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff_ker : LinearIndependent R v ↔ LinearMap.ker (Finsupp
.linearCombination R v) = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
-/
theorem linearIndependent_iff_ker :
    LinearIndependent R v ↔ LinearMap.ker (Finsupp.linearCombination R v) = ⊥ :=
  LinearMap.ker_eq_bot.symm
/-
**linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff : LinearIndependent R v ↔ forall l, Finsupp.linearCo
mbination R v l = 0 -> l = 0
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
theorem linearIndependent_iff :
    LinearIndependent R v ↔ ∀ l, Finsupp.linearCombination R v l = 0 → l = 0 := by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']

/-- A version of `linearIndependent_iff` where the linear combination is a `Finset` sum. -/
/-
**linearIndependent_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff'ₛ : LinearIndependent R v ↔ forall s : Finset ι, for
all f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i • v i -> forall i in s, f 
i = g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'ₛ`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} {
v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mod
ule R M],   L…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
A version of `linearIndependent_iff` where the linear combination is a `Finset` 
sum.
-/
theorem linearIndependent_iff' :
    LinearIndependent R v ↔
      ∀ s : Finset ι, ∀ g : ι → R, ∑ i ∈ s, g i • v i = 0 → ∀ i ∈ s, g i = 0 := by
  rw [linearIndependent_iff'ₛ]
  refine ⟨fun h s f ↦ ?_, fun h s f g ↦ ?_⟩
  · convert! h s f 0; simp_rw [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    convert! h s (f - g) using 3; simp only [Pi.sub_apply, sub_smul, sub_eq_zero]

/-- A version of `linearIndependent_iff` where the linear combination is a `Finset` sum
of a function with support contained in the `Finset`. -/
/-
**linearIndependent_iff''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff''ₛ : LinearIndependent R v ↔ forall (s : Finset ι) (
f g : ι -> R), (forall i ∉ s, f i = g i) -> ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> forall i, f i = g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_extend_by_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M),   (∑ i ∈ s, if 
i ∈ s then f i …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of `linearIndependent_iff` where the linear combination is a `Finset` 
sum
of a function with support contained in the `Finset`.
-/
theorem linearIndependent_iff'' :
    LinearIndependent R v ↔
      ∀ (s : Finset ι) (g : ι → R), (∀ i ∉ s, g i = 0) → ∑ i ∈ s, g i • v i = 0 → ∀ i, g i = 0 := by
  classical
  exact linearIndependent_iff'.trans
    ⟨fun H s g hg hv i => if his : i ∈ s then H s g hv i his else hg i his, fun H s g hg i hi => by
      convert!
        H s (fun j => if j ∈ s then g j else 0) (fun j hj => if_neg hj)
          (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg]) i
      exact (if_pos hi).symm⟩
/-
**linearIndependent_add_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_add_smul_iff {c : ι -> R} {i : ι} (h₀ : c i = 0) : Linea
rIndependent R (v + (c · • v i)) ↔ LinearIndependent R v
参数：h₀ : c i = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.linearCombination_comp_addSingleEquiv`：Finsupp.linearCombination
_comp_addSingleEquiv (v : ι -> M) : linearCombination R v ∘ₗ addSingleEquiv i c 
h₀ = linearCombination R (v + (c · …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem linearIndependent_add_smul_iff {c : ι → R} {i : ι} (h₀ : c i = 0) :
    LinearIndependent R (v + (c · • v i)) ↔ LinearIndependent R v := by
  simp [linearIndependent_iff_injective_finsuppLinearCombination,
    ← Finsupp.linearCombination_comp_addSingleEquiv i c h₀]
/-
**not_linearIndependent_iff_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_linearIndependent_iff_linearCombination : ¬LinearIndependent R v ↔ exi
sts l, (Finsupp.linearCombination R v) l = 0 ∧ l != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_linearIndependent_iff_linearCombination :
    ¬LinearIndependent R v ↔ ∃ l, (Finsupp.linearCombination R v) l = 0 ∧ l ≠ 0 := by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot']
/-
**not_linearIndependent_iff_finsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_linearIndependent_iff_finsupp : ¬LinearIndependent R v ↔ exists (f : ι
 ->₀ R), f.sum (fun x r => r • v x) = 0 ∧ f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_linearIndependent_iff_finsupp :
    ¬LinearIndependent R v ↔ ∃ (f : ι →₀ R), f.sum (fun x r ↦ r • v x) = 0 ∧ f ≠ 0 := by
  simp [linearIndependent_iff_ker, LinearMap.ker_eq_bot', Finsupp.linearCombination]
/-
**not_linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_linearIndependent_iff : ¬LinearIndependent R v ↔ exists s : Finset ι, 
exists g : ι -> R, ∑ i in s, g i • v i = 0 ∧ exists i in s, g i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_linearIndependent_iff :
    ¬LinearIndependent R v ↔
      ∃ s : Finset ι, ∃ g : ι → R, ∑ i ∈ s, g i • v i = 0 ∧ ∃ i ∈ s, g i ≠ 0 := by
  rw [linearIndependent_iff']
  simp only [exists_prop, not_forall]
/-
**Fintype.linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.linearIndependent_iff [Fintype ι] : LinearIndependent R v ↔ forall
 g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff''`：linearIndependent_iff''ₛ : LinearIndependent R 
v ↔ forall (s : Finset ι) (f g : ι -> R), (forall i ∉ s, f i = g i) -> ∑ i in s,
 f i • v i = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem Fintype.linearIndependent_iff [Fintype ι] :
    LinearIndependent R v ↔ ∀ g : ι → R, ∑ i, g i • v i = 0 → ∀ i, g i = 0 := by
  refine
    ⟨fun H g => by simpa using linearIndependent_iff'.1 H Finset.univ g, fun H =>
      linearIndependent_iff''.2 fun s g hg hs i => H _ ?_ _⟩
  rw [← hs]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hg i hi, zero_smul]
/-
**Fintype.not_linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.not_linearIndependent_iff [Fintype ι] : ¬LinearIndependent R v ↔ e
xists g : ι -> R, ∑ i, g i • v i = 0 ∧ exists i, g i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
-/
theorem Fintype.not_linearIndependent_iff [Fintype ι] :
    ¬LinearIndependent R v ↔ ∃ g : ι → R, ∑ i, g i • v i = 0 ∧ ∃ i, g i ≠ 0 := by
  simpa using not_iff_not.2 Fintype.linearIndependent_iff
/-
**linearIndepOn_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndepOn_finset_iff {s : Finset ι} : LinearIndepOn R v s ↔ forall f :
 ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) 
[inst_1 : Decidable p] (a : α) (b : p → β) (c : ¬p → β),   (if h : p then b h e…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
lemma linearIndepOn_finset_iff {s : Finset ι} :
    LinearIndepOn R v s ↔ ∀ f : ι → R, ∑ i ∈ s, f i • v i = 0 → ∀ i ∈ s, f i = 0 := by
  classical
  simp_rw [LinearIndepOn, Fintype.linearIndependent_iff]
  constructor
  · rintro hv f hf i hi
    rw [← s.sum_attach] at hf
    exact hv (f ∘ Subtype.val) hf ⟨i, hi⟩
  · rintro hv f hf₀ i
    simpa using hv (fun j ↦ if hj : j ∈ s then f ⟨j, hj⟩ else 0)
      (by simpa +contextual [← s.sum_attach]) i
/-
**not_linearIndepOn_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_linearIndepOn_finset_iff {s : Finset ι} : ¬LinearIndepOn R v s ↔ exist
s f : ι -> R, ∑ i in s, f i • v i = 0 ∧ exists i in s, f i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `linearIndepOn_finset_iff`：linearIndepOn_finset_iff {s : Finset ι} : Line
arIndepOn R v s ↔ forall f : ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f
 i = 0
-/
lemma not_linearIndepOn_finset_iff {s : Finset ι} :
    ¬LinearIndepOn R v s ↔ ∃ f : ι → R, ∑ i ∈ s, f i • v i = 0 ∧ ∃ i ∈ s, f i ≠ 0 := by
  simpa using linearIndepOn_finset_iff.not

/-- If the kernel of a linear map is disjoint from the span of a family of vectors,
then the family is linearly independent iff it is linearly independent after composing with
the linear map. -/
/-
**LinearMap.linearIndependent_iff_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} {M' : Type u_5} [inst : Ring
 R] [inst_1 : AddCommGroup M]   [inst_2 : AddCommGroup M'] [inst_3 : _root_.Modu
le R M] [inst_4 : _root_.Module R M'] {v : ι → M} (f : M →ₗ[R] M'),   Disjoint (
Submodule.span R (Set.range v)) f.ker → (LinearIndependent R (⇑f ∘ v) ↔ LinearIn
dependent R v)
参数：f : M →ₗ[R] M'；Submodule.span R (Set.range v)；LinearIndependent R (⇑f ∘ v) ↔ 
LinearIndependent R v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `LinearMap.injOn_of_disjoint_ker`：injOn_of_disjoint_ker {p : Submodule R 
M} {s : Set M} (h : s subseteq p) (hd : Disjoint p (ker f)) : Set.InjOn f s
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If the kernel of a linear map is disjoint from the span of a family of vectors,
then the family is linearly independent iff it is linearly independent after com
posing with
the linear map.
-/
protected theorem LinearMap.linearIndependent_iff_of_disjoint (f : M →ₗ[R] M')
    (hf_inj : Disjoint (span R (Set.range v)) (LinearMap.ker f)) :
    LinearIndependent R (f ∘ v) ↔ LinearIndependent R v :=
  f.linearIndependent_iff_of_injOn <| LinearMap.injOn_of_disjoint_ker le_rfl hf_inj

section LinearIndepOn

/-! The following give equivalent versions of `LinearIndepOn` and its negation. -/

/-
**linearIndepOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff : LinearIndepOn R v s ↔ forall l in Finsupp.supported R 
R s, (Finsupp.linearCombination R v) l = 0 -> l = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `linearIndepOn_iffₛ`：linearIndepOn_iffₛ : LinearIndepOn R v s ↔ forall f 
in Finsupp.supported R R s, forall g in Finsupp.supported R R s, Finsupp.linearC
ombinati…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
The following give equivalent versions of `LinearIndepOn` and its negation.
-/
theorem linearIndepOn_iff : LinearIndepOn R v s ↔
      ∀ l ∈ Finsupp.supported R R s, (Finsupp.linearCombination R v) l = 0 → l = 0 :=
  linearIndepOn_iffₛ.trans ⟨fun h l hl ↦ h l hl 0 (zero_mem _), fun h f hf g hg eq ↦
    sub_eq_zero.mp (h (f - g) (sub_mem hf hg) <| by rw [map_sub, eq, sub_self])⟩

/-- An indexed set of vectors is linearly dependent iff there is a nontrivial
`Finsupp.linearCombination` of the vectors that is zero. -/
/-
**linearDepOn_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearDepOn_iff'ₛ : ¬LinearIndepOn R v s ↔ exists f g : ι ->₀ R, f in Fins
upp.supported R R s ∧ g in Finsupp.supported R R s ∧ Finsupp.linearCombination R
 v f = Finsupp.linearCombination R v g ∧ f != g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An indexed set of vectors is linearly dependent iff there is a nontrivial
`Finsupp.linearCombination` of the vectors that is zero.
-/
theorem linearDepOn_iff' : ¬LinearIndepOn R v s ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ Finsupp.linearCombination R v f = 0 ∧ f ≠ 0 := by
  simp [linearIndepOn_iff]

/-- A version of `linearDepOn_iff'` with `Finsupp.linearCombination` unfolded. -/
/-
**linearDepOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearDepOn_iff : ¬LinearIndepOn R v s ↔ exists f : ι ->₀ R, f in Finsupp.
supported R R s ∧ ∑ i in f.support, f i • v i = 0 ∧ f != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearDepOn_iff'`：linearDepOn_iff'ₛ : ¬LinearIndepOn R v s ↔ exists f g 
: ι ->₀ R, f in Finsupp.supported R R s ∧ g in Finsupp.supported R R s ∧ Finsupp
.linea…

--- 原说明 ---
A version of `linearDepOn_iff'` with `Finsupp.linearCombination` unfolded.
-/
theorem linearDepOn_iff : ¬LinearIndepOn R v s ↔
      ∃ f : ι →₀ R, f ∈ Finsupp.supported R R s ∧ ∑ i ∈ f.support, f i • v i = 0 ∧ f ≠ 0 :=
  linearDepOn_iff'
/-
**linearIndepOn_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff_disjoint : LinearIndepOn R v s ↔ Disjoint (Finsupp.suppo
rted R R s) (LinearMap.ker <| Finsupp.linearCombination R v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndepOn_iff`：linearIndepOn_iff : LinearIndepOn R v s ↔ forall l in
 Finsupp.supported R R s, (Finsupp.linearCombination R v) l = 0 -> l = 0
· 使用定理 `LinearMap.disjoint_ker`：disjoint_ker {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule
 R M} : Disjoint p (ker f) ↔ forall x in p, f x = 0 -> x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndepOn_iff_disjoint : LinearIndepOn R v s ↔
      Disjoint (Finsupp.supported R R s) (LinearMap.ker <| Finsupp.linearCombination R v) := by
  rw [linearIndepOn_iff, LinearMap.disjoint_ker]
/-
**linearIndepOn_iff_linearCombinationOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff_linearCombinationOn : LinearIndepOn R v s ↔ (LinearMap.k
er <| Finsupp.linearCombinationOn ι M R v s) = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `linearIndepOn_iff_linearCombinationOnₛ`：linearIndepOn_iff_linearCombinat
ionOnₛ : LinearIndepOn R v s ↔ Injective (Finsupp.linearCombinationOn ι M R v s)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
-/
theorem linearIndepOn_iff_linearCombinationOn :
    LinearIndepOn R v s ↔ (LinearMap.ker <| Finsupp.linearCombinationOn ι M R v s) = ⊥ :=
  linearIndepOn_iff_linearCombinationOnₛ.trans <|
    LinearMap.ker_eq_bot (M := Finsupp.supported R R s).symm

/-- A version of `linearIndepOn_iff` where the linear combination is a `Finset` sum. -/
/-
**linearIndepOn_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff' : LinearIndepOn R v s ↔ forall (t : Finset ι) (g : ι ->
 R), (t : Set ι) subseteq s -> ∑ i in t, g i • v i = 0 -> forall i in t, g i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndepOn.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v : ι
 → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] (s :…
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Finset.sum_preimage`：∀ {ι : Type u_1} {κ : Type u_2} {β : Type u_3} [ins
t : AddCommMonoid β] (f : ι → κ) (s : Finset κ)   (hf : Set.InjOn f (f ⁻¹' ↑s)) 
(g : κ → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `dite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) 
[inst_1 : Decidable p] (a : α) (b : p → β) (c : ¬p → β),   (if h : p then b h e…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
A version of `linearIndepOn_iff` where the linear combination is a `Finset` sum.
-/
lemma linearIndepOn_iff' : LinearIndepOn R v s ↔ ∀ (t : Finset ι) (g : ι → R), (t : Set ι) ⊆ s →
    ∑ i ∈ t, g i • v i = 0 → ∀ i ∈ t, g i = 0 := by
  classical
  rw [LinearIndepOn, linearIndependent_iff']
  refine ⟨fun h t g hts h0 i hit ↦ ?_, fun h t g h0 i hit ↦ ?_⟩
  · refine h (t.preimage _ Subtype.val_injective.injOn) (fun i ↦ g i) ?_ ⟨i, hts hit⟩ (by simpa)
    rwa [t.sum_preimage ((↑) : s → ι) Subtype.val_injective.injOn (fun i ↦ g i • v i)]
    simp only [Subtype.range_coe_subtype, ofPred_mem_eq]
    exact fun x hxt hxs ↦ (hxs (hts hxt)) |>.elim
  replace h : ∀ i (hi : i ∈ s), ⟨i, hi⟩ ∈ t → ∀ (h : i ∈ s), g ⟨i, h⟩ = 0 := by
    simpa [h0] using h (t.image (↑)) (fun i ↦ if hi : i ∈ s then g ⟨i, hi⟩ else 0)
  apply h _ _ hit

/-- A version of `linearIndepOn_iff` where the linear combination is a `Finset` sum
of a function with support contained in the `Finset`. -/
/-
**linearIndepOn_iff''** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff'' : LinearIndepOn R v s ↔ forall (t : Finset ι) (g : ι -
> R), (t : Set ι) subseteq s -> (forall i ∉ t, g i = 0) -> ∑ i in t, g i • v i =
 0 -> forall i in t, g i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `linearIndepOn_iff'`：linearIndepOn_iff' : LinearIndepOn R v s ↔ forall (t
 : Finset ι) (g : ι -> R), (t : Set ι) subseteq s -> ∑ i in t, g i • v i = 0 -> 
forall i…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A version of `linearIndepOn_iff` where the linear combination is a `Finset` sum
of a function with support contained in the `Finset`.
-/
lemma linearIndepOn_iff'' : LinearIndepOn R v s ↔ ∀ (t : Finset ι) (g : ι → R), (t : Set ι) ⊆ s →
    (∀ i ∉ t, g i = 0) → ∑ i ∈ t, g i • v i = 0 → ∀ i ∈ t, g i = 0 := by
  classical
  exact linearIndepOn_iff'.trans ⟨fun h t g hts htg h0 ↦ h _ _ hts h0, fun h t g hts h0 ↦
    by simpa +contextual [h0] using h t (fun i ↦ if i ∈ t then g i else 0) hts⟩

end LinearIndepOn

open LinearMap

/-
**linearIndependent_iff_eq_zero_of_smul_mem_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff_eq_zero_of_smul_mem_span : LinearIndependent R v ↔ f
orall (i : ι) (a : R), a • v i in span R (v '' (univ \ {i})) -> a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.eq_zero_of_smul_mem_span`：LinearIndependent.eq_zero_of
_smul_mem_span (hv : LinearIndependent R v) (i : ι) (a : R) (ha : a • v i in spa
n R (v '' (univ \ {i}))) : a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_supported'`：mem_supported' {s : Set α} (p : α ->₀ M) : p in 
supported M R s ↔ forall x ∉ s, p x = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem linearIndependent_iff_eq_zero_of_smul_mem_span :
    LinearIndependent R v ↔ ∀ (i : ι) (a : R), a • v i ∈ span R (v '' (univ \ {i})) → a = 0 :=
  ⟨fun hv ↦ hv.eq_zero_of_smul_mem_span, fun H =>
    linearIndependent_iff.2 fun l hl => by
      ext i; simp only [Finsupp.zero_apply]
      by_contra hn
      refine hn (H i _ ?_)
      refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨Finsupp.single i (l i) - l, ?_, ?_⟩
      · rw [Finsupp.mem_supported']
        intro j hj
        have hij : j = i :=
          Classical.not_not.1 fun hij : j ≠ i =>
            hj ((mem_sdiff _).2 ⟨mem_univ _, fun h => hij (eq_of_mem_singleton h)⟩)
        simp [hij]
      · simp [hl]⟩

/-- Version of `LinearIndependent.of_subsingleton` that works for the zero ring. -/
/-
**LinearIndependent.of_subsingleton'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.of_subsingleton' [Subsingleton ι] (i : ι) (hi : forall r
 : R, r • v i = 0 -> r = 0) : LinearIndependent R v
参数：i : ι；hi : forall r : R, r • v i = 0 -> r = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_unique`：linearCombination_unique [Unique α] (l
 : α ->₀ R) (v : α -> M) : linearCombination R v l = l default • v default

--- 原说明 ---
Version of `LinearIndependent.of_subsingleton` that works for the zero ring.
-/
lemma LinearIndependent.of_subsingleton' [Subsingleton ι] (i : ι)
    (hi : ∀ r : R, r • v i = 0 → r = 0) : LinearIndependent R v := by
  let := uniqueOfSubsingleton i
  simpa [linearIndependent_iff, Finsupp.linearCombination_unique, Finsupp.ext_iff,
    Unique.forall_iff] using! fun _ ↦ hi _

/-- Version of `LinearIndepOn.singleton` that works for the zero ring. -/
@[simp]
/-
**LinearIndepOn.singleton'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndepOn.singleton' (hi : forall r : R, r • v i = 0 -> r = 0) : Linea
rIndepOn R v {i}
参数：hi : forall r : R, r • v i = 0 -> r = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndependent.of_subsingleton'`：LinearIndependent.of_subsingleton' [
Subsingleton ι] (i : ι) (hi : forall r : R, r • v i = 0 -> r = 0) : LinearIndepe
ndent R v
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
Version of `LinearIndepOn.singleton` that works for the zero ring.
-/
lemma LinearIndepOn.singleton' (hi : ∀ r : R, r • v i = 0 → r = 0) : LinearIndepOn R v {i} :=
  LinearIndependent.of_subsingleton' ⟨i, rfl⟩ hi

variable [IsDomain R] [IsTorsionFree R M]
/-
**LinearIndependent.of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.of_subsingleton [Subsingleton ι] (i : ι) (hi : v i != 0)
 : LinearIndependent R v
参数：i : ι；hi : v i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndependent.of_subsingleton'`：LinearIndependent.of_subsingleton' [
Subsingleton ι] (i : ι) (hi : forall r : R, r • v i = 0 -> r = 0) : LinearIndepe
ndent R v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma LinearIndependent.of_subsingleton [Subsingleton ι] (i : ι) (hi : v i ≠ 0) :
    LinearIndependent R v := .of_subsingleton' i (by simp [hi])
/-
**LinearIndepOn.singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndepOn.singleton (hi : v i != 0) : LinearIndepOn R v {i}
参数：hi : v i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma LinearIndepOn.singleton (hi : v i ≠ 0) : LinearIndepOn R v {i} := by simp [hi]

end Module

/-!
### Properties which require `DivisionRing K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable {v : ι → V} {s t : Set ι} {x y : V}

open Submodule

/-
**linearIndependent_iff_notMem_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff_notMem_span : LinearIndependent K v ↔ forall i, v i 
∉ span K (v '' (univ \ {i}))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `linearIndependent_iff_eq_zero_of_smul_mem_span`：linearIndependent_iff_eq
_zero_of_smul_mem_span : LinearIndependent R v ↔ forall (i : ι) (a : R), a • v i
 in span R (v '' (univ \ {i})) -> a …
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
-/
theorem linearIndependent_iff_notMem_span :
    LinearIndependent K v ↔ ∀ i, v i ∉ span K (v '' (univ \ {i})) := by
  apply linearIndependent_iff_eq_zero_of_smul_mem_span.trans
  constructor
  · intro h i h_in_span
    apply one_ne_zero (h i 1 (by simp [h_in_span]))
  · intro h i a ha
    by_contra ha'
    exact False.elim (h _ ((smul_mem_iff _ ha').1 ha))
/-
**linearIndepOn_iff_notMem_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：linearIndepOn_iff_notMem_span : LinearIndepOn K v s ↔ forall i in s, v i ∉
 span K (v '' (s \ {i}))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndepOn.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v : ι
 → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] (s :…
· 使用定理 `linearIndependent_iff_notMem_span`：linearIndependent_iff_notMem_span : L
inearIndependent K v ↔ forall i, v i ∉ span K (v '' (univ \ {i}))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma linearIndepOn_iff_notMem_span :
    LinearIndepOn K v s ↔ ∀ i ∈ s, v i ∉ span K (v '' (s \ {i})) := by
  rw [LinearIndepOn, linearIndependent_iff_notMem_span, ← Function.comp_def]
  simp_rw [Set.image_comp]
  simp [Set.image_sdiff Subtype.val_injective]

end Module

