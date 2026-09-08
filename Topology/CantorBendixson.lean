/-
Copyright (c) 2026 Zikang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zikang Yu
-/
module

public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FixedPointApproximants
public import Mathlib.Topology.DerivedSet

/-!
# Cantor-Bendixson derivatives and perfect kernel

This file defines the transfinite iteration of the relative derived-set operator
and the associated perfect kernel.

For closed sets, the relative derived set agrees with `derivedSet`, so this recovers the usual
Cantor-Bendixson derivative sequence of a closed set.

## Main definitions

* `CantorBendixson.iteratedDerivedSet s a`: the `a`-th transfinite iterate of `relDerivedSet`
  starting from `s`.
* `CantorBendixson.perfectKernel s`: the largest perfect subset of `s`, defined as the
  intersection of all iterated derived sets of `s`.

## Main statements

* `CantorBendixson.iteratedDerivedSet_constant_iff_preperfect`: a set is preperfect if and only
  if every iterated derived set is equal to the original set.
* `CantorBendixson.iteratedDerivedSet_stay`: the iterated derived-set sequence eventually
  stabilizes.
* `CantorBendixson.perfect_perfectKernel`: the perfect kernel of a closed set is perfect.
* `CantorBendixson.subset_perfectKernel_of_perfect`: the perfect kernel is the largest perfect
  subset.

## Notation

* `sᵈ[a]`: the `a`-th iterated relative derived set of `s`.

## Implementation notes

* We define `iteratedDerivedSet` using `OrdinalApprox.gfpApprox` applied to `relDerivedSet`.
  This keeps the transfinite sequence antitone for arbitrary sets.
* If `s` is closed, then `relDerivedSet s = derivedSet s`, so successor stages agree with the
  ambient derived-set operator.

## TODO

* Pointwise and setwise Cantor-Bendixson ranks.
* A generalized Cantor-Bendixson decomposition theorem for arbitrary topological spaces and
  arbitrary cardinalities of topological bases.

-/

@[expose] public section

open Filter Set Cardinal OrdinalApprox Function

universe u

namespace CantorBendixson

section

variable {X : Type u} [TopologicalSpace X]

/-- The transfinite iteration of the relative derived-set operator on a set. -/
/-
**CantorBendixson.iteratedDerivedSet** 是 Mathlib 中的一个定义，位于命名空间 `CantorBendixson`
。
形式化陈述：iteratedDerivedSet (s : Set X) : Ordinal -> Set X
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transfinite iteration of the relative derived-set operator on a set.
-/
def iteratedDerivedSet (s : Set X) : Ordinal → Set X :=
  gfpApprox relDerivedSet s

@[inherit_doc CantorBendixson.iteratedDerivedSet]
scoped[CantorBendixson] notation:max s "ᵈ[" a "]" => iteratedDerivedSet s a

variable {s t : Set X} {a b : Ordinal}

@[simp]
/-
**CantorBendixson.iteratedDerivedSet_zero** 是 Mathlib 中的一个定理，位于命名空间 `CantorBendi
xson`。
形式化陈述：iteratedDerivedSet_zero : sᵈ[0] = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrdinalApprox.gfpApprox_zero`：gfpApprox_zero : gfpApprox f x 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivedSet_zero :
    sᵈ[0] = s := by
  simp [iteratedDerivedSet, gfpApprox_zero]

@[simp]
/-
**CantorBendixson.iteratedDerivedSet_succ** 是 Mathlib 中的一个定理，位于命名空间 `CantorBendi
xson`。
形式化陈述：iteratedDerivedSet_succ : sᵈ[a + 1] = relDerivedSet (sᵈ[a])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.gfpApprox_add_one`：gfpApprox_add_one (hx : f x <= x) (a : 
Ordinal) : gfpApprox f x (a + 1) = f (gfpApprox f x a)
· 使用引理 `relDerivedSet_subset`：relDerivedSet_subset {A : Set X} : relDerivedSet A
 subseteq A
-/
theorem iteratedDerivedSet_succ :
    sᵈ[a + 1] = relDerivedSet (sᵈ[a]) := by
  simpa [iteratedDerivedSet] using
    gfpApprox_add_one relDerivedSet relDerivedSet_subset a
/-
**CantorBendixson.iteratedDerivedSet_limit** 是 Mathlib 中的一个定理，位于命名空间 `CantorBend
ixson`。
形式化陈述：iteratedDerivedSet_limit (ha : Order.IsSuccLimit a) : sᵈ[a] = ⋂ b : Set.Ii
o a, sᵈ[b]
参数：ha : Order.IsSuccLimit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `OrdinalApprox.gfpApprox_of_isSuccLimit`：gfpApprox_of_isSuccLimit {a : Or
dinal} (ha : Order.IsSuccLimit a) : gfpApprox f x a = ⨅ b : Set.Iio a, gfpApprox
 f x b
-/
theorem iteratedDerivedSet_limit (ha : Order.IsSuccLimit a) :
    sᵈ[a] = ⋂ b : Set.Iio a, sᵈ[b] := by
  simpa [iteratedDerivedSet] using gfpApprox_of_isSuccLimit relDerivedSet ha

/-- A set is preperfect if and only if every stage of its iterated relative derived-set sequence
is equal to the original set. -/
/-
**CantorBendixson.iteratedDerivedSet_constant_iff_preperfect** 是 Mathlib 中的一个定理，
位于命名空间 `CantorBendixson`。
形式化陈述：iteratedDerivedSet_constant_iff_preperfect : Preperfect s ↔ forall a : Ord
inal, sᵈ[a] = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `preperfect_iff_eq_relDerivedSet`：preperfect_iff_eq_relDerivedSet {U : Se
t X} : Preperfect U ↔ U = relDerivedSet U
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrdinalApprox.gfpApprox_eq_all_of_fixedPoint`：gfpApprox_eq_all_of_fixedP
oint (hx : f x <= x) : (forall o, gfpApprox f x o = x) ↔ f x = x
· 使用引理 `relDerivedSet_subset`：relDerivedSet_subset {A : Set X} : relDerivedSet A
 subseteq A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A set is preperfect if and only if every stage of its iterated relative derived-
set sequence
is equal to the original set.
-/
theorem iteratedDerivedSet_constant_iff_preperfect :
    Preperfect s ↔ ∀ a : Ordinal, sᵈ[a] = s := by
  rw [preperfect_iff_eq_relDerivedSet, eq_comm,
    ← (gfpApprox_eq_all_of_fixedPoint relDerivedSet (relDerivedSet_subset))]
  simp [iteratedDerivedSet]
/-
**CantorBendixson.isClosed_iteratedDerivedSet** 是 Mathlib 中的一个定理，位于命名空间 `CantorB
endixson`。
形式化陈述：isClosed_iteratedDerivedSet (hs : IsClosed s) : forall a : Ordinal, IsClos
ed sᵈ[a]
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CantorBendixson.iteratedDerivedSet_zero`：iteratedDerivedSet_zero : sᵈ[0]
 = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CantorBendixson.iteratedDerivedSet_succ`：iteratedDerivedSet_succ : sᵈ[a 
+ 1] = relDerivedSet (sᵈ[a])
· 使用引理 `IsClosed.relDerivedSet_eq`：IsClosed.relDerivedSet_eq {A : Set X} (hA : I
sClosed A) : relDerivedSet A = derivedSet A
· 使用定理 `CantorBendixson.iteratedDerivedSet_limit`：iteratedDerivedSet_limit (ha :
 Order.IsSuccLimit a) : sᵈ[a] = ⋂ b : Set.Iio a, sᵈ[b]
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
-/
theorem isClosed_iteratedDerivedSet (hs : IsClosed s) :
    ∀ a : Ordinal, IsClosed sᵈ[a] := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => simpa only [iteratedDerivedSet_zero]
  | add_one a ha =>
    simp_all [ha.relDerivedSet_eq, isClosed_iff_derivedSet_subset, derivedSet_mono]
  | limit a ha ih =>
    simpa [iteratedDerivedSet_limit ha] using
      isClosed_iInter fun i => isClosed_iInter fun hi => ih i hi
/-
**CantorBendixson.iteratedDerivedSet_antitone** 是 Mathlib 中的一个定理，位于命名空间 `CantorB
endixson`。
形式化陈述：iteratedDerivedSet_antitone (s : Set X) : Antitone (iteratedDerivedSet s)
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.gfpApprox_anti_right`：gfpApprox_anti_right : Antitone (gfp
Approx f x)
-/
theorem iteratedDerivedSet_antitone (s : Set X) :
    Antitone (iteratedDerivedSet s) := gfpApprox_anti_right relDerivedSet
/-
**CantorBendixson.iteratedDerivedSet_mono** 是 Mathlib 中的一个定理，位于命名空间 `CantorBendi
xson`。
形式化陈述：iteratedDerivedSet_mono : Monotone (fun s : Set X => iteratedDerivedSet s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrdinalApprox.gfpApprox_mono_mid`：gfpApprox_mono_mid : Monotone (gfpAppr
ox f)
-/
theorem iteratedDerivedSet_mono :
    Monotone (fun s : Set X => iteratedDerivedSet s) :=
  gfpApprox_mono_mid _

/-- If the iterated derived set stops changing at a successor stage, then `sᵈ[a]` is a fixed
point of `relDerivSet`. -/
/-
**CantorBendixson.mem_fixedPoints_of_iteratedDerivedSet_succ_eq** 是 Mathlib 中的一个
定理，位于命名空间 `CantorBendixson`。
形式化陈述：mem_fixedPoints_of_iteratedDerivedSet_succ_eq (ha : sᵈ[a + 1] = sᵈ[a]) : s
ᵈ[a] in fixedPoints relDerivedSet
参数：ha : sᵈ[a + 1] = sᵈ[a]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CantorBendixson.iteratedDerivedSet_succ`：iteratedDerivedSet_succ : sᵈ[a 
+ 1] = relDerivedSet (sᵈ[a])
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the iterated derived set stops changing at a successor stage, then `sᵈ[a]` is
 a fixed
point of `relDerivSet`.
-/
theorem mem_fixedPoints_of_iteratedDerivedSet_succ_eq (ha : sᵈ[a + 1] = sᵈ[a]) :
    sᵈ[a] ∈ fixedPoints relDerivedSet := by
  rw [Function.mem_fixedPoints_iff]
  simpa [iteratedDerivedSet_succ] using ha.symm
/-
**CantorBendixson.iteratedDerivedSet_mem_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `
CantorBendixson`。
形式化陈述：iteratedDerivedSet_mem_fixedPoints (s : Set X) : exists a : Ordinal, sᵈ[a]
 in fixedPoints relDerivedSet
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrdinalApprox.gfpApprox_ord_mem_fixedPoint`：gfpApprox_ord_mem_fixedPoint
 (hx : f x <= x) : gfpApprox f x (ord <| succ #α) in fixedPoints f
· 使用引理 `relDerivedSet_subset`：relDerivedSet_subset {A : Set X} : relDerivedSet A
 subseteq A
-/
theorem iteratedDerivedSet_mem_fixedPoints (s : Set X) :
    ∃ a : Ordinal, sᵈ[a] ∈ fixedPoints relDerivedSet := by
  refine ⟨(Order.succ #(Set X)).ord,
    gfpApprox_ord_mem_fixedPoint relDerivedSet relDerivedSet_subset⟩

/-- The perfect kernel of a set, defined as the intersection of all iterated derived sets. It is
the largest perfect subset of the original set. -/
/-
**CantorBendixson.perfectKernel** 是 Mathlib 中的一个定义，位于命名空间 `CantorBendixson`。
形式化陈述：perfectKernel (s : Set X) : Set X
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The perfect kernel of a set, defined as the intersection of all iterated derived
 sets. It is
the largest perfect subset of the original set.
-/
def perfectKernel (s : Set X) : Set X :=
  ⋂ a : Ordinal, sᵈ[a]
/-
**CantorBendixson.perfectKernel_subset_iteratedDerivedSet** 是 Mathlib 中的一个定理，位于命
名空间 `CantorBendixson`。
形式化陈述：perfectKernel_subset_iteratedDerivedSet (s : Set X) (a : Ordinal) : perfec
tKernel s subseteq sᵈ[a]
参数：s : Set X；a : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem perfectKernel_subset_iteratedDerivedSet (s : Set X) (a : Ordinal) :
    perfectKernel s ⊆ sᵈ[a] :=
  Set.iInter_subset _ a
/-
**CantorBendixson.perfectKernel_subset** 是 Mathlib 中的一个定理，位于命名空间 `CantorBendixso
n`。
形式化陈述：perfectKernel_subset (s : Set X) : perfectKernel s subseteq s
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CantorBendixson.iteratedDerivedSet_zero`：iteratedDerivedSet_zero : sᵈ[0]
 = s
· 使用定理 `CantorBendixson.perfectKernel_subset_iteratedDerivedSet`：perfectKernel_s
ubset_iteratedDerivedSet (s : Set X) (a : Ordinal) : perfectKernel s subseteq sᵈ
[a]
-/
theorem perfectKernel_subset (s : Set X) :
    perfectKernel s ⊆ s := by
  simpa [iteratedDerivedSet_zero] using perfectKernel_subset_iteratedDerivedSet s 0
/-
**CantorBendixson.perfectKernel_mono** 是 Mathlib 中的一个定理，位于命名空间 `CantorBendixson`
。
形式化陈述：perfectKernel_mono (hst : s subseteq t) : perfectKernel s subseteq perfect
Kernel t
参数：hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter_mono''`：iInter_mono'' {s t : ι -> Set α} (h : forall i, s i s
ubseteq t i) : iInter s subseteq iInter t
· 使用定理 `CantorBendixson.iteratedDerivedSet_mono`：iteratedDerivedSet_mono : Monot
one (fun s : Set X => iteratedDerivedSet s)
-/
theorem perfectKernel_mono (hst : s ⊆ t) :
    perfectKernel s ⊆ perfectKernel t := by
  simpa [perfectKernel] using Set.iInter_mono'' (iteratedDerivedSet_mono hst)
/-
**CantorBendixson.isClosed_perfectKernel** 是 Mathlib 中的一个定理，位于命名空间 `CantorBendix
son`。
形式化陈述：isClosed_perfectKernel (hs : IsClosed s) : IsClosed (perfectKernel s)
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `CantorBendixson.isClosed_iteratedDerivedSet`：isClosed_iteratedDerivedSet
 (hs : IsClosed s) : forall a : Ordinal, IsClosed sᵈ[a]
-/
theorem isClosed_perfectKernel (hs : IsClosed s) :
    IsClosed (perfectKernel s) :=
  isClosed_iInter (isClosed_iteratedDerivedSet hs)

@[simp]
/-
**CantorBendixson.perfectKernel_empty** 是 Mathlib 中的一个定理，位于命名空间 `CantorBendixson
`。
形式化陈述：perfectKernel_empty : perfectKernel (∅ : Set X) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CantorBendixson.perfectKernel_subset`：perfectKernel_subset (s : Set X) :
 perfectKernel s subseteq s
-/
theorem perfectKernel_empty :
    perfectKernel (∅ : Set X) = ∅ := by
  simpa using perfectKernel_subset ∅

/-- Once `sᵈ[a]` is a fixed point of `relDerivSet`, the perfect kernel equals `sᵈ[a]`. -/
/-
**CantorBendixson.perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints** 是 Mat
hlib 中的一个定理，位于命名空间 `CantorBendixson`。
形式化陈述：perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints (ha : sᵈ[a] in fixe
dPoints relDerivedSet) : perfectKernel s = sᵈ[a]
参数：ha : sᵈ[a] in fixedPoints relDerivedSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CantorBendixson.perfectKernel_subset_iteratedDerivedSet`：perfectKernel_s
ubset_iteratedDerivedSet (s : Set X) (a : Ordinal) : perfectKernel s subseteq sᵈ
[a]
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `CantorBendixson.iteratedDerivedSet_antitone`：iteratedDerivedSet_antitone
 (s : Set X) : Antitone (iteratedDerivedSet s)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `OrdinalApprox.gfpApprox_eq_of_mem_fixedPoints`：gfpApprox_eq_of_mem_fixed
Points {a b : Ordinal} (h_ab : a <= b) (h : gfpApprox f x a in fixedPoints f) : 
gfpApprox f x b = gfpApprox f x a

--- 原说明 ---
Once `sᵈ[a]` is a fixed point of `relDerivSet`, the perfect kernel equals `sᵈ[a]
`.
-/
theorem perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints
    (ha : sᵈ[a] ∈ fixedPoints relDerivedSet) :
    perfectKernel s = sᵈ[a] := by
  refine le_antisymm (perfectKernel_subset_iteratedDerivedSet s a) ?_
  refine Set.subset_iInter fun i => ?_
  rcases lt_or_ge i a with hi | hi
  · exact iteratedDerivedSet_antitone s hi.le
  · exact (gfpApprox_eq_of_mem_fixedPoints relDerivedSet hi ha).ge

/-- Every perfect subset of a set is contained in its perfect kernel. -/
/-
**CantorBendixson._root_.Perfect.subset_perfectKernel** 是 Mathlib 中的一个定理，位于命名空间 
`CantorBendixson`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every perfect subset of a set is contained in its perfect kernel.
-/
theorem _root_.Perfect.subset_perfectKernel
    {P : Set X} (hP : Perfect P) (hPs : P ⊆ s) :
    P ⊆ perfectKernel s := by
  refine Set.subset_iInter fun i => ?_
  simpa [iteratedDerivedSet_constant_iff_preperfect.mp hP.acc i] using
    iteratedDerivedSet_mono hPs i

/-- The perfect kernel of a closed set is perfect. -/
/-
**CantorBendixson.perfect_perfectKernel** 是 Mathlib 中的一个定理，位于命名空间 `CantorBendixs
on`。
形式化陈述：perfect_perfectKernel (hs : IsClosed s) : Perfect (perfectKernel s)
参数：hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CantorBendixson.iteratedDerivedSet_mem_fixedPoints`：iteratedDerivedSet_m
em_fixedPoints (s : Set X) : exists a : Ordinal, sᵈ[a] in fixedPoints relDerived
Set
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CantorBendixson.perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints`：
perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints (ha : sᵈ[a] in fixedPoint
s relDerivedSet) : perfectKernel s = sᵈ[a]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `perfect_iff_eq_derivedSet`：perfect_iff_eq_derivedSet {U : Set X} : Perfe
ct U ↔ U = derivedSet U
· 使用引理 `IsClosed.relDerivedSet_eq`：IsClosed.relDerivedSet_eq {A : Set X} (hA : I
sClosed A) : relDerivedSet A = derivedSet A
· 使用定理 `CantorBendixson.isClosed_iteratedDerivedSet`：isClosed_iteratedDerivedSet
 (hs : IsClosed s) : forall a : Ordinal, IsClosed sᵈ[a]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x

--- 原说明 ---
The perfect kernel of a closed set is perfect.
-/
theorem perfect_perfectKernel (hs : IsClosed s) :
    Perfect (perfectKernel s) := by
  obtain ⟨a, ha⟩ := iteratedDerivedSet_mem_fixedPoints s
  rw [perfectKernel_eq_iteratedDerivedSet_of_mem_fixedPoints ha]
  refine perfect_iff_eq_derivedSet.mpr ?_
  simpa [(isClosed_iteratedDerivedSet hs a).relDerivedSet_eq] using
    (Function.mem_fixedPoints_iff.mp ha).symm

/-- Taking the perfect kernel of a closed set is idempotent. -/
/-
**CantorBendixson.perfectKernel_idem** 是 Mathlib 中的一个定理，位于命名空间 `CantorBendixson`
。
形式化陈述：perfectKernel_idem (hs : IsClosed s) : perfectKernel (perfectKernel s) = p
erfectKernel s
参数：hs : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `CantorBendixson.perfectKernel_subset`：perfectKernel_subset (s : Set X) :
 perfectKernel s subseteq s
· 使用定理 `Perfect.subset_perfectKernel`：∀ {X : Type u} [inst : TopologicalSpace X]
 {s P : Set X}, Perfect P → P ⊆ s → P ⊆ CantorBendixson.perfectKernel s
· 使用定理 `CantorBendixson.perfect_perfectKernel`：perfect_perfectKernel (hs : IsClo
sed s) : Perfect (perfectKernel s)
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
Taking the perfect kernel of a closed set is idempotent.
-/
theorem perfectKernel_idem (hs : IsClosed s) :
    perfectKernel (perfectKernel s) = perfectKernel s :=
  subset_antisymm (perfectKernel_subset _) <|
    (perfect_perfectKernel hs).subset_perfectKernel Subset.rfl

end

end CantorBendixson

