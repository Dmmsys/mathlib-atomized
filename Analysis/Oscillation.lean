/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Topology.EMetricSpace.Diam

/-!
# Oscillation

In this file we define the oscillation of a function `f: E → F` at a point `x` of `E`. (`E` is
required to be a TopologicalSpace and `F` a PseudoEMetricSpace.) The oscillation of `f` at `x` is
defined to be the infimum of `diam f '' N` for all neighborhoods `N` of `x`. We also define
`oscillationWithin f D x`, which is the oscillation at `x` of `f` restricted to `D`.

We also prove some simple facts about oscillation, most notably that the oscillation of `f`
at `x` is 0 if and only if `f` is continuous at `x`, with versions for both `oscillation` and
`oscillationWithin`.

## Tags

oscillation, oscillationWithin
-/

@[expose] public section

open Topology Metric Set ENNReal

universe u v

variable {E : Type u} {F : Type v} [PseudoEMetricSpace F]

/-- The oscillation of `f : E → F` at `x`. -/
/-
**oscillation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：oscillation [TopologicalSpace E] (f : E -> F) (x : E) : ENNReal
参数：f : E -> F；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The oscillation of `f : E → F` at `x`.
-/
noncomputable def oscillation [TopologicalSpace E] (f : E → F) (x : E) : ENNReal :=
  ⨅ S ∈ (𝓝 x).map f, ediam S

/-- The oscillation of `f : E → F` within `D` at `x`. -/
/-
**oscillationWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：oscillationWithin [TopologicalSpace E] (f : E -> F) (D : Set E) (x : E) : 
ENNReal
参数：f : E -> F；D : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The oscillation of `f : E → F` within `D` at `x`.
-/
noncomputable def oscillationWithin [TopologicalSpace E] (f : E → F) (D : Set E) (x : E) :
    ENNReal :=
  ⨅ S ∈ (𝓝[D] x).map f, ediam S

/-- The oscillation of `f` at `x` within a neighborhood `D` of `x` is equal to `oscillation f x` -/
/-
**oscillationWithin_nhds_eq_oscillation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：oscillationWithin_nhds_eq_oscillation [TopologicalSpace E] (f : E -> F) (D
 : Set E) (x : E) (hD : D in 𝓝 x) : oscillationWithin f D x = oscillation f x
参数：f : E -> F；D : Set E；x : E；hD : D in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `oscillation.eq_1`：∀ {E : Type u} {F : Type v} [inst : PseudoEMetricSpace
 F] [inst_1 : TopologicalSpace E] (f : E → F) (x : E),   oscillation f x = ⨅ S ∈
 Filte…
· 使用定理 `oscillationWithin.eq_1`：∀ {E : Type u} {F : Type v} [inst : PseudoEMetri
cSpace F] [inst_1 : TopologicalSpace E] (f : E → F) (D : Set E) (x : E),   oscil
lationWithin…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_eq_nhds`：∀ {α : Type u_1} [inst : TopologicalSpace α] {a : α}
 {s : Set α}, nhdsWithin a s = nhds a ↔ s ∈ nhds a

--- 原说明 ---
The oscillation of `f` at `x` within a neighborhood `D` of `x` is equal to `osci
llation f x`
-/
theorem oscillationWithin_nhds_eq_oscillation [TopologicalSpace E] (f : E → F) (D : Set E) (x : E)
    (hD : D ∈ 𝓝 x) : oscillationWithin f D x = oscillation f x := by
  rw [oscillation, oscillationWithin, nhdsWithin_eq_nhds.2 hD]

/-- The oscillation of `f` at `x` within `univ` is equal to `oscillation f x` -/
/-
**oscillationWithin_univ_eq_oscillation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：oscillationWithin_univ_eq_oscillation [TopologicalSpace E] (f : E -> F) (x
 : E) : oscillationWithin f univ x = oscillation f x
参数：f : E -> F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `oscillationWithin_nhds_eq_oscillation`：oscillationWithin_nhds_eq_oscilla
tion [TopologicalSpace E] (f : E -> F) (D : Set E) (x : E) (hD : D in 𝓝 x) : osc
illationWithin f D x = osci…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
The oscillation of `f` at `x` within `univ` is equal to `oscillation f x`
-/
theorem oscillationWithin_univ_eq_oscillation [TopologicalSpace E] (f : E → F) (x : E) :
    oscillationWithin f univ x = oscillation f x :=
  oscillationWithin_nhds_eq_oscillation f univ x Filter.univ_mem

namespace ContinuousWithinAt

/-
**ContinuousWithinAt.oscillationWithin_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousWithinAt`。
形式化陈述：oscillationWithin_eq_zero [TopologicalSpace E] {f : E -> F} {D : Set E} {x
 : E} (hf : ContinuousWithinAt f D x) : oscillationWithin f D x = 0
参数：hf : ContinuousWithinAt f D x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `biInf_le`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_8} {s 
: Set ι} (f : ι → α) {i : ι}, i ∈ s → ⨅ i ∈ s, f i ≤ f i
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Metric.ediam_eball_le`：ediam_eball_le {r : Real>=0∞} : ediam (eball x r)
 <= 2 * r
· 使用定理 `ENNReal.mul_div_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (b / a) =
 b
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
theorem oscillationWithin_eq_zero [TopologicalSpace E] {f : E → F} {D : Set E}
    {x : E} (hf : ContinuousWithinAt f D x) : oscillationWithin f D x = 0 := by
  rw [← nonpos_iff_eq_zero]
  refine _root_.le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [zero_add]
  have : eball (f x) (ε / 2) ∈ (𝓝[D] x).map f :=
    hf <| eball_mem_nhds _ (by simp [ne_of_gt hε])
  refine (biInf_le ediam this).trans (le_of_le_of_eq ediam_eball_le ?_)
  exact (ENNReal.mul_div_cancel (by simp) (by simp))

end ContinuousWithinAt

namespace ContinuousAt

/-
**ContinuousAt.oscillation_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：oscillation_eq_zero [TopologicalSpace E] {f : E -> F} {x : E} (hf : Contin
uousAt f x) : oscillation f x = 0
参数：hf : ContinuousAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.oscillationWithin_eq_zero`：oscillationWithin_eq_zero 
[TopologicalSpace E] {f : E -> F} {D : Set E} {x : E} (hf : ContinuousWithinAt f
 D x) : oscillationWithin f D x = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `oscillationWithin_univ_eq_oscillation`：oscillationWithin_univ_eq_oscilla
tion [TopologicalSpace E] (f : E -> F) (x : E) : oscillationWithin f univ x = os
cillation f x
-/
theorem oscillation_eq_zero [TopologicalSpace E] {f : E → F} {x : E} (hf : ContinuousAt f x) :
    oscillation f x = 0 := by
  rw [← continuousWithinAt_univ f x] at hf
  exact oscillationWithin_univ_eq_oscillation f x ▸ hf.oscillationWithin_eq_zero

end ContinuousAt

namespace OscillationWithin

/-- The oscillation within `D` of `f` at `x ∈ D` is 0 if and only if `ContinuousWithinAt f D x`. -/
/-
**OscillationWithin.eq_zero_iff_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Os
cillationWithin`。
形式化陈述：eq_zero_iff_continuousWithinAt [TopologicalSpace E] (f : E -> F) {D : Set 
E} {x : E} (xD : x in D) : oscillationWithin f D x = 0 ↔ ContinuousWithinAt f D 
x
参数：f : E -> F；xD : x in D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EMetric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} :
 Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, edist (u x) a < ε
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `ContinuousWithinAt.oscillationWithin_eq_zero`：oscillationWithin_eq_zero 
[TopologicalSpace E] {f : E -> F} {D : Set E} {x : E} (hf : ContinuousWithinAt f
 D x) : oscillationWithin f D x = …

--- 原说明 ---
The oscillation within `D` of `f` at `x ∈ D` is 0 if and only if `ContinuousWith
inAt f D x`.
-/
theorem eq_zero_iff_continuousWithinAt [TopologicalSpace E] (f : E → F) {D : Set E}
    {x : E} (xD : x ∈ D) : oscillationWithin f D x = 0 ↔ ContinuousWithinAt f D x := by
  refine ⟨fun hf ↦ EMetric.tendsto_nhds.mpr (fun ε ε0 ↦ ?_), fun hf ↦ hf.oscillationWithin_eq_zero⟩
  simp_rw [← hf, oscillationWithin, iInf_lt_iff] at ε0
  obtain ⟨S, hS, Sε⟩ := ε0
  refine Filter.mem_of_superset hS (fun y hy ↦ lt_of_le_of_lt ?_ Sε)
  exact edist_le_ediam_of_mem (mem_preimage.1 hy) <| mem_preimage.1 (mem_of_mem_nhdsWithin xD hS)

end OscillationWithin

namespace Oscillation

/-- The oscillation of `f` at `x` is 0 if and only if `f` is continuous at `x`. -/
/-
**Oscillation.eq_zero_iff_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `Oscillation`。
形式化陈述：eq_zero_iff_continuousAt [TopologicalSpace E] (f : E -> F) (x : E) : oscil
lation f x = 0 ↔ ContinuousAt f x
参数：f : E -> F；x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `oscillationWithin_univ_eq_oscillation`：oscillationWithin_univ_eq_oscilla
tion [TopologicalSpace E] (f : E -> F) (x : E) : oscillationWithin f univ x = os
cillation f x
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `OscillationWithin.eq_zero_iff_continuousWithinAt`：eq_zero_iff_continuous
WithinAt [TopologicalSpace E] (f : E -> F) {D : Set E} {x : E} (xD : x in D) : o
scillationWithin f D x = 0 ↔ Continuou…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The oscillation of `f` at `x` is 0 if and only if `f` is continuous at `x`.
-/
theorem eq_zero_iff_continuousAt [TopologicalSpace E] (f : E → F) (x : E) :
    oscillation f x = 0 ↔ ContinuousAt f x := by
  rw [← oscillationWithin_univ_eq_oscillation, ← continuousWithinAt_univ f x]
  exact OscillationWithin.eq_zero_iff_continuousWithinAt f (mem_univ x)

end Oscillation

namespace IsCompact

variable [PseudoEMetricSpace E] {K : Set E}
variable {f : E → F} {D : Set E} {ε : ENNReal}

/-- If `oscillationWithin f D x < ε` at every `x` in a compact set `K`, then there exists `δ > 0`
such that the oscillation of `f` on `ball x δ ∩ D` is less than `ε` for every `x` in `K`. -/
/-
**IsCompact.uniform_oscillationWithin** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：uniform_oscillationWithin (comp : IsCompact K) (hK : forall x in K, oscill
ationWithin f D x < ε) : exists δ > 0, forall x in K, ediam (f '' (eball x (ENNR
eal.ofReal δ) inter D)) <= ε
参数：comp : IsCompact K；hK : forall x in K, oscillationWithin f D x < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EMetric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0,
 eball x ε subseteq s
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 118 条，此处仅展示前 30 条）

--- 原说明 ---
If `oscillationWithin f D x < ε` at every `x` in a compact set `K`, then there e
xists `δ > 0`
such that the oscillation of `f` on `ball x δ ∩ D` is less than `ε` for every `x
` in `K`.
-/
theorem uniform_oscillationWithin (comp : IsCompact K) (hK : ∀ x ∈ K, oscillationWithin f D x < ε) :
    ∃ δ > 0, ∀ x ∈ K, ediam (f '' (eball x (ENNReal.ofReal δ) ∩ D)) ≤ ε := by
  let S := fun r ↦
    {x : E | ∃ (a : ℝ), (a > r ∧ ediam (f '' (eball x (ENNReal.ofReal a) ∩ D)) ≤ ε)}
  have S_open : ∀ r > 0, IsOpen (S r) := by
    refine fun r _ ↦ EMetric.isOpen_iff.mpr fun x ⟨a, ar, ha⟩ ↦
      ⟨ENNReal.ofReal ((a - r) / 2), by simp [ar], ?_⟩
    refine fun y hy ↦ ⟨a - (a - r) / 2, by linarith,
      le_trans (ediam_mono (image_mono fun z hz ↦ ?_)) ha⟩
    refine ⟨lt_of_le_of_lt (edist_triangle z y x) (lt_of_lt_of_eq (ENNReal.add_lt_add hz.1 hy) ?_),
      hz.2⟩
    rw [← ofReal_add (by linarith) (by linarith), sub_add_cancel]
  have S_cover : K ⊆ ⋃ r > 0, S r := by
    intro x hx
    have : oscillationWithin f D x < ε := hK x hx
    simp only [oscillationWithin, Filter.mem_map, iInf_lt_iff] at this
    obtain ⟨n, hn₁, hn₂⟩ := this
    obtain ⟨r, r0, hr⟩ := EMetric.mem_nhdsWithin_iff.1 hn₁
    simp only [gt_iff_lt, mem_iUnion, exists_prop]
    have : ∀ r', (ENNReal.ofReal r') ≤ r →
        ediam (f '' (eball x (ENNReal.ofReal r') ∩ D)) ≤ ε := by
      intro r' hr'
      grw [← hn₂, ← image_subset_iff.2 hr, hr']
    by_cases r_top : r = ⊤
    · exact ⟨1, one_pos, 2, by simp, this 2 (by simp only [r_top, le_top])⟩
    · obtain ⟨r', hr'⟩ := exists_between (toReal_pos (ne_of_gt r0) r_top)
      use r', hr'.1, r.toReal, hr'.2, this r.toReal ofReal_toReal_le
  have S_antitone : ∀ (r₁ r₂ : ℝ), r₁ ≤ r₂ → S r₂ ⊆ S r₁ :=
    fun r₁ r₂ hr x ⟨a, ar₂, ha⟩ ↦ ⟨a, lt_of_le_of_lt hr ar₂, ha⟩
  obtain ⟨δ, δ0, hδ⟩ : ∃ r > 0, K ⊆ S r := by
    obtain ⟨T, Tb, Tfin, hT⟩ := comp.elim_finite_subcover_image S_open S_cover
    by_cases T_nonempty : T.Nonempty
    · use Tfin.isWF.min T_nonempty, Tb (Tfin.isWF.min_mem T_nonempty)
      intro x hx
      obtain ⟨r, hr⟩ := mem_iUnion.1 (hT hx)
      simp only [mem_iUnion, exists_prop] at hr
      exact (S_antitone _ r (IsWF.min_le Tfin.isWF T_nonempty hr.1)) hr.2
    · rw [not_nonempty_iff_eq_empty] at T_nonempty
      use 1, one_pos, subset_trans hT (by simp [T_nonempty])
  use δ, δ0
  intro x xK
  obtain ⟨a, δa, ha⟩ := hδ xK
  grw [← ha]
  gcongr

/-- If `oscillation f x < ε` at every `x` in a compact set `K`, then there exists `δ > 0` such
that the oscillation of `f` on `ball x δ` is less than `ε` for every `x` in `K`. -/
/-
**IsCompact.uniform_oscillation** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：uniform_oscillation {K : Set E} (comp : IsCompact K) {f : E -> F} {ε : ENN
Real} (hK : forall x in K, oscillation f x < ε) : exists δ > 0, forall x in K, e
diam (f '' (eball x (ENNReal.ofReal δ))) <= ε
参数：comp : IsCompact K；hK : forall x in K, oscillation f x < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `IsCompact.uniform_oscillationWithin`：uniform_oscillationWithin (comp : I
sCompact K) (hK : forall x in K, oscillationWithin f D x < ε) : exists δ > 0, fo
rall x in K, ediam (f '' …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `oscillation f x < ε` at every `x` in a compact set `K`, then there exists `δ
 > 0` such
that the oscillation of `f` on `ball x δ` is less than `ε` for every `x` in `K`.
-/
theorem uniform_oscillation {K : Set E} (comp : IsCompact K)
    {f : E → F} {ε : ENNReal} (hK : ∀ x ∈ K, oscillation f x < ε) :
    ∃ δ > 0, ∀ x ∈ K, ediam (f '' (eball x (ENNReal.ofReal δ))) ≤ ε := by
  simp only [← oscillationWithin_univ_eq_oscillation] at hK
  convert! ← comp.uniform_oscillationWithin hK
  exact inter_univ _

end IsCompact

