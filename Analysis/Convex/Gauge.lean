/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.RCLike.Basic

/-!
# The Minkowski functional

This file defines the Minkowski functional, aka gauge.

The Minkowski functional of a set `s` is the function which associates each point to how much you
need to scale `s` for `x` to be inside it. When `s` is symmetric, convex and absorbent, its gauge is
a seminorm. Reciprocally, any seminorm arises as the gauge of some set, namely its unit ball. This
induces the equivalence of seminorms and locally convex topological vector spaces.

## Main declarations

For a real vector space,
* `gauge`: Aka Minkowski functional. `gauge s x` is the least (actually, an infimum) `r` such
  that `x ∈ r • s`.
* `gaugeSeminorm`: The Minkowski functional as a seminorm, when `s` is symmetric, convex and
  absorbent.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

Minkowski functional, gauge
-/

@[expose] public section

open NormedField Set
open scoped Pointwise Topology NNReal

noncomputable section

variable {𝕜 E : Type*}

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E]

/-- The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
/-
**gauge** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gauge (s : Set E) (x : E) : Real
参数：s : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is t
he functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r
`.
-/
def gauge (s : Set E) (x : E) : ℝ :=
  sInf { r : ℝ | 0 < r ∧ x ∈ r • s }

variable {s t : Set E} {x : E} {a : ℝ}
/-
**gauge_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_def : gauge s x = sInf ({ r in Set.Ioi (0 : Real) | x in r • s })
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gauge_def : gauge s x = sInf ({ r ∈ Set.Ioi (0 : ℝ) | x ∈ r • s }) :=
  rfl

/-- An alternative definition of the gauge using scalar multiplication on the element rather than on
the set. -/
/-
**gauge_def'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹ • x in s}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
An alternative definition of the gauge using scalar multiplication on the elemen
t rather than on
the set.
-/
theorem gauge_def' : gauge s x = sInf {r ∈ Set.Ioi (0 : ℝ) | r⁻¹ • x ∈ s} := by
  congrm sInf {r | ?_}
  exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _
/-
**bddBelow_gauge_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bddBelow_gauge_set : BddBelow { r : ℝ | 0 < r ∧ x ∈ r • s } :=
  ⟨0, fun _ hr => hr.1.le⟩

/-- If the given subset is `Absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge. -/
/-
**Absorbent.gauge_set_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Absorbent.gauge_set_nonempty (absorbs : Absorbent Real s) : { r : Real | 0
 < r ∧ x in r • s }.Nonempty
参数：absorbs : Absorbent Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Absorbs.exists_pos`：Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 
0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
If the given subset is `Absorbent` then the set we take an infimum over in `gaug
e` is nonempty,
which is useful for proving many properties about the gauge.
-/
theorem Absorbent.gauge_set_nonempty (absorbs : Absorbent ℝ s) :
    { r : ℝ | 0 < r ∧ x ∈ r • s }.Nonempty :=
  let ⟨r, hr₁, hr₂⟩ := (absorbs x).exists_pos
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).ge rfl⟩
/-
**gauge_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_mono (hs : Absorbent Real s) (h : s subseteq t) : gauge t <= gauge s
参数：hs : Absorbent Real s；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s t : Set α},   BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s
· 使用定理 `_private.Mathlib.Analysis.Convex.Gauge.0.bddBelow_gauge_set`：∀ {E : Type
 u_2} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] {s : Set E} {x : E}, 
  BddBelow {r | 0 < r ∧ x ∈ r • s}
· 使用定理 `Absorbent.gauge_set_nonempty`：Absorbent.gauge_set_nonempty (absorbs : Ab
sorbent Real s) : { r : Real | 0 < r ∧ x in r • s }.Nonempty
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
-/
theorem gauge_mono (hs : Absorbent ℝ s) (h : s ⊆ t) : gauge t ≤ gauge s := fun _ => by
  unfold gauge
  gcongr; exacts [bddBelow_gauge_set, hs.gauge_set_nonempty]
/-
**exists_lt_of_gauge_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_of_gauge_lt (absorbs : Absorbent Real s) (h : gauge s x < a) : e
xists b, 0 < b ∧ b < a ∧ x in b • s
参数：absorbs : Absorbent Real s；h : gauge s x < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_of_csInf_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLin
earOrder α] {s : Set α} {b : α},   s.Nonempty → sInf s < b → ∃ a ∈ s, a < b
· 使用定理 `Absorbent.gauge_set_nonempty`：Absorbent.gauge_set_nonempty (absorbs : Ab
sorbent Real s) : { r : Real | 0 < r ∧ x in r • s }.Nonempty
-/
theorem exists_lt_of_gauge_lt (absorbs : Absorbent ℝ s) (h : gauge s x < a) :
    ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s := by
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_csInf_lt absorbs.gauge_set_nonempty h
  exact ⟨b, hb, hba, hx⟩

/-- The gauge evaluated at `0` is always zero (mathematically this requires `0` to be in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds unconditionally). -/
@[simp]
/-
**gauge_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_zero : gauge s 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gauge_def'`：gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹
 • x in s}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.sep_true`：sep_true : { x in s | True } = s
· 使用定理 `csInf_Ioi`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {a :
 α} [NoMaxOrder α] [DenselyOrdered α], sInf (Set.Ioi a) = a
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.sep_false`：sep_false : { x in s | False } = ∅
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0

--- 原说明 ---
The gauge evaluated at `0` is always zero (mathematically this requires `0` to b
e in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds un
conditionally).
-/
theorem gauge_zero : gauge s 0 = 0 := by
  rw [gauge_def']
  by_cases h : (0 : E) ∈ s
  · simp only [smul_zero, sep_true, h, csInf_Ioi]
  · simp only [smul_zero, sep_false, h, Real.sInf_empty]

@[simp]
/-
**gauge_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_zero' : gauge (0 : Set E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gauge_def'`：gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹
 • x in s}
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.sep_true`：sep_true : { x in s | True } = s
· 使用定理 `csInf_Ioi`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {a :
 α} [NoMaxOrder α] [DenselyOrdered α], sInf (Set.Ioi a) = a
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
-/
theorem gauge_zero' : gauge (0 : Set E) = 0 := by
  ext x
  rw [gauge_def']
  obtain rfl | hx := eq_or_ne x 0
  · simp only [csInf_Ioi, mem_zero, Pi.zero_apply, sep_true, smul_zero]
  · simp only [mem_zero, Pi.zero_apply, inv_eq_zero, smul_eq_zero]
    convert! Real.sInf_empty
    exact eq_empty_iff_forall_notMem.2 fun r hr => hr.2.elim (ne_of_gt hr.1) hx

@[simp]
/-
**gauge_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_empty : gauge (∅ : Set E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gauge_def'`：gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹
 • x in s}
· 使用定理 `Set.sep_false`：sep_false : { x in s | False } = ∅
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gauge_empty : gauge (∅ : Set E) = 0 := by
  ext
  simp only [gauge_def', Real.sInf_empty, mem_empty_iff_false, Pi.zero_apply, sep_false]
/-
**gauge_of_subset_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_of_subset_zero (h : s subseteq 0) : gauge s = 0
参数：h : s subseteq 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_singleton_iff_eq`：subset_singleton_iff_eq {s : Set α} {x : α}
 : s subseteq {x} ↔ s = ∅ ∨ s = {x}
· 使用定理 `gauge_empty`：gauge_empty : gauge (∅ : Set E) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gauge_zero'`：gauge_zero' : gauge (0 : Set E) = 0
-/
theorem gauge_of_subset_zero (h : s ⊆ 0) : gauge s = 0 := by
  obtain rfl | rfl := subset_singleton_iff_eq.1 h
  exacts [gauge_empty, gauge_zero']

/-- The gauge is always nonnegative. -/
/-
**gauge_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_nonneg (x : E) : 0 <= gauge s x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.sInf_nonneg`：sInf_nonneg (hs : forall x in s, 0 <= x) : 0 <= sInf s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
The gauge is always nonnegative.
-/
theorem gauge_nonneg (x : E) : 0 ≤ gauge s x :=
  Real.sInf_nonneg fun _ hx => hx.1.le
/-
**gauge_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_neg (symmetric : forall x in s, -x in s) (x : E) : gauge s (-x) = ga
uge s x
参数：symmetric : forall x in s, -x in s；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `gauge_def'`：gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹
 • x in s}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gauge_neg (symmetric : ∀ x ∈ s, -x ∈ s) (x : E) : gauge s (-x) = gauge s x := by
  have : ∀ x, -x ∈ s ↔ x ∈ s := fun x => ⟨fun h => by simpa using symmetric _ h, symmetric x⟩
  simp_rw [gauge_def', smul_neg, this]
/-
**gauge_neg_set_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_neg_set_neg (x : E) : gauge (-s) (-x) = gauge s x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gauge_def'`：gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹
 • x in s}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gauge_neg_set_neg (x : E) : gauge (-s) (-x) = gauge s x := by
  simp_rw [gauge_def', smul_neg, neg_mem_neg]
/-
**gauge_neg_set_eq_gauge_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_neg_set_eq_gauge_neg (x : E) : gauge (-s) x = gauge s (-x)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gauge_neg_set_neg`：gauge_neg_set_neg (x : E) : gauge (-s) (-x) = gauge s
 x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem gauge_neg_set_eq_gauge_neg (x : E) : gauge (-s) x = gauge s (-x) := by
  rw [← gauge_neg_set_neg, neg_neg]
/-
**gauge_le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_le_of_mem (ha : 0 <= a) (hx : x in a • s) : gauge s x <= a
参数：ha : 0 <= a；hx : x in a • s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用引理 `Set.zero_smul_set_subset`：zero_smul_set_subset (s : Set β) : (0 : α) • s
 subseteq 0
· 使用定理 `gauge_zero`：gauge_zero : gauge s 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `_private.Mathlib.Analysis.Convex.Gauge.0.bddBelow_gauge_set`：∀ {E : Type
 u_2} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] {s : Set E} {x : E}, 
  BddBelow {r | 0 < r ∧ x ∈ r • s}
-/
theorem gauge_le_of_mem (ha : 0 ≤ a) (hx : x ∈ a • s) : gauge s x ≤ a := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [mem_singleton_iff.1 (zero_smul_set_subset _ hx), gauge_zero]
  · exact csInf_le bddBelow_gauge_set ⟨ha', hx⟩
/-
**setOfPred_gauge_le_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_gauge_le_eq (hs₁ : Convex Real s) (hs₀ : (0 : E) in s) (hs₂ : Ab
sorbent Real s) (ha : 0 <= a) : { x | gauge s x <= a } = ⋂ (r : Real) (_ : a < r
), r • s
参数：hs₁ : Convex Real s；hs₀ : (0 : E) in s；hs₂ : Absorbent Real s；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `exists_lt_of_gauge_lt`：exists_lt_of_gauge_lt (absorbs : Absorbent Real s
) (h : gauge s x < a) : exists b, 0 < b ∧ b < a ∧ x in b • s
· 使用定理 `Convex.smul_mem_of_zero_mem`：Convex.smul_mem_of_zero_mem (hs : Convex 𝕜 
s) {x : E} (zero_mem : (0 : E) in s) (hx : x in s) {t : 𝕜} (ht : t in Icc (0 : 𝕜
) 1) : t • x in s
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `inv_mul_le_iff₀`：inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b <= a ↔ b <= c * 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `le_of_forall_pos_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Li
nearOrder α] [AddLeftMono α] {a b : α},   (∀ (ε : α), 0 < ε → a < b + ε) → a ≤ b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 87 条，此处仅展示前 30 条）
-/
theorem setOfPred_gauge_le_eq (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : Absorbent ℝ s)
    (ha : 0 ≤ a) : { x | gauge s x ≤ a } = ⋂ (r : ℝ) (_ : a < r), r • s := by
  ext x
  simp_rw [Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun h r hr => ?_, fun h => le_of_forall_pos_lt_add fun ε hε => ?_⟩
  · have hr' := ha.trans_lt hr
    rw [mem_smul_set_iff_inv_smul_mem₀ hr'.ne']
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr)
    suffices (r⁻¹ * δ) • δ⁻¹ • x ∈ s by rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this
    rw [mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne'] at hδ
    refine hs₁.smul_mem_of_zero_mem hs₀ hδ ⟨by positivity, ?_⟩
    rw [inv_mul_le_iff₀ hr', mul_one]
    exact hδr.le
  · linarith [gauge_le_of_mem (by linarith) <| h (a + ε / 2) (by linarith)]

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_le_eq := setOfPred_gauge_le_eq

@[deprecated (since := "2026-06-17")] alias gauge_le_eq := setOfPred_gauge_le_eq
/-
**setOfPred_gauge_lt_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_gauge_lt_eq' (absorbs : Absorbent Real s) (a : Real) : { x | gau
ge s x < a } = ⋃ (r : Real) (_ : 0 < r) (_ : r < a), r • s
参数：absorbs : Absorbent Real s；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_lt_of_gauge_lt`：exists_lt_of_gauge_lt (absorbs : Absorbent Real s
) (h : gauge s x < a) : exists b, 0 < b ∧ b < a ∧ x in b • s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `gauge_le_of_mem`：gauge_le_of_mem (ha : 0 <= a) (hx : x in a • s) : gauge
 s x <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem setOfPred_gauge_lt_eq' (absorbs : Absorbent ℝ s) (a : ℝ) :
    { x | gauge s x < a } = ⋃ (r : ℝ) (_ : 0 < r) (_ : r < a), r • s := by
  ext
  simp_rw [mem_ofPred, mem_iUnion, exists_prop]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_eq' := setOfPred_gauge_lt_eq'

@[deprecated (since := "2026-06-17")] alias gauge_lt_eq' := setOfPred_gauge_lt_eq'
/-
**setOfPred_gauge_lt_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_gauge_lt_eq (absorbs : Absorbent Real s) (a : Real) : { x | gaug
e s x < a } = ⋃ r in Set.Ioo 0 (a : Real), r • s
参数：absorbs : Absorbent Real s；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_lt_of_gauge_lt`：exists_lt_of_gauge_lt (absorbs : Absorbent Real s
) (h : gauge s x < a) : exists b, 0 < b ∧ b < a ∧ x in b • s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `gauge_le_of_mem`：gauge_le_of_mem (ha : 0 <= a) (hx : x in a • s) : gauge
 s x <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem setOfPred_gauge_lt_eq (absorbs : Absorbent ℝ s) (a : ℝ) :
    { x | gauge s x < a } = ⋃ r ∈ Set.Ioo 0 (a : ℝ), r • s := by
  ext
  simp_rw [mem_ofPred, mem_iUnion, exists_prop, mem_Ioo, and_assoc]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_eq := setOfPred_gauge_lt_eq

@[deprecated (since := "2026-06-17")] alias gauge_lt_eq := setOfPred_gauge_lt_eq
/-
**mem_openSegment_of_gauge_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_openSegment_of_gauge_lt_one (absorbs : Absorbent Real s) (hgauge : gau
ge s x < 1) : exists y in s, x in openSegment Real 0 y
参数：absorbs : Absorbent Real s；hgauge : gauge s x < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_of_gauge_lt`：exists_lt_of_gauge_lt (absorbs : Absorbent Real s
) (h : gauge s x < a) : exists b, 0 < b ∧ b < a ∧ x in b • s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mem_openSegment_of_gauge_lt_one (absorbs : Absorbent ℝ s) (hgauge : gauge s x < 1) :
    ∃ y ∈ s, x ∈ openSegment ℝ 0 y := by
  rcases exists_lt_of_gauge_lt absorbs hgauge with ⟨r, hr₀, hr₁, y, hy, rfl⟩
  refine ⟨y, hy, 1 - r, r, ?_⟩
  simp [*]
/-
**setOfPred_gauge_lt_one_subset_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_gauge_lt_one_subset_self (hs : Convex Real s) (h₀ : (0 : E) in s
) (absorbs : Absorbent Real s) : { x | gauge s x < 1 } subseteq s
参数：hs : Convex Real s；h₀ : (0 : E) in s；absorbs : Absorbent Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_openSegment_of_gauge_lt_one`：mem_openSegment_of_gauge_lt_one (absorb
s : Absorbent Real s) (hgauge : gauge s x < 1) : exists y in s, x in openSegment
 Real 0 y
· 使用定理 `Convex.openSegment_subset`：Convex.openSegment_subset (h : Convex 𝕜 s) {x
 y : E} (hx : x in s) (hy : y in s) : openSegment 𝕜 x y subseteq s
-/
theorem setOfPred_gauge_lt_one_subset_self (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s)
    (absorbs : Absorbent ℝ s) : { x | gauge s x < 1 } ⊆ s := fun _x hx ↦
  let ⟨_y, hys, hx⟩ := mem_openSegment_of_gauge_lt_one absorbs hx
  hs.openSegment_subset h₀ hys hx

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_subset_self := setOfPred_gauge_lt_one_subset_self

@[deprecated (since := "2026-06-17")]
alias gauge_lt_one_subset_self := setOfPred_gauge_lt_one_subset_self
/-
**gauge_le_one_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_le_one_of_mem {x : E} (hx : x in s) : gauge s x <= 1
参数：hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gauge_le_of_mem`：gauge_le_of_mem (ha : 0 <= a) (hx : x in a • s) : gauge
 s x <= a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
  gauge_le_of_mem zero_le_one <| by rwa [one_smul]

/-- Gauge is subadditive. -/
/-
**gauge_add_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_add_le (hs : Convex Real s) (absorbs : Absorbent Real s) (x y : E) :
 gauge s (x + y) <= gauge s x + gauge s y
参数：hs : Convex Real s；absorbs : Absorbent Real s；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_pos_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Li
nearOrder α] [AddLeftMono α] {a b : α},   (∀ (ε : α), 0 < ε → a < b + ε) → a ≤ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `exists_lt_of_gauge_lt`：exists_lt_of_gauge_lt (absorbs : Absorbent Real s
) (h : gauge s x < a) : exists b, 0 < b ∧ b < a ∧ x in b • s
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `gauge_le_of_mem`：gauge_le_of_mem (ha : 0 <= a) (hx : x in a • s) : gauge
 s x <= a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.add_smul`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Field 𝕜] [inst_
1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : AddCommGroup E] [inst_4 :
 _roo…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
Gauge is subadditive.
-/
theorem gauge_add_le (hs : Convex ℝ s) (absorbs : Absorbent ℝ s) (x y : E) :
    gauge s (x + y) ≤ gauge s x + gauge s y := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha, ha', x, hx, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb, hb', y, hy, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))
  calc
    gauge s (a • x + b • y) ≤ a + b := gauge_le_of_mem (by positivity) <| by
      rw [hs.add_smul ha.le hb.le]
      exact add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
    _ < gauge s (a • x) + gauge s (b • y) + ε := by linarith
/-
**gauge_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_sum_le {ι : Type*} (hs : Convex Real s) (absorbs : Absorbent Real s)
 (t : Finset ι) (f : ι -> E) : gauge s (∑ i in t, f i) <= ∑ i in t, gauge s (f i
)
参数：hs : Convex Real s；absorbs : Absorbent Real s；t : Finset ι；f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sum_of_subadditive`：∀ {ι : Type u_1} {M : Type u_4} {N : Type 
u_5} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] [inst_2 : Preorder N]  
 [IsOrderedAddMono…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `gauge_zero`：gauge_zero : gauge s 0 = 0
· 使用定理 `gauge_add_le`：gauge_add_le (hs : Convex Real s) (absorbs : Absorbent Rea
l s) (x y : E) : gauge s (x + y) <= gauge s x + gauge s y
-/
theorem gauge_sum_le {ι : Type*} (hs : Convex ℝ s) (absorbs : Absorbent ℝ s) (t : Finset ι)
    (f : ι → E) : gauge s (∑ i ∈ t, f i) ≤ ∑ i ∈ t, gauge s (f i) :=
  Finset.le_sum_of_subadditive _ gauge_zero.le (gauge_add_le hs absorbs) _ _
/-
**self_subset_setOfPred_gauge_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_subset_setOfPred_gauge_le_one : s subseteq { x | gauge s x <= 1 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gauge_le_one_of_mem`：gauge_le_one_of_mem {x : E} (hx : x in s) : gauge s
 x <= 1
-/
theorem self_subset_setOfPred_gauge_le_one : s ⊆ { x | gauge s x ≤ 1 } :=
  fun _ => gauge_le_one_of_mem

@[deprecated (since := "2026-07-09")]
alias self_subset_setOf_gauge_le_one := self_subset_setOfPred_gauge_le_one

@[deprecated (since := "2026-06-17")]
alias self_subset_gauge_le_one := self_subset_setOfPred_gauge_le_one
/-
**Convex.setOfPred_gauge_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.setOfPred_gauge_le (hs : Convex Real s) (h₀ : (0 : E) in s) (absorb
s : Absorbent Real s) (a : Real) : Convex Real { x | gauge s x <= a }
参数：hs : Convex Real s；h₀ : (0 : E) in s；absorbs : Absorbent Real s；a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `setOfPred_gauge_le_eq`：setOfPred_gauge_le_eq (hs₁ : Convex Real s) (hs₀ 
: (0 : E) in s) (hs₂ : Absorbent Real s) (ha : 0 <= a) : { x | gauge s x <= a } 
= ⋂ (r : Re…
· 使用定理 `convex_iInter`：convex_iInter {ι : Sort*} {s : ι -> Set E} (h : forall i,
 Convex 𝕜 (s i)) : Convex 𝕜 (⋂ i, s i)
· 使用定理 `Convex.smul`：Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `gauge_nonneg`：gauge_nonneg (x : E) : 0 <= gauge s x
· 使用定理 `convex_empty`：convex_empty : Convex 𝕜 (∅ : Set E)
-/
theorem Convex.setOfPred_gauge_le (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s)
    (a : ℝ) : Convex ℝ { x | gauge s x ≤ a } := by
  by_cases ha : 0 ≤ a
  · rw [setOfPred_gauge_le_eq hs h₀ absorbs ha]
    exact convex_iInter fun i => convex_iInter fun _ => hs.smul _
  · convert! convex_empty (𝕜 := ℝ)
    exact eq_empty_iff_forall_notMem.2 fun x hx => ha <| (gauge_nonneg _).trans hx

@[deprecated (since := "2026-07-09")]
alias Convex.setOf_gauge_le := Convex.setOfPred_gauge_le

@[deprecated (since := "2026-06-17")] alias Convex.gauge_le := Convex.setOfPred_gauge_le
/-
**le_gauge_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_gauge_of_notMem (hs₀ : StarConvex Real 0 s) (hs₂ : Absorbs Real s {x}) 
(hx : x ∉ a • s) : a <= gauge s x
参数：hs₀ : StarConvex Real 0 s；hs₂ : Absorbs Real s {x}；hx : x ∉ a • s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Absorbs.exists_pos`：Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 
0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `starConvex_zero_iff`：starConvex_zero_iff : StarConvex 𝕜 0 s ↔ forall ⦃x 
: E⦄, x in s -> forall ⦃a : 𝕜⦄, 0 <= a -> a <= 1 -> a • x in s
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem le_gauge_of_notMem (hs₀ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ a • s) :
    a ≤ gauge s x := by
  rw [starConvex_zero_iff] at hs₀
  obtain ⟨r, hr, h⟩ := hs₂.exists_pos
  refine le_csInf ⟨r, hr, singleton_subset_iff.1 <| h _ (Real.norm_of_nonneg hr.le).ge⟩ ?_
  rintro b ⟨hb, x, hx', rfl⟩
  refine not_lt.1 fun hba => hx ?_
  have ha := hb.trans hba
  refine ⟨(a⁻¹ * b) • x, hs₀ hx' (by positivity) ?_, ?_⟩
  · rw [← div_eq_inv_mul]
    exact div_le_one_of_le₀ hba.le ha.le
  · dsimp only
    rw [← mul_smul, mul_inv_cancel_left₀ ha.ne']
/-
**one_le_gauge_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_gauge_of_notMem (hs₁ : StarConvex Real 0 s) (hs₂ : Absorbs Real s {
x}) (hx : x ∉ s) : 1 <= gauge s x
参数：hs₁ : StarConvex Real 0 s；hs₂ : Absorbs Real s {x}；hx : x ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_gauge_of_notMem`：le_gauge_of_notMem (hs₀ : StarConvex Real 0 s) (hs₂ 
: Absorbs Real s {x}) (hx : x ∉ a • s) : a <= gauge s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem one_le_gauge_of_notMem (hs₁ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ s) :
    1 ≤ gauge s x :=
  le_gauge_of_notMem hs₁ hs₂ <| by rwa [one_smul]

section LinearOrderedField

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [MulActionWithZero α ℝ] [IsStrictOrderedModule α ℝ]

/-
**gauge_smul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_smul_of_nonneg [MulActionWithZero α E] [IsScalarTower α Real (Set E)
] {s : Set E} {a : α} (ha : 0 <= a) (x : E) : gauge s (a • x) = a • gauge s x
参数：Set E；ha : 0 <= a；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `gauge_zero`：gauge_zero : gauge s 0 = 0
· 使用定理 `gauge_def'`：gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹
 • x in s}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sInf_smul_of_nonneg`：Real.sInf_smul_of_nonneg (ha : 0 <= a) (s : Se
t Real) : sInf (a • s) = a • sInf s
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_pos`：smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0
 < a • b
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem gauge_smul_of_nonneg [MulActionWithZero α E] [IsScalarTower α ℝ (Set E)] {s : Set E} {a : α}
    (ha : 0 ≤ a) (x : E) : gauge s (a • x) = a • gauge s x := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul, gauge_zero, zero_smul]
  rw [gauge_def', gauge_def', ← Real.sInf_smul_of_nonneg ha]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, hx⟩
    simp_rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx
    have := smul_pos (inv_pos.2 ha') hr
    refine ⟨a⁻¹ • r, ⟨this, ?_⟩, smul_inv_smul₀ ha'.ne' _⟩
    rwa [← mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc,
      mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha'.ne'), inv_inv]
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx
    have := smul_pos ha' hr
    refine ⟨this, ?_⟩
    rw [← mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc]
    exact smul_mem_smul_set hx
/-
**gauge_smul_left_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_smul_left_of_nonneg [MulActionWithZero α E] [SMulCommClass α Real Re
al] [IsScalarTower α Real Real] [IsScalarTower α Real E] {s : Set E} {a : α} (ha
 : 0 <= a) : gauge (a • s) = a⁻¹ • gauge s
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `gauge_of_subset_zero`：gauge_of_subset_zero (h : s subseteq 0) : gauge s 
= 0
· 使用引理 `Set.zero_smul_set_subset`：zero_smul_set_subset (s : Set β) : (0 : α) • s
 subseteq 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `gauge_def'`：gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹
 • x in s}
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sInf_smul_of_nonneg`：Real.sInf_smul_of_nonneg (ha : 0 <= a) (s : Se
t Real) : sInf (a • s) = a • sInf s
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_pos`：smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0
 < a • b
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用引理 `smul_inv₀`：smul_inv₀ (c : G₀) (x : G₀') : (c • x)⁻¹ = c⁻¹ • x⁻¹
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem gauge_smul_left_of_nonneg [MulActionWithZero α E] [SMulCommClass α ℝ ℝ]
    [IsScalarTower α ℝ ℝ] [IsScalarTower α ℝ E] {s : Set E} {a : α} (ha : 0 ≤ a) :
    gauge (a • s) = a⁻¹ • gauge s := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_set_subset _)]
  ext x
  rw [gauge_def', Pi.smul_apply, gauge_def', ← Real.sInf_smul_of_nonneg (inv_nonneg.2 ha)]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, y, hy, h⟩
    simp_rw [mem_Ioi] at hr ⊢
    refine ⟨a • r, ⟨smul_pos ha' hr, ?_⟩, inv_smul_smul₀ ha'.ne' _⟩
    rwa [smul_inv₀, smul_assoc, ← h, inv_smul_smul₀ ha'.ne']
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    rw [mem_Ioi] at hr ⊢
    refine ⟨smul_pos (inv_pos.2 ha') hr, r⁻¹ • x, hx, ?_⟩
    rw [smul_inv₀, smul_assoc, inv_inv]
/-
**gauge_smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_smul_left [Module α E] [SMulCommClass α Real Real] [IsScalarTower α 
Real Real] [IsScalarTower α Real E] {s : Set E} (symmetric : forall x in s, -x i
n s) (a : α) : gauge (a • s) = |a|⁻¹ • gauge s
参数：symmetric : forall x in s, -x in s；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gauge_smul_left_of_nonneg`：gauge_smul_left_of_nonneg [MulActionWithZero 
α E] [SMulCommClass α Real Real] [IsScalarTower α Real Real] [IsScalarTower α Re
al E] {s : Set …
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用引理 `Set.neg_smul_set`：neg_smul_set : -a • t = -(a • t)
· 使用引理 `Set.smul_set_neg`：smul_set_neg : a • -t = -(a • t)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem gauge_smul_left [Module α E] [SMulCommClass α ℝ ℝ] [IsScalarTower α ℝ ℝ]
    [IsScalarTower α ℝ E] {s : Set E} (symmetric : ∀ x ∈ s, -x ∈ s) (a : α) :
    gauge (a • s) = |a|⁻¹ • gauge s := by
  rw [← gauge_smul_left_of_nonneg (abs_nonneg a)]
  obtain h | h := abs_choice a
  · rw [h]
  · rw [h, Set.neg_smul_set, ← Set.smul_set_neg]
    congr
    ext y
    refine ⟨symmetric _, fun hy => ?_⟩
    rw [← neg_neg y]
    exact symmetric _ hy

end LinearOrderedField

section RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

/-
**gauge_norm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_norm_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (‖r‖ • x) = 
gauge s (r • x)
参数：hs : Balanced 𝕜 s；r : 𝕜；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.real_smul_eq_coe_smul`：real_smul_eq_coe_smul [AddCommGroup E] [Mo
dule K E] [Module Real E] [IsScalarTower Real K E] (r : Real) (x : E) : r • x = 
(r : K) • x
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Balanced.smul_mem_iff`：Balanced.smul_mem_iff (hs : Balanced 𝕜 s) (h : ‖a
‖ = ‖b‖) : a • x in s ↔ b • x in s
· 使用定理 `Balanced.smul`：Balanced.smul (a : 𝕝) (hs : Balanced 𝕜 s) : Balanced 𝕜 (a
 • s)
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `RCLike.norm_ofReal`：norm_ofReal (r : Real) : ‖(r : K)‖ = |r|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
-/
theorem gauge_norm_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) :
    gauge s (‖r‖ • x) = gauge s (r • x) := by
  unfold gauge
  congr with θ
  rw [@RCLike.real_smul_eq_coe_smul 𝕜]
  refine and_congr_right fun hθ => (hs.smul _).smul_mem_iff ?_
  rw [RCLike.norm_ofReal, abs_norm]

/-- If `s` is balanced, then the Minkowski functional is ℂ-homogeneous. -/
/-
**gauge_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (r • x) = ‖r‖ * g
auge s x
参数：hs : Balanced 𝕜 s；r : 𝕜；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `gauge_smul_of_nonneg`：gauge_smul_of_nonneg [MulActionWithZero α E] [IsSc
alarTower α Real (Set E)] {s : Set E} {a : α} (ha : 0 <= a) (x : E) : gauge s (a
 • x) = a …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `gauge_norm_smul`：gauge_norm_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : g
auge s (‖r‖ • x) = gauge s (r • x)

--- 原说明 ---
If `s` is balanced, then the Minkowski functional is ℂ-homogeneous.
-/
theorem gauge_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (r • x) = ‖r‖ * gauge s x := by
  rw [← smul_eq_mul, ← gauge_smul_of_nonneg (norm_nonneg r), gauge_norm_smul hs]

end RCLike

open Filter

section TopologicalSpace

variable [TopologicalSpace E]

/-
**comap_gauge_nhds_zero_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_gauge_nhds_zero_le (ha : Absorbent Real s) (hb : Bornology.IsVonNBou
nded Real s) : comap (gauge s) (𝓝 0) <= 𝓝 0
参数：ha : Absorbent Real s；hb : Bornology.IsVonNBounded Real s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Absorbs.exists_pos`：Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 
0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `exists_lt_of_gauge_lt`：exists_lt_of_gauge_lt (absorbs : Absorbent Real s
) (h : gauge s x < a) : exists b, 0 < b ∧ b < a ∧ x in b • s
· 使用引理 `lt_inv_comm₀`：lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem comap_gauge_nhds_zero_le (ha : Absorbent ℝ s) (hb : Bornology.IsVonNBounded ℝ s) :
    comap (gauge s) (𝓝 0) ≤ 𝓝 0 := fun u hu ↦ by
  rcases (hb hu).exists_pos with ⟨r, hr₀, hr⟩
  filter_upwards [preimage_mem_comap (gt_mem_nhds (inv_pos.2 hr₀))] with x (hx : gauge s x < r⁻¹)
  rcases exists_lt_of_gauge_lt ha hx with ⟨c, hc₀, hcr, y, hy, rfl⟩
  have hrc := (lt_inv_comm₀ hr₀ hc₀).2 hcr
  rcases hr c⁻¹ (hrc.le.trans (le_abs_self _)) hy with ⟨z, hz, rfl⟩
  simpa only [smul_inv_smul₀ hc₀.ne']

variable [T1Space E]
/-
**gauge_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_eq_zero (hs : Absorbent Real s) (hb : Bornology.IsVonNBounded Real s
) : gauge s x = 0 ↔ x = 0
参数：hs : Absorbent Real s；hb : Bornology.IsVonNBounded Real s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `comap_gauge_nhds_zero_le`：comap_gauge_nhds_zero_le (ha : Absorbent Real 
s) (hb : Bornology.IsVonNBounded Real s) : comap (gauge s) (𝓝 0) <= 𝓝 0
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `nhds_basis_zero_abs_lt`：∀ (α : Type u_1) [inst : TopologicalSpace α] [in
st_1 : AddCommGroup α] [inst_2 : LinearOrder α] [IsOrderedAddMonoid α]   [OrderT
opology α] […
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `gauge_zero`：gauge_zero : gauge s 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem gauge_eq_zero (hs : Absorbent ℝ s) (hb : Bornology.IsVonNBounded ℝ s) :
    gauge s x = 0 ↔ x = 0 := by
  refine ⟨fun h₀ ↦ by_contra fun (hne : x ≠ 0) ↦ ?_, fun h ↦ h.symm ▸ gauge_zero⟩
  have : {x}ᶜ ∈ comap (gauge s) (𝓝 0) :=
    comap_gauge_nhds_zero_le hs hb (isOpen_compl_singleton.mem_nhds hne.symm)
  rcases ((nhds_basis_zero_abs_lt _).comap _).mem_iff.1 this with ⟨r, hr₀, hr⟩
  exact hr (by simpa [h₀]) rfl
/-
**gauge_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_pos (hs : Absorbent Real s) (hb : Bornology.IsVonNBounded Real s) : 
0 < gauge s x ↔ x != 0
参数：hs : Absorbent Real s；hb : Bornology.IsVonNBounded Real s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_iff_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (b < a ↔ a ≠ b)
· 使用定理 `gauge_nonneg`：gauge_nonneg (x : E) : 0 <= gauge s x
· 使用定理 `gauge_eq_zero`：gauge_eq_zero (hs : Absorbent Real s) (hb : Bornology.IsV
onNBounded Real s) : gauge s x = 0 ↔ x = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem gauge_pos (hs : Absorbent ℝ s) (hb : Bornology.IsVonNBounded ℝ s) :
    0 < gauge s x ↔ x ≠ 0 := by
  simp only [(gauge_nonneg _).lt_iff_ne', Ne, gauge_eq_zero hs hb]

end TopologicalSpace

section ContinuousSMul

variable [TopologicalSpace E] [ContinuousSMul ℝ E]

open Filter in
/-
**interior_subset_gauge_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_subset_gauge_lt_one (s : Set E) : interior s subseteq { x | gauge
 s x < 1 }
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.Tendsto.smul`：Filter.Tendsto.smul {f : α -> M} {g : α -> X} {l : 
Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) : Te
ndsto (fu…
· 使用定理 `Filter.Tendsto.inv₀`：Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a
)) (ha : a != 0) : Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 35 条，此处仅展示前 30 条）
-/
theorem interior_subset_gauge_lt_one (s : Set E) : interior s ⊆ { x | gauge s x < 1 } := by
  intro x hx
  have H₁ : Tendsto (fun r : ℝ ↦ r⁻¹ • x) (𝓝[<] 1) (𝓝 ((1 : ℝ)⁻¹ • x)) :=
    ((tendsto_id.inv₀ one_ne_zero).smul tendsto_const_nhds).mono_left inf_le_left
  rw [inv_one, one_smul] at H₁
  have H₂ : ∀ᶠ r in 𝓝[<] (1 : ℝ), x ∈ r • s ∧ 0 < r ∧ r < 1 := by
    filter_upwards [H₁ (mem_interior_iff_mem_nhds.1 hx), Ioo_mem_nhdsLT one_pos] with r h₁ h₂
    exact ⟨(mem_smul_set_iff_inv_smul_mem₀ h₂.1.ne' _ _).2 h₁, h₂⟩
  rcases H₂.exists with ⟨r, hxr, hr₀, hr₁⟩
  exact (gauge_le_of_mem hr₀.le hxr).trans_lt hr₁
/-
**setOfPred_gauge_lt_one_eq_self_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_gauge_lt_one_eq_self_of_isOpen (hs₁ : Convex Real s) (hs₀ : (0 :
 E) in s) (hs₂ : IsOpen s) : { x | gauge s x < 1 } = s
参数：hs₁ : Convex Real s；hs₀ : (0 : E) in s；hs₂ : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `setOfPred_gauge_lt_one_subset_self`：setOfPred_gauge_lt_one_subset_self (
hs : Convex Real s) (h₀ : (0 : E) in s) (absorbs : Absorbent Real s) : { x | gau
ge s x < 1 } subseteq s
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `interior_subset_gauge_lt_one`：interior_subset_gauge_lt_one (s : Set E) :
 interior s subseteq { x | gauge s x < 1 }
-/
theorem setOfPred_gauge_lt_one_eq_self_of_isOpen (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s)
    (hs₂ : IsOpen s) : { x | gauge s x < 1 } = s := by
  refine (setOfPred_gauge_lt_one_subset_self hs₁ ‹_› <| absorbent_nhds_zero <|
    hs₂.mem_nhds hs₀).antisymm ?_
  convert! interior_subset_gauge_lt_one s
  exact hs₂.interior_eq.symm

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_eq_self_of_isOpen := setOfPred_gauge_lt_one_eq_self_of_isOpen

@[deprecated (since := "2026-06-17")]
alias gauge_lt_one_eq_self_of_isOpen := setOfPred_gauge_lt_one_eq_self_of_isOpen
/-
**gauge_lt_one_of_mem_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_lt_one_of_mem_of_isOpen (hs₂ : IsOpen s) {x : E} (hx : x in s) : gau
ge s x < 1
参数：hs₂ : IsOpen s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_subset_gauge_lt_one`：interior_subset_gauge_lt_one (s : Set E) :
 interior s subseteq { x | gauge s x < 1 }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem gauge_lt_one_of_mem_of_isOpen (hs₂ : IsOpen s) {x : E} (hx : x ∈ s) :
    gauge s x < 1 :=
  interior_subset_gauge_lt_one s <| by rwa [hs₂.interior_eq]
/-
**gauge_lt_of_mem_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_lt_of_mem_smul (x : E) (ε : Real) (hε : 0 < ε) (hs₂ : IsOpen s) (hx 
: x in ε • s) : gauge s x < ε
参数：x : E；ε : Real；hε : 0 < ε；hs₂ : IsOpen s；hx : x in ε • s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `gauge_lt_one_of_mem_of_isOpen`：gauge_lt_one_of_mem_of_isOpen (hs₂ : IsOp
en s) {x : E} (hx : x in s) : gauge s x < 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `inv_mul_lt_iff₀`：inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `gauge_smul_of_nonneg`：gauge_smul_of_nonneg [MulActionWithZero α E] [IsSc
alarTower α Real (Set E)] {s : Set E} {a : α} (ha : 0 <= a) (x : E) : gauge s (a
 • x) = a …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem gauge_lt_of_mem_smul (x : E) (ε : ℝ) (hε : 0 < ε) (hs₂ : IsOpen s) (hx : x ∈ ε • s) :
    gauge s x < ε := by
  have : ε⁻¹ • x ∈ s := by rwa [← mem_smul_set_iff_inv_smul_mem₀ hε.ne']
  have h_gauge_lt := gauge_lt_one_of_mem_of_isOpen hs₂ this
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff₀ hε, mul_one]
    at h_gauge_lt
/-
**mem_closure_of_gauge_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_of_gauge_le_one (hc : Convex Real s) (hs₀ : 0 in s) (ha : Abso
rbent Real s) (h : gauge s x <= 1) : x in closure s
参数：hc : Convex Real s；hs₀ : 0 in s；ha : Absorbent Real s；h : gauge s x <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ico_mem_nhdsLT`：Ico_mem_nhdsLT (H : a < b) : Ico a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `setOfPred_gauge_lt_one_subset_self`：setOfPred_gauge_lt_one_subset_self (
hs : Convex Real s) (h₀ : (0 : E) in s) (absorbs : Absorbent Real s) : { x | gau
ge s x < 1 } subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `gauge_smul_of_nonneg`：gauge_smul_of_nonneg [MulActionWithZero α E] [IsSc
alarTower α Real (Set E)] {s : Set E} {a : α} (ha : 0 <= a) (x : E) : gauge s (a
 • x) = a …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用引理 `mul_lt_one_of_nonneg_of_lt_one_left`：mul_lt_one_of_nonneg_of_lt_one_left
 [PosMulMono M₀] (ha₀ : 0 <= a) (ha : a < 1) (hb : b <= 1) : a * b < 1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem mem_closure_of_gauge_le_one (hc : Convex ℝ s) (hs₀ : 0 ∈ s) (ha : Absorbent ℝ s)
    (h : gauge s x ≤ 1) : x ∈ closure s := by
  have : ∀ᶠ r : ℝ in 𝓝[<] 1, r • x ∈ s := by
    filter_upwards [Ico_mem_nhdsLT one_pos] with r ⟨hr₀, hr₁⟩
    apply setOfPred_gauge_lt_one_subset_self hc hs₀ ha
    rw [mem_ofPred_eq, gauge_smul_of_nonneg hr₀]
    exact mul_lt_one_of_nonneg_of_lt_one_left hr₀ hr₁ h
  refine mem_closure_of_tendsto ?_ this
  exact Filter.Tendsto.mono_left (Continuous.tendsto' (by fun_prop) _ _ (one_smul _ _))
    inf_le_left
/-
**mem_frontier_of_gauge_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_frontier_of_gauge_eq_one (hc : Convex Real s) (hs₀ : 0 in s) (ha : Abs
orbent Real s) (h : gauge s x = 1) : x in frontier s
参数：hc : Convex Real s；hs₀ : 0 in s；ha : Absorbent Real s；h : gauge s x = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_gauge_le_one`：mem_closure_of_gauge_le_one (hc : Convex Re
al s) (hs₀ : 0 in s) (ha : Absorbent Real s) (h : gauge s x <= 1) : x in closure
 s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `interior_subset_gauge_lt_one`：interior_subset_gauge_lt_one (s : Set E) :
 interior s subseteq { x | gauge s x < 1 }
-/
theorem mem_frontier_of_gauge_eq_one (hc : Convex ℝ s) (hs₀ : 0 ∈ s) (ha : Absorbent ℝ s)
    (h : gauge s x = 1) : x ∈ frontier s :=
  ⟨mem_closure_of_gauge_le_one hc hs₀ ha h.le, fun h' ↦
    (interior_subset_gauge_lt_one s h').out.ne h⟩
/-
**tendsto_gauge_nhds_zero_nhdsGE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_gauge_nhds_zero_nhdsGE (hs : s in 𝓝 0) : Tendsto (gauge s) (𝓝 0) (
𝓝[>=] 0)
参数：hs : s in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `nhdsGE_basis_Icc`：nhdsGE_basis_Icc [NoMaxOrder α] [DenselyOrdered α] {a 
: α} : (𝓝[>=] a).HasBasis (a < ·) (Icc a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `set_smul_mem_nhds_zero_iff`：set_smul_mem_nhds_zero_iff {s : Set α} {c : 
G₀} (hc : c != 0) : c • s in 𝓝 (0 : α) ↔ s in 𝓝 (0 : α)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `gauge_nonneg`：gauge_nonneg (x : E) : 0 <= gauge s x
· 使用定理 `gauge_le_of_mem`：gauge_le_of_mem (ha : 0 <= a) (hx : x in a • s) : gauge
 s x <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem tendsto_gauge_nhds_zero_nhdsGE (hs : s ∈ 𝓝 0) : Tendsto (gauge s) (𝓝 0) (𝓝[≥] 0) := by
  refine nhdsGE_basis_Icc.tendsto_right_iff.2 fun ε hε ↦ ?_
  rw [← set_smul_mem_nhds_zero_iff hε.ne'] at hs
  filter_upwards [hs] with x hx
  exact ⟨gauge_nonneg _, gauge_le_of_mem hε.le hx⟩
/-
**tendsto_gauge_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_gauge_nhds_zero (hs : s in 𝓝 0) : Tendsto (gauge s) (𝓝 0) (𝓝 0)
参数：hs : s in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `tendsto_gauge_nhds_zero_nhdsGE`：tendsto_gauge_nhds_zero_nhdsGE (hs : s i
n 𝓝 0) : Tendsto (gauge s) (𝓝 0) (𝓝[>=] 0)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem tendsto_gauge_nhds_zero (hs : s ∈ 𝓝 0) : Tendsto (gauge s) (𝓝 0) (𝓝 0) :=
  (tendsto_gauge_nhds_zero_nhdsGE hs).mono_right inf_le_left

/-- If `s` is a neighborhood of the origin, then `gauge s` is continuous at the origin.
See also `continuousAt_gauge`. -/
/-
**continuousAt_gauge_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_gauge_zero (hs : s in 𝓝 0) : ContinuousAt (gauge s) 0
参数：hs : s in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `gauge_zero`：gauge_zero : gauge s 0 = 0
· 使用定理 `tendsto_gauge_nhds_zero`：tendsto_gauge_nhds_zero (hs : s in 𝓝 0) : Tends
to (gauge s) (𝓝 0) (𝓝 0)

--- 原说明 ---
If `s` is a neighborhood of the origin, then `gauge s` is continuous at the orig
in.
See also `continuousAt_gauge`.
-/
theorem continuousAt_gauge_zero (hs : s ∈ 𝓝 0) : ContinuousAt (gauge s) 0 := by
  rw [ContinuousAt, gauge_zero]
  exact tendsto_gauge_nhds_zero hs
/-
**comap_gauge_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_gauge_nhds_zero (hb : Bornology.IsVonNBounded Real s) (h₀ : s in 𝓝 0
) : comap (gauge s) (𝓝 0) = 𝓝 0
参数：hb : Bornology.IsVonNBounded Real s；h₀ : s in 𝓝 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `comap_gauge_nhds_zero_le`：comap_gauge_nhds_zero_le (ha : Absorbent Real 
s) (hb : Bornology.IsVonNBounded Real s) : comap (gauge s) (𝓝 0) <= 𝓝 0
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `tendsto_gauge_nhds_zero`：tendsto_gauge_nhds_zero (hs : s in 𝓝 0) : Tends
to (gauge s) (𝓝 0) (𝓝 0)
-/
theorem comap_gauge_nhds_zero (hb : Bornology.IsVonNBounded ℝ s) (h₀ : s ∈ 𝓝 0) :
    comap (gauge s) (𝓝 0) = 𝓝 0 :=
  (comap_gauge_nhds_zero_le (absorbent_nhds_zero h₀) hb).antisymm
    (tendsto_gauge_nhds_zero h₀).le_comap

end ContinuousSMul

section TopologicalVectorSpace

open Filter

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- If `s` is a convex neighborhood of the origin in a topological real vector space, then `gauge s`
is continuous. If the ambient space is a normed space, then `gauge s` is Lipschitz continuous, see
`Convex.lipschitz_gauge`. -/
/-
**continuousAt_gauge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_gauge (hc : Convex Real s) (hs₀ : s in 𝓝 0) : ContinuousAt (g
auge s) x
参数：hc : Convex Real s；hs₀ : s in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `nhds_basis_Icc_pos`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1
 : AddCommGroup α] [inst_2 : LinearOrder α] [IsOrderedAddMonoid α]   [OrderTopol
ogy α] […
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add_left_nhds_zero`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : AddGroup G] [IsTopologicalAddGroup G] (x : G),   Filter.map (fun x_1 => x +
 x_1) (nhds …
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `set_smul_mem_nhds_zero_iff`：set_smul_mem_nhds_zero_iff {s : Set α} {c : 
G₀} (hc : c != 0) : c • s in 𝓝 (0 : α) ↔ s in 𝓝 (0 : α)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `neg_mem_nhds_zero`：∀ (G : Type w) [inst : TopologicalSpace G] [inst_1 : 
AddGroup G] [IsTopologicalAddGroup G] {S : Set G},   S ∈ nhds 0 → -S ∈ nhds 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `gauge_add_le`：gauge_add_le (hs : Convex Real s) (absorbs : Absorbent Rea
l s) (x y : E) : gauge s (x + y) <= gauge s x + gauge s y
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is a convex neighborhood of the origin in a topological real vector space
, then `gauge s`
is continuous. If the ambient space is a normed space, then `gauge s` is Lipschi
tz continuous, see
`Convex.lipschitz_gauge`.
-/
theorem continuousAt_gauge (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) : ContinuousAt (gauge s) x := by
  have ha : Absorbent ℝ s := absorbent_nhds_zero hs₀
  refine (nhds_basis_Icc_pos _).tendsto_right_iff.2 fun ε hε₀ ↦ ?_
  rw [← map_add_left_nhds_zero, eventually_map]
  have : ε • s ∩ -(ε • s) ∈ 𝓝 0 :=
    inter_mem ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀)
      (neg_mem_nhds_zero _ ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀))
  filter_upwards [this] with y hy
  constructor
  · rw [sub_le_iff_le_add]
    calc
      gauge s x = gauge s (x + y + (-y)) := by simp
      _ ≤ gauge s (x + y) + gauge s (-y) := gauge_add_le hc ha _ _
      _ ≤ gauge s (x + y) + ε := by grw [gauge_le_of_mem hε₀.le (mem_neg.1 hy.2)]
  · calc
      gauge s (x + y) ≤ gauge s x + gauge s y := gauge_add_le hc ha _ _
      _ ≤ gauge s x + ε := by grw [gauge_le_of_mem hε₀.le hy.1]

/-- If `s` is a convex neighborhood of the origin in a topological real vector space, then `gauge s`
is continuous. If the ambient space is a normed space, then `gauge s` is Lipschitz continuous, see
`Convex.lipschitz_gauge`. -/
@[continuity, fun_prop]
/-
**continuous_gauge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_gauge (hc : Convex Real s) (hs₀ : s in 𝓝 0) : Continuous (gauge
 s)
参数：hc : Convex Real s；hs₀ : s in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `continuousAt_gauge`：continuousAt_gauge (hc : Convex Real s) (hs₀ : s in 
𝓝 0) : ContinuousAt (gauge s) x

--- 原说明 ---
If `s` is a convex neighborhood of the origin in a topological real vector space
, then `gauge s`
is continuous. If the ambient space is a normed space, then `gauge s` is Lipschi
tz continuous, see
`Convex.lipschitz_gauge`.
-/
theorem continuous_gauge (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) : Continuous (gauge s) :=
  continuous_iff_continuousAt.2 fun _ ↦ continuousAt_gauge hc hs₀
/-
**setOfPred_gauge_lt_one_eq_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_gauge_lt_one_eq_interior (hc : Convex Real s) (hs₀ : s in 𝓝 0) :
 { x | gauge s x < 1 } = interior s
参数：hc : Convex Real s；hs₀ : s in 𝓝 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `mem_openSegment_of_gauge_lt_one`：mem_openSegment_of_gauge_lt_one (absorb
s : Absorbent Real s) (hgauge : gauge s x < 1) : exists y in s, x in openSegment
 Real 0 y
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `Convex.openSegment_interior_self_subset_interior`：Convex.openSegment_int
erior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x in in
terior s) (hy : y in s) : openSegment …
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `interior_subset_gauge_lt_one`：interior_subset_gauge_lt_one (s : Set E) :
 interior s subseteq { x | gauge s x < 1 }
-/
theorem setOfPred_gauge_lt_one_eq_interior (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) :
    { x | gauge s x < 1 } = interior s := by
  refine Subset.antisymm (fun x hx ↦ ?_) (interior_subset_gauge_lt_one s)
  rcases mem_openSegment_of_gauge_lt_one (absorbent_nhds_zero hs₀) hx with ⟨y, hys, hxy⟩
  exact hc.openSegment_interior_self_subset_interior (mem_interior_iff_mem_nhds.2 hs₀) hys hxy

@[deprecated (since := "2026-07-09")]
alias setOf_gauge_lt_one_eq_interior := setOfPred_gauge_lt_one_eq_interior

@[deprecated (since := "2026-06-17")]
alias gauge_lt_one_eq_interior := setOfPred_gauge_lt_one_eq_interior
/-
**gauge_lt_one_iff_mem_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_lt_one_iff_mem_interior (hc : Convex Real s) (hs₀ : s in 𝓝 0) : gaug
e s x < 1 ↔ x in interior s
参数：hc : Convex Real s；hs₀ : s in 𝓝 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `setOfPred_gauge_lt_one_eq_interior`：setOfPred_gauge_lt_one_eq_interior (
hc : Convex Real s) (hs₀ : s in 𝓝 0) : { x | gauge s x < 1 } = interior s
-/
theorem gauge_lt_one_iff_mem_interior (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) :
    gauge s x < 1 ↔ x ∈ interior s :=
  Set.ext_iff.1 (setOfPred_gauge_lt_one_eq_interior hc hs₀) _
/-
**gauge_le_one_iff_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_le_one_iff_mem_closure (hc : Convex Real s) (hs₀ : s in 𝓝 0) : gauge
 s x <= 1 ↔ x in closure s
参数：hc : Convex Real s；hs₀ : s in 𝓝 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_gauge_le_one`：mem_closure_of_gauge_le_one (hc : Convex Re
al s) (hs₀ : 0 in s) (ha : Absorbent Real s) (h : gauge s x <= 1) : x in closure
 s
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `absorbent_nhds_zero`：absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbe
nt 𝕜 A
· 使用定理 `le_on_closure`：le_on_closure [TopologicalSpace β] {f g : β -> α} {s : Se
t β} (h : forall x in s, f x <= g x) (hf : ContinuousOn f (closure s)) (hg : Con
tin…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `gauge_le_one_of_mem`：gauge_le_one_of_mem {x : E} (hx : x in s) : gauge s
 x <= 1
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_gauge`：continuous_gauge (hc : Convex Real s) (hs₀ : s in 𝓝 0)
 : Continuous (gauge s)
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem gauge_le_one_iff_mem_closure (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) :
    gauge s x ≤ 1 ↔ x ∈ closure s :=
  ⟨mem_closure_of_gauge_le_one hc (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀), fun h ↦
    le_on_closure (fun _ ↦ gauge_le_one_of_mem) (continuous_gauge hc hs₀).continuousOn
      continuousOn_const h⟩
/-
**gauge_eq_one_iff_mem_frontier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_eq_one_iff_mem_frontier (hc : Convex Real s) (hs₀ : s in 𝓝 0) : gaug
e s x = 1 ↔ x in frontier s
参数：hc : Convex Real s；hs₀ : s in 𝓝 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_iff_le_not_lt`：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
· 使用定理 `gauge_le_one_iff_mem_closure`：gauge_le_one_iff_mem_closure (hc : Convex 
Real s) (hs₀ : s in 𝓝 0) : gauge s x <= 1 ↔ x in closure s
· 使用定理 `gauge_lt_one_iff_mem_interior`：gauge_lt_one_iff_mem_interior (hc : Conve
x Real s) (hs₀ : s in 𝓝 0) : gauge s x < 1 ↔ x in interior s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem gauge_eq_one_iff_mem_frontier (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) :
    gauge s x = 1 ↔ x ∈ frontier s := by
  rw [eq_iff_le_not_lt, gauge_le_one_iff_mem_closure hc hs₀, gauge_lt_one_iff_mem_interior hc hs₀]
  rfl

end TopologicalVectorSpace

section RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

/-- `gauge s` as a seminorm when `s` is balanced, convex and absorbent. -/
@[simps!]
/-
**gaugeSeminorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gaugeSeminorm (hs₀ : Balanced 𝕜 s) (hs₁ : Convex Real s) (hs₂ : Absorbent 
Real s) : Seminorm 𝕜 E
参数：hs₀ : Balanced 𝕜 s；hs₁ : Convex Real s；hs₂ : Absorbent Real s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `gauge_add_le`：gauge_add_le (hs : Convex Real s) (absorbs : Absorbent Rea
l s) (x y : E) : gauge s (x + y) <= gauge s x + gauge s y
· 使用定理 `gauge_smul`：gauge_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (r 
• x) = ‖r‖ * gauge s x

--- 原说明 ---
`gauge s` as a seminorm when `s` is balanced, convex and absorbent.
-/
def gaugeSeminorm (hs₀ : Balanced 𝕜 s) (hs₁ : Convex ℝ s) (hs₂ : Absorbent ℝ s) : Seminorm 𝕜 E :=
  Seminorm.of (gauge s) (gauge_add_le hs₁ hs₂) (gauge_smul hs₀)

variable {hs₀ : Balanced 𝕜 s} {hs₁ : Convex ℝ s} {hs₂ : Absorbent ℝ s} [TopologicalSpace E]
  [ContinuousSMul ℝ E]
/-
**gaugeSeminorm_lt_one_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaugeSeminorm_lt_one_of_isOpen (hs : IsOpen s) {x : E} (hx : x in s) : gau
geSeminorm hs₀ hs₁ hs₂ x < 1
参数：hs : IsOpen s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gauge_lt_one_of_mem_of_isOpen`：gauge_lt_one_of_mem_of_isOpen (hs₂ : IsOp
en s) {x : E} (hx : x in s) : gauge s x < 1
-/
theorem gaugeSeminorm_lt_one_of_isOpen (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    gaugeSeminorm hs₀ hs₁ hs₂ x < 1 :=
  gauge_lt_one_of_mem_of_isOpen hs hx
/-
**gaugeSeminorm_ball_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaugeSeminorm_ball_one (hs : IsOpen s) : (gaugeSeminorm hs₀ hs₁ hs₂).ball 
0 1 = s
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.ball_zero_eq`：ball_zero_eq : ball p 0 r = { y : E | p y < r }
· 使用定理 `setOfPred_gauge_lt_one_eq_self_of_isOpen`：setOfPred_gauge_lt_one_eq_self
_of_isOpen (hs₁ : Convex Real s) (hs₀ : (0 : E) in s) (hs₂ : IsOpen s) : { x | g
auge s x < 1 } = s
· 使用引理 `Absorbent.zero_mem`：Absorbent.zero_mem [NeBot (cobounded G₀)] [AddMonoid
 E] [DistribMulAction G₀ E] {s : Set E} (hs : Absorbent G₀ s) : (0 : E) in s
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
theorem gaugeSeminorm_ball_one (hs : IsOpen s) : (gaugeSeminorm hs₀ hs₁ hs₂).ball 0 1 = s := by
  rw [Seminorm.ball_zero_eq]
  exact setOfPred_gauge_lt_one_eq_self_of_isOpen hs₁ hs₂.zero_mem hs

end RCLike

/-- Any seminorm arises as the gauge of its unit ball. -/
@[simp]
/-
**Seminorm.gauge_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {E : Type u_2} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] (p :
 Seminorm ℝ E), gauge (p.ball 0 1) = ⇑p
参数：p : Seminorm ℝ E；p.ball 0 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gauge.eq_1`：∀ {E : Type u_2} [inst : AddCommGroup E] [inst_1 : _root_.Mo
dule ℝ E] (s : Set E) (x : E),   gauge s x = sInf {r | 0 < r ∧ x ∈ r • s}
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `inv_mul_lt_iff₀`：inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `lt_mul_of_one_lt_left`：lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 
0 < b) (h : 1 < a) : b < a * b
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Any seminorm arises as the gauge of its unit ball.
-/
protected theorem Seminorm.gauge_ball (p : Seminorm ℝ E) : gauge (p.ball 0 1) = p := by
  ext x
  obtain hp | hp := { r : ℝ | 0 < r ∧ x ∈ r • p.ball 0 1 }.eq_empty_or_nonempty
  · rw [gauge, hp, Real.sInf_empty]
    by_contra h
    have hpx : 0 < p x := (apply_nonneg _ _).lt_of_ne h
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx
    refine hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, ?_, smul_inv_smul₀ hpx₂.ne' _⟩
    rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpx₂),
      inv_mul_lt_iff₀ hpx₂, mul_one]
    exact lt_mul_of_one_lt_left hpx one_lt_two
  refine IsGLB.csInf_eq ⟨fun r => ?_, fun r hr => le_of_forall_pos_le_add fun ε hε => ?_⟩ hp
  · rintro ⟨hr, y, hy, rfl⟩
    rw [p.mem_ball_zero] at hy
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le hy.le
  · have hpε : 0 < p x + ε := by positivity
    refine hr ⟨hpε, (p x + ε)⁻¹ • x, ?_, smul_inv_smul₀ hpε.ne' _⟩
    rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpε),
      inv_mul_lt_iff₀ hpε, mul_one]
    exact lt_add_of_pos_right _ hε
/-
**Seminorm.gaugeSeminorm_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Seminorm.gaugeSeminorm_ball (p : Seminorm Real E) : gaugeSeminorm (p.balan
ced_ball_zero 1) (p.convex_ball 0 1) (p.absorbent_ball_zero zero_lt_one) = p
参数：p : Seminorm Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Seminorm.balanced_ball_zero`：balanced_ball_zero (r : Real) : Balanced 𝕜 
(ball p 0 r)
· 使用定理 `Seminorm.convex_ball`：convex_ball : Convex Real (ball p x r)
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Seminorm.absorbent_ball_zero`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : No
rmedDivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   (p 
: Seminorm 𝕜 E) {r…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Seminorm.gauge_ball`：∀ {E : Type u_2} [inst : AddCommGroup E] [inst_1 : 
_root_.Module ℝ E] (p : Seminorm ℝ E), gauge (p.ball 0 1) = ⇑p
-/
theorem Seminorm.gaugeSeminorm_ball (p : Seminorm ℝ E) :
    gaugeSeminorm (p.balanced_ball_zero 1) (p.convex_ball 0 1) (p.absorbent_ball_zero zero_lt_one) =
      p :=
  DFunLike.coe_injective p.gauge_ball

end AddCommGroup

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {r : ℝ} {x : E}
open Metric

/-
**gauge_unit_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_unit_ball (x : E) : gauge (ball (0 : E) 1) x = ‖x‖
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ball_normSeminorm`：ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.
ball
· 使用定理 `Seminorm.gauge_ball`：∀ {E : Type u_2} [inst : AddCommGroup E] [inst_1 : 
_root_.Module ℝ E] (p : Seminorm ℝ E), gauge (p.ball 0 1) = ⇑p
· 使用定理 `coe_normSeminorm`：coe_normSeminorm : ⇑(normSeminorm 𝕜 E) = norm
-/
theorem gauge_unit_ball (x : E) : gauge (ball (0 : E) 1) x = ‖x‖ := by
  rw [← ball_normSeminorm ℝ, Seminorm.gauge_ball, coe_normSeminorm]
/-
**gauge_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_ball (hr : 0 <= r) (x : E) : gauge (ball (0 : E) r) x = ‖x‖ / r
参数：hr : 0 <= r；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.ball_zero`：ball_zero : ball x 0 = ∅
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `gauge_empty`：gauge_empty : gauge (∅ : Set E) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_unitBall_of_pos`：smul_unitBall_of_pos {r : Real} (hr : 0 < r) : r •
 ball (0 : E) 1 = ball (0 : E) r
· 使用定理 `gauge_smul_left`：gauge_smul_left [Module α E] [SMulCommClass α Real Real
] [IsScalarTower α Real Real] [IsScalarTower α Real E] {s : Set E} (symmetric : 
foral…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `gauge_unit_ball`：gauge_unit_ball (x : E) : gauge (ball (0 : E) 1) x = ‖x
‖
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
-/
theorem gauge_ball (hr : 0 ≤ r) (x : E) : gauge (ball (0 : E) r) x = ‖x‖ / r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  · rw [← smul_unitBall_of_pos hr, gauge_smul_left, Pi.smul_apply, gauge_unit_ball, smul_eq_mul,
    abs_of_nonneg hr.le, div_eq_inv_mul]
    simp_rw [mem_ball_zero_iff, norm_neg]
    exact fun _ => id

@[simp]
/-
**gauge_closure_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_closure_zero : gauge (closure (0 : Set E)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `gauge_def'`：gauge_def' : gauge s x = sInf {r in Set.Ioi (0 : Real) | r⁻¹
 • x in s}
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `csInf_Ioi`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {a :
 α} [NoMaxOrder α] [DenselyOrdered α], sInf (Set.Ioi a) = a
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
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
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
-/
theorem gauge_closure_zero : gauge (closure (0 : Set E)) = 0 := funext fun x ↦ by
  simp only [← singleton_zero, gauge_def', mem_closure_zero_iff_norm, norm_smul, mul_eq_zero,
    norm_eq_zero, inv_eq_zero]
  rcases (norm_nonneg x).eq_or_lt' with hx | hx
  · convert! csInf_Ioi (a := (0 : ℝ))
    exact Set.ext fun r ↦ and_iff_left (.inr hx)
  · convert! Real.sInf_empty
    exact eq_empty_of_forall_notMem fun r ⟨hr₀, hr⟩ ↦ hx.ne' <| hr.resolve_left hr₀.out.ne'

@[simp]
/-
**gauge_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gauge_closedBall (hr : 0 <= r) (x : E) : gauge (closedBall (0 : E) r) x = 
‖x‖ / r
参数：hr : 0 <= r；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用引理 `Metric.closedBall_zero'`：closedBall_zero' (x : α) : closedBall x 0 = clo
sure {x}
· 使用定理 `Set.singleton_zero`：∀ {α : Type u_2} [inst : Zero α], {0} = 0
· 使用定理 `gauge_closure_zero`：gauge_closure_zero : gauge (closure (0 : Set E)) = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gauge_ball`：gauge_ball (hr : 0 <= r) (x : E) : gauge (ball (0 : E) r) x 
= ‖x‖ / r
· 使用定理 `gauge_mono`：gauge_mono (hs : Absorbent Real s) (h : s subseteq t) : gaug
e t <= gauge s
· 使用定理 `absorbent_ball_zero`：absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Met
ric.ball (0 : E) r)
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Absorbent.mono`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [in
st_1 : SMul M α] {s t : Set α},   Absorbent M s → s ⊆ t → Absorbent M t
· 使用定理 `Metric.closedBall_subset_ball`：closedBall_subset_ball (h : ε₁ < ε₂) : cl
osedBall x ε₁ subseteq ball x ε₂
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
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
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
（共 38 条，此处仅展示前 30 条）
-/
theorem gauge_closedBall (hr : 0 ≤ r) (x : E) : gauge (closedBall (0 : E) r) x = ‖x‖ / r := by
  rcases hr.eq_or_lt with rfl | hr'
  · rw [div_zero, closedBall_zero', singleton_zero, gauge_closure_zero]; rfl
  · apply le_antisymm
    · rw [← gauge_ball hr]
      exact gauge_mono (absorbent_ball_zero hr') ball_subset_closedBall x
    · suffices ∀ᶠ R in 𝓝[>] r, ‖x‖ / R ≤ gauge (closedBall 0 r) x by
        refine le_of_tendsto ?_ this
        exact tendsto_const_nhds.div inf_le_left hr'.ne'
      filter_upwards [self_mem_nhdsWithin] with R hR
      rw [← gauge_ball (hr.trans hR.out.le)]
      refine gauge_mono ?_ (closedBall_subset_ball hR) _
      exact (absorbent_ball_zero hr').mono ball_subset_closedBall
/-
**mul_gauge_le_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_gauge_le_norm (hs : Metric.ball (0 : E) r subseteq s) : r * gauge s x 
<= ‖x‖
参数：hs : Metric.ball (0 : E) r subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `gauge_nonneg`：gauge_nonneg (x : E) : 0 <= gauge s x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `gauge_ball`：gauge_ball (hr : 0 <= r) (x : E) : gauge (ball (0 : E) r) x 
= ‖x‖ / r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `gauge_mono`：gauge_mono (hs : Absorbent Real s) (h : s subseteq t) : gaug
e t <= gauge s
· 使用定理 `absorbent_ball_zero`：absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Met
ric.ball (0 : E) r)
-/
theorem mul_gauge_le_norm (hs : Metric.ball (0 : E) r ⊆ s) : r * gauge s x ≤ ‖x‖ := by
  obtain hr | hr := le_or_gt r 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hr <| gauge_nonneg _).trans (norm_nonneg _)
  rw [mul_comm, ← le_div_iff₀ hr, ← gauge_ball hr.le]
  exact gauge_mono (absorbent_ball_zero hr) hs x
/-
**Convex.lipschitzWith_gauge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.lipschitzWith_gauge {r : Real>=0} (hc : Convex Real s) (hr : 0 < r)
 (hs : Metric.ball (0 : E) r subseteq s) : LipschitzWith r⁻¹ (gauge s)
参数：hc : Convex Real s；hr : 0 < r；hs : Metric.ball (0 : E) r subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `absorbent_ball_zero`：absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Met
ric.ball (0 : E) r)
· 使用定理 `LipschitzWith.of_le_add_mul`：∀ {α : Type u} [inst : PseudoMetricSpace α]
 {f : α → ℝ} (K : NNReal),   (∀ (x y : α), f x ≤ f y + ↑K * dist x y) → Lipschit
zWith K f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `gauge_add_le`：gauge_add_le (hs : Convex Real s) (absorbs : Absorbent Rea
l s) (x y : E) : gauge s (x + y) <= gauge s x + gauge s y
· 使用定理 `Absorbent.mono`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [in
st_1 : SMul M α] {s t : Set α},   Absorbent M s → s ⊆ t → Absorbent M t
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `gauge_mono`：gauge_mono (hs : Absorbent Real s) (h : s subseteq t) : gaug
e t <= gauge s
· 使用定理 `gauge_ball`：gauge_ball (hr : 0 <= r) (x : E) : gauge (ball (0 : E) r) x 
= ‖x‖ / r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `NNReal.coe_inv`：∀ (r : NNReal), ↑r⁻¹ = (↑r)⁻¹
-/
theorem Convex.lipschitzWith_gauge {r : ℝ≥0} (hc : Convex ℝ s) (hr : 0 < r)
    (hs : Metric.ball (0 : E) r ⊆ s) : LipschitzWith r⁻¹ (gauge s) :=
  have : Absorbent ℝ (Metric.ball (0 : E) r) := absorbent_ball_zero hr
  LipschitzWith.of_le_add_mul _ fun x y =>
    calc
      gauge s x = gauge s (y + (x - y)) := by simp
      _ ≤ gauge s y + gauge s (x - y) := gauge_add_le hc (this.mono hs) _ _
      _ ≤ gauge s y + ‖x - y‖ / r := by grw [gauge_mono this hs (x - y), gauge_ball]; positivity
      _ = gauge s y + r⁻¹ * dist x y := by rw [dist_eq_norm, div_eq_inv_mul, NNReal.coe_inv]
/-
**Convex.lipschitz_gauge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.lipschitz_gauge (hc : Convex Real s) (h₀ : s in 𝓝 (0 : E)) : exists
 K, LipschitzWith K (gauge s)
参数：hc : Convex Real s；h₀ : s in 𝓝 (0 : E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Convex.lipschitzWith_gauge`：Convex.lipschitzWith_gauge {r : Real>=0} (hc
 : Convex Real s) (hr : 0 < r) (hs : Metric.ball (0 : E) r subseteq s) : Lipschi
tzWith r⁻¹ (gaug…
-/
theorem Convex.lipschitz_gauge (hc : Convex ℝ s) (h₀ : s ∈ 𝓝 (0 : E)) :
    ∃ K, LipschitzWith K (gauge s) :=
  let ⟨r, hr₀, hr⟩ := Metric.mem_nhds_iff.1 h₀
  ⟨(⟨r, hr₀.le⟩ : ℝ≥0)⁻¹, hc.lipschitzWith_gauge hr₀ hr⟩
/-
**Convex.uniformContinuous_gauge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.uniformContinuous_gauge (hc : Convex Real s) (h₀ : s in 𝓝 (0 : E)) 
: UniformContinuous (gauge s)
参数：hc : Convex Real s；h₀ : s in 𝓝 (0 : E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.lipschitz_gauge`：Convex.lipschitz_gauge (hc : Convex Real s) (h₀ 
: s in 𝓝 (0 : E)) : exists K, LipschitzWith K (gauge s)
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
-/
theorem Convex.uniformContinuous_gauge (hc : Convex ℝ s) (h₀ : s ∈ 𝓝 (0 : E)) :
    UniformContinuous (gauge s) :=
  let ⟨_K, hK⟩ := hc.lipschitz_gauge h₀; hK.uniformContinuous

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {r : ℝ} {x : E}
open Metric

/-
**le_gauge_of_subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_gauge_of_subset_closedBall (hs : Absorbent Real s) (hr : 0 <= r) (hsr :
 s subseteq closedBall 0 r) : ‖x‖ / r <= gauge s x
参数：hs : Absorbent Real s；hr : 0 <= r；hsr : s subseteq closedBall 0 r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gauge_closedBall`：gauge_closedBall (hr : 0 <= r) (x : E) : gauge (closed
Ball (0 : E) r) x = ‖x‖ / r
· 使用定理 `gauge_mono`：gauge_mono (hs : Absorbent Real s) (h : s subseteq t) : gaug
e t <= gauge s
-/
theorem le_gauge_of_subset_closedBall (hs : Absorbent ℝ s) (hr : 0 ≤ r) (hsr : s ⊆ closedBall 0 r) :
    ‖x‖ / r ≤ gauge s x := by
  rw [← gauge_closedBall hr]
  exact gauge_mono hs hsr _

end Normed

