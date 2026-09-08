/-
Copyright (c) 2024 Jana Göken. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artur Szafarczyk, Suraj Krishna M S, Jean-Baptiste Stiegler, Isabelle Dubois,
Tomáš Jakl, Lorenzo Zanichelli, Alina Yan, Emilie Uthaiwat, Jana Göken,
Filippo A. E. Nuccio
-/
module

public import Mathlib.Analysis.Real.OfDigits
public import Mathlib.Data.Stream.Init
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Field

/-!
# Ternary Cantor Set

This file defines the Cantor ternary set and proves a few properties.

## Main Definitions

* `preCantorSet n`: The order `n` pre-Cantor set, defined inductively as the union of the images
  under the functions `(· / 3)` and `((2 + ·) / 3)`, with `preCantorSet 0 := Set.Icc 0 1`, i.e.
  `preCantorSet 0` is the unit interval [0,1].
* `cantorSet`: The ternary Cantor set, defined as the intersection of all pre-Cantor sets.
* `cantorToTernary`: given a number `x` in the Cantor set, returns its ternary representation
  `(d₀, d₁, ...)` consisting only of digits `0` and `2`, such that `x = 0.d₀d₁...`
  (see `ofDigits_cantorToTernary`).
* `ofDigits_zero_two_sequence_mem_cantorSet`: any such sequence corresponds to a number
  in the Cantor set.
* `ofDigits_zero_two_sequence_unique`: such a representation is unique.
-/

@[expose] public section

/-- The order `n` pre-Cantor set, defined starting from `[0, 1]` and successively removing the
middle third of each interval. Formally, the order `n + 1` pre-Cantor set is the
union of the images under the functions `(· / 3)` and `((2 + ·) / 3)` of `preCantorSet n`.
-/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**preCantorSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ℕ → Set ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def preCantorSet : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | n + 1 => (· / 3) '' preCantorSet n ∪ (fun x ↦ (2 + x) / 3) '' preCantorSet n
/-
**preCantorSet_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preCantorSet 0 = Set.Icc 0 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preCantorSet_zero : preCantorSet 0 = Set.Icc 0 1 := rfl
/-
**preCantorSet_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (n : ℕ), preCantorSet (n + 1) = (fun x => x / 3) '' preCantorSet n ∪ (fu
n x => (2 + x) / 3) '' preCantorSet n
参数：n : ℕ；n + 1；fun x => x / 3；fun x => (2 + x) / 3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preCantorSet_succ (n : ℕ) :
    preCantorSet (n + 1) = (· / 3) '' preCantorSet n ∪ (fun x ↦ (2 + x) / 3) '' preCantorSet n :=
  rfl

/-- The Cantor set is the subset of the unit interval obtained as the intersection of all
pre-Cantor sets. This means that the Cantor set is obtained by iteratively removing the
open middle third of each subinterval, starting from the unit interval `[0, 1]`.
-/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**cantorSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cantorSet : Set Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def cantorSet : Set ℝ := ⋂ n, preCantorSet n


/-!
## Simple Properties
-/

/-
**quarters_mem_preCantorSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quarters_mem_preCantorSet (n : Nat) : 1 / 4 in preCantorSet n ∧ 3 / 4 in p
reCantorSet n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_eq_true`：∀ {α : Type u} [inst : Semiring α]
 {a b : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNu
m.IsNNRat b n d → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…

--- 原说明 ---
## Simple Properties
-/
lemma quarters_mem_preCantorSet (n : ℕ) : 1 / 4 ∈ preCantorSet n ∧ 3 / 4 ∈ preCantorSet n := by
  induction n with
  | zero =>
    simp only [preCantorSet_zero]
    refine ⟨⟨ ?_, ?_⟩, ?_, ?_⟩ <;> norm_num
  | succ n ih =>
    apply And.intro
    · -- goal: 1 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hypothesis, since 3 / 4 ∈ preCantorSet n
      exact Or.inl ⟨3 / 4, ih.2, by norm_num⟩
    · -- goal: 3 / 4 ∈ preCantorSet (n + 1)
      -- follows by the inductive hypothesis, since 1 / 4 ∈ preCantorSet n
      exact Or.inr ⟨1 / 4, ih.1, by norm_num⟩
/-
**quarter_mem_preCantorSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quarter_mem_preCantorSet (n : Nat) : 1 / 4 in preCantorSet n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `quarters_mem_preCantorSet`：quarters_mem_preCantorSet (n : Nat) : 1 / 4 i
n preCantorSet n ∧ 3 / 4 in preCantorSet n
-/
lemma quarter_mem_preCantorSet (n : ℕ) : 1 / 4 ∈ preCantorSet n := (quarters_mem_preCantorSet n).1
/-
**quarter_mem_cantorSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quarter_mem_cantorSet : 1 / 4 in cantorSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用引理 `quarter_mem_preCantorSet`：quarter_mem_preCantorSet (n : Nat) : 1 / 4 in 
preCantorSet n
-/
theorem quarter_mem_cantorSet : 1 / 4 ∈ cantorSet :=
  Set.mem_iInter.mpr quarter_mem_preCantorSet
/-
**zero_mem_preCantorSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_mem_preCantorSet (n : Nat) : 0 in preCantorSet n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_mem_preCantorSet (n : ℕ) : 0 ∈ preCantorSet n := by
  induction n with
  | zero =>
    simp [preCantorSet]
  | succ n ih =>
    exact Or.inl ⟨0, ih, by simp only [zero_div]⟩
/-
**zero_mem_cantorSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_mem_cantorSet : 0 in cantorSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem zero_mem_cantorSet : 0 ∈ cantorSet := by simp [cantorSet, zero_mem_preCantorSet]
/-
**preCantorSet_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preCantorSet_antitone : Antitone preCantorSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
-/
theorem preCantorSet_antitone : Antitone preCantorSet := by
  refine antitone_nat_of_succ_le fun m ↦ ?_
  induction m with grind [preCantorSet_zero, preCantorSet_succ]
/-
**preCantorSet_subset_unitInterval** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preCantorSet_subset_unitInterval {n : Nat} : preCantorSet n subseteq Set.I
cc 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `preCantorSet_zero`：preCantorSet 0 = Set.Icc 0 1
· 使用定理 `preCantorSet_antitone`：preCantorSet_antitone : Antitone preCantorSet
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma preCantorSet_subset_unitInterval {n : ℕ} : preCantorSet n ⊆ Set.Icc 0 1 := by
  rw [← preCantorSet_zero]
  exact preCantorSet_antitone (by simp)

/-- The ternary Cantor set is a subset of [0,1]. -/
/-
**cantorSet_subset_unitInterval** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cantorSet_subset_unitInterval : cantorSet subseteq Set.Icc 0 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i

--- 原说明 ---
The ternary Cantor set is a subset of [0,1].
-/
lemma cantorSet_subset_unitInterval : cantorSet ⊆ Set.Icc 0 1 :=
  Set.iInter_subset _ 0

/-- The ternary Cantor set satisfies the equation `C = C / 3 ∪ (2 / 3 + C / 3)`. -/
/-
**cantorSet_eq_union_halves** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cantorSet_eq_union_halves : cantorSet = (· / 3) '' cantorSet union (fun x 
=> (2 + x) / 3) '' cantorSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_iInter`：image_iInter {f : α -> β} (hf : Bijective f) (s : ι ->
 Set α) : (f '' ⋂ i, s i) = ⋂ i, f '' s i
· 使用定理 `mulRight_bijective₀`：∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] (a : G₀
), a ≠ 0 → Function.Bijective fun x => x * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `AddGroup.addLeft_bijective`：∀ {G : Type u_5} [inst : AddGroup G] (a : G)
, Function.Bijective fun x => a + x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iInter_union_of_antitone`：iInter_union_of_antitone {ι α} [Preorder ι
] [IsDirectedOrder ι] {s t : ι -> Set α} (hs : Antitone s) (ht : Antitone t) : ⋂
 i, s i union t i …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用引理 `Set.monotone_image`：monotone_image : Monotone (image f)
· 使用定理 `preCantorSet_antitone`：preCantorSet_antitone : Antitone preCantorSet
· 使用定理 `Antitone.iInter_nat_add`：∀ {α : Type u_1} {f : ℕ → Set α}, Antitone f → 
∀ (k : ℕ), ⋂ n, f (n + k) = ⋂ n, f n

--- 原说明 ---
The ternary Cantor set satisfies the equation `C = C / 3 ∪ (2 / 3 + C / 3)`.
-/
theorem cantorSet_eq_union_halves :
    cantorSet = (· / 3) '' cantorSet ∪ (fun x ↦ (2 + x) / 3) '' cantorSet := by
  simp only [cantorSet]
  rw [Set.image_iInter, Set.image_iInter]
  rotate_left
  · exact (mulRight_bijective₀ 3⁻¹ (by simp)).comp (AddGroup.addLeft_bijective 2)
  · exact mulRight_bijective₀ 3⁻¹ (by simp)
  simp_rw [← Function.comp_def,
    ← Set.iInter_union_of_antitone
      (Set.monotone_image.comp_antitone preCantorSet_antitone)
      (Set.monotone_image.comp_antitone preCantorSet_antitone),
    Function.comp_def, ← preCantorSet_succ]
  exact (preCantorSet_antitone.iInter_nat_add _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The preCantor sets are closed. -/
/-
**isClosed_preCantorSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_preCantorSet (n : Nat) : IsClosed (preCantorSet n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Homeomorph.mulLeft₀.congr_simp`：∀ {α : Type u_1} [inst : TopologicalSpac
e α] [inst_1 : GroupWithZero α] [inst_2 : SeparatelyContinuousMul α] (c c_1 : α)
   (e_c : c = c_1) (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h

--- 原说明 ---
The preCantor sets are closed.
-/
lemma isClosed_preCantorSet (n : ℕ) : IsClosed (preCantorSet n) := by
  let f := Homeomorph.mulLeft₀ (1 / 3 : ℝ) (by simp)
  let g := (Homeomorph.addLeft (2 : ℝ)).trans f
  induction n with
  | zero => exact isClosed_Icc
  | succ n ih =>
    refine IsClosed.union ?_ ?_
    · simpa [f, div_eq_inv_mul] using f.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih
    · simpa [g, f, div_eq_inv_mul] using g.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih

/-- The ternary Cantor set is closed. -/
/-
**isClosed_cantorSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_cantorSet : IsClosed cantorSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用引理 `isClosed_preCantorSet`：isClosed_preCantorSet (n : Nat) : IsClosed (preCa
ntorSet n)

--- 原说明 ---
The ternary Cantor set is closed.
-/
lemma isClosed_cantorSet : IsClosed cantorSet :=
  isClosed_iInter isClosed_preCantorSet

/-- The ternary Cantor set is compact. -/
/-
**isCompact_cantorSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCompact_cantorSet : IsCompact cantorSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `isClosed_cantorSet`：isClosed_cantorSet : IsClosed cantorSet
· 使用引理 `cantorSet_subset_unitInterval`：cantorSet_subset_unitInterval : cantorSet
 subseteq Set.Icc 0 1

--- 原说明 ---
The ternary Cantor set is compact.
-/
lemma isCompact_cantorSet : IsCompact cantorSet :=
  isCompact_Icc.of_isClosed_subset isClosed_cantorSet cantorSet_subset_unitInterval

/-!
## The Cantor set as the set of 0–2 numbers in the ternary system.
-/

section ternary02

open Real

/-- If `x = 0.d₀d₁...` in base-3 (ternary), and none of the digits `dᵢ` is `1`,
then `x` belongs to the Cantor set. -/
/-
**ofDigits_zero_two_sequence_mem_cantorSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDigits_zero_two_sequence_mem_cantorSet {a : Nat -> Fin 3} (h : forall n,
 a n != 1) : ofDigits a in cantorSet
参数：h : forall n, a n != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.ofDigits_nonneg`：ofDigits_nonneg {b : Nat} (digits : Nat -> Fin b) 
: 0 <= ofDigits digits
· 使用定理 `Real.ofDigits_le_one`：ofDigits_le_one {b : Nat} (digits : Nat -> Fin b) 
: ofDigits digits <= 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Real.ofDigits_eq_sum_add_ofDigits`：ofDigits_eq_sum_add_ofDigits {b : Nat
} (a : Nat -> Fin b) (n : Nat) : ofDigits a = (∑ i in Finset.range n, ofDigitsTe
rm a i) + ((b : Real) ^…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
If `x = 0.d₀d₁...` in base-3 (ternary), and none of the digits `dᵢ` is `1`,
then `x` belongs to the Cantor set.
-/
theorem ofDigits_zero_two_sequence_mem_cantorSet {a : ℕ → Fin 3}
    (h : ∀ n, a n ≠ 1) : ofDigits a ∈ cantorSet := by
  simp only [cantorSet, Set.mem_iInter]
  intro i
  induction i generalizing a with
  | zero =>
    simp only [preCantorSet_zero, Set.mem_Icc]
    exact ⟨ofDigits_nonneg a, ofDigits_le_one a⟩
  | succ i ih =>
    simp only [preCantorSet, Set.mem_union, Set.mem_image, ← exists_or]
    use ofDigits (fun i ↦ a (i + 1))
    have : (ofDigits fun i ↦ a (i + 1)) ∈ preCantorSet i := ih (by solve_by_elim)
    simp only [this, ofDigits_eq_sum_add_ofDigits a 1, Finset.range_one, ofDigitsTerm,
      Nat.cast_ofNat, Finset.sum_singleton, zero_add, pow_one, true_and, field]
    specialize h 0
    generalize a 0 = x at h
    fin_cases x <;> simp at ⊢ h

/-- If two base-3 representations using only digits `0` and `2` define the same number,
then the sequences must be equal.
This uniqueness fails for general base-3 representations (e.g. `0.1000... = 0.0222...`). -/
/-
**ofDigits_zero_two_sequence_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDigits_zero_two_sequence_unique {a b : Nat -> Fin 3} (ha : forall n, a n
 != 1) (hb : forall n, b n != 1) (h : ofDigits a = ofDigits b) : a = b
参数：ha : forall n, a n != 1；hb : forall n, b n != 1；h : ofDigits a = ofDigits b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 129 条，此处仅展示前 30 条）

--- 原说明 ---
If two base-3 representations using only digits `0` and `2` define the same numb
er,
then the sequences must be equal.
This uniqueness fails for general base-3 representations (e.g. `0.1000... = 0.02
22...`).
-/
theorem ofDigits_zero_two_sequence_unique {a b : ℕ → Fin 3} (ha : ∀ n, a n ≠ 1) (hb : ∀ n, b n ≠ 1)
    (h : ofDigits a = ofDigits b) :
    a = b := by
  by_contra! h
  rw [Function.ne_iff] at h
  let n0 := Nat.find h
  have h1 (n) (hn : n < n0) : a n = b n := by simpa using Nat.find_min h hn
  have h2 : a n0 ≠ b n0 := by simpa using Nat.find_spec h
  generalize n0 = n1 at h1 h2
  clear h n0
  wlog h3 : a n1 = 0 ∧ b n1 = 2 generalizing a b
  · exact this hb ha h.symm (fun n hn ↦ (h1 n hn).symm) h2.symm (by grind)
  obtain ⟨h3, h4⟩ := h3
  clear h2
  have : ∑ x ∈ Finset.range n1, ofDigitsTerm a x = ∑ x ∈ Finset.range n1, ofDigitsTerm b x := by
    apply Finset.sum_congr rfl
    grind [ofDigitsTerm]
  rw [ofDigits_eq_sum_add_ofDigits a (n1 + 1),
    ofDigits_eq_sum_add_ofDigits b (n1 + 1), Finset.sum_range_succ,
    Finset.sum_range_succ, this] at h
  replace h : ofDigitsTerm a n1 + (3⁻¹ ^ n1 * ofDigits fun i ↦ a (1 + n1 + i)) * (1 / 3) =
      (3⁻¹ ^ n1 * ofDigits fun i ↦ b (1 + n1 + i)) * (1 / 3) + ofDigitsTerm b n1 := by
    ring_nf at h
    linarith
  simp only [ofDigitsTerm, h3, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero,
    Nat.cast_ofNat, pow_succ, mul_inv_rev, zero_mul, inv_pow, one_div, zero_add, h4,
    Nat.mod_succ] at h
  replace h : (ofDigits fun i ↦ a (1 + n1 + i)) * 3⁻¹ =
      (ofDigits fun i ↦ b (1 + n1 + i)) * 3⁻¹ + 2 * 3⁻¹ := by
    rw [← mul_right_inj' (show ((3 : ℝ) ^ n1)⁻¹ ≠ 0 by positivity)]
    linarith
  linarith [ofDigits_nonneg (fun i ↦ b (1 + n1 + i)), ofDigits_le_one (fun i ↦ a (1 + n1 + i))]

/-- Given `x ∈ [0, 1/3] ∪ [2/3, 1]` (i.e. a level of the Cantor set),
this function rescales the interval containing `x` back to `[0, 1]`.
Used to iteratively extract the ternary representation of `x`. -/
/-
**cantorStep** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cantorStep (x : Real) : Real
参数：x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `x ∈ [0, 1/3] ∪ [2/3, 1]` (i.e. a level of the Cantor set),
this function rescales the interval containing `x` back to `[0, 1]`.
Used to iteratively extract the ternary representation of `x`.
-/
noncomputable def cantorStep (x : ℝ) : ℝ :=
  if x ∈ Set.Icc 0 (1 / 3) then
    3 * x
  else
    3 * x - 2
/-
**cantorStep_mem_cantorSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cantorStep_mem_cantorSet {x : Real} (hx : x in cantorSet) : cantorStep x i
n cantorSet
参数：hx : x in cantorSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cantorSet_eq_union_halves`：cantorSet_eq_union_halves : cantorSet = (· / 
3) '' cantorSet union (fun x => (2 + x) / 3) '' cantorSet
-/
theorem cantorStep_mem_cantorSet {x : ℝ} (hx : x ∈ cantorSet) : cantorStep x ∈ cantorSet := by
  simp only [cantorStep]
  obtain ⟨y, hy, rfl | rfl⟩ : ∃ y ∈ cantorSet, y / 3 = x ∨ (2 + y) / 3 = x := by
    rw [cantorSet_eq_union_halves] at hx
    grind
  all_goals
    grind [cantorSet_subset_unitInterval]

/-- The infinite sequence obtained by repeatedly applying `cantorStep` to `x`. -/
/-
**cantorSequence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cantorSequence (x : Real) : Stream' Real
参数：x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infinite sequence obtained by repeatedly applying `cantorStep` to `x`.
-/
noncomputable def cantorSequence (x : ℝ) : Stream' ℝ :=
  Stream'.iterate cantorStep x
/-
**cantorSequence_mem_cantorSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cantorSequence_mem_cantorSet {x : Real} (hx : x in cantorSet) (n : Nat) : 
(cantorSequence x).get n in cantorSet
参数：hx : x in cantorSet；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cantorStep_mem_cantorSet`：cantorStep_mem_cantorSet {x : Real} (hx : x in
 cantorSet) : cantorStep x in cantorSet
-/
theorem cantorSequence_mem_cantorSet {x : ℝ} (hx : x ∈ cantorSet) (n : ℕ) :
    (cantorSequence x).get n ∈ cantorSet := by
  induction n with
  | zero => simpa [cantorSequence]
  | succ n ih => exact cantorStep_mem_cantorSet ih

/-- Points of the Cantor set correspond to infinite paths in the full binary tree.
at each level `n`, the set `preCantorSet (n + 1)` splits each interval in
`preCantorSet n` into two parts.
Given `x ∈ cantorSet`, the point `x` lies in one of the intervals of `preCantorSet n`.
This function tracks which of the two intervals in `preCantorSet (n + 1)`
contains `x` at each step, producing the corresponding path as a stream of booleans. -/
/-
**cantorToBinary** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cantorToBinary (x : Real) : Stream' Bool
参数：x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Points of the Cantor set correspond to infinite paths in the full binary tree.
at each level `n`, the set `preCantorSet (n + 1)` splits each interval in
`preCantorSet n` into two parts.
Given `x ∈ cantorSet`, the point `x` lies in one of the intervals of `preCantorS
et n`.
This function tracks which of the two intervals in `preCantorSet (n + 1)`
contains `x` at each step, producing the corresponding path as a stream of boole
ans.
-/
noncomputable def cantorToBinary (x : ℝ) : Stream' Bool :=
  (cantorSequence x).map fun x ↦
    if x ∈ Set.Icc 0 (1 / 3) then
      false
    else
      true

/-- Given `x` in the Cantor set, return its ternary representation `(d₀, d₁, …)`
using only digits `0` and `2`, such that `x = 0.d₀d₁...` in base-3. -/
/-
**cantorToTernary** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cantorToTernary (x : Real) : Stream' (Fin 3)
参数：x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `x` in the Cantor set, return its ternary representation `(d₀, d₁, …)`
using only digits `0` and `2`, such that `x = 0.d₀d₁...` in base-3.
-/
noncomputable def cantorToTernary (x : ℝ) : Stream' (Fin 3) :=
  (cantorToBinary x).map (cond · 2 0)
/-
**ofDigits_bool_to_fin_three_mem_cantorSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDigits_bool_to_fin_three_mem_cantorSet (f : Nat -> Bool) : ofDigits (fun
 i => cond (f i) (2 : Fin 3) 0) in cantorSet
参数：f : Nat -> Bool。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ofDigits_zero_two_sequence_mem_cantorSet`：ofDigits_zero_two_sequence_mem
_cantorSet {a : Nat -> Fin 3} (h : forall n, a n != 1) : ofDigits a in cantorSet
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem ofDigits_bool_to_fin_three_mem_cantorSet (f : ℕ → Bool) :
    ofDigits (fun i ↦ cond (f i) (2 : Fin 3) 0) ∈ cantorSet :=
  ofDigits_zero_two_sequence_mem_cantorSet (by grind)
/-
**cantorToTernary_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cantorToTernary_ne_one {x : Real} {n : Nat} : (cantorToTernary x).get n !=
 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cantorToTernary_ne_one {x : ℝ} {n : ℕ} : (cantorToTernary x).get n ≠ 1 := by
  grind [cantorToTernary, Stream'.get_map]
/-
**cantorSequence_get_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cantorSequence_get_succ (x : Real) (n : Nat) : (cantorSequence x).get (n +
 1) = 3 * ((cantorSequence x).get n - 3 ^ n * ofDigitsTerm (cantorToTernary x).g
et n)
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.if_true_right`：∀ (p : Prop) [h : Decidable p] (t : Bool), (if p the
n t else true) = (!decide p || t)
· 使用定理 `Bool.or_false`：∀ (b : Bool), (b || false) = b
· 使用定理 `Bool.cond_not`：∀ {α : Sort u_1} (b : Bool) (t e : α), (bif !b then t els
e e) = bif b then e else t
· 使用定理 `Bool.cond_decide`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (t e 
: α), (bif decide p then t else e) = if p then t else e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
（共 89 条，此处仅展示前 30 条）
-/
theorem cantorSequence_get_succ (x : ℝ) (n : ℕ) :
    (cantorSequence x).get (n + 1) =
      3 * ((cantorSequence x).get n - 3 ^ n * ofDigitsTerm (cantorToTernary x).get n) := by
  simp only [cantorSequence, ofDigitsTerm, cantorToTernary, cantorToBinary, Set.mem_Icc,
    Bool.if_true_right, Bool.or_false, Stream'.get_map, Bool.cond_not, Bool.cond_decide,
    Stream'.get_succ_iterate', cantorStep]
  split_ifs <;> simp
  field
/-
**cantorSequence_eq_self_sub_sum_cantorToTernary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cantorSequence_eq_self_sub_sum_cantorToTernary (x : Real) (n : Nat) : (can
torSequence x).get n = (x - ∑ i in Finset.range n, ofDigitsTerm (cantorToTernary
 x).get i) * 3 ^ n
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `cantorSequence_get_succ`：cantorSequence_get_succ (x : Real) (n : Nat) : 
(cantorSequence x).get (n + 1) = 3 * ((cantorSequence x).get n - 3 ^ n * ofDigit
sTerm (cantor…
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 49 条，此处仅展示前 30 条）
-/
theorem cantorSequence_eq_self_sub_sum_cantorToTernary (x : ℝ) (n : ℕ) :
    (cantorSequence x).get n =
    (x - ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToTernary x).get i) * 3 ^ n := by
  induction n with
  | zero => simp [cantorSequence]
  | succ n ih => rw [cantorSequence_get_succ, ih, Finset.sum_range_succ]; ring
/-
**ofDigits_cantorToTernary_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDigits_cantorToTernary_sum_le {x : Real} (hx : x in cantorSet) {n : Nat}
 : ∑ i in Finset.range n, ofDigitsTerm (cantorToTernary x) i <= x
参数：hx : x in cantorSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cantorSequence_mem_cantorSet`：cantorSequence_mem_cantorSet {x : Real} (h
x : x in cantorSet) (n : Nat) : (cantorSequence x).get n in cantorSet
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `cantorSet_subset_unitInterval`：cantorSet_subset_unitInterval : cantorSet
 subseteq Set.Icc 0 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cantorSequence_eq_self_sub_sum_cantorToTernary`：cantorSequence_eq_self_s
ub_sum_cantorToTernary (x : Real) (n : Nat) : (cantorSequence x).get n = (x - ∑ 
i in Finset.range n, ofDigitsTerm (c…
-/
theorem ofDigits_cantorToTernary_sum_le {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToTernary x) i ≤ x := by
  have h_mem := cantorSequence_mem_cantorSet hx n
  rw [cantorSequence_eq_self_sub_sum_cantorToTernary x n] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  simpa using! h_mem.left
/-
**le_ofDigits_cantorToTernary_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ofDigits_cantorToTernary_sum {x : Real} (hx : x in cantorSet) {n : Nat}
 : x - (3⁻¹ : Real) ^ n <= ∑ i in Finset.range n, ofDigitsTerm (cantorToTernary 
x) i
参数：hx : x in cantorSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cantorSequence_mem_cantorSet`：cantorSequence_mem_cantorSet {x : Real} (h
x : x in cantorSet) (n : Nat) : (cantorSequence x).get n in cantorSet
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_left₀`：mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflect
LE α] (a0 : 0 < a) : b * a <= c * a ↔ b <= c
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 74 条，此处仅展示前 30 条）
-/
theorem le_ofDigits_cantorToTernary_sum {x : ℝ} (hx : x ∈ cantorSet) {n : ℕ} :
    x - (3⁻¹ : ℝ) ^ n ≤ ∑ i ∈ Finset.range n, ofDigitsTerm (cantorToTernary x) i := by
  have h_mem := cantorSequence_mem_cantorSet hx n
  rw [cantorSequence_eq_self_sub_sum_cantorToTernary x n] at h_mem
  apply cantorSet_subset_unitInterval at h_mem
  simp only [Set.mem_Icc] at h_mem
  rw [← mul_le_mul_iff_left₀ (show 0 < (3 : ℝ) ^ n by positivity), sub_mul, inv_pow,
    inv_mul_cancel₀ (by simp)]
  linarith!
/-
**ofDigits_cantorToTernary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDigits_cantorToTernary {x : Real} (hx : x in cantorSet) : ofDigits (cant
orToTernary x).get = x
参数：hx : x in cantorSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_iff_tendsto_nat_of_summable_norm`：hasSum_iff_tendsto_nat_of_summa
ble_norm {f : Nat -> E} {a : E} (hf : Summable fun i => ‖f i‖) : HasSum f a ↔ Te
ndsto (fun n : Nat => ∑ i in …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Real.ofDigitsTerm_nonneg`：ofDigitsTerm_nonneg {b : Nat} {digits : Nat ->
 Fin b} {n : Nat} : 0 <= ofDigitsTerm digits n
· 使用定理 `Real.summable_ofDigitsTerm`：summable_ofDigitsTerm {b : Nat} {digits : Na
t -> Fin b} : Summable (ofDigitsTerm digits)
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_sub_nhds_zero_iff`：∀ {G : Type w} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] {α : Type u_1} {l : Filter α}   {x
 : G} {u : α → …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`：tendsto_pow_atTop_nhds_zero_o
f_abs_lt_one {r : Real} (h : |r| < 1) : Tendsto (fun n : Nat => r ^ n) atTop (𝓝 
0)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_abs_nonneg`：isNNRat_abs_nonneg {α : Type*} 
[DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α] {a : α} {num den : Nat}
 (ra : IsNNRat a num den) : I…
（共 39 条，此处仅展示前 30 条）
-/
theorem ofDigits_cantorToTernary {x : ℝ} (hx : x ∈ cantorSet) :
    ofDigits (cantorToTernary x).get = x := by
  simp only [ofDigits]
  rw [HasSum.tsum_eq]
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  swap
  · simpa only [norm_of_nonneg ofDigitsTerm_nonneg] using summable_ofDigitsTerm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n ↦ x - (3⁻¹ : ℝ) ^ n) (h := fun _ ↦ x)
  · rw [← tendsto_sub_nhds_zero_iff]
    simp only [sub_sub_cancel_left]
    rw [show 0 = -(0 : ℝ) by simp]
    exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)).neg
  · exact tendsto_const_nhds
  · exact fun _ ↦ le_ofDigits_cantorToTernary_sum hx
  · exact fun _ ↦ ofDigits_cantorToTernary_sum_le hx
/-
**cantorSet_eq_zero_two_ofDigits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cantorSet_eq_zero_two_ofDigits : cantorSet = {x | exists a : Nat -> Fin 3,
 (forall i, a i != 1) ∧ ofDigits a = x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `cantorToTernary_ne_one`：cantorToTernary_ne_one {x : Real} {n : Nat} : (c
antorToTernary x).get n != 1
· 使用定理 `ofDigits_cantorToTernary`：ofDigits_cantorToTernary {x : Real} (hx : x in
 cantorSet) : ofDigits (cantorToTernary x).get = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ofDigits_zero_two_sequence_mem_cantorSet`：ofDigits_zero_two_sequence_mem
_cantorSet {a : Nat -> Fin 3} (h : forall n, a n != 1) : ofDigits a in cantorSet
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem cantorSet_eq_zero_two_ofDigits :
    cantorSet = {x | ∃ a : ℕ → Fin 3, (∀ i, a i ≠ 1) ∧ ofDigits a = x} := by
  ext x
  refine ⟨fun h ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · use cantorToTernary x
    exact ⟨fun _ ↦ cantorToTernary_ne_one, ofDigits_cantorToTernary h⟩
  · rw [← ha.right]
    exact ofDigits_zero_two_sequence_mem_cantorSet ha.left

end ternary02

/-!
## The Cantor set is homeomorphic to `ℕ → Bool`
-/

open Real

/-- Canonical bijection between the Cantor set and infinite binary tree. -/
/-
**cantorSetEquivNatToBool** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cantorSetEquivNatToBool : cantorSet ≃ (Nat -> Bool) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ofDigits_bool_to_fin_three_mem_cantorSet`：ofDigits_bool_to_fin_three_mem
_cantorSet (f : Nat -> Bool) : ofDigits (fun i => cond (f i) (2 : Fin 3) 0) in c
antorSet

--- 原说明 ---
Canonical bijection between the Cantor set and infinite binary tree.
-/
noncomputable def cantorSetEquivNatToBool : cantorSet ≃ (ℕ → Bool) where
  toFun := fun ⟨x, h⟩ ↦ (cantorToBinary x).get
  invFun (y : ℕ → Bool) :=
    ⟨ofDigits (fun i ↦ cond (y i) 2 0), ofDigits_bool_to_fin_three_mem_cantorSet y⟩
  left_inv := by
    intro ⟨x, hx⟩
    simp only [Fin.isValue, Subtype.mk.injEq]
    exact ofDigits_cantorToTernary hx
  right_inv := by
    intro y
    simp only [Fin.isValue]
    set x := @ofDigits 3 (fun i ↦ cond (y i) 2 0)
    have := ofDigits_cantorToTernary (ofDigits_bool_to_fin_three_mem_cantorSet y)
    apply ofDigits_zero_two_sequence_unique at this
    rotate_left
    · exact fun n ↦ cantorToTernary_ne_one
    · grind
    ext n
    apply congrFun (a := n) at this
    grind [cantorToTernary, Stream'.get_map]

/-- Canonical homeomorphism between the Cantor set and `ℕ → Bool`. -/
/-
**cantorSetHomeomorphNatToBool** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cantorSetHomeomorphNatToBool : cantorSet ≃ₜ (Nat -> Bool)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Canonical homeomorphism between the Cantor set and `ℕ → Bool`.
-/
noncomputable def cantorSetHomeomorphNatToBool : cantorSet ≃ₜ (ℕ → Bool) :=
  Homeomorph.symm <| Continuous.homeoOfEquivCompactToT2 (f := cantorSetEquivNatToBool.symm)
    (Continuous.subtype_mk (Continuous.comp continuous_ofDigits (by fun_prop)) _)

/-- The Cantor space is homeomorphic to a countable product of copies of itself. -/
/-
**cantorSpaceHomeomorphNatToCantorSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cantorSpaceHomeomorphNatToCantorSpace : (Nat -> Bool) ≃ₜ (Nat -> Nat -> Bo
ol)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The Cantor space is homeomorphic to a countable product of copies of itself.
-/
def cantorSpaceHomeomorphNatToCantorSpace : (ℕ → Bool) ≃ₜ (ℕ → ℕ → Bool) :=
  (Homeomorph.piCongrLeft Nat.pairEquiv.symm).trans Homeomorph.piCurry
