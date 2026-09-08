/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Compatibility of algebraic operations with metric space structures

In this file we define mixin typeclasses `LipschitzMul`, `LipschitzAdd`,
`IsBoundedSMul` expressing compatibility of multiplication, addition and scalar-multiplication
operations with an underlying metric space structure.  The intended use case is to abstract certain
properties shared by normed groups and by `R≥0`.

## Implementation notes

We deduce a `ContinuousMul` instance from `LipschitzMul`, etc.  In principle there should
be an intermediate typeclass for uniform spaces, but the algebraic hierarchy there (see
`IsUniformGroup`) is structured differently.

-/

@[expose] public section

open NNReal Filter Set
open scoped Topology Uniformity

noncomputable section

variable (α β : Type*) [PseudoMetricSpace α] [PseudoMetricSpace β]

section LipschitzMul

/-- Class `LipschitzAdd M` says that the addition `(+) : X × X → X` is Lipschitz jointly in
the two arguments. -/
/-
**LipschitzAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(β : Type u_2) → [PseudoMetricSpace β] → [AddMonoid β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class `LipschitzAdd M` says that the addition `(+) : X × X → X` is Lipschitz joi
ntly in
the two arguments.
-/
class LipschitzAdd [AddMonoid β] : Prop where
  lipschitz_add : ∃ C, LipschitzWith C fun p : β × β => p.1 + p.2

/-- Class `LipschitzMul M` says that the multiplication `(*) : X × X → X` is Lipschitz jointly
in the two arguments. -/
@[to_additive]
/-
**LipschitzMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(β : Type u_2) → [PseudoMetricSpace β] → [Monoid β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class `LipschitzMul M` says that the multiplication `(*) : X × X → X` is Lipschi
tz jointly
in the two arguments.
-/
class LipschitzMul [Monoid β] : Prop where
  lipschitz_mul : ∃ C, LipschitzWith C fun p : β × β => p.1 * p.2

variable [Monoid β]

/-- The Lipschitz constant of a monoid `β` satisfying `LipschitzMul` -/
@[to_additive /-- The Lipschitz constant of an `AddMonoid` `β` satisfying `LipschitzAdd` -/]
/-
**LipschitzMul.C** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LipschitzMul.C [_i : LipschitzMul β] : Real>=0
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzMul.lipschitz_mul`：∀ {β : Type u_2} {inst : PseudoMetricSpace β
} {inst_1 : Monoid β} [self : LipschitzMul β],   ∃ C, LipschitzWith C fun p => p
.1 * p.2

--- 原说明 ---
The Lipschitz constant of a monoid `β` satisfying `LipschitzMul`
-/
def LipschitzMul.C [_i : LipschitzMul β] : ℝ≥0 := Classical.choose _i.lipschitz_mul

variable {β}

@[to_additive]
/-
**lipschitzWith_lipschitz_const_mul_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_lipschitz_const_mul_edist [_i : LipschitzMul β] : LipschitzW
ith (LipschitzMul.C β) fun p : β × β => p.1 * p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `LipschitzMul.lipschitz_mul`：∀ {β : Type u_2} {inst : PseudoMetricSpace β
} {inst_1 : Monoid β} [self : LipschitzMul β],   ∃ C, LipschitzWith C fun p => p
.1 * p.2
-/
theorem lipschitzWith_lipschitz_const_mul_edist [_i : LipschitzMul β] :
    LipschitzWith (LipschitzMul.C β) fun p : β × β => p.1 * p.2 :=
  Classical.choose_spec _i.lipschitz_mul

variable [LipschitzMul β]

@[to_additive]
/-
**lipschitz_with_lipschitz_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitz_with_lipschitz_const_mul : forall p q : β × β, dist (p.1 * p.2) 
(q.1 * q.2) <= LipschitzMul.C β * dist p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lipschitzWith_iff_dist_le_mul`：lipschitzWith_iff_dist_le_mul [PseudoMetr
icSpace α] [PseudoMetricSpace β] {K : Real>=0} {f : α -> β} : LipschitzWith K f 
↔ forall x y, dist …
· 使用定理 `lipschitzWith_lipschitz_const_mul_edist`：lipschitzWith_lipschitz_const_m
ul_edist [_i : LipschitzMul β] : LipschitzWith (LipschitzMul.C β) fun p : β × β 
=> p.1 * p.2
-/
theorem lipschitz_with_lipschitz_const_mul :
    ∀ p q : β × β, dist (p.1 * p.2) (q.1 * q.2) ≤ LipschitzMul.C β * dist p q := by
  rw [← lipschitzWith_iff_dist_le_mul]
  exact lipschitzWith_lipschitz_const_mul_edist

-- see Note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LipschitzMul.continuousMul : ContinuousMul β :=
  ⟨lipschitzWith_lipschitz_const_mul_edist.continuous⟩

@[to_additive]
/-
**Submonoid.lipschitzMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submonoid.lipschitzMul (s : Submonoid β) : LipschitzMul s where lipschitz_
mul
参数：s : Submonoid β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lipschitzWith_lipschitz_const_mul_edist`：lipschitzWith_lipschitz_const_m
ul_edist [_i : LipschitzMul β] : LipschitzWith (LipschitzMul.C β) fun p : β × β 
=> p.1 * p.2
-/
instance Submonoid.lipschitzMul (s : Submonoid β) : LipschitzMul s where
  lipschitz_mul := ⟨LipschitzMul.C β, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    convert! lipschitzWith_lipschitz_const_mul_edist ⟨(x₁ : β), x₂⟩ ⟨y₁, y₂⟩ using 1⟩

@[to_additive]
/-
**MulOpposite.lipschitzMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.lipschitzMul : LipschitzMul βᵐᵒᵖ where lipschitz_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `lipschitzWith_lipschitz_const_mul_edist`：lipschitzWith_lipschitz_const_m
ul_edist [_i : LipschitzMul β] : LipschitzWith (LipschitzMul.C β) fun p : β × β 
=> p.1 * p.2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
-/
instance MulOpposite.lipschitzMul : LipschitzMul βᵐᵒᵖ where
  lipschitz_mul := ⟨LipschitzMul.C β, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ =>
    (lipschitzWith_lipschitz_const_mul_edist ⟨x₂.unop, x₁.unop⟩ ⟨y₂.unop, y₁.unop⟩).trans_eq
      (congr_arg _ <| max_comm _ _)⟩

-- this instance could be deduced from `NormedAddCommGroup.lipschitzAdd`, but we prove it
-- separately here so that it is available earlier in the hierarchy
/-
**Real.hasLipschitzAdd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.hasLipschitzAdd : LipschitzAdd Real where lipschitz_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `abs_add_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddCommGroup α
] [AddLeftMono α] (a b : α), |a + b| ≤ |a| + |b|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
instance Real.hasLipschitzAdd : LipschitzAdd ℝ where
  lipschitz_add := ⟨2, LipschitzWith.of_dist_le_mul fun p q => by
    simp only [Real.dist_eq, Prod.dist_eq, NNReal.coe_ofNat,
      add_sub_add_comm, two_mul]
    refine le_trans (abs_add_le (p.1 - q.1) (p.2 - q.2)) ?_
    exact add_le_add (le_max_left _ _) (le_max_right _ _)⟩

-- this instance has the same proof as `AddSubmonoid.lipschitzAdd`, but the former can't
-- directly be applied here since `ℝ≥0` is a subtype of `ℝ`, not an additive submonoid.
/-
**NNReal.hasLipschitzAdd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNReal.hasLipschitzAdd : LipschitzAdd Real>=0 where lipschitz_add
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `lipschitzWith_lipschitz_const_add_edist`：∀ {β : Type u_2} [inst : Pseudo
MetricSpace β] [inst_1 : AddMonoid β] [_i : LipschitzAdd β],   LipschitzWith (Li
pschitzAdd.C β) fun p => p.1 …
-/
instance NNReal.hasLipschitzAdd : LipschitzAdd ℝ≥0 where
  lipschitz_add := ⟨LipschitzAdd.C ℝ, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    exact lipschitzWith_lipschitz_const_add_edist ⟨(x₁ : ℝ), x₂⟩ ⟨y₁, y₂⟩⟩

end LipschitzMul

section IsBoundedSMul

variable [Zero α] [Zero β] [SMul α β]

/-- Mixin typeclass on a scalar action of a metric space `α` on a metric space `β` both with
distinguished points `0`, requiring compatibility of the action in the sense that
`dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂` and
`dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0`.

If `[NormedDivisionRing α] [SeminormedAddCommGroup β] [Module α β]` are assumed, then prefer writing
`[NormSMulClass α β]` instead of using `[IsBoundedSMul α β]`, since while equivalent, typeclass
search can only infer the latter from the former and not vice versa. -/
/-
**IsBoundedSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) →   (β : Type u_2) → [PseudoMetricSpace α] → [PseudoMetricS
pace β] → [Zero α] → [Zero β] → [SMul α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mixin typeclass on a scalar action of a metric space `α` on a metric space `β` b
oth with
distinguished points `0`, requiring compatibility of the action in the sense tha
t
`dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂` and
`dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0`.

If `[NormedDivisionRing α] [SeminormedAddCommGroup β] [Module α β]` are assumed,
 then prefer writing
`[NormSMulClass α β]` instead of using `[IsBoundedSMul α β]`, since while equiva
lent, typeclass
search can only infer the latter from the former and not vice versa.
-/
class IsBoundedSMul : Prop where
  dist_smul_pair' : ∀ x : α, ∀ y₁ y₂ : β, dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂
  dist_pair_smul' : ∀ x₁ x₂ : α, ∀ y : β, dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0

variable {α β}
variable [IsBoundedSMul α β]
/-
**dist_smul_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • y₂) <= dist x 0 * 
dist y₁ y₂
参数：x : α；y₁ y₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.dist_smul_pair'`：∀ {α : Type u_1} {β : Type u_2} {inst : P
seudoMetricSpace α} {inst_1 : PseudoMetricSpace β} {inst_2 : Zero α}   {inst_3 :
 Zero β} {inst_4 : …
-/
theorem dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂ :=
  IsBoundedSMul.dist_smul_pair' x y₁ y₂
/-
**dist_pair_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ • y) <= dist x₁ x₂ 
* dist y 0
参数：x₁ x₂ : α；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.dist_pair_smul'`：∀ {α : Type u_1} {β : Type u_2} {inst : P
seudoMetricSpace α} {inst_1 : PseudoMetricSpace β} {inst_2 : Zero α}   {inst_3 :
 Zero β} {inst_4 : …
-/
theorem dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0 :=
  IsBoundedSMul.dist_pair_smul' x₁ x₂ y
/-
**Bornology.IsBounded.uniformContinuousOn_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bornology.IsBounded.uniformContinuousOn_smul {s : Set (α × β)} (hs : IsBou
nded s) : UniformContinuousOn (· • ·).uncurry s
参数：α × β；hs : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset_ball_lt`：∀ {α : Type u} {s : Set α} [inst : P
seudoMetricSpace α],   Bornology.IsBounded s → ∀ (a : ℝ) (c : α), ∃ r, a < r ∧ s
 ⊆ Metric.ball c r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.uniformContinuousOn_iff_le`：uniformContinuousOn_iff_le [PseudoMet
ricSpace β] {f : α -> β} {s : Set α} : UniformContinuousOn f s ↔ forall ε > 0, e
xists δ > 0, forall x i…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用引理 `Prod.dist_eq`：Prod.dist_eq {x y : α × β} : dist x y = max (dist x.1 y.1)
 (dist x.2 y.2)
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
（共 71 条，此处仅展示前 30 条）
-/
theorem Bornology.IsBounded.uniformContinuousOn_smul {s : Set (α × β)} (hs : IsBounded s) :
    UniformContinuousOn (· • ·).uncurry s := by
  rcases hs.subset_ball_lt 0 0 with ⟨C, hC₀, hC⟩
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  refine ⟨ε / (2 * C), by positivity, fun ⟨a, b⟩ hab ⟨x, y⟩ hxy h ↦ ?_⟩
  grw [hC, Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hab hxy
  rw [Prod.dist_eq, max_le_iff] at h
  dsimp at hab hxy h ⊢
  grw [dist_triangle _ (a • y), dist_pair_smul, dist_smul_pair, hab.1, hxy.2, h.2, h.1]
  field_simp
  norm_num1

-- see Note [lower instance priority]
/-- The typeclass `IsBoundedSMul` on a metric-space scalar action implies continuity of the
action. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass `IsBoundedSMul` on a metric-space scalar action implies continuity
 of the
action.
-/
instance (priority := 100) IsBoundedSMul.continuousSMul : ContinuousSMul α β where
  continuous_smul := by
    rw [continuous_iff_continuousAt]
    intro x
    refine Metric.isBounded_ball (x := 0) (r := dist x 0 + 1) |>.uniformContinuousOn_smul
      |>.continuousOn |>.continuousAt ?_
    exact Metric.isOpen_ball.mem_nhds (by simp)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsBoundedSMul.toUniformContinuousConstSMul :
    UniformContinuousConstSMul α β :=
  ⟨fun c => ((lipschitzWith_iff_dist_le_mul (K := nndist c 0)).2 fun _ _ =>
    dist_smul_pair c _ _).uniformContinuous⟩

@[to_fun]
/-
**TendstoLocallyUniformlyOn.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem TendstoLocallyUniformlyOn.smul₀_of_isBoundedUnder {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {G : ι → X → β} {f : X → α} {g : X → β} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ∀ x ∈ s, (𝓝[s] x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (f y) 0))
    (hg : ∀ x ∈ s, (𝓝[s] x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (g y) 0)) :
    TendstoLocallyUniformlyOn (F • G) (f • g) l s := by
  have H := hF.prodMk hG
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rcases (hf x hx).sup (hg x hx) with ⟨C, hC⟩
  simp_rw [Filter.eventually_map, max_le_iff] at hC
  refine Tendsto.comp
    (Metric.isBounded_ball (x := (0 : α × β)) (r := C + 1)).uniformContinuousOn_smul
    (tendsto_inf.mpr ⟨H x hx, tendsto_principal.mpr ?_⟩)
  filter_upwards [hF x hx (Metric.dist_mem_uniformity one_pos),
    hG x hx (Metric.dist_mem_uniformity one_pos), tendsto_snd hC] with ⟨n, y⟩ hFn hGn hfg
  simp only [mem_prod, Metric.mem_ball, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero, sup_lt_iff,
    mem_preimage, mem_ofPred] at hFn hGn hfg ⊢
  grw [dist_triangle_left (F n y) 0 (f y), dist_triangle_left (G n y) 0 (g y)]
  constructor <;> constructor <;> linarith

@[to_fun]
/-
**TendstoLocallyUniformlyOn.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.mul (hf : TendstoLocallyUniformlyOn F f l s) (hg
 : TendstoLocallyUniformlyOn G g l s) : TendstoLocallyUniformlyOn (F * G) (f * g
) l s
参数：hf : TendstoLocallyUniformlyOn F f l s；hg : TendstoLocallyUniformlyOn G g l s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformlyOn`：UniformContinuous.comp
_tendstoLocallyUniformlyOn (hg : UniformContinuous g) (hf : TendstoLocallyUnifor
mlyOn F f p s) : TendstoLocallyUniform…
· 使用定理 `uniformContinuous_mul`：uniformContinuous_mul : UniformContinuous fun p :
 α × α => p.1 * p.2
· 使用定理 `TendstoLocallyUniformlyOn.prodMk`：TendstoLocallyUniformlyOn.prodMk [Unif
ormSpace γ] {G : ι -> α -> γ} {g : α -> γ} (hF : TendstoLocallyUniformlyOn F f p
 s) (hG : TendstoLocal…
-/
theorem TendstoLocallyUniformlyOn.mul₀_of_isBoundedUnder {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {s : Set X} {F : ι → X → M} {G : ι → X → M} {f : X → M} {g : X → M} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ∀ x ∈ s, (𝓝[s] x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (f y) 0))
    (hg : ∀ x ∈ s, (𝓝[s] x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (g y) 0)) :
    TendstoLocallyUniformlyOn (F * G) (f * g) l s :=
  hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]
/-
**TendstoLocallyUniformly.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem TendstoLocallyUniformly.smul₀_of_isBoundedUnder {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {G : ι → X → β} {f : X → α} {g : X → β} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : ∀ x, (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (f y) 0))
    (hg : ∀ x, (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (g y) 0)) :
    TendstoLocallyUniformly (F • G) (f • g) l := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.smul₀_of_isBoundedUnder hG <;> simpa

@[to_fun]
/-
**TendstoLocallyUniformly.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.mul (hf : TendstoLocallyUniformly F f l) (hg : Ten
dstoLocallyUniformly G g l) : TendstoLocallyUniformly (F * G) (f * g) l
参数：hf : TendstoLocallyUniformly F f l；hg : TendstoLocallyUniformly G g l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformly`：UniformContinuous.comp_t
endstoLocallyUniformly (hg : UniformContinuous g) (hf : TendstoLocallyUniformly 
F f p) : TendstoLocallyUniformly (g …
· 使用定理 `uniformContinuous_mul`：uniformContinuous_mul : UniformContinuous fun p :
 α × α => p.1 * p.2
· 使用定理 `TendstoLocallyUniformly.prodMk`：TendstoLocallyUniformly.prodMk [UniformS
pace γ] {G : ι -> α -> γ} {g : α -> γ} (hF : TendstoLocallyUniformly F f p) (hG 
: TendstoLocallyUnif…
-/
theorem TendstoLocallyUniformly.mul₀_of_isBoundedUnder {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {F : ι → X → M} {G : ι → X → M} {f : X → M} {g : X → M} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : ∀ x, (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (f y) 0))
    (hg : ∀ x, (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (g y) 0)) :
    TendstoLocallyUniformly (F * G) (f * g) l :=
  hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]
/-
**TendstoLocallyUniformlyOn.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem TendstoLocallyUniformlyOn.smul₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {G : ι → X → β} {f : X → α} {g : X → β} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hfc : ContinuousOn f s) (hgc : ContinuousOn g s) :
    TendstoLocallyUniformlyOn (F • G) (f • g) l s :=
  hF.smul₀_of_isBoundedUnder hG
    (fun x hx ↦ ((hfc x hx).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x hx ↦ ((hgc x hx).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]
/-
**TendstoLocallyUniformlyOn.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.mul (hf : TendstoLocallyUniformlyOn F f l s) (hg
 : TendstoLocallyUniformlyOn G g l s) : TendstoLocallyUniformlyOn (F * G) (f * g
) l s
参数：hf : TendstoLocallyUniformlyOn F f l s；hg : TendstoLocallyUniformlyOn G g l s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformlyOn`：UniformContinuous.comp
_tendstoLocallyUniformlyOn (hg : UniformContinuous g) (hf : TendstoLocallyUnifor
mlyOn F f p s) : TendstoLocallyUniform…
· 使用定理 `uniformContinuous_mul`：uniformContinuous_mul : UniformContinuous fun p :
 α × α => p.1 * p.2
· 使用定理 `TendstoLocallyUniformlyOn.prodMk`：TendstoLocallyUniformlyOn.prodMk [Unif
ormSpace γ] {G : ι -> α -> γ} {g : α -> γ} (hF : TendstoLocallyUniformlyOn F f p
 s) (hG : TendstoLocal…
-/
theorem TendstoLocallyUniformlyOn.mul₀ {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {s : Set X} {F : ι → X → M} {G : ι → X → M} {f : X → M} {g : X → M} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    TendstoLocallyUniformlyOn (F * G) (f * g) l s :=
  hF.smul₀ hG hf hg

@[to_fun]
/-
**TendstoLocallyUniformly.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem TendstoLocallyUniformly.smul₀ {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {G : ι → X → β} {f : X → α} {g : X → β} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hfc : Continuous f) (hgc : Continuous g) :
    TendstoLocallyUniformly (F • G) (f • g) l :=
  hF.smul₀_of_isBoundedUnder hG
    (fun x ↦ ((hfc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x ↦ ((hgc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]
/-
**TendstoLocallyUniformly.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.mul (hf : TendstoLocallyUniformly F f l) (hg : Ten
dstoLocallyUniformly G g l) : TendstoLocallyUniformly (F * G) (f * g) l
参数：hf : TendstoLocallyUniformly F f l；hg : TendstoLocallyUniformly G g l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp_tendstoLocallyUniformly`：UniformContinuous.comp_t
endstoLocallyUniformly (hg : UniformContinuous g) (hf : TendstoLocallyUniformly 
F f p) : TendstoLocallyUniformly (g …
· 使用定理 `uniformContinuous_mul`：uniformContinuous_mul : UniformContinuous fun p :
 α × α => p.1 * p.2
· 使用定理 `TendstoLocallyUniformly.prodMk`：TendstoLocallyUniformly.prodMk [UniformS
pace γ] {G : ι -> α -> γ} {g : α -> γ} (hF : TendstoLocallyUniformly F f p) (hG 
: TendstoLocallyUnif…
-/
theorem TendstoLocallyUniformly.mul₀ {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {F : ι → X → M} {G : ι → X → M} {f : X → M} {g : X → M} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : Continuous f) (hg : Continuous g) :
    TendstoLocallyUniformly (F * G) (f * g) l :=
  hF.smul₀ hG hf hg

-- this instance could be deduced from `NormedSpace.isBoundedSMul`, but we prove it separately
-- here so that it is available earlier in the hierarchy
/-
**Real.isBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.isBoundedSMul : IsBoundedSMul Real Real where dist_smul_pair' x y₁ y₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
-/
instance Real.isBoundedSMul : IsBoundedSMul ℝ ℝ where
  dist_smul_pair' x y₁ y₂ := by simpa [Real.dist_eq, mul_sub] using (abs_mul x (y₁ - y₂)).le
  dist_pair_smul' x₁ x₂ y := by simpa [Real.dist_eq, sub_mul] using (abs_mul (x₁ - x₂) y).le
/-
**NNReal.isBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNReal.isBoundedSMul : IsBoundedSMul Real>=0 Real>=0 where dist_smul_pair'
 x y₁ y₂
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0
-/
instance NNReal.isBoundedSMul : IsBoundedSMul ℝ≥0 ℝ≥0 where
  dist_smul_pair' x y₁ y₂ := by convert! dist_smul_pair (x : ℝ) (y₁ : ℝ) y₂ using 1
  dist_pair_smul' x₁ x₂ y := by convert! dist_pair_smul (x₁ : ℝ) x₂ (y : ℝ) using 1

/-- If a scalar is central, then its right action is bounded when its left action is. -/
/-
**IsBoundedSMul.op** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsBoundedSMul.op [SMul αᵐᵒᵖ β] [IsCentralScalar α β] : IsBoundedSMul αᵐᵒᵖ 
β where dist_smul_pair'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0

--- 原说明 ---
If a scalar is central, then its right action is bounded when its left action is
.
-/
instance IsBoundedSMul.op [SMul αᵐᵒᵖ β] [IsCentralScalar α β] : IsBoundedSMul αᵐᵒᵖ β where
  dist_smul_pair' :=
    MulOpposite.rec' fun x y₁ y₂ => by simpa only [op_smul_eq_smul] using! dist_smul_pair x y₁ y₂
  dist_pair_smul' :=
    MulOpposite.rec' fun x₁ =>
      MulOpposite.rec' fun x₂ y => by simpa only [op_smul_eq_smul] using! dist_pair_smul x₁ x₂ y

end IsBoundedSMul

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [LipschitzMul α] : LipschitzAdd (Additive α) :=
  ⟨@LipschitzMul.lipschitz_mul α _ _ _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid α] [LipschitzAdd α] : LipschitzMul (Multiplicative α) :=
  ⟨@LipschitzAdd.lipschitz_add α _ _ _⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [LipschitzMul α] : LipschitzMul αᵒᵈ :=
  ‹LipschitzMul α›

variable {ι : Type*} [Fintype ι]
/-
**Pi.instIsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instIsBoundedSMul {α : Type*} {β : ι -> Type*} [PseudoMetricSpace α] [f
orall i, PseudoMetricSpace (β i)] [Zero α] [forall i, Zero (β i)] [forall i, SMu
l α (β i)] [forall i, IsBoundedSMul α (β i)] : IsBoundedSMul α (forall i, β i) w
here dist_smul_pair' x y₁ y₂
参数：β i；β i；β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `dist_pi_le_iff`：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 
<= r) : dist f g <= r ↔ forall b, dist (f b) (g b) <= r
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用引理 `dist_le_pi_dist`：dist_le_pi_dist (f g : forall b, X b) (b : β) : dist (f
 b) (g b) <= dist f g
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0
-/
instance Pi.instIsBoundedSMul {α : Type*} {β : ι → Type*} [PseudoMetricSpace α]
    [∀ i, PseudoMetricSpace (β i)] [Zero α] [∀ i, Zero (β i)] [∀ i, SMul α (β i)]
    [∀ i, IsBoundedSMul α (β i)] : IsBoundedSMul α (∀ i, β i) where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff <| by positivity).2 fun _ ↦
      (dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ ↦
      (dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (dist_le_pi_dist _ 0 _) dist_nonneg
/-
**Pi.instIsBoundedSMul'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instIsBoundedSMul' {α β : ι -> Type*} [forall i, PseudoMetricSpace (α i
)] [forall i, PseudoMetricSpace (β i)] [forall i, Zero (α i)] [forall i, Zero (β
 i)] [forall i, SMul (α i) (β i)] [forall i, IsBoundedSMul (α i) (β i)] : IsBoun
dedSMul (forall i, α i) (forall i, β i) where dist_smul_pair' x y₁ y₂
参数：α i；β i；α i；β i；α i；β i；α i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `dist_pi_le_iff`：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 
<= r) : dist f g <= r ↔ forall b, dist (f b) (g b) <= r
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `dist_le_pi_dist`：dist_le_pi_dist (f g : forall b, X b) (b : β) : dist (f
 b) (g b) <= dist f g
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0
-/
instance Pi.instIsBoundedSMul' {α β : ι → Type*} [∀ i, PseudoMetricSpace (α i)]
    [∀ i, PseudoMetricSpace (β i)] [∀ i, Zero (α i)] [∀ i, Zero (β i)] [∀ i, SMul (α i) (β i)]
    [∀ i, IsBoundedSMul (α i) (β i)] : IsBoundedSMul (∀ i, α i) (∀ i, β i) where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff <| by positivity).2 fun _ ↦
      (dist_smul_pair _ _ _).trans <|
        mul_le_mul (dist_le_pi_dist _ 0 _) (dist_le_pi_dist _ _ _) dist_nonneg dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ ↦
      (dist_pair_smul _ _ _).trans <|
        mul_le_mul (dist_le_pi_dist _ _ _) (dist_le_pi_dist _ 0 _) dist_nonneg dist_nonneg
/-
**Prod.instIsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instIsBoundedSMul {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetric
Space β] [PseudoMetricSpace γ] [Zero α] [Zero β] [Zero γ] [SMul α β] [SMul α γ] 
[IsBoundedSMul α β] [IsBoundedSMul α γ] : IsBoundedSMul α (β × γ) where dist_smu
l_pair' _x _y₁ _y₂
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0
-/
instance Prod.instIsBoundedSMul {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] [Zero α] [Zero β] [Zero γ] [SMul α β] [SMul α γ] [IsBoundedSMul α β]
    [IsBoundedSMul α γ] : IsBoundedSMul α (β × γ) where
  dist_smul_pair' _x _y₁ _y₂ :=
    max_le ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)
  dist_pair_smul' _x₁ _x₂ _y :=
    max_le ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Type*}
    [PseudoMetricSpace α] [PseudoMetricSpace β] [Zero α] [Zero β] [SMul α β] [IsBoundedSMul α β] :
    IsBoundedSMul α (SeparationQuotient β) where
  dist_smul_pair' _ := Quotient.ind₂ <| dist_smul_pair _
  dist_pair_smul' _ _ := Quotient.ind <| dist_pair_smul _ _

-- We don't have the `SMul α γ → SMul β δ → SMul (α × β) (γ × δ)` instance, but if we did, then
-- `IsBoundedSMul α γ → IsBoundedSMul β δ → IsBoundedSMul (α × β) (γ × δ)` would hold
