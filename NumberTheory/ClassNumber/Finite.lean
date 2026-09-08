/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Norm.Basic

/-!
# Class numbers of global fields

In this file, we use the notion of "admissible absolute value" to prove
finiteness of the class group for number fields and function fields.

## Main definitions
- `ClassGroup.fintypeOfAdmissibleOfAlgebraic`: if `R` has an admissible absolute value,
  its integral closure has a finite class group
-/

@[expose] public section

open Module Ring
open scoped nonZeroDivisors

namespace ClassGroup
section EuclideanDomain

variable {R S : Type*} (K L : Type*) [EuclideanDomain R] [CommRing S] [IsDomain S]
variable [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [algRL : Algebra R L] [IsScalarTower R K L]
variable [Algebra R S] [Algebra S L]
variable [ist : IsScalarTower R S L]
variable (abv : AbsoluteValue R ℤ)
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (bS : Basis ι R S)

/-- If `b` is an `R`-basis of `S` of cardinality `n`, then `normBound abv b` is an integer
such that for every `R`-integral element `a : S` with coordinates `≤ y`,
we have `Algebra.norm a ≤ normBound abv b * y ^ n`. (See also `norm_le` and `norm_lt`). -/
/-
**ClassGroup.normBound** 是 Mathlib 中的一个定义，位于命名空间 `ClassGroup`。
形式化陈述：normBound : Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1

--- 原说明 ---
If `b` is an `R`-basis of `S` of cardinality `n`, then `normBound abv b` is an i
nteger
such that for every `R`-integral element `a : S` with coordinates `≤ y`,
we have `Algebra.norm a ≤ normBound abv b * y ^ n`. (See also `norm_le` and `nor
m_lt`).
-/
noncomputable def normBound : ℤ :=
  let n := Fintype.card ι
  let i : ι := Nonempty.some bS.index_nonempty
  let m : ℤ :=
    Finset.max'
      (Finset.univ.image fun ijk : ι × ι × ι =>
        abv (Algebra.leftMulMatrix bS (bS ijk.1) ijk.2.1 ijk.2.2))
      ⟨_, Finset.mem_image.mpr ⟨⟨i, i, i⟩, Finset.mem_univ _, rfl⟩⟩
  Nat.factorial n • (n • m) ^ n
/-
**ClassGroup.normBound_pos** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：normBound_pos : 0 < normBound abv bS
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Module.Basis.index_nonempty`：index_nonempty (b : Basis ι R M) [Nontrivia
l M] : Nonempty ι
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.Basis.ne_zero`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Algebra.leftMulMatrix_injective`：leftMulMatrix_injective : Function.Inje
ctive (leftMulMatrix b)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `AbsoluteValue.pos`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [
inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : 
R}, x ≠…
（共 33 条，此处仅展示前 30 条）
-/
theorem normBound_pos : 0 < normBound abv bS := by
  obtain ⟨i, j, k, hijk⟩ : ∃ i j k, Algebra.leftMulMatrix bS (bS i) j k ≠ 0 := by
    by_contra! h
    obtain ⟨i⟩ := bS.index_nonempty
    apply bS.ne_zero i
    apply
      (injective_iff_map_eq_zero (Algebra.leftMulMatrix bS)).mp (Algebra.leftMulMatrix_injective bS)
    ext j k
    simp [h]
  simp only [normBound, Algebra.smul_def, eq_natCast]
  apply mul_pos (Int.natCast_pos.mpr (Nat.factorial_pos _))
  refine pow_pos (mul_pos (Int.natCast_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)) ?_) _
  refine lt_of_lt_of_le (abv.pos hijk) (Finset.le_max' _ _ ?_)
  exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

/-- If the `R`-integral element `a : S` has coordinates `≤ y` with respect to some basis `b`,
its norm is less than `normBound abv b * y ^ dim S`. -/
/-
**ClassGroup.norm_le** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：norm_le (a : S) {y : Int} (hy : forall k, abv (bS.repr a k) <= y) : abv (A
lgebra.norm R a) <= normBound abv bS * y ^ Fintype.card ι
参数：a : S；hy : forall k, abv (bS.repr a k) <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `Algebra.norm_apply`：norm_apply (x : S) : norm R x = LinearMap.det (lmul 
R S x)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Matrix.det_sum_smul_le`：det_sum_smul_le {ι : Type*} (s : Finset ι) {c : 
ι -> R} {A : ι -> Matrix n n R} {abv : AbsoluteValue R S} {x : S} (hx : forall k
 i j, abv (A…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If the `R`-integral element `a : S` has coordinates `≤ y` with respect to some b
asis `b`,
its norm is less than `normBound abv b * y ^ dim S`.
-/
theorem norm_le (a : S) {y : ℤ} (hy : ∀ k, abv (bS.repr a k) ≤ y) :
    abv (Algebra.norm R a) ≤ normBound abv bS * y ^ Fintype.card ι := by
  conv_lhs => rw [← bS.sum_repr a]
  rw [Algebra.norm_apply, ← LinearMap.det_toMatrix bS]
  simp only [map_sum, map_smul, map_sum, map_smul,
    normBound, smul_mul_assoc, ← mul_pow]
  convert! Matrix.det_sum_smul_le Finset.univ _ hy using 3
  · rw [Finset.card_univ, smul_mul_assoc, mul_comm]
  · intro i j k
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩

/-- If the `R`-integral element `a : S` has coordinates `< y` with respect to some basis `b`,
its norm is strictly less than `normBound abv b * y ^ dim S`. -/
/-
**ClassGroup.norm_lt** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：norm_lt {T : Type*} [Ring T] [LinearOrder T] [IsStrictOrderedRing T] (a : 
S) {y : T} (hy : forall k, (abv (bS.repr a k) : T) < y) : (abv (Algebra.norm R a
) : T) < normBound abv bS * y ^ Fintype.card ι
参数：a : S；hy : forall k, (abv (bS.repr a k) : T) < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.index_nonempty`：index_nonempty (b : Basis ι R M) [Nontrivia
l M] : Nonempty ι
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.max'_image`：∀ {α : Type u_2} {β : Type u_3} [inst : LinearOrder α
] [inst_1 : LinearOrder β] {f : α → β},   Monotone f → ∀ (s : Finset α) (h : (Fi
nset.im…
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.max'_lt_iff`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset 
α) (H : s.Nonempty) {x : α}, s.max' H < x ↔ ∀ y ∈ s, y < x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ClassGroup.norm_le`：norm_le (a : S) {y : Int} (hy : forall k, abv (bS.re
pr a k) <= y) : abv (Algebra.norm R a) <= normBound abv bS * y ^ Fintype.card ι
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If the `R`-integral element `a : S` has coordinates `< y` with respect to some b
asis `b`,
its norm is strictly less than `normBound abv b * y ^ dim S`.
-/
theorem norm_lt {T : Type*} [Ring T] [LinearOrder T] [IsStrictOrderedRing T] (a : S) {y : T}
    (hy : ∀ k, (abv (bS.repr a k) : T) < y) :
    (abv (Algebra.norm R a) : T) < normBound abv bS * y ^ Fintype.card ι := by
  obtain ⟨i⟩ := bS.index_nonempty
  have him : (Finset.univ.image fun k => abv (bS.repr a k)).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  set y' : ℤ := Finset.max' _ him with y'_def
  have hy' : ∀ k, abv (bS.repr a k) ≤ y' := by
    intro k
    exact @Finset.le_max' ℤ _ _ _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have : (y' : T) < y := by
    rw [y'_def,
      ← Finset.max'_image (show Monotone (_ : ℤ → T) from fun x y h => Int.cast_le.mpr h)
          _ (him.image _)]
    apply (Finset.max'_lt_iff _ (him.image _)).mpr
    simp only [Finset.mem_image]
    rintro _ ⟨x, ⟨k, -, rfl⟩, rfl⟩
    exact hy k
  have y'_nonneg : 0 ≤ y' := le_trans (abv.nonneg _) (hy' i)
  apply (Int.cast_le.mpr (norm_le abv bS a hy')).trans_lt
  simp only [Int.cast_mul, Int.cast_pow]
  apply mul_lt_mul' le_rfl
  · exact pow_lt_pow_left₀ this (by positivity) (@Fintype.card_ne_zero _ _ ⟨i⟩)
  · positivity
  · exact Int.cast_pos.mpr (normBound_pos abv bS)


/-- A nonzero ideal has an element of minimal norm. -/
/-
**ClassGroup.exists_min** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：exists_min (I : (Ideal S)⁰) : exists b in (I : Ideal S), b != 0 ∧ forall c
 in (I : Ideal S), abv (Algebra.norm R c) < abv (Algebra.norm R b) -> c = (0 : S
)
参数：I : (Ideal S)⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.exists_least_of_bdd`：exists_least_of_bdd {P : Int -> Prop} (Hbdd : e
xists b : Int, forall z : Int, P z -> b <= z) (Hinh : exists z : Int, P z) : exi
sts lb : Int,…
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
A nonzero ideal has an element of minimal norm.
-/
theorem exists_min (I : (Ideal S)⁰) :
    ∃ b ∈ (I : Ideal S),
      b ≠ 0 ∧ ∀ c ∈ (I : Ideal S), abv (Algebra.norm R c) < abv (Algebra.norm R b) → c =
      (0 : S) := by
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ := @Int.exists_least_of_bdd
      (fun a => ∃ b ∈ (I : Ideal S), b ≠ (0 : S) ∧ abv (Algebra.norm R b) = a)
    (by
      use 0
      rintro _ ⟨b, _, _, rfl⟩
      apply abv.nonneg)
    (by
      obtain ⟨b, b_mem, b_ne_zero⟩ := (I : Ideal S).ne_bot_iff.mp (nonZeroDivisors.coe_ne_zero I)
      exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩)
  refine ⟨b, b_mem, b_ne_zero, ?_⟩
  intro c hc lt
  contrapose! lt with c_ne_zero
  exact min _ ⟨c, hc, c_ne_zero, rfl⟩

section IsAdmissible

variable {abv}
variable (adm : abv.IsAdmissible)

/-- If we have a large enough set of elements in `R^ι`, then there will be a pair
whose remainders are close together. We'll show that all sets of cardinality
at least `cardM bS adm` elements satisfy this condition.

The value of `cardM` is not at all optimal: for specific choices of `R`,
the minimum cardinality can be exponentially smaller.
-/
/-
**ClassGroup.cardM** 是 Mathlib 中的一个定义，位于命名空间 `ClassGroup`。
形式化陈述：cardM : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have a large enough set of elements in `R^ι`, then there will be a pair
whose remainders are close together. We'll show that all sets of cardinality
at least `cardM bS adm` elements satisfy this condition.

The value of `cardM` is not at all optimal: for specific choices of `R`,
the minimum cardinality can be exponentially smaller.
-/
noncomputable def cardM : ℕ :=
  adm.card (normBound abv bS ^ (-1 / Fintype.card ι : ℝ)) ^ Fintype.card ι

variable [Infinite R]

/-- In the following results, we need a large set of distinct elements of `R`. -/
/-
**ClassGroup.distinctElems** 是 Mathlib 中的一个定义，位于命名空间 `ClassGroup`。
形式化陈述：distinctElems : Fin (cardM bS adm).succ ↪ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the following results, we need a large set of distinct elements of `R`.
-/
noncomputable def distinctElems : Fin (cardM bS adm).succ ↪ R :=
  Fin.valEmbedding.trans (Infinite.natEmbedding R)

variable [DecidableEq R]

/-- `finsetApprox` is a finite set such that each fractional ideal in the integral closure
contains an element close to `finsetApprox`. -/
/-
**ClassGroup.finsetApprox** 是 Mathlib 中的一个定义，位于命名空间 `ClassGroup`。
形式化陈述：finsetApprox : Finset R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`finsetApprox` is a finite set such that each fractional ideal in the integral c
losure
contains an element close to `finsetApprox`.
-/
noncomputable def finsetApprox : Finset R :=
  (Finset.univ.image fun xy : _ × _ => distinctElems bS adm xy.1 - distinctElems bS adm xy.2).erase
    0
/-
**ClassGroup.finsetApprox.zero_notMem** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup.fins
etApprox`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : EuclideanDomain R] [inst_1 : CommR
ing S] [inst_2 : IsDomain S]   [inst_3 : Algebra R S] {abv : AbsoluteValue R ℤ} 
{ι : Type u_5} [inst_4 : DecidableEq ι] [inst_5 : Fintype ι]   (bS : Module.Basi
s ι R S) (adm : abv.IsAdmissible) [inst_6 : Infinite R] [inst_7 : DecidableEq R]
,   0 ∉ ClassGroup.finsetApprox bS adm
参数：bS : Module.Basis ι R S；adm : abv.IsAdmissible。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
-/
theorem finsetApprox.zero_notMem : (0 : R) ∉ finsetApprox bS adm :=
  Finset.notMem_erase _ _

@[simp]
/-
**ClassGroup.mem_finsetApprox** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：mem_finsetApprox {x : R} : x in finsetApprox bS adm ↔ exists i j, i != j ∧
 distinctElems bS adm i - distinctElems bS adm j = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem mem_finsetApprox {x : R} :
    x ∈ finsetApprox bS adm ↔ ∃ i j, i ≠ j ∧ distinctElems bS adm i - distinctElems bS adm j =
    x := by
  simp only [finsetApprox, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hx, ⟨i, j⟩, _, rfl⟩
    refine ⟨i, j, ?_, rfl⟩
    rintro rfl
    simp at hx
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨?_, ⟨i, j⟩, Finset.mem_univ _, rfl⟩
    rw [Ne, sub_eq_zero]
    exact fun h => hij ((distinctElems bS adm).injective h)

section Real

open Real

attribute [-instance] Real.decidableEq

set_option backward.isDefEq.respectTransparency.types false in
/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
/-
**ClassGroup.exists_mem_finsetApprox** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：exists_mem_finsetApprox (a : S) {b} (hb : b != (0 : R)) : exists q : S, ex
ists r in finsetApprox bS adm, abv (Algebra.norm R (r • a - b • q)) < abv (Algeb
ra.norm R (algebraMap R S b))
参数：a : S；hb : b != (0 : R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Module.Basis.index_nonempty`：index_nonempty (b : Basis ι R M) [Nontrivia
l M] : Nonempty ι
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ClassGroup.normBound_pos`：normBound_pos : 0 < normBound abv bS
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `Int.cast_nonneg`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1
 : PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] {n : ℤ},   0 ≤ n → 0 ≤ ↑n
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
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
（共 108 条，此处仅展示前 30 条）

--- 原说明 ---
We can approximate `a / b : L` with `q / r`, where `r` has finitely many options
 for `L`.
-/
theorem exists_mem_finsetApprox (a : S) {b} (hb : b ≠ (0 : R)) :
    ∃ q : S,
      ∃ r ∈ finsetApprox bS adm, abv (Algebra.norm R (r • a - b • q)) <
      abv (Algebra.norm R (algebraMap R S b)) := by
  have dim_pos := Fintype.card_pos_iff.mpr bS.index_nonempty
  set ε : ℝ := normBound abv bS ^ (-1 / Fintype.card ι : ℝ) with ε_eq
  have hε : 0 < ε := Real.rpow_pos_of_pos (Int.cast_pos.mpr (normBound_pos abv bS)) _
  have ε_le : (normBound abv bS : ℝ) * (abv b • ε) ^ (Fintype.card ι : ℝ)
                ≤ abv b ^ (Fintype.card ι : ℝ) := by
    have := normBound_pos abv bS
    have := abv.nonneg b
    rw [ε_eq, Algebra.smul_def, eq_intCast, mul_rpow, ← rpow_mul, div_mul_cancel₀, rpow_neg_one,
      mul_left_comm, mul_inv_cancel₀, mul_one, rpow_natCast] <;>
      try norm_cast; lia
    · exact Int.cast_nonneg this
    · linarith
  set μ : Fin (cardM bS adm).succ ↪ R := distinctElems bS adm
  let s : ι →₀ R := bS.repr a
  have s_eq : ∀ i, s i = bS.repr a i := fun i => rfl
  let qs : Fin (cardM bS adm).succ → ι → R := fun j i => μ j * s i / b
  let rs : Fin (cardM bS adm).succ → ι → R := fun j i => μ j * s i % b
  have r_eq : ∀ j i, rs j i = μ j * s i % b := fun i j => rfl
  have μ_eq : ∀ i j, μ j * s i = b * qs j i + rs j i := by
    intro i j
    rw [r_eq, EuclideanDomain.div_add_mod]
  have μ_mul_a_eq : ∀ j, μ j • a = b • ∑ i, qs j i • bS i + ∑ i, rs j i • bS i := by
    intro j
    rw [← bS.sum_repr a]
    simp only [μ, qs, rs, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← s_eq, ← mul_smul, μ_eq, add_smul, mul_smul, ← μ_eq]
  obtain ⟨j, k, j_ne_k, hjk⟩ := adm.exists_approx hε hb fun j i => μ j * s i
  have hjk' : ∀ i, (abv (rs k i - rs j i) : ℝ) < abv b • ε := by simpa only [r_eq] using hjk
  let q := ∑ i, (qs k i - qs j i) • bS i
  set r := μ k - μ j with r_eq
  refine ⟨q, r, (mem_finsetApprox bS adm).mpr ?_, ?_⟩
  · exact ⟨k, j, j_ne_k.symm, rfl⟩
  have : r • a - b • q = ∑ x : ι, (rs k x • bS x - rs j x • bS x) := by
    simp only [q, r_eq, sub_smul, μ_mul_a_eq, Finset.smul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, smul_sub]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [this, Algebra.norm_algebraMap_of_basis bS, abv.map_pow]
  refine Int.cast_lt.mp ((norm_lt abv bS _ fun i => lt_of_le_of_lt ?_ (hjk' i)).trans_le ?_)
  · apply le_of_eq
    congr
    simp_rw [map_sum, map_sub, map_smul, Finset.sum_apply',
      Finsupp.sub_apply, Finsupp.smul_apply, Finset.sum_sub_distrib, Basis.repr_self_apply,
      smul_eq_mul, mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · exact mod_cast ε_le

/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
/-
**ClassGroup.exists_mem_finset_approx'** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：exists_mem_finset_approx' [Algebra.IsAlgebraic R S] (a : S) {b : S} (hb : 
b != 0) : exists q : S, exists r in finsetApprox bS adm, abv (Algebra.norm R (r 
• a - q * b)) < abv (Algebra.norm R b)
参数：a : S；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.exists_smul_eq_mul`：Algebra.IsAlgebraic.exists_smul_
eq_mul [NoZeroDivisors S] [Algebra.IsAlgebraic R S] (a : S) {b : S} (hb : b != 0
) : existsᵉ (c : S) (d != (0…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ClassGroup.exists_mem_finsetApprox`：exists_mem_finsetApprox (a : S) {b} 
(hb : b != (0 : R)) : exists q : S, exists r in finsetApprox bS adm, abv (Algebr
a.norm R (r • a - b • q)…
· 使用定理 `lt_of_mul_lt_mul_left`：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a 
* b < a * c) (a0 : 0 <= a) : b < c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AbsoluteValue.map_mul`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (
x y : R), a…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α]   [MulPosStrictMono α], a < b → c ≤ d →
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `AbsoluteValue.pos`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [
inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : 
R}, x ≠…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.norm_ne_zero_iff_of_basis`：norm_ne_zero_iff_of_basis [IsDomain R
] [IsDomain S] (b : Basis ι R S) {x : S} : Algebra.norm R x != 0 ↔ x != 0
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
We can approximate `a / b : L` with `q / r`, where `r` has finitely many options
 for `L`.
-/
theorem exists_mem_finset_approx' [Algebra.IsAlgebraic R S] (a : S) {b : S} (hb : b ≠ 0) :
    ∃ q : S,
      ∃ r ∈ finsetApprox bS adm, abv (Algebra.norm R (r • a - q * b)) < abv (Algebra.norm R b) := by
  obtain ⟨a', b', hb', h⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul R a hb
  obtain ⟨q, r, hr, hqr⟩ := exists_mem_finsetApprox bS adm a' hb'
  refine ⟨q, r, hr, ?_⟩
  refine
    lt_of_mul_lt_mul_left ?_ (show 0 ≤ abv (Algebra.norm R (algebraMap R S b')) from abv.nonneg _)
  refine
    lt_of_le_of_lt (le_of_eq ?_)
      (mul_lt_mul hqr le_rfl (abv.pos ((Algebra.norm_ne_zero_iff_of_basis bS).mpr hb))
        (abv.nonneg _))
  rw [← abv.map_mul, ← map_mul, ← abv.map_mul, ← map_mul, ← Algebra.smul_def,
    smul_sub b', sub_mul, smul_comm, h, mul_comm b a', Algebra.smul_mul_assoc r a' b,
    Algebra.smul_mul_assoc b' q b]

end Real

/-
**ClassGroup.prod_finsetApprox_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：prod_finsetApprox_ne_zero : algebraMap R S (∏ m in finsetApprox bS adm, m)
 != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Module.Basis.algebraMap_injective`：Module.Basis.algebraMap_injective {ι 
: Type*} (b : Basis ι R S) : Function.Injective (algebraMap R S)
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ClassGroup.finsetApprox.zero_notMem`：∀ {R : Type u_1} {S : Type u_2} [in
st : EuclideanDomain R] [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : 
Algebra R S] {abv : Absol…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_finsetApprox_ne_zero : algebraMap R S (∏ m ∈ finsetApprox bS adm, m) ≠ 0 := by
  refine mt ((injective_iff_map_eq_zero _).mp bS.algebraMap_injective _) ?_
  simp only [Finset.prod_eq_zero_iff, not_exists]
  rintro x ⟨hx, rfl⟩
  exact finsetApprox.zero_notMem bS adm hx
/-
**ClassGroup.ne_bot_of_prod_finsetApprox_mem** 是 Mathlib 中的一个定理，位于命名空间 `ClassGro
up`。
形式化陈述：ne_bot_of_prod_finsetApprox_mem (J : Ideal S) (h : algebraMap _ _ (∏ m in 
finsetApprox bS adm, m) in J) : J != ⊥
参数：J : Ideal S；h : algebraMap _ _ (∏ m in finsetApprox bS adm, m) in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `ClassGroup.prod_finsetApprox_ne_zero`：prod_finsetApprox_ne_zero : algebr
aMap R S (∏ m in finsetApprox bS adm, m) != 0
-/
theorem ne_bot_of_prod_finsetApprox_mem (J : Ideal S)
    (h : algebraMap _ _ (∏ m ∈ finsetApprox bS adm, m) ∈ J) : J ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, h, prod_finsetApprox_ne_zero _ _⟩

set_option linter.overlappingInstances false

/-- Each class in the class group contains an ideal `J`
such that `M := Π m ∈ finsetApprox` is in `J`. -/
/-
**ClassGroup.exists_mk0_eq_mk0** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：exists_mk0_eq_mk0 [IsDedekindDomain S] [Algebra.IsAlgebraic R S] (I : (Ide
al S)⁰) : exists J : (Ideal S)⁰, ClassGroup.mk0 I = ClassGroup.mk0 J ∧ algebraMa
p _ _ (∏ m in finsetApprox bS adm, m) in (J : Ideal S)
参数：I : (Ideal S)⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClassGroup.prod_finsetApprox_ne_zero`：prod_finsetApprox_ne_zero : algebr
aMap R S (∏ m in finsetApprox bS adm, m) != 0
· 使用定理 `ClassGroup.exists_min`：exists_min (I : (Ideal S)⁰) : exists b in (I : Id
eal S), b != 0 ∧ forall c in (I : Ideal S), abv (Algebra.norm R c) < abv (Algebr
a.norm R b)…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Ideal.mul_le`：mul_le : I * J <= K ↔ forall r in I, forall s in J, r * s 
in K
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `ClassGroup.exists_mem_finset_approx'`：exists_mem_finset_approx' [Algebra
.IsAlgebraic R S] (a : S) {b : S} (hb : b != 0) : exists q : S, exists r in fins
etApprox bS adm, abv (Alge…
· 使用定理 `dvd_of_mul_left_dvd`：dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_dvd_mul_right`：mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `Multiset.dvd_prod`：dvd_prod : a in s -> a ∣ s.prod
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Submodule.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] {A : Ty
pe v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTow
er R A A] [NoZeroD…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Each class in the class group contains an ideal `J`
such that `M := Π m ∈ finsetApprox` is in `J`.
-/
theorem exists_mk0_eq_mk0 [IsDedekindDomain S] [Algebra.IsAlgebraic R S] (I : (Ideal S)⁰) :
    ∃ J : (Ideal S)⁰,
      ClassGroup.mk0 I = ClassGroup.mk0 J ∧
        algebraMap _ _ (∏ m ∈ finsetApprox bS adm, m) ∈ (J : Ideal S) := by
  set M := ∏ m ∈ finsetApprox bS adm, m
  have hM : algebraMap R S M ≠ 0 := prod_finsetApprox_ne_zero bS adm
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min abv I
  suffices Ideal.span {b} ∣ Ideal.span {algebraMap _ _ M} * I.1 by
    obtain ⟨J, hJ⟩ := this
    refine ⟨⟨J, ?_⟩, ?_, ?_⟩
    · rw [mem_nonZeroDivisors_iff_ne_zero]
      rintro rfl
      rw [Ideal.zero_eq_bot, Ideal.mul_bot] at hJ
      exact hM (Ideal.span_singleton_eq_bot.mp (I.2.2 _ hJ))
    · rw [ClassGroup.mk0_eq_mk0_iff]
      exact ⟨algebraMap _ _ M, b, hM, b_ne_zero, hJ⟩
    rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ← Ideal.dvd_iff_le]
    apply (mul_dvd_mul_iff_left _).mp _
    swap; · exact mt Ideal.span_singleton_eq_bot.mp b_ne_zero
    rw [Subtype.coe_mk, Ideal.dvd_iff_le, ← hJ, mul_comm]
    apply Ideal.mul_mono le_rfl
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact b_mem
  rw [Ideal.dvd_iff_le, Ideal.mul_le]
  intro r' hr' a ha
  rw [Ideal.mem_span_singleton] at hr' ⊢
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' bS adm a b_ne_zero
  apply @dvd_of_mul_left_dvd _ _ q
  simp only [Algebra.smul_def] at lt
  rw [←
    sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt)]
  refine mul_dvd_mul_right (dvd_trans (map_dvd _ ?_) hr') _
  exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨_, r_mem, rfl⟩)

/-- `ClassGroup.mkMMem` is a specialization of `ClassGroup.mk0` to (the finite set of)
ideals that contain `M := ∏ m ∈ finsetApprox L f abs, m`.
By showing this function is surjective, we prove that the class group is finite. -/
/-
**ClassGroup.mkMMem** 是 Mathlib 中的一个定义，位于命名空间 `ClassGroup`。
形式化陈述：mkMMem [IsDedekindDomain S] (J : { J : Ideal S // algebraMap _ _ (∏ m in f
insetApprox bS adm, m) in J }) : ClassGroup S
参数：J : { J : Ideal S // algebraMap _ _ (∏ m in finsetApprox bS adm, m) in J }。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ClassGroup.mkMMem` is a specialization of `ClassGroup.mk0` to (the finite set o
f)
ideals that contain `M := ∏ m ∈ finsetApprox L f abs, m`.
By showing this function is surjective, we prove that the class group is finite.
-/
noncomputable def mkMMem [IsDedekindDomain S]
    (J : { J : Ideal S // algebraMap _ _ (∏ m ∈ finsetApprox bS adm, m) ∈ J }) : ClassGroup S :=
  ClassGroup.mk0
    ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr (ne_bot_of_prod_finsetApprox_mem bS adm J.1 J.2)⟩
/-
**ClassGroup.mkMMem_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：mkMMem_surjective [IsDedekindDomain S] [Algebra.IsAlgebraic R S] : Functio
n.Surjective (ClassGroup.mkMMem bS adm)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClassGroup.mk0_surjective`：ClassGroup.mk0_surjective [IsDedekindDomain R
] : Function.Surjective (ClassGroup.mk0 : (Ideal R)⁰ -> ClassGroup R)
· 使用定理 `ClassGroup.exists_mk0_eq_mk0`：exists_mk0_eq_mk0 [IsDedekindDomain S] [Al
gebra.IsAlgebraic R S] (I : (Ideal S)⁰) : exists J : (Ideal S)⁰, ClassGroup.mk0 
I = ClassGroup.mk0…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mkMMem_surjective [IsDedekindDomain S] [Algebra.IsAlgebraic R S] :
    Function.Surjective (ClassGroup.mkMMem bS adm) := by
  intro I'
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective I'
  obtain ⟨J, mk0_eq_mk0, J_dvd⟩ := exists_mk0_eq_mk0 bS adm ⟨I, hI⟩
  exact ⟨⟨J, J_dvd⟩, mk0_eq_mk0.symm⟩

open scoped Classical in
/-- The **class number theorem**: the class group of an integral closure `S` of `R` in an
algebraic extension `L` is finite if there is an admissible absolute value.

See also `ClassGroup.fintypeOfAdmissibleOfFinite` where `L` is a finite
extension of `K = Frac(R)`, supplying most of the required assumptions automatically.
-/
@[instance_reducible]
/-
**ClassGroup.fintypeOfAdmissibleOfAlgebraic** 是 Mathlib 中的一个定义，位于命名空间 `ClassGrou
p`。
形式化陈述：fintypeOfAdmissibleOfAlgebraic [IsDedekindDomain S] [Algebra.IsAlgebraic R
 S] : Fintype (ClassGroup S)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `ClassGroup.mkMMem_surjective`：mkMMem_surjective [IsDedekindDomain S] [Al
gebra.IsAlgebraic R S] : Function.Surjective (ClassGroup.mkMMem bS adm)

--- 原说明 ---
The **class number theorem**: the class group of an integral closure `S` of `R` 
in an
algebraic extension `L` is finite if there is an admissible absolute value.

See also `ClassGroup.fintypeOfAdmissibleOfFinite` where `L` is a finite
extension of `K = Frac(R)`, supplying most of the required assumptions automatic
ally.
-/
noncomputable def fintypeOfAdmissibleOfAlgebraic [IsDedekindDomain S]
    [Algebra.IsAlgebraic R S] : Fintype (ClassGroup S) :=
  @Fintype.ofSurjective _ _ _
    (@Fintype.ofEquiv _
      { J // J ∣ Ideal.span ({algebraMap R S (∏ m ∈ finsetApprox bS adm, m)} : Set S) }
      (UniqueFactorizationMonoid.fintypeSubtypeDvd _
        (by
          rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
          exact prod_finsetApprox_ne_zero bS adm))
      ((Equiv.refl _).subtypeEquiv fun I =>
        Ideal.dvd_iff_le.trans (by
          rw [Equiv.refl_apply, Ideal.span_le, Set.singleton_subset_iff]; rfl)))
    (ClassGroup.mkMMem bS adm) (ClassGroup.mkMMem_surjective bS adm)

/-- The main theorem: the class group of an integral closure `S` of `R` in a
finite extension `L` of `K = Frac(R)` is finite if there is an admissible
absolute value.

See also `ClassGroup.fintypeOfAdmissibleOfAlgebraic` where `L` is an
algebraic extension of `R`, that includes some extra assumptions.
-/
@[instance_reducible]
/-
**ClassGroup.fintypeOfAdmissibleOfFinite** 是 Mathlib 中的一个定义，位于命名空间 `ClassGroup`。
形式化陈述：fintypeOfAdmissibleOfFinite [IsIntegralClosure S R L] : Fintype (ClassGrou
p S)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `EuclideanDomain.instIsDomain`：∀ (R : Type u_1) [e : EuclideanDomain R], 
IsDomain R

--- 原说明 ---
The main theorem: the class group of an integral closure `S` of `R` in a
finite extension `L` of `K = Frac(R)` is finite if there is an admissible
absolute value.

See also `ClassGroup.fintypeOfAdmissibleOfAlgebraic` where `L` is an
algebraic extension of `R`, that includes some extra assumptions.
-/
noncomputable def fintypeOfAdmissibleOfFinite [IsIntegralClosure S R L] :
    Fintype (ClassGroup S) := by
  letI := Classical.decEq L
  letI := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  letI := IsIntegralClosure.isDedekindDomain R K L S
  choose s b hb_int using FiniteDimensional.exists_is_basis_integral R K L
  have : LinearIndependent R ((Algebra.traceForm K L).dualBasis
      (traceForm_nondegenerate K L) b) := by
    apply (Basis.linearIndependent _).restrict_scalars
    simp only [Algebra.smul_def, mul_one]
    apply IsFractionRing.injective
  obtain ⟨n, b⟩ :=
    Submodule.basisOfPidOfLESpan this (IsIntegralClosure.range_le_span_dualBasis S b hb_int)
  let f : (S ⧸ LinearMap.ker (LinearMap.restrictScalars R (Algebra.linearMap S L))) ≃ₗ[R] S := by
    rw [LinearMap.ker_eq_bot.mpr]
    · exact Submodule.quotEquivOfEqBot _ rfl
    · exact IsIntegralClosure.algebraMap_injective _ R _
  let bS := b.map ((LinearMap.quotKerEquivRange _).symm ≪≫ₗ f)
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  exact fintypeOfAdmissibleOfAlgebraic bS adm

end IsAdmissible

end EuclideanDomain

end ClassGroup

