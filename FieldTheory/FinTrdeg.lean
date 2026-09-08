/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Extensions with Finite Transcendence Degree

A field extension L/K has finite transcendence degree if
the transcendence degree of L over K is finite.
Equivalently, if L is an algebraic extension of a finitely generated field extension of K.
-/

public section

open IntermediateField

/-- A field extension L/K is said to have finite transcendence degree if there is some
intermediate extension L/E/K with E/K finitely generated and L/E algebraic. -/
/-
**FinTrdeg** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_1) → (L : Type u_2) → [inst : Field K] → [inst_1 : Field L] → 
[Algebra K L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field extension L/K is said to have finite transcendence degree if there is so
me
intermediate extension L/E/K with E/K finitely generated and L/E algebraic.
-/
class FinTrdeg (K L : Type*) [Field K] [Field L] [Algebra K L] where
  exists_fg_isAlgebraic (K L) : ∃ E : IntermediateField K L, E.FG ∧ Algebra.IsAlgebraic E L

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (K L) in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsAlgebraic K L] : FinTrdeg K L where
  exists_fg_isAlgebraic := ⟨⊥, IntermediateField.fg_bot, inferInstance⟩

variable (K L) in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.EssFiniteType K L] : FinTrdeg K L where
  exists_fg_isAlgebraic := ⟨⊤, IntermediateField.fg_top_iff.mpr ‹_›, inferInstance⟩
/-
**finTrdeg_iff_trdeg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finTrdeg_iff_trdeg : FinTrdeg K L ↔ Algebra.trdeg K L < .aleph0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `trdeg_add_eq`：∀ (R : Type u_1) (S : Type v) [inst : CommRing R] [inst_1 
: CommRing S] [inst_2 : Algebra R S] [Nontrivial R]   {A : Type v} [inst_4 : Com
mR…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.instFaithfulSMulSubtypeMem`：∀ {K : Type u_1} {L : Type
 u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] {X : Type u_4} 
  [inst_3 : SMul L X] [FaithfulSMu…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `trdeg_eq_zero_iff`：trdeg_eq_zero_iff : trdeg R A = 0 ↔ Algebra.IsAlgebra
ic R A
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Algebra.essFiniteType_iff_exists_subalgebra`：essFiniteType_iff_exists_su
balgebra : EssFiniteType R S ↔ exists (S₀ : Subalgebra R S) (M : Submonoid S₀), 
FiniteType R S₀ ∧ IsLocalization …
· 使用引理 `IntermediateField.essFiniteType_iff`：essFiniteType_iff {K : Intermediate
Field F E} : Algebra.EssFiniteType F K ↔ K.FG
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subalgebra.instFaithfulSMulSubtypeMem`：∀ {R : Type u} {A : Type v} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_1}  
 [inst_3 : SMul A α] [Faith…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.isAlgebraic`：IsLocalization.isAlgebraic [Nontrivial R] (M
 : Submonoid R) [IsLocalization M S] : Algebra.IsAlgebraic R S where isAlgebraic
 x
· 使用定理 `trdeg_lt_aleph0_of_finiteType`：trdeg_lt_aleph0_of_finiteType [IsDomain R
] [fin : FiniteType R S] : trdeg R S < ℵ₀
· 使用定理 `exists_isTranscendenceBasis`：exists_isTranscendenceBasis [FaithfulSMul R
 A] : exists s : Set A, IsTranscendenceBasis R ((↑) : s -> A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0_iff_set_finite`：lt_aleph0_iff_set_finite {S : Set α} 
: #S < ℵ₀ ↔ S.Finite
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `IsTranscendenceBasis.cardinalMk_eq_trdeg`：cardinalMk_eq_trdeg {ι : Type 
w} {x : ι -> A} (hx : IsTranscendenceBasis R x) : #ι = trdeg R A
· 使用定理 `IntermediateField.fg_adjoin_of_finite`：fg_adjoin_of_finite {t : Set E} (
h : Set.Finite t) : (adjoin F t).FG
· 使用定理 `IsTranscendenceBasis.isAlgebraic_field`：IsTranscendenceBasis.isAlgebraic
_field {F E : Type*} {x : ι -> E} [Field F] [Field E] [Algebra F E] (hx : IsTran
scendenceBasis F x) : Algebr…
（共 31 条，此处仅展示前 30 条）
-/
theorem finTrdeg_iff_trdeg : FinTrdeg K L ↔ Algebra.trdeg K L < .aleph0 := by
  constructor
  · intro ⟨E, fg, alg⟩
    rw [← trdeg_add_eq K E, trdeg_eq_zero_iff.2 alg, add_zero]
    rw [← essFiniteType_iff, Algebra.essFiniteType_iff_exists_subalgebra] at fg
    obtain ⟨S₀, M, fin, islocal⟩ := fg
    rw [← trdeg_add_eq K S₀, trdeg_eq_zero_iff.2 islocal.isAlgebraic, add_zero]
    exact trdeg_lt_aleph0_of_finiteType
  · intro h
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
    have fin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.1 (hs.cardinalMk_eq_trdeg.trans_lt h)
    constructor
    refine ⟨adjoin K s, fg_adjoin_of_finite fin, ?_⟩
    have alg := hs.isAlgebraic_field
    rwa [Subtype.range_coe] at alg

alias ⟨_, FinTrdeg.of_trdeg⟩ := finTrdeg_iff_trdeg

variable (K L) in
/-
**trdeg_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trdeg_lt_aleph0 [FinTrdeg K L] : Algebra.trdeg K L < .aleph0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `finTrdeg_iff_trdeg`：finTrdeg_iff_trdeg : FinTrdeg K L ↔ Algebra.trdeg K 
L < .aleph0
-/
theorem trdeg_lt_aleph0 [FinTrdeg K L] : Algebra.trdeg K L < .aleph0 :=
  finTrdeg_iff_trdeg.mp ‹_›
/-
**FinTrdeg.trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FinTrdeg.trans (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E]
 [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FinTrdeg K E] [FinTrdeg E L]
 : FinTrdeg K L
参数：K E L : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finTrdeg_iff_trdeg`：finTrdeg_iff_trdeg : FinTrdeg K L ↔ Algebra.trdeg K 
L < .aleph0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt_aleph0`：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c 
< ℵ₀ ↔ c < ℵ₀
· 使用定理 `lift_trdeg_add_eq`：∀ (R : Type u_1) (S : Type v) (A : Type w) [inst : Co
mmRing R] [inst_1 : CommRing S] [inst_2 : CommRing A]   [inst_3 : Algebra R S] [
inst_4 …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Cardinal.add_lt_aleph0_iff`：add_lt_aleph0_iff {a b : Cardinal} : a + b <
 ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀
· 使用定理 `trdeg_lt_aleph0`：trdeg_lt_aleph0 [FinTrdeg K L] : Algebra.trdeg K L < .a
leph0
-/
theorem FinTrdeg.trans (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FinTrdeg K E] [FinTrdeg E L] : FinTrdeg K L := by
  rw [finTrdeg_iff_trdeg, ← Cardinal.lift_lt_aleph0, ← lift_trdeg_add_eq K E L,
    Cardinal.add_lt_aleph0_iff, Cardinal.lift_lt_aleph0, Cardinal.lift_lt_aleph0]
  exact ⟨trdeg_lt_aleph0 K E, trdeg_lt_aleph0 E L⟩
/-
**finite_of_isTranscendenceBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_of_isTranscendenceBasis [FinTrdeg K L] {ι : Type*} {x : ι -> L} (hx
 : IsTranscendenceBasis K x) : Finite ι
参数：hx : IsTranscendenceBasis K x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.mk_lt_aleph0_iff`：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
· 使用定理 `Cardinal.lift_lt_aleph0`：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c 
< ℵ₀ ↔ c < ℵ₀
· 使用定理 `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`：lift_cardinalMk_eq_trdeg 
(hx : IsTranscendenceBasis R x) : lift.{w} #ι = lift.{u} (trdeg R A)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `trdeg_lt_aleph0`：trdeg_lt_aleph0 [FinTrdeg K L] : Algebra.trdeg K L < .a
leph0
-/
theorem finite_of_isTranscendenceBasis [FinTrdeg K L] {ι : Type*} {x : ι → L}
    (hx : IsTranscendenceBasis K x) : Finite ι := by
  rw [← Cardinal.mk_lt_aleph0_iff, ← Cardinal.lift_lt_aleph0,
    hx.lift_cardinalMk_eq_trdeg, Cardinal.lift_lt_aleph0]
  exact trdeg_lt_aleph0 K L
/-
**finite_of_algebraicIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finite_of_algebraicIndependent [FinTrdeg K L] {ι : Type*} {x : ι -> L} (hx
 : AlgebraicIndependent K x) : Finite ι
参数：hx : AlgebraicIndependent K x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.mk_lt_aleph0_iff`：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
· 使用定理 `Cardinal.lift_lt_aleph0`：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c 
< ℵ₀ ↔ c < ℵ₀
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `AlgebraicIndependent.lift_cardinalMk_le_trdeg`：AlgebraicIndependent.lift
_cardinalMk_le_trdeg [Nontrivial R] (hx : AlgebraicIndependent R x) : lift.{v} #
ι <= lift.{u} (trdeg R A)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `trdeg_lt_aleph0`：trdeg_lt_aleph0 [FinTrdeg K L] : Algebra.trdeg K L < .a
leph0
-/
theorem finite_of_algebraicIndependent [FinTrdeg K L] {ι : Type*} {x : ι → L}
    (hx : AlgebraicIndependent K x) : Finite ι := by
  rw [← Cardinal.mk_lt_aleph0_iff, ← Cardinal.lift_lt_aleph0]
  exact hx.lift_cardinalMk_le_trdeg.trans_lt (Cardinal.lift_lt_aleph0.mpr (trdeg_lt_aleph0 K L))
/-
**FinTrdeg.of_isTranscendenceBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FinTrdeg.of_isTranscendenceBasis {ι : Type*} [Finite ι] {x : ι -> L} (hx :
 IsTranscendenceBasis K x) : FinTrdeg K L
参数：hx : IsTranscendenceBasis K x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finTrdeg_iff_trdeg`：finTrdeg_iff_trdeg : FinTrdeg K L ↔ Algebra.trdeg K 
L < .aleph0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt_aleph0`：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c 
< ℵ₀ ↔ c < ℵ₀
· 使用定理 `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`：lift_cardinalMk_eq_trdeg 
(hx : IsTranscendenceBasis R x) : lift.{w} #ι = lift.{u} (trdeg R A)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Cardinal.mk_lt_aleph0`：∀ {α : Type u} [Finite α], Cardinal.mk α < Cardin
al.aleph0
-/
theorem FinTrdeg.of_isTranscendenceBasis {ι : Type*} [Finite ι] {x : ι → L}
    (hx : IsTranscendenceBasis K x) : FinTrdeg K L := by
  rw [finTrdeg_iff_trdeg, ← Cardinal.lift_lt_aleph0,
    ← hx.lift_cardinalMk_eq_trdeg, Cardinal.lift_lt_aleph0]
  exact Cardinal.mk_lt_aleph0

variable (K L) in
/-
**exists_finset_isTranscendenceBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_finset_isTranscendenceBasis [FinTrdeg K L] : exists s : Finset L, I
sTranscendenceBasis K ((↑) : s -> L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isTranscendenceBasis`：exists_isTranscendenceBasis [FaithfulSMul R
 A] : exists s : Set A, IsTranscendenceBasis R ((↑) : s -> A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.mem_range_coe_iff`：mem_range_coe_iff {s : Set α} : s in Set.range
 ((↑) : Finset α -> Set α) ↔ s.Finite where mp
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `finite_of_isTranscendenceBasis`：finite_of_isTranscendenceBasis [FinTrdeg
 K L] {ι : Type*} {x : ι -> L} (hx : IsTranscendenceBasis K x) : Finite ι
-/
theorem exists_finset_isTranscendenceBasis [FinTrdeg K L] :
    ∃ s : Finset L, IsTranscendenceBasis K ((↑) : s → L) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  obtain ⟨s, rfl⟩ := Finset.mem_range_coe_iff.2
    (Set.finite_coe_iff.1 (finite_of_isTranscendenceBasis hs))
  exact ⟨s, hs⟩
