/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.SeparablyGenerated

/-!

# Smooth algebras over fields

We show that separably generated extensions of fields are smooth.
In particular finitely generated field extensions over perfect fields are smooth.

-/

public section

variable {K L ι : Type*} [Field L] [Field K] [Algebra K L]

open scoped IntermediateField.algebraAdjoinAdjoin in
/-
**Algebra.FormallySmooth.adjoin_of_algebraicIndependent** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：Algebra.FormallySmooth.adjoin_of_algebraicIndependent {v : ι -> L} (hb : A
lgebraicIndependent K v) : Algebra.FormallySmooth K (IntermediateField.adjoin K 
(Set.range v))
参数：hb : AlgebraicIndependent K v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_equiv`：∀ {R : Type u_4} [inst : CommRing R] {A
 : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst
_3 : CommRing B] [ins…
· 使用定理 `Algebra.FormallySmooth.of_isLocalization`：∀ {R : Type u_4} {Rₘ : Type u_
6} [inst : CommRing R] [inst_1 : CommRing Rₘ] (M : Submonoid R) [inst_2 : Algebr
a R Rₘ]   [IsLocalization M Rₘ…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsFractionRingSubtypeMemSubalg
ebraAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fie
ld E] [inst_2 : Algebra F E] (S : Set E),   IsFractionRing ↥(Algebra.adjoin F …
· 使用定理 `Algebra.FormallySmooth.comp`：∀ (R : Type u_4) [inst : CommRing R] (A : T
ype u_5) [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6)   [inst_3 :
 CommRing B] [ins…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalge
braAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fiel
d E] [inst_2 : Algebra F E] (S : Set E) (X : Type u_3)   [inst_3 : SMul X F] …
-/
lemma Algebra.FormallySmooth.adjoin_of_algebraicIndependent {v : ι → L}
    (hb : AlgebraicIndependent K v) :
    Algebra.FormallySmooth K (IntermediateField.adjoin K (Set.range v)) := by
  have : Algebra.FormallySmooth K (adjoin K (Set.range v)) :=
    .of_equiv hb.aevalEquiv
  have : Algebra.FormallySmooth (adjoin K (Set.range v))
      (IntermediateField.adjoin K (Set.range v)) :=
    .of_isLocalization (nonZeroDivisors _)
  exact .comp _ (adjoin K (Set.range v)) _

/-- Purely transcendental extensions are formally smooth. -/
/-
**Algebra.FormallySmooth.of_algebraicIndependent** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.FormallySmooth.of_algebraicIndependent {v : ι -> L} (hb : Algebrai
cIndependent K v) (hb' : IntermediateField.adjoin K (Set.range v) = ⊤) : Algebra
.FormallySmooth K L
参数：hb : AlgebraicIndependent K v；hb' : IntermediateField.adjoin K (Set.range v) 
= ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FormallySmooth.adjoin_of_algebraicIndependent`：Algebra.FormallyS
mooth.adjoin_of_algebraicIndependent {v : ι -> L} (hb : AlgebraicIndependent K v
) : Algebra.FormallySmooth K (IntermediateF…
· 使用定理 `Algebra.FormallySmooth.of_equiv`：∀ {R : Type u_4} [inst : CommRing R] {A
 : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst
_3 : CommRing B] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Purely transcendental extensions are formally smooth.
-/
lemma Algebra.FormallySmooth.of_algebraicIndependent {v : ι → L}
    (hb : AlgebraicIndependent K v) (hb' : IntermediateField.adjoin K (Set.range v) = ⊤) :
    Algebra.FormallySmooth K L := by
  have := Algebra.FormallySmooth.adjoin_of_algebraicIndependent hb
  rw [hb'] at this
  exact .of_equiv IntermediateField.topEquiv

/-- Separably generated extensions are formally smooth. -/
/-
**Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable {v : ι -> L}
 (hb : AlgebraicIndependent K v) [Algebra.IsSeparable (IntermediateField.adjoin 
K (Set.range v)) L] : Algebra.FormallySmooth K L
参数：hb : AlgebraicIndependent K v；IntermediateField.adjoin K (Set.range v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FormallySmooth.adjoin_of_algebraicIndependent`：Algebra.FormallyS
mooth.adjoin_of_algebraicIndependent {v : ι -> L} (hb : AlgebraicIndependent K v
) : Algebra.FormallySmooth K (IntermediateF…
· 使用引理 `Algebra.FormallyEtale.of_isSeparable`：of_isSeparable [Algebra.IsSeparabl
e K L] : FormallyEtale K L
· 使用定理 `Algebra.FormallySmooth.comp`：∀ (R : Type u_4) [inst : CommRing R] (A : T
ype u_5) [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6)   [inst_3 :
 CommRing B] [ins…
· 使用定理 `Algebra.FormallyEtale.instFormallySmooth`：∀ {R : Type u} {A : Type v} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Formal
lyEtale R A], Algebra.Formally…

--- 原说明 ---
Separably generated extensions are formally smooth.
-/
lemma Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable
    {v : ι → L} (hb : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) L] :
    Algebra.FormallySmooth K L := by
  have := FormallySmooth.adjoin_of_algebraicIndependent hb
  have : FormallyEtale (IntermediateField.adjoin K (Set.range v)) L :=
    Algebra.FormallyEtale.of_isSeparable _ L
  exact .comp _ (IntermediateField.adjoin K (Set.range v)) _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) Algebra.FormallySmooth.of_perfectField
    [PerfectField K] [Algebra.EssFiniteType K L] : Algebra.FormallySmooth K L := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have : Algebra.IsSeparable (↥(IntermediateField.adjoin K (Set.range ((↑) : s → L)))) L := by
    convert! H <;> simp
  exact .of_algebraicIndependent_of_isSeparable hs.1
