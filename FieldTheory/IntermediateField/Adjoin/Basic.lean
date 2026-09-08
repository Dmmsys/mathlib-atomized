/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.Algebra.Subalgebra.IsSimpleOrder
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public import Mathlib.RingTheory.Adjoin.Dimension
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.SetTheory.Cardinal.Subfield

/-!
# Adjoining Elements to Fields

This file contains many results about adjoining elements to fields.
-/

@[expose] public section

open Module Polynomial

namespace IntermediateField

section

/-
**IntermediateField.restrictScalars_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Intermedia
teField`。
形式化陈述：restrictScalars_le_iff (K : Type*) {L E : Type*} [Field K] [Field L] [Fiel
d E] [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E] {E₁ E₂ : In
termediateField L E} : E₁.restrictScalars K <= E₂.restrictScalars K ↔ E₁ <= E₂
参数：K : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrictScalars_le_iff (K : Type*) {L E : Type*} [Field K] [Field L]
    [Field E] [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E₁ E₂ : IntermediateField L E} : E₁.restrictScalars K ≤ E₂.restrictScalars K ↔ E₁ ≤ E₂ := .rfl
/-
**IntermediateField.FG.of_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField.FG`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} {E : Type u_3} [inst : Field K] [inst_1 : 
Field L] [inst_2 : Field E]   [inst_3 : Algebra K L] [inst_4 : Algebra K E] [ins
t_5 : Algebra L E] [inst_6 : IsScalarTower K L E]   {E' : IntermediateField L E}
, (IntermediateField.restrictScalars K E').FG → E'.FG
参数：IntermediateField.restrictScalars K E'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IntermediateField.restrictScalars_le_iff`：restrictScalars_le_iff (K : Ty
pe*) {L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E] [Al
gebra L E] [IsScalarTower K L …
-/
lemma FG.of_restrictScalars {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    {E' : IntermediateField L E} (H : (E'.restrictScalars K).FG) : E'.FG := by
  obtain ⟨s, hs⟩ := H
  refine ⟨s, le_antisymm ?_ ?_⟩
  · rw [adjoin_le_iff]
    exact (subset_adjoin K _).trans_eq congr(($hs : Set E))
  · rw [← restrictScalars_le_iff K, ← hs, adjoin_le_iff]
    exact subset_adjoin L _

end

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {S : Set E}

/-
**IntermediateField.mem_adjoin_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：mem_adjoin_range_iff {ι : Type*} (i : ι -> E) (x : E) : x in adjoin F (Set
.range i) ↔ exists r s : MvPolynomial ι F, x = MvPolynomial.aeval i r / MvPolyno
mial.aeval i s
参数：i : ι -> E；x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.adjoin_range_eq_range_aeval`：∀ (R : Type u) {S₁ : Type v} {σ : T
ype u_1} [inst : CommSemiring R] [inst_1 : CommSemiring S₁] [inst_2 : Algebra R 
S₁]   (f : σ → S₁), Algeb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_adjoin_range_iff {ι : Type*} (i : ι → E) (x : E) :
    x ∈ adjoin F (Set.range i) ↔ ∃ r s : MvPolynomial ι F,
      x = MvPolynomial.aeval i r / MvPolynomial.aeval i s := by
  simp_rw [mem_adjoin_iff_div, Algebra.adjoin_range_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]
/-
**IntermediateField.mem_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：mem_adjoin_iff (x : E) : x in adjoin F S ↔ exists r s : MvPolynomial S F, 
x = MvPolynomial.aeval Subtype.val r / MvPolynomial.aeval Subtype.val s
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.mem_adjoin_range_iff`：mem_adjoin_range_iff {ι : Type*}
 (i : ι -> E) (x : E) : x in adjoin F (Set.range i) ↔ exists r s : MvPolynomial 
ι F, x = MvPolynomial.aeval …
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_adjoin_iff (x : E) :
    x ∈ adjoin F S ↔ ∃ r s : MvPolynomial S F,
      x = MvPolynomial.aeval Subtype.val r / MvPolynomial.aeval Subtype.val s := by
  rw [← mem_adjoin_range_iff, Subtype.range_coe]
/-
**IntermediateField.mem_adjoin_simple_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField`。
形式化陈述：mem_adjoin_simple_iff {α : E} (x : E) : x in adjoin F {α} ↔ exists r s : F
[X], x = aeval α r / aeval α s
参数：x : E。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.adjoin_singleton_eq_range_aeval`：adjoin_singleton_eq_range_aeval
 (x : A) : adjoin R {x} = (aeval x).range
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_adjoin_simple_iff {α : E} (x : E) :
    x ∈ adjoin F {α} ↔ ∃ r s : F[X], x = aeval α r / aeval α s := by
  simp only [mem_adjoin_iff_div, Algebra.adjoin_singleton_eq_range_aeval,
    AlgHom.mem_range, exists_exists_eq_and]
/-
**IntermediateField.forall_mem_adjoin_smul_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField`。
形式化陈述：forall_mem_adjoin_smul_eq_self_iff {M : Type*} [Monoid M] [MulSemiringActi
on M E] [SMulCommClass M F E] (m : M) : (forall x in adjoin F S, m • x = x) ↔ fo
rall x in S, m • x = x
参数：m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
-/
theorem forall_mem_adjoin_smul_eq_self_iff {M : Type*} [Monoid M] [MulSemiringAction M E]
    [SMulCommClass M F E] (m : M) :
    (∀ x ∈ adjoin F S, m • x = x) ↔ ∀ x ∈ S, m • x = x := by
  simpa [-adjoin_le_iff, Set.subset_def, SetLike.le_def, FixedBy.intermediateField_mem_iff] using
    adjoin_le_iff (T := FixedBy.intermediateField F E m)

variable {F}

section Supremum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)

/-
**IntermediateField.finiteDimensional_sup** 是 Mathlib 中的一个实例，位于命名空间 `Intermediat
eField`。
形式化陈述：finiteDimensional_sup [FiniteDimensional K E1] [FiniteDimensional K E2] : 
FiniteDimensional K (E1 ⊔ E2 : IntermediateField K L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.productMap_range`：productMap_range : (productMap f
 g).range = f.range ⊔ g.range
· 使用定理 `IntermediateField.range_val`：range_val : S.val.range = S.toSubalgebra
· 使用定理 `IntermediateField.sup_toSubalgebra_of_left`：sup_toSubalgebra_of_left [Fi
niteDimensional K E1] : (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgeb
ra
-/
instance finiteDimensional_sup [FiniteDimensional K E1] [FiniteDimensional K E2] :
    FiniteDimensional K (E1 ⊔ E2 : IntermediateField K L) := by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  suffices g.range = (E1 ⊔ E2).toSubalgebra by
    have h : FiniteDimensional K (Subalgebra.toSubmodule g.range) :=
      g.toLinearMap.finiteDimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.productMap_range, E1.range_val, E2.range_val, sup_toSubalgebra_of_left]

/-- If `E1` and `E2` are intermediate fields, and at least one them are algebraic, then the rank of
the compositum of `E1` and `E2` is less than or equal to the product of that of `E1` and `E2`.
Note that this result is also true without algebraic assumption,
but the proof becomes very complicated. -/
/-
**IntermediateField.rank_sup_le_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：rank_sup_le_of_isAlgebraic (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAl
gebraic K E2) : Module.rank K ↥(E1 ⊔ E2) <= Module.rank K E1 * Module.rank K E2
参数：halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.rank_sup_le_of_free`：rank_sup_le_of_free : Module.rank R ↥(A 
⊔ B) <= Module.rank R A * Module.rank R B
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic`：sup_toSubalgebra_of_i
sAlgebraic (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) : (E1 ⊔ 
E2).toSubalgebra = E1.toSubalgebra ⊔ E2…

--- 原说明 ---
If `E1` and `E2` are intermediate fields, and at least one them are algebraic, t
hen the rank of
the compositum of `E1` and `E2` is less than or equal to the product of that of 
`E1` and `E2`.
Note that this result is also true without algebraic assumption,
but the proof becomes very complicated.
-/
theorem rank_sup_le_of_isAlgebraic
    (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) :
    Module.rank K ↥(E1 ⊔ E2) ≤ Module.rank K E1 * Module.rank K E2 := by
  have := E1.toSubalgebra.rank_sup_le_of_free E2.toSubalgebra
  rwa [← sup_toSubalgebra_of_isAlgebraic E1 E2 halg] at this

/-- If `E1` and `E2` are intermediate fields, then the `Module.finrank` of
the compositum of `E1` and `E2` is less than or equal to the product of that of `E1` and `E2`. -/
/-
**IntermediateField.finrank_sup_le** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`
。
形式化陈述：finrank_sup_le : finrank K ↥(E1 ⊔ E2) <= finrank K E1 * finrank K E2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.finrank_sup_le_of_free`：finrank_sup_le_of_free : finrank R ↥(
A ⊔ B) <= finrank R A * finrank R B
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.sup_toSubalgebra_of_left`：sup_toSubalgebra_of_left [Fi
niteDimensional K E1] : (E1 ⊔ E2).toSubalgebra = E1.toSubalgebra ⊔ E2.toSubalgeb
ra
· 使用定理 `LinearMap.rank_le_of_injective`：LinearMap.rank_le_of_injective (f : M ->
ₗ[R] M₁) (i : Injective f) : Module.rank R M <= Module.rank R M₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
· 使用定理 `Cardinal.toNat_apply_of_aleph0_le`：toNat_apply_of_aleph0_le {c : Cardina
l} (h : ℵ₀ <= c) : toNat c = 0
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `Module.rank_lt_aleph0_iff`：rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ M
odule.Finite R M
· 使用定理 `FiniteDimensional.eq_1`：∀ (K : Type u_1) (V : Type u_2) [inst : Division
Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   FiniteDimensio
nal K V = Mo…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `E1` and `E2` are intermediate fields, then the `Module.finrank` of
the compositum of `E1` and `E2` is less than or equal to the product of that of 
`E1` and `E2`.
-/
theorem finrank_sup_le :
    finrank K ↥(E1 ⊔ E2) ≤ finrank K E1 * finrank K E2 := by
  by_cases h : FiniteDimensional K E1
  · have := E1.toSubalgebra.finrank_sup_le_of_free E2.toSubalgebra
    change _ ≤ finrank K E1 * finrank K E2 at this
    rwa [← sup_toSubalgebra_of_left] at this
  rw [FiniteDimensional, ← rank_lt_aleph0_iff, not_lt] at h
  have := LinearMap.rank_le_of_injective _ <| Submodule.inclusion_injective <|
    show Subalgebra.toSubmodule E1.toSubalgebra ≤ Subalgebra.toSubmodule (E1 ⊔ E2).toSubalgebra by
      simp
  rw [show finrank K E1 = 0 from Cardinal.toNat_apply_of_aleph0_le h,
    show finrank K ↥(E1 ⊔ E2) = 0 from Cardinal.toNat_apply_of_aleph0_le (h.trans this), zero_mul]

variable {ι : Type*} {t : ι → IntermediateField K L}
/-
**IntermediateField.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：coe_iSup_of_directed [Nonempty ι] (dir : Directed (· <= ·) t) : ↑(iSup t) 
= ⋃ i, (t i : Set L)
参数：dir : Directed (· <= ·) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.coe_iSup_of_directed`：coe_iSup_of_directed (dir : Directed (·
 <= ·) K) : ↑(iSup K) = ⋃ i, (K i : Set A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.inv_mem`：∀ {K : Type u_1} {L : Type u_2} [inst : Field
 K] [inst_1 : Field L] [inst_2 : Algebra K L] (S : IntermediateField K L)   {x :
 L}, x ∈ S → x⁻…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
-/
theorem coe_iSup_of_directed [Nonempty ι] (dir : Directed (· ≤ ·) t) :
    ↑(iSup t) = ⋃ i, (t i : Set L) :=
  let M : IntermediateField K L :=
    { __ := Subalgebra.copy _ _ (Subalgebra.coe_iSup_of_directed dir).symm
      inv_mem' := fun _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (t i).inv_mem hi⟩ }
  have : iSup t = M := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (t i : Set L)) i) (Set.iUnion_subset fun _ ↦ le_iSup t _)
  this.symm ▸ rfl
/-
**IntermediateField.toSubalgebra_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：toSubalgebra_iSup_of_directed (dir : Directed (· <= ·) t) : (iSup t).toSub
algebra = ⨆ i, (t i).toSubalgebra
参数：dir : Directed (· <= ·) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty`：iSup_of_empty [IsEmpty ι] (f : ι -> α) : iSup f = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IntermediateField.coe_iSup_of_directed`：coe_iSup_of_directed [Nonempty ι
] (dir : Directed (· <= ·) t) : ↑(iSup t) = ⋃ i, (t i : Set L)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.coe_iSup_of_directed`：coe_iSup_of_directed (dir : Directed (·
 <= ·) K) : ↑(iSup K) = ⋃ i, (K i : Set A)
-/
theorem toSubalgebra_iSup_of_directed (dir : Directed (· ≤ ·) t) :
    (iSup t).toSubalgebra = ⨆ i, (t i).toSubalgebra := by
  cases isEmpty_or_nonempty ι
  · simp_rw [iSup_of_empty, bot_toSubalgebra]
  · exact SetLike.ext' ((coe_iSup_of_directed dir).trans (Subalgebra.coe_iSup_of_directed dir).symm)
/-
**IntermediateField.finiteDimensional_iSup_of_finite** 是 Mathlib 中的一个实例，位于命名空间 `
IntermediateField`。
形式化陈述：finiteDimensional_iSup_of_finite [h : Finite ι] [forall i, FiniteDimension
al K (t i)] : FiniteDimensional K (⨆ i, t i : IntermediateField K L)
参数：t i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_univ`：iSup_univ {f : β -> α} : ⨆ x in (univ : Set β), f x = ⨆ x, f 
x
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `iSup_emptyset`：iSup_emptyset {f : β -> α} : ⨆ x in (∅ : Set β), f x = ⊥
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `iSup_insert`：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in inser
t b s, f x = f b ⊔ ⨆ x in s, f x
-/
instance finiteDimensional_iSup_of_finite [h : Finite ι] [∀ i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i, t i : IntermediateField K L) := by
  rw [← iSup_univ]
  induction Set.univ, Set.finite_univ (α := ι) using Set.Finite.induction_on with
  | empty =>
    rw [iSup_emptyset]
    exact (botEquiv K L).symm.toLinearEquiv.finiteDimensional
  | insert s hs =>
    rw [iSup_insert]
    exact IntermediateField.finiteDimensional_sup _ _

/-- See `finiteDimensional_iSup_of_finset'` for a stronger version,
that was the one used in mathlib3. -/
/-
**IntermediateField.finiteDimensional_iSup_of_finset** 是 Mathlib 中的一个实例，位于命名空间 `
IntermediateField`。
形式化陈述：finiteDimensional_iSup_of_finset {s : Finset ι} [forall i, FiniteDimension
al K (t i)] : FiniteDimensional K (⨆ i in s, t i : IntermediateField K L)
参数：t i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t

--- 原说明 ---
See `finiteDimensional_iSup_of_finset'` for a stronger version,
that was the one used in mathlib3.
-/
instance finiteDimensional_iSup_of_finset
    {s : Finset ι} [∀ i, FiniteDimensional K (t i)] :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite
/-
**IntermediateField.finiteDimensional_iSup_of_finset'** 是 Mathlib 中的一个定理，位于命名空间 
`IntermediateField`。
形式化陈述：finiteDimensional_iSup_of_finset' {s : Finset ι} (h : forall i in s, Finit
eDimensional K (t i)) : FiniteDimensional K (⨆ i in s, t i : IntermediateField K
 L)
参数：h : forall i in s, FiniteDimensional K (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
-/
theorem finiteDimensional_iSup_of_finset'
    {s : Finset ι} (h : ∀ i ∈ s, FiniteDimensional K (t i)) :
    FiniteDimensional K (⨆ i ∈ s, t i : IntermediateField K L) :=
  have := Subtype.forall'.mp h
  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite

/-- A compositum of splitting fields is a splitting field -/
/-
**IntermediateField.isSplittingField_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField`。
形式化陈述：isSplittingField_iSup {p : ι -> K[X]} {s : Finset ι} (h0 : ∏ i in s, p i !
= 0) (h : forall i in s, (p i).IsSplittingField K (t i)) : (∏ i in s, p i).IsSpl
ittingField K (⨆ i in s, t i : IntermediateField K L)
参数：h0 : ∏ i in s, p i != 0；h : forall i in s, (p i).IsSplittingField K (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_prod`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R)
 (s : Fin…
· 使用定理 `Polynomial.Splits.prod`：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Ty
pe u_2} {f : ι → Polynomial R} {s : Finset ι},   (∀ i ∈ s, (f i).Splits) → (∏ i 
∈ s, f i).Sp…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.rootSet_prod`：rootSet_prod [CommRing S] [IsDomain S] [Algebra
 R S] {ι : Type*} (f : ι -> R[X]) (s : Finset ι) (h : s.prod f != 0) : (s.prod f
).rootSet S =…
· 使用定理 `GaloisConnection.l_iSup₂`：l_iSup₂ {f : forall i, κ i -> α} : l (⨆ (i) (j
), f i j) = ⨆ (i) (j), l (f i j)
· 使用定理 `IntermediateField.gc`：gc : GaloisConnection (adjoin F : Set E -> Interme
diateField F E) (fun (x : IntermediateField F E) => (x : Set E))
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A compositum of splitting fields is a splitting field
-/
theorem isSplittingField_iSup {p : ι → K[X]}
    {s : Finset ι} (h0 : ∏ i ∈ s, p i ≠ 0) (h : ∀ i ∈ s, (p i).IsSplittingField K (t i)) :
    (∏ i ∈ s, p i).IsSplittingField K (⨆ i ∈ s, t i : IntermediateField K L) := by
  let F : IntermediateField K L := ⨆ i ∈ s, t i
  have hF : ∀ i ∈ s, t i ≤ F := fun i hi ↦ le_iSup_of_le i (le_iSup (fun _ ↦ t i) hi)
  simp only [isSplittingField_iff, Polynomial.map_prod] at h ⊢
  refine ⟨Splits.prod fun i hi ↦ by
    simpa [Polynomial.map_map] using (h i hi).1.map (inclusion (hF i hi)).toRingHom, ?_⟩
  simp only [rootSet_prod p s h0, ← Set.iSup_eq_iUnion, (@gc K _ L _ _).l_iSup₂]
  exact iSup_congr fun i ↦ iSup_congr fun hi ↦ (h i hi).2

end Supremum

section Tower

variable (E)
variable {K : Type*} [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/-- If `K / E / F` is a field extension tower, `L` is an intermediate field of `K / F`, such that
either `E / F` or `L / F` is algebraic, then `[E(L) : E] ≤ [L : F]`. A corollary of
`Subalgebra.adjoin_rank_le` since in this case `E(L) = E[L]`. -/
/-
**IntermediateField.adjoin_rank_le_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：adjoin_rank_le_of_isAlgebraic (L : IntermediateField F K) (halg : Algebra.
IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) : Module.rank E (adjoin E (L : Set K)
) <= Module.rank F L
参数：L : IntermediateField F K；halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebrai
c F L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic`：
adjoin_intermediateField_toSubalgebra_of_isAlgebraic (L : IntermediateField F K)
 (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) …
· 使用引理 `Subalgebra.adjoin_rank_le`：Subalgebra.adjoin_rank_le {F : Type*} (E : Ty
pe*) {K : Type*} [CommSemiring F] [StrongRankCondition F] [CommSemiring E] [Stro
ngRankCondition…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁

--- 原说明 ---
If `K / E / F` is a field extension tower, `L` is an intermediate field of `K / 
F`, such that
either `E / F` or `L / F` is algebraic, then `[E(L) : E] ≤ [L : F]`. A corollary
 of
`Subalgebra.adjoin_rank_le` since in this case `E(L) = E[L]`.
-/
theorem adjoin_rank_le_of_isAlgebraic (L : IntermediateField F K)
    (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F L) :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L := by
  have h : (adjoin E (L.toSubalgebra : Set K)).toSubalgebra =
      Algebra.adjoin E (L.toSubalgebra : Set K) :=
    L.adjoin_intermediateField_toSubalgebra_of_isAlgebraic E halg
  have := L.toSubalgebra.adjoin_rank_le E
  rwa [(Subalgebra.equivOfEq _ _ h).symm.toLinearEquiv.rank_eq] at this
/-
**IntermediateField.adjoin_rank_le_of_isAlgebraic_left** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField`。
形式化陈述：adjoin_rank_le_of_isAlgebraic_left (L : IntermediateField F K) [halg : Alg
ebra.IsAlgebraic F E] : Module.rank E (adjoin E (L : Set K)) <= Module.rank F L
参数：L : IntermediateField F K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_rank_le_of_isAlgebraic`：adjoin_rank_le_of_isAlg
ebraic (L : IntermediateField F K) (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsA
lgebraic F L) : Module.rank E (adjoin…
-/
theorem adjoin_rank_le_of_isAlgebraic_left (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F E] :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inl halg)
/-
**IntermediateField.adjoin_rank_le_of_isAlgebraic_right** 是 Mathlib 中的一个定理，位于命名空
间 `IntermediateField`。
形式化陈述：adjoin_rank_le_of_isAlgebraic_right (L : IntermediateField F K) [halg : Al
gebra.IsAlgebraic F L] : Module.rank E (adjoin E (L : Set K)) <= Module.rank F L
参数：L : IntermediateField F K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_rank_le_of_isAlgebraic`：adjoin_rank_le_of_isAlg
ebraic (L : IntermediateField F K) (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsA
lgebraic F L) : Module.rank E (adjoin…
-/
theorem adjoin_rank_le_of_isAlgebraic_right (L : IntermediateField F K)
    [halg : Algebra.IsAlgebraic F L] :
    Module.rank E (adjoin E (L : Set K)) ≤ Module.rank F L :=
  adjoin_rank_le_of_isAlgebraic E L (Or.inr halg)

end Tower

open Set CompleteLattice

/-- Adjoining a single element is compact in the lattice of intermediate fields. -/
/-
**IntermediateField.adjoin_simple_isCompactElement** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
形式化陈述：adjoin_simple_isCompactElement (x : E) : IsCompactElement F⟮x⟯
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `IntermediateField.coe_iSup_of_directed`：coe_iSup_of_directed [Nonempty ι
] (dir : Directed (· <= ·) t) : ↑(iSup t) = ⋃ i, (t i : Set L)
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p

--- 原说明 ---
Adjoining a single element is compact in the lattice of intermediate fields.
-/
theorem adjoin_simple_isCompactElement (x : E) : IsCompactElement F⟮x⟯ := by
  simp_rw [isCompactElement_iff_le_of_directed_sSup_le,
    adjoin_simple_le_iff, sSup_eq_iSup', ← exists_prop]
  intro s hne hs hx
  have := hne.to_subtype
  rwa [← SetLike.mem_coe, coe_iSup_of_directed hs.directed_val, mem_iUnion, Subtype.exists] at hx

/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
/-
**IntermediateField.adjoin_finset_isCompactElement** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
形式化陈述：adjoin_finset_isCompactElement (S : Finset E) : IsCompactElement (adjoin F
 S : IntermediateField F E)
参数：S : Finset E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.biSup_adjoin_simple`：biSup_adjoin_simple : ⨆ x in S, F
⟮x⟯ = adjoin F S
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CompleteLattice.isCompactElement_finsetSup`：isCompactElement_finsetSup {
α β : Type*} [CompleteLattice α] {f : β -> α} (s : Finset β) (h : forall x in s,
 IsCompactElement (f x)) : IsCom…
· 使用定理 `IntermediateField.adjoin_simple_isCompactElement`：adjoin_simple_isCompac
tElement (x : E) : IsCompactElement F⟮x⟯

--- 原说明 ---
Adjoining a finite subset is compact in the lattice of intermediate fields.
-/
theorem adjoin_finset_isCompactElement (S : Finset E) :
    IsCompactElement (adjoin F S : IntermediateField F E) := by
  rw [← biSup_adjoin_simple]
  simp_rw [Finset.mem_coe, ← Finset.sup_eq_iSup]
  exact isCompactElement_finsetSup S fun x _ => adjoin_simple_isCompactElement x

/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
/-
**IntermediateField.adjoin_finite_isCompactElement** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
形式化陈述：adjoin_finite_isCompactElement {S : Set E} (h : S.Finite) : IsCompactEleme
nt (adjoin F S)
参数：h : S.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin_finset_isCompactElement`：adjoin_finset_isCompac
tElement (S : Finset E) : IsCompactElement (adjoin F S : IntermediateField F E)
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s

--- 原说明 ---
Adjoining a finite subset is compact in the lattice of intermediate fields.
-/
theorem adjoin_finite_isCompactElement {S : Set E} (h : S.Finite) : IsCompactElement (adjoin F S) :=
  Finite.coe_toFinset h ▸ adjoin_finset_isCompactElement h.toFinset

/-- The lattice of intermediate fields is compactly generated. -/
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lattice of intermediate fields is compactly generated.
-/
instance : IsCompactlyGenerated (IntermediateField F E) :=
  ⟨fun s =>
    ⟨(fun x => F⟮x⟯) '' s,
      ⟨by rintro t ⟨x, _, rfl⟩; exact adjoin_simple_isCompactElement x,
        sSup_image.trans <| (biSup_adjoin_simple _).trans <|
          le_antisymm (adjoin_le_iff.mpr le_rfl) <| subset_adjoin F (s : Set E)⟩⟩⟩
/-
**IntermediateField.exists_finset_of_mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：exists_finset_of_mem_iSup {ι : Type*} {f : ι -> IntermediateField F E} {x 
: E} (hx : x in ⨆ i, f i) : exists s : Finset ι, x in ⨆ i in s, f i
参数：hx : x in ⨆ i, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLattice.IsCompactElement.exists_finset_of_le_iSup`：∀ (α : Type u
_2) [inst : CompleteLattice α] {k : α},   IsCompactElement k → ∀ {ι : Type u_3} 
(f : ι → α), k ≤ ⨆ i, f i → ∃ s, k ≤ ⨆ i ∈ s, f…
· 使用定理 `IntermediateField.adjoin_simple_isCompactElement`：adjoin_simple_isCompac
tElement (x : E) : IsCompactElement F⟮x⟯
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem exists_finset_of_mem_iSup {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset ι, x ∈ ⨆ i ∈ s, f i := by
  have := (adjoin_simple_isCompactElement x).exists_finset_of_le_iSup (IntermediateField F E) f
  simp only [adjoin_simple_le_iff] at this
  exact this hx
/-
**IntermediateField.exists_finset_of_mem_supr'** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：exists_finset_of_mem_supr' {ι : Type*} {f : ι -> IntermediateField F E} {x
 : E} (hx : x in ⨆ i, f i) : exists s : Finset (Σ i, f i), x in ⨆ i in s, F⟮(i.2
 : E)⟯
参数：hx : x in ⨆ i, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_finset_of_mem_iSup`：exists_finset_of_mem_iSup {
ι : Type*} {f : ι -> IntermediateField F E} {x : E} (hx : x in ⨆ i, f i) : exist
s s : Finset ι, x in ⨆ i in s, f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IntermediateField.mem_adjoin_simple_self`：mem_adjoin_simple_self : α in 
F⟮α⟯
-/
theorem exists_finset_of_mem_supr' {ι : Type*} {f : ι → IntermediateField F E} {x : E}
    (hx : x ∈ ⨆ i, f i) : ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, F⟮(i.2 : E)⟯ := by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le fun i x h ↦ ?_) hx)
  exact SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)
/-
**IntermediateField.exists_finset_of_mem_supr''** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField`。
形式化陈述：exists_finset_of_mem_supr'' {ι : Type*} {f : ι -> IntermediateField F E} (
h : forall i, Algebra.IsAlgebraic F (f i)) {x : E} (hx : x in ⨆ i, f i) : exists
 s : Finset (Σ i, f i), x in ⨆ i in s, adjoin F ((minpoly F (i.2 :)).rootSet E)
参数：h : forall i, Algebra.IsAlgebraic F (f i)；hx : x in ⨆ i, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_finset_of_mem_iSup`：exists_finset_of_mem_iSup {
ι : Type*} {f : ι -> IntermediateField F E} {x : E} (hx : x in ⨆ i, f i) : exist
s s : Finset ι, x in ⨆ i in s, f …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.minpoly_eq`：minpoly_eq (x : S) : minpoly K x = minpoly
 K (x : L)
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用引理 `Polynomial.mem_rootSet_of_ne`：mem_rootSet_of_ne {p : T[X]} {S : Type*} [
IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] (
hp : p != 0) {a : …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IntermediateField.isIntegral_iff`：isIntegral_iff {x : S} : IsIntegral K 
x ↔ IsIntegral K (x : L)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
-/
theorem exists_finset_of_mem_supr'' {ι : Type*} {f : ι → IntermediateField F E}
    (h : ∀ i, Algebra.IsAlgebraic F (f i)) {x : E} (hx : x ∈ ⨆ i, f i) :
    ∃ s : Finset (Σ i, f i), x ∈ ⨆ i ∈ s, adjoin F ((minpoly F (i.2 :)).rootSet E) := by
  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i x1 hx1 => ?_)) hx)
  refine SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ ?_)
    (subset_adjoin F (rootSet (minpoly F x1) E) ?_)
  · rw [IntermediateField.minpoly_eq, Subtype.coe_mk]
  · rw [mem_rootSet_of_ne, minpoly.aeval]
    exact minpoly.ne_zero (isIntegral_iff.mp (Algebra.IsIntegral.isIntegral (⟨x1, hx1⟩ : f i)))
/-
**IntermediateField.exists_finset_of_mem_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField`。
形式化陈述：exists_finset_of_mem_adjoin {S : Set E} {x : E} (hx : x in adjoin F S) : e
xists T : Finset E, (T : Set E) subseteq S ∧ x in adjoin F (T : Set E)
参数：hx : x in adjoin F S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_finset_of_mem_iSup`：exists_finset_of_mem_iSup {
ι : Type*} {f : ι -> IntermediateField F E} {x : E} (hx : x in ⨆ i, f i) : exist
s s : Finset ι, x in ⨆ i in s, f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.biSup_adjoin_simple`：biSup_adjoin_simple : ⨆ x in S, F
⟮x⟯ = adjoin F S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
-/
theorem exists_finset_of_mem_adjoin {S : Set E} {x : E} (hx : x ∈ adjoin F S) :
    ∃ T : Finset E, (T : Set E) ⊆ S ∧ x ∈ adjoin F (T : Set E) := by
  simp_rw [← biSup_adjoin_simple S, ← iSup_subtype''] at hx
  obtain ⟨s, hx'⟩ := exists_finset_of_mem_iSup hx
  classical
  refine ⟨s.image Subtype.val, by simp, SetLike.le_def.mp ?_ hx'⟩
  simp_rw [Finset.coe_image, iSup_le_iff, adjoin_le_iff]
  rintro _ h _ rfl
  exact subset_adjoin F _ ⟨_, h, rfl⟩

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E} {S : Set E}

section AdjoinRank

open Module Module

variable {K L : IntermediateField F E}

@[simp]
/-
**IntermediateField.rank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：rank_eq_one_iff : Module.rank F K = 1 ↔ K = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.toSubalgebra_inj`：toSubalgebra_inj : F.toSubalgebra = 
E.toSubalgebra ↔ F = E
· 使用定理 `IntermediateField.rank_eq_rank_subalgebra`：rank_eq_rank_subalgebra : Mod
ule.rank K F.toSubalgebra = Module.rank K F
· 使用定理 `Subalgebra.rank_eq_one_iff`：rank_eq_one_iff [Nontrivial E] [Module.Free 
F S] : Module.rank F S = 1 ↔ S = ⊥
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IntermediateField.bot_toSubalgebra`：bot_toSubalgebra : (⊥ : Intermediate
Field F E).toSubalgebra = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rank_eq_one_iff : Module.rank F K = 1 ↔ K = ⊥ := by
  rw [← toSubalgebra_inj, ← rank_eq_rank_subalgebra, Subalgebra.rank_eq_one_iff,
    bot_toSubalgebra]

@[simp]
/-
**IntermediateField.finrank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.toSubalgebra_inj`：toSubalgebra_inj : F.toSubalgebra = 
E.toSubalgebra ↔ F = E
· 使用定理 `IntermediateField.finrank_eq_finrank_subalgebra`：finrank_eq_finrank_suba
lgebra : finrank K F.toSubalgebra = finrank K F
· 使用定理 `Subalgebra.finrank_eq_one_iff`：finrank_eq_one_iff [Nontrivial E] [Module
.Free F S] : finrank F S = 1 ↔ S = ⊥
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IntermediateField.bot_toSubalgebra`：bot_toSubalgebra : (⊥ : Intermediate
Field F E).toSubalgebra = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ := by
  rw [← toSubalgebra_inj, ← finrank_eq_finrank_subalgebra, Subalgebra.finrank_eq_one_iff,
    bot_toSubalgebra]

@[simp]
/-
**IntermediateField.rank_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E], Module.rank F ↥⊥ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.rank_eq_one_iff`：rank_eq_one_iff : Module.rank F K = 1
 ↔ K = ⊥
-/
protected theorem rank_bot : Module.rank F (⊥ : IntermediateField F E) = 1 := by
  rw [rank_eq_one_iff]

@[simp]
/-
**IntermediateField.finrank_bot** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E], Module.finrank F ↥⊥ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.finrank_eq_one_iff`：finrank_eq_one_iff : finrank F K =
 1 ↔ K = ⊥
-/
protected theorem finrank_bot : finrank F (⊥ : IntermediateField F E) = 1 := by
  rw [finrank_eq_one_iff]
/-
**IntermediateField.rank_bot'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E],   Module.rank (↥⊥) E = Module.rank F E
参数：↥⊥。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_mul_rank`：rank_mul_rank (A : Type v) [AddCommMonoid A] [Module K A]
 [Module F A] [IsScalarTower F K A] [Module.Free K A] : Module.rank F K * Module
.ra…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IntermediateField.rank_bot`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.rank F ↥⊥ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
@[simp] theorem rank_bot' : Module.rank (⊥ : IntermediateField F E) E = Module.rank F E := by
  rw [← rank_mul_rank F (⊥ : IntermediateField F E) E, IntermediateField.rank_bot, one_mul]

@[simp]
/-
**IntermediateField.finrank_bot'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：finrank_bot' : finrank (⊥ : IntermediateField F E) E = finrank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.rank_bot'`：∀ {F : Type u_1} [inst : Field F] {E : Type
 u_2} [inst_1 : Field E] [inst_2 : Algebra F E],   Module.rank (↥⊥) E = Module.r
ank F E
-/
theorem finrank_bot' : finrank (⊥ : IntermediateField F E) E = finrank F E :=
  congr(Cardinal.toNat $(rank_bot'))
/-
**IntermediateField.rank_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E], Module.rank (↥⊤) E = 1
参数：↥⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subalgebra.bot_eq_top_iff_rank_eq_one`：bot_eq_top_iff_rank_eq_one [Nontr
ivial E] [Module.Free F E] : (⊥ : Subalgebra F E) = ⊤ ↔ Module.rank F E = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `trivial`：True
-/
@[simp] protected theorem rank_top : Module.rank (⊤ : IntermediateField F E) E = 1 :=
  Subalgebra.bot_eq_top_iff_rank_eq_one.mp <| top_le_iff.mp fun x _ ↦ ⟨⟨x, trivial⟩, rfl⟩

@[simp]
/-
**IntermediateField.finrank_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E], Module.finrank (↥⊤) E = 1
参数：↥⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.rank_eq_one_iff_finrank_eq_one`：rank_eq_one_iff_finrank_eq_one : 
Module.rank R M = 1 ↔ finrank R M = 1
· 使用定理 `IntermediateField.rank_top`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.rank (↥⊤) E = 1
-/
protected theorem finrank_top : finrank (⊤ : IntermediateField F E) E = 1 :=
  rank_eq_one_iff_finrank_eq_one.mp IntermediateField.rank_top
/-
**IntermediateField.rank_top'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E],   Module.rank F ↥⊤ = Module.rank F E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rank_top`：rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M
-/
@[simp] theorem rank_top' : Module.rank F (⊤ : IntermediateField F E) = Module.rank F E :=
  rank_top F E
/-
**IntermediateField.finrank_top'** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {E : Type u_2} [inst_1 : Field E] [inst_
2 : Algebra F E],   Module.finrank F ↥⊤ = Module.finrank F E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
-/
@[simp] theorem finrank_top' : finrank F (⊤ : IntermediateField F E) = finrank F E :=
  finrank_top F E
/-
**IntermediateField.finrank_eq_one_iff_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Interme
diateField`。
形式化陈述：finrank_eq_one_iff_eq_top {K : IntermediateField F E} : Module.finrank K E
 = 1 ↔ K = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.bot_eq_top_iff_finrank_eq_one`：bot_eq_top_iff_finrank_eq_one 
[Nontrivial E] [Module.Free F E] : (⊥ : Subalgebra F E) = ⊤ ↔ finrank F E = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `IntermediateField.mem_top`：mem_top {x : E} : x in (⊤ : IntermediateField
 F E)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IntermediateField.finrank_top`：∀ {F : Type u_1} [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.finrank (↥⊤) E = 1
-/
lemma finrank_eq_one_iff_eq_top {K : IntermediateField F E} :
    Module.finrank K E = 1 ↔ K = ⊤ := by
  refine ⟨?_, (· ▸ IntermediateField.finrank_top)⟩
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one, ← top_le_iff, ← top_le_iff]
  intro H x _
  obtain ⟨x, rfl⟩ := @H x IntermediateField.mem_top
  exact x.2
/-
**IntermediateField.bot_eq_top_iff_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：bot_eq_top_iff_finrank_eq_one : (⊥ : IntermediateField F E) = ⊤ ↔ Module.f
inrank F E = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.finrank_bot'`：finrank_bot' : finrank (⊥ : Intermediate
Field F E) E = finrank F E
· 使用引理 `IntermediateField.finrank_eq_one_iff_eq_top`：finrank_eq_one_iff_eq_top {
K : IntermediateField F E} : Module.finrank K E = 1 ↔ K = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot_eq_top_iff_finrank_eq_one :
    (⊥ : IntermediateField F E) = ⊤ ↔ Module.finrank F E = 1 := by
  rw [← IntermediateField.finrank_bot', ← finrank_eq_one_iff_eq_top]

variable (F E) in
/-
**IntermediateField.isSimpleOrder_of_finrank_prime** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
形式化陈述：isSimpleOrder_of_finrank_prime (hp : Nat.Prime (Module.finrank F E)) : IsS
impleOrder (IntermediateField F E)
参数：hp : Nat.Prime (Module.finrank F E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_one_false`：Nat.Prime 1 → False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.bot_eq_top_iff_finrank_eq_one`：bot_eq_top_iff_finrank_
eq_one : (⊥ : IntermediateField F E) = ⊤ ↔ Module.finrank F E = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.apply_eq_bot_iff`：StrictMono.apply_eq_bot_iff (hf : StrictMon
o f) : f a = f ⊥ ↔ a = ⊥
· 使用定理 `IntermediateField.toSubalgebra_strictMono`：toSubalgebra_strictMono : Str
ictMono (IntermediateField.toSubalgebra : _ -> Subalgebra K L)
· 使用定理 `StrictMono.apply_eq_top_iff`：StrictMono.apply_eq_top_iff (hf : StrictMon
o f) : f a = f ⊤ ↔ a = ⊤
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `Subalgebra.isSimpleOrder_of_finrank_prime`：Subalgebra.isSimpleOrder_of_f
inrank_prime (F A) [Field F] [Ring A] [IsDomain A] [Algebra F A] (hp : (finrank 
F A).Prime) : IsSimpleOrder (Su…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem isSimpleOrder_of_finrank_prime (hp : Nat.Prime (Module.finrank F E)) :
    IsSimpleOrder (IntermediateField F E) := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · exact ⟨⊥, ⊤, fun h ↦ Nat.prime_one_false (bot_eq_top_iff_finrank_eq_one.mp h ▸ hp)⟩
  · intro K
    simpa [← toSubalgebra_strictMono.apply_eq_bot_iff, ← toSubalgebra_strictMono.apply_eq_top_iff]
      using (Subalgebra.isSimpleOrder_of_finrank_prime _ _ hp).eq_bot_or_eq_top K.toSubalgebra
/-
**IntermediateField.rank_adjoin_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：rank_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S subseteq (⊥ : 
IntermediateField F E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IntermediateField.rank_eq_one_iff`：rank_eq_one_iff : Module.rank F K = 1
 ↔ K = ⊥
· 使用定理 `IntermediateField.adjoin_eq_bot_iff`：adjoin_eq_bot_iff : adjoin F S = ⊥ 
↔ S subseteq (⊥ : IntermediateField F E)
-/
theorem rank_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans rank_eq_one_iff adjoin_eq_bot_iff
/-
**IntermediateField.rank_adjoin_simple_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：rank_adjoin_simple_eq_one_iff : Module.rank F F⟮α⟯ = 1 ↔ α in (⊥ : Interme
diateField F E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.rank_adjoin_eq_one_iff`：rank_adjoin_eq_one_iff : Modul
e.rank F (adjoin F S) = 1 ↔ S subseteq (⊥ : IntermediateField F E)
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem rank_adjoin_simple_eq_one_iff :
    Module.rank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [rank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff
/-
**IntermediateField.finrank_adjoin_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S subseteq (⊥ : I
ntermediateField F E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IntermediateField.finrank_eq_one_iff`：finrank_eq_one_iff : finrank F K =
 1 ↔ K = ⊥
· 使用定理 `IntermediateField.adjoin_eq_bot_iff`：adjoin_eq_bot_iff : adjoin F S = ⊥ 
↔ S subseteq (⊥ : IntermediateField F E)
-/
theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff
/-
**IntermediateField.finrank_adjoin_simple_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
形式化陈述：finrank_adjoin_simple_eq_one_iff : finrank F F⟮α⟯ = 1 ↔ α in (⊥ : Intermed
iateField F E)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.finrank_adjoin_eq_one_iff`：finrank_adjoin_eq_one_iff :
 finrank F (adjoin F S) = 1 ↔ S subseteq (⊥ : IntermediateField F E)
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem finrank_adjoin_simple_eq_one_iff :
    finrank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : IntermediateField F E) := by
  rw [finrank_adjoin_eq_one_iff]; exact Set.singleton_subset_iff

/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
/-
**IntermediateField.bot_eq_top_of_rank_adjoin_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
形式化陈述：bot_eq_top_of_rank_adjoin_eq_one (h : forall x : E, Module.rank F F⟮x⟯ = 1
) : (⊥ : IntermediateField F E) = ⊤
参数：h : forall x : E, Module.rank F F⟮x⟯ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true_right`：∀ {a b : Prop}, a → ((b ↔ a) ↔ b)
· 使用定理 `IntermediateField.mem_top`：mem_top {x : E} : x in (⊤ : IntermediateField
 F E)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.rank_adjoin_simple_eq_one_iff`：rank_adjoin_simple_eq_o
ne_iff : Module.rank F F⟮α⟯ = 1 ↔ α in (⊥ : IntermediateField F E)

--- 原说明 ---
If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`.
-/
theorem bot_eq_top_of_rank_adjoin_eq_one (h : ∀ x : E, Module.rank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact rank_adjoin_simple_eq_one_iff.mp (h y)
/-
**IntermediateField.bot_eq_top_of_finrank_adjoin_eq_one** 是 Mathlib 中的一个定理，位于命名空
间 `IntermediateField`。
形式化陈述：bot_eq_top_of_finrank_adjoin_eq_one (h : forall x : E, finrank F F⟮x⟯ = 1)
 : (⊥ : IntermediateField F E) = ⊤
参数：h : forall x : E, finrank F F⟮x⟯ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true_right`：∀ {a b : Prop}, a → ((b ↔ a) ↔ b)
· 使用定理 `IntermediateField.mem_top`：mem_top {x : E} : x in (⊤ : IntermediateField
 F E)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.finrank_adjoin_simple_eq_one_iff`：finrank_adjoin_simpl
e_eq_one_iff : finrank F F⟮α⟯ = 1 ↔ α in (⊥ : IntermediateField F E)
-/
theorem bot_eq_top_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext y
  rw [iff_true_right IntermediateField.mem_top]
  exact finrank_adjoin_simple_eq_one_iff.mp (h y)
/-
**IntermediateField.subsingleton_of_rank_adjoin_eq_one** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField`。
形式化陈述：subsingleton_of_rank_adjoin_eq_one (h : forall x : E, Module.rank F F⟮x⟯ =
 1) : Subsingleton (IntermediateField F E)
参数：h : forall x : E, Module.rank F F⟮x⟯ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `IntermediateField.bot_eq_top_of_rank_adjoin_eq_one`：bot_eq_top_of_rank_a
djoin_eq_one (h : forall x : E, Module.rank F F⟮x⟯ = 1) : (⊥ : IntermediateField
 F E) = ⊤
-/
theorem subsingleton_of_rank_adjoin_eq_one (h : ∀ x : E, Module.rank F F⟮x⟯ = 1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_rank_adjoin_eq_one h)
/-
**IntermediateField.subsingleton_of_finrank_adjoin_eq_one** 是 Mathlib 中的一个定理，位于命
名空间 `IntermediateField`。
形式化陈述：subsingleton_of_finrank_adjoin_eq_one (h : forall x : E, finrank F F⟮x⟯ = 
1) : Subsingleton (IntermediateField F E)
参数：h : forall x : E, finrank F F⟮x⟯ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `IntermediateField.bot_eq_top_of_finrank_adjoin_eq_one`：bot_eq_top_of_fin
rank_adjoin_eq_one (h : forall x : E, finrank F F⟮x⟯ = 1) : (⊥ : IntermediateFie
ld F E) = ⊤
-/
theorem subsingleton_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)

/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
/-
**IntermediateField.bot_eq_top_of_finrank_adjoin_le_one** 是 Mathlib 中的一个定理，位于命名空
间 `IntermediateField`。
形式化陈述：bot_eq_top_of_finrank_adjoin_le_one [FiniteDimensional F E] (h : forall x 
: E, finrank F F⟮x⟯ <= 1) : (⊥ : IntermediateField F E) = ⊤
参数：h : forall x : E, finrank F F⟮x⟯ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.bot_eq_top_of_finrank_adjoin_eq_one`：bot_eq_top_of_fin
rank_adjoin_eq_one (h : forall x : E, finrank F F⟮x⟯ = 1) : (⊥ : IntermediateFie
ld F E) = ⊤
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`.
-/
theorem bot_eq_top_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h : ∀ x : E, finrank F F⟮x⟯ ≤ 1) : (⊥ : IntermediateField F E) = ⊤ := by
  apply bot_eq_top_of_finrank_adjoin_eq_one
  exact fun x => by linarith [h x, show 0 < finrank F F⟮x⟯ from finrank_pos]
/-
**IntermediateField.subsingleton_of_finrank_adjoin_le_one** 是 Mathlib 中的一个定理，位于命
名空间 `IntermediateField`。
形式化陈述：subsingleton_of_finrank_adjoin_le_one [FiniteDimensional F E] (h : forall 
x : E, finrank F F⟮x⟯ <= 1) : Subsingleton (IntermediateField F E)
参数：h : forall x : E, finrank F F⟮x⟯ <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `IntermediateField.bot_eq_top_of_finrank_adjoin_le_one`：bot_eq_top_of_fin
rank_adjoin_le_one [FiniteDimensional F E] (h : forall x : E, finrank F F⟮x⟯ <= 
1) : (⊥ : IntermediateField F E) = ⊤
-/
theorem subsingleton_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h : ∀ x : E, finrank F F⟮x⟯ ≤ 1) : Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)

end AdjoinRank

end AdjoinIntermediateFieldLattice

section AdjoinIntegralElement

universe u

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {α : E}
variable {K : Type u} [Field K] [Algebra F K]

/-
**IntermediateField.minpoly_gen** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：minpoly_gen (α : E) : minpoly F (AdjoinSimple.gen F α) = minpoly F α
参数：α : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.algebraMap_eq`：algebraMap_eq {B} [CommRing B] [Algebra A B] [Alg
ebra B B'] [IsScalarTower A B B'] (h : Function.Injective (algebraMap B B')) (x 
: B) : minp…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.AdjoinSimple.algebraMap_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   (al
gebraMap (↥F⟮α⟯) E) (IntermediateFi…
-/
theorem minpoly_gen (α : E) :
    minpoly F (AdjoinSimple.gen F α) = minpoly F α := by
  rw [← minpoly.algebraMap_eq (algebraMap F⟮α⟯ E).injective, AdjoinSimple.algebraMap_gen]
/-
**IntermediateField.aeval_gen_minpoly** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：aeval_gen_minpoly (α : E) : aeval (AdjoinSimple.gen F α) (minpoly F α) = 0
参数：α : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IntermediateField.AdjoinSimple.algebraMap_gen`：∀ (F : Type u_1) [inst : 
Field F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (α : E),   (al
gebraMap (↥F⟮α⟯) E) (IntermediateFi…
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
-/
theorem aeval_gen_minpoly (α : E) : aeval (AdjoinSimple.gen F α) (minpoly F α) = 0 := by
  ext
  convert! minpoly.aeval F α
  conv in aeval α => rw [← AdjoinSimple.algebraMap_gen F α]
  exact (aeval_algebraMap_apply E (AdjoinSimple.gen F α) _).symm

/-- algebra isomorphism between `AdjoinRoot` and `F⟮α⟯` -/
@[stacks 09G1 "Algebraic case"]
/-
**IntermediateField.adjoinRootEquivAdjoin** 是 Mathlib 中的一个定义，位于命名空间 `Intermediat
eField`。
形式化陈述：adjoinRootEquivAdjoin (h : IsIntegral F α) : AdjoinRoot (minpoly F α) ≃ₐ[F
] F⟮α⟯
参数：h : IsIntegral F α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.aeval_gen_minpoly`：aeval_gen_minpoly (α : E) : aeval (
AdjoinSimple.gen F α) (minpoly F α) = 0

--- 原说明 ---
algebra isomorphism between `AdjoinRoot` and `F⟮α⟯`
-/
noncomputable def adjoinRootEquivAdjoin (h : IsIntegral F α) :
    AdjoinRoot (minpoly F α) ≃ₐ[F] F⟮α⟯ :=
  AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom (minpoly F α) _ (AdjoinSimple.gen F α) (aeval_gen_minpoly F α))
    (by
      set f := AdjoinRoot.lift _ _ (aeval_gen_minpoly F α :)
      have := Fact.mk (minpoly.irreducible h)
      constructor
      · exact RingHom.injective f
      · suffices F⟮α⟯.toSubfield ≤ RingHom.fieldRange (F⟮α⟯.toSubfield.subtype.comp f) by
          intro x
          obtain ⟨y, hy⟩ := this (Subtype.mem x)
          exact ⟨y, Subtype.ext hy⟩
        refine Subfield.closure_le.mpr (Set.union_subset (fun x hx => ?_) ?_)
        · obtain ⟨y, hy⟩ := hx
          refine ⟨y, ?_⟩
          rw [RingHom.comp_apply]
          dsimp only [coe_type_toSubfield]
          rw [AdjoinRoot.lift_of (aeval_gen_minpoly F α)]
          exact hy
        · refine Set.singleton_subset_iff.mpr ⟨AdjoinRoot.root (minpoly F α), ?_⟩
          rw [RingHom.comp_apply]
          dsimp only [coe_type_toSubfield]
          rw [AdjoinRoot.lift_root (aeval_gen_minpoly F α)]
          rfl)
/-
**IntermediateField.adjoinRootEquivAdjoin_apply_root** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
形式化陈述：adjoinRootEquivAdjoin_apply_root (h : IsIntegral F α) : adjoinRootEquivAdj
oin F h (AdjoinRoot.root (minpoly F α)) = AdjoinSimple.gen F α
参数：h : IsIntegral F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdjoinRoot.lift_root`：lift_root : lift i a h (root f) = a
· 使用定理 `IntermediateField.aeval_gen_minpoly`：aeval_gen_minpoly (α : E) : aeval (
AdjoinSimple.gen F α) (minpoly F α) = 0
-/
theorem adjoinRootEquivAdjoin_apply_root (h : IsIntegral F α) :
    adjoinRootEquivAdjoin F h (AdjoinRoot.root (minpoly F α)) = AdjoinSimple.gen F α :=
  AdjoinRoot.lift_root (aeval_gen_minpoly F α)

@[simp]
/-
**IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen** 是 Mathlib 中的一个定理，位于命名
空间 `IntermediateField`。
形式化陈述：adjoinRootEquivAdjoin_symm_apply_gen (h : IsIntegral F α) : (adjoinRootEqu
ivAdjoin F h).symm (AdjoinSimple.gen F α) = AdjoinRoot.root (minpoly F α)
参数：h : IsIntegral F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_eq`：symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x
 = y ↔ x = e y
· 使用定理 `IntermediateField.adjoinRootEquivAdjoin_apply_root`：adjoinRootEquivAdjoi
n_apply_root (h : IsIntegral F α) : adjoinRootEquivAdjoin F h (AdjoinRoot.root (
minpoly F α)) = AdjoinSimple.gen F α
-/
theorem adjoinRootEquivAdjoin_symm_apply_gen (h : IsIntegral F α) :
    (adjoinRootEquivAdjoin F h).symm (AdjoinSimple.gen F α) = AdjoinRoot.root (minpoly F α) := by
  rw [AlgEquiv.symm_apply_eq, adjoinRootEquivAdjoin_apply_root]
/-
**IntermediateField.adjoin_root_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：adjoin_root_eq_top (p : K[X]) [Fact (Irreducible p)] : K⟮AdjoinRoot.root p
⟯ = ⊤
参数：p : K[X]；Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.eq_adjoin_of_eq_algebra_adjoin`：eq_adjoin_of_eq_algebr
a_adjoin (K : IntermediateField F E) (h : K.toSubalgebra = Algebra.adjoin F S) :
 K = adjoin F S
· 使用定理 `AdjoinRoot.adjoinRoot_eq_top`：adjoinRoot_eq_top : Algebra.adjoin R ({roo
t f} : Set (AdjoinRoot f)) = ⊤
-/
theorem adjoin_root_eq_top (p : K[X]) [Fact (Irreducible p)] : K⟮AdjoinRoot.root p⟯ = ⊤ :=
  (eq_adjoin_of_eq_algebra_adjoin K _ ⊤ (AdjoinRoot.adjoinRoot_eq_top (f := p)).symm).symm

section PowerBasis

variable {L : Type*} [Field L] [Algebra K L]

/-- The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
/-
**IntermediateField.powerBasisAux** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：powerBasisAux {x : L} (hx : IsIntegral K x) : Basis (Fin (minpoly K x).nat
Degree) K K⟮x⟯
参数：hx : IsIntegral K x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`.
-/
noncomputable def powerBasisAux {x : L} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K K⟮x⟯ :=
  (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).basis
    |>.map (adjoinRootEquivAdjoin K hx).toLinearEquiv
    |>.reindex (finCongr rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps]
/-
**IntermediateField.adjoin.powerBasis** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateFie
ld.adjoin`。
形式化陈述：{K : Type u} →   [inst : Field K] →     {L : Type u_3} → [inst_1 : Field L
] → [inst_2 : Algebra K L] → {x : L} → IsIntegral K x → PowerBasis K ↥K⟮x⟯
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`.
-/
noncomputable def adjoin.powerBasis {x : L} (hx : IsIntegral K x) : PowerBasis K K⟮x⟯ where
  gen := AdjoinSimple.gen K x
  dim := (minpoly K x).natDegree
  basis := powerBasisAux hx
  basis_eq_pow i := by
    rw [powerBasisAux, Basis.reindex_apply, Basis.map_apply, PowerBasis.basis_eq_pow,
      finCongr_symm, finCongr_apply, Fin.cast_eq_self, AlgEquiv.toLinearEquiv_apply,
      map_pow, AdjoinRoot.powerBasis_gen, adjoinRootEquivAdjoin_apply_root]
/-
**IntermediateField.adjoin.finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField.adjoin`。
形式化陈述：∀ {K : Type u} [inst : Field K] {L : Type u_3} [inst_1 : Field L] [inst_2 
: Algebra K L] {x : L},   IsIntegral K x → FiniteDimensional K ↥K⟮x⟯
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerBasis.finite`：finite (pb : PowerBasis R S) : Module.Finite R S
-/
theorem adjoin.finiteDimensional {x : L} (hx : IsIntegral K x) : FiniteDimensional K K⟮x⟯ :=
  (adjoin.powerBasis hx).finite
/-
**IntermediateField.isAlgebraic_adjoin_simple** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：isAlgebraic_adjoin_simple {x : L} (hx : IsIntegral K x) : Algebra.IsAlgebr
aic K K⟮x⟯
参数：hx : IsIntegral K x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem isAlgebraic_adjoin_simple {x : L} (hx : IsIntegral K x) : Algebra.IsAlgebraic K K⟮x⟯ :=
  have := adjoin.finiteDimensional hx; Algebra.IsAlgebraic.of_finite K K⟮x⟯

/-- If `x` is an algebraic element of field `K`, then its minimal polynomial has degree
`[K(x) : K]`. -/
@[stacks 09GN]
/-
**IntermediateField.adjoin.finrank** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField.
adjoin`。
形式化陈述：∀ {K : Type u} [inst : Field K] {L : Type u_3} [inst_1 : Field L] [inst_2 
: Algebra K L] {x : L},   IsIntegral K x → Module.finrank K ↥K⟮x⟯ = (minpoly K x
).natDegree
参数：minpoly K x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerBasis.finrank`：finrank [StrongRankCondition R] (pb : PowerBasis R S
) : Module.finrank R S = pb.dim
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If `x` is an algebraic element of field `K`, then its minimal polynomial has deg
ree
`[K(x) : K]`.
-/
theorem adjoin.finrank {x : L} (hx : IsIntegral K x) :
    Module.finrank K K⟮x⟯ = (minpoly K x).natDegree := by
  rw [PowerBasis.finrank (adjoin.powerBasis hx :)]
  rfl

/-- If `K / E / F` is a field extension tower, `S ⊂ K` is such that `F(S) = K`,
then `E(S) = K`. -/
/-
**IntermediateField.adjoin_eq_top_of_adjoin_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `In
termediateField`。
形式化陈述：adjoin_eq_top_of_adjoin_eq_top [Algebra E K] [IsScalarTower F E K] {S : Se
t K} (hprim : adjoin F S = ⊤) : adjoin E S = ⊤
参数：hprim : adjoin F S = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.restrictScalars_injective`：restrictScalars_injective :
 Function.Injective (restrictScalars K : IntermediateField L' L -> IntermediateF
ield K L)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.restrictScalars_top`：restrictScalars_top : (⊤ : Interm
ediateField F E).restrictScalars K = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `IntermediateField.coe_restrictScalars`：coe_restrictScalars {E : Intermed
iateField L' L} : (restrictScalars K E : Set L) = (E : Set L)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `K / E / F` is a field extension tower, `S ⊂ K` is such that `F(S) = K`,
then `E(S) = K`.
-/
theorem adjoin_eq_top_of_adjoin_eq_top [Algebra E K] [IsScalarTower F E K]
    {S : Set K} (hprim : adjoin F S = ⊤) : adjoin E S = ⊤ :=
  restrictScalars_injective F <| by
    rw [restrictScalars_top, ← top_le_iff, ← hprim, adjoin_le_iff,
      coe_restrictScalars, ← adjoin_le_iff]

/-- If `E / F` is a finite extension such that `E = F(α)`, then for any intermediate field `K`, the
`F` adjoin the coefficients of `minpoly K α` is equal to `K` itself. -/
/-
**IntermediateField.adjoin_minpoly_coeff_of_exists_primitive_element** 是 Mathlib
 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：adjoin_minpoly_coeff_of_exists_primitive_element [FiniteDimensional F E] (
hprim : adjoin F {α} = ⊤) (K : IntermediateField F E) : adjoin F ((minpoly K α).
map (algebraMap K E)).coeffs = K
参数：hprim : adjoin F {α} = ⊤；K : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Polynomial.mem_coeffs_iff`：mem_coeffs_iff {p : R[X]} {c : R} : c in p.co
effs ↔ exists n in p.support, c = p.coeff n
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Polynomial.map_toSubring`：map_toSubring : (p.toSubring T hp).map (Subrin
g.subtype T) = p
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IntermediateField.finrank_top'`：∀ {F : Type u_1} [inst : Field F] {E : T
ype u_2} [inst_1 : Field E] [inst_2 : Algebra F E],   Module.finrank F ↥⊤ = Modu
le.finrank F E
· 使用定理 `IntermediateField.adjoin_eq_top_of_adjoin_eq_top`：adjoin_eq_top_of_adjoi
n_eq_top [Algebra E K] [IsScalarTower F E K] {S : Set K} (hprim : adjoin F S = ⊤
) : adjoin E S = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IntermediateField.eq_of_le_of_finrank_le'`：eq_of_le_of_finrank_le' [Fini
teDimensional F L] (h_le : F <= E) (h_finrank : finrank F L <= finrank E L) : F 
= E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Polynomial.natDegree_toSubring`：natDegree_toSubring : (toSubring p T hp)
.natDegree = p.natDegree
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If `E / F` is a finite extension such that `E = F(α)`, then for any intermediate
 field `K`, the
`F` adjoin the coefficients of `minpoly K α` is equal to `K` itself.
-/
theorem adjoin_minpoly_coeff_of_exists_primitive_element
    [FiniteDimensional F E] (hprim : adjoin F {α} = ⊤) (K : IntermediateField F E) :
    adjoin F ((minpoly K α).map (algebraMap K E)).coeffs = K := by
  set g := (minpoly K α).map (algebraMap K E)
  set K' : IntermediateField F E := adjoin F g.coeffs
  have hsub : K' ≤ K := by
    refine adjoin_le_iff.mpr fun x ↦ ?_
    rw [Finset.mem_coe, mem_coeffs_iff]
    rintro ⟨n, -, rfl⟩
    rw [coeff_map]
    apply Subtype.mem
  have dvd_g : minpoly K' α ∣ g.toSubring K'.toSubring (subset_adjoin F _) := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_eq_eval_map]
    erw [g.map_toSubring K'.toSubring]
    rw [eval_map_algebraMap]
    exact minpoly.aeval K α
  have finrank_eq : ∀ K : IntermediateField F E, finrank K E = natDegree (minpoly K α) := by
    intro K
    have := adjoin.finrank (.of_finite K α)
    rw [adjoin_eq_top_of_adjoin_eq_top F hprim] at this
    simp_all
  refine eq_of_le_of_finrank_le' hsub ?_
  simp_rw [finrank_eq]
  convert!
    natDegree_le_of_dvd dvd_g
      ((g.monic_toSubring _ _).mpr <| (minpoly.monic <| .of_finite K α).map _).ne_zero using 1
  rw [natDegree_toSubring, natDegree_map]
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite F (⊥ : IntermediateField F E) := Subalgebra.finite_bot

variable {F} in
/-- If `E / F` is an infinite algebraic extension, then there exists an intermediate field
`L / F` with arbitrarily large finite extension degree. -/
/-
**IntermediateField.exists_lt_finrank_of_infinite_dimensional** 是 Mathlib 中的一个定理
，位于命名空间 `IntermediateField`。
形式化陈述：exists_lt_finrank_of_infinite_dimensional [Algebra.IsAlgebraic F E] (hnfd 
: ¬ FiniteDimensional F E) (n : Nat) : exists L : IntermediateField F E, FiniteD
imensional F L ∧ n < finrank F L
参数：hnfd : ¬ FiniteDimensional F E；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IntermediateField.instFiniteSubtypeMemBot`：∀ (F : Type u_1) [inst : Fiel
d F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.Finite F ↥
⊥
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IntermediateField.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le [hfin :
 FiniteDimensional K E] (h_le : F <= E) (h_finrank : finrank K E <= finrank K F)
 : F = E
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `E / F` is an infinite algebraic extension, then there exists an intermediate
 field
`L / F` with arbitrarily large finite extension degree.
-/
theorem exists_lt_finrank_of_infinite_dimensional
    [Algebra.IsAlgebraic F E] (hnfd : ¬ FiniteDimensional F E) (n : ℕ) :
    ∃ L : IntermediateField F E, FiniteDimensional F L ∧ n < finrank F L := by
  induction n with
  | zero => exact ⟨⊥, Subalgebra.finite_bot, finrank_pos⟩
  | succ n ih =>
    obtain ⟨L, fin, hn⟩ := ih
    obtain ⟨x, hx⟩ : ∃ x : E, x ∉ L := by
      contrapose! hnfd
      rw [show L = ⊤ from eq_top_iff.2 fun x _ ↦ hnfd x] at fin
      exact topEquiv.toLinearEquiv.finiteDimensional
    let L' := L ⊔ F⟮x⟯
    have := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
    refine ⟨L', inferInstance, by_contra fun h ↦ ?_⟩
    have h1 : L = L' := eq_of_le_of_finrank_le le_sup_left ((not_lt.1 h).trans hn)
    have h2 : F⟮x⟯ ≤ L' := le_sup_right
    exact hx <| (h1.symm ▸ h2) <| mem_adjoin_simple_self F x

/-- If `x : L` is an integral element in a field extension `L` over `K`, then the degree of the
  minimal polynomial of `x` over `K` divides `[L : K]`. -/
/-
**IntermediateField._root_.minpoly.degree_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x : L` is an integral element in a field extension `L` over `K`, then the de
gree of the
  minimal polynomial of `x` over `K` divides `[L : K]`.
-/
theorem _root_.minpoly.degree_dvd {x : L} (hx : IsIntegral K x) :
    (minpoly K x).natDegree ∣ finrank K L := by
  rw [dvd_iff_exists_eq_mul_left, ← IntermediateField.adjoin.finrank hx]
  use finrank K⟮x⟯ L
  rw [mul_comm, finrank_mul_finrank]
/-
**IntermediateField._root_.Polynomial.Irreducible.natDegree_dvd_finrank** 是 Math
lib 中的一个定理，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.Irreducible.natDegree_dvd_finrank {f : K[X]} (hi : Irreducible f)
    (hs : (f.map (algebraMap K L)).Splits) : f.natDegree ∣ finrank K L := by
  have := hi.degree_pos.ne'
  rw [← f.degree_map (algebraMap K L)] at this
  obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero this
  rw [eval_map_algebraMap] at hx
  have key := minpoly.Irreducible.eq_minpoly hi hx
  replace hi := hi.ne_zero
  rw [key, natDegree_C_mul (leadingCoeff_ne_zero.mpr hi)]
  apply minpoly.degree_dvd
  rw [← minpoly.ne_zero_iff]
  contrapose hi
  rwa [hi, mul_zero] at key
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsAlgebraic K (⊥ : IntermediateField K L) where
  isAlgebraic := by
    intro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := hx
    exact isAlgebraic_algebraMap c
/-
**IntermediateField.** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsAlgebraic (⊤ : IntermediateField K L) L where
  isAlgebraic := by
    intro x
    let xt : (⊤ : IntermediateField K L) := ⟨x, mem_top⟩
    exact isAlgebraic_algebraMap xt

-- TODO: generalize to `Sort`
/-- A compositum of algebraic extensions is algebraic -/
/-
**IntermediateField.isAlgebraic_iSup** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：isAlgebraic_iSup {ι : Type*} {t : ι -> IntermediateField K L} (h : forall 
i, Algebra.IsAlgebraic K (t i)) : Algebra.IsAlgebraic K (⨆ i, t i : Intermediate
Field K L)
参数：h : forall i, Algebra.IsAlgebraic K (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_finset_of_mem_supr'`：exists_finset_of_mem_supr'
 {ι : Type*} {f : ι -> IntermediateField F E} {x : E} (hx : x in ⨆ i, f i) : exi
sts s : Finset (Σ i, f i), x in ⨆ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.isAlgebraic_iff`：isAlgebraic_iff {x : S} : IsAlgebraic
 K x ↔ IsAlgebraic K (x : L)
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.isIntegral_iff`：isIntegral_iff {x : S} : IsIntegral K 
x ↔ IsIntegral K (x : L)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `IsAlgebraic.of_finite`：IsAlgebraic.of_finite (e : A) [Module.Finite R A]
 : IsAlgebraic R e
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
A compositum of algebraic extensions is algebraic
-/
theorem isAlgebraic_iSup {ι : Type*} {t : ι → IntermediateField K L}
    (h : ∀ i, Algebra.IsAlgebraic K (t i)) :
    Algebra.IsAlgebraic K (⨆ i, t i : IntermediateField K L) := by
  constructor
  rintro ⟨x, hx⟩
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr' hx
  rw [isAlgebraic_iff, Subtype.coe_mk, ← Subtype.coe_mk (p := (· ∈ _)) x hx, ← isAlgebraic_iff]
  have : ∀ i : Σ i, t i, FiniteDimensional K K⟮(i.2 : L)⟯ := fun ⟨i, x⟩ ↦
    adjoin.finiteDimensional (isIntegral_iff.1 (Algebra.IsIntegral.isIntegral x))
  apply IsAlgebraic.of_finite
/-
**IntermediateField.isAlgebraic_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：isAlgebraic_adjoin {S : Set L} (hS : forall x in S, IsIntegral K x) : Alge
bra.IsAlgebraic K (adjoin K S)
参数：hS : forall x in S, IsIntegral K x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.biSup_adjoin_simple`：biSup_adjoin_simple : ⨆ x in S, F
⟮x⟯ = adjoin F S
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `IntermediateField.isAlgebraic_iSup`：isAlgebraic_iSup {ι : Type*} {t : ι 
-> IntermediateField K L} (h : forall i, Algebra.IsAlgebraic K (t i)) : Algebra.
IsAlgebraic K (⨆ i, t i …
· 使用定理 `IntermediateField.isAlgebraic_adjoin_simple`：isAlgebraic_adjoin_simple {
x : L} (hx : IsIntegral K x) : Algebra.IsAlgebraic K K⟮x⟯
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isAlgebraic_adjoin {S : Set L} (hS : ∀ x ∈ S, IsIntegral K x) :
    Algebra.IsAlgebraic K (adjoin K S) := by
  rw [← biSup_adjoin_simple, ← iSup_subtype'']
  exact isAlgebraic_iSup fun x ↦ isAlgebraic_adjoin_simple (hS x x.2)

/-- If `L / K` is a field extension, `S` is a finite subset of `L`, such that every element of `S`
is integral (= algebraic) over `K`, then `K(S) / K` is a finite extension.
A direct corollary of `finiteDimensional_iSup_of_finite`. -/
/-
**IntermediateField.finiteDimensional_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Intermed
iateField`。
形式化陈述：finiteDimensional_adjoin {S : Set L} [Finite S] (hS : forall x in S, IsInt
egral K x) : FiniteDimensional K (adjoin K S)
参数：hS : forall x in S, IsIntegral K x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.biSup_adjoin_simple`：biSup_adjoin_simple : ⨆ x in S, F
⟮x⟯ = adjoin F S
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If `L / K` is a field extension, `S` is a finite subset of `L`, such that every 
element of `S`
is integral (= algebraic) over `K`, then `K(S) / K` is a finite extension.
A direct corollary of `finiteDimensional_iSup_of_finite`.
-/
theorem finiteDimensional_adjoin {S : Set L} [Finite S] (hS : ∀ x ∈ S, IsIntegral K x) :
    FiniteDimensional K (adjoin K S) := by
  rw [← biSup_adjoin_simple, ← iSup_subtype'']
  have (x : S) := adjoin.finiteDimensional (hS x.1 x.2)
  exact finiteDimensional_iSup_of_finite

end PowerBasis

/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
/-
**IntermediateField.algHomAdjoinIntegralEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Interme
diateField`。
形式化陈述：algHomAdjoinIntegralEquiv (h : IsIntegral F α) : (F⟮α⟯ ->ₐ[F] K) ≃ { x // 
x in (minpoly F α).aroots K }
参数：h : IsIntegral F α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`.
-/
noncomputable def algHomAdjoinIntegralEquiv (h : IsIntegral F α) :
    (F⟮α⟯ →ₐ[F] K) ≃ { x // x ∈ (minpoly F α).aroots K } :=
  (adjoin.powerBasis h).liftEquiv'.trans
    ((Equiv.refl _).subtypeEquiv fun x => by
      rw [adjoin.powerBasis_gen, minpoly_gen, Equiv.refl_apply])
/-
**IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen** 是 Mathlib 中的一个引理，
位于命名空间 `IntermediateField`。
形式化陈述：algHomAdjoinIntegralEquiv_symm_apply_gen (h : IsIntegral F α) (x : { x // 
x in (minpoly F α).aroots K }) : (algHomAdjoinIntegralEquiv F h).symm x (AdjoinS
imple.gen F α) = x
参数：h : IsIntegral F α；x : { x // x in (minpoly F α).aroots K }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `PowerBasis.lift_gen`：lift_gen (pb : PowerBasis A S) (y : S') (hy : aeval
 y (minpoly A pb.gen) = 0) : pb.lift y hy pb.gen = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin.powerBasis_gen`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
· 使用定理 `IntermediateField.minpoly_gen`：minpoly_gen (α : E) : minpoly F (AdjoinSi
mple.gen F α) = minpoly F α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_aroots`：mem_aroots [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔
 p != 0 ∧ a…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma algHomAdjoinIntegralEquiv_symm_apply_gen (h : IsIntegral F α)
    (x : { x // x ∈ (minpoly F α).aroots K }) :
    (algHomAdjoinIntegralEquiv F h).symm x (AdjoinSimple.gen F α) = x :=
  (adjoin.powerBasis h).lift_gen x.val <| by
    rw [adjoin.powerBasis_gen, minpoly_gen]; exact (mem_aroots.mp x.2).2

/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
@[instance_reducible]
/-
**IntermediateField.fintypeOfAlgHomAdjoinIntegral** 是 Mathlib 中的一个定义，位于命名空间 `Int
ermediateField`。
形式化陈述：fintypeOfAlgHomAdjoinIntegral (h : IsIntegral F α) : Fintype (F⟮α⟯ ->ₐ[F] 
K)
参数：h : IsIntegral F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K`
-/
noncomputable def fintypeOfAlgHomAdjoinIntegral (h : IsIntegral F α) : Fintype (F⟮α⟯ →ₐ[F] K) :=
  PowerBasis.AlgHom.fintype (adjoin.powerBasis h)
/-
**IntermediateField.card_algHom_adjoin_integral** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField`。
形式化陈述：card_algHom_adjoin_integral (h : IsIntegral F α) (h_sep : IsSeparable F α)
 (h_splits : ((minpoly F α).map (algebraMap F K)).Splits) : Nat.card (F⟮α⟯ ->ₐ[F
] K) = (minpoly F α).natDegree
参数：h : IsIntegral F α；h_sep : IsSeparable F α；h_splits : ((minpoly F α).map (alg
ebraMap F K)).Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgHom.card_of_powerBasis`：AlgHom.card_of_powerBasis (pb : PowerBasis K 
S) (h_sep : IsSeparable K pb.gen) (h_splits : ((minpoly K pb.gen).map (algebraMa
p K L)).Splits)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IntermediateField.adjoin.powerBasis_gen`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
· 使用定理 `IntermediateField.minpoly_gen`：minpoly_gen (α : E) : minpoly F (AdjoinSi
mple.gen F α) = minpoly F α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IntermediateField.adjoin.powerBasis_dim`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_algHom_adjoin_integral (h : IsIntegral F α) (h_sep : IsSeparable F α)
    (h_splits : ((minpoly F α).map (algebraMap F K)).Splits) :
    Nat.card (F⟮α⟯ →ₐ[F] K) = (minpoly F α).natDegree := by
  let _ : Fintype (F⟮α⟯ →ₐ[F] K) := fintypeOfAlgHomAdjoinIntegral F h
  rw [Nat.card_eq_fintype_card, AlgHom.card_of_powerBasis] <;>
    simp only [IsSeparable, adjoin.powerBasis_dim, adjoin.powerBasis_gen, minpoly_gen, h_splits]
  exact h_sep

-- Apparently `K⟮root f⟯ →+* K⟮root f⟯` is expensive to unify during instance synthesis.
open Module AdjoinRoot in
/-- Let `f, g` be monic polynomials over `K`. If `f` is irreducible, and `g(x) - α` is irreducible
in `K⟮α⟯` with `α` a root of `f`, then `f(g(x))` is irreducible. -/
/-
**IntermediateField._root_.Polynomial.irreducible_comp** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f, g` be monic polynomials over `K`. If `f` is irreducible, and `g(x) - α` 
is irreducible
in `K⟮α⟯` with `α` a root of `f`, then `f(g(x))` is irreducible.
-/
theorem _root_.Polynomial.irreducible_comp {f g : K[X]} (hfm : f.Monic) (hgm : g.Monic)
    (hf : Irreducible f)
    (hg : ∀ (E : Type u) [Field E] [Algebra K E] (x : E) (_ : minpoly K x = f),
      Irreducible (g.map (algebraMap _ _) - C (AdjoinSimple.gen K x))) :
    Irreducible (f.comp g) := by
  have hf' : natDegree f ≠ 0 :=
    fun e ↦ not_irreducible_C (f.coeff 0) (eq_C_of_natDegree_eq_zero e ▸ hf)
  have hg' : natDegree g ≠ 0 := by
    have := Fact.mk hf
    intro e
    apply not_irreducible_C ((g.map (algebraMap _ _)).coeff 0 - AdjoinSimple.gen K (root f))
    -- Needed to specialize `map_sub` to avoid a timeout https://github.com/leanprover-community/mathlib4/pull/8386
    rw [RingHom.map_sub, coeff_map, ← map_C, ← eq_C_of_natDegree_eq_zero e]
    apply hg (AdjoinRoot f)
    rw [AdjoinRoot.minpoly_root hf.ne_zero, hfm, inv_one, map_one, mul_one]
  have H₁ : f.comp g ≠ 0 := fun h ↦ by simpa [hf', hg', natDegree_comp] using congr_arg natDegree h
  have H₂ : ¬ IsUnit (f.comp g) := fun h ↦
    by simpa [hf', hg', natDegree_comp] using natDegree_eq_zero_of_isUnit h
  have ⟨p, hp₁, hp₂⟩ := WfDvdMonoid.exists_irreducible_factor H₂ H₁
  suffices natDegree p = natDegree f * natDegree g from (associated_of_dvd_of_natDegree_le hp₂ H₁
    (this.trans natDegree_comp.symm).ge).irreducible hp₁
  have := Fact.mk hp₁
  let Kx := AdjoinRoot p
  let := (AdjoinRoot.powerBasis hp₁.ne_zero).finite
  have key₁ : f = minpoly K (aeval (root p) g) := by
    refine minpoly.eq_of_irreducible_of_monic hf ?_ hfm
    rw [← aeval_comp]
    exact aeval_eq_zero_of_dvd_aeval_eq_zero hp₂ (AdjoinRoot.eval₂_root p)
  have key₁' : finrank K K⟮aeval (root p) g⟯ = natDegree f := by
    rw [adjoin.finrank, ← key₁]
    exact IsIntegral.of_finite _ _
  have key₂ : g.map (algebraMap _ _) - C (AdjoinSimple.gen K (aeval (root p) g)) =
      minpoly K⟮aeval (root p) g⟯ (root p) :=
    minpoly.eq_of_irreducible_of_monic (hg _ _ key₁.symm) (by simp [AdjoinSimple.gen])
      (Monic.sub_of_left (hgm.map _) (degree_lt_degree (by simpa [Nat.pos_iff_ne_zero] using hg')))
  have key₂' : finrank K⟮aeval (root p) g⟯ Kx = natDegree g := by
    trans natDegree (minpoly K⟮aeval (root p) g⟯ (root p))
    · have : K⟮aeval (root p) g⟯⟮root p⟯ = ⊤ := by
        apply restrictScalars_injective K
        rw [restrictScalars_top, adjoin_adjoin_left, Set.union_comm, ← adjoin_adjoin_left,
          adjoin_root_eq_top p, restrictScalars_adjoin]
        simp
      rw [← finrank_top', ← this, adjoin.finrank]
      exact IsIntegral.of_finite _ _
    · simp [← key₂]
  have := Module.finrank_mul_finrank K K⟮aeval (root p) g⟯ Kx
  rwa [key₁', key₂', (AdjoinRoot.powerBasis hp₁.ne_zero).finrank, powerBasis_dim, eq_comm] at this

end AdjoinIntegralElement

end IntermediateField

namespace minpoly
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open AlgEquiv IntermediateField

/-- If `y : L` is a root of `minpoly K x`, then `minpoly K y = minpoly K x`. -/
/-
**minpoly.eq_of_root** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：eq_of_root {x y : L} (hx : IsAlgebraic K x) (h_ev : Polynomial.aeval y (mi
npoly K x) = 0) : minpoly K y = minpoly K x
参数：hx : IsAlgebraic K x；h_ev : Polynomial.aeval y (minpoly K x) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `minpoly.eq_iff_aeval_minpoly_eq_zero`：eq_iff_aeval_minpoly_eq_zero [IsDo
main B] {C} [Ring C] [Algebra A C] [Nontrivial C] {b : B} (h : IsIntegral A b) {
c : C} : minpoly A b = min…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x

--- 原说明 ---
If `y : L` is a root of `minpoly K x`, then `minpoly K y = minpoly K x`.
-/
theorem eq_of_root {x y : L} (hx : IsAlgebraic K x)
    (h_ev : Polynomial.aeval y (minpoly K x) = 0) : minpoly K y = minpoly K x :=
  ((eq_iff_aeval_minpoly_eq_zero hx.isIntegral).mpr h_ev).symm

/-- The canonical `algEquiv` between `K⟮x⟯` and `K⟮y⟯`, sending `x` to `y`, where `x` and `y` have
  the same minimal polynomial over `K`. -/
/-
**minpoly.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `minpoly`。
形式化陈述：algEquiv {x y : L} (hx : IsAlgebraic K x) (h_mp : minpoly K x = minpoly K 
y) : K⟮x⟯ ≃ₐ[K] K⟮y⟯
参数：hx : IsAlgebraic K x；h_mp : minpoly K x = minpoly K y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `algEquiv` between `K⟮x⟯` and `K⟮y⟯`, sending `x` to `y`, where `x
` and `y` have
  the same minimal polynomial over `K`.
-/
noncomputable def algEquiv {x y : L} (hx : IsAlgebraic K x)
    (h_mp : minpoly K x = minpoly K y) : K⟮x⟯ ≃ₐ[K] K⟮y⟯ := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  exact (adjoinRootEquivAdjoin K hx.isIntegral).symm.trans <|
    (AdjoinRoot.algEquivOfEq _ _ _ h_mp).trans (adjoinRootEquivAdjoin K hy.isIntegral)

/-- `minpoly.algEquiv` sends the generator of `K⟮x⟯` to the generator of `K⟮y⟯`. -/
/-
**minpoly.algEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `minpoly`。
形式化陈述：algEquiv_apply {x y : L} (hx : IsAlgebraic K x) (h_mp : minpoly K x = minp
oly K y) : algEquiv hx h_mp (AdjoinSimple.gen K x) = AdjoinSimple.gen K y
参数：hx : IsAlgebraic K x；h_mp : minpoly K x = minpoly K y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.algEquiv.eq_1`：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] 
[inst_1 : Field L] [inst_2 : Algebra K L] {x y : L}   (hx : IsAlgebraic K x) (h_
mp : minpol…
· 使用定理 `AlgEquiv.trans_apply`：trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) 
(x : A₁) : (e₁.trans e₂) x = e₂ (e₁ x)
· 使用定理 `IntermediateField.adjoinRootEquivAdjoin_apply_root`：adjoinRootEquivAdjoi
n_apply_root (h : IsIntegral F α) : adjoinRootEquivAdjoin F h (AdjoinRoot.root (
minpoly F α)) = AdjoinSimple.gen F α
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用引理 `AdjoinRoot.algEquivOfEq_root`：algEquivOfEq_root (f g : S[X]) (hfg) : alg
EquivOfEq R f g hfg (root f) = root g

--- 原说明 ---
`minpoly.algEquiv` sends the generator of `K⟮x⟯` to the generator of `K⟮y⟯`.
-/
theorem algEquiv_apply {x y : L} (hx : IsAlgebraic K x) (h_mp : minpoly K x = minpoly K y) :
    algEquiv hx h_mp (AdjoinSimple.gen K x) = AdjoinSimple.gen K y := by
  have hy : IsAlgebraic K y := ⟨minpoly K x, ne_zero hx.isIntegral, (h_mp ▸ aeval _ _)⟩
  rw [algEquiv, trans_apply, ← adjoinRootEquivAdjoin_apply_root K hx.isIntegral,
    symm_apply_apply, trans_apply, AdjoinRoot.algEquivOfEq_root,
    adjoinRootEquivAdjoin_apply_root K hy.isIntegral]

end minpoly

namespace PowerBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open IntermediateField

/-- `pb.equivAdjoinSimple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
/-
**PowerBasis.equivAdjoinSimple** 是 Mathlib 中的一个定义，位于命名空间 `PowerBasis`。
形式化陈述：equivAdjoinSimple (pb : PowerBasis K L) : K⟮pb.gen⟯ ≃ₐ[K] L
参数：pb : PowerBasis K L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pb.equivAdjoinSimple` is the equivalence between `K⟮pb.gen⟯` and `L` itself.
-/
noncomputable def equivAdjoinSimple (pb : PowerBasis K L) : K⟮pb.gen⟯ ≃ₐ[K] L :=
  (adjoin.powerBasis pb.isIntegral_gen).equivOfMinpoly pb <| by
    rw [adjoin.powerBasis_gen, minpoly_gen]

@[simp]
/-
**PowerBasis.equivAdjoinSimple_aeval** 是 Mathlib 中的一个定理，位于命名空间 `PowerBasis`。
形式化陈述：equivAdjoinSimple_aeval (pb : PowerBasis K L) (f : K[X]) : pb.equivAdjoinS
imple (aeval (AdjoinSimple.gen K pb.gen) f) = aeval pb.gen f
参数：pb : PowerBasis K L；f : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerBasis.equivOfMinpoly_aeval`：equivOfMinpoly_aeval (pb : PowerBasis A
 S) (pb' : PowerBasis A S') (h : minpoly A pb.gen = minpoly A pb'.gen) (f : A[X]
) : pb.equivOfMinpoly…
-/
theorem equivAdjoinSimple_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple (aeval (AdjoinSimple.gen K pb.gen) f) = aeval pb.gen f :=
  equivOfMinpoly_aeval _ pb _ f

@[simp]
/-
**PowerBasis.equivAdjoinSimple_gen** 是 Mathlib 中的一个定理，位于命名空间 `PowerBasis`。
形式化陈述：equivAdjoinSimple_gen (pb : PowerBasis K L) : pb.equivAdjoinSimple (Adjoin
Simple.gen K pb.gen) = pb.gen
参数：pb : PowerBasis K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerBasis.equivOfMinpoly_gen`：equivOfMinpoly_gen (pb : PowerBasis A S) 
(pb' : PowerBasis A S') (h : minpoly A pb.gen = minpoly A pb'.gen) : pb.equivOfM
inpoly pb' h pb.gen…
-/
theorem equivAdjoinSimple_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple (AdjoinSimple.gen K pb.gen) = pb.gen :=
  equivOfMinpoly_gen _ pb _

@[simp]
/-
**PowerBasis.equivAdjoinSimple_symm_aeval** 是 Mathlib 中的一个定理，位于命名空间 `PowerBasis`
。
形式化陈述：equivAdjoinSimple_symm_aeval (pb : PowerBasis K L) (f : K[X]) : pb.equivAd
joinSimple.symm (aeval pb.gen f) = aeval (AdjoinSimple.gen K pb.gen) f
参数：pb : PowerBasis K L；f : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerBasis.equivAdjoinSimple.eq_1`：∀ {K : Type u_1} {L : Type u_2} [inst
 : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (pb : PowerBasis K L),   p
b.equivAdjoinSimple = (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerBasis.equivOfMinpoly_symm`：equivOfMinpoly_symm (pb : PowerBasis A S
) (pb' : PowerBasis A S') (h : minpoly A pb.gen = minpoly A pb'.gen) : (pb.equiv
OfMinpoly pb' h).sym…
· 使用定理 `PowerBasis.equivOfMinpoly_aeval`：equivOfMinpoly_aeval (pb : PowerBasis A
 S) (pb' : PowerBasis A S') (h : minpoly A pb.gen = minpoly A pb'.gen) (f : A[X]
) : pb.equivOfMinpoly…
· 使用定理 `IntermediateField.adjoin.powerBasis_gen`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
-/
theorem equivAdjoinSimple_symm_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple.symm (aeval pb.gen f) = aeval (AdjoinSimple.gen K pb.gen) f := by
  rw [equivAdjoinSimple, equivOfMinpoly_symm, equivOfMinpoly_aeval, adjoin.powerBasis_gen]

@[simp]
/-
**PowerBasis.equivAdjoinSimple_symm_gen** 是 Mathlib 中的一个定理，位于命名空间 `PowerBasis`。
形式化陈述：equivAdjoinSimple_symm_gen (pb : PowerBasis K L) : pb.equivAdjoinSimple.sy
mm pb.gen = AdjoinSimple.gen K pb.gen
参数：pb : PowerBasis K L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerBasis.equivAdjoinSimple.eq_1`：∀ {K : Type u_1} {L : Type u_2} [inst
 : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] (pb : PowerBasis K L),   p
b.equivAdjoinSimple = (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerBasis.equivOfMinpoly_symm`：equivOfMinpoly_symm (pb : PowerBasis A S
) (pb' : PowerBasis A S') (h : minpoly A pb.gen = minpoly A pb'.gen) : (pb.equiv
OfMinpoly pb' h).sym…
· 使用定理 `PowerBasis.equivOfMinpoly_gen`：equivOfMinpoly_gen (pb : PowerBasis A S) 
(pb' : PowerBasis A S') (h : minpoly A pb.gen = minpoly A pb'.gen) : pb.equivOfM
inpoly pb' h pb.gen…
· 使用定理 `IntermediateField.adjoin.powerBasis_gen`：∀ {K : Type u} [inst : Field K]
 {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L} (hx : IsIntegr
al K x),   (IntermediateField…
-/
theorem equivAdjoinSimple_symm_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple.symm pb.gen = AdjoinSimple.gen K pb.gen := by
  rw [equivAdjoinSimple, equivOfMinpoly_symm, equivOfMinpoly_gen, adjoin.powerBasis_gen]

end PowerBasis

namespace IntermediateField

universe u v

open Cardinal

variable (F : Type u) [Field F]

/-
**IntermediateField.lift_cardinalMk_adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：lift_cardinalMk_adjoin_le {E : Type v} [Field E] [Algebra F E] (s : Set E)
 : Cardinal.lift.{u} #(adjoin F s) <= Cardinal.lift.{v} #F ⊔ Cardinal.lift.{u} #
s ⊔ ℵ₀
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin_toSubfield`：adjoin_toSubfield : (adjoin F S).to
Subfield = Subfield.closure (Set.range (algebraMap F E) union S)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用引理 `Subfield.cardinalMk_closure_le_max`：cardinalMk_closure_le_max : #(closur
e s) <= max #s ℵ₀
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.mk_union_le`：mk_union_le {α : Type u} (S T : Set α) : #(S union
 T : Set α) <= #S + #T
· 使用定理 `Cardinal.add_le_max`：add_le_max (a b : Cardinal) : a + b <= max (max a b
) ℵ₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem lift_cardinalMk_adjoin_le {E : Type v} [Field E] [Algebra F E] (s : Set E) :
    Cardinal.lift.{u} #(adjoin F s) ≤ Cardinal.lift.{v} #F ⊔ Cardinal.lift.{u} #s ⊔ ℵ₀ := by
  rw [show ↥(adjoin F s) = (adjoin F s).toSubfield from rfl, adjoin_toSubfield]
  apply (Cardinal.lift_le.mpr (Subfield.cardinalMk_closure_le_max _)).trans
  rw [lift_max, sup_le_iff, lift_aleph0]
  refine ⟨(Cardinal.lift_le.mpr ((mk_union_le _ _).trans <| add_le_max _ _)).trans ?_, le_sup_right⟩
  simp_rw [lift_max, lift_aleph0]
  grw [mk_range_le_lift]
/-
**IntermediateField.cardinalMk_adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：cardinalMk_adjoin_le {E : Type u} [Field E] [Algebra F E] (s : Set E) : #(
adjoin F s) <= #F ⊔ #s ⊔ ℵ₀
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IntermediateField.lift_cardinalMk_adjoin_le`：lift_cardinalMk_adjoin_le {
E : Type v} [Field E] [Algebra F E] (s : Set E) : Cardinal.lift.{u} #(adjoin F s
) <= Cardinal.lift.{v} #F ⊔ Cardi…
-/
theorem cardinalMk_adjoin_le {E : Type u} [Field E] [Algebra F E] (s : Set E) :
    #(adjoin F s) ≤ #F ⊔ #s ⊔ ℵ₀ := by
  simpa using lift_cardinalMk_adjoin_le F s

section AdjoinPair

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {x y : L}

/-
**IntermediateField.isAlgebraic_adjoin_pair** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：isAlgebraic_adjoin_pair (hx : IsIntegral K x) (hy : IsIntegral K y) : Alge
bra.IsAlgebraic K K⟮x, y⟯
参数：hx : IsIntegral K x；hy : IsIntegral K y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.isAlgebraic_adjoin`：isAlgebraic_adjoin {S : Set L} (hS
 : forall x in S, IsIntegral K x) : Algebra.IsAlgebraic K (adjoin K S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isAlgebraic_adjoin_pair (hx : IsIntegral K x) (hy : IsIntegral K y) :
    Algebra.IsAlgebraic K K⟮x, y⟯ := by
  apply IntermediateField.isAlgebraic_adjoin
  simp [hx, hy]
/-
**IntermediateField.finiteDimensional_adjoin_pair** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：finiteDimensional_adjoin_pair (hx : IsIntegral K x) (hy : IsIntegral K y) 
: FiniteDimensional K K⟮x, y⟯
参数：hx : IsIntegral K x；hy : IsIntegral K y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `IntermediateField.adjoin_union`：adjoin_union {S T : Set E} : adjoin F (S
 union T) = adjoin F S ⊔ adjoin F T
-/
theorem finiteDimensional_adjoin_pair (hx : IsIntegral K x) (hy : IsIntegral K y) :
    FiniteDimensional K K⟮x, y⟯ := by
  have := adjoin.finiteDimensional hx
  have := adjoin.finiteDimensional hy
  rw [← Set.singleton_union, adjoin_union]
  exact finiteDimensional_sup K⟮x⟯ K⟮y⟯

variable (K x y)
/-
**IntermediateField.mem_adjoin_pair_left** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：mem_adjoin_pair_left : x in K⟮x, y⟯
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem mem_adjoin_pair_left : x ∈ K⟮x, y⟯ := subset_adjoin K {x, y} (Set.mem_insert x {y})
/-
**IntermediateField.mem_adjoin_pair_right** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField`。
形式化陈述：mem_adjoin_pair_right : y in K⟮x, y⟯
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem mem_adjoin_pair_right : y ∈ K⟮x, y⟯ :=
  subset_adjoin K {x, y} (Set.mem_insert_of_mem x (Set.mem_singleton y))

/-- The first generator of an intermediate field of the form `K⟮x, y⟯`. -/
/-
**IntermediateField.AdjoinPair.gen** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first generator of an intermediate field of the form `K⟮x, y⟯`.
-/
def AdjoinPair.gen₁ : K⟮x, y⟯ := ⟨x, mem_adjoin_pair_left K x y⟩

/-- The second generator of an intermediate field of the form `K⟮x, y⟯`. -/
/-
**IntermediateField.AdjoinPair.gen** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second generator of an intermediate field of the form `K⟮x, y⟯`.
-/
def AdjoinPair.gen₂ : K⟮x, y⟯ := ⟨y, mem_adjoin_pair_right K x y⟩
/-
**IntermediateField.AdjoinPair.algebraMap_gen** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdjoinPair.algebraMap_gen₁ : (algebraMap (↥K⟮x, y⟯) L) (gen₁ K x y) = x := rfl
/-
**IntermediateField.AdjoinPair.algebraMap_gen** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AdjoinPair.algebraMap_gen₂ : (algebraMap (↥K⟮x, y⟯) L) (gen₂ K x y) = y := rfl

end AdjoinPair

end IntermediateField

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [CommSemiring R] (K : Type*) [Field K] [Algebra R K]
    (S : Type*) [Semiring S] [Algebra R S] [Module.Finite R S] :
    Finite (S →ₐ[R] K) :=
  .of_equiv _ (Algebra.TensorProduct.liftEquivRight _ K _ _).symm
