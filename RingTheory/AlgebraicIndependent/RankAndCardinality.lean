/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.MvRatFunc.Rank
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Cardinality of a transcendence basis

This file concerns the cardinality of a transcendence basis.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence basis, transcendence degree, transcendence

-/

public section

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u v w

open AlgebraicIndependent

open Cardinal

/-
**IsTranscendenceBasis.lift_cardinalMk_eq_max_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.lift_cardinalMk_eq_max_lift {F : Type u} {E : Type v}
 [CommRing F] [Nontrivial F] [CommRing E] [IsDomain E] [Algebra F E] {ι : Type w
} {x : ι -> E} [Nonempty ι] (hx : IsTranscendenceBasis F x) : lift.{max u w} #E 
= lift.{max v w} #F ⊔ lift.{max u v} #ι ⊔ ℵ₀
参数：hx : IsTranscendenceBasis F x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTranscendenceBasis.isAlgebraic`：IsTranscendenceBasis.isAlgebraic [Nont
rivial R] (hx : IsTranscendenceBasis R x) : Algebra.IsAlgebraic (adjoin R (range
 x)) A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.infinite_iff`：Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infini
te β
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `Algebra.IsAlgebraic.cardinalMk_le_max`：cardinalMk_le_max : #L <= max #R 
ℵ₀
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `MvPolynomial.cardinalMk_eq_max_lift`：cardinalMk_eq_max_lift [Nonempty σ]
 [Nontrivial R] : #(MvPolynomial σ R) = lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsTranscendenceBasis.lift_cardinalMk_eq_max_lift
    {F : Type u} {E : Type v} [CommRing F] [Nontrivial F] [CommRing E] [IsDomain E] [Algebra F E]
    {ι : Type w} {x : ι → E} [Nonempty ι] (hx : IsTranscendenceBasis F x) :
    lift.{max u w} #E = lift.{max v w} #F ⊔ lift.{max u v} #ι ⊔ ℵ₀ := by
  let K := Algebra.adjoin F (Set.range x)
  suffices #E = #K by simp [K, this, ← lift_mk_eq'.2 ⟨hx.1.aevalEquiv.toEquiv⟩]
  have : Algebra.IsAlgebraic K E := hx.isAlgebraic
  refine le_antisymm ?_ (mk_le_of_injective Subtype.val_injective)
  have : Infinite K := hx.1.aevalEquiv.infinite_iff.1 inferInstance
  simpa only [sup_eq_left.2 (aleph0_le_mk K)] using Algebra.IsAlgebraic.cardinalMk_le_max K E
/-
**IsTranscendenceBasis.lift_rank_eq_max_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTranscendenceBasis.lift_rank_eq_max_lift {F : Type u} {E : Type v} [Fiel
d F] [Field E] [Algebra F E] {ι : Type w} {x : ι -> E} [Nonempty ι] (hx : IsTran
scendenceBasis F x) : lift.{max u w} (Module.rank F E) = lift.{max v w} #F ⊔ lif
t.{max u v} #ι ⊔ ℵ₀
参数：hx : IsTranscendenceBasis F x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTranscendenceBasis.isAlgebraic_field`：IsTranscendenceBasis.isAlgebraic
_field {F E : Type*} {x : ι -> E} [Field F] [Field E] [Algebra F E] (hx : IsTran
scendenceBasis F x) : Algebr…
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
· 使用定理 `Cardinal.lift_mul`：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = li
ft.{v} a * lift.{v} b
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvRatFunc.rank_eq_max_lift`：MvRatFunc.rank_eq_max_lift {σ : Type u} {F :
 Type v} [Field F] [Nonempty σ] : Module.rank F (FractionRing (MvPolynomial σ F)
) = lift.{u} #F …
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.mul_eq_left`：mul_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) (hb' : b != 0) : a * b = a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `rank_le_card`：rank_le_card : Module.rank R M <= #M
· 使用定理 `Algebra.IsAlgebraic.cardinalMk_le_max`：cardinalMk_le_max : #L <= max #R 
ℵ₀
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
（共 43 条，此处仅展示前 30 条）
-/
theorem IsTranscendenceBasis.lift_rank_eq_max_lift
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {ι : Type w} {x : ι → E} [Nonempty ι] (hx : IsTranscendenceBasis F x) :
    lift.{max u w} (Module.rank F E) = lift.{max v w} #F ⊔ lift.{max u v} #ι ⊔ ℵ₀ := by
  let K := IntermediateField.adjoin F (Set.range x)
  have : Algebra.IsAlgebraic K E := hx.isAlgebraic_field
  rw [← rank_mul_rank F K E, lift_mul, ← hx.1.aevalEquivField.toLinearEquiv.lift_rank_eq,
    MvRatFunc.rank_eq_max_lift, lift_max, lift_max, lift_lift, lift_lift, lift_aleph0]
  refine mul_eq_left le_sup_right ((lift_le.2 ((rank_le_card K E).trans
    (Algebra.IsAlgebraic.cardinalMk_le_max K E))).trans_eq ?_) (by simp [rank_pos.ne'])
  simp [K, ← lift_mk_eq'.2 ⟨hx.1.aevalEquivField.toEquiv⟩]
/-
**Algebra.Transcendental.rank_eq_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.Transcendental.rank_eq_cardinalMk (F : Type u) (E : Type v) [Field
 F] [Field E] [Algebra F E] [Algebra.Transcendental F E] : Module.rank F E = #E
参数：F : Type u；E : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isTranscendenceBasis'`：exists_isTranscendenceBasis' [FaithfulSMul
 R A] : exists (ι : Type w) (x : ι -> A), IsTranscendenceBasis R x
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
· 使用定理 `IsTranscendenceBasis.nonempty_iff_transcendental`：IsTranscendenceBasis.n
onempty_iff_transcendental [Nontrivial R] (hx : IsTranscendenceBasis R x) : None
mpty ι ↔ Algebra.Transcendental R A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTranscendenceBasis.lift_cardinalMk_eq_max_lift`：IsTranscendenceBasis.l
ift_cardinalMk_eq_max_lift {F : Type u} {E : Type v} [CommRing F] [Nontrivial F]
 [CommRing E] [IsDomain E] [Algebra F …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsTranscendenceBasis.lift_rank_eq_max_lift`：IsTranscendenceBasis.lift_ra
nk_eq_max_lift {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] {ι : 
Type w} {x : ι -> E} [Nonempty ι…
-/
theorem Algebra.Transcendental.rank_eq_cardinalMk
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [Algebra.Transcendental F E] :
    Module.rank F E = #E := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F E
  have := hx.nonempty_iff_transcendental.2 ‹_›
  simpa [← hx.lift_cardinalMk_eq_max_lift] using hx.lift_rank_eq_max_lift
/-
**IntermediateField.rank_sup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.rank_sup_le {F : Type u} {E : Type v} [Field F] [Field E
] [Algebra F E] (A B : IntermediateField F E) : Module.rank F ↥(A ⊔ B) <= Module
.rank F A * Module.rank F B
参数：A B : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.rank_sup_le_of_isAlgebraic`：rank_sup_le_of_isAlgebraic
 (halg : Algebra.IsAlgebraic K E1 ∨ Algebra.IsAlgebraic K E2) : Module.rank K ↥(
E1 ⊔ E2) <= Module.rank K E1 * Mod…
· 使用定理 `Algebra.Transcendental.ringHom_of_comp_eq`：Algebra.Transcendental.ringHo
m_of_comp_eq [H : Algebra.Transcendental R A] (hf : Function.Surjective f) (hg :
 Function.Injective g) (h : Rin…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `IntermediateField.inclusion_injective`：inclusion_injective {E F : Interm
ediateField K L} (hEF : E <= F) : Function.Injective (inclusion hEF)
· 使用定理 `Algebra.Transcendental.infinite`：Algebra.Transcendental.infinite [Algebr
a.Transcendental R A] : Infinite A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.Transcendental.rank_eq_cardinalMk`：Algebra.Transcendental.rank_e
q_cardinalMk (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [Algebr
a.Transcendental F E] : Module.…
· 使用定理 `IntermediateField.sup_def`：sup_def (S T : IntermediateField F E) : S ⊔ T
 = adjoin F (S union T : Set E)
· 使用定理 `Cardinal.mul_mk_eq_max`：mul_mk_eq_max {α β : Type u} [Infinite α] [Infin
ite β] : #α * #β = max #α #β
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IntermediateField.lift_cardinalMk_adjoin_le`：lift_cardinalMk_adjoin_le {
E : Type v} [Field E] [Algebra F E] (s : Set E) : Cardinal.lift.{u} #(adjoin F s
) <= Cardinal.lift.{v} #F ⊔ Cardi…
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Cardinal.mk_union_le`：mk_union_le {α : Type u} (S T : Set α) : #(S union
 T : Set α) <= #S + #T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.add_mk_eq_max`：add_mk_eq_max {α β : Type u} [Infinite α] : #α +
 #β = max #α #β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
（共 40 条，此处仅展示前 30 条）
-/
theorem IntermediateField.rank_sup_le
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] (A B : IntermediateField F E) :
    Module.rank F ↥(A ⊔ B) ≤ Module.rank F A * Module.rank F B := by
  by_cases hA : Algebra.IsAlgebraic F A
  · exact rank_sup_le_of_isAlgebraic A B (Or.inl hA)
  by_cases hB : Algebra.IsAlgebraic F B
  · exact rank_sup_le_of_isAlgebraic A B (Or.inr hB)
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at hA hB
  have : Algebra.Transcendental F ↥(A ⊔ B) := .ringHom_of_comp_eq (RingHom.id F)
    (inclusion le_sup_left) Function.surjective_id (inclusion_injective _) rfl
  have := Algebra.Transcendental.infinite F A
  have := Algebra.Transcendental.infinite F B
  simp_rw [Algebra.Transcendental.rank_eq_cardinalMk]
  rw [sup_def, mul_mk_eq_max, ← Cardinal.lift_le.{u}]
  refine (lift_cardinalMk_adjoin_le _ _).trans ?_
  calc
    _ ≤ Cardinal.lift.{v} #F ⊔ Cardinal.lift.{u} (#A ⊔ #B) ⊔ ℵ₀ := by
      gcongr
      rw [Cardinal.lift_le]
      exact (mk_union_le _ _).trans_eq (by simp)
    _ = _ := by
      simp [lift_mk_le_lift_mk_of_injective (algebraMap F A).injective]
