/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Nakayama


/-!

We gather results about the quotients of local rings.

-/

@[expose] public section

open Submodule FiniteDimensional Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Module.Finite R S]

namespace IsLocalRing

local notation "p" => maximalIdeal R
local notation "pS" => Ideal.map (algebraMap R S) p

/-
**IsLocalRing.quotient_span_eq_top_iff_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Is
LocalRing`。
形式化陈述：quotient_span_eq_top_iff_span_eq_top (s : Set S) : span (R ⧸ p) ((Ideal.Qu
otient.mk (I
参数：s : Set S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.tower_quotient_map_quotient`：∀ {R : Type u_1} [inst : Com
mRing R] {S : Type u_2} [inst_1 : CommRing S] {p : Ideal R} [inst_2 : Algebra R 
S],   IsScalarTower R (R ⧸ p) (S…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.restrictScalars_span`：restrictScalars_span (hsur : Function.Su
rjective (algebraMap R A)) (X : Set M) : restrictScalars R (span A X) = span R X
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用引理 `LinearMap.coe_coe`：coe_coe {F : Type*} [FunLike F M M₃] [SemilinearMapCl
ass F σ M M₃] {f : F} : ⇑(f : M ->ₛₗ[σ] M₃) = f
· 使用定理 `IsScalarTower.coe_toAlgHom'`：coe_toAlgHom' : (toAlgHom R S A : S -> A) =
 algebraMap S A
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Submodule.le_of_le_smul_of_le_jacobson_bot`：le_of_le_smul_of_le_jacobson
_bot {R M} [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R} {N N' : Subm
odule R M} (hN' : N'.FG) (hIJ : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsLocalRing.jacobson_eq_maximalIdeal`：jacobson_eq_maximalIdeal (I : Idea
l R) (h : I != ⊤) : I.jacobson = IsLocalRing.maximalIdeal R
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
（共 37 条，此处仅展示前 30 条）
-/
theorem quotient_span_eq_top_iff_span_eq_top (s : Set S) :
    span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s) = ⊤ ↔ span R s = ⊤ := by
  have H : (span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s)).restrictScalars R =
      (span R s).map (IsScalarTower.toAlgHom R S (S ⧸ pS) : S →ₗ[R] S ⧸ pS) := by
    rw [map_span, ← restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective,
      LinearMap.coe_coe, IsScalarTower.coe_toAlgHom', Ideal.Quotient.algebraMap_eq]
  constructor
  · intro hs
    rw [← top_le_iff]
    apply le_of_le_smul_of_le_jacobson_bot
    · exact Module.finite_def.mp ‹_›
    · exact (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · rw [Ideal.smul_top_eq_map]
      rintro x -
      have : LinearMap.ker (IsScalarTower.toAlgHom R S (S ⧸ pS) : S →ₗ[R] S ⧸ pS) =
          Submodule.restrictScalars R pS := by
        ext; simp [Ideal.Quotient.eq_zero_iff_mem]
      rw [← this, ← comap_map_eq, mem_comap, ← H, hs, restrictScalars_top]
      exact mem_top
  · intro hs
    rwa [hs, Submodule.map_top, LinearMap.range_eq_top.mpr,
      restrictScalars_eq_top_iff] at H
    rw [LinearMap.coe_coe, IsScalarTower.coe_toAlgHom', Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective

attribute [local instance] Ideal.Quotient.field

variable [Module.Free R S] {ι : Type*}
/-
**IsLocalRing.finrank_quotient_map** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：finrank_quotient_map : finrank (R ⧸ p) (S ⧸ pS) = finrank R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.tower_quotient_map_quotient`：∀ {R : Type u_1} [inst : Com
mRing R] {S : Type u_2} [inst_1 : CommRing S] {p : Ideal R} [inst_2 : Algebra R 
S],   IsScalarTower R (R ⧸ p) (S…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用引理 `finrank_le_of_span_eq_top`：finrank_le_of_span_eq_top {ι : Type*} [Fintyp
e ι] {v : ι -> M} (hv : Submodule.span R (Set.range v) = ⊤) : finrank R M <= Fin
type.card ι
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalRing.quotient_span_eq_top_iff_span_eq_top`：quotient_span_eq_top_i
ff_span_eq_top (s : Set S) : span (R ⧸ p) ((Ideal.Quotient.mk (I
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem finrank_quotient_map :
    finrank (R ⧸ p) (S ⧸ pS) = finrank R S := by
  have : Module.Finite (R ⧸ p) (S ⧸ pS) := Module.Finite.of_restrictScalars_finite R _ _
  apply le_antisymm
  · let b := Module.Free.chooseBasis R S
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    apply finrank_le_of_span_eq_top
    rw [Set.range_comp]
    apply (quotient_span_eq_top_iff_span_eq_top _).mpr b.span_eq
  · let b := Module.Free.chooseBasis (R ⧸ p) (S ⧸ pS)
    choose b' hb' using fun i ↦ Ideal.Quotient.mk_surjective (b i)
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    refine finrank_le_of_span_eq_top (v := b') ?_
    apply (quotient_span_eq_top_iff_span_eq_top _).mp
    rw [← Set.range_comp, show Ideal.Quotient.mk pS ∘ b' = ⇑b from funext hb']
    exact b.span_eq

/-- Given a basis of `S`, the induced basis of `S / Ideal.map (algebraMap R S) p`. -/
noncomputable
/-
**IsLocalRing.basisQuotient** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing`。
形式化陈述：basisQuotient [Fintype ι] (b : Basis ι R S) : Basis ι (R ⧸ p) (S ⧸ pS)
参数：b : Basis ι R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def basisQuotient [Fintype ι] (b : Basis ι R S) : Basis ι (R ⧸ p) (S ⧸ pS) :=
  basisOfTopLeSpanOfCardEqFinrank (Ideal.Quotient.mk pS ∘ b)
    (by
      rw [Set.range_comp]
      exact ((quotient_span_eq_top_iff_span_eq_top _).mpr b.span_eq).ge)
    (by rw [finrank_quotient_map, finrank_eq_card_basis b])
/-
**IsLocalRing.basisQuotient_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：basisQuotient_apply [Fintype ι] (b : Basis ι R S) (i) : (basisQuotient b) 
i = Ideal.Quotient.mk pS (b i)
参数：b : Basis ι R S；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coe_basisOfTopLeSpanOfCardEqFinrank`：coe_basisOfTopLeSpanOfCardEqFinrank
 {ι : Type*} [Fintype ι] (b : ι -> M) (le_span : ⊤ <= span R (Set.range b)) (car
d_eq : Fintype.card ι = f…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma basisQuotient_apply [Fintype ι] (b : Basis ι R S) (i) :
    (basisQuotient b) i = Ideal.Quotient.mk pS (b i) := by
  delta basisQuotient
  rw [coe_basisOfTopLeSpanOfCardEqFinrank, Function.comp_apply]
/-
**IsLocalRing.basisQuotient_repr** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：basisQuotient_repr {ι} [Fintype ι] (b : Basis ι R S) (x) (i) : (basisQuoti
ent b).repr (Ideal.Quotient.mk pS x) i = Ideal.Quotient.mk p (b.repr x i)
参数：b : Basis ι R S；x；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.linearEquivFunOnFinite_symm_coe`：linearEquivFunOnFinite_symm_coe
 (f : α ->₀ M) : (linearEquivFunOnFinite R M α).symm f = f
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_eq_fintype_linearCombination_apply`：Finsupp.li
nearCombination_eq_fintype_linearCombination_apply (x : α -> R) : linearCombinat
ion R v ((Finsupp.linearEquivFunOnFinite R R α).sy…
· 使用定理 `Fintype.linearCombination_apply`：Fintype.linearCombination_apply (f) : F
intype.linearCombination R v f = ∑ i, f i • v i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `IsLocalRing.basisQuotient_apply`：basisQuotient_apply [Fintype ι] (b : Ba
sis ι R S) (i) : (basisQuotient b) i = Ideal.Quotient.mk pS (b i)
· 使用定理 `Ideal.Quotient.mk_smul_mk_quotient_map_quotient`：∀ {R : Type u_1} [inst 
: CommRing R] {S : Type u_2} [inst_1 : CommRing S] {p : Ideal R} [inst_2 : Algeb
ra R S] (x : R)   (y : S),   (Ideal.Q…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
-/
lemma basisQuotient_repr {ι} [Fintype ι] (b : Basis ι R S) (x) (i) :
    (basisQuotient b).repr (Ideal.Quotient.mk pS x) i =
    Ideal.Quotient.mk p (b.repr x i) := by
  refine congr_fun (g := Ideal.Quotient.mk p ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ p) _ _).symm.injective
  apply (basisQuotient b).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply (R ⧸ p),
    Fintype.linearCombination_apply]
  simp only [Function.comp_apply, basisQuotient_apply,
    Ideal.Quotient.mk_smul_mk_quotient_map_quotient, ← Algebra.smul_def]
  rw [← map_sum, Basis.sum_repr b x]
/-
**IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient** 是 Mathlib 
中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：exists_maximalIdeal_pow_le_of_isArtinianRing_quotient (I : Ideal R) [IsArt
inianRing (R ⧸ I)] : exists n, maximalIdeal R ^ n <= I
参数：I : Ideal R；R ⧸ I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.nontrivial_iff`：∀ {R : Type u_3} [inst : Ring R] {I : Ide
al R}, Nontrivial (R ⧸ I) ↔ I ≠ ⊤
· 使用定理 `IsLocalRing.of_surjective'`：of_surjective' [Ring S] [Nontrivial S] (f : 
R ->+* S) (hf : Function.Surjective f) : IsLocalRing S
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `IsLocalHom.of_surjective`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] [Nontrivial S] [IsLocalRing R] (f : R →+* S),   Func
tion.Surjectiv…
· 使用定理 `IsArtinianRing.isNilpotent_jacobson_bot`：isNilpotent_jacobson_bot {R} [R
ing R] [IsArtinianRing R] : IsNilpotent (Ideal.jacobson (⊥ : Ideal R))
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.map_eq_bot_iff_le_ker`：map_eq_bot_iff_le_ker {I : Ideal R} (f : F)
 : I.map f = ⊥ ↔ I <= RingHom.ker f
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `IsLocalRing.jacobson_eq_maximalIdeal`：jacobson_eq_maximalIdeal (I : Idea
l R) (h : I != ⊤) : I.jacobson = IsLocalRing.maximalIdeal R
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
-/
lemma exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] : ∃ n, maximalIdeal R ^ n ≤ I := by
  by_cases hI : I = ⊤
  · simp [hI]
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
  have : (maximalIdeal R).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (le_maximalIdeal hI)]
  rw [jacobson_eq_maximalIdeal _ bot_ne_top, ← this, ← Ideal.map_pow, Ideal.zero_eq_bot,
    Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hn
  exact ⟨n, hn⟩
/-
**IsLocalRing.finite_quotient_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：finite_quotient_iff [IsNoetherianRing R] [Finite (ResidueField R)] {I : Id
eal R} : Finite (R ⧸ I) ↔ exists n, (maximalIdeal R) ^ n <= I
参数：ResidueField R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`：exist
s_maximalIdeal_pow_le_of_isArtinianRing_quotient (I : Ideal R) [IsArtinianRing (
R ⧸ I)] : exists n, maximalIdeal R ^ n <= I
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `SetLike.instFinite`：∀ {A : Type u_1} {B : Type u_2} [SetLike A B] [Finit
e B], Finite A
· 使用引理 `Ideal.finite_quotient_pow`：Ideal.finite_quotient_pow (hI : I.FG) [Finite
 (R ⧸ I)] (n) : Finite (R ⧸ I ^ n)
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Ideal.Quotient.factor_surjective`：factor_surjective (H : S <= T) : Funct
ion.Surjective (factor H)
-/
lemma finite_quotient_iff [IsNoetherianRing R] [Finite (ResidueField R)] {I : Ideal R} :
    Finite (R ⧸ I) ↔ ∃ n, (maximalIdeal R) ^ n ≤ I := by
  refine ⟨fun _ ↦ exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I, ?_⟩
  rintro ⟨n, hn⟩
  have : Finite (R ⧸ maximalIdeal R) := ‹_›
  have := (Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) n)
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hn)

end IsLocalRing

