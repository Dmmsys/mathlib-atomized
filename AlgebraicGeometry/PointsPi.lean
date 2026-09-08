/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!

# `Π Rᵢ`-Points of Schemes

We show that the canonical map `X(Π Rᵢ) ⟶ Π X(Rᵢ)` (`AlgebraicGeometry.pointsPi`)
is injective and surjective under various assumptions.

-/

@[expose] public section

open CategoryTheory Limits PrimeSpectrum

namespace AlgebraicGeometry

universe u v

variable {ι : Type u} (R : ι → CommRingCat.{u})

/-
**AlgebraicGeometry.Ideal.span_eq_top_of_span_image_evalRingHom** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.Ideal`。
形式化陈述：∀ {ι : Type u_2} {R : ι → Type u_1} [inst : (i : ι) → CommRing (R i)] (s :
 Set ((i : ι) → R i)),   s.Finite → (∀ (i : ι), Ideal.span (⇑(Pi.evalRingHom (fu
n x => R x) i) '' s) = ⊤) → Ideal.span s = ⊤
参数：i : ι；R i；s : Set ((i : ι) → R i)；∀ (i : ι), Ideal.span (⇑(Pi.evalRingHom (fu
n x => R x) i) '' s) = ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.equivFunOnFinite_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_
4} [inst : Zero M] [inst_1 : Finite α] (f : α → M) (a : α),   (Finsupp.equivFunO
nFinite.symm f) a = f a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma Ideal.span_eq_top_of_span_image_evalRingHom
    {ι} {R : ι → Type*} [∀ i, CommRing (R i)] (s : Set (Π i, R i))
    (hs : s.Finite) (hs' : ∀ i, Ideal.span (Pi.evalRingHom (R ·) i '' s) = ⊤) :
    Ideal.span s = ⊤ := by
  simp only [Ideal.eq_top_iff_one, ← Subtype.range_val (s := s), ← Set.range_comp,
    Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hs' ⊢
  choose f hf using hs'
  have : Fintype s := hs.fintype
  refine ⟨Finsupp.equivFunOnFinite.symm fun i x ↦ f x i, ?_⟩
  ext i
  simpa [Finsupp.sum_fintype] using hf i

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.eq_top_of_sigmaSpec_subset_of_isCompact** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry`。
形式化陈述：eq_top_of_sigmaSpec_subset_of_isCompact (U : (Spec <| .of <| Π i, R i).Ope
ns) (V : Set (Spec <| .of <| Π i, R i)) (hV : ↑(sigmaSpec R).opensRange subseteq
 V) (hV' : IsCompact (X
参数：U : (Spec <| .of <| Π i, R i).Opens；V : Set (Spec <| .of <| Π i, R i)；hV : ↑(
sigmaSpec R).opensRange subseteq V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionSigmaSpec`：∀ {ι : Type u} (R : ι → 
CommRingCat), AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.sigmaSpec R)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isOpen_iff`：isOpen_iff (U : Set (PrimeSpectrum R)) : IsOpe
n U ↔ exists s, Uᶜ = zeroLocus s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PrimeSpectrum.basicOpen_eq_zeroLocus_compl`：basicOpen_eq_zeroLocus_compl
 (r : R) : (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.zeroLocus_iUnion₂`：zeroLocus_iUnion₂ {ι : Sort*} {κ : (i :
 ι) -> Sort*} (s : forall i, κ i -> Set R) : zeroLocus (⋃ (i) (j), s i j) = ⋂ (i
) (j), zeroLocus (s i…
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
（共 52 条，此处仅展示前 30 条）
-/
lemma eq_top_of_sigmaSpec_subset_of_isCompact
    (U : (Spec <| .of <| Π i, R i).Opens) (V : Set (Spec <| .of <| Π i, R i))
    (hV : ↑(sigmaSpec R).opensRange ⊆ V)
    (hV' : IsCompact (X := Spec (.of <| Π i, R i)) V)
    (hVU : V ⊆ U) : U = ⊤ := by
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff _).mp U.2
  obtain ⟨t, hts, ht, ht'⟩ : ∃ t ⊆ s, t.Finite ∧ V ⊆ ⋃ i ∈ t, (basicOpen i).1 := by
    obtain ⟨t, ht⟩ := hV'.elim_finite_subcover
      (fun i : s ↦ (basicOpen i.1).1) (fun _ ↦ (basicOpen _).2)
      (by simpa [← Set.compl_iInter, ← zeroLocus_iUnion₂ (κ := (· ∈ s)), ← hs])
    exact ⟨t.map (Function.Embedding.subtype _), by simp, Finset.finite_toSet _, by simpa using ht⟩
  replace ht' : V ⊆ (zeroLocus t)ᶜ := by
    simpa [← Set.compl_iInter, ← zeroLocus_iUnion₂ (κ := (· ∈ t))] using ht'
  have (i : _) : Ideal.span (Pi.evalRingHom (R ·) i '' t) = ⊤ := by
    rw [← zeroLocus_empty_iff_eq_top, zeroLocus_span, ← preimage_comap_zeroLocus,
      ← Set.compl_univ_iff, ← Set.preimage_compl, Set.preimage_eq_univ_iff]
    trans (Sigma.ι _ i ≫ sigmaSpec R).opensRange.1
    · simp; rfl
    · rw [Scheme.Hom.opensRange_comp]
      exact (Set.image_subset_range _ _).trans (hV.trans ht')
  have : Ideal.span s = ⊤ := top_le_iff.mp
    ((Ideal.span_eq_top_of_span_image_evalRingHom _ ht this).ge.trans (Ideal.span_mono hts))
  simpa [← zeroLocus_span s, zeroLocus_empty_iff_eq_top.mpr this] using hs
/-
**AlgebraicGeometry.eq_bot_of_comp_quotientMk_eq_sigmaSpec** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：eq_bot_of_comp_quotientMk_eq_sigmaSpec (I : Ideal (Π i, R i)) (f : (∐ fun 
i => Spec (R i)) ⟶ Spec (.of <| (Π i, R i) ⧸ I)) (hf : f ≫ Spec.map (CommRingCat
.ofHom (Ideal.Quotient.mk I)) = sigmaSpec R) : I = ⊥
参数：I : Ideal (Π i, R i)；f : (∐ fun i => Spec (R i)) ⟶ Spec (.of <| (Π i, R i) ⧸ 
I)；hf : f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = sigmaSpec R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.ι_sigmaSpec`：ι_sigmaSpec (R : ι -> CommRingCat) (i) : 
Sigma.ι _ i ≫ sigmaSpec R = Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))
· 使用定理 `AlgebraicGeometry.Spec.preimage_map`：∀ {R S : CommRingCat} (φ : R ⟶ S), 
AlgebraicGeometry.Spec.preimage (AlgebraicGeometry.Spec.map φ) = φ
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `AlgebraicGeometry.Spec.preimage_comp`：∀ {R S T : CommRingCat} (f : Algeb
raicGeometry.Spec R ⟶ AlgebraicGeometry.Spec S)   (g : AlgebraicGeometry.Spec S 
⟶ AlgebraicGeometry.Spec T…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eq_bot_of_comp_quotientMk_eq_sigmaSpec (I : Ideal (Π i, R i))
    (f : (∐ fun i ↦ Spec (R i)) ⟶ Spec (.of <| (Π i, R i) ⧸ I))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = sigmaSpec R) :
    I = ⊥ := by
  refine le_bot_iff.mp fun x hx ↦ ?_
  ext i
  simpa [← Category.assoc, Ideal.Quotient.eq_zero_iff_mem.mpr hx] using
    congr((Spec.preimage (Sigma.ι (Spec <| R ·) i ≫ $hf)).hom x).symm

/-- If `V` is a locally closed subscheme of `Spec (Π Rᵢ)` containing `∐ Spec Rᵢ`, then
`V = Spec (Π Rᵢ)`. -/
/-
**AlgebraicGeometry.isIso_of_comp_eq_sigmaSpec** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry`。
形式化陈述：isIso_of_comp_eq_sigmaSpec {V : Scheme} (f : (∐ fun i => Spec (R i)) ⟶ V) 
(g : V ⟶ Spec (.of <| Π i, R i)) [IsImmersion g] [CompactSpace V] (hU' : f ≫ g =
 sigmaSpec R) : IsIso g
参数：f : (∐ fun i => Spec (R i)) ⟶ V；g : V ⟶ Spec (.of <| Π i, R i)；hU' : f ≫ g = 
sigmaSpec R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionSigmaSpec`：∀ {ι : Type u} (R : ι → 
CommRingCat), AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.sigmaSpec R)
· 使用引理 `AlgebraicGeometry.eq_top_of_sigmaSpec_subset_of_isCompact`：eq_top_of_sig
maSpec_subset_of_isCompact (U : (Spec <| .of <| Π i, R i).Opens) (V : Set (Spec 
<| .of <| Π i, R i)) (hV : ↑(sigmaSpec R).opens…
· 使用引理 `subset_coborder`：subset_coborder : s subseteq coborder s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.opensRange.congr_simp`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f f_1 : X ⟶ Y) (e_f : f = f_1) [H : AlgebraicGeometry.IsOpenImme
rsion f],   AlgebraicGeometry.Scheme.Hom…
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.topIso_hom`：∀ (X : AlgebraicGeometry.Scheme), X
.topIso.hom = ⊤.ι
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   CategoryTheory.C
ategoryStruct.comp (AlgebraicGeom…
· 使用定理 `AlgebraicGeometry.instIsClosedImmersionLiftCoborder`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsImmersion f],   Algebrai
cGeometry.IsClosedImmersion (AlgebraicGeo…
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instOfIsIsoScheme`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.IsClos
edImmersion f
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.IsClosedImmersion.Spec_iff`：Spec_iff {R : CommRingCat}
 {f : X ⟶ Spec R} : IsClosedImmersion f ↔ exists I : Ideal R, exists e : X ≅ Spe
c (.of <| R ⧸ I), f = e.hom ≫ Spec…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeMapOfCommRingCat`：∀ {R S : CommRingCat}
 (f : R ⟶ S) [CategoryTheory.IsIso f], CategoryTheory.IsIso (AlgebraicGeometry.S
pec.map f)
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `AlgebraicGeometry.eq_bot_of_comp_quotientMk_eq_sigmaSpec`：eq_bot_of_comp
_quotientMk_eq_sigmaSpec (I : Ideal (Π i, R i)) (f : (∐ fun i => Spec (R i)) ⟶ S
pec (.of <| (Π i, R i) ⧸ I)) (hf : f ≫ Spec.ma…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
If `V` is a locally closed subscheme of `Spec (Π Rᵢ)` containing `∐ Spec Rᵢ`, th
en
`V = Spec (Π Rᵢ)`.
-/
lemma isIso_of_comp_eq_sigmaSpec {V : Scheme}
    (f : (∐ fun i ↦ Spec (R i)) ⟶ V) (g : V ⟶ Spec (.of <| Π i, R i))
    [IsImmersion g] [CompactSpace V]
    (hU' : f ≫ g = sigmaSpec R) : IsIso g := by
  have : g.coborderRange = ⊤ := by
    apply eq_top_of_sigmaSpec_subset_of_isCompact (hVU := subset_coborder)
    · simpa only [← hU'] using! Set.range_comp_subset_range f g
    · exact isCompact_range g.continuous
  have : IsClosedImmersion g := by
    have : IsIso g.coborderRange.ι := by rw [this, ← Scheme.topIso_hom]; infer_instance
    rw [← g.liftCoborder_ι]
    infer_instance
  obtain ⟨I, e, rfl⟩ := IsClosedImmersion.Spec_iff.mp this
  obtain rfl := eq_bot_of_comp_quotientMk_eq_sigmaSpec R I (f ≫ e.hom) (by rwa [Category.assoc])
  convert_to! IsIso (e.hom ≫ Spec.map (RingEquiv.quotientBot _).toCommRingCatIso.inv)
  infer_instance

variable (X : Scheme)

/-- The canonical map `X(Π Rᵢ) ⟶ Π X(Rᵢ)`.
This is injective if `X` is quasi-separated, surjective if `X` is affine,
or if `X` is compact and each `Rᵢ` is local. -/
noncomputable
/-
**AlgebraicGeometry.pointsPi** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：pointsPi : (Spec (.of <| Π i, R i) ⟶ X) -> Π i, Spec (R i) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pointsPi : (Spec (.of <| Π i, R i) ⟶ X) → Π i, Spec (R i) ⟶ X :=
  fun f i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (R ·) i)) ≫ f

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.pointsPi_injective** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：pointsPi_injective [QuasiSeparatedSpace X] : Function.Injective (pointsPi 
R X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `AlgebraicGeometry.instHasFiniteLimitsScheme`：CategoryTheory.Limits.HasFi
niteLimits AlgebraicGeometry.Scheme
· 使用引理 `AlgebraicGeometry.isIso_of_comp_eq_sigmaSpec`：isIso_of_comp_eq_sigmaSpec
 {V : Scheme} (f : (∐ fun i => Spec (R i)) ⟶ V) (g : V ⟶ Spec (.of <| Π i, R i))
 [IsImmersion g] [CompactSpace V] …
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.ι_sigmaSpec_assoc`：∀ {ι : Type u} (R : ι → CommRingCat
) (i : ι) {Z : AlgebraicGeometry.Scheme}   (h : AlgebraicGeometry.Spec (CommRing
Cat.of ((i : ι) → ↑(R i))…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `AlgebraicGeometry.IsImmersion.instιScheme`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f g : X ⟶ Y), AlgebraicGeometry.IsImmersion (CategoryTheory.Limits.equali
zer.ι f g)
· 使用定理 `AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatEqualizerSche
meOfQuasiSeparatedSpace`：∀ {X Y : AlgebraicGeometry.Scheme} [CompactSpace ↥X] [Q
uasiSeparatedSpace ↥Y] (f g : X ⟶ Y),   CompactSpace ↥(CategoryTheory.Limits.equ
alize…
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
-/
lemma pointsPi_injective [QuasiSeparatedSpace X] : Function.Injective (pointsPi R X) := by
  rintro f g e
  have := isIso_of_comp_eq_sigmaSpec R (V := equalizer f g)
    (equalizer.lift (sigmaSpec R) (by ext1 i; simpa using! congr_fun e i))
    (equalizer.ι f g) (by simp)
  rw [← cancel_epi (equalizer.ι f g), equalizer.condition]
/-
**AlgebraicGeometry.pointsPi_surjective_of_isAffine** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：pointsPi_surjective_of_isAffine [IsAffine X] : Function.Surjective (points
Pi R X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
-/
lemma pointsPi_surjective_of_isAffine [IsAffine X] : Function.Surjective (pointsPi R X) := by
  rintro f
  refine ⟨Spec.map (CommRingCat.ofHom
    (RingHom.pi fun i ↦ (Spec.preimage (f i ≫ X.isoSpec.hom)).1)) ≫ X.isoSpec.inv, ?_⟩
  ext i : 1
  simp only [pointsPi, ← Spec.map_comp_assoc, Iso.comp_inv_eq]
  exact Spec.map_preimage _
/-
**AlgebraicGeometry.pointsPi_surjective** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：pointsPi_surjective [CompactSpace X] [forall i, IsLocalRing (R i)] : Funct
ion.Surjective (pointsPi R X)
参数：R i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `IsLocalRing.specializes_closedPoint`：specializes_closedPoint (x : PrimeS
pectrum R) : x ⤳ closedPoint R
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用引理 `AlgebraicGeometry.pointsPi_surjective_of_isAffine`：pointsPi_surjective_o
f_isAffine [IsAffine X] : Function.Surjective (pointsPi R X)
· 使用定理 `AlgebraicGeometry.instIsAffineXSchemeFiniteSubcover`：∀ (X : AlgebraicGeo
metry.Scheme) [inst : CompactSpace ↥X] (𝒰 : X.OpenCover)   [∀ (i : 𝒰.I₀), Algebr
aicGeometry.IsAffine (𝒰.X i)] (i : 𝒰.fini…
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeSigmaSpecOfFinite`：∀ {ι : Type u} [Fini
te ι] (R : ι → CommRingCat), CategoryTheory.IsIso (AlgebraicGeometry.sigmaSpec R
)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.pointsPi.eq_1`：∀ {ι : Type u} (R : ι → CommRingCat) (X
 : AlgebraicGeometry.Scheme)   (f : AlgebraicGeometry.Spec (CommRingCat.of ((i :
 ι) → ↑(R i))) ⟶ X) (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
· 使用引理 `CommRingCat.ofHom_comp`：ofHom_comp {R S T : Type u} [CommRing R] [CommRi
ng S] [CommRing T] (f : R ->+* S) (g : S ->+* T) : ofHom (g.comp f) = ofHom f ≫ 
ofHom g
· 使用引理 `AlgebraicGeometry.ι_sigmaSpec`：ι_sigmaSpec (R : ι -> CommRingCat) (i) : 
Sigma.ι _ i ≫ sigmaSpec R = Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_desc`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {β : Type w} {f : β → C}   [inst_1 : CategoryTheory.Limits.
HasCoproduct f] {P : C} …
（共 33 条，此处仅展示前 30 条）
-/
lemma pointsPi_surjective [CompactSpace X] [∀ i, IsLocalRing (R i)] :
    Function.Surjective (pointsPi R X) := by
  intro f
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  have (i : _) : ∃ j, Set.range (f i) ⊆ (𝒰.f j).opensRange := by
    refine ⟨𝒰.idx ((f i) (IsLocalRing.closedPoint (R i))), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map (f i).continuous).mem_open
      (𝒰.f _).opensRange.2 (𝒰.covers _)
  choose j hj using this
  have (j₀ : _) := pointsPi_surjective_of_isAffine (ι := { i // j i = j₀ }) (R ·) (𝒰.X j₀)
    (fun i ↦ IsOpenImmersion.lift (𝒰.f j₀) (f i.1) (by rcases i with ⟨i, rfl⟩; exact hj i))
  choose g hg using this
  simp_rw [funext_iff, pointsPi] at hg
  let R' (j₀) := CommRingCat.of (Π i : { i // j i = j₀ }, R i)
  let e : (Π i, R i) ≃+* Π j₀, R' j₀ :=
  { toFun f _ i := f i
    invFun f i := f _ ⟨i, rfl⟩
    right_inv _ := funext₂ fun j₀ i ↦ by rcases i with ⟨i, rfl⟩; rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl }
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ inv (sigmaSpec R') ≫
    Sigma.desc fun j₀ ↦ g j₀ ≫ 𝒰.f j₀, ?_⟩
  ext i : 1
  have : (Pi.evalRingHom (R ·) i).comp e.symm.toRingHom =
    (Pi.evalRingHom _ ⟨i, rfl⟩).comp (Pi.evalRingHom (R' ·) (j i)) := rfl
  rw [pointsPi, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, this, CommRingCat.ofHom_comp,
    Spec.map_comp_assoc, ← ι_sigmaSpec R', Category.assoc, IsIso.hom_inv_id_assoc,
    Sigma.ι_desc, ← Category.assoc, hg, IsOpenImmersion.lift_fac]

end AlgebraicGeometry

