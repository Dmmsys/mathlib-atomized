/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.CategoryTheory.ObjectProperty.Small


/-! # Smallness results on the category of `CommRing` -/

@[expose] public section

universe u

open CategoryTheory

namespace CommRingCat

variable {P Q : ObjectProperty CommRingCat.{u}}

/-
**CommRingCat.essentiallySmall_of_finiteType** 是 Mathlib 中的一个引理，位于命名空间 `CommRing
Cat`。
形式化陈述：essentiallySmall_of_finiteType [ObjectProperty.EssentiallySmall.{u} Q] (hP
Q : forall S, P S -> exists R, Q R ∧ exists (f : R ⟶ S), f.hom.FiniteType) : Obj
ectProperty.EssentiallySmall.{u} P
参数：hPQ : forall S, P S -> exists R, Q R ∧ exists (f : R ⟶ S), f.hom.FiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectPrope
rty C)   [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `RingHom.FiniteType.exists_smallRepr`：RingHom.FiniteType.exists_smallRepr
 {S : Type v} [CommRing S] {f : R ->+* S} (hf : f.FiniteType) : exists (T : FGAl
gCatSkeleton R) (e : T.ev…
· 使用定理 `RingHom.FiniteType.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg : g.Fini
teType) (hf : f.FiniteType) : (g.comp f).FiniteType
· 使用定理 `RingHom.Finite.finiteType`：finiteType {f : A ->+* B} (hf : f.Finite) : F
initeType f
· 使用定理 `RingEquiv.finite`：∀ {A : Type u_1} {B : Type u_2} [inst : CommRing A] [i
nst_1 : CommRing B] (e : A ≃+* B), e.toRingHom.Finite
-/
lemma essentiallySmall_of_finiteType [ObjectProperty.EssentiallySmall.{u} Q]
    (hPQ : ∀ S, P S → ∃ R, Q R ∧ ∃ (f : R ⟶ S), f.hom.FiniteType) :
    ObjectProperty.EssentiallySmall.{u} P := by
  obtain ⟨Q', _, hQ'Q, hQQ'⟩ := ObjectProperty.EssentiallySmall.exists_small_le Q
  let f (S : Σ R : Subtype Q', FGAlgCatSkeleton R) : CommRingCat := .of S.2.eval.obj
  refine ⟨.ofObj f, inferInstance, fun S hS ↦ ?_⟩
  obtain ⟨R, hR, φ, hφ⟩ := hPQ S hS
  wlog hR' : Q' R generalizing R
  · obtain ⟨R', hR', ⟨e⟩⟩ := hQQ' _ hR
    exact this R' (hQ'Q _ hR') (e.inv ≫ φ)
      (hφ.comp e.symm.commRingCatIsoToRingEquiv.finite.finiteType) hR'
  obtain ⟨T, e, he⟩ := hφ.exists_smallRepr
  exact ⟨_, ⟨⟨_, hR'⟩, T⟩, ⟨RingEquiv.toCommRingCatIso e.symm⟩⟩
/-
**CommRingCat.essentiallySmall_of_localizationAway** 是 Mathlib 中的一个引理，位于命名空间 `Co
mmRingCat`。
形式化陈述：essentiallySmall_of_localizationAway [ObjectProperty.EssentiallySmall.{u} 
Q] (hPQ : forall S, P S -> exists s : Set S, Ideal.span s = ⊤ ∧ forall f in s, Q
 (.of (Localization.Away f))) : ObjectProperty.EssentiallySmall.{u} P
参数：hPQ : forall S, P S -> exists s : Set S, Ideal.span s = ⊤ ∧ forall f in s, Q 
(.of (Localization.Away f))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small_le`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectPrope
rty C)   [CategoryTheory.ObjectProperty.EssentiallyS…
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `Localization.algebraMap_injective_of_span_eq_top`：algebraMap_injective_o
f_span_eq_top (s : Set R) (span_eq : Ideal.span s = ⊤) : Function.Injective (alg
ebraMap R <| Π a : s, Away a.1)
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.injective_codRestrict`：injective_codRestrict {f : R ->+* S} {s :
 σS} {h : forall x, f x in s} : Function.Injective (f.codRestrict s h) ↔ Functio
n.Injective f
· 使用定理 `RingHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : R ->+* S
) : Function.Surjective f.rangeRestrict
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
lemma essentiallySmall_of_localizationAway [ObjectProperty.EssentiallySmall.{u} Q]
    (hPQ : ∀ S, P S → ∃ s : Set S, Ideal.span s = ⊤ ∧ ∀ f ∈ s, Q (.of (Localization.Away f))) :
    ObjectProperty.EssentiallySmall.{u} P := by
  obtain ⟨Q', _, hQ'Q, hQQ'⟩ := ObjectProperty.EssentiallySmall.exists_small_le Q
  let f (S : Σ (n : ℕ) (R : Fin n → Subtype Q'), Subring (Π i, (R i).1)) : CommRingCat := .of S.2.2
  refine ⟨.ofObj f, inferInstance, fun S hS ↦ ?_⟩
  obtain ⟨s, hs, H⟩ := hPQ S hS
  wlog hs' : s.Finite generalizing s
  · obtain ⟨s', hs's, hs'⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    exact this s' hs' (fun f hf ↦ H f (hs's hf)) s'.finite_toSet
  choose S' hS' e using fun (f : s) ↦ hQQ' _ (H _ f.2)
  let φ : S →+* Π i, S' (hs'.equivFin.symm i) :=
    ((RingEquiv.piCongrRight fun i ↦ (e i).some.commRingCatIsoToRingEquiv).trans
      (RingEquiv.piCongrLeft (S' ·) hs'.equivFin.symm).symm).toRingHom.comp (algebraMap _ _)
  have hφ : Function.Injective φ := by
    dsimp only [RingHom.coe_comp, φ]
    refine (RingEquiv.injective _).comp (Localization.algebraMap_injective_of_span_eq_top _ hs)
  refine ⟨_, ⟨Nat.card s, (fun f ↦ ⟨S' f, hS' f⟩) ∘ hs'.equivFin.symm, φ.range⟩, ⟨?_⟩⟩
  exact (RingEquiv.ofBijective φ.rangeRestrict
    ⟨φ.injective_codRestrict.mpr hφ, φ.rangeRestrict_surjective⟩).toCommRingCatIso

end CommRingCat

