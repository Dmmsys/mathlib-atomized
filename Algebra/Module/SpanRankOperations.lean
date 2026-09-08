/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Span rank under operations

In this file we show how operations on submodules interact with `Submodule.spanRank`.

# Main Results

* `Submodule.spanRank_baseChange_le`: Base change doesn't increase the span rank.

* `TensorProduct.spanFinrank_top_eq_of_residueField`: For a finitely generated module over
  a local ring, the dimension of the base change to the residue field is equal to its span rank.

* `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`: The minimal number of
  generators of the unique maximal ideal is equal to the dimension of the cotangent space.

-/

public section

open IsLocalRing TensorProduct Submodule

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M)

/-
**Submodule.spanRank_baseChange_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.spanRank_baseChange_le : (N.baseChange A).spanRank <= N.spanRank
.lift
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.baseChange_span`：baseChange_span (s : Set M) : (span R s).base
Change A = span A (TensorProduct.mk R A M 1 '' s)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Submodule.spanRank_span_le_card`：spanRank_span_le_card (s : Set M) : (Su
bmodule.span R s).spanRank <= #s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.mk_image_le_lift`：mk_image_le_lift {α : Type u} {β : Type v} {f
 : α -> β} {s : Set α} : lift.{u} #(f '' s) <= lift.{v} #s
-/
lemma Submodule.spanRank_baseChange_le : (N.baseChange A).spanRank ≤ N.spanRank.lift := by
  obtain ⟨s, hs₁, hs₂⟩ := N.exists_span_set_card_eq_spanRank
  grw [← hs₁, ← hs₂, baseChange_span, spanRank_span_le_card]
  convert! Cardinal.mk_image_le_lift (f := TensorProduct.mk R A M 1) (s := s)
  · exact (Cardinal.lift_id' _).symm
  · exact Cardinal.lift_umax.symm
/-
**Submodule.FG.spanFinrank_baseChange_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.FG.spanFinrank_baseChange_le (fg : N.FG) : (N.baseChange A).span
Finrank <= N.spanFinrank
参数：fg : N.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.spanFinrank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R
 M), p.spanFinra…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用引理 `Submodule.spanRank_baseChange_le`：Submodule.spanRank_baseChange_le : (N.
baseChange A).spanRank <= N.spanRank.lift
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submodule.spanRank_finite_iff_fg`：spanRank_finite_iff_fg {p : Submodule 
R M} : p.spanRank < aleph0 ↔ p.FG
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
-/
lemma Submodule.FG.spanFinrank_baseChange_le (fg : N.FG) :
    (N.baseChange A).spanFinrank ≤ N.spanFinrank := by
  grw [spanFinrank, spanRank_baseChange_le, Cardinal.toNat_lift, spanFinrank]
  simp [Cardinal.lift_lt_aleph0, spanRank_finite_iff_fg.mpr fg]
/-
**TensorProduct.spanRank_top_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.spanRank_top_le : (⊤ : Submodule A (A otimes[R] N)).spanRank
 <= N.spanRank.lift
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.baseChange_top`：baseChange_top : (⊤ : Submodule R M).baseChang
e A = ⊤
· 使用引理 `Submodule.spanRank_top`：spanRank_top (p : Submodule R M) : (⊤ : Submodul
e R p).spanRank = p.spanRank
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Submodule.spanRank_baseChange_le`：Submodule.spanRank_baseChange_le : (N.
baseChange A).spanRank <= N.spanRank.lift
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma TensorProduct.spanRank_top_le : (⊤ : Submodule A (A ⊗[R] N)).spanRank ≤ N.spanRank.lift := by
  grw [← Submodule.baseChange_top, ← N.spanRank_top, spanRank_baseChange_le]
/-
**TensorProduct.spanFinrank_top_le_of_fg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.spanFinrank_top_le_of_fg (fg : N.FG) : (⊤ : Submodule A (A o
times[R] N)).spanFinrank <= N.spanFinrank
参数：fg : N.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.baseChange_top`：baseChange_top : (⊤ : Submodule R M).baseChang
e A = ⊤
· 使用引理 `Submodule.spanFinrank_top`：spanFinrank_top (p : Submodule R M) : (⊤ : Su
bmodule R p).spanFinrank = p.spanFinrank
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Submodule.FG.spanFinrank_baseChange_le`：Submodule.FG.spanFinrank_baseCha
nge_le (fg : N.FG) : (N.baseChange A).spanFinrank <= N.spanFinrank
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (N : Submodule R M), ⊤.F
G ↔ N.…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma TensorProduct.spanFinrank_top_le_of_fg (fg : N.FG) :
    (⊤ : Submodule A (A ⊗[R] N)).spanFinrank ≤ N.spanFinrank := by
  grw [← Submodule.baseChange_top, ← N.spanFinrank_top, (N.fg_top.mpr fg).spanFinrank_baseChange_le]

variable [IsLocalRing R]
local notation "𝓀" => ResidueField R
/-
**TensorProduct.spanFinrank_top_eq_of_residueField** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.spanFinrank_top_eq_of_residueField (fg : N.FG) : (⊤ : Submod
ule 𝓀 (𝓀 otimes[R] N)).spanFinrank = N.spanFinrank
参数：fg : N.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `TensorProduct.spanFinrank_top_le_of_fg`：TensorProduct.spanFinrank_top_le
_of_fg (fg : N.FG) : (⊤ : Submodule A (A otimes[R] N)).spanFinrank <= N.spanFinr
ank
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Cardinal.mk_lt_aleph0_iff`：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `TensorProduct.mk_surjective`：TensorProduct.mk_surjective (h : Function.S
urjective (algebraMap R S)) : Function.Surjective (TensorProduct.mk R S M 1)
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用引理 `Function.comp_surjInv`：comp_surjInv (hf : f.Surjective) : f ∘ f.surjInv 
hf = id
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `IsLocalRing.map_tensorProduct_mk_eq_top`：map_tensorProduct_mk_eq_top {N 
: Submodule R M} [Module.Finite R M] : N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N 
= ⊤
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.restrictScalars_span`：restrictScalars_span (hsur : Function.Su
rjective (algebraMap R A)) (X : Set M) : restrictScalars R (span A X) = span R X
· 使用定理 `Submodule.restrictScalars_eq_top_iff`：restrictScalars_eq_top_iff {p : Su
bmodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤
· 使用引理 `Submodule.spanFinrank_top`：spanFinrank_top (p : Submodule R M) : (⊤ : Su
bmodule R p).spanFinrank = p.spanFinrank
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Submodule.spanFinrank_span_le_ncard_of_finite`：spanFinrank_span_le_ncard
_of_finite {s : Set M} (hs : s.Finite) : (span R s).spanFinrank <= s.ncard
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Submodule.spanFinrank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R
 M), p.spanFinra…
· 使用定理 `Set.ncard_image_le`：ncard_image_le (hs : s.Finite
-/
lemma TensorProduct.spanFinrank_top_eq_of_residueField (fg : N.FG) :
    (⊤ : Submodule 𝓀 (𝓀 ⊗[R] N)).spanFinrank = N.spanFinrank := by
  let : Module.Finite R N := Module.Finite.iff_fg.mpr fg
  apply (TensorProduct.spanFinrank_top_le_of_fg N fg).antisymm
  obtain ⟨s, hs₁, hs₂⟩ := (⊤ : Submodule 𝓀 (𝓀 ⊗[R] N)).exists_span_set_card_eq_spanRank
  have hs₃ : s.Finite := Cardinal.mk_lt_aleph0_iff.mp (by simpa [hs₁] using Module.Finite.fg_top)
  let t := Function.surjInv (mk_surjective R N 𝓀 residue_surjective) '' s
  have ht₁ : mk R 𝓀 N 1 '' t = s := by rw [← Set.image_comp, Function.comp_surjInv, s.image_id]
  have ht₂ : span R t = ⊤ := by
    rwa [← restrictScalars_eq_top_iff R, restrictScalars_span _ _ (by exact residue_surjective),
      ← ht₁, ← map_span, map_tensorProduct_mk_eq_top] at hs₂
  grw [← N.spanFinrank_top, ← ht₂, spanFinrank_span_le_ncard_of_finite (hs₃.image _), spanFinrank,
    ← hs₁, Set.ncard_image_le hs₃]
  rfl

namespace IsLocalRing

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalRing.spanFinrank_eq_finrank_quotient** 是 Mathlib 中的一个引理，位于命名空间 `IsLocal
Ring`。
形式化陈述：spanFinrank_eq_finrank_quotient (N : Submodule R M) (fg : N.FG) : N.spanFi
nrank = Module.finrank (R ⧸ maximalIdeal R) (N ⧸ (maximalIdeal R) • (⊤ : Submodu
le R N))
参数：N : Submodule R M；fg : N.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Module.isTorsionBySet_quotient_ideal_smul`：isTorsionBySet_quotient_ideal
_smul : IsTorsionBySet R (M ⧸ I • (⊤ : Submodule R M)) I
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TensorProduct.spanFinrank_top_eq_of_residueField`：TensorProduct.spanFinr
ank_top_eq_of_residueField (fg : N.FG) : (⊤ : Submodule 𝓀 (𝓀 otimes[R] N)).spanF
inrank = N.spanFinrank
· 使用引理 `Module.finrank_eq_spanFinrank_of_free`：Module.finrank_eq_spanFinrank_of_
free [StrongRankCondition R] [Module.Free R M] : Module.finrank R M = (⊤ : Submo
dule R M).spanFinrank
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
lemma spanFinrank_eq_finrank_quotient (N : Submodule R M) (fg : N.FG) :
    N.spanFinrank =
      Module.finrank (R ⧸ maximalIdeal R) (N ⧸ (maximalIdeal R) • (⊤ : Submodule R N)) := by
  let : Module 𝓀 (N ⧸ maximalIdeal R • (⊤ : Submodule R N)) :=
    inferInstanceAs (Module (R ⧸ maximalIdeal R) _)
  let : IsScalarTower R 𝓀 (N ⧸ maximalIdeal R • (⊤ : Submodule R N)) :=
    inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) _)
  rw [← spanFinrank_top_eq_of_residueField N fg, ← Module.finrank_eq_spanFinrank_of_free]
  let e : 𝓀 ⊗[R] N ≃ₗ[𝓀] N ⧸ (maximalIdeal R) • (⊤ : Submodule R N) :=
    (quotTensorEquivQuotSMul N (maximalIdeal R)).extendScalarsOfSurjective residue_surjective
  exact e.finrank_eq
/-
**IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg** 是 Mathl
ib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg (fg : (maximalIde
al R).FG) : (maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (Cota
ngentSpace R)
参数：fg : (maximalIdeal R).FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalRing.spanFinrank_eq_finrank_quotient`：spanFinrank_eq_finrank_quot
ient (N : Submodule R M) (fg : N.FG) : N.spanFinrank = Module.finrank (R ⧸ maxim
alIdeal R) (N ⧸ (maximalIdeal R) …
-/
lemma spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg (fg : (maximalIdeal R).FG) :
    (maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R) :=
  spanFinrank_eq_finrank_quotient _ fg

variable (R) in
/-
**IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace** 是 Mathlib 中的一
个引理，位于命名空间 `IsLocalRing`。
形式化陈述：spanFinrank_maximalIdeal_eq_finrank_cotangentSpace [IsNoetherianRing R] : 
(maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg`：sp
anFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg (fg : (maximalIdeal R).FG
) : (maximalIdeal R).spanFinrank = Module.finrank (Residue…
· 使用引理 `Ideal.fg_of_isNoetherianRing`：Ideal.fg_of_isNoetherianRing {R : Type*} [
Semiring R] [IsNoetherianRing R] (I : Ideal R) : I.FG
-/
lemma spanFinrank_maximalIdeal_eq_finrank_cotangentSpace [IsNoetherianRing R] :
    (maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R) :=
  spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg (maximalIdeal R).fg_of_isNoetherianRing

end IsLocalRing

