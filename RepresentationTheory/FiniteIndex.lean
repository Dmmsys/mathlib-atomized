/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# (Co)induced representations of a finite index subgroup

Given a commutative ring `k`, a finite index subgroup `S ≤ G`, and a `k`-linear `S`-representation
`A`, this file defines an isomorphism $Ind_S^G(A) ≅ Coind_S^G(A)$. Given `g : G` and `a : A`, the
forward map sends `⟦g ⊗ₜ[k] a⟧` to the function `G → A` supported at `sg` by `ρ(s)(a)` for `s : S`
and which is 0 elsewhere. Meanwhile, the inverse sends `f : G → A` to `∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for
`1 ≤ i ≤ n`, where `g₁, ..., gₙ` is a set of right coset representatives of `S`.

## Main definitions

* `Rep.indCoindIso A`: An isomorphism `Ind_S^G(A) ≅ Coind_S^G(A)` for a finite index subgroup
  `S ≤ G` and a `k`-linear `S`-representation `A`.
* `Rep.indCoindNatIso k S`: A natural isomorphism between the functors `Ind_S^G` and `Coind_S^G`.

TODO : Fix the universe constraint
-/

@[expose] public section

universe t w u u' v v'

namespace Rep

open CategoryTheory Finsupp TensorProduct Representation

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel (QuotientGroup.rightRel S)] (A : Rep.{w} k S)

/--
Definition of `indToCoindAux` / `indToCoindAux` 的定义

English:
definition indToCoindAux
  signature: (g : G)
  body: LinearMap.pi (fun g₁ => if h : (QuotientGroup.rightRel S).r g₁ g then
    A.ρ ⟨g₁ * g⁻¹, by rcases h with ⟨s, rfl⟩; exact mul_inv_cancel_right s.1 g ▸ s.2⟩ else 0)

中文:
定义 indToCoindAux
  签名: (g : G)
  定义体: LinearMap.pi (fun g₁ => if h : (QuotientGroup.rightRel S).r g₁ g then
    A.ρ ⟨g₁ * g⁻¹, by rcases h with ⟨s, rfl⟩; exact mul_inv_cancel_right s.1 g ▸ s.2⟩ else 0)

Depends on / 依赖: LinearMap, LinearMap.pi, QuotientGroup, QuotientGroup.rightRel, mul_inv_cancel_right, rightRel
-/
noncomputable def indToCoindAux (g : G) : A ->ₗ[k] (G -> A) :=
  LinearMap.pi (fun g₁ => if h : (QuotientGroup.rightRel S).r g₁ g then
    A.ρ ⟨g₁ * g⁻¹, by rcases h with ⟨s, rfl⟩; exact mul_inv_cancel_right s.1 g ▸ s.2⟩ else 0)

variable {A}

@[simp]
/--
lemma `indToCoindAux_self` / 引理 `indToCoindAux_self`

English:
lemma indToCoindAux_self
  given: (g : G) (a : A)
  proof: by
  rw [indToCoindAux]; rw [LinearMap.pi_apply]; rw [dif_pos]
  · simp [← S.1.one_def]
  · rfl

中文:
引理 indToCoindAux_self
  条件: (g : G) (a : A)
  证明: by
  rw [indToCoindAux]; rw [LinearMap.pi_apply]; rw [dif_pos]
  · simp [← S.1.one_def]
  · rfl

Depends on / 依赖: LinearMap, LinearMap.pi_apply, dif_pos, indToCoindAux, one_def, pi_apply
-/
lemma indToCoindAux_self (g : G) (a : A) :
    indToCoindAux A g a g = a := by
  rw [indToCoindAux]; rw [LinearMap.pi_apply]; rw [dif_pos]
  · simp [← S.1.one_def]
  · rfl

/--
lemma `indToCoindAux_of_not_rel` / 引理 `indToCoindAux_of_not_rel`

English:
lemma indToCoindAux_of_not_rel
  given: (g g₁ : G) (a : A) (h : ¬(QuotientGroup.rightRel S).r g₁ g)
  proof: by
  simp [indToCoindAux, dif_neg h]

@[simp]

中文:
引理 indToCoindAux_of_not_rel
  条件: (g g₁ : G) (a : A) (h : ¬(商群.rightRel S).r g₁ g)
  证明: by
  simp [indToCoindAux, dif_neg h]

@[simp]

Depends on / 依赖: dif_neg, indToCoindAux
-/
lemma indToCoindAux_of_not_rel (g g₁ : G) (a : A) (h : ¬(QuotientGroup.rightRel S).r g₁ g) :
    indToCoindAux A g a g₁ = 0 := by
  simp [indToCoindAux, dif_neg h]

@[simp]
/--
lemma `indToCoindAux_mul_snd` / 引理 `indToCoindAux_mul_snd`

English:
lemma indToCoindAux_mul_snd
  given: (g g₁ : G) (a : A) (s : S)
  proof: by
  rcases em ((QuotientGroup.rightRel S).r g₁ g) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s * s₁]; rw [mul_assoc ..⟩]; rw [dif_pos ⟨s₁]; rw [rfl⟩]
    simp [S.1.smul_def, mul_assoc, ← S.1.mul_def]
  · rw [indToCoindAux_of_not_rel _ _ _ h, indToCoindAux_of_not_rel, map_zero]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s⁻¹ * s₁, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]

中文:
引理 indToCoindAux_mul_snd
  条件: (g g₁ : G) (a : A) (s : S)
  证明: by
  rcases em ((QuotientGroup.rightRel S).r g₁ g) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s * s₁]; rw [mul_assoc ..⟩]; rw [dif_pos ⟨s₁]; rw [rfl⟩]
    simp [S.1.smul_def, mul_assoc, ← S.1.mul_def]
  · rw [indToCoindAux_of_not_rel _ _ _ h, indToCoindAux_of_not_rel, map_zero]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s⁻¹ * s₁, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]

Depends on / 依赖: LinearMap, LinearMap.pi_apply, QuotientGroup, QuotientGroup.rightRel, dif_pos, indToCoindAux, indToCoindAux_of_not_rel, map_zero, mul_assoc, mul_def, pi_apply, rightRel, smul_def
-/
lemma indToCoindAux_mul_snd (g g₁ : G) (a : A) (s : S) :
    indToCoindAux A g a (s * g₁) = A.ρ s (indToCoindAux A g a g₁) := by
  rcases em ((QuotientGroup.rightRel S).r g₁ g) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s * s₁]; rw [mul_assoc ..⟩]; rw [dif_pos ⟨s₁]; rw [rfl⟩]
    simp [S.1.smul_def, mul_assoc, ← S.1.mul_def]
  · rw [indToCoindAux_of_not_rel _ _ _ h, indToCoindAux_of_not_rel, map_zero]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s⁻¹ * s₁, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]
/--
lemma `indToCoindAux_mul_fst` / 引理 `indToCoindAux_mul_fst`

English:
lemma indToCoindAux_mul_fst
  given: (g₁ g₂ : G) (a : A) (s : S)
  proof: by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s₁ * s⁻¹]; rw [by simp [S.1.smul_def]; rw [smul_eq_mul]; rw [mul_assoc]⟩, dif_pos ⟨s₁, rfl⟩,
      ← Module.End.mul_apply, ← map_mul]
    congr
    simp [Subtype.ext_iff, S.1.smul_def, mul_assoc]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s₁ * s, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]

中文:
引理 indToCoindAux_mul_fst
  条件: (g₁ g₂ : G) (a : A) (s : S)
  证明: by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s₁ * s⁻¹]; rw [by simp [S.1.smul_def]; rw [smul_eq_mul]; rw [mul_assoc]⟩, dif_pos ⟨s₁, rfl⟩,
      ← Module.End.mul_apply, ← map_mul]
    congr
    simp [Subtype.ext_iff, S.1.smul_def, mul_assoc]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s₁ * s, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]

Depends on / 依赖: LinearMap, LinearMap.pi_apply, Module, Module.End.mul_apply, QuotientGroup, QuotientGroup.rightRel, Subtype, Subtype.ext_iff, dif_pos, ext_iff, indToCoindAux, indToCoindAux_of_not_rel, map_mul, mul_apply, mul_assoc, pi_apply, rightRel, smul_def, smul_eq_mul
-/
lemma indToCoindAux_mul_fst (g₁ g₂ : G) (a : A) (s : S) :
     indToCoindAux A (s * g₁) (A.ρ s a) g₂ = indToCoindAux A g₁ a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s₁ * s⁻¹]; rw [by simp [S.1.smul_def]; rw [smul_eq_mul]; rw [mul_assoc]⟩, dif_pos ⟨s₁, rfl⟩,
      ← Module.End.mul_apply, ← map_mul]
    congr
    simp [Subtype.ext_iff, S.1.smul_def, mul_assoc]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s₁ * s, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]
/--
lemma `indToCoindAux_snd_mul_inv` / 引理 `indToCoindAux_snd_mul_inv`

English:
lemma indToCoindAux_snd_mul_inv
  given: (g₁ g₂ g₃ : G) (a : A)
  proof: by
  rcases em ((QuotientGroup.rightRel S).r (g₂ * g₃⁻¹) g₁) with ⟨s, hs⟩ | h
  · simp [S.1.smul_def, mul_assoc, ← eq_mul_inv_iff_mul_eq.1 hs]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s, hs⟩ => ⟨s, by simpa [S.1.smul_def, eq_mul_inv_iff_mul_eq, mul_assoc]⟩) h

@[simp]

中文:
引理 indToCoindAux_snd_mul_inv
  条件: (g₁ g₂ g₃ : G) (a : A)
  证明: by
  rcases em ((QuotientGroup.rightRel S).r (g₂ * g₃⁻¹) g₁) with ⟨s, hs⟩ | h
  · simp [S.1.smul_def, mul_assoc, ← eq_mul_inv_iff_mul_eq.1 hs]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s, hs⟩ => ⟨s, by simpa [S.1.smul_def, eq_mul_inv_iff_mul_eq, mul_assoc]⟩) h

@[simp]

Depends on / 依赖: QuotientGroup, QuotientGroup.rightRel, eq_mul_inv_iff_mul_eq, indToCoindAux_of_not_rel, mul_assoc, rightRel, smul_def
-/
lemma indToCoindAux_snd_mul_inv (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux A g₁ a (g₂ * g₃⁻¹) = indToCoindAux A (g₁ * g₃) a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r (g₂ * g₃⁻¹) g₁) with ⟨s, hs⟩ | h
  · simp [S.1.smul_def, mul_assoc, ← eq_mul_inv_iff_mul_eq.1 hs]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s, hs⟩ => ⟨s, by simpa [S.1.smul_def, eq_mul_inv_iff_mul_eq, mul_assoc]⟩) h

@[simp]
/--
lemma `indToCoindAux_fst_mul_inv` / 引理 `indToCoindAux_fst_mul_inv`

English:
lemma indToCoindAux_fst_mul_inv
  given: (g₁ g₂ g₃ : G) (a : A)
  proof: by
  simpa using (indToCoindAux_snd_mul_inv g₁ g₃ g₂⁻¹ a).symm

中文:
引理 indToCoindAux_fst_mul_inv
  条件: (g₁ g₂ g₃ : G) (a : A)
  证明: by
  simpa using (indToCoindAux_snd_mul_inv g₁ g₃ g₂⁻¹ a).symm

Depends on / 依赖: indToCoindAux_snd_mul_inv
-/
lemma indToCoindAux_fst_mul_inv (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux A (g₁ * g₂⁻¹) a g₃ = indToCoindAux A g₁ a (g₃ * g₂) := by
  simpa using (indToCoindAux_snd_mul_inv g₁ g₃ g₂⁻¹ a).symm

/--
lemma `indToCoindAux_comm` / 引理 `indToCoindAux_comm`

English:
lemma indToCoindAux_comm
  given: {A B : Rep k S} (f : A ⟶ B) (g₁ g₂ : G) (a : A)
  proof: by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s, rfl⟩ | h
  · simp [S.1.smul_def, hom_comm_apply]
  · simp [indToCoindAux_of_not_rel (h := h)]

中文:
引理 indToCoindAux_comm
  条件: {A B : Rep k S} (f : A ⟶ B) (g₁ g₂ : G) (a : A)
  证明: by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s, rfl⟩ | h
  · simp [S.1.smul_def, hom_comm_apply]
  · simp [indToCoindAux_of_not_rel (h := h)]

Depends on / 依赖: QuotientGroup, QuotientGroup.rightRel, hom_comm_apply, indToCoindAux_of_not_rel, rightRel, smul_def
-/
lemma indToCoindAux_comm {A B : Rep k S} (f : A ⟶ B) (g₁ g₂ : G) (a : A) :
    indToCoindAux B g₁ (f.hom a) g₂ = f.hom (indToCoindAux A g₁ a g₂) := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s, rfl⟩ | h
  · simp [S.1.smul_def, hom_comm_apply]
  · simp [indToCoindAux_of_not_rel (h := h)]

set_option backward.isDefEq.respectTransparency.types false in
variable (A) in
/--
Definition of `indToCoind` / `indToCoind` 的定义

English:
abbreviation indToCoind
  signature: :
  body: Representation.Coinvariants.lift _ (TensorProduct.lift <| (linearCombination _ fun g =>
    LinearMap.codRestrict _ (indToCoindAux A g) fun _ _ _ => by simp) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun _ => by ext; simp

中文:
缩写 indToCoind
  签名: :
  定义体: Representation.Coinvariants.lift _ (TensorProduct.lift <| (linearCombination _ fun g =>
    LinearMap.codRestrict _ (indToCoindAux A g) fun _ _ _ => by simp) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun _ => by ext; simp

Depends on / 依赖: Coinvariants, LinearMap, LinearMap.codRestrict, MonoidAlgebra, MonoidAlgebra.coeffLinearEquiv, Representation, Representation.Coinvariants.lift, TensorProduct, TensorProduct.lift, codRestrict, coeffLinearEquiv, indToCoindAux, linearCombination, toLinearMap
-/
noncomputable abbrev indToCoind :
    ind S.subtype A ->ₗ[k] coind S.subtype A :=
  Representation.Coinvariants.lift _ (TensorProduct.lift <| (linearCombination _ fun g =>
    LinearMap.codRestrict _ (indToCoindAux A g) fun _ _ _ => by simp) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun _ => by ext; simp

variable [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (A) in
/-- Let `S ≤ G` be a finite index subgroup, `g₁, ..., gₙ` a set of right coset representatives of
`S`, and `A` a `k`-linear `S`-representation. This is the `k`-linear map
`Coind_S^G(A) →ₗ[k] Ind_S^G(A)` sending `f : G → A` to `∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for `1 ≤ i ≤ n`. -/
@[simps]
/--
Definition of `coindToInd` / `coindToInd` 的定义

English:
definition coindToInd
  signature: : coind S.subtype A ->ₗ[k] ind S.subtype A where
  body: ∑ g : Quotient (QuotientGroup.rightRel S), Quotient.liftOn g (fun g =>
    IndV.mk S.subtype _ g (f.1 g)) fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
(Submodule.Quotient.eq _).2 Coinvariants.mem_ker_of_eq s
(.single g₂ 1 otimesₜ[k] f.1 g₂) _ by have := f.2 s g₂; simp_all
  map_add' _ _ := by simpa [← Finset.sum_add_distrib, TensorProduct.tmul_add] using
      Finset.sum_congr rfl fun z _ => Quotient.inductionOn z fun _ => by simp
  map_smul' _ _ := by simpa [Finset.smul_sum] using Finset.sum_congr rfl fun z _ =>
    Quotient.inductionOn z fun _ => by simp

omit [DecidableRel (QuotientGroup.rightRel S)] in

中文:
定义 coindToInd
  签名: : coind S.subtype A ->ₗ[k] ind S.subtype A where
  定义体: ∑ g : Quotient (QuotientGroup.rightRel S), Quotient.liftOn g (fun g =>
    IndV.mk S.subtype _ g (f.1 g)) fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
(Submodule.Quotient.eq _).2 Coinvariants.mem_ker_of_eq s
(.single g₂ 1 otimesₜ[k] f.1 g₂) _ by have := f.2 s g₂; simp_all
  map_add' _ _ := by simpa [← Finset.sum_add_distrib, TensorProduct.tmul_add] using
      Finset.sum_congr rfl fun z _ => Quotient.inductionOn z fun _ => by simp
  map_smul' _ _ := by simpa [Finset.smul_sum] using Finset.sum_congr rfl fun z _ =>
    Quotient.inductionOn z fun _ => by simp

omit [DecidableRel (QuotientGroup.rightRel S)] in

Depends on / 依赖: Quotient, Quotient.liftOn, QuotientGroup, QuotientGroup.rightRel, liftOn, rightRel
-/
noncomputable def coindToInd : coind S.subtype A ->ₗ[k] ind S.subtype A where
  toFun f := ∑ g : Quotient (QuotientGroup.rightRel S), Quotient.liftOn g (fun g =>
    IndV.mk S.subtype _ g (f.1 g)) fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
(Submodule.Quotient.eq _).2 Coinvariants.mem_ker_of_eq s
(.single g₂ 1 otimesₜ[k] f.1 g₂) _ by have := f.2 s g₂; simp_all
  map_add' _ _ := by simpa [← Finset.sum_add_distrib, TensorProduct.tmul_add] using
      Finset.sum_congr rfl fun z _ => Quotient.inductionOn z fun _ => by simp
  map_smul' _ _ := by simpa [Finset.smul_sum] using Finset.sum_congr rfl fun z _ =>
    Quotient.inductionOn z fun _ => by simp

omit [DecidableRel (QuotientGroup.rightRel S)] in
/--
lemma `coindToInd_of_support_subset_orbit` / 引理 `coindToInd_of_support_subset_orbit`

English:
lemma coindToInd_of_support_subset_orbit
  statement: (g : G) (f : coind S.subtype A)
  proof: by
  rw [coindToInd_apply]; rw [Finset.sum_eq_single ⟦g⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    have : f.1 b = 0 := by
      simp_all only [Function.support_subset_iff, ne_eq, Quotient.eq]
      contrapose! hx
      use b, hx, hb
    simp_all
  · simp

中文:
引理 coindToInd_of_support_subset_orbit
  结论: (g : G) (f : coind S.subtype A)
  证明: by
  rw [coindToInd_apply]; rw [Finset.sum_eq_single ⟦g⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    have : f.1 b = 0 := by
      simp_all only [Function.support_subset_iff, ne_eq, Quotient.eq]
      contrapose! hx
      use b, hx, hb
    simp_all
  · simp

Depends on / 依赖: Finset, Finset.sum_eq_single, Function, Function.support_subset_iff, Quotient, Quotient.eq, Quotient.inductionOn, coindToInd_apply, contrapose, inductionOn, ne_eq, sum_eq_single, support_subset_iff
-/
lemma coindToInd_of_support_subset_orbit (g : G) (f : coind S.subtype A)
    (hx : f.1.support subseteq MulAction.orbit S g) :
    coindToInd A f = IndV.mk S.subtype _ g (f.1 g) := by
  rw [coindToInd_apply]; rw [Finset.sum_eq_single ⟦g⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    have : f.1 b = 0 := by
      simp_all only [Function.support_subset_iff, ne_eq, Quotient.eq]
      contrapose! hx
      use b, hx, hb
    simp_all
  · simp

variable (A)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `coindToInd_indToCoind` / 引理 `coindToInd_indToCoind`

English:
lemma coindToInd_indToCoind
  statement: A.indToCoind ∘ₗ A.coindToInd = LinearMap.id
  proof: by
  ext g a
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  conv_lhs => rw [coindToInd_apply]
  simp only [map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single ⟦a⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    simpa using indToCoindAux_of_not_rel b a (g.1 b) (mt Quotient.sound hb.symm)
  · simp

中文:
引理 coindToInd_indToCoind
  结论: A.indToCoind ∘ₗ A.coindToInd = 线性映射.id
  证明: by
  ext g a
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  conv_lhs => rw [coindToInd_apply]
  simp only [map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single ⟦a⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    simpa using indToCoindAux_of_not_rel b a (g.1 b) (mt Quotient.sound hb.symm)
  · simp

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.coe_finsetSum, Finset, Finset.sum_apply, Finset.sum_eq_single, Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, LinearMap.id_coe, Quotient, Quotient.inductionOn, Quotient.sound, coe_comp, coe_finsetSum, coindToInd_apply, comp_apply, conv_lhs, hb.symm, id_coe
-/
lemma coindToInd_indToCoind : A.indToCoind ∘ₗ A.coindToInd = LinearMap.id := by
  ext g a
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  conv_lhs => rw [coindToInd_apply]
  simp only [map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single ⟦a⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    simpa using indToCoindAux_of_not_rel b a (g.1 b) (mt Quotient.sound hb.symm)
  · simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `indToCoind_coindToInd` / 引理 `indToCoind_coindToInd`

English:
lemma indToCoind_coindToInd
  statement: A.coindToInd ∘ₗ A.indToCoind = LinearMap.id
  proof: by
  ext g a
  simp only [LinearMap.comp_apply, AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.id_apply]
  rw [coindToInd_of_support_subset_orbit g]
  · simp
  · intro x hx
    contrapose hx
    simpa using indToCoindAux_of_not_rel g x a hx

中文:
引理 indToCoind_coindToInd
  结论: A.coindToInd ∘ₗ A.indToCoind = 线性映射.id
  证明: by
  ext g a
  simp only [LinearMap.comp_apply, AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.id_apply]
  rw [coindToInd_of_support_subset_orbit g]
  · simp
  · intro x hx
    contrapose hx
    simpa using indToCoindAux_of_not_rel g x a hx

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.curry_apply, LinearMap, LinearMap.coe_restrictScalars, LinearMap.comp_apply, LinearMap.id_apply, TensorProduct, TensorProduct.curry_apply, coe_restrictScalars, coindToInd_of_support_subset_orbit, comp_apply, contrapose, curry_apply, id_apply, indToCoindAux_of_not_rel
-/
lemma indToCoind_coindToInd : A.coindToInd ∘ₗ A.indToCoind = LinearMap.id := by
  ext g a
  simp only [LinearMap.comp_apply, AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.id_apply]
  rw [coindToInd_of_support_subset_orbit g]
  · simp
  · intro x hx
    contrapose hx
    simpa using indToCoindAux_of_not_rel g x a hx

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `S ≤ G` be a finite index subgroup, `g₁, ..., gₙ` a set of right coset representatives of
`S`, and `A` a `k`-linear `S`-representation. This is an isomorphism `Ind_S^G(A) ≅ Coind_S^G(A)`.
The forward map sends `(⟦g ⊗ₜ[k] a⟧, sg) ↦ ρ(s)(a)`, and the inverse sends `f : G → A` to
`∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for `1 ≤ i ≤ n`. -/
@[simps! hom_hom_toLinearMap inv_hom_toLinearMap]
/--
Definition of `indCoindIso` / `indCoindIso` 的定义

English:
definition indCoindIso
  signature: (A : Rep.{max w u} k S)
  body: mkIso (.mk (.ofLinearMap (indToCoind A) (coindToInd A)
    (coindToInd_indToCoind A) (indToCoind_coindToInd A)) <| fun g => by ext; simp)

中文:
定义 indCoindIso
  签名: (A : Rep.{最大值 w u} k S)
  定义体: mkIso (.mk (.ofLinearMap (indToCoind A) (coindToInd A)
    (coindToInd_indToCoind A) (indToCoind_coindToInd A)) <| fun g => by ext; simp)

Depends on / 依赖: coindToInd, coindToInd_indToCoind, indToCoind, indToCoind_coindToInd, ofLinearMap
-/
noncomputable def indCoindIso (A : Rep.{max w u} k S) :
    ind S.subtype A ≅ coind S.subtype A :=
  mkIso (.mk (.ofLinearMap (indToCoind A) (coindToInd A)
    (coindToInd_indToCoind A) (indToCoind_coindToInd A)) <| fun g => by ext; simp)

variable (k S)

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a finite index subgroup `S ≤ G`, this is a natural isomorphism between the `Ind_S^G` and
`Coind_G^S` functors `Rep k S ⥤ Rep k G`. -/
@[implicit_reducible, simps! hom_app inv_app]
/--
Definition of `indCoindNatIso` / `indCoindNatIso` 的定义

English:
definition indCoindNatIso
  signature: :
  body: NatIso.ofComponents (fun (A : Rep k S) => indCoindIso A) fun f => by
    simp only [indFunctor_obj, coindFunctor_obj];
    ext g1 x g2
    simp [indToCoind, indMap, indToCoindAux_comm]

中文:
定义 indCoind自然数Iso
  签名: :
  定义体: NatIso.ofComponents (fun (A : Rep k S) => indCoindIso A) fun f => by
    simp only [indFunctor_obj, coindFunctor_obj];
    ext g1 x g2
    simp [indToCoind, indMap, indToCoindAux_comm]

Depends on / 依赖: NatIso, NatIso.ofComponents, coindFunctor_obj, indCoindIso, indFunctor_obj, indMap, indToCoind, indToCoindAux_comm, ofComponents, of_restrictScalars
-/
noncomputable def indCoindNatIso :
    indFunctor k S.subtype ≅ coindFunctor.{max w u} k S.subtype :=
  NatIso.ofComponents (fun (A : Rep k S) => indCoindIso A) fun f => by
    simp only [indFunctor_obj, coindFunctor_obj];
    ext g1 x g2
    simp [indToCoind, indMap, indToCoindAux_comm]

/--
Definition of `resIndAdjunction` / `resIndAdjunction` 的定义

English:
definition resIndAdjunction
  signature: :
  body: (resCoindAdjunction.{max w u v} k S.subtype).ofNatIsoRight (indCoindNatIso.{max w u v} k S).symm

omit [DecidableRel (QuotientGroup.rightRel S)] in
@[instance] -- Note: we must use `@[instance] theorem` here due to [lean4#5595](https://github.com/leanprover/lean4/issues/5595).

中文:
定义 resIndAdjunction
  签名: :
  定义体: (resCoindAdjunction.{max w u v} k S.subtype).ofNatIsoRight (indCoindNatIso.{max w u v} k S).symm

omit [DecidableRel (QuotientGroup.rightRel S)] in
@[instance] -- Note: we must use `@[instance] theorem` here due to [lean4#5595](https://github.com/leanprover/lean4/issues/5595).

Depends on / 依赖: S.subtype, indCoindNatIso, ofNatIsoRight, resCoindAdjunction, subtype
-/
noncomputable def resIndAdjunction :
    resFunctor.{max w u v} S.subtype ⊣ indFunctor.{max w u v} k S.subtype :=
  (resCoindAdjunction.{max w u v} k S.subtype).ofNatIsoRight (indCoindNatIso.{max w u v} k S).symm

omit [DecidableRel (QuotientGroup.rightRel S)] in
@[instance] -- Note: we must use `@[instance] theorem` here due to [lean4#5595](https://github.com/leanprover/lean4/issues/5595).
/--
theorem `instIsRightAdjointSubtypeMemSubgroupIndFunctorSubtype` / 定理 `instIsRightAdjointSubtypeMemSubgroupIndFunctorSubtype`

English:
theorem instIsRightAdjointSubtypeMemSubgroupIndFunctorSubtype
  proof: open scoped Classical in (resIndAdjunction k S).isRightAdjoint

中文:
定理 instIsRightAdjointSubtypeMemSubgroupIndFunctorSubtype
  证明: open scoped Classical in (resIndAdjunction k S).isRightAdjoint

Depends on / 依赖: Classical, isRightAdjoint, resIndAdjunction, scoped
-/
theorem instIsRightAdjointSubtypeMemSubgroupIndFunctorSubtype :
    (indFunctor.{max w u v} k S.subtype).IsRightAdjoint :=
  open scoped Classical in (resIndAdjunction k S).isRightAdjoint

variable {k S}

@[simp]
/--
lemma `resIndAdjunction_counit_app` / 引理 `resIndAdjunction_counit_app`

English:
lemma resIndAdjunction_counit_app
  given: (A : Rep.{max w u v} k S)
  proof: rfl

@[simp]

中文:
引理 resIndAdjunction_counit_app
  条件: (A : Rep.{最大值 w u v} k S)
  证明: rfl

@[simp]
-/
lemma resIndAdjunction_counit_app (A : Rep.{max w u v} k S) :
    (resIndAdjunction.{w, u, v} k S).counit.app A =
      (resFunctor S.subtype).map (indCoindIso.{max w (max u v)} A).hom ≫
      (resCoindAdjunction.{max w u} k S.subtype).counit.app A := rfl

@[simp]
/--
lemma `resIndAdjunction_unit_app` / 引理 `resIndAdjunction_unit_app`

English:
lemma resIndAdjunction_unit_app
  given: (B : Rep.{max w u v} k G)
  proof: rfl

中文:
引理 resIndAdjunction_unit_app
  条件: (B : Rep.{最大值 w u v} k G)
  证明: rfl
-/
lemma resIndAdjunction_unit_app (B : Rep.{max w u v} k G) :
    (resIndAdjunction.{w, u, v} k S).unit.app B =
      (resCoindAdjunction.{max w u} k S.subtype).unit.app B ≫
      (indCoindIso.{max w (max u v)} (res S.subtype B)).inv := rfl

/--
lemma `resIndAdjunction_homEquiv_apply` / 引理 `resIndAdjunction_homEquiv_apply`

English:
lemma resIndAdjunction_homEquiv_apply
  statement: (A : Rep.{max w u v} k S)
  proof: by
  rw [resIndAdjunction]; rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  simp [resCoindHomEquiv]

中文:
引理 resIndAdjunction_homEquiv_apply
  结论: (A : Rep.{最大值 w u v} k S)
  证明: by
  rw [resIndAdjunction]; rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  simp [resCoindHomEquiv]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_ofNatIsoRight_apply, homEquiv_ofNatIsoRight_apply, resCoindHomEquiv, resIndAdjunction
-/
lemma resIndAdjunction_homEquiv_apply (A : Rep.{max w u v} k S)
    {B : Rep.{max w u v} k G} (f : res S.subtype B ⟶ A) :
    (resIndAdjunction.{w, u, v} k S).homEquiv _ _ f =
      resCoindHomEquiv.{max w u v} S.subtype B A f ≫ (indCoindIso.{max w u v} A).inv := by
  rw [resIndAdjunction]; rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  simp [resCoindHomEquiv]

/--
lemma `resIndAdjunction_homEquiv_symm_apply` / 引理 `resIndAdjunction_homEquiv_symm_apply`

English:
lemma resIndAdjunction_homEquiv_symm_apply
  statement: (A : Rep.{max w u v} k S)
  proof: rfl

中文:
引理 resIndAdjunction_homEquiv_symm_apply
  结论: (A : Rep.{最大值 w u v} k S)
  证明: rfl
-/
lemma resIndAdjunction_homEquiv_symm_apply (A : Rep.{max w u v} k S)
    {B : Rep.{max w u v} k G}
    (f : B ⟶ (indFunctor k S.subtype).obj A) :
    ((resIndAdjunction k S).homEquiv _ _).symm f =
      (resCoindHomEquiv.{max w u v} S.subtype B A).symm (f ≫ (indCoindIso.{max w u v} A).hom) :=
  rfl

variable (k S) in
/--
Definition of `coindResAdjunction` / `coindResAdjunction` 的定义

English:
definition coindResAdjunction
  signature: :
  body: (indResAdjunction k S.subtype).ofNatIsoLeft (indCoindNatIso.{max w u v} k S)

omit [DecidableRel (QuotientGroup.rightRel S)] in
@[instance] -- Note: we must use `@[instance] theorem` here due to [lean4#5595](https://github.com/leanprover/lean4/issues/5595).

中文:
定义 coindResAdjunction
  签名: :
  定义体: (indResAdjunction k S.subtype).ofNatIsoLeft (indCoindNatIso.{max w u v} k S)

omit [DecidableRel (QuotientGroup.rightRel S)] in
@[instance] -- Note: we must use `@[instance] theorem` here due to [lean4#5595](https://github.com/leanprover/lean4/issues/5595).

Depends on / 依赖: S.subtype, indCoindNatIso, indResAdjunction, ofNatIsoLeft, subtype
-/
noncomputable def coindResAdjunction :
    coindFunctor k S.subtype ⊣ resFunctor.{max w u v} S.subtype :=
  (indResAdjunction k S.subtype).ofNatIsoLeft (indCoindNatIso.{max w u v} k S)

omit [DecidableRel (QuotientGroup.rightRel S)] in
@[instance] -- Note: we must use `@[instance] theorem` here due to [lean4#5595](https://github.com/leanprover/lean4/issues/5595).
/--
theorem `instIsLeftAdjointSubtypeMemSubgroupCoindFunctorSubtype` / 定理 `instIsLeftAdjointSubtypeMemSubgroupCoindFunctorSubtype`

English:
theorem instIsLeftAdjointSubtypeMemSubgroupCoindFunctorSubtype
  proof: open scoped Classical in (coindResAdjunction k S).isLeftAdjoint

@[simp]

中文:
定理 instIsLeftAdjointSubtypeMemSubgroupCoindFunctorSubtype
  证明: open scoped Classical in (coindResAdjunction k S).isLeftAdjoint

@[simp]

Depends on / 依赖: Classical, coindResAdjunction, isLeftAdjoint, scoped
-/
theorem instIsLeftAdjointSubtypeMemSubgroupCoindFunctorSubtype :
    (coindFunctor.{max w u v} k S.subtype).IsLeftAdjoint :=
  open scoped Classical in (coindResAdjunction k S).isLeftAdjoint

@[simp]
/--
lemma `coindResAdjunction_counit_app` / 引理 `coindResAdjunction_counit_app`

English:
lemma coindResAdjunction_counit_app
  given: (B : Rep.{max w u v} k G)
  proof: rfl

中文:
引理 coindResAdjunction_counit_app
  条件: (B : Rep.{最大值 w u v} k G)
  证明: rfl
-/
lemma coindResAdjunction_counit_app (B : Rep.{max w u v} k G) :
    (coindResAdjunction.{w, u, v} k S).counit.app B =
      (indCoindIso.{max w u v} (res S.subtype B)).inv ≫
      (indResAdjunction k S.subtype).counit.app B :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `coindResAdjunction_unit_app` / 引理 `coindResAdjunction_unit_app`

English:
lemma coindResAdjunction_unit_app
  given: (A : Rep.{max w u v} k S)
  proof: by
  ext
  simp [coindResAdjunction]

中文:
引理 coindResAdjunction_unit_app
  条件: (A : Rep.{最大值 w u v} k S)
  证明: by
  ext
  simp [coindResAdjunction]

Depends on / 依赖: coindResAdjunction
-/
lemma coindResAdjunction_unit_app (A : Rep.{max w u v} k S) :
    (coindResAdjunction k S).unit.app A = (indResAdjunction k S.subtype).unit.app A ≫
      (resFunctor S.subtype).map (indCoindIso.{max w u v} A).hom := by
  ext
  simp [coindResAdjunction]

/--
lemma `coindResAdjunction_homEquiv_apply` / 引理 `coindResAdjunction_homEquiv_apply`

English:
lemma coindResAdjunction_homEquiv_apply
  statement: (A : Rep.{max w u v} k S)
  proof: by
  rfl

中文:
引理 coindResAdjunction_homEquiv_apply
  结论: (A : Rep.{最大值 w u v} k S)
  证明: by
  rfl
-/
lemma coindResAdjunction_homEquiv_apply (A : Rep.{max w u v} k S)
    {B : Rep k G} (f : coind S.subtype A ⟶ B) :
    (coindResAdjunction k S).homEquiv _ _ f =
      indResHomEquiv S.subtype A B ((indCoindIso.{max w u v} A).hom ≫ f) := by
  rfl

/--
lemma `coindResAdjunction_homEquiv_symm_apply` / 引理 `coindResAdjunction_homEquiv_symm_apply`

English:
lemma coindResAdjunction_homEquiv_symm_apply
  statement: (A : Rep.{max w u v} k S)
  proof: by
  simp [coindResAdjunction, indResHomEquiv, indResAdjunction,
    Adjunction.homEquiv_ofNatIsoLeft_symm_apply _]

中文:
引理 coindResAdjunction_homEquiv_symm_apply
  结论: (A : Rep.{最大值 w u v} k S)
  证明: by
  simp [coindResAdjunction, indResHomEquiv, indResAdjunction,
    Adjunction.homEquiv_ofNatIsoLeft_symm_apply _]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply, coindResAdjunction, homEquiv_ofNatIsoLeft_symm_apply, indResAdjunction, indResHomEquiv
-/
lemma coindResAdjunction_homEquiv_symm_apply (A : Rep.{max w u v} k S)
    {B : Rep k G} (f : A ⟶ res S.subtype B) :
    ((coindResAdjunction.{max w u v} k S).homEquiv _ _).symm f =
      (indCoindIso.{max w u v} A).inv ≫ (indResHomEquiv S.subtype A B).symm f := by
  simp [coindResAdjunction, indResHomEquiv, indResAdjunction,
    Adjunction.homEquiv_ofNatIsoLeft_symm_apply _]

end Rep
