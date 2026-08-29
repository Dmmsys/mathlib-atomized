/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Multilinear.TensorProduct

/-!
# Exterior product of alternating maps

In this file we define `AlternatingMap.domCoprod`
to be the exterior product of two alternating maps,
taking values in the tensor product of the codomains of the original maps.
-/

@[expose] public section

open TensorProduct

variable {ιa ιb : Type*} [Fintype ιa] [Fintype ιb]
variable {R' : Type*} {Mᵢ N₁ N₂ : Type*} [CommSemiring R'] [AddCommGroup N₁] [Module R' N₁]
  [AddCommGroup N₂] [Module R' N₂] [AddCommMonoid Mᵢ] [Module R' Mᵢ]

namespace Equiv.Perm

/--
Definition of `ModSumCongr` / `ModSumCongr` 的定义

English:
abbreviation ModSumCongr
  signature: (α β : Type*)
  body: _ ⧸ (Equiv.Perm.sumCongrHom α β).range

中文:
缩写 ModSumCongr
  签名: (α β : 类型)
  定义体: _ ⧸ (Equiv.Perm.sumCongrHom α β).range

Depends on / 依赖: Equiv.Perm.sumCongrHom, sumCongrHom
-/
abbrev ModSumCongr (α β : Type*) :=
  _ ⧸ (Equiv.Perm.sumCongrHom α β).range

end Equiv.Perm

namespace AlternatingMap

open Equiv

variable [DecidableEq ιa] [DecidableEq ιb]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `domCoprod.summand` / `domCoprod.summand` 的定义

English:
definition domCoprod.summand
  signature: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  body: Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ otimes N₂)).domDomCongr σ)
    fun σ₁ σ₂ H => by
    rw [QuotientGroup.leftRel_apply] at H
    obtain ⟨⟨sl, sr⟩, h⟩ := H
    ext v
    simp only [MultilinearMap.do

中文:
定义 domCoprod.summand
  签名: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  定义体: Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ otimes N₂)).domDomCongr σ)
    fun σ₁ σ₂ H => by
    rw [QuotientGroup.leftRel_apply] at H
    obtain ⟨⟨sl, sr⟩, h⟩ := H
    ext v
    simp only [MultilinearMap.do

Depends on / 依赖: Equiv.Perm.sign, MultilinearMap, MultilinearMap.domCoprod, MultilinearMap.domCoprod_apply, MultilinearMap.domDomCongr_apply, Perm.sumCongrHom, Quotient, Quotient.liftOn, QuotientGroup, QuotientGroup.leftRel_apply, _root_, _root_.smul_apply, coe_multilinearMap, domCoprod, domCoprod_apply, domDomCongr, domDomCongr_apply, h.symm, inv_mul_eq_iff_eq_mul, inv_mul_eq_iff_eq_mul.mp
-/
def domCoprod.summand (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
    (σ : Perm.ModSumCongr ιa ιb) : MultilinearMap R' (fun _ : ιa oplus ιb => Mᵢ) (N₁ otimes[R'] N₂) :=
  Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ otimes N₂)).domDomCongr σ)
    fun σ₁ σ₂ H => by
    rw [QuotientGroup.leftRel_apply] at H
    obtain ⟨⟨sl, sr⟩, h⟩ := H
    ext v
    simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      coe_multilinearMap, _root_.smul_apply]
    replace h := inv_mul_eq_iff_eq_mul.mp h.symm
    have : Equiv.Perm.sign (σ₁ * Perm.sumCongrHom _ _ (sl, sr))
      = Equiv.Perm.sign σ₁ * (Equiv.Perm.sign sl * Equiv.Perm.sign sr) := by simp
    rw [h]; rw [this]; rw [mul_smul]; rw [mul_smul]; rw [smul_left_cancel_iff]; rw [← TensorProduct.tmul_smul]; rw [TensorProduct.smul_tmul']; rw [a.map_congr_perm _ sl]; rw [b.map_congr_perm _ sr]
    simp only [Sum.map_inr, Perm.sumCongrHom_apply, Perm.sumCongr_apply, Sum.map_inl,
      Function.comp_def, Perm.coe_mul]

/--
theorem `domCoprod.summand_mk''` / 定理 `domCoprod.summand_mk''`

English:
theorem domCoprod.summand_mk''
  statement: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  proof: rfl

中文:
定理 domCoprod.summand_mk''
  结论: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  证明: rfl
-/
theorem domCoprod.summand_mk'' (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
    (σ : Equiv.Perm (ιa oplus ιb)) :
    domCoprod.summand a b (Quotient.mk'' σ) =
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ otimes N₂)).domDomCongr
          σ :=
  rfl

/--
theorem `domCoprod.summand_add_swap_smul_eq_zero` / 定理 `domCoprod.summand_add_swap_smul_eq_zero`

English:
theorem domCoprod.summand_add_swap_smul_eq_zero
  statement: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁)
  proof: by
  induction σ using Quotient.inductionOn'
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    domCoprod.summand]
  rw [smul_eq_mul]; rw [Perm.sign_mul]; rw [Perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Perm.coe_mul,
 

中文:
定理 domCoprod.summand_add_swap_smul_eq_zero
  结论: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁)
  证明: by
  induction σ using Quotient.inductionOn'
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    domCoprod.summand]
  rw [smul_eq_mul]; rw [Perm.sign_mul]; rw [Perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Perm.coe_mul,
 

Depends on / 依赖: Equiv.apply_swap_eq_self, Function, Function.comp_apply, MulAction, MulAction.Quotient.smul_mk, MultilinearMap, MultilinearMap.domCoprod_apply, MultilinearMap.domDomCongr_apply, Perm.coe_mul, Perm.sign_mul, Perm.sign_swap, Quotient, Quotient.inductionOn, Quotient.liftOn, Quotient.map, Units.neg_smul, _root_, _root_.neg_apply, _root_.smul_apply, add_neg_cancel
-/
theorem domCoprod.summand_add_swap_smul_eq_zero (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : ιa oplus ιb -> Mᵢ}
    {i j : ιa oplus ιb} (hv : v i = v j) (hij : i != j) :
    domCoprod.summand a b σ v + domCoprod.summand a b (swap i j • σ) v = 0 := by
  induction σ using Quotient.inductionOn'
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    domCoprod.summand]
  rw [smul_eq_mul]; rw [Perm.sign_mul]; rw [Perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Perm.coe_mul,
    _root_.smul_apply, _root_.neg_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply]
  convert! add_neg_cancel (G := N₁ otimes[R'] N₂) _ using 6 <;>
    · ext k
      rw [Equiv.apply_swap_eq_self hv]

/--
theorem `domCoprod.summand_eq_zero_of_smul_invariant` / 定理 `domCoprod.summand_eq_zero_of_smul_invariant`

English:
theorem domCoprod.summand_eq_zero_of_smul_invariant
  statement: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁)
  proof: by
  induction σ using Quotient.inductionOn' with | _ σ
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', _root_.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, domCoprod.summand]
  intro hσ
  obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.

中文:
定理 domCoprod.summand_eq_zero_of_smul_invariant
  结论: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁)
  证明: by
  induction σ using Quotient.inductionOn' with | _ σ
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', _root_.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, domCoprod.summand]
  intro hσ
  obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.

Depends on / 依赖: MultilinearMap, MultilinearMap.domCoprod_apply, MultilinearMap.domDomCongr_apply, Perm.inv_eq_iff_eq, Quotient, Quotient.exact, Quotient.inductionOn, Quotient.liftOn, Quotient.map, QuotientGroup, QuotientGroup.leftRel_apply.mp, _root_, _root_.smul_apply, domCoprod, domCoprod.summand, domCoprod_apply, domDomCongr_apply, inductionOn, inv_eq_iff_eq, leftRel_apply
-/
theorem domCoprod.summand_eq_zero_of_smul_invariant (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : ιa oplus ιb -> Mᵢ}
    {i j : ιa oplus ιb} (hv : v i = v j) (hij : i != j) :
    swap i j • σ = σ -> domCoprod.summand a b σ v = 0 := by
  induction σ using Quotient.inductionOn' with | _ σ
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', _root_.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, domCoprod.summand]
  intro hσ
  obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
  rcases hi : σ⁻¹ i with i' | i' <;> rcases hj : σ⁻¹ j with j' | j' <;>
    rw [Perm.inv_eq_iff_eq] at hi hj <;> subst hi hj
  -- the term pairs with and cancels another term
  case inl.inr => simpa using Equiv.congr_fun hσ (Sum.inl i')
  case inr.inl => simpa using Equiv.congr_fun hσ (Sum.inr i')
  -- the term does not pair but is zero
  case inl.inl =>
    suffices (a fun i => v (σ (Sum.inl i))) = 0 by simp_all
    exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
  case inr.inr =>
    suffices (b fun i => v (σ (Sum.inr i))) = 0 by simp_all
    exact b.map_eq_zero_of_eq _ hv fun hij' => hij (hij' ▸ rfl)

/-- Like `MultilinearMap.domCoprod`, but ensures the result is also alternating.

Note that this is usually defined (for instance, as used in Proposition 22.24 in [Gallier2011Notes])
over integer indices `ιa = Fin n` and `ιb = Fin m`, as
$$
(f \wedge g)(u_1, \ldots, u_{m+n}) =
  \sum_{\operatorname{shuffle}(m, n)} \operatorname{sign}(\sigma)
    f(u_{\sigma(1)}, \ldots, u_{\sigma(m)}) g(u_{\sigma(m+1)}, \ldots, u_{\sigma(m+n)}),
$$
where $\operatorname{shuffle}(m, n)$ consists of all permutations of $[1, m+n]$ such that
$\sigma(1) < \cdots < \sigma(m)$ and $\sigma(m+1) < \cdots < \sigma(m+n)$.

Here, we generalize this by replacing:
* the product in the sum with a tensor product
* the filtering of $[1, m+n]$ to shuffles with an isomorphic quotient
* the additions in the subscripts of $\sigma$ with an index of type `Sum`

The specialized version can be obtained by combining this definition with `finSumFinEquiv` and
`LinearMap.mul'`.
-/
@[simps]
/--
Definition of `domCoprod` / `domCoprod` 的定义

English:
definition domCoprod
  signature: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  body: { ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ with
    toFun := fun v => (⇑(∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      rw [_root_.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
     

中文:
定义 domCoprod
  签名: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  定义体: { ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ with
    toFun := fun v => (⇑(∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      rw [_root_.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
     

Depends on / 依赖: Equiv.swap, Equiv.swap_smul_involutive, Finset, Finset.mem_univ, Finset.sum_involution, ModSumCongr, Perm.ModSumCongr, _root_, _root_.sum_apply, domCoprod, domCoprod.summand, domCoprod.summand_add_swap_smul_eq_zero, domCoprod.summand_eq_zero_of_smul_invariant, map_eq_zero_of_eq, mem_univ, sum_apply, sum_involution, summand, summand_add_swap_smul_eq_zero, summand_eq_zero_of_smul_invariant
-/
def domCoprod (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂) :
    Mᵢ [⋀^ιa oplus ιb]->ₗ[R'] (N₁ otimes[R'] N₂) :=
  { ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ with
    toFun := fun v => (⇑(∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      rw [_root_.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => domCoprod.summand_add_swap_smul_eq_zero a b σ hv hij)
          (fun σ _ => mt <| domCoprod.summand_eq_zero_of_smul_invariant a b σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.swap_smul_involutive i j σ }

/--
theorem `domCoprod_coe` / 定理 `domCoprod_coe`

English:
theorem domCoprod_coe
  given: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  proof: MultilinearMap.ext fun _ => rfl

中文:
定理 domCoprod_coe
  条件: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  证明: MultilinearMap.ext fun _ => rfl

Depends on / 依赖: MultilinearMap, MultilinearMap.ext
-/
theorem domCoprod_coe (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂) :
    (↑(a.domCoprod b) : MultilinearMap R' (fun _ => Mᵢ) _) =
      ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ :=
  MultilinearMap.ext fun _ => rfl

/--
Definition of `domCoprod'` / `domCoprod'` 的定义

English:
definition domCoprod'
  signature: :
  body: TensorProduct.lift by
    refine
      LinearMap.mk₂ R' domCoprod (fun m₁ m₂ n => ?_) (fun c m n => ?_) (fun m n₁ n₂ => ?_)
        fun c m n => ?_ <;>
    · ext
      simp only [domCoprod_apply, add_apply, smul_apply, ← Finset.sum_add_distrib,
        Finset.smul_sum, _root_.sum_apply, domCoprod.su

中文:
定义 domCoprod'
  签名: :
  定义体: TensorProduct.lift by
    refine
      LinearMap.mk₂ R' domCoprod (fun m₁ m₂ n => ?_) (fun c m n => ?_) (fun m n₁ n₂ => ?_)
        fun c m n => ?_ <;>
    · ext
      simp only [domCoprod_apply, add_apply, smul_apply, ← Finset.sum_add_distrib,
        Finset.smul_sum, _root_.sum_apply, domCoprod.su

Depends on / 依赖: Finset, Finset.smul_sum, Finset.sum_add_distrib, LinearMap, LinearMap.mk, MultilinearMap, MultilinearMap.domCoprod, Quotient, Quotient.inductionOn, Quotient.liftOn, TensorP, TensorProduct, TensorProduct.add_tmul, TensorProduct.lift, TensorProduct.smul_tmul, _apply, _root_, _root_.smul_apply, _root_.sum_apply, add_apply
-/
def domCoprod' :
    (Mᵢ [⋀^ιa]->ₗ[R'] N₁) otimes[R'] (Mᵢ [⋀^ιb]->ₗ[R'] N₂) ->ₗ[R']
      (Mᵢ [⋀^ιa oplus ιb]->ₗ[R'] (N₁ otimes[R'] N₂)) :=
TensorProduct.lift by
    refine
      LinearMap.mk₂ R' domCoprod (fun m₁ m₂ n => ?_) (fun c m n => ?_) (fun m n₁ n₂ => ?_)
        fun c m n => ?_ <;>
    · ext
      simp only [domCoprod_apply, add_apply, smul_apply, ← Finset.sum_add_distrib,
        Finset.smul_sum, _root_.sum_apply, domCoprod.summand]
      congr
      ext σ
      induction σ using Quotient.inductionOn'
      simp only [Quotient.liftOn'_mk'', coe_add, coe_smul, _root_.smul_apply,
        ← MultilinearMap.domCoprod'_apply]
      simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul', TensorProduct.tmul_add,
        TensorProduct.tmul_smul, map_add, map_smul]
      first | rw [← smul_add] | rw [smul_comm]
      rfl

@[simp]
/--
theorem `domCoprod'_apply` / 定理 `domCoprod'_apply`

English:
theorem domCoprod'_apply
  given: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  proof: rfl

中文:
定理 domCoprod'_apply
  条件: (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂)
  证明: rfl
-/
theorem domCoprod'_apply (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂) :
    domCoprod' (a otimesₜ[R'] b) = domCoprod a b :=
  rfl

end AlternatingMap

open Equiv

/--
theorem `MultilinearMap.domCoprod_alternization_coe` / 定理 `MultilinearMap.domCoprod_alternization_coe`

English:
theorem MultilinearMap.domCoprod_alternization_coe
  statement: [DecidableEq ιa] [DecidableEq ιb]
  proof: by
  simp_rw [← MultilinearMap.domCoprod'_apply, MultilinearMap.alternatization_coe]
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, _root_.map_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rfl

中文:
定理 MultilinearMap.domCoprod_alternization_coe
  结论: [DecidableEq ιa] [DecidableEq ιb]
  证明: by
  simp_rw [← MultilinearMap.domCoprod'_apply, MultilinearMap.alternatization_coe]
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, _root_.map_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rfl

Depends on / 依赖: MultilinearMap, MultilinearMap.alternatization_coe, MultilinearMap.domCoprod, TensorProduct, TensorProduct.smul_tmul, TensorProduct.sum_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_sum, TopologicalSpace, _apply, _root_, _root_.map_sum, alternatization_coe, domCoprod, map_sum, simp_rw, smul_tmul, standardBorel_of_polish, sum_tmul, tmul_smul
-/
theorem MultilinearMap.domCoprod_alternization_coe [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.domCoprod (MultilinearMap.alternatization a)
      (MultilinearMap.alternatization b) =
      ∑ σa : Perm ιa, ∑ σb : Perm ιb,
        Equiv.Perm.sign σa • Equiv.Perm.sign σb •
          MultilinearMap.domCoprod (a.domDomCongr σa) (b.domDomCongr σb) := by
  simp_rw [← MultilinearMap.domCoprod'_apply, MultilinearMap.alternatization_coe]
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, _root_.map_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rfl

open AlternatingMap

set_option backward.isDefEq.respectTransparency.types false in
open Perm in
/--
theorem `MultilinearMap.domCoprod_alternization` / 定理 `MultilinearMap.domCoprod_alternization`

English:
theorem MultilinearMap.domCoprod_alternization
  statement: [DecidableEq ιa] [DecidableEq ιb]
  proof: by
  apply coe_multilinearMap_injective
  rw [domCoprod_coe]; rw [MultilinearMap.alternatization_coe]; rw [Finset.sum_partition (QuotientGroup.leftRel (Perm.sumCongrHom ιa ιb).range)]
  congr 1
  ext1 σ
  induction σ using Quotient.inductionOn' with
  | h σ =>
  set f := sumCongrHom ιa ιb
  calc
   

中文:
定理 MultilinearMap.domCoprod_alternization
  结论: [DecidableEq ιa] [DecidableEq ιb]
  证明: by
  apply coe_multilinearMap_injective
  rw [domCoprod_coe]; rw [MultilinearMap.alternatization_coe]; rw [Finset.sum_partition (QuotientGroup.leftRel (Perm.sumCongrHom ιa ιb).range)]
  congr 1
  ext1 σ
  induction σ using Quotient.inductionOn' with
  | h σ =>
  set f := sumCongrHom ιa ιb
  calc
   

Depends on / 依赖: DiscreteMeasurableSpace, Finset, Finset.sum_partition, MultilinearMap, MultilinearMap.alternatization_coe, Perm.sumCongrHom, Quotient, Quotient.eq, Quotient.inductionOn, QuotientGroup, QuotientGroup.leftRel, QuotientGroup.leftRel_apply, a.domCoprod, alternatization_coe, coe_multilinearMap_injective, domCoprod, domCoprod_coe, domDomCongr, f.range, inductionOn
-/
theorem MultilinearMap.domCoprod_alternization [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.alternatization (MultilinearMap.domCoprod a b) =
      a.alternatization.domCoprod (MultilinearMap.alternatization b) := by
  apply coe_multilinearMap_injective
  rw [domCoprod_coe]; rw [MultilinearMap.alternatization_coe]; rw [Finset.sum_partition (QuotientGroup.leftRel (Perm.sumCongrHom ιa ιb).range)]
  congr 1
  ext1 σ
  induction σ using Quotient.inductionOn' with
  | h σ =>
  set f := sumCongrHom ιa ιb
  calc
    ∑ τ in _, sign τ • domDomCongr τ (a.domCoprod b) =
        ∑ τ in {τ | τ⁻¹ * σ in f.range}, sign τ • domDomCongr τ (a.domCoprod b) := by
      simp [QuotientGroup.leftRel_apply, f, Quotient.eq]
    _ = ∑ τ in {τ | τ⁻¹ in f.range}, sign (σ * τ) • domDomCongr (σ * τ) (a.domCoprod b) := by
      conv_lhs => rw [← Finset.map_univ_equiv (Equiv.mulLeft σ), Finset.filter_map, Finset.sum_map]
      simp [-MonoidHom.mem_range]
    _ = ∑ τ, sign (σ * f τ) • domDomCongr (σ * f τ) (a.domCoprod b) := by
      simp_rw [f, Subgroup.inv_mem_iff, MonoidHom.mem_range, Finset.univ_filter_exists,
        Finset.sum_image sumCongrHom_injective.injOn]
    _ = ∑ τ : Perm ιa × Perm ιb,
         sign σ • (domDomCongrEquiv σ) (sign τ.1 • sign τ.2 •
           (domDomCongr τ.1 a).domCoprod (domDomCongr τ.2 b)) := by
      simp [f, domDomCongr_mul, domCoprod_domDomCongr_sumCongr, mul_smul]
    _ = domCoprod.summand (alternatization a) (alternatization b) (Quotient.mk'' σ) := by
      simp [domCoprod.summand_mk'', domCoprod_alternization_coe, ← domDomCongrEquiv_apply,
        Finset.smul_sum, ← Finset.sum_product']

/--
theorem `MultilinearMap.domCoprod_alternization_eq` / 定理 `MultilinearMap.domCoprod_alternization_eq`

English:
theorem MultilinearMap.domCoprod_alternization_eq
  statement: [DecidableEq ιa] [DecidableEq ιb]
  proof: by
  rw [MultilinearMap.domCoprod_alternization]; rw [coe_alternatization]; rw [coe_alternatization]; rw [mul_smul]; rw [← AlternatingMap.domCoprod'_apply]; rw [← AlternatingMap.domCoprod'_apply]; rw [← TensorProduct.smul_tmul']; rw [TensorProduct.tmul_smul]; rw [LinearMap.map_smul_of_tower Alternat

中文:
定理 MultilinearMap.domCoprod_alternization_eq
  结论: [DecidableEq ιa] [DecidableEq ιb]
  证明: by
  rw [MultilinearMap.domCoprod_alternization]; rw [coe_alternatization]; rw [coe_alternatization]; rw [mul_smul]; rw [← AlternatingMap.domCoprod'_apply]; rw [← AlternatingMap.domCoprod'_apply]; rw [← TensorProduct.smul_tmul']; rw [TensorProduct.tmul_smul]; rw [LinearMap.map_smul_of_tower Alternat

Depends on / 依赖: AlternatingMap, AlternatingMap.domCoprod, LinearMap, LinearMap.map_smul_of_tower, MultilinearMap, MultilinearMap.domCoprod_alternization, StandardBorelSpace, TensorProduct, TensorProduct.smul_tmul, TensorProduct.tmul_smul, _apply, coe_alternatization, countablyGenerated_of_standardBorel, domCoprod, domCoprod_alternization, map_smul_of_tower, mul_smul, smul_tmul, tmul_smul
-/
theorem MultilinearMap.domCoprod_alternization_eq [DecidableEq ιa] [DecidableEq ιb]
    (a : Mᵢ [⋀^ιa]->ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]->ₗ[R'] N₂) :
    MultilinearMap.alternatization
      (MultilinearMap.domCoprod a b : MultilinearMap R' (fun _ : ιa oplus ιb => Mᵢ) (N₁ otimes N₂)) =
      ((Fintype.card ιa).factorial * (Fintype.card ιb).factorial) • a.domCoprod b := by
  rw [MultilinearMap.domCoprod_alternization]; rw [coe_alternatization]; rw [coe_alternatization]; rw [mul_smul]; rw [← AlternatingMap.domCoprod'_apply]; rw [← AlternatingMap.domCoprod'_apply]; rw [← TensorProduct.smul_tmul']; rw [TensorProduct.tmul_smul]; rw [LinearMap.map_smul_of_tower AlternatingMap.domCoprod']; rw [LinearMap.map_smul_of_tower AlternatingMap.domCoprod']
