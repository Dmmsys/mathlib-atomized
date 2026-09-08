/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.Geometry.Convex.Cone.TensorProduct
public import Mathlib.Topology.Algebra.Module.TopDualPairing

/-!
# Tensor Products of Pointed Cones

This file proves that the minimal and maximal tensor products of pointed cones in
finite-dimensional real vector spaces are equal when one cone is simplicial and generating
and the other is proper (pointed and closed).

Finite-dimensionality of the proper cone ambient space is by explicit declaration and is required
for the `topDualPairing_isContPerfPair` instance (in `Topology.Algebra.Module.TopDualPairing`).
The simplicial and generating cone ambient space is implicitly finite dimensional by the
simplicial and generating assumption.

This file uses `topDualPairing` (the canonical pairing of a vector space and its topological dual)
to avoid explicit topology assumptions on `Module.Dual`.

The proof relies on the following result:

* **Bipolar theorem** (`ProperCone.dual_dual_flip`): The double dual of a proper cone is itself.

This requires:
- Local convexity and Hausdorff separation (for Hahn-Banach)
- A continuous perfect pairing between the module and its dual.

## Main results

* `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_left`:
  If `C₁` is simplicial and generating and `C₂` is proper, then the minimal and
  maximal tensor products are equal.

* `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_right`:
  If `C₁` is a proper cone and `C₂` is a simplicial and generating cone, then their minimal
  and maximal tensor products are equal.

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]
-/

public section

/-! ### Equality of minimal and maximal tensor products -/

namespace PointedCone

section BasisCoordDual

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

open Module

/-- If a pointed cone `C` is contained in the conic hull of a basis `b`, then the coordinate
functionals of `b` lie in the dual cone of `C`. -/
/-
**PointedCone.basis_coord_mem_dual** 是 Mathlib 中的一个引理，位于命名空间 `PointedCone`。
形式化陈述：basis_coord_mem_dual {ι : Type*} (b : Basis ι R M) (C : PointedCone R M) (
hC : (C : Set M) subseteq (hull R (Set.range b) : Set M)) (i : ι) : b.coord i in
 dual (Dual.eval R M) (C : Set M)
参数：b : Basis ι R M；C : PointedCone R M；hC : (C : Set M) subseteq (hull R (Set.ra
nge b) : Set M)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PointedCone.dual_le_dual`：∀ {R : Type u_1} [inst : CommSemiring R] [inst
_1 : PartialOrder R] [inst_2 : IsOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid M] [i…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PointedCone.dual_hull`：dual_hull (s : Set M) : dual p (hull R s) = dual 
p s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_nonneg`：∀ {α : Type u_1} [inst : Zero α] {p : Prop} [inst_1 : Decida
ble p] {a b : α} [inst_2 : LE α],   0 ≤ a → 0 ≤ b → 0 ≤ if p then a else b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If a pointed cone `C` is contained in the conic hull of a basis `b`, then the co
ordinate
functionals of `b` lie in the dual cone of `C`.
-/
lemma basis_coord_mem_dual {ι : Type*} (b : Basis ι R M) (C : PointedCone R M)
    (hC : (C : Set M) ⊆ (hull R (Set.range b) : Set M)) (i : ι) :
    b.coord i ∈ dual (Dual.eval R M) (C : Set M) := by
  classical
  refine dual_le_dual hC ?_
  simp [Finsupp.single_apply, ite_nonneg zero_le_one le_rfl]

end BasisCoordDual

section MainTheorems

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
variable [FiniteDimensional ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

open TensorProduct Module

set_option backward.isDefEq.respectTransparency false in
/-- If `C₁` is a simplicial and generating cone and `C₂` is a proper cone, then their minimal
and maximal tensor products are equal. -/
/-
**PointedCone.minTensorProduct_eq_max_of_simplicial_generating_left** 是 Mathlib 
中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：minTensorProduct_eq_max_of_simplicial_generating_left (C₁ : PointedCone Re
al E) (C₂ : ProperCone Real F) (h₁_simp : C₁.IsSimplicial) (h₁_gen : Submodule.s
pan Real (C₁ : Set E) = ⊤) : minTensorProduct C₁ C₂.toPointedCone = maxTensorPro
duct C₁ C₂.toPointedCone
参数：C₁ : PointedCone Real E；C₂ : ProperCone Real F；h₁_simp : C₁.IsSimplicial；h₁_g
en : Submodule.span Real (C₁ : Set E) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PointedCone.mem_hull_set`：mem_hull_set {s : Set E} : x in hull R s ↔ exi
sts c : E ->₀ R, ↑c.support subseteq s ∧ (forall y, 0 <= c y) ∧ c.sum (fun m r =
> r • m) = x
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `PointedCone.basis_coord_mem_dual`：basis_coord_mem_dual {ι : Type*} (b : 
Basis ι R M) (C : PointedCone R M) (hC : (C : Set M) subseteq (hull R (Set.range
 b) : Set M)) (i : ι) …
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `PointedCone.minTensorProduct_le_maxTensorProduct`：minTensorProduct_le_ma
xTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) : minTensorProduct 
C₁ C₂ <= maxTensorProduct C₁ C₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用引理 `TensorProduct.equivFinsuppOfBasisLeft_symm_apply`：TensorProduct.equivFin
suppOfBasisLeft_symm_apply (b : ι ->₀ N) : (TensorProduct.equivFinsuppOfBasisLef
t ℬ).symm b = b.sum fun i n => ℬ i oti…
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
If `C₁` is a simplicial and generating cone and `C₂` is a proper cone, then thei
r minimal
and maximal tensor products are equal.
-/
theorem minTensorProduct_eq_max_of_simplicial_generating_left (C₁ : PointedCone ℝ E)
    (C₂ : ProperCone ℝ F) (h₁_simp : C₁.IsSimplicial) (h₁_gen : Submodule.span ℝ (C₁ : Set E) = ⊤) :
    minTensorProduct C₁ C₂.toPointedCone = maxTensorProduct C₁ C₂.toPointedCone := by
  classical
  obtain ⟨s, hs_fin, hs_lin, hs_span⟩ := h₁_simp
  have : Fintype s := hs_fin.fintype
  -- The conic hull (R≥0-span) is contained in the linear span (ℝ-span)
  have hull_sub_span : (hull ℝ s : Set E) ⊆ Submodule.span ℝ s := by
    intro x hx
    rw [SetLike.mem_coe, PointedCone.mem_hull_set] at hx
    obtain ⟨c, hc_supp, _, hc_sum⟩ := hx
    exact hc_sum ▸ Submodule.sum_mem _ fun m hm =>
      Submodule.smul_mem _ _ (Submodule.subset_span (hc_supp hm))
  -- Extract basis from `C₁.IsSimplicial` + generating
  let b := Basis.mk hs_lin <| by
    simpa only [id_eq, Subtype.range_coe] using!
      h₁_gen ▸ hs_span ▸ Submodule.span_le.mpr hull_sub_span
  -- Dual basis elements are in C₁*
  have h_coord_dual : ∀ i, b.coord i ∈ dual (Dual.eval ℝ E) C₁ :=
    basis_coord_mem_dual _ _ (hs_span ▸ (Submodule.span_mono <| by simp [b]))
  -- Reduce to proving z ∈ max → z ∈ min
  apply le_antisymm (minTensorProduct_le_maxTensorProduct C₁ C₂.toPointedCone)
  intro z hz
  -- Express z using basis: z = ∑ b_i ⊗ y_i
  rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply z,
    TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]
  -- Show z ∈ min by showing b_i ∈ C₁ and y_i ∈ C₂
  refine Submodule.sum_mem _ fun i _ => tmul_mem_minTensorProduct ?_ ?_
  · simpa only [b, Basis.coe_mk] using! (hs_span ▸ subset_hull) i.prop
  · simp only [equivFinsuppOfBasisLeft_apply]
    rw [← ProperCone.dual_dual_flip (topDualPairing ℝ F) C₂]
    intro f (hf : (f : F →ₗ[ℝ] ℝ) ∈ dual (Dual.eval ℝ F) (C₂ : Set F))
    simp only [mem_maxTensorProduct] at hz
    have h_nonneg := hz (b.coord i) (h_coord_dual i) (f : F →ₗ[ℝ] ℝ) hf
    have h_eq : dualDistrib ℝ E F ((b.coord i) ⊗ₜ[ℝ] (f : F →ₗ[ℝ] ℝ)) =
        (f : F →ₗ[ℝ] ℝ) ∘ₗ (TensorProduct.lid ℝ F) ∘ₗ (b.coord i).rTensor F := by
      ext; simp [mul_comm]
    simpa only [h_eq, LinearMap.comp_apply, LinearEquiv.coe_coe] using! h_nonneg

/-- If `C₁` is a proper cone and `C₂` is a simplicial and generating cone, then their minimal
and maximal tensor products are equal. -/
/-
**PointedCone.minTensorProduct_eq_max_of_simplicial_generating_right** 是 Mathlib
 中的一个定理，位于命名空间 `PointedCone`。
形式化陈述：minTensorProduct_eq_max_of_simplicial_generating_right (C₁ : ProperCone Re
al F) (C₂ : PointedCone Real E) (h₂_simp : C₂.IsSimplicial) (h₂_gen : Submodule.
span Real (C₂ : Set E) = ⊤) : minTensorProduct C₁.toPointedCone C₂ = maxTensorPr
oduct C₁.toPointedCone C₂
参数：C₁ : ProperCone Real F；C₂ : PointedCone Real E；h₂_simp : C₂.IsSimplicial；h₂_g
en : Submodule.span Real (C₂ : Set E) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PointedCone.minTensorProduct_comm`：minTensorProduct_comm : (minTensorPro
duct C₁ C₂).map (TensorProduct.comm R G H) = minTensorProduct C₂ C₁
· 使用定理 `PointedCone.maxTensorProduct_comm`：maxTensorProduct_comm : (maxTensorPro
duct C₁ C₂).map (TensorProduct.comm R G H) = maxTensorProduct C₂ C₁
· 使用定理 `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_left`：minTe
nsorProduct_eq_max_of_simplicial_generating_left (C₁ : PointedCone Real E) (C₂ :
 ProperCone Real F) (h₁_simp : C₁.IsSimplicial) (h₁_gen…

--- 原说明 ---
If `C₁` is a proper cone and `C₂` is a simplicial and generating cone, then thei
r minimal
and maximal tensor products are equal.
-/
theorem minTensorProduct_eq_max_of_simplicial_generating_right (C₁ : ProperCone ℝ F)
    (C₂ : PointedCone ℝ E) (h₂_simp : C₂.IsSimplicial)
    (h₂_gen : Submodule.span ℝ (C₂ : Set E) = ⊤) :
    minTensorProduct C₁.toPointedCone C₂ = maxTensorProduct C₁.toPointedCone C₂ := by
  rw [← minTensorProduct_comm, ← maxTensorProduct_comm,
    minTensorProduct_eq_max_of_simplicial_generating_left C₂ C₁ h₂_simp h₂_gen]

end MainTheorems

end PointedCone

