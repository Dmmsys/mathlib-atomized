/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree homology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file contains specialised API for
the cycles and group homology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.
In `Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean`, we define the `n`th group
homology of `A` to be the homology of a complex `inhomogeneousChains A`, whose objects are
`(Fin n →₀ G) → A`; this is unnecessarily unwieldy in low degree.

Given an additive abelian group `A` with an appropriate scalar action of `G`, we provide support
for turning a finsupp `f : G →₀ A` satisfying the 1-cycle identity into an element of the
`cycles₁` of the representation on `A` corresponding to the scalar action. We also do this for
0-boundaries, 1-boundaries, 2-cycles and 2-boundaries.

The file also contains an identification between the definitions in
`Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean`, `groupHomology.cycles A n`, and
the `cyclesₙ` in this file for `n = 1, 2`, as well as an isomorphism
`groupHomology.cycles A 0 ≅ A.V`.
Moreover, we provide API for the natural maps `cyclesₙ A → Hn A` for `n = 1, 2`.

We show that when the representation on `A` is trivial, `H₁(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A`.

## Main definitions

* `groupHomology.H0Iso A`: isomorphism between `H₀(G, A)` and the coinvariants `A_G` of the
  `G`-representation on `A`.
* `groupHomology.H1π A`: epimorphism from the 1-cycles (i.e. `Z₁(G, A) := Ker(d₀ : (G →₀ A) → A`)
  to `H₁(G, A)`.
* `groupHomology.H2π A`: epimorphism from the 2-cycles
  (i.e. `Z₂(G, A) := Ker(d₁ : (G² →₀ A) → (G →₀ A)`) to `H₂(G, A)`.
* `groupHomology.H1AddEquivOfIsTrivial`: an isomorphism `H₁(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A` when the
  representation on `A` is trivial.

-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits Representation Rep Finsupp

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

namespace groupHomology

section Chains

/--
Definition of `chainsIso₀` / `chainsIso₀` 的定义

English:
definition chainsIso₀
  signature: : (inhomogeneousChains A).X 0 ≅ ModuleCat.of k A.V
  body: (uniqueLinearEquiv _ _ default).toModuleIso

中文:
定义 chainsIso₀
  签名: : (inhomogeneousChains A).X 0 ≅ 模范畴.of k A.V
  定义体: (uniqueLinearEquiv _ _ default).toModuleIso

Depends on / 依赖: toModuleIso, uniqueLinearEquiv
-/
def chainsIso₀ : (inhomogeneousChains A).X 0 ≅ ModuleCat.of k A.V :=
  (uniqueLinearEquiv _ _ default).toModuleIso

/--
Definition of `chainsIso₁` / `chainsIso₁` 的定义

English:
definition chainsIso₁
  signature: : (inhomogeneousChains A).X 1 ≅ ModuleCat.of k (G ->₀ A)
  body: (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)).toModuleIso

中文:
定义 chainsIso₁
  签名: : (inhomogeneousChains A).X 1 ≅ 模范畴.of k (G ->₀ A)
  定义体: (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)).toModuleIso

Depends on / 依赖: Equiv.funUnique, Finsupp, Finsupp.domLCongr, domLCongr, funUnique, toModuleIso
-/
def chainsIso₁ : (inhomogeneousChains A).X 1 ≅ ModuleCat.of k (G ->₀ A) :=
  (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)).toModuleIso

/--
Definition of `chainsIso₂` / `chainsIso₂` 的定义

English:
definition chainsIso₂
  signature: : (inhomogeneousChains A).X 2 ≅ ModuleCat.of k (G × G ->₀ A)
  body: (Finsupp.domLCongr (piFinTwoEquiv fun _ => G)).toModuleIso

中文:
定义 chainsIso₂
  签名: : (inhomogeneousChains A).X 2 ≅ 模范畴.of k (G × G ->₀ A)
  定义体: (Finsupp.domLCongr (piFinTwoEquiv fun _ => G)).toModuleIso

Depends on / 依赖: Finsupp, Finsupp.domLCongr, domLCongr, piFinTwoEquiv, toModuleIso
-/
def chainsIso₂ : (inhomogeneousChains A).X 2 ≅ ModuleCat.of k (G × G ->₀ A) :=
  (Finsupp.domLCongr (piFinTwoEquiv fun _ => G)).toModuleIso

/--
Definition of `chainsIso₃` / `chainsIso₃` 的定义

English:
definition chainsIso₃
  signature: : (inhomogeneousChains A).X 3 ≅ ModuleCat.of k (G × G × G ->₀ A)
  body: (Finsupp.domLCongr ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso

中文:
定义 chainsIso₃
  签名: : (inhomogeneousChains A).X 3 ≅ 模范畴.of k (G × G × G ->₀ A)
  定义体: (Finsupp.domLCongr ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso

Depends on / 依赖: Equiv.refl, Fin.consEquiv, Finsupp, Finsupp.domLCongr, consEquiv, domLCongr, piFinTwoEquiv, prodCongr, symm.trans, toModuleIso
-/
def chainsIso₃ : (inhomogeneousChains A).X 3 ≅ ModuleCat.of k (G × G × G ->₀ A) :=
  (Finsupp.domLCongr ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso

end Chains

section Differentials

/--
Definition of `d₁₀` / `d₁₀` 的定义

English:
definition d₁₀
  signature: : ModuleCat.of k (G ->₀ A) ⟶ ModuleCat.of k A.V
  body: ModuleCat.ofHom lsum k fun g => A.ρ g⁻¹ - LinearMap.id

@[simp]

中文:
定义 d₁₀
  签名: : 模范畴.of k (G ->₀ A) ⟶ 模范畴.of k A.V
  定义体: ModuleCat.ofHom lsum k fun g => A.ρ g⁻¹ - LinearMap.id

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id, ModuleCat, ModuleCat.ofHom
-/
def d₁₀ : ModuleCat.of k (G ->₀ A) ⟶ ModuleCat.of k A.V :=
ModuleCat.ofHom lsum k fun g => A.ρ g⁻¹ - LinearMap.id

@[simp]
/--
theorem `d₁₀_single` / 定理 `d₁₀_single`

English:
theorem d₁₀_single
  given: (g : G) (a : A)
  statement: d₁₀ A (single g a) = A.ρ g⁻¹ a - a
  proof: by
  simp [d₁₀]

中文:
定理 d₁₀_single
  条件: (g : G) (a : A)
  结论: d₁₀ A (single g a) = A.ρ g⁻¹ a - a
  证明: by
  simp [d₁₀]
-/
theorem d₁₀_single (g : G) (a : A) : d₁₀ A (single g a) = A.ρ g⁻¹ a - a := by
  simp [d₁₀]

/--
theorem `d₁₀_single_one` / 定理 `d₁₀_single_one`

English:
theorem d₁₀_single_one
  given: (a : A)
  statement: d₁₀ A (single 1 a) = 0
  proof: by
  simp [d₁₀]

中文:
定理 d₁₀_single_one
  条件: (a : A)
  结论: d₁₀ A (single 1 a) = 0
  证明: by
  simp [d₁₀]
-/
theorem d₁₀_single_one (a : A) : d₁₀ A (single 1 a) = 0 := by
  simp [d₁₀]

/--
theorem `d₁₀_single_inv` / 定理 `d₁₀_single_inv`

English:
theorem d₁₀_single_inv
  given: (g : G) (a : A)
  proof: by
  simp [d₁₀]

中文:
定理 d₁₀_single_inv
  条件: (g : G) (a : A)
  证明: by
  simp [d₁₀]
-/
theorem d₁₀_single_inv (g : G) (a : A) :
    d₁₀ A (single g⁻¹ a) = -d₁₀ A (single g (A.ρ g a)) := by
  simp [d₁₀]

/--
theorem `range_d₁₀_eq_coinvariantsKer` / 定理 `range_d₁₀_eq_coinvariantsKer`

English:
theorem range_d₁₀_eq_coinvariantsKer
  proof: by
  symm
  apply Submodule.span_eq_of_le
  · rintro _ ⟨x, rfl⟩
    use single x.1⁻¹ x.2
    simp [d₁₀]
  · rintro x ⟨y, hy⟩
    induction y using Finsupp.induction generalizing x with
    | zero => simp [← hy]
    | single_add _ _ _ _ _ h =>
      simpa [← hy, add_sub_add_comm, sum_add_index, d₁₀_single (G := G)]
        using! Submodule.add_mem _ (Coinvariants.mem_ker_of_eq _ _ _ rfl) (h rfl)

中文:
定理 range_d₁₀_eq_coinvariantsKer
  证明: by
  symm
  apply Submodule.span_eq_of_le
  · rintro _ ⟨x, rfl⟩
    use single x.1⁻¹ x.2
    simp [d₁₀]
  · rintro x ⟨y, hy⟩
    induction y using Finsupp.induction generalizing x with
    | zero => simp [← hy]
    | single_add _ _ _ _ _ h =>
      simpa [← hy, add_sub_add_comm, sum_add_index, d₁₀_single (G := G)]
        using! Submodule.add_mem _ (Coinvariants.mem_ker_of_eq _ _ _ rfl) (h rfl)

Depends on / 依赖: Coinvariants, Coinvariants.mem_ker_of_eq, Finsupp, Finsupp.induction, Submodule, Submodule.add_mem, Submodule.span_eq_of_le, add_mem, add_sub_add_comm, generalizing, mem_ker_of_eq, single, single_add, span_eq_of_le, sum_add_index
-/
theorem range_d₁₀_eq_coinvariantsKer :
    LinearMap.range (d₁₀ A).hom = Coinvariants.ker A.ρ := by
  symm
  apply Submodule.span_eq_of_le
  · rintro _ ⟨x, rfl⟩
    use single x.1⁻¹ x.2
    simp [d₁₀]
  · rintro x ⟨y, hy⟩
    induction y using Finsupp.induction generalizing x with
    | zero => simp [← hy]
    | single_add _ _ _ _ _ h =>
      simpa [← hy, add_sub_add_comm, sum_add_index, d₁₀_single (G := G)]
        using! Submodule.add_mem _ (Coinvariants.mem_ker_of_eq _ _ _ rfl) (h rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `d₁₀_comp_coinvariantsMk` / 引理 `d₁₀_comp_coinvariantsMk`

English:
lemma d₁₀_comp_coinvariantsMk
  statement: d₁₀ A ≫ (coinvariantsMk k G).app A = 0
  proof: by
  ext
  simp [d₁₀]

中文:
引理 d₁₀_comp_coinvariantsMk
  结论: d₁₀ A ≫ (coinvariantsMk k G).app A = 0
  证明: by
  ext
  simp [d₁₀]
-/
lemma d₁₀_comp_coinvariantsMk : d₁₀ A ≫ (coinvariantsMk k G).app A = 0 := by
  ext
  simp [d₁₀]

/--
Definition of `chains₁ToCoinvariantsKer` / `chains₁ToCoinvariantsKer` 的定义

English:
definition chains₁ToCoinvariantsKer
  signature: :
  body: ModuleCat.ofHom (d₁₀ A).hom.codRestrict _
    range_d₁₀_eq_coinvariantsKer A ▸ LinearMap.mem_range_self _

中文:
定义 chains₁ToCoinvariantsKer
  签名: :
  定义体: ModuleCat.ofHom (d₁₀ A).hom.codRestrict _
    range_d₁₀_eq_coinvariantsKer A ▸ LinearMap.mem_range_self _

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, ModuleCat, ModuleCat.ofHom, codRestrict, hom.codRestrict, mem_range_self
-/
def chains₁ToCoinvariantsKer :
    ModuleCat.of k (G ->₀ A) ⟶ ModuleCat.of k (Coinvariants.ker A.ρ) :=
ModuleCat.ofHom (d₁₀ A).hom.codRestrict _
    range_d₁₀_eq_coinvariantsKer A ▸ LinearMap.mem_range_self _

/--
lemma `chains₁ToCoinvariantsKer_surjective` / 引理 `chains₁ToCoinvariantsKer_surjective`

English:
lemma chains₁ToCoinvariantsKer_surjective
  proof: by
  rintro ⟨x, hx⟩
  rcases range_d₁₀_eq_coinvariantsKer A ▸ hx with ⟨y, hy⟩
  use y, Subtype.ext hy

@[simp]

中文:
引理 chains₁ToCoinvariantsKer_surjective
  证明: by
  rintro ⟨x, hx⟩
  rcases range_d₁₀_eq_coinvariantsKer A ▸ hx with ⟨y, hy⟩
  use y, Subtype.ext hy

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma chains₁ToCoinvariantsKer_surjective :
    Function.Surjective (chains₁ToCoinvariantsKer A) := by
  rintro ⟨x, hx⟩
  rcases range_d₁₀_eq_coinvariantsKer A ▸ hx with ⟨y, hy⟩
  use y, Subtype.ext hy

@[simp]
/--
theorem `d₁₀_eq_zero_of_isTrivial` / 定理 `d₁₀_eq_zero_of_isTrivial`

English:
theorem d₁₀_eq_zero_of_isTrivial
  given: [A.IsTrivial]
  statement: d₁₀ A = 0
  proof: by
  ext
  simp [d₁₀]

中文:
定理 d₁₀_eq_zero_of_isTrivial
  条件: [A.是平凡]
  结论: d₁₀ A = 0
  证明: by
  ext
  simp [d₁₀]
-/
theorem d₁₀_eq_zero_of_isTrivial [A.IsTrivial] : d₁₀ A = 0 := by
  ext
  simp [d₁₀]

/--
Definition of `d₂₁` / `d₂₁` 的定义

English:
definition d₂₁
  signature: : ModuleCat.of k (G × G ->₀ A) ⟶ ModuleCat.of k (G ->₀ A)
  body: ModuleCat.ofHom lsum k fun g => lsingle g.2 ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2) + lsingle g.1

中文:
定义 d₂₁
  签名: : 模范畴.of k (G × G ->₀ A) ⟶ 模范畴.of k (G ->₀ A)
  定义体: ModuleCat.ofHom lsum k fun g => lsingle g.2 ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2) + lsingle g.1

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, lsingle
-/
def d₂₁ : ModuleCat.of k (G × G ->₀ A) ⟶ ModuleCat.of k (G ->₀ A) :=
ModuleCat.ofHom lsum k fun g => lsingle g.2 ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2) + lsingle g.1

variable {A}

@[simp]
/--
lemma `d₂₁_single` / 引理 `d₂₁_single`

English:
lemma d₂₁_single
  given: (g : G × G) (a : A)
  proof: by
  simp [d₂₁]

中文:
引理 d₂₁_single
  条件: (g : G × G) (a : A)
  证明: by
  simp [d₂₁]
-/
lemma d₂₁_single (g : G × G) (a : A) :
    d₂₁ A (single g a) = single g.2 (A.ρ g.1⁻¹ a) - single (g.1 * g.2) a + single g.1 a := by
  simp [d₂₁]

/--
lemma `d₂₁_single_one_fst` / 引理 `d₂₁_single_one_fst`

English:
lemma d₂₁_single_one_fst
  given: (g : G) (a : A)
  proof: by
  simp [d₂₁]

中文:
引理 d₂₁_single_one_fst
  条件: (g : G) (a : A)
  证明: by
  simp [d₂₁]
-/
lemma d₂₁_single_one_fst (g : G) (a : A) :
    d₂₁ A (single (1, g) a) = single 1 a := by
  simp [d₂₁]

/--
lemma `d₂₁_single_one_snd` / 引理 `d₂₁_single_one_snd`

English:
lemma d₂₁_single_one_snd
  given: (g : G) (a : A)
  proof: by
  simp [d₂₁]

中文:
引理 d₂₁_single_one_snd
  条件: (g : G) (a : A)
  证明: by
  simp [d₂₁]
-/
lemma d₂₁_single_one_snd (g : G) (a : A) :
    d₂₁ A (single (g, 1) a) = single 1 (A.ρ g⁻¹ a) := by
  simp [d₂₁]

/--
lemma `d₂₁_single_inv_self_ρ_sub_self_inv` / 引理 `d₂₁_single_inv_self_ρ_sub_self_inv`

English:
lemma d₂₁_single_inv_self_ρ_sub_self_inv
  given: (g : G) (a : A)
  proof: by
  simp only [map_sub, d₂₁_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel,
    mul_inv_cancel]
  abel

中文:
引理 d₂₁_single_inv_self_ρ_sub_self_inv
  条件: (g : G) (a : A)
  证明: by
  simp only [map_sub, d₂₁_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel,
    mul_inv_cancel]
  abel

Depends on / 依赖: inv_inv, inv_mul_cancel, map_sub, mul_inv_cancel, self_inv_apply
-/
lemma d₂₁_single_inv_self_ρ_sub_self_inv (g : G) (a : A) :
    d₂₁ A (single (g⁻¹, g) (A.ρ g⁻¹ a) - single (g, g⁻¹) a) =
      single 1 a - single 1 (A.ρ g⁻¹ a) := by
  simp only [map_sub, d₂₁_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel,
    mul_inv_cancel]
  abel

/--
lemma `d₂₁_single_self_inv_ρ_sub_inv_self` / 引理 `d₂₁_single_self_inv_ρ_sub_inv_self`

English:
lemma d₂₁_single_self_inv_ρ_sub_inv_self
  given: (g : G) (a : A)
  proof: by
  simp only [map_sub, d₂₁_single (G := G), inv_self_apply, mul_inv_cancel, inv_inv,
    inv_mul_cancel]
  abel

中文:
引理 d₂₁_single_self_inv_ρ_sub_inv_self
  条件: (g : G) (a : A)
  证明: by
  simp only [map_sub, d₂₁_single (G := G), inv_self_apply, mul_inv_cancel, inv_inv,
    inv_mul_cancel]
  abel

Depends on / 依赖: inv_inv, inv_mul_cancel, inv_self_apply, map_sub, mul_inv_cancel
-/
lemma d₂₁_single_self_inv_ρ_sub_inv_self (g : G) (a : A) :
    d₂₁ A (single (g, g⁻¹) (A.ρ g a) - single (g⁻¹, g) a) =
      single 1 a - single 1 (A.ρ g a) := by
  simp only [map_sub, d₂₁_single (G := G), inv_self_apply, mul_inv_cancel, inv_inv,
    inv_mul_cancel]
  abel

/--
lemma `d₂₁_single_ρ_add_single_inv_mul` / 引理 `d₂₁_single_ρ_add_single_inv_mul`

English:
lemma d₂₁_single_ρ_add_single_inv_mul
  given: (g h : G) (a : A)
  proof: by
  simp only [map_add, d₂₁_single (G := G), inv_self_apply, inv_inv, inv_mul_cancel_left]
  abel

中文:
引理 d₂₁_single_ρ_add_single_inv_mul
  条件: (g h : G) (a : A)
  证明: by
  simp only [map_add, d₂₁_single (G := G), inv_self_apply, inv_inv, inv_mul_cancel_left]
  abel

Depends on / 依赖: inv_inv, inv_mul_cancel_left, inv_self_apply, map_add
-/
lemma d₂₁_single_ρ_add_single_inv_mul (g h : G) (a : A) :
    d₂₁ A (single (g, h) (A.ρ g a) + single (g⁻¹, g * h) a) =
      single g (A.ρ g a) + single g⁻¹ a := by
  simp only [map_add, d₂₁_single (G := G), inv_self_apply, inv_inv, inv_mul_cancel_left]
  abel

/--
lemma `d₂₁_single_inv_mul_ρ_add_single` / 引理 `d₂₁_single_inv_mul_ρ_add_single`

English:
lemma d₂₁_single_inv_mul_ρ_add_single
  given: (g h : G) (a : A)
  proof: by
  simp only [map_add, d₂₁_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel_left]
  abel

中文:
引理 d₂₁_single_inv_mul_ρ_add_single
  条件: (g h : G) (a : A)
  证明: by
  simp only [map_add, d₂₁_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel_left]
  abel

Depends on / 依赖: inv_inv, inv_mul_cancel_left, map_add, self_inv_apply
-/
lemma d₂₁_single_inv_mul_ρ_add_single (g h : G) (a : A) :
    d₂₁ A (single (g⁻¹, g * h) (A.ρ g⁻¹ a) + single (g, h) a) =
      single g⁻¹ (A.ρ g⁻¹ a) + single g a := by
  simp only [map_add, d₂₁_single (G := G), inv_inv, self_inv_apply, inv_mul_cancel_left]
  abel

variable (A) in
/--
Definition of `d₃₂` / `d₃₂` 的定义

English:
definition d₃₂
  signature: : ModuleCat.of k (G × G × G ->₀ A) ⟶ ModuleCat.of k (G × G ->₀ A)
  body: ModuleCat.ofHom lsum k fun g =>
    lsingle (g.2.1, g.2.2) ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2.1, g.2.2) +
    lsingle (g.1, g.2.1 * g.2.2) - lsingle (g.1, g.2.1)

@[simp]

中文:
定义 d₃₂
  签名: : 模范畴.of k (G × G × G ->₀ A) ⟶ 模范畴.of k (G × G ->₀ A)
  定义体: ModuleCat.ofHom lsum k fun g =>
    lsingle (g.2.1, g.2.2) ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2.1, g.2.2) +
    lsingle (g.1, g.2.1 * g.2.2) - lsingle (g.1, g.2.1)

@[simp]

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, lsingle
-/
def d₃₂ : ModuleCat.of k (G × G × G ->₀ A) ⟶ ModuleCat.of k (G × G ->₀ A) :=
ModuleCat.ofHom lsum k fun g =>
    lsingle (g.2.1, g.2.2) ∘ₗ A.ρ g.1⁻¹ - lsingle (g.1 * g.2.1, g.2.2) +
    lsingle (g.1, g.2.1 * g.2.2) - lsingle (g.1, g.2.1)

@[simp]
/--
lemma `d₃₂_single` / 引理 `d₃₂_single`

English:
lemma d₃₂_single
  given: (g : G × G × G) (a : A)
  proof: by
  simp [d₃₂]

中文:
引理 d₃₂_single
  条件: (g : G × G × G) (a : A)
  证明: by
  simp [d₃₂]
-/
lemma d₃₂_single (g : G × G × G) (a : A) :
    d₃₂ A (single g a) = single (g.2.1, g.2.2) (A.ρ g.1⁻¹ a) - single (g.1 * g.2.1, g.2.2) a +
      single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a := by
  simp [d₃₂]

/--
lemma `d₃₂_single_one_fst` / 引理 `d₃₂_single_one_fst`

English:
lemma d₃₂_single_one_fst
  given: (g h : G) (a : A)
  proof: by
  simp [d₃₂]

中文:
引理 d₃₂_single_one_fst
  条件: (g h : G) (a : A)
  证明: by
  simp [d₃₂]
-/
lemma d₃₂_single_one_fst (g h : G) (a : A) :
    d₃₂ A (single (1, g, h) a) = single (1, g * h) a - single (1, g) a := by
  simp [d₃₂]

/--
lemma `d₃₂_single_one_snd` / 引理 `d₃₂_single_one_snd`

English:
lemma d₃₂_single_one_snd
  given: (g h : G) (a : A)
  proof: by
  simp [d₃₂]

中文:
引理 d₃₂_single_one_snd
  条件: (g h : G) (a : A)
  证明: by
  simp [d₃₂]
-/
lemma d₃₂_single_one_snd (g h : G) (a : A) :
    d₃₂ A (single (g, 1, h) a) = single (1, h) (A.ρ g⁻¹ a) - single (g, 1) a := by
  simp [d₃₂]

/--
lemma `d₃₂_single_one_thd` / 引理 `d₃₂_single_one_thd`

English:
lemma d₃₂_single_one_thd
  given: (g h : G) (a : A)
  proof: by
  simp [d₃₂]

中文:
引理 d₃₂_single_one_thd
  条件: (g h : G) (a : A)
  证明: by
  simp [d₃₂]
-/
lemma d₃₂_single_one_thd (g h : G) (a : A) :
    d₃₂ A (single (g, h, 1) a) = single (h, 1) (A.ρ g⁻¹ a) - single (g * h, 1) a := by
  simp [d₃₂]

variable (A)

/--
theorem `comp_d₁₀_eq` / 定理 `comp_d₁₀_eq`

English:
theorem comp_d₁₀_eq
  proof: ModuleCat.hom_ext lhom_ext fun _ _ => by
    simp [chainsIso₀, chainsIso₁, d₁₀_single (G := G), ChainComplex.of.d,
      Unique.eq_default (α := Fin 0 -> G), sub_eq_add_neg, inhomogeneousChains.d_single (G := G)]

中文:
定理 comp_d₁₀_eq
  证明: ModuleCat.hom_ext lhom_ext fun _ _ => by
    simp [chainsIso₀, chainsIso₁, d₁₀_single (G := G), ChainComplex.of.d,
      Unique.eq_default (α := Fin 0 -> G), sub_eq_add_neg, inhomogeneousChains.d_single (G := G)]

Depends on / 依赖: ChainComplex, ChainComplex.of.d, ModuleCat, ModuleCat.hom_ext, Unique, Unique.eq_default, d_single, eq_default, hom_ext, inhomogeneousChains, inhomogeneousChains.d_single, lhom_ext, sub_eq_add_neg
-/
theorem comp_d₁₀_eq :
    (chainsIso₁ A).hom ≫ d₁₀ A = (inhomogeneousChains A).d 1 0 ≫ (chainsIso₀ A).hom :=
ModuleCat.hom_ext lhom_ext fun _ _ => by
    simp [chainsIso₀, chainsIso₁, d₁₀_single (G := G), ChainComplex.of.d,
      Unique.eq_default (α := Fin 0 -> G), sub_eq_add_neg, inhomogeneousChains.d_single (G := G)]

-- @[reassoc (attr := simp), elementwise (attr := simp)]
@[reassoc, elementwise]
/--
theorem `eq_d₁₀_comp_inv` / 定理 `eq_d₁₀_comp_inv`

English:
theorem eq_d₁₀_comp_inv
  proof: (CommSq.horiz_inv ⟨comp_d₁₀_eq A⟩).w

中文:
定理 eq_d₁₀_comp_inv
  证明: (CommSq.horiz_inv ⟨comp_d₁₀_eq A⟩).w

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
theorem eq_d₁₀_comp_inv :
    (chainsIso₁ A).inv ≫ (inhomogeneousChains A).d 1 0 = d₁₀ A ≫ (chainsIso₀ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₁₀_eq A⟩).w

/--
theorem `comp_d₂₁_eq` / 定理 `comp_d₂₁_eq`

English:
theorem comp_d₂₁_eq
  proof: ModuleCat.hom_ext lhom_ext fun _ _ => by
    simp [chainsIso₁, add_assoc, chainsIso₂, d₂₁_single (G := G),
      -Finsupp.domLCongr_apply, domLCongr_single, sub_eq_add_neg, ChainComplex.of.d,
      Fin.contractNth, inhomogeneousChains.d_single (G := G)]

@[reassoc, elementwise]

中文:
定理 comp_d₂₁_eq
  证明: ModuleCat.hom_ext lhom_ext fun _ _ => by
    simp [chainsIso₁, add_assoc, chainsIso₂, d₂₁_single (G := G),
      -Finsupp.domLCongr_apply, domLCongr_single, sub_eq_add_neg, ChainComplex.of.d,
      Fin.contractNth, inhomogeneousChains.d_single (G := G)]

@[reassoc, elementwise]

Depends on / 依赖: ChainComplex, ChainComplex.of.d, Fin.contractNth, Finsupp, Finsupp.domLCongr_apply, ModuleCat, ModuleCat.hom_ext, add_assoc, contractNth, d_single, domLCongr_apply, domLCongr_single, hom_ext, inhomogeneousChains, inhomogeneousChains.d_single, lhom_ext, sub_eq_add_neg
-/
theorem comp_d₂₁_eq :
    (chainsIso₂ A).hom ≫ d₂₁ A = (inhomogeneousChains A).d 2 1 ≫ (chainsIso₁ A).hom :=
ModuleCat.hom_ext lhom_ext fun _ _ => by
    simp [chainsIso₁, add_assoc, chainsIso₂, d₂₁_single (G := G),
      -Finsupp.domLCongr_apply, domLCongr_single, sub_eq_add_neg, ChainComplex.of.d,
      Fin.contractNth, inhomogeneousChains.d_single (G := G)]

@[reassoc, elementwise]
/--
theorem `eq_d₂₁_comp_inv` / 定理 `eq_d₂₁_comp_inv`

English:
theorem eq_d₂₁_comp_inv
  proof: (CommSq.horiz_inv ⟨comp_d₂₁_eq A⟩).w

中文:
定理 eq_d₂₁_comp_inv
  证明: (CommSq.horiz_inv ⟨comp_d₂₁_eq A⟩).w

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
theorem eq_d₂₁_comp_inv :
    (chainsIso₂ A).inv ≫ (inhomogeneousChains A).d 2 1 = d₂₁ A ≫ (chainsIso₁ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₂₁_eq A⟩).w

/--
theorem `comp_d₃₂_eq` / 定理 `comp_d₃₂_eq`

English:
theorem comp_d₃₂_eq
  proof: ModuleCat.hom_ext lhom_ext fun _ _ => by
    simp [chainsIso₂, ChainComplex.of.d, pow_succ, chainsIso₃,
      -domLCongr_apply, domLCongr_single, d₃₂, Fin.sum_univ_three,
      Fin.contractNth, Fin.tail_def, sub_eq_add_neg, add_assoc,
      inhomogeneousChains.d_single (G := G), add_rotate' (-(single (_ * _, _) _)),
      add_left_comm (single (_, _ * _) _)]

@[reassoc, elementwise]

中文:
定理 comp_d₃₂_eq
  证明: ModuleCat.hom_ext lhom_ext fun _ _ => by
    simp [chainsIso₂, ChainComplex.of.d, pow_succ, chainsIso₃,
      -domLCongr_apply, domLCongr_single, d₃₂, Fin.sum_univ_three,
      Fin.contractNth, Fin.tail_def, sub_eq_add_neg, add_assoc,
      inhomogeneousChains.d_single (G := G), add_rotate' (-(single (_ * _, _) _)),
      add_left_comm (single (_, _ * _) _)]

@[reassoc, elementwise]

Depends on / 依赖: ChainComplex, ChainComplex.of.d, Fin.contractNth, Fin.sum_univ_three, Fin.tail_def, ModuleCat, ModuleCat.hom_ext, add_assoc, add_left_comm, add_rotate, contractNth, d_single, domLCongr_apply, domLCongr_single, hom_ext, inhomogeneousChains, inhomogeneousChains.d_single, lhom_ext, pow_succ, single
-/
theorem comp_d₃₂_eq :
    (chainsIso₃ A).hom ≫ d₃₂ A = (inhomogeneousChains A).d 3 2 ≫ (chainsIso₂ A).hom :=
ModuleCat.hom_ext lhom_ext fun _ _ => by
    simp [chainsIso₂, ChainComplex.of.d, pow_succ, chainsIso₃,
      -domLCongr_apply, domLCongr_single, d₃₂, Fin.sum_univ_three,
      Fin.contractNth, Fin.tail_def, sub_eq_add_neg, add_assoc,
      inhomogeneousChains.d_single (G := G), add_rotate' (-(single (_ * _, _) _)),
      add_left_comm (single (_, _ * _) _)]

@[reassoc, elementwise]
/--
theorem `eq_d₃₂_comp_inv` / 定理 `eq_d₃₂_comp_inv`

English:
theorem eq_d₃₂_comp_inv
  proof: (CommSq.horiz_inv ⟨comp_d₃₂_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 eq_d₃₂_comp_inv
  证明: (CommSq.horiz_inv ⟨comp_d₃₂_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
theorem eq_d₃₂_comp_inv :
    (chainsIso₃ A).inv ≫ (inhomogeneousChains A).d 3 2 = d₃₂ A ≫ (chainsIso₂ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₃₂_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `d₂₁_comp_d₁₀` / 定理 `d₂₁_comp_d₁₀`

English:
theorem d₂₁_comp_d₁₀
  statement: d₂₁ A ≫ d₁₀ A = 0
  proof: by
  ext x g
  simp [d₁₀, d₂₁, sum_add_index', sum_sub_index, sub_sub_sub_comm, add_sub_add_comm]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 d₂₁_comp_d₁₀
  结论: d₂₁ A ≫ d₁₀ A = 0
  证明: by
  ext x g
  simp [d₁₀, d₂₁, sum_add_index', sum_sub_index, sub_sub_sub_comm, add_sub_add_comm]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: add_sub_add_comm, sub_sub_sub_comm, sum_add_index, sum_sub_index
-/
theorem d₂₁_comp_d₁₀ : d₂₁ A ≫ d₁₀ A = 0 := by
  ext x g
  simp [d₁₀, d₂₁, sum_add_index', sum_sub_index, sub_sub_sub_comm, add_sub_add_comm]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `d₃₂_comp_d₂₁` / 定理 `d₃₂_comp_d₂₁`

English:
theorem d₃₂_comp_d₂₁
  statement: d₃₂ A ≫ d₂₁ A = 0
  proof: by
  simp [← cancel_mono (chainsIso₁ A).inv, ← eq_d₂₁_comp_inv, ← eq_d₃₂_comp_inv_assoc,
    ChainComplex.of.d, inhomogeneousChains.d_comp_d]

中文:
定理 d₃₂_comp_d₂₁
  结论: d₃₂ A ≫ d₂₁ A = 0
  证明: by
  simp [← cancel_mono (chainsIso₁ A).inv, ← eq_d₂₁_comp_inv, ← eq_d₃₂_comp_inv_assoc,
    ChainComplex.of.d, inhomogeneousChains.d_comp_d]

Depends on / 依赖: ChainComplex, ChainComplex.of.d, cancel_mono, d_comp_d, inhomogeneousChains, inhomogeneousChains.d_comp_d
-/
theorem d₃₂_comp_d₂₁ : d₃₂ A ≫ d₂₁ A = 0 := by
  simp [← cancel_mono (chainsIso₁ A).inv, ← eq_d₂₁_comp_inv, ← eq_d₃₂_comp_inv_assoc,
    ChainComplex.of.d, inhomogeneousChains.d_comp_d]

open ShortComplex

/-- The (exact) short complex `(G →₀ A) ⟶ A ⟶ A.ρ.coinvariants`. -/
@[simps! -isSimp f g]
/--
Definition of `shortComplexH0` / `shortComplexH0` 的定义

English:
definition shortComplexH0
  signature: : ShortComplex (ModuleCat k)
  body: mk _ _ (d₁₀_comp_coinvariantsMk A)

中文:
定义 shortComplexH0
  签名: : 短复形 (模范畴 k)
  定义体: mk _ _ (d₁₀_comp_coinvariantsMk A)
-/
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  mk _ _ (d₁₀_comp_coinvariantsMk A)

/-- The short complex `(G² →₀ A) --d₂₁--> (G →₀ A) --d₁₀--> A`. -/
@[simps! -isSimp f g]
/--
Definition of `shortComplexH1` / `shortComplexH1` 的定义

English:
definition shortComplexH1
  signature: : ShortComplex (ModuleCat k)
  body: mk _ _ (d₂₁_comp_d₁₀ A)

中文:
定义 shortComplexH1
  签名: : 短复形 (模范畴 k)
  定义体: mk _ _ (d₂₁_comp_d₁₀ A)
-/
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  mk _ _ (d₂₁_comp_d₁₀ A)

/-- The short complex `(G³ →₀ A) --d₃₂--> (G² →₀ A) --d₂₁--> (G →₀ A)`. -/
@[simps! -isSimp f g]
/--
Definition of `shortComplexH2` / `shortComplexH2` 的定义

English:
definition shortComplexH2
  signature: : ShortComplex (ModuleCat k)
  body: mk _ _ (d₃₂_comp_d₂₁ A)

中文:
定义 shortComplexH2
  签名: : 短复形 (模范畴 k)
  定义体: mk _ _ (d₃₂_comp_d₂₁ A)
-/
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  mk _ _ (d₃₂_comp_d₂₁ A)

end Differentials

section Cycles

/--
Definition of `cycles₁` / `cycles₁` 的定义

English:
definition cycles₁
  signature: : Submodule k (G ->₀ A)
  body: LinearMap.ker (d₁₀ A).hom

中文:
定义 cycles₁
  签名: : 子模 k (G ->₀ A)
  定义体: LinearMap.ker (d₁₀ A).hom

Depends on / 依赖: LinearMap, LinearMap.ker
-/
def cycles₁ : Submodule k (G ->₀ A) := LinearMap.ker (d₁₀ A).hom

/--
Definition of `cycles₂` / `cycles₂` 的定义

English:
definition cycles₂
  signature: : Submodule k (G × G ->₀ A)
  body: LinearMap.ker (d₂₁ A).hom

中文:
定义 cycles₂
  签名: : 子模 k (G × G ->₀ A)
  定义体: LinearMap.ker (d₂₁ A).hom

Depends on / 依赖: LinearMap, LinearMap.ker
-/
def cycles₂ : Submodule k (G × G ->₀ A) := LinearMap.ker (d₂₁ A).hom

variable {A}

/--
theorem `mem_cycles₁_iff` / 定理 `mem_cycles₁_iff`

English:
theorem mem_cycles₁_iff
  given: (x : G ->₀ A)
  proof: by
  change x.sum (fun g a => A.ρ g⁻¹ a - a) = 0 ↔ _
  rw [sum_sub]; rw [sub_eq_zero]

中文:
定理 mem_cycles₁_iff
  条件: (x : G ->₀ A)
  证明: by
  change x.sum (fun g a => A.ρ g⁻¹ a - a) = 0 ↔ _
  rw [sum_sub]; rw [sub_eq_zero]

Depends on / 依赖: sub_eq_zero, sum_sub, x.sum
-/
theorem mem_cycles₁_iff (x : G ->₀ A) :
    x in cycles₁ A ↔ x.sum (fun g a => A.ρ g⁻¹ a) = x.sum (fun _ a => a) := by
  change x.sum (fun g a => A.ρ g⁻¹ a - a) = 0 ↔ _
  rw [sum_sub]; rw [sub_eq_zero]

/--
theorem `single_mem_cycles₁_iff` / 定理 `single_mem_cycles₁_iff`

English:
theorem single_mem_cycles₁_iff
  given: (g : G) (a : A)
  proof: by
  simp [mem_cycles₁_iff, ← (A.ρ.apply_bijective g).1.eq_iff (a := A.ρ g⁻¹ a), eq_comm]

中文:
定理 single_mem_cycles₁_iff
  条件: (g : G) (a : A)
  证明: by
  simp [mem_cycles₁_iff, ← (A.ρ.apply_bijective g).1.eq_iff (a := A.ρ g⁻¹ a), eq_comm]

Depends on / 依赖: apply_bijective, eq_comm, eq_iff
-/
theorem single_mem_cycles₁_iff (g : G) (a : A) :
    single g a in cycles₁ A ↔ A.ρ g a = a := by
  simp [mem_cycles₁_iff, ← (A.ρ.apply_bijective g).1.eq_iff (a := A.ρ g⁻¹ a), eq_comm]

/--
theorem `single_mem_cycles₁_of_mem_invariants` / 定理 `single_mem_cycles₁_of_mem_invariants`

English:
theorem single_mem_cycles₁_of_mem_invariants
  given: (g : G) (a : A) (ha : a in A.ρ.invariants)
  proof: (single_mem_cycles₁_iff g a).2 (ha g)

中文:
定理 single_mem_cycles₁_of_mem_invariants
  条件: (g : G) (a : A) (ha : a in A.ρ.invariants)
  证明: (single_mem_cycles₁_iff g a).2 (ha g)
-/
theorem single_mem_cycles₁_of_mem_invariants (g : G) (a : A) (ha : a in A.ρ.invariants) :
    single g a in cycles₁ A :=
  (single_mem_cycles₁_iff g a).2 (ha g)

/--
theorem `d₂₁_apply_mem_cycles₁` / 定理 `d₂₁_apply_mem_cycles₁`

English:
theorem d₂₁_apply_mem_cycles₁
  given: (x : G × G ->₀ A)
  proof: congr($(d₂₁_comp_d₁₀ A) x)

中文:
定理 d₂₁_apply_mem_cycles₁
  条件: (x : G × G ->₀ A)
  证明: congr($(d₂₁_comp_d₁₀ A) x)
-/
theorem d₂₁_apply_mem_cycles₁ (x : G × G ->₀ A) :
    d₂₁ A x in cycles₁ A :=
  congr($(d₂₁_comp_d₁₀ A) x)

variable (A) in
/--
theorem `cycles₁_eq_top_of_isTrivial` / 定理 `cycles₁_eq_top_of_isTrivial`

English:
theorem cycles₁_eq_top_of_isTrivial
  given: [A.IsTrivial]
  statement: cycles₁ A = ⊤
  proof: by
  rw [cycles₁]; rw [d₁₀_eq_zero_of_isTrivial]; rw [ModuleCat.hom_zero]; rw [LinearMap.ker_zero]

中文:
定理 cycles₁_eq_top_of_isTrivial
  条件: [A.是平凡]
  结论: cycles₁ A = ⊤
  证明: by
  rw [cycles₁]; rw [d₁₀_eq_zero_of_isTrivial]; rw [ModuleCat.hom_zero]; rw [LinearMap.ker_zero]

Depends on / 依赖: LinearMap, LinearMap.ker_zero, ModuleCat, ModuleCat.hom_zero, hom_zero, ker_zero
-/
theorem cycles₁_eq_top_of_isTrivial [A.IsTrivial] : cycles₁ A = ⊤ := by
  rw [cycles₁]; rw [d₁₀_eq_zero_of_isTrivial]; rw [ModuleCat.hom_zero]; rw [LinearMap.ker_zero]

variable (A) in
/--
Definition of `cycles₁IsoOfIsTrivial` / `cycles₁IsoOfIsTrivial` 的定义

English:
definition cycles₁IsoOfIsTrivial
  signature: [A.IsTrivial]
  body: (LinearEquiv.ofTop _ (cycles₁_eq_top_of_isTrivial A)).toModuleIso

@[simp]

中文:
定义 cycles₁IsoOfIsTrivial
  签名: [A.是平凡]
  定义体: (LinearEquiv.ofTop _ (cycles₁_eq_top_of_isTrivial A)).toModuleIso

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofTop, toModuleIso
-/
def cycles₁IsoOfIsTrivial [A.IsTrivial] :
    ModuleCat.of k (cycles₁ A) ≅ ModuleCat.of k (G ->₀ A) :=
  (LinearEquiv.ofTop _ (cycles₁_eq_top_of_isTrivial A)).toModuleIso

@[simp]
/--
lemma `cycles₁IsoOfIsTrivial_hom_apply` / 引理 `cycles₁IsoOfIsTrivial_hom_apply`

English:
lemma cycles₁IsoOfIsTrivial_hom_apply
  given: [A.IsTrivial] (x : cycles₁ A)
  proof: rfl

@[simp]

中文:
引理 cycles₁IsoOfIsTrivial_hom_apply
  条件: [A.是平凡] (x : cycles₁ A)
  证明: rfl

@[simp]
-/
lemma cycles₁IsoOfIsTrivial_hom_apply [A.IsTrivial] (x : cycles₁ A) :
    (cycles₁IsoOfIsTrivial A).hom x = x.1 := rfl

@[simp]
/--
lemma `cycles₁IsoOfIsTrivial_inv_apply` / 引理 `cycles₁IsoOfIsTrivial_inv_apply`

English:
lemma cycles₁IsoOfIsTrivial_inv_apply
  given: [A.IsTrivial] (x : G ->₀ A)
  proof: rfl

中文:
引理 cycles₁IsoOfIsTrivial_inv_apply
  条件: [A.是平凡] (x : G ->₀ A)
  证明: rfl
-/
lemma cycles₁IsoOfIsTrivial_inv_apply [A.IsTrivial] (x : G ->₀ A) :
    ((cycles₁IsoOfIsTrivial A).inv x).1 = x := rfl

/--
theorem `mem_cycles₂_iff` / 定理 `mem_cycles₂_iff`

English:
theorem mem_cycles₂_iff
  given: (x : G × G ->₀ A)
  proof: by
  change x.sum (fun g a => _) = 0 ↔ _
  simp [sub_add_eq_add_sub, sub_eq_zero]

中文:
定理 mem_cycles₂_iff
  条件: (x : G × G ->₀ A)
  证明: by
  change x.sum (fun g a => _) = 0 ↔ _
  simp [sub_add_eq_add_sub, sub_eq_zero]

Depends on / 依赖: sub_add_eq_add_sub, sub_eq_zero, x.sum
-/
theorem mem_cycles₂_iff (x : G × G ->₀ A) :
    x in cycles₂ A ↔ x.sum (fun g a => single g.2 (A.ρ g.1⁻¹ a) + single g.1 a) =
      x.sum (fun g a => single (g.1 * g.2) a) := by
  change x.sum (fun g a => _) = 0 ↔ _
  simp [sub_add_eq_add_sub, sub_eq_zero]

/--
theorem `single_mem_cycles₂_iff_inv` / 定理 `single_mem_cycles₂_iff_inv`

English:
theorem single_mem_cycles₂_iff_inv
  given: (g : G × G) (a : A)
  proof: by
  simp [mem_cycles₂_iff]

中文:
定理 single_mem_cycles₂_iff_inv
  条件: (g : G × G) (a : A)
  证明: by
  simp [mem_cycles₂_iff]
-/
theorem single_mem_cycles₂_iff_inv (g : G × G) (a : A) :
    single g a in cycles₂ A ↔ single g.2 (A.ρ g.1⁻¹ a) + single g.1 a = single (g.1 * g.2) a := by
  simp [mem_cycles₂_iff]

/--
theorem `single_mem_cycles₂_iff` / 定理 `single_mem_cycles₂_iff`

English:
theorem single_mem_cycles₂_iff
  given: (g : G × G) (a : A)
  proof: by
  rw [← (mapRange_injective (α := G) _ (map_zero _) (A.ρ.apply_bijective g.1⁻¹).1).eq_iff]
  simp [mem_cycles₂_iff, mapRange_add, eq_comm]

中文:
定理 single_mem_cycles₂_iff
  条件: (g : G × G) (a : A)
  证明: by
  rw [← (mapRange_injective (α := G) _ (map_zero _) (A.ρ.apply_bijective g.1⁻¹).1).eq_iff]
  simp [mem_cycles₂_iff, mapRange_add, eq_comm]

Depends on / 依赖: apply_bijective, eq_comm, eq_iff, mapRange_add, mapRange_injective, map_zero
-/
theorem single_mem_cycles₂_iff (g : G × G) (a : A) :
    single g a in cycles₂ A ↔
      single (g.1 * g.2) (A.ρ g.1 a) = single g.2 a + single g.1 (A.ρ g.1 a) := by
  rw [← (mapRange_injective (α := G) _ (map_zero _) (A.ρ.apply_bijective g.1⁻¹).1).eq_iff]
  simp [mem_cycles₂_iff, mapRange_add, eq_comm]

/--
theorem `d₃₂_apply_mem_cycles₂` / 定理 `d₃₂_apply_mem_cycles₂`

English:
theorem d₃₂_apply_mem_cycles₂
  given: (x : G × G × G ->₀ A)
  proof: congr($(d₃₂_comp_d₂₁ A) x)

中文:
定理 d₃₂_apply_mem_cycles₂
  条件: (x : G × G × G ->₀ A)
  证明: congr($(d₃₂_comp_d₂₁ A) x)
-/
theorem d₃₂_apply_mem_cycles₂ (x : G × G × G ->₀ A) :
    d₃₂ A x in cycles₂ A :=
  congr($(d₃₂_comp_d₂₁ A) x)

end Cycles

section Boundaries

/--
Definition of `boundaries₁` / `boundaries₁` 的定义

English:
definition boundaries₁
  signature: : Submodule k (G ->₀ A)
  body: LinearMap.range (d₂₁ A).hom

中文:
定义 boundaries₁
  签名: : 子模 k (G ->₀ A)
  定义体: LinearMap.range (d₂₁ A).hom

Depends on / 依赖: LinearMap, LinearMap.range
-/
def boundaries₁ : Submodule k (G ->₀ A) :=
  LinearMap.range (d₂₁ A).hom

/--
Definition of `boundaries₂` / `boundaries₂` 的定义

English:
definition boundaries₂
  signature: : Submodule k (G × G ->₀ A)
  body: LinearMap.range (d₃₂ A).hom

中文:
定义 boundaries₂
  签名: : 子模 k (G × G ->₀ A)
  定义体: LinearMap.range (d₃₂ A).hom

Depends on / 依赖: LinearMap, LinearMap.range
-/
def boundaries₂ : Submodule k (G × G ->₀ A) :=
  LinearMap.range (d₃₂ A).hom

variable {A}

section

/--
lemma `mem_cycles₁_of_mem_boundaries₁` / 引理 `mem_cycles₁_of_mem_boundaries₁`

English:
lemma mem_cycles₁_of_mem_boundaries₁
  given: (f : G ->₀ A) (h : f in boundaries₁ A)
  proof: by
  rcases h with ⟨x, rfl⟩
  exact d₂₁_apply_mem_cycles₁ x

中文:
引理 mem_cycles₁_of_mem_boundaries₁
  条件: (f : G ->₀ A) (h : f in boundaries₁ A)
  证明: by
  rcases h with ⟨x, rfl⟩
  exact d₂₁_apply_mem_cycles₁ x
-/
lemma mem_cycles₁_of_mem_boundaries₁ (f : G ->₀ A) (h : f in boundaries₁ A) :
    f in cycles₁ A := by
  rcases h with ⟨x, rfl⟩
  exact d₂₁_apply_mem_cycles₁ x

variable (A) in
/--
lemma `boundaries₁_le_cycles₁` / 引理 `boundaries₁_le_cycles₁`

English:
lemma boundaries₁_le_cycles₁
  statement: boundaries₁ A <= cycles₁ A
  proof: mem_cycles₁_of_mem_boundaries₁

中文:
引理 boundaries₁_le_cycles₁
  结论: boundaries₁ A <= cycles₁ A
  证明: mem_cycles₁_of_mem_boundaries₁
-/
lemma boundaries₁_le_cycles₁ : boundaries₁ A <= cycles₁ A :=
  mem_cycles₁_of_mem_boundaries₁

variable (A) in
/--
Definition of `boundariesToCycles₁` / `boundariesToCycles₁` 的定义

English:
abbreviation boundariesToCycles₁
  signature: : boundaries₁ A ->ₗ[k] cycles₁ A
  body: Submodule.inclusion (boundaries₁_le_cycles₁ A)

@[simp]

中文:
缩写 boundariesToCycles₁
  签名: : boundaries₁ A ->ₗ[k] cycles₁ A
  定义体: Submodule.inclusion (boundaries₁_le_cycles₁ A)

@[simp]

Depends on / 依赖: Submodule, Submodule.inclusion, inclusion
-/
abbrev boundariesToCycles₁ : boundaries₁ A ->ₗ[k] cycles₁ A :=
  Submodule.inclusion (boundaries₁_le_cycles₁ A)

@[simp]
/--
lemma `boundariesToCycles₁_apply` / 引理 `boundariesToCycles₁_apply`

English:
lemma boundariesToCycles₁_apply
  given: (x : boundaries₁ A)
  proof: rfl

中文:
引理 boundariesToCycles₁_apply
  条件: (x : boundaries₁ A)
  证明: rfl
-/
lemma boundariesToCycles₁_apply (x : boundaries₁ A) :
    (boundariesToCycles₁ A x).1 = x.1 := rfl

end

/--
theorem `single_one_mem_boundaries₁` / 定理 `single_one_mem_boundaries₁`

English:
theorem single_one_mem_boundaries₁
  given: (a : A)
  proof: by
  use single (1, 1) a
  simp [d₂₁]

中文:
定理 single_one_mem_boundaries₁
  条件: (a : A)
  证明: by
  use single (1, 1) a
  simp [d₂₁]

Depends on / 依赖: single
-/
theorem single_one_mem_boundaries₁ (a : A) :
    single 1 a in boundaries₁ A := by
  use single (1, 1) a
  simp [d₂₁]

/--
theorem `single_ρ_self_add_single_inv_mem_boundaries₁` / 定理 `single_ρ_self_add_single_inv_mem_boundaries₁`

English:
theorem single_ρ_self_add_single_inv_mem_boundaries₁
  given: (g : G) (a : A)
  proof: by
  rw [← d₂₁_single_ρ_add_single_inv_mul g 1]
  exact Set.mem_range_self _

中文:
定理 single_ρ_self_add_single_inv_mem_boundaries₁
  条件: (g : G) (a : A)
  证明: by
  rw [← d₂₁_single_ρ_add_single_inv_mul g 1]
  exact Set.mem_range_self _

Depends on / 依赖: Set.mem_range_self, mem_range_self
-/
theorem single_ρ_self_add_single_inv_mem_boundaries₁ (g : G) (a : A) :
    single g (A.ρ g a) + single g⁻¹ a in boundaries₁ A := by
  rw [← d₂₁_single_ρ_add_single_inv_mul g 1]
  exact Set.mem_range_self _

/--
theorem `single_inv_ρ_self_add_single_mem_boundaries₁` / 定理 `single_inv_ρ_self_add_single_mem_boundaries₁`

English:
theorem single_inv_ρ_self_add_single_mem_boundaries₁
  given: (g : G) (a : A)
  proof: by
  rw [← d₂₁_single_inv_mul_ρ_add_single g 1]
  exact Set.mem_range_self _

中文:
定理 single_inv_ρ_self_add_single_mem_boundaries₁
  条件: (g : G) (a : A)
  证明: by
  rw [← d₂₁_single_inv_mul_ρ_add_single g 1]
  exact Set.mem_range_self _

Depends on / 依赖: Set.mem_range_self, mem_range_self
-/
theorem single_inv_ρ_self_add_single_mem_boundaries₁ (g : G) (a : A) :
    single g⁻¹ (A.ρ g⁻¹ a) + single g a in boundaries₁ A := by
  rw [← d₂₁_single_inv_mul_ρ_add_single g 1]
  exact Set.mem_range_self _

section

/--
lemma `mem_cycles₂_of_mem_boundaries₂` / 引理 `mem_cycles₂_of_mem_boundaries₂`

English:
lemma mem_cycles₂_of_mem_boundaries₂
  given: (x : G × G ->₀ A) (h : x in boundaries₂ A)
  proof: by
  rcases h with ⟨x, rfl⟩
  exact d₃₂_apply_mem_cycles₂ x

中文:
引理 mem_cycles₂_of_mem_boundaries₂
  条件: (x : G × G ->₀ A) (h : x in boundaries₂ A)
  证明: by
  rcases h with ⟨x, rfl⟩
  exact d₃₂_apply_mem_cycles₂ x
-/
lemma mem_cycles₂_of_mem_boundaries₂ (x : G × G ->₀ A) (h : x in boundaries₂ A) :
    x in cycles₂ A := by
  rcases h with ⟨x, rfl⟩
  exact d₃₂_apply_mem_cycles₂ x

variable (A) in
/--
lemma `boundaries₂_le_cycles₂` / 引理 `boundaries₂_le_cycles₂`

English:
lemma boundaries₂_le_cycles₂
  statement: boundaries₂ A <= cycles₂ A
  proof: mem_cycles₂_of_mem_boundaries₂

中文:
引理 boundaries₂_le_cycles₂
  结论: boundaries₂ A <= cycles₂ A
  证明: mem_cycles₂_of_mem_boundaries₂
-/
lemma boundaries₂_le_cycles₂ : boundaries₂ A <= cycles₂ A :=
  mem_cycles₂_of_mem_boundaries₂

variable (A) in
/--
Definition of `boundariesToCycles₂` / `boundariesToCycles₂` 的定义

English:
abbreviation boundariesToCycles₂
  signature: : boundaries₂ A ->ₗ[k] cycles₂ A
  body: Submodule.inclusion (boundaries₂_le_cycles₂ A)

@[simp]

中文:
缩写 boundariesToCycles₂
  签名: : boundaries₂ A ->ₗ[k] cycles₂ A
  定义体: Submodule.inclusion (boundaries₂_le_cycles₂ A)

@[simp]

Depends on / 依赖: Submodule, Submodule.inclusion, inclusion
-/
abbrev boundariesToCycles₂ : boundaries₂ A ->ₗ[k] cycles₂ A :=
  Submodule.inclusion (boundaries₂_le_cycles₂ A)

@[simp]
/--
lemma `boundariesToCycles₂_apply` / 引理 `boundariesToCycles₂_apply`

English:
lemma boundariesToCycles₂_apply
  given: (x : boundaries₂ A)
  proof: rfl

中文:
引理 boundariesToCycles₂_apply
  条件: (x : boundaries₂ A)
  证明: rfl
-/
lemma boundariesToCycles₂_apply (x : boundaries₂ A) :
    (boundariesToCycles₂ A x).1 = x.1 := rfl

end

/--
lemma `single_one_fst_sub_single_one_fst_mem_boundaries₂` / 引理 `single_one_fst_sub_single_one_fst_mem_boundaries₂`

English:
lemma single_one_fst_sub_single_one_fst_mem_boundaries₂
  given: (g h : G) (a : A)
  proof: by
  use single (1, g, h) a
  simp [d₃₂]

中文:
引理 single_one_fst_sub_single_one_fst_mem_boundaries₂
  条件: (g h : G) (a : A)
  证明: by
  use single (1, g, h) a
  simp [d₃₂]

Depends on / 依赖: single
-/
lemma single_one_fst_sub_single_one_fst_mem_boundaries₂ (g h : G) (a : A) :
    single (1, g * h) a - single (1, g) a in boundaries₂ A := by
  use single (1, g, h) a
  simp [d₃₂]

/--
lemma `single_one_fst_sub_single_one_snd_mem_boundaries₂` / 引理 `single_one_fst_sub_single_one_snd_mem_boundaries₂`

English:
lemma single_one_fst_sub_single_one_snd_mem_boundaries₂
  given: (g h : G) (a : A)
  proof: by
  use single (g, 1, h) a
  simp [d₃₂]

中文:
引理 single_one_fst_sub_single_one_snd_mem_boundaries₂
  条件: (g h : G) (a : A)
  证明: by
  use single (g, 1, h) a
  simp [d₃₂]

Depends on / 依赖: single
-/
lemma single_one_fst_sub_single_one_snd_mem_boundaries₂ (g h : G) (a : A) :
    single (1, h) (A.ρ g⁻¹ a) - single (g, 1) a in boundaries₂ A := by
  use single (g, 1, h) a
  simp [d₃₂]

/--
lemma `single_one_snd_sub_single_one_fst_mem_boundaries₂` / 引理 `single_one_snd_sub_single_one_fst_mem_boundaries₂`

English:
lemma single_one_snd_sub_single_one_fst_mem_boundaries₂
  given: (g h : G) (a : A)
  proof: by
  use single (g, 1, h) (A.ρ g (-a))
  simp [d₃₂_single (G := G)]

中文:
引理 single_one_snd_sub_single_one_fst_mem_boundaries₂
  条件: (g h : G) (a : A)
  证明: by
  use single (g, 1, h) (A.ρ g (-a))
  simp [d₃₂_single (G := G)]

Depends on / 依赖: single
-/
lemma single_one_snd_sub_single_one_fst_mem_boundaries₂ (g h : G) (a : A) :
    single (g, 1) (A.ρ g a) - single (1, h) a in boundaries₂ A := by
  use single (g, 1, h) (A.ρ g (-a))
  simp [d₃₂_single (G := G)]

/--
lemma `single_one_snd_sub_single_one_snd_mem_boundaries₂` / 引理 `single_one_snd_sub_single_one_snd_mem_boundaries₂`

English:
lemma single_one_snd_sub_single_one_snd_mem_boundaries₂
  given: (g h : G) (a : A)
  proof: by
  use single (g, h, 1) a
  simp [d₃₂]

中文:
引理 single_one_snd_sub_single_one_snd_mem_boundaries₂
  条件: (g h : G) (a : A)
  证明: by
  use single (g, h, 1) a
  simp [d₃₂]

Depends on / 依赖: single
-/
lemma single_one_snd_sub_single_one_snd_mem_boundaries₂ (g h : G) (a : A) :
    single (h, 1) (A.ρ g⁻¹ a) - single (g * h, 1) a in boundaries₂ A := by
  use single (g, h, 1) a
  simp [d₃₂]

end Boundaries

section IsCycle

section

variable {G A : Type*} [Mul G] [Inv G] [AddCommGroup A] [SMul G A]

/--
Definition of `IsCycle₁` / `IsCycle₁` 的定义

English:
definition IsCycle₁
  signature: (x : G ->₀ A)
  body: x.sum (fun g a => g⁻¹ • a) = x.sum (fun _ a => a)

中文:
定义 IsCycle₁
  签名: (x : G ->₀ A)
  定义体: x.sum (fun g a => g⁻¹ • a) = x.sum (fun _ a => a)

Depends on / 依赖: x.sum
-/
def IsCycle₁ (x : G ->₀ A) : Prop := x.sum (fun g a => g⁻¹ • a) = x.sum (fun _ a => a)

/--
Definition of `IsCycle₂` / `IsCycle₂` 的定义

English:
definition IsCycle₂
  signature: (x : G × G ->₀ A)
  body: x.sum (fun g a => single g.2 (g.1⁻¹ • a) + single g.1 a) =
    x.sum (fun g a => single (g.1 * g.2) a)

中文:
定义 IsCycle₂
  签名: (x : G × G ->₀ A)
  定义体: x.sum (fun g a => single g.2 (g.1⁻¹ • a) + single g.1 a) =
    x.sum (fun g a => single (g.1 * g.2) a)

Depends on / 依赖: single, x.sum
-/
def IsCycle₂ (x : G × G ->₀ A) : Prop :=
  x.sum (fun g a => single g.2 (g.1⁻¹ • a) + single g.1 a) =
    x.sum (fun g a => single (g.1 * g.2) a)

end

section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

@[simp]
/--
theorem `single_isCycle₁_iff` / 定理 `single_isCycle₁_iff`

English:
theorem single_isCycle₁_iff
  given: (g : G) (a : A)
  proof: by
  rw [← (MulAction.bijective g⁻¹).1.eq_iff]
  simp [IsCycle₁, eq_comm]

中文:
定理 single_isCycle₁_iff
  条件: (g : G) (a : A)
  证明: by
  rw [← (MulAction.bijective g⁻¹).1.eq_iff]
  simp [IsCycle₁, eq_comm]

Depends on / 依赖: MulAction, MulAction.bijective, bijective, eq_comm, eq_iff
-/
theorem single_isCycle₁_iff (g : G) (a : A) :
    IsCycle₁ (single g a) ↔ g • a = a := by
  rw [← (MulAction.bijective g⁻¹).1.eq_iff]
  simp [IsCycle₁, eq_comm]

/--
theorem `single_isCycle₁_of_mem_fixedPoints` / 定理 `single_isCycle₁_of_mem_fixedPoints`

English:
theorem single_isCycle₁_of_mem_fixedPoints
  proof: by
  simp_all [IsCycle₁]

中文:
定理 single_isCycle₁_of_mem_fixedPoints
  证明: by
  simp_all [IsCycle₁]
-/
theorem single_isCycle₁_of_mem_fixedPoints
    (g : G) (a : A) (ha : a in MulAction.fixedPoints G A) :
    IsCycle₁ (single g a) := by
  simp_all [IsCycle₁]

/--
theorem `single_isCycle₂_iff_inv` / 定理 `single_isCycle₂_iff_inv`

English:
theorem single_isCycle₂_iff_inv
  given: (g : G × G) (a : A)
  proof: by
  simp [IsCycle₂]

@[simp]

中文:
定理 single_isCycle₂_iff_inv
  条件: (g : G × G) (a : A)
  证明: by
  simp [IsCycle₂]

@[simp]
-/
theorem single_isCycle₂_iff_inv (g : G × G) (a : A) :
    IsCycle₂ (single g a) ↔
      single g.2 (g.1⁻¹ • a) + single g.1 a = single (g.1 * g.2) a := by
  simp [IsCycle₂]

@[simp]
/--
theorem `single_isCycle₂_iff` / 定理 `single_isCycle₂_iff`

English:
theorem single_isCycle₂_iff
  given: (g : G × G) (a : A)
  proof: by
  rw [← (Finsupp.mapRange_injective (α := G) _ (smul_zero _) (MulAction.bijective g.1⁻¹).1).eq_iff]
  simp [mapRange_add, IsCycle₂]

中文:
定理 single_isCycle₂_iff
  条件: (g : G × G) (a : A)
  证明: by
  rw [← (Finsupp.mapRange_injective (α := G) _ (smul_zero _) (MulAction.bijective g.1⁻¹).1).eq_iff]
  simp [mapRange_add, IsCycle₂]

Depends on / 依赖: Finsupp, Finsupp.mapRange_injective, MulAction, MulAction.bijective, bijective, eq_iff, mapRange_add, mapRange_injective, smul_zero
-/
theorem single_isCycle₂_iff (g : G × G) (a : A) :
    IsCycle₂ (single g a) ↔
      single g.2 a + single g.1 (g.1 • a) = single (g.1 * g.2) (g.1 • a) := by
  rw [← (Finsupp.mapRange_injective (α := G) _ (smul_zero _) (MulAction.bijective g.1⁻¹).1).eq_iff]
  simp [mapRange_add, IsCycle₂]

end

end IsCycle

section IsBoundary

section

variable {G A : Type*} [Mul G] [Inv G] [AddCommGroup A] [SMul G A]

variable (G) in
/--
Definition of `IsBoundary₀` / `IsBoundary₀` 的定义

English:
definition IsBoundary₀
  signature: (a : A)
  body: exists (x : G ->₀ A), x.sum (fun g z => g⁻¹ • z - z) = a

中文:
定义 IsBoundary₀
  签名: (a : A)
  定义体: exists (x : G ->₀ A), x.sum (fun g z => g⁻¹ • z - z) = a

Depends on / 依赖: x.sum
-/
def IsBoundary₀ (a : A) : Prop :=
  exists (x : G ->₀ A), x.sum (fun g z => g⁻¹ • z - z) = a

/--
Definition of `IsBoundary₁` / `IsBoundary₁` 的定义

English:
definition IsBoundary₁
  signature: (x : G ->₀ A)
  body: exists y : G × G ->₀ A, y.sum
    (fun g a => single g.2 (g.1⁻¹ • a) - single (g.1 * g.2) a + single g.1 a) = x

中文:
定义 IsBoundary₁
  签名: (x : G ->₀ A)
  定义体: exists y : G × G ->₀ A, y.sum
    (fun g a => single g.2 (g.1⁻¹ • a) - single (g.1 * g.2) a + single g.1 a) = x

Depends on / 依赖: single, y.sum
-/
def IsBoundary₁ (x : G ->₀ A) : Prop :=
  exists y : G × G ->₀ A, y.sum
    (fun g a => single g.2 (g.1⁻¹ • a) - single (g.1 * g.2) a + single g.1 a) = x

/--
Definition of `IsBoundary₂` / `IsBoundary₂` 的定义

English:
definition IsBoundary₂
  signature: (x : G × G ->₀ A)
  body: exists y : G × G × G ->₀ A, y.sum (fun g a => single (g.2.1, g.2.2) (g.1⁻¹ • a) -
    single (g.1 * g.2.1, g.2.2) a + single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a) = x

中文:
定义 IsBoundary₂
  签名: (x : G × G ->₀ A)
  定义体: exists y : G × G × G ->₀ A, y.sum (fun g a => single (g.2.1, g.2.2) (g.1⁻¹ • a) -
    single (g.1 * g.2.1, g.2.2) a + single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a) = x

Depends on / 依赖: single, y.sum
-/
def IsBoundary₂ (x : G × G ->₀ A) : Prop :=
  exists y : G × G × G ->₀ A, y.sum (fun g a => single (g.2.1, g.2.2) (g.1⁻¹ • a) -
    single (g.1 * g.2.1, g.2.2) a + single (g.1, g.2.1 * g.2.2) a - single (g.1, g.2.1) a) = x

end

section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

variable (G) in
/--
theorem `isBoundary₀_iff` / 定理 `isBoundary₀_iff`

English:
theorem isBoundary₀_iff
  given: (a : A)
  proof: by
  constructor
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (-(g⁻¹ • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (-(g • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

中文:
定理 isBoundary₀_iff
  条件: (a : A)
  证明: by
  constructor
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (-(g⁻¹ • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (-(g • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

Depends on / 依赖: neg_add_eq_sub, single, sum_neg_index, sum_sum_index, x.sum
-/
theorem isBoundary₀_iff (a : A) :
    IsBoundary₀ G a ↔ exists x : G ->₀ A, x.sum (fun g z => g • z - z) = a := by
  constructor
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (-(g⁻¹ • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (-(g • a)))
    simp_all [sum_neg_index, sum_sum_index, neg_add_eq_sub]

/--
theorem `isBoundary₁_iff` / 定理 `isBoundary₁_iff`

English:
theorem isBoundary₁_iff
  given: (x : G ->₀ A)
  proof: by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_sum_index]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_sum_index]

中文:
定理 isBoundary₁_iff
  条件: (x : G ->₀ A)
  证明: by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_sum_index]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_sum_index]

Depends on / 依赖: single, sum_sum_index, x.sum, y.sum
-/
theorem isBoundary₁_iff (x : G ->₀ A) :
    IsBoundary₁ x ↔ exists y : G × G ->₀ A, y.sum
      (fun g a => single g.2 a - single (g.1 * g.2) (g.1 • a) + single g.1 (g.1 • a)) = x := by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_sum_index]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_sum_index]

/--
theorem `isBoundary₂_iff` / 定理 `isBoundary₂_iff`

English:
theorem isBoundary₂_iff
  given: (x : G × G ->₀ A)
  proof: by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_sum_index]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_sum_index]

中文:
定理 isBoundary₂_iff
  条件: (x : G × G ->₀ A)
  证明: by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_sum_index]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_sum_index]

Depends on / 依赖: single, sum_sum_index, x.sum, y.sum
-/
theorem isBoundary₂_iff (x : G × G ->₀ A) :
    IsBoundary₂ x ↔ exists y : G × G × G ->₀ A, y.sum
      (fun g a => single (g.2.1, g.2.2) a - single (g.1 * g.2.1, g.2.2) (g.1 • a) +
        single (g.1, g.2.1 * g.2.2) (g.1 • a) - single (g.1, g.2.1) (g.1 • a)) = x := by
  constructor
  · rintro ⟨y, hy⟩
    use y.sum (fun g a => single g (g.1⁻¹ • a))
    simp_all [sum_sum_index]
  · rintro ⟨x, hx⟩
    use x.sum (fun g a => single g (g.1 • a))
    simp_all [sum_sum_index]

end

end IsBoundary

section ofDistribMulAction

variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a term
`x : A` satisfying the 0-boundary condition, this produces an element of the kernel of the quotient
map `A → A_G` for the representation on `A` induced by the `DistribMulAction`. -/
@[simps]
/--
Definition of `coinvariantsKerOfIsBoundary₀` / `coinvariantsKerOfIsBoundary₀` 的定义

English:
definition coinvariantsKerOfIsBoundary₀
  signature: (x : A) (hx : IsBoundary₀ G x)
  body: ⟨x, by
    rcases (isBoundary₀_iff G x).1 hx with ⟨y, rfl⟩
    exact Submodule.finsuppSum_mem _ _ _ _ fun g _ => Coinvariants.mem_ker_of_eq g (y g) _ rfl⟩

中文:
定义 coinvariantsKerOfIsBoundary₀
  签名: (x : A) (hx : IsBoundary₀ G x)
  定义体: ⟨x, by
    rcases (isBoundary₀_iff G x).1 hx with ⟨y, rfl⟩
    exact Submodule.finsuppSum_mem _ _ _ _ fun g _ => Coinvariants.mem_ker_of_eq g (y g) _ rfl⟩

Depends on / 依赖: Coinvariants, Coinvariants.mem_ker_of_eq, Submodule, Submodule.finsuppSum_mem, finsuppSum_mem, mem_ker_of_eq
-/
def coinvariantsKerOfIsBoundary₀ (x : A) (hx : IsBoundary₀ G x) :
    Coinvariants.ker (Representation.ofDistribMulAction k G A) :=
  ⟨x, by
    rcases (isBoundary₀_iff G x).1 hx with ⟨y, rfl⟩
    exact Submodule.finsuppSum_mem _ _ _ _ fun g _ => Coinvariants.mem_ker_of_eq g (y g) _ rfl⟩

/--
theorem `isBoundary₀_of_mem_coinvariantsKer` / 定理 `isBoundary₀_of_mem_coinvariantsKer`

English:
theorem isBoundary₀_of_mem_coinvariantsKer
  proof: Submodule.span_induction (fun _ ⟨g, hg⟩ => ⟨single g.1⁻¹ g.2, by simp_all⟩) ⟨0, by simp⟩
    (fun _ _ _ _ ⟨X, hX⟩ ⟨Y, hY⟩ => ⟨X + Y, by simp_all [sum_add_index', add_sub_add_comm]⟩)
    (fun r _ _ ⟨X, hX⟩ => ⟨r • X, by simp [← hX, sum_smul_index', smul_comm, smul_sub, smul_sum]⟩)
    hx

中文:
定理 isBoundary₀_of_mem_coinvariantsKer
  证明: Submodule.span_induction (fun _ ⟨g, hg⟩ => ⟨single g.1⁻¹ g.2, by simp_all⟩) ⟨0, by simp⟩
    (fun _ _ _ _ ⟨X, hX⟩ ⟨Y, hY⟩ => ⟨X + Y, by simp_all [sum_add_index', add_sub_add_comm]⟩)
    (fun r _ _ ⟨X, hX⟩ => ⟨r • X, by simp [← hX, sum_smul_index', smul_comm, smul_sub, smul_sum]⟩)
    hx

Depends on / 依赖: Submodule, Submodule.span_induction, add_sub_add_comm, single, smul_comm, smul_sub, smul_sum, span_induction, sum_add_index, sum_smul_index
-/
theorem isBoundary₀_of_mem_coinvariantsKer
    (x : A) (hx : x in Coinvariants.ker (Representation.ofDistribMulAction k G A)) :
    IsBoundary₀ G x :=
  Submodule.span_induction (fun _ ⟨g, hg⟩ => ⟨single g.1⁻¹ g.2, by simp_all⟩) ⟨0, by simp⟩
    (fun _ _ _ _ ⟨X, hX⟩ ⟨Y, hY⟩ => ⟨X + Y, by simp_all [sum_add_index', add_sub_add_comm]⟩)
    (fun r _ _ ⟨X, hX⟩ => ⟨r • X, by simp [← hX, sum_smul_index', smul_comm, smul_sub, smul_sum]⟩)
    hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G →₀ A` satisfying the 1-cycle condition, produces a 1-cycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
/--
Definition of `cyclesOfIsCycle₁` / `cyclesOfIsCycle₁` 的定义

English:
definition cyclesOfIsCycle₁
  signature: (x : G ->₀ A) (hx : IsCycle₁ x)
  body: ⟨x, (mem_cycles₁_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

中文:
定义 cyclesOfIsCycle₁
  签名: (x : G ->₀ A) (hx : IsCycle₁ x)
  定义体: ⟨x, (mem_cycles₁_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

Depends on / 依赖: Rep.ofDistribMulAction, ofDistribMulAction
-/
def cyclesOfIsCycle₁ (x : G ->₀ A) (hx : IsCycle₁ x) :
    cycles₁ (Rep.ofDistribMulAction k G A) :=
  ⟨x, (mem_cycles₁_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

/--
theorem `isCycle₁_of_mem_cycles₁` / 定理 `isCycle₁_of_mem_cycles₁`

English:
theorem isCycle₁_of_mem_cycles₁
  proof: by
  simpa using! (mem_cycles₁_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

中文:
定理 isCycle₁_of_mem_cycles₁
  证明: by
  simpa using! (mem_cycles₁_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

Depends on / 依赖: Rep.ofDistribMulAction, ofDistribMulAction
-/
theorem isCycle₁_of_mem_cycles₁
    (x : G ->₀ A) (hx : x in cycles₁ (Rep.ofDistribMulAction k G A)) :
    IsCycle₁ x := by
  simpa using! (mem_cycles₁_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G →₀ A` satisfying the 1-boundary condition, produces a 1-boundary for the representation
on `A` induced by the `DistribMulAction`. -/
@[simps]
/--
Definition of `boundariesOfIsBoundary₁` / `boundariesOfIsBoundary₁` 的定义

English:
definition boundariesOfIsBoundary₁
  signature: (x : G ->₀ A) (hx : IsBoundary₁ x)
  body: ⟨x, hx⟩

中文:
定义 boundariesOfIsBoundary₁
  签名: (x : G ->₀ A) (hx : IsBoundary₁ x)
  定义体: ⟨x, hx⟩
-/
def boundariesOfIsBoundary₁ (x : G ->₀ A) (hx : IsBoundary₁ x) :
    boundaries₁ (Rep.ofDistribMulAction k G A) :=
  ⟨x, hx⟩

/--
theorem `isBoundary₁_of_mem_boundaries₁` / 定理 `isBoundary₁_of_mem_boundaries₁`

English:
theorem isBoundary₁_of_mem_boundaries₁
  proof: hx

中文:
定理 isBoundary₁_of_mem_boundaries₁
  证明: hx
-/
theorem isBoundary₁_of_mem_boundaries₁
    (x : G ->₀ A) (hx : x in boundaries₁ (Rep.ofDistribMulAction k G A)) :
    IsBoundary₁ x := hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G × G →₀ A` satisfying the 2-cycle condition, produces a 2-cycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
/--
Definition of `cyclesOfIsCycle₂` / `cyclesOfIsCycle₂` 的定义

English:
definition cyclesOfIsCycle₂
  signature: (x : G × G ->₀ A) (hx : IsCycle₂ x)
  body: ⟨x, (mem_cycles₂_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

中文:
定义 cyclesOfIsCycle₂
  签名: (x : G × G ->₀ A) (hx : IsCycle₂ x)
  定义体: ⟨x, (mem_cycles₂_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

Depends on / 依赖: Rep.ofDistribMulAction, ofDistribMulAction
-/
def cyclesOfIsCycle₂ (x : G × G ->₀ A) (hx : IsCycle₂ x) :
    cycles₂ (Rep.ofDistribMulAction k G A) :=
  ⟨x, (mem_cycles₂_iff (A := Rep.ofDistribMulAction k G A) x).2 hx⟩

/--
theorem `isCycle₂_of_mem_cycles₂` / 定理 `isCycle₂_of_mem_cycles₂`

English:
theorem isCycle₂_of_mem_cycles₂
  proof: (mem_cycles₂_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

中文:
定理 isCycle₂_of_mem_cycles₂
  证明: (mem_cycles₂_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

Depends on / 依赖: Rep.ofDistribMulAction, ofDistribMulAction
-/
theorem isCycle₂_of_mem_cycles₂
    (x : G × G ->₀ A) (hx : x in cycles₂ (Rep.ofDistribMulAction k G A)) :
    IsCycle₂ x := (mem_cycles₂_iff (A := Rep.ofDistribMulAction k G A) x).1 hx

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a finsupp
`x : G × G →₀ A` satisfying the 2-boundary condition, produces a 2-boundary for the
representation on `A` induced by the `DistribMulAction`. -/
@[simps]
/--
Definition of `boundariesOfIsBoundary₂` / `boundariesOfIsBoundary₂` 的定义

English:
definition boundariesOfIsBoundary₂
  signature: (x : G × G ->₀ A) (hx : IsBoundary₂ x)
  body: ⟨x, hx⟩

中文:
定义 boundariesOfIsBoundary₂
  签名: (x : G × G ->₀ A) (hx : IsBoundary₂ x)
  定义体: ⟨x, hx⟩
-/
def boundariesOfIsBoundary₂ (x : G × G ->₀ A) (hx : IsBoundary₂ x) :
    boundaries₂ (Rep.ofDistribMulAction k G A) :=
  ⟨x, hx⟩

/--
theorem `isBoundary₂_of_mem_boundaries₂` / 定理 `isBoundary₂_of_mem_boundaries₂`

English:
theorem isBoundary₂_of_mem_boundaries₂
  proof: hx

中文:
定理 isBoundary₂_of_mem_boundaries₂
  证明: hx
-/
theorem isBoundary₂_of_mem_boundaries₂
    (x : G × G ->₀ A) (hx : x in boundaries₂ (Rep.ofDistribMulAction k G A)) :
    IsBoundary₂ x := hx

end ofDistribMulAction

open ShortComplex

section cyclesIso₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (shortComplexH0 A).g
  body: inferInstanceAs Epi ((coinvariantsMk k G).app A)

中文:
实例 :
  签名: 满态射 (shortComplexH0 A).g
  定义体: inferInstanceAs Epi ((coinvariantsMk k G).app A)

Depends on / 依赖: coinvariantsMk
-/
instance : Epi (shortComplexH0 A).g := inferInstanceAs Epi ((coinvariantsMk k G).app A)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `shortComplexH0_exact` / 引理 `shortComplexH0_exact`

English:
lemma shortComplexH0_exact
  statement: (shortComplexH0 A).Exact
  proof: by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x (hx : Coinvariants.mk _ _ = 0)
  rw [Coinvariants.mk_eq_zero]; rw [← range_d₁₀_eq_coinvariantsKer] at hx
  rcases hx with ⟨x, hx, rfl⟩
  use x
  rfl

中文:
引理 shortComplexH0_exact
  结论: (shortComplexH0 A).正合
  证明: by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x (hx : Coinvariants.mk _ _ = 0)
  rw [Coinvariants.mk_eq_zero]; rw [← range_d₁₀_eq_coinvariantsKer] at hx
  rcases hx with ⟨x, hx, rfl⟩
  use x
  rfl

Depends on / 依赖: Coinvariants, Coinvariants.mk, Coinvariants.mk_eq_zero, ShortComplex, ShortComplex.moduleCat_exact_iff, mk_eq_zero, moduleCat_exact_iff
-/
lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x (hx : Coinvariants.mk _ _ = 0)
  rw [Coinvariants.mk_eq_zero]; rw [← range_d₁₀_eq_coinvariantsKer] at hx
  rcases hx with ⟨x, hx, rfl⟩
  use x
  rfl

/--
Definition of `cyclesIso₀` / `cyclesIso₀` 的定义

English:
definition cyclesIso₀
  signature: : cycles A 0 ≅ ModuleCat.of k A.V
  body: (inhomogeneousChains A).iCyclesIso _ 0 (by simp) (by simp [ChainComplex.of.d]) ≪≫ chainsIso₀ A

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定义 cyclesIso₀
  签名: : cycles A 0 ≅ 模范畴.of k A.V
  定义体: (inhomogeneousChains A).iCyclesIso _ 0 (by simp) (by simp [ChainComplex.of.d]) ≪≫ chainsIso₀ A

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: ChainComplex, ChainComplex.of.d, iCyclesIso, inhomogeneousChains
-/
def cyclesIso₀ : cycles A 0 ≅ ModuleCat.of k A.V :=
  (inhomogeneousChains A).iCyclesIso _ 0 (by simp) (by simp [ChainComplex.of.d]) ≪≫ chainsIso₀ A

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cyclesIso₀_inv_comp_iCycles` / 引理 `cyclesIso₀_inv_comp_iCycles`

English:
lemma cyclesIso₀_inv_comp_iCycles
  proof: by
  simp [cyclesIso₀]

中文:
引理 cyclesIso₀_inv_comp_iCycles
  证明: by
  simp [cyclesIso₀]
-/
lemma cyclesIso₀_inv_comp_iCycles :
    (cyclesIso₀ A).inv ≫ iCycles A 0 = (chainsIso₀ A).inv := by
  simp [cyclesIso₀]

/-- The arrow `(G →₀ A) --d₁₀--> A` is isomorphic to the differential
`(inhomogeneousChains A).d 1 0` of the complex of inhomogeneous chains of `A`. -/
@[simps! hom_left hom_right inv_left inv_right]
/--
Definition of `d₁₀ArrowIso` / `d₁₀ArrowIso` 的定义

English:
definition d₁₀ArrowIso
  signature: :
  body: Arrow.isoMk (chainsIso₁ A) (chainsIso₀ A) (comp_d₁₀_eq A)

中文:
定义 d₁₀ArrowIso
  签名: :
  定义体: Arrow.isoMk (chainsIso₁ A) (chainsIso₀ A) (comp_d₁₀_eq A)

Depends on / 依赖: Arrow.isoMk
-/
def d₁₀ArrowIso :
    Arrow.mk ((inhomogeneousChains A).d 1 0) ≅ Arrow.mk (d₁₀ A) :=
  Arrow.isoMk (chainsIso₁ A) (chainsIso₀ A) (comp_d₁₀_eq A)

/--
Definition of `opcyclesIso₀` / `opcyclesIso₀` 的定义

English:
definition opcyclesIso₀
  signature: : (inhomogeneousChains A).opcycles 0 ≅ (coinvariantsFunctor k G).obj A
  body: CokernelCofork.mapIsoOfIsColimit
    ((inhomogeneousChains A).opcyclesIsCokernel 1 0 (by simp)) (shortComplexH0_exact A).gIsCokernel
      (d₁₀ArrowIso A)

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定义 opcyclesIso₀
  签名: : (inhomogeneousChains A).opcycles 0 ≅ (coinvariantsFunctor k G).obj A
  定义体: CokernelCofork.mapIsoOfIsColimit
    ((inhomogeneousChains A).opcyclesIsCokernel 1 0 (by simp)) (shortComplexH0_exact A).gIsCokernel
      (d₁₀ArrowIso A)

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: CokernelCofork, CokernelCofork.mapIsoOfIsColimit, gIsCokernel, inhomogeneousChains, mapIsoOfIsColimit, opcyclesIsCokernel, shortComplexH0_exact
-/
def opcyclesIso₀ : (inhomogeneousChains A).opcycles 0 ≅ (coinvariantsFunctor k G).obj A :=
  CokernelCofork.mapIsoOfIsColimit
    ((inhomogeneousChains A).opcyclesIsCokernel 1 0 (by simp)) (shortComplexH0_exact A).gIsCokernel
      (d₁₀ArrowIso A)

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `pOpcycles_comp_opcyclesIso_hom` / 引理 `pOpcycles_comp_opcyclesIso_hom`

English:
lemma pOpcycles_comp_opcyclesIso_hom
  proof: CokernelCofork.π_mapOfIsColimit (φ := (d₁₀ArrowIso A).hom) _ _

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 pOpcycles_comp_opcyclesIso_hom
  证明: CokernelCofork.π_mapOfIsColimit (φ := (d₁₀ArrowIso A).hom) _ _

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: CokernelCofork
-/
lemma pOpcycles_comp_opcyclesIso_hom :
    (inhomogeneousChains A).pOpcycles 0 ≫ (opcyclesIso₀ A).hom =
      (chainsIso₀ A).hom ≫ (coinvariantsMk k G).app A :=
  CokernelCofork.π_mapOfIsColimit (φ := (d₁₀ArrowIso A).hom) _ _

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `coinvariantsMk_comp_opcyclesIso₀_inv` / 引理 `coinvariantsMk_comp_opcyclesIso₀_inv`

English:
lemma coinvariantsMk_comp_opcyclesIso₀_inv
  proof: (CommSq.vert_inv ⟨pOpcycles_comp_opcyclesIso_hom A⟩).w

中文:
引理 coinvariantsMk_comp_opcyclesIso₀_inv
  证明: (CommSq.vert_inv ⟨pOpcycles_comp_opcyclesIso_hom A⟩).w

Depends on / 依赖: CommSq, CommSq.vert_inv, pOpcycles_comp_opcyclesIso_hom, vert_inv
-/
lemma coinvariantsMk_comp_opcyclesIso₀_inv :
    (coinvariantsMk k G).app A ≫ (opcyclesIso₀ A).inv =
      (chainsIso₀ A).inv ≫ (inhomogeneousChains A).pOpcycles 0 :=
  (CommSq.vert_inv ⟨pOpcycles_comp_opcyclesIso_hom A⟩).w

/--
lemma `cyclesMk₀_eq` / 引理 `cyclesMk₀_eq`

English:
lemma cyclesMk₀_eq
  given: (x : A)
  proof: (ModuleCat.mono_iff_injective <| iCycles A 0).1 inferInstance by rw [iCycles_mk]; simp

中文:
引理 cyclesMk₀_eq
  条件: (x : A)
  证明: (ModuleCat.mono_iff_injective <| iCycles A 0).1 inferInstance by rw [iCycles_mk]; simp

Depends on / 依赖: ModuleCat, ModuleCat.mono_iff_injective, iCycles, iCycles_mk, mono_iff_injective
-/
lemma cyclesMk₀_eq (x : A) :
    cyclesMk 0 0 (by simp) ((chainsIso₀ A).inv x) (by simp [ChainComplex.of.d]) =
    (cyclesIso₀ A).inv x :=
(ModuleCat.mono_iff_injective <| iCycles A 0).1 inferInstance by rw [iCycles_mk]; simp

end cyclesIso₀

section isoCycles₁

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The short complex `(G² →₀ A) --d₂₁--> (G →₀ A) --d₁₀--> A` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous chains of `A`. -/
@[simps! hom inv]
/--
Definition of `isoShortComplexH1` / `isoShortComplexH1` 的定义

English:
definition isoShortComplexH1
  signature: : (inhomogeneousChains A).sc 1 ≅ shortComplexH1 A
  body: (inhomogeneousChains A).isoSc' 2 1 0 (by simp) (by simp) ≪≫
    isoMk (chainsIso₂ A) (chainsIso₁ A) (chainsIso₀ A) (comp_d₂₁_eq A) (comp_d₁₀_eq A)

中文:
定义 isoShortComplexH1
  签名: : (inhomogeneousChains A).sc 1 ≅ shortComplexH1 A
  定义体: (inhomogeneousChains A).isoSc' 2 1 0 (by simp) (by simp) ≪≫
    isoMk (chainsIso₂ A) (chainsIso₁ A) (chainsIso₀ A) (comp_d₂₁_eq A) (comp_d₁₀_eq A)

Depends on / 依赖: inhomogeneousChains
-/
def isoShortComplexH1 : (inhomogeneousChains A).sc 1 ≅ shortComplexH1 A :=
  (inhomogeneousChains A).isoSc' 2 1 0 (by simp) (by simp) ≪≫
    isoMk (chainsIso₂ A) (chainsIso₁ A) (chainsIso₀ A) (comp_d₂₁_eq A) (comp_d₁₀_eq A)

/--
Definition of `isoCycles₁` / `isoCycles₁` 的定义

English:
definition isoCycles₁
  signature: : cycles A 1 ≅ ModuleCat.of k (cycles₁ A)
  body: cyclesMapIso' (isoShortComplexH1 A) ((inhomogeneousChains A).sc 1).leftHomologyData
      (shortComplexH1 A).moduleCatLeftHomologyData

中文:
定义 isoCycles₁
  签名: : cycles A 1 ≅ 模范畴.of k (cycles₁ A)
  定义体: cyclesMapIso' (isoShortComplexH1 A) ((inhomogeneousChains A).sc 1).leftHomologyData
      (shortComplexH1 A).moduleCatLeftHomologyData

Depends on / 依赖: cyclesMapIso, inhomogeneousChains, isoShortComplexH1, leftHomologyData, moduleCatLeftHomologyData, shortComplexH1
-/
def isoCycles₁ : cycles A 1 ≅ ModuleCat.of k (cycles₁ A) :=
    cyclesMapIso' (isoShortComplexH1 A) ((inhomogeneousChains A).sc 1).leftHomologyData
      (shortComplexH1 A).moduleCatLeftHomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `isoCycles₁_hom_comp_i` / 引理 `isoCycles₁_hom_comp_i`

English:
lemma isoCycles₁_hom_comp_i
  proof: by
  simp [isoCycles₁, iCycles, HomologicalComplex.iCycles, ShortComplex.iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 isoCycles₁_hom_comp_i
  证明: by
  simp [isoCycles₁, iCycles, HomologicalComplex.iCycles, ShortComplex.iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.iCycles, ShortComplex, ShortComplex.iCycles, iCycles
-/
lemma isoCycles₁_hom_comp_i :
    (isoCycles₁ A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.i =
      iCycles A 1 ≫ (chainsIso₁ A).hom := by
  simp [isoCycles₁, iCycles, HomologicalComplex.iCycles, ShortComplex.iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `isoCycles₁_inv_comp_iCycles` / 引理 `isoCycles₁_inv_comp_iCycles`

English:
lemma isoCycles₁_inv_comp_iCycles
  proof: (CommSq.horiz_inv ⟨isoCycles₁_hom_comp_i A⟩).w

中文:
引理 isoCycles₁_inv_comp_iCycles
  证明: (CommSq.horiz_inv ⟨isoCycles₁_hom_comp_i A⟩).w

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
lemma isoCycles₁_inv_comp_iCycles :
    (isoCycles₁ A).inv ≫ iCycles A 1 =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ (chainsIso₁ A).inv :=
  (CommSq.horiz_inv ⟨isoCycles₁_hom_comp_i A⟩).w

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `toCycles_comp_isoCycles₁_hom` / 引理 `toCycles_comp_isoCycles₁_hom`

English:
lemma toCycles_comp_isoCycles₁_hom
  proof: by
  simp [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, comp_d₂₁_eq,
    shortComplexH1_f]

中文:
引理 toCycles_comp_isoCycles₁_hom
  证明: by
  simp [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, comp_d₂₁_eq,
    shortComplexH1_f]

Depends on / 依赖: cancel_mono, moduleCatLeftHomologyData, moduleCatLeftHomologyData.i, shortComplexH1, shortComplexH1_f
-/
lemma toCycles_comp_isoCycles₁_hom :
    toCycles A 2 1 ≫ (isoCycles₁ A).hom =
      (chainsIso₂ A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, comp_d₂₁_eq,
    shortComplexH1_f]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `cyclesMk₁_eq` / 引理 `cyclesMk₁_eq`

English:
lemma cyclesMk₁_eq
  given: (x : cycles₁ A)
  proof: (ModuleCat.mono_iff_injective <| iCycles A 1).1 inferInstance by
    rw [iCycles_mk]
    simp only [ChainComplex.of_X, isoCycles₁_inv_comp_iCycles_apply]
    rfl

中文:
引理 cyclesMk₁_eq
  条件: (x : cycles₁ A)
  证明: (ModuleCat.mono_iff_injective <| iCycles A 1).1 inferInstance by
    rw [iCycles_mk]
    simp only [ChainComplex.of_X, isoCycles₁_inv_comp_iCycles_apply]
    rfl

Depends on / 依赖: ChainComplex, ChainComplex.of_X, ModuleCat, ModuleCat.mono_iff_injective, iCycles, iCycles_mk, mono_iff_injective, of_X
-/
lemma cyclesMk₁_eq (x : cycles₁ A) :
    cyclesMk 1 0 (by simp) ((chainsIso₁ A).inv x) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₁₀_comp_inv]; simp) =
      (isoCycles₁ A).inv x :=
(ModuleCat.mono_iff_injective <| iCycles A 1).1 inferInstance by
    rw [iCycles_mk]
    simp only [ChainComplex.of_X, isoCycles₁_inv_comp_iCycles_apply]
    rfl

end isoCycles₁

section isoCycles₂

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The short complex `(G³ →₀ A) --d₃₂--> (G² →₀ A) --d₂₁--> (G →₀ A)` is isomorphic to the 2nd
short complex associated to the complex of inhomogeneous chains of `A`. -/
@[simps! hom inv]
/--
Definition of `isoShortComplexH2` / `isoShortComplexH2` 的定义

English:
definition isoShortComplexH2
  signature: : (inhomogeneousChains A).sc 2 ≅ shortComplexH2 A
  body: (inhomogeneousChains A).isoSc' 3 2 1 (by simp) (by simp) ≪≫
    isoMk (chainsIso₃ A) (chainsIso₂ A) (chainsIso₁ A) (comp_d₃₂_eq A) (comp_d₂₁_eq A)

中文:
定义 isoShortComplexH2
  签名: : (inhomogeneousChains A).sc 2 ≅ shortComplexH2 A
  定义体: (inhomogeneousChains A).isoSc' 3 2 1 (by simp) (by simp) ≪≫
    isoMk (chainsIso₃ A) (chainsIso₂ A) (chainsIso₁ A) (comp_d₃₂_eq A) (comp_d₂₁_eq A)

Depends on / 依赖: inhomogeneousChains
-/
def isoShortComplexH2 : (inhomogeneousChains A).sc 2 ≅ shortComplexH2 A :=
  (inhomogeneousChains A).isoSc' 3 2 1 (by simp) (by simp) ≪≫
    isoMk (chainsIso₃ A) (chainsIso₂ A) (chainsIso₁ A) (comp_d₃₂_eq A) (comp_d₂₁_eq A)

/--
Definition of `isoCycles₂` / `isoCycles₂` 的定义

English:
definition isoCycles₂
  signature: : cycles A 2 ≅ ModuleCat.of k (cycles₂ A)
  body: cyclesMapIso' (isoShortComplexH2 A) ((inhomogeneousChains A).sc 2).leftHomologyData
      (shortComplexH2 A).moduleCatLeftHomologyData

中文:
定义 isoCycles₂
  签名: : cycles A 2 ≅ 模范畴.of k (cycles₂ A)
  定义体: cyclesMapIso' (isoShortComplexH2 A) ((inhomogeneousChains A).sc 2).leftHomologyData
      (shortComplexH2 A).moduleCatLeftHomologyData

Depends on / 依赖: cyclesMapIso, inhomogeneousChains, isoShortComplexH2, leftHomologyData, moduleCatLeftHomologyData, shortComplexH2
-/
def isoCycles₂ : cycles A 2 ≅ ModuleCat.of k (cycles₂ A) :=
    cyclesMapIso' (isoShortComplexH2 A) ((inhomogeneousChains A).sc 2).leftHomologyData
      (shortComplexH2 A).moduleCatLeftHomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `isoCycles₂_hom_comp_i` / 引理 `isoCycles₂_hom_comp_i`

English:
lemma isoCycles₂_hom_comp_i
  proof: by
  simp [isoCycles₂, iCycles, HomologicalComplex.iCycles, ShortComplex.iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 isoCycles₂_hom_comp_i
  证明: by
  simp [isoCycles₂, iCycles, HomologicalComplex.iCycles, ShortComplex.iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.iCycles, ShortComplex, ShortComplex.iCycles, iCycles
-/
lemma isoCycles₂_hom_comp_i :
    (isoCycles₂ A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.i =
      iCycles A 2 ≫ (chainsIso₂ A).hom := by
  simp [isoCycles₂, iCycles, HomologicalComplex.iCycles, ShortComplex.iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `isoCycles₂_inv_comp_iCycles` / 引理 `isoCycles₂_inv_comp_iCycles`

English:
lemma isoCycles₂_inv_comp_iCycles
  proof: (CommSq.horiz_inv ⟨isoCycles₂_hom_comp_i A⟩).w

中文:
引理 isoCycles₂_inv_comp_iCycles
  证明: (CommSq.horiz_inv ⟨isoCycles₂_hom_comp_i A⟩).w

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
lemma isoCycles₂_inv_comp_iCycles :
    (isoCycles₂ A).inv ≫ iCycles A 2 =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ (chainsIso₂ A).inv :=
  (CommSq.horiz_inv ⟨isoCycles₂_hom_comp_i A⟩).w

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `toCycles_comp_isoCycles₂_hom` / 引理 `toCycles_comp_isoCycles₂_hom`

English:
lemma toCycles_comp_isoCycles₂_hom
  proof: by
  simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, comp_d₃₂_eq,
    shortComplexH2_f]

中文:
引理 toCycles_comp_isoCycles₂_hom
  证明: by
  simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, comp_d₃₂_eq,
    shortComplexH2_f]

Depends on / 依赖: cancel_mono, moduleCatLeftHomologyData, moduleCatLeftHomologyData.i, shortComplexH2, shortComplexH2_f
-/
lemma toCycles_comp_isoCycles₂_hom :
    toCycles A 3 2 ≫ (isoCycles₂ A).hom =
      (chainsIso₃ A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, comp_d₃₂_eq,
    shortComplexH2_f]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `cyclesMk₂_eq` / 引理 `cyclesMk₂_eq`

English:
lemma cyclesMk₂_eq
  given: (x : cycles₂ A)
  proof: (ModuleCat.mono_iff_injective <| iCycles A 2).1 inferInstance by
    rw [iCycles_mk]
    simp only [ChainComplex.of_X, isoCycles₂_inv_comp_iCycles_apply]
    rfl

中文:
引理 cyclesMk₂_eq
  条件: (x : cycles₂ A)
  证明: (ModuleCat.mono_iff_injective <| iCycles A 2).1 inferInstance by
    rw [iCycles_mk]
    simp only [ChainComplex.of_X, isoCycles₂_inv_comp_iCycles_apply]
    rfl

Depends on / 依赖: ChainComplex, ChainComplex.of_X, ModuleCat, ModuleCat.mono_iff_injective, iCycles, iCycles_mk, mono_iff_injective, of_X
-/
lemma cyclesMk₂_eq (x : cycles₂ A) :
    cyclesMk 2 1 (by simp) ((chainsIso₂ A).inv x) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [eq_d₂₁_comp_inv]
      simp) = (isoCycles₂ A).inv x :=
(ModuleCat.mono_iff_injective <| iCycles A 2).1 inferInstance by
    rw [iCycles_mk]
    simp only [ChainComplex.of_X, isoCycles₂_inv_comp_iCycles_apply]
    rfl

end isoCycles₂

section Homology

section H0

/--
Definition of `H0` / `H0` 的定义

English:
abbreviation H0
  body: groupHomology A 0

中文:
缩写 H0
  定义体: groupHomology A 0

Depends on / 依赖: groupHomology
-/
abbrev H0 := groupHomology A 0

/--
Definition of `H0Iso` / `H0Iso` 的定义

English:
definition H0Iso
  signature: : H0 A ≅ (coinvariantsFunctor k G).obj A
  body: (ChainComplex.isoHomologyι₀ _) ≪≫ opcyclesIso₀ A

中文:
定义 H0Iso
  签名: : H0 A ≅ (coinvariantsFunctor k G).obj A
  定义体: (ChainComplex.isoHomologyι₀ _) ≪≫ opcyclesIso₀ A

Depends on / 依赖: ChainComplex, ChainComplex.isoHomology
-/
def H0Iso : H0 A ≅ (coinvariantsFunctor k G).obj A :=
  (ChainComplex.isoHomologyι₀ _) ≪≫ opcyclesIso₀ A

/--
Definition of `H0π` / `H0π` 的定义

English:
definition H0π
  signature: : ModuleCat.of k A.V ⟶ H0 A
  body: (cyclesIso₀ A).inv ≫ π A 0

中文:
定义 H0π
  签名: : 模范畴.of k A.V ⟶ H0 A
  定义体: (cyclesIso₀ A).inv ≫ π A 0
-/
def H0π : ModuleCat.of k A.V ⟶ H0 A := (cyclesIso₀ A).inv ≫ π A 0

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (H0π A)
  body: inferInstanceAs Epi (_ ≫ _)

中文:
实例 :
  签名: 满态射 (H0π A)
  定义体: inferInstanceAs Epi (_ ≫ _)
-/
instance : Epi (H0π A) := inferInstanceAs Epi (_ ≫ _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `π_comp_H0Iso_hom` / 引理 `π_comp_H0Iso_hom`

English:
lemma π_comp_H0Iso_hom
  proof: by
  simp [H0Iso, cyclesIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 π_comp_H0Iso_hom
  证明: by
  simp [H0Iso, cyclesIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]
-/
lemma π_comp_H0Iso_hom :
    π A 0 ≫ (H0Iso A).hom = (cyclesIso₀ A).hom ≫ (coinvariantsMk k G).app A := by
  simp [H0Iso, cyclesIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `coinvariantsMk_comp_H0Iso_inv` / 引理 `coinvariantsMk_comp_H0Iso_inv`

English:
lemma coinvariantsMk_comp_H0Iso_inv
  proof: (CommSq.vert_inv ⟨π_comp_H0Iso_hom A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 coinvariantsMk_comp_H0Iso_inv
  证明: (CommSq.vert_inv ⟨π_comp_H0Iso_hom A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: CommSq, CommSq.vert_inv, vert_inv
-/
lemma coinvariantsMk_comp_H0Iso_inv :
    (coinvariantsMk k G).app A ≫ (H0Iso A).inv = H0π A :=
  (CommSq.vert_inv ⟨π_comp_H0Iso_hom A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `H0π_comp_H0Iso_hom` / 引理 `H0π_comp_H0Iso_hom`

English:
lemma H0π_comp_H0Iso_hom
  proof: by
  simp [H0π]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 H0π_comp_H0Iso_hom
  证明: by
  simp [H0π]

@[reassoc (attr := simp), elementwise (attr := simp)]
-/
lemma H0π_comp_H0Iso_hom :
    H0π A ≫ (H0Iso A).hom = (coinvariantsMk k G).app A := by
  simp [H0π]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cyclesIso₀_comp_H0π` / 引理 `cyclesIso₀_comp_H0π`

English:
lemma cyclesIso₀_comp_H0π
  proof: by
  simp [H0π]

@[elab_as_elim]

中文:
引理 cyclesIso₀_comp_H0π
  证明: by
  simp [H0π]

@[elab_as_elim]
-/
lemma cyclesIso₀_comp_H0π :
    (cyclesIso₀ A).hom ≫ H0π A = π A 0 := by
  simp [H0π]

@[elab_as_elim]
/--
theorem `H0_induction_on` / 定理 `H0_induction_on`

English:
theorem H0_induction_on
  statement: {C : H0 A -> Prop} (x : H0 A)
  proof: groupHomology_induction_on x fun y => by simpa using h ((cyclesIso₀ A).hom y)

中文:
定理 H0_induction_on
  结论: {C : H0 A -> 命题} (x : H0 A)
  证明: groupHomology_induction_on x fun y => by simpa using h ((cyclesIso₀ A).hom y)

Depends on / 依赖: groupHomology_induction_on
-/
theorem H0_induction_on {C : H0 A -> Prop} (x : H0 A)
    (h : forall x : A, C (H0π A x)) : C x :=
  groupHomology_induction_on x fun y => by simpa using h ((cyclesIso₀ A).hom y)

section IsTrivial

variable [A.IsTrivial]

/--
Definition of `H0IsoOfIsTrivial` / `H0IsoOfIsTrivial` 的定义

English:
definition H0IsoOfIsTrivial
  signature: :
  body: ((inhomogeneousChains A).isoHomologyπ 1 0 (by simp) <| by
    ext; simp [inhomogeneousChains.d_single (G := G), ChainComplex.of.d,
       Unique.eq_default (α := Fin 0 -> G)]).symm ≪≫ cyclesIso₀ A

@[simp]

中文:
定义 H0IsoOfIsTrivial
  签名: :
  定义体: ((inhomogeneousChains A).isoHomologyπ 1 0 (by simp) <| by
    ext; simp [inhomogeneousChains.d_single (G := G), ChainComplex.of.d,
       Unique.eq_default (α := Fin 0 -> G)]).symm ≪≫ cyclesIso₀ A

@[simp]

Depends on / 依赖: ChainComplex, ChainComplex.of.d, Unique, Unique.eq_default, d_single, eq_default, inhomogeneousChains, inhomogeneousChains.d_single
-/
def H0IsoOfIsTrivial :
    H0 A ≅ ModuleCat.of k A.V :=
  ((inhomogeneousChains A).isoHomologyπ 1 0 (by simp) <| by
    ext; simp [inhomogeneousChains.d_single (G := G), ChainComplex.of.d,
       Unique.eq_default (α := Fin 0 -> G)]).symm ≪≫ cyclesIso₀ A

@[simp]
/--
theorem `H0IsoOfIsTrivial_inv_eq_π` / 定理 `H0IsoOfIsTrivial_inv_eq_π`

English:
theorem H0IsoOfIsTrivial_inv_eq_π
  proof: rfl

中文:
定理 H0IsoOfIsTrivial_inv_eq_π
  证明: rfl
-/
theorem H0IsoOfIsTrivial_inv_eq_π :
    (H0IsoOfIsTrivial A).inv = H0π A := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `π_comp_H0IsoOfIsTrivial_hom` / 定理 `π_comp_H0IsoOfIsTrivial_hom`

English:
theorem π_comp_H0IsoOfIsTrivial_hom
  proof: by
  simp [H0IsoOfIsTrivial]

中文:
定理 π_comp_H0IsoOfIsTrivial_hom
  证明: by
  simp [H0IsoOfIsTrivial]

Depends on / 依赖: H0IsoOfIsTrivial
-/
theorem π_comp_H0IsoOfIsTrivial_hom :
    π A 0 ≫ (H0IsoOfIsTrivial A).hom = (cyclesIso₀ A).hom := by
  simp [H0IsoOfIsTrivial]

end IsTrivial

end H0

section H1

/--
Definition of `H1` / `H1` 的定义

English:
abbreviation H1
  body: groupHomology A 1

中文:
缩写 H1
  定义体: groupHomology A 1

Depends on / 依赖: groupHomology
-/
abbrev H1 := groupHomology A 1

/--
Definition of `H1π` / `H1π` 的定义

English:
definition H1π
  signature: : ModuleCat.of k (cycles₁ A) ⟶ H1 A
  body: (isoCycles₁ A).inv ≫ π A 1

中文:
定义 H1π
  签名: : 模范畴.of k (cycles₁ A) ⟶ H1 A
  定义体: (isoCycles₁ A).inv ≫ π A 1
-/
def H1π : ModuleCat.of k (cycles₁ A) ⟶ H1 A :=
  (isoCycles₁ A).inv ≫ π A 1

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (H1π A)
  body: inferInstanceAs Epi (_ ≫ _)

中文:
实例 :
  签名: 满态射 (H1π A)
  定义体: inferInstanceAs Epi (_ ≫ _)
-/
instance : Epi (H1π A) := inferInstanceAs Epi (_ ≫ _)

variable {A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `H1π_eq_zero_iff` / 引理 `H1π_eq_zero_iff`

English:
lemma H1π_eq_zero_iff
  given: (x : cycles₁ A)
  statement: H1π A x = 0 ↔ x.1 in boundaries₁ A
  proof: by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH1 A).inv
    (shortComplexH1 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousChains A).sc 1).leftHomologyIso.hom
  simp only [H1π, isoCycles₁, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, boundaries₁, shortComplexH1, cycles₁]

中文:
引理 H1π_eq_zero_iff
  条件: (x : cycles₁ A)
  结论: H1π A x = 0 ↔ x.1 in boundaries₁ A
  证明: by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH1 A).inv
    (shortComplexH1 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousChains A).sc 1).leftHomologyIso.hom
  simp only [H1π, isoCycles₁, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, boundaries₁, shortComplexH1, cycles₁]

Depends on / 依赖: Function, Function.comp_apply, HomologicalComplex, HomologicalComplex.homology, LinearMap, LinearMap.coe_comp, LinearMap.range_codRestrict, ModuleCat, ModuleCat.hom_comp, ModuleCat.mono_iff_injective, _assoc, _inv, coe_comp, comp_apply, cyclesMapIso, hom_comp, inhomogeneousChains, isoShortComplexH1, leftHomologyData, leftHomologyIso
-/
lemma H1π_eq_zero_iff (x : cycles₁ A) : H1π A x = 0 ↔ x.1 in boundaries₁ A := by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH1 A).inv
    (shortComplexH1 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousChains A).sc 1).leftHomologyIso.hom
  simp only [H1π, isoCycles₁, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, boundaries₁, shortComplexH1, cycles₁]

/--
lemma `H1π_eq_iff` / 引理 `H1π_eq_iff`

English:
lemma H1π_eq_iff
  given: (x y : cycles₁ A)
  proof: by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H1π_eq_zero_iff]
  rfl

@[elab_as_elim]

中文:
引理 H1π_eq_iff
  条件: (x y : cycles₁ A)
  证明: by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H1π_eq_zero_iff]
  rfl

@[elab_as_elim]

Depends on / 依赖: map_sub, sub_eq_zero
-/
lemma H1π_eq_iff (x y : cycles₁ A) :
    H1π A x = H1π A y ↔ x.1 - y.1 in boundaries₁ A := by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H1π_eq_zero_iff]
  rfl

@[elab_as_elim]
/--
theorem `H1_induction_on` / 定理 `H1_induction_on`

English:
theorem H1_induction_on
  given: {C : H1 A -> Prop} (x : H1 A) (h : forall x : cycles₁ A, C (H1π A x))
  proof: groupHomology_induction_on x fun y => by simpa [H1π] using h ((isoCycles₁ A).hom y)

中文:
定理 H1_induction_on
  条件: {C : H1 A -> 命题} (x : H1 A) (h : 对任意 x : cycles₁ A, C (H1π A x))
  证明: groupHomology_induction_on x fun y => by simpa [H1π] using h ((isoCycles₁ A).hom y)

Depends on / 依赖: groupHomology_induction_on
-/
theorem H1_induction_on {C : H1 A -> Prop} (x : H1 A) (h : forall x : cycles₁ A, C (H1π A x)) :
    C x :=
  groupHomology_induction_on x fun y => by simpa [H1π] using h ((isoCycles₁ A).hom y)

variable (A)

/--
Definition of `H1Iso` / `H1Iso` 的定义

English:
definition H1Iso
  signature: : H1 A ≅ (shortComplexH1 A).moduleCatLeftHomologyData.H
  body: (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (isoShortComplexH1 A) _ _)

中文:
定义 H1Iso
  签名: : H1 A ≅ (shortComplexH1 A).moduleCatLeftHomologyData.H
  定义体: (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (isoShortComplexH1 A) _ _)

Depends on / 依赖: isoShortComplexH1, leftHomologyIso, leftHomologyMapIso
-/
def H1Iso : H1 A ≅ (shortComplexH1 A).moduleCatLeftHomologyData.H :=
  (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (isoShortComplexH1 A) _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `π_comp_H1Iso_hom` / 引理 `π_comp_H1Iso_hom`

English:
lemma π_comp_H1Iso_hom
  proof: by
  simp [H1Iso, isoCycles₁, π, HomologicalComplex.homologyπ, leftHomologyπ]

中文:
引理 π_comp_H1Iso_hom
  证明: by
  simp [H1Iso, isoCycles₁, π, HomologicalComplex.homologyπ, leftHomologyπ]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homology
-/
lemma π_comp_H1Iso_hom :
    π A 1 ≫ (H1Iso A).hom = (isoCycles₁ A).hom ≫
      (shortComplexH1 A).moduleCatLeftHomologyData.π := by
  simp [H1Iso, isoCycles₁, π, HomologicalComplex.homologyπ, leftHomologyπ]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `π_comp_H1Iso_inv` / 引理 `π_comp_H1Iso_inv`

English:
lemma π_comp_H1Iso_inv
  proof: (CommSq.vert_inv ⟨π_comp_H1Iso_hom A⟩).w

中文:
引理 π_comp_H1Iso_inv
  证明: (CommSq.vert_inv ⟨π_comp_H1Iso_hom A⟩).w

Depends on / 依赖: CommSq, CommSq.vert_inv, MonoidHom, MonoidHom.map_zpowers, MonoidHom.range_eq_map, Subgroup, Subgroup.subtype_range, generator_zpowers_eq_valueGroup, map_subtype_inj, map_zpowers, range_eq_map, subtype_apply, subtype_range, vert_inv
-/
lemma π_comp_H1Iso_inv :
    (shortComplexH1 A).moduleCatLeftHomologyData.π ≫ (H1Iso A).inv = H1π A :=
  (CommSq.vert_inv ⟨π_comp_H1Iso_hom A⟩).w

section IsTrivial

variable [A.IsTrivial]

open TensorProduct

/--
Definition of `mkH1OfIsTrivial` / `mkH1OfIsTrivial` 的定义

English:
definition mkH1OfIsTrivial
  signature: : Additive (Abelianization G) ->ₗ[Int] A ->ₗ[Int] H1 A
  body: AddMonoidHom.toIntLinearMap AddMonoidHom.toMultiplicativeRight.symm Abelianization.lift {
    toFun g := Multiplicative.ofAdd (AddMonoidHom.toIntLinearMap (AddMonoidHomClass.toAddMonoidHom
      ((H1π A).hom ∘ₗ (cycles₁IsoOfIsTrivial A).inv.hom ∘ₗ lsingle g)))
map_one' := Multiplicative.toAdd.injective
LinearMap.ext fun _ => (H1π_eq_zero_iff _).2 single_one_mem_boundaries₁ _
map_mul' g h := Multiplicative.toAdd.injective LinearMap.ext fun a => by
      simpa [← map_add] using ((H1π_eq_iff _ _).2 ⟨single (g, h) a, by
        simp [cycles₁IsoOfIsTrivial, sub_add_eq_add_sub, add_comm (single h a),
          d₂₁_single (A := A)]⟩).symm }

中文:
定义 mkH1OfIsTrivial
  签名: : 加性 (交换化 G) ->ₗ[整数] A ->ₗ[整数] H1 A
  定义体: AddMonoidHom.toIntLinearMap AddMonoidHom.toMultiplicativeRight.symm Abelianization.lift {
    toFun g := Multiplicative.ofAdd (AddMonoidHom.toIntLinearMap (AddMonoidHomClass.toAddMonoidHom
      ((H1π A).hom ∘ₗ (cycles₁IsoOfIsTrivial A).inv.hom ∘ₗ lsingle g)))
map_one' := Multiplicative.toAdd.injective
LinearMap.ext fun _ => (H1π_eq_zero_iff _).2 single_one_mem_boundaries₁ _
map_mul' g h := Multiplicative.toAdd.injective LinearMap.ext fun a => by
      simpa [← map_add] using ((H1π_eq_iff _ _).2 ⟨single (g, h) a, by
        simp [cycles₁IsoOfIsTrivial, sub_add_eq_add_sub, add_comm (single h a),
          d₂₁_single (A := A)]⟩).symm }

Depends on / 依赖: Abelianization, Abelianization.lift, AddMonoidHom, AddMonoidHom.toIntLinearMap, AddMonoidHom.toMultiplicativeRight.symm, AddMonoidHomClass, AddMonoidHomClass.toAddMonoidHom, LinearMap, LinearMap.ext, Multiplicative, Multiplicative.ofAdd, Multiplicative.toAdd.injective, choose_spec, exists_generator_lt_one, injective, inv.hom, lsingle, map_add, map_mul, map_one
-/
def mkH1OfIsTrivial : Additive (Abelianization G) ->ₗ[Int] A ->ₗ[Int] H1 A :=
AddMonoidHom.toIntLinearMap AddMonoidHom.toMultiplicativeRight.symm Abelianization.lift {
    toFun g := Multiplicative.ofAdd (AddMonoidHom.toIntLinearMap (AddMonoidHomClass.toAddMonoidHom
      ((H1π A).hom ∘ₗ (cycles₁IsoOfIsTrivial A).inv.hom ∘ₗ lsingle g)))
map_one' := Multiplicative.toAdd.injective
LinearMap.ext fun _ => (H1π_eq_zero_iff _).2 single_one_mem_boundaries₁ _
map_mul' g h := Multiplicative.toAdd.injective LinearMap.ext fun a => by
      simpa [← map_add] using ((H1π_eq_iff _ _).2 ⟨single (g, h) a, by
        simp [cycles₁IsoOfIsTrivial, sub_add_eq_add_sub, add_comm (single h a),
          d₂₁_single (A := A)]⟩).symm }

variable {A} in
@[simp]
/--
lemma `mkH1OfIsTrivial_apply` / 引理 `mkH1OfIsTrivial_apply`

English:
lemma mkH1OfIsTrivial_apply
  given: (g : G) (a : A)
  proof: rfl

中文:
引理 mkH1OfIsTrivial_apply
  条件: (g : G) (a : A)
  证明: rfl
-/
lemma mkH1OfIsTrivial_apply (g : G) (a : A) :
    mkH1OfIsTrivial A (Additive.ofMul (Abelianization.of g)) a =
      H1π A ((cycles₁IsoOfIsTrivial A).inv (single g a)) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `H1ToTensorOfIsTrivial` / `H1ToTensorOfIsTrivial` 的定义

English:
definition H1ToTensorOfIsTrivial
  signature: : H1 A ->ₗ[Int] (Additive <| Abelianization G) otimes[Int] A
  body: ((QuotientAddGroup.lift _ ((Finsupp.liftAddHom fun g => AddMonoidHomClass.toAddMonoidHom
    (TensorProduct.mk Int _ _ (Additive.ofMul (Abelianization.of g)))).comp
      (cycles₁ A).toAddSubgroup.subtype) fun ⟨y, hy⟩ ⟨z, hz⟩ => AddMonoidHom.mem_ker.2 <| by
      simp [← hz, d₂₁, sum_sum_index, sum_add_index', tmul_add, sum_sub_index, tmul_sub,
        shortComplexH1]).comp <| AddMonoidHomClass.toAddMonoidHom (H1Iso A).hom.hom).toIntLinearMap

中文:
定义 H1ToTensorOfIsTrivial
  签名: : H1 A ->ₗ[整数] (加性 <| 交换化 G) otimes[整数] A
  定义体: ((QuotientAddGroup.lift _ ((Finsupp.liftAddHom fun g => AddMonoidHomClass.toAddMonoidHom
    (TensorProduct.mk Int _ _ (Additive.ofMul (Abelianization.of g)))).comp
      (cycles₁ A).toAddSubgroup.subtype) fun ⟨y, hy⟩ ⟨z, hz⟩ => AddMonoidHom.mem_ker.2 <| by
      simp [← hz, d₂₁, sum_sum_index, sum_add_index', tmul_add, sum_sub_index, tmul_sub,
        shortComplexH1]).comp <| AddMonoidHomClass.toAddMonoidHom (H1Iso A).hom.hom).toIntLinearMap

Depends on / 依赖: Abelianization, Abelianization.of, AddMonoidHom, AddMonoidHom.mem_ker, AddMonoidHomClass, AddMonoidHomClass.toAddMonoidHom, Additive, Additive.ofMul, Finsupp, Finsupp.liftAddHom, QuotientAddGroup, QuotientAddGroup.lift, TensorProduct, TensorProduct.mk, hom.hom, liftAddHom, mem_ker, shortComplexH1, subtype, sum_add_index
-/
def H1ToTensorOfIsTrivial : H1 A ->ₗ[Int] (Additive <| Abelianization G) otimes[Int] A :=
  ((QuotientAddGroup.lift _ ((Finsupp.liftAddHom fun g => AddMonoidHomClass.toAddMonoidHom
    (TensorProduct.mk Int _ _ (Additive.ofMul (Abelianization.of g)))).comp
      (cycles₁ A).toAddSubgroup.subtype) fun ⟨y, hy⟩ ⟨z, hz⟩ => AddMonoidHom.mem_ker.2 <| by
      simp [← hz, d₂₁, sum_sum_index, sum_add_index', tmul_add, sum_sub_index, tmul_sub,
        shortComplexH1]).comp <| AddMonoidHomClass.toAddMonoidHom (H1Iso A).hom.hom).toIntLinearMap

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {A} in
@[simp]
/--
lemma `H1ToTensorOfIsTrivial_H1π_single` / 引理 `H1ToTensorOfIsTrivial_H1π_single`

English:
lemma H1ToTensorOfIsTrivial_H1π_single
  given: (g : G) (a : A)
  proof: by
  simp only [H1ToTensorOfIsTrivial, H1π, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp]
  -- todo: change this proof so that we don't need `change` that abuses defeq.
  change QuotientAddGroup.lift _ _ _ ((H1Iso A).hom _) = _
  simp [π_comp_H1Iso_hom_apply, ← Submodule.Quotient.quotientAddGroupMk_eq_mk, Submodule.mkQ,
    AddSubgroup.subtype, cycles₁IsoOfIsTrivial]

中文:
引理 H1ToTensorOfIsTrivial_H1π_single
  条件: (g : G) (a : A)
  证明: by
  simp only [H1ToTensorOfIsTrivial, H1π, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp]
  -- todo: change this proof so that we don't need `change` that abuses defeq.
  change QuotientAddGroup.lift _ _ _ ((H1Iso A).hom _) = _
  simp [π_comp_H1Iso_hom_apply, ← Submodule.Quotient.quotientAddGroupMk_eq_mk, Submodule.mkQ,
    AddSubgroup.subtype, cycles₁IsoOfIsTrivial]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_comp, AddMonoidHom.coe_toIntLinearMap, H1ToTensorOfIsTrivial, coe_comp, coe_toIntLinearMap
-/
lemma H1ToTensorOfIsTrivial_H1π_single (g : G) (a : A) :
    H1ToTensorOfIsTrivial A (H1π A <| (cycles₁IsoOfIsTrivial A).inv (single g a)) =
      Additive.ofMul (Abelianization.of g) otimesₜ[Int] a := by
  simp only [H1ToTensorOfIsTrivial, H1π, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp]
  -- todo: change this proof so that we don't need `change` that abuses defeq.
  change QuotientAddGroup.lift _ _ _ ((H1Iso A).hom _) = _
  simp [π_comp_H1Iso_hom_apply, ← Submodule.Quotient.quotientAddGroupMk_eq_mk, Submodule.mkQ,
    AddSubgroup.subtype, cycles₁IsoOfIsTrivial]

set_option backward.isDefEq.respectTransparency false in
/-- If a `G`-representation on `A` is trivial, this is the group isomorphism between
`H₁(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A` defined by `⟦single g a⟧ ↦ ⟦g⟧ ⊗ a`. -/
@[simps! -isSimp]
/--
Definition of `H1AddEquivOfIsTrivial` / `H1AddEquivOfIsTrivial` 的定义

English:
definition H1AddEquivOfIsTrivial
  signature: :
  body: LinearEquiv.toAddEquiv LinearEquiv.ofLinearMap
    (H1ToTensorOfIsTrivial A) (lift <| mkH1OfIsTrivial A)
    (ext <| LinearMap.toAddMonoidHom_injective <| by
      ext g a
      simp [TensorProduct.mk_apply, TensorProduct.lift.tmul, mkH1OfIsTrivial_apply,
        H1ToTensorOfIsTrivial_H1π_single g a])
    (LinearMap.toAddMonoidHom_injective <|
(H1Iso A).symm.toLinearEquiv.toAddEquiv.comp_left_injective
QuotientAddGroup.addMonoidHom_ext _
(cycles₁IsoOfIsTrivial A).symm.toLinearEquiv.toAddEquiv.comp_left_injective by
        ext
        simp only [H1ToTensorOfIsTrivial, Iso.toLinearEquiv, AddMonoidHom.coe_comp,
          LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, AddMonoidHom.coe_toIntLinearMap]
        -- todo: change this proof so that we don't need `change` and `simpa` that both abuse defeq.
        change TensorProduct.lift _ (QuotientAddGroup.lift _ _ _ ((H1Iso A).hom _)) = _
        simpa [AddSubgroup.subtype, -π_comp_H1Iso_inv_apply, QuotientAddGroup.mk',
          cycles₁IsoOfIsTrivial_inv_apply (A := A)] using! (π_comp_H1Iso_inv_apply A _).symm)

@[simp]

中文:
定义 H1AddEquivOfIsTrivial
  签名: :
  定义体: LinearEquiv.toAddEquiv LinearEquiv.ofLinearMap
    (H1ToTensorOfIsTrivial A) (lift <| mkH1OfIsTrivial A)
    (ext <| LinearMap.toAddMonoidHom_injective <| by
      ext g a
      simp [TensorProduct.mk_apply, TensorProduct.lift.tmul, mkH1OfIsTrivial_apply,
        H1ToTensorOfIsTrivial_H1π_single g a])
    (LinearMap.toAddMonoidHom_injective <|
(H1Iso A).symm.toLinearEquiv.toAddEquiv.comp_left_injective
QuotientAddGroup.addMonoidHom_ext _
(cycles₁IsoOfIsTrivial A).symm.toLinearEquiv.toAddEquiv.comp_left_injective by
        ext
        simp only [H1ToTensorOfIsTrivial, Iso.toLinearEquiv, AddMonoidHom.coe_comp,
          LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, AddMonoidHom.coe_toIntLinearMap]
        -- todo: change this proof so that we don't need `change` and `simpa` that both abuse defeq.
        change TensorProduct.lift _ (QuotientAddGroup.lift _ _ _ ((H1Iso A).hom _)) = _
        simpa [AddSubgroup.subtype, -π_comp_H1Iso_inv_apply, QuotientAddGroup.mk',
          cycles₁IsoOfIsTrivial_inv_apply (A := A)] using! (π_comp_H1Iso_inv_apply A _).symm)

@[simp]

Depends on / 依赖: H1ToTensorOfIsTrivial, LinearEquiv, LinearEquiv.ofLinearMap, LinearEquiv.toAddEquiv, LinearMap, LinearMap.toAddMonoidHom_injective, QuotientAddGroup, QuotientAddGroup.addMonoidHom_ext, TensorProduct, TensorProduct.lift.tmul, TensorProduct.mk_apply, addMonoidHom_ext, comp_left_injective, mkH1OfIsTrivial, mkH1OfIsTrivial_apply, mk_apply, ofLinearMap, symm.toLinearEquiv.toAddEquiv.comp_left_injective, toAddEquiv, toAddMonoidHom_injective
-/
def H1AddEquivOfIsTrivial :
    H1 A ≃+ (Additive <| Abelianization G) otimes[Int] A :=
LinearEquiv.toAddEquiv LinearEquiv.ofLinearMap
    (H1ToTensorOfIsTrivial A) (lift <| mkH1OfIsTrivial A)
    (ext <| LinearMap.toAddMonoidHom_injective <| by
      ext g a
      simp [TensorProduct.mk_apply, TensorProduct.lift.tmul, mkH1OfIsTrivial_apply,
        H1ToTensorOfIsTrivial_H1π_single g a])
    (LinearMap.toAddMonoidHom_injective <|
(H1Iso A).symm.toLinearEquiv.toAddEquiv.comp_left_injective
QuotientAddGroup.addMonoidHom_ext _
(cycles₁IsoOfIsTrivial A).symm.toLinearEquiv.toAddEquiv.comp_left_injective by
        ext
        simp only [H1ToTensorOfIsTrivial, Iso.toLinearEquiv, AddMonoidHom.coe_comp,
          LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, AddMonoidHom.coe_toIntLinearMap]
        -- todo: change this proof so that we don't need `change` and `simpa` that both abuse defeq.
        change TensorProduct.lift _ (QuotientAddGroup.lift _ _ _ ((H1Iso A).hom _)) = _
        simpa [AddSubgroup.subtype, -π_comp_H1Iso_inv_apply, QuotientAddGroup.mk',
          cycles₁IsoOfIsTrivial_inv_apply (A := A)] using! (π_comp_H1Iso_inv_apply A _).symm)

@[simp]
/--
lemma `H1AddEquivOfIsTrivial_single` / 引理 `H1AddEquivOfIsTrivial_single`

English:
lemma H1AddEquivOfIsTrivial_single
  given: (g : G) (a : A)
  proof: by
  rw [H1AddEquivOfIsTrivial_apply]; rw [H1ToTensorOfIsTrivial_H1π_single g a]

@[simp]

中文:
引理 H1AddEquivOfIsTrivial_single
  条件: (g : G) (a : A)
  证明: by
  rw [H1AddEquivOfIsTrivial_apply]; rw [H1ToTensorOfIsTrivial_H1π_single g a]

@[simp]

Depends on / 依赖: H1AddEquivOfIsTrivial_apply
-/
lemma H1AddEquivOfIsTrivial_single (g : G) (a : A) :
    H1AddEquivOfIsTrivial A (H1π A <| (cycles₁IsoOfIsTrivial A).inv (single g a)) =
      Additive.ofMul (Abelianization.of g) otimesₜ[Int] a := by
  rw [H1AddEquivOfIsTrivial_apply]; rw [H1ToTensorOfIsTrivial_H1π_single g a]

@[simp]
/--
lemma `H1AddEquivOfIsTrivial_symm_tmul` / 引理 `H1AddEquivOfIsTrivial_symm_tmul`

English:
lemma H1AddEquivOfIsTrivial_symm_tmul
  given: (g : G) (a : A)
  proof: by
  rfl

中文:
引理 H1AddEquivOfIsTrivial_symm_tmul
  条件: (g : G) (a : A)
  证明: by
  rfl
-/
lemma H1AddEquivOfIsTrivial_symm_tmul (g : G) (a : A) :
    (H1AddEquivOfIsTrivial A).symm (Additive.ofMul (Abelianization.of g) otimesₜ[Int] a) =
      H1π A ((cycles₁IsoOfIsTrivial A).inv <| single g a) := by
  rfl

end IsTrivial

end H1

section H2

/--
Definition of `H2` / `H2` 的定义

English:
abbreviation H2
  body: groupHomology A 2

中文:
缩写 H2
  定义体: groupHomology A 2

Depends on / 依赖: groupHomology
-/
abbrev H2 := groupHomology A 2

/--
Definition of `H2π` / `H2π` 的定义

English:
definition H2π
  signature: : ModuleCat.of k (cycles₂ A) ⟶ H2 A
  body: (isoCycles₂ A).inv ≫ π A 2

中文:
定义 H2π
  签名: : 模范畴.of k (cycles₂ A) ⟶ H2 A
  定义体: (isoCycles₂ A).inv ≫ π A 2
-/
def H2π : ModuleCat.of k (cycles₂ A) ⟶ H2 A :=
  (isoCycles₂ A).inv ≫ π A 2

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (H2π A)
  body: inferInstanceAs Epi (_ ≫ _)

中文:
实例 :
  签名: 满态射 (H2π A)
  定义体: inferInstanceAs Epi (_ ≫ _)
-/
instance : Epi (H2π A) := inferInstanceAs Epi (_ ≫ _)

variable {A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `H2π_eq_zero_iff` / 引理 `H2π_eq_zero_iff`

English:
lemma H2π_eq_zero_iff
  given: (x : cycles₂ A)
  statement: H2π A x = 0 ↔ x.1 in boundaries₂ A
  proof: by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH2 A).inv
    (shortComplexH2 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousChains A).sc 2).leftHomologyIso.hom
  simp only [H2π, isoCycles₂, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, boundaries₂, shortComplexH2, cycles₂]

中文:
引理 H2π_eq_zero_iff
  条件: (x : cycles₂ A)
  结论: H2π A x = 0 ↔ x.1 in boundaries₂ A
  证明: by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH2 A).inv
    (shortComplexH2 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousChains A).sc 2).leftHomologyIso.hom
  simp only [H2π, isoCycles₂, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, boundaries₂, shortComplexH2, cycles₂]

Depends on / 依赖: Function, Function.comp_apply, HomologicalComplex, HomologicalComplex.homology, LinearMap, LinearMap.coe_comp, LinearMap.range_codRestrict, ModuleCat, ModuleCat.hom_comp, ModuleCat.mono_iff_injective, _assoc, _inv, coe_comp, comp_apply, cyclesMapIso, hom_comp, inhomogeneousChains, isoShortComplexH2, leftHomologyData, leftHomologyIso
-/
lemma H2π_eq_zero_iff (x : cycles₂ A) : H2π A x = 0 ↔ x.1 in boundaries₂ A := by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH2 A).inv
    (shortComplexH2 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousChains A).sc 2).leftHomologyIso.hom
  simp only [H2π, isoCycles₂, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, boundaries₂, shortComplexH2, cycles₂]

/--
lemma `H2π_eq_iff` / 引理 `H2π_eq_iff`

English:
lemma H2π_eq_iff
  given: (x y : cycles₂ A)
  proof: by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H2π_eq_zero_iff]
  rfl

@[elab_as_elim]

中文:
引理 H2π_eq_iff
  条件: (x y : cycles₂ A)
  证明: by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H2π_eq_zero_iff]
  rfl

@[elab_as_elim]

Depends on / 依赖: map_sub, sub_eq_zero
-/
lemma H2π_eq_iff (x y : cycles₂ A) :
    H2π A x = H2π A y ↔ x.1 - y.1 in boundaries₂ A := by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H2π_eq_zero_iff]
  rfl

@[elab_as_elim]
/--
theorem `H2_induction_on` / 定理 `H2_induction_on`

English:
theorem H2_induction_on
  given: {C : H2 A -> Prop} (x : H2 A) (h : forall x : cycles₂ A, C (H2π A x))
  proof: groupHomology_induction_on x (fun y => by simpa [H2π] using h ((isoCycles₂ A).hom y))

中文:
定理 H2_induction_on
  条件: {C : H2 A -> 命题} (x : H2 A) (h : 对任意 x : cycles₂ A, C (H2π A x))
  证明: groupHomology_induction_on x (fun y => by simpa [H2π] using h ((isoCycles₂ A).hom y))

Depends on / 依赖: groupHomology_induction_on
-/
theorem H2_induction_on {C : H2 A -> Prop} (x : H2 A) (h : forall x : cycles₂ A, C (H2π A x)) :
    C x :=
  groupHomology_induction_on x (fun y => by simpa [H2π] using h ((isoCycles₂ A).hom y))

variable (A)

/--
Definition of `H2Iso` / `H2Iso` 的定义

English:
definition H2Iso
  signature: : H2 A ≅ (shortComplexH2 A).moduleCatLeftHomologyData.H
  body: (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (isoShortComplexH2 A) _ _)

中文:
定义 H2Iso
  签名: : H2 A ≅ (shortComplexH2 A).moduleCatLeftHomologyData.H
  定义体: (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (isoShortComplexH2 A) _ _)

Depends on / 依赖: isoShortComplexH2, leftHomologyIso, leftHomologyMapIso
-/
def H2Iso : H2 A ≅ (shortComplexH2 A).moduleCatLeftHomologyData.H :=
  (leftHomologyIso _).symm ≪≫ (leftHomologyMapIso' (isoShortComplexH2 A) _ _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `π_comp_H2Iso_hom` / 引理 `π_comp_H2Iso_hom`

English:
lemma π_comp_H2Iso_hom
  proof: by
  simp [H2Iso, isoCycles₂, π, HomologicalComplex.homologyπ, leftHomologyπ]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 π_comp_H2Iso_hom
  证明: by
  simp [H2Iso, isoCycles₂, π, HomologicalComplex.homologyπ, leftHomologyπ]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homology
-/
lemma π_comp_H2Iso_hom :
    π A 2 ≫ (H2Iso A).hom = (isoCycles₂ A).hom ≫
      (shortComplexH2 A).moduleCatLeftHomologyData.π := by
  simp [H2Iso, isoCycles₂, π, HomologicalComplex.homologyπ, leftHomologyπ]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `π_comp_H2Iso_inv` / 引理 `π_comp_H2Iso_inv`

English:
lemma π_comp_H2Iso_inv
  proof: (CommSq.vert_inv ⟨π_comp_H2Iso_hom A⟩).w

中文:
引理 π_comp_H2Iso_inv
  证明: (CommSq.vert_inv ⟨π_comp_H2Iso_hom A⟩).w

Depends on / 依赖: CommSq, CommSq.vert_inv, vert_inv
-/
lemma π_comp_H2Iso_inv :
    (shortComplexH2 A).moduleCatLeftHomologyData.π ≫ (H2Iso A).inv = H2π A :=
  (CommSq.vert_inv ⟨π_comp_H2Iso_hom A⟩).w

end H2

end Homology

end groupHomology
