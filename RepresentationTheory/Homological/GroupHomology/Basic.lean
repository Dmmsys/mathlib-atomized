/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# The group homology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group homology of
`A : Rep k G` to be the homology of the complex
$$\dots \to \bigoplus_{G^2} A \to \bigoplus_{G^1} A \to \bigoplus_{G^0} A$$
with differential $d_n$ sending $a\cdot (g_0, \dots, g_n)$ to
$$\rho(g_0^{-1})(a)\cdot (g_1, \dots, g_n)$$
$$+ \sum_{i = 0}^{n - 1}(-1)^{i + 1}a\cdot (g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}a\cdot (g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism
$\bigoplus_{G^n} A \cong (A \otimes_k \left(\bigoplus_{G^n} k[G]\right))_G$ given by
`Rep.coinvariantsTensorFreeLEquiv`. If we conjugate the $n$th differential in $(A \otimes_k P)_G$
by this isomorphism, where `P` is the bar resolution of `k` as a trivial `k`-linear
`G`-representation, then the resulting map agrees with the differential $d_n$ defined
above, a fact we prove.

Hence our $d_n$ squares to zero, and we get
$\mathrm{H}_n(G, A) \cong \mathrm{Tor}_n(A, k),$ where $\mathrm{Tor}$ is defined by deriving the
second argument of the functor $(A, B) \mapsto (A \otimes_k B)_G.$

To talk about homology in low degree, the file
`Mathlib/RepresentationTheory/Homological/GroupHomology/LowDegree.lean` provides API specialized to
`H₀`, `H₁`, `H₂`.

## Main definitions

* `Rep.Tor k G n`: the left-derived functors given by deriving the second argument of
  $(A, B) \mapsto (A \otimes_k B)_G$.
* `groupHomology.inhomogeneousChains A`: a complex whose objects are
  $\bigoplus_{G^n} A$ and whose homology is the group homology $\mathrm{H}_n(G, A).$
* `groupHomology.inhomogeneousChainsIso A`: an isomorphism between the above two complexes.
* `groupHomology A n`: this is $\mathrm{H}_n(G, A),$ defined as the $n$th homology of the
  second complex, `inhomogeneousChains A`.
* `groupHomologyIsoTor A n`: an isomorphism $\mathrm{H}_n(G, A) \cong \mathrm{Tor}_n(A, k)$
  induced by `inhomogeneousChainsIso A`.

## Implementation notes

Group homology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep` definition.
We avoid using instances `Module k[G] A` so that we do not run into possible scalar action diamonds.

Note that the existing definition of `Tor` in `Mathlib.CategoryTheory.Monoidal.Tor` is for monoidal
categories, and the bifunctor we need to derive here maps to `ModuleCat k`. Hence we define
`Rep.Tor k G n` by instead left-deriving the second argument of `Rep.coinvariantsTensor k G`:
$(A, B) \mapsto (A \otimes_k B)_G$. The functor `Rep.coinvariantsTensor k G` is naturally
isomorphic to the functor sending `A, B` to `A ⊗[k[G]] B`, where we give `A` the `k[G]ᵐᵒᵖ`-module
structure defined by `g • a := A.ρ g⁻¹ a`, but currently mathlib's `TensorProduct` is only defined
for commutative rings.

## TODO

* Upgrading `groupHomologyIsoTor` to an isomorphism of derived functors.

-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

variable (k G : Type u) [CommRing k] [Group G]

open MonoidalCategory Representation Finsupp

section Tor

variable {k G} in
/--
Definition of `HomologicalComplex.coinvariantsTensorObj` / `HomologicalComplex.coinvariantsTensorObj` 的定义

English:
abbreviation HomologicalComplex.coinvariantsTensorObj
  signature: {α : Type*} [AddRightCancelSemigroup α] [One α]
  body: (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj P

中文:
缩写 同调复形.coinvariantsTensorObj
  签名: {α : 类型} [加法右消去半群 α] [幺 α]
  定义体: (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj P

Depends on / 依赖: Rep.coinvariantsTensor, coinvariantsTensor, mapHomologicalComplex
-/
abbrev HomologicalComplex.coinvariantsTensorObj {α : Type*} [AddRightCancelSemigroup α] [One α]
    (A : Rep k G) (P : ChainComplex (Rep k G) α) :
    ChainComplex (ModuleCat k) α :=
  (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj P

namespace Rep

/-- The left-derived functors given by deriving the second argument of `A, B ↦ (A ⊗[k] B)_G`. -/
@[simps]
/--
Definition of `Tor` / `Tor` 的定义

English:
definition Tor
  signature: (n : Nat)
  body: Functor.leftDerived ((coinvariantsTensor k G).obj X) n
  map f := NatTrans.leftDerived ((coinvariantsTensor k G).map f) n

中文:
定义 Tor
  签名: (n : 自然数)
  定义体: Functor.leftDerived ((coinvariantsTensor k G).obj X) n
  map f := NatTrans.leftDerived ((coinvariantsTensor k G).map f) n

Depends on / 依赖: Functor, Functor.leftDerived, coinvariantsTensor, leftDerived
-/
def Tor (n : Nat) : Rep k G ⥤ Rep k G ⥤ ModuleCat k where
  obj X := Functor.leftDerived ((coinvariantsTensor k G).obj X) n
  map f := NatTrans.leftDerived ((coinvariantsTensor k G).map f) n

variable {k G} (A : Rep.{w} k G)

/--
Definition of `torIso` / `torIso` 的定义

English:
abbreviation torIso
  signature: (A : Rep k G) {B : Rep k G} (P : ProjectiveResolution B) (n : Nat)
  body: P.isoLeftDerivedObj _ n

中文:
缩写 torIso
  签名: (A : Rep k G) {B : Rep k G} (P : 投射消解 B) (n : 自然数)
  定义体: P.isoLeftDerivedObj _ n

Depends on / 依赖: P.isoLeftDerivedObj, isoLeftDerivedObj
-/
abbrev torIso (A : Rep k G) {B : Rep k G} (P : ProjectiveResolution B) (n : Nat) :
    ((Rep.Tor k G n).obj A).obj B ≅ (P.complex.coinvariantsTensorObj A).homology n :=
  P.isoLeftDerivedObj _ n

/--
lemma `isZero_Tor_succ_of_projective` / 引理 `isZero_Tor_succ_of_projective`

English:
lemma isZero_Tor_succ_of_projective
  given: (X Y : Rep k G) [Projective Y] (n : Nat)
  proof: Functor.isZero_leftDerived_obj_projective_succ ..

中文:
引理 isZero_Tor_succ_of_projective
  条件: (X Y : Rep k G) [投射 Y] (n : 自然数)
  证明: Functor.isZero_leftDerived_obj_projective_succ ..

Depends on / 依赖: Functor, Functor.isZero_leftDerived_obj_projective_succ, isZero_leftDerived_obj_projective_succ
-/
lemma isZero_Tor_succ_of_projective (X Y : Rep k G) [Projective Y] (n : Nat) :
    IsZero (((Tor k G (n + 1)).obj X).obj Y) :=
  Functor.isZero_leftDerived_obj_projective_succ ..

end Rep
end Tor

namespace groupHomology

open Rep Finsupp

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (n : Nat)

namespace inhomogeneousChains

/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: : ModuleCat.of k ((Fin (n + 1) -> G) ->₀ A) ⟶ ModuleCat.of k ((Fin n -> G) ->₀ A)
  body: ModuleCat.ofHom lsum (R := k) k fun g => lsingle (fun i => g i.succ) ∘ₗ A.ρ (g 0)⁻¹ +
    Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : Nat) + 1) • lsingle (Fin.contractNth j (· * ·) g)

中文:
定义 d
  签名: : 模范畴.of k ((有限集 (n + 1) -> G) ->₀ A) ⟶ 模范畴.of k ((有限集 n -> G) ->₀ A)
  定义体: ModuleCat.ofHom lsum (R := k) k fun g => lsingle (fun i => g i.succ) ∘ₗ A.ρ (g 0)⁻¹ +
    Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : Nat) + 1) • lsingle (Fin.contractNth j (· * ·) g)

Depends on / 依赖: Fin.contractNth, Finset, Finset.univ.sum, ModuleCat, ModuleCat.ofHom, contractNth, i.succ, lsingle
-/
def d : ModuleCat.of k ((Fin (n + 1) -> G) ->₀ A) ⟶ ModuleCat.of k ((Fin n -> G) ->₀ A) :=
ModuleCat.ofHom lsum (R := k) k fun g => lsingle (fun i => g i.succ) ∘ₗ A.ρ (g 0)⁻¹ +
    Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : Nat) + 1) • lsingle (Fin.contractNth j (· * ·) g)

variable {A n} in
@[simp]
/--
theorem `d_single` / 定理 `d_single`

English:
theorem d_single
  given: (n : Nat) (g : Fin (n + 1) -> G) (a : A)
  proof: by
  simp [d]

中文:
定理 d_single
  条件: (n : 自然数) (g : 有限集 (n + 1) -> G) (a : A)
  证明: by
  simp [d]
-/
theorem d_single (n : Nat) (g : Fin (n + 1) -> G) (a : A) :
    d A n (single g a) = single (fun i => g i.succ) (A.ρ (g 0)⁻¹ a) +
      Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : Nat) + 1) • single (Fin.contractNth j (· * ·) g) a := by
  simp [d]

open ModuleCat.MonoidalCategory

set_option backward.defeqAttrib.useBackward true in
/--
theorem `d_eq` / 定理 `d_eq`

English:
theorem d_eq
  given: [DecidableEq G]
  proof: by
  ext : 3
  simp [d_single (k := k), TensorProduct.tmul_add, TensorProduct.tmul_sum,
    barComplex.d_single (k := k)]

中文:
定理 d_eq
  条件: [DecidableEq G]
  证明: by
  ext : 3
  simp [d_single (k := k), TensorProduct.tmul_add, TensorProduct.tmul_sum,
    barComplex.d_single (k := k)]

Depends on / 依赖: TensorProduct, TensorProduct.tmul_add, TensorProduct.tmul_sum, barComplex, barComplex.d_single, d_single, tmul_add, tmul_sum
-/
theorem d_eq [DecidableEq G] :
    d A n = (coinvariantsTensorFreeLEquiv A (Fin (n + 1) -> G)).toModuleIso.inv ≫
      ((barComplex k G).coinvariantsTensorObj A).d (n + 1) n ≫
      (coinvariantsTensorFreeLEquiv A (Fin n -> G)).toModuleIso.hom := by
  ext : 3
  simp [d_single (k := k), TensorProduct.tmul_add, TensorProduct.tmul_sum,
    barComplex.d_single (k := k)]

end inhomogeneousChains

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inhomogeneousChains` / `inhomogeneousChains` 的定义

English:
abbreviation inhomogeneousChains
  signature: :
  body: ChainComplex.of (fun n => ModuleCat.of k ((Fin n -> G) ->₀ A))
    (fun n => inhomogeneousChains.d A n) fun n => by
    classical
    rw [inhomogeneousChains.d_eq]; rw [inhomogeneousChains.d_eq]
    slice_lhs 3 4 => rw [Iso.hom_inv_id]
    slice_lhs 2 4 => rw [Category.id_comp, ((barComplex k G).coi

中文:
缩写 inhomogeneousChains
  签名: :
  定义体: ChainComplex.of (fun n => ModuleCat.of k ((Fin n -> G) ->₀ A))
    (fun n => inhomogeneousChains.d A n) fun n => by
    classical
    rw [inhomogeneousChains.d_eq]; rw [inhomogeneousChains.d_eq]
    slice_lhs 3 4 => rw [Iso.hom_inv_id]
    slice_lhs 2 4 => rw [Category.id_comp, ((barComplex k G).coi

Depends on / 依赖: Category, Category.id_comp, ChainComplex, ChainComplex.of, Iso.hom_inv_id, ModuleCat, ModuleCat.of, barComplex, classical, coinvariantsTensorObj, d_comp_d, d_eq, hom_inv_id, id_comp, inhomogeneousChains, inhomogeneousChains.d, inhomogeneousChains.d_eq, slice_lhs
-/
noncomputable abbrev inhomogeneousChains :
    ChainComplex (ModuleCat k) Nat :=
  ChainComplex.of (fun n => ModuleCat.of k ((Fin n -> G) ->₀ A))
    (fun n => inhomogeneousChains.d A n) fun n => by
    classical
    rw [inhomogeneousChains.d_eq]; rw [inhomogeneousChains.d_eq]
    slice_lhs 3 4 => rw [Iso.hom_inv_id]
    slice_lhs 2 4 => rw [Category.id_comp, ((barComplex k G).coinvariantsTensorObj A).d_comp_d]
    simp

open inhomogeneousChains

variable {A n} in
@[ext]
/--
theorem `inhomogeneousChains.ext` / 定理 `inhomogeneousChains.ext`

English:
theorem inhomogeneousChains.ext
  statement: {M : ModuleCat k} {x y : (inhomogeneousChains A).X n ⟶ M}
  proof: ModuleCat.hom_ext lhom_ext' fun g => ModuleCat.hom_ext_iff.1 (h g)

中文:
定理 inhomogeneousChains.ext
  结论: {M : 模范畴 k} {x y : (inhomogeneousChains A).X n ⟶ M}
  证明: ModuleCat.hom_ext lhom_ext' fun g => ModuleCat.hom_ext_iff.1 (h g)

Depends on / 依赖: ModuleCat, ModuleCat.hom_ext, ModuleCat.hom_ext_iff, hom_ext, hom_ext_iff, lhom_ext
-/
theorem inhomogeneousChains.ext {M : ModuleCat k} {x y : (inhomogeneousChains A).X n ⟶ M}
    (h : forall g, ModuleCat.ofHom (lsingle g) ≫ x = ModuleCat.ofHom (lsingle g) ≫ y) :
x = y := ModuleCat.hom_ext lhom_ext' fun g => ModuleCat.hom_ext_iff.1 (h g)

/--
theorem `inhomogeneousChains.d_def` / 定理 `inhomogeneousChains.d_def`

English:
theorem inhomogeneousChains.d_def
  given: (n : Nat)
  proof: by
  simp [inhomogeneousChains]

中文:
定理 inhomogeneousChains.d_def
  条件: (n : 自然数)
  证明: by
  simp [inhomogeneousChains]

Depends on / 依赖: inhomogeneousChains
-/
theorem inhomogeneousChains.d_def (n : Nat) :
    (inhomogeneousChains A).d (n + 1) n = d A n := by
  simp [inhomogeneousChains]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `inhomogeneousChains.d_comp_d` / 定理 `inhomogeneousChains.d_comp_d`

English:
theorem inhomogeneousChains.d_comp_d
  proof: by
  simpa [ChainComplex.of.d] using ((inhomogeneousChains A).d_comp_d (n + 2) (n + 1) n)

中文:
定理 inhomogeneousChains.d_comp_d
  证明: by
  simpa [ChainComplex.of.d] using ((inhomogeneousChains A).d_comp_d (n + 2) (n + 1) n)

Depends on / 依赖: ChainComplex, ChainComplex.of.d, d_comp_d, inhomogeneousChains
-/
theorem inhomogeneousChains.d_comp_d :
    d A (n + 1) ≫ d A n = 0 := by
  simpa [ChainComplex.of.d] using ((inhomogeneousChains A).d_comp_d (n + 2) (n + 1) n)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inhomogeneousChainsIso` / `inhomogeneousChainsIso` 的定义

English:
definition inhomogeneousChainsIso
  signature: [DecidableEq G]
  body: by
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro i
    apply (coinvariantsTensorFreeLEquiv A (Fin i -> G)).toModuleIso.symm
  rintro i j rfl
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

中文:
定义 inhomogeneousChainsIso
  签名: [DecidableEq G]
  定义体: by
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro i
    apply (coinvariantsTensorFreeLEquiv A (Fin i -> G)).toModuleIso.symm
  rintro i j rfl
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, LinearEquiv, LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_inv, coinvariantsTensorFreeLEquiv, d_eq, isoOfComponents, toModuleIso, toModuleIso.symm, toModuleIso_hom, toModuleIso_inv
-/
def inhomogeneousChainsIso [DecidableEq G] :
    inhomogeneousChains A ≅ (barComplex k G).coinvariantsTensorObj A := by
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro i
    apply (coinvariantsTensorFreeLEquiv A (Fin i -> G)).toModuleIso.symm
  rintro i j rfl
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

/--
Definition of `cycles` / `cycles` 的定义

English:
abbreviation cycles
  signature: (n : Nat)
  body: (inhomogeneousChains A).cycles n

中文:
缩写 cycles
  签名: (n : 自然数)
  定义体: (inhomogeneousChains A).cycles n

Depends on / 依赖: cycles, inhomogeneousChains
-/
abbrev cycles (n : Nat) : ModuleCat k := (inhomogeneousChains A).cycles n

open HomologicalComplex

variable {A} in
/--
Definition of `cyclesMk` / `cyclesMk` 的定义

English:
abbreviation cyclesMk
  signature: (m n : Nat) (h : (ComplexShape.down Nat).next m = n) (f : (Fin m -> G) ->₀ A)
  body: (inhomogeneousChains A).cyclesMk f n h hf

中文:
缩写 cyclesMk
  签名: (m n : 自然数) (h : (余mplexShape.down 自然数).next m = n) (f : (有限集 m -> G) ->₀ A)
  定义体: (inhomogeneousChains A).cyclesMk f n h hf

Depends on / 依赖: cyclesMk, inhomogeneousChains
-/
abbrev cyclesMk (m n : Nat) (h : (ComplexShape.down Nat).next m = n) (f : (Fin m -> G) ->₀ A)
    (hf : (inhomogeneousChains A).d m n f = 0) : cycles A m :=
  (inhomogeneousChains A).cyclesMk f n h hf

/--
Definition of `iCycles` / `iCycles` 的定义

English:
abbreviation iCycles
  signature: (n : Nat)
  body: (inhomogeneousChains A).iCycles n

中文:
缩写 iCycles
  签名: (n : 自然数)
  定义体: (inhomogeneousChains A).iCycles n

Depends on / 依赖: iCycles, inhomogeneousChains
-/
abbrev iCycles (n : Nat) : cycles A n ⟶ (inhomogeneousChains A).X n :=
  (inhomogeneousChains A).iCycles n

variable {A} in
/--
theorem `iCycles_mk` / 定理 `iCycles_mk`

English:
theorem iCycles_mk
  statement: {m n : Nat} (h : (ComplexShape.down Nat).next m = n) (f : (Fin m -> G) ->₀ A)
  proof: by
  exact (inhomogeneousChains A).i_cyclesMk f n h hf

中文:
定理 iCycles_mk
  结论: {m n : 自然数} (h : (余mplexShape.down 自然数).next m = n) (f : (有限集 m -> G) ->₀ A)
  证明: by
  exact (inhomogeneousChains A).i_cyclesMk f n h hf

Depends on / 依赖: i_cyclesMk, inhomogeneousChains
-/
theorem iCycles_mk {m n : Nat} (h : (ComplexShape.down Nat).next m = n) (f : (Fin m -> G) ->₀ A)
    (hf : (inhomogeneousChains A).d m n f = 0) :
    iCycles A m (cyclesMk m n h f hf) = f := by
  exact (inhomogeneousChains A).i_cyclesMk f n h hf

/--
Definition of `toCycles` / `toCycles` 的定义

English:
abbreviation toCycles
  signature: (i j : Nat)
  body: (inhomogeneousChains A).toCycles i j

中文:
缩写 toCycles
  签名: (i j : 自然数)
  定义体: (inhomogeneousChains A).toCycles i j

Depends on / 依赖: inhomogeneousChains, toCycles
-/
abbrev toCycles (i j : Nat) : (inhomogeneousChains A).X i ⟶ cycles A j :=
  (inhomogeneousChains A).toCycles i j

end groupHomology

open groupHomology Rep

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/--
Definition of `groupHomology` / `groupHomology` 的定义

English:
definition groupHomology
  signature: (n : Nat)
  body: (inhomogeneousChains A).homology n

中文:
定义 groupHomology
  签名: (n : 自然数)
  定义体: (inhomogeneousChains A).homology n

Depends on / 依赖: homology, inhomogeneousChains
-/
def groupHomology (n : Nat) : ModuleCat k :=
  (inhomogeneousChains A).homology n

/--
Definition of `groupHomology.π` / `groupHomology.π` 的定义

English:
abbreviation groupHomology.π
  signature: (n : Nat)
  body: (inhomogeneousChains A).homologyπ n

中文:
缩写 groupHomology.π
  签名: (n : 自然数)
  定义体: (inhomogeneousChains A).homologyπ n

Depends on / 依赖: inhomogeneousChains
-/
abbrev groupHomology.π (n : Nat) :
    cycles A n ⟶ groupHomology A n :=
  (inhomogeneousChains A).homologyπ n

set_option backward.isDefEq.respectTransparency false in
variable {A} in
@[elab_as_elim]
/--
theorem `groupHomology_induction_on` / 定理 `groupHomology_induction_on`

English:
theorem groupHomology_induction_on
  statement: {n : Nat}
  proof: by
  rcases (ModuleCat.epi_iff_surjective (π A n)).1 inferInstance x with ⟨y, rfl⟩
  exact h y

中文:
定理 groupHomology_induction_on
  结论: {n : 自然数}
  证明: by
  rcases (ModuleCat.epi_iff_surjective (π A n)).1 inferInstance x with ⟨y, rfl⟩
  exact h y

Depends on / 依赖: ModuleCat, ModuleCat.epi_iff_surjective, epi_iff_surjective
-/
theorem groupHomology_induction_on {n : Nat}
    {C : groupHomology A n -> Prop} (x : groupHomology A n)
    (h : forall x : cycles A n, C (π A n x)) : C x := by
  rcases (ModuleCat.epi_iff_surjective (π A n)).1 inferInstance x with ⟨y, rfl⟩
  exact h y

/--
Definition of `groupHomologyIsoTor` / `groupHomologyIsoTor` 的定义

English:
definition groupHomologyIsoTor
  signature: [DecidableEq G] (n : Nat)
  body: isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousChainsIso A)).hom n ≪≫
    (torIso A (barResolution k G) n).symm

中文:
定义 groupHomologyIsoTor
  签名: [DecidableEq G] (n : 自然数)
  定义体: isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousChainsIso A)).hom n ≪≫
    (torIso A (barResolution k G) n).symm

Depends on / 依赖: HomotopyEquiv, HomotopyEquiv.ofIso, barResolution, inhomogeneousChainsIso, isoOfQuasiIsoAt, torIso
-/
def groupHomologyIsoTor [DecidableEq G] (n : Nat) :
    groupHomology A n ≅ ((Tor k G n).obj A).obj (Rep.trivial k G k) :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousChainsIso A)).hom n ≪≫
    (torIso A (barResolution k G) n).symm

/--
Definition of `groupHomologyIso` / `groupHomologyIso` 的定义

English:
definition groupHomologyIso
  signature: [DecidableEq G] (A : Rep k G) (n : Nat)
  body: groupHomologyIsoTor A n ≪≫ torIso A P n

中文:
定义 groupHomologyIso
  签名: [DecidableEq G] (A : Rep k G) (n : 自然数)
  定义体: groupHomologyIsoTor A n ≪≫ torIso A P n

Depends on / 依赖: groupHomologyIsoTor, torIso
-/
def groupHomologyIso [DecidableEq G] (A : Rep k G) (n : Nat)
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    groupHomology A n ≅ (P.complex.coinvariantsTensorObj A).homology n :=
  groupHomologyIsoTor A n ≪≫ torIso A P n

/--
lemma `isZero_groupHomology_succ_of_subsingleton` / 引理 `isZero_groupHomology_succ_of_subsingleton`

English:
lemma isZero_groupHomology_succ_of_subsingleton
  given: [Subsingleton G] (n : Nat)
  proof: (isZero_Tor_succ_of_projective A (Rep.trivial k G k) n).of_iso groupHomologyIsoTor _ _

中文:
引理 isZero_groupHomology_succ_of_subsingleton
  条件: [子单例 G] (n : 自然数)
  证明: (isZero_Tor_succ_of_projective A (Rep.trivial k G k) n).of_iso groupHomologyIsoTor _ _

Depends on / 依赖: Rep.trivial, groupHomologyIsoTor, isZero_Tor_succ_of_projective, of_iso
-/
lemma isZero_groupHomology_succ_of_subsingleton [Subsingleton G] (n : Nat) :
    Limits.IsZero (groupHomology A (n + 1)) :=
(isZero_Tor_succ_of_projective A (Rep.trivial k G k) n).of_iso groupHomologyIsoTor _ _

end
