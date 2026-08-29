/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# The group cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group cohomology of
`A : Rep k G` to be the cohomology of the complex
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
with differential $d^n$ sending $f: G^n \to A$ to the function mapping $(g_0, \dots, g_n)$ to
$$\rho(g_0)(f(g_1, \dots, g_n))$$
$$+ \sum_{i = 0}^{n - 1} (-1)^{i + 1}\cdot f(g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}\cdot f(g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism
$\mathrm{Fun}(G^n, A) \cong \mathrm{Hom}(\bigoplus_{G^n} k[G], A)$, where
the right-hand side is morphisms in `Rep k G`, and $k[G]$ is equipped with the left regular
representation. If we conjugate the $n$th differential in $\mathrm{Hom}(P, A)$ by this isomorphism,
where `P` is the bar resolution of `k` as a trivial `k`-linear `G`-representation, then the
resulting map agrees with the differential $d^n$ defined above, a fact we prove.

This gives us for free a proof that our $d^n$ squares to zero. It also gives us an isomorphism
$\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A),$ where $\mathrm{Ext}$ is taken in the category
`Rep k G`.

To talk about cohomology in low degree, please see the file
`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`, which provides API
specialized to `H⁰`, `H¹`, `H²`.

## Main definitions

* `groupCohomology.inhomogeneousCochains A`: a complex whose objects are
  $\mathrm{Fun}(G^n, A)$ and whose cohomology is the group cohomology $\mathrm{H}^n(G, A).$
* `groupCohomology.inhomogeneousCochainsIso A`: an isomorphism between the above complex and the
  complex $\mathrm{Hom}(P, A),$ where `P` is the bar resolution of `k` as a trivial resolution.
* `groupCohomology A n`: this is $\mathrm{H}^n(G, A),$ defined as the $n$th cohomology of
  `inhomogeneousCochains A`.
* `groupCohomologyIsoExt A n`: an isomorphism $\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A)$
  (where $\mathrm{Ext}$ is taken in the category `Rep k G`) induced by `inhomogeneousCochainsIso A`.

## Implementation notes

Group cohomology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `Module k[G] A` so that we do not run into
possible scalar action diamonds.

## TODO

* Upgrading `groupCohomologyIsoExt` to an isomorphism of derived functors.
* Profinite cohomology.

Longer term:
* The Hochschild-Serre spectral sequence (this is perhaps a good toy example for the theory of
  spectral sequences in general).
-/

@[expose] public section


noncomputable section

universe u

variable {k G : Type u} [CommRing k] {n : Nat}

open CategoryTheory

namespace inhomogeneousCochains

open Rep

/-- The differential in the complex of inhomogeneous cochains used to
calculate group cohomology. -/
@[simps! -isSimp]
/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: [Monoid G] (A : Rep k G) (n : Nat)
  body: ModuleCat.ofHom
  { toFun f g :=
      A.ρ (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : Nat) + 1) • f (Fin.contractNth j (· * ·) g)
    map_add' f g := by
      ext
      simp [Finset.sum_add_distrib, add_add_add_comm]
    map_smul' r f := by
      ext
      simp [Finset.smul_sum, ← smul_assoc, mul_comm r] }

中文:
定义 d
  签名: [幺半群 G] (A : Rep k G) (n : 自然数)
  定义体: ModuleCat.ofHom
  { toFun f g :=
      A.ρ (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : Nat) + 1) • f (Fin.contractNth j (· * ·) g)
    map_add' f g := by
      ext
      simp [Finset.sum_add_distrib, add_add_add_comm]
    map_smul' r f := by
      ext
      simp [Finset.smul_sum, ← smul_assoc, mul_comm r] }

Depends on / 依赖: Fin.contractNth, Finset, Finset.smul_sum, Finset.sum_add_distrib, Finset.univ.sum, ModuleCat, ModuleCat.ofHom, add_add_add_comm, contractNth, i.succ, map_add, map_smul, mul_comm, smul_assoc, smul_sum, sum_add_distrib
-/
def d [Monoid G] (A : Rep k G) (n : Nat) :
    ModuleCat.of k ((Fin n -> G) -> A) ⟶ ModuleCat.of k ((Fin (n + 1) -> G) -> A) :=
  ModuleCat.ofHom
  { toFun f g :=
      A.ρ (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : Nat) + 1) • f (Fin.contractNth j (· * ·) g)
    map_add' f g := by
      ext
      simp [Finset.sum_add_distrib, add_add_add_comm]
    map_smul' r f := by
      ext
      simp [Finset.smul_sum, ← smul_assoc, mul_comm r] }

variable [Group G] (A : Rep k G) (n : Nat)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `d_eq` / 定理 `d_eq`

English:
theorem d_eq
  proof: by
  ext
  simp [d_hom_apply, map_add, barComplex.d_single (k := k), homEquiv]

中文:
定理 d_eq
  证明: by
  ext
  simp [d_hom_apply, map_add, barComplex.d_single (k := k), homEquiv]

Depends on / 依赖: barComplex, barComplex.d_single, d_hom_apply, d_single, homEquiv, map_add
-/
theorem d_eq :
    d A n =
      (freeLiftLEquiv k G (Fin n -> G) A).toModuleIso.inv ≫
        ((barComplex k G).linearYonedaObj k A).d n (n + 1) ≫
          (freeLiftLEquiv k G (Fin (n + 1) -> G) A).toModuleIso.hom := by
  ext
  simp [d_hom_apply, map_add, barComplex.d_single (k := k), homEquiv]

end inhomogeneousCochains

namespace groupCohomology

variable [Group G] (n) (A : Rep.{u} k G)

open inhomogeneousCochains Rep

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inhomogeneousCochains` / `inhomogeneousCochains` 的定义

English:
abbreviation inhomogeneousCochains
  signature: : CochainComplex (ModuleCat k) Nat
  body: CochainComplex.of (fun n => ModuleCat.of k ((Fin n -> G) -> A))
    (fun n => inhomogeneousCochains.d A n) fun n => by
    rw [d_eq]; rw [d_eq]
    slice_lhs 3 4 => rw [Iso.hom_inv_id]
    slice_lhs 2 4 => rw [Category.id_comp, ((barComplex k G).linearYonedaObj k A).d_comp_d]
    simp

中文:
缩写 inhomogeneousCochains
  签名: : 上链复形 (模范畴 k) 自然数
  定义体: CochainComplex.of (fun n => ModuleCat.of k ((Fin n -> G) -> A))
    (fun n => inhomogeneousCochains.d A n) fun n => by
    rw [d_eq]; rw [d_eq]
    slice_lhs 3 4 => rw [Iso.hom_inv_id]
    slice_lhs 2 4 => rw [Category.id_comp, ((barComplex k G).linearYonedaObj k A).d_comp_d]
    simp

Depends on / 依赖: Category, Category.id_comp, CochainComplex, CochainComplex.of, Iso.hom_inv_id, ModuleCat, ModuleCat.of, barComplex, d_comp_d, d_eq, hom_inv_id, id_comp, inhomogeneousCochains, inhomogeneousCochains.d, linearYonedaObj, slice_lhs
-/
noncomputable abbrev inhomogeneousCochains : CochainComplex (ModuleCat k) Nat :=
  CochainComplex.of (fun n => ModuleCat.of k ((Fin n -> G) -> A))
    (fun n => inhomogeneousCochains.d A n) fun n => by
    rw [d_eq]; rw [d_eq]
    slice_lhs 3 4 => rw [Iso.hom_inv_id]
    slice_lhs 2 4 => rw [Category.id_comp, ((barComplex k G).linearYonedaObj k A).d_comp_d]
    simp

variable {A n} in
@[ext]
/--
theorem `inhomogeneousCochains.ext` / 定理 `inhomogeneousCochains.ext`

English:
theorem inhomogeneousCochains.ext
  given: {x y : (inhomogeneousCochains A).X n} (h : forall g, x g = y g)
  proof: funext h

中文:
定理 inhomogeneousCochains.ext
  条件: {x y : (inhomogeneousCochains A).X n} (h : 对任意 g, x g = y g)
  证明: funext h
-/
theorem inhomogeneousCochains.ext {x y : (inhomogeneousCochains A).X n} (h : forall g, x g = y g) :
    x = y := funext h

/--
theorem `inhomogeneousCochains.d_def` / 定理 `inhomogeneousCochains.d_def`

English:
theorem inhomogeneousCochains.d_def
  given: (n : Nat)
  proof: by
  simp

中文:
定理 inhomogeneousCochains.d_def
  条件: (n : 自然数)
  证明: by
  simp
-/
theorem inhomogeneousCochains.d_def (n : Nat) :
    (inhomogeneousCochains A).d n (n + 1) = d A n := by
  simp

set_option backward.defeqAttrib.useBackward true in
/--
theorem `inhomogeneousCochains.d_comp_d` / 定理 `inhomogeneousCochains.d_comp_d`

English:
theorem inhomogeneousCochains.d_comp_d
  proof: by
  simpa [CochainComplex.of.d] using (inhomogeneousCochains A).d_comp_d n (n + 1) (n + 2)

中文:
定理 inhomogeneousCochains.d_comp_d
  证明: by
  simpa [CochainComplex.of.d] using (inhomogeneousCochains A).d_comp_d n (n + 1) (n + 2)

Depends on / 依赖: CochainComplex, CochainComplex.of.d, d_comp_d, inhomogeneousCochains
-/
theorem inhomogeneousCochains.d_comp_d :
    d A n ≫ d A (n + 1) = 0 := by
  simpa [CochainComplex.of.d] using (inhomogeneousCochains A).d_comp_d n (n + 1) (n + 2)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inhomogeneousCochainsIso` / `inhomogeneousCochainsIso` 的定义

English:
definition inhomogeneousCochainsIso
  signature: :
  body: by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (Rep.freeLiftLEquiv k G (Fin i -> G) A).toModuleIso.symm) ?_
  rintro i j (h : i + 1 = j)
  subst h
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

中文:
定义 inhomogeneousCochainsIso
  签名: :
  定义体: by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (Rep.freeLiftLEquiv k G (Fin i -> G) A).toModuleIso.symm) ?_
  rintro i j (h : i + 1 = j)
  subst h
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, LinearEquiv, LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_inv, Rep.freeLiftLEquiv, d_eq, freeLiftLEquiv, isoOfComponents, toModuleIso, toModuleIso.symm, toModuleIso_hom, toModuleIso_inv
-/
def inhomogeneousCochainsIso :
    inhomogeneousCochains A ≅ (barComplex k G).linearYonedaObj k A := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (Rep.freeLiftLEquiv k G (Fin i -> G) A).toModuleIso.symm) ?_
  rintro i j (h : i + 1 = j)
  subst h
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

/--
Definition of `cocycles` / `cocycles` 的定义

English:
abbreviation cocycles
  signature: (n : Nat)
  body: (inhomogeneousCochains A).cycles n

中文:
缩写 cocycles
  签名: (n : 自然数)
  定义体: (inhomogeneousCochains A).cycles n

Depends on / 依赖: cycles, inhomogeneousCochains
-/
abbrev cocycles (n : Nat) : ModuleCat k := (inhomogeneousCochains A).cycles n

variable {A} in
/--
Definition of `cocyclesMk` / `cocyclesMk` 的定义

English:
abbreviation cocyclesMk
  signature: {n : Nat} (f : (Fin n -> G) -> A) (h : inhomogeneousCochains.d A n f = 0)
  body: (inhomogeneousCochains A).cyclesMk f (n + 1) (by simp) (by simp [h])

中文:
缩写 cocyclesMk
  签名: {n : 自然数} (f : (有限集 n -> G) -> A) (h : inhomogeneousCochains.d A n f = 0)
  定义体: (inhomogeneousCochains A).cyclesMk f (n + 1) (by simp) (by simp [h])

Depends on / 依赖: cyclesMk, inhomogeneousCochains
-/
abbrev cocyclesMk {n : Nat} (f : (Fin n -> G) -> A) (h : inhomogeneousCochains.d A n f = 0) :
    cocycles A n :=
  (inhomogeneousCochains A).cyclesMk f (n + 1) (by simp) (by simp [h])

/--
Definition of `iCocycles` / `iCocycles` 的定义

English:
abbreviation iCocycles
  signature: (n : Nat)
  body: (inhomogeneousCochains A).iCycles n

中文:
缩写 iCocycles
  签名: (n : 自然数)
  定义体: (inhomogeneousCochains A).iCycles n

Depends on / 依赖: iCycles, inhomogeneousCochains
-/
abbrev iCocycles (n : Nat) : cocycles A n ⟶ (inhomogeneousCochains A).X n :=
  (inhomogeneousCochains A).iCycles n

/--
Definition of `toCocycles` / `toCocycles` 的定义

English:
abbreviation toCocycles
  signature: (i j : Nat)
  body: (inhomogeneousCochains A).toCycles i j

中文:
缩写 toCocycles
  签名: (i j : 自然数)
  定义体: (inhomogeneousCochains A).toCycles i j

Depends on / 依赖: inhomogeneousCochains, toCycles
-/
abbrev toCocycles (i j : Nat) : (inhomogeneousCochains A).X i ⟶ cocycles A j :=
  (inhomogeneousCochains A).toCycles i j

variable {A} in
/--
theorem `iCocycles_mk` / 定理 `iCocycles_mk`

English:
theorem iCocycles_mk
  given: {n : Nat} (f : (Fin n -> G) -> A) (h : inhomogeneousCochains.d A n f = 0)
  proof: by
  exact (inhomogeneousCochains A).i_cyclesMk (i := n) f (n + 1) (by simp) (by simp [h])

中文:
定理 iCocycles_mk
  条件: {n : 自然数} (f : (有限集 n -> G) -> A) (h : inhomogeneousCochains.d A n f = 0)
  证明: by
  exact (inhomogeneousCochains A).i_cyclesMk (i := n) f (n + 1) (by simp) (by simp [h])

Depends on / 依赖: i_cyclesMk, inhomogeneousCochains
-/
theorem iCocycles_mk {n : Nat} (f : (Fin n -> G) -> A) (h : inhomogeneousCochains.d A n f = 0) :
    iCocycles A n (cocyclesMk f h) = f := by
  exact (inhomogeneousCochains A).i_cyclesMk (i := n) f (n + 1) (by simp) (by simp [h])

end groupCohomology

open groupCohomology

/--
Definition of `groupCohomology` / `groupCohomology` 的定义

English:
definition groupCohomology
  signature: [Group G] (A : Rep k G) (n : Nat)
  body: (inhomogeneousCochains A).homology n

中文:
定义 groupCohomology
  签名: [群 G] (A : Rep k G) (n : 自然数)
  定义体: (inhomogeneousCochains A).homology n

Depends on / 依赖: homology, inhomogeneousCochains
-/
def groupCohomology [Group G] (A : Rep k G) (n : Nat) : ModuleCat k :=
  (inhomogeneousCochains A).homology n

/--
Definition of `groupCohomology.π` / `groupCohomology.π` 的定义

English:
abbreviation groupCohomology.π
  signature: [Group G] (A : Rep k G) (n : Nat)
  body: (inhomogeneousCochains A).homologyπ n

中文:
缩写 groupCohomology.π
  签名: [群 G] (A : Rep k G) (n : 自然数)
  定义体: (inhomogeneousCochains A).homologyπ n

Depends on / 依赖: inhomogeneousCochains
-/
abbrev groupCohomology.π [Group G] (A : Rep k G) (n : Nat) :
    groupCohomology.cocycles A n ⟶ groupCohomology A n :=
  (inhomogeneousCochains A).homologyπ n

set_option backward.isDefEq.respectTransparency false in
@[elab_as_elim]
/--
theorem `groupCohomology_induction_on` / 定理 `groupCohomology_induction_on`

English:
theorem groupCohomology_induction_on
  statement: [Group G] {A : Rep k G} {n : Nat}
  proof: by
  rcases (ModuleCat.epi_iff_surjective (π A n)).1 inferInstance x with ⟨y, rfl⟩
  exact h y

中文:
定理 groupCohomology_induction_on
  结论: [群 G] {A : Rep k G} {n : 自然数}
  证明: by
  rcases (ModuleCat.epi_iff_surjective (π A n)).1 inferInstance x with ⟨y, rfl⟩
  exact h y

Depends on / 依赖: ModuleCat, ModuleCat.epi_iff_surjective, epi_iff_surjective
-/
theorem groupCohomology_induction_on [Group G] {A : Rep k G} {n : Nat}
    {C : groupCohomology A n -> Prop} (x : groupCohomology A n)
    (h : forall x : cocycles A n, C (π A n x)) : C x := by
  rcases (ModuleCat.epi_iff_surjective (π A n)).1 inferInstance x with ⟨y, rfl⟩
  exact h y

/--
Definition of `groupCohomologyIsoExt` / `groupCohomologyIsoExt` 的定义

English:
definition groupCohomologyIsoExt
  signature: [Group G] (A : Rep k G) (n : Nat)
  body: isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (Rep.barResolution.extIso k G A n).symm

中文:
定义 groupCohomologyIsoExt
  签名: [群 G] (A : Rep k G) (n : 自然数)
  定义体: isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (Rep.barResolution.extIso k G A n).symm

Depends on / 依赖: HomotopyEquiv, HomotopyEquiv.ofIso, Rep.barResolution.extIso, barResolution, extIso, inhomogeneousCochainsIso, isoOfQuasiIsoAt
-/
def groupCohomologyIsoExt [Group G] (A : Rep k G) (n : Nat) :
    groupCohomology A n ≅ ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (Rep.barResolution.extIso k G A n).symm

/--
Definition of `groupCohomologyIso` / `groupCohomologyIso` 的定义

English:
definition groupCohomologyIso
  signature: [Group G] (A : Rep k G) (n : Nat)
  body: groupCohomologyIsoExt A n ≪≫ P.isoExt _ _

中文:
定义 groupCohomologyIso
  签名: [群 G] (A : Rep k G) (n : 自然数)
  定义体: groupCohomologyIsoExt A n ≪≫ P.isoExt _ _

Depends on / 依赖: P.isoExt, groupCohomologyIsoExt, isoExt
-/
def groupCohomologyIso [Group G] (A : Rep k G) (n : Nat)
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    groupCohomology A n ≅ (P.complex.linearYonedaObj k A).homology n :=
  groupCohomologyIsoExt A n ≪≫ P.isoExt _ _

/--
lemma `isZero_groupCohomology_succ_of_subsingleton` / 引理 `isZero_groupCohomology_succ_of_subsingleton`

English:
lemma isZero_groupCohomology_succ_of_subsingleton
  proof: (isZero_Ext_succ_of_projective (Rep.trivial k G k) A n).of_iso groupCohomologyIsoExt _ _

中文:
引理 isZero_groupCohomology_succ_of_subsingleton
  证明: (isZero_Ext_succ_of_projective (Rep.trivial k G k) A n).of_iso groupCohomologyIsoExt _ _

Depends on / 依赖: Rep.trivial, groupCohomologyIsoExt, isZero_Ext_succ_of_projective, of_iso
-/
lemma isZero_groupCohomology_succ_of_subsingleton
    [Group G] [Subsingleton G] (A : Rep k G) (n : Nat) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
(isZero_Ext_succ_of_projective (Rep.trivial k G k) A n).of_iso groupCohomologyIsoExt _ _
