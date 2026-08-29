/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Invariants

/-!
# The low-degree cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file contains specialised API for
the cocycles and group cohomology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.

In `Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`, we define the `n`th group
cohomology of `A` to be the cohomology of a complex `inhomogeneousCochains A`, whose objects are
`(Fin n → G) → A`; this is unnecessarily unwieldy in low degree. Here, meanwhile, we define the one
and two cocycles and coboundaries as submodules of `Fun(G, A)` and `Fun(G × G, A)`, and provide
maps to `H1` and `H2`.

We also show that when the representation on `A` is trivial, `H¹(G, A) ≃ Hom(G, A)`.

Given an additive or multiplicative abelian group `A` with an appropriate scalar action of `G`,
we provide support for turning a function `f : G → A` satisfying the 1-cocycle identity into an
element of the `cocycles₁` of the representation on `A` (or `Additive A`) corresponding to the
scalar action. We also do this for 1-coboundaries, 2-cocycles and 2-coboundaries. The
multiplicative case, starting with the section `IsMulCocycle`, just mirrors the additive case;
unfortunately `@[to_additive]` can't deal with scalar actions.

The file also contains an identification between the definitions in
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`,
`groupCohomology.cocycles A n`, and the `cocyclesₙ` in this file, for `n = 0, 1, 2`.

## Main definitions

* `groupCohomology.H0Iso A`: isomorphism between `H⁰(G, A)` and the invariants `Aᴳ` of the
  `G`-representation on `A`.
* `groupCohomology.H1π A`: epimorphism from the 1-cocycles
  (i.e. `Z¹(G, A) := Ker(d¹ : Fun(G, A) → Fun(G², A)`) to `H¹(G, A)`.
* `groupCohomology.H2π A`: epimorphism from the 2-cocycles
  (i.e. `Z²(G, A) := Ker(d² : Fun(G², A) → Fun(G³, A)`) to `H²(G, A)`.
* `groupCohomology.H1IsoOfIsTrivial`: the isomorphism `H¹(G, A) ≅ Hom(G, A)` when the
  representation on `A` is trivial.

## TODO

* The relationship between `H2` and group extensions
* Nonabelian group cohomology

-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace groupCohomology

section Cochains

/--
Definition of `cochainsIso₀` / `cochainsIso₀` 的定义

English:
definition cochainsIso₀
  signature: : (inhomogeneousCochains A).X 0 ≅ ModuleCat.of k A.V
  body: (LinearEquiv.funUnique (Fin 0 -> G) k A).toModuleIso

中文:
定义 cochainsIso₀
  签名: : (inhomogeneousCochains A).X 0 ≅ 模范畴.of k A.V
  定义体: (LinearEquiv.funUnique (Fin 0 -> G) k A).toModuleIso

Depends on / 依赖: LinearEquiv, LinearEquiv.funUnique, funUnique, toModuleIso
-/
def cochainsIso₀ : (inhomogeneousCochains A).X 0 ≅ ModuleCat.of k A.V :=
  (LinearEquiv.funUnique (Fin 0 -> G) k A).toModuleIso

/--
Definition of `cochainsIso₁` / `cochainsIso₁` 的定义

English:
definition cochainsIso₁
  signature: : (inhomogeneousCochains A).X 1 ≅ ModuleCat.of k (G -> A)
  body: (LinearEquiv.funCongrLeft k A (Equiv.funUnique (Fin 1) G)).toModuleIso.symm

中文:
定义 cochainsIso₁
  签名: : (inhomogeneousCochains A).X 1 ≅ 模范畴.of k (G -> A)
  定义体: (LinearEquiv.funCongrLeft k A (Equiv.funUnique (Fin 1) G)).toModuleIso.symm

Depends on / 依赖: Equiv.funUnique, LinearEquiv, LinearEquiv.funCongrLeft, funCongrLeft, funUnique, toModuleIso, toModuleIso.symm
-/
def cochainsIso₁ : (inhomogeneousCochains A).X 1 ≅ ModuleCat.of k (G -> A) :=
  (LinearEquiv.funCongrLeft k A (Equiv.funUnique (Fin 1) G)).toModuleIso.symm

/--
Definition of `cochainsIso₂` / `cochainsIso₂` 的定义

English:
definition cochainsIso₂
  signature: : (inhomogeneousCochains A).X 2 ≅ ModuleCat.of k (G × G -> A)
  body: (LinearEquiv.funCongrLeft k A <| (piFinTwoEquiv fun _ => G)).toModuleIso.symm

中文:
定义 cochainsIso₂
  签名: : (inhomogeneousCochains A).X 2 ≅ 模范畴.of k (G × G -> A)
  定义体: (LinearEquiv.funCongrLeft k A <| (piFinTwoEquiv fun _ => G)).toModuleIso.symm

Depends on / 依赖: LinearEquiv, LinearEquiv.funCongrLeft, funCongrLeft, piFinTwoEquiv, toModuleIso, toModuleIso.symm
-/
def cochainsIso₂ : (inhomogeneousCochains A).X 2 ≅ ModuleCat.of k (G × G -> A) :=
  (LinearEquiv.funCongrLeft k A <| (piFinTwoEquiv fun _ => G)).toModuleIso.symm

/--
Definition of `cochainsIso₃` / `cochainsIso₃` 的定义

English:
definition cochainsIso₃
  signature: : (inhomogeneousCochains A).X 3 ≅ ModuleCat.of k (G × G × G -> A)
  body: (LinearEquiv.funCongrLeft k A <| ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso.symm

中文:
定义 cochainsIso₃
  签名: : (inhomogeneousCochains A).X 3 ≅ 模范畴.of k (G × G × G -> A)
  定义体: (LinearEquiv.funCongrLeft k A <| ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso.symm

Depends on / 依赖: Equiv.refl, Fin.consEquiv, LinearEquiv, LinearEquiv.funCongrLeft, consEquiv, funCongrLeft, piFinTwoEquiv, prodCongr, symm.trans, toModuleIso, toModuleIso.symm
-/
def cochainsIso₃ : (inhomogeneousCochains A).X 3 ≅ ModuleCat.of k (G × G × G -> A) :=
  (LinearEquiv.funCongrLeft k A <| ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso.symm

end Cochains

section Differentials

/-- The 0th differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `A → Fun(G, A)`. It sends `(a, g) ↦ ρ_A(g)(a) - a.` -/
@[simps!]
/--
Definition of `d₀₁` / `d₀₁` 的定义

English:
definition d₀₁
  signature: : ModuleCat.of k A.V ⟶ ModuleCat.of k (G -> A)
  body: ModuleCat.ofHom
  { toFun m g := A.ρ g m - m
    map_add' x y := funext fun g => by simp only [map_add, add_sub_add_comm]; rfl
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_sub] }

中文:
定义 d₀₁
  签名: : 模范畴.of k A.V ⟶ 模范畴.of k (G -> A)
  定义体: ModuleCat.ofHom
  { toFun m g := A.ρ g m - m
    map_add' x y := funext fun g => by simp only [map_add, add_sub_add_comm]; rfl
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_sub] }

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, add_sub_add_comm, map_add, map_smul, smul_sub
-/
def d₀₁ : ModuleCat.of k A.V ⟶ ModuleCat.of k (G -> A) :=
  ModuleCat.ofHom
  { toFun m g := A.ρ g m - m
    map_add' x y := funext fun g => by simp only [map_add, add_sub_add_comm]; rfl
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_sub] }

/--
theorem `d₀₁_ker_eq_invariants` / 定理 `d₀₁_ker_eq_invariants`

English:
theorem d₀₁_ker_eq_invariants
  statement: LinearMap.ker (d₀₁ A).hom = invariants A.ρ
  proof: by
  ext x
  simp only [LinearMap.mem_ker, mem_invariants, ← @sub_eq_zero _ _ _ x, funext_iff]
  rfl

中文:
定理 d₀₁_ker_eq_invariants
  结论: 线性映射.ker (d₀₁ A).hom = invariants A.ρ
  证明: by
  ext x
  simp only [LinearMap.mem_ker, mem_invariants, ← @sub_eq_zero _ _ _ x, funext_iff]
  rfl

Depends on / 依赖: LinearMap, LinearMap.mem_ker, funext_iff, mem_invariants, mem_ker, sub_eq_zero
-/
theorem d₀₁_ker_eq_invariants : LinearMap.ker (d₀₁ A).hom = invariants A.ρ := by
  ext x
  simp only [LinearMap.mem_ker, mem_invariants, ← @sub_eq_zero _ _ _ x, funext_iff]
  rfl

/--
theorem `d₀₁_eq_zero` / 定理 `d₀₁_eq_zero`

English:
theorem d₀₁_eq_zero
  given: [A.IsTrivial]
  statement: d₀₁ A = 0
  proof: by
  ext
  rw [d₀₁_hom_apply]; rw [isTrivial_apply]; rw [sub_self]
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 d₀₁_eq_zero
  条件: [A.是平凡]
  结论: d₀₁ A = 0
  证明: by
  ext
  rw [d₀₁_hom_apply]; rw [isTrivial_apply]; rw [sub_self]
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
-/
@[simp] theorem d₀₁_eq_zero [A.IsTrivial] : d₀₁ A = 0 := by
  ext
  rw [d₀₁_hom_apply]; rw [isTrivial_apply]; rw [sub_self]
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `subtype_comp_d₀₁` / 引理 `subtype_comp_d₀₁`

English:
lemma subtype_comp_d₀₁
  statement: ModuleCat.ofHom (A.ρ.invariants.subtype) ≫ d₀₁ A = 0
  proof: by
  ext ⟨x, hx⟩ g
  replace hx := hx g
  rw [← sub_eq_zero] at hx
  exact hx

中文:
引理 subtype_comp_d₀₁
  结论: 模范畴.ofHom (A.ρ.invariants.subtype) ≫ d₀₁ A = 0
  证明: by
  ext ⟨x, hx⟩ g
  replace hx := hx g
  rw [← sub_eq_zero] at hx
  exact hx

Depends on / 依赖: replace, sub_eq_zero
-/
lemma subtype_comp_d₀₁ : ModuleCat.ofHom (A.ρ.invariants.subtype) ≫ d₀₁ A = 0 := by
  ext ⟨x, hx⟩ g
  replace hx := hx g
  rw [← sub_eq_zero] at hx
  exact hx

/-- The 1st differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G, A) → Fun(G × G, A)`. It sends
`(f, (g₁, g₂)) ↦ ρ_A(g₁)(f(g₂)) - f(g₁g₂) + f(g₁).` -/
@[simps!]
/--
Definition of `d₁₂` / `d₁₂` 的定义

English:
definition d₁₂
  signature: : ModuleCat.of k (G -> A) ⟶ ModuleCat.of k (G × G -> A)
  body: ModuleCat.ofHom
  { toFun f g := A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1
    map_add' x y := funext fun g => by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm]
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_add, smul_sub] }

中文:
定义 d₁₂
  签名: : 模范畴.of k (G -> A) ⟶ 模范畴.of k (G × G -> A)
  定义体: ModuleCat.ofHom
  { toFun f g := A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1
    map_add' x y := funext fun g => by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm]
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_add, smul_sub] }

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, add_add_add_comm, add_sub_add_comm, map_add, map_smul, smul_add, smul_sub
-/
def d₁₂ : ModuleCat.of k (G -> A) ⟶ ModuleCat.of k (G × G -> A) :=
  ModuleCat.ofHom
  { toFun f g := A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1
    map_add' x y := funext fun g => by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm]
    map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_add, smul_sub] }

/-- The 2nd differential in the complex of inhomogeneous cochains of `A : Rep k G`, as a
`k`-linear map `Fun(G × G, A) → Fun(G × G × G, A)`. It sends
`(f, (g₁, g₂, g₃)) ↦ ρ_A(g₁)(f(g₂, g₃)) - f(g₁g₂, g₃) + f(g₁, g₂g₃) - f(g₁, g₂).` -/
@[simps!]
/--
Definition of `d₂₃` / `d₂₃` 的定义

English:
definition d₂₃
  signature: : ModuleCat.of k (G × G -> A) ⟶ ModuleCat.of k (G × G × G -> A)
  body: ModuleCat.ofHom
  { toFun f g :=
      A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1)
    map_add' x y :=
      funext fun g => by
        dsimp
        rw [map_add]; rw [add_sub_add_comm (A.ρ _ _)]; rw [add_sub_assoc]; rw [add_sub_add_comm]; rw [add_add_add_comm]; rw [add_sub_assoc]; rw [add_sub_assoc]
    map_smul' r x := funext fun g => by dsimp; simp only [map_smul, smul_add, smul_sub] }

中文:
定义 d₂₃
  签名: : 模范畴.of k (G × G -> A) ⟶ 模范畴.of k (G × G × G -> A)
  定义体: ModuleCat.ofHom
  { toFun f g :=
      A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1)
    map_add' x y :=
      funext fun g => by
        dsimp
        rw [map_add]; rw [add_sub_add_comm (A.ρ _ _)]; rw [add_sub_assoc]; rw [add_sub_add_comm]; rw [add_add_add_comm]; rw [add_sub_assoc]; rw [add_sub_assoc]
    map_smul' r x := funext fun g => by dsimp; simp only [map_smul, smul_add, smul_sub] }

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, add_add_add_comm, add_sub_add_comm, add_sub_assoc, map_add, map_smul, smul_add, smul_sub
-/
def d₂₃ : ModuleCat.of k (G × G -> A) ⟶ ModuleCat.of k (G × G × G -> A) :=
  ModuleCat.ofHom
  { toFun f g :=
      A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1)
    map_add' x y :=
      funext fun g => by
        dsimp
        rw [map_add]; rw [add_sub_add_comm (A.ρ _ _)]; rw [add_sub_assoc]; rw [add_sub_add_comm]; rw [add_add_add_comm]; rw [add_sub_assoc]; rw [add_sub_assoc]
    map_smul' r x := funext fun g => by dsimp; simp only [map_smul, smul_add, smul_sub] }

/--
theorem `comp_d₀₁_eq` / 定理 `comp_d₀₁_eq`

English:
theorem comp_d₀₁_eq
  proof: by
  ext x a y
  simp only [cochainsIso₀, LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp,
    ConcreteCategory.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearEquiv.funUnique_apply, LinearMap.coe_single, Function.comp_apply, Function.eval,
    d₀₁_hom_apply, zero_add, ↓reduceDIte, Nat.reduceAdd, eqToHom_refl, Category.comp_id,
    cochainsIso₁, Iso.symm_hom, LinearEquiv.toModuleIso_inv, LinearEquiv.funCongrLeft_symm,
    LinearEquiv.funCongrLeft_apply, Equiv.funUnique_symm_apply, LinearMap.funLeft_apply,
    inhomogeneousCochains.d_hom_apply, Fin.isValue, uniqueElim_const, Finset.univ_unique,
    Fin.default_eq_zero, Fin.val_eq_zero, pow_one, neg_smul, one_smul, Finset.sum_neg_distrib,
    Finset.sum_singleton, ← sub_eq_add_neg, CochainComplex.of.d]
  rw [← Subsingleton.elim (α := Fin 0 -> G) default (fun i => y)]; rw [Subsingleton.elim
    (Fin.contractNth 0 _) default]; rw [Pi.default_def]

中文:
定理 comp_d₀₁_eq
  证明: by
  ext x a y
  simp only [cochainsIso₀, LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp,
    ConcreteCategory.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearEquiv.funUnique_apply, LinearMap.coe_single, Function.comp_apply, Function.eval,
    d₀₁_hom_apply, zero_add, ↓reduceDIte, Nat.reduceAdd, eqToHom_refl, Category.comp_id,
    cochainsIso₁, Iso.symm_hom, LinearEquiv.toModuleIso_inv, LinearEquiv.funCongrLeft_symm,
    LinearEquiv.funCongrLeft_apply, Equiv.funUnique_symm_apply, LinearMap.funLeft_apply,
    inhomogeneousCochains.d_hom_apply, Fin.isValue, uniqueElim_const, Finset.univ_unique,
    Fin.default_eq_zero, Fin.val_eq_zero, pow_one, neg_smul, one_smul, Finset.sum_neg_distrib,
    Finset.sum_singleton, ← sub_eq_add_neg, CochainComplex.of.d]
  rw [← Subsingleton.elim (α := Fin 0 -> G) default (fun i => y)]; rw [Subsingleton.elim
    (Fin.contractNth 0 _) default]; rw [Pi.default_def]

Depends on / 依赖: Category, Category.comp_id, ConcreteCategory, ConcreteCategory.hom_ofHom, Equiv.funUnique_symm_apply, Function, Function.comp_apply, Function.eval, Iso.symm_hom, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply, LinearEquiv.funCongrLeft_symm, LinearEquiv.funUnique_apply, LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_inv, LinearMap, LinearMap.coe_comp, LinearMap.coe_single, LinearMap.funLeft_apply
-/
theorem comp_d₀₁_eq :
    (cochainsIso₀ A).hom ≫ d₀₁ A =
      (inhomogeneousCochains A).d 0 1 ≫ (cochainsIso₁ A).hom := by
  ext x a y
  simp only [cochainsIso₀, LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp,
    ConcreteCategory.hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe,
    LinearEquiv.funUnique_apply, LinearMap.coe_single, Function.comp_apply, Function.eval,
    d₀₁_hom_apply, zero_add, ↓reduceDIte, Nat.reduceAdd, eqToHom_refl, Category.comp_id,
    cochainsIso₁, Iso.symm_hom, LinearEquiv.toModuleIso_inv, LinearEquiv.funCongrLeft_symm,
    LinearEquiv.funCongrLeft_apply, Equiv.funUnique_symm_apply, LinearMap.funLeft_apply,
    inhomogeneousCochains.d_hom_apply, Fin.isValue, uniqueElim_const, Finset.univ_unique,
    Fin.default_eq_zero, Fin.val_eq_zero, pow_one, neg_smul, one_smul, Finset.sum_neg_distrib,
    Finset.sum_singleton, ← sub_eq_add_neg, CochainComplex.of.d]
  rw [← Subsingleton.elim (α := Fin 0 -> G) default (fun i => y)]; rw [Subsingleton.elim
    (Fin.contractNth 0 _) default]; rw [Pi.default_def]

-- @[reassoc (attr := simp), elementwise (attr := simp)]
@[reassoc, elementwise]
/--
theorem `eq_d₀₁_comp_inv` / 定理 `eq_d₀₁_comp_inv`

English:
theorem eq_d₀₁_comp_inv
  proof: (CommSq.horiz_inv ⟨comp_d₀₁_eq A⟩).w

中文:
定理 eq_d₀₁_comp_inv
  证明: (CommSq.horiz_inv ⟨comp_d₀₁_eq A⟩).w

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
theorem eq_d₀₁_comp_inv :
    (cochainsIso₀ A).inv ≫ (inhomogeneousCochains A).d 0 1 =
      d₀₁ A ≫ (cochainsIso₁ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₀₁_eq A⟩).w

/--
theorem `comp_d₁₂_eq` / 定理 `comp_d₁₂_eq`

English:
theorem comp_d₁₂_eq
  proof: by
  ext x y
  change A.ρ y.1 (x _) - x _ + x _ = _ + _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one,
    Nat.one_add, neg_one_sq, sub_eq_add_neg, add_assoc]
  rcongr i <;> rw [Subsingleton.elim i 0] <;> rfl

中文:
定理 comp_d₁₂_eq
  证明: by
  ext x y
  change A.ρ y.1 (x _) - x _ + x _ = _ + _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one,
    Nat.one_add, neg_one_sq, sub_eq_add_neg, add_assoc]
  rcongr i <;> rw [Subsingleton.elim i 0] <;> rfl

Depends on / 依赖: Fin.sum_univ_two, Fin.val_one, Fin.val_zero, Nat.one_add, Subsingleton, Subsingleton.elim, add_assoc, neg_one_sq, neg_smul, one_add, one_smul, pow_one, rcongr, sub_eq_add_neg, sum_univ_two, val_one, val_zero, zero_add
-/
theorem comp_d₁₂_eq :
    (cochainsIso₁ A).hom ≫ d₁₂ A =
      (inhomogeneousCochains A).d 1 2 ≫ (cochainsIso₂ A).hom := by
  ext x y
  change A.ρ y.1 (x _) - x _ + x _ = _ + _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one,
    Nat.one_add, neg_one_sq, sub_eq_add_neg, add_assoc]
  rcongr i <;> rw [Subsingleton.elim i 0] <;> rfl

-- @[reassoc (attr := simp), elementwise (attr := simp)]
@[reassoc, elementwise]
/--
theorem `eq_d₁₂_comp_inv` / 定理 `eq_d₁₂_comp_inv`

English:
theorem eq_d₁₂_comp_inv
  proof: (CommSq.horiz_inv ⟨comp_d₁₂_eq A⟩).w

中文:
定理 eq_d₁₂_comp_inv
  证明: (CommSq.horiz_inv ⟨comp_d₁₂_eq A⟩).w

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
theorem eq_d₁₂_comp_inv :
    (cochainsIso₁ A).inv ≫ (inhomogeneousCochains A).d 1 2 =
      d₁₂ A ≫ (cochainsIso₂ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₁₂_eq A⟩).w

/--
theorem `comp_d₂₃_eq` / 定理 `comp_d₂₃_eq`

English:
theorem comp_d₂₃_eq
  proof: by
  ext x y
  change A.ρ y.1 (x _) - x _ + x _ - x _ = _ + _
  dsimp
  rw [Fin.sum_univ_three]
  simp only [sub_eq_add_neg, add_assoc, Fin.val_zero, zero_add, pow_one, neg_smul,
    one_smul, Fin.val_one, Fin.val_two, pow_succ' (-1 : k) 2, neg_sq, Nat.one_add, one_pow, mul_one]
  rcongr i <;> fin_cases i <;> rfl

中文:
定理 comp_d₂₃_eq
  证明: by
  ext x y
  change A.ρ y.1 (x _) - x _ + x _ - x _ = _ + _
  dsimp
  rw [Fin.sum_univ_three]
  simp only [sub_eq_add_neg, add_assoc, Fin.val_zero, zero_add, pow_one, neg_smul,
    one_smul, Fin.val_one, Fin.val_two, pow_succ' (-1 : k) 2, neg_sq, Nat.one_add, one_pow, mul_one]
  rcongr i <;> fin_cases i <;> rfl

Depends on / 依赖: Fin.sum_univ_three, Fin.val_one, Fin.val_two, Fin.val_zero, Nat.one_add, add_assoc, fin_cases, mul_one, neg_smul, neg_sq, one_add, one_pow, one_smul, pow_one, pow_succ, rcongr, sub_eq_add_neg, sum_univ_three, val_one, val_two
-/
theorem comp_d₂₃_eq :
    (cochainsIso₂ A).hom ≫ d₂₃ A =
      (inhomogeneousCochains A).d 2 3 ≫ (cochainsIso₃ A).hom := by
  ext x y
  change A.ρ y.1 (x _) - x _ + x _ - x _ = _ + _
  dsimp
  rw [Fin.sum_univ_three]
  simp only [sub_eq_add_neg, add_assoc, Fin.val_zero, zero_add, pow_one, neg_smul,
    one_smul, Fin.val_one, Fin.val_two, pow_succ' (-1 : k) 2, neg_sq, Nat.one_add, one_pow, mul_one]
  rcongr i <;> fin_cases i <;> rfl

-- @[reassoc (attr := simp), elementwise (attr := simp)]
@[reassoc, elementwise]
/--
theorem `eq_d₂₃_comp_inv` / 定理 `eq_d₂₃_comp_inv`

English:
theorem eq_d₂₃_comp_inv
  proof: (CommSq.horiz_inv ⟨comp_d₂₃_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 eq_d₂₃_comp_inv
  证明: (CommSq.horiz_inv ⟨comp_d₂₃_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
theorem eq_d₂₃_comp_inv :
    (cochainsIso₂ A).inv ≫ (inhomogeneousCochains A).d 2 3 =
      d₂₃ A ≫ (cochainsIso₃ A).inv :=
  (CommSq.horiz_inv ⟨comp_d₂₃_eq A⟩).w

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `d₀₁_comp_d₁₂` / 定理 `d₀₁_comp_d₁₂`

English:
theorem d₀₁_comp_d₁₂
  statement: d₀₁ A ≫ d₁₂ A = 0
  proof: by
  ext
  simp [Pi.zero_apply (M := fun _ => A)]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 d₀₁_comp_d₁₂
  结论: d₀₁ A ≫ d₁₂ A = 0
  证明: by
  ext
  simp [Pi.zero_apply (M := fun _ => A)]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: Pi.zero_apply, zero_apply
-/
theorem d₀₁_comp_d₁₂ : d₀₁ A ≫ d₁₂ A = 0 := by
  ext
  simp [Pi.zero_apply (M := fun _ => A)]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `d₁₂_comp_d₂₃` / 定理 `d₁₂_comp_d₂₃`

English:
theorem d₁₂_comp_d₂₃
  statement: d₁₂ A ≫ d₂₃ A = 0
  proof: by
  ext f g
  simp [mul_assoc, Pi.zero_apply (M := fun _ => A)]
  abel

中文:
定理 d₁₂_comp_d₂₃
  结论: d₁₂ A ≫ d₂₃ A = 0
  证明: by
  ext f g
  simp [mul_assoc, Pi.zero_apply (M := fun _ => A)]
  abel

Depends on / 依赖: Pi.zero_apply, mul_assoc, zero_apply
-/
theorem d₁₂_comp_d₂₃ : d₁₂ A ≫ d₂₃ A = 0 := by
  ext f g
  simp [mul_assoc, Pi.zero_apply (M := fun _ => A)]
  abel

open ShortComplex

/-- The (exact) short complex `A.ρ.invariants ⟶ A ⟶ (G → A)`. -/
@[simps! -isSimp f g]
/--
Definition of `shortComplexH0` / `shortComplexH0` 的定义

English:
definition shortComplexH0
  signature: : ShortComplex (ModuleCat k)
  body: mk _ _ (subtype_comp_d₀₁ A)

中文:
定义 shortComplexH0
  签名: : 短复形 (模范畴 k)
  定义体: mk _ _ (subtype_comp_d₀₁ A)
-/
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  mk _ _ (subtype_comp_d₀₁ A)

/-- The short complex `A --d₀₁--> Fun(G, A) --d₁₂--> Fun(G × G, A)`. -/
@[simps! -isSimp f g]
/--
Definition of `shortComplexH1` / `shortComplexH1` 的定义

English:
definition shortComplexH1
  signature: : ShortComplex (ModuleCat k)
  body: mk (d₀₁ A) (d₁₂ A) (d₀₁_comp_d₁₂ A)

中文:
定义 shortComplexH1
  签名: : 短复形 (模范畴 k)
  定义体: mk (d₀₁ A) (d₁₂ A) (d₀₁_comp_d₁₂ A)
-/
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  mk (d₀₁ A) (d₁₂ A) (d₀₁_comp_d₁₂ A)

/-- The short complex `Fun(G, A) --d₁₂--> Fun(G × G, A) --d₂₃--> Fun(G × G × G, A)`. -/
@[simps! -isSimp f g]
/--
Definition of `shortComplexH2` / `shortComplexH2` 的定义

English:
definition shortComplexH2
  signature: : ShortComplex (ModuleCat k)
  body: mk (d₁₂ A) (d₂₃ A) (d₁₂_comp_d₂₃ A)

中文:
定义 shortComplexH2
  签名: : 短复形 (模范畴 k)
  定义体: mk (d₁₂ A) (d₂₃ A) (d₁₂_comp_d₂₃ A)
-/
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  mk (d₁₂ A) (d₂₃ A) (d₁₂_comp_d₂₃ A)

end Differentials

section Cocycles

/--
Definition of `cocycles₁` / `cocycles₁` 的定义

English:
definition cocycles₁
  signature: : Submodule k (G -> A)
  body: LinearMap.ker (d₁₂ A).hom

中文:
定义 cocycles₁
  签名: : 子模 k (G -> A)
  定义体: LinearMap.ker (d₁₂ A).hom

Depends on / 依赖: LinearMap, LinearMap.ker
-/
def cocycles₁ : Submodule k (G -> A) := LinearMap.ker (d₁₂ A).hom

/--
Definition of `cocycles₂` / `cocycles₂` 的定义

English:
definition cocycles₂
  signature: : Submodule k (G × G -> A)
  body: LinearMap.ker (d₂₃ A).hom

中文:
定义 cocycles₂
  签名: : 子模 k (G × G -> A)
  定义体: LinearMap.ker (d₂₃ A).hom

Depends on / 依赖: LinearMap, LinearMap.ker
-/
def cocycles₂ : Submodule k (G × G -> A) := LinearMap.ker (d₂₃ A).hom

variable {A}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (cocycles₁ A) G A
  body: ⟨Subtype.val, Subtype.val_injective⟩

@[simp]

中文:
实例 :
  签名: 函数状 (cocycles₁ A) G A
  定义体: ⟨Subtype.val, Subtype.val_injective⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.val, Subtype.val_injective, val_injective
-/
instance : FunLike (cocycles₁ A) G A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
/--
theorem `cocycles₁.coe_mk` / 定理 `cocycles₁.coe_mk`

English:
theorem cocycles₁.coe_mk
  given: (f : G -> A) (hf)
  statement: ((⟨f, hf⟩ : cocycles₁ A) : G -> A) = f
  proof: rfl

@[simp]

中文:
定理 cocycles₁.coe_mk
  条件: (f : G -> A) (hf)
  结论: ((⟨f, hf⟩ : cocycles₁ A) : G -> A) = f
  证明: rfl

@[simp]
-/
theorem cocycles₁.coe_mk (f : G -> A) (hf) : ((⟨f, hf⟩ : cocycles₁ A) : G -> A) = f := rfl

@[simp]
/--
theorem `cocycles₁.val_eq_coe` / 定理 `cocycles₁.val_eq_coe`

English:
theorem cocycles₁.val_eq_coe
  given: (f : cocycles₁ A)
  statement: f.1 = f
  proof: rfl

@[ext]

中文:
定理 cocycles₁.val_eq_coe
  条件: (f : cocycles₁ A)
  结论: f.1 = f
  证明: rfl

@[ext]
-/
theorem cocycles₁.val_eq_coe (f : cocycles₁ A) : f.1 = f := rfl

@[ext]
/--
theorem `cocycles₁_ext` / 定理 `cocycles₁_ext`

English:
theorem cocycles₁_ext
  given: {f₁ f₂ : cocycles₁ A} (h : forall g : G, f₁ g = f₂ g)
  statement: f₁ = f₂
  proof: DFunLike.ext f₁ f₂ h

中文:
定理 cocycles₁_ext
  条件: {f₁ f₂ : cocycles₁ A} (h : 对任意 g : G, f₁ g = f₂ g)
  结论: f₁ = f₂
  证明: DFunLike.ext f₁ f₂ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem cocycles₁_ext {f₁ f₂ : cocycles₁ A} (h : forall g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h

/--
theorem `mem_cocycles₁_def` / 定理 `mem_cocycles₁_def`

English:
theorem mem_cocycles₁_def
  given: (f : G -> A)
  proof: LinearMap.mem_ker.trans by
    simp_rw [funext_iff, d₁₂_hom_apply, Prod.forall]
    rfl

中文:
定理 mem_cocycles₁_def
  条件: (f : G -> A)
  证明: LinearMap.mem_ker.trans by
    simp_rw [funext_iff, d₁₂_hom_apply, Prod.forall]
    rfl

Depends on / 依赖: LinearMap, LinearMap.mem_ker.trans, Prod.forall, funext_iff, mem_ker, simp_rw
-/
theorem mem_cocycles₁_def (f : G -> A) :
    f in cocycles₁ A ↔ forall g h : G, A.ρ g (f h) - f (g * h) + f g = 0 :=
LinearMap.mem_ker.trans by
    simp_rw [funext_iff, d₁₂_hom_apply, Prod.forall]
    rfl

/--
theorem `mem_cocycles₁_iff` / 定理 `mem_cocycles₁_iff`

English:
theorem mem_cocycles₁_iff
  given: (f : G -> A)
  proof: by
  simp_rw [mem_cocycles₁_def, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

中文:
定理 mem_cocycles₁_iff
  条件: (f : G -> A)
  证明: by
  simp_rw [mem_cocycles₁_def, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

Depends on / 依赖: eq_comm, simp_rw, sub_add_eq_add_sub, sub_eq_zero
-/
theorem mem_cocycles₁_iff (f : G -> A) :
    f in cocycles₁ A ↔ forall g h : G, f (g * h) = A.ρ g (f h) + f g := by
  simp_rw [mem_cocycles₁_def, sub_add_eq_add_sub, sub_eq_zero, eq_comm]

/--
theorem `cocycles₁_map_one` / 定理 `cocycles₁_map_one`

English:
theorem cocycles₁_map_one
  given: (f : cocycles₁ A)
  statement: f 1 = 0
  proof: by
  have := (mem_cocycles₁_def f).1 f.2 1 1
  simpa only [map_one, Module.End.one_apply, mul_one, sub_self, zero_add] using this

中文:
定理 cocycles₁_map_one
  条件: (f : cocycles₁ A)
  结论: f 1 = 0
  证明: by
  have := (mem_cocycles₁_def f).1 f.2 1 1
  simpa only [map_one, Module.End.one_apply, mul_one, sub_self, zero_add] using this
-/
@[simp] theorem cocycles₁_map_one (f : cocycles₁ A) : f 1 = 0 := by
  have := (mem_cocycles₁_def f).1 f.2 1 1
  simpa only [map_one, Module.End.one_apply, mul_one, sub_self, zero_add] using this

/--
theorem `cocycles₁_map_inv` / 定理 `cocycles₁_map_inv`

English:
theorem cocycles₁_map_inv
  given: (f : cocycles₁ A) (g : G)
  proof: by
  rw [← add_eq_zero_iff_eq_neg]; rw [← cocycles₁_map_one f]; rw [← mul_inv_cancel g]; rw [(mem_cocycles₁_iff f).1 f.2 g g⁻¹]

中文:
定理 cocycles₁_map_inv
  条件: (f : cocycles₁ A) (g : G)
  证明: by
  rw [← add_eq_zero_iff_eq_neg]; rw [← cocycles₁_map_one f]; rw [← mul_inv_cancel g]; rw [(mem_cocycles₁_iff f).1 f.2 g g⁻¹]
-/
@[simp] theorem cocycles₁_map_inv (f : cocycles₁ A) (g : G) :
    A.ρ g (f g⁻¹) = -f g := by
  rw [← add_eq_zero_iff_eq_neg]; rw [← cocycles₁_map_one f]; rw [← mul_inv_cancel g]; rw [(mem_cocycles₁_iff f).1 f.2 g g⁻¹]

/--
theorem `d₀₁_apply_mem_cocycles₁` / 定理 `d₀₁_apply_mem_cocycles₁`

English:
theorem d₀₁_apply_mem_cocycles₁
  given: (x : A)
  proof: d₀₁_comp_d₁₂_apply _ _

@[simp]

中文:
定理 d₀₁_apply_mem_cocycles₁
  条件: (x : A)
  证明: d₀₁_comp_d₁₂_apply _ _

@[simp]
-/
theorem d₀₁_apply_mem_cocycles₁ (x : A) :
    d₀₁ A x in cocycles₁ A :=
  d₀₁_comp_d₁₂_apply _ _

@[simp]
/--
theorem `cocycles₁.d₁₂_apply` / 定理 `cocycles₁.d₁₂_apply`

English:
theorem cocycles₁.d₁₂_apply
  given: (x : cocycles₁ A)
  proof: x.2

中文:
定理 cocycles₁.d₁₂_apply
  条件: (x : cocycles₁ A)
  证明: x.2
-/
theorem cocycles₁.d₁₂_apply (x : cocycles₁ A) :
    d₁₂ A x = 0 := x.2

/--
theorem `cocycles₁_map_mul_of_isTrivial` / 定理 `cocycles₁_map_mul_of_isTrivial`

English:
theorem cocycles₁_map_mul_of_isTrivial
  given: [A.IsTrivial] (f : cocycles₁ A) (g h : G)
  proof: by
  rw [(mem_cocycles₁_iff f).1 f.2]; rw [isTrivial_apply A.ρ g (f h)]; rw [add_comm]

中文:
定理 cocycles₁_map_mul_of_isTrivial
  条件: [A.是平凡] (f : cocycles₁ A) (g h : G)
  证明: by
  rw [(mem_cocycles₁_iff f).1 f.2]; rw [isTrivial_apply A.ρ g (f h)]; rw [add_comm]

Depends on / 依赖: add_comm, isTrivial_apply
-/
theorem cocycles₁_map_mul_of_isTrivial [A.IsTrivial] (f : cocycles₁ A) (g h : G) :
    f (g * h) = f g + f h := by
  rw [(mem_cocycles₁_iff f).1 f.2]; rw [isTrivial_apply A.ρ g (f h)]; rw [add_comm]

/--
theorem `mem_cocycles₁_of_addMonoidHom` / 定理 `mem_cocycles₁_of_addMonoidHom`

English:
theorem mem_cocycles₁_of_addMonoidHom
  given: [A.IsTrivial] (f : Additive G ->+ A)
  proof: (mem_cocycles₁_iff _).2 fun g h => by
    simp only [Function.comp_apply, ofMul_mul, map_add,
      isTrivial_apply A.ρ g (f (Additive.ofMul h)), add_comm (f (Additive.ofMul g))]

中文:
定理 mem_cocycles₁_of_addMonoidHom
  条件: [A.是平凡] (f : 加性 G ->+ A)
  证明: (mem_cocycles₁_iff _).2 fun g h => by
    simp only [Function.comp_apply, ofMul_mul, map_add,
      isTrivial_apply A.ρ g (f (Additive.ofMul h)), add_comm (f (Additive.ofMul g))]

Depends on / 依赖: Additive, Additive.ofMul, Function, Function.comp_apply, add_comm, comp_apply, isTrivial_apply, map_add, ofMul_mul
-/
theorem mem_cocycles₁_of_addMonoidHom [A.IsTrivial] (f : Additive G ->+ A) :
    f ∘ Additive.ofMul in cocycles₁ A :=
  (mem_cocycles₁_iff _).2 fun g h => by
    simp only [Function.comp_apply, ofMul_mul, map_add,
      isTrivial_apply A.ρ g (f (Additive.ofMul h)), add_comm (f (Additive.ofMul g))]

variable (A) in
/-- When `A : Rep k G` is a trivial representation of `G`, `Z¹(G, A)` is isomorphic to the
group homs `G → A`. -/
@[simps!]
/--
Definition of `cocycles₁IsoOfIsTrivial` / `cocycles₁IsoOfIsTrivial` 的定义

English:
definition cocycles₁IsoOfIsTrivial
  signature: [hA : A.IsTrivial]
  body: LinearEquiv.toModuleIso
  { toFun f :=
      { toFun := f ∘ Additive.toMul
        map_zero' := cocycles₁_map_one f
        map_add' := cocycles₁_map_mul_of_isTrivial f }
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    invFun f :=
      { val := f
        property := mem_cocycles₁_of_addMonoidHom f } }

中文:
定义 cocycles₁IsoOfIsTrivial
  签名: [hA : A.是平凡]
  定义体: LinearEquiv.toModuleIso
  { toFun f :=
      { toFun := f ∘ Additive.toMul
        map_zero' := cocycles₁_map_one f
        map_add' := cocycles₁_map_mul_of_isTrivial f }
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    invFun f :=
      { val := f
        property := mem_cocycles₁_of_addMonoidHom f } }

Depends on / 依赖: Additive, Additive.toMul, LinearEquiv, LinearEquiv.toModuleIso, invFun, map_add, map_smul, map_zero, property, toModuleIso
-/
def cocycles₁IsoOfIsTrivial [hA : A.IsTrivial] :
    ModuleCat.of k (cocycles₁ A) ≅ ModuleCat.of k (Additive G ->+ A) :=
  LinearEquiv.toModuleIso
  { toFun f :=
      { toFun := f ∘ Additive.toMul
        map_zero' := cocycles₁_map_one f
        map_add' := cocycles₁_map_mul_of_isTrivial f }
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    invFun f :=
      { val := f
        property := mem_cocycles₁_of_addMonoidHom f } }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (cocycles₂ A) (G × G) A
  body: ⟨Subtype.val, Subtype.val_injective⟩

@[simp]

中文:
实例 :
  签名: 函数状 (cocycles₂ A) (G × G) A
  定义体: ⟨Subtype.val, Subtype.val_injective⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.val, Subtype.val_injective, val_injective
-/
instance : FunLike (cocycles₂ A) (G × G) A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
/--
theorem `cocycles₂.coe_mk` / 定理 `cocycles₂.coe_mk`

English:
theorem cocycles₂.coe_mk
  given: (f : G × G -> A) (hf)
  statement: ((⟨f, hf⟩ : cocycles₂ A) : G × G -> A) = f
  proof: rfl

@[simp]

中文:
定理 cocycles₂.coe_mk
  条件: (f : G × G -> A) (hf)
  结论: ((⟨f, hf⟩ : cocycles₂ A) : G × G -> A) = f
  证明: rfl

@[simp]
-/
theorem cocycles₂.coe_mk (f : G × G -> A) (hf) : ((⟨f, hf⟩ : cocycles₂ A) : G × G -> A) = f := rfl

@[simp]
/--
theorem `cocycles₂.val_eq_coe` / 定理 `cocycles₂.val_eq_coe`

English:
theorem cocycles₂.val_eq_coe
  given: (f : cocycles₂ A)
  statement: f.1 = f
  proof: rfl

@[ext]

中文:
定理 cocycles₂.val_eq_coe
  条件: (f : cocycles₂ A)
  结论: f.1 = f
  证明: rfl

@[ext]
-/
theorem cocycles₂.val_eq_coe (f : cocycles₂ A) : f.1 = f := rfl

@[ext]
/--
theorem `cocycles₂_ext` / 定理 `cocycles₂_ext`

English:
theorem cocycles₂_ext
  given: {f₁ f₂ : cocycles₂ A} (h : forall g h : G, f₁ (g, h) = f₂ (g, h))
  statement: f₁ = f₂
  proof: DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

中文:
定理 cocycles₂_ext
  条件: {f₁ f₂ : cocycles₂ A} (h : 对任意 g h : G, f₁ (g, h) = f₂ (g, h))
  结论: f₁ = f₂
  证明: DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

Depends on / 依赖: DFunLike, DFunLike.ext, Prod.forall.mpr
-/
theorem cocycles₂_ext {f₁ f₂ : cocycles₂ A} (h : forall g h : G, f₁ (g, h) = f₂ (g, h)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

/--
theorem `mem_cocycles₂_def` / 定理 `mem_cocycles₂_def`

English:
theorem mem_cocycles₂_def
  given: (f : G × G -> A)
  proof: LinearMap.mem_ker.trans by
    simp_rw [funext_iff, d₂₃_hom_apply, Prod.forall]
    rfl

中文:
定理 mem_cocycles₂_def
  条件: (f : G × G -> A)
  证明: LinearMap.mem_ker.trans by
    simp_rw [funext_iff, d₂₃_hom_apply, Prod.forall]
    rfl

Depends on / 依赖: LinearMap, LinearMap.mem_ker.trans, Prod.forall, funext_iff, mem_ker, simp_rw
-/
theorem mem_cocycles₂_def (f : G × G -> A) :
    f in cocycles₂ A ↔ forall g h j : G,
      A.ρ g (f (h, j)) - f (g * h, j) + f (g, h * j) - f (g, h) = 0 :=
LinearMap.mem_ker.trans by
    simp_rw [funext_iff, d₂₃_hom_apply, Prod.forall]
    rfl

/--
theorem `mem_cocycles₂_iff` / 定理 `mem_cocycles₂_iff`

English:
theorem mem_cocycles₂_iff
  given: (f : G × G -> A)
  proof: by
  simp_rw [mem_cocycles₂_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]

中文:
定理 mem_cocycles₂_iff
  条件: (f : G × G -> A)
  证明: by
  simp_rw [mem_cocycles₂_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]

Depends on / 依赖: add_comm, eq_comm, simp_rw, sub_add_eq_add_sub, sub_eq_iff_eq_add, sub_eq_zero
-/
theorem mem_cocycles₂_iff (f : G × G -> A) :
    f in cocycles₂ A ↔ forall g h j : G,
      f (g * h, j) + f (g, h) =
        A.ρ g (f (h, j)) + f (g, h * j) := by
  simp_rw [mem_cocycles₂_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]

/--
theorem `cocycles₂_map_one_fst` / 定理 `cocycles₂_map_one_fst`

English:
theorem cocycles₂_map_one_fst
  given: (f : cocycles₂ A) (g : G)
  proof: by
  have := ((mem_cocycles₂_iff f).1 f.2 1 1 g).symm
  simpa only [map_one, Module.End.one_apply, one_mul, add_right_inj, this]

中文:
定理 cocycles₂_map_one_fst
  条件: (f : cocycles₂ A) (g : G)
  证明: by
  have := ((mem_cocycles₂_iff f).1 f.2 1 1 g).symm
  simpa only [map_one, Module.End.one_apply, one_mul, add_right_inj, this]

Depends on / 依赖: Module, Module.End.one_apply, add_right_inj, map_one, one_apply, one_mul
-/
theorem cocycles₂_map_one_fst (f : cocycles₂ A) (g : G) :
    f (1, g) = f (1, 1) := by
  have := ((mem_cocycles₂_iff f).1 f.2 1 1 g).symm
  simpa only [map_one, Module.End.one_apply, one_mul, add_right_inj, this]

/--
theorem `cocycles₂_map_one_snd` / 定理 `cocycles₂_map_one_snd`

English:
theorem cocycles₂_map_one_snd
  given: (f : cocycles₂ A) (g : G)
  proof: by
  have := (mem_cocycles₂_iff f).1 f.2 g 1 1
  simpa only [mul_one, add_left_inj, this]

中文:
定理 cocycles₂_map_one_snd
  条件: (f : cocycles₂ A) (g : G)
  证明: by
  have := (mem_cocycles₂_iff f).1 f.2 g 1 1
  simpa only [mul_one, add_left_inj, this]

Depends on / 依赖: add_left_inj, mul_one
-/
theorem cocycles₂_map_one_snd (f : cocycles₂ A) (g : G) :
    f (g, 1) = A.ρ g (f (1, 1)) := by
  have := (mem_cocycles₂_iff f).1 f.2 g 1 1
  simpa only [mul_one, add_left_inj, this]

/--
lemma `cocycles₂_ρ_map_inv_sub_map_inv` / 引理 `cocycles₂_ρ_map_inv_sub_map_inv`

English:
lemma cocycles₂_ρ_map_inv_sub_map_inv
  given: (f : cocycles₂ A) (g : G)
  proof: by
  have := (mem_cocycles₂_iff f).1 f.2 g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, cocycles₂_map_one_fst _ g]
    at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

中文:
引理 cocycles₂_ρ_map_inv_sub_map_inv
  条件: (f : cocycles₂ A) (g : G)
  证明: by
  have := (mem_cocycles₂_iff f).1 f.2 g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, cocycles₂_map_one_fst _ g]
    at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

Depends on / 依赖: inv_mul_cancel, mul_inv_cancel, sub_eq_sub_iff_add_eq_add, this.symm
-/
lemma cocycles₂_ρ_map_inv_sub_map_inv (f : cocycles₂ A) (g : G) :
    A.ρ g (f (g⁻¹, g)) - f (g, g⁻¹)
      = f (1, 1) - f (g, 1) := by
  have := (mem_cocycles₂_iff f).1 f.2 g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, cocycles₂_map_one_fst _ g]
    at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

/--
theorem `d₁₂_apply_mem_cocycles₂` / 定理 `d₁₂_apply_mem_cocycles₂`

English:
theorem d₁₂_apply_mem_cocycles₂
  given: (x : G -> A)
  proof: d₁₂_comp_d₂₃_apply _ _

@[simp]

中文:
定理 d₁₂_apply_mem_cocycles₂
  条件: (x : G -> A)
  证明: d₁₂_comp_d₂₃_apply _ _

@[simp]
-/
theorem d₁₂_apply_mem_cocycles₂ (x : G -> A) :
    d₁₂ A x in cocycles₂ A :=
  d₁₂_comp_d₂₃_apply _ _

@[simp]
/--
theorem `cocycles₂.d₂₃_apply` / 定理 `cocycles₂.d₂₃_apply`

English:
theorem cocycles₂.d₂₃_apply
  given: (x : cocycles₂ A)
  proof: x.2

中文:
定理 cocycles₂.d₂₃_apply
  条件: (x : cocycles₂ A)
  证明: x.2
-/
theorem cocycles₂.d₂₃_apply (x : cocycles₂ A) :
    d₂₃ A x = 0 := x.2

end Cocycles

section Coboundaries

/--
Definition of `coboundaries₁` / `coboundaries₁` 的定义

English:
definition coboundaries₁
  signature: : Submodule k (G -> A)
  body: LinearMap.range (d₀₁ A).hom

中文:
定义 coboundaries₁
  签名: : 子模 k (G -> A)
  定义体: LinearMap.range (d₀₁ A).hom

Depends on / 依赖: LinearMap, LinearMap.range
-/
def coboundaries₁ : Submodule k (G -> A) :=
  LinearMap.range (d₀₁ A).hom

/--
Definition of `coboundaries₂` / `coboundaries₂` 的定义

English:
definition coboundaries₂
  signature: : Submodule k (G × G -> A)
  body: LinearMap.range (d₁₂ A).hom

中文:
定义 coboundaries₂
  签名: : 子模 k (G × G -> A)
  定义体: LinearMap.range (d₁₂ A).hom

Depends on / 依赖: CommMonoidWithZero, LinearMap, LinearMap.range, MonoidHom, MonoidHom.mrange, MonoidWithZeroHom, MonoidWithZeroHom.ofClass, mrange, ofClass
-/
def coboundaries₂ : Submodule k (G × G -> A) :=
  LinearMap.range (d₁₂ A).hom

variable {A}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (coboundaries₁ A) G A
  body: ⟨Subtype.val, Subtype.val_injective⟩

@[simp]

中文:
实例 :
  签名: 函数状 (coboundaries₁ A) G A
  定义体: ⟨Subtype.val, Subtype.val_injective⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.val, Subtype.val_injective, val_injective
-/
instance : FunLike (coboundaries₁ A) G A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
/--
theorem `coboundaries₁.coe_mk` / 定理 `coboundaries₁.coe_mk`

English:
theorem coboundaries₁.coe_mk
  given: (f : G -> A) (hf)
  proof: rfl

@[simp]

中文:
定理 coboundaries₁.coe_mk
  条件: (f : G -> A) (hf)
  证明: rfl

@[simp]

Depends on / 依赖: CommGroupWithZero, MonoidHom, MonoidHom.mrange, MonoidWithZeroHom, MonoidWithZeroHom.ofClass, mrange, ofClass
-/
theorem coboundaries₁.coe_mk (f : G -> A) (hf) :
    ((⟨f, hf⟩ : coboundaries₁ A) : G -> A) = f := rfl

@[simp]
/--
theorem `coboundaries₁.val_eq_coe` / 定理 `coboundaries₁.val_eq_coe`

English:
theorem coboundaries₁.val_eq_coe
  given: (f : coboundaries₁ A)
  statement: f.1 = f
  proof: rfl

@[ext]

中文:
定理 coboundaries₁.val_eq_coe
  条件: (f : coboundaries₁ A)
  结论: f.1 = f
  证明: rfl

@[ext]
-/
theorem coboundaries₁.val_eq_coe (f : coboundaries₁ A) : f.1 = f := rfl

@[ext]
/--
theorem `coboundaries₁_ext` / 定理 `coboundaries₁_ext`

English:
theorem coboundaries₁_ext
  given: {f₁ f₂ : coboundaries₁ A} (h : forall g : G, f₁ g = f₂ g)
  statement: f₁ = f₂
  proof: DFunLike.ext f₁ f₂ h

中文:
定理 coboundaries₁_ext
  条件: {f₁ f₂ : coboundaries₁ A} (h : 对任意 g : G, f₁ g = f₂ g)
  结论: f₁ = f₂
  证明: DFunLike.ext f₁ f₂ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem coboundaries₁_ext {f₁ f₂ : coboundaries₁ A} (h : forall g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h

variable (A) in
/--
lemma `coboundaries₁_le_cocycles₁` / 引理 `coboundaries₁_le_cocycles₁`

English:
lemma coboundaries₁_le_cocycles₁
  statement: coboundaries₁ A <= cocycles₁ A
  proof: by
  rintro _ ⟨x, rfl⟩
  exact d₀₁_apply_mem_cocycles₁ x

中文:
引理 coboundaries₁_le_cocycles₁
  结论: coboundaries₁ A <= cocycles₁ A
  证明: by
  rintro _ ⟨x, rfl⟩
  exact d₀₁_apply_mem_cocycles₁ x
-/
lemma coboundaries₁_le_cocycles₁ : coboundaries₁ A <= cocycles₁ A := by
  rintro _ ⟨x, rfl⟩
  exact d₀₁_apply_mem_cocycles₁ x

variable (A) in
/--
Definition of `coboundariesToCocycles₁` / `coboundariesToCocycles₁` 的定义

English:
abbreviation coboundariesToCocycles₁
  signature: : coboundaries₁ A ->ₗ[k] cocycles₁ A
  body: Submodule.inclusion (coboundaries₁_le_cocycles₁ A)

@[simp]

中文:
缩写 coboundariesToCocycles₁
  签名: : coboundaries₁ A ->ₗ[k] cocycles₁ A
  定义体: Submodule.inclusion (coboundaries₁_le_cocycles₁ A)

@[simp]

Depends on / 依赖: Submodule, Submodule.inclusion, inclusion
-/
abbrev coboundariesToCocycles₁ : coboundaries₁ A ->ₗ[k] cocycles₁ A :=
  Submodule.inclusion (coboundaries₁_le_cocycles₁ A)

@[simp]
/--
lemma `coboundariesToCocycles₁_apply` / 引理 `coboundariesToCocycles₁_apply`

English:
lemma coboundariesToCocycles₁_apply
  given: (x : coboundaries₁ A)
  proof: rfl

中文:
引理 coboundariesToCocycles₁_apply
  条件: (x : coboundaries₁ A)
  证明: rfl
-/
lemma coboundariesToCocycles₁_apply (x : coboundaries₁ A) :
    coboundariesToCocycles₁ A x = x.1 := rfl

/--
theorem `coboundaries₁_eq_bot_of_isTrivial` / 定理 `coboundaries₁_eq_bot_of_isTrivial`

English:
theorem coboundaries₁_eq_bot_of_isTrivial
  given: (A : Rep k G) [A.IsTrivial]
  proof: by
  simp_rw [coboundaries₁, d₀₁_eq_zero]
  exact LinearMap.range_eq_bot.2 rfl

中文:
定理 coboundaries₁_eq_bot_of_isTrivial
  条件: (A : Rep k G) [A.是平凡]
  证明: by
  simp_rw [coboundaries₁, d₀₁_eq_zero]
  exact LinearMap.range_eq_bot.2 rfl

Depends on / 依赖: LinearMap, LinearMap.range_eq_bot, range_eq_bot, simp_rw
-/
theorem coboundaries₁_eq_bot_of_isTrivial (A : Rep k G) [A.IsTrivial] :
    coboundaries₁ A = ⊥ := by
  simp_rw [coboundaries₁, d₀₁_eq_zero]
  exact LinearMap.range_eq_bot.2 rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (coboundaries₂ A) (G × G) A
  body: ⟨Subtype.val, Subtype.val_injective⟩

@[simp]

中文:
实例 :
  签名: 函数状 (coboundaries₂ A) (G × G) A
  定义体: ⟨Subtype.val, Subtype.val_injective⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.val, Subtype.val_injective, val_injective
-/
instance : FunLike (coboundaries₂ A) (G × G) A := ⟨Subtype.val, Subtype.val_injective⟩

@[simp]
/--
theorem `coboundaries₂.coe_mk` / 定理 `coboundaries₂.coe_mk`

English:
theorem coboundaries₂.coe_mk
  given: (f : G × G -> A) (hf)
  proof: rfl

@[simp]

中文:
定理 coboundaries₂.coe_mk
  条件: (f : G × G -> A) (hf)
  证明: rfl

@[simp]
-/
theorem coboundaries₂.coe_mk (f : G × G -> A) (hf) :
    ((⟨f, hf⟩ : coboundaries₂ A) : G × G -> A) = f := rfl

@[simp]
/--
theorem `coboundaries₂.val_eq_coe` / 定理 `coboundaries₂.val_eq_coe`

English:
theorem coboundaries₂.val_eq_coe
  given: (f : coboundaries₂ A)
  statement: f.1 = f
  proof: rfl

@[ext]

中文:
定理 coboundaries₂.val_eq_coe
  条件: (f : coboundaries₂ A)
  结论: f.1 = f
  证明: rfl

@[ext]
-/
theorem coboundaries₂.val_eq_coe (f : coboundaries₂ A) : f.1 = f := rfl

@[ext]
/--
theorem `coboundaries₂_ext` / 定理 `coboundaries₂_ext`

English:
theorem coboundaries₂_ext
  given: {f₁ f₂ : coboundaries₂ A} (h : forall g h : G, f₁ (g, h) = f₂ (g, h))
  proof: DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

中文:
定理 coboundaries₂_ext
  条件: {f₁ f₂ : coboundaries₂ A} (h : 对任意 g h : G, f₁ (g, h) = f₂ (g, h))
  证明: DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

Depends on / 依赖: DFunLike, DFunLike.ext, Prod.forall.mpr
-/
theorem coboundaries₂_ext {f₁ f₂ : coboundaries₂ A} (h : forall g h : G, f₁ (g, h) = f₂ (g, h)) :
    f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.mpr h)

variable (A) in
/--
lemma `coboundaries₂_le_cocycles₂` / 引理 `coboundaries₂_le_cocycles₂`

English:
lemma coboundaries₂_le_cocycles₂
  statement: coboundaries₂ A <= cocycles₂ A
  proof: by
  rintro _ ⟨x, rfl⟩
  exact d₁₂_apply_mem_cocycles₂ x

中文:
引理 coboundaries₂_le_cocycles₂
  结论: coboundaries₂ A <= cocycles₂ A
  证明: by
  rintro _ ⟨x, rfl⟩
  exact d₁₂_apply_mem_cocycles₂ x
-/
lemma coboundaries₂_le_cocycles₂ : coboundaries₂ A <= cocycles₂ A := by
  rintro _ ⟨x, rfl⟩
  exact d₁₂_apply_mem_cocycles₂ x

variable (A) in
/--
Definition of `coboundariesToCocycles₂` / `coboundariesToCocycles₂` 的定义

English:
abbreviation coboundariesToCocycles₂
  signature: : coboundaries₂ A ->ₗ[k] cocycles₂ A
  body: Submodule.inclusion (coboundaries₂_le_cocycles₂ A)

@[simp]

中文:
缩写 coboundariesToCocycles₂
  签名: : coboundaries₂ A ->ₗ[k] cocycles₂ A
  定义体: Submodule.inclusion (coboundaries₂_le_cocycles₂ A)

@[simp]

Depends on / 依赖: Submodule, Submodule.inclusion, inclusion
-/
abbrev coboundariesToCocycles₂ : coboundaries₂ A ->ₗ[k] cocycles₂ A :=
  Submodule.inclusion (coboundaries₂_le_cocycles₂ A)

@[simp]
/--
lemma `coboundariesToCocycles₂_apply` / 引理 `coboundariesToCocycles₂_apply`

English:
lemma coboundariesToCocycles₂_apply
  given: (x : coboundaries₂ A)
  proof: rfl

中文:
引理 coboundariesToCocycles₂_apply
  条件: (x : coboundaries₂ A)
  证明: rfl
-/
lemma coboundariesToCocycles₂_apply (x : coboundaries₂ A) :
    coboundariesToCocycles₂ A x = x.1 := rfl

end Coboundaries

section IsCocycle

section

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/--
Definition of `IsCocycle₁` / `IsCocycle₁` 的定义

English:
definition IsCocycle₁
  signature: (f : G -> A)
  body: forall g h : G, f (g * h) = g • f h + f g

中文:
定义 IsCocycle₁
  签名: (f : G -> A)
  定义体: forall g h : G, f (g * h) = g • f h + f g
-/
def IsCocycle₁ (f : G -> A) : Prop := forall g h : G, f (g * h) = g • f h + f g

/--
Definition of `IsCocycle₂` / `IsCocycle₂` 的定义

English:
definition IsCocycle₂
  signature: (f : G × G -> A)
  body: forall g h j : G, f (g * h, j) + f (g, h) = g • (f (h, j)) + f (g, h * j)

中文:
定义 IsCocycle₂
  签名: (f : G × G -> A)
  定义体: forall g h j : G, f (g * h, j) + f (g, h) = g • (f (h, j)) + f (g, h * j)
-/
def IsCocycle₂ (f : G × G -> A) : Prop :=
  forall g h j : G, f (g * h, j) + f (g, h) = g • (f (h, j)) + f (g, h * j)

end

section

variable {G A : Type*} [Monoid G] [AddCommGroup A] [MulAction G A]

/--
theorem `map_one_of_isCocycle₁` / 定理 `map_one_of_isCocycle₁`

English:
theorem map_one_of_isCocycle₁
  given: {f : G -> A} (hf : IsCocycle₁ f)
  proof: by
  simpa only [mul_one, one_smul, left_eq_add] using hf 1 1

中文:
定理 map_one_of_isCocycle₁
  条件: {f : G -> A} (hf : IsCocycle₁ f)
  证明: by
  simpa only [mul_one, one_smul, left_eq_add] using hf 1 1

Depends on / 依赖: left_eq_add, mul_one, one_smul
-/
theorem map_one_of_isCocycle₁ {f : G -> A} (hf : IsCocycle₁ f) :
    f 1 = 0 := by
  simpa only [mul_one, one_smul, left_eq_add] using hf 1 1

/--
theorem `map_one_fst_of_isCocycle₂` / 定理 `map_one_fst_of_isCocycle₂`

English:
theorem map_one_fst_of_isCocycle₂
  given: {f : G × G -> A} (hf : IsCocycle₂ f) (g : G)
  proof: by
  simpa only [one_smul, one_mul, mul_one, add_right_inj] using (hf 1 1 g).symm

中文:
定理 map_one_fst_of_isCocycle₂
  条件: {f : G × G -> A} (hf : IsCocycle₂ f) (g : G)
  证明: by
  simpa only [one_smul, one_mul, mul_one, add_right_inj] using (hf 1 1 g).symm

Depends on / 依赖: add_right_inj, mul_one, one_mul, one_smul
-/
theorem map_one_fst_of_isCocycle₂ {f : G × G -> A} (hf : IsCocycle₂ f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, add_right_inj] using (hf 1 1 g).symm

/--
theorem `map_one_snd_of_isCocycle₂` / 定理 `map_one_snd_of_isCocycle₂`

English:
theorem map_one_snd_of_isCocycle₂
  given: {f : G × G -> A} (hf : IsCocycle₂ f) (g : G)
  proof: by
  simpa only [mul_one, add_left_inj] using hf g 1 1

中文:
定理 map_one_snd_of_isCocycle₂
  条件: {f : G × G -> A} (hf : IsCocycle₂ f) (g : G)
  证明: by
  simpa only [mul_one, add_left_inj] using hf g 1 1

Depends on / 依赖: add_left_inj, mul_one
-/
theorem map_one_snd_of_isCocycle₂ {f : G × G -> A} (hf : IsCocycle₂ f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, add_left_inj] using hf g 1 1

end

section

variable {G A : Type*} [Group G] [AddCommGroup A] [MulAction G A]

/--
theorem `map_inv_of_isCocycle₁` / 定理 `map_inv_of_isCocycle₁`

English:
theorem map_inv_of_isCocycle₁
  given: {f : G -> A} (hf : IsCocycle₁ f) (g : G)
  proof: by
  rw [← add_eq_zero_iff_eq_neg]; rw [← map_one_of_isCocycle₁ hf]; rw [← mul_inv_cancel g]; rw [hf g g⁻¹]

中文:
定理 map_inv_of_isCocycle₁
  条件: {f : G -> A} (hf : IsCocycle₁ f) (g : G)
  证明: by
  rw [← add_eq_zero_iff_eq_neg]; rw [← map_one_of_isCocycle₁ hf]; rw [← mul_inv_cancel g]; rw [hf g g⁻¹]
-/
@[scoped simp] theorem map_inv_of_isCocycle₁ {f : G -> A} (hf : IsCocycle₁ f) (g : G) :
    g • f g⁻¹ = -f g := by
  rw [← add_eq_zero_iff_eq_neg]; rw [← map_one_of_isCocycle₁ hf]; rw [← mul_inv_cancel g]; rw [hf g g⁻¹]

/--
theorem `smul_map_inv_sub_map_inv_of_isCocycle₂` / 定理 `smul_map_inv_sub_map_inv_of_isCocycle₂`

English:
theorem smul_map_inv_sub_map_inv_of_isCocycle₂
  given: {f : G × G -> A} (hf : IsCocycle₂ f) (g : G)
  proof: by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isCocycle₂ hf g] at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

中文:
定理 smul_map_inv_sub_map_inv_of_isCocycle₂
  条件: {f : G × G -> A} (hf : IsCocycle₂ f) (g : G)
  证明: by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isCocycle₂ hf g] at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

Depends on / 依赖: inv_mul_cancel, mul_inv_cancel, sub_eq_sub_iff_add_eq_add, this.symm
-/
theorem smul_map_inv_sub_map_inv_of_isCocycle₂ {f : G × G -> A} (hf : IsCocycle₂ f) (g : G) :
    g • f (g⁻¹, g) - f (g, g⁻¹) = f (1, 1) - f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isCocycle₂ hf g] at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm

end

end IsCocycle

section IsCoboundary

variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]

/--
Definition of `IsCoboundary₁` / `IsCoboundary₁` 的定义

English:
definition IsCoboundary₁
  signature: (f : G -> A)
  body: exists x : A, forall g : G, g • x - x = f g

中文:
定义 IsCoboundary₁
  签名: (f : G -> A)
  定义体: exists x : A, forall g : G, g • x - x = f g
-/
def IsCoboundary₁ (f : G -> A) : Prop := exists x : A, forall g : G, g • x - x = f g

/--
Definition of `IsCoboundary₂` / `IsCoboundary₂` 的定义

English:
definition IsCoboundary₂
  signature: (f : G × G -> A)
  body: exists x : G -> A, forall g h : G, g • x h - x (g * h) + x g = f (g, h)

中文:
定义 IsCoboundary₂
  签名: (f : G × G -> A)
  定义体: exists x : G -> A, forall g h : G, g • x h - x (g * h) + x g = f (g, h)
-/
def IsCoboundary₂ (f : G × G -> A) : Prop :=
  exists x : G -> A, forall g h : G, g • x h - x (g * h) + x g = f (g, h)

end IsCoboundary

section ofDistribMulAction

variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-cocycle condition, produces a 1-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
/--
Definition of `cocyclesOfIsCocycle₁` / `cocyclesOfIsCocycle₁` 的定义

English:
definition cocyclesOfIsCocycle₁
  signature: {f : G -> A} (hf : IsCocycle₁ f)
  body: ⟨f, (mem_cocycles₁_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

中文:
定义 cocyclesOfIsCocycle₁
  签名: {f : G -> A} (hf : IsCocycle₁ f)
  定义体: ⟨f, (mem_cocycles₁_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

Depends on / 依赖: Rep.ofDistribMulAction, ofDistribMulAction
-/
def cocyclesOfIsCocycle₁ {f : G -> A} (hf : IsCocycle₁ f) :
    cocycles₁ (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_cocycles₁_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

/--
theorem `isCocycle₁_of_mem_cocycles₁` / 定理 `isCocycle₁_of_mem_cocycles₁`

English:
theorem isCocycle₁_of_mem_cocycles₁
  proof: fun _ _ => (mem_cocycles₁_iff (A := Rep.ofDistribMulAction k G A) f).1 hf _ _

中文:
定理 isCocycle₁_of_mem_cocycles₁
  证明: fun _ _ => (mem_cocycles₁_iff (A := Rep.ofDistribMulAction k G A) f).1 hf _ _

Depends on / 依赖: Rep.ofDistribMulAction, ofDistribMulAction
-/
theorem isCocycle₁_of_mem_cocycles₁
    (f : G -> A) (hf : f in cocycles₁ (Rep.ofDistribMulAction k G A)) :
    IsCocycle₁ f :=
  fun _ _ => (mem_cocycles₁_iff (A := Rep.ofDistribMulAction k G A) f).1 hf _ _

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G → A` satisfying the 1-coboundary condition, produces a 1-coboundary for the representation
on `A` induced by the `DistribMulAction`. -/
@[simps]
/--
Definition of `coboundariesOfIsCoboundary₁` / `coboundariesOfIsCoboundary₁` 的定义

English:
definition coboundariesOfIsCoboundary₁
  signature: {f : G -> A} (hf : IsCoboundary₁ f)
  body: ⟨f, hf.choose, funext hf.choose_spec⟩

中文:
定义 coboundariesOfIsCoboundary₁
  签名: {f : G -> A} (hf : IsCoboundary₁ f)
  定义体: ⟨f, hf.choose, funext hf.choose_spec⟩

Depends on / 依赖: choose_spec, hf.choose, hf.choose_spec
-/
def coboundariesOfIsCoboundary₁ {f : G -> A} (hf : IsCoboundary₁ f) :
    coboundaries₁ (Rep.ofDistribMulAction k G A) :=
  ⟨f, hf.choose, funext hf.choose_spec⟩

/--
theorem `isCoboundary₁_of_mem_coboundaries₁` / 定理 `isCoboundary₁_of_mem_coboundaries₁`

English:
theorem isCoboundary₁_of_mem_coboundaries₁
  proof: by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ => rfl⟩

中文:
定理 isCoboundary₁_of_mem_coboundaries₁
  证明: by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ => rfl⟩
-/
theorem isCoboundary₁_of_mem_coboundaries₁
    (f : G -> A) (hf : f in coboundaries₁ (Rep.ofDistribMulAction k G A)) :
    IsCoboundary₁ f := by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ => rfl⟩

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-cocycle condition, produces a 2-cocycle for the representation on
`A` induced by the `DistribMulAction`. -/
@[simps]
/--
Definition of `cocyclesOfIsCocycle₂` / `cocyclesOfIsCocycle₂` 的定义

English:
definition cocyclesOfIsCocycle₂
  signature: {f : G × G -> A} (hf : IsCocycle₂ f)
  body: ⟨f, (mem_cocycles₂_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

中文:
定义 cocyclesOfIsCocycle₂
  签名: {f : G × G -> A} (hf : IsCocycle₂ f)
  定义体: ⟨f, (mem_cocycles₂_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

Depends on / 依赖: Rep.ofDistribMulAction, ofDistribMulAction
-/
def cocyclesOfIsCocycle₂ {f : G × G -> A} (hf : IsCocycle₂ f) :
    cocycles₂ (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_cocycles₂_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩

/--
theorem `isCocycle₂_of_mem_cocycles₂` / 定理 `isCocycle₂_of_mem_cocycles₂`

English:
theorem isCocycle₂_of_mem_cocycles₂
  proof: (mem_cocycles₂_iff (A := Rep.ofDistribMulAction k G A) f).1 hf

中文:
定理 isCocycle₂_of_mem_cocycles₂
  证明: (mem_cocycles₂_iff (A := Rep.ofDistribMulAction k G A) f).1 hf

Depends on / 依赖: Rep.ofDistribMulAction, ofDistribMulAction
-/
theorem isCocycle₂_of_mem_cocycles₂
    (f : G × G -> A) (hf : f in cocycles₂ (Rep.ofDistribMulAction k G A)) :
    IsCocycle₂ f := (mem_cocycles₂_iff (A := Rep.ofDistribMulAction k G A) f).1 hf

/-- Given a `k`-module `A` with a compatible `DistribMulAction` of `G`, and a function
`f : G × G → A` satisfying the 2-coboundary condition, produces a 2-coboundary for the
representation on `A` induced by the `DistribMulAction`. -/
@[simps]
/--
Definition of `coboundariesOfIsCoboundary₂` / `coboundariesOfIsCoboundary₂` 的定义

English:
definition coboundariesOfIsCoboundary₂
  signature: {f : G × G -> A} (hf : IsCoboundary₂ f)
  body: ⟨f, hf.choose,funext fun g => hf.choose_spec g.1 g.2⟩

中文:
定义 coboundariesOfIsCoboundary₂
  签名: {f : G × G -> A} (hf : IsCoboundary₂ f)
  定义体: ⟨f, hf.choose,funext fun g => hf.choose_spec g.1 g.2⟩

Depends on / 依赖: choose_spec, hf.choose, hf.choose_spec
-/
def coboundariesOfIsCoboundary₂ {f : G × G -> A} (hf : IsCoboundary₂ f) :
    coboundaries₂ (Rep.ofDistribMulAction k G A) :=
  ⟨f, hf.choose,funext fun g => hf.choose_spec g.1 g.2⟩

/--
theorem `isCoboundary₂_of_mem_coboundaries₂` / 定理 `isCoboundary₂_of_mem_coboundaries₂`

English:
theorem isCoboundary₂_of_mem_coboundaries₂
  proof: by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ _ => rfl⟩

中文:
定理 isCoboundary₂_of_mem_coboundaries₂
  证明: by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ _ => rfl⟩
-/
theorem isCoboundary₂_of_mem_coboundaries₂
    (f : G × G -> A) (hf : f in coboundaries₂ (Rep.ofDistribMulAction k G A)) :
    IsCoboundary₂ f := by
  rcases hf with ⟨a, rfl⟩
  exact ⟨a, fun _ _ => rfl⟩

end ofDistribMulAction

/-! The next few sections, until the section `CocyclesIso`, are a multiplicative copy of the
previous few sections beginning with `IsCocycle`. Unfortunately `@[to_additive]` doesn't work with
scalar actions. -/

section IsMulCocycle

section

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/--
Definition of `IsMulCocycle₁` / `IsMulCocycle₁` 的定义

English:
definition IsMulCocycle₁
  signature: (f : G -> M)
  body: forall g h : G, f (g * h) = g • f h * f g

中文:
定义 IsMulCocycle₁
  签名: (f : G -> M)
  定义体: forall g h : G, f (g * h) = g • f h * f g
-/
def IsMulCocycle₁ (f : G -> M) : Prop := forall g h : G, f (g * h) = g • f h * f g

/--
Definition of `IsMulCocycle₂` / `IsMulCocycle₂` 的定义

English:
definition IsMulCocycle₂
  signature: (f : G × G -> M)
  body: forall g h j : G, f (g * h, j) * f (g, h) = g • (f (h, j)) * f (g, h * j)

中文:
定义 IsMulCocycle₂
  签名: (f : G × G -> M)
  定义体: forall g h j : G, f (g * h, j) * f (g, h) = g • (f (h, j)) * f (g, h * j)
-/
def IsMulCocycle₂ (f : G × G -> M) : Prop :=
  forall g h j : G, f (g * h, j) * f (g, h) = g • (f (h, j)) * f (g, h * j)

end

section

variable {G M : Type*} [Monoid G] [CommGroup M] [MulAction G M]

/--
theorem `map_one_of_isMulCocycle₁` / 定理 `map_one_of_isMulCocycle₁`

English:
theorem map_one_of_isMulCocycle₁
  given: {f : G -> M} (hf : IsMulCocycle₁ f)
  proof: by
  simpa only [mul_one, one_smul, left_eq_mul] using hf 1 1

中文:
定理 map_one_of_isMulCocycle₁
  条件: {f : G -> M} (hf : IsMulCocycle₁ f)
  证明: by
  simpa only [mul_one, one_smul, left_eq_mul] using hf 1 1

Depends on / 依赖: left_eq_mul, mul_one, one_smul
-/
theorem map_one_of_isMulCocycle₁ {f : G -> M} (hf : IsMulCocycle₁ f) :
    f 1 = 1 := by
  simpa only [mul_one, one_smul, left_eq_mul] using hf 1 1

/--
theorem `map_one_fst_of_isMulCocycle₂` / 定理 `map_one_fst_of_isMulCocycle₂`

English:
theorem map_one_fst_of_isMulCocycle₂
  given: {f : G × G -> M} (hf : IsMulCocycle₂ f) (g : G)
  proof: by
  simpa only [one_smul, one_mul, mul_one, mul_right_inj] using (hf 1 1 g).symm

中文:
定理 map_one_fst_of_isMulCocycle₂
  条件: {f : G × G -> M} (hf : IsMulCocycle₂ f) (g : G)
  证明: by
  simpa only [one_smul, one_mul, mul_one, mul_right_inj] using (hf 1 1 g).symm

Depends on / 依赖: mul_one, mul_right_inj, one_mul, one_smul
-/
theorem map_one_fst_of_isMulCocycle₂ {f : G × G -> M} (hf : IsMulCocycle₂ f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, mul_right_inj] using (hf 1 1 g).symm

/--
theorem `map_one_snd_of_isMulCocycle₂` / 定理 `map_one_snd_of_isMulCocycle₂`

English:
theorem map_one_snd_of_isMulCocycle₂
  given: {f : G × G -> M} (hf : IsMulCocycle₂ f) (g : G)
  proof: by
  simpa only [mul_one, mul_left_inj] using hf g 1 1

中文:
定理 map_one_snd_of_isMulCocycle₂
  条件: {f : G × G -> M} (hf : IsMulCocycle₂ f) (g : G)
  证明: by
  simpa only [mul_one, mul_left_inj] using hf g 1 1

Depends on / 依赖: mul_left_inj, mul_one
-/
theorem map_one_snd_of_isMulCocycle₂ {f : G × G -> M} (hf : IsMulCocycle₂ f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, mul_left_inj] using hf g 1 1

end

section

variable {G M : Type*} [Group G] [CommGroup M] [MulAction G M]

/--
theorem `map_inv_of_isMulCocycle₁` / 定理 `map_inv_of_isMulCocycle₁`

English:
theorem map_inv_of_isMulCocycle₁
  given: {f : G -> M} (hf : IsMulCocycle₁ f) (g : G)
  proof: by
  rw [← mul_eq_one_iff_eq_inv]; rw [← map_one_of_isMulCocycle₁ hf]; rw [← mul_inv_cancel g]; rw [hf g g⁻¹]

中文:
定理 map_inv_of_isMulCocycle₁
  条件: {f : G -> M} (hf : IsMulCocycle₁ f) (g : G)
  证明: by
  rw [← mul_eq_one_iff_eq_inv]; rw [← map_one_of_isMulCocycle₁ hf]; rw [← mul_inv_cancel g]; rw [hf g g⁻¹]
-/
@[scoped simp] theorem map_inv_of_isMulCocycle₁ {f : G -> M} (hf : IsMulCocycle₁ f) (g : G) :
    g • f g⁻¹ = (f g)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv]; rw [← map_one_of_isMulCocycle₁ hf]; rw [← mul_inv_cancel g]; rw [hf g g⁻¹]

/--
theorem `smul_map_inv_div_map_inv_of_isMulCocycle₂` / 定理 `smul_map_inv_div_map_inv_of_isMulCocycle₂`

English:
theorem smul_map_inv_div_map_inv_of_isMulCocycle₂
  proof: by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isMulCocycle₂ hf g] at this
  exact div_eq_div_iff_mul_eq_mul.2 this.symm

中文:
定理 smul_map_inv_div_map_inv_of_isMulCocycle₂
  证明: by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isMulCocycle₂ hf g] at this
  exact div_eq_div_iff_mul_eq_mul.2 this.symm

Depends on / 依赖: div_eq_div_iff_mul_eq_mul, inv_mul_cancel, mul_inv_cancel, this.symm
-/
theorem smul_map_inv_div_map_inv_of_isMulCocycle₂
    {f : G × G -> M} (hf : IsMulCocycle₂ f) (g : G) :
    g • f (g⁻¹, g) / f (g, g⁻¹) = f (1, 1) / f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isMulCocycle₂ hf g] at this
  exact div_eq_div_iff_mul_eq_mul.2 this.symm

end

end IsMulCocycle

section IsMulCoboundary

variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]

/--
Definition of `IsMulCoboundary₁` / `IsMulCoboundary₁` 的定义

English:
definition IsMulCoboundary₁
  signature: (f : G -> M)
  body: exists x : M, forall g : G, g • x / x = f g

中文:
定义 IsMulCoboundary₁
  签名: (f : G -> M)
  定义体: exists x : M, forall g : G, g • x / x = f g
-/
def IsMulCoboundary₁ (f : G -> M) : Prop := exists x : M, forall g : G, g • x / x = f g

/--
Definition of `IsMulCoboundary₂` / `IsMulCoboundary₂` 的定义

English:
definition IsMulCoboundary₂
  signature: (f : G × G -> M)
  body: exists x : G -> M, forall g h : G, g • x h / x (g * h) * x g = f (g, h)

中文:
定义 IsMulCoboundary₂
  签名: (f : G × G -> M)
  定义体: exists x : G -> M, forall g h : G, g • x h / x (g * h) * x g = f (g, h)
-/
def IsMulCoboundary₂ (f : G × G -> M) : Prop :=
  exists x : G -> M, forall g h : G, g • x h / x (g * h) * x g = f (g, h)

end IsMulCoboundary

section ofMulDistribMulAction

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-cocycle condition, produces a 1-cocycle for the
representation on `Additive M` induced by the `MulDistribMulAction`. -/
@[simps]
/--
Definition of `cocyclesOfIsMulCocycle₁` / `cocyclesOfIsMulCocycle₁` 的定义

English:
definition cocyclesOfIsMulCocycle₁
  signature: {f : G -> M} (hf : IsMulCocycle₁ f)
  body: ⟨Additive.ofMul ∘ f, (mem_cocycles₁_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

中文:
定义 cocyclesOfIsMulCocycle₁
  签名: {f : G -> M} (hf : IsMulCocycle₁ f)
  定义体: ⟨Additive.ofMul ∘ f, (mem_cocycles₁_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

Depends on / 依赖: Additive, Additive.ofMul, Rep.ofMulDistribMulAction, ofMulDistribMulAction
-/
def cocyclesOfIsMulCocycle₁ {f : G -> M} (hf : IsMulCocycle₁ f) :
    cocycles₁ (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_cocycles₁_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

/--
theorem `isMulCocycle₁_of_mem_cocycles₁` / 定理 `isMulCocycle₁_of_mem_cocycles₁`

English:
theorem isMulCocycle₁_of_mem_cocycles₁
  proof: (mem_cocycles₁_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

中文:
定理 isMulCocycle₁_of_mem_cocycles₁
  证明: (mem_cocycles₁_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

Depends on / 依赖: Rep.ofMulDistribMulAction, ofMulDistribMulAction
-/
theorem isMulCocycle₁_of_mem_cocycles₁
    (f : G -> M) (hf : f in cocycles₁ (Rep.ofMulDistribMulAction G M)) :
    IsMulCocycle₁ (Additive.toMul ∘ f) :=
  (mem_cocycles₁_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G → M` satisfying the multiplicative 1-coboundary condition, produces a
1-coboundary for the representation on `Additive M` induced by the `MulDistribMulAction`. -/
@[simps]
/--
Definition of `coboundariesOfIsMulCoboundary₁` / `coboundariesOfIsMulCoboundary₁` 的定义

English:
definition coboundariesOfIsMulCoboundary₁
  signature: {f : G -> M} (hf : IsMulCoboundary₁ f)
  body: ⟨Additive.ofMul ∘ f, hf.choose, funext hf.choose_spec⟩

中文:
定义 coboundariesOfIsMulCoboundary₁
  签名: {f : G -> M} (hf : IsMulCoboundary₁ f)
  定义体: ⟨Additive.ofMul ∘ f, hf.choose, funext hf.choose_spec⟩

Depends on / 依赖: Additive, Additive.ofMul, choose_spec, hf.choose, hf.choose_spec
-/
def coboundariesOfIsMulCoboundary₁ {f : G -> M} (hf : IsMulCoboundary₁ f) :
    coboundaries₁ (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, hf.choose, funext hf.choose_spec⟩

/--
theorem `isMulCoboundary₁_of_mem_coboundaries₁` / 定理 `isMulCoboundary₁_of_mem_coboundaries₁`

English:
theorem isMulCoboundary₁_of_mem_coboundaries₁
  proof: by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ => rfl⟩

中文:
定理 isMulCoboundary₁_of_mem_coboundaries₁
  证明: by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ => rfl⟩

Depends on / 依赖: Additive, Additive.ofMul
-/
theorem isMulCoboundary₁_of_mem_coboundaries₁
    (f : G -> M) (hf : f in coboundaries₁ (Rep.ofMulDistribMulAction G M)) :
    IsMulCoboundary₁ (M := M) (Additive.ofMul ∘ f) := by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ => rfl⟩

/-- Given an abelian group `M` with a `MulDistribMulAction` of `G`, and a function
`f : G × G → M` satisfying the multiplicative 2-cocycle condition, produces a 2-cocycle for the
representation on `cochainsIso₁Additive M` induced by the `MulDistribMulAction`. -/
@[simps]
/--
Definition of `cocyclesOfIsMulCocycle₂` / `cocyclesOfIsMulCocycle₂` 的定义

English:
definition cocyclesOfIsMulCocycle₂
  signature: {f : G × G -> M} (hf : IsMulCocycle₂ f)
  body: ⟨Additive.ofMul ∘ f, (mem_cocycles₂_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

中文:
定义 cocyclesOfIsMulCocycle₂
  签名: {f : G × G -> M} (hf : IsMulCocycle₂ f)
  定义体: ⟨Additive.ofMul ∘ f, (mem_cocycles₂_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

Depends on / 依赖: Additive, Additive.ofMul, Rep.ofMulDistribMulAction, ofMulDistribMulAction
-/
def cocyclesOfIsMulCocycle₂ {f : G × G -> M} (hf : IsMulCocycle₂ f) :
    cocycles₂ (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_cocycles₂_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩

/--
theorem `isMulCocycle₂_of_mem_cocycles₂` / 定理 `isMulCocycle₂_of_mem_cocycles₂`

English:
theorem isMulCocycle₂_of_mem_cocycles₂
  proof: (mem_cocycles₂_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

中文:
定理 isMulCocycle₂_of_mem_cocycles₂
  证明: (mem_cocycles₂_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

Depends on / 依赖: Rep.ofMulDistribMulAction, ofMulDistribMulAction
-/
theorem isMulCocycle₂_of_mem_cocycles₂
    (f : G × G -> M) (hf : f in cocycles₂ (Rep.ofMulDistribMulAction G M)) :
    IsMulCocycle₂ (Additive.toMul ∘ f) :=
  (mem_cocycles₂_iff (A := Rep.ofMulDistribMulAction G M) f).1 hf

/--
Definition of `coboundariesOfIsMulCoboundary₂` / `coboundariesOfIsMulCoboundary₂` 的定义

English:
definition coboundariesOfIsMulCoboundary₂
  signature: {f : G × G -> M} (hf : IsMulCoboundary₂ f)
  body: ⟨Additive.ofMul ∘ f, hf.choose, funext fun g => hf.choose_spec g.1 g.2⟩

中文:
定义 coboundariesOfIsMulCoboundary₂
  签名: {f : G × G -> M} (hf : IsMulCoboundary₂ f)
  定义体: ⟨Additive.ofMul ∘ f, hf.choose, funext fun g => hf.choose_spec g.1 g.2⟩

Depends on / 依赖: Additive, Additive.ofMul, choose_spec, hf.choose, hf.choose_spec
-/
def coboundariesOfIsMulCoboundary₂ {f : G × G -> M} (hf : IsMulCoboundary₂ f) :
    coboundaries₂ (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, hf.choose, funext fun g => hf.choose_spec g.1 g.2⟩

/--
theorem `isMulCoboundary₂_of_mem_coboundaries₂` / 定理 `isMulCoboundary₂_of_mem_coboundaries₂`

English:
theorem isMulCoboundary₂_of_mem_coboundaries₂
  proof: by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ _ => rfl⟩

中文:
定理 isMulCoboundary₂_of_mem_coboundaries₂
  证明: by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ _ => rfl⟩

Depends on / 依赖: Additive, Additive.toMul
-/
theorem isMulCoboundary₂_of_mem_coboundaries₂
    (f : G × G -> M) (hf : f in coboundaries₂ (Rep.ofMulDistribMulAction G M)) :
    IsMulCoboundary₂ (M := M) (Additive.toMul ∘ f) := by
  rcases hf with ⟨x, rfl⟩
  exact ⟨x, fun _ _ => rfl⟩

end ofMulDistribMulAction

open ShortComplex

section CocyclesIso

section cocyclesIso₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (shortComplexH0 A).f
  body: by
  rw [ModuleCat.mono_iff_injective]
  apply Submodule.injective_subtype

中文:
实例 :
  签名: 单态射 (shortComplexH0 A).f
  定义体: by
  rw [ModuleCat.mono_iff_injective]
  apply Submodule.injective_subtype

Depends on / 依赖: ModuleCat, ModuleCat.mono_iff_injective, Submodule, Submodule.injective_subtype, injective_subtype, mono_iff_injective
-/
instance : Mono (shortComplexH0 A).f := by
  rw [ModuleCat.mono_iff_injective]
  apply Submodule.injective_subtype

/--
lemma `shortComplexH0_exact` / 引理 `shortComplexH0_exact`

English:
lemma shortComplexH0_exact
  statement: (shortComplexH0 A).Exact
  proof: by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : d₀₁ _ x = 0)
  refine ⟨⟨x, fun g => ?_⟩, rfl⟩
  rw [← sub_eq_zero]
  exact congr_fun hx g

中文:
引理 shortComplexH0_exact
  结论: (shortComplexH0 A).正合
  证明: by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : d₀₁ _ x = 0)
  refine ⟨⟨x, fun g => ?_⟩, rfl⟩
  rw [← sub_eq_zero]
  exact congr_fun hx g

Depends on / 依赖: ShortComplex, ShortComplex.moduleCat_exact_iff, congr_fun, moduleCat_exact_iff, sub_eq_zero
-/
lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : d₀₁ _ x = 0)
  refine ⟨⟨x, fun g => ?_⟩, rfl⟩
  rw [← sub_eq_zero]
  exact congr_fun hx g

/-- The arrow `A --d₀₁--> Fun(G, A)` is isomorphic to the differential
`(inhomogeneousCochains A).d 0 1` of the complex of inhomogeneous cochains of `A`. -/
@[simps! hom_left hom_right inv_left inv_right]
/--
Definition of `dArrowIso₀₁` / `dArrowIso₀₁` 的定义

English:
definition dArrowIso₀₁
  signature: :
  body: Arrow.isoMk (cochainsIso₀ A) (cochainsIso₁ A) (comp_d₀₁_eq A)

中文:
定义 dArrowIso₀₁
  签名: :
  定义体: Arrow.isoMk (cochainsIso₀ A) (cochainsIso₁ A) (comp_d₀₁_eq A)

Depends on / 依赖: Arrow.isoMk
-/
def dArrowIso₀₁ :
    Arrow.mk ((inhomogeneousCochains A).d 0 1) ≅ Arrow.mk (d₀₁ A) :=
  Arrow.isoMk (cochainsIso₀ A) (cochainsIso₁ A) (comp_d₀₁_eq A)

/--
Definition of `cocyclesIso₀` / `cocyclesIso₀` 的定义

English:
definition cocyclesIso₀
  signature: : cocycles A 0 ≅ ModuleCat.of k A.ρ.invariants
  body: KernelFork.mapIsoOfIsLimit
    ((inhomogeneousCochains A).cyclesIsKernel 0 1 (by simp)) (shortComplexH0_exact A).fIsKernel
      (dArrowIso₀₁ A)

中文:
定义 cocyclesIso₀
  签名: : cocycles A 0 ≅ 模范畴.of k A.ρ.invariants
  定义体: KernelFork.mapIsoOfIsLimit
    ((inhomogeneousCochains A).cyclesIsKernel 0 1 (by simp)) (shortComplexH0_exact A).fIsKernel
      (dArrowIso₀₁ A)

Depends on / 依赖: KernelFork, KernelFork.mapIsoOfIsLimit, cyclesIsKernel, fIsKernel, inhomogeneousCochains, mapIsoOfIsLimit, shortComplexH0_exact
-/
def cocyclesIso₀ : cocycles A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  KernelFork.mapIsoOfIsLimit
    ((inhomogeneousCochains A).cyclesIsKernel 0 1 (by simp)) (shortComplexH0_exact A).fIsKernel
      (dArrowIso₀₁ A)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cocyclesIso₀_hom_comp_f` / 引理 `cocyclesIso₀_hom_comp_f`

English:
lemma cocyclesIso₀_hom_comp_f
  proof: by
  dsimp [cocyclesIso₀]
  apply KernelFork.mapOfIsLimit_ι

中文:
引理 cocyclesIso₀_hom_comp_f
  证明: by
  dsimp [cocyclesIso₀]
  apply KernelFork.mapOfIsLimit_ι

Depends on / 依赖: KernelFork, KernelFork.mapOfIsLimit_
-/
lemma cocyclesIso₀_hom_comp_f :
    (cocyclesIso₀ A).hom ≫ (shortComplexH0 A).f = iCocycles A 0 ≫ (cochainsIso₀ A).hom := by
  dsimp [cocyclesIso₀]
  apply KernelFork.mapOfIsLimit_ι

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cocyclesIso₀_inv_comp_iCocycles` / 引理 `cocyclesIso₀_inv_comp_iCocycles`

English:
lemma cocyclesIso₀_inv_comp_iCocycles
  proof: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [cocyclesIso₀_hom_comp_f]

中文:
引理 cocyclesIso₀_inv_comp_iCocycles
  证明: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [cocyclesIso₀_hom_comp_f]

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, Iso.inv_comp_eq, eq_comp_inv, inv_comp_eq
-/
lemma cocyclesIso₀_inv_comp_iCocycles :
    (cocyclesIso₀ A).inv ≫ iCocycles A 0 =
      (shortComplexH0 A).f ≫ (cochainsIso₀ A).inv := by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [cocyclesIso₀_hom_comp_f]

variable {A} in
/--
lemma `cocyclesMk₀_eq` / 引理 `cocyclesMk₀_eq`

English:
lemma cocyclesMk₀_eq
  given: (x : A.ρ.invariants)
  proof: (ModuleCat.mono_iff_injective <| iCocycles A 0).1 inferInstance by
    rw [iCocycles_mk]
    exact (cocyclesIso₀_inv_comp_iCocycles_apply A x).symm

中文:
引理 cocyclesMk₀_eq
  条件: (x : A.ρ.invariants)
  证明: (ModuleCat.mono_iff_injective <| iCocycles A 0).1 inferInstance by
    rw [iCocycles_mk]
    exact (cocyclesIso₀_inv_comp_iCocycles_apply A x).symm
-/
lemma cocyclesMk₀_eq (x : A.ρ.invariants) :
    cocyclesMk ((cochainsIso₀ A).inv x.1) (by ext g; simp [cochainsIso₀, x.2 (g 0),
      inhomogeneousCochains.d, Pi.zero_apply (M := fun _ => A)]) = (cocyclesIso₀ A).inv x :=
(ModuleCat.mono_iff_injective <| iCocycles A 0).1 inferInstance by
    rw [iCocycles_mk]
    exact (cocyclesIso₀_inv_comp_iCocycles_apply A x).symm

end cocyclesIso₀

section isoCocycles₁

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The short complex `A --d₀₁--> Fun(G, A) --d₁₂--> Fun(G × G, A)` is isomorphic to the 1st
short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom inv]
/--
Definition of `isoShortComplexH1` / `isoShortComplexH1` 的定义

English:
definition isoShortComplexH1
  signature: : (inhomogeneousCochains A).sc 1 ≅ shortComplexH1 A
  body: (inhomogeneousCochains A).isoSc' 0 1 2 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₀ A) (cochainsIso₁ A) (cochainsIso₂ A)
      (comp_d₀₁_eq A) (comp_d₁₂_eq A)

中文:
定义 isoShortComplexH1
  签名: : (inhomogeneousCochains A).sc 1 ≅ shortComplexH1 A
  定义体: (inhomogeneousCochains A).isoSc' 0 1 2 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₀ A) (cochainsIso₁ A) (cochainsIso₂ A)
      (comp_d₀₁_eq A) (comp_d₁₂_eq A)

Depends on / 依赖: inhomogeneousCochains
-/
def isoShortComplexH1 : (inhomogeneousCochains A).sc 1 ≅ shortComplexH1 A :=
  (inhomogeneousCochains A).isoSc' 0 1 2 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₀ A) (cochainsIso₁ A) (cochainsIso₂ A)
      (comp_d₀₁_eq A) (comp_d₁₂_eq A)

/--
Definition of `isoCocycles₁` / `isoCocycles₁` 的定义

English:
definition isoCocycles₁
  signature: : cocycles A 1 ≅ ModuleCat.of k (cocycles₁ A)
  body: cyclesMapIso' (isoShortComplexH1 A) _ (shortComplexH1 A).moduleCatLeftHomologyData

中文:
定义 isoCocycles₁
  签名: : cocycles A 1 ≅ 模范畴.of k (cocycles₁ A)
  定义体: cyclesMapIso' (isoShortComplexH1 A) _ (shortComplexH1 A).moduleCatLeftHomologyData

Depends on / 依赖: cyclesMapIso, isoShortComplexH1, moduleCatLeftHomologyData, shortComplexH1
-/
def isoCocycles₁ : cocycles A 1 ≅ ModuleCat.of k (cocycles₁ A) :=
  cyclesMapIso' (isoShortComplexH1 A) _ (shortComplexH1 A).moduleCatLeftHomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `isoCocycles₁_hom_comp_i` / 引理 `isoCocycles₁_hom_comp_i`

English:
lemma isoCocycles₁_hom_comp_i
  proof: by
  simp [isoCocycles₁, iCocycles, HomologicalComplex.iCycles, iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 isoCocycles₁_hom_comp_i
  证明: by
  simp [isoCocycles₁, iCocycles, HomologicalComplex.iCycles, iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.iCycles, iCocycles, iCycles
-/
lemma isoCocycles₁_hom_comp_i :
    (isoCocycles₁ A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.i =
      iCocycles A 1 ≫ (cochainsIso₁ A).hom := by
  simp [isoCocycles₁, iCocycles, HomologicalComplex.iCycles, iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `isoCocycles₁_inv_comp_iCocycles` / 引理 `isoCocycles₁_inv_comp_iCocycles`

English:
lemma isoCocycles₁_inv_comp_iCocycles
  proof: (CommSq.horiz_inv ⟨isoCocycles₁_hom_comp_i A⟩).w

中文:
引理 isoCocycles₁_inv_comp_iCocycles
  证明: (CommSq.horiz_inv ⟨isoCocycles₁_hom_comp_i A⟩).w

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
lemma isoCocycles₁_inv_comp_iCocycles :
    (isoCocycles₁ A).inv ≫ iCocycles A 1 =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ (cochainsIso₁ A).inv :=
  (CommSq.horiz_inv ⟨isoCocycles₁_hom_comp_i A⟩).w

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `toCocycles_comp_isoCocycles₁_hom` / 引理 `toCocycles_comp_isoCocycles₁_hom`

English:
lemma toCocycles_comp_isoCocycles₁_hom
  proof: by
  simp [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, comp_d₀₁_eq,
    shortComplexH1_f]

中文:
引理 toCocycles_comp_isoCocycles₁_hom
  证明: by
  simp [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, comp_d₀₁_eq,
    shortComplexH1_f]

Depends on / 依赖: cancel_mono, moduleCatLeftHomologyData, moduleCatLeftHomologyData.i, shortComplexH1, shortComplexH1_f
-/
lemma toCocycles_comp_isoCocycles₁_hom :
    toCocycles A 0 1 ≫ (isoCocycles₁ A).hom =
      (cochainsIso₀ A).hom ≫ (shortComplexH1 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH1 A).moduleCatLeftHomologyData.i, comp_d₀₁_eq,
    shortComplexH1_f]

/--
lemma `cocyclesMk₁_eq` / 引理 `cocyclesMk₁_eq`

English:
lemma cocyclesMk₁_eq
  given: (x : cocycles₁ A)
  proof: by
  apply_fun (forget₂ _ Ab).map ((inhomogeneousCochains A).iCycles 1) using
(AddCommGrpCat.mono_iff_injective _).1 (forget₂ _ _).map_mono _
  have := (isoCocycles₁_inv_comp_iCocycles_apply _ x).symm
  rw [HomologicalComplex.i_cyclesMk]
  simp only [ModuleCat.forget₂_obj, ModuleCat.forget₂_map, ConcreteCategory.hom_ofHom,
    AddMonoidHom.coe_coe]
  rw [← this]
  rfl

中文:
引理 cocyclesMk₁_eq
  条件: (x : cocycles₁ A)
  证明: by
  apply_fun (forget₂ _ Ab).map ((inhomogeneousCochains A).iCycles 1) using
(AddCommGrpCat.mono_iff_injective _).1 (forget₂ _ _).map_mono _
  have := (isoCocycles₁_inv_comp_iCocycles_apply _ x).symm
  rw [HomologicalComplex.i_cyclesMk]
  simp only [ModuleCat.forget₂_obj, ModuleCat.forget₂_map, ConcreteCategory.hom_ofHom,
    AddMonoidHom.coe_coe]
  rw [← this]
  rfl

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.mono_iff_injective, AddMonoidHom, AddMonoidHom.coe_coe, ConcreteCategory, ConcreteCategory.hom_ofHom, HomologicalComplex, HomologicalComplex.i_cyclesMk, ModuleCat, ModuleCat.forget, apply_fun, coe_coe, hom_ofHom, iCycles, i_cyclesMk, inhomogeneousCochains, map_mono, mono_iff_injective
-/
lemma cocyclesMk₁_eq (x : cocycles₁ A) :
    cocyclesMk ((cochainsIso₁ A).inv x) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [← inhomogeneousCochains.d_def]; rw [eq_d₁₂_comp_inv]; rw [ModuleCat.hom_comp]; rw [LinearMap.comp_apply]; rw [cocycles₁.d₁₂_apply x]; rw [map_zero]) = (isoCocycles₁ A).inv x := by
  apply_fun (forget₂ _ Ab).map ((inhomogeneousCochains A).iCycles 1) using
(AddCommGrpCat.mono_iff_injective _).1 (forget₂ _ _).map_mono _
  have := (isoCocycles₁_inv_comp_iCocycles_apply _ x).symm
  rw [HomologicalComplex.i_cyclesMk]
  simp only [ModuleCat.forget₂_obj, ModuleCat.forget₂_map, ConcreteCategory.hom_ofHom,
    AddMonoidHom.coe_coe]
  rw [← this]
  rfl

end isoCocycles₁

section isoCocycles₂

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The short complex `Fun(G, A) --d₁₂--> Fun(G × G, A) --dTwo--> Fun(G × G × G, A)` is
isomorphic to the 2nd short complex associated to the complex of inhomogeneous cochains of `A`. -/
@[simps! hom inv]
/--
Definition of `isoShortComplexH2` / `isoShortComplexH2` 的定义

English:
definition isoShortComplexH2
  signature: :
  body: (inhomogeneousCochains A).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₁ A) (cochainsIso₂ A) (cochainsIso₃ A)
      (comp_d₁₂_eq A) (comp_d₂₃_eq A)

中文:
定义 isoShortComplexH2
  签名: :
  定义体: (inhomogeneousCochains A).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₁ A) (cochainsIso₂ A) (cochainsIso₃ A)
      (comp_d₁₂_eq A) (comp_d₂₃_eq A)

Depends on / 依赖: inhomogeneousCochains
-/
def isoShortComplexH2 :
    (inhomogeneousCochains A).sc 2 ≅ shortComplexH2 A :=
  (inhomogeneousCochains A).isoSc' 1 2 3 (by simp) (by simp) ≪≫
    isoMk (cochainsIso₁ A) (cochainsIso₂ A) (cochainsIso₃ A)
      (comp_d₁₂_eq A) (comp_d₂₃_eq A)

/--
Definition of `isoCocycles₂` / `isoCocycles₂` 的定义

English:
definition isoCocycles₂
  signature: : cocycles A 2 ≅ ModuleCat.of k (cocycles₂ A)
  body: cyclesMapIso' (isoShortComplexH2 A) _ (shortComplexH2 A).moduleCatLeftHomologyData

中文:
定义 isoCocycles₂
  签名: : cocycles A 2 ≅ 模范畴.of k (cocycles₂ A)
  定义体: cyclesMapIso' (isoShortComplexH2 A) _ (shortComplexH2 A).moduleCatLeftHomologyData

Depends on / 依赖: cyclesMapIso, isoShortComplexH2, moduleCatLeftHomologyData, shortComplexH2
-/
def isoCocycles₂ : cocycles A 2 ≅ ModuleCat.of k (cocycles₂ A) :=
  cyclesMapIso' (isoShortComplexH2 A) _ (shortComplexH2 A).moduleCatLeftHomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `isoCocycles₂_hom_comp_i` / 引理 `isoCocycles₂_hom_comp_i`

English:
lemma isoCocycles₂_hom_comp_i
  proof: by
  simp [isoCocycles₂, iCocycles, HomologicalComplex.iCycles, iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 isoCocycles₂_hom_comp_i
  证明: by
  simp [isoCocycles₂, iCocycles, HomologicalComplex.iCycles, iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.iCycles, iCocycles, iCycles
-/
lemma isoCocycles₂_hom_comp_i :
    (isoCocycles₂ A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.i =
      iCocycles A 2 ≫ (cochainsIso₂ A).hom := by
  simp [isoCocycles₂, iCocycles, HomologicalComplex.iCycles, iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `isoCocycles₂_inv_comp_iCocycles` / 引理 `isoCocycles₂_inv_comp_iCocycles`

English:
lemma isoCocycles₂_inv_comp_iCocycles
  proof: (CommSq.horiz_inv ⟨isoCocycles₂_hom_comp_i A⟩).w

中文:
引理 isoCocycles₂_inv_comp_iCocycles
  证明: (CommSq.horiz_inv ⟨isoCocycles₂_hom_comp_i A⟩).w

Depends on / 依赖: CommSq, CommSq.horiz_inv, horiz_inv
-/
lemma isoCocycles₂_inv_comp_iCocycles :
    (isoCocycles₂ A).inv ≫ iCocycles A 2 =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ (cochainsIso₂ A).inv :=
  (CommSq.horiz_inv ⟨isoCocycles₂_hom_comp_i A⟩).w

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `toCocycles_comp_isoCocycles₂_hom` / 引理 `toCocycles_comp_isoCocycles₂_hom`

English:
lemma toCocycles_comp_isoCocycles₂_hom
  proof: by
  simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, comp_d₁₂_eq,
    shortComplexH2_f]

中文:
引理 toCocycles_comp_isoCocycles₂_hom
  证明: by
  simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, comp_d₁₂_eq,
    shortComplexH2_f]

Depends on / 依赖: cancel_mono, moduleCatLeftHomologyData, moduleCatLeftHomologyData.i, shortComplexH2, shortComplexH2_f
-/
lemma toCocycles_comp_isoCocycles₂_hom :
    toCocycles A 1 2 ≫ (isoCocycles₂ A).hom =
      (cochainsIso₁ A).hom ≫ (shortComplexH2 A).moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono (shortComplexH2 A).moduleCatLeftHomologyData.i, comp_d₁₂_eq,
    shortComplexH2_f]

/--
lemma `cocyclesMk₂_eq` / 引理 `cocyclesMk₂_eq`

English:
lemma cocyclesMk₂_eq
  given: (x : cocycles₂ A)
  proof: by
  apply_fun (forget₂ _ Ab).map ((inhomogeneousCochains A).iCycles 2) using
(AddCommGrpCat.mono_iff_injective _).1 (forget₂ _ _).map_mono _
  rw [HomologicalComplex.i_cyclesMk]
  simp; rfl

中文:
引理 cocyclesMk₂_eq
  条件: (x : cocycles₂ A)
  证明: by
  apply_fun (forget₂ _ Ab).map ((inhomogeneousCochains A).iCycles 2) using
(AddCommGrpCat.mono_iff_injective _).1 (forget₂ _ _).map_mono _
  rw [HomologicalComplex.i_cyclesMk]
  simp; rfl

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.mono_iff_injective, HomologicalComplex, HomologicalComplex.i_cyclesMk, apply_fun, iCycles, i_cyclesMk, inhomogeneousCochains, map_mono, mono_iff_injective
-/
lemma cocyclesMk₂_eq (x : cocycles₂ A) :
    cocyclesMk ((cochainsIso₂ A).inv x) (by
      rw [← LinearMap.comp_apply]; rw [← ModuleCat.hom_comp]; rw [← inhomogeneousCochains.d_def]; rw [eq_d₂₃_comp_inv]; rw [ModuleCat.hom_comp]; rw [LinearMap.comp_apply]; rw [cocycles₂.d₂₃_apply x]; rw [map_zero]) = (isoCocycles₂ A).inv x := by
  apply_fun (forget₂ _ Ab).map ((inhomogeneousCochains A).iCycles 2) using
(AddCommGrpCat.mono_iff_injective _).1 (forget₂ _ _).map_mono _
  rw [HomologicalComplex.i_cyclesMk]
  simp; rfl

end isoCocycles₂
end CocyclesIso

section Cohomology

section H0

/--
Definition of `H0` / `H0` 的定义

English:
abbreviation H0
  body: groupCohomology A 0

中文:
缩写 H0
  定义体: groupCohomology A 0

Depends on / 依赖: groupCohomology
-/
abbrev H0 := groupCohomology A 0

/--
Definition of `H0Iso` / `H0Iso` 的定义

English:
definition H0Iso
  signature: : H0 A ≅ ModuleCat.of k A.ρ.invariants
  body: (CochainComplex.isoHomologyπ₀ _).symm ≪≫ cocyclesIso₀ A

中文:
定义 H0Iso
  签名: : H0 A ≅ 模范畴.of k A.ρ.invariants
  定义体: (CochainComplex.isoHomologyπ₀ _).symm ≪≫ cocyclesIso₀ A

Depends on / 依赖: CochainComplex, CochainComplex.isoHomology
-/
def H0Iso : H0 A ≅ ModuleCat.of k A.ρ.invariants :=
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫ cocyclesIso₀ A

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `π_comp_H0Iso_hom` / 引理 `π_comp_H0Iso_hom`

English:
lemma π_comp_H0Iso_hom
  proof: by
  simp [H0Iso]

@[elab_as_elim]

中文:
引理 π_comp_H0Iso_hom
  证明: by
  simp [H0Iso]

@[elab_as_elim]
-/
lemma π_comp_H0Iso_hom :
    π A 0 ≫ (H0Iso A).hom = (cocyclesIso₀ A).hom := by
  simp [H0Iso]

@[elab_as_elim]
/--
theorem `H0_induction_on` / 定理 `H0_induction_on`

English:
theorem H0_induction_on
  statement: {C : H0 A -> Prop} (x : H0 A)
  proof: by
  simpa using h ((H0Iso A).hom x)

中文:
定理 H0_induction_on
  结论: {C : H0 A -> 命题} (x : H0 A)
  证明: by
  simpa using h ((H0Iso A).hom x)
-/
theorem H0_induction_on {C : H0 A -> Prop} (x : H0 A)
    (h : forall x : A.ρ.invariants, C ((H0Iso A).inv x)) : C x := by
  simpa using h ((H0Iso A).hom x)

section IsTrivial

variable [A.IsTrivial]

/--
Definition of `H0IsoOfIsTrivial` / `H0IsoOfIsTrivial` 的定义

English:
definition H0IsoOfIsTrivial
  signature: :
  body: H0Iso A ≪≫ (LinearEquiv.ofTop _ (invariants_eq_top A.ρ)).toModuleIso

@[simp]

中文:
定义 H0IsoOfIsTrivial
  签名: :
  定义体: H0Iso A ≪≫ (LinearEquiv.ofTop _ (invariants_eq_top A.ρ)).toModuleIso

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofTop, invariants_eq_top, toModuleIso
-/
def H0IsoOfIsTrivial :
    H0 A ≅ ModuleCat.of k A.V :=
    H0Iso A ≪≫ (LinearEquiv.ofTop _ (invariants_eq_top A.ρ)).toModuleIso

@[simp]
/--
theorem `H0IsoOfIsTrivial_hom` / 定理 `H0IsoOfIsTrivial_hom`

English:
theorem H0IsoOfIsTrivial_hom
  proof: rfl

中文:
定理 H0IsoOfIsTrivial_hom
  证明: rfl
-/
theorem H0IsoOfIsTrivial_hom :
    (H0IsoOfIsTrivial A).hom = (H0Iso A).hom ≫ (shortComplexH0 A).f := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/--
theorem `π_comp_H0IsoOfIsTrivial_hom` / 定理 `π_comp_H0IsoOfIsTrivial_hom`

English:
theorem π_comp_H0IsoOfIsTrivial_hom
  proof: by
  simp

中文:
定理 π_comp_H0IsoOfIsTrivial_hom
  证明: by
  simp
-/
theorem π_comp_H0IsoOfIsTrivial_hom :
    π A 0 ≫ (H0IsoOfIsTrivial A).hom = iCocycles A 0 ≫ (cochainsIso₀ A).hom := by
  simp

variable {A} in
@[simp]
/--
theorem `H0IsoOfIsTrivial_inv_apply` / 定理 `H0IsoOfIsTrivial_inv_apply`

English:
theorem H0IsoOfIsTrivial_inv_apply
  given: (x : A)
  proof: rfl

中文:
定理 H0IsoOfIsTrivial_inv_apply
  条件: (x : A)
  证明: rfl
-/
theorem H0IsoOfIsTrivial_inv_apply (x : A) :
    (H0IsoOfIsTrivial A).inv x = (H0Iso A).inv ⟨x, by simp⟩ := rfl

end IsTrivial
end H0
section H1

/--
Definition of `H1` / `H1` 的定义

English:
abbreviation H1
  body: groupCohomology A 1

中文:
缩写 H1
  定义体: groupCohomology A 1

Depends on / 依赖: groupCohomology
-/
abbrev H1 := groupCohomology A 1

/--
Definition of `H1π` / `H1π` 的定义

English:
definition H1π
  signature: : ModuleCat.of k (cocycles₁ A) ⟶ H1 A
  body: (isoCocycles₁ A).inv ≫ π A 1

中文:
定义 H1π
  签名: : 模范畴.of k (cocycles₁ A) ⟶ H1 A
  定义体: (isoCocycles₁ A).inv ≫ π A 1
-/
def H1π : ModuleCat.of k (cocycles₁ A) ⟶ H1 A :=
  (isoCocycles₁ A).inv ≫ π A 1

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
  given: (x : cocycles₁ A)
  statement: H1π A x = 0 ↔ ⇑x in coboundaries₁ A
  proof: by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH1 A).inv
    (shortComplexH1 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 1).leftHomologyIso.hom
  simp only [H1π, isoCocycles₁, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₁, shortComplexH1, cocycles₁]

中文:
引理 H1π_eq_zero_iff
  条件: (x : cocycles₁ A)
  结论: H1π A x = 0 ↔ ⇑x in coboundaries₁ A
  证明: by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH1 A).inv
    (shortComplexH1 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 1).leftHomologyIso.hom
  simp only [H1π, isoCocycles₁, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₁, shortComplexH1, cocycles₁]

Depends on / 依赖: Function, Function.comp_apply, HomologicalComplex, HomologicalComplex.homology, LinearMap, LinearMap.coe_comp, LinearMap.range_codRestrict, ModuleCat, ModuleCat.hom_comp, ModuleCat.mono_iff_injective, _assoc, _inv, coe_comp, comp_apply, cyclesMapIso, hom_comp, inhomogeneousCochains, isoShortComplexH1, leftHomologyData, leftHomologyIso
-/
lemma H1π_eq_zero_iff (x : cocycles₁ A) : H1π A x = 0 ↔ ⇑x in coboundaries₁ A := by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH1 A).inv
    (shortComplexH1 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 1).leftHomologyIso.hom
  simp only [H1π, isoCocycles₁, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₁, shortComplexH1, cocycles₁]

/--
lemma `H1π_eq_iff` / 引理 `H1π_eq_iff`

English:
lemma H1π_eq_iff
  given: (x y : cocycles₁ A)
  proof: by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H1π_eq_zero_iff]
  rfl

@[elab_as_elim]

中文:
引理 H1π_eq_iff
  条件: (x y : cocycles₁ A)
  证明: by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H1π_eq_zero_iff]
  rfl

@[elab_as_elim]

Depends on / 依赖: map_sub, sub_eq_zero
-/
lemma H1π_eq_iff (x y : cocycles₁ A) :
    H1π A x = H1π A y ↔ ⇑x - ⇑y in coboundaries₁ A := by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H1π_eq_zero_iff]
  rfl

@[elab_as_elim]
/--
theorem `H1_induction_on` / 定理 `H1_induction_on`

English:
theorem H1_induction_on
  given: {C : H1 A -> Prop} (x : H1 A) (h : forall x : cocycles₁ A, C (H1π A x))
  proof: groupCohomology_induction_on x fun y => by simpa [H1π] using h ((isoCocycles₁ A).hom y)

中文:
定理 H1_induction_on
  条件: {C : H1 A -> 命题} (x : H1 A) (h : 对任意 x : cocycles₁ A, C (H1π A x))
  证明: groupCohomology_induction_on x fun y => by simpa [H1π] using h ((isoCocycles₁ A).hom y)

Depends on / 依赖: groupCohomology_induction_on
-/
theorem H1_induction_on {C : H1 A -> Prop} (x : H1 A) (h : forall x : cocycles₁ A, C (H1π A x)) :
    C x :=
  groupCohomology_induction_on x fun y => by simpa [H1π] using h ((isoCocycles₁ A).hom y)

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

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `π_comp_H1Iso_hom` / 引理 `π_comp_H1Iso_hom`

English:
lemma π_comp_H1Iso_hom
  proof: by
  simp [H1Iso, isoCocycles₁, π, HomologicalComplex.homologyπ, leftHomologyπ]

中文:
引理 π_comp_H1Iso_hom
  证明: by
  simp [H1Iso, isoCocycles₁, π, HomologicalComplex.homologyπ, leftHomologyπ]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homology
-/
lemma π_comp_H1Iso_hom :
    π A 1 ≫ (H1Iso A).hom = (isoCocycles₁ A).hom ≫
      (shortComplexH1 A).moduleCatLeftHomologyData.π := by
  simp [H1Iso, isoCocycles₁, π, HomologicalComplex.homologyπ, leftHomologyπ]

section IsTrivial

variable [A.IsTrivial]

/--
Definition of `H1IsoOfIsTrivial` / `H1IsoOfIsTrivial` 的定义

English:
definition H1IsoOfIsTrivial
  signature: :
  body: (HomologicalComplex.isoHomologyπ _ 0 1 (CochainComplex.prev_nat_succ 0) <| by
    ext; simp [inhomogeneousCochains.d, Unique.eq_default (α := Fin 0 -> G),
      CochainComplex.of.d]).symm ≪≫
  isoCocycles₁ A ≪≫ cocycles₁IsoOfIsTrivial A

中文:
定义 H1IsoOfIsTrivial
  签名: :
  定义体: (HomologicalComplex.isoHomologyπ _ 0 1 (CochainComplex.prev_nat_succ 0) <| by
    ext; simp [inhomogeneousCochains.d, Unique.eq_default (α := Fin 0 -> G),
      CochainComplex.of.d]).symm ≪≫
  isoCocycles₁ A ≪≫ cocycles₁IsoOfIsTrivial A

Depends on / 依赖: CochainComplex, CochainComplex.of.d, CochainComplex.prev_nat_succ, HomologicalComplex, HomologicalComplex.isoHomology, Unique, Unique.eq_default, eq_default, inhomogeneousCochains, inhomogeneousCochains.d, prev_nat_succ
-/
def H1IsoOfIsTrivial :
    H1 A ≅ ModuleCat.of k (Additive G ->+ A) :=
  (HomologicalComplex.isoHomologyπ _ 0 1 (CochainComplex.prev_nat_succ 0) <| by
    ext; simp [inhomogeneousCochains.d, Unique.eq_default (α := Fin 0 -> G),
      CochainComplex.of.d]).symm ≪≫
  isoCocycles₁ A ≪≫ cocycles₁IsoOfIsTrivial A

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `H1π_comp_H1IsoOfIsTrivial_hom` / 定理 `H1π_comp_H1IsoOfIsTrivial_hom`

English:
theorem H1π_comp_H1IsoOfIsTrivial_hom
  proof: by
  simp [H1IsoOfIsTrivial, H1π]

中文:
定理 H1π_comp_H1IsoOfIsTrivial_hom
  证明: by
  simp [H1IsoOfIsTrivial, H1π]

Depends on / 依赖: H1IsoOfIsTrivial
-/
theorem H1π_comp_H1IsoOfIsTrivial_hom :
    H1π A ≫ (H1IsoOfIsTrivial A).hom = (cocycles₁IsoOfIsTrivial A).hom := by
  simp [H1IsoOfIsTrivial, H1π]

variable {A}

/--
theorem `H1IsoOfIsTrivial_H1π_apply_apply` / 定理 `H1IsoOfIsTrivial_H1π_apply_apply`

English:
theorem H1IsoOfIsTrivial_H1π_apply_apply
  proof: by simp

中文:
定理 H1IsoOfIsTrivial_H1π_apply_apply
  证明: by simp
-/
theorem H1IsoOfIsTrivial_H1π_apply_apply
    (f : cocycles₁ A) (x : Additive G) :
    (H1IsoOfIsTrivial A).hom (H1π A f) x = f x.toMul := by simp

/--
theorem `H1IsoOfIsTrivial_inv_apply` / 定理 `H1IsoOfIsTrivial_inv_apply`

English:
theorem H1IsoOfIsTrivial_inv_apply
  given: (f : Additive G ->+ A)
  proof: rfl

中文:
定理 H1IsoOfIsTrivial_inv_apply
  条件: (f : 加性 G ->+ A)
  证明: rfl
-/
theorem H1IsoOfIsTrivial_inv_apply (f : Additive G ->+ A) :
    (H1IsoOfIsTrivial A).inv f = H1π A ((cocycles₁IsoOfIsTrivial A).inv f) := rfl

end IsTrivial
end H1
section H2

/--
Definition of `H2` / `H2` 的定义

English:
abbreviation H2
  body: groupCohomology A 2

中文:
缩写 H2
  定义体: groupCohomology A 2

Depends on / 依赖: groupCohomology
-/
abbrev H2 := groupCohomology A 2

/--
Definition of `H2π` / `H2π` 的定义

English:
definition H2π
  signature: : ModuleCat.of k (cocycles₂ A) ⟶ H2 A
  body: (isoCocycles₂ A).inv ≫ π A 2

中文:
定义 H2π
  签名: : 模范畴.of k (cocycles₂ A) ⟶ H2 A
  定义体: (isoCocycles₂ A).inv ≫ π A 2
-/
def H2π : ModuleCat.of k (cocycles₂ A) ⟶ H2 A :=
  (isoCocycles₂ A).inv ≫ π A 2

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
  given: (x : cocycles₂ A)
  statement: H2π A x = 0 ↔ ⇑x in coboundaries₂ A
  proof: by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH2 A).inv
    (shortComplexH2 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 2).leftHomologyIso.hom
  simp only [H2π, isoCocycles₂, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₂, shortComplexH2, cocycles₂]

中文:
引理 H2π_eq_zero_iff
  条件: (x : cocycles₂ A)
  结论: H2π A x = 0 ↔ ⇑x in coboundaries₂ A
  证明: by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH2 A).inv
    (shortComplexH2 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 2).leftHomologyIso.hom
  simp only [H2π, isoCocycles₂, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₂, shortComplexH2, cocycles₂]

Depends on / 依赖: Function, Function.comp_apply, HomologicalComplex, HomologicalComplex.homology, LinearMap, LinearMap.coe_comp, LinearMap.range_codRestrict, ModuleCat, ModuleCat.hom_comp, ModuleCat.mono_iff_injective, _assoc, _inv, coe_comp, comp_apply, cyclesMapIso, hom_comp, inhomogeneousCochains, isoShortComplexH2, leftHomologyData, leftHomologyIso
-/
lemma H2π_eq_zero_iff (x : cocycles₂ A) : H2π A x = 0 ↔ ⇑x in coboundaries₂ A := by
  have h := leftHomologyπ_naturality'_assoc (isoShortComplexH2 A).inv
    (shortComplexH2 A).moduleCatLeftHomologyData (leftHomologyData _)
    ((inhomogeneousCochains A).sc 2).leftHomologyIso.hom
  simp only [H2π, isoCocycles₂, π, HomologicalComplex.homologyπ, homologyπ,
    cyclesMapIso'_inv, leftHomologyπ, ← h, ← leftHomologyMapIso'_inv, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, map_eq_zero_iff _
    ((ModuleCat.mono_iff_injective <| _).1 inferInstance)]
  simp [LinearMap.range_codRestrict, coboundaries₂, shortComplexH2, cocycles₂]

/--
lemma `H2π_eq_iff` / 引理 `H2π_eq_iff`

English:
lemma H2π_eq_iff
  given: (x y : cocycles₂ A)
  proof: by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H2π_eq_zero_iff]
  rfl

@[elab_as_elim]

中文:
引理 H2π_eq_iff
  条件: (x y : cocycles₂ A)
  证明: by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H2π_eq_zero_iff]
  rfl

@[elab_as_elim]

Depends on / 依赖: map_sub, sub_eq_zero
-/
lemma H2π_eq_iff (x y : cocycles₂ A) :
    H2π A x = H2π A y ↔ ⇑x - ⇑y in coboundaries₂ A := by
  rw [← sub_eq_zero]; rw [← map_sub]; rw [H2π_eq_zero_iff]
  rfl

@[elab_as_elim]
/--
theorem `H2_induction_on` / 定理 `H2_induction_on`

English:
theorem H2_induction_on
  given: {C : H2 A -> Prop} (x : H2 A) (h : forall x : cocycles₂ A, C (H2π A x))
  proof: groupCohomology_induction_on x fun y => by simpa [H2π] using h ((isoCocycles₂ A).hom y)

中文:
定理 H2_induction_on
  条件: {C : H2 A -> 命题} (x : H2 A) (h : 对任意 x : cocycles₂ A, C (H2π A x))
  证明: groupCohomology_induction_on x fun y => by simpa [H2π] using h ((isoCocycles₂ A).hom y)

Depends on / 依赖: V.integer_valuation, groupCohomology_induction_on, infer_instance, integer_valuation
-/
theorem H2_induction_on {C : H2 A -> Prop} (x : H2 A) (h : forall x : cocycles₂ A, C (H2π A x)) :
    C x :=
  groupCohomology_induction_on x fun y => by simpa [H2π] using h ((isoCocycles₂ A).hom y)

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

Depends on / 依赖: IsIntegrallyClosed, V.toSubring, isoShortComplexH2, leftHomologyIso, leftHomologyMapIso, toSubring
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
  simp [H2Iso, isoCocycles₂, π, HomologicalComplex.homologyπ, leftHomologyπ]

中文:
引理 π_comp_H2Iso_hom
  证明: by
  simp [H2Iso, isoCocycles₂, π, HomologicalComplex.homologyπ, leftHomologyπ]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homology
-/
lemma π_comp_H2Iso_hom :
    π A 2 ≫ (H2Iso A).hom = (isoCocycles₂ A).hom ≫
      (shortComplexH2 A).moduleCatLeftHomologyData.π := by
  simp [H2Iso, isoCocycles₂, π, HomologicalComplex.homologyπ, leftHomologyπ]

end H2
end Cohomology
end groupCohomology
