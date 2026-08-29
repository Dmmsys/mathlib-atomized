/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
/-!
# Constructions of new partial homeomorphisms from old

## Main definitions

* `OpenPartialHomeomorph.const`: an open partial homeomorphism which is a constant map,
  whose source and target are necessarily singleton sets
* `OpenPartialHomeomorph.subtypeRestr`: restriction to a subtype
* `OpenPartialHomeomorph.prod`: the product of two open partial homeomorphisms,
  as an open partial homeomorphism on the product space
* `OpenPartialHomeomorph.pi`: the product of a finite family of open partial homeomorphisms
* `OpenPartialHomeomorph.disjointUnion`: combine two open partial homeomorphisms with disjoint
  sources and disjoint targets
* `OpenPartialHomeomorph.lift_openEmbedding`: extend an open partial homeomorphism `X → Y`
  under an open embedding `X → X'`, to an open partial homeomorphism `X' → Z`.
  (This is used to define the disjoint union of charted spaces.)
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-!
## Constants

`PartialEquiv.const` as an open partial homeomorphism
-/
section const

variable {a : X} {b : Y}

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (ha : IsOpen {a}) (hb : IsOpen {b})
  body: PartialEquiv.single a b
  open_source := ha
  open_target := hb
  continuousOn_toFun := by simp
  continuousOn_invFun := by simp

@[simp, mfld_simps]

中文:
定义 const
  签名: (ha : 是开集 {a}) (hb : 是开集 {b})
  定义体: PartialEquiv.single a b
  open_source := ha
  open_target := hb
  continuousOn_toFun := by simp
  continuousOn_invFun := by simp

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.single, single
-/
def const (ha : IsOpen {a}) (hb : IsOpen {b}) : OpenPartialHomeomorph X Y where
  toPartialEquiv := PartialEquiv.single a b
  open_source := ha
  open_target := hb
  continuousOn_toFun := by simp
  continuousOn_invFun := by simp

@[simp, mfld_simps]
/--
lemma `const_apply` / 引理 `const_apply`

English:
lemma const_apply
  given: (ha : IsOpen {a}) (hb : IsOpen {b}) (x : X)
  statement: (const ha hb) x = b
  proof: rfl

@[simp, mfld_simps]

中文:
引理 const_apply
  条件: (ha : 是开集 {a}) (hb : 是开集 {b}) (x : X)
  结论: (const ha hb) x = b
  证明: rfl

@[simp, mfld_simps]
-/
lemma const_apply (ha : IsOpen {a}) (hb : IsOpen {b}) (x : X) : (const ha hb) x = b := rfl

@[simp, mfld_simps]
/--
lemma `const_source` / 引理 `const_source`

English:
lemma const_source
  given: (ha : IsOpen {a}) (hb : IsOpen {b})
  statement: (const ha hb).source = {a}
  proof: rfl

@[simp, mfld_simps]

中文:
引理 const_source
  条件: (ha : 是开集 {a}) (hb : 是开集 {b})
  结论: (const ha hb).source = {a}
  证明: rfl

@[simp, mfld_simps]
-/
lemma const_source (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).source = {a} := rfl

@[simp, mfld_simps]
/--
lemma `const_target` / 引理 `const_target`

English:
lemma const_target
  given: (ha : IsOpen {a}) (hb : IsOpen {b})
  statement: (const ha hb).target = {b}
  proof: rfl

中文:
引理 const_target
  条件: (ha : 是开集 {a}) (hb : 是开集 {b})
  结论: (const ha hb).target = {b}
  证明: rfl
-/
lemma const_target (ha : IsOpen {a}) (hb : IsOpen {b}) : (const ha hb).target = {b} := rfl

end const

/-!
## Products

Product of two open partial homeomorphisms
-/
section Prod

/-- The product of two open partial homeomorphisms, as an open partial homeomorphism on the product
space. -/
@[simps! (attr := mfld_simps) -fullyApplied toPartialHomeomorph apply,
  simps! -isSimp source target symm_apply]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y')
  body: eX.open_source.prod eY.open_source
  open_target := eX.open_target.prod eY.open_target
  continuousOn_toFun := eX.continuousOn.prodMap eY.continuousOn
  continuousOn_invFun := eX.continuousOn_symm.prodMap eY.continuousOn_symm
  toPartialEquiv := eX.toPartialEquiv.prod eY.toPartialEquiv

@[deprecated

中文:
定义 乘积
  签名: (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y')
  定义体: eX.open_source.prod eY.open_source
  open_target := eX.open_target.prod eY.open_target
  continuousOn_toFun := eX.continuousOn.prodMap eY.continuousOn
  continuousOn_invFun := eX.continuousOn_symm.prodMap eY.continuousOn_symm
  toPartialEquiv := eX.toPartialEquiv.prod eY.toPartialEquiv

@[deprecated

Depends on / 依赖: eX.open_source.prod, eY.open_source, open_source
-/
def prod (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
    OpenPartialHomeomorph (X × Y) (X' × Y') where
  open_source := eX.open_source.prod eY.open_source
  open_target := eX.open_target.prod eY.open_target
  continuousOn_toFun := eX.continuousOn.prodMap eY.continuousOn
  continuousOn_invFun := eX.continuousOn_symm.prodMap eY.continuousOn_symm
  toPartialEquiv := eX.toPartialEquiv.prod eY.toPartialEquiv

@[deprecated "deprecated in favour of `OpenPartialHomeomorph.prod_toPartialHomeomorph`"
  (since := "2026-06-24")]
/--
lemma `prod_toPartialEquiv` / 引理 `prod_toPartialEquiv`

English:
lemma prod_toPartialEquiv
  given: (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y')
  proof: rfl
@[simp, mfld_simps]

中文:
引理 prod_toPartialEquiv
  条件: (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y')
  证明: rfl
@[simp, mfld_simps]

Depends on / 依赖: mfld_simps
-/
lemma prod_toPartialEquiv (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
    (eX.prod eY).toPartialHomeomorph.toPartialEquiv = eX.toPartialEquiv.prod eY.toPartialEquiv :=
  rfl
@[simp, mfld_simps]
/--
theorem `prod_symm` / 定理 `prod_symm`

English:
theorem prod_symm
  given: (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y')
  proof: rfl

@[simp]

中文:
定理 prod_symm
  条件: (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y')
  证明: rfl

@[simp]
-/
theorem prod_symm (eX : OpenPartialHomeomorph X X') (eY : OpenPartialHomeomorph Y Y') :
    (eX.prod eY).symm = eX.symm.prod eY.symm :=
  rfl

@[simp]
/--
theorem `refl_prod_refl` / 定理 `refl_prod_refl`

English:
theorem refl_prod_refl
  statement: (OpenPartialHomeomorph.refl X).prod (OpenPartialHomeomorph.refl Y) =
  proof: OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ

@[simp, mfld_simps]

中文:
定理 refl_prod_refl
  结论: (OpenPartialHomeomorph.refl X).乘积 (OpenPartialHomeomorph.refl Y) =
  证明: OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ

@[simp, mfld_simps]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.ext, univ_prod_univ
-/
theorem refl_prod_refl : (OpenPartialHomeomorph.refl X).prod (OpenPartialHomeomorph.refl Y) =
    OpenPartialHomeomorph.refl (X × Y) :=
  OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) univ_prod_univ

@[simp, mfld_simps]
/--
theorem `prod_trans` / 定理 `prod_trans`

English:
theorem prod_trans
  statement: (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph Y Z)
  proof: toPartialEquiv_injective e.1.prod_trans ..

中文:
定理 prod_trans
  结论: (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph Y Z)
  证明: toPartialEquiv_injective e.1.prod_trans ..

Depends on / 依赖: prod_trans, toPartialEquiv_injective
-/
theorem prod_trans (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph Y Z)
    (e' : OpenPartialHomeomorph X' Y') (f' : OpenPartialHomeomorph Y' Z') :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') :=
toPartialEquiv_injective e.1.prod_trans ..

/--
theorem `prod_eq_prod_of_nonempty` / 定理 `prod_eq_prod_of_nonempty`

English:
theorem prod_eq_prod_of_nonempty
  statement: {eX eX' : OpenPartialHomeomorph X X'}
  proof: by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  have : Nonempty X := ⟨x⟩
  have : Nonempty X' := ⟨eX x⟩
  have : Nonempty Y := ⟨y⟩
  have : Nonempty Y' := ⟨eY y⟩
  simp_rw [OpenPartialHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Pr

中文:
定理 prod_eq_prod_of_nonempty
  结论: {eX eX' : OpenPartialHomeomorph X X'}
  证明: by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  have : Nonempty X := ⟨x⟩
  have : Nonempty X' := ⟨eX x⟩
  have : Nonempty Y := ⟨y⟩
  have : Nonempty Y' := ⟨eY y⟩
  simp_rw [OpenPartialHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Pr

Depends on / 依赖: Nonempty, OpenPartialHomeomorph, OpenPartialHomeomorph.ext_iff, Prod.ext_iff, Prod.forall, Set.prod_eq_prod_iff_of_nonempty, and_assoc, and_left_comm, ext_iff, forall_and, forall_const, prod_apply, prod_eq_prod_iff_of_nonempty, prod_source, prod_symm_apply, simp_rw
-/
theorem prod_eq_prod_of_nonempty {eX eX' : OpenPartialHomeomorph X X'}
    {eY eY' : OpenPartialHomeomorph Y Y'} (h : (eX.prod eY).source.Nonempty) :
    eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  have : Nonempty X := ⟨x⟩
  have : Nonempty X' := ⟨eX x⟩
  have : Nonempty Y := ⟨y⟩
  have : Nonempty Y' := ⟨eY y⟩
  simp_rw [OpenPartialHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and, Prod.forall, forall_const,
    and_assoc, and_left_comm]

/--
theorem `prod_eq_prod_of_nonempty'` / 定理 `prod_eq_prod_of_nonempty'`

English:
theorem prod_eq_prod_of_nonempty'
  proof: by
  rw [eq_comm]; rw [prod_eq_prod_of_nonempty h]; rw [eq_comm]; rw [@eq_comm _ eY']

中文:
定理 prod_eq_prod_of_nonempty'
  证明: by
  rw [eq_comm]; rw [prod_eq_prod_of_nonempty h]; rw [eq_comm]; rw [@eq_comm _ eY']

Depends on / 依赖: eq_comm, prod_eq_prod_of_nonempty
-/
theorem prod_eq_prod_of_nonempty'
    {eX eX' : OpenPartialHomeomorph X X'} {eY eY' : OpenPartialHomeomorph Y Y'}
    (h : (eX'.prod eY').source.Nonempty) : eX.prod eY = eX'.prod eY' ↔ eX = eX' ∧ eY = eY' := by
  rw [eq_comm]; rw [prod_eq_prod_of_nonempty h]; rw [eq_comm]; rw [@eq_comm _ eY']

/--
theorem `prod_symm_trans_prod` / 定理 `prod_symm_trans_prod`

English:
theorem prod_symm_trans_prod
  proof: by
  simp

中文:
定理 prod_symm_trans_prod
  证明: by
  simp
-/
theorem prod_symm_trans_prod
    (e f : OpenPartialHomeomorph X Y) (e' f' : OpenPartialHomeomorph X' Y') :
    (e.prod e').symm.trans (f.prod f') = (e.symm.trans f).prod (e'.symm.trans f') := by
  simp

end Prod

/-!
## Pi types

Finite indexed products of partial homeomorphisms
-/
section Pi

variable {ι : Type*} [Finite ι] {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)]
  [forall i, TopologicalSpace (Y i)] (ei : forall i, OpenPartialHomeomorph (X i) (Y i))

/-- The product of a finite family of `OpenPartialHomeomorph`s. -/
@[simps! toPartialHomeomorph apply symm_apply]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: : OpenPartialHomeomorph (forall i, X i) (forall i, Y i) where
  body: PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).contin

中文:
定义 pi
  签名: : OpenPartialHomeomorph (对任意 i, X i) (对任意 i, Y i) where
  定义体: PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).contin

Depends on / 依赖: PartialEquiv, PartialEquiv.pi, toPartialEquiv
-/
def pi : OpenPartialHomeomorph (forall i, X i) (forall i, Y i) where
  toPartialEquiv := PartialEquiv.pi fun i => (ei i).toPartialEquiv
  open_source := isOpen_set_pi finite_univ fun i _ => (ei i).open_source
  open_target := isOpen_set_pi finite_univ fun i _ => (ei i).open_target
  continuousOn_toFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial
  continuousOn_invFun := continuousOn_pi.2 fun i =>
    (ei i).continuousOn_symm.comp (continuous_apply _).continuousOn fun _f hf => hf i trivial

end Pi

/-!
## Disjoint union

Combining two partial homeomorphisms using `Set.piecewise`
-/
section Piecewise

/-- Combine two `OpenPartialHomeomorph`s using `Set.piecewise`. The source of the new
`OpenPartialHomeomorph` is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly
for target. The function sends `e.source ∩ s` to `e.target ∩ t` using `e` and
`e'.source \ s` to `e'.target \ t` using `e'`, and similarly for the inverse function.
To ensure the maps `toFun` and `invFun` are inverse of each other on the new `source` and `target`,
the definition assumes that the sets `s` and `t` are related both by `e.is_image` and `e'.is_image`.
To ensure that the new maps are continuous on `source`/`target`, it also assumes that `e.source` and
`e'.source` meet `frontier s` on the same set and `e x = e' x` on this intersection. -/
@[simps! -fullyApplied toPartialHomeomorph apply]
/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: (e e' : OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y) [forall x, Decidable (x in s)]
  body: e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
e.open_target.ite e'.open_target H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs

中文:
定义 piecewise
  签名: (e e' : OpenPartialHomeomorph X Y) (s : 集合 X) (t : 集合 Y) [对任意 x, 可判定 (x in s)]
  定义体: e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
e.open_target.ite e'.open_target H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs

Depends on / 依赖: e.toPartialEquiv.piecewise, piecewise, toPartialEquiv
-/
def piecewise (e e' : OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y) [forall x, Decidable (x in s)]
    [forall y, Decidable (y in t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source inter frontier s = e'.source inter frontier s)
    (Heq : EqOn e e' (e.source inter frontier s)) : OpenPartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target :=
e.open_target.ite e'.open_target H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq
  continuousOn_toFun := continuousOn_piecewise_ite e.continuousOn e'.continuousOn Hs Heq
  continuousOn_invFun :=
    continuousOn_piecewise_ite e.continuousOn_symm e'.continuousOn_symm
      (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
      (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq)

@[simp]
/--
theorem `symm_piecewise` / 定理 `symm_piecewise`

English:
theorem symm_piecewise
  statement: (e e' : OpenPartialHomeomorph X Y) {s : Set X} {t : Set Y}
  proof: rfl

中文:
定理 symm_piecewise
  结论: (e e' : OpenPartialHomeomorph X Y) {s : 集合 X} {t : 集合 Y}
  证明: rfl
-/
theorem symm_piecewise (e e' : OpenPartialHomeomorph X Y) {s : Set X} {t : Set Y}
    [forall x, Decidable (x in s)] [forall y, Decidable (y in t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.source inter frontier s = e'.source inter frontier s)
    (Heq : EqOn e e' (e.source inter frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm
        (H.frontier.inter_eq_of_inter_eq_of_eqOn H'.frontier Hs Heq)
        (H.frontier.symm_eqOn_of_inter_eq_of_eqOn Hs Heq) :=
  rfl

/--
Definition of `disjointUnion` / `disjointUnion` 的定义

English:
definition disjointUnion
  signature: (e e' : OpenPartialHomeomorph X Y) [forall x, Decidable (x in e.source)]
  body: (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eq

中文:
定义 disjointUnion
  签名: (e e' : OpenPartialHomeomorph X Y) [对任意 x, 可判定 (x in e.source)]
  定义体: (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eq

Depends on / 依赖: Hs.symm, Hs.symm.frontier_right, Ht.symm, PartialEquiv, PartialEquiv.disjointUnion_eq_piecewise, disjointUnion, disjointUnion_eq_piecewise, e.isImage_source_target, e.open_source.inter_frontier_eq, e.piecewise, e.source, e.target, e.toPartialEquiv.disjointUnion, eqOn_empty, frontier_right, inter_eq, inter_frontier_eq, isImage_source_target, isImage_source_target_of_disjoint, open_source
-/
def disjointUnion (e e' : OpenPartialHomeomorph X Y) [forall x, Decidable (x in e.source)]
    [forall y, Decidable (y in e.target)] (Hs : Disjoint e.source e'.source)
    (Ht : Disjoint e.target e'.target) : OpenPartialHomeomorph X Y :=
  (e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint e Hs.symm Ht.symm)
        (by rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eqOn_empty _ _)).replacePartialEquiv
    (e.toPartialEquiv.disjointUnion e'.toPartialEquiv Hs Ht)
    (PartialEquiv.disjointUnion_eq_piecewise _ _ _ _).symm

end Piecewise

/-
## Post-composition

Post-composing an `OpenPartialHomeomorph` with a homeomorphism
-/
section transHomeomorph

/-- Postcompose an open partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
/--
Definition of `transHomeomorph` / `transHomeomorph` 的定义

English:
definition transHomeomorph
  signature: (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z)
  body: e.toPartialEquiv.transEquiv f'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.preimage f'.symm.continuous
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id

中文:
定义 transHomeomorph
  签名: (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z)
  定义体: e.toPartialEquiv.transEquiv f'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.preimage f'.symm.continuous
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id

Depends on / 依赖: e.toPartialEquiv.transEquiv, toEquiv, toPartialEquiv, transEquiv
-/
def transHomeomorph (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) : OpenPartialHomeomorph X Z where
  toPartialEquiv := e.toPartialEquiv.transEquiv f'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.preimage f'.symm.continuous
  continuousOn_toFun := f'.continuous.comp_continuousOn e.continuousOn
  continuousOn_invFun := e.symm.continuousOn.comp f'.symm.continuous.continuousOn fun _ => id

/--
theorem `transHomeomorph_eq_trans` / 定理 `transHomeomorph_eq_trans`

English:
theorem transHomeomorph_eq_trans
  given: (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z)
  proof: toPartialEquiv_injective PartialEquiv.transEquiv_eq_trans _ _

@[simp, mfld_simps]

中文:
定理 transHomeomorph_eq_trans
  条件: (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z)
  证明: toPartialEquiv_injective PartialEquiv.transEquiv_eq_trans _ _

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.transEquiv_eq_trans, toPartialEquiv_injective, transEquiv_eq_trans
-/
theorem transHomeomorph_eq_trans (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z) :
    e.transHomeomorph f' = e.trans f'.toOpenPartialHomeomorph :=
toPartialEquiv_injective PartialEquiv.transEquiv_eq_trans _ _

@[simp, mfld_simps]
/--
theorem `transHomeomorph_transHomeomorph` / 定理 `transHomeomorph_transHomeomorph`

English:
theorem transHomeomorph_transHomeomorph
  statement: (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z)
  proof: by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toOpenPartialHomeomorph]

@[simp, mfld_simps]

中文:
定理 transHomeomorph_transHomeomorph
  结论: (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z)
  证明: by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toOpenPartialHomeomorph]

@[simp, mfld_simps]

Depends on / 依赖: Homeomorph, Homeomorph.trans_toOpenPartialHomeomorph, transHomeomorph_eq_trans, trans_assoc, trans_toOpenPartialHomeomorph
-/
theorem transHomeomorph_transHomeomorph (e : OpenPartialHomeomorph X Y) (f' : Y ≃ₜ Z)
    (f'' : Z ≃ₜ Z') :
    (e.transHomeomorph f').transHomeomorph f'' = e.transHomeomorph (f'.trans f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc, Homeomorph.trans_toOpenPartialHomeomorph]

@[simp, mfld_simps]
/--
theorem `trans_transHomeomorph` / 定理 `trans_transHomeomorph`

English:
theorem trans_transHomeomorph
  statement: (e : OpenPartialHomeomorph X Y) (e' : OpenPartialHomeomorph Y Z)
  proof: by
  simp only [transHomeomorph_eq_trans, trans_assoc]

中文:
定理 trans_transHomeomorph
  结论: (e : OpenPartialHomeomorph X Y) (e' : OpenPartialHomeomorph Y Z)
  证明: by
  simp only [transHomeomorph_eq_trans, trans_assoc]

Depends on / 依赖: transHomeomorph_eq_trans, trans_assoc
-/
theorem trans_transHomeomorph (e : OpenPartialHomeomorph X Y) (e' : OpenPartialHomeomorph Y Z)
    (f'' : Z ≃ₜ Z') :
    (e.trans e').transHomeomorph f'' = e.trans (e'.transHomeomorph f'') := by
  simp only [transHomeomorph_eq_trans, trans_assoc]

end transHomeomorph

/-!
## Restriction to a subtype

`subtypeRestr`: restriction to a subtype
-/
section subtypeRestr

open TopologicalSpace

variable (e : OpenPartialHomeomorph X Y)
variable {s : Opens X} (hs : Nonempty s)

/--
Definition of `subtypeRestr` / `subtypeRestr` 的定义

English:
definition subtypeRestr
  signature: : OpenPartialHomeomorph s Y
  body: (s.openPartialHomeomorphSubtypeCoe hs).trans e

中文:
定义 subtypeRestr
  签名: : OpenPartialHomeomorph s Y
  定义体: (s.openPartialHomeomorphSubtypeCoe hs).trans e

Depends on / 依赖: openPartialHomeomorphSubtypeCoe, s.openPartialHomeomorphSubtypeCoe
-/
noncomputable def subtypeRestr : OpenPartialHomeomorph s Y :=
  (s.openPartialHomeomorphSubtypeCoe hs).trans e

/--
theorem `subtypeRestr_def` / 定理 `subtypeRestr_def`

English:
theorem subtypeRestr_def
  statement: e.subtypeRestr hs = (s.openPartialHomeomorphSubtypeCoe hs).trans e
  proof: rfl

@[simp, mfld_simps]

中文:
定理 subtypeRestr_def
  结论: e.subtypeRestr hs = (s.openPartialHomeomorphSubtypeCoe hs).trans e
  证明: rfl

@[simp, mfld_simps]
-/
theorem subtypeRestr_def : e.subtypeRestr hs = (s.openPartialHomeomorphSubtypeCoe hs).trans e :=
  rfl

@[simp, mfld_simps]
/--
theorem `subtypeRestr_coe` / 定理 `subtypeRestr_coe`

English:
theorem subtypeRestr_coe
  proof: rfl

@[simp, mfld_simps]

中文:
定理 subtypeRestr_coe
  证明: rfl

@[simp, mfld_simps]
-/
theorem subtypeRestr_coe :
    ((e.subtypeRestr hs : OpenPartialHomeomorph s Y) : s -> Y) = Set.domRestrict ↑s (e : X -> Y) :=
  rfl

@[simp, mfld_simps]
/--
theorem `subtypeRestr_source` / 定理 `subtypeRestr_source`

English:
theorem subtypeRestr_source
  statement: (e.subtypeRestr hs).source = (↑) ⁻¹' e.source
  proof: by
  simp only [subtypeRestr_def, mfld_simps]

中文:
定理 subtypeRestr_source
  结论: (e.subtypeRestr hs).source = (↑) ⁻¹' e.source
  证明: by
  simp only [subtypeRestr_def, mfld_simps]

Depends on / 依赖: mfld_simps, subtypeRestr_def
-/
theorem subtypeRestr_source : (e.subtypeRestr hs).source = (↑) ⁻¹' e.source := by
  simp only [subtypeRestr_def, mfld_simps]

/--
theorem `map_subtype_source` / 定理 `map_subtype_source`

English:
theorem map_subtype_source
  given: {x : s} (hxe : (x : X) in e.source)
  proof: by
  refine ⟨e.map_source hxe, ?_⟩
  rw [s.openPartialHomeomorphSubtypeCoe_target]; rw [mem_preimage]; rw [e.leftInvOn hxe]
  exact x.prop

中文:
定理 map_subtype_source
  条件: {x : s} (hxe : (x : X) in e.source)
  证明: by
  refine ⟨e.map_source hxe, ?_⟩
  rw [s.openPartialHomeomorphSubtypeCoe_target]; rw [mem_preimage]; rw [e.leftInvOn hxe]
  exact x.prop

Depends on / 依赖: e.leftInvOn, e.map_source, leftInvOn, map_source, mem_preimage, openPartialHomeomorphSubtypeCoe_target, s.openPartialHomeomorphSubtypeCoe_target, x.prop
-/
theorem map_subtype_source {x : s} (hxe : (x : X) in e.source) :
    e x in (e.subtypeRestr hs).target := by
  refine ⟨e.map_source hxe, ?_⟩
  rw [s.openPartialHomeomorphSubtypeCoe_target]; rw [mem_preimage]; rw [e.leftInvOn hxe]
  exact x.prop

/--
lemma `subtypeRestr_target_subset` / 引理 `subtypeRestr_target_subset`

English:
lemma subtypeRestr_target_subset
  given: (hs : Nonempty s)
  statement: (e.subtypeRestr hs).target subseteq e.target
  proof: by
  rw [← e.image_source_eq_target]; rw [← OpenPartialHomeomorph.image_source_eq_target]; rw [e.subtypeRestr_source]
  rintro z ⟨z₀, hz₀, rfl⟩
  use z₀.val
  simpa

中文:
引理 subtypeRestr_target_subset
  条件: (hs : 非空 s)
  结论: (e.subtypeRestr hs).target subseteq e.target
  证明: by
  rw [← e.image_source_eq_target]; rw [← OpenPartialHomeomorph.image_source_eq_target]; rw [e.subtypeRestr_source]
  rintro z ⟨z₀, hz₀, rfl⟩
  use z₀.val
  simpa

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.image_source_eq_target, e.image_source_eq_target, e.subtypeRestr_source, image_source_eq_target, subtypeRestr_source
-/
lemma subtypeRestr_target_subset (hs : Nonempty s) : (e.subtypeRestr hs).target subseteq e.target := by
  rw [← e.image_source_eq_target]; rw [← OpenPartialHomeomorph.image_source_eq_target]; rw [e.subtypeRestr_source]
  rintro z ⟨z₀, hz₀, rfl⟩
  use z₀.val
  simpa

/--
theorem `subtypeRestr_symm_trans_subtypeRestr` / 定理 `subtypeRestr_symm_trans_subtypeRestr`

English:
theorem subtypeRestr_symm_trans_subtypeRestr
  given: (f f' : OpenPartialHomeomorph X Y)
  proof: by
  simp only [subtypeRestr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target inter f.symm ⁻¹' s) := f.isOpen_inter_preimage_symm s.2
  rw [← ofSet_trans _ openness₁]; rw [← trans_assoc]; rw [← trans_assoc]
  refine EqOnSource.trans' ?_ (eqOnSource_refl _)
  -- f' has been eli

中文:
定理 subtypeRestr_symm_trans_subtypeRestr
  条件: (f f' : OpenPartialHomeomorph X Y)
  证明: by
  simp only [subtypeRestr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target inter f.symm ⁻¹' s) := f.isOpen_inter_preimage_symm s.2
  rw [← ofSet_trans _ openness₁]; rw [← trans_assoc]; rw [← trans_assoc]
  refine EqOnSource.trans' ?_ (eqOnSource_refl _)
  -- f' has been eli

Depends on / 依赖: EqOnSource, EqOnSource.trans, IsOpen, eqOnSource_refl, f.isOpen_inter_preimage_symm, f.symm, f.target, isOpen_inter_preimage_symm, ofSet_trans, subtypeRestr_def, target, trans_assoc, trans_symm_eq_symm_trans_symm
-/
theorem subtypeRestr_symm_trans_subtypeRestr (f f' : OpenPartialHomeomorph X Y) :
    (f.subtypeRestr hs).symm.trans (f'.subtypeRestr hs) ≈
      (f.symm.trans f').restr (f.target inter f.symm ⁻¹' s) := by
  simp only [subtypeRestr_def, trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target inter f.symm ⁻¹' s) := f.isOpen_inter_preimage_symm s.2
  rw [← ofSet_trans _ openness₁]; rw [← trans_assoc]; rw [← trans_assoc]
  refine EqOnSource.trans' ?_ (eqOnSource_refl _)
  -- f' has been eliminated !!!
  have set_identity : f.symm.source inter (f.target inter f.symm ⁻¹' s) = f.symm.source inter f.symm ⁻¹' s := by
    mfld_set_tac
  have openness₂ : IsOpen (s : Set X) := s.2
  rw [ofSet_trans']; rw [set_identity]; rw [← trans_of_set' _ openness₂]; rw [trans_assoc]
  refine EqOnSource.trans' (eqOnSource_refl _) ?_
  -- f has been eliminated !!!
  refine Setoid.trans (symm_trans_self (s.openPartialHomeomorphSubtypeCoe hs)) ?_
  simp only [mfld_simps, Setoid.refl]

/--
theorem `subtypeRestr_symm_apply` / 定理 `subtypeRestr_symm_apply`

English:
theorem subtypeRestr_symm_apply
  statement: {U : Opens X} (hU : Nonempty U)
  proof: by
  rw [e.eq_symm_apply _ hy.1]
  · change domRestrict _ e _ = _
    rw [← e.subtypeRestr_coe hU]; rw [(e.subtypeRestr hU).right_inv hy]
  · have := OpenPartialHomeomorph.map_target _ hy
    rwa [e.subtypeRestr_source] at this

中文:
定理 subtypeRestr_symm_apply
  结论: {U : Opens X} (hU : 非空 U)
  证明: by
  rw [e.eq_symm_apply _ hy.1]
  · change domRestrict _ e _ = _
    rw [← e.subtypeRestr_coe hU]; rw [(e.subtypeRestr hU).right_inv hy]
  · have := OpenPartialHomeomorph.map_target _ hy
    rwa [e.subtypeRestr_source] at this

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.map_target, domRestrict, e.eq_symm_apply, e.subtypeRestr, e.subtypeRestr_coe, e.subtypeRestr_source, eq_symm_apply, map_target, right_inv, subtypeRestr, subtypeRestr_coe, subtypeRestr_source
-/
theorem subtypeRestr_symm_apply {U : Opens X} (hU : Nonempty U)
    {y : Y} (hy : y in (e.subtypeRestr hU).target) :
    (Subtype.val ∘ (e.subtypeRestr hU).symm) y = e.symm y := by
  rw [e.eq_symm_apply _ hy.1]
  · change domRestrict _ e _ = _
    rw [← e.subtypeRestr_coe hU]; rw [(e.subtypeRestr hU).right_inv hy]
  · have := OpenPartialHomeomorph.map_target _ hy
    rwa [e.subtypeRestr_source] at this

/--
theorem `subtypeRestr_symm_eqOn` / 定理 `subtypeRestr_symm_eqOn`

English:
theorem subtypeRestr_symm_eqOn
  given: {U : Opens X} (hU : Nonempty U)
  proof: fun _y hy => (e.subtypeRestr_symm_apply hU hy).symm

中文:
定理 subtypeRestr_symm_eqOn
  条件: {U : Opens X} (hU : 非空 U)
  证明: fun _y hy => (e.subtypeRestr_symm_apply hU hy).symm

Depends on / 依赖: e.subtypeRestr_symm_apply, subtypeRestr_symm_apply
-/
theorem subtypeRestr_symm_eqOn {U : Opens X} (hU : Nonempty U) :
    EqOn e.symm (Subtype.val ∘ (e.subtypeRestr hU).symm) (e.subtypeRestr hU).target :=
  fun _y hy => (e.subtypeRestr_symm_apply hU hy).symm

/--
theorem `subtypeRestr_symm_eqOn_of_le` / 定理 `subtypeRestr_symm_eqOn_of_le`

English:
theorem subtypeRestr_symm_eqOn_of_le
  statement: {U V : Opens X} (hU : Nonempty U) (hV : Nonempty V)
  proof: by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [OpenPartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y in (V.openPartialHomeomorphSubtypeCoe hV).target := by
    rw [Opens.openPartialHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine (V.openPartialHomeomorphSubtype

中文:
定理 subtypeRestr_symm_eqOn_of_le
  结论: {U V : Opens X} (hU : 非空 U) (hV : 非空 V)
  证明: by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [OpenPartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y in (V.openPartialHomeomorphSubtypeCoe hV).target := by
    rw [Opens.openPartialHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine (V.openPartialHomeomorphSubtype

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.subtypeRestr_def, Opens.openPartialHomeomorphSubtypeCoe_target, Set.inclusion, U.openPartialHomeomorphSubtypeCoe, V.openPartialHomeomorphSubtypeCoe, e.symm, inclusion, openPartialHomeomorphSubtypeCoe, openPartialHomeomorphSubtypeCoe_target, right_inv, subtypeRestr_def, target
-/
theorem subtypeRestr_symm_eqOn_of_le {U V : Opens X} (hU : Nonempty U) (hV : Nonempty V)
    (hUV : U <= V) : EqOn (e.subtypeRestr hV).symm (Set.inclusion hUV ∘ (e.subtypeRestr hU).symm)
      (e.subtypeRestr hU).target := by
  set i := Set.inclusion hUV
  intro y hy
  dsimp [OpenPartialHomeomorph.subtypeRestr_def] at hy ⊢
  have hyV : e.symm y in (V.openPartialHomeomorphSubtypeCoe hV).target := by
    rw [Opens.openPartialHomeomorphSubtypeCoe_target] at hy ⊢
    exact hUV hy.2
  refine (V.openPartialHomeomorphSubtypeCoe hV).injOn ?_ trivial ?_
  · simp
  · rw [(V.openPartialHomeomorphSubtypeCoe hV).right_inv hyV]
    change _ = U.openPartialHomeomorphSubtypeCoe hU _
    rw [(U.openPartialHomeomorphSubtypeCoe hU).right_inv hy.2]

end subtypeRestr

/-!
## Extending along an open embedding
-/
section lift_openEmbedding

variable {X X' Z : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Z]
  [Nonempty Z] {f : X -> X'}

/--
Definition of `lift_openEmbedding` / `lift_openEmbedding` 的定义

English:
definition lift_openEmbedding
  signature: (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f)
  body: extend f e (fun _ => (Classical.arbitrary Z))
  invFun := f ∘ e.invFun
  source := f '' e.source
  target := e.target
  map_source' := by
    rintro x ⟨x₀, hx₀, hxx₀⟩
    rw [← hxx₀]; rw [hf.injective.extend_apply e]
    exact e.map_source' hx₀
  map_target' z hz := mem_image_of_mem f (e.map_target'

中文:
定义 lift_openEmbedding
  签名: (e : OpenPartialHomeomorph X Z) (hf : 是开嵌入 f)
  定义体: extend f e (fun _ => (Classical.arbitrary Z))
  invFun := f ∘ e.invFun
  source := f '' e.source
  target := e.target
  map_source' := by
    rintro x ⟨x₀, hx₀, hxx₀⟩
    rw [← hxx₀]; rw [hf.injective.extend_apply e]
    exact e.map_source' hx₀
  map_target' z hz := mem_image_of_mem f (e.map_target'

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, extend
-/
noncomputable def lift_openEmbedding (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    OpenPartialHomeomorph X' Z where
  toFun := extend f e (fun _ => (Classical.arbitrary Z))
  invFun := f ∘ e.invFun
  source := f '' e.source
  target := e.target
  map_source' := by
    rintro x ⟨x₀, hx₀, hxx₀⟩
    rw [← hxx₀]; rw [hf.injective.extend_apply e]
    exact e.map_source' hx₀
  map_target' z hz := mem_image_of_mem f (e.map_target' hz)
  left_inv' := by
    intro x ⟨x₀, hx₀, hxx₀⟩
    rw [← hxx₀]; rw [hf.injective.extend_apply e]; rw [comp_apply]
    congr
    exact e.left_inv' hx₀
  right_inv' z hz := by simpa only [comp_apply, hf.injective.extend_apply e] using! e.right_inv' hz
  open_source := hf.isOpenMap _ e.open_source
  open_target := e.open_target
  continuousOn_toFun := by
    by_cases Nonempty X; swap
    · intro x hx; simp_all
    set F := (extend f e (fun _ => (Classical.arbitrary Z))) with F_eq
    have heq : EqOn F (e ∘ (hf.toOpenPartialHomeomorph).symm) (f '' e.source) := by
      intro x ⟨x₀, hx₀, hxx₀⟩
      rw [← hxx₀]; rw [F_eq]; rw [hf.injective.extend_apply e]; rw [comp_apply]; rw [hf.toOpenPartialHomeomorph_left_inv]
    have : ContinuousOn (e ∘ (hf.toOpenPartialHomeomorph).symm) (f '' e.source) := by
      apply e.continuousOn_toFun.comp; swap
      · intro x' ⟨x, hx, hx'x⟩
        rw [← hx'x]; rw [hf.toOpenPartialHomeomorph_left_inv]; exact hx
      have : ContinuousOn (hf.toOpenPartialHomeomorph).symm (f '' univ) :=
        (hf.toOpenPartialHomeomorph).continuousOn_invFun
exact this.mono image_mono subset_univ _
    exact ContinuousOn.congr this heq
  continuousOn_invFun := hf.continuous.comp_continuousOn e.continuousOn_invFun

@[simp, mfld_simps]
/--
lemma `lift_openEmbedding_toFun` / 引理 `lift_openEmbedding_toFun`

English:
lemma lift_openEmbedding_toFun
  given: (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f)
  proof: rfl

中文:
引理 lift_openEmbedding_toFun
  条件: (e : OpenPartialHomeomorph X Z) (hf : 是开嵌入 f)
  证明: rfl
-/
lemma lift_openEmbedding_toFun (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf) = extend f e (fun _ => (Classical.arbitrary Z)) := rfl

/--
lemma `lift_openEmbedding_apply` / 引理 `lift_openEmbedding_apply`

English:
lemma lift_openEmbedding_apply
  given: (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) {x : X}
  proof: by
  simp_rw [e.lift_openEmbedding_toFun]
  apply hf.injective.extend_apply

@[simp, mfld_simps]

中文:
引理 lift_openEmbedding_apply
  条件: (e : OpenPartialHomeomorph X Z) (hf : 是开嵌入 f) {x : X}
  证明: by
  simp_rw [e.lift_openEmbedding_toFun]
  apply hf.injective.extend_apply

@[simp, mfld_simps]

Depends on / 依赖: e.lift_openEmbedding_toFun, extend_apply, hf.injective.extend_apply, injective, lift_openEmbedding_toFun, simp_rw
-/
lemma lift_openEmbedding_apply (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) {x : X} :
    (lift_openEmbedding e hf) (f x) = e x := by
  simp_rw [e.lift_openEmbedding_toFun]
  apply hf.injective.extend_apply

@[simp, mfld_simps]
/--
lemma `lift_openEmbedding_source` / 引理 `lift_openEmbedding_source`

English:
lemma lift_openEmbedding_source
  given: (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f)
  proof: rfl

@[simp, mfld_simps]

中文:
引理 lift_openEmbedding_source
  条件: (e : OpenPartialHomeomorph X Z) (hf : 是开嵌入 f)
  证明: rfl

@[simp, mfld_simps]
-/
lemma lift_openEmbedding_source (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).source = f '' e.source := rfl

@[simp, mfld_simps]
/--
lemma `lift_openEmbedding_target` / 引理 `lift_openEmbedding_target`

English:
lemma lift_openEmbedding_target
  given: (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f)
  proof: rfl

@[simp, mfld_simps]

中文:
引理 lift_openEmbedding_target
  条件: (e : OpenPartialHomeomorph X Z) (hf : 是开嵌入 f)
  证明: rfl

@[simp, mfld_simps]
-/
lemma lift_openEmbedding_target (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).target = e.target := rfl

@[simp, mfld_simps]
/--
lemma `lift_openEmbedding_symm` / 引理 `lift_openEmbedding_symm`

English:
lemma lift_openEmbedding_symm
  given: (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f)
  proof: rfl

@[simp, mfld_simps]

中文:
引理 lift_openEmbedding_symm
  条件: (e : OpenPartialHomeomorph X Z) (hf : 是开嵌入 f)
  证明: rfl

@[simp, mfld_simps]
-/
lemma lift_openEmbedding_symm (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm = f ∘ e.symm := rfl

@[simp, mfld_simps]
/--
lemma `lift_openEmbedding_symm_source` / 引理 `lift_openEmbedding_symm_source`

English:
lemma lift_openEmbedding_symm_source
  given: (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f)
  proof: rfl

@[simp, mfld_simps]

中文:
引理 lift_openEmbedding_symm_source
  条件: (e : OpenPartialHomeomorph X Z) (hf : 是开嵌入 f)
  证明: rfl

@[simp, mfld_simps]
-/
lemma lift_openEmbedding_symm_source (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.source = e.target := rfl

@[simp, mfld_simps]
/--
lemma `lift_openEmbedding_symm_target` / 引理 `lift_openEmbedding_symm_target`

English:
lemma lift_openEmbedding_symm_target
  given: (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f)
  proof: by
  rw [OpenPartialHomeomorph.symm_target]; rw [e.lift_openEmbedding_source]

中文:
引理 lift_openEmbedding_symm_target
  条件: (e : OpenPartialHomeomorph X Z) (hf : 是开嵌入 f)
  证明: by
  rw [OpenPartialHomeomorph.symm_target]; rw [e.lift_openEmbedding_source]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.symm_target, e.lift_openEmbedding_source, lift_openEmbedding_source, symm_target
-/
lemma lift_openEmbedding_symm_target (e : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.target = f '' e.source := by
  rw [OpenPartialHomeomorph.symm_target]; rw [e.lift_openEmbedding_source]

/--
lemma `lift_openEmbedding_trans_apply` / 引理 `lift_openEmbedding_trans_apply`

English:
lemma lift_openEmbedding_trans_apply
  proof: by
  simp [hf.injective.extend_apply e']

@[simp, mfld_simps]

中文:
引理 lift_openEmbedding_trans_apply
  证明: by
  simp [hf.injective.extend_apply e']

@[simp, mfld_simps]

Depends on / 依赖: extend_apply, hf.injective.extend_apply, injective
-/
lemma lift_openEmbedding_trans_apply
    (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) (z : Z) :
    (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmbedding hf) z = (e.symm.trans e') z := by
  simp [hf.injective.extend_apply e']

@[simp, mfld_simps]
/--
lemma `lift_openEmbedding_trans` / 引理 `lift_openEmbedding_trans`

English:
lemma lift_openEmbedding_trans
  given: (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f)
  proof: by
  ext z
  · exact e.lift_openEmbedding_trans_apply e' hf z
  · simp [hf.injective.extend_apply e]
  · simp_rw [OpenPartialHomeomorph.trans_source, e.lift_openEmbedding_symm_source, e.symm_source,
      e.lift_openEmbedding_symm, e'.lift_openEmbedding_source]
    refine ⟨fun ⟨hx, ⟨y, hy, hxy⟩⟩ => 

中文:
引理 lift_openEmbedding_trans
  条件: (e e' : OpenPartialHomeomorph X Z) (hf : 是开嵌入 f)
  证明: by
  ext z
  · exact e.lift_openEmbedding_trans_apply e' hf z
  · simp [hf.injective.extend_apply e]
  · simp_rw [OpenPartialHomeomorph.trans_source, e.lift_openEmbedding_symm_source, e.symm_source,
      e.lift_openEmbedding_symm, e'.lift_openEmbedding_source]
    refine ⟨fun ⟨hx, ⟨y, hy, hxy⟩⟩ => 

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.trans_source, comp_apply, e.lift_openEmbedding_symm, e.lift_openEmbedding_symm_source, e.lift_openEmbedding_trans_apply, e.symm_source, extend_apply, hf.injective, hf.injective.extend_apply, injective, lift_openEmbedding_source, lift_openEmbedding_symm, lift_openEmbedding_symm_source, lift_openEmbedding_trans_apply, mem_image_of_mem, mem_preimage, simp_rw, symm_source, trans_source
-/
lemma lift_openEmbedding_trans (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) :
    (e.lift_openEmbedding hf).symm.trans (e'.lift_openEmbedding hf) = e.symm.trans e' := by
  ext z
  · exact e.lift_openEmbedding_trans_apply e' hf z
  · simp [hf.injective.extend_apply e]
  · simp_rw [OpenPartialHomeomorph.trans_source, e.lift_openEmbedding_symm_source, e.symm_source,
      e.lift_openEmbedding_symm, e'.lift_openEmbedding_source]
    refine ⟨fun ⟨hx, ⟨y, hy, hxy⟩⟩ => ⟨hx, ?_⟩, fun ⟨hx, hx'⟩ => ⟨hx, mem_image_of_mem f hx'⟩⟩
    rw [mem_preimage]; rw [comp_apply] at hxy
    exact (hf.injective hxy) ▸ hy

end lift_openEmbedding

end OpenPartialHomeomorph
