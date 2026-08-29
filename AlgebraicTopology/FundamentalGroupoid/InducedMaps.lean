/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala, Yury Kudryashov
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product

/-!
# Homotopic maps induce naturally isomorphic functors

## Main definitions

- `FundamentalGroupoidFunctor.homotopicMapsNatIso H` The natural isomorphism
  between the induced functors `f : π(X) ⥤ π(Y)` and `g : π(X) ⥤ π(Y)`, given a homotopy
  `H : f ∼ g`

- `FundamentalGroupoidFunctor.equivOfHomotopyEquiv hequiv` The equivalence of the categories
  `π(X)` and `π(Y)` given a homotopy equivalence `hequiv : X ≃ₕ Y` between them.
-/

@[expose] public section

noncomputable section

universe u v

open FundamentalGroupoid CategoryTheory FundamentalGroupoidFunctor
open scoped FundamentalGroupoid unitInterval

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Path.Homotopic.map_trans_evalAt` / 定理 `Path.Homotopic.map_trans_evalAt`

English:
theorem Path.Homotopic.map_trans_evalAt
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  proof: by
  /- Let `G` be the continuous map on the unit square sending `(t, s)` to `F(t, p(s))`.
  Then our homotopy is the image under `G` of a homotopy
  between the two paths from `(0, 0)` to `(1, 1)` along the sides of the square. -/
  set G : C(I × I, Y) := F.toContinuousMap.comp (.prodMap (.id _) p)

中文:
定理 Path.Homotopic.map_trans_evalAt
  结论: {X Y : 类型} [TopologicalSpace X] [TopologicalSpace Y]
  证明: by
  /- Let `G` be the continuous map on the unit square sending `(t, s)` to `F(t, p(s))`.
  Then our homotopy is the image under `G` of a homotopy
  between the two paths from `(0, 0)` to `(1, 1)` along the sides of the square. -/
  set G : C(I × I, Y) := F.toContinuousMap.comp (.prodMap (.id _) p)
-/
theorem Path.Homotopic.map_trans_evalAt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (F : f.Homotopy g) {x₁ x₂ : X} (p : Path x₁ x₂) :
    ((p.map (map_continuous f)).trans (F.evalAt x₂)).Homotopic
      ((F.evalAt x₁).trans (p.map (map_continuous g))) := by
  /- Let `G` be the continuous map on the unit square sending `(t, s)` to `F(t, p(s))`.
  Then our homotopy is the image under `G` of a homotopy
  between the two paths from `(0, 0)` to `(1, 1)` along the sides of the square. -/
  set G : C(I × I, Y) := F.toContinuousMap.comp (.prodMap (.id _) p)
  set p₁ : Path ((0, 0) : I × I) (1, 1) := .prod (.trans (.refl _) .id) (.trans .id (.refl _))
  set p₂ : Path ((0, 0) : I × I) (1, 1) := .prod (.trans .id (.refl _)) (.trans (.refl _) .id)
  set Fsq : p₁.Homotopy p₂ :=
    Path.Homotopic.prodHomotopy (.trans (.reflTrans _) (.symm <| .transRefl _))
      (.trans (.transRefl _) (.symm <| .reflTrans _))
  refine ⟨((Fsq.map G).pathCast ?H0 ?H1).cast ?hp ?hq⟩
  all_goals aesop (add simp Path.trans_apply)

namespace FundamentalGroupoidFunctor

open CategoryTheory
open scoped FundamentalGroupoid ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}

set_option backward.isDefEq.respectTransparency false in
set_option pp.proofs.withType true in
/--
Definition of `homotopicMapsNatIso` / `homotopicMapsNatIso` 的定义

English:
definition homotopicMapsNatIso
  signature: (H : ContinuousMap.Homotopy f g)
  body: ⟦H.evalAt x.as⟧
  naturality := by
    rintro ⟨x⟩ ⟨y⟩ p
    rcases Path.Homotopic.Quotient.mk_surjective p with ⟨p, rfl⟩
    simp only [map_map, Path.Homotopic.Quotient.mk''_eq_mk, comp_eq,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans]
    rw [Path.Homotopic.Quotient.eq

中文:
定义 homotopicMapsNatIso
  签名: (H : ContinuousMap.Homotopy f g)
  定义体: ⟦H.evalAt x.as⟧
  naturality := by
    rintro ⟨x⟩ ⟨y⟩ p
    rcases Path.Homotopic.Quotient.mk_surjective p with ⟨p, rfl⟩
    simp only [map_map, Path.Homotopic.Quotient.mk''_eq_mk, comp_eq,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans]
    rw [Path.Homotopic.Quotient.eq

Depends on / 依赖: H.evalAt, evalAt, x.as
-/
def homotopicMapsNatIso (H : ContinuousMap.Homotopy f g) : map f ⟶ map g where
  app x := ⟦H.evalAt x.as⟧
  naturality := by
    rintro ⟨x⟩ ⟨y⟩ p
    rcases Path.Homotopic.Quotient.mk_surjective p with ⟨p, rfl⟩
    simp only [map_map, Path.Homotopic.Quotient.mk''_eq_mk, comp_eq,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans]
    rw [Path.Homotopic.Quotient.eq]
    exact .map_trans_evalAt _ _

instance (H : ContinuousMap.Homotopy f g) : IsIso (homotopicMapsNatIso H) :=
  NatIso.isIso_of_isIso_app _

open scoped ContinuousMap

/--
Definition of `equivOfHomotopyEquiv` / `equivOfHomotopyEquiv` 的定义

English:
definition equivOfHomotopyEquiv
  signature: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (hequiv : X ≃ₕ Y)
  body: by
  apply CategoryTheory.Equivalence.mk (map hequiv.toFun) (map hequiv.invFun)
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using (asIso (homotopicMapsNatIso hequiv.left_inv.some)).symm
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
    

中文:
定义 equivOfHomotopyEquiv
  签名: {X Y : 类型} [TopologicalSpace X] [TopologicalSpace Y] (hequiv : X ≃ₕ Y)
  定义体: by
  apply CategoryTheory.Equivalence.mk (map hequiv.toFun) (map hequiv.invFun)
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using (asIso (homotopicMapsNatIso hequiv.left_inv.some)).symm
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
    

Depends on / 依赖: CategoryTheory, CategoryTheory.Equivalence.mk, Equivalence, FundamentalGroupoid, FundamentalGroupoid.map_comp, FundamentalGroupoid.map_id, hequiv, hequiv.invFun, hequiv.left_inv.some, hequiv.right_inv.some, hequiv.toFun, homotopicMapsNatIso, invFun, left_inv, map_comp, map_id, right_inv
-/
def equivOfHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (hequiv : X ≃ₕ Y) :
    πₓ (.of X) ≌ πₓ (.of Y) := by
  apply CategoryTheory.Equivalence.mk (map hequiv.toFun) (map hequiv.invFun)
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using (asIso (homotopicMapsNatIso hequiv.left_inv.some)).symm
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using asIso (homotopicMapsNatIso hequiv.right_inv.some)

end FundamentalGroupoidFunctor

/-!
### Old proof

The rest of the file contains definitions and theorems required to write the same proof
in a slightly different manner.

The proof was rewritten in 2025 for two reasons:

- the new proof is much more straightforward;
- the new proof is fully universe polymorphic.

TODO: review which of these definitions and theorems are useful for other reasons,
then deprecate the rest of them.
-/

namespace unitInterval

/--
Definition of `path01` / `path01` 的定义

English:
definition path01
  signature: : Path (0 : I) 1 where
  body: id
  source' := rfl
  target' := rfl

中文:
定义 path01
  签名: : Path (0 : I) 1 where
  定义体: id
  source' := rfl
  target' := rfl
-/
def path01 : Path (0 : I) 1 where
  toFun := id
  source' := rfl
  target' := rfl

/--
Definition of `upath01` / `upath01` 的定义

English:
definition upath01
  signature: : Path (ULift.up 0 : ULift.{u} I) (ULift.up 1) where
  body: ULift.up
  source' := rfl
  target' := rfl

中文:
定义 upath01
  签名: : Path (ULift.up 0 : ULift.{u} I) (ULift.up 1) where
  定义体: ULift.up
  source' := rfl
  target' := rfl

Depends on / 依赖: ULift.up
-/
def upath01 : Path (ULift.up 0 : ULift.{u} I) (ULift.up 1) where
  toFun := ULift.up
  source' := rfl
  target' := rfl

/--
Definition of `uhpath01` / `uhpath01` 的定义

English:
definition uhpath01
  signature: : @fromTop (TopCat.of <| ULift.{u} I) (ULift.up (0 : I)) ⟶ fromTop (ULift.up 1)
  body: ⟦upath01⟧

中文:
定义 uhpath01
  签名: : @fromTop (TopCat.of <| ULift.{u} I) (ULift.up (0 : I)) ⟶ fromTop (ULift.up 1)
  定义体: ⟦upath01⟧

Depends on / 依赖: upath01
-/
def uhpath01 : @fromTop (TopCat.of <| ULift.{u} I) (ULift.up (0 : I)) ⟶ fromTop (ULift.up 1) :=
  ⟦upath01⟧

end unitInterval

namespace ContinuousMap.Homotopy

open unitInterval (uhpath01)

section Casts

/--
Definition of `hcast` / `hcast` 的定义

English:
abbreviation hcast
  signature: {X : TopCat.{u}} {x₀ x₁ : X} (hx : x₀ = x₁)
  body: eqToHom FundamentalGroupoid.ext hx

@[simp]

中文:
缩写 hcast
  签名: {X : TopCat.{u}} {x₀ x₁ : X} (hx : x₀ = x₁)
  定义体: eqToHom FundamentalGroupoid.ext hx

@[simp]

Depends on / 依赖: FundamentalGroupoid, FundamentalGroupoid.ext, eqToHom
-/
abbrev hcast {X : TopCat.{u}} {x₀ x₁ : X} (hx : x₀ = x₁) : fromTop x₀ ⟶ fromTop x₁ :=
eqToHom FundamentalGroupoid.ext hx

@[simp]
/--
theorem `hcast_def` / 定理 `hcast_def`

English:
theorem hcast_def
  given: {X : TopCat.{u}} {x₀ x₁ : X} (hx₀ : x₀ = x₁)
  proof: rfl

中文:
定理 hcast_def
  条件: {X : TopCat.{u}} {x₀ x₁ : X} (hx₀ : x₀ = x₁)
  证明: rfl
-/
theorem hcast_def {X : TopCat.{u}} {x₀ x₁ : X} (hx₀ : x₀ = x₁) :
    hcast hx₀ = eqToHom (FundamentalGroupoid.ext hx₀) :=
  rfl

variable {X₁ X₂ Y : TopCat.{u}} {f : C(X₁, Y)} {g : C(X₂, Y)} {x₀ x₁ : X₁} {x₂ x₃ : X₂}
  {p : Path x₀ x₁} {q : Path x₂ x₃} (hfg : forall t, f (p t) = g (q t))
include hfg

/--
theorem `heq_path_of_eq_image` / 定理 `heq_path_of_eq_image`

English:
theorem heq_path_of_eq_image
  proof: by
  apply Path.Homotopic.hpath_hext
  exact hfg

中文:
定理 heq_path_of_eq_image
  证明: by
  apply Path.Homotopic.hpath_hext
  exact hfg

Depends on / 依赖: Homotopic, Path.Homotopic.hpath_hext, hpath_hext
-/
theorem heq_path_of_eq_image :
    (πₘ (TopCat.ofHom f)).map ⟦p⟧ ≍ (πₘ (TopCat.ofHom g)).map ⟦q⟧ := by
  apply Path.Homotopic.hpath_hext
  exact hfg

set_option backward.privateInPublic true in
/--
theorem `start_path` / 定理 `start_path`

English:
theorem start_path
  statement: f x₀ = g x₂
  proof: by convert! hfg 0 <;> simp only [Path.source]

中文:
定理 start_path
  结论: f x₀ = g x₂
  证明: by convert! hfg 0 <;> simp only [Path.source]
-/
private theorem start_path : f x₀ = g x₂ := by convert! hfg 0 <;> simp only [Path.source]

set_option backward.privateInPublic true in
/--
theorem `end_path` / 定理 `end_path`

English:
theorem end_path
  statement: f x₁ = g x₃
  proof: by convert! hfg 1 <;> simp only [Path.target]

中文:
定理 end_path
  结论: f x₁ = g x₃
  证明: by convert! hfg 1 <;> simp only [Path.target]
-/
private theorem end_path : f x₁ = g x₃ := by convert! hfg 1 <;> simp only [Path.target]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `eq_path_of_eq_image` / 定理 `eq_path_of_eq_image`

English:
theorem eq_path_of_eq_image
  proof: by
  rw [conj_eqToHom_iff_heq
    ((πₘ (TopCat.ofHom f)).map ⟦p⟧) ((πₘ (TopCat.ofHom g)).map ⟦q⟧)
    (FundamentalGroupoid.ext <| start_path hfg)
    (FundamentalGroupoid.ext <| end_path hfg)]
  exact heq_path_of_eq_image hfg

中文:
定理 eq_path_of_eq_image
  证明: by
  rw [conj_eqToHom_iff_heq
    ((πₘ (TopCat.ofHom f)).map ⟦p⟧) ((πₘ (TopCat.ofHom g)).map ⟦q⟧)
    (FundamentalGroupoid.ext <| start_path hfg)
    (FundamentalGroupoid.ext <| end_path hfg)]
  exact heq_path_of_eq_image hfg

Depends on / 依赖: FundamentalGroupoid, FundamentalGroupoid.ext, TopCat, TopCat.ofHom, conj_eqToHom_iff_heq, end_path, heq_path_of_eq_image, start_path
-/
theorem eq_path_of_eq_image :
    (πₘ (TopCat.ofHom f)).map ⟦p⟧ =
        hcast (start_path hfg) ≫ (πₘ (TopCat.ofHom g)).map ⟦q⟧ ≫ hcast (end_path hfg).symm := by
  rw [conj_eqToHom_iff_heq
    ((πₘ (TopCat.ofHom f)).map ⟦p⟧) ((πₘ (TopCat.ofHom g)).map ⟦q⟧)
    (FundamentalGroupoid.ext <| start_path hfg)
    (FundamentalGroupoid.ext <| end_path hfg)]
  exact heq_path_of_eq_image hfg

end Casts

-- We let `X` and `Y` be spaces, and `f` and `g` be homotopic maps between them
variable {X Y : TopCat.{u}} {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) {x₀ x₁ : X}
  (p : fromTop x₀ ⟶ fromTop x₁)

/-!
These definitions set up the following diagram, for each path `p`:

```
            f(p)
        *--------*
        | \ |
    H₀ | \ d | H₁
        | \ |
        *--------*
            g(p)
```

Here, `H₀ = H.evalAt x₀` is the path from `f(x₀)` to `g(x₀)`,
and similarly for `H₁`. Similarly, `f(p)` denotes the
path in Y that the induced map `f` takes `p`, and similarly for `g(p)`.

Finally, `d`, the diagonal path, is H(0 ⟶ 1, p), the result of the induced `H` on
`Path.Homotopic.prod (0 ⟶ 1) p`, where `(0 ⟶ 1)` denotes the path from `0` to `1` in `I`.

It is clear that the diagram commutes (`H₀ ≫ g(p) = d = f(p) ≫ H₁`), but unfortunately,
many of the paths do not have defeq starting/ending points, so we end up needing some casting.
-/


/--
Definition of `uliftMap` / `uliftMap` 的定义

English:
definition uliftMap
  signature: : C(TopCat.of (ULift.{u} I × X), Y)
  body: ⟨fun x => H (x.1.down, x.2),
    H.continuous.comp ((continuous_uliftDown.comp continuous_fst).prodMk continuous_snd)⟩

中文:
定义 uliftMap
  签名: : C(TopCat.of (ULift.{u} I × X), Y)
  定义体: ⟨fun x => H (x.1.down, x.2),
    H.continuous.comp ((continuous_uliftDown.comp continuous_fst).prodMk continuous_snd)⟩

Depends on / 依赖: H.continuous.comp, continuous, continuous_fst, continuous_snd, continuous_uliftDown, continuous_uliftDown.comp, prodMk
-/
def uliftMap : C(TopCat.of (ULift.{u} I × X), Y) :=
  ⟨fun x => H (x.1.down, x.2),
    H.continuous.comp ((continuous_uliftDown.comp continuous_fst).prodMk continuous_snd)⟩

/--
theorem `ulift_apply` / 定理 `ulift_apply`

English:
theorem ulift_apply
  given: (i : ULift.{u} I) (x : X)
  statement: H.uliftMap (i, x) = H (i.down, x)
  proof: rfl

中文:
定理 ulift_apply
  条件: (i : ULift.{u} I) (x : X)
  结论: H.uliftMap (i, x) = H (i.down, x)
  证明: rfl
-/
theorem ulift_apply (i : ULift.{u} I) (x : X) : H.uliftMap (i, x) = H (i.down, x) :=
  rfl

/--
Definition of `prodToProdTopI` / `prodToProdTopI` 的定义

English:
abbreviation prodToProdTopI
  signature: {a₁ a₂ : TopCat.of (ULift I)} {b₁ b₂ : X} (p₁ : fromTop a₁ ⟶ fromTop a₂)
  body: (prodToProdTop (TopCat.of <| ULift I) X).map (X := (⟨a₁⟩, ⟨b₁⟩)) (Y := (⟨a₂⟩, ⟨b₂⟩)) (p₁, p₂)

中文:
缩写 prodToProdTopI
  签名: {a₁ a₂ : TopCat.of (ULift I)} {b₁ b₂ : X} (p₁ : fromTop a₁ ⟶ fromTop a₂)
  定义体: (prodToProdTop (TopCat.of <| ULift I) X).map (X := (⟨a₁⟩, ⟨b₁⟩)) (Y := (⟨a₂⟩, ⟨b₂⟩)) (p₁, p₂)

Depends on / 依赖: TopCat, TopCat.of, prodToProdTop
-/
abbrev prodToProdTopI {a₁ a₂ : TopCat.of (ULift I)} {b₁ b₂ : X} (p₁ : fromTop a₁ ⟶ fromTop a₂)
    (p₂ : fromTop b₁ ⟶ fromTop b₂) :=
  (prodToProdTop (TopCat.of <| ULift I) X).map (X := (⟨a₁⟩, ⟨b₁⟩)) (Y := (⟨a₂⟩, ⟨b₂⟩)) (p₁, p₂)

/--
Definition of `diagonalPath` / `diagonalPath` 的定义

English:
definition diagonalPath
  signature: : fromTop (H (0, x₀)) ⟶ fromTop (H (1, x₁))
  body: (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI uhpath01 p)

中文:
定义 diagonalPath
  签名: : fromTop (H (0, x₀)) ⟶ fromTop (H (1, x₁))
  定义体: (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI uhpath01 p)

Depends on / 依赖: H.uliftMap, TopCat, TopCat.ofHom, prodToProdTopI, uhpath01, uliftMap
-/
def diagonalPath : fromTop (H (0, x₀)) ⟶ fromTop (H (1, x₁)) :=
  (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI uhpath01 p)

/--
Definition of `diagonalPath'` / `diagonalPath'` 的定义

English:
definition diagonalPath'
  signature: : fromTop (f x₀) ⟶ fromTop (g x₁)
  body: hcast (H.apply_zero x₀).symm ≫ H.diagonalPath p ≫ hcast (H.apply_one x₁)

中文:
定义 diagonalPath'
  签名: : fromTop (f x₀) ⟶ fromTop (g x₁)
  定义体: hcast (H.apply_zero x₀).symm ≫ H.diagonalPath p ≫ hcast (H.apply_one x₁)

Depends on / 依赖: H.apply_one, H.apply_zero, H.diagonalPath, apply_one, apply_zero, diagonalPath
-/
def diagonalPath' : fromTop (f x₀) ⟶ fromTop (g x₁) :=
  hcast (H.apply_zero x₀).symm ≫ H.diagonalPath p ≫ hcast (H.apply_one x₁)

/--
theorem `apply_zero_path` / 定理 `apply_zero_path`

English:
theorem apply_zero_path
  statement: (πₘ (TopCat.ofHom f)).map p = hcast (H.apply_zero x₀).symm ≫
  proof: Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe]; rw [ulift_apply H]
    simp

中文:
定理 apply_zero_path
  结论: (πₘ (TopCat.ofHom f)).map p = hcast (H.apply_zero x₀).symm ≫
  证明: Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe]; rw [ulift_apply H]
    simp

Depends on / 依赖: H.uliftMap, Path.prod_coe, Path.refl, Quotient, Quotient.inductionOn, ULift.up, eq_path_of_eq_image, inductionOn, intros, prod_coe, uliftMap, ulift_apply
-/
theorem apply_zero_path : (πₘ (TopCat.ofHom f)).map p = hcast (H.apply_zero x₀).symm ≫
    (πₘ (TopCat.ofHom H.uliftMap)).map
      (prodToProdTopI (𝟙 (@fromTop (TopCat.of _) (ULift.up 0))) p) ≫
    hcast (H.apply_zero x₁) :=
  Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe]; rw [ulift_apply H]
    simp

/--
theorem `apply_one_path` / 定理 `apply_one_path`

English:
theorem apply_one_path
  statement: (πₘ (TopCat.ofHom g)).map p = hcast (H.apply_one x₀).symm ≫
  proof: Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe]; rw [ulift_apply H]
    simp

中文:
定理 apply_one_path
  结论: (πₘ (TopCat.ofHom g)).map p = hcast (H.apply_one x₀).symm ≫
  证明: Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe]; rw [ulift_apply H]
    simp

Depends on / 依赖: H.uliftMap, Path.prod_coe, Path.refl, Quotient, Quotient.inductionOn, ULift.up, eq_path_of_eq_image, inductionOn, intros, prod_coe, uliftMap, ulift_apply
-/
theorem apply_one_path : (πₘ (TopCat.ofHom g)).map p = hcast (H.apply_one x₀).symm ≫
    (πₘ (TopCat.ofHom H.uliftMap)).map
      (prodToProdTopI (𝟙 (@fromTop (TopCat.of _) (ULift.up 1))) p) ≫
    hcast (H.apply_one x₁) :=
  Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe]; rw [ulift_apply H]
    simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `evalAt_eq` / 定理 `evalAt_eq`

English:
theorem evalAt_eq
  given: (x : X)
  statement: ⟦H.evalAt x⟧ = hcast (H.apply_zero x).symm ≫
  proof: by
  dsimp only [prodToProdTopI, uhpath01, hcast]
  refine (@conj_eqToHom_iff_heq (πₓ Y) _ _ _ _ _ _ _ _
    (FundamentalGroupoid.ext <| H.apply_one x).symm).mpr ?_
  simp only [map_eq]
  apply Path.Homotopic.hpath_hext; intro; rfl

中文:
定理 evalAt_eq
  条件: (x : X)
  结论: ⟦H.evalAt x⟧ = hcast (H.apply_zero x).symm ≫
  证明: by
  dsimp only [prodToProdTopI, uhpath01, hcast]
  refine (@conj_eqToHom_iff_heq (πₓ Y) _ _ _ _ _ _ _ _
    (FundamentalGroupoid.ext <| H.apply_one x).symm).mpr ?_
  simp only [map_eq]
  apply Path.Homotopic.hpath_hext; intro; rfl

Depends on / 依赖: FundamentalGroupoid, FundamentalGroupoid.ext, H.apply_one, Homotopic, Path.Homotopic.hpath_hext, apply_one, conj_eqToHom_iff_heq, hpath_hext, map_eq, prodToProdTopI, uhpath01
-/
theorem evalAt_eq (x : X) : ⟦H.evalAt x⟧ = hcast (H.apply_zero x).symm ≫
    (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI uhpath01 (𝟙 (fromTop x))) ≫
      hcast (H.apply_one x).symm.symm := by
  dsimp only [prodToProdTopI, uhpath01, hcast]
  refine (@conj_eqToHom_iff_heq (πₓ Y) _ _ _ _ _ _ _ _
    (FundamentalGroupoid.ext <| H.apply_one x).symm).mpr ?_
  simp only [map_eq]
  apply Path.Homotopic.hpath_hext; intro; rfl

set_option backward.isDefEq.respectTransparency false in
-- Finally, we show `d = f(p) ≫ H₁ = H₀ ≫ g(p)`
/--
theorem `eq_diag_path` / 定理 `eq_diag_path`

English:
theorem eq_diag_path
  statement: (πₘ (TopCat.ofHom f)).map p ≫ ⟦H.evalAt x₁⟧ = H.diagonalPath' p ∧
  proof: by
  rw [H.apply_zero_path]; rw [H.apply_one_path]; rw [H.evalAt_eq]
  erw [H.evalAt_eq]
  dsimp only [prodToProdTopI]
  constructor
  · slice_lhs 2 4 => rw [eqToHom_trans, eqToHom_refl] -- Porting note: this ↓ `simp` didn't do this
    slice_lhs 2 4 => simp [← CategoryTheory.Functor.map_comp]
    r

中文:
定理 eq_diag_path
  结论: (πₘ (TopCat.ofHom f)).map p ≫ ⟦H.evalAt x₁⟧ = H.diagonalPath' p ∧
  证明: by
  rw [H.apply_zero_path]; rw [H.apply_one_path]; rw [H.evalAt_eq]
  erw [H.evalAt_eq]
  dsimp only [prodToProdTopI]
  constructor
  · slice_lhs 2 4 => rw [eqToHom_trans, eqToHom_refl] -- Porting note: this ↓ `simp` didn't do this
    slice_lhs 2 4 => simp [← CategoryTheory.Functor.map_comp]
    r

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_comp, Functor, H.apply_one_path, H.apply_zero_path, H.evalAt_eq, Porting, apply_one_path, apply_zero_path, eqToHom_refl, eqToHom_trans, evalAt_eq, map_comp, prodToProdTopI, slice_lhs
-/
theorem eq_diag_path : (πₘ (TopCat.ofHom f)).map p ≫ ⟦H.evalAt x₁⟧ = H.diagonalPath' p ∧
    (⟦H.evalAt x₀⟧ ≫ (πₘ (TopCat.ofHom g)).map p :
    fromTop (f x₀) ⟶ fromTop (g x₁)) = H.diagonalPath' p := by
  rw [H.apply_zero_path]; rw [H.apply_one_path]; rw [H.evalAt_eq]
  erw [H.evalAt_eq]
  dsimp only [prodToProdTopI]
  constructor
  · slice_lhs 2 4 => rw [eqToHom_trans, eqToHom_refl] -- Porting note: this ↓ `simp` didn't do this
    slice_lhs 2 4 => simp [← CategoryTheory.Functor.map_comp]
    rfl
  · slice_lhs 2 4 => rw [eqToHom_trans, eqToHom_refl] -- Porting note: this ↓ `simp` didn't do this
    slice_lhs 2 4 => simp [← CategoryTheory.Functor.map_comp]
    rfl

end ContinuousMap.Homotopy
