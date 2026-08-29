/-
Copyright (c) 2021 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homotopy.Path

/-!
# Product of homotopies

In this file, we introduce definitions for the product of
homotopies. We show that the products of relative homotopies
are still relative homotopies. Finally, we specialize to the case
of path homotopies, and provide the definition for the product of path classes.
We show various lemmas associated with these products, such as the fact that
path products commute with path composition, and that projection is the inverse
of products.

## Definitions

### General homotopies
- `ContinuousMap.Homotopy.pi homotopies`: Let f and g be a family of functions
  indexed on I, such that for each i ∈ I, fᵢ and gᵢ are maps from A to Xᵢ.
  Let `homotopies` be a family of homotopies from fᵢ to gᵢ for each i.
  Then `Homotopy.pi homotopies` is the canonical homotopy
  from ∏ f to ∏ g, where ∏ f is the product map from A to Πi, Xᵢ,
  and similarly for ∏ g.

- `ContinuousMap.HomotopyRel.pi homotopies`: Same as `ContinuousMap.Homotopy.pi`, but
  all homotopies are done relative to some set S ⊆ A.

- `ContinuousMap.Homotopy.prod F G` is the product of homotopies F and G,
  where F is a homotopy between f₀ and f₁, G is a homotopy between g₀ and g₁.
  The result F × G is a homotopy between (f₀ × g₀) and (f₁ × g₁).
  Again, all homotopies are done relative to S.

- `ContinuousMap.HomotopyRel.prod F G`: Same as `ContinuousMap.Homotopy.prod`, but
  all homotopies are done relative to some set S ⊆ A.

### Path products
- `Path.Homotopic.pi` The product of a family of path classes, where a path class is an equivalence
  class of paths up to path homotopy.

- `Path.Homotopic.prod` The product of two path classes.
-/

@[expose] public section


noncomputable section

namespace ContinuousMap

open ContinuousMap

section Pi

variable {I A : Type*} {X : I -> Type*} [forall i, TopologicalSpace (X i)] [TopologicalSpace A]
  {f g : forall i, C(A, X i)} {S : Set A}

/-- The relative product homotopy of `homotopies` between functions `f` and `g` -/
@[simps!]
/--
Definition of `HomotopyRel.pi` / `HomotopyRel.pi` 的定义

English:
definition HomotopyRel.pi
  signature: (homotopies : forall i : I, HomotopyRel (f i) (g i) S)
  body: { Homotopy.pi fun i => (homotopies i).toHomotopy with
    prop' := by
      intro t x hx
      dsimp only [coe_mk, pi_eval, toFun_eq_coe, HomotopyWith.coe_toContinuousMap]
      simp only [funext_iff]
      intro i
      exact (homotopies i).prop' t x hx }

中文:
定义 HomotopyRel.pi
  签名: (homotopies : 对任意 i : I, HomotopyRel (f i) (g i) S)
  定义体: { Homotopy.pi fun i => (homotopies i).toHomotopy with
    prop' := by
      intro t x hx
      dsimp only [coe_mk, pi_eval, toFun_eq_coe, HomotopyWith.coe_toContinuousMap]
      simp only [funext_iff]
      intro i
      exact (homotopies i).prop' t x hx }

Depends on / 依赖: Homotopy, Homotopy.pi, HomotopyWith, HomotopyWith.coe_toContinuousMap, coe_mk, coe_toContinuousMap, funext_iff, homotopies, pi_eval, toFun_eq_coe, toHomotopy
-/
def HomotopyRel.pi (homotopies : forall i : I, HomotopyRel (f i) (g i) S) :
    HomotopyRel (pi f) (pi g) S :=
  { Homotopy.pi fun i => (homotopies i).toHomotopy with
    prop' := by
      intro t x hx
      dsimp only [coe_mk, pi_eval, toFun_eq_coe, HomotopyWith.coe_toContinuousMap]
      simp only [funext_iff]
      intro i
      exact (homotopies i).prop' t x hx }

end Pi

section Prod

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {A : Type*} [TopologicalSpace A]
  {f₀ f₁ : C(A, α)} {g₀ g₁ : C(A, β)} {S : Set A}

/-- The product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁` and `G` takes `g₀` to `g₁` -/
@[simps]
/--
Definition of `Homotopy.prod` / `Homotopy.prod` 的定义

English:
definition Homotopy.prod
  signature: (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁)
  body: (F t, G t)
  map_zero_left x := by simp only [prod_eval, Homotopy.apply_zero]
  map_one_left x := by simp only [prod_eval, Homotopy.apply_one]

中文:
定义 Homotopy.prod
  签名: (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁)
  定义体: (F t, G t)
  map_zero_left x := by simp only [prod_eval, Homotopy.apply_zero]
  map_one_left x := by simp only [prod_eval, Homotopy.apply_one]
-/
def Homotopy.prod (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (ContinuousMap.prodMk f₀ g₀) (ContinuousMap.prodMk f₁ g₁) where
  toFun t := (F t, G t)
  map_zero_left x := by simp only [prod_eval, Homotopy.apply_zero]
  map_one_left x := by simp only [prod_eval, Homotopy.apply_one]

/-- The relative product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁` and `G` takes `g₀` to `g₁` -/
@[simps!]
/--
Definition of `HomotopyRel.prod` / `HomotopyRel.prod` 的定义

English:
definition HomotopyRel.prod
  signature: (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel g₀ g₁ S)
  body: Homotopy.prod F.toHomotopy G.toHomotopy
  prop' t x hx := Prod.ext (F.prop' t x hx) (G.prop' t x hx)

中文:
定义 HomotopyRel.prod
  签名: (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel g₀ g₁ S)
  定义体: Homotopy.prod F.toHomotopy G.toHomotopy
  prop' t x hx := Prod.ext (F.prop' t x hx) (G.prop' t x hx)

Depends on / 依赖: F.toHomotopy, G.toHomotopy, Homotopy, Homotopy.prod, toHomotopy
-/
def HomotopyRel.prod (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel g₀ g₁ S) :
    HomotopyRel (prodMk f₀ g₀) (prodMk f₁ g₁) S where
  toHomotopy := Homotopy.prod F.toHomotopy G.toHomotopy
  prop' t x hx := Prod.ext (F.prop' t x hx) (G.prop' t x hx)

end Prod

end ContinuousMap

namespace Path.Homotopic

local infixl:70 " ⬝ " => Quotient.trans

section Pi

variable {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] {as bs cs : forall i, X i}

/--
Definition of `piHomotopy` / `piHomotopy` 的定义

English:
definition piHomotopy
  signature: (γ₀ γ₁ : forall i, Path (as i) (bs i)) (H : forall i, Path.Homotopy (γ₀ i) (γ₁ i))
  body: ContinuousMap.HomotopyRel.pi H

中文:
定义 piHomotopy
  签名: (γ₀ γ₁ : 对任意 i, Path (as i) (bs i)) (H : 对任意 i, Path.Homotopy (γ₀ i) (γ₁ i))
  定义体: ContinuousMap.HomotopyRel.pi H

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.pi, HomotopyRel
-/
def piHomotopy (γ₀ γ₁ : forall i, Path (as i) (bs i)) (H : forall i, Path.Homotopy (γ₀ i) (γ₁ i)) :
    Path.Homotopy (Path.pi γ₀) (Path.pi γ₁) :=
  ContinuousMap.HomotopyRel.pi H

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (γ : forall i, Path.Homotopic.Quotient (as i) (bs i))
  body: (_root_.Quotient.map Path.pi fun x y hxy =>
    Nonempty.map (piHomotopy x y) (Classical.nonempty_pi.mpr hxy)) (Quotient.choice γ)

中文:
定义 pi
  签名: (γ : 对任意 i, Path.Homotopic.Quotient (as i) (bs i))
  定义体: (_root_.Quotient.map Path.pi fun x y hxy =>
    Nonempty.map (piHomotopy x y) (Classical.nonempty_pi.mpr hxy)) (Quotient.choice γ)

Depends on / 依赖: Classical, Classical.nonempty_pi.mpr, Nonempty, Nonempty.map, Path.pi, Quotient, Quotient.choice, _root_, _root_.Quotient.map, choice, nonempty_pi, piHomotopy
-/
def pi (γ : forall i, Path.Homotopic.Quotient (as i) (bs i)) : Path.Homotopic.Quotient as bs :=
  (_root_.Quotient.map Path.pi fun x y hxy =>
    Nonempty.map (piHomotopy x y) (Classical.nonempty_pi.mpr hxy)) (Quotient.choice γ)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pi_lift` / 定理 `pi_lift`

English:
theorem pi_lift
  given: (γ : forall i, Path (as i) (bs i))
  proof: by
  simp_rw [← Quotient.mk'_eq_mk, Quotient.mk', pi, Quotient.choice_eq, Quotient.map_mk]

中文:
定理 pi_lift
  条件: (γ : 对任意 i, Path (as i) (bs i))
  证明: by
  simp_rw [← Quotient.mk'_eq_mk, Quotient.mk', pi, Quotient.choice_eq, Quotient.map_mk]

Depends on / 依赖: Quotient, Quotient.choice_eq, Quotient.map_mk, Quotient.mk, _eq_mk, choice_eq, map_mk, simp_rw
-/
theorem pi_lift (γ : forall i, Path (as i) (bs i)) :
    (Path.Homotopic.pi fun i => (Quotient.mk (γ i))) = Quotient.mk (Path.pi γ) := by
  simp_rw [← Quotient.mk'_eq_mk, Quotient.mk', pi, Quotient.choice_eq, Quotient.map_mk]

/--
theorem `comp_pi_eq_pi_comp` / 定理 `comp_pi_eq_pi_comp`

English:
theorem comp_pi_eq_pi_comp
  statement: (γ₀ : forall i, Path.Homotopic.Quotient (as i) (bs i))
  proof: by
  induction γ₁ using Quotient.induction_on_pi with | _ a =>
  induction γ₀ using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk, pi_lift]
  rw [← Path.Homotopic.Quotient.mk_trans]; rw [Path.trans_pi_eq_pi_trans]; rw [← pi_lift]
  rfl

中文:
定理 comp_pi_eq_pi_comp
  结论: (γ₀ : 对任意 i, Path.Homotopic.Quotient (as i) (bs i))
  证明: by
  induction γ₁ using Quotient.induction_on_pi with | _ a =>
  induction γ₀ using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk, pi_lift]
  rw [← Path.Homotopic.Quotient.mk_trans]; rw [Path.trans_pi_eq_pi_trans]; rw [← pi_lift]
  rfl

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient.mk_trans, Path.trans_pi_eq_pi_trans, Quotient, Quotient.induction_on_pi, Quotient.mk, _eq_mk, induction_on_pi, mk_trans, pi_lift, trans_pi_eq_pi_trans
-/
theorem comp_pi_eq_pi_comp (γ₀ : forall i, Path.Homotopic.Quotient (as i) (bs i))
    (γ₁ : forall i, Path.Homotopic.Quotient (bs i) (cs i)) : pi γ₀ ⬝ pi γ₁ = pi fun i => γ₀ i ⬝ γ₁ i := by
  induction γ₁ using Quotient.induction_on_pi with | _ a =>
  induction γ₀ using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk, pi_lift]
  rw [← Path.Homotopic.Quotient.mk_trans]; rw [Path.trans_pi_eq_pi_trans]; rw [← pi_lift]
  rfl

/--
Definition of `proj` / `proj` 的定义

English:
abbreviation proj
  signature: (i : ι) (p : Path.Homotopic.Quotient as bs)
  body: p.map ⟨_, continuous_apply i⟩

中文:
缩写 proj
  签名: (i : ι) (p : Path.Homotopic.Quotient as bs)
  定义体: p.map ⟨_, continuous_apply i⟩

Depends on / 依赖: continuous_apply, p.map
-/
abbrev proj (i : ι) (p : Path.Homotopic.Quotient as bs) : Path.Homotopic.Quotient (as i) (bs i) :=
  p.map ⟨_, continuous_apply i⟩

/-- Lemmas showing projection is the inverse of pi. -/
@[simp]
/--
theorem `proj_pi` / 定理 `proj_pi`

English:
theorem proj_pi
  given: (i : ι) (paths : forall i, Path.Homotopic.Quotient (as i) (bs i))
  proof: by
  induction paths using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk]
  rw [proj]; rw [pi_lift]
  congr

@[simp]

中文:
定理 proj_pi
  条件: (i : ι) (paths : 对任意 i, Path.Homotopic.Quotient (as i) (bs i))
  证明: by
  induction paths using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk]
  rw [proj]; rw [pi_lift]
  congr

@[simp]

Depends on / 依赖: Quotient, Quotient.induction_on_pi, Quotient.mk, _eq_mk, induction_on_pi, pi_lift
-/
theorem proj_pi (i : ι) (paths : forall i, Path.Homotopic.Quotient (as i) (bs i)) :
    proj i (pi paths) = paths i := by
  induction paths using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk]
  rw [proj]; rw [pi_lift]
  congr

@[simp]
/--
theorem `pi_proj` / 定理 `pi_proj`

English:
theorem pi_proj
  given: (p : Path.Homotopic.Quotient as bs)
  statement: (pi fun i => proj i p) = p
  proof: by
  induction p using Quotient.inductionOn
  simp only [Quotient.mk''_eq_mk, ← Path.Homotopic.Quotient.mk_map, pi_lift]
  congr

中文:
定理 pi_proj
  条件: (p : Path.Homotopic.Quotient as bs)
  结论: (pi fun i => proj i p) = p
  证明: by
  induction p using Quotient.inductionOn
  simp only [Quotient.mk''_eq_mk, ← Path.Homotopic.Quotient.mk_map, pi_lift]
  congr

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient.mk_map, Quotient, Quotient.inductionOn, Quotient.mk, _eq_mk, inductionOn, mk_map, pi_lift
-/
theorem pi_proj (p : Path.Homotopic.Quotient as bs) : (pi fun i => proj i p) = p := by
  induction p using Quotient.inductionOn
  simp only [Quotient.mk''_eq_mk, ← Path.Homotopic.Quotient.mk_map, pi_lift]
  congr

end Pi

section Prod

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {a₁ a₂ a₃ : α} {b₁ b₂ b₃ : β}
  {p₁ p₁' : Path a₁ a₂} {p₂ p₂' : Path b₁ b₂} (q₁ : Path.Homotopic.Quotient a₁ a₂)
  (q₂ : Path.Homotopic.Quotient b₁ b₂)

/--
Definition of `prodHomotopy` / `prodHomotopy` 的定义

English:
definition prodHomotopy
  signature: (h₁ : Path.Homotopy p₁ p₁') (h₂ : Path.Homotopy p₂ p₂')
  body: ContinuousMap.HomotopyRel.prod h₁ h₂

中文:
定义 prodHomotopy
  签名: (h₁ : Path.Homotopy p₁ p₁') (h₂ : Path.Homotopy p₂ p₂')
  定义体: ContinuousMap.HomotopyRel.prod h₁ h₂

Depends on / 依赖: ContinuousMap, ContinuousMap.HomotopyRel.prod, HomotopyRel
-/
def prodHomotopy (h₁ : Path.Homotopy p₁ p₁') (h₂ : Path.Homotopy p₂ p₂') :
    Path.Homotopy (p₁.prod p₂) (p₁'.prod p₂') :=
  ContinuousMap.HomotopyRel.prod h₁ h₂

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (q₁ : Path.Homotopic.Quotient a₁ a₂) (q₂ : Path.Homotopic.Quotient b₁ b₂)
  body: Quotient.map₂ Path.prod (fun _ _ h₁ _ _ h₂ => Nonempty.map2 prodHomotopy h₁ h₂) q₁ q₂

中文:
定义 prod
  签名: (q₁ : Path.Homotopic.Quotient a₁ a₂) (q₂ : Path.Homotopic.Quotient b₁ b₂)
  定义体: Quotient.map₂ Path.prod (fun _ _ h₁ _ _ h₂ => Nonempty.map2 prodHomotopy h₁ h₂) q₁ q₂

Depends on / 依赖: Nonempty, Nonempty.map2, Path.prod, Quotient, Quotient.map, prodHomotopy
-/
def prod (q₁ : Path.Homotopic.Quotient a₁ a₂) (q₂ : Path.Homotopic.Quotient b₁ b₂) :
    Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂) :=
  Quotient.map₂ Path.prod (fun _ _ h₁ _ _ h₂ => Nonempty.map2 prodHomotopy h₁ h₂) q₁ q₂

variable (p₁ p₁' p₂ p₂')

/--
theorem `prod_lift` / 定理 `prod_lift`

English:
theorem prod_lift
  statement: prod (Quotient.mk p₁) (Quotient.mk p₂) = Quotient.mk (p₁.prod p₂)
  proof: rfl

中文:
定理 prod_lift
  结论: prod (Quotient.mk p₁) (Quotient.mk p₂) = Quotient.mk (p₁.prod p₂)
  证明: rfl
-/
theorem prod_lift : prod (Quotient.mk p₁) (Quotient.mk p₂) = Quotient.mk (p₁.prod p₂) :=
  rfl

variable (r₁ : Path.Homotopic.Quotient a₂ a₃) (r₂ : Path.Homotopic.Quotient b₂ b₃)

/--
theorem `comp_prod_eq_prod_comp` / 定理 `comp_prod_eq_prod_comp`

English:
theorem comp_prod_eq_prod_comp
  statement: prod q₁ q₂ ⬝ prod r₁ r₂ = prod (q₁ ⬝ r₁) (q₂ ⬝ r₂)
  proof: by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  induction r₁, r₂ using Path.Homotopic.Quotient.ind₂
  simp only [prod_lift, ← Path.Homotopic.Quotient.mk_trans, Path.trans_prod_eq_prod_trans]

中文:
定理 comp_prod_eq_prod_comp
  结论: prod q₁ q₂ ⬝ prod r₁ r₂ = prod (q₁ ⬝ r₁) (q₂ ⬝ r₂)
  证明: by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  induction r₁, r₂ using Path.Homotopic.Quotient.ind₂
  simp only [prod_lift, ← Path.Homotopic.Quotient.mk_trans, Path.trans_prod_eq_prod_trans]

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient.ind, Path.Homotopic.Quotient.mk_trans, Path.trans_prod_eq_prod_trans, Quotient, mk_trans, prod_lift, trans_prod_eq_prod_trans
-/
theorem comp_prod_eq_prod_comp : prod q₁ q₂ ⬝ prod r₁ r₂ = prod (q₁ ⬝ r₁) (q₂ ⬝ r₂) := by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  induction r₁, r₂ using Path.Homotopic.Quotient.ind₂
  simp only [prod_lift, ← Path.Homotopic.Quotient.mk_trans, Path.trans_prod_eq_prod_trans]

variable {c₁ c₂ : α × β}

/--
Definition of `projLeft` / `projLeft` 的定义

English:
abbreviation projLeft
  signature: (p : Path.Homotopic.Quotient c₁ c₂)
  body: p.map ⟨_, continuous_fst⟩

中文:
缩写 projLeft
  签名: (p : Path.Homotopic.Quotient c₁ c₂)
  定义体: p.map ⟨_, continuous_fst⟩

Depends on / 依赖: continuous_fst, p.map
-/
abbrev projLeft (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.1 c₂.1 :=
  p.map ⟨_, continuous_fst⟩

/--
Definition of `projRight` / `projRight` 的定义

English:
abbreviation projRight
  signature: (p : Path.Homotopic.Quotient c₁ c₂)
  body: p.map ⟨_, continuous_snd⟩

中文:
缩写 projRight
  签名: (p : Path.Homotopic.Quotient c₁ c₂)
  定义体: p.map ⟨_, continuous_snd⟩

Depends on / 依赖: continuous_snd, p.map
-/
abbrev projRight (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.2 c₂.2 :=
  p.map ⟨_, continuous_snd⟩

/-- Lemmas showing projection is the inverse of product. -/
@[simp]
/--
theorem `projLeft_prod` / 定理 `projLeft_prod`

English:
theorem projLeft_prod
  statement: projLeft (prod q₁ q₂) = q₁
  proof: by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projLeft]; rw [prod_lift]; rw [← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]

中文:
定理 projLeft_prod
  结论: projLeft (prod q₁ q₂) = q₁
  证明: by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projLeft]; rw [prod_lift]; rw [← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient.ind, Path.Homotopic.Quotient.mk_map, Quotient, mk_map, prod_lift, projLeft
-/
theorem projLeft_prod : projLeft (prod q₁ q₂) = q₁ := by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projLeft]; rw [prod_lift]; rw [← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]
/--
theorem `projRight_prod` / 定理 `projRight_prod`

English:
theorem projRight_prod
  statement: projRight (prod q₁ q₂) = q₂
  proof: by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projRight]; rw [prod_lift]; rw [← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]

中文:
定理 projRight_prod
  结论: projRight (prod q₁ q₂) = q₂
  证明: by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projRight]; rw [prod_lift]; rw [← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient.ind, Path.Homotopic.Quotient.mk_map, Quotient, mk_map, prod_lift, projRight
-/
theorem projRight_prod : projRight (prod q₁ q₂) = q₂ := by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projRight]; rw [prod_lift]; rw [← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]
/--
theorem `prod_projLeft_projRight` / 定理 `prod_projLeft_projRight`

English:
theorem prod_projLeft_projRight
  given: (p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂))
  proof: by
  induction p using Path.Homotopic.Quotient.ind
  simp only [projLeft, projRight, ← Path.Homotopic.Quotient.mk_map]
  congr

中文:
定理 prod_projLeft_projRight
  条件: (p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂))
  证明: by
  induction p using Path.Homotopic.Quotient.ind
  simp only [projLeft, projRight, ← Path.Homotopic.Quotient.mk_map]
  congr

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient.ind, Path.Homotopic.Quotient.mk_map, Quotient, mk_map, projLeft, projRight
-/
theorem prod_projLeft_projRight (p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂)) :
    prod (projLeft p) (projRight p) = p := by
  induction p using Path.Homotopic.Quotient.ind
  simp only [projLeft, projRight, ← Path.Homotopic.Quotient.mk_map]
  congr

end Prod

end Path.Homotopic
