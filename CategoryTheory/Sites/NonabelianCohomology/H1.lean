/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Basic

/-! # The cohomology of a sheaf of groups in degree 1

In this file, we shall define the cohomology in degree 1 of a sheaf
of groups (TODO).

Currently, given a presheaf of groups `G : Cᵒᵖ ⥤ GrpCat` and a family
of objects `U : I → C`, we define 1-cochains/1-cocycles/H^1 with values
in `G` over `U`. (This definition neither requires the assumption that `G`
is a sheaf, nor that `U` covers the terminal object.)
As we do not assume that `G` is a presheaf of abelian groups, this
cohomology theory is only defined in low degrees; in the abelian
case, it would be a particular case of Čech cohomology (TODO).

## TODO

* show that if `1 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 1` is a short exact sequence of sheaves
  of groups, and `x₃` is a global section of `G₃` which can be locally lifted
  to a section of `G₂`, there is an associated canonical cohomology class of `G₁`
  which is trivial iff `x₃` can be lifted to a global section of `G₂`.
  (This should hold more generally if `G₂` is a sheaf of sets on which `G₁` acts
  freely, and `G₃` is the quotient sheaf.)
* deduce a similar result for abelian sheaves
* when the notion of quasi-coherent sheaves on schemes is defined, show that
  if `0 ⟶ Q ⟶ M ⟶ N ⟶ 0` is an exact sequence of abelian sheaves over a scheme `X`
  and `Q` is the underlying sheaf of a quasi-coherent sheaf, then `M(U) ⟶ N(U)`
  is surjective for any affine open `U`.
* take the colimit of `OneCohomology G U` over all covering families `U` (for
  a Grothendieck topology)

# References

* [J. Frenkel, *Cohomologie non abélienne et espaces fibrés*][frenkel1957]

-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace PresheafOfGroups

variable (G : Cᵒᵖ ⥤ GrpCat.{w}) {I : Type w'} (U : I -> C)

/--
Definition of `ZeroCochain` / `ZeroCochain` 的定义

English:
definition ZeroCochain
  body: forall (i : I), G.obj (Opposite.op (U i))

中文:
定义 ZeroCochain
  定义体: forall (i : I), G.obj (Opposite.op (U i))

Depends on / 依赖: G.obj, Opposite, Opposite.op
-/
def ZeroCochain := forall (i : I), G.obj (Opposite.op (U i))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (ZeroCochain G U)
  body: Pi.group

中文:
实例 :
  签名: 群 (ZeroCochain G U)
  定义体: Pi.group

Depends on / 依赖: Pi.group
-/
instance : Group (ZeroCochain G U) := Pi.group

namespace Cochain₀

@[simp]
/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: (i : I)
  statement: (1 : ZeroCochain G U) i = 1
  proof: rfl

@[simp]

中文:
引理 one_apply
  条件: (i : I)
  结论: (1 : ZeroCochain G U) i = 1
  证明: rfl

@[simp]
-/
lemma one_apply (i : I) : (1 : ZeroCochain G U) i = 1 := rfl

@[simp]
/--
lemma `inv_apply` / 引理 `inv_apply`

English:
lemma inv_apply
  given: (γ : ZeroCochain G U) (i : I)
  statement: γ⁻¹ i = (γ i)⁻¹
  proof: rfl

@[simp]

中文:
引理 inv_apply
  条件: (γ : ZeroCochain G U) (i : I)
  结论: γ⁻¹ i = (γ i)⁻¹
  证明: rfl

@[simp]
-/
lemma inv_apply (γ : ZeroCochain G U) (i : I) : γ⁻¹ i = (γ i)⁻¹ := rfl

@[simp]
/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (γ₁ γ₂ : ZeroCochain G U) (i : I)
  statement: (γ₁ * γ₂) i = γ₁ i * γ₂ i
  proof: rfl

中文:
引理 mul_apply
  条件: (γ₁ γ₂ : ZeroCochain G U) (i : I)
  结论: (γ₁ * γ₂) i = γ₁ i * γ₂ i
  证明: rfl
-/
lemma mul_apply (γ₁ γ₂ : ZeroCochain G U) (i : I) : (γ₁ * γ₂) i = γ₁ i * γ₂ i := rfl

end Cochain₀

/-- A 1-cochain of a presheaf of groups `G : Cᵒᵖ ⥤ GrpCat` on a family `U : I → C` of objects
consists of the data of an element in `G.obj (Opposite.op T)` whenever we have elements
`i` and `j` in `I` and maps `a : T ⟶ U i` and `b : T ⟶ U j`, and it must satisfy a compatibility
with respect to precomposition. (When the binary product of `U i` and `U j` exists, this
data for all `T`, `a` and `b` corresponds to the data of a section of `G` on this product.) -/
@[ext]
/--
Definition of `OneCochain` / `OneCochain` 的定义

English:
structure OneCochain
  parameters: where
  axioms and operations (2):
    - ev((i j : I) ⦃T) : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) : G.obj (Opposite.op T)
    - ev_precomp((i j : I) ⦃T T') : C⦄ (φ : T ⟶ T') (a : T' ⟶ U i) (b : T' ⟶ U j) : G.map φ.op (ev i j a b) = ev i j (φ ≫ a) (φ ≫ b)  [default: by aesop]

中文:
结构 OneCochain
  参数: where
  公理与运算 (2 个):
    - ev((i j : I) ⦃T) : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) : G.obj (对偶.op T)
    - ev_precomp((i j : I) ⦃T T') : C⦄ (φ : T ⟶ T') (a : T' ⟶ U i) (b : T' ⟶ U j) : G.map φ.op (ev i j a b) = ev i j (φ ≫ a) (φ ≫ b)  [默认: by aesop]
-/
structure OneCochain where
  /-- the data involved in a 1-cochain -/
  ev (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) : G.obj (Opposite.op T)
  ev_precomp (i j : I) ⦃T T' : C⦄ (φ : T ⟶ T') (a : T' ⟶ U i) (b : T' ⟶ U j) :
    G.map φ.op (ev i j a b) = ev i j (φ ≫ a) (φ ≫ b) := by aesop

namespace OneCochain

attribute [simp] OneCochain.ev_precomp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (OneCochain G U)
  body: { ev := fun _ _ _ _ _ => 1 }

@[simp]

中文:
实例 :
  签名: 幺 (OneCochain G U)
  定义体: { ev := fun _ _ _ _ _ => 1 }

@[simp]
-/
instance : One (OneCochain G U) where
  one := { ev := fun _ _ _ _ _ => 1 }

@[simp]
/--
lemma `one_ev` / 引理 `one_ev`

English:
lemma one_ev
  given: (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j)
  proof: rfl

中文:
引理 one_ev
  条件: (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j)
  证明: rfl
-/
lemma one_ev (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (1 : OneCochain G U).ev i j a b = 1 := rfl

variable {G U}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (OneCochain G U)
  body: { ev := fun i j _ a b => γ₁.ev i j a b * γ₂.ev i j a b }

@[simp]

中文:
实例 :
  签名: 乘法 (OneCochain G U)
  定义体: { ev := fun i j _ a b => γ₁.ev i j a b * γ₂.ev i j a b }

@[simp]
-/
instance : Mul (OneCochain G U) where
  mul γ₁ γ₂ := { ev := fun i j _ a b => γ₁.ev i j a b * γ₂.ev i j a b }

@[simp]
/--
lemma `mul_ev` / 引理 `mul_ev`

English:
lemma mul_ev
  given: (γ₁ γ₂ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j)
  proof: rfl

中文:
引理 mul_ev
  条件: (γ₁ γ₂ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j)
  证明: rfl
-/
lemma mul_ev (γ₁ γ₂ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (γ₁ * γ₂).ev i j a b = γ₁.ev i j a b * γ₂.ev i j a b := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (OneCochain G U)
  body: { ev := fun i j _ a b => (γ.ev i j a b)⁻¹ }

@[simp]

中文:
实例 :
  签名: 取逆 (OneCochain G U)
  定义体: { ev := fun i j _ a b => (γ.ev i j a b)⁻¹ }

@[simp]
-/
instance : Inv (OneCochain G U) where
  inv γ := { ev := fun i j _ a b => (γ.ev i j a b)⁻¹ }

@[simp]
/--
lemma `inv_ev` / 引理 `inv_ev`

English:
lemma inv_ev
  given: (γ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j)
  proof: rfl

中文:
引理 inv_ev
  条件: (γ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j)
  证明: rfl
-/
lemma inv_ev (γ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (γ⁻¹).ev i j a b = (γ.ev i j a b)⁻¹ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (OneCochain G U)
  body: by ext; apply mul_assoc
  one_mul _ := by ext; apply one_mul
  mul_one _ := by ext; apply mul_one
  inv_mul_cancel _ := by ext; apply inv_mul_cancel

中文:
实例 :
  签名: 群 (OneCochain G U)
  定义体: by ext; apply mul_assoc
  one_mul _ := by ext; apply one_mul
  mul_one _ := by ext; apply mul_one
  inv_mul_cancel _ := by ext; apply inv_mul_cancel

Depends on / 依赖: inv_mul_cancel, mul_assoc, mul_one, one_mul
-/
instance : Group (OneCochain G U) where
  mul_assoc _ _ _ := by ext; apply mul_assoc
  one_mul _ := by ext; apply one_mul
  mul_one _ := by ext; apply mul_one
  inv_mul_cancel _ := by ext; apply inv_mul_cancel

end OneCochain

/--
Definition of `OneCocycle` / `OneCocycle` 的定义

English:
structure OneCocycle
  parameters: extends OneCochain G U
  extends: OneCochain G U
  axioms and operations (1):
    - ev_trans((i j k : I) ⦃T) : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k) : ev i j a b * ev j k b c = ev i k a c  [default: by aesop]

中文:
结构 OneCocycle
  参数: extends OneCochain G U
  继承: OneCochain G U
  公理与运算 (1 个):
    - ev_trans((i j k : I) ⦃T) : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k) : ev i j a b * ev j k b c = ev i k a c  [默认: by aesop]
-/
structure OneCocycle extends OneCochain G U where
  ev_trans (i j k : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k) :
      ev i j a b * ev j k b c = ev i k a c := by aesop

namespace OneCocycle

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (OneCocycle G U)
  body: OneCocycle.mk 1

@[simp]

中文:
实例 :
  签名: 幺 (OneCocycle G U)
  定义体: OneCocycle.mk 1

@[simp]

Depends on / 依赖: OneCocycle, OneCocycle.mk
-/
instance : One (OneCocycle G U) where
  one := OneCocycle.mk 1

@[simp]
/--
lemma `one_toOneCochain` / 引理 `one_toOneCochain`

English:
lemma one_toOneCochain
  statement: (1 : OneCocycle G U).toOneCochain = 1
  proof: rfl

@[simp]

中文:
引理 one_toOneCochain
  结论: (1 : OneCocycle G U).toOneCochain = 1
  证明: rfl

@[simp]
-/
lemma one_toOneCochain : (1 : OneCocycle G U).toOneCochain = 1 := rfl

@[simp]
/--
lemma `ev_refl` / 引理 `ev_refl`

English:
lemma ev_refl
  given: (γ : OneCocycle G U) (i : I) ⦃T
  statement: C⦄ (a : T ⟶ U i) :
  proof: by
  simpa using γ.ev_trans i i i a a a

中文:
引理 ev_refl
  条件: (γ : OneCocycle G U) (i : I) ⦃T
  结论: C⦄ (a : T ⟶ U i) :
  证明: by
  simpa using γ.ev_trans i i i a a a

Depends on / 依赖: ev_trans
-/
lemma ev_refl (γ : OneCocycle G U) (i : I) ⦃T : C⦄ (a : T ⟶ U i) :
    γ.ev i i a a = 1 := by
  simpa using γ.ev_trans i i i a a a

/--
lemma `ev_symm` / 引理 `ev_symm`

English:
lemma ev_symm
  given: (γ : OneCocycle G U) (i j : I) ⦃T
  statement: C⦄ (a : T ⟶ U i) (b : T ⟶ U j) :
  proof: by
  rw [← mul_left_inj (γ.ev j i b a)]; rw [γ.ev_trans i j i a b a]; rw [ev_refl]; rw [inv_mul_cancel]

中文:
引理 ev_symm
  条件: (γ : OneCocycle G U) (i j : I) ⦃T
  结论: C⦄ (a : T ⟶ U i) (b : T ⟶ U j) :
  证明: by
  rw [← mul_left_inj (γ.ev j i b a)]; rw [γ.ev_trans i j i a b a]; rw [ev_refl]; rw [inv_mul_cancel]

Depends on / 依赖: ev_refl, ev_trans, inv_mul_cancel, mul_left_inj
-/
lemma ev_symm (γ : OneCocycle G U) (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) :
    γ.ev i j a b = (γ.ev j i b a)⁻¹ := by
  rw [← mul_left_inj (γ.ev j i b a)]; rw [γ.ev_trans i j i a b a]; rw [ev_refl]; rw [inv_mul_cancel]

end OneCocycle

variable {G U}

/--
Definition of `OneCohomologyRelation` / `OneCohomologyRelation` 的定义

English:
definition OneCohomologyRelation
  signature: (γ₁ γ₂ : OneCochain G U) (α : ZeroCochain G U)
  body: forall (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j),
    G.map a.op (α i) * γ₁.ev i j a b = γ₂.ev i j a b * G.map b.op (α j)

中文:
定义 OneCohomologyRelation
  签名: (γ₁ γ₂ : OneCochain G U) (α : ZeroCochain G U)
  定义体: forall (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j),
    G.map a.op (α i) * γ₁.ev i j a b = γ₂.ev i j a b * G.map b.op (α j)

Depends on / 依赖: G.map, a.op, b.op
-/
def OneCohomologyRelation (γ₁ γ₂ : OneCochain G U) (α : ZeroCochain G U) : Prop :=
  forall (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j),
    G.map a.op (α i) * γ₁.ev i j a b = γ₂.ev i j a b * G.map b.op (α j)

namespace OneCohomologyRelation

/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: (γ : OneCochain G U)
  statement: OneCohomologyRelation γ γ 1
  proof: fun _ _ _ _ _ => by simp

中文:
引理 refl
  条件: (γ : OneCochain G U)
  结论: OneCohomologyRelation γ γ 1
  证明: fun _ _ _ _ _ => by simp
-/
lemma refl (γ : OneCochain G U) : OneCohomologyRelation γ γ 1 := fun _ _ _ _ _ => by simp

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: {γ₁ γ₂ : OneCochain G U} {α : ZeroCochain G U} (h : OneCohomologyRelation γ₁ γ₂ α)
  proof: fun i j T a b => by
  rw [← mul_left_inj (G.map b.op (α j))]; rw [mul_assoc]; rw [← h i j a b]; rw [mul_assoc]; rw [Cochain₀.inv_apply]; rw [map_inv]; rw [inv_mul_cancel_left]; rw [Cochain₀.inv_apply]; rw [map_inv]; rw [inv_mul_cancel]; rw [mul_one]

中文:
引理 symm
  条件: {γ₁ γ₂ : OneCochain G U} {α : ZeroCochain G U} (h : OneCohomologyRelation γ₁ γ₂ α)
  证明: fun i j T a b => by
  rw [← mul_left_inj (G.map b.op (α j))]; rw [mul_assoc]; rw [← h i j a b]; rw [mul_assoc]; rw [Cochain₀.inv_apply]; rw [map_inv]; rw [inv_mul_cancel_left]; rw [Cochain₀.inv_apply]; rw [map_inv]; rw [inv_mul_cancel]; rw [mul_one]

Depends on / 依赖: G.map, b.op, inv_apply, inv_mul_cancel, inv_mul_cancel_left, map_inv, mul_assoc, mul_left_inj, mul_one
-/
lemma symm {γ₁ γ₂ : OneCochain G U} {α : ZeroCochain G U} (h : OneCohomologyRelation γ₁ γ₂ α) :
    OneCohomologyRelation γ₂ γ₁ α⁻¹ := fun i j T a b => by
  rw [← mul_left_inj (G.map b.op (α j))]; rw [mul_assoc]; rw [← h i j a b]; rw [mul_assoc]; rw [Cochain₀.inv_apply]; rw [map_inv]; rw [inv_mul_cancel_left]; rw [Cochain₀.inv_apply]; rw [map_inv]; rw [inv_mul_cancel]; rw [mul_one]

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  statement: {γ₁ γ₂ γ₃ : OneCochain G U} {α β : ZeroCochain G U}
  proof: fun i j T a b => by
  dsimp
  rw [map_mul]; rw [map_mul]; rw [mul_assoc]; rw [h₁₂ i j a b]; rw [← mul_assoc]; rw [h₂₃ i j a b]; rw [mul_assoc]

中文:
引理 trans
  结论: {γ₁ γ₂ γ₃ : OneCochain G U} {α β : ZeroCochain G U}
  证明: fun i j T a b => by
  dsimp
  rw [map_mul]; rw [map_mul]; rw [mul_assoc]; rw [h₁₂ i j a b]; rw [← mul_assoc]; rw [h₂₃ i j a b]; rw [mul_assoc]

Depends on / 依赖: map_mul, mul_assoc
-/
lemma trans {γ₁ γ₂ γ₃ : OneCochain G U} {α β : ZeroCochain G U}
    (h₁₂ : OneCohomologyRelation γ₁ γ₂ α) (h₂₃ : OneCohomologyRelation γ₂ γ₃ β) :
    OneCohomologyRelation γ₁ γ₃ (β * α) := fun i j T a b => by
  dsimp
  rw [map_mul]; rw [map_mul]; rw [mul_assoc]; rw [h₁₂ i j a b]; rw [← mul_assoc]; rw [h₂₃ i j a b]; rw [mul_assoc]

end OneCohomologyRelation

namespace OneCocycle

/--
Definition of `IsCohomologous` / `IsCohomologous` 的定义

English:
definition IsCohomologous
  signature: (γ₁ γ₂ : OneCocycle G U)
  body: exists (α : ZeroCochain G U), OneCohomologyRelation γ₁.toOneCochain γ₂.toOneCochain α

中文:
定义 IsCohomologous
  签名: (γ₁ γ₂ : OneCocycle G U)
  定义体: exists (α : ZeroCochain G U), OneCohomologyRelation γ₁.toOneCochain γ₂.toOneCochain α

Depends on / 依赖: OneCohomologyRelation, ZeroCochain, toOneCochain
-/
def IsCohomologous (γ₁ γ₂ : OneCocycle G U) : Prop :=
  exists (α : ZeroCochain G U), OneCohomologyRelation γ₁.toOneCochain γ₂.toOneCochain α

variable (G U)

/--
lemma `equivalence_isCohomologous` / 引理 `equivalence_isCohomologous`

English:
lemma equivalence_isCohomologous
  proof: ⟨_, OneCohomologyRelation.refl γ.toOneCochain⟩
  symm := by
    rintro γ₁ γ₂ ⟨α, h⟩
    exact ⟨_, h.symm⟩
  trans := by
    rintro γ₁ γ₂ γ₂ ⟨α, h⟩ ⟨β, h'⟩
    exact ⟨_, h.trans h'⟩

中文:
引理 equivalence_isCohomologous
  证明: ⟨_, OneCohomologyRelation.refl γ.toOneCochain⟩
  symm := by
    rintro γ₁ γ₂ ⟨α, h⟩
    exact ⟨_, h.symm⟩
  trans := by
    rintro γ₁ γ₂ γ₂ ⟨α, h⟩ ⟨β, h'⟩
    exact ⟨_, h.trans h'⟩
-/
lemma equivalence_isCohomologous :
    _root_.Equivalence (IsCohomologous (G := G) (U := U)) where
  refl γ := ⟨_, OneCohomologyRelation.refl γ.toOneCochain⟩
  symm := by
    rintro γ₁ γ₂ ⟨α, h⟩
    exact ⟨_, h.symm⟩
  trans := by
    rintro γ₁ γ₂ γ₂ ⟨α, h⟩ ⟨β, h'⟩
    exact ⟨_, h.trans h'⟩

end OneCocycle

variable (G U) in
/--
Definition of `H1` / `H1` 的定义

English:
definition H1
  body: Quot (OneCocycle.IsCohomologous (G := G) (U := U))

中文:
定义 H1
  定义体: Quot (OneCocycle.IsCohomologous (G := G) (U := U))

Depends on / 依赖: IsCohomologous, OneCocycle, OneCocycle.IsCohomologous
-/
def H1 := Quot (OneCocycle.IsCohomologous (G := G) (U := U))

/--
Definition of `OneCocycle.class` / `OneCocycle.class` 的定义

English:
definition OneCocycle.class
  signature: (γ : OneCocycle G U)
  body: Quot.mk _ γ

中文:
定义 OneCocycle.class
  签名: (γ : OneCocycle G U)
  定义体: Quot.mk _ γ

Depends on / 依赖: Quot.mk
-/
def OneCocycle.class (γ : OneCocycle G U) : H1 G U := Quot.mk _ γ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (H1 G U)
  body: OneCocycle.class 1

中文:
实例 :
  签名: 幺 (H1 G U)
  定义体: OneCocycle.class 1

Depends on / 依赖: OneCocycle, OneCocycle.class
-/
instance : One (H1 G U) where
  one := OneCocycle.class 1

/--
lemma `OneCocycle.class_eq_iff` / 引理 `OneCocycle.class_eq_iff`

English:
lemma OneCocycle.class_eq_iff
  given: (γ₁ γ₂ : OneCocycle G U)
  proof: (equivalence_isCohomologous _ _).quot_mk_eq_iff _ _

中文:
引理 OneCocycle.class_eq_iff
  条件: (γ₁ γ₂ : OneCocycle G U)
  证明: (equivalence_isCohomologous _ _).quot_mk_eq_iff _ _

Depends on / 依赖: equivalence_isCohomologous, quot_mk_eq_iff
-/
lemma OneCocycle.class_eq_iff (γ₁ γ₂ : OneCocycle G U) :
    γ₁.class = γ₂.class ↔ γ₁.IsCohomologous γ₂ :=
  (equivalence_isCohomologous _ _).quot_mk_eq_iff _ _

/--
lemma `OneCocycle.IsCohomologous.class_eq` / 引理 `OneCocycle.IsCohomologous.class_eq`

English:
lemma OneCocycle.IsCohomologous.class_eq
  given: {γ₁ γ₂ : OneCocycle G U} (h : γ₁.IsCohomologous γ₂)
  proof: Quot.sound h

中文:
引理 OneCocycle.IsCohomologous.class_eq
  条件: {γ₁ γ₂ : OneCocycle G U} (h : γ₁.IsCohomologous γ₂)
  证明: Quot.sound h

Depends on / 依赖: Quot.sound
-/
lemma OneCocycle.IsCohomologous.class_eq {γ₁ γ₂ : OneCocycle G U} (h : γ₁.IsCohomologous γ₂) :
    γ₁.class = γ₂.class :=
  Quot.sound h

end PresheafOfGroups

end CategoryTheory
