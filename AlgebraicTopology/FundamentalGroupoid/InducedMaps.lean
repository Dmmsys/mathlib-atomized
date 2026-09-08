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
/-- Let `F` be a homotopy between two continuous maps `f g : C(X, Y)`.
Given a path `p : Path x₁ x₂` in the domain, consider the following two paths in the codomain.
One path goes along the image of `p` under `f`, then along the trajectory of `x₂` under `F`.
The other path goes along the trajectory of `x₁` under `F`, then along the image of `p` under `g`.

These two paths are homotopic. -/
/-
**Path.Homotopic.map_trans_evalAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Path.Homotopic.map_trans_evalAt {X Y : Type*} [TopologicalSpace X] [Topolo
gicalSpace Y] {f g : C(X, Y)} (F : f.Homotopy g) {x₁ x₂ : X} (p : Path x₁ x₂) : 
((p.map (map_continuous f)).trans (F.evalAt x₂)).Homotopic ((F.evalAt x₁).trans 
(p.map (map_continuous g)))
参数：X, Y；F : f.Homotopy g；p : Path x₁ x₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.prodMap_apply`：∀ {α₁ : Type u_5} {α₂ : Type u_6} {β₁ : Typ
e u_7} {β₂ : Type u_8} [inst : TopologicalSpace α₁]   [inst_1 : TopologicalSpace
 α₂] [inst_2 : To…
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `ContinuousMap.Homotopy.apply_zero`：apply_zero (F : Homotopy f₀ f₁) (x : 
X) : F (0, x) = f₀ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
· 使用定理 `ContinuousMap.Homotopy.apply_one`：apply_one (F : Homotopy f₀ f₁) (x : X)
 : F (1, x) = f₁ x
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `unitInterval.two_mul_sub_one_mem_iff`：two_mul_sub_one_mem_iff {t : Real}
 : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `unitInterval.mul_pos_mem_iff`：mul_pos_mem_iff {a t : Real} (ha : 0 < a) 
: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Let `F` be a homotopy between two continuous maps `f g : C(X, Y)`.
Given a path `p : Path x₁ x₂` in the domain, consider the following two paths in
 the codomain.
One path goes along the image of `p` under `f`, then along the trajectory of `x₂
` under `F`.
The other path goes along the trajectory of `x₁` under `F`, then along the image
 of `p` under `g`.

These two paths are homotopic.
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
/-- Given a homotopy H : f ∼ g, we have an associated natural isomorphism between the induced
functors `map f` and `map g` on fundamental groupoids. -/
/-
**FundamentalGroupoidFunctor.homotopicMapsNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Fund
amentalGroupoidFunctor`。
形式化陈述：homotopicMapsNatIso (H : ContinuousMap.Homotopy f g) : map f ⟶ map g where
 app x
参数：H : ContinuousMap.Homotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a homotopy H : f ∼ g, we have an associated natural isomorphism between th
e induced
functors `map f` and `map g` on fundamental groupoids.
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
/-
**FundamentalGroupoidFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `FundamentalGroupoidFunc
tor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : ContinuousMap.Homotopy f g) : IsIso (homotopicMapsNatIso H) :=
  NatIso.isIso_of_isIso_app _

open scoped ContinuousMap

/-- Homotopy equivalent topological spaces have equivalent fundamental groupoids. -/
/-
**FundamentalGroupoidFunctor.equivOfHomotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Fun
damentalGroupoidFunctor`。
形式化陈述：equivOfHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace 
Y] (hequiv : X ≃ₕ Y) : πₓ (.of X) ≌ πₓ (.of Y)
参数：hequiv : X ≃ₕ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyEquiv.left_inv`：∀ {X : Type u} {Y : Type v} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : ContinuousMap.Homo
topyEquiv X Y), (self.invF…
· 使用定理 `ContinuousMap.HomotopyEquiv.right_inv`：∀ {X : Type u} {Y : Type v} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : ContinuousMap.Hom
otopyEquiv X Y), (self.toFu…

--- 原说明 ---
Homotopy equivalent topological spaces have equivalent fundamental groupoids.
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

/-- The path 0 ⟶ 1 in `I` -/
/-
**unitInterval.path01** 是 Mathlib 中的一个定义，位于命名空间 `unitInterval`。
形式化陈述：path01 : Path (0 : I) 1 where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path 0 ⟶ 1 in `I`
-/
def path01 : Path (0 : I) 1 where
  toFun := id
  source' := rfl
  target' := rfl

/-- The path 0 ⟶ 1 in `ULift I` -/
/-
**unitInterval.upath01** 是 Mathlib 中的一个定义，位于命名空间 `unitInterval`。
形式化陈述：upath01 : Path (ULift.up 0 : ULift.{u} I) (ULift.up 1) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path 0 ⟶ 1 in `ULift I`
-/
def upath01 : Path (ULift.up 0 : ULift.{u} I) (ULift.up 1) where
  toFun := ULift.up
  source' := rfl
  target' := rfl

/-- The homotopy path class of 0 → 1 in `ULift I` -/
/-
**unitInterval.uhpath01** 是 Mathlib 中的一个定义，位于命名空间 `unitInterval`。
形式化陈述：uhpath01 : @fromTop (TopCat.of <| ULift.{u} I) (ULift.up (0 : I)) ⟶ fromTo
p (ULift.up 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy path class of 0 → 1 in `ULift I`
-/
def uhpath01 : @fromTop (TopCat.of <| ULift.{u} I) (ULift.up (0 : I)) ⟶ fromTop (ULift.up 1) :=
  ⟦upath01⟧

end unitInterval

namespace ContinuousMap.Homotopy

open unitInterval (uhpath01)

section Casts

/-- Abbreviation for `eqToHom` that accepts points in a topological space -/
/-
**ContinuousMap.Homotopy.hcast** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousMap.Homoto
py`。
形式化陈述：hcast {X : TopCat.{u}} {x₀ x₁ : X} (hx : x₀ = x₁) : fromTop x₀ ⟶ fromTop x
₁
参数：hx : x₀ = x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for `eqToHom` that accepts points in a topological space
-/
abbrev hcast {X : TopCat.{u}} {x₀ x₁ : X} (hx : x₀ = x₁) : fromTop x₀ ⟶ fromTop x₁ :=
  eqToHom <| FundamentalGroupoid.ext hx

@[simp]
/-
**ContinuousMap.Homotopy.hcast_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topy`。
形式化陈述：hcast_def {X : TopCat.{u}} {x₀ x₁ : X} (hx₀ : x₀ = x₁) : hcast hx₀ = eqToH
om (FundamentalGroupoid.ext hx₀)
参数：hx₀ : x₀ = x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hcast_def {X : TopCat.{u}} {x₀ x₁ : X} (hx₀ : x₀ = x₁) :
    hcast hx₀ = eqToHom (FundamentalGroupoid.ext hx₀) :=
  rfl

variable {X₁ X₂ Y : TopCat.{u}} {f : C(X₁, Y)} {g : C(X₂, Y)} {x₀ x₁ : X₁} {x₂ x₃ : X₂}
  {p : Path x₀ x₁} {q : Path x₂ x₃} (hfg : ∀ t, f (p t) = g (q t))
include hfg

/-- If `f(p(t) = g(q(t))` for two paths `p` and `q`, then the induced path homotopy classes
`f(p)` and `g(p)` are the same as well, despite having a priori different types -/
/-
**ContinuousMap.Homotopy.heq_path_of_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousMap.Homotopy`。
形式化陈述：heq_path_of_eq_image : (πₘ (TopCat.ofHom f)).map ⟦p⟧ ≍ (πₘ (TopCat.ofHom g
)).map ⟦q⟧
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.hpath_hext`：hpath_hext {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃
} (hp : forall t, p₁ t = p₂ t) : HEq (α
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f

--- 原说明 ---
If `f(p(t) = g(q(t))` for two paths `p` and `q`, then the induced path homotopy 
classes
`f(p)` and `g(p)` are the same as well, despite having a priori different types
-/
theorem heq_path_of_eq_image :
    (πₘ (TopCat.ofHom f)).map ⟦p⟧ ≍ (πₘ (TopCat.ofHom g)).map ⟦q⟧ := by
  apply Path.Homotopic.hpath_hext
  exact hfg

set_option backward.privateInPublic true in
/-
**ContinuousMap.Homotopy.start_path** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Hom
otopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem start_path : f x₀ = g x₂ := by convert! hfg 0 <;> simp only [Path.source]

set_option backward.privateInPublic true in
/-
**ContinuousMap.Homotopy.end_path** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homot
opy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem end_path : f x₁ = g x₃ := by convert! hfg 1 <;> simp only [Path.target]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**ContinuousMap.Homotopy.eq_path_of_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap.Homotopy`。
形式化陈述：eq_path_of_eq_image : (πₘ (TopCat.ofHom f)).map ⟦p⟧ = hcast (start_path hf
g) ≫ (πₘ (TopCat.ofHom g)).map ⟦q⟧ ≫ hcast (end_path hfg).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps.0.Con
tinuousMap.Homotopy.start_path`：∀ {X₁ X₂ Y : TopCat} {f : C(↑X₁, ↑Y)} {g : C(↑X₂
, ↑Y)} {x₀ x₁ : ↑X₁} {x₂ x₃ : ↑X₂} {p : Path x₀ x₁} {q : Path x₂ x₃},   (∀ (t : 
↑unitInterva…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps.0.Con
tinuousMap.Homotopy.end_path`：∀ {X₁ X₂ Y : TopCat} {f : C(↑X₁, ↑Y)} {g : C(↑X₂, 
↑Y)} {x₀ x₁ : ↑X₁} {x₂ x₃ : ↑X₂} {p : Path x₀ x₁} {q : Path x₂ x₃},   (∀ (t : ↑u
nitInterva…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FundamentalGroupoid.ext`：∀ {X : Type u_3} {x y : FundamentalGroupoid X},
 x.as = y.as → x = y
· 使用定理 `CategoryTheory.conj_eqToHom_iff_heq`：conj_eqToHom_iff_heq {W X Y Z : C} 
(f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) : f = eqToHom h ≫ g ≫ eqToHom h
'.symm ↔ f ≍ g
· 使用定理 `ContinuousMap.Homotopy.heq_path_of_eq_image`：heq_path_of_eq_image : (πₘ 
(TopCat.ofHom f)).map ⟦p⟧ ≍ (πₘ (TopCat.ofHom g)).map ⟦q⟧
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
        | \      |
    H₀  |   \ d  |  H₁
        |     \  |
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


/-- Interpret a homotopy `H : C(I × X, Y)` as a map `C(ULift I × X, Y)` -/
/-
**ContinuousMap.Homotopy.uliftMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homot
opy`。
形式化陈述：uliftMap : C(TopCat.of (ULift.{u} I × X), Y)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a homotopy `H : C(I × X, Y)` as a map `C(ULift I × X, Y)`
-/
def uliftMap : C(TopCat.of (ULift.{u} I × X), Y) :=
  ⟨fun x => H (x.1.down, x.2),
    H.continuous.comp ((continuous_uliftDown.comp continuous_fst).prodMk continuous_snd)⟩
/-
**ContinuousMap.Homotopy.ulift_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Ho
motopy`。
形式化陈述：ulift_apply (i : ULift.{u} I) (x : X) : H.uliftMap (i, x) = H (i.down, x)
参数：i : ULift.{u} I；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ulift_apply (i : ULift.{u} I) (x : X) : H.uliftMap (i, x) = H (i.down, x) :=
  rfl

/-- An abbreviation for `prodToProdTop`, with some types already in place to help the
typechecker. In particular, the first path should be on the ulifted unit interval. -/
/-
**ContinuousMap.Homotopy.prodToProdTopI** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousM
ap.Homotopy`。
形式化陈述：prodToProdTopI {a₁ a₂ : TopCat.of (ULift I)} {b₁ b₂ : X} (p₁ : fromTop a₁ 
⟶ fromTop a₂) (p₂ : fromTop b₁ ⟶ fromTop b₂)
参数：ULift I；p₁ : fromTop a₁ ⟶ fromTop a₂；p₂ : fromTop b₁ ⟶ fromTop b₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `prodToProdTop`, with some types already in place to help th
e
typechecker. In particular, the first path should be on the ulifted unit interva
l.
-/
abbrev prodToProdTopI {a₁ a₂ : TopCat.of (ULift I)} {b₁ b₂ : X} (p₁ : fromTop a₁ ⟶ fromTop a₂)
    (p₂ : fromTop b₁ ⟶ fromTop b₂) :=
  (prodToProdTop (TopCat.of <| ULift I) X).map (X := (⟨a₁⟩, ⟨b₁⟩)) (Y := (⟨a₂⟩, ⟨b₂⟩)) (p₁, p₂)

/-- The diagonal path `d` of a homotopy `H` on a path `p` -/
/-
**ContinuousMap.Homotopy.diagonalPath** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.H
omotopy`。
形式化陈述：diagonalPath : fromTop (H (0, x₀)) ⟶ fromTop (H (1, x₁))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal path `d` of a homotopy `H` on a path `p`
-/
def diagonalPath : fromTop (H (0, x₀)) ⟶ fromTop (H (1, x₁)) :=
  (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI uhpath01 p)

/-- The diagonal path, but starting from `f x₀` and going to `g x₁` -/
/-
**ContinuousMap.Homotopy.diagonalPath'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.
Homotopy`。
形式化陈述：diagonalPath' : fromTop (f x₀) ⟶ fromTop (g x₁)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal path, but starting from `f x₀` and going to `g x₁`
-/
def diagonalPath' : fromTop (f x₀) ⟶ fromTop (g x₁) :=
  hcast (H.apply_zero x₀).symm ≫ H.diagonalPath p ≫ hcast (H.apply_one x₁)

/-- Proof that `f(p) = H(0 ⟶ 0, p)`, with the appropriate casts -/
/-
**ContinuousMap.Homotopy.apply_zero_path** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p.Homotopy`。
形式化陈述：apply_zero_path : (πₘ (TopCat.ofHom f)).map p = hcast (H.apply_zero x₀).sy
mm ≫ (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI (𝟙 (@fromTop (TopCat.of 
_) (ULift.up 0))) p) ≫ hcast (H.apply_zero x₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.Homotopy.apply_zero`：apply_zero (F : Homotopy f₀ f₁) (x : 
X) : F (0, x) = f₀ x
· 使用定理 `ContinuousMap.Homotopy.eq_path_of_eq_image`：eq_path_of_eq_image : (πₘ (T
opCat.ofHom f)).map ⟦p⟧ = hcast (start_path hfg) ≫ (πₘ (TopCat.ofHom g)).map ⟦q⟧
 ≫ hcast (end_path hfg).symm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.prod_coe`：prod_coe (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : ⇑(γ₁.prod 
γ₂) = fun t => (γ₁ t, γ₂ t)
· 使用定理 `ContinuousMap.Homotopy.ulift_apply`：ulift_apply (i : ULift.{u} I) (x : X
) : H.uliftMap (i, x) = H (i.down, x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Path.refl_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (x
_1 : ↑unitInterval), (Path.refl x) x_1 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Proof that `f(p) = H(0 ⟶ 0, p)`, with the appropriate casts
-/
theorem apply_zero_path : (πₘ (TopCat.ofHom f)).map p = hcast (H.apply_zero x₀).symm ≫
    (πₘ (TopCat.ofHom H.uliftMap)).map
      (prodToProdTopI (𝟙 (@fromTop (TopCat.of _) (ULift.up 0))) p) ≫
    hcast (H.apply_zero x₁) :=
  Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe, ulift_apply H]
    simp

/-- Proof that `g(p) = H(1 ⟶ 1, p)`, with the appropriate casts -/
/-
**ContinuousMap.Homotopy.apply_one_path** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
.Homotopy`。
形式化陈述：apply_one_path : (πₘ (TopCat.ofHom g)).map p = hcast (H.apply_one x₀).symm
 ≫ (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI (𝟙 (@fromTop (TopCat.of _)
 (ULift.up 1))) p) ≫ hcast (H.apply_one x₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.Homotopy.apply_one`：apply_one (F : Homotopy f₀ f₁) (x : X)
 : F (1, x) = f₁ x
· 使用定理 `ContinuousMap.Homotopy.eq_path_of_eq_image`：eq_path_of_eq_image : (πₘ (T
opCat.ofHom f)).map ⟦p⟧ = hcast (start_path hfg) ≫ (πₘ (TopCat.ofHom g)).map ⟦q⟧
 ≫ hcast (end_path hfg).symm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.prod_coe`：prod_coe (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : ⇑(γ₁.prod 
γ₂) = fun t => (γ₁ t, γ₂ t)
· 使用定理 `ContinuousMap.Homotopy.ulift_apply`：ulift_apply (i : ULift.{u} I) (x : X
) : H.uliftMap (i, x) = H (i.down, x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Path.refl_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (x
_1 : ↑unitInterval), (Path.refl x) x_1 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Proof that `g(p) = H(1 ⟶ 1, p)`, with the appropriate casts
-/
theorem apply_one_path : (πₘ (TopCat.ofHom g)).map p = hcast (H.apply_one x₀).symm ≫
    (πₘ (TopCat.ofHom H.uliftMap)).map
      (prodToProdTopI (𝟙 (@fromTop (TopCat.of _) (ULift.up 1))) p) ≫
    hcast (H.apply_one x₁) :=
  Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe, ulift_apply H]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Proof that `H.evalAt x = H(0 ⟶ 1, x ⟶ x)`, with the appropriate casts -/
/-
**ContinuousMap.Homotopy.evalAt_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topy`。
形式化陈述：evalAt_eq (x : X) : ⟦H.evalAt x⟧ = hcast (H.apply_zero x).symm ≫ (πₘ (TopC
at.ofHom H.uliftMap)).map (prodToProdTopI uhpath01 (𝟙 (fromTop x))) ≫ hcast (H.a
pply_one x).symm.symm
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.Homotopy.apply_zero`：apply_zero (F : Homotopy f₀ f₁) (x : 
X) : F (0, x) = f₀ x
· 使用定理 `ContinuousMap.Homotopy.apply_one`：apply_one (F : Homotopy f₀ f₁) (x : X)
 : F (1, x) = f₁ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FundamentalGroupoid.ext`：∀ {X : Type u_3} {x y : FundamentalGroupoid X},
 x.as = y.as → x = y
· 使用定理 `CategoryTheory.conj_eqToHom_iff_heq`：conj_eqToHom_iff_heq {W X Y Z : C} 
(f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) : f = eqToHom h ≫ g ≫ eqToHom h
'.symm ↔ f ≍ g
· 使用定理 `Path.Homotopic.hpath_hext`：hpath_hext {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃
} (hp : forall t, p₁ t = p₂ t) : HEq (α
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f

--- 原说明 ---
Proof that `H.evalAt x = H(0 ⟶ 1, x ⟶ x)`, with the appropriate casts
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
/-
**ContinuousMap.Homotopy.eq_diag_path** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.H
omotopy`。
形式化陈述：eq_diag_path : (πₘ (TopCat.ofHom f)).map p ≫ ⟦H.evalAt x₁⟧ = H.diagonalPat
h' p ∧ (⟦H.evalAt x₀⟧ ≫ (πₘ (TopCat.ofHom g)).map p : fromTop (f x₀) ⟶ fromTop (
g x₁)) = H.diagonalPath' p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.Homotopy.apply_zero`：apply_zero (F : Homotopy f₀ f₁) (x : 
X) : F (0, x) = f₀ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.Homotopy.apply_zero_path`：apply_zero_path : (πₘ (TopCat.of
Hom f)).map p = hcast (H.apply_zero x₀).symm ≫ (πₘ (TopCat.ofHom H.uliftMap)).ma
p (prodToProdTopI (𝟙 (@fromT…
· 使用定理 `ContinuousMap.Homotopy.apply_one`：apply_one (F : Homotopy f₀ f₁) (x : X)
 : F (1, x) = f₁ x
· 使用定理 `ContinuousMap.Homotopy.apply_one_path`：apply_one_path : (πₘ (TopCat.ofHo
m g)).map p = hcast (H.apply_one x₀).symm ≫ (πₘ (TopCat.ofHom H.uliftMap)).map (
prodToProdTopI (𝟙 (@fromTop…
· 使用定理 `ContinuousMap.Homotopy.evalAt_eq`：evalAt_eq (x : X) : ⟦H.evalAt x⟧ = hca
st (H.apply_zero x).symm ≫ (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI uh
path01 (𝟙 (fromTop x))…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem eq_diag_path : (πₘ (TopCat.ofHom f)).map p ≫ ⟦H.evalAt x₁⟧ = H.diagonalPath' p ∧
    (⟦H.evalAt x₀⟧ ≫ (πₘ (TopCat.ofHom g)).map p :
    fromTop (f x₀) ⟶ fromTop (g x₁)) = H.diagonalPath' p := by
  rw [H.apply_zero_path, H.apply_one_path, H.evalAt_eq]
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

