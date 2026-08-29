/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.Category.FinPartOrd
public import Mathlib.Order.Category.LinOrd

/-!
# Nonempty finite linear orders

This defines `NonemptyFinLinOrd`, the category of nonempty finite linear
orders with monotone maps. This is the index category for simplicial objects.

Note: `NonemptyFinLinOrd` is *not* a subcategory of `FinBddDistLat` because its morphisms do not
preserve `⊥` and `⊤`.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

/--
Definition of `NonemptyFinLinOrd` / `NonemptyFinLinOrd` 的定义

English:
structure NonemptyFinLinOrd
  parameters: extends LinOrd
  extends: LinOrd
  axioms and operations (2):
    - [nonempty : Nonempty carrier]
    - [fintype : Fintype carrier]

中文:
结构 NonemptyFinLinOrd
  参数: extends LinOrd
  继承: LinOrd
  公理与运算 (2 个):
    - [nonempty : Nonempty carrier]
    - [fintype : Fintype carrier]
-/
structure NonemptyFinLinOrd extends LinOrd where
  [nonempty : Nonempty carrier]
  [fintype : Fintype carrier]

attribute [instance] NonemptyFinLinOrd.nonempty NonemptyFinLinOrd.fintype

namespace NonemptyFinLinOrd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort NonemptyFinLinOrd (Type _)
  body: X.carrier

中文:
实例 :
  签名: CoeSort NonemptyFinLinOrd (Type _)
  定义体: X.carrier

Depends on / 依赖: X.carrier, carrier
-/
instance : CoeSort NonemptyFinLinOrd (Type _) where
  coe X := X.carrier

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory NonemptyFinLinOrd
  body: inferInstanceAs Category (InducedCategory _ toLinOrd)

中文:
实例 :
  签名: LargeCategory NonemptyFinLinOrd
  定义体: inferInstanceAs Category (InducedCategory _ toLinOrd)

Depends on / 依赖: Category, InducedCategory, toLinOrd
-/
instance : LargeCategory NonemptyFinLinOrd :=
inferInstanceAs Category (InducedCategory _ toLinOrd)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory NonemptyFinLinOrd (· ->o ·)
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toLinOrd) _

中文:
实例 :
  签名: ConcreteCategory NonemptyFinLinOrd (· ->o ·)
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toLinOrd) _

Depends on / 依赖: Action, Action.forget_map, ConcreteCategory, FDRep.isoToLinearEquiv, FGModuleCat, FGModuleCat.Iso.conj_hom_eq_conj, Functor, Functor.mapIso_hom, InducedCategory, Iso.conj_apply, ModuleCat, ModuleCat.hom_ext_iff, ModuleCat.hom_ofHom, cat_disch, conj_apply, conj_hom_eq_conj, forget_map, hom_ext_iff, hom_ofHom, i.hom.comm
-/
instance : ConcreteCategory NonemptyFinLinOrd (· ->o ·) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toLinOrd) _

instance (X : NonemptyFinLinOrd) : BoundedOrder X :=
  Fintype.toBoundedOrder X

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α]
  body: α

中文:
缩写 of
  签名: (α : 类型) [Nonempty α] [Fintype α] [LinearOrder α]
  定义体: α
-/
abbrev of (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α] : NonemptyFinLinOrd where
  carrier := α

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [Nonempty α] [Fintype α] [LinearOrder α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [Nonempty α] [Fintype α] [LinearOrder α] : ↥(of α) = α :=
  rfl

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X]
  body: ConcreteCategory.ofHom (C := NonemptyFinLinOrd) f

@[simp]

中文:
缩写 ofHom
  签名: {X Y : 类型u} [Nonempty X] [LinearOrder X] [Fintype X]
  定义体: ConcreteCategory.ofHom (C := NonemptyFinLinOrd) f

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, NonemptyFinLinOrd
-/
abbrev ofHom {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X]
    [Nonempty Y] [LinearOrder Y] [Fintype Y] (f : X ->o Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := NonemptyFinLinOrd) f

@[simp]
/--
lemma `hom_hom_id` / 引理 `hom_hom_id`

English:
lemma hom_hom_id
  given: {X : NonemptyFinLinOrd}
  statement: (𝟙 X : X ⟶ X).hom.hom = OrderHom.id
  proof: rfl

中文:
引理 hom_hom_id
  条件: {X : NonemptyFinLinOrd}
  结论: (𝟙 X : X ⟶ X).hom.hom = OrderHom.id
  证明: rfl
-/
lemma hom_hom_id {X : NonemptyFinLinOrd} : (𝟙 X : X ⟶ X).hom.hom = OrderHom.id := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : NonemptyFinLinOrd) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : NonemptyFinLinOrd) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : NonemptyFinLinOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_hom_comp` / 引理 `hom_hom_comp`

English:
lemma hom_hom_comp
  given: {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_hom_comp
  条件: {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_hom_comp {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : NonemptyFinLinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : NonemptyFinLinOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom)
  statement: f = g
  proof: InducedCategory.hom_ext (ConcreteCategory.ext hf)

@[simp]

中文:
引理 hom_ext
  条件: {X Y : NonemptyFinLinOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom)
  结论: f = g
  证明: InducedCategory.hom_ext (ConcreteCategory.ext hf)

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext, InducedCategory, InducedCategory.hom_ext, hom_ext
-/
lemma hom_ext {X Y : NonemptyFinLinOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (ConcreteCategory.ext hf)

@[simp]
/--
lemma `hom_hom_ofHom` / 引理 `hom_hom_ofHom`

English:
lemma hom_hom_ofHom
  statement: {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X] [Nonempty Y]
  proof: rfl

@[simp]

中文:
引理 hom_hom_ofHom
  结论: {X Y : 类型u} [Nonempty X] [LinearOrder X] [Fintype X] [Nonempty Y]
  证明: rfl

@[simp]
-/
lemma hom_hom_ofHom {X Y : Type u} [Nonempty X] [LinearOrder X] [Fintype X] [Nonempty Y]
    [LinearOrder Y] [Fintype Y] (f : X ->o Y) :
  (ofHom f).hom.hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : NonemptyFinLinOrd} (f : X ⟶ Y)
  proof: rfl

中文:
引理 ofHom_hom
  条件: {X Y : NonemptyFinLinOrd} (f : X ⟶ Y)
  证明: rfl
-/
lemma ofHom_hom {X Y : NonemptyFinLinOrd} (f : X ⟶ Y) :
    ofHom f.hom.hom = f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited NonemptyFinLinOrd
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: Inhabited NonemptyFinLinOrd
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited NonemptyFinLinOrd :=
  ⟨of PUnit⟩

/--
Instance `hasForgetToLinOrd` / 实例 `hasForgetToLinOrd`

English:
instance hasForgetToLinOrd
  signature: : HasForget₂ NonemptyFinLinOrd LinOrd
  body: inferInstanceAs HasForget₂ (InducedCategory _ toLinOrd) _

中文:
实例 hasForgetToLinOrd
  签名: : HasForget₂ NonemptyFinLinOrd LinOrd
  定义体: inferInstanceAs HasForget₂ (InducedCategory _ toLinOrd) _

Depends on / 依赖: InducedCategory, toLinOrd
-/
instance hasForgetToLinOrd : HasForget₂ NonemptyFinLinOrd LinOrd :=
inferInstanceAs HasForget₂ (InducedCategory _ toLinOrd) _

/--
Instance `hasForgetToFinPartOrd` / 实例 `hasForgetToFinPartOrd`

English:
instance hasForgetToFinPartOrd
  signature: : HasForget₂ NonemptyFinLinOrd FinPartOrd where
  body: .of X
  forget₂.map f := FinPartOrd.ofHom f.hom.hom

中文:
实例 hasForgetToFinPartOrd
  签名: : HasForget₂ NonemptyFinLinOrd FinPartOrd where
  定义体: .of X
  forget₂.map f := FinPartOrd.ofHom f.hom.hom
-/
instance hasForgetToFinPartOrd : HasForget₂ NonemptyFinLinOrd FinPartOrd where
  forget₂.obj X := .of X
  forget₂.map f := FinPartOrd.ofHom f.hom.hom

/-- Constructs an equivalence between nonempty finite linear orders from an order isomorphism
between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : NonemptyFinLinOrd.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 Iso.mk
  签名: {α β : NonemptyFinLinOrd.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def Iso.mk {α β : NonemptyFinLinOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd where
  body: of Xᵒᵈ
  map f := ofHom f.hom.hom.dual

中文:
定义 dual
  签名: : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.hom.dual

Depends on / 依赖: Module, Module.injective_iff_injective_object, Module.injective_of_isSemisimpleRing, Rep.equivalenceModuleMonoidAlgebra.map_injective_iff, equivalenceModuleMonoidAlgebra, injective_iff_injective_object, injective_of_isSemisimpleRing, map_injective_iff
-/
def dual : NonemptyFinLinOrd ⥤ NonemptyFinLinOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.hom.dual

/-- The equivalence between `NonemptyFinLinOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : NonemptyFinLinOrd ≌ NonemptyFinLinOrd where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : NonemptyFinLinOrd ≌ NonemptyFinLinOrd where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

Depends on / 依赖: IsProjective, IsProjective.iff_projective, Module, Module.projective_of_isSemisimpleRing, Rep.equivalenceModuleMonoidAlgebra.map_projective_iff, equivalenceModuleMonoidAlgebra, iff_projective, map_projective_iff, projective_of_isSemisimpleRing
-/
def dualEquiv : NonemptyFinLinOrd ≌ NonemptyFinLinOrd where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

/--
theorem `mono_iff_injective` / 定理 `mono_iff_injective`

English:
theorem mono_iff_injective
  given: {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B)
  proof: by
  refine ⟨?_, ConcreteCategory.mono_of_injective f⟩
  intro _ a₁ a₂ h
  let X := of (ULift (Fin 1))
  let g₁ : X ⟶ A := ofHom ⟨fun _ => a₁, fun _ _ _ => by rfl⟩
  let g₂ : X ⟶ A := ofHom ⟨fun _ => a₂, fun _ _ _ => by rfl⟩
  change g₁ (ULift.up (0 : Fin 1)) = g₂ (ULift.up (0 : Fin 1))
  have eq : 

中文:
定理 mono_iff_injective
  条件: {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B)
  证明: by
  refine ⟨?_, ConcreteCategory.mono_of_injective f⟩
  intro _ a₁ a₂ h
  let X := of (ULift (Fin 1))
  let g₁ : X ⟶ A := ofHom ⟨fun _ => a₁, fun _ _ _ => by rfl⟩
  let g₂ : X ⟶ A := ofHom ⟨fun _ => a₂, fun _ _ _ => by rfl⟩
  change g₁ (ULift.up (0 : Fin 1)) = g₂ (ULift.up (0 : Fin 1))
  have eq : 

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, ULift.up, cancel_mono, mono_of_injective
-/
theorem mono_iff_injective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Mono f ↔ Function.Injective f := by
  refine ⟨?_, ConcreteCategory.mono_of_injective f⟩
  intro _ a₁ a₂ h
  let X := of (ULift (Fin 1))
  let g₁ : X ⟶ A := ofHom ⟨fun _ => a₁, fun _ _ _ => by rfl⟩
  let g₂ : X ⟶ A := ofHom ⟨fun _ => a₂, fun _ _ _ => by rfl⟩
  change g₁ (ULift.up (0 : Fin 1)) = g₂ (ULift.up (0 : Fin 1))
  have eq : g₁ ≫ f = g₂ ≫ f := by
    ext
    exact h
  rw [cancel_mono] at eq
  rw [eq]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  given: {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B)
  proof: by
  constructor
  · intro
    dsimp only [Function.Surjective]
    by_contra! ⟨m, hm⟩
    let Y := of (ULift (Fin 2))
    let p₁ : B ⟶ Y := ofHom
      ⟨fun b => if b < m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin

中文:
定理 epi_iff_surjective
  条件: {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B)
  证明: by
  constructor
  · intro
    dsimp only [Function.Surjective]
    by_contra! ⟨m, hm⟩
    let Y := of (ULift (Fin 2))
    let p₁ : B ⟶ Y := ofHom
      ⟨fun b => if b < m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin

Depends on / 依赖: Fin.zero_le, Function, Function.Surjective, Surjective, ULift.up, any_goals, h.trans, lt_of_le_of_lt, split_ifs, zero_le
-/
theorem epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · intro
    dsimp only [Function.Surjective]
    by_contra! ⟨m, hm⟩
    let Y := of (ULift (Fin 2))
    let p₁ : B ⟶ Y := ofHom
      ⟨fun b => if b < m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (lt_of_le_of_lt h h₂)
        · rfl⟩
    let p₂ : B ⟶ Y := ofHom
      ⟨fun b => if b <= m then ULift.up 0 else ULift.up 1, fun x₁ x₂ h => by
        simp only
        split_ifs with h₁ h₂ h₂
        any_goals apply Fin.zero_le
        · exfalso
          exact h₁ (h.trans h₂)
        · rfl⟩
    have h : p₁ m = p₂ m := by
      congr
      rw [← cancel_epi f]
      ext a : 3
      simp only [p₁, p₂, hom_hom_comp, OrderHom.comp_coe, Function.comp_apply]
      change ite _ _ _ = ite _ _ _
      split_ifs with h₁ h₂ h₂
      any_goals rfl
      · exfalso
        exact h₂ (le_of_lt h₁)
      · exfalso
        exact hm a (eq_of_le_of_not_lt h₂ h₁)
    simp [Y, p₁, p₂, ConcreteCategory.hom_ofHom] at h
  · intro h
    exact ConcreteCategory.epi_of_surjective f h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SplitEpiCategory NonemptyFinLinOrd.{u}
  body: ⟨fun {X Y} f hf => by
    have H : forall y : Y, Nonempty (f ⁻¹' {y}) := by
      rw [epi_iff_surjective] at hf
      intro y
      exact Nonempty.intro ⟨(hf y).choose, (hf y).choose_spec⟩
    let φ : Y -> X := fun y => (H y).some.1
    have hφ : forall y : Y, f (φ y) = y := fun y => (H y).some.2
  

中文:
实例 :
  签名: SplitEpiCategory NonemptyFinLinOrd.{u}
  定义体: ⟨fun {X Y} f hf => by
    have H : forall y : Y, Nonempty (f ⁻¹' {y}) := by
      rw [epi_iff_surjective] at hf
      intro y
      exact Nonempty.intro ⟨(hf y).choose, (hf y).choose_spec⟩
    let φ : Y -> X := fun y => (H y).some.1
    have hφ : forall y : Y, f (φ y) = y := fun y => (H y).some.2
  

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, Nonempty, Nonempty.intro, choose_spec, contrapose, epi_iff_surjective, f.hom, lt_of_le_of_ne, not_le
-/
instance : SplitEpiCategory NonemptyFinLinOrd.{u} :=
  ⟨fun {X Y} f hf => by
    have H : forall y : Y, Nonempty (f ⁻¹' {y}) := by
      rw [epi_iff_surjective] at hf
      intro y
      exact Nonempty.intro ⟨(hf y).choose, (hf y).choose_spec⟩
    let φ : Y -> X := fun y => (H y).some.1
    have hφ : forall y : Y, f (φ y) = y := fun y => (H y).some.2
    refine IsSplitEpi.mk' ⟨ofHom ⟨φ, ?_⟩, ?_⟩
    swap
    · ext b
      apply hφ
    · intro a b
      contrapose
      intro h
      simp only [not_le] at h ⊢
      suffices b <= a by
        apply lt_of_le_of_ne this
        rintro rfl
        exfalso
        simp at h
      have H : f (φ b) <= f (φ a) := f.hom.hom.monotone (le_of_lt h)
      simpa only [hφ] using H⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasStrongEpiMonoFactorisations NonemptyFinLinOrd.{u}
  body: ⟨fun {X Y} f => by
    let I := of (Set.image f ⊤)
    let e : X ⟶ I := ofHom ⟨fun x => ⟨f x, ⟨x, by tauto⟩⟩, fun x₁ x₂ h => f.hom.hom.monotone h⟩
    let m : I ⟶ Y := ofHom ⟨fun y => y.1, by tauto⟩
    have : Epi e := by
      rw [epi_iff_surjective]
      rintro ⟨_, y, h, rfl⟩
      exact ⟨y, rfl⟩

中文:
实例 :
  签名: HasStrongEpiMonoFactorisations NonemptyFinLinOrd.{u}
  定义体: ⟨fun {X Y} f => by
    let I := of (Set.image f ⊤)
    let e : X ⟶ I := ofHom ⟨fun x => ⟨f x, ⟨x, by tauto⟩⟩, fun x₁ x₂ h => f.hom.hom.monotone h⟩
    let m : I ⟶ Y := ofHom ⟨fun y => y.1, by tauto⟩
    have : Epi e := by
      rw [epi_iff_surjective]
      rintro ⟨_, y, h, rfl⟩
      exact ⟨y, rfl⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, Set.image, StrongEpi, Subtype, Subtype.ext, epi_iff_surjective, f.hom.hom.monotone, mono_of_injective, monotone, strongEpi_of_epi
-/
instance : HasStrongEpiMonoFactorisations NonemptyFinLinOrd.{u} :=
  ⟨fun {X Y} f => by
    let I := of (Set.image f ⊤)
    let e : X ⟶ I := ofHom ⟨fun x => ⟨f x, ⟨x, by tauto⟩⟩, fun x₁ x₂ h => f.hom.hom.monotone h⟩
    let m : I ⟶ Y := ofHom ⟨fun y => y.1, by tauto⟩
    have : Epi e := by
      rw [epi_iff_surjective]
      rintro ⟨_, y, h, rfl⟩
      exact ⟨y, rfl⟩
    have : StrongEpi e := strongEpi_of_epi e
    have : Mono m := ConcreteCategory.mono_of_injective _ (fun x y h => Subtype.ext h)
    exact ⟨⟨I, m, e, rfl⟩⟩⟩

end NonemptyFinLinOrd

/--
theorem `nonemptyFinLinOrd_dual_comp_forget_to_linOrd` / 定理 `nonemptyFinLinOrd_dual_comp_forget_to_linOrd`

English:
theorem nonemptyFinLinOrd_dual_comp_forget_to_linOrd
  proof: rfl

中文:
定理 nonemptyFinLinOrd_dual_comp_forget_to_linOrd
  证明: rfl
-/
theorem nonemptyFinLinOrd_dual_comp_forget_to_linOrd :
    NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd LinOrd =
      forget₂ NonemptyFinLinOrd LinOrd ⋙ LinOrd.dual :=
  rfl

/--
Definition of `nonemptyFinLinOrdDualCompForgetToFinPartOrd` / `nonemptyFinLinOrdDualCompForgetToFinPartOrd` 的定义

English:
definition nonemptyFinLinOrdDualCompForgetToFinPartOrd
  signature: :
  body: FinPartOrd.ofHom OrderHom.id
  inv.app X := FinPartOrd.ofHom OrderHom.id

中文:
定义 nonemptyFinLinOrdDualCompForgetToFinPartOrd
  签名: :
  定义体: FinPartOrd.ofHom OrderHom.id
  inv.app X := FinPartOrd.ofHom OrderHom.id

Depends on / 依赖: FinPartOrd, FinPartOrd.ofHom, OrderHom, OrderHom.id
-/
def nonemptyFinLinOrdDualCompForgetToFinPartOrd :
    NonemptyFinLinOrd.dual ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ≅
      forget₂ NonemptyFinLinOrd FinPartOrd ⋙ FinPartOrd.dual where
  hom.app X := FinPartOrd.ofHom OrderHom.id
  inv.app X := FinPartOrd.ofHom OrderHom.id

/--
Definition of `Fin.homSucc` / `Fin.homSucc` 的定义

English:
definition Fin.homSucc
  signature: {n} (i : Fin n)
  body: homOfLE (Fin.castSucc_le_succ i)

@[deprecated (since := "2026-07-18")]
alias Fin.hom_succ := Fin.homSucc

中文:
定义 Fin.homSucc
  签名: {n} (i : Fin n)
  定义体: homOfLE (Fin.castSucc_le_succ i)

@[deprecated (since := "2026-07-18")]
alias Fin.hom_succ := Fin.homSucc

Depends on / 依赖: Fin.castSucc_le_succ, castSucc_le_succ, homOfLE
-/
def Fin.homSucc {n} (i : Fin n) : i.castSucc ⟶ i.succ := homOfLE (Fin.castSucc_le_succ i)

@[deprecated (since := "2026-07-18")]
alias Fin.hom_succ := Fin.homSucc
