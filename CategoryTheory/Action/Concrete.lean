/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Constructors for `Action V G` for some concrete categories

We construct `Action (Type*) G` from a `[MulAction G X]` instance and give some applications.
-/

@[expose] public section

assert_not_exists Field

universe u v

open CategoryTheory Limits

namespace TypeCat

instance (X : Type u) : CoeFun (End X) (fun _ => X -> X) := (inferInstance : CoeFun (X ⟶ X) _)

/-- The group isomorphism between `Function.End X` and `CategoryTheory.End X`. -/
@[simps apply symm_apply]
/--
Definition of `endEquiv` / `endEquiv` 的定义

English:
definition endEquiv
  signature: (X : Type u)
  body: ↾f
  invFun f := (ConcreteCategory.hom f : _ -> _)
  left_inv := by intro; rfl
  right_inv := by intro; rfl
  map_mul' := by aesop

中文:
定义 endEquiv
  签名: (X : 类型u)
  定义体: ↾f
  invFun f := (ConcreteCategory.hom f : _ -> _)
  left_inv := by intro; rfl
  right_inv := by intro; rfl
  map_mul' := by aesop
-/
def endEquiv (X : Type u) : Function.End X ≃* End X where
  toFun f := ↾f
  invFun f := (ConcreteCategory.hom f : _ -> _)
  left_inv := by intro; rfl
  right_inv := by intro; rfl
  map_mul' := by aesop

end TypeCat

namespace Action

section
variable {G : Type u} [Group G] {A : Action (Type u) G}

@[simp]
/--
theorem `ρ_inv_self_apply` / 定理 `ρ_inv_self_apply`

English:
theorem ρ_inv_self_apply
  given: (g : G) (x : A.V)
  proof: show ConcreteCategory.hom (A.ρ g⁻¹ * A.ρ g) x = x by simp [← map_mul]

@[simp]

中文:
定理 ρ_inv_self_apply
  条件: (g : G) (x : A.V)
  证明: show ConcreteCategory.hom (A.ρ g⁻¹ * A.ρ g) x = x by simp [← map_mul]

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, map_mul
-/
theorem ρ_inv_self_apply (g : G) (x : A.V) :
    ConcreteCategory.hom ((A.ρ) g⁻¹) (ConcreteCategory.hom (A.ρ g) x) = x :=
  show ConcreteCategory.hom (A.ρ g⁻¹ * A.ρ g) x = x by simp [← map_mul]

@[simp]
/--
theorem `ρ_self_inv_apply` / 定理 `ρ_self_inv_apply`

English:
theorem ρ_self_inv_apply
  given: (g : G) (x : A.V)
  proof: show ConcreteCategory.hom (A.ρ g * A.ρ g⁻¹) x = x by simp [← map_mul]

中文:
定理 ρ_self_inv_apply
  条件: (g : G) (x : A.V)
  证明: show ConcreteCategory.hom (A.ρ g * A.ρ g⁻¹) x = x by simp [← map_mul]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, map_mul
-/
theorem ρ_self_inv_apply (g : G) (x : A.V) :
    ConcreteCategory.hom (A.ρ g) (ConcreteCategory.hom (A.ρ g⁻¹) x) = x :=
  show ConcreteCategory.hom (A.ρ g * A.ρ g⁻¹) x = x by simp [← map_mul]

end

/-- Bundles a type `H` with a multiplicative action of `G` as an `Action`. -/
@[simps -isSimp]
/--
Definition of `ofMulAction` / `ofMulAction` 的定义

English:
definition ofMulAction
  signature: (G : Type*) (H : Type u) [Monoid G] [MulAction G H]
  body: H
  ρ := (TypeCat.endEquiv _).toMonoidHom.comp (@MulAction.toEndHom _ _ _ (by assumption))

@[simp]

中文:
定义 ofMulAction
  签名: (G : 类型) (H : 类型u) [Monoid G] [MulAction G H]
  定义体: H
  ρ := (TypeCat.endEquiv _).toMonoidHom.comp (@MulAction.toEndHom _ _ _ (by assumption))

@[simp]
-/
def ofMulAction (G : Type*) (H : Type u) [Monoid G] [MulAction G H] :
    Action (Type u) G where
  V := H
  ρ := (TypeCat.endEquiv _).toMonoidHom.comp (@MulAction.toEndHom _ _ _ (by assumption))

@[simp]
/--
theorem `ofMulAction_apply` / 定理 `ofMulAction_apply`

English:
theorem ofMulAction_apply
  given: {G : Type*} {H : Type*} [Monoid G] [MulAction G H] (g : G) (x : H)
  proof: rfl

中文:
定理 ofMulAction_apply
  条件: {G : 类型} {H : 类型} [Monoid G] [MulAction G H] (g : G) (x : H)
  证明: rfl
-/
theorem ofMulAction_apply {G : Type*} {H : Type*} [Monoid G] [MulAction G H] (g : G) (x : H) :
    (ofMulAction G H).ρ g x = (g • x : H) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ofMulActionLimitCone` / `ofMulActionLimitCone` 的定义

English:
definition ofMulActionLimitCone
  signature: {ι : Type v} (G : Type max v u) [Monoid G] (F : ι -> Type max v u)
  body: { pt := Action.ofMulAction G (forall i : ι, F i)
      π := Discrete.natTrans (fun i => ⟨↾fun x => x i.as, fun _ => rfl⟩) }
  isLimit :=
    { lift := fun s =>
        { hom := ↾fun x i => (s.π.app ⟨i⟩).hom x
          comm := fun g => by
            ext x
            funext j
            exact Conc

中文:
定义 ofMulActionLimitCone
  签名: {ι : 类型v} (G : Type max v u) [Monoid G] (F : ι -> Type max v u)
  定义体: { pt := Action.ofMulAction G (forall i : ι, F i)
      π := Discrete.natTrans (fun i => ⟨↾fun x => x i.as, fun _ => rfl⟩) }
  isLimit :=
    { lift := fun s =>
        { hom := ↾fun x i => (s.π.app ⟨i⟩).hom x
          comm := fun g => by
            ext x
            funext j
            exact Conc

Depends on / 依赖: Action, Action.ofMulAction, ConcreteCategory, ConcreteCategory.congr_hom, ContinuousSMul, Discrete, Discrete.natTrans, ObjectProperty, ObjectProperty.isoMk, X.obj.V, congr_hom, exists_lift_of_continuous, i.as, isLimit, natTrans, ofMulAction
-/
def ofMulActionLimitCone {ι : Type v} (G : Type max v u) [Monoid G] (F : ι -> Type max v u)
    [forall i : ι, MulAction G (F i)] :
    LimitCone (Discrete.functor fun i : ι => Action.ofMulAction G (F i)) where
  cone :=
    { pt := Action.ofMulAction G (forall i : ι, F i)
      π := Discrete.natTrans (fun i => ⟨↾fun x => x i.as, fun _ => rfl⟩) }
  isLimit :=
    { lift := fun s =>
        { hom := ↾fun x i => (s.π.app ⟨i⟩).hom x
          comm := fun g => by
            ext x
            funext j
            exact ConcreteCategory.congr_hom ((s.π.app ⟨j⟩).comm g) x }
      fac := fun _ _ => rfl
      uniq := fun s f h => by
        ext x
        funext j
        dsimp at *
        rw [← h ⟨j⟩]
        rfl }

/--
Definition of `leftRegular` / `leftRegular` 的定义

English:
abbreviation leftRegular
  signature: (G : Type u) [Monoid G]
  body: Action.ofMulAction G G

中文:
缩写 leftRegular
  签名: (G : 类型u) [Monoid G]
  定义体: Action.ofMulAction G G

Depends on / 依赖: Action, Action.ofMulAction, ofMulAction
-/
abbrev leftRegular (G : Type u) [Monoid G] : Action (Type u) G :=
  Action.ofMulAction G G

/--
Definition of `diagonal` / `diagonal` 的定义

English:
abbreviation diagonal
  signature: (G : Type u) [Monoid G] (n : Nat)
  body: Action.ofMulAction G (Fin n -> G)

中文:
缩写 diagonal
  签名: (G : 类型u) [Monoid G] (n : 自然数)
  定义体: Action.ofMulAction G (Fin n -> G)

Depends on / 依赖: Action, Action.ofMulAction, ofMulAction
-/
abbrev diagonal (G : Type u) [Monoid G] (n : Nat) : Action (Type u) G :=
  Action.ofMulAction G (Fin n -> G)

/--
Definition of `diagonalOneIsoLeftRegular` / `diagonalOneIsoLeftRegular` 的定义

English:
definition diagonalOneIsoLeftRegular
  signature: (G : Type*) [Monoid G]
  body: Action.mkIso (Equiv.funUnique _ _).toIso fun _ => rfl

中文:
定义 diagonalOneIsoLeftRegular
  签名: (G : 类型) [Monoid G]
  定义体: Action.mkIso (Equiv.funUnique _ _).toIso fun _ => rfl

Depends on / 依赖: Action, Action.mkIso, Equiv.funUnique, funUnique
-/
def diagonalOneIsoLeftRegular (G : Type*) [Monoid G] : diagonal G 1 ≅ leftRegular G :=
  Action.mkIso (Equiv.funUnique _ _).toIso fun _ => rfl

namespace FintypeCat

/-- If `X` is a type with `[Fintype X]` and `G` acts on `X`, then `G` also acts on
`FintypeCat.of X`. -/
instance (G : Type*) (X : Type*) [Monoid G] [MulAction G X] [Fintype X] :
    MulAction G (FintypeCat.of X) :=
inferInstanceAs MulAction G X

/--
Definition of `ofMulAction` / `ofMulAction` 的定义

English:
definition ofMulAction
  signature: (G : Type*) (H : FintypeCat.{u}) [Monoid G] [MulAction G H]
  body: H
ρ := InducedCategory.endEquiv.symm.toMonoidHom.comp (TypeCat.endEquiv _).toMonoidHom.comp
    MulAction.toEndHom

@[simp]

中文:
定义 ofMulAction
  签名: (G : 类型) (H : FintypeCat.{u}) [Monoid G] [MulAction G H]
  定义体: H
ρ := InducedCategory.endEquiv.symm.toMonoidHom.comp (TypeCat.endEquiv _).toMonoidHom.comp
    MulAction.toEndHom

@[simp]
-/
def ofMulAction (G : Type*) (H : FintypeCat.{u}) [Monoid G] [MulAction G H] :
    Action FintypeCat G where
  V := H
ρ := InducedCategory.endEquiv.symm.toMonoidHom.comp (TypeCat.endEquiv _).toMonoidHom.comp
    MulAction.toEndHom

@[simp]
/--
theorem `ofMulAction_apply` / 定理 `ofMulAction_apply`

English:
theorem ofMulAction_apply
  statement: {G : Type*} {H : FintypeCat.{u}} [Monoid G] [MulAction G H]
  proof: rfl

中文:
定理 ofMulAction_apply
  结论: {G : 类型} {H : FintypeCat.{u}} [Monoid G] [MulAction G H]
  证明: rfl
-/
theorem ofMulAction_apply {G : Type*} {H : FintypeCat.{u}} [Monoid G] [MulAction G H]
    (g : G) (x : H) : ConcreteCategory.hom ((FintypeCat.ofMulAction G H).ρ g) x = (g • x : H) :=
  rfl

section

/-- Shorthand notation for the quotient of `G` by `H` as a finite `G`-set. -/
notation:10 G:10 " ⧸ₐ " H:10 => Action.FintypeCat.ofMulAction G (FintypeCat.of <| G ⧸ H)

variable {G : Type*} [Group G] (H N : Subgroup G) [Fintype (G ⧸ N)]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `toEndHom` / `toEndHom` 的定义

English:
definition toEndHom
  signature: [N.Normal]
  body: { hom := FintypeCat.homMk (Quotient.lift (fun σ => ⟦σ * v⁻¹⟧) <| fun a b h => Quotient.sound <| by
      apply (QuotientGroup.leftRel_apply).mpr
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
      simpa [mul

中文:
定义 toEndHom
  签名: [N.Normal]
  定义体: { hom := FintypeCat.homMk (Quotient.lift (fun σ => ⟦σ * v⁻¹⟧) <| fun a b h => Quotient.sound <| by
      apply (QuotientGroup.leftRel_apply).mpr
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
      simpa [mul

Depends on / 依赖: FintypeCat, FintypeCat.homMk, Quotient, Quotient.lift, Quotient.sound, QuotientGroup, QuotientGroup.leftRel_apply, leftRel_apply
-/
def toEndHom [N.Normal] : G ->* End (G ⧸ₐ N) where
  toFun v :=
  { hom := FintypeCat.homMk (Quotient.lift (fun σ => ⟦σ * v⁻¹⟧) <| fun a b h => Quotient.sound <| by
      apply (QuotientGroup.leftRel_apply).mpr
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
      simpa [mul_assoc] using Subgroup.Normal.conj_mem ‹_› _ (QuotientGroup.leftRel_apply.mp h) _)
    comm := fun (g : G) => by
      ext (x : G ⧸ N)
      induction x using Quotient.inductionOn with | h x
      dsimp
      apply (Quotient.lift_mk _ _ _).trans
      simp only [QuotientGroup.mk_mul, mul_assoc]
      rfl }
  map_one' := by
    apply Action.hom_ext
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn
    simp
  map_mul' σ τ := by
    apply Action.hom_ext
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn with | _ x
    change ⟦x * (σ * τ)⁻¹⟧ = ⟦x * τ⁻¹ * σ⁻¹⟧
    rw [mul_inv_rev]; rw [mul_assoc]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `toEndHom_apply` / 引理 `toEndHom_apply`

English:
lemma toEndHom_apply
  given: [N.Normal] (g h : G)
  statement: (toEndHom N g).hom ⟦h⟧ = ⟦h * g⁻¹⟧
  proof: rfl

中文:
引理 toEndHom_apply
  条件: [N.Normal] (g h : G)
  结论: (toEndHom N g).hom ⟦h⟧ = ⟦h * g⁻¹⟧
  证明: rfl
-/
lemma toEndHom_apply [N.Normal] (g h : G) : (toEndHom N g).hom ⟦h⟧ = ⟦h * g⁻¹⟧ := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {N} in
/--
lemma `toEndHom_trivial_of_mem` / 引理 `toEndHom_trivial_of_mem`

English:
lemma toEndHom_trivial_of_mem
  given: [N.Normal] {n : G} (hn : n in N)
  statement: toEndHom N n = 𝟙 (G ⧸ₐ N)
  proof: by
  apply Action.hom_ext
  ext (x : G ⧸ N)
  induction x using Quotient.inductionOn
  exact Quotient.sound ((QuotientGroup.leftRel_apply).mpr <| by simpa)

中文:
引理 toEndHom_trivial_of_mem
  条件: [N.Normal] {n : G} (hn : n in N)
  结论: toEndHom N n = 𝟙 (G ⧸ₐ N)
  证明: by
  apply Action.hom_ext
  ext (x : G ⧸ N)
  induction x using Quotient.inductionOn
  exact Quotient.sound ((QuotientGroup.leftRel_apply).mpr <| by simpa)

Depends on / 依赖: Action, Action.hom_ext, Quotient, Quotient.inductionOn, Quotient.sound, QuotientGroup, QuotientGroup.leftRel_apply, hom_ext, inductionOn, leftRel_apply
-/
lemma toEndHom_trivial_of_mem [N.Normal] {n : G} (hn : n in N) : toEndHom N n = 𝟙 (G ⧸ₐ N) := by
  apply Action.hom_ext
  ext (x : G ⧸ N)
  induction x using Quotient.inductionOn
  exact Quotient.sound ((QuotientGroup.leftRel_apply).mpr <| by simpa)

/--
Definition of `quotientToEndHom` / `quotientToEndHom` 的定义

English:
definition quotientToEndHom
  signature: [N.Normal]
  body: QuotientGroup.lift (Subgroup.subgroupOf N H) ((toEndHom N).comp H.subtype) fun _ uinU' =>
    toEndHom_trivial_of_mem uinU'

中文:
定义 quotientToEndHom
  签名: [N.Normal]
  定义体: QuotientGroup.lift (Subgroup.subgroupOf N H) ((toEndHom N).comp H.subtype) fun _ uinU' =>
    toEndHom_trivial_of_mem uinU'

Depends on / 依赖: H.subtype, QuotientGroup, QuotientGroup.lift, Subgroup, Subgroup.subgroupOf, subgroupOf, subtype, toEndHom, toEndHom_trivial_of_mem
-/
def quotientToEndHom [N.Normal] : H ⧸ Subgroup.subgroupOf N H ->* End (G ⧸ₐ N) :=
QuotientGroup.lift (Subgroup.subgroupOf N H) ((toEndHom N).comp H.subtype) fun _ uinU' =>
    toEndHom_trivial_of_mem uinU'

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `quotientToEndHom_mk` / 引理 `quotientToEndHom_mk`

English:
lemma quotientToEndHom_mk
  given: [N.Normal] (x : H) (g : G)
  proof: rfl

中文:
引理 quotientToEndHom_mk
  条件: [N.Normal] (x : H) (g : G)
  证明: rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, Functor, Functor.mono_of_mono_map, Subtype, Subtype.val_injective, forget, mono_of_injective, mono_of_mono_map, val_injective
-/
lemma quotientToEndHom_mk [N.Normal] (x : H) (g : G) :
    (quotientToEndHom H N ⟦x⟧).hom ⟦g⟧ = ⟦g * x⁻¹⟧ :=
  rfl

/--
Definition of `quotientToQuotientOfLE` / `quotientToQuotientOfLE` 的定义

English:
definition quotientToQuotientOfLE
  signature: [Fintype (G ⧸ H)] (h : N <= H)
  body: FintypeCat.homMk (Quotient.lift _ <| fun _ _ hab => Quotient.sound <|
    (QuotientGroup.leftRel_apply).mpr (h <| (QuotientGroup.leftRel_apply).mp hab))
  comm g := by
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn
    rfl

@[simp]

中文:
定义 quotientToQuotientOfLE
  签名: [Fintype (G ⧸ H)] (h : N <= H)
  定义体: FintypeCat.homMk (Quotient.lift _ <| fun _ _ hab => Quotient.sound <|
    (QuotientGroup.leftRel_apply).mpr (h <| (QuotientGroup.leftRel_apply).mp hab))
  comm g := by
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn
    rfl

@[simp]

Depends on / 依赖: FintypeCat, FintypeCat.homMk, Quotient, Quotient.lift, Quotient.sound
-/
def quotientToQuotientOfLE [Fintype (G ⧸ H)] (h : N <= H) : (G ⧸ₐ N) ⟶ (G ⧸ₐ H) where
  hom := FintypeCat.homMk (Quotient.lift _ <| fun _ _ hab => Quotient.sound <|
    (QuotientGroup.leftRel_apply).mpr (h <| (QuotientGroup.leftRel_apply).mp hab))
  comm g := by
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn
    rfl

@[simp]
/--
lemma `quotientToQuotientOfLE_hom_mk` / 引理 `quotientToQuotientOfLE_hom_mk`

English:
lemma quotientToQuotientOfLE_hom_mk
  given: [Fintype (G ⧸ H)] (h : N <= H) (x : G)
  proof: rfl

中文:
引理 quotientToQuotientOfLE_hom_mk
  条件: [Fintype (G ⧸ H)] (h : N <= H) (x : G)
  证明: rfl
-/
lemma quotientToQuotientOfLE_hom_mk [Fintype (G ⧸ H)] (h : N <= H) (x : G) :
    (quotientToQuotientOfLE H N h).hom ⟦x⟧ = ⟦x⟧ :=
  rfl

end

end FintypeCat

section ToMulAction

variable {V : Type (u + 1)} [LargeCategory V] {FV : V -> V -> Type*} {CV : V -> Type*}
variable [forall X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV]

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: {G : Type*} [Monoid G] (X : Action V G)
  body: ConcreteCategory.hom (X.ρ g) x
  one_smul x := by
    change ConcreteCategory.hom (X.ρ 1) x = x
    simp
  mul_smul g h x := by
    change ConcreteCategory.hom (X.ρ (g * h)) x =
      ConcreteCategory.hom (X.ρ g) ((ConcreteCategory.hom (X.ρ h)) x)
    simp

中文:
实例 instMulAction
  签名: {G : 类型} [Monoid G] (X : Action V G)
  定义体: ConcreteCategory.hom (X.ρ g) x
  one_smul x := by
    change ConcreteCategory.hom (X.ρ 1) x = x
    simp
  mul_smul g h x := by
    change ConcreteCategory.hom (X.ρ (g * h)) x =
      ConcreteCategory.hom (X.ρ g) ((ConcreteCategory.hom (X.ρ h)) x)
    simp

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom
-/
instance instMulAction {G : Type*} [Monoid G] (X : Action V G) :
    MulAction G (ToType X) where
  smul g x := ConcreteCategory.hom (X.ρ g) x
  one_smul x := by
    change ConcreteCategory.hom (X.ρ 1) x = x
    simp
  mul_smul g h x := by
    change ConcreteCategory.hom (X.ρ (g * h)) x =
      ConcreteCategory.hom (X.ρ g) ((ConcreteCategory.hom (X.ρ h)) x)
    simp

/-- Specialize `instMulAction` to assist typeclass inference. -/
instance {G : Type*} [Monoid G] (X : Action FintypeCat G) : MulAction G X.V :=
  Action.instMulAction X

end ToMulAction

end Action
