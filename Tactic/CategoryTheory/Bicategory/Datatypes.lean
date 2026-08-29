/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public meta import Mathlib.Tactic.CategoryTheory.Coherence.Datatypes
public import Mathlib.Tactic.CategoryTheory.BicategoricalComp
public import Mathlib.Tactic.CategoryTheory.Coherence.Datatypes

/-!
# Expressions for bicategories

This file converts lean expressions representing 2-morphisms in bicategories into `Mor₂Iso`
or `Mor` terms. The converted expressions are used in the coherence tactics and the string diagram
widgets.

-/

public meta section

open Lean Meta Elab Qq
open CategoryTheory Mathlib.Tactic.BicategoryLike Bicategory

namespace Mathlib.Tactic.Bicategory

/--
Definition of `srcExpr` / `srcExpr` 的定义

English:
definition srcExpr
  signature: (η : Expr)
  body: do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => return f
  | _ => throwError m!"{η} is not a morphism"

中文:
定义 srcExpr
  签名: (η : Expr)
  定义体: do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => return f
  | _ => throwError m!"{η} is not a morphism"
-/
def srcExpr (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => return f
  | _ => throwError m!"{η} is not a morphism"

/--
Definition of `tgtExpr` / `tgtExpr` 的定义

English:
definition tgtExpr
  signature: (η : Expr)
  body: do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => return g
  | _ => throwError m!"{η} is not a morphism"

中文:
定义 tgtExpr
  签名: (η : Expr)
  定义体: do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => return g
  | _ => throwError m!"{η} is not a morphism"
-/
def tgtExpr (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => return g
  | _ => throwError m!"{η} is not a morphism"

/--
Definition of `srcExprOfIso` / `srcExprOfIso` 的定义

English:
definition srcExprOfIso
  signature: (η : Expr)
  body: do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Iso, #[_, _, f, _]) => return f
  | _ => throwError m!"{η} is not a morphism"

中文:
定义 srcExprOfIso
  签名: (η : Expr)
  定义体: do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Iso, #[_, _, f, _]) => return f
  | _ => throwError m!"{η} is not a morphism"
-/
def srcExprOfIso (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Iso, #[_, _, f, _]) => return f
  | _ => throwError m!"{η} is not a morphism"

/--
Definition of `tgtExprOfIso` / `tgtExprOfIso` 的定义

English:
definition tgtExprOfIso
  signature: (η : Expr)
  body: do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Iso, #[_, _, _, g]) => return g
  | _ => throwError m!"{η} is not a morphism"

中文:
定义 tgtExprOfIso
  签名: (η : Expr)
  定义体: do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Iso, #[_, _, _, g]) => return g
  | _ => throwError m!"{η} is not a morphism"
-/
def tgtExprOfIso (η : Expr) : MetaM Expr := do
  match (← whnfR (← inferType η)).getAppFnArgs with
  | (``Iso, #[_, _, _, g]) => return g
  | _ => throwError m!"{η} is not a morphism"

initialize registerTraceClass `bicategory

/--
Definition of `Context` / `Context` 的定义

English:
structure Context
  parameters: where
  axioms and operations (5):
    - level₂ : Level
    - level₁ : Level
    - level₀ : Level
    - B : Q(Type level₀)
    - instBicategory : Q(Bicategory.{level₂, level₁} $B)

中文:
结构 Context
  参数: where
  公理与运算 (5 个):
    - level₂ : Level
    - level₁ : Level
    - level₀ : Level
    - B : Q(Type level₀)
    - instBicategory : Q(Bicategory.{level₂, level₁} $B)
-/
structure Context where
  /-- The level for 2-morphisms. -/
  level₂ : Level
  /-- The level for 1-morphisms. -/
  level₁ : Level
  /-- The level for objects. -/
  level₀ : Level
  /-- The expression for the underlying category. -/
  B : Q(Type level₀)
  /-- The bicategory instance. -/
  instBicategory : Q(Bicategory.{level₂, level₁} $B)

/--
Definition of `mkContext?` / `mkContext?` 的定义

English:
definition mkContext?
  signature: (e : Expr)
  body: do
  let e ← instantiateMVars e
let type ← instantiateMVars ← inferType e
  match (← whnfR (← inferType e)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) =>
let fType ← instantiateMVars ← inferType f
    match (← whnfR fType).getAppFnArgs with
    | (``Quiver.Hom, #[_, _, a, _]) =>
      let B

中文:
定义 mkContext?
  签名: (e : Expr)
  定义体: do
  let e ← instantiateMVars e
let type ← instantiateMVars ← inferType e
  match (← whnfR (← inferType e)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) =>
let fType ← instantiateMVars ← inferType f
    match (← whnfR fType).getAppFnArgs with
    | (``Quiver.Hom, #[_, _, a, _]) =>
      let B
-/
def mkContext? (e : Expr) : MetaM (Option Context) := do
  let e ← instantiateMVars e
let type ← instantiateMVars ← inferType e
  match (← whnfR (← inferType e)).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) =>
let fType ← instantiateMVars ← inferType f
    match (← whnfR fType).getAppFnArgs with
    | (``Quiver.Hom, #[_, _, a, _]) =>
      let B ← inferType a
      let .succ level₀ ← getLevel B | return none
      let .succ level₁ ← getLevel fType | return none
      let .succ level₂ ← getLevel type | return none
      let some instBicategory ← synthInstance?
        (mkAppN (.const ``Bicategory [level₂, level₁, level₀]) #[B]) | return none
      return some ⟨level₂, level₁, level₀, B, instBicategory⟩
    | _ => return none
  | _ => return none

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BicategoryLike.Context Bicategory.Context
  body: Bicategory.mkContext?

中文:
实例 :
  签名: BicategoryLike.Context Bicategory.Context
  定义体: Bicategory.mkContext?

Depends on / 依赖: Bicategory, Bicategory.mkContext, e.symm, mkContext
-/
instance : BicategoryLike.Context Bicategory.Context where
  mkContext? := Bicategory.mkContext?

/--
Definition of `BicategoryM` / `BicategoryM` 的定义

English:
abbreviation BicategoryM
  body: CoherenceM Context

中文:
缩写 BicategoryM
  定义体: CoherenceM Context

Depends on / 依赖: CoherenceM, Context
-/
abbrev BicategoryM := CoherenceM Context

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadMor₁ BicategoryM
  body: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a_e : Q($ctx.B) := a.e
    return .id q(𝟙 $a_e) a
  comp₁M f g := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    h

中文:
实例 :
  签名: MonadMor₁ BicategoryM
  定义体: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a_e : Q($ctx.B) := a.e
    return .id q(𝟙 $a_e) a
  comp₁M f g := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    h
-/
instance : MonadMor₁ BicategoryM where
  id₁M a := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a_e : Q($ctx.B) := a.e
    return .id q(𝟙 $a_e) a
  comp₁M f g := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($b ⟶ $c) := g.e
    return .comp q($f_e ≫ $g_e) f g

section

universe w v u
variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

/--
theorem `structuralIso_inv` / 定理 `structuralIso_inv`

English:
theorem structuralIso_inv
  given: {f g : a ⟶ b} (η : f ≅ g)
  proof: by
  simp only [Iso.symm_hom]

中文:
定理 structuralIso_inv
  条件: {f g : a ⟶ b} (η : f ≅ g)
  证明: by
  simp only [Iso.symm_hom]

Depends on / 依赖: Iso.symm_hom, symm_hom
-/
theorem structuralIso_inv {f g : a ⟶ b} (η : f ≅ g) :
    η.symm.hom = η.inv := by
  simp only [Iso.symm_hom]

/--
theorem `structuralIsoOfExpr_comp` / 定理 `structuralIsoOfExpr_comp`

English:
theorem structuralIsoOfExpr_comp
  statement: {f g h : a ⟶ b}
  proof: by
  simp [ih_η, ih_θ]

中文:
定理 structuralIsoOfExpr_comp
  结论: {f g h : a ⟶ b}
  证明: by
  simp [ih_η, ih_θ]
-/
theorem structuralIsoOfExpr_comp {f g h : a ⟶ b}
    (η : f ⟶ g) (η' : f ≅ g) (ih_η : η'.hom = η)
    (θ : g ⟶ h) (θ' : g ≅ h) (ih_θ : θ'.hom = θ) :
    (η' ≪≫ θ').hom = η ≫ θ := by
  simp [ih_η, ih_θ]

/--
theorem `structuralIsoOfExpr_whiskerLeft` / 定理 `structuralIsoOfExpr_whiskerLeft`

English:
theorem structuralIsoOfExpr_whiskerLeft
  statement: (f : a ⟶ b) {g h : b ⟶ c}
  proof: by
  simp [ih_η]

中文:
定理 structuralIsoOfExpr_whiskerLeft
  结论: (f : a ⟶ b) {g h : b ⟶ c}
  证明: by
  simp [ih_η]
-/
theorem structuralIsoOfExpr_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c}
    (η : g ⟶ h) (η' : g ≅ h) (ih_η : η'.hom = η) :
    (whiskerLeftIso f η').hom = f ◁ η := by
  simp [ih_η]

/--
theorem `structuralIsoOfExpr_whiskerRight` / 定理 `structuralIsoOfExpr_whiskerRight`

English:
theorem structuralIsoOfExpr_whiskerRight
  statement: {f g : a ⟶ b} (h : b ⟶ c)
  proof: by
  simp [ih_η]

中文:
定理 structuralIsoOfExpr_whiskerRight
  结论: {f g : a ⟶ b} (h : b ⟶ c)
  证明: by
  simp [ih_η]
-/
theorem structuralIsoOfExpr_whiskerRight {f g : a ⟶ b} (h : b ⟶ c)
    (η : f ⟶ g) (η' : f ≅ g) (ih_η : η'.hom = η) :
    (whiskerRightIso η' h).hom = η ▷ h := by
  simp [ih_η]

/--
theorem `StructuralOfExpr_bicategoricalComp` / 定理 `StructuralOfExpr_bicategoricalComp`

English:
theorem StructuralOfExpr_bicategoricalComp
  statement: {f g h i : a ⟶ b} [BicategoricalCoherence g h]
  proof: by
  simp [ih_η, ih_θ, bicategoricalIsoComp, bicategoricalComp]

中文:
定理 StructuralOfExpr_bicategoricalComp
  结论: {f g h i : a ⟶ b} [BicategoricalCoherence g h]
  证明: by
  simp [ih_η, ih_θ, bicategoricalIsoComp, bicategoricalComp]

Depends on / 依赖: bicategoricalComp, bicategoricalIsoComp
-/
theorem StructuralOfExpr_bicategoricalComp {f g h i : a ⟶ b} [BicategoricalCoherence g h]
    (η : f ⟶ g) (η' : f ≅ g) (ih_η : η'.hom = η) (θ : h ⟶ i) (θ' : h ≅ i) (ih_θ : θ'.hom = θ) :
    (bicategoricalIsoComp η' θ').hom = η otimes≫ θ := by
  simp [ih_η, ih_θ, bicategoricalIsoComp, bicategoricalComp]

end

open MonadMor₁

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadMor₂Iso BicategoryM
  body: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have d : Q($ctx.B) := h.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($b ⟶ $c) := g.e
    have h_e : Q($c ⟶ $d) := h.e
    re

中文:
实例 :
  签名: MonadMor₂Iso BicategoryM
  定义体: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have d : Q($ctx.B) := h.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($b ⟶ $c) := g.e
    have h_e : Q($c ⟶ $d) := h.e
    re
-/
instance : MonadMor₂Iso BicategoryM where
  associatorM f g h := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have d : Q($ctx.B) := h.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($b ⟶ $c) := g.e
    have h_e : Q($c ⟶ $d) := h.e
    return .associator q(α_ $f_e $g_e $h_e) f g h
  leftUnitorM f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    return .leftUnitor q(fun_ $f_e) f
  rightUnitorM f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    return .rightUnitor q(ρ_ $f_e) f
  id₂M f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    return .id q(Iso.refl $f_e) f
  coherenceHomM f g inst := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have inst : Q(BicategoricalCoherence $f_e $g_e) := inst
    match (← whnfI inst).getAppFnArgs with
    | (``BicategoricalCoherence.mk, #[_, _, _, _, _, _, α]) =>
      let e : Q($f_e ≅ $g_e) := q(BicategoricalCoherence.iso)
      return ⟨e, f, g, inst, α⟩
    | _ => throwError m!"failed to unfold {inst}"
  comp₂M η θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have h_e : Q($a ⟶ $b) := h.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    have θ_e : Q($g_e ≅ $h_e) := θ.e
    return .comp q($η_e ≪≫ $θ_e) f g h η θ
  whiskerLeftM f η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let g ← η.srcM
    let h ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($b ⟶ $c) := g.e
    have h_e : Q($b ⟶ $c) := h.e
    have η_e : Q($g_e ≅ $h_e) := η.e
    return .whiskerLeft q(whiskerLeftIso $f_e $η_e) f g h η
  whiskerRightM η h := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := h.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have h_e : Q($b ⟶ $c) := h.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    return .whiskerRight q(whiskerRightIso $η_e $h_e) f g η h
  horizontalCompM _ _ := throwError "horizontal composition is not implemented"
  symmM η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    return .inv q(Iso.symm $η_e) f g η
  coherenceCompM α η θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have h_e : Q($a ⟶ $b) := h.e
    have i_e : Q($a ⟶ $b) := i.e
    have _inst : Q(BicategoricalCoherence $g_e $h_e) := α.inst
    have η_e : Q($f_e ≅ $g_e) := η.e
    have θ_e : Q($h_e ≅ $i_e) := θ.e
    return .coherenceComp q($η_e ≪otimes≫ $θ_e) f g h i α η θ

open MonadMor₂Iso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadMor₂ BicategoryM
  body: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    let e : Q($f_e ⟶ $g_e) := q(

中文:
实例 :
  签名: MonadMor₂ BicategoryM
  定义体: do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    let e : Q($f_e ⟶ $g_e) := q(
-/
instance : MonadMor₂ BicategoryM where
  homM η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    let e : Q($f_e ⟶ $g_e) := q(Iso.hom $η_e)
    have eq : Q(Iso.hom $η_e = $e) := q(rfl)
    return .isoHom q(Iso.hom $η_e) ⟨η, eq⟩ η
  atomHomM η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f := η.src
    let g := η.tgt
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    return .mk q(Iso.hom $η_e) f g
  invM η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    let e : Q($g_e ⟶ $f_e) := q(Iso.inv $η_e)
    let η_inv ← symmM η
    let eq : Q(Iso.inv $η_e = $e) := q(Iso.symm_hom $η_e)
    return .isoInv e ⟨η_inv, eq⟩ η
  atomInvM η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f := η.src
    let g := η.tgt
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have η_e : Q($f_e ≅ $g_e) := η.e
    return .mk q(Iso.inv $η_e) g f
  id₂M f := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    let e : Q($f_e ⟶ $f_e) := q(𝟙 $f_e)
    let eq : Q(𝟙 $f_e = $e) := q(Iso.refl_hom $f_e)
return .id e ⟨.structuralAtom ← id₂M f, eq⟩ f
  comp₂M η θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have h_e : Q($a ⟶ $b) := h.e
    have η_e : Q($f_e ⟶ $g_e) := η.e
    have θ_e : Q($g_e ⟶ $h_e) := θ.e
    let iso_lift? ← (match (η.isoLift?, θ.isoLift?) with
      | (some η_iso, some θ_iso) =>
        have η_iso_e : Q($f_e ≅ $g_e) := η_iso.e.e
        have θ_iso_e : Q($g_e ≅ $h_e) := θ_iso.e.e
        have η_iso_eq : Q(Iso.hom $η_iso_e = $η_e) := η_iso.eq
        have θ_iso_eq : Q(Iso.hom $θ_iso_e = $θ_e) := θ_iso.eq
        let eq := q(structuralIsoOfExpr_comp _ _ $η_iso_eq _ _ $θ_iso_eq)
        return some ⟨← comp₂M η_iso.e θ_iso.e, eq⟩
      | _ => return none)
    let e : Q($f_e ⟶ $h_e) := q($η_e ≫ $θ_e)
    return .comp e iso_lift? f g h η θ
  whiskerLeftM f η := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let g ← η.srcM
    let h ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have c : Q($ctx.B) := g.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($b ⟶ $c) := g.e
    have h_e : Q($b ⟶ $c) := h.e
    have η_e : Q($g_e ⟶ $h_e) := η.e
    let iso_lift? ← (match η.isoLift? with
      | some η_iso => do
        have η_iso_e : Q($g_e ≅ $h_e) := η_iso.e.e
        have η_iso_eq : Q(Iso.hom $η_iso_e = $η_e) := η_iso.eq
        let eq := q(structuralIsoOfExpr_whiskerLeft $f_e _ _ $η_iso_eq)
        return some ⟨← whiskerLeftM f η_iso.e, eq⟩
      | _ => return none)
    let e : Q($f_e ≫ $g_e ⟶ $f_e ≫ $h_e) := q($f_e ◁ $η_e)
    return .whiskerLeft e iso_lift? f g h η
  whiskerRightM η h := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := h.src.e
    have c : Q($ctx.B) := h.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have h_e : Q($b ⟶ $c) := h.e
    have η_e : Q($f_e ⟶ $g_e) := η.e
    let iso_lift? ← (match η.isoLift? with
      | some η_iso => do
        have η_iso_e : Q($f_e ≅ $g_e) := η_iso.e.e
        have η_iso_eq : Q(Iso.hom $η_iso_e = $η_e) := η_iso.eq
        let eq := q(structuralIsoOfExpr_whiskerRight $h_e _ _ $η_iso_eq)
        return some ⟨← whiskerRightM η_iso.e h, eq⟩
      | _ => return none)
    let e : Q($f_e ≫ $h_e ⟶ $g_e ≫ $h_e) := q($η_e ▷ $h_e)
    return .whiskerRight e iso_lift? f g η h
  horizontalCompM _ _ := throwError "horizontal composition is not implemented"
  coherenceCompM α η θ := do
    let ctx ← read
    let _bicat := ctx.instBicategory
    let f ← η.srcM
    let g ← η.tgtM
    let h ← θ.srcM
    let i ← θ.tgtM
    have a : Q($ctx.B) := f.src.e
    have b : Q($ctx.B) := f.tgt.e
    have f_e : Q($a ⟶ $b) := f.e
    have g_e : Q($a ⟶ $b) := g.e
    have h_e : Q($a ⟶ $b) := h.e
    have i_e : Q($a ⟶ $b) := i.e
    have _inst : Q(BicategoricalCoherence $g_e $h_e) := α.inst
    have η_e : Q($f_e ⟶ $g_e) := η.e
    have θ_e : Q($h_e ⟶ $i_e) := θ.e
    let iso_lift? ← (match (η.isoLift?, θ.isoLift?) with
      | (some η_iso, some θ_iso) => do
        have η_iso_e : Q($f_e ≅ $g_e) := η_iso.e.e
        have θ_iso_e : Q($h_e ≅ $i_e) := θ_iso.e.e
        have η_iso_eq : Q(Iso.hom $η_iso_e = $η_e) := η_iso.eq
        have θ_iso_eq : Q(Iso.hom $θ_iso_e = $θ_e) := θ_iso.eq
        let eq := q(StructuralOfExpr_bicategoricalComp _ _ $η_iso_eq _ _ $θ_iso_eq)
        return some ⟨← coherenceCompM α η_iso.e θ_iso.e, eq⟩
      | _ => return none)
    let e : Q($f_e ⟶ $i_e) := q($η_e otimes≫ $θ_e)
    return .coherenceComp e iso_lift? f g h i α η θ

/--
Definition of `id₁?` / `id₁?` 的定义

English:
definition id₁?
  signature: (e : Expr)
  body: do
  let ctx ← read
  let _bicat := ctx.instBicategory
  let a : Q($ctx.B) ← mkFreshExprMVar ctx.B
if ← withDefault isDefEq e q(𝟙 $a) then
    return some ⟨← instantiateMVars a⟩
  else
    return none

中文:
定义 id₁?
  签名: (e : Expr)
  定义体: do
  let ctx ← read
  let _bicat := ctx.instBicategory
  let a : Q($ctx.B) ← mkFreshExprMVar ctx.B
if ← withDefault isDefEq e q(𝟙 $a) then
    return some ⟨← instantiateMVars a⟩
  else
    return none
-/
def id₁? (e : Expr) : BicategoryM (Option Obj) := do
  let ctx ← read
  let _bicat := ctx.instBicategory
  let a : Q($ctx.B) ← mkFreshExprMVar ctx.B
if ← withDefault isDefEq e q(𝟙 $a) then
    return some ⟨← instantiateMVars a⟩
  else
    return none

/--
Definition of `comp?` / `comp?` 的定义

English:
definition comp?
  signature: (e : Expr)
  body: do
  let ctx ← read
  let _bicat := ctx.instBicategory
  let a ← mkFreshExprMVarQ ctx.B
  let b ← mkFreshExprMVarQ ctx.B
  let c ← mkFreshExprMVarQ ctx.B
  let f ← mkFreshExprMVarQ q($a ⟶ $b)
  let g ← mkFreshExprMVarQ q($b ⟶ $c)
if ← withDefault isDefEq e q($f ≫ $g) then
    let a ← instantiateMVar

中文:
定义 comp?
  签名: (e : Expr)
  定义体: do
  let ctx ← read
  let _bicat := ctx.instBicategory
  let a ← mkFreshExprMVarQ ctx.B
  let b ← mkFreshExprMVarQ ctx.B
  let c ← mkFreshExprMVarQ ctx.B
  let f ← mkFreshExprMVarQ q($a ⟶ $b)
  let g ← mkFreshExprMVarQ q($b ⟶ $c)
if ← withDefault isDefEq e q($f ≫ $g) then
    let a ← instantiateMVar
-/
def comp? (e : Expr) : BicategoryM (Option (Mor₁ × Mor₁)) := do
  let ctx ← read
  let _bicat := ctx.instBicategory
  let a ← mkFreshExprMVarQ ctx.B
  let b ← mkFreshExprMVarQ ctx.B
  let c ← mkFreshExprMVarQ ctx.B
  let f ← mkFreshExprMVarQ q($a ⟶ $b)
  let g ← mkFreshExprMVarQ q($b ⟶ $c)
if ← withDefault isDefEq e q($f ≫ $g) then
    let a ← instantiateMVars a
    let b ← instantiateMVars b
    let c ← instantiateMVars c
    let f ← instantiateMVars f
    let g ← instantiateMVars g
    return some ((.of ⟨f, ⟨a⟩, ⟨b⟩⟩), .of ⟨g, ⟨b⟩, ⟨c⟩⟩)
  else
    return none

/--
Definition of `mor₁OfExpr` / `mor₁OfExpr` 的定义

English:
definition mor₁OfExpr
  signature: (e : Expr)
  body: do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError m!"expression contains metavariables:\n{e}"
  if let some f := (← get).cache.find? e then
    return f
  let f ←
    if let some a ← id₁? e then
      MonadMor₁.id₁M a
    else if let some (f, g) ← comp? e then
      MonadMor₁.co

中文:
定义 mor₁OfExpr
  签名: (e : Expr)
  定义体: do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError m!"expression contains metavariables:\n{e}"
  if let some f := (← get).cache.find? e then
    return f
  let f ←
    if let some a ← id₁? e then
      MonadMor₁.id₁M a
    else if let some (f, g) ← comp? e then
      MonadMor₁.co
-/
partial def mor₁OfExpr (e : Expr) : BicategoryM Mor₁ := do
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError m!"expression contains metavariables:\n{e}"
  if let some f := (← get).cache.find? e then
    return f
  let f ←
    if let some a ← id₁? e then
      MonadMor₁.id₁M a
    else if let some (f, g) ← comp? e then
      MonadMor₁.comp₁M (← mor₁OfExpr f.e) (← mor₁OfExpr g.e)
    else
      return Mor₁.of ⟨e, ⟨← srcExpr e⟩, ⟨ ← tgtExpr e⟩⟩
  modify fun s => { s with cache := s.cache.insert e f }
  return f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MkMor₁ BicategoryM
  body: mor₁OfExpr

中文:
实例 :
  签名: MkMor₁ BicategoryM
  定义体: mor₁OfExpr
-/
instance : MkMor₁ BicategoryM where
  ofExpr := mor₁OfExpr

/--
Definition of `Mor₂IsoOfExpr` / `Mor₂IsoOfExpr` 的定义

English:
definition Mor₂IsoOfExpr
  signature: (e : Expr)
  body: do
  match (← whnfR e).getAppFnArgs with
  | (``Bicategory.associator, #[_, _, _, _, _, _, f, g, h]) =>
    associatorM' (← MkMor₁.ofExpr f) (← MkMor₁.ofExpr g) (← MkMor₁.ofExpr h)
  | (``Bicategory.leftUnitor, #[_, _, _, _, f]) =>
    leftUnitorM' (← MkMor₁.ofExpr f)
  | (``Bicategory.rightUnitor, 

中文:
定义 Mor₂IsoOfExpr
  签名: (e : Expr)
  定义体: do
  match (← whnfR e).getAppFnArgs with
  | (``Bicategory.associator, #[_, _, _, _, _, _, f, g, h]) =>
    associatorM' (← MkMor₁.ofExpr f) (← MkMor₁.ofExpr g) (← MkMor₁.ofExpr h)
  | (``Bicategory.leftUnitor, #[_, _, _, _, f]) =>
    leftUnitorM' (← MkMor₁.ofExpr f)
  | (``Bicategory.rightUnitor, 
-/
partial def Mor₂IsoOfExpr (e : Expr) : BicategoryM Mor₂Iso := do
  match (← whnfR e).getAppFnArgs with
  | (``Bicategory.associator, #[_, _, _, _, _, _, f, g, h]) =>
    associatorM' (← MkMor₁.ofExpr f) (← MkMor₁.ofExpr g) (← MkMor₁.ofExpr h)
  | (``Bicategory.leftUnitor, #[_, _, _, _, f]) =>
    leftUnitorM' (← MkMor₁.ofExpr f)
  | (``Bicategory.rightUnitor, #[_, _, _, _, f]) =>
    rightUnitorM' (← MkMor₁.ofExpr f)
  | (``Iso.refl, #[_, _, f]) =>
    id₂M' (← MkMor₁.ofExpr f)
  | (``Iso.symm, #[_, _, _, _, η]) =>
    symmM (← Mor₂IsoOfExpr η)
  | (``Iso.trans, #[_, _, _, _, _, η, θ]) =>
    comp₂M (← Mor₂IsoOfExpr η) (← Mor₂IsoOfExpr θ)
  | (``Bicategory.whiskerLeftIso, #[_, _, _, _, _, f, _, _, η]) =>
    whiskerLeftM (← MkMor₁.ofExpr f) (← Mor₂IsoOfExpr η)
  | (``Bicategory.whiskerRightIso, #[_, _, _, _, _, _, _, η, h]) =>
    whiskerRightM (← Mor₂IsoOfExpr η) (← MkMor₁.ofExpr h)
  | (``bicategoricalIsoComp, #[_, _, _, _, _, g, h, _, inst, η, θ]) =>
    let α ← coherenceHomM (← MkMor₁.ofExpr g) (← MkMor₁.ofExpr h) inst
    coherenceCompM α (← Mor₂IsoOfExpr η) (← Mor₂IsoOfExpr θ)
  | (``BicategoricalCoherence.iso, #[_, _, _, _, f, g, inst]) =>
    coherenceHomM' (← MkMor₁.ofExpr f) (← MkMor₁.ofExpr g) inst
  | _ =>
    return .of ⟨e, ← MkMor₁.ofExpr (← srcExprOfIso e), ← MkMor₁.ofExpr (← tgtExprOfIso e)⟩

open MonadMor₂ in
/--
Definition of `Mor₂OfExpr` / `Mor₂OfExpr` 的定义

English:
definition Mor₂OfExpr
  signature: (e : Expr)
  body: do
  match ← whnfR e with
  -- whnfR version of `Iso.hom η`
  | .proj ``Iso 0 η => homM (← Mor₂IsoOfExpr η)
  -- whnfR version of `Iso.inv η`
  | .proj ``Iso 1 η => invM (← Mor₂IsoOfExpr η)
  | .app .. => match (← whnfR e).getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) => id₂M (← MkMor₁.o

中文:
定义 Mor₂OfExpr
  签名: (e : Expr)
  定义体: do
  match ← whnfR e with
  -- whnfR version of `Iso.hom η`
  | .proj ``Iso 0 η => homM (← Mor₂IsoOfExpr η)
  -- whnfR version of `Iso.inv η`
  | .proj ``Iso 1 η => invM (← Mor₂IsoOfExpr η)
  | .app .. => match (← whnfR e).getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) => id₂M (← MkMor₁.o
-/
partial def Mor₂OfExpr (e : Expr) : BicategoryM Mor₂ := do
  match ← whnfR e with
  -- whnfR version of `Iso.hom η`
  | .proj ``Iso 0 η => homM (← Mor₂IsoOfExpr η)
  -- whnfR version of `Iso.inv η`
  | .proj ``Iso 1 η => invM (← Mor₂IsoOfExpr η)
  | .app .. => match (← whnfR e).getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) => id₂M (← MkMor₁.ofExpr f)
    | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
      comp₂M (← Mor₂OfExpr η) (← Mor₂OfExpr θ)
    | (``Bicategory.whiskerLeft, #[_, _, _, _, _, f, _, _, η]) =>
      whiskerLeftM (← MkMor₁.ofExpr f) (← Mor₂OfExpr η)
    | (``Bicategory.whiskerRight, #[_, _, _, _, _, _, _, η, h]) =>
      whiskerRightM (← Mor₂OfExpr η) (← MkMor₁.ofExpr h)
    | (``bicategoricalComp, #[_, _, _, _, _, g, h, _, inst, η, θ]) =>
      let α ← coherenceHomM (← MkMor₁.ofExpr g) (← MkMor₁.ofExpr h) inst
      coherenceCompM α (← Mor₂OfExpr η) (← Mor₂OfExpr θ)
    | _ => return .of ⟨e, ← MkMor₁.ofExpr (← srcExpr e), ← MkMor₁.ofExpr (← tgtExpr e)⟩
  | _ =>
    return .of ⟨e, ← MkMor₁.ofExpr (← srcExpr e), ← MkMor₁.ofExpr (← tgtExpr e)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BicategoryLike.MkMor₂ BicategoryM
  body: Mor₂OfExpr

中文:
实例 :
  签名: BicategoryLike.MkMor₂ BicategoryM
  定义体: Mor₂OfExpr
-/
instance : BicategoryLike.MkMor₂ BicategoryM where
  ofExpr := Mor₂OfExpr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonadCoherehnceHom BicategoryM
  body: Mor₂IsoOfExpr α.unfold

中文:
实例 :
  签名: MonadCoherehnceHom BicategoryM
  定义体: Mor₂IsoOfExpr α.unfold
-/
instance : MonadCoherehnceHom BicategoryM where
  unfoldM α := Mor₂IsoOfExpr α.unfold

end Mathlib.Tactic.Bicategory
